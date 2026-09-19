package service

import (
	"bytes"
	"context"
	"crypto/aes"
	"crypto/cipher"
	"crypto/ed25519"
	"crypto/hmac"
	"crypto/sha256"
	"crypto/x509"
	"encoding/base64"
	"encoding/hex"
	"encoding/json"
	"errors"
	"fmt"
	"io"
	"log/slog"
	"net/http"
	"net/url"
	"strconv"
	"strings"
	"sync"
	"time"

	"golang.org/x/crypto/hkdf"
	"golang.org/x/sync/singleflight"
)

// ZCode V4 客户端签名（逆向自 ZCode 3.11.2 桌面端，2026-09 实测）：
// 先用 API key secret 经 HKDF 派生的 HMAC 与智谱握手，换回 AES-GCM 加密的
// Ed25519 私钥（仅凭据可解密），再给每个出站请求附上 PoW 与 Ed25519 签名头
// （X-Client-*）。服务端据此把请求识别为 ZCode 渠道，渠道专属计量优惠
// （如夜间畅用、150% 额度）只对签名请求生效，普通请求照常计量。
// 任一环节失败一律 fail-open：仅记 Warn 不设头，绝不阻断请求。
const (
	zcodeSignAppID         = "zcode"
	zcodeSignClientVersion = "3.11.2"
	zcodeSignKDFSalt       = "WD_CLIENT_SIGN_KDF_SALT"
	// zcodeSignHost 是 ZCode 签名唯一支持的出站官方域名（对齐 omp zcode.ts
	// 的 SIGN_ORIGIN）：签名只被官方识别，中转/自定义 base_url 不签名。
	zcodeSignHost = "open.bigmodel.cn"
	// zcodePowLeadingZeroBytes 是 PoW 难度：SHA-256 摘要首字节为 0（8 bit），
	// 期望约 256 次哈希，毫秒级。
	zcodePowLeadingZeroBytes = 1
	// zcodeNonceHexLen 是握手/签名 nonce 的 hex 字符数（randomHex 按字节计）。
	zcodeNonceHexLen      = 16
	zcodeHandshakeTimeout = 15 * time.Second
)

// zcodeHandshakeURL 是握手端点；包级 var 便于测试用 httptest 替换。
var zcodeHandshakeURL = "https://open.bigmodel.cn/api/paas/c1f3a7e2/v2/client"

var (
	// zcodePrivateKeys 按 apiKeyId 缓存握手换来的 Ed25519 私钥；
	// VERIFY_* 失效后清缓存重握手。
	zcodePrivateKeys sync.Map
	// zcodeHandshakeFlight 按 apiKeyId 去重并发握手。
	zcodeHandshakeFlight singleflight.Group
	// zcodeSessionID 是进程级会话 id，参与 PoW 与签名消息，只需稳定，
	// 无需与 ZCode 客户端一致。
	zcodeSessionID = sync.OnceValue(func() string { return randomHex(zcodeNonceHexLen / 2) })
)

// IsZcodeSigningEnabled 判断 zhipu API Key 账号是否处于 ZCode 渠道签名
// 协议档（api_protocol=zcode）。该档位绑定智谱官方固定端点（前端锁定
// base_url，出站另有域名守卫），coding/payg 模式均可选用。
func (a *Account) IsZcodeSigningEnabled() bool {
	return a != nil && a.Platform == PlatformZhipu && a.Type == AccountTypeAPIKey &&
		a.GetAPIProtocol() == APIProtocolZcode
}

// isZcodeSigningTarget 报告本次出站目标是否 ZCode 签名唯一支持的官方域名。
func isZcodeSigningTarget(targetURL string) bool {
	u, err := url.Parse(strings.TrimSpace(targetURL))
	return err == nil && strings.EqualFold(u.Hostname(), zcodeSignHost)
}

// zcodeParseSigningCredential 解析 `<id>.<secret>` 形式的智谱凭据；
// 恰含一个分隔点才算合法，否则 ok=false（等价于不签名，fail-open）。
func zcodeParseSigningCredential(credential string) (apiKeyID, apiKeySecret string, ok bool) {
	dot := strings.Index(credential, ".")
	if dot <= 0 || dot != strings.LastIndex(credential, ".") {
		return "", "", false
	}
	id, secret := credential[:dot], credential[dot+1:]
	if id == "" || secret == "" {
		return "", "", false
	}
	return id, secret, true
}

// zcodeDerive 按 ZCode 客户端 KDF 从 API key secret 派生 32 字节密钥
// （HKDF-SHA256，salt 固定，info 区分用途）。
func zcodeDerive(secret, info string) ([]byte, error) {
	reader := hkdf.New(sha256.New, []byte(secret), []byte(zcodeSignKDFSalt), []byte(info))
	key := make([]byte, 32)
	if _, err := io.ReadFull(reader, key); err != nil {
		return nil, fmt.Errorf("zcode hkdf derive %q: %w", info, err)
	}
	return key, nil
}

// zcodeSignDoer 是签名握手所需的出站请求能力，HTTPUpstream.Do 已满足。
type zcodeSignDoer interface {
	Do(*http.Request, string, int64, int) (*http.Response, error)
}

// zcodeHandshake 执行 ZCode V4 握手：用 API key secret 派生的 HMAC 自证
// 持钥，服务端返回 AES-GCM 加密的 Ed25519 私钥（AAD 为 apiKeyId），解密
// 明文是 base64 字符串，内层才是 PKCS8 DER。算法串与 zcode.ts 参考实现
// 逐字对齐，不得改动。
func zcodeHandshake(
	ctx context.Context,
	doer zcodeSignDoer,
	proxyURL, credential, apiKeyID, apiKeySecret string,
	accountID int64,
	accountConcurrency int,
) (ed25519.PrivateKey, error) {
	ts := strconv.FormatInt(time.Now().UnixMilli(), 10)
	nonce := randomHex(zcodeNonceHexLen / 2)
	hmacKey, err := zcodeDerive(apiKeySecret, "getSignKey_hmac")
	if err != nil {
		return nil, err
	}
	mac := hmac.New(sha256.New, hmacKey)
	mac.Write([]byte("get_sign_key\n" + apiKeyID + "\n" + ts + "\n" + nonce))
	sig := base64.StdEncoding.EncodeToString(mac.Sum(nil))

	payload, err := json.Marshal(struct {
		APIKey string `json:"apiKey"`
		Nonce  string `json:"nonce"`
		Sig    string `json:"sig"`
		Ts     string `json:"ts"`
	}{credential, nonce, sig, ts})
	if err != nil {
		return nil, fmt.Errorf("zcode handshake marshal body: %w", err)
	}

	req, err := http.NewRequestWithContext(ctx, http.MethodPost, zcodeHandshakeURL, bytes.NewReader(payload))
	if err != nil {
		return nil, fmt.Errorf("zcode handshake build request: %w", err)
	}
	req.Header.Set("Authorization", credential)
	req.Header.Set("Content-Type", "application/json")

	resp, err := doer.Do(req, proxyURL, accountID, accountConcurrency)
	if err != nil {
		return nil, fmt.Errorf("zcode handshake request: %w", err)
	}
	defer func() { _ = resp.Body.Close() }()
	body, err := io.ReadAll(io.LimitReader(resp.Body, 1<<20))
	if err != nil {
		return nil, fmt.Errorf("zcode handshake read body: %w", err)
	}
	if resp.StatusCode != http.StatusOK {
		return nil, fmt.Errorf("zcode handshake rejected: http %d", resp.StatusCode)
	}
	var handshakeResp struct {
		Code int `json:"code"`
		Data struct {
			PrivateCipher string `json:"privateCipher"`
		} `json:"data"`
	}
	if err := json.Unmarshal(body, &handshakeResp); err != nil {
		return nil, fmt.Errorf("zcode handshake parse body: %w", err)
	}
	if handshakeResp.Code != http.StatusOK || handshakeResp.Data.PrivateCipher == "" {
		return nil, fmt.Errorf("zcode handshake rejected: http %d code %d", resp.StatusCode, handshakeResp.Code)
	}

	cipherText, err := base64.StdEncoding.DecodeString(handshakeResp.Data.PrivateCipher)
	if err != nil {
		return nil, fmt.Errorf("zcode handshake decode privateCipher: %w", err)
	}
	if len(cipherText) <= 12+16 {
		return nil, fmt.Errorf("zcode handshake privateCipher too short: %d", len(cipherText))
	}
	aesKey, err := zcodeDerive(apiKeySecret, "ed25519_priv")
	if err != nil {
		return nil, err
	}
	block, err := aes.NewCipher(aesKey)
	if err != nil {
		return nil, fmt.Errorf("zcode handshake aes key: %w", err)
	}
	gcm, err := cipher.NewGCM(block)
	if err != nil {
		return nil, fmt.Errorf("zcode handshake gcm: %w", err)
	}
	plain, err := gcm.Open(nil, cipherText[:12], cipherText[12:], []byte(apiKeyID))
	if err != nil {
		return nil, fmt.Errorf("zcode handshake decrypt: %w", err)
	}
	der, err := base64.StdEncoding.DecodeString(string(plain))
	if err != nil {
		return nil, fmt.Errorf("zcode handshake decode private key: %w", err)
	}
	parsed, err := x509.ParsePKCS8PrivateKey(der)
	if err != nil {
		return nil, fmt.Errorf("zcode handshake parse pkcs8: %w", err)
	}
	key, ok := parsed.(ed25519.PrivateKey)
	if !ok {
		return nil, fmt.Errorf("zcode handshake private key is %T, want ed25519", parsed)
	}
	return key, nil
}

// zcodeEnsurePrivateKey 返回该凭据的签名私钥：优先取握手缓存，未命中时经
// singleflight 按 apiKeyId 去重并发握手。握手 ctx 由调用方 ctx 经
// WithoutCancel 派生并施加独立超时——握手结果进程级缓存，不应随调用方
// 请求取消或客户端断连而作废。
func zcodeEnsurePrivateKey(
	ctx context.Context,
	doer zcodeSignDoer,
	proxyURL, credential string,
	accountID int64,
	accountConcurrency int,
) (ed25519.PrivateKey, error) {
	apiKeyID, apiKeySecret, ok := zcodeParseSigningCredential(credential)
	if !ok {
		return nil, errors.New("zcode credential is not <id>.<secret>")
	}
	if cached, ok := zcodePrivateKeys.Load(apiKeyID); ok {
		return cached.(ed25519.PrivateKey), nil
	}
	hsCtx, cancel := context.WithTimeout(context.WithoutCancel(ctx), zcodeHandshakeTimeout)
	defer cancel()
	v, err, _ := zcodeHandshakeFlight.Do(apiKeyID, func() (any, error) {
		// 跟随者再次查缓存：领导者完成到本次进入之间缓存可能已写入。
		if cached, ok := zcodePrivateKeys.Load(apiKeyID); ok {
			return cached.(ed25519.PrivateKey), nil
		}
		key, err := zcodeHandshake(hsCtx, doer, proxyURL, credential, apiKeyID, apiKeySecret, accountID, accountConcurrency)
		if err != nil {
			return nil, err
		}
		zcodePrivateKeys.Store(apiKeyID, key)
		return key, nil
	})
	if err != nil {
		return nil, err
	}
	return v.(ed25519.PrivateKey), nil
}

// zcodeSolvePow 计算 ZCode PoW：SHA-256(apiKeyId\nzcode\nsessionId\nts) 的
// hex 前 32 字符作前缀，穷举 `salt12hex + counter8hex` 使
// SHA-256(prefix\ncandidate) 摘要首字节为 0。
func zcodeSolvePow(apiKeyID, ts string) (string, error) {
	seed := sha256.Sum256([]byte(apiKeyID + "\n" + zcodeSignAppID + "\n" + zcodeSessionID() + "\n" + ts))
	prefix := hex.EncodeToString(seed[:])[:32]
	salt := randomHex(12 / 2)
	for counter := 0; counter < 1<<32; counter++ {
		candidate := salt + fmt.Sprintf("%08x", counter)
		digest := sha256.Sum256([]byte(prefix + "\n" + candidate))
		if bytes.Equal(digest[:zcodePowLeadingZeroBytes], make([]byte, zcodePowLeadingZeroBytes)) {
			return candidate, nil
		}
	}
	return "", errors.New("zcode pow unsolved")
}

// applyZcodeClientSigning 为 zhipu 账号出站请求注入 ZCode V4 客户端签名头。
// 仅当出站目标为官方固定域名（open.bigmodel.cn）时签名，其余（中转/自定义
// base_url）静默跳过。任一环节失败：记 slog.Warn 并整体不设头（fail-open，
// 对齐 ZCode 桌面端语义），绝不返回 error 阻断请求。凭据取
// GetOpenAIProtocolAPIKey，与数据面 Authorization 同源。
func (s *OpenAIGatewayService) applyZcodeClientSigning(ctx context.Context, account *Account, targetURL string, header http.Header) {
	if !isZcodeSigningTarget(targetURL) {
		slog.Warn("zcode_sign_skip_non_official_target", "account_id", account.ID, "target", targetURL)
		return
	}
	credential := account.GetOpenAIProtocolAPIKey()
	apiKeyID, _, ok := zcodeParseSigningCredential(credential)
	if !ok {
		slog.Warn("zcode_sign_skip_credential", "account_id", account.ID)
		return
	}
	if s == nil || s.httpUpstream == nil {
		slog.Warn("zcode_sign_skip_no_upstream", "account_id", account.ID)
		return
	}
	proxyURL := ""
	if account.ProxyID != nil && account.Proxy != nil {
		proxyURL = account.Proxy.URL()
	}
	priv, err := zcodeEnsurePrivateKey(ctx, s.httpUpstream, proxyURL, credential, account.ID, account.Concurrency)
	if err != nil {
		slog.Warn("zcode_sign_handshake_failed", "account_id", account.ID, "error", err)
		return
	}
	ts := strconv.FormatInt(time.Now().UnixMilli(), 10)
	nonce := randomHex(zcodeNonceHexLen / 2)
	pow, err := zcodeSolvePow(apiKeyID, ts)
	if err != nil {
		slog.Warn("zcode_sign_pow_failed", "account_id", account.ID, "error", err)
		return
	}
	sigMsg := apiKeyID + "\n" + ts + "\n" + zcodeSignClientVersion + "\n" + zcodeSessionID() + "\n" + nonce
	sig := base64.StdEncoding.EncodeToString(ed25519.Sign(priv, []byte(sigMsg)))
	// 先算齐再一次性写全 7 个头，避免半套签名头被服务端误判。
	header.Set("X-Client-Ts", ts)
	header.Set("X-Client-Version", zcodeSignClientVersion)
	header.Set("X-Client-Sig", sig)
	header.Set("X-Session-Id", zcodeSessionID())
	header.Set("X-Client-Nonce", nonce)
	header.Set("X-App-Id", zcodeSignAppID)
	header.Set("X-Client-Pow", pow)
}

// zcodeVerifyFailure 判定 401 响应体是否为签名/密钥失效
// （VERIFY_SIGNATURE_INVALID / VERIFY_APIKEY_EXPIRED）。此类失败凭据仍有效，
// 可经重新握手自愈。
func zcodeVerifyFailure(responseBody []byte) bool {
	return bytes.Contains(responseBody, []byte("VERIFY_SIGNATURE_INVALID")) ||
		bytes.Contains(responseBody, []byte("VERIFY_APIKEY_EXPIRED"))
}

// zcodeInvalidateSigningKey 清除该账号凭据的握手私钥缓存，下一次请求重新握手。
func zcodeInvalidateSigningKey(account *Account) {
	if apiKeyID, _, ok := zcodeParseSigningCredential(account.GetOpenAIProtocolAPIKey()); ok {
		zcodePrivateKeys.Delete(apiKeyID)
	}
}
