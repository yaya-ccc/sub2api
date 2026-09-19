package service

import (
	"bytes"
	"context"
	"crypto/aes"
	"crypto/cipher"
	"crypto/ed25519"
	"crypto/hmac"
	"crypto/rand"
	"crypto/sha256"
	"crypto/x509"
	"encoding/base64"
	"encoding/hex"
	"encoding/json"
	"fmt"
	"io"
	"net/http"
	"net/http/httptest"
	"strings"
	"sync"
	"testing"

	"github.com/Wei-Shaw/sub2api/internal/pkg/tlsfingerprint"
	"github.com/gin-gonic/gin"
	"github.com/stretchr/testify/require"
)

// zcodeSwapHandshakeURL 将握手端点替换为测试服务器 URL，返回还原函数。
func zcodeSwapHandshakeURL(t *testing.T, url string) func() {
	t.Helper()
	orig := zcodeHandshakeURL
	zcodeHandshakeURL = url
	return func() { zcodeHandshakeURL = orig }
}

// buildZcodePrivateCipher 按握手协议正向构造 privateCipher：PKCS8 DER →
// base64 明文 → HKDF 派生 AES-GCM 加密（AAD=apiKeyID）→ base64。
func buildZcodePrivateCipher(t *testing.T, apiKeyID, apiKeySecret string, priv ed25519.PrivateKey) string {
	t.Helper()
	der, err := x509.MarshalPKCS8PrivateKey(priv)
	require.NoError(t, err)
	inner := base64.StdEncoding.EncodeToString(der)
	aesKey, err := zcodeDerive(apiKeySecret, "ed25519_priv")
	require.NoError(t, err)
	block, err := aes.NewCipher(aesKey)
	require.NoError(t, err)
	gcm, err := cipher.NewGCM(block)
	require.NoError(t, err)
	nonce := make([]byte, gcm.NonceSize())
	sealed := gcm.Seal(nil, nonce, []byte(inner), []byte(apiKeyID))
	return base64.StdEncoding.EncodeToString(append(nonce, sealed...))
}

// zcodeRoutingDoer 把握手请求转发到测试服务器（计数），其余数据面请求直接
// 返回固定 200 并捕获，避免测试触网。
type zcodeRoutingDoer struct {
	mu           sync.Mutex
	handshakes   int
	dataReqs     []*http.Request
	handshakeSrv *httptest.Server
}

func (d *zcodeRoutingDoer) Do(req *http.Request, _ string, _ int64, _ int) (*http.Response, error) {
	if req.URL.String() == zcodeHandshakeURL {
		d.mu.Lock()
		d.handshakes++
		d.mu.Unlock()
		return d.handshakeSrv.Client().Do(req)
	}
	d.mu.Lock()
	d.dataReqs = append(d.dataReqs, req)
	d.mu.Unlock()
	return &http.Response{
		StatusCode: http.StatusOK,
		Header:     http.Header{"Content-Type": []string{"application/json"}},
		Body:       io.NopCloser(strings.NewReader(`{"id":"stub","choices":[]}`)),
	}, nil
}

func (d *zcodeRoutingDoer) DoWithTLS(req *http.Request, proxyURL string, accountID int64, accountConcurrency int, _ *tlsfingerprint.Profile) (*http.Response, error) {
	return d.Do(req, proxyURL, accountID, accountConcurrency)
}

func (d *zcodeRoutingDoer) handshakeCount() int {
	d.mu.Lock()
	defer d.mu.Unlock()
	return d.handshakes
}

// zcodeHandshakeCapture 记录握手服务器收到的请求内容，供主测试协程断言。
type zcodeHandshakeCapture struct {
	mu    sync.Mutex
	reqs  []zcodeHandshakeRequestBody
	authz []string
}

type zcodeHandshakeRequestBody struct {
	APIKey string `json:"apiKey"`
	Nonce  string `json:"nonce"`
	Sig    string `json:"sig"`
	Ts     string `json:"ts"`
}

// newZcodeHandshakeServer 启动返回固定 privateCipher 的握手服务器。
func newZcodeHandshakeServer(t *testing.T, cipherB64 string) (*httptest.Server, *zcodeHandshakeCapture) {
	t.Helper()
	capture := &zcodeHandshakeCapture{}
	srv := httptest.NewServer(http.HandlerFunc(func(w http.ResponseWriter, r *http.Request) {
		var body zcodeHandshakeRequestBody
		_ = json.NewDecoder(r.Body).Decode(&body)
		capture.mu.Lock()
		capture.reqs = append(capture.reqs, body)
		capture.authz = append(capture.authz, r.Header.Get("Authorization"))
		capture.mu.Unlock()
		w.Header().Set("Content-Type", "application/json")
		_, _ = fmt.Fprintf(w, `{"code":200,"data":{"privateCipher":%q}}`, cipherB64)
	}))
	t.Cleanup(srv.Close)
	return srv, capture
}

// newZcodeSigningTestAccount 构造 zhipu APIKey 账号；zcode=true 表示
// api_protocol=zcode（签名协议档），否则为普通 chat_completions 档。
func newZcodeSigningTestAccount(id int64, credential string, zcode bool) *Account {
	protocol := APIProtocolChatCompletions
	if zcode {
		protocol = APIProtocolZcode
	}
	return &Account{
		ID:          id,
		Name:        "zhipu-zcode",
		Platform:    PlatformZhipu,
		Type:        AccountTypeAPIKey,
		Concurrency: 1,
		Credentials: map[string]any{"api_key": credential, "api_protocol": protocol},
	}
}

var zcodeHeaderKeys = []string{
	"X-Client-Ts", "X-Client-Version", "X-Client-Sig",
	"X-Session-Id", "X-Client-Nonce", "X-App-Id", "X-Client-Pow",
}

func zcodeHasNoSigningHeaders(header http.Header) bool {
	for _, key := range zcodeHeaderKeys {
		if header.Get(key) != "" {
			return false
		}
	}
	return true
}

// TestZcodeClientSigningFullChain 覆盖握手+签名头全链路：HMAC 请求形态、
// 7 头齐全、PoW 自校验、会话 id 稳定、Ed25519 签名可用公钥验签。
func TestZcodeClientSigningFullChain(t *testing.T) {

	const apiKeyID = "zctest-full-id"
	const apiKeySecret = "zctest-full-secret"
	credential := apiKeyID + "." + apiKeySecret

	pub, priv, err := ed25519.GenerateKey(rand.Reader)
	require.NoError(t, err)
	srv, capture := newZcodeHandshakeServer(t, buildZcodePrivateCipher(t, apiKeyID, apiKeySecret, priv))
	defer zcodeSwapHandshakeURL(t, srv.URL)()

	doer := &zcodeRoutingDoer{handshakeSrv: srv}
	svc := &OpenAIGatewayService{httpUpstream: doer}
	account := newZcodeSigningTestAccount(101, credential, true)

	header := http.Header{}
	svc.applyZcodeClientSigning(context.Background(), account, "https://open.bigmodel.cn/api/coding/paas/v4/chat/completions", header)

	// 握手请求形态：Authorization 为完整凭据，body 携带 apiKey/nonce/sig/ts，
	// sig 为按服务端同款 KDF 计算的 HMAC。
	require.Equal(t, 1, doer.handshakeCount())
	capture.mu.Lock()
	require.Len(t, capture.reqs, 1)
	handshakeReq := capture.reqs[0]
	handshakeAuthz := capture.authz[0]
	capture.mu.Unlock()
	require.Equal(t, credential, handshakeAuthz)
	require.Equal(t, credential, handshakeReq.APIKey)
	require.Len(t, handshakeReq.Nonce, zcodeNonceHexLen)
	require.NotEmpty(t, handshakeReq.Ts)
	hmacKey, err := zcodeDerive(apiKeySecret, "getSignKey_hmac")
	require.NoError(t, err)
	mac := hmac.New(sha256.New, hmacKey)
	_, _ = mac.Write([]byte("get_sign_key\n" + apiKeyID + "\n" + handshakeReq.Ts + "\n" + handshakeReq.Nonce))
	require.Equal(t, base64.StdEncoding.EncodeToString(mac.Sum(nil)), handshakeReq.Sig)

	// 7 个签名头齐全。
	require.Equal(t, "zcode", header.Get("X-App-Id"))
	require.Equal(t, zcodeSignClientVersion, header.Get("X-Client-Version"))
	ts := header.Get("X-Client-Ts")
	nonce := header.Get("X-Client-Nonce")
	require.NotEmpty(t, ts)
	require.Len(t, nonce, zcodeNonceHexLen)
	sessionID := header.Get("X-Session-Id")
	require.NotEmpty(t, sessionID)

	// PoW 自校验：sha256(prefix+"\n"+pow) 首字节为 0，prefix 与算法一致。
	pow := header.Get("X-Client-Pow")
	require.Len(t, pow, 12+8)
	seed := sha256.Sum256([]byte(apiKeyID + "\n" + zcodeSignAppID + "\n" + sessionID + "\n" + ts))
	prefix := hex.EncodeToString(seed[:])[:32]
	digest := sha256.Sum256([]byte(prefix + "\n" + pow))
	require.Zero(t, digest[0])

	// X-Client-Sig 可用对应公钥验签（签名消息格式拼装）。
	sigBytes, err := base64.StdEncoding.DecodeString(header.Get("X-Client-Sig"))
	require.NoError(t, err)
	sigMsg := apiKeyID + "\n" + ts + "\n" + zcodeSignClientVersion + "\n" + sessionID + "\n" + nonce
	require.True(t, ed25519.Verify(pub, []byte(sigMsg), sigBytes))

	// 第二次调用：会话 id 稳定，握手命中缓存不再请求。
	header2 := http.Header{}
	svc.applyZcodeClientSigning(context.Background(), account, "https://open.bigmodel.cn/api/coding/paas/v4/chat/completions", header2)
	require.Equal(t, sessionID, header2.Get("X-Session-Id"))
	require.NotEqual(t, header2.Get("X-Client-Nonce"), nonce)
	require.Equal(t, 1, doer.handshakeCount())
}

// TestZcodeClientSigningFailOpen 覆盖 fail-open：握手 HTTP 500、业务 code!=200、
// 凭据无点号/两个点号时均不设任何签名头且不阻断。
func TestZcodeClientSigningFailOpen(t *testing.T) {

	newService := func(t *testing.T, handler http.HandlerFunc) (*OpenAIGatewayService, *zcodeRoutingDoer) {
		srv := httptest.NewServer(handler)
		t.Cleanup(srv.Close)
		t.Cleanup(zcodeSwapHandshakeURL(t, srv.URL))
		doer := &zcodeRoutingDoer{handshakeSrv: srv}
		return &OpenAIGatewayService{httpUpstream: doer}, doer
	}

	t.Run("handshake http 500", func(t *testing.T) {
		svc, doer := newService(t, func(w http.ResponseWriter, _ *http.Request) {
			w.WriteHeader(http.StatusInternalServerError)
		})
		account := newZcodeSigningTestAccount(111, "zcfail500-id.zcfail500-secret", true)
		header := http.Header{}
		svc.applyZcodeClientSigning(context.Background(), account, "https://open.bigmodel.cn/api/coding/paas/v4/chat/completions", header)
		require.True(t, zcodeHasNoSigningHeaders(header))
		require.Equal(t, 1, doer.handshakeCount())
	})

	t.Run("handshake code not 200", func(t *testing.T) {
		svc, _ := newService(t, func(w http.ResponseWriter, _ *http.Request) {
			w.Header().Set("Content-Type", "application/json")
			_, _ = w.Write([]byte(`{"code":500,"msg":"rejected"}`))
		})
		account := newZcodeSigningTestAccount(112, "zcfailcode-id.zcfailcode-secret", true)
		header := http.Header{}
		svc.applyZcodeClientSigning(context.Background(), account, "https://open.bigmodel.cn/api/coding/paas/v4/chat/completions", header)
		require.True(t, zcodeHasNoSigningHeaders(header))
	})

	t.Run("credential without dot", func(t *testing.T) {
		svc, doer := newService(t, func(w http.ResponseWriter, _ *http.Request) {
			_, _ = w.Write([]byte(`{"code":200}`))
		})
		account := newZcodeSigningTestAccount(113, "no-dot-credential", true)
		header := http.Header{}
		svc.applyZcodeClientSigning(context.Background(), account, "https://open.bigmodel.cn/api/coding/paas/v4/chat/completions", header)
		require.True(t, zcodeHasNoSigningHeaders(header))
		require.Zero(t, doer.handshakeCount())
	})

	t.Run("credential with two dots", func(t *testing.T) {
		svc, doer := newService(t, func(w http.ResponseWriter, _ *http.Request) {
			_, _ = w.Write([]byte(`{"code":200}`))
		})
		account := newZcodeSigningTestAccount(114, "two.dot.credential", true)
		header := http.Header{}
		svc.applyZcodeClientSigning(context.Background(), account, "https://open.bigmodel.cn/api/coding/paas/v4/chat/completions", header)
		require.True(t, zcodeHasNoSigningHeaders(header))
		require.Zero(t, doer.handshakeCount())
	})
}

// TestZcodeHandshakeCacheUnderConcurrency 冷缓存下 10 个并发请求同一凭据，
// singleflight 保证仅 1 次握手。
func TestZcodeHandshakeCacheUnderConcurrency(t *testing.T) {

	const apiKeyID = "zcpow-conc-id"
	credential := apiKeyID + ".zcpow-conc-secret"
	_, priv, err := ed25519.GenerateKey(rand.Reader)
	require.NoError(t, err)
	srv, _ := newZcodeHandshakeServer(t, buildZcodePrivateCipher(t, apiKeyID, "zcpow-conc-secret", priv))
	defer zcodeSwapHandshakeURL(t, srv.URL)()

	doer := &zcodeRoutingDoer{handshakeSrv: srv}
	svc := &OpenAIGatewayService{httpUpstream: doer}
	account := newZcodeSigningTestAccount(120, credential, true)

	start := make(chan struct{})
	var wg sync.WaitGroup
	headers := make([]http.Header, 10)
	for i := 0; i < 10; i++ {
		wg.Add(1)
		go func(i int) {
			defer wg.Done()
			<-start
			h := http.Header{}
			svc.applyZcodeClientSigning(context.Background(), account, "https://open.bigmodel.cn/api/coding/paas/v4/chat/completions", h)
			headers[i] = h
		}(i)
	}
	close(start)
	wg.Wait()

	require.Equal(t, 1, doer.handshakeCount())
	for _, h := range headers {
		require.NotEmpty(t, h.Get("X-Client-Sig"), "并发请求均应携带签名头")
	}
}

// TestZcodeVerifyFailureHandling 覆盖 VERIFY_* 401 早退：清缓存返回 false；
// 非 VERIFY 401 不清缓存（nil rateLimitService 下同样返回 false，以缓存
// 是否保留区分路径）。
func TestZcodeVerifyFailureHandling(t *testing.T) {
	t.Parallel()

	const apiKeyID = "zcverify-id"
	credential := apiKeyID + ".zcverify-secret"
	_, priv, err := ed25519.GenerateKey(rand.Reader)
	require.NoError(t, err)
	zcodePrivateKeys.Store(apiKeyID, priv)
	defer zcodePrivateKeys.Delete(apiKeyID)

	svc := &OpenAIGatewayService{}
	account := newZcodeSigningTestAccount(130, credential, true)

	for _, body := range []string{
		`{"error":{"code":"VERIFY_SIGNATURE_INVALID"}}`,
		`{"error":{"code":"VERIFY_APIKEY_EXPIRED"}}`,
	} {
		got := svc.handleOpenAIAccountUpstreamError(context.Background(), account, http.StatusUnauthorized, nil, []byte(body), "glm-5.3")
		require.False(t, got, "VERIFY_* 401 应早退返回 false 保持账号可调度")
		_, cached := zcodePrivateKeys.Load(apiKeyID)
		require.False(t, cached, "VERIFY_* 401 应清除私钥缓存触发重握手")
		zcodePrivateKeys.Store(apiKeyID, priv)
	}

	// 非 VERIFY 401：走既有路径（nil rateLimitService 返回 false），缓存保留。
	zcodePrivateKeys.Store(apiKeyID, priv)
	got := svc.handleOpenAIAccountUpstreamError(context.Background(), account, http.StatusUnauthorized, nil, []byte(`{"error":"invalid api key"}`), "glm-5.3")
	require.False(t, got)
	_, cached := zcodePrivateKeys.Load(apiKeyID)
	require.True(t, cached, "非 VERIFY 401 不应清除私钥缓存")
}

// TestSendCCUpstreamRequestZcodeSigningWiring 覆盖 CC 出站组头点接线：
// zcode 协议档 + 官方端点→注入签名头；官方端点 + 普通协议档→不注入；
// zcode 协议档 + 非官方中转端点→域名守卫静默跳过。
func TestSendCCUpstreamRequestZcodeSigningWiring(t *testing.T) {

	const apiKeyID = "zcwire-cc-id"
	credential := apiKeyID + ".zcwire-cc-secret"
	_, priv, err := ed25519.GenerateKey(rand.Reader)
	require.NoError(t, err)
	srv, _ := newZcodeHandshakeServer(t, buildZcodePrivateCipher(t, apiKeyID, "zcwire-cc-secret", priv))
	defer zcodeSwapHandshakeURL(t, srv.URL)()

	doer := &zcodeRoutingDoer{handshakeSrv: srv}
	svc := &OpenAIGatewayService{httpUpstream: doer}
	body := []byte(`{"model":"glm-5.3","messages":[{"role":"user","content":"hi"}]}`)

	send := func(account *Account, targetURL string) *http.Request {
		gin.SetMode(gin.TestMode)
		rec := httptest.NewRecorder()
		c, _ := gin.CreateTestContext(rec)
		c.Request = httptest.NewRequest(http.MethodPost, "/v1/chat/completions", bytes.NewReader(body))
		resp, err := svc.sendCCUpstreamRequest(context.Background(), c, account, targetURL, body, false, credential, "", "")
		require.NoError(t, err)
		require.NotNil(t, resp)
		return doer.dataReqs[len(doer.dataReqs)-1]
	}

	zcodeAccount := newZcodeSigningTestAccount(150, credential, true)
	req := send(zcodeAccount, "https://open.bigmodel.cn/api/coding/paas/v4/chat/completions")
	require.NotEmpty(t, req.Header.Get("X-Client-Sig"), "zcode 档官方端点应携带签名头")
	require.Equal(t, "zcode", req.Header.Get("X-App-Id"))

	plainAccount := newZcodeSigningTestAccount(151, credential, false)
	reqPlain := send(plainAccount, "https://open.bigmodel.cn/api/coding/paas/v4/chat/completions")
	require.True(t, zcodeHasNoSigningHeaders(reqPlain.Header), "普通协议档不应注入签名头")

	relayAccount := newZcodeSigningTestAccount(152, credential, true)
	reqRelay := send(relayAccount, "https://relay.example.com/v1/chat/completions")
	require.True(t, zcodeHasNoSigningHeaders(reqRelay.Header), "非官方端点应被域名守卫跳过")
}

// TestZcodeParseSigningCredential 覆盖凭据解析边界。
func TestZcodeParseSigningCredential(t *testing.T) {
	t.Parallel()

	id, secret, ok := zcodeParseSigningCredential("abc.def")
	require.True(t, ok)
	require.Equal(t, "abc", id)
	require.Equal(t, "def", secret)

	for _, credential := range []string{"", "nodot", ".secret", "id.", "a.b.c", "a.b.c.d"} {
		_, _, ok := zcodeParseSigningCredential(credential)
		require.False(t, ok, "凭据 %q 不应解析成功", credential)
	}
}

// TestIsZcodeSigningEnabled 覆盖协议档守卫矩阵：仅 zhipu + APIKey +
// api_protocol=zcode 生效。
func TestIsZcodeSigningEnabled(t *testing.T) {
	t.Parallel()

	require.True(t, (&Account{
		Platform: PlatformZhipu, Type: AccountTypeAPIKey,
		Credentials: map[string]any{"api_protocol": APIProtocolZcode},
	}).IsZcodeSigningEnabled())
	require.False(t, (&Account{
		Platform: PlatformZhipu, Type: AccountTypeAPIKey,
		Credentials: map[string]any{"api_protocol": APIProtocolChatCompletions},
	}).IsZcodeSigningEnabled())
	require.False(t, (&Account{
		Platform: PlatformZhipu, Type: AccountTypeAPIKey,
	}).IsZcodeSigningEnabled())
	require.False(t, (&Account{
		Platform: PlatformZhipu, Type: AccountTypeOAuth,
		Credentials: map[string]any{"api_protocol": APIProtocolZcode},
	}).IsZcodeSigningEnabled())
	require.False(t, (&Account{
		Platform: PlatformKimi, Type: AccountTypeAPIKey,
		Credentials: map[string]any{"api_protocol": APIProtocolZcode},
	}).IsZcodeSigningEnabled())
	require.False(t, (*Account)(nil).IsZcodeSigningEnabled())
}

// TestIsZcodeSigningTarget 覆盖官方域名守卫。
func TestIsZcodeSigningTarget(t *testing.T) {
	t.Parallel()

	require.True(t, isZcodeSigningTarget("https://open.bigmodel.cn/api/coding/paas/v4/chat/completions"))
	require.True(t, isZcodeSigningTarget("https://OPEN.BIGMODEL.CN/api/paas/v4/chat/completions"))
	require.False(t, isZcodeSigningTarget("https://relay.example.com/v1/chat/completions"))
	require.False(t, isZcodeSigningTarget("https://open.bigmodel.cn.evil.com/v1/chat/completions"))
	require.False(t, isZcodeSigningTarget(""))
}
