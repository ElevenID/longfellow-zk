package zk

import (
	"crypto/ecdsa"
	"crypto/elliptic"
	"crypto/rand"
	"crypto/x509"
	"crypto/x509/pkix"
	"math/big"
	"net/http"
	"net/http/httptest"
	"testing"
	"time"

	"github.com/fxamacker/cbor/v2"
)

func TestLoadVICAL(t *testing.T) {
	IssuerRoots = x509.NewCertPool()
	cborData := syntheticVICAL(t)

	ts := httptest.NewServer(http.HandlerFunc(func(w http.ResponseWriter, r *http.Request) {
		w.Header().Set("Content-Type", "application/cbor")
		w.Write(cborData)
	}))
	defer ts.Close()

	initialCount := len(IssuerRoots.Subjects())

	if err := LoadVICAL(ts.URL); err != nil {
		t.Fatalf("LoadVICAL failed: %v", err)
	}

	finalCount := len(IssuerRoots.Subjects())
	if got, want := finalCount-initialCount, 2; got != want {
		t.Errorf("LoadVICAL loaded %d certificates, want %d", got, want)
	}
}

func syntheticVICAL(t *testing.T) []byte {
	t.Helper()
	rootA := syntheticVICALRoot(t, 1001, "Longfellow Synthetic VICAL Root A")
	rootB := syntheticVICALRoot(t, 1002, "Longfellow Synthetic VICAL Root B")

	nestedCBOR, err := cbor.Marshal([]any{
		[]byte("ignored non-certificate payload"),
		rootB.Raw,
	})
	if err != nil {
		t.Fatalf("failed to marshal nested synthetic VICAL payload: %v", err)
	}

	data, err := cbor.Marshal([]any{
		map[string]any{
			"fixture":      "synthetic-vical",
			"certificates": []any{rootA.Raw, nestedCBOR},
		},
	})
	if err != nil {
		t.Fatalf("failed to marshal synthetic VICAL: %v", err)
	}
	return data
}

func syntheticVICALRoot(t *testing.T, serial int64, commonName string) *x509.Certificate {
	t.Helper()
	priv, err := ecdsa.GenerateKey(elliptic.P256(), rand.Reader)
	if err != nil {
		t.Fatalf("failed to generate synthetic VICAL root key: %v", err)
	}

	template := x509.Certificate{
		SerialNumber: big.NewInt(serial),
		Subject: pkix.Name{
			Country:            []string{"ZZ"},
			Organization:       []string{"Longfellow ZK Synthetic Trust"},
			OrganizationalUnit: []string{"Reference Verifier Tests"},
			CommonName:         commonName,
		},
		NotBefore:             time.Date(2026, 1, 1, 0, 0, 0, 0, time.UTC),
		NotAfter:              time.Date(2036, 1, 1, 0, 0, 0, 0, time.UTC),
		KeyUsage:              x509.KeyUsageCertSign | x509.KeyUsageCRLSign,
		BasicConstraintsValid: true,
		IsCA:                  true,
	}

	der, err := x509.CreateCertificate(rand.Reader, &template, &template, &priv.PublicKey, priv)
	if err != nil {
		t.Fatalf("failed to create synthetic VICAL root: %v", err)
	}
	cert, err := x509.ParseCertificate(der)
	if err != nil {
		t.Fatalf("failed to parse synthetic VICAL root: %v", err)
	}
	return cert
}
