// Copyright 2025 Google LLC
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

package zk

import (
	"crypto/ecdsa"
	"crypto/elliptic"
	"crypto/rand"
	"crypto/x509"
	"crypto/x509/pkix"
	"encoding/pem"
	"math/big"
	"os"
	"strings"
	"testing"
	"time"

	"github.com/fxamacker/cbor/v2"
)

func TestLoadIssuerRootCA(t *testing.T) {
	ca, _, err := generateTestCA()
	if err != nil {
		t.Fatalf("failed to generate test CA: %v", err)
	}

	pemBlock := &pem.Block{
		Type:  "CERTIFICATE",
		Bytes: ca.Raw,
	}
	pemBytes := pem.EncodeToMemory(pemBlock)

	if err := LoadIssuerRootCA(pemBytes); err != nil {
		t.Errorf("LoadIssuerRootCA() error = %v, wantErr %v", err, false)
	}

	if len(IssuerRoots.Subjects()) == 0 {
		t.Error("IssuerRoots should not be empty after loading a CA")
	}
}

func TestBundledIssuerRootsAreSynthetic(t *testing.T) {
	pemBytes, err := os.ReadFile("../certs.pem")
	if err != nil {
		t.Fatalf("failed to read bundled certs.pem: %v", err)
	}

	IssuerRoots = x509.NewCertPool()
	if err := LoadIssuerRootCA(pemBytes); err != nil {
		t.Fatalf("LoadIssuerRootCA() bundled synthetic roots error = %v", err)
	}

	count := 0
	for len(pemBytes) > 0 {
		block, rest := pem.Decode(pemBytes)
		if block == nil {
			break
		}
		pemBytes = rest
		if block.Type != "CERTIFICATE" {
			continue
		}
		cert, err := x509.ParseCertificate(block.Bytes)
		if err != nil {
			t.Fatalf("bundled cert %d failed to parse: %v", count+1, err)
		}
		count++
		if !cert.IsCA {
			t.Errorf("bundled cert %d is not a CA", count)
		}
		if got := cert.Subject.Country; len(got) != 1 || got[0] != "ZZ" {
			t.Errorf("bundled cert %d Country = %v, want [ZZ] synthetic marker", count, got)
		}
		if got := cert.Subject.Organization; len(got) != 1 || got[0] != "Longfellow ZK Synthetic Trust" {
			t.Errorf("bundled cert %d Organization = %v, want synthetic trust marker", count, got)
		}
		if !strings.Contains(cert.Subject.CommonName, "Synthetic") {
			t.Errorf("bundled cert %d CommonName = %q, want Synthetic marker", count, cert.Subject.CommonName)
		}
	}

	if count != 3 {
		t.Fatalf("bundled cert count = %d, want 3 synthetic issuer roots", count)
	}
	if got := len(IssuerRoots.Subjects()); got != count {
		t.Fatalf("IssuerRoots subjects = %d, want %d", got, count)
	}
}

func TestValidateIssuerKey(t *testing.T) {
	ca, _, err := generateTestCA()
	if err != nil {
		t.Fatalf("failed to generate test CA: %v", err)
	}
	pemBlock := &pem.Block{
		Type:  "CERTIFICATE",
		Bytes: ca.Raw,
	}
	pemBytes := pem.EncodeToMemory(pemBlock)
	if err := LoadIssuerRootCA(pemBytes); err != nil {
		t.Fatalf("failed to load issuer root CA: %v", err)
	}

	doc, err := createTestZkDocument()
	if err != nil {
		t.Fatalf("failed to create test zk document: %v", err)
	}

	x509b, _ := doc.MsoX5chain.Unprotected[X5ChainIndex]
	_, _, err = validateIssuerKey(x509b)
	if err != nil {
		t.Errorf("validateIssuerKey() error = %v, wantErr %v", err, false)
	}
}

func TestProcessDeviceResponseISO(t *testing.T) {
	IssuerRoots = x509.NewCertPool()
	caCert, caKey, err := generateTestCA()
	if err != nil {
		t.Fatalf("failed to generate test CA: %v", err)
	}
	pemBlock := &pem.Block{
		Type:  "CERTIFICATE",
		Bytes: caCert.Raw,
	}
	pemBytes := pem.EncodeToMemory(pemBlock)
	if err := LoadIssuerRootCA(pemBytes); err != nil {
		t.Fatalf("failed to load issuer root CA: %v", err)
	}

	leafCert, _, err := createLeafCert(caCert, caKey)
	if err != nil {
		t.Fatalf("failed to create leaf cert: %v", err)
	}

	issuerSigned := IssuerSigned{
		"test_namespace": []zkSignedItem{
			{
				ElementIdentifier: "test_identifier",
				ElementValue:      cbor.RawMessage([]byte{0x81, 0x45, 0x68, 0x65, 0x6c, 0x6c, 0x6f}), // ["hello"]
			},
		},
	}

	t.Run("single cert", func(t *testing.T) {
		docData := &zkDocumentDataIso{
			DocType:      "test_doctype",
			ZkSystemId:   "0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef",
			IssuerSigned: issuerSigned,
			MsoX5chain:   leafCert.Raw,
			Timestamp:    "2025-01-01T00:00:00Z",
		}
		docDataBytes, err := cbor.Marshal(docData)
		if err != nil {
			t.Fatalf("failed to marshal doc data: %v", err)
		}
		zkDoc := zkDocumentIso{
			DocumentData: docDataBytes,
			Proof:        []byte("test_proof"),
		}
		resp := &zkDeviceResponseIso{
			Version:     "1.0",
			ZKDocuments: []zkDocumentIso{zkDoc},
			Status:      0,
		}
		respBytes, err := cbor.Marshal(resp)
		if err != nil {
			t.Fatalf("failed to marshal response: %v", err)
		}

		if _, err := ProcessDeviceResponseISO(respBytes); err != nil {
			t.Errorf("ProcessDeviceResponseISO() with single cert error = %v, wantErr %v", err, false)
		}
	})

	t.Run("array of certs", func(t *testing.T) {
		docData := &zkDocumentDataIso{
			DocType:      "test_doctype",
			ZkSystemId:   "0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef",
			IssuerSigned: issuerSigned,
			MsoX5chain:   [][]byte{leafCert.Raw},
			Timestamp:    "2025-01-01T00:00:00Z",
		}
		docDataBytes, err := cbor.Marshal(docData)
		if err != nil {
			t.Fatalf("failed to marshal doc data: %v", err)
		}
		zkDoc := zkDocumentIso{
			DocumentData: docDataBytes,
			Proof:        []byte("test_proof"),
		}
		resp := &zkDeviceResponseIso{
			Version:     "1.0",
			ZKDocuments: []zkDocumentIso{zkDoc},
			Status:      0,
		}
		respBytes, err := cbor.Marshal(resp)
		if err != nil {
			t.Fatalf("failed to marshal response: %v", err)
		}

		if _, err := ProcessDeviceResponseISO(respBytes); err != nil {
			t.Errorf("ProcessDeviceResponseISO() with array of certs error = %v, wantErr %v", err, false)
		}
	})
}

func generateTestCA() (*x509.Certificate, *ecdsa.PrivateKey, error) {
	priv, err := ecdsa.GenerateKey(elliptic.P256(), rand.Reader)
	if err != nil {
		return nil, nil, err
	}

	template := x509.Certificate{
		SerialNumber: big.NewInt(1),
		Subject: pkix.Name{
			Organization: []string{"Test CA"},
		},
		NotBefore:             time.Now(),
		NotAfter:              time.Now().Add(time.Hour),
		KeyUsage:              x509.KeyUsageCertSign,
		ExtKeyUsage:           []x509.ExtKeyUsage{x509.ExtKeyUsageServerAuth},
		BasicConstraintsValid: true,
		IsCA:                  true,
	}

	derBytes, err := x509.CreateCertificate(rand.Reader, &template, &template, &priv.PublicKey, priv)
	if err != nil {
		return nil, nil, err
	}

	cert, err := x509.ParseCertificate(derBytes)
	if err != nil {
		return nil, nil, err
	}

	return cert, priv, nil
}

func createLeafCert(caCert *x509.Certificate, caKey *ecdsa.PrivateKey) (*x509.Certificate, *ecdsa.PrivateKey, error) {
	priv, err := ecdsa.GenerateKey(elliptic.P256(), rand.Reader)
	if err != nil {
		return nil, nil, err
	}

	template := x509.Certificate{
		SerialNumber: big.NewInt(2),
		Subject: pkix.Name{
			Organization: []string{"Test Cert"},
		},
		NotBefore: time.Now(),
		NotAfter:  time.Now().Add(time.Hour),
		KeyUsage:  x509.KeyUsageDigitalSignature,
	}

	derBytes, err := x509.CreateCertificate(rand.Reader, &template, caCert, &priv.PublicKey, caKey)
	if err != nil {
		return nil, nil, err
	}

	cert, err := x509.ParseCertificate(derBytes)
	if err != nil {
		return nil, nil, err
	}
	return cert, priv, nil
}

func createTestZkDocument() (*zkDocument, error) {
	caCert, caKey, err := generateTestCA()
	if err != nil {
		return nil, err
	}

	pemBlock := &pem.Block{
		Type:  "CERTIFICATE",
		Bytes: caCert.Raw,
	}
	pemBytes := pem.EncodeToMemory(pemBlock)
	if err := LoadIssuerRootCA(pemBytes); err != nil {
		return nil, err
	}

	priv, err := ecdsa.GenerateKey(elliptic.P256(), rand.Reader)
	if err != nil {
		return nil, err
	}

	template := x509.Certificate{
		SerialNumber: big.NewInt(2),
		Subject: pkix.Name{
			Organization: []string{"Test Cert"},
		},
		NotBefore: time.Now(),
		NotAfter:  time.Now().Add(time.Hour),
		KeyUsage:  x509.KeyUsageDigitalSignature,
	}

	derBytes, err := x509.CreateCertificate(rand.Reader, &template, caCert, &priv.PublicKey, caKey)
	if err != nil {
		return nil, err
	}

	cert, err := x509.ParseCertificate(derBytes)
	if err != nil {
		return nil, err
	}

	return &zkDocument{
		DocType: "test_doctype",
		ZKSystemType: zkSpec{
			System: LONGFELLOW_V1,
			Params: zkParam{
				Version:       1,
				CircuitHash:   "0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef",
				NumAttributes: 1,
			},
		},
		IssuerSigned: IssuerSigned{
			"test_namespace": []zkSignedItem{
				{
					ElementIdentifier: "test_identifier",
					ElementValue:      cbor.RawMessage([]byte{0x81, 0x45, 0x68, 0x65, 0x6c, 0x6c, 0x6f}), // ["hello"]
				},
			},
		},
		MsoX5chain: chainCoseSign1{
			Unprotected: map[int][]byte{
				X5ChainIndex: cert.Raw,
			},
		},
		Timestamp: "2025-01-01T00:00:00Z",
		Proof:     []byte("test_proof"),
	}, nil
}
