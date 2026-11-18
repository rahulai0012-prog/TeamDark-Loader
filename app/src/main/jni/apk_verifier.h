#pragma once
#include <cstdint>
namespace apk_integrity {
// Strict release profile: one v2 signer, RSA PKCS#1 SHA-256, no split APKs.
bool verify_fd(int fd, const unsigned char expected_certificate[32]);
bool verify_installed(const char* reported_apk);
}
