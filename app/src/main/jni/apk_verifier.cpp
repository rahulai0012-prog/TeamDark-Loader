#include "apk_verifier.h"
#include <openssl/evp.h>
#include <openssl/x509.h>
#include <openssl/sha.h>
#include <openssl/crypto.h>
#include <algorithm>
#include <vector>
#include <string>
#include <cstring>
#include <cstdio>
#include <memory>
#include <cerrno>
#include <fcntl.h>
#include <unistd.h>
#include <sys/stat.h>
#include <dlfcn.h>
#include <limits.h>
#include <fstream>
#include <mutex>
#include <chrono>

namespace {
using Bytes = std::vector<unsigned char>;
uint32_t u32(const unsigned char* p) {
    return uint32_t(p[0]) | uint32_t(p[1]) << 8 | uint32_t(p[2]) << 16 | uint32_t(p[3]) << 24;
}
uint64_t u64(const unsigned char* p) { return u32(p) | uint64_t(u32(p + 4)) << 32; }
void put32(unsigned char* p, uint32_t n) { for (int i = 0; i < 4; ++i) p[i] = n >> (8 * i); }
struct Reader {
    const unsigned char* p;
    size_t n;
    bool lp(Reader& out) {
        if (n < 4) return false;
        size_t len = u32(p);
        if (len > n - 4) return false;
        out = {p + 4, len}; p += 4 + len; n -= 4 + len; return true;
    }
};
bool readAt(int fd, uint64_t offset, unsigned char* out, size_t size) {
    while (size) {
        ssize_t got = pread(fd, out, size, static_cast<off_t>(offset));
        if (got < 0 && errno == EINTR) continue;
        if (got <= 0) return false;
        offset += got; out += got; size -= got;
    }
    return true;
}
bool record(Reader list, Reader& value) {
    Reader item{};
    // Deliberately reject unsupported/multiple algorithms instead of downgrading.
    if (!list.lp(item) || list.n || item.n < 4 || u32(item.p) != 0x0103) return false;
    item.p += 4; item.n -= 4;
    return item.lp(value) && item.n == 0;
}
bool verifySigner(Reader block, const unsigned char* pin, Bytes& digest) {
    Reader signers{}, signer{}, data{}, signatures{}, key{}, digests{}, certs{}, attrs{}, cert{}, sig{}, hash{};
    if (!block.lp(signers) || block.n || !signers.lp(signer) || signers.n
            || !signer.lp(data) || !signer.lp(signatures) || !signer.lp(key) || signer.n) return false;
    Reader fields = data;
    if (!fields.lp(digests) || !fields.lp(certs) || !fields.lp(attrs)
            // Some release signers append one empty length-prefixed field.
            // Accept only this exact zero word; it is covered by the RSA signature.
            || (fields.n != 0 && (fields.n != 4 || u32(fields.p) != 0))
            || !certs.lp(cert) || cert.n == 0 || cert.n > 65536
            || !record(signatures, sig) || !record(digests, hash) || hash.n != 32) return false;
    // Validate framing of optional certificate chain and attributes too.
    Reader extra{};
    while (certs.n) if (!certs.lp(extra) || !extra.n) return false;
    while (attrs.n) if (!attrs.lp(extra) || extra.n < 4) return false;
    unsigned char certHash[32];
    SHA256(cert.p, cert.n, certHash);
    if (CRYPTO_memcmp(certHash, pin, 32)) return false;
    const unsigned char* cursor = cert.p;
    std::unique_ptr<X509, decltype(&X509_free)> x509(d2i_X509(nullptr, &cursor, cert.n), X509_free);
    if (!x509 || cursor != cert.p + cert.n) return false;
    std::unique_ptr<EVP_PKEY, decltype(&EVP_PKEY_free)> publicKey(X509_get_pubkey(x509.get()), EVP_PKEY_free);
    if (!publicKey || EVP_PKEY_base_id(publicKey.get()) != EVP_PKEY_RSA) return false;
    int keySize = i2d_PUBKEY(publicKey.get(), nullptr);
    if (keySize <= 0 || size_t(keySize) != key.n) return false;
    Bytes encodedKey(keySize);
    unsigned char* encoded = encodedKey.data();
    if (i2d_PUBKEY(publicKey.get(), &encoded) != keySize || CRYPTO_memcmp(encodedKey.data(), key.p, key.n)) return false;
    std::unique_ptr<EVP_MD_CTX, decltype(&EVP_MD_CTX_free)> ctx(EVP_MD_CTX_new(), EVP_MD_CTX_free);
    if (!ctx || EVP_DigestVerifyInit(ctx.get(), nullptr, EVP_sha256(), nullptr, publicKey.get()) != 1
            || EVP_DigestVerifyUpdate(ctx.get(), data.p, data.n) != 1
            || EVP_DigestVerifyFinal(ctx.get(), sig.p, sig.n) != 1) return false;
    digest.assign(hash.p, hash.p + hash.n);
    return true;
}
bool contentDigest(int fd, uint64_t signingStart, uint64_t cd, uint64_t eocdOffset,
                   Bytes eocd, const Bytes& expected) {
    constexpr size_t CHUNK = 1024 * 1024;
    const uint64_t lengths[] = {signingStart, eocdOffset - cd, eocd.size()};
    const uint64_t starts[] = {0, cd, 0};
    uint64_t count = 0;
    for (auto len : lengths) count += (len + CHUNK - 1) / CHUNK;
    if (count > UINT32_MAX) return false;
    unsigned char prefix[5] = {0x5a}; put32(prefix + 1, count);
    SHA256_CTX total; SHA256_Init(&total); SHA256_Update(&total, prefix, 5);
    put32(eocd.data() + 16, signingStart);
    Bytes buffer(CHUNK);
    for (int section = 0; section < 3; ++section) {
        for (uint64_t offset = 0; offset < lengths[section]; offset += CHUNK) {
            size_t size = std::min<uint64_t>(CHUNK, lengths[section] - offset);
            const unsigned char* bytes = buffer.data();
            if (section == 2) bytes = eocd.data() + offset;
            else if (!readAt(fd, starts[section] + offset, buffer.data(), size)) return false;
            unsigned char chunkHash[32];
            prefix[0] = 0xa5; put32(prefix + 1, size);
            SHA256_CTX chunk; SHA256_Init(&chunk);
            SHA256_Update(&chunk, prefix, 5); SHA256_Update(&chunk, bytes, size);
            SHA256_Final(chunkHash, &chunk); SHA256_Update(&total, chunkHash, 32);
        }
    }
    unsigned char actual[32]; SHA256_Final(actual, &total);
    return expected.size() == 32 && CRYPTO_memcmp(actual, expected.data(), 32) == 0;
}
}
namespace apk_integrity {
bool verify_fd(int fd, const unsigned char pin[32]) {
    struct stat before{}, after{};
    if (!pin || fstat(fd, &before) || !S_ISREG(before.st_mode) || before.st_size < 54
            || uint64_t(before.st_size) > UINT32_MAX) return false;
    const size_t tailSize = std::min<uint64_t>(before.st_size, 65535 + 22);
    Bytes tail(tailSize);
    if (!readAt(fd, before.st_size - tailSize, tail.data(), tailSize)) return false;
    size_t e = tailSize;
    for (size_t i = tailSize - 22;; --i) {
        if (u32(tail.data() + i) == 0x06054b50
                && i + 22 + (tail[i + 20] | unsigned(tail[i + 21]) << 8) == tailSize) { e = i; break; }
        if (!i) break;
    }
    if (e == tailSize) return false;
    Bytes eocd(tail.begin() + e, tail.end());
    // No spanning/ZIP64. Release APKs are ordinary single-disk ZIPs.
    if (u32(eocd.data() + 4) || eocd[8] != eocd[10] || eocd[9] != eocd[11]
            || (eocd[10] == 0xff && eocd[11] == 0xff)) return false;
    uint64_t eocdOffset = before.st_size - tailSize + e;
    uint64_t cd = u32(eocd.data() + 16), cdSize = u32(eocd.data() + 12);
    if (cd < 32 || cd + cdSize != eocdOffset) return false;
    unsigned char footer[24];
    if (!readAt(fd, cd - 24, footer, 24) || memcmp(footer + 8, "APK Sig Block 42", 16)) return false;
    uint64_t blockSize = u64(footer);
    if (blockSize < 24 || blockSize > 16 * 1024 * 1024 || blockSize > cd - 8) return false;
    uint64_t start = cd - blockSize - 8;
    Bytes block(blockSize + 8);
    if (!readAt(fd, start, block.data(), block.size()) || u64(block.data()) != blockSize) return false;
    Reader v2{}; bool found = false;
    for (size_t offset = 8; offset < block.size() - 24;) {
        size_t remaining = block.size() - 24 - offset;
        if (remaining < 12) return false;
        uint64_t size = u64(block.data() + offset);
        if (size < 4 || size > remaining - 8) return false;
        if (u32(block.data() + offset + 8) == 0x7109871a) {
            if (found) return false;
            found = true; v2 = {block.data() + offset + 12, size_t(size - 4)};
        }
        offset += 8 + size;
    }
    Bytes digest;
    if (!found || !verifySigner(v2, pin, digest) || !contentDigest(fd, start, cd, eocdOffset, eocd, digest)) return false;
    return fstat(fd, &after) == 0 && before.st_dev == after.st_dev && before.st_ino == after.st_ino
            && before.st_size == after.st_size && before.st_mtime == after.st_mtime
            && before.st_ctime == after.st_ctime;
}

bool verify_installed(const char* reported_apk) {
    // Derive base.apk from this loaded native library, never from a caller/Java
    // sourceDir that a signature-spoofing wrapper can redirect to an embedded APK.
    // This release uses extracted libraries (useLegacyPackaging=true).
    Dl_info info{}; char resolved[PATH_MAX];
    if (!dladdr(reinterpret_cast<void*>(&verify_installed), &info) || !info.dli_fname
            || !realpath(info.dli_fname, resolved)) return false;
    std::string library(resolved);
    const auto lib = library.rfind("/lib/");
    if (library.compare(0, 10, "/data/app/") != 0 || lib == std::string::npos
            || library.substr(library.find_last_of('/') + 1) != "libTeamDarkLoader.so") return false;
    std::string path = library.substr(0, lib) + "/base.apk";
    char reported[PATH_MAX];
    if (!reported_apk || !realpath(reported_apk, reported) || path != reported) return false;
    int fd = open(path.c_str(), O_RDONLY | O_CLOEXEC | O_NOFOLLOW);
    if (fd < 0) return false;
    struct stat st{};
    bool trusted = fstat(fd, &st) == 0 && (st.st_uid == 1000 || st.st_uid == 0) && !(st.st_mode & 0022);
    static const unsigned char pin[32] = {
        0x95,0xd4,0x22,0x74,0x43,0x0c,0x19,0x8e,0x20,0x05,0x6d,0xa0,0x0e,0x5e,0x4d,0xca,
        0xfd,0x59,0x35,0xd9,0x3d,0x2e,0x43,0x80,0xe2,0x78,0x8b,0x1b,0x7f,0xf8,0xa3,0x2f
    };
    // Require our verified APK to be mapped. Other installed APKs can belong to
    // legitimate shared resources/WebView; their presence is not tamper evidence.
    // The ApplicationInfo path above must still match this library's installation.
    std::ifstream maps("/proc/self/maps");
    bool sawBase = false;
    std::string line;
    if (!maps.is_open()) trusted = false;
    while (trusted && std::getline(maps, line)) {
        auto pos = line.find("/data/app/");
        if (pos == std::string::npos) continue;
        std::string mapped = line.substr(pos);
        if (mapped.find(".apk") == std::string::npos) continue;
        if (mapped == path + " (deleted)") { trusted = false; break; }
        if (mapped == path) sawBase = true;
    }
    trusted = trusted && sawBase && !maps.bad();
    // The runtime guard calls every three seconds. Bound repeat hashing to once
    // a minute, but invalidate immediately on inode/size/nanosecond timestamp changes.
    static std::mutex mutex;
    static struct stat cached{};
    static std::chrono::steady_clock::time_point checked{};
    static bool accepted = false;
    std::lock_guard<std::mutex> lock(mutex);
    auto now = std::chrono::steady_clock::now();
    bool same = accepted && cached.st_dev == st.st_dev && cached.st_ino == st.st_ino
            && cached.st_size == st.st_size
            && cached.st_mtim.tv_sec == st.st_mtim.tv_sec && cached.st_mtim.tv_nsec == st.st_mtim.tv_nsec
            && cached.st_ctim.tv_sec == st.st_ctim.tv_sec && cached.st_ctim.tv_nsec == st.st_ctim.tv_nsec
            && now - checked < std::chrono::seconds(60);
    bool ok = trusted && (same || verify_fd(fd, pin));
    if (ok && !same) { cached = st; checked = now; }
    accepted = ok;
    close(fd);
    return ok;
}
}
