#include <stdint.h>
#include <string.h>
#include <stdlib.h>
#include <stdio.h>
#include <errno.h>

static inline uint32_t rotr(uint32_t x, unsigned n) {
    return (x >> n) | (x << (32 - n));
}

static inline uint32_t ch(uint32_t x, uint32_t y, uint32_t z) {
    return (x & y) ^ (~x & z);
}

static inline uint32_t maj(uint32_t x, uint32_t y, uint32_t z) {
    return (x & y) ^ (x & z) ^ (y & z);
}

static inline uint32_t Sigma0(uint32_t x) { return rotr(x, 2) ^ rotr(x, 13) ^ rotr(x, 22); }
static inline uint32_t Sigma1(uint32_t x) { return rotr(x, 6) ^ rotr(x, 11) ^ rotr(x, 25); }
static inline uint32_t sigma0(uint32_t x) { return rotr(x, 7) ^ rotr(x, 18) ^ (x >> 3); }
static inline uint32_t sigma1(uint32_t x) { return rotr(x, 17) ^ rotr(x, 19) ^ (x >> 10); }


static inline uint32_t load_be32(const uint8_t *p) {
    return ((uint32_t)p[0] << 24) | ((uint32_t)p[1] << 16) | ((uint32_t)p[2] << 8) | ((uint32_t)p[3]);
}

static inline void store_be32(uint8_t *p, uint32_t v) {
    p[0] = (uint8_t)((v >> 24) & 0xFF);
    p[1] = (uint8_t)((v >> 16) & 0xFF);
    p[2] = (uint8_t)((v >> 8) & 0xFF);
    p[3] = (uint8_t)(v & 0xFF);
}

static inline void store_be64(uint8_t *p, uint64_t v) {
    p[0] = (uint8_t)((v >> 56) & 0xFF);
    p[1] = (uint8_t)((v >> 48) & 0xFF);
    p[2] = (uint8_t)((v >> 40) & 0xFF);
    p[3] = (uint8_t)((v >> 32) & 0xFF);
    p[4] = (uint8_t)((v >> 24) & 0xFF);
    p[5] = (uint8_t)((v >> 16) & 0xFF);
    p[6] = (uint8_t)((v >> 8) & 0xFF);
    p[7] = (uint8_t)(v & 0xFF);
}


typedef struct {
    uint32_t h[8];
    uint8_t buf[64];
    size_t buf_len;      
    uint64_t bit_len;    
} sha256_ctx;

static void sha256_init(sha256_ctx *ctx) {
    ctx->h[0] = 0x6a09e667;
    ctx->h[1] = 0xbb67ae85;
    ctx->h[2] = 0x3c6ef372;
    ctx->h[3] = 0xa54ff53a;
    ctx->h[4] = 0x510e527f;
    ctx->h[5] = 0x9b05688c;
    ctx->h[6] = 0x1f83d9ab;
    ctx->h[7] = 0x5be0cd19;
    ctx->buf_len = 0;
    ctx->bit_len = 0;
}

static void sha256_compress(sha256_ctx *ctx, const uint8_t chunk[64]) {
    static const uint32_t k[64] = {
        0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5, 0x3956c25b, 0x59f111f1, 0x923f82a4, 0xab1c5ed5,
        0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3, 0x72be5d74, 0x80deb1fe, 0x9bdc06a7, 0xc19bf174,
        0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc, 0x2de92c6f, 0x4a7484aa, 0x5cb0a9dc, 0x76f988da,
        0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7, 0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967,
        0x27b70a85, 0x2e1b2138, 0x4d2c6dfc, 0x53380d13, 0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85,
        0xa2bfe8a1, 0xa81a664b, 0xc24b8b70, 0xc76c51a3, 0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070,
        0x19a4c116, 0x1e376c08, 0x2748774c, 0x34b0bcb5, 0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3,
        0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208, 0x90befffa, 0xa4506ceb, 0xbef9a3f7, 0xc67178f2
    };
    uint32_t w[64];
    for (int t = 0; t < 16; t++) w[t] = load_be32(chunk + t*4);
    for (int t = 16; t < 64; t++) w[t] = sigma1(w[t-2]) + w[t-7] + sigma0(w[t-15]) + w[t-16];

    uint32_t a = ctx->h[0];
    uint32_t b = ctx->h[1];
    uint32_t c = ctx->h[2];
    uint32_t d = ctx->h[3];
    uint32_t e = ctx->h[4];
    uint32_t f = ctx->h[5];
    uint32_t g = ctx->h[6];
    uint32_t hh = ctx->h[7];

    for (int t = 0; t < 64; t++) {
        uint32_t T1 = hh + Sigma1(e) + ch(e, f, g) + k[t] + w[t];
        uint32_t T2 = Sigma0(a) + maj(a, b, c);
        hh = g; g = f; f = e; e = d + T1; d = c; c = b; b = a; a = T1 + T2;
    }

    ctx->h[0] += a; ctx->h[1] += b; ctx->h[2] += c; ctx->h[3] += d;
    ctx->h[4] += e; ctx->h[5] += f; ctx->h[6] += g; ctx->h[7] += hh;
}

static void sha256_update(sha256_ctx *ctx, const uint8_t *data, size_t len) {
    ctx->bit_len += (uint64_t)len * 8ULL;
    size_t pos = 0;
    if (ctx->buf_len > 0) {
        size_t need = 64 - ctx->buf_len;
        if (len < need) {
            memcpy(ctx->buf + ctx->buf_len, data, len);
            ctx->buf_len += len;
            return;
        }
        memcpy(ctx->buf + ctx->buf_len, data, need);
        sha256_compress(ctx, ctx->buf);
        pos += need;
        ctx->buf_len = 0;
    }
    while (pos + 64 <= len) {
        sha256_compress(ctx, data + pos);
        pos += 64;
    }
    if (pos < len) {
        ctx->buf_len = len - pos;
        memcpy(ctx->buf, data + pos, ctx->buf_len);
    }
}

static void sha256_final(sha256_ctx *ctx, uint8_t out[32]) {
    
    size_t i = ctx->buf_len;
    ctx->buf[i++] = 0x80;
    if (i > 56) {
        while (i < 64) ctx->buf[i++] = 0;
        sha256_compress(ctx, ctx->buf);
        i = 0;
    }
    while (i < 56) ctx->buf[i++] = 0;
    store_be64(ctx->buf + 56, ctx->bit_len);
    sha256_compress(ctx, ctx->buf);
    for (int j = 0; j < 8; j++) store_be32(out + j*4, ctx->h[j]);
}

uint8_t *sha256_digest_alloc(const uint8_t *data, size_t len) {
    uint8_t *d = malloc(32);
    if (!d) return NULL;
    sha256_ctx ctx;
    sha256_init(&ctx);
    sha256_update(&ctx, data, len);
    sha256_final(&ctx, d);
    return d;
}

char *sha256_hex(const uint8_t *data, size_t len) {
    uint8_t *d = sha256_digest_alloc(data, len);
    if (!d) return NULL;
    char *s = malloc(64 + 1);
    if (!s) { free(d); return NULL; }
    static const char *hex = "0123456789abcdef";
    for (int i = 0; i < 32; i++) {
        s[i*2] = hex[(d[i] >> 4) & 0xF];
        s[i*2 + 1] = hex[d[i] & 0xF];
    }
    s[64] = '\0';
    free(d);
    return s;
}

static void print_hex(const uint8_t *d, size_t n) {
    static const char *hex = "0123456789abcdef";
    for (size_t i = 0; i < n; i++) {
        putchar(hex[(d[i] >> 4) & 0xF]);
        putchar(hex[d[i] & 0xF]);
    }
}

static uint8_t *read_stream_all(FILE *f, size_t *out_len) {
    const size_t chunk = 1 << 16; /* 64KB */
    uint8_t *buf = NULL;
    size_t cap = 0, len = 0;
    while (1) {
        if (len + chunk + 1 > cap) {
            size_t newcap = cap ? cap * 2 : chunk;
            uint8_t *nb = realloc(buf, newcap);
            if (!nb) { free(buf); return NULL; }
            buf = nb; cap = newcap;
        }
        size_t r = fread(buf + len, 1, chunk, f);
        len += r;
        if (r < chunk) {
            if (feof(f)) break;
            if (ferror(f)) { free(buf); return NULL; }
        }
    }
    *out_len = len;
    return buf;
}

int main(int argc, char *argv[]) {
    
    if (argc == 1) {
        size_t len; uint8_t *data = read_stream_all(stdin, &len);
        if (!data && ferror(stdin)) { fprintf(stderr, "read error\n"); return 1; }
        char *hex = sha256_hex(data, len);
        if (!hex) { free(data); fprintf(stderr, "compute failed\n"); return 1; }
        printf("%s  -\n", hex);
        free(hex); free(data);
        return 0;
    }

    for (int i = 1; i < argc; i++) {
        const char *fn = argv[i];
        FILE *f = fopen(fn, "rb");
        if (!f) { fprintf(stderr, "%s: %s\n", fn, strerror(errno)); continue; }
        size_t len; uint8_t *data = read_stream_all(f, &len);
        fclose(f);
        if (!data) { fprintf(stderr, "%s: read failed\n", fn); continue; }
        char *hex = sha256_hex(data, len);
        if (!hex) { fprintf(stderr, "%s: compute failed\n", fn); free(data); continue; }
        printf("%s  %s\n", hex, fn);
        free(hex); free(data);
    }
    return 0;
}