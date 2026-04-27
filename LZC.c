#include <stdint.h>
#include <stddef.h>

// From: https://github.com/PrincetonUniversity/VST/blob/master/progs/queue.c
extern void *malloc(size_t n);
extern void free(void *p);
extern void exit(int code);
void *surely_malloc(size_t n) {
    void *p = malloc(n);
    if (!p) exit(1);
    return p;
}


// nat_to_bytes
uint64_t encode_length(uint64_t len, uint8_t *out) {
    if (len == 0) return 0;
    uint64_t idx = 0;
    while (1) {
        if (len < 128) {
            out[idx++] = (uint8_t)len;
            break;
        } else {
            out[idx++] = (uint8_t)((len % 128) + 128);
            len /= 128;
        }
    }
    return idx;
}

// bytes_to_nat
// We need to assume that in_size <= 64 / 7 = 9.
uint64_t decode_length(const uint8_t *in, uint64_t in_len, uint64_t *out) {
    if (in_len == 0) {
        *out = 0;
        return 0;
    }
    uint64_t idx = 0;
    while (idx < in_len) {
        uint8_t n = in[idx++];
        if (n < 128) {
            *out += ((uint64_t)n) << (7 * (idx - 1));
            return idx;
        } else {
            *out += ((uint64_t)(n % 128)) << (7 * (idx - 1));
        }
    }
    return idx;
}

void find_largest_match(const uint8_t *in,
                        uint64_t in_len,
                        uint64_t p,
                        uint64_t *len,
                        uint64_t *off) {
    uint8_t best_len = 0;
    uint16_t best_off = 0;
    uint64_t max_match_len = in_len - p;
    if (max_match_len > 18) max_match_len = 18;

    uint64_t start = 0;
    if (p >= 4098) start = p - 4098;

    for (uint64_t i = start; i < p; i++) {
        uint64_t match_len = 0;
        while (match_len < max_match_len && in[i + match_len] == in[p + match_len]) match_len++;
        if (3 <= match_len && best_len < match_len) {
            best_len = match_len;
            best_off = p - i;
        }
    }

    if (3 <= best_len) {
        *len = best_len;
        *off = best_off;
    } else {
        *len = 0;
        *off = 0;
    }
}

// compress_to_bytes
uint8_t *compress(const uint8_t *in, uint64_t in_len) {
    // TODO: Replace 65 with the correct value. 
    uint64_t out_len = (9 * in_len + 7) / 8 + 65;
    uint8_t *out = (uint8_t *)surely_malloc(out_len);
    uint64_t out_i = encode_length(in_len, out);
    uint64_t in_i = 0;

    uint8_t flag = 0;
    uint8_t token_count = 0;
    uint64_t flag_i = out_i;
    if (0 < in_len) out_i++;

    while (in_i < in_len) {
        uint64_t len = 0;
        uint64_t off = 0;
        find_largest_match(in, in_len, in_i, &len, &off);
        if (3 <= len) {
            flag = flag << 1;
            uint64_t len_opt = len - 3;
            uint64_t off_opt = off - 3;
            out[out_i++] = (len_opt << 4) | ((uint8_t)(off_opt >> 8));
            out[out_i++] = (uint8_t)off_opt;
            in_i += len;
        } else {
            flag = (flag << 1) | 1;
            out[out_i++] = in[in_i++];
        }

        token_count++;
        if (token_count == 8) {
            out[flag_i] = flag;
            flag = 0;
            token_count = 0;
            flag_i = out_i++;
        }
    }

    if (0 < token_count) {
        flag = flag << (8 - token_count);
        out[flag_i] = flag;
    }

    return out;
}

// decompress_from_bytes
uint8_t *decompress(const uint8_t *in, uint64_t in_len) {
    uint64_t out_len = 0;
    uint64_t in_i = decode_length(in, in_len, &out_len);
    uint64_t out_i = 0;
    uint8_t *out = (uint8_t *)surely_malloc(out_len);

    uint8_t flag = 0;
    uint8_t token_count = 0;
    uint64_t flag_i = out_i;

    while (out_i < out_len && in_i < in_len) {
        if (token_count == 0) {
            flag = in[in_i++];
            token_count = 8;
        }

        if (flag >> 7) {
            out[out_i++] = in[in_i++];
        } else {
            uint8_t b0 = in[in_i++];
            uint8_t b1 = in[in_i++];
            uint8_t len_opt = b0 >> 4;
            uint8_t off_hi = b0 & 0x0F;
            uint8_t off_lo = b1;
            uint64_t len = len_opt + 3;
            uint64_t off = (off_hi << 8) + off_lo + 3;

            for (uint64_t k = 0; k < len; k++) {
                out[out_i] = out[out_i - off];
                out_i++;
            }
        }

        flag <<= 1;
        token_count--;
    }

    return out;
}

int main(void) {
}

