//#include <cstdint>
#include <stdint.h>

// encrypts a 64-bit block (stored in an array of two 32-bit values)
// using a 128-bit key (stored in an array of four 32-bit values).
void tea_encrypt(uint32_t v[2], const uint32_t key[4]) {
    uint32_t v0 = v[0], v1 = v[1];
    uint32_t k0 = key[0], k1 = key[1], k2 = key[2], k3 = key[3];
    uint32_t sum = 0;
    const uint32_t delta = 0x9e3779b9;
    for (unsigned int i = 0; i < 32; i++) {
        sum += delta;
        v0 += ((v1 << 4) + k0) ^ (v1 + sum) ^ ((v1 >> 5) + k1);
        v1 += ((v0 << 4) + k2) ^ (v0 + sum) ^ ((v0 >> 5) + k3);
    }
    v[0] = v0;
    v[1] = v1;
}

