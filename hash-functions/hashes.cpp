#include <cstdio>
#include <cstdint>
#include <cmath>

uint32_t murmur_hash_11(uint32_t src) {
    const uint32_t M = 0x5bd1e995u;
    uint32_t h = 1190494759u;
    src *= M; src ^= src>>24; src *= M;
    h *= M; h ^= src;
    h ^= h>>13; h *= M; h ^= h>>15;
    return h;
}

float sine_based_hash(float src) {
    float i;
    float f = modf(sin(src * 12.9898) * 43758.5453123, &i);
    if (f < 0.0) f += 1.0;
    return f;
}

int main() {
    std::puts("hashes");
    int loop_count = 100000;
    for (int i = 0; i < loop_count; ++i) {
        union {
            float f;
            uint32_t u;
        } hash;
        hash.u = (murmur_hash_11(i) & 0x007fffffu) | 0x3f800000u;
        std::printf("%.9f\n", hash.f - 1.0);
        /*
        std::printf("%.9f\n", sine_based_hash((float)i / loop_count));
        */
    }
}
