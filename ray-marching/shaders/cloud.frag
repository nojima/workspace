#version 300 es

#ifdef GL_ES
precision highp float;
precision highp int;
#endif

const float PI = acos(-1.0);

uniform vec2 uResolution;
uniform float uTime;

out vec4 out_FragColor;

//-- hash functions -----------------------------------------------------------

uint murmurHash13(uvec3 src) {
    const uint M = 0x5bd1e995u;
    uint h = 1190494759u;
    src *= M; src ^= src>>24u; src *= M;
    h *= M; h ^= src.x; h *= M; h ^= src.y; h *= M; h ^= src.z;
    h ^= h>>13u; h *= M; h ^= h>>15u;
    return h;
}

// 1 output, 3 inputs
float hash13(vec3 src) {
    uint h = murmurHash13(floatBitsToUint(src));
    return uintBitsToFloat(h & 0x007fffffu | 0x3f800000u) - 1.0;
}

//-- noise --------------------------------------------------------------------

float valueNoise(vec3 src) {
    vec3 i = floor(src);
    vec3 f = fract(src);

    float v1 = hash13(i + vec3(0.0, 0.0, 0.0));
    float v2 = hash13(i + vec3(1.0, 0.0, 0.0));
    float v3 = hash13(i + vec3(0.0, 1.0, 0.0));
    float v4 = hash13(i + vec3(1.0, 1.0, 0.0));
    float v5 = hash13(i + vec3(0.0, 0.0, 1.0));
    float v6 = hash13(i + vec3(1.0, 0.0, 1.0));
    float v7 = hash13(i + vec3(0.0, 1.0, 1.0));
    float v8 = hash13(i + vec3(1.0, 1.0, 1.0));

    vec3 a = f * f * f * (10.0 + f * (-15.0 + f * 6.0));

    return 2.0 * mix(
        mix(mix(v1, v2, a.x), mix(v3, v4, a.x), a.y),
        mix(mix(v5, v6, a.x), mix(v7, v8, a.x), a.y),
        a.z
    ) - 1.0;
}

float fbm(vec3 src) {
    const int NUM_OCTAVES = 5;
    float f = 0.25;
    float a = 1.0;
    float ret = 0.0;
    for (int i = 0; i < NUM_OCTAVES; ++i) {
        ret += a * valueNoise(f * src);
        f *= 2.0;
        a *= 0.5;
    }
    const float s = (1.0 - pow(0.5, float(NUM_OCTAVES))) * 2.0;
    return ret / s;
}

//-- color space --------------------------------------------------------------

vec3 sRGB(vec3 linearColor) {
    linearColor = clamp(linearColor, 0.0, 1.0);
    return pow(linearColor, vec3(1.0) / 2.2);
}

//-- main ---------------------------------------------------------------------

vec3 render(vec2 coord) {
    const float k1 = 2.0;
    const float k2 = 4.0;
    vec3 p = vec3(coord * 10.0, uTime);

    vec3 q = vec3(
        fbm(p),
        fbm(p + vec3(5.2, 1.3, 7.9)),
        fbm(p + vec3(3.9, 5.9, 2.4))
    );

    vec3 r = vec3(
        fbm(p + k1*q),
        fbm(p + k1*q + vec3(1.5, 9.1, 6.1)),
        fbm(p + k1*q + vec3(8.1, 2.2, 3.1))
    );

    float v = fbm(p + k2*r);

    vec3 color0 = vec3(0.2, 0.9, 0.8);
    vec3 color1 = vec3(0.1, 0.3, 0.3);
    vec3 color2 = vec3(0.0, 0.4, 0.1);
    vec3 color3 = vec3(0.7, 0.0, 0.1);
    vec3 c1 = mix(color0, color1, v * 0.5 + 0.5);
    vec3 c2 = mix(c1, color2, q * 0.5 + 0.5);
    vec3 c3 = mix(c2, color3, r * 0.5 + 0.5);

    return c3;
}

void main() {
    vec2 coord = (gl_FragCoord.xy / min(uResolution.x, uResolution.y)) * 2.0 - 1.0;
    vec3 linearColor = render(coord);
    out_FragColor = vec4(sRGB(linearColor), 1.0);   
}
