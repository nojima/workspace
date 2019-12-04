#version 300 es

#ifdef GL_ES
precision highp float;
precision highp int;
#endif

const float PI = acos(-1.0);
const float TAU = 2.0 * PI;
const float SQRT2 = sqrt(2.0);

uniform vec2 uResolution;
uniform float uTime;

out vec4 out_FragColor;

// http://www.isthe.com/chongo/tech/comp/fnv/index.html
uint FNV_1a(uint src1, uint src2) {
    const uint offsetBias = 2166136261u;
    const uint prime = 16777619u;

    uint hash = offsetBias;
    #define FNV_ROUND(src, i) \
        hash ^= (src >> (8*i)) & 0xFFu; \
        hash *= prime;
    #define FNV_HASH_UINT(src) \
        FNV_ROUND(src, 0) \
        FNV_ROUND(src, 1) \
        FNV_ROUND(src, 2) \
        FNV_ROUND(src, 3)
    FNV_HASH_UINT(src1)
    FNV_HASH_UINT(src2)
    #undef FNV_HASH_UINT
    #undef FNV_ROUND
    return hash;
}

float hash21(vec2 st) {
    uint h = FNV_1a(floatBitsToUint(st.x), floatBitsToUint(st.y));
    return float(h) / 4294967295.0;
}

float Noise21(vec2 st) {
    float t = dot(st, vec2(12.9898, 78.233));
    return fract(sin(t) * 43758.5453123);
}

float Noise31_1(vec3 p) {
	float t = dot(p, vec3(17, 1527, 113));	
    return fract(sin(t) * 43758.5453123);
}

float Noise31_2(vec3 p) {
    float h = dot(p, vec3(1275.231,4461.7,7182.423));
    return fract(sin(h)*43758.543123);
}

/*
float ValueNoise(vec2 st) {
    vec2 i = floor(st);
    vec2 f = fract(st);

    float a = Noise21(i);
    float b = Noise21(i + vec2(1.0, 0.0));
    float c = Noise21(i + vec2(0.0, 1.0));
    float d = Noise21(i + vec2(1.0, 1.0));

    vec2 u = f * f * (3.0 - 2.0 * f);

    return mix(mix(a, b, u.x), mix(c, d, u.x), u.y);
}
*/

vec2 RandomUnitVector(vec2 st) {
    float r = TAU * Noise21(st);
    return vec2(cos(r), sin(r));
}

vec3 RandomUnitVector(vec3 p) {
    float r1 = Noise31_1(p) * 2.0;
    float r2 = Noise31_2(p) * TAU;
    float theta = acos(1.0 - r1);
    float phi = r2;
    return vec3(sin(theta) * cos(phi), sin(theta) * sin(phi), cos(theta));
}

#define DEFINE_LOCAL_DISPLACEMENT(T) \
    float LocalDisplacement(T grid, T p) { \
        T localPos = p - grid; \
        T grad = RandomUnitVector(grid); \
        return dot(grad, localPos); \
    }
DEFINE_LOCAL_DISPLACEMENT(vec2)
DEFINE_LOCAL_DISPLACEMENT(vec3)

#define DEFINE_QUINTIC_INTERPOLATION(T) \
    T QuinticInterpolation(T x) { \
        return x * x * x * (10.0 + x * (-15.0 + x * 6.0)); \
    }
DEFINE_QUINTIC_INTERPOLATION(vec2)
DEFINE_QUINTIC_INTERPOLATION(vec3)

float PerlinNoise2D(vec2 st) {
    vec2 grid0 = floor(st);
    vec2 grid1 = grid0 + 1.0;

    float v0 = LocalDisplacement(grid0, st);
    float v1 = LocalDisplacement(vec2(grid1.x, grid0.y), st);
    float v2 = LocalDisplacement(vec2(grid0.x, grid1.y), st);
    float v3 = LocalDisplacement(grid1, st);

    vec2 a = QuinticInterpolation(fract(st));

    return SQRT2 * mix(mix(v0, v1, a.x), mix(v2, v3, a.x), a.y);
}

float PerlinNoise3D(vec3 p) {
    vec3 grid0 = floor(p);
    vec3 grid1 = grid0 + 1.0;

    float v0 = LocalDisplacement(vec3(grid0.x, grid0.y, grid0.z), p);
    float v1 = LocalDisplacement(vec3(grid1.x, grid0.y, grid0.z), p);
    float v2 = LocalDisplacement(vec3(grid0.x, grid1.y, grid0.z), p);
    float v3 = LocalDisplacement(vec3(grid1.x, grid1.y, grid0.z), p);
    float v4 = LocalDisplacement(vec3(grid0.x, grid0.y, grid1.z), p);
    float v5 = LocalDisplacement(vec3(grid1.x, grid0.y, grid1.z), p);
    float v6 = LocalDisplacement(vec3(grid0.x, grid1.y, grid1.z), p);
    float v7 = LocalDisplacement(vec3(grid1.x, grid1.y, grid1.z), p);

    vec3 a = QuinticInterpolation(fract(p));
    const float SCALE = 2.0 / sqrt(3.0);

    return SCALE * mix(
        mix(mix(v0, v1, a.x), mix(v2, v3, a.x), a.y),
        mix(mix(v4, v5, a.x), mix(v6, v7, a.x), a.y),
        a.z
    );
}

vec3 LinearToSRGB(vec3 color) {
    color = clamp(color, 0.0, 1.0);
    return vec3(
        pow(color.r, 1.0/2.2),
        pow(color.g, 1.0/2.2),
        pow(color.b, 1.0/2.2)
    );
}

mat3 RotateXMatrix(float theta) {
    return mat3(cos(theta), 0.0, sin(theta),
                0.0, 1.0, 0.0,
                -sin(theta), 0.0, cos(theta));
}

void main() {
    vec2 st = (gl_FragCoord.xy * 2.0 - uResolution) / uResolution;

    //float r = PerlinNoise2D(st * 10.0) * 0.5 + 0.5;
    //vec3 p = RotateXMatrix(1.0) * vec3(st * 5.0, uTime * 1.0);
    //float r = PerlinNoise3D(p) * 0.8 + 0.6;
    float r = hash21(st * 10.0) * 0.5 + 0.5;

    vec3 albedo = vec3(1.0, 1.0, 1.0);
    vec3 srgb = LinearToSRGB(albedo * r);
    out_FragColor = vec4(srgb, 1.0);
}
