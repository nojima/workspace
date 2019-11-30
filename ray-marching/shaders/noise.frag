#ifdef GL_ES
precision highp float;
#endif

const float PI = acos(-1.0);
const float TAU = 2.0 * PI;
const float SQRT2 = sqrt(2.0);

uniform vec2 uResolution;
uniform float uTime;

float Noise21(vec2 st) {
    return fract(sin(dot(st.xy, vec2(12.9898, 78.233))) * 43758.5453123);
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

vec2 RandomGradient(vec2 st) {
    float r = TAU * Noise21(st);
    return vec2(cos(r), sin(r));
}

float LocalDisplacement(vec2 grid, vec2 st) {
    vec2 localPos = st - grid;
    vec2 grad = RandomGradient(grid);
    return dot(grad, localPos);
}

vec2 QuinticInterpolation(vec2 x) {
    return x * x * x * (10.0 + x * (-15.0 + x * 6.0));
}

float PerlinNoise(vec2 st) {
    vec2 grid0 = floor(st);
    vec2 grid1 = grid0 + 1.0;

    float v0 = LocalDisplacement(grid0, st);
    float v1 = LocalDisplacement(vec2(grid1.x, grid0.y), st);
    float v2 = LocalDisplacement(vec2(grid0.x, grid1.y), st);
    float v3 = LocalDisplacement(grid1, st);

    vec2 a = QuinticInterpolation(fract(st));

    return SQRT2 * mix(mix(v0, v1, a.x), mix(v2, v3, a.x), a.y);
}

void main() {
    vec2 st = (gl_FragCoord.xy * 2.0 - uResolution) / uResolution;

    float r = PerlinNoise(st * 10.0) * 0.5 + 0.5;

    gl_FragColor = vec4(r, r, r, 1.0);
}
