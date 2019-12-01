#version 300 es

#ifdef GL_ES
precision highp float;
precision highp int;
#endif

const float PI = acos(-1.0);

uniform vec2 uResolution;
uniform float uTime;

out vec4 out_FragColor;

float hash(vec2 p) {
    float h = dot(p, vec2(127.1, 311.7));
    return fract(sin(h) * 43758.5453123);
}

vec2 cubicHermineCurve(vec2 x) {
    return x * x * (3.0 - 2.0 * x);
}

/*
vec2 quinticHermineCurve(vec2 x) {
    return x * x * x * (x * (x * 6.0 - 15.0) + 10.0);
}
*/

float valueNoise(vec2 p) {
    vec2 i = floor(p);
    vec2 f = fract(p);

    vec2 u = cubicHermineCurve(f);

    float v0 = hash(i + vec2(0.0, 0.0));
    float v1 = hash(i + vec2(1.0, 0.0));
    float v2 = hash(i + vec2(0.0, 1.0));
    float v3 = hash(i + vec2(1.0, 1.0));

    float v = mix(mix(v0, v1, u.x), mix(v2, v3, u.x), u.y);
    return v * 2.0 - 1.0;
}

vec3 renderSky(vec3 eye) {
    float h = 1.0 - max(eye.y, 0.0);
    return vec3(h * h, h, 0.6 + 0.4 * h);
}

float wave(vec2 coord, float choppy) {
    coord += valueNoise(coord);
    vec2 wv = 1.0 - abs(sin(coord));
    vec2 swv = abs(cos(coord));
    wv = mix(wv, swv, wv);
    return pow(1.0 - pow(wv.x * wv.y, 0.65), choppy);
}

float heightMap(vec2 coord) {
    const mat2 octave_m = mat2(1.6, 1.2, -1.2, 1.6);

    coord += 10.0;

    float freq = 0.16;
    float amp = 0.6;
    float choppy = 4.0;

    float t = 1.0 + uTime * 0.8;

    float h = 0.0;
    for (int i = 0; i < 5; ++i) {
        float d = wave((coord + t) * freq, choppy);
        d += wave((coord - t) * freq, choppy);
        h += d * amp;
        coord *= octave_m;
        freq *= 2.0;
        amp *= 0.2;
        choppy = mix(choppy, 1.0, 0.2);
    }

    return h;
}

float altitude(vec3 p) {
    return p.y - heightMap(p.xz);
}

vec3 gradient(vec3 p, float eps) {
    float a0 = altitude(p);
    float ax = altitude(p + vec3(eps, 0.0, 0.0));
    float az = altitude(p + vec3(0.0, 0.0, eps));
    float dax = (ax - a0) / eps;
    float daz = (az - a0) / eps;
    return normalize(vec3(
        sign(dax) * sqrt(dax * dax + 1.0),
        1.0,
        sign(daz) * sqrt(daz * daz + 1.0)
    ));
}

float castRay(vec3 cameraPos, vec3 rayDir) {
    float near = 0.0;
    float far = 1000.0;

    float farAlt = altitude(cameraPos + rayDir * far);
    if (farAlt >= 0.0) {
        return far;
    }
    float nearAlt = altitude(cameraPos + rayDir * near);

    float middle;
    for (int i = 0; i < 8; ++i) {
        float alpha = nearAlt / (nearAlt - farAlt);
        middle = mix(near, far, alpha);
        vec3 middlePos = cameraPos + rayDir * middle;
        float middleAlt = altitude(middlePos);
        if (middleAlt < 0.0) {
            far = middle;
            farAlt = middleAlt;
        } else {
            near = middle;
            nearAlt = middleAlt;
        }
    }
    return middle;
}

float fresnel(float cosine, float f0) {
    return f0 + (1.0 - f0) * pow(1.0 - cosine, 5.0);
}

vec3 diffuse(vec3 normal, vec3 light) {
    const vec3 albedo = vec3(0.8, 0.9, 0.6);
    return dot(normal, light) * albedo / PI;
}

float specular(vec3 normal, vec3 light, vec3 eye) {
    const float shininess = 30.0;
    vec3 reflectionDir = -reflect(light, normal);
    float d = max(dot(reflectionDir, -eye), 0.0);
    return (shininess + 1.0) * pow(d, shininess) / (2.0 * PI);
}

vec3 fog(vec3 baseColor, vec3 fogColor, float depth) {
    float alpha = exp(-depth * 0.005);
    return mix(fogColor, baseColor, alpha);
}

vec3 renderSea(vec3 p, vec3 normal, vec3 light, vec3 eye, float depth) {
    float fr = fresnel(max(dot(normal, -eye), 0.0), 0.4);

    vec3 reflected = renderSky(reflect(eye, normal));
    vec3 refracted = vec3(0.0, 0.1, 0.3) + diffuse(normal, light);

    vec3 color = vec3(0.0, 0.0, 0.0);
    color += mix(refracted, reflected, fr);
    color += fr * specular(normal, light, eye);

    return fog(color, vec3(1.0, 1.0, 1.0), depth);
}

vec3 render(vec2 coord) {
    const vec3 light = normalize(vec3(1.0, 1.0, 0.5));
    vec3 cameraPos = vec3(0.0, 3.5, 5.0);
    vec3 rayDir = normalize(vec3(coord, 0.0) + vec3(0.0, -0.5, -2.0));

    float depth = castRay(cameraPos, rayDir);
    vec3 surfacePos = cameraPos + rayDir * depth;

    float eps = (depth + 1.0) * 0.05 / min(uResolution.x, uResolution.y);
    vec3 normal = gradient(surfacePos, eps);

    vec3 seaColor = renderSea(surfacePos, normal, light, rayDir, depth);
    vec3 skyColor = renderSky(rayDir);

    return mix(seaColor, skyColor, depth / 1000.0);
}

vec3 sRGB(vec3 linearColor) {
    linearColor = clamp(linearColor, 0.0, 1.0);
    return pow(linearColor, vec3(1.0, 1.0, 1.0) / 2.2);
}

void main() {
    vec2 coord = (gl_FragCoord.xy / uResolution) * 2.0 - 1.0;
    vec3 linearColor = render(coord);
    out_FragColor = vec4(sRGB(linearColor), 1.0);
}
