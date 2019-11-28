#ifdef GL_ES
precision highp float;
#endif

const int LOOP_COUNT = 50;

const float EPS = 1e-4;
const float PI = acos(-1.0);

uniform vec2 uResolution;

float Sphere(vec3 p, vec3 center, float radius) {
    return distance(p, center) - radius;
}

float DistanceField(vec3 p) {
    return Sphere(p, vec3(0.0, 0.0, 0.0), 0.5);
}

vec3 GradientDirection(vec3 p) {
    float dist = DistanceField(p);
    float dx = DistanceField(p + vec3(EPS, 0.0, 0.0)) - dist;
    float dy = DistanceField(p + vec3(0.0, EPS, 0.0)) - dist;
    float dz = DistanceField(p + vec3(0.0, 0.0, EPS)) - dist;
    return normalize(vec3(dx, dy, dz));
}

vec3 RenderMaterial(vec3 p) {
    const vec3 albedo = vec3(0.7, 0.8, 0.3);
    vec3 color = vec3(0.0, 0.0, 0.0);

    // Diffuse
    vec3 light = normalize(vec3(-0.3, 1.0, -1.0));
    vec3 normal  = GradientDirection(p);
    color += albedo * max(dot(light, normal), 0.0) / PI;

    // Ambient
    const float ambient = 0.3;
    color += albedo * ambient;

    return color;
}

vec3 RayMarching(vec3 screenPos, vec3 cameraPos, vec3 backgroundColor) {
    vec3 rayDir = normalize(screenPos - cameraPos);

    float depth = 0.0;
    for (int i = 0; i < LOOP_COUNT; i++) {
        vec3 p = cameraPos + rayDir * depth;
        float dist = DistanceField(p);
        if (dist < EPS)
            return RenderMaterial(p);
        depth += dist;
    }

    return backgroundColor;
}

void main() {
    vec2 st = (gl_FragCoord.xy * 2.0 - uResolution) / min(uResolution.x, uResolution.y);

    const vec3 cameraPos = vec3(0.0, 0.0, -5.0);
    const float screenZ = 2.5;
    const vec3 backgroundColor = vec3(0.2, 0.2, 0.2);

    vec3 color = RayMarching(vec3(st, screenZ), cameraPos, backgroundColor);
    gl_FragColor = vec4(color, 1.0);
}
