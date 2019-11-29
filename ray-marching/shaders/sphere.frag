#ifdef GL_ES
precision highp float;
#endif

const int LOOP_COUNT = 100;

const float EPS = 1e-4;
const float PI = acos(-1.0);

uniform vec2 uResolution;

float Sphere(vec3 p, vec3 center, float radius) {
    return distance(p, center) - radius;
}

float DistanceField(vec3 p) {
    p.z = mod(p.z, 1.0);
    p.y = mod(p.y, 1.0);
    p.x = mod(p.x, 0.5);
    return Sphere(p, vec3(0.25, 0.5, 0.5), 0.1);
}

vec3 GradientDirection(vec3 p) {
    float dist = DistanceField(p);
    float dx = DistanceField(p + vec3(EPS, 0.0, 0.0)) - dist;
    float dy = DistanceField(p + vec3(0.0, EPS, 0.0)) - dist;
    float dz = DistanceField(p + vec3(0.0, 0.0, EPS)) - dist;
    return normalize(vec3(dx, dy, dz));
}

vec3 RenderMaterial(vec3 p, float depth, vec3 normal, vec3 cameraPos) {
    const vec3 albedo = vec3(0.7, 0.8, 0.3);
    const float lightIntencity = 1.2;
    const vec3 lightDir = normalize(vec3(-0.3, 1.0, -1.0));
    const float shininess = 50.0;
    const float fresnel = 0.1;

    vec3 color = vec3(0.0, 0.0, 0.0);

    // Diffuse (Lambert)
    color += albedo * max(dot(lightDir, normal), 0.0) * lightIntencity / PI;

    // Specular (Phong)
    vec3 viewDir = normalize(cameraPos - p);
    vec3 reflectionDir = -reflect(lightDir, normal);
    float d = max(dot(reflectionDir, viewDir), 0.0);
    color += fresnel * (shininess + 1.0) * pow(d, shininess) * lightIntencity / (2.0 * PI);

    // Ambient
    const float ambient = 0.3;
    color += albedo * ambient * lightIntencity;

    return color * exp(-0.1 * depth);
}

vec3 RayMarching(vec3 screenPos, vec3 cameraPos, vec3 backgroundColor) {
    vec3 rayDir = normalize(screenPos - cameraPos);

    float depth = 0.0;
    for (int i = 0; i < LOOP_COUNT; i++) {
        vec3 p = cameraPos + rayDir * depth;
        float dist = DistanceField(p);
        if (dist < EPS) {
            vec3 normal = GradientDirection(p);
            return RenderMaterial(p, depth, normal, cameraPos);
        }
        depth += dist;
    }

    return backgroundColor;
}

void main() {
    vec2 st = (gl_FragCoord.xy * 2.0 - uResolution) / min(uResolution.x, uResolution.y);

    const vec3 cameraPos = vec3(0.0, 0.25, -3.0);
    const float screenZ = 0.0;
    const vec3 backgroundColor = vec3(0.0, 0.0, 0.0);

    vec3 color = RayMarching(vec3(st, screenZ), cameraPos, backgroundColor);
    gl_FragColor = vec4(color, 1.0);
}
