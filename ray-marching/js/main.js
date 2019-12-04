"use strict";

async function downloadText(url) {
    const resp = await fetch(url);
    if (!resp.ok) {
        console.log(resp);
        throw new Error(`Failed to download text: url=${url}, status=${resp.status}`);
    }
    return await resp.text();
}

async function newShaderMaterial(uTime, uResolution) {
    var vertexShader = await downloadText("/shaders/basic.vert");
    var fragmentShader = await downloadText("/shaders/wave.frag");

    const uniforms = {
        uResolution: uResolution,
        uTime: uTime,
    };

    return new THREE.RawShaderMaterial({
        uniforms: uniforms,
        vertexShader: vertexShader,
        fragmentShader: fragmentShader,
    });
}

async function main() {
    const scene = new THREE.Scene();
    const camera = new THREE.OrthographicCamera(-0.5, 0.5, 0.5, -0.5, 0.0, 1000.0);

    const canvas = document.createElement("canvas");
    const context = canvas.getContext("webgl2", { alpha: false });
    const renderer = new THREE.WebGLRenderer({ canvas: canvas, context: context });
    renderer.setSize(window.innerWidth, window.innerHeight);
    renderer.setClearColor(0x333333, 1);
    renderer.gammaInput = true;
    renderer.gammaOutput = true;
    renderer.gammaFactor = 2.2;
    document.body.appendChild(renderer.domElement);

    const uTime = new THREE.Uniform(0.0);
    const uResolution = new THREE.Uniform(new THREE.Vector2(window.innerWidth, window.innerHeight));

    const geometry = new THREE.PlaneGeometry(1.0, 1.0);
    const material = await newShaderMaterial(uTime, uResolution);
    const plane = new THREE.Mesh(geometry, material);

    scene.add(plane);

    function render() {
        uTime.value = performance.now() / 1000.0;
        renderer.render(scene, camera);
    }
    renderer.setAnimationLoop(render);
}

main();
