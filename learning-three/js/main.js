"use strict";

async function downloadText(url) {
    const resp = await fetch(url);
    if (!resp.ok) {
        console.log(resp);
        throw new Error(`Failed to download text: url=${url}, status=${resp.status}`);
    }
    return await resp.text();
}

async function newShaderMaterial(resolution) {
    var vertexShader = await downloadText("/shaders/basic.vert");
    var fragmentShader = await downloadText("/shaders/sphere.frag");

    const uniforms = {
        uResolution: { value: resolution },
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

    const renderer = new THREE.WebGLRenderer();
    renderer.setSize(window.innerWidth, window.innerHeight);
    renderer.setClearColor(0x333333, 1);
    renderer.gammaInput = true;
    renderer.gammaOutput = true;
    renderer.gammaFactor = 2.2;
    document.body.appendChild(renderer.domElement);

    const geometry = new THREE.PlaneGeometry(1.0, 1.0);
    const material = await newShaderMaterial(new THREE.Vector2(window.innerWidth, window.innerHeight));
    const plane = new THREE.Mesh(geometry, material);

    scene.add(plane);

    function render() {
        renderer.render(scene, camera);
    }
    renderer.setAnimationLoop(render);
}

main();
