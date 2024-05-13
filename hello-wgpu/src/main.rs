use wasm_bindgen_futures::spawn_local;
use gloo::utils::{document, document_element};
use wasm_bindgen::JsCast;
use web_sys::HtmlCanvasElement;

#[global_allocator]
static ALLOC: wee_alloc::WeeAlloc = wee_alloc::WeeAlloc::INIT;

async fn run() {
    let canvas = document().create_element("canvas").unwrap();
    document_element().append_child(&canvas).unwrap();
    let canvas: HtmlCanvasElement = canvas.dyn_into().unwrap();

    let width = canvas.width();
    let height = canvas.height();

    let instance = wpgu::Instance::new(wgpu::Backends::all());
    let surface = instance.create_surface_from_canvas(&canvs);

}

fn main() {
    wasm_logger::init(wasm_logger::Config::default());
    spawn_local(run());
}
