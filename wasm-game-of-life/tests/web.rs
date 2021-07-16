//! Test suite for the Web and headless browsers.

#![cfg(target_arch = "wasm32")]

extern crate wasm_bindgen_test;
use std::assert_eq;

use wasm_bindgen_test::*;
use wasm_game_of_life::{expected_spaceship, input_spaceship};

wasm_bindgen_test_configure!(run_in_browser);

#[wasm_bindgen_test]
pub fn test_tick() {
    let mut input_universe = input_spaceship();
    let expected_universe = expected_spaceship();
    input_universe.tick();
    assert_eq!(&input_universe.get_cells(), &expected_universe.get_cells());
}
