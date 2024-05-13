use std::{
    collections::{hash_map::Entry, HashMap},
    fmt::Display,
    sync::Mutex,
};

use once_cell::sync::Lazy;

static SYMBOL_TO_STRING: Mutex<Vec<&'static str>> = Mutex::new(Vec::new());
static STRING_TO_SYMBOL: Lazy<Mutex<HashMap<&'static str, Symbol>>> =
    Lazy::new(|| Mutex::new(HashMap::new()));

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct Symbol(usize);

impl From<String> for Symbol {
    fn from(value: String) -> Self {
        From::<&'static str>::from(value.leak())
    }
}

impl From<&'static str> for Symbol {
    fn from(str: &'static str) -> Self {
        let mut string_to_symbol = STRING_TO_SYMBOL.lock().unwrap();
        match string_to_symbol.entry(str) {
            Entry::Occupied(entry) => *entry.get(),
            Entry::Vacant(entry) => {
                let mut symbol_to_string = SYMBOL_TO_STRING.lock().unwrap();
                let symbol = Symbol(symbol_to_string.len());
                symbol_to_string.push(str);
                entry.insert(symbol);
                symbol
            }
        }
    }
}

impl Display for Symbol {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let symbol_to_string = SYMBOL_TO_STRING.lock().unwrap();
        symbol_to_string[self.0].fmt(f)
    }
}
