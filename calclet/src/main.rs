mod lexer;
mod token;

static SAMPLE_CODE: &str = "// This is a comment
let x = 42;
let y = 3.14;
let z = \"Hello, World!\";
if y >= 0 then
  x + y
else
  x - y
";

fn main() -> anyhow::Result<()> {
    for r in lexer::Lexer::new(SAMPLE_CODE) {
        let (span_start, token, span_end) = r?;
        println!("[{:3}:{:3}] {:?}", span_start, span_end, token);
    }
    Ok(())
}
