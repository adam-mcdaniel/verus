/*
fn main() {
    println!("Hello, world!");
}
*/
mod parser; // This tells Rust to include src/parser.rs as a module.
use parser::Parser; // Now we can use Parser here.

fn main() {
    let inputs = [
        "42",
        "True",
        r#""Hello, world!""#,
        "struct { x: 42, y: 7 }",
        "Option::Some(42)",
        "x -> { x }",
    ];

    for input in &inputs {
        let mut parser = Parser::new(input);
        match parser.parse_expr() {
            Ok(expr) => println!("Input: {}\nParsed AST: {:?}\n", input, expr),
            Err(e) => println!("Input: {}\nError: {}\n", input, e),
        }
    }
}