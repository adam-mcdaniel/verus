use tracing::*;
use verus::*;

/*
use std::cell::RefCell;
use std::rc::Rc;
fn test_parse_program() -> anyhow::Result<()> {
    let input = r#"{
        let test = \x: Int -> \y: Str -> x;
        
        let x = (let test = 5 in test);
        let g = test x;
        g "hello!"
    }"#;

    let expr = parse(input);
    println!("{input:?} -> {expr:?}");

    match expr {
        Ok(expr) => {
            println!("Parsed expression: {:#?}", expr);
            let mut env = CheckEnv::new();
            let result = expr.check(&mut env);

            println!("Check result: {:#?}", result);

            match expr.eval(Rc::new(RefCell::new(EvalEnv::new()))) {
                Ok(result) => {
                    println!("Eval result: {:#?}", result);
                }
                Err(e) => {
                    panic!("Failed to evaluate expression: {e}");
                }
            }
        }
        Err(e) => {
            panic!("Failed to parse program:\n{e}");
        }
    }

    Ok(())
}

fn test_parse_program2() {
    let input = r#"{
        let test = \x:Num -> \y:Str -> x;
        
        let fact n:Num = product (range 1 n + 1);

        let test1 = min (append [1, 2, 3, 5, 4] (-1));

        let mul = \x:Num -> \y:Num -> x * y;

        let double = mul 2;

        let square = \x:Num -> x * x;

        let head | tail = [1, 2, 3, 4, 5];
        debug "Head:";
        debug head;
        debug "Tail:";
        debug tail;

        let l = [1, 2, 3, 4, 5];
        let l1 = mapnum square l;

        help rev;

        info (fread "Cargo.toml");

        let g = test (max l1);
        g "hello!"
    }"#;

    match parse(input) {
        Ok(expr) => {
            let expr = Library::stdlib().import(expr);

            if let Err(e) = check(expr.clone()) {
                panic!("Failed to check expression: {e}");
            }

            match eval(expr.clone()) {
                Ok(result) => {
                    println!("Eval result: {:#?}", result);
                }
                Err(e) => {
                    panic!("Failed to evaluate expression: {e}");
                }
            }
        }
        Err(e) => {
            panic!("Failed to parse program:\n{e}");
        }
    }
}
 */

fn main() {
    init_logging("debug");
    match cli() {
        Ok(_) => {
            info!("Program executed successfully");
        }
        Err(e) => {
            error!("Error: {e}");
            std::process::exit(1);
        }
    }
}
