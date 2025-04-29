use verus::*;
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


fn main() {
    init_logging("debug");
    let input = r#"{
        let test = \x: Int -> \y: Str -> x;
        
        let x = (let test = 5 in test);
        let g = test x;
        g "hello!"
    }"#;

    match parse(input) {
        Ok(expr) => {
            println!("Parsed expression: {:#?}", expr);
        
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
