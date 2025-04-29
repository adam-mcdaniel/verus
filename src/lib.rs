use std::cell::RefCell;
use std::rc::Rc;
use std::str::FromStr;

pub mod expr;
pub use expr::*;

pub mod parser;
pub use parser::*;

pub mod libraries;
pub use libraries::*;

use tracing::*;

pub fn init_logging(level: &str) {
    let level = Level::from_str(level).unwrap_or(Level::INFO);
    let _ = tracing_subscriber::fmt()
        .with_max_level(level)
        .without_time()
        .with_target(false)
        .try_init();
}

pub fn check(expr: impl Into<Expr>) -> Result<Type, CheckError> {
    let expr = expr.into();
    let mut env = CheckEnv::new();
    let result = expr.check(&mut env);

    if let Err(e) = &result {
        error!("Check failed: {e}");
    } else {
        debug!("Check result: {result:?}");
    }
    result
}

pub fn eval(expr: impl Into<Expr>) -> Result<Const, CheckError> {
    let expr = expr.into();
    let env = EvalEnv::new();
    let result = expr.eval(Rc::new(RefCell::new(env)));

    if let Err(e) = &result {
        error!("Eval failed: {e}");
    } else {
        debug!("Eval result: {result:?}");
    }
    result
}

pub fn parse_type(input: &str) -> Result<Type, String> {
    use nom::combinator::all_consuming;
    use nom::error::convert_error;
    use nom::error::VerboseError;
    match all_consuming(parser::parse_type::<VerboseError<&str>>)(input) {
        Ok((_, expr)) => Ok(expr),
        Err(e) => {
            // Convert the error to a string
            let err_str = match e {
                nom::Err::Error(e) | nom::Err::Failure(e) => convert_error(input, e),
                nom::Err::Incomplete(_) => "Incomplete input".to_string(),
            };
            Err(err_str)
        }
    }
}
