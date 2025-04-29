use std::cell::RefCell;
use std::rc::Rc;
use std::str::FromStr;

pub mod expr;
pub use expr::*;

pub mod parser;
pub use parser::*;

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

    if result.is_err() {
        error!("Check failed: {result:?}");
    } else {
        debug!("Check result: {result:?}");
    }
    result
}

pub fn eval(expr: impl Into<Expr>) -> Result<Const, CheckError> {
    let expr = expr.into();
    let env = EvalEnv::new();
    let result = expr.eval(Rc::new(RefCell::new(env)));

    if result.is_err() {
        error!("Eval failed: {result:?}");
    } else {
        debug!("Eval result: {result:?}");
    }
    result
}