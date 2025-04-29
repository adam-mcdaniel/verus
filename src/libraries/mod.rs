use crate::*;

mod list;
mod math;
mod string;

#[macro_export]
macro_rules! builtin {
    ($name:ident, $ty:expr, $short_help:literal, $long_help:literal, $body:expr) => {
        lazy_static::lazy_static! {
            pub static ref $name: Builtin = Builtin::new(
                stringify!($name).to_lowercase().to_string(),
                $ty,
                $short_help,
                $long_help,
                $body
            );
        }
    };
}

builtin!(
    NEGATE,
    Type::function([Type::number()], Type::number()),
    "Negate a number",
    "Take a float or integer and return its negative value.",
    |args| {
        let arg = args[0].clone();
        Ok(match arg {
            Const::Int(i) => Const::Int(-i),
            Const::Float(f) => Const::Float(-f),
            _ => Err(anyhow::anyhow!("Expected a number"))?,
        })
    }
);

builtin!(
    NOT,
    "\\Bool -> Bool",
    "Negate a boolean",
    "Take a boolean. If the input is false, return true. If the input is true, return false.",
    |args| {
        let arg = args[0].clone();
        Ok(match arg {
            Const::Bool(b) => Const::Bool(!b),
            _ => Err(anyhow::anyhow!("Expected a boolean"))?,
        })
    }
);

builtin!(
    ADD,
    Type::function([Type::number(), Type::number()], Type::number()),
    "Add two numbers",
    "Take two numbers and return their sum.",
    |args| {
        let arg1 = args[0].clone();
        let arg2 = args[1].clone();
        Ok(match (arg1, arg2) {
            (Const::Int(i1), Const::Int(i2)) => Const::Int(i1 + i2),
            (Const::Float(f1), Const::Float(f2)) => Const::Float(f1 + f2),
            (Const::Int(i), Const::Float(f)) => Const::Float(i as f64 + f),
            (Const::Float(f), Const::Int(i)) => Const::Float(f + i as f64),

            _ => Err(anyhow::anyhow!("Expected two numbers"))?,
        })
    }
);

builtin!(
    SUBTRACT,
    Type::function([Type::number(), Type::number()], Type::number()),
    "Subtract two numbers",
    "Take two numbers and return their difference.",
    |args| {
        let arg1 = args[0].clone();
        let arg2 = args[1].clone();
        Ok(match (arg1, arg2) {
            (Const::Int(i1), Const::Int(i2)) => Const::Int(i1 - i2),
            (Const::Float(f1), Const::Float(f2)) => Const::Float(f1 - f2),
            (Const::Int(i), Const::Float(f)) => Const::Float(i as f64 - f),
            (Const::Float(f), Const::Int(i)) => Const::Float(f - i as f64),

            _ => Err(anyhow::anyhow!("Expected two numbers"))?,
        })
    }
);

builtin!(
    MULTIPLY,
    Type::function([Type::number(), Type::number()], Type::number()),
    "Multiply two numbers",
    "Take two numbers and return their product.",
    |args| {
        let arg1 = args[0].clone();
        let arg2 = args[1].clone();
        Ok(match (arg1, arg2) {
            (Const::Int(i1), Const::Int(i2)) => Const::Int(i1 * i2),
            (Const::Float(f1), Const::Float(f2)) => Const::Float(f1 * f2),
            (Const::Int(i), Const::Float(f)) => Const::Float(i as f64 * f),
            (Const::Float(f), Const::Int(i)) => Const::Float(f * i as f64),

            _ => Err(anyhow::anyhow!("Expected two numbers"))?,
        })
    }
);

builtin!(
    DIVIDE,
    Type::function([Type::number(), Type::number()], Type::number()),
    "Divide two numbers",
    "Take two numbers and return their quotient.",
    |args| {
        let arg1 = args[0].clone();
        let arg2 = args[1].clone();
        Ok(match (arg1, arg2) {
            (Const::Int(i1), Const::Int(i2)) => Const::Int(i1 / i2),
            (Const::Float(f1), Const::Float(f2)) => Const::Float(f1 / f2),
            (Const::Int(i), Const::Float(f)) => Const::Float(i as f64 / f),
            (Const::Float(f), Const::Int(i)) => Const::Float(f / i as f64),

            _ => Err(anyhow::anyhow!("Expected two numbers"))?,
        })
    }
);

builtin!(
    REMAINDER,
    Type::function([Type::number(), Type::number()], Type::number()),
    "Get the remainder of two numbers",
    "Take two numbers and return their remainder.",
    |args| {
        let arg1 = args[0].clone();
        let arg2 = args[1].clone();
        Ok(match (arg1, arg2) {
            (Const::Int(i1), Const::Int(i2)) => Const::Int(i1 % i2),
            (Const::Float(f1), Const::Float(f2)) => Const::Float(f1 % f2),
            (Const::Int(i), Const::Float(f)) => Const::Float(i as f64 % f),
            (Const::Float(f), Const::Int(i)) => Const::Float(f % i as f64),

            _ => Err(anyhow::anyhow!("Expected two numbers"))?,
        })
    }
);

builtin!(
    EQUAL,
    Type::function([Type::Any, Type::Any], Type::Bool),
    "Check if two values are equal",
    "Take two values and return true if they are equal, false otherwise.",
    |args| {
        let arg1 = args[0].clone();
        let arg2 = args[1].clone();
        Ok((arg1 == arg2).into())
    }
);

builtin!(
    NOT_EQUAL,
    Type::function([Type::Any, Type::Any], Type::Bool),
    "Check if two values are not equal",
    "Take two values and return true if they are not equal, false otherwise.",
    |args| {
        let arg1 = args[0].clone();
        let arg2 = args[1].clone();
        Ok((arg1 != arg2).into())
    }
);

builtin!(
    LESS_THAN,
    Type::function([Type::Any, Type::Any], Type::Bool),
    "Check if the first value is less than the second",
    "Take two values and return true if the first value is less than the second, false otherwise.",
    |args| {
        let arg1 = args[0].clone();
        let arg2 = args[1].clone();
        Ok((arg1 < arg2).into())
    }
);

builtin!(LESS_THAN_OR_EQUAL,
    Type::function([Type::Any, Type::Any], Type::Bool),
    "Check if the first value is less than or equal to the second",
    "Take two values and return true if the first value is less than or equal to the second, false otherwise.", |args| {
    let arg1 = args[0].clone();
    let arg2 = args[1].clone();
    Ok((arg1 <= arg2).into())
});

builtin!(GREATER_THAN,
    Type::function([Type::Any, Type::Any], Type::Bool),
    "Check if the first value is greater than the second",
    "Take two values and return true if the first value is greater than the second, false otherwise.", |args| {
    let arg1 = args[0].clone();
    let arg2 = args[1].clone();
    Ok((arg1 > arg2).into())
});

builtin!(GREATER_THAN_OR_EQUAL,
    Type::function([Type::Any, Type::Any], Type::Bool),
    "Check if the first value is greater than or equal to the second",
    "Take two values and return true if the first value is greater than or equal to the second, false otherwise.", |args| {
    let arg1 = args[0].clone();
    let arg2 = args[1].clone();
    Ok((arg1 >= arg2).into())
});

builtin!(
    AND,
    Type::function([Type::Bool, Type::Bool], Type::Bool),
    "Logical AND",
    "Take two booleans and return true if both are true, false otherwise.",
    |args| {
        let arg1 = args[0].clone();
        let arg2 = args[1].clone();
        Ok(match (arg1, arg2) {
            (Const::Bool(b1), Const::Bool(b2)) => Const::Bool(b1 && b2),
            _ => Err(anyhow::anyhow!("Expected two booleans"))?,
        })
    }
);

builtin!(
    OR,
    Type::function([Type::Bool, Type::Bool], Type::Bool),
    "Logical OR",
    "Take two booleans and return true if at least one is true, false otherwise.",
    |args| {
        let arg1 = args[0].clone();
        let arg2 = args[1].clone();
        Ok(match (arg1, arg2) {
            (Const::Bool(b1), Const::Bool(b2)) => Const::Bool(b1 || b2),
            _ => Err(anyhow::anyhow!("Expected two booleans"))?,
        })
    }
);

pub struct Library {
    builtins: Vec<Builtin>,
}

impl Library {
    pub fn new(builtins: impl IntoIterator<Item = Builtin>) -> Self {
        Self {
            builtins: builtins.into_iter().collect(),
        }
    }

    pub fn check_duplicates(&self) -> Result<(), String> {
        use std::collections::HashSet;
        let mut seen = HashSet::new();
        for builtin in &self.builtins {
            if !seen.insert(builtin.name.clone()) {
                return Err(format!("Duplicate builtin: {}", builtin.name));
            }
        }
        Ok(())
    }

    pub fn import(&self, expr: Expr) -> Expr {
        let mut result = expr;
        for builtin in &self.builtins {
            // Add a let binding for each builtin
            let name = builtin.name.clone();
            result = Expr::let_var(name.into(), None, builtin.clone(), result.clone());
        }
        result
    }

    pub fn join(libs: impl IntoIterator<Item = Library>) -> Self {
        let mut result = Self::new([]);
        for lib in libs {
            result.builtins.extend(lib.builtins);
        }
        result.check_duplicates().unwrap();
        result
    }

    pub fn stdlib() -> Self {
        Self::join([
            math::create_math_library(),
            string::create_string_library(),
            list::create_list_library(),
        ])
    }
}
