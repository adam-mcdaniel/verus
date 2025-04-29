use super::*;

builtin!(
    PRODUCT,
    Type::function([Type::list(Type::number())], Type::number()),
    "Multiply all numbers in a list",
    "Take a list of numbers and return their product.",
    |args| {
        let arg = args[0].clone();
        Ok(match arg {
            Const::List(list) => {
                let mut product = Const::Int(1);
                for item in list {
                    product = match (item, product) {
                        (Const::Int(i), Const::Int(p)) => Const::Int(i * p),
                        (Const::Float(f), Const::Float(p)) => Const::Float(f * p),
                        (Const::Int(i), Const::Float(p)) => Const::Float(i as f64 * p),
                        (Const::Float(f), Const::Int(i)) => Const::Float(f * i as f64),
                        _ => Err(anyhow::anyhow!("Expected a number"))?,
                    }
                }
                product
            }
            _ => Err(anyhow::anyhow!("Expected a list"))?,
        })
    }
);

builtin!(
    SUM,
    Type::function([Type::list(Type::number())], Type::number()),
    "Add two numbers",
    "Take two numbers and return their sum.",
    |args| {
        let arg = args[0].clone();
        Ok(match arg {
            Const::List(list) => {
                let mut sum = Const::Int(0);
                for item in list {
                    sum = match (item, sum) {
                        (Const::Int(i), Const::Int(s)) => Const::Int(i + s),
                        (Const::Float(f), Const::Float(s)) => Const::Float(f + s),
                        (Const::Int(i), Const::Float(s)) => Const::Float(i as f64 + s),
                        (Const::Float(f), Const::Int(i)) => Const::Float(f + i as f64),
                        _ => Err(anyhow::anyhow!("Expected a number"))?,
                    }
                }
                sum
            }
            _ => Err(anyhow::anyhow!("Expected a list"))?,
        })
    }
);

builtin!(
    RANGE,
    Type::function([Type::number(), Type::number()], Type::list(Type::number())),
    "Create a range of numbers",
    "Create a list of numbers from start to end (exclusive).",
    |args| {
        let start = args[0].clone();
        let end = args[1].clone();
        Ok(match (start, end) {
            (Const::Int(s), Const::Int(e)) => {
                let mut range = Vec::new();
                for i in s..e {
                    range.push(Const::Int(i));
                }
                Const::List(range)
            }
            (Const::Float(s), Const::Float(e)) => {
                let mut range = Vec::new();
                for i in (s as i64)..(e as i64) {
                    range.push(Const::Float(i as f64));
                }
                Const::List(range)
            }
            _ => Err(anyhow::anyhow!("Expected two numbers"))?,
        })
    }
);

builtin!(
    MIN,
    Type::function([Type::list(Type::number())], Type::number()),
    "Find the minimum value in a list",
    "Take a list of numbers and return the minimum value.",
    |args| {
        let arg = args[0].clone();
        Ok(match arg {
            Const::List(list) => {
                let mut min = match list[0] {
                    Const::Int(i) => Const::Int(i),
                    Const::Float(f) => Const::Float(f),
                    _ => Err(anyhow::anyhow!("Expected a number"))?,
                };
                for item in list {
                    min = match (item, min) {
                        (Const::Int(i), Const::Int(m)) if i < m => Const::Int(i),
                        (Const::Float(f), Const::Float(m)) if f < m => Const::Float(f),
                        (_, x) => x,
                    }
                }
                min
            }
            _ => Err(anyhow::anyhow!("Expected a list"))?,
        })
    }
);

builtin!(
    MAX,
    Type::function([Type::list(Type::number())], Type::number()),
    "Find the maximum value in a list",
    "Take a list of numbers and return the maximum value.",
    |args| {
        let arg = args[0].clone();
        Ok(match arg {
            Const::List(list) => {
                let mut max = match list[0] {
                    Const::Int(i) => Const::Int(i),
                    Const::Float(f) => Const::Float(f),
                    _ => Err(anyhow::anyhow!("Expected a number"))?,
                };
                for item in list {
                    max = match (item, max) {
                        (Const::Int(i), Const::Int(m)) if i > m => Const::Int(i),
                        (Const::Float(f), Const::Float(m)) if f > m => Const::Float(f),
                        (_, x) => x,
                    }
                }
                max
            }
            _ => Err(anyhow::anyhow!("Expected a list"))?,
        })
    }
);

builtin!(
    MEAN,
    Type::function([Type::list(Type::number())], Type::number()),
    "Calculate the mean of a list of numbers",
    "Take a list of numbers and return their mean.",
    |args| {
        let arg = args[0].clone();
        Ok(match arg {
            Const::List(list) => {
                let sum = list
                    .iter()
                    .fold(Const::Int(0), |acc, item| match (item, acc) {
                        (Const::Int(i), Const::Int(s)) => Const::Int(i + s),
                        (Const::Float(f), Const::Float(s)) => Const::Float(f + s),
                        (Const::Int(i), Const::Float(s)) => Const::Float((*i as f64) + s),
                        (Const::Float(f), Const::Int(i)) => Const::Float(f + i as f64),
                        _ => Const::Void,
                    });
                if sum == Const::Void {
                    Err(anyhow::anyhow!("Expected a number"))?
                }
                let count = list.len() as f64;
                match sum {
                    Const::Int(s) => Const::Float(s as f64 / count),
                    Const::Float(s) => Const::Float(s / count),
                    _ => Err(anyhow::anyhow!("Expected a number"))?,
                }
            }
            _ => Err(anyhow::anyhow!("Expected a list"))?,
        })
    }
);

builtin!(
    ABS,
    Type::function([Type::number()], Type::number()),
    "Calculate the absolute value of a number",
    "Take a number and return its absolute value.",
    |args| {
        let arg = args[0].clone();
        Ok(match arg {
            Const::Int(i) => Const::Int(i.abs()),
            Const::Float(f) => Const::Float(f.abs()),
            _ => Err(anyhow::anyhow!("Expected a number"))?,
        })
    }
);

builtin!(
    POW,
    Type::function([Type::number(), Type::number()], Type::number()),
    "Calculate the power of a number",
    "Take a base and an exponent and return the result of base raised to the power of exponent.",
    |args| {
        let base = args[0].clone();
        let exponent = args[1].clone();
        Ok(match (base, exponent) {
            (Const::Int(b), Const::Int(e)) => Const::Int(b.pow(e as u32)),
            (Const::Float(b), Const::Float(e)) => Const::Float(b.powf(e)),
            (Const::Int(b), Const::Float(e)) => Const::Float((b as f64).powf(e)),
            (Const::Float(b), Const::Int(e)) => Const::Float(b.powi(e as i32)),
            _ => Err(anyhow::anyhow!("Expected two numbers"))?,
        })
    }
);

builtin!(
    SQRT,
    Type::function([Type::number()], Type::number()),
    "Calculate the square root of a number",
    "Take a number and return its square root.",
    |args| {
        let arg = args[0].clone();
        Ok(match arg {
            Const::Int(i) => Const::Float((i as f64).sqrt()),
            Const::Float(f) => Const::Float(f.sqrt()),
            _ => Err(anyhow::anyhow!("Expected a number"))?,
        })
    }
);

builtin!(
    CLAMP,
    Type::function(
        [Type::number(), Type::number(), Type::number()],
        Type::number()
    ),
    "Clamp a number between two values",
    "Take a number and two bounds and return the number clamped between the bounds.",
    |args| {
        let arg = args[0].clone();
        let min = args[1].clone();
        let max = args[2].clone();
        Ok(match (arg, min, max) {
            (Const::Int(i), Const::Int(min), Const::Int(max)) => Const::Int(i.clamp(min, max)),
            (Const::Float(f), Const::Float(min), Const::Float(max)) => {
                Const::Float(f.clamp(min, max))
            }
            _ => Err(anyhow::anyhow!("Expected three numbers"))?,
        })
    }
);

builtin!(
    FLOOR,
    Type::function([Type::number()], Type::number()),
    "Calculate the floor of a number",
    "Take a number and return its floor value.",
    |args| {
        let arg = args[0].clone();
        Ok(match arg {
            Const::Int(i) => Const::Int(i),
            Const::Float(f) => Const::Int(f.floor() as i64),
            _ => Err(anyhow::anyhow!("Expected a number"))?,
        })
    }
);

builtin!(
    CEIL,
    Type::function([Type::number()], Type::number()),
    "Calculate the ceiling of a number",
    "Take a number and return its ceiling value.",
    |args| {
        let arg = args[0].clone();
        Ok(match arg {
            Const::Int(i) => Const::Int(i),
            Const::Float(f) => Const::Int(f.ceil() as i64),
            _ => Err(anyhow::anyhow!("Expected a number"))?,
        })
    }
);

builtin!(
    ROUND,
    Type::function([Type::number()], Type::number()),
    "Round a number to the nearest integer",
    "Take a number and return its rounded value.",
    |args| {
        let arg = args[0].clone();
        Ok(match arg {
            Const::Int(i) => Const::Int(i),
            Const::Float(f) => Const::Int(f.round() as i64),
            _ => Err(anyhow::anyhow!("Expected a number"))?,
        })
    }
);

pub fn create_math_library() -> Library {
    Library::new([
        PRODUCT.clone(),
        SUM.clone(),
        RANGE.clone(),
        MIN.clone(),
        MAX.clone(),
        MEAN.clone(),
        ABS.clone(),
        POW.clone(),
        SQRT.clone(),
        CLAMP.clone(),
        FLOOR.clone(),
        CEIL.clone(),
        ROUND.clone(),
    ])
}
