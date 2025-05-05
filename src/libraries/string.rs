use super::*;

builtin!(
    STRLEN,
    Type::function([Type::Str], Type::Int),
    "Get the length of a string",
    "Take a string and return its length.",
    |args| {
        let arg1 = args[0].clone();
        Ok(match arg1 {
            Const::Str(s) => Const::Int(s.len() as i64),
            _ => Err(anyhow::anyhow!("Expected a string"))?,
        })
    }
);

builtin!(
    UPPER,
    Type::function([Type::Str], Type::Str),
    "Convert a string to uppercase",
    "Take a string and return its uppercase version.",
    |args| {
        let arg1 = args[0].clone();
        Ok(match arg1 {
            Const::Str(s) => Const::Str(s.to_uppercase()),
            _ => Err(anyhow::anyhow!("Expected a string"))?,
        })
    }
);

builtin!(
    LOWER,
    Type::function([Type::Str], Type::Str),
    "Convert a string to lowercase",
    "Take a string and return its lowercase version.",
    |args| {
        let arg1 = args[0].clone();
        Ok(match arg1 {
            Const::Str(s) => Const::Str(s.to_lowercase()),
            _ => Err(anyhow::anyhow!("Expected a string"))?,
        })
    }
);

builtin!(
    TRIM,
    Type::function([Type::Str], Type::Str),
    "Trim whitespace from a string",
    "Take a string and return it with leading and trailing whitespace removed.",
    |args| {
        let arg1 = args[0].clone();
        Ok(match arg1 {
            Const::Str(s) => Const::Str(s.trim().to_string()),
            _ => Err(anyhow::anyhow!("Expected a string"))?,
        })
    }
);

builtin!(
    STRSPLIT,
    Type::function([Type::Str, Type::Str], Type::list(Type::Str)),
    "Split a string by a delimiter",
    "Take a string and a delimiter and return a list of strings.",
    |args| {
        let arg1 = args[0].clone();
        let arg2 = args[1].clone();
        Ok(match (arg1, arg2) {
            (Const::Str(s), Const::Str(delim)) => {
                let parts: Vec<Const> =
                    s.split(&delim).map(|s| Const::Str(s.to_string())).collect();
                Const::List(parts)
            }
            _ => Err(anyhow::anyhow!("Expected two strings"))?,
        })
    }
);

builtin!(
    JOIN,
    Type::function([Type::list(Type::Str), Type::Str], Type::Str),
    "Join a list of strings with a delimiter",
    "Take a list of strings and a delimiter and return a single string.",
    |args| {
        let arg1 = args[0].clone();
        let arg2 = args[1].clone();
        Ok(match (arg1, arg2) {
            (Const::List(list), Const::Str(delim)) => {
                let mut parts: Vec<String> = vec![];
                for item in list {
                    if let Const::Str(s) = item {
                        parts.push(s);
                    } else {
                        Err(anyhow::anyhow!("Expected a list of strings"))?;
                    }
                }
                Const::Str(parts.join(&delim))
            }
            _ => Err(anyhow::anyhow!("Expected a list of strings and a string"))?,
        })
    }
);

builtin!(
    STRCONTAINS,
    Type::function([Type::Str, Type::Str], Type::Bool),
    "Check if a string contains a substring",
    "Take a string and a substring and return true if the string contains the substring, false otherwise.",
    |args| {
        let arg1 = args[0].clone();
        let arg2 = args[1].clone();
        Ok(match (arg1, arg2) {
            (Const::Str(s), Const::Str(sub)) => Const::Bool(s.contains(&sub)),
            _ => Err(anyhow::anyhow!("Expected two strings"))?,
        })
    }
);

builtin!(
    STRREPLACE,
    Type::function([Type::Str, Type::Str, Type::Str], Type::Str),
    "Replace a substring in a string",
    "Take a string, a substring to replace, and a replacement string and return the modified string.",
    |args| {
        let arg1 = args[0].clone();
        let arg2 = args[1].clone();
        let arg3 = args[2].clone();
        Ok(match (arg1, arg2, arg3) {
            (Const::Str(s), Const::Str(old), Const::Str(new)) => {
                Const::Str(s.replace(&old, &new))
            }
            _ => Err(anyhow::anyhow!("Expected three strings"))?,
        })
    }
);

builtin!(
    STARTS_WITH,
    Type::function([Type::Str, Type::Str], Type::Bool),
    "Check if a string starts with a substring",
    "Take a string and a substring and return true if the string starts with the substring, false otherwise.",
    |args| {
        let arg1 = args[0].clone();
        let arg2 = args[1].clone();
        Ok(match (arg1, arg2) {
            (Const::Str(s), Const::Str(prefix)) => Const::Bool(s.starts_with(&prefix)),
            _ => Err(anyhow::anyhow!("Expected two strings"))?,
        })
    }
);

builtin!(
    ENDS_WITH,
    Type::function([Type::Str, Type::Str], Type::Bool),
    "Check if a string ends with a substring",
    "Take a string and a substring and return true if the string ends with the substring, false otherwise.",
    |args| {
        let arg1 = args[0].clone();
        let arg2 = args[1].clone();
        Ok(match (arg1, arg2) {
            (Const::Str(s), Const::Str(suffix)) => Const::Bool(s.ends_with(&suffix)),
            _ => Err(anyhow::anyhow!("Expected two strings"))?,
        })
    }
);

builtin!(
    STRREPEAT,
    Type::function([Type::Str, Type::Int], Type::Str),
    "Repeat a string a given number of times",
    "Take a string and an integer and return the string repeated that many times.",
    |args| {
        let arg1 = args[0].clone();
        let arg2 = args[1].clone();
        Ok(match (arg1, arg2) {
            (Const::Str(s), Const::Int(n)) => Const::Str(s.repeat(n as usize)),
            _ => Err(anyhow::anyhow!("Expected a string and an integer"))?,
        })
    }
);

builtin!(
    SUBSTR,
    Type::function([Type::Str, Type::Int, Type::Int], Type::Str),
    "Get a substring of a string",
    "Take a string, a start index, and an end index and return the substring.",
    |args| {
        let arg1 = args[0].clone();
        let arg2 = args[1].clone();
        let arg3 = args[2].clone();
        Ok(match (arg1, arg2, arg3) {
            (Const::Str(s), Const::Int(start), Const::Int(end)) => Const::Str(
                s.get(start as usize..end as usize)
                    .unwrap_or("")
                    .to_string(),
            ),
            _ => Err(anyhow::anyhow!("Expected a string and two integers"))?,
        })
    }
);

builtin!(
    STRREV,
    Type::function([Type::Str], Type::Str),
    "Reverse a string",
    "Take a string and return it reversed.",
    |args| {
        let arg1 = args[0].clone();
        Ok(match arg1 {
            Const::Str(s) => Const::Str(s.chars().rev().collect()),
            _ => Err(anyhow::anyhow!("Expected a string"))?,
        })
    }
);

builtin!(
    STRCAT,
    Type::function([Type::Str, Type::Str], Type::Str),
    "Concatenate two strings",
    "Take two strings and return their concatenation.",
    |args| {
        let arg1 = args[0].clone();
        let arg2 = args[1].clone();
        Ok(match (arg1, arg2) {
            (Const::Str(s1), Const::Str(s2)) => Const::Str(s1 + &s2),
            _ => Err(anyhow::anyhow!("Expected two strings"))?,
        })
    }
);

pub fn create_string_library() -> Library {
    Library::new([
        STRLEN.clone(),
        UPPER.clone(),
        LOWER.clone(),
        TRIM.clone(),
        STRSPLIT.clone(),
        JOIN.clone(),
        STRCAT.clone(),
        STRCONTAINS.clone(),
        STRREPLACE.clone(),
        STARTS_WITH.clone(),
        ENDS_WITH.clone(),
        STRREPEAT.clone(),
        SUBSTR.clone(),
        STRREV.clone(),
    ])
}
