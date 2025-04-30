use super::*;

builtin!(
    DEBUG,
    Type::function([Type::Any], Type::Void),
    "Debug a value",
    "Take a value and print it to the console as debug output.",
    |args| {
        let arg1 = args[0].clone();
        debug!("{}", arg1);
        Ok(Const::Void)
    }
);

builtin!(
    INFO,
    Type::function([Type::Any], Type::Void),
    "Info a value",
    "Take a value and print it to the console as info output.",
    |args| {
        let arg1 = args[0].clone();
        info!("{}", arg1);
        Ok(Const::Void)
    }
);

builtin!(
    WARN,
    Type::function([Type::Any], Type::Void),
    "Warn a value",
    "Take a value and print it to the console as warning output.",
    |args| {
        let arg1 = args[0].clone();
        warn!("{}", arg1);
        Ok(Const::Void)
    }
);

builtin!(
    ERROR,
    Type::function([Type::Any], Type::Void),
    "Error a value",
    "Take a value and print it to the console as error output.",
    |args| {
        let arg1 = args[0].clone();
        error!("{}", arg1);
        Ok(Const::Void)
    }
);

builtin!(
    HELP,
    Type::function([Type::Any], Type::Void),
    "Get help for a function",
    "Take a function name and print its documentation.",
    |args| {
        let arg1 = args[0].clone();
        Ok(match arg1 {
            Const::Builtin(f) => {
                println!("{}: {}\n\n{}", f.name, f.help_short, f.help_long);
                Const::Void
            }
            _ => Err(anyhow::anyhow!("Expected a builtin function"))?,
        })
    }
);

builtin!(
    PRINT,
    Type::function([Type::Any], Type::Void),
    "Print a value",
    "Take a value and print it to the console.",
    |args| {
        let arg1 = args[0].clone();
        println!("{}", arg1);
        Ok(Const::Void)
    }
);

builtin!(
    PRINTLN,
    Type::function([Type::Any], Type::Void),
    "Print a value with a newline",
    "Take a value and print it to the console with a newline.",
    |args| {
        let arg1 = args[0].clone();
        println!("{}", arg1);
        Ok(Const::Void)
    }
);

builtin!(
    INPUT,
    Type::function([], Type::Str),
    "Read input from the console",
    "Read a line of input from the console and return it as a string.",
    |_| {
        let mut input = String::new();
        std::io::stdin().read_line(&mut input).unwrap();
        Ok(Const::Str(input.trim().to_string()))
    }
);

builtin!(
    SLEEP,
    Type::function([Type::Int], Type::Void),
    "Sleep for a specified number of milliseconds",
    "Take an integer and sleep for that many milliseconds.",
    |args| {
        let arg1 = args[0].clone();
        Ok(match arg1 {
            Const::Int(ms) => {
                std::thread::sleep(std::time::Duration::from_millis(ms as u64));
                Const::Void
            }
            _ => Err(anyhow::anyhow!("Expected an integer"))?,
        })
    }
);

builtin!(
    TIME,
    Type::function([], Type::Int),
    "Get the current time in milliseconds since the epoch",
    "Return the current time in milliseconds since the Unix epoch.",
    |_| {
        let now = std::time::SystemTime::now();
        let duration = now.duration_since(std::time::UNIX_EPOCH).unwrap();
        Ok(Const::Int(duration.as_millis() as i64))
    }
);

builtin!(
    RAND,
    Type::function([], Type::Int),
    "Generate a random integer",
    "Return a random integer.",
    |_| {
        use rand::prelude::*;
        let mut rng = rand::rng();
        let random_number = rng.random::<i64>();
        Ok(Const::Int(random_number as i64))
    }
);

builtin!(
    RAND_FLOAT,
    Type::function([], Type::Float),
    "Generate a random float",
    "Return a random float.",
    |_| {
        use rand::prelude::*;
        let mut rng = rand::rng();
        let random_number = rng.random::<f64>();
        Ok(Const::Float(random_number))
    }
);

builtin!(
    FREAD,
    Type::function([Type::Str], Type::Str),
    "Read a file",
    "Take a file path and return its contents as a string.",
    |args| {
        let arg1 = args[0].clone();
        Ok(match arg1 {
            Const::Str(path) => {
                let contents = std::fs::read_to_string(path).map_err(|e| anyhow::anyhow!(e))?;
                Const::Str(contents)
            }
            _ => Err(anyhow::anyhow!("Expected a string"))?,
        })
    }
);

builtin!(
    FWRITE,
    Type::function([Type::Str, Type::Str], Type::Void),
    "Write to a file",
    "Take a file path and a string, and write the string to the file.",
    |args| {
        let arg1 = args[0].clone();
        let arg2 = args[1].clone();
        Ok(match (arg1, arg2) {
            (Const::Str(path), Const::Str(contents)) => {
                std::fs::write(path, contents).map_err(|e| anyhow::anyhow!(e))?;
                Const::Void
            }
            _ => Err(anyhow::anyhow!("Expected two strings"))?,
        })
    }
);

builtin!(
    FAPPEND,
    Type::function([Type::Str, Type::Str], Type::Void),
    "Append to a file",
    "Take a file path and a string, and append the string to the file.",
    |args| {
        let arg1 = args[0].clone();
        let arg2 = args[1].clone();
        Ok(match (arg1, arg2) {
            (Const::Str(path), Const::Str(contents)) => {
                use std::io::Write;
                let mut file = std::fs::OpenOptions::new()
                    .append(true)
                    .open(path)
                    .map_err(|e| anyhow::anyhow!(e))?;
                writeln!(file, "{}", contents).map_err(|e| anyhow::anyhow!(e))?;
                Const::Void
            }
            _ => Err(anyhow::anyhow!("Expected two strings"))?,
        })
    }
);

builtin!(
    ARGS,
    Type::function([Type::Void], Type::list(Type::Str)),
    "Get the passed arguments",
    "Return the arguments passed to the program as a list of strings.",
    |args| {
        let arg1 = args[0].clone();
        Ok(match arg1 {
            Const::Void => {
                let args: Vec<String> = std::env::args().skip(1).collect();
                Const::List(args.into_iter().map(Const::Str).collect())
            }
            _ => Err(anyhow::anyhow!("Expected void"))?,
        })
    }
);

pub fn create_io_library() -> Library {
    Library::new([
        DEBUG.clone(),
        INFO.clone(),
        WARN.clone(),
        ERROR.clone(),
        HELP.clone(),
        PRINT.clone(),
        PRINTLN.clone(),
        INPUT.clone(),
        SLEEP.clone(),
        TIME.clone(),
        RAND.clone(),
        RAND_FLOAT.clone(),
        FREAD.clone(),
        FWRITE.clone(),
        FAPPEND.clone(),
        ARGS.clone(),
    ])
}
