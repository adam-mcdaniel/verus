use super::*;

builtin!(
    APPEND,
    Type::function([Type::list(Type::Any), Type::Any], Type::list(Type::Any)),
    "Append an element to a list",
    "Take a list and an element and return a new list with the element appended.",
    |args| {
        let arg1 = args[0].clone();
        let arg2 = args[1].clone();
        Ok(match arg1 {
            Const::List(mut list) => {
                list.push(arg2);
                Const::List(list)
            }
            _ => Err(anyhow::anyhow!("Expected a list"))?,
        })
    }
);

builtin!(
    PREPEND,
    Type::function([Type::Any, Type::list(Type::Any)], Type::list(Type::Any)),
    "Prepend an element to a list",
    "Take an element and a list and return a new list with the element prepended.",
    |args| {
        let arg1 = args[0].clone();
        let arg2 = args[1].clone();
        Ok(match arg2 {
            Const::List(mut list) => {
                list.insert(0, arg1);
                Const::List(list)
            }
            _ => Err(anyhow::anyhow!("Expected a list"))?,
        })
    }
);

builtin!(
    REV,
    Type::function([Type::list(Type::Any)], Type::list(Type::Any)),
    "Reverse a list",
    "Take a list and return a new list with the elements in reverse order.",
    |args| {
        let arg1 = args[0].clone();
        Ok(match arg1 {
            Const::List(list) => {
                let mut reversed = list.clone();
                reversed.reverse();
                Const::List(reversed)
            }
            _ => Err(anyhow::anyhow!("Expected a list"))?,
        })
    }
);

builtin!(
    LEN,
    Type::function([Type::list(Type::Any)], Type::Int),
    "Get the length of a list",
    "Take a list and return its length.",
    |args| {
        let arg1 = args[0].clone();
        Ok(match arg1 {
            Const::List(list) => Const::Int(list.len() as i64),
            _ => Err(anyhow::anyhow!("Expected a list"))?,
        })
    }
);

builtin!(
    HEAD,
    Type::function([Type::list(Type::Any)], Type::Any),
    "Get the first element of a list",
    "Take a list and return its first element.",
    |args| {
        let arg1 = args[0].clone();
        Ok(match arg1 {
            Const::List(list) => {
                if let Some(first) = list.first() {
                    first.clone()
                } else {
                    Err(anyhow::anyhow!("List is empty"))?
                }
            }
            _ => Err(anyhow::anyhow!("Expected a list"))?,
        })
    }
);

builtin!(
    TAIL,
    Type::function([Type::list(Type::Any)], Type::list(Type::Any)),
    "Get the tail of a list",
    "Take a list and return a new list with the first element removed.",
    |args| {
        let arg1 = args[0].clone();
        Ok(match arg1 {
            Const::List(mut list) => {
                if list.is_empty() {
                    Err(anyhow::anyhow!("List is empty"))?
                } else {
                    list.remove(0);
                    Const::List(list)
                }
            }
            _ => Err(anyhow::anyhow!("Expected a list"))?,
        })
    }
);

builtin!(
    MAP,
    Type::function(
        [
            Type::function([Type::Any], Type::Any),
            Type::list(Type::Any)
        ],
        Type::list(Type::Any)
    ),
    "Map a function over a list",
    "Take a function and a list and return a new list with the function applied to each element.",
    |args| {
        let func = args[0].clone();
        let list = args[1].clone();
        Ok(match list {
            Const::List(list) => {
                let mut new_list = Vec::new();
                for item in list {
                    let result = eval(Expr::from(func.clone()).app([item.into()]))?;
                    new_list.push(result);
                }
                Const::List(new_list)
            }
            _ => Err(anyhow::anyhow!("Expected a list"))?,
        })
    }
);

builtin!(
    MAPNUM,
    Type::function(
        [
            Type::function([Type::number()], Type::number()),
            Type::list(Type::Any)
        ],
        Type::list(Type::number())
    ),
    "Map a function over a list",
    "Take a function and a list and return a new list with the function applied to each element.",
    |args| {
        let func = args[0].clone();
        let list = args[1].clone();
        Ok(match list {
            Const::List(list) => {
                let mut new_list = Vec::new();
                for item in list {
                    let result = eval(Expr::from(func.clone()).app([item.into()]))?;
                    new_list.push(result);
                }
                Const::List(new_list)
            }
            _ => Err(anyhow::anyhow!("Expected a list"))?,
        })
    }
);

builtin!(
    FILTER,
    Type::function([Type::function([Type::Any], Type::Bool), Type::list(Type::Any)], Type::list(Type::Any)),
    "Filter a list by a predicate",
    "Take a predicate function and a list and return a new list with only the elements that satisfy the predicate.",
    |args| {
        let func = args[0].clone();
        let list = args[1].clone();
        Ok(match list {
            Const::List(list) => {
                let mut new_list = Vec::new();
                for item in list {
                    let result = eval(Expr::from(func.clone()).app([item.clone().into()]))?;
                    if result == Const::Bool(true) {
                        new_list.push(item);
                    }
                }
                Const::List(new_list)
            }
            _ => Err(anyhow::anyhow!("Expected a list"))?,
        })
    }
);

builtin!(
    FOLD,
    Type::function([Type::function([Type::Any, Type::Any], Type::Any), Type::Any, Type::list(Type::Any)], Type::Any),
    "Fold a list by a function",
    "Take a function, an initial value, and a list and return a new value by applying the function to each element of the list.",
    |args| {
        let func = args[0].clone();
        let init = args[1].clone();
        let list = args[2].clone();
        Ok(match list {
            Const::List(list) => {
                let mut acc = init;
                for item in list {
                    acc = eval(Expr::from(func.clone()).app([acc.into(), item.into()]))?;
                }
                acc
            }
            _ => Err(anyhow::anyhow!("Expected a list"))?,
        })
    }
);

builtin!(
    ZIP,
    Type::function(
        [Type::list(Type::Any), Type::list(Type::Any)],
        Type::list(Type::list(Type::Any))
    ),
    "Zip two lists together",
    "Take two lists and return a new list of pairs.",
    |args| {
        let list1 = args[0].clone();
        let list2 = args[1].clone();
        Ok(match (list1, list2) {
            (Const::List(list1), Const::List(list2)) => {
                let mut zipped = Vec::new();
                for (item1, item2) in list1.into_iter().zip(list2.into_iter()) {
                    zipped.push(Const::List(vec![item1, item2]));
                }
                Const::List(zipped)
            }
            _ => Err(anyhow::anyhow!("Expected two lists"))?,
        })
    }
);

pub fn create_list_library() -> Library {
    Library::new([
        APPEND.clone(),
        PREPEND.clone(),
        REV.clone(),
        LEN.clone(),
        HEAD.clone(),
        TAIL.clone(),
        MAP.clone(),
        MAPNUM.clone(),
        FILTER.clone(),
        FOLD.clone(),
        ZIP.clone(),
    ])
}
