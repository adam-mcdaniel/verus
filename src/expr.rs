use std::cell::RefCell;
use std::collections::{BTreeMap, HashMap};
use std::fmt::{Display, Formatter, Result as FmtResult};
use std::rc::Rc;
use std::sync::Arc;

use anyhow::Result;
use thiserror::Error;

#[derive(Debug, Clone, PartialEq)]
pub struct SourceCodeLocation {
    line: usize,
    column: usize,
    length: usize,
}

#[derive(Debug, Clone, PartialEq)]
pub enum Metadata {
    Many(Vec<Self>),
    Description(String),
    Location(SourceCodeLocation),
}

impl Display for Metadata {
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        match self {
            Metadata::Many(metadata) => {
                for m in metadata {
                    write!(f, "{}", m)?;
                }
                Ok(())
            }
            Metadata::Description(description) => write!(f, "{}", description),
            Metadata::Location(location) => write!(
                f,
                "line: {}, column: {}, length: {}",
                location.line, location.column, location.length
            ),
        }
    }
}

impl From<SourceCodeLocation> for Metadata {
    fn from(location: SourceCodeLocation) -> Self {
        Metadata::Location(location)
    }
}

impl From<&str> for Metadata {
    fn from(desc: &str) -> Self {
        Metadata::Description(desc.to_string())
    }
}

pub trait WithMetadata {
    fn with_metadata(self, metadata: impl Into<Metadata>) -> Self;
}

impl WithMetadata for CheckError {
    fn with_metadata(self, metadata: impl Into<Metadata>) -> Self {
        CheckError::WithMetadata(Box::new(self), metadata.into())
    }
}

impl<T> WithMetadata for Result<T, CheckError> {
    fn with_metadata(self, metadata: impl Into<Metadata>) -> Self {
        self.map_err(|e| e.with_metadata(metadata))
    }
}

#[derive(Error, Debug, Clone)]
pub enum CheckError {
    #[error("{0} ({1})")]
    WithMetadata(Box<CheckError>, Metadata),

    #[error("Mismatched types in {expr} (expected {expected}, but found {found})")]
    MismatchType {
        expected: Type,
        found: Type,
        expr: Expr,
    },

    #[error("Invalid condition in {0} (expected Bool)")]
    InvalidCondition(Const),

    #[error("Field \"{name}\" not found in {container} used in {expr}")]
    FieldNotFound {
        container: Type,
        name: Symbol,
        expr: Expr,
    },
    #[error("Variant \"{variant}\" not found in type {container} used in {expr}")]
    VariantNotFound {
        container: Type,
        variant: Symbol,
        expr: Expr,
    },

    #[error("Tried to get field \"{field}\" of non-struct type {container} used in {expr}")]
    FieldNonStruct {
        container: Type,
        field: Symbol,
        expr: Expr,
    },

    #[error("Pattern structure {0} doesn't match the provided expression {1}")]
    PatternMismatch(Pattern, Const),

    #[error("Expected constant expression, but found {0}")]
    InvalidConstant(Expr),

    #[error("Expected constant expression, but found {0}")]
    InvalidConstantValue(Const),

    #[error("{0}")]
    Custom(Arc<anyhow::Error>),

    #[error("Variable \"{name}\" not found in {expr}")]
    VariableNotFound { name: Symbol, expr: Expr },

    #[error("Type {0} not found")]
    TypeNotFound(Symbol),

    #[error("Wrong number of arguments: expected {expected}, found {found} in {expr}")]
    WrongNumberOfArguments {
        expected: usize,
        found: usize,
        expr: Expr,
    },

    #[error("Attempted to apply a non-function value {0}")]
    NotAFunction(Const),

    #[error("Unexpanded macro used in expression {0}")]
    UnexpandedMacro(Expr),

    #[error("Non-exhaustive match in {0}")]
    NonExhaustiveMatch(Expr),
}

impl CheckError {
    pub fn custom(err: anyhow::Error) -> Self {
        CheckError::Custom(Arc::new(err))
    }
}

/// A symbol is just a string.
pub type Symbol = String;

/// Our type system supports algebraic data types (enums and records) as well as some primitives.
#[derive(Clone, Debug, PartialEq)]
pub enum Type {
    /// A sum type where each variant has an associated type.
    Enum(BTreeMap<Symbol, Box<Type>>),
    /// A product type (record/struct) mapping field names to types.
    Record(BTreeMap<Symbol, Box<Type>>),
    /// A homogeneous list type.
    List(Box<Type>),
    Str,
    Char,
    Bool,
    Int,
    Float,
    Void,
    /// A named type.
    Name(Symbol),
}

impl Type {
    pub fn name(name: impl ToString) -> Self {
        Type::Name(name.to_string())
    }

    pub fn record(fields: impl IntoIterator<Item = (Symbol, Type)>) -> Self {
        let map = fields
            .into_iter()
            .map(|(name, ty)| (name, Box::new(ty)))
            .collect();
        Type::Record(map)
    }

    pub fn enum_variants(variants: impl IntoIterator<Item = (Symbol, Type)>) -> Self {
        let map = variants
            .into_iter()
            .map(|(name, ty)| (name, Box::new(ty)))
            .collect();
        Type::Enum(map)
    }
}

impl Display for Type {
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        use Type::*;
        match self {
            Enum(map) => {
                write!(f, "enum {{")?;
                for (i, (name, ty)) in map.iter().enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "{}: {}", name, ty)?;
                }
                write!(f, "}}")
            }
            Record(map) => {
                write!(f, "{{")?;
                for (i, (name, ty)) in map.iter().enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "{}: {}", name, ty)?;
                }
                write!(f, "}}")
            }
            List(ty) => write!(f, "[{}]", ty),
            Str => write!(f, "String"),
            Char => write!(f, "Char"),
            Bool => write!(f, "Bool"),
            Int => write!(f, "Int"),
            Float => write!(f, "Float"),
            Void => write!(f, "Void"),
            Name(name) => write!(f, "{}", name),
        }
    }
}

/// A built–in function that can be called from our STLC expressions.
#[derive(Clone, Debug, PartialEq)]
pub struct Builtin {
    pub name: Symbol,
    pub help_short: String,
    pub help_long: String,
    // Builtins take a vector of evaluated constant arguments and return a constant result.
    pub exec: fn(args: Vec<Const>) -> Result<Const, CheckError>,
}

/// A macro that transforms an expression before type–checking. (The implementation here is just a placeholder.)
#[derive(Clone, Debug, PartialEq)]
pub struct Macro {
    pub name: Symbol,
    pub help_short: String,
    pub help_long: String,
    pub transform: fn(expr: Expr) -> Expr,
}

/// Patterns for use in let–bindings or match expressions.
#[derive(Clone, Debug, PartialEq)]
pub enum Pattern {
    /// A variable pattern that binds the matched value.
    Var(Symbol),
    /// Destructures a record mapping field names to variables.
    Record(BTreeMap<Symbol, Symbol>),
    /// Destructures an enum variant. The inner pattern matches the value contained in the variant.
    Variant(Symbol, Box<Pattern>),
    /// Matches a nonempty list by splitting head and tail.
    List {
        head: Box<Pattern>,
        tail: Box<Pattern>,
    },
    /// Matches a constant.
    Const(Const),
}

impl Pattern {
    pub fn var(name: impl ToString) -> Self {
        Pattern::Var(name.to_string())
    }

    pub fn record(fields: BTreeMap<Symbol, Symbol>) -> Self {
        Pattern::Record(fields)
    }

    pub fn variant(name: impl ToString, inner: Pattern) -> Self {
        Pattern::Variant(name.to_string(), Box::new(inner))
    }

    pub fn list(head: Pattern, tail: Pattern) -> Self {
        Pattern::List {
            head: Box::new(head),
            tail: Box::new(tail),
        }
    }
}

impl Display for Pattern {
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        use Pattern::*;
        match self {
            Var(name) => write!(f, "{}", name),
            Record(map) => {
                write!(f, "{{")?;
                for (i, (name, var)) in map.iter().enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "{}: {}", name, var)?;
                }
                write!(f, "}}")
            }
            Variant(name, inner) => write!(f, "of {}({})", name, inner),
            List { head, tail } => write!(f, "[{} | {}]", head, tail),
            Const(c) => write!(f, "{}", c),
        }
    }
}

/// Constant values in our language. We now include closures and builtins as constants.
#[derive(Clone, Debug, PartialEq)]
pub enum Const {
    List(Vec<Const>),
    Int(i64),
    Float(f64),
    Str(String),
    Char(char),
    Bool(bool),
    Record(BTreeMap<Symbol, Const>),
    Variant(Type, Symbol, Box<Const>),
    Void,
    Closure(Vec<(Symbol, Type)>, Box<Expr>, Rc<RefCell<EvalEnv>>),
    Builtin(Builtin),
}

impl Const {
    pub fn record<T>(fields: impl IntoIterator<Item = (T, Const)>) -> Self
    where
        T: Into<Symbol>,
    {
        let mut map = BTreeMap::new();
        for (name, val) in fields {
            map.insert(name.into(), val);
        }
        Const::Record(map)
    }

    pub fn variant(typ: Type, name: impl Into<Symbol>, inner: Const) -> Self {
        Const::Variant(typ, name.into(), Box::new(inner))
    }
}

impl Display for Const {
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        use Const::*;
        match self {
            Int(n) => write!(f, "{}", n),
            Float(n) => write!(f, "{}", n),
            Str(s) => write!(f, "{:?}", s),
            Char(c) => write!(f, "{:?}", c),
            Bool(b) => write!(f, "{}", b),
            Void => write!(f, "void"),
            Record(map) => {
                write!(f, "{{")?;
                for (i, (name, val)) in map.iter().enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "{}: {}", name, val)?;
                }
                write!(f, "}}")
            }
            Variant(typ, name, inner) => {
                write!(f, "{} of {}({})", typ, name, inner)
            }
            List(list) => {
                write!(f, "[")?;
                for (i, v) in list.iter().enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "{}", v)?;
                }
                write!(f, "]")
            }
            Closure(_, _, _) => write!(f, "<closure>"),
            Builtin(builtin) => write!(f, "<builtin: {}>", builtin.name),
        }
    }
}

/// The core expression language.
#[derive(Clone, Debug, PartialEq)]
pub enum Expr {
    Annotated(Metadata, Box<Self>),

    Const(Const),
    Record(BTreeMap<Symbol, Expr>),
    Variant(Type, Symbol, Box<Expr>),
    List(Vec<Expr>),

    /// A type annotation (ignored at runtime)
    Type(Symbol, Type),
    /// Let–binding: let pattern : Type = val in body
    Let {
        var: Pattern,
        ty: Option<Type>,
        val: Box<Expr>,
        body: Box<Expr>,
    },
    /// Application: function applied to zero or more arguments.
    App(Box<Expr>, Vec<Expr>),
    /// A lambda abstraction with a list of (argument name, type) pairs.
    Lam(Vec<(Symbol, Type)>, Box<Expr>),
    /// A variable reference.
    Var(Symbol),
    /// A builtin function.
    Builtin(Builtin),
    /// A macro (should be expanded before evaluation).
    Macro(Macro),

    /// Pattern matching: match expr { pat => expr, ... }
    Match(Box<Expr>, Vec<(Pattern, Box<Expr>)>),
    /// If expression.
    If(Box<Expr>, Box<Expr>, Box<Expr>),

    /// A block of expressions evaluated sequentially.
    Many(Vec<Expr>),
}

impl Expr {
    pub const VOID: Expr = Expr::Const(Const::Void);

    pub fn var(name: impl ToString) -> Expr {
        Expr::Var(name.to_string())
    }

    pub fn let_var(
        var: Pattern,
        ty: Option<Type>,
        val: impl Into<Expr>,
        body: impl Into<Expr>,
    ) -> Expr {
        Expr::Let {
            var,
            ty,
            val: Box::new(val.into()),
            body: Box::new(body.into()),
        }
    }

    /// Strip annotations recursively.
    pub fn strip_annotations(&self) -> &Self {
        match self {
            Self::Annotated(_, expr) => expr.strip_annotations(),
            _ => self,
        }
    }

    pub fn list(exprs: impl IntoIterator<Item = Expr>) -> Expr {
        let exprs_vec: Vec<Expr> = exprs.into_iter().collect();
        Expr::List(exprs_vec)
    }

    pub fn many(exprs: impl IntoIterator<Item = Expr>) -> Expr {
        let exprs_vec: Vec<Expr> = exprs.into_iter().collect();
        if exprs_vec.is_empty() {
            // Return void if no expressions are provided.
            Expr::Const(Const::Void)
        } else {
            Expr::Many(exprs_vec)
        }
    }
}

impl Display for Expr {
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        match self {
            Expr::Const(c) => write!(f, "{}", c),
            Expr::Var(sym) => write!(f, "{}", sym),
            Expr::Lam(params, body) => {
                write!(f, "\\")?;
                for (i, (name, ty)) in params.iter().enumerate() {
                    if i > 0 {
                        write!(f, " ")?;
                    }
                    write!(f, "{}: {}", name, ty)?;
                }
                write!(f, ". {}", body)
            }
            Expr::App(func_expr, args_exprs) => {
                write!(f, "{}(", func_expr)?;
                for (i, arg) in args_exprs.iter().enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "{}", arg)?;
                }
                write!(f, ")")
            }
            _ => unimplemented!(),
        }
    }
}

/// Environment for type–checking. (Not used in evaluation.)
pub struct CheckEnv {
    pub vars: HashMap<Symbol, Type>,
    pub macros: HashMap<Symbol, Macro>,
    pub builtins: HashMap<Symbol, Builtin>,
}

/// Environment for evaluation.
#[derive(Clone, Default, Debug, PartialEq)]
pub struct EvalEnv {
    pub vars: HashMap<Symbol, Const>,
    pub builtins: HashMap<Symbol, Builtin>,
}

impl EvalEnv {
    pub fn new() -> Self {
        Self::default()
    }
}

/// Try to match a pattern against a constant value and, if successful, return a binding of variable names to constants.
fn match_pattern(pattern: &Pattern, value: &Const) -> Result<HashMap<Symbol, Const>, CheckError> {
    let mut bindings = HashMap::new();
    match (pattern, value) {
        (Pattern::Var(sym), v) => {
            bindings.insert(sym.clone(), v.clone());
            Ok(bindings)
        }
        (Pattern::Const(c), v) => {
            if c == v {
                Ok(bindings)
            } else {
                Err(CheckError::PatternMismatch(pattern.clone(), v.clone()))
            }
        }
        (Pattern::Record(pat_map), Const::Record(val_map)) => {
            for (key, var_name) in pat_map {
                if let Some(val) = val_map.get(key) {
                    bindings.insert(var_name.clone(), val.clone());
                } else {
                    return Err(CheckError::PatternMismatch(pattern.clone(), value.clone()));
                }
            }
            Ok(bindings)
        }
        (Pattern::Variant(variant_name, inner_pat), Const::Variant(_, name, inner_val)) => {
            if variant_name == name {
                let inner_bindings = match_pattern(inner_pat, inner_val)?;
                bindings.extend(inner_bindings);
                Ok(bindings)
            } else {
                Err(CheckError::PatternMismatch(pattern.clone(), value.clone()))
            }
        }
        (Pattern::List { head, tail }, Const::List(list)) => {
            if list.is_empty() {
                return Err(CheckError::PatternMismatch(pattern.clone(), value.clone()));
            }
            let head_val = &list[0];
            let tail_val = Const::List(list[1..].to_vec());
            let head_bindings = match_pattern(head, head_val)?;
            let tail_bindings = match_pattern(tail, &tail_val)?;
            bindings.extend(head_bindings);
            bindings.extend(tail_bindings);
            Ok(bindings)
        }
        _ => Err(CheckError::PatternMismatch(pattern.clone(), value.clone())),
    }
}

/// Evaluate an expression in the given evaluation environment, producing a constant.
impl Expr {
    pub fn eval(&self, env: Rc<RefCell<EvalEnv>>) -> Result<Const, CheckError> {
        match self {
            Expr::Annotated(metadata, expr) => {
                // Evaluate the inner expression and attach metadata to the result.
                expr.strip_annotations()
                    .eval(env)
                    .with_metadata(metadata.clone())
            }
            Expr::List(exprs) => {
                let mut list = Vec::new();
                for expr in exprs {
                    list.push(expr.eval(env.clone())?);
                }
                Ok(Const::List(list))
            }
            Expr::Const(c) => Ok(c.clone()),
            Expr::Var(sym) => {
                let env_ref = env.borrow();
                env_ref
                    .vars
                    .get(sym)
                    .cloned()
                    .or_else(|| env_ref.builtins.get(sym).map(|b| Const::Builtin(b.clone())))
                    .ok_or_else(|| CheckError::VariableNotFound {
                        name: sym.clone(),
                        expr: self.clone(),
                    })
            }
            Expr::Lam(params, body) => {
                // Capture the current environment in the closure.
                Ok(Const::Closure(params.clone(), body.clone(), env))
            }
            Expr::App(func_expr, args_exprs) => {
                let func = func_expr.eval(env.clone())?;
                let mut args = Vec::new();
                for arg_expr in args_exprs {
                    args.push(arg_expr.eval(env.clone())?);
                }
                apply_function(func, args)
            }
            Expr::Let {
                var,
                ty: _ty,
                val,
                body,
            } => {
                let val_evaluated = val.eval(env.clone())?;
                let bindings = match_pattern(var, &val_evaluated)?;
                let mut new_env = env.borrow().clone();
                new_env.vars.extend(bindings);
                let new_env = Rc::new(RefCell::new(new_env));
                body.eval(new_env)
            }
            Expr::Record(fields) => {
                let mut rec = BTreeMap::new();
                for (k, expr) in fields {
                    rec.insert(k.clone(), expr.eval(env.clone())?);
                }
                Ok(Const::Record(rec))
            }
            Expr::Variant(typ, variant_name, inner_expr) => {
                let inner_val = inner_expr.eval(env)?;
                Ok(Const::Variant(
                    typ.clone(),
                    variant_name.clone(),
                    Box::new(inner_val),
                ))
            }
            Expr::Builtin(builtin) => Ok(Const::Builtin(builtin.clone())),
            Expr::Macro(_m) => Err(CheckError::UnexpandedMacro(self.clone())),
            Expr::Match(expr, arms) => {
                let scrutinee = expr.eval(env.clone())?;
                for (pat, arm_expr) in arms {
                    if let Ok(bindings) = match_pattern(pat, &scrutinee) {
                        let mut new_env = env.borrow().clone();
                        new_env.vars.extend(bindings);
                        let new_env = Rc::new(RefCell::new(new_env));
                        return arm_expr.eval(new_env);
                    }
                }
                Err(CheckError::NonExhaustiveMatch(self.clone()))
            }
            Expr::If(cond, then_expr, else_expr) => {
                let cond_val = cond.eval(env.clone())?;
                match cond_val {
                    Const::Bool(true) => then_expr.eval(env),
                    Const::Bool(false) => else_expr.eval(env),
                    _ => Err(CheckError::InvalidCondition(cond_val)),
                }
            }
            Expr::Many(exprs) => {
                let mut last = Const::Void;
                for expr in exprs {
                    last = expr.eval(env.clone())?;
                }
                Ok(last)
            }
            Expr::Type(_, _) => Ok(Const::Void),
        }
    }
}

/// Apply a function constant (either a closure or a builtin) to the given arguments.
fn apply_function(func: Const, args: Vec<Const>) -> Result<Const, CheckError> {
    match &func {
        Const::Closure(params, body, closure_env) => {
            if args.len() != params.len() {
                return Err(CheckError::WrongNumberOfArguments {
                    expected: params.len(),
                    found: args.len(),
                    expr: Expr::App(
                        Box::new(func.into()),
                        args.into_iter().map(Expr::Const).collect(),
                    ),
                });
            }
            let mut new_env_map = closure_env.borrow().vars.clone();
            for ((param_name, _param_ty), arg) in params.iter().zip(args.into_iter()) {
                new_env_map.insert(param_name.clone(), arg);
            }
            let new_env = Rc::new(RefCell::new(EvalEnv {
                vars: new_env_map,
                builtins: closure_env.borrow().builtins.clone(),
            }));
            body.eval(new_env)
        }
        Const::Builtin(builtin) => (builtin.exec)(args),
        _ => Err(CheckError::NotAFunction(func)),
    }
}

impl From<Const> for Expr {
    fn from(c: Const) -> Self {
        Expr::Const(c)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use anyhow::anyhow;

    /// Example of a builtin function: addition.
    fn builtin_add(args: Vec<Const>) -> Result<Const, CheckError> {
        if args.len() != 2 {
            return Err(CheckError::custom(anyhow!("add expects two arguments")));
        }
        match (&args[0], &args[1]) {
            (Const::Int(a), Const::Int(b)) => Ok(Const::Int(a + b)),
            _ => Err(CheckError::custom(anyhow!("add expects integer arguments"))),
        }
    }

    #[test]
    fn test_add_builtin() {
        let add_builtin = Builtin {
            name: "add".to_string(),
            help_short: "Adds two integers".to_string(),
            help_long: "Usage: add x y, where x and y are integers".to_string(),
            exec: builtin_add,
        };

        let env = Rc::new(RefCell::new(EvalEnv {
            vars: HashMap::new(),
            builtins: {
                let mut map = HashMap::new();
                map.insert("add".to_string(), add_builtin.clone());
                map
            },
        }));

        // Represent the expression: add(2, 3)
        let expr = Expr::App(
            Box::new(Expr::Builtin(add_builtin)),
            vec![Expr::Const(Const::Int(2)), Expr::Const(Const::Int(3))],
        );

        let result = expr.eval(env).unwrap();
        match result {
            Const::Int(n) => assert_eq!(n, 5),
            _ => panic!("Expected integer result"),
        }
    }

    /// Test let–binding using a record pattern.
    #[test]
    fn test_let_record_pattern() {
        let add_builtin = Builtin {
            name: "add".to_string(),
            help_short: "Adds two integers".to_string(),
            help_long: "Usage: add x y".to_string(),
            exec: builtin_add,
        };

        // let { x: a, y: b } : { x: Int, y: Int } = { x = 1, y = 2 } in add(a, b)
        let let_expr = Expr::Let {
            var: Pattern::Record({
                let mut map = BTreeMap::new();
                map.insert("x".to_string(), "a".to_string());
                map.insert("y".to_string(), "b".to_string());
                map
            }),
            ty: Some(Type::Record({
                let mut map = BTreeMap::new();
                map.insert("x".to_string(), Box::new(Type::Int));
                map.insert("y".to_string(), Box::new(Type::Int));
                map
            })),
            val: Box::new(Expr::Record({
                let mut map = BTreeMap::new();
                map.insert("x".to_string(), Expr::Const(Const::Int(1)));
                map.insert("y".to_string(), Expr::Const(Const::Int(2)));
                map
            })),
            body: Box::new(Expr::App(
                Box::new(Expr::Builtin(add_builtin.clone())),
                vec![Expr::Var("a".to_string()), Expr::Var("b".to_string())],
            )),
        };

        let env = Rc::new(RefCell::new(EvalEnv {
            vars: HashMap::new(),
            builtins: {
                let mut map = HashMap::new();
                map.insert("add".to_string(), add_builtin.clone());
                map
            },
        }));

        let result = let_expr.eval(env).unwrap();
        match result {
            Const::Int(n) => assert_eq!(n, 3),
            _ => panic!("Expected integer result from record destructuring"),
        }
    }

    /// Test let–binding using a variant pattern.
    #[test]
    fn test_let_variant_pattern() {
        let option_type = Type::Enum({
            let mut map = BTreeMap::new();
            map.insert("Some".to_string(), Box::new(Type::Int));
            map.insert("None".to_string(), Box::new(Type::Void));
            map
        });
        // let Some(x) : Option = Some(42) in x
        let let_expr = Expr::Let {
            var: Pattern::Variant("Some".to_string(), Box::new(Pattern::Var("x".to_string()))),
            ty: Some(option_type.clone()),
            val: Box::new(Expr::Variant(
                option_type,
                "Some".to_string(),
                Box::new(Expr::Const(Const::Int(42))),
            )),
            body: Box::new(Expr::Var("x".to_string())),
        };

        let env = Rc::new(RefCell::new(EvalEnv {
            vars: HashMap::new(),
            builtins: HashMap::new(),
        }));

        let result = let_expr.eval(env).unwrap();
        match result {
            Const::Int(n) => assert_eq!(n, 42),
            _ => panic!("Expected integer result from variant destructuring"),
        }
    }

    /// Test that pattern destructuring fails if the value does not match the pattern.
    #[test]
    fn test_let_pattern_failure() {
        let let_expr = Expr::Let {
            var: Pattern::Record({
                let mut map = BTreeMap::new();
                map.insert("x".to_string(), "a".to_string());
                map.insert("y".to_string(), "b".to_string());
                map
            }),
            ty: Some(Type::Record({
                let mut map = BTreeMap::new();
                map.insert("x".to_string(), Box::new(Type::Int));
                map.insert("y".to_string(), Box::new(Type::Int));
                map
            })),
            // The record value only provides "x".
            val: Box::new(Expr::Record({
                let mut map = BTreeMap::new();
                map.insert("x".to_string(), Expr::Const(Const::Int(1)));
                map
            })),
            body: Box::new(Expr::Const(Const::Int(0))),
        };

        let env = Rc::new(RefCell::new(EvalEnv {
            vars: HashMap::new(),
            builtins: HashMap::new(),
        }));

        let result = let_expr.eval(env);
        match &result {
            Ok(val) => println!("Unexpected success: {}", val),
            Err(e) => println!("Expected error: {}", e),
        }
        assert!(
            result.is_err(),
            "Expected pattern match to fail due to missing field"
        );
    }

    /// Test a match expression on a variant (Option–like type)
    #[test]
    fn test_match_variant_expression() {
        let option_type = Type::Enum({
            let mut map = BTreeMap::new();
            map.insert("Some".to_string(), Box::new(Type::Int));
            map.insert("None".to_string(), Box::new(Type::Void));
            map
        });

        // match Some(42) with
        //   Some(x) => x
        //   None(default) => 0
        let match_expr = Expr::Match(
            Box::new(Expr::Variant(
                option_type.clone(),
                "Some".to_string(),
                Box::new(Expr::Const(Const::Int(42))),
            )),
            vec![
                (
                    Pattern::Variant("Some".to_string(), Box::new(Pattern::Var("x".to_string()))),
                    Box::new(Expr::Var("x".to_string())),
                ),
                (
                    Pattern::Variant(
                        "None".to_string(),
                        Box::new(Pattern::Var("default".to_string())),
                    ),
                    Box::new(Expr::Const(Const::Int(0))),
                ),
            ],
        );

        let env = Rc::new(RefCell::new(EvalEnv {
            vars: HashMap::new(),
            builtins: HashMap::new(),
        }));

        let result = match_expr.eval(env).unwrap();
        match result {
            Const::Int(n) => assert_eq!(n, 42),
            _ => panic!("Expected integer result from match expression"),
        }
    }

    /// Test a match expression on a variant, matching the "None" branch.
    #[test]
    fn test_match_variant_expression2() {
        let option_type = Type::Enum({
            let mut map = BTreeMap::new();
            map.insert("Some".to_string(), Box::new(Type::Int));
            map.insert("None".to_string(), Box::new(Type::Void));
            map
        });

        // match None with
        //   Some(x) => x
        //   None(default) => 0
        let match_expr = Expr::Match(
            Box::new(Expr::Variant(
                option_type.clone(),
                "None".to_string(),
                Box::new(Expr::Const(Const::Void)),
            )),
            vec![
                (
                    Pattern::Variant("Some".to_string(), Box::new(Pattern::Var("x".to_string()))),
                    Box::new(Expr::Var("x".to_string())),
                ),
                (
                    Pattern::Variant(
                        "None".to_string(),
                        Box::new(Pattern::Var("default".to_string())),
                    ),
                    Box::new(Expr::Const(Const::Int(0))),
                ),
            ],
        );

        let env = Rc::new(RefCell::new(EvalEnv {
            vars: HashMap::new(),
            builtins: HashMap::new(),
        }));

        let result = match_expr.eval(env).unwrap();
        match result {
            Const::Int(n) => assert_eq!(n, 0),
            _ => panic!("Expected integer result from match expression"),
        }
    }
}
