use core::f64;
use std::cell::RefCell;
use std::collections::{BTreeMap, BTreeSet, HashMap};
use std::fmt::{Display, Formatter, Result as FmtResult};
use std::rc::Rc;
use std::str::FromStr;
use std::sync::Arc;

use anyhow::Result;
use thiserror::Error;

use tracing::*;

#[derive(Debug, Clone, PartialEq, PartialOrd, Eq, Ord)]
pub struct SourceCodeLocation {
    line: usize,
    column: usize,
    length: usize,
}

#[derive(Debug, Clone, PartialEq, PartialOrd, Eq, Ord)]
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

    #[error("Bad cast in {expr} from type {from} to {to}")]
    BadCast {
        from: Type,
        to: Type,
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

    #[error("Pattern type {0} doesn't match the provided type {1}")]
    PatternMismatchType(Pattern, Type),

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

    #[error("Ambiguous type in {0} (found {1})")]
    AmbiguousType(Expr, Type),

    #[error("Index out of bounds: {index} in {expr} (length: {length})")]
    IndexOutOfBounds {
        index: usize,
        length: usize,
        expr: Expr,
    },
}

impl From<anyhow::Error> for CheckError {
    fn from(err: anyhow::Error) -> Self {
        CheckError::Custom(Arc::new(err))
    }
}

impl CheckError {
    pub fn custom(err: anyhow::Error) -> Self {
        CheckError::Custom(Arc::new(err))
    }
}

/// A symbol is just a string.
pub type Symbol = String;

/// Our type system supports algebraic data types (enums and records) as well as some primitives.
#[derive(Clone, Debug, PartialOrd, Ord, Eq, Hash)]
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
    /// A signed integer type.
    Int,
    /// A floating–point type.
    Float,
    /// A number type that can be either an integer or a float.
    Number,
    /// A type that represents no value.
    Void,
    /// A type that matches anything.
    /// Reserved for builtin and internal use.
    Any,
    /// A type that matches one of several types.
    /// Reserved for builtin and internal use.
    OneOf(BTreeSet<Type>),

    Function {
        arg_types: Vec<Type>,
        return_type: Box<Type>,
    },
    /// A named type.
    Name(Symbol),
}

impl Type {
    pub fn name(name: impl ToString) -> Self {
        Type::Name(name.to_string())
    }

    pub fn list(ty: Type) -> Self {
        Type::List(Box::new(ty))
    }

    pub fn one_of(tys: impl IntoIterator<Item = Type>) -> Self {
        let tys_vec: BTreeSet<Type> = tys.into_iter().collect();
        Type::OneOf(tys_vec)
    }

    pub fn number() -> Self {
        // Type::one_of([Type::Int, Type::Float])
        Type::Number
    }

    pub fn is_ambiguous(&self) -> bool {
        match self {
            Type::Any => true,
            Type::OneOf(tys) => tys.len() > 1,
            Type::List(ty) => ty.is_ambiguous(),
            Type::Record(fields) => fields.values().any(|ty| ty.is_ambiguous()),
            Type::Enum(fields) => fields.values().any(|ty| ty.is_ambiguous()),
            _ => false,
        }
    }

    pub fn can_cast_to(&self, other: &Type) -> bool {
        if self == other {
            return true;
        }
        match (self, other) {
            (Type::Any, _) => true,
            (_, Type::Any) => true,
            (Type::OneOf(tys), _) => tys.contains(other),
            (_, Type::OneOf(tys)) => tys.contains(self),
            (Type::List(a), Type::List(b)) => a.can_cast_to(b),
            (
                Type::Function {
                    arg_types: a_arg_types,
                    return_type: a_return_type,
                },
                Type::Function {
                    arg_types: b_arg_types,
                    return_type: b_return_type,
                },
            ) => {
                if a_arg_types.len() != b_arg_types.len() {
                    return false;
                }
                for (a, b) in a_arg_types.iter().zip(b_arg_types.iter()) {
                    if !a.can_cast_to(b) {
                        return false;
                    }
                }
                a_return_type.can_cast_to(b_return_type)
            }
            (Type::Record(a), Type::Record(b)) => {
                for (name, ty) in a {
                    if let Some(other_ty) = b.get(name) {
                        if !ty.can_cast_to(other_ty) {
                            return false;
                        }
                    } else {
                        return false;
                    }
                }
                true
            }
            (Type::Int, Type::Float) => true,
            (Type::Float, Type::Int) => true,

            (Type::Str, Type::Char) => true,
            (Type::Char, Type::Str) => true,

            (Type::Bool, Type::Int) => true,
            (Type::Int, Type::Bool) => true,

            (Type::Number, Type::Str) => true,
            (Type::Str, Type::Number) => true,
            (Type::Number, Type::Char) => true,
            (Type::Char, Type::Number) => true,

            (Type::Int, Type::Number) => true,
            (Type::Float, Type::Number) => true,
            (Type::Number, Type::Int) => true,
            (Type::Number, Type::Float) => true,
            
            _ => false,
        }
    }

    pub fn can_be_used_as(&self, other: &Type) -> bool {
        if self == other {
            return true;
        }
        match (self, other) {
            (Type::Any, _) => true,
            (_, Type::Any) => true,
            (Type::OneOf(tys), _) => tys.contains(other),
            (_, Type::OneOf(tys)) => tys.contains(self),
            (Type::List(a), Type::List(b)) => a.can_be_used_as(b),
            (
                Type::Function {
                    arg_types: a_arg_types,
                    return_type: a_return_type,
                },
                Type::Function {
                    arg_types: b_arg_types,
                    return_type: b_return_type,
                },
            ) => {
                if a_arg_types.len() != b_arg_types.len() {
                    return false;
                }
                for (a, b) in a_arg_types.iter().zip(b_arg_types.iter()) {
                    if !a.can_be_used_as(b) {
                        return false;
                    }
                }
                a_return_type.can_be_used_as(b_return_type)
            }
            (Type::Record(a), Type::Record(b)) => {
                for (name, ty) in a {
                    if let Some(other_ty) = b.get(name) {
                        if !ty.can_be_used_as(other_ty) {
                            return false;
                        }
                    } else {
                        return false;
                    }
                }
                true
            }
            (Type::Int, Type::Number) => true,
            (Type::Float, Type::Number) => true,
            (Type::Number, Type::Int) => true,
            (Type::Number, Type::Float) => true,
            _ => false,
        }
    }

    pub fn is_function(&self) -> bool {
        matches!(self, Type::Function { .. })
            || matches!(self, Type::OneOf(tys) if tys.iter().any(|t| t.is_function()))
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

    pub fn function(arg_types: impl IntoIterator<Item = Type>, return_type: Type) -> Self {
        Type::Function {
            arg_types: arg_types.into_iter().collect(),
            return_type: Box::new(return_type),
        }
    }
}

impl FromStr for Type {
    type Err = String;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        crate::parse_type(s)
    }
}

impl From<&str> for Type {
    fn from(s: &str) -> Self {
        s.parse().unwrap()
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
            Any => write!(f, "Any"),
            OneOf(tys) => {
                write!(f, "OneOf(")?;
                for (i, ty) in tys.iter().enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "{}", ty)?;
                }
                write!(f, ")")
            }
            List(ty) => write!(f, "[{}]", ty),
            Str => write!(f, "Str"),
            Char => write!(f, "Char"),
            Bool => write!(f, "Bool"),
            Int => write!(f, "Int"),
            Float => write!(f, "Float"),
            Number => write!(f, "Num"),
            Void => write!(f, "Void"),
            Function {
                arg_types,
                return_type,
            } => {
                write!(f, "(")?;
                for (i, arg_type) in arg_types.iter().enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "{}", arg_type)?;
                }
                write!(f, ") -> {}", return_type)
            }
            Name(name) => write!(f, "{}", name),
        }
    }
}

impl PartialEq for Type {
    fn eq(&self, other: &Self) -> bool {
        use Type::*;
        match (self, other) {
            (Any, _) => true,
            (_, Any) => true,
            (Enum(a), Enum(b)) => a == b,
            (Record(a), Record(b)) => a == b,
            (List(a), List(b)) => a == b,
            (Str, Str) => true,
            (Char, Char) => true,
            (Bool, Bool) => true,
            (Int, Int) => true,
            (Float, Float) => true,
            (Void, Void) => true,
            (Number, Number) => true,
            (
                Function {
                    arg_types: a_arg_types,
                    return_type: a_return_type,
                },
                Function {
                    arg_types: b_arg_types,
                    return_type: b_return_type,
                },
            ) => a_arg_types == b_arg_types && a_return_type == b_return_type,
            (OneOf(a), OneOf(b)) => a == b,
            (OneOf(a), b) => a.contains(b),
            (a, OneOf(b)) => b.contains(a),
            (Name(a), Name(b)) => a == b,
            _ => false,
        }
    }
}

/// A built–in function that can be called from our STLC expressions.
#[derive(Clone, Debug, PartialEq, PartialOrd, Eq)]
pub struct Builtin {
    pub name: Symbol,
    pub help_short: String,
    pub help_long: String,
    pub ty: Type,
    // Builtins take a vector of evaluated constant arguments and return a constant result.
    pub exec: fn(args: Vec<Const>) -> Result<Const, CheckError>,
}

impl Builtin {
    pub fn new(
        name: impl ToString,
        ty: impl Into<Type>,
        help_short: impl ToString,
        help_long: impl ToString,
        exec: fn(args: Vec<Const>) -> Result<Const, CheckError>,
    ) -> Self {
        Builtin {
            name: name.to_string(),
            help_short: help_short.to_string(),
            help_long: help_long.to_string(),
            ty: ty.into(),
            exec,
        }
    }

    pub fn get_type(&self) -> Type {
        self.ty.clone()
    }
}

/// A macro that transforms an expression before type–checking. (The implementation here is just a placeholder.)
#[derive(Debug, Clone, PartialEq, PartialOrd, Eq, Ord)]
pub struct Macro {
    pub name: Symbol,
    pub help_short: String,
    pub help_long: String,
    pub transform: fn(expr: Expr) -> Expr,
}

/// Patterns for use in let–bindings or match expressions.
#[derive(Clone, Debug, PartialEq, PartialOrd)]
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

impl From<&str> for Pattern {
    fn from(s: &str) -> Self {
        Pattern::Var(s.to_string())
    }
}

impl From<String> for Pattern {
    fn from(s: String) -> Self {
        Pattern::Var(s)
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
#[derive(Clone, Debug)]
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

    pub fn get_type(&self) -> Type {
        match self {
            Const::Int(_) => Type::number(),
            Const::Float(_) => Type::number(),
            Const::Str(_) => Type::Str,
            Const::Char(_) => Type::Char,
            Const::Bool(_) => Type::Bool,
            Const::Record(map) => {
                let mut fields = BTreeMap::new();
                for (name, val) in map {
                    fields.insert(name.clone(), Box::new(val.get_type()));
                }
                Type::Record(fields)
            }
            Const::List(elems) => {
                let mut elem_ty: Option<Type> = None;
                for elem in elems {
                    let ty = elem.get_type();
                    if let Some(existing) = &elem_ty {
                        if !ty.can_be_used_as(&existing) {
                            elem_ty = Some(Type::Any);
                        }
                    } else {
                        elem_ty = Some(ty);
                    }
                }
                Type::List(Box::new(elem_ty.unwrap_or(Type::Any)))
            }
            Const::Variant(typ, _, _) => typ.clone(),
            Const::Void => Type::Void,
            Const::Closure(_, _, _) => Type::Void,
            Const::Builtin(b) => b.get_type(),
        }
    }
}

impl From<bool> for Const {
    fn from(b: bool) -> Self {
        Const::Bool(b)
    }
}

impl From<i64> for Const {
    fn from(i: i64) -> Self {
        Const::Int(i)
    }
}

impl From<f64> for Const {
    fn from(f: f64) -> Self {
        Const::Float(f)
    }
}

impl From<String> for Const {
    fn from(s: String) -> Self {
        Const::Str(s)
    }
}

impl From<char> for Const {
    fn from(c: char) -> Self {
        Const::Char(c)
    }
}

impl From<Vec<Const>> for Const {
    fn from(list: Vec<Const>) -> Self {
        Const::List(list)
    }
}

impl From<BTreeMap<Symbol, Const>> for Const {
    fn from(map: BTreeMap<Symbol, Const>) -> Self {
        Const::Record(map)
    }
}

impl From<i32> for Const {
    fn from(i: i32) -> Self {
        Const::Int(i as i64)
    }
}

impl From<Builtin> for Const {
    fn from(b: Builtin) -> Self {
        Const::Builtin(b)
    }
}

impl PartialEq for Const {
    fn eq(&self, other: &Self) -> bool {
        use Const::*;
        match (self, other) {
            (Int(a), Int(b)) => a == b,
            (Float(a), Float(b)) => a == b,
            (Int(a), Float(b)) => (*a as f64) == *b,
            (Float(a), Int(b)) => *a == (*b as f64),
            (Str(a), Str(b)) => a == b,
            (Char(a), Char(b)) => a == b,
            (Bool(a), Bool(b)) => a == b,
            (Void, Void) => true,
            (Record(a), Record(b)) => a == b,
            (Variant(typ_a, name_a, inner_a), Variant(typ_b, name_b, inner_b)) => {
                typ_a == typ_b && name_a == name_b && inner_a == inner_b
            }
            (Builtin(a), Builtin(b)) => a == b,
            (Closure(_, _, _), Closure(_, _, _)) => false,
            (List(a), List(b)) => a == b,
            _ => false,
        }
    }
}

impl PartialOrd for Const {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        use Const::*;

        match (self, other) {
            (Int(a), Int(b)) => a.partial_cmp(b),
            (Float(a), Float(b)) => a.partial_cmp(b),
            (Int(a), Float(b)) => (*a as f64).partial_cmp(b),
            (Float(a), Int(b)) => a.partial_cmp(&(*b as f64)),

            (Str(a), Str(b)) => a.partial_cmp(b),
            (Char(a), Char(b)) => a.partial_cmp(b),
            (Bool(a), Bool(b)) => a.partial_cmp(b),
            (Void, Void) => Some(std::cmp::Ordering::Equal),
            (Record(a), Record(b)) => a.partial_cmp(b),
            (Variant(typ_a, name_a, inner_a), Variant(typ_b, name_b, inner_b)) => {
                if typ_a == typ_b && name_a == name_b {
                    inner_a.partial_cmp(inner_b)
                } else {
                    None
                }
            }
            (Builtin(a), Builtin(b)) => a.partial_cmp(b),
            (Closure(_, _, _), Closure(_, _, _)) => None,
            (List(a), List(b)) => a.partial_cmp(b),
            _ => None,
        }
    }
}

impl Display for Const {
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        use Const::*;
        match self {
            Int(n) => write!(f, "{}", n),
            Float(n) => write!(f, "{}", n),
            Str(s) => write!(f, "{}", s),
            Char(c) => write!(f, "{}", c),
            Bool(b) => write!(f, "{}", b),
            Void => write!(f, "()"),
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
#[derive(Clone, Debug, PartialEq, PartialOrd)]
pub enum Expr {
    Annotated(Metadata, Box<Self>),

    Const(Const),
    Record(BTreeMap<Symbol, Expr>),
    Variant(Type, Symbol, Box<Expr>),
    List(Vec<Expr>),

    Get {
        container: Box<Expr>,
        field: Box<Expr>,
    },

    /// A type–annotated expression.
    As(Box<Expr>, Type),

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

    pub fn app(&self, args: impl IntoIterator<Item = Expr>) -> Expr {
        let args_vec: Vec<Expr> = args.into_iter().collect();
        Expr::App(Box::new(self.clone()), args_vec)
    }

    pub fn check(&self, env: &mut CheckEnv) -> Result<Type, CheckError> {
        let result = match self {
            Expr::Get { container, field } => {
                // If the container is a list, confirm that the field is an index.
                let container_ty = container.check(env)?;
                match &container_ty {
                    Type::List(elem_ty) => {
                        let field_ty = field.check(env)?;
                        if !field_ty.can_cast_to(&Type::Int) {
                            return Err(CheckError::MismatchType {
                                expected: Type::Int,
                                found: field_ty,
                                expr: self.clone(),
                            });
                        }
                        Ok(*elem_ty.clone())
                    }
                    Type::Record(fields) => {
                        // Get the field as a symbol
                        match &**field {
                            Expr::Var(name) => {
                                if let Some(ty) = fields.get(name) {
                                    Ok((**ty).clone())
                                } else {
                                    Err(CheckError::FieldNotFound {
                                        container: container_ty,
                                        name: name.clone(),
                                        expr: self.clone(),
                                    })
                                }
                            }
                            _ => Err(CheckError::FieldNotFound {
                                container: container_ty,
                                name: field.to_string(),
                                expr: self.clone(),
                            }),
                        }
                    }
                    _ => Err(CheckError::FieldNonStruct {
                        container: container_ty,
                        field: field.check(env)?.to_string(),
                        expr: self.clone(),
                    }),
                }
            }

            Expr::Annotated(_, expr) => expr.check(env),
            Expr::Const(c) => Ok(c.get_type()),
            Expr::Var(sym) => env.get_var(sym),
            Expr::Lam(params, body) => {
                let mut new_env = env.clone();

                for (name, ty) in params {
                    new_env.vars.insert(name.clone(), ty.clone());
                }
                let body_ty = body.check(&mut new_env)?;

                for (_, ty) in params {
                    env.check_if_type_exists(ty)?;
                }
                env.check_if_type_exists(&body_ty)?;

                Ok(Type::Function {
                    arg_types: params.iter().map(|(_, ty)| ty.clone()).collect(),
                    return_type: Box::new(body_ty),
                })
            }
            Expr::App(func_expr, args_exprs) => {
                let func_ty = func_expr.check(env)?;
                let found_arg_types: Vec<_> = args_exprs
                    .iter()
                    .map(|arg| arg.check(env))
                    .collect::<Result<_, _>>()?;
                env.check_if_type_exists(&func_ty)?;
                for ty in &found_arg_types {
                    env.check_if_type_exists(ty)?;
                }
                match func_ty {
                    Type::Function {
                        arg_types: param_types,
                        return_type,
                    } => {
                        if param_types.len() != found_arg_types.len() {
                            return Err(CheckError::WrongNumberOfArguments {
                                expected: param_types.len(),
                                found: found_arg_types.len(),
                                expr: self.clone(),
                            });
                        }
                        for (expected, found) in param_types.iter().zip(found_arg_types.iter()) {
                            env.check_if_type_exists(expected)?;

                            if !found.can_be_used_as(expected) {
                                return Err(CheckError::MismatchType {
                                    expected: expected.clone(),
                                    found: found.clone(),
                                    expr: self.clone(),
                                });
                            }
                        }
                        Ok(*return_type)
                    }
                    _ => Err(CheckError::MismatchType {
                        expected: Type::Function {
                            arg_types: vec![],
                            return_type: Box::new(Type::Void),
                        },
                        found: func_ty,
                        expr: self.clone(),
                    }),
                }
            }
            Expr::Let { var, ty, val, body } => {
                let val_ty = val.check(env)?;
                if let Some(expected_ty) = ty {
                    let expected_ty = env.simplify_type(expected_ty);
                    env.check_if_type_exists(&expected_ty)?;

                    if !val_ty.can_be_used_as(&expected_ty) {
                        return Err(CheckError::MismatchType {
                            expected: expected_ty.clone(),
                            found: val_ty,
                            expr: self.clone(),
                        });
                    }
                } else {
                    if val_ty.is_ambiguous() {
                        return Err(CheckError::AmbiguousType(*val.clone(), val_ty.clone()));
                    }
                }

                let bindings = match_pattern_types(var, &env.simplify_type(&val_ty))?;

                if **body == Expr::VOID {
                    env.vars.extend(bindings);
                    body.check(env)
                } else {
                    let mut new_env = env.clone();
                    new_env.vars.extend(bindings);
                    let body_ty = body.check(&mut new_env)?;
                    Ok(body_ty)
                }
            }
            Expr::Record(fields) => {
                let mut field_map = BTreeMap::new();
                for (k, v) in fields {
                    field_map.insert(k.clone(), v.check(env)?.into());
                }
                Ok(Type::Record(field_map))
            }
            Expr::Variant(typ, variant_name, inner_expr) => {
                // Confirm that the variant and the given data match
                let typ = env.simplify_type(typ);
                env.check_if_type_exists(&typ)?;
                let inner_ty = inner_expr.check(env)?;
                if let Type::Enum(variants) = &typ {
                    if !variants.contains_key(variant_name) {
                        return Err(CheckError::VariantNotFound {
                            container: typ.clone(),
                            variant: variant_name.clone(),
                            expr: self.clone(),
                        });
                    }
                    let expected_inner_ty = variants.get(variant_name).unwrap();
                    if !inner_ty.can_be_used_as(expected_inner_ty) {
                        return Err(CheckError::MismatchType {
                            expected: *expected_inner_ty.clone(),
                            found: inner_ty,
                            expr: self.clone(),
                        });
                    }
                } else {
                    return Err(CheckError::VariantNotFound {
                        container: typ.clone(),
                        variant: variant_name.clone(),
                        expr: self.clone(),
                    });
                }
                Ok(typ)
            }
            Expr::List(exprs) => {
                let mut elem_ty: Option<Type> = None;
                for expr in exprs {
                    let ty = expr.check(env)?;
                    if let Some(existing_ty) = &elem_ty {
                        if !ty.can_be_used_as(existing_ty) {
                            return Err(CheckError::MismatchType {
                                expected: existing_ty.clone(),
                                found: ty,
                                expr: self.clone(),
                            });
                        }
                    } else {
                        elem_ty = Some(ty);
                    }
                }
                println!("elem_ty: {:?}", elem_ty);
                Ok(Type::List(Box::new(elem_ty.unwrap_or(Type::Void))))
            }
            Expr::Builtin(builtin) => Ok(builtin.get_type()),
            Expr::Macro(_) => Err(CheckError::UnexpandedMacro(self.clone())),
            Expr::Match(scrutinee, arms) => {
                let scrutinee_ty = scrutinee.check(env)?;
                let mut arm_tys = Vec::new();
                for (pat, arm_expr) in arms {
                    let pat_ty = match_pattern_types(pat, &scrutinee_ty)?;
                    env.vars.extend(pat_ty);
                    arm_tys.push(arm_expr.check(env)?);
                }
                if arm_tys.is_empty() {
                    return Err(CheckError::NonExhaustiveMatch(self.clone()));
                }
                let first_arm_ty = arm_tys[0].clone();
                for ty in &arm_tys[1..] {
                    if !ty.can_be_used_as(&first_arm_ty) {
                        return Err(CheckError::MismatchType {
                            expected: first_arm_ty.clone(),
                            found: ty.clone(),
                            expr: self.clone(),
                        });
                    }
                }
                Ok(first_arm_ty)
            }
            Expr::If(cond, then_expr, else_expr) => {
                let cond_ty = cond.check(env)?;
                if cond_ty != Type::Bool {
                    return Err(CheckError::InvalidCondition(Const::Bool(false)));
                }
                let then_ty = then_expr.check(env)?;
                let else_ty = else_expr.check(env)?;
                if then_ty != else_ty {
                    return Err(CheckError::MismatchType {
                        expected: then_ty,
                        found: else_ty,
                        expr: self.clone(),
                    });
                }
                Ok(then_ty)
            }
            Expr::Many(exprs) => {
                let mut last_ty = Type::Void;
                let old_env = env.clone();
                for expr in exprs {
                    last_ty = expr.check(env)?;
                }
                env.vars = old_env.vars;
                Ok(last_ty)
            }
            Expr::Type(name, ty) => {
                env.check_if_type_exists(ty)?;
                env.types.insert(name.clone(), ty.clone());
                Ok(Type::Name(name.clone()))
            }
            Expr::As(expr, ty) => {
                env.check_if_type_exists(ty)?;

                let expr_ty = expr.check(env)?;
                if !expr_ty.can_cast_to(ty) {
                    return Err(CheckError::BadCast {
                        from: expr_ty,
                        to: ty.clone(),
                        expr: self.clone(),
                    });
                }
                Ok(ty.clone())
            }
        }?;
        // debug!("check: {} => {:?}", self, result);

        Ok(env.simplify_type(&result))
    }
}

impl From<Const> for Expr {
    fn from(c: Const) -> Self {
        Expr::Const(c)
    }
}

impl From<Builtin> for Expr {
    fn from(b: Builtin) -> Self {
        Expr::Builtin(b)
    }
}

impl Display for Expr {
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        match self {
            Expr::Get { container, field } => {
                write!(f, "{}@{}", container, field)
            }
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
            Expr::Let { var, val, body, .. } => {
                write!(f, "let {} = {} in {}", var, val, body)
            }
            Expr::Record(fields) => {
                write!(f, "{{")?;
                for (i, (name, val)) in fields.iter().enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "{}: {}", name, val)?;
                }
                write!(f, "}}")
            }
            Expr::As(expr, ty) => write!(f, "{} as {}", expr, ty),
            Expr::Variant(typ, name, inner_expr) => {
                write!(f, "{} of {}({})", typ, name, inner_expr)
            }
            Expr::List(exprs) => {
                write!(f, "[")?;
                for (i, v) in exprs.iter().enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "{}", v)?;
                }
                write!(f, "]")
            }
            Expr::Builtin(builtin) => write!(f, "<builtin: {}>", builtin.name),
            Expr::Macro(macro_) => write!(f, "<macro: {}>", macro_.name),
            Expr::Match(scrutinee, arms) => {
                write!(f, "match {} {{", scrutinee)?;
                for (i, (pat, arm_expr)) in arms.iter().enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "{} => {}", pat, arm_expr)?;
                }
                write!(f, "}}")
            }
            Expr::If(cond, then_expr, else_expr) => {
                write!(f, "if {} then {} else {}", cond, then_expr, else_expr)
            }
            Expr::Many(exprs) => {
                write!(f, "{{")?;
                for (i, expr) in exprs.iter().enumerate() {
                    if i > 0 {
                        write!(f, "; ")?;
                    }
                    write!(f, "{}", expr)?;
                }
                write!(f, "}}")
            }
            Expr::Annotated(_metadata, expr) => {
                write!(f, "{}", expr)
            }
            Expr::Type(name, ty) => {
                write!(f, "type {} = {}", name, ty)
            }
        }
    }
}

/// Environment for type–checking. (Not used in evaluation.)
#[derive(Clone, Default, Debug, PartialEq)]
pub struct CheckEnv {
    pub vars: HashMap<Symbol, Type>,
    pub types: HashMap<Symbol, Type>,
    pub macros: HashMap<Symbol, Macro>,
    pub builtins: HashMap<Symbol, Builtin>,
}

impl CheckEnv {
    pub fn new() -> Self {
        CheckEnv {
            vars: HashMap::new(),
            types: HashMap::new(),
            macros: HashMap::new(),
            builtins: HashMap::new(),
        }
    }

    pub fn check_if_type_exists(&self, ty: &Type) -> Result<(), CheckError> {
        use Type::*;
        match ty {
            Name(name) => {
                if self.types.contains_key(name) {
                    Ok(())
                } else {
                    Err(CheckError::TypeNotFound(name.clone()))
                }
            }
            Record(fields) => {
                for (_, field_ty) in fields {
                    self.check_if_type_exists(field_ty)?;
                }
                Ok(())
            }
            Enum(variants) => {
                for (_, variant_ty) in variants {
                    self.check_if_type_exists(variant_ty)?;
                }
                Ok(())
            }
            OneOf(tys) => {
                for ty in tys {
                    self.check_if_type_exists(ty)?;
                }
                Ok(())
            }
            List(ty) => self.check_if_type_exists(ty),
            Any | Str | Char | Bool | Int | Float | Number | Void => Ok(()),
            Function {
                arg_types,
                return_type,
            } => {
                for arg_ty in arg_types {
                    self.check_if_type_exists(arg_ty)?;
                }
                self.check_if_type_exists(return_type)
            }
        }
    }

    pub fn get_type(&self, name: &Symbol) -> Result<Type, CheckError> {
        self.types
            .get(name)
            .cloned()
            .ok_or(CheckError::TypeNotFound(name.clone()))
    }

    pub fn get_var(&self, name: &Symbol) -> Result<Type, CheckError> {
        self.vars
            .get(name)
            .cloned()
            .ok_or(CheckError::VariableNotFound {
                name: name.clone(),
                expr: Expr::Var(name.clone()),
            })
    }

    pub fn get_builtin(&self, name: &Symbol) -> Result<Builtin, CheckError> {
        self.builtins
            .get(name)
            .cloned()
            .ok_or(CheckError::VariableNotFound {
                name: name.clone(),
                expr: Expr::Var(name.clone()),
            })
    }

    pub fn check(&mut self, expr: &Expr) -> Result<Type, CheckError> {
        self.collect_type_definitions(expr)?;
        println!("types: {:?}", self.types);
        let ty = expr.check(self)?;
        self.check_if_type_exists(&ty)?;
        Ok(self.simplify_type(&ty))
    }

    pub fn simplify_type(&self, ty: &Type) -> Type {
        match ty {
            Type::Name(name) => self
                .types
                .get(name)
                .cloned()
                .ok_or_else(|| CheckError::TypeNotFound(name.clone()))
                .unwrap_or_else(|_| ty.clone()),
            Type::Record(fields) => {
                let mut new_fields = BTreeMap::new();
                for (name, field_ty) in fields {
                    new_fields.insert(name.clone(), Box::new(self.simplify_type(field_ty)));
                }
                Type::Record(new_fields)
            }
            Type::Enum(variants) => {
                let mut new_variants = BTreeMap::new();
                for (name, variant_ty) in variants {
                    new_variants.insert(name.clone(), Box::new(self.simplify_type(variant_ty)));
                }
                Type::Enum(new_variants)
            }
            Type::OneOf(tys) => {
                let new_tys: Vec<_> = tys.iter().map(|t| self.simplify_type(t)).collect();
                Type::one_of(new_tys)
            }
            Type::List(ty) => Type::List(Box::new(self.simplify_type(ty))),
            Type::Any
            | Type::Str
            | Type::Char
            | Type::Bool
            | Type::Int
            | Type::Float
            | Type::Number
            | Type::Void => ty.clone(),
            Type::Function {
                arg_types,
                return_type,
            } => Type::Function {
                arg_types: arg_types.iter().map(|t| self.simplify_type(t)).collect(),
                return_type: Box::new(self.simplify_type(return_type)),
            },
        }
    }

    pub fn collect_type_definitions(&mut self, expr: &Expr) -> Result<(), CheckError> {
        match expr {
            Expr::Get { container, field } => {
                self.collect_type_definitions(container)?;
                self.collect_type_definitions(field)?;
            }
            Expr::Type(name, ty) => {
                // Define a type named `name` with the given type `ty`.
                self.types.insert(name.clone(), ty.clone());
            }
            Expr::Let { val, body, .. } => {
                self.collect_type_definitions(val)?;
                self.collect_type_definitions(body)?;
            }
            Expr::As(expr, _ty) => {
                self.collect_type_definitions(expr)?;
            }
            Expr::Lam(params, body) => {
                for (_, param_ty) in params {
                    self.collect_type_definitions(&Expr::Type(
                        param_ty.to_string(),
                        param_ty.clone(),
                    ))?;
                }
                self.collect_type_definitions(body)?;
            }
            Expr::App(func_expr, args_exprs) => {
                self.collect_type_definitions(func_expr)?;
                for arg in args_exprs {
                    self.collect_type_definitions(arg)?;
                }
            }
            Expr::Record(fields) => {
                for (_, field_expr) in fields {
                    self.collect_type_definitions(field_expr)?;
                }
            }
            Expr::Variant(_, _, inner_expr) => {
                self.collect_type_definitions(inner_expr)?;
            }
            Expr::List(exprs) => {
                for expr in exprs {
                    self.collect_type_definitions(expr)?;
                }
            }
            Expr::Many(exprs) => {
                for expr in exprs {
                    self.collect_type_definitions(expr)?;
                }
            }
            Expr::Match(scrutinee, arms) => {
                self.collect_type_definitions(scrutinee)?;
                for (pat, arm_expr) in arms {
                    self.collect_type_definitions(arm_expr)?;
                    match pat {
                        Pattern::Record(fields) => {
                            for (_, var_name) in fields {
                                self.collect_type_definitions(&Expr::Type(
                                    var_name.clone(),
                                    Type::Void,
                                ))?;
                            }
                        }
                        Pattern::Variant(_, inner_pat) => {
                            self.collect_type_definitions(&Expr::Type(
                                inner_pat.to_string(),
                                Type::Void,
                            ))?;
                        }
                        _ => {}
                    }
                }
            }
            Expr::If(cond, then_expr, else_expr) => {
                self.collect_type_definitions(cond)?;
                self.collect_type_definitions(then_expr)?;
                self.collect_type_definitions(else_expr)?;
            }
            Expr::Annotated(_, expr) => {
                self.collect_type_definitions(expr)?;
            }
            Expr::Macro(_) => {
                // Macros are not expanded here, so we don't collect type definitions from them.
            }
            Expr::Var(_) | Expr::Builtin(_) | Expr::Const(_) => {
                // No type definitions to collect from variables or builtins.
            }
        }
        Ok(())
    }
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

/// Try to match a pattern against a constant value and, if successful, return a binding of variable names to constants.
fn match_pattern_types(
    pattern: &Pattern,
    value: &Type,
) -> Result<HashMap<Symbol, Type>, CheckError> {
    // debug!("match_pattern_types: {:?} against {:?}", pattern, value);
    let mut bindings = HashMap::new();
    match (pattern, value) {
        (Pattern::Var(sym), v) => {
            bindings.insert(sym.clone(), v.clone());
            Ok(bindings)
        }
        (Pattern::Const(c), v) => {
            if c.get_type().can_be_used_as(v) {
                Ok(bindings)
            } else {
                Err(CheckError::PatternMismatchType(pattern.clone(), v.clone()))
            }
        }
        (Pattern::Record(pat_map), Type::Record(val_map)) => {
            if pat_map.len() != val_map.len() {
                return Err(CheckError::PatternMismatchType(
                    pattern.clone(),
                    value.clone(),
                ));
            }

            for (key, var_name) in pat_map {
                if let Some(val) = val_map.get(key) {
                    bindings.insert(var_name.clone(), *val.clone());
                } else {
                    return Err(CheckError::PatternMismatchType(
                        pattern.clone(),
                        value.clone(),
                    ));
                }
            }
            Ok(bindings)
        }
        (Pattern::Variant(variant_name, inner_pat), Type::Enum(variants)) => {
            if let Some(inner_ty) = variants.get(variant_name) {
                let inner_bindings = match_pattern_types(inner_pat, inner_ty)?;
                bindings.extend(inner_bindings);
                Ok(bindings)
            } else {
                Err(CheckError::PatternMismatchType(
                    pattern.clone(),
                    value.clone(),
                ))
            }
        }
        (Pattern::List { head, tail }, Type::List(list)) => {
            // if list.is_empty() {
            //     return Err(CheckError::PatternMismatch(pattern.clone(), value.clone()));
            // }
            let head_bindings = match_pattern_types(head, list)?;
            let tail_bindings = match_pattern_types(tail, value)?;
            bindings.extend(head_bindings);
            bindings.extend(tail_bindings);
            Ok(bindings)
        }
        _ => Err(CheckError::PatternMismatchType(
            pattern.clone(),
            value.clone(),
        )),
    }
}

/// Evaluate an expression in the given evaluation environment, producing a constant.
impl Expr {
    pub fn get(&self, field: impl Into<Expr>) -> Expr {
        Expr::Get {
            container: Box::new(self.clone()),
            field: Box::new(field.into()),
        }
    }

    pub fn eval(&self, env: Rc<RefCell<EvalEnv>>) -> Result<Const, CheckError> {
        match self {
            Expr::Get { container, field } => {
                let container_val = container.eval(env.clone())?;
                match container_val {
                    Const::Record(fields) => {
                        if let Some(val) = fields.get(&field.to_string()) {
                            Ok(val.clone())
                        } else {
                            Err(anyhow::anyhow!("Invalid index: {}", field.to_string()))?
                        }
                    }
                    Const::List(list) => match field.eval(env.clone())? {
                        Const::Int(index) => {
                            let index = index as usize;
                            if index < list.len() {
                                Ok(list[index].clone())
                            } else {
                                Err(CheckError::IndexOutOfBounds {
                                    index,
                                    length: list.len(),
                                    expr: self.clone(),
                                })
                            }
                        }
                        _ => Err(anyhow::anyhow!("Invalid index: {}", field.to_string()))?,
                    },
                    _ => Err(CheckError::FieldNonStruct {
                        container: container_val.get_type(),
                        field: field.to_string(),
                        expr: self.clone(),
                    }),
                }
            }
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
            Expr::As(expr, desired_ty) => {
                let result = expr.eval(env.clone())?;
                let found_ty = result.get_type();
                if !found_ty.can_cast_to(desired_ty) {
                    return Err(CheckError::BadCast {
                        to: desired_ty.clone(),
                        from: found_ty,
                        expr: self.clone(),
                    });
                }

                match (&found_ty, desired_ty) {
                    (Type::Int, Type::Float) => {
                        if let Const::Int(i) = result {
                            Ok(Const::Float(i as f64))
                        } else {
                            Err(CheckError::BadCast {
                                to: desired_ty.clone(),
                                from: found_ty,
                                expr: self.clone(),
                            })
                        }
                    }
                    (Type::Float, Type::Int) => {
                        if let Const::Float(f) = result {
                            Ok(Const::Int(f as i64))
                        } else {
                            Err(CheckError::BadCast {
                                to: desired_ty.clone(),
                                from: found_ty,
                                expr: self.clone(),
                            })
                        }
                    }
                    (Type::Str, Type::Number) => {
                        if let Const::Str(s) = result {
                            // First try integer
                            if let Ok(i) = s.parse::<i64>() {
                                Ok(Const::Int(i))
                            } else if let Ok(f) = s.parse::<f64>() {
                                Ok(Const::Float(f))
                            } else {
                                Ok(Const::Float(f64::NAN))
                            }
                        } else {
                            Err(CheckError::BadCast {
                                to: desired_ty.clone(),
                                from: found_ty,
                                expr: self.clone(),
                            })
                        }
                    }
                    (Type::Number, Type::Str) => {
                        if let Const::Int(i) = result {
                            Ok(Const::Str(i.to_string()))
                        } else if let Const::Float(f) = result {
                            Ok(Const::Str(f.to_string()))
                        } else {
                            Err(CheckError::BadCast {
                                to: desired_ty.clone(),
                                from: found_ty,
                                expr: self.clone(),
                            })
                        }
                    }

                    (Type::Char, Type::Str) => {
                        if let Const::Char(c) = result {
                            Ok(Const::Str(c.to_string()))
                        } else {
                            Err(CheckError::BadCast {
                                to: desired_ty.clone(),
                                from: found_ty,
                                expr: self.clone(),
                            })
                        }
                    }
                    (Type::Str, Type::Char) => {
                        if let Const::Str(s) = result {
                            if s.len() == 1 {
                                Ok(Const::Char(s.chars().next().unwrap()))
                            } else {
                                Ok(Const::Char('\0'))
                            }
                        } else {
                            Err(CheckError::BadCast {
                                to: desired_ty.clone(),
                                from: found_ty,
                                expr: self.clone(),
                            })
                        }
                    }
                    _ => {
                        Ok(result)
                    }
                }
            }
            Expr::Lam(params, body) => {
                // Remove any of the parameters from the environment.
                let mut env_map = env.borrow().vars.clone();
                for (name, _) in params {
                    env_map.remove(name);
                }
                let env = Rc::new(RefCell::new(EvalEnv {
                    vars: env_map,
                    builtins: env.borrow().builtins.clone(),
                }));

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
                if **body == Expr::VOID {
                    // Create a new environment with the bindings from the pattern match.
                    env.borrow_mut().vars.extend(bindings);
                    // Evaluate the body in the new environment.
                    body.eval(env.clone())
                } else {
                    let mut new_env = env.borrow().clone();
                    new_env.vars.extend(bindings);
                    let new_env = Rc::new(RefCell::new(new_env));
                    body.eval(new_env)
                }
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
                let old_env_vars = env.borrow().vars.clone();
                for expr in exprs {
                    last = expr.eval(env.clone())?;
                }
                // Restore the original environment.
                env.borrow_mut().vars = old_env_vars;
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
            ty: Type::function([Type::Int, Type::Int], Type::Int),
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
            ty: Type::function([Type::Int, Type::Int], Type::Int),
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
