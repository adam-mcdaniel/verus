//fn main() {
//    println!("Hello, world!");
//}

/*

Ints/strings/chars use same syntax as python
Bool: True and False
Record:  struct { x: TypeName, y: TypeName }
Variant: TypeName::EnumVariant
Void nil()
Closure / lambda x -> {x + 1}
Builtin is reserved. Certain builtin symbols like strcpy or whatever else are bound to Builtin functions internally inside the interpreter


*/


use std::iter::Peekable;
use std::str::Chars;
use std::collections::{BTreeMap, HashMap};
use std::rc::Rc;
use std::cell::RefCell;

use crate::ast::*; // Assume your AST types (Expr, Const, Type, Pattern, Builtin, etc.) are defined here.
use anyhow::anyhow;

// A simple recursive descent parser.
pub struct Parser<'a> {
    input: Peekable<Chars<'a>>,
}

impl<'a> Parser<'a> {
    /// Create a new parser from an input string.
    pub fn new(source: &'a str) -> Self {
        Parser {
            input: source.chars().peekable(),
        }
    }

    /// Skip whitespace characters.
    fn skip_whitespace(&mut self) {
        while let Some(&c) = self.input.peek() {
            if c.is_whitespace() {
                self.input.next();
            } else {
                break;
            }
        }
    }

    /// Expect a specific character and consume it.
    fn expect_char(&mut self, expected: char) -> Result<(), String> {
        self.skip_whitespace();
        match self.input.next() {
            Some(c) if c == expected => Ok(()),
            Some(c) => Err(format!("Expected '{}', found '{}'", expected, c)),
            None => Err(format!("Expected '{}', but reached end of input", expected)),
        }
    }

    /// Peek if the next characters match the given keyword.
    fn peek_keyword(&mut self, kw: &str) -> bool {
        let mut iter = self.input.clone();
        for ch in kw.chars() {
            match iter.next() {
                Some(c) if c == ch => continue,
                _ => return false,
            }
        }
        // Make sure we aren’t in the middle of a longer identifier.
        if let Some(&next) = iter.peek() {
            !(next.is_alphanumeric() || next == '_')
        } else {
            true
        }
    }

    /// Parse an identifier (starts with letter or underscore, then alphanumerics or underscores).
    fn parse_identifier(&mut self) -> Result<String, String> {
        self.skip_whitespace();
        let mut ident = String::new();
        match self.input.peek() {
            Some(&c) if c.is_alphabetic() || c == '_' => {
                ident.push(c);
                self.input.next();
            }
            _ => return Err("Identifier must start with a letter or '_'".into()),
        }
        while let Some(&c) = self.input.peek() {
            if c.is_alphanumeric() || c == '_' {
                ident.push(c);
                self.input.next();
            } else {
                break;
            }
        }
        Ok(ident)
    }

    /// Parse an integer literal.
    fn parse_number(&mut self) -> Result<Const, String> {
        self.skip_whitespace();
        let mut num_str = String::new();
        while let Some(&c) = self.input.peek() {
            if c.is_digit(10) {
                num_str.push(c);
                self.input.next();
            } else {
                break;
            }
        }
        if num_str.is_empty() {
            Err("Expected a number".into())
        } else {
            let value = num_str.parse::<i64>().map_err(|e| e.to_string())?;
            Ok(Const::Int(value))
        }
    }

    /// Parse a string literal (Python style, using double quotes).
    fn parse_string(&mut self) -> Result<Const, String> {
        self.skip_whitespace();
        self.expect_char('"')?;
        let mut s = String::new();
        while let Some(c) = self.input.next() {
            if c == '"' {
                break;
            } else {
                s.push(c);
            }
        }
        Ok(Const::Str(s))
    }

    /// Parse a character literal (using single quotes).
    fn parse_char(&mut self) -> Result<Const, String> {
        self.skip_whitespace();
        self.expect_char('\'')?;
        let c = self.input.next().ok_or("Expected a character")?;
        self.expect_char('\'')?;
        Ok(Const::Char(c))
    }

    /// Parse literal constants: integer, string, char, booleans, or the void literal.
    fn parse_literal(&mut self) -> Result<Expr, String> {
        self.skip_whitespace();
        // Check for void literal: nil or nil()
        if self.peek_keyword("nil") {
            for _ in 0.."nil".len() { self.input.next(); }
            self.skip_whitespace();
            if let Some(&'(') = self.input.peek() {
                self.input.next();
                self.skip_whitespace();
                self.expect_char(')')?;
            }
            return Ok(Expr::Const(Const::Void));
        }
        // Booleans: True and False.
        if self.peek_keyword("True") {
            for _ in 0.."True".len() { self.input.next(); }
            return Ok(Expr::Const(Const::Bool(true)));
        }
        if self.peek_keyword("False") {
            for _ in 0.."False".len() { self.input.next(); }
            return Ok(Expr::Const(Const::Bool(false)));
        }
        // Integer, string, or char literal.
        if let Some(&c) = self.input.peek() {
            if c.is_digit(10) {
                let n = self.parse_number()?;
                return Ok(Expr::Const(n));
            } else if c == '"' {
                let s = self.parse_string()?;
                return Ok(Expr::Const(s));
            } else if c == '\'' {
                let ch = self.parse_char()?;
                return Ok(Expr::Const(ch));
            }
        }
        Err("Unrecognized literal".into())
    }

    /// Parse a parenthesized expression.
    fn parse_paren_expr(&mut self) -> Result<Expr, String> {
        self.skip_whitespace();
        self.expect_char('(')?;
        let expr = self.parse_expr()?;
        self.skip_whitespace();
        self.expect_char(')')?;
        Ok(expr)
    }

    /// Parse a record literal: struct { field: expr, ... }
    fn parse_record(&mut self) -> Result<Expr, String> {
        self.skip_whitespace();
        // Consume the keyword "struct"
        let keyword = self.parse_identifier()?;
        if keyword != "struct" {
            return Err("Expected 'struct' keyword for record literal".into());
        }
        self.skip_whitespace();
        self.expect_char('{')?;
        let mut fields = BTreeMap::new();
        loop {
            self.skip_whitespace();
            if let Some(&'}') = self.input.peek() {
                self.input.next();
                break;
            }
            let field_name = self.parse_identifier()?;
            self.skip_whitespace();
            self.expect_char(':')?;
            let field_expr = self.parse_expr()?;
            fields.insert(field_name, field_expr);
            self.skip_whitespace();
            if let Some(&',') = self.input.peek() {
                self.input.next();
            }
        }
        Ok(Expr::Record(fields))
    }

    /// Parse a variant expression: TypeName::EnumVariant ( ( expr ) )?
    fn parse_variant(&mut self) -> Result<Expr, String> {
        self.skip_whitespace();
        // Parse the type name.
        let type_name = self.parse_identifier()?;
        self.skip_whitespace();
        // Expect the "::" separator.
        self.expect_char(':')?;
        self.expect_char(':')?;
        let variant_name = self.parse_identifier()?;
        self.skip_whitespace();
        // Optionally parse a payload in parentheses.
        let payload = if let Some(&'(') = self.input.peek() {
            self.input.next(); // consume '('
            let expr = self.parse_expr()?;
            self.skip_whitespace();
            self.expect_char(')')?;
            expr
        } else {
            // If no payload, use the void literal.
            Expr::Const(Const::Void)
        };
        // Create a named type for the variant.
        let ty = Type::Name(type_name);
        Ok(Expr::Variant(ty, variant_name, Box::new(payload)))
    }

    /// Parse a lambda expression (closure) of the form: x -> { expr }
    fn parse_lambda(&mut self) -> Result<Expr, String> {
        self.skip_whitespace();
        // Parse a parameter identifier.
        let param = self.parse_identifier()?;
        self.skip_whitespace();
        // Expect the arrow "->".
        if self.input.next() != Some('-') || self.input.next() != Some('>') {
            return Err("Expected '->' in lambda expression".into());
        }
        self.skip_whitespace();
        // Expect a block for the lambda body.
        self.expect_char('{')?;
        let body = self.parse_expr()?;
        self.skip_whitespace();
        self.expect_char('}')?;
        // Without type annotations, assign a default type (here we choose Void).
        let params = vec![(param, Type::Void)];
        Ok(Expr::Lam(params, Box::new(body)))
    }

    /// Parse an identifier expression; if the identifier is a reserved builtin name, produce a Builtin.
    fn parse_identifier_expr(&mut self) -> Result<Expr, String> {
        let ident = self.parse_identifier()?;
        // A simple builtin table.
        let builtins = vec!["strcpy", "print", "input"];
        if builtins.contains(&ident.as_str()) {
            let builtin = Builtin {
                name: ident.clone(),
                help_short: "".into(),
                help_long: "".into(),
                exec: |_args| Err(CheckError::Custom(std::sync::Arc::new(anyhow!("Builtin not implemented")))),
            };
            return Ok(Expr::Builtin(builtin));
        }
        Ok(Expr::Var(ident))
    }

    /// Parse a primary expression.
    fn parse_primary(&mut self) -> Result<Expr, String> {
        self.skip_whitespace();
        if let Some(&c) = self.input.peek() {
            match c {
                '(' => self.parse_paren_expr(),
                '{' => {
                    // Here we assume a block isn’t a primary expression; you could extend this.
                    Err("Unexpected block. Use 'struct { ... }' for record literals.".into())
                }
                _ => {
                    // Check for record literal (starts with "struct").
                    if self.peek_keyword("struct") {
                        return self.parse_record();
                    }
                    // Check for lambda by peeking ahead for "->".
                    let checkpoint = self.input.clone();
                    if let Ok(_id) = self.parse_identifier() {
                        self.skip_whitespace();
                        if let Some(&'-') = self.input.peek() {
                            let mut temp = self.input.clone();
                            temp.next();
                            if let Some('>') = temp.next() {
                                // It’s a lambda; reset and parse it.
                                self.input = checkpoint;
                                return self.parse_lambda();
                            }
                        }
                        // Not a lambda; reset and treat as identifier expression.
                        self.input = checkpoint;
                        self.parse_identifier_expr()
                    } else if c.is_digit(10) || c == '"' || c == '\'' {
                        self.parse_literal()
                    } else {
                        Err("Unexpected token in primary expression".into())
                    }
                }
            }
        } else {
            Err("Unexpected end of input in primary expression".into())
        }
    }

    /// Parse function application: a primary expression followed by optional arguments.
    fn parse_application(&mut self) -> Result<Expr, String> {
        let mut expr = self.parse_primary()?;
        loop {
            self.skip_whitespace();
            // If the next token is "::", it signals a variant.
            if let Some(&':') = self.input.peek() {
                expr = self.parse_variant()?;
                continue;
            }
            // If the next token is '(' then parse an argument list.
            if let Some(&'(') = self.input.peek() {
                self.expect_char('(')?;
                let mut args = Vec::new();
                self.skip_whitespace();
                if let Some(&')') = self.input.peek() {
                    self.input.next(); // empty argument list
                } else {
                    loop {
                        let arg = self.parse_expr()?;
                        args.push(arg);
                        self.skip_whitespace();
                        if let Some(&',') = self.input.peek() {
                            self.input.next();
                        } else {
                            break;
                        }
                    }
                    self.skip_whitespace();
                    self.expect_char(')')?;
                }
                expr = Expr::App(Box::new(expr), args);
                continue;
            }
            break;
        }
        Ok(expr)
    }

    /// Parse an expression.
    pub fn parse_expr(&mut self) -> Result<Expr, String> {
        self.skip_whitespace();
        self.parse_application()
    }

    /// Parse a type.
    /// For our language we support simple named types and record types.
    pub fn parse_type(&mut self) -> Result<Type, String> {
        self.skip_whitespace();
        if self.peek_keyword("struct") {
            // Parse record type: struct { field: Type, ... }
            let _ = self.parse_identifier()?; // consumes "struct"
            self.skip_whitespace();
            self.expect_char('{')?;
            let mut fields = BTreeMap::new();
            loop {
                self.skip_whitespace();
                if let Some(&'}') = self.input.peek() {
                    self.input.next();
                    break;
                }
                let field_name = self.parse_identifier()?;
                self.skip_whitespace();
                self.expect_char(':')?;
                let ty = self.parse_type()?;
                fields.insert(field_name, Box::new(ty));
                self.skip_whitespace();
                if let Some(&',') = self.input.peek() {
                    self.input.next();
                }
            }
            return Ok(Type::Record(fields));
        }
        // Otherwise, parse a simple type name.
        let name = self.parse_identifier()?;
        match name.as_str() {
            "Int" => Ok(Type::Int),
            "Str" | "String" => Ok(Type::Str),
            "Char" => Ok(Type::Char),
            "Bool" => Ok(Type::Bool),
            "Void" => Ok(Type::Void),
            _ => Ok(Type::Name(name)),
        }
    }
}

