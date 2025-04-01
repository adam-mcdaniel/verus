use nom::{
    branch::alt,
    bytes::complete::{is_not, tag, take_while, take_while1, take_while_m_n},
    character::complete::{char, digit1, hex_digit1, multispace1, oct_digit1},
    combinator::{all_consuming, cut, map, map_opt, opt, recognize, verify},
    error::{ContextError, ParseError},
    multi::{fold_many0, many0, many1, many0_count, separated_list0},
    sequence::{delimited, pair, preceded, terminated, tuple, separated_pair},
    IResult, Parser,
};
use nom::{
    character::complete::{alpha1, alphanumeric1},
    combinator::value,
    error::{convert_error, ErrorKind, FromExternalError, VerboseError},
};
use super::*;

const KEYWORDS: &[&str] = &[
    "fun", "struct", "enum", "mut", "let", "if", "else", "while", "for", "return", "match",
];

fn is_symbol_char(c: char) -> bool {
    c.is_alphanumeric() || c == '_'
}

fn bin_digit1<'a, E: ParseError<&'a str> + ContextError<&'a str>>(
    input: &'a str,
) -> IResult<&'a str, &'a str, E> {
    take_while1(|c: char| c == '0' || c == '1')(input)
}

fn whitespace<'a, E: ParseError<&'a str> + ContextError<&'a str>>(
    input: &'a str,
) -> IResult<&'a str, &'a str, E> {
    take_while(|c: char| c.is_whitespace())(input)
}

fn parse_unit_literal<'a, E: ParseError<&'a str> + ContextError<&'a str>>(
    input: &'a str,
) -> IResult<&'a str, (), E> {
    let (input, _) = whitespace(input)?;
    let (input, _) = tag("(")(input)?;
    let (input, _) = whitespace(input)?;
    let (input, _) = tag(")")(input)?;
    let (input, _) = whitespace(input)?;
    Ok((input, ()))
}

fn parse_int_literal<'a, E: ParseError<&'a str> + ContextError<&'a str>>(
    input: &'a str,
) -> IResult<&'a str, i64, E> {
    // First try to parse hex
    // Check if its negative
    let (input, _) = whitespace(input)?;
    let (input, is_negative) = opt(tag("-"))(input)?;
    let is_negative = is_negative.is_some();
    let (input, _) = whitespace(input)?;

    let (input, result) = alt((
        map(preceded(tag("0x"), hex_digit1), |s: &str| {
            i64::from_str_radix(s, 16).unwrap()
        }),
        // Try octal
        map(preceded(tag("0o"), oct_digit1), |s: &str| {
            i64::from_str_radix(s, 8).unwrap()
        }),
        // Try binary
        map(preceded(tag("0b"), bin_digit1), |s: &str| {
            i64::from_str_radix(s, 2).unwrap()
        }),
        map(digit1, |s: &str| s.parse().unwrap()),
    ))(input)?;

    // let (input, result) = map(digit1, |s: &str| s.parse().unwrap())(input)?;
    if let Some(c) = input.chars().next() {
        if is_symbol_char(c) {
            return Err(nom::Err::Error(E::from_error_kind(input, ErrorKind::Digit)));
        }
    }

    let result = if is_negative { -result } else { result };

    Ok((input, result))
}

fn parse_float_literal<'a, E: ParseError<&'a str> + ContextError<&'a str>>(
    input: &'a str,
) -> IResult<&'a str, f64, E> {
    // Parse a signed float
    let (input, _) = whitespace(input)?;
    let (input, is_negative) = opt(tag("-"))(input)?;

    // Use builtin nom double
    let (input, result) = nom::number::complete::recognize_float(input)?;
    // Try to parse as an integer first
    let result: f64 = if let Ok(_i) = result.parse::<i64>() {
        // Fail
        return Err(nom::Err::Error(E::from_error_kind(input, ErrorKind::Digit)));
    } else {
        result.parse().unwrap()
    };

    if is_negative.is_some() {
        Ok((input, -result))
    } else {
        Ok((input, result))
    }
}

/// Parse a unicode sequence, of the form u{XXXX}, where XXXX is 1 to 6
/// hexadecimal numerals. We will combine this later with parse_escaped_char
/// to parse sequences like \u{00AC}.
fn parse_unicode<'a, E>(input: &'a str) -> IResult<&'a str, char, E>
where
    E: ParseError<&'a str>,
{
    // `take_while_m_n` parses between `m` and `n` bytes (inclusive) that match
    // a predicate. `parse_hex` here parses between 1 and 6 hexadecimal numerals.
    let parse_hex = take_while_m_n(1, 6, |c: char| c.is_ascii_hexdigit());

    // `preceded` takes a prefix parser, and if it succeeds, returns the result
    // of the body parser. In this case, it parses u{XXXX}.
    let parse_delimited_hex = preceded(
        char('u'),
        // `delimited` is like `preceded`, but it parses both a prefix and a suffix.
        // It returns the result of the middle parser. In this case, it parses
        // {XXXX}, where XXXX is 1 to 6 hex numerals, and returns XXXX
        delimited(char('{'), parse_hex, char('}')),
    );

    // `map_res` takes the result of a parser and applies a function that returns
    // a Result. In this case we take the hex bytes from parse_hex and attempt to
    // convert them to a u32.
    let parse_u32 = map(parse_delimited_hex, move |hex| {
        u32::from_str_radix(hex, 16).unwrap()
    });

    // map_opt is like map_res, but it takes an Option instead of a Result. If
    // the function returns None, map_opt returns an error. In this case, because
    // not all u32 values are valid unicode code points, we have to fallibly
    // convert to char with from_u32.
    map_opt(parse_u32, std::char::from_u32).parse(input)
}

/// Parse an escaped character: \n, \t, \r, \u{00AC}, etc.
fn parse_escaped_char<'a, E>(input: &'a str) -> IResult<&'a str, char, E>
where
    E: ParseError<&'a str>,
{
    preceded(
        char('\\'),
        // `alt` tries each parser in sequence, returning the result of
        // the first successful match
        alt((
            parse_unicode,
            // The `value` parser returns a fixed value (the first argument) if its
            // parser (the second argument) succeeds. In these cases, it looks for
            // the marker characters (n, r, t, etc) and returns the matching
            // character (\n, \r, \t, etc).
            value('\0', char('0')),
            value('\n', char('n')),
            value('\r', char('r')),
            value('\t', char('t')),
            value('\u{08}', char('b')),
            value('\u{0C}', char('f')),
            value('\\', char('\\')),
            value('/', char('/')),
            value('"', char('"')),
            value('\'', char('\'')),
            // Parse an \x followed by two hex digits, and convert it to a char
            map(
                preceded(char('x'), take_while_m_n(2, 2, |c: char| c.is_ascii_hexdigit())),
                |hex| u8::from_str_radix(hex, 16).unwrap() as char,
            ),
            // Parse an \u followed by four hex digits, and convert it to a char
            // map(
            //     preceded(char('u'), take_while_m_n(4, 4, |c: char| c.is_ascii_hexdigit())),
            //     |hex| char::from_u32(u32::from_str_radix(hex, 16).unwrap()).unwrap(),
            // ),
        )),
    )
    .parse(input)
}

/// Parse a backslash, followed by any amount of whitespace. This is used later
/// to discard any escaped whitespace.
fn parse_escaped_whitespace<'a, E: ParseError<&'a str>>(
    input: &'a str,
) -> IResult<&'a str, &'a str, E> {
    preceded(char('\\'), multispace1).parse(input)
}

/// Parse a non-empty block of text that doesn't include \ or "
fn parse_literal_intermediate<'a, E: ParseError<&'a str>>(
    input: &'a str,
) -> IResult<&'a str, &'a str, E> {
    // `is_not` parses a string of 0 or more characters that aren't one of the
    // given characters.
    let not_quote_slash = is_not("\"\\");

    // `verify` runs a parser, then runs a verification function on the output of
    // the parser. The verification function accepts out output only if it
    // returns true. In this case, we want to ensure that the output of is_not
    // is non-empty.
    verify(not_quote_slash, |s: &str| !s.is_empty()).parse(input)
}

/// Parse a non-empty block of text that doesn't include \ or "
fn parse_literal_intermediate_char<'a, E: ParseError<&'a str>>(
    input: &'a str,
) -> IResult<&'a str, &'a str, E> {
    // `is_not` parses a string of 0 or more characters that aren't one of the
    // given characters.
    let not_quote_slash = is_not("\'\\");

    // `verify` runs a parser, then runs a verification function on the output of
    // the parser. The verification function accepts out output only if it
    // returns true. In this case, we want to ensure that the output of is_not
    // is non-empty.
    verify(not_quote_slash, |s: &str| !s.is_empty()).parse(input)
}

/// A string fragment contains a fragment of a string being parsed: either
/// a non-empty Literal (a series of non-escaped characters), a single
/// parsed escaped character, or a block of escaped whitespace.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum StringFragment<'a> {
    Literal(&'a str),
    EscapedChar(char),
    EscapedWS,
}

/// Combine parse_literal, parse_escaped_whitespace, and parse_escaped_char
/// into a StringFragment.
fn parse_fragment_str<'a, E>(input: &'a str) -> IResult<&'a str, StringFragment<'a>, E>
where
    E: ParseError<&'a str>,
{
    alt((
        // The `map` combinator runs a parser, then applies a function to the output
        // of that parser.
        map(parse_literal_intermediate, StringFragment::Literal),
        map(parse_escaped_char, StringFragment::EscapedChar),
        value(StringFragment::EscapedWS, parse_escaped_whitespace),
    ))
    .parse(input)
}

fn parse_fragment_char<'a, E>(input: &'a str) -> IResult<&'a str, StringFragment<'a>, E>
where
    E: ParseError<&'a str>,
{
    alt((
        // The `map` combinator runs a parser, then applies a function to the output
        // of that parser.
        map(parse_literal_intermediate_char, StringFragment::Literal),
        map(parse_escaped_char, StringFragment::EscapedChar),
        value(StringFragment::EscapedWS, parse_escaped_whitespace),
    ))
    .parse(input)
}

/// Parse a string. Use a loop of parse_fragment and push all of the fragments
/// into an output string.
fn parse_string<'a, E: ParseError<&'a str> + ContextError<&'a str>>(input: &'a str) -> IResult<&'a str, String, E>
where
    E: ParseError<&'a str> + FromExternalError<&'a str, std::num::ParseIntError>,
{
    // fold is the equivalent of iterator::fold. It runs a parser in a loop,
    // and for each output value, calls a folding function on each output value.
    let build_string = fold_many0(
        // Our parser function – parses a single string fragment
        parse_fragment_str,
        // Our init value, an empty string
        String::new,
        // Our folding function. For each fragment, append the fragment to the
        // string.
        |mut string, fragment| {
            match fragment {
                StringFragment::Literal(s) => string.push_str(s),
                StringFragment::EscapedChar(c) => string.push(c),
                StringFragment::EscapedWS => {}
            }
            string
        },
    );

    // Finally, parse the string. Note that, if `build_string` could accept a raw
    // " character, the closing delimiter " would never match. When using
    // `delimited` with a looping parser (like fold), be sure that the
    // loop won't accidentally match your closing delimiter!
    delimited(char('"'), build_string, char('"')).parse(input)
}

fn parse_char_literal<'a, E: ParseError<&'a str> + ContextError<&'a str>>(
    input: &'a str,
) -> IResult<&'a str, char, E> {
    let (input, _) = whitespace(input)?;
    // fold is the equivalent of iterator::fold. It runs a parser in a loop,
    // and for each output value, calls a folding function on each output value.
    let build_string = fold_many0(
        // Our parser function – parses a single string fragment
        parse_fragment_char,
        // Our init value, an empty string
        String::new,
        // Our folding function. For each fragment, append the fragment to the
        // string.
        |mut string, fragment| {
            match fragment {
                StringFragment::Literal(s) => string.push_str(s),
                StringFragment::EscapedChar(c) => string.push(c),
                StringFragment::EscapedWS => {}
            }
            string
        },
    );

    // Finally, parse the string. Note that, if `build_string` could accept a raw
    // " character, the closing delimiter " would never match. When using
    // `delimited` with a looping parser (like fold), be sure that the
    // loop won't accidentally match your closing delimiter!
    let (input, result) = delimited(char('\''), cut(build_string), cut(char('\''))).parse(input)?;
    if result.len() != 1 {
        return Err(nom::Err::Error(E::from_error_kind(input, ErrorKind::Digit)));
    }
    Ok((input, result.chars().next().unwrap()))
}

fn parse_string_literal<'a, E: ParseError<&'a str> + ContextError<&'a str>>(
    input: &'a str,
) -> IResult<&'a str, String, E> {
    // map(context(
    //   "string",
    //   alt((
    //         // preceded(char('\''), cut(terminated(parse_inner_str_single, char('\'')))),
    //         preceded(char('"'), cut(terminated(parse_inner_str_double, char('"')))),
    //   )),
    // ), |s| s.to_string())(input)
    if let Ok((input, s)) = parse_string::<VerboseError<&str>>(input) {
        Ok((input, s))
    } else {
        Err(nom::Err::Error(E::from_error_kind(input, ErrorKind::Tag)))
    }
}

fn parse_bool_literal<'a, E: ParseError<&'a str> + ContextError<&'a str>>(
    input: &'a str,
) -> IResult<&'a str, bool, E> {
    let (input, result) = alt((value(true, tag("true")), value(false, tag("false"))))(input)?;

    // Peek and make sure the next character is not a symbol character
    if let Some(c) = input.chars().next() {
        if is_symbol_char(c) {
            return Err(nom::Err::Error(E::from_error_kind(input, ErrorKind::Digit)));
        }
    }

    Ok((input, result))
}

fn parse_symbol<'a, E: ParseError<&'a str> + ContextError<&'a str>>(
    input: &'a str,
) -> IResult<&'a str, &'a str, E> {
    let (input, _) = whitespace(input)?;
    // recognize(all_consuming(pair(
    //     verify(anychar, |&c| c.is_lowercase() || c == '_'),
    //     many0_count(preceded(opt(char('_')), alphanumeric1)),
    // )))(input)
    let (input, result) = recognize(pair(
        alt((alpha1, tag("_"))),
        many0_count(alt((alphanumeric1, tag("_")))),
    ))(input)?;
    if KEYWORDS.contains(&result) {
        return Err(nom::Err::Error(E::add_context(input, "Expected symbol, got a keyword", E::from_error_kind(input, ErrorKind::Tag))));
    }
    Ok((input, result))
}

fn parse_type_record<'a, E: ParseError<&'a str> + ContextError<&'a str>>(
    input: &'a str,
) -> IResult<&'a str, Type, E> {
    let (input, _) = whitespace(input)?;
    let (input, _) = opt(tag("struct"))(input)?;
    let (input, _) = whitespace(input)?;
    let (input, _) = tag("{")(input)?;
    let (input, _) = whitespace(input)?;
    let (input, fields) = cut(separated_list0(
        delimited(whitespace, char(','), whitespace),
        separated_pair(parse_symbol, delimited(whitespace, char(':'), whitespace), parse_type),
    ))(input)?;
    let (input, _) = whitespace(input)?;
    let (input, _) = tag("}")(input)?;

    Ok((input, Type::Record(fields.into_iter().map(|(k, v)| (k.to_owned(), v.into())).collect())))
}

fn parse_type_enum<'a, E: ParseError<&'a str> + ContextError<&'a str>>(
    input: &'a str,
) -> IResult<&'a str, Type, E> {
    let (input, _) = whitespace(input)?;
    let (input, _) = opt(tag("enum"))(input)?;
    let (input, _) = whitespace(input)?;
    let (input, _) = tag("{")(input)?;
    let (input, _) = whitespace(input)?;
    let (input, fields) = separated_list0(
        delimited(whitespace, tag("|"), whitespace),
        alt((
            separated_pair(parse_symbol, whitespace, parse_type),
            map(delimited(whitespace, parse_symbol, whitespace), |s| (s, Type::Void)),
        )),
    )(input)?;
    let (input, _) = whitespace(input)?;
    let (input, _) = tag("}")(input)?;

    Ok((input, Type::Enum(fields.into_iter().map(|(k, v)| (k.to_owned(), v.into())).collect())))
}

fn parse_type_list<'a, E: ParseError<&'a str> + ContextError<&'a str>>(
    input: &'a str,
) -> IResult<&'a str, Type, E> {
    let (input, _) = whitespace(input)?;
    let (input, _) = tag("[")(input)?;
    let (input, _) = whitespace(input)?;
    let (input, t) = cut(parse_type)(input)?;
    let (input, _) = whitespace(input)?;
    let (input, _) = tag("]")(input)?;

    Ok((input, Type::List(Box::new(t))))
}

fn parse_type_primitive<'a, E: ParseError<&'a str> + ContextError<&'a str>>(
    input: &'a str,
) -> IResult<&'a str, Type, E> {
    let (input, _) = whitespace(input)?;
    let (input, result) = alt((
        value(Type::Int, tag("Int")),
        value(Type::Float, tag("Float")),
        value(Type::Char, tag("Char")),
        value(Type::Bool, tag("Bool")),
        value(Type::Void, tag("Void")),
    ))(input)?;

    Ok((input, result))
}

fn parse_type_parenthesized<'a, E: ParseError<&'a str> + ContextError<&'a str>>(
    input: &'a str,
) -> IResult<&'a str, Type, E> {
    let (input, _) = whitespace(input)?;
    let (input, _) = tag("(")(input)?;
    let (input, _) = whitespace(input)?;
    let (input, t) = cut(parse_type)(input)?;
    let (input, _) = whitespace(input)?;
    let (input, _) = tag(")")(input)?;

    Ok((input, t))
}

fn parse_type<'a, E: ParseError<&'a str> + ContextError<&'a str>>(
    input: &'a str,
) -> IResult<&'a str, Type, E> {
    alt((
        parse_type_enum,
        parse_type_record,
        parse_type_list,
        parse_type_primitive,
        parse_type_parenthesized,
        map(parse_symbol, Type::name),
    ))(input)
}





fn parse_const_record<'a, E: ParseError<&'a str> + ContextError<&'a str>>(
    input: &'a str,
) -> IResult<&'a str, Const, E> {
    let (input, _) = whitespace(input)?;
    let (input, _) = tag("{")(input)?;
    let (input, _) = whitespace(input)?;
    let (input, fields) = cut(separated_list0(
        delimited(whitespace, char(','), whitespace),
        separated_pair(parse_symbol, delimited(whitespace, char(':'), whitespace), parse_const),
    ))(input)?;
    let (input, _) = whitespace(input)?;
    let (input, _) = tag("}")(input)?;

    Ok((input, Const::Record(fields.into_iter().map(|(k, v)| (k.to_owned(), v)).collect())))
}

fn parse_const_list<'a, E: ParseError<&'a str> + ContextError<&'a str>>(
    input: &'a str,
) -> IResult<&'a str, Const, E> {
    let (input, _) = whitespace(input)?;
    let (input, _) = tag("[")(input)?;
    let (input, _) = whitespace(input)?;
    let (input, elements) = cut(separated_list0(
        delimited(whitespace, char(','), whitespace),
        parse_const,
    ))(input)?;
    let (input, _) = whitespace(input)?;
    let (input, _) = tag("]")(input)?;

    Ok((input, Const::List(elements)))
}

fn parse_const_variant<'a, E: ParseError<&'a str> + ContextError<&'a str>>(
    input: &'a str,
) -> IResult<&'a str, Const, E> {
    let (input, _) = whitespace(input)?;
    // Parse the type
    let (input, ty) = parse_type(input)?;
    let (input, _) = whitespace(input)?;
    let (input, _) = tag("of")(input)?;
    let (input, _) = whitespace(input)?;
    // Parse the variant name
    let (input, variant) = parse_symbol(input)?;
    let (input, _) = whitespace(input)?;
    // Parse the value
    let (input, value) = opt(parse_const)(input)?;

    Ok((input, Const::Variant(ty, variant.to_owned(), Box::new(value.unwrap_or(Const::Void)))))
}

fn parse_const_parenthesized<'a, E: ParseError<&'a str> + ContextError<&'a str>>(
    input: &'a str,
) -> IResult<&'a str, Const, E> {
    let (input, _) = whitespace(input)?;
    let (input, _) = tag("(")(input)?;
    let (input, _) = whitespace(input)?;
    let (input, c) = cut(parse_const)(input)?;
    let (input, _) = whitespace(input)?;
    let (input, _) = tag(")")(input)?;

    Ok((input, c))
}

fn parse_const<'a, E: ParseError<&'a str> + ContextError<&'a str>>(
    input: &'a str,
) -> IResult<&'a str, Const, E> {
    alt((
        parse_const_parenthesized,
        map(parse_float_literal, Const::Float),
        map(parse_int_literal, Const::Int),
        map(parse_bool_literal, Const::Bool),
        map(parse_char_literal, Const::Char),
        map(parse_string_literal, Const::Str),
        parse_const_record,
        parse_const_list,
        parse_const_variant,
    ))(input)
}

fn parse_expr_record<'a, E: ParseError<&'a str> + ContextError<&'a str>>(
    input: &'a str,
) -> IResult<&'a str, Expr, E> {
    let (input, _) = whitespace(input)?;
    let (input, _) = opt(tag("struct"))(input)?;
    let (input, _) = whitespace(input)?;
    let (input, _) = tag("{")(input)?;
    let (input, _) = whitespace(input)?;
    let (input, fields) = cut(separated_list0(
        delimited(whitespace, char(','), whitespace),
        separated_pair(parse_symbol, delimited(whitespace, char(':'), whitespace), parse_expr),
    ))(input)?;
    let (input, _) = whitespace(input)?;
    let (input, _) = tag("}")(input)?;

    Ok((input, Expr::Record(fields.into_iter().map(|(k, v)| (k.to_owned(), v)).collect())))
}

fn parse_expr_variant<'a, E: ParseError<&'a str> + ContextError<&'a str>>(
    input: &'a str,
) -> IResult<&'a str, Expr, E> {
    let (input, _) = whitespace(input)?;
    // Parse the type
    let (input, ty) = parse_type(input)?;
    let (input, _) = whitespace(input)?;
    let (input, _) = tag("of")(input)?;
    let (input, _) = whitespace(input)?;
    // Parse the variant name
    let (input, variant) = parse_symbol(input)?;
    let (input, _) = whitespace(input)?;
    // Parse the value
    let (input, value) = opt(parse_expr)(input)?;

    Ok((input, Expr::Variant(ty, variant.to_owned(), Box::new(value.unwrap_or(Expr::VOID)))))
}

fn parse_expr_parenthesized<'a, E: ParseError<&'a str> + ContextError<&'a str>>(
    input: &'a str,
) -> IResult<&'a str, Expr, E> {
    let (input, _) = whitespace(input)?;
    let (input, _) = tag("(")(input)?;
    let (input, _) = whitespace(input)?;
    let (input, e) = cut(parse_expr)(input)?;
    let (input, _) = whitespace(input)?;
    let (input, _) = tag(")")(input)?;

    Ok((input, e))
}

fn parse_expr_list<'a, E: ParseError<&'a str> + ContextError<&'a str>>(
    input: &'a str,
) -> IResult<&'a str, Expr, E> {
    let (input, _) = whitespace(input)?;
    let (input, _) = tag("[")(input)?;
    let (input, _) = whitespace(input)?;
    let (input, elements) = cut(separated_list0(
        delimited(whitespace, char(','), whitespace),
        parse_expr,
    ))(input)?;
    let (input, _) = whitespace(input)?;
    let (input, _) = tag("]")(input)?;

    Ok((input, Expr::List(elements)))
}

fn parse_expr<'a, E: ParseError<&'a str> + ContextError<&'a str>>(
    input: &'a str,
) -> IResult<&'a str, Expr, E> {
    alt((
        map(parse_const, Expr::Const),
        parse_expr_parenthesized,
        parse_expr_record,
        parse_expr_variant,
        map(parse_symbol, Expr::var),
    ))(input)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_parse_const_record() {
        let input_and_expected = [
            ("{x: 1, y: 2}", Const::record([
                ("x", Const::Int(1)),
                ("y", Const::Int(2)),
            ])),

            ("{x: 1, y: 2, z: 3}", Const::record([
                ("x", Const::Int(1)),
                ("y", Const::Int(2)),
                ("z", Const::Int(3)),
            ])),

            ("{x: 1, y: 2, z: 3, w: 4.0}", Const::record([
                ("x", Const::Int(1)),
                ("y", Const::Int(2)),
                ("z", Const::Int(3)),
                ("w", Const::Float(4.0)),
            ])),
        ];

        for (input, expected) in input_and_expected {
            let result = parse_const_record::<VerboseError<&str>>(input);
            println!("{input:?} -> {result:?}");
            assert_eq!(result, Ok(("", expected.clone())));
        }
    }

    #[test]
    fn test_parse_const_list() {
        let input_and_expected = [
            ("[1, 2, 3]", Const::List(vec![
                Const::Int(1),
                Const::Int(2),
                Const::Int(3),
            ])),

            ("[1, 2, 3, 4.0]", Const::List(vec![
                Const::Int(1),
                Const::Int(2),
                Const::Int(3),
                Const::Float(4.0),
            ])),
        ];

        for (input, expected) in input_and_expected {
            let result = parse_const_list::<VerboseError<&str>>(input);
            println!("{input:?} -> {result:?}");
            assert_eq!(result, Ok(("", expected.clone())));
        }
    }

    #[test]
    fn test_parse_const_variant() {
        let input_and_expected = [
            ("{Some(Int) | None} of None", Const::variant(
                Type::enum_variants([
                    ("Some".to_owned(), Type::Int),
                    ("None".to_owned(), Type::Void),
                ]),
                "None",
                Const::Void,
            )),

            ("{Some(Int) | None} of Some(5)",
                Const::variant(
                    Type::enum_variants([
                        ("Some".to_owned(), Type::Int),
                        ("None".to_owned(), Type::Void),
                    ]),
                    "Some",
                    Const::Int(5),
                )
            ),
        ];

        for (input, expected) in input_and_expected {
            let result = parse_const_variant::<VerboseError<&str>>(input);
            println!("{input:?} -> {result:?}");
            assert_eq!(result, Ok(("", expected.clone())));
        }
    }

    #[test]
    fn test_parse_expr_list() {
        let input_and_expected = [
            ("[1, 2, 3]", Expr::List(vec![
                Expr::Const(Const::Int(1)),
                Expr::Const(Const::Int(2)),
                Expr::Const(Const::Int(3)),
            ])),

            ("[1, 2, 3, 4.0]", Expr::List(vec![
                Expr::Const(Const::Int(1)),
                Expr::Const(Const::Int(2)),
                Expr::Const(Const::Int(3)),
                Expr::Const(Const::Float(4.0)),
            ])),
        ];

        for (input, expected) in input_and_expected {
            let result = parse_expr_list::<VerboseError<&str>>(input);
            println!("{input:?} -> {result:?}");
            assert_eq!(result, Ok(("", expected.clone())));
        }
    }


    #[test]
    fn test_parse_type_enum() -> anyhow::Result<()> {
        let input_and_expected = [
            ("{Some(Int) | None}", Type::enum_variants([
                ("Some".to_owned(), Type::Int),
                ("None".to_owned(), Type::Void),
            ])),

            ("{Some(Int) | None | Another(Float)}", Type::enum_variants([
                ("Some".to_owned(), Type::Int),
                ("None".to_owned(), Type::Void),
                ("Another".to_owned(), Type::Float),
            ])),
        ];

        for (input, expected) in input_and_expected {
            let (_, result) = all_consuming(parse_type_enum)(input).map_err(|e| {
                match e {
                    nom::Err::Error(e) | nom::Err::Failure(e) => {
                        convert_error(input, e)
                    }
                    nom::Err::Incomplete(_) => unreachable!(),
                }
            }).map_err(anyhow::Error::msg)?;
            println!("{input:?} -> {result:?}");
        }
        
        Ok(())
    }
}