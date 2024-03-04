//! Handles pest stuff.

// Assume any .unwrap()s in this file are checked by the grammar itself.

use std::str::FromStr;
use descape::UnescapeExt;
use pest::{
    Parser as _,
    Span,
    iterators::{Pair, Pairs},
    error::ErrorVariant
};
use crate::tokens::{Element, EnumRepr, Type, TypeTag, Visibility};

/// Alias for pest errors.
type PestError = pest::error::Error<Rule>;

mod pest_parser {
    #![allow(missing_docs, clippy::missing_docs_in_private_items)]

    use pest_derive::Parser;

    #[derive(Parser)]
    #[grammar = "parsing/grammar.pest"]
    pub(crate) struct Parser;
}

use pest_parser::{Parser, Rule};

/// A single token in a pest tree.
/// This is transformed from Pest for convenience of parsing.
pub(crate) struct TokenTree<'s, R> {
    /// The span of this token.
    pub(crate) span: Span<'s>,
    /// The line-column position of this token.
    pub(crate) line_col: (usize, usize),
    /// The rule of this token.
    pub(crate) rule: R,
    /// This token's children. Empty represents a terminal.
    pub(crate) children: Vec<TokenTree<'s, R>>
}

/// Parse a number from a pair.
fn parse_integer(pair: &Pair<'_, Rule>) -> Option<i128> {
    match pair.as_rule() {
        Rule::sint => {
            let mut inner = pair.into_inner();
            let sign = inner.next().unwrap();
            let num = inner.next().unwrap();
            let mut int = parse_integer(&num)?;
            if sign.as_rule() == Rule::neg {
                int = -int;
            }
            Some(int)
        },
        Rule::dec_int => pair.as_str().parse().ok(),
        Rule::hex_int => i128::from_str_radix(&pair.as_str()[2..], 16).ok(),
        Rule::oct_int => i128::from_str_radix(&pair.as_str()[2..], 8).ok(),
        Rule::bin_int => i128::from_str_radix(&pair.as_str()[2..], 2).ok(),
        Rule::char =>
            pair
                .as_str()
                .trim_matches('\'')
                .to_unescaped()
                .ok()
                .map(|s|
                    s.chars()
                        .next().unwrap()
                        as i128
                ),
        _ => None
    }
}

/// Constructs a pest error with a given span and message.
macro_rules! pest_err {
    ($span: expr; $($tt: tt)*) => {
        PestError::new_from_span(
            ErrorVariant::CustomError {
                message: format!($($tt)*)
            },
            $span
        )
    };
}

/// Bails out of the current function with a pest error given a span and message.
macro_rules! pest_bail {
    ($span: expr; $($tt: tt)*) => {{
        Err(pest_err!($span; $($tt)*))?;
        loop {} // unreachable :)
    }};
}

impl TryFrom<Pair<'_, Rule>> for Type {
    type Error = PestError;

    fn try_from(value: Pair<Rule>) -> Result<Self, Self::Error> {
        let mut tags = vec![];
        let mut current = value;
        loop {
            let rule = current.as_rule();
            match rule {
                Rule::arr_ty => {
                    let mut inner = current.into_inner();
                    let child = inner.next().unwrap();
                    let count = inner.next().unwrap();
                    let count = parse_integer(&count)
                        .and_then(|v: i128| v.try_into().ok())
                        .ok_or_else(|| pest_err!(
                            count.as_span();
                            "could not parse this as an integer"
                        ))?;
                    tags.push(
                        TypeTag::Array { length: count }
                    );
                    current = child;
                },
                Rule::ptr_ty => {
                    let mut inner = current.into_inner();
                    let child = inner.next().unwrap();
                    tags.push(TypeTag::Pointer);
                    current = child;
                },
                Rule::idt_ty => {
                    let ty = Type {
                        tags,
                        name: current.as_str().into()
                    };
                    break Ok(ty)
                }
                rule => pest_bail!(
                    current.as_span();
                    "failed to parse type (unexpected rule {rule:?})"
                )
            }
        }
    }
}

impl TryFrom<Pair<'_, Rule>> for Visibility {
    type Error = PestError;

    fn try_from(value: Pair<'_, Rule>) -> Result<Self, Self::Error> {
        let mut inner = value.into_inner();
        let Some(child) = inner.next() else {
            return Ok(Visibility::Private);
        };
        match child.as_rule() {
            Rule::public => Ok(Visibility::Public),
            Rule::internal => Ok(Visibility::Internal),
            rule => Err(pest_err!(
                child.as_span();
                "failed to parse visibility rule (unexpected rule {rule:?})"
            ))
        }
    }
}

impl FromStr for EnumRepr {
    type Err = ();

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        Ok(match s {
            "uint8" => Self::Unsigned8,
            "uint16" => Self::Unsigned16,
            "uint32" => Self::Unsigned32,
            "uint64" => Self::Unsigned64,
            "int8" => Self::Signed8,
            "int16" => Self::Signed16,
            "int32" => Self::Signed32,
            "int64" => Self::Signed64,
            "uptr" => Self::UnsignedPointer,
            "ptr" => Self::SignedPointer,
            _ => return Err(())
        })
    }
}

impl TryFrom<Pair<'_, Rule>> for EnumRepr {
    type Error = PestError;

    fn try_from(value: Pair<Rule>) -> Result<Self, Self::Error> {
        let rule = value.as_rule();
        if rule != Rule::enum_repr {
            pest_bail!(value.as_span(); "failed to parse enum repr (unexpected rule {rule:?})")
        }
        value.as_str().parse().map_err(|_| pest_err!(
            value.as_span(); "failed to parse enum repr (invalid string)"
        ))
    }
}

impl TryFrom<Pair<'_, Rule>> for Element {
    type Error = PestError;

    fn try_from(value: Pair<'_, Rule>) -> Result<Self, Self::Error> {
        let span = value.as_span();
        let rule = value.as_rule();
        let mut inner = value.into_inner();

        return Ok(match rule {
            Rule::r#struct | Rule::union => {
                let visibility = inner.next().unwrap().try_into()?;
                let name = inner.next().unwrap().as_str().into();
                let fields = inner.map(|pair| {
                    let mut inner = pair.into_inner();
                    let visibility: Visibility = inner.next().unwrap().try_into()?;
                    let ty: Type = inner.next().unwrap().try_into()?;
                    let name: String = inner.next().unwrap().as_str().into();
                    Ok((visibility, ty, name))
                }).collect()?;
                match rule {
                    Rule::r#struct => Element::Struct {
                        vis: visibility,
                        name,
                        fields
                    },
                    Rule::union => Element::Struct {
                        vis: visibility,
                        name,
                        fields
                    },
                    _ => unreachable!()
                }
            },
            Rule::r#enum => {
                let visibility = inner.next().unwrap().try_into()?;
                let repr = inner.next().unwrap().try_into()?;
                let name = inner.next().unwrap().as_str().into();
                let mut current_repr: i128 = 0;
                let variants = inner.map(|field| {
                    let mut inner = field.into_inner();
                    let visibility: Visibility = inner.next().unwrap().try_into()?;
                    let name = inner.next().unwrap()
                        .as_str().to_string();
                    let repr = match inner.next() {
                        None => {
                            let r = current_repr;
                            current_repr = current_repr.wrapping_add(1);
                            r
                        },
                        Some(pair) => {
                            let span = pair.as_span();
                            let literal = parse_integer(&pair)
                                .ok_or(pest_err!(span; "failed to parse integer value"))?;
                            current_repr = literal.wrapping_add(1);
                            literal
                        }
                    };
                    Ok((visibility, name, repr))
                }).collect()?;
                Element::Enum {
                    vis: visibility,
                    repr,
                    name,
                    variants
                }
            },
            Rule::func => {},
            Rule::import => {},
            Rule::r#extern => {},
            Rule::constant | Rule::r#static => {},
            _ =>
                pest_bail!(span; "failed to parse element (unexpected rule {rule:?})")
        })
    }
}

/// Parses a file into an AST of tokens.
#[allow(clippy::result_large_err)]
pub fn parse(str: &str) -> Result<Vec<Element>, PestError> {
    let pest_tree = Parser::parse(Rule::file, str)?;

    // Doing this lint changes semantics in a way that makes type check fail
    #[allow(clippy::redundant_closure_for_method_calls)]
    pest_tree.filter(|p| p.as_rule() != Rule::EOI)
        //.map(Element::try_from) (this errors in the ide for some reason, no clue why)
        .map(|pair| pair.try_into())
        .collect()
}
