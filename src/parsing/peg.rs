//! Handles pest stuff.

#![allow(missing_docs)]

use pest_derive::Parser;

#[derive(Parser)]
#[grammar = "parsing/grammar.pest"]
pub(crate) struct Parser;
