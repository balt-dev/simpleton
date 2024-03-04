#![warn(missing_docs, clippy::pedantic, clippy::perf, clippy::missing_docs_in_private_items)]
//! A relatively simple compiled language. Made for fun.
//!
//! Syntax is similar to both Rust and C.
//!
//! TODO: Better documentation


mod parsing;
pub use parsing::{
    tokens,
    parse,
    pest
};
