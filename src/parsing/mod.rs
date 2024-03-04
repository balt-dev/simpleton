//! Handles parsing of the language.

pub(crate) mod peg;
pub use peg::parse;
/// Re-export of [`pest`] for API convenience
pub use pest;

pub mod tokens;
