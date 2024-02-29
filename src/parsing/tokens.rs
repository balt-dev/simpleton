//! Language constructs defining the AST of the language.

use std::fmt::{
    self,
    Display,
    Formatter,
};
use itertools::Itertools;

/// Alias for referencing a block of statements.
pub type Block = Vec<Statement>;

#[non_exhaustive]
#[derive(Debug, Clone, PartialEq)]
/// A single top-level language element.
pub enum Element {
    /// Import a module from a path.
    Import {
        /// This import's visibility rule.
        vis: Visibility,
        /// This import's module path.
        path: Vec<String>,
    },
    /// Import code from an object file relative to this file.
    /// This may be a `.so` or a `.dll`, depending on the platform.
    ExternalImport {
        /// This external import's visibility rule.
        vis: Visibility,
        /// This external import's file path.
        path: String,
    },
    /// A struct.
    Struct {
        /// This struct's visibility rule.
        vis: Visibility,
        /// This struct's name.
        name: String,
        /// This struct's fields.
        fields: Vec<(Visibility, Type, String)>,
    },
    /// A constant value. Every instance of this variable is replaced inline.
    Constant {
        /// This constant value's visibility rule.
        vis: Visibility,
        /// This constant value's type.
        ty: Type,
        /// This constant value's name.
        name: String,
        /// The expression evaluating to this constant value.
        value: Expression,
    },
    /// A static variable. Every instance of this variable refers to this value in the binary.
    Static {
        /// This static variable's visibility rule.
        vis: Visibility,
        /// This static variable's type.
        ty: Type,
        /// This static variable's name.
        name: String,
        /// The expression evaluating to this static variable's value.
        value: Expression,
    },
    /// An enumeration.
    Enum {
        /// This enum's visibility rule.
        vis: Visibility,
        /// This enum's internal representation.
        repr: EnumRepr,
        /// This enum's name.
        name: String,
        /// This enum's variants.
        variants: Vec<(Visibility, String, u64)>,
    },
    /// A union.
    Union {
        /// This union's visibility rule.
        vis: Visibility,
        /// This union's name.
        name: String,
        /// The ways this union can represent its data.
        representations: Vec<(Visibility, Type, String)>,
    },
    /// A callable function.
    Function {
        /// This function's visibility rule.
        vis: Visibility,
        /// Whether this function can be called from a constant context.
        constant: bool,
        /// Whether this function should be inlined.
        inline: bool,
        /// This function's return type.
        ty: Type,
        /// This function's identifying path.
        path: Vec<String>,
        /// This function's arguments.
        arguments: Vec<(Type, String)>,
        /// This function's body.
        block: Block,
    },
}

/// An enum's internal representation.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum EnumRepr {
    /// 8-bit, unsigned.
    Unsigned8,
    /// 16-bit, unsigned.
    Unsigned16,
    /// 32-bit, unsigned.
    Unsigned32,
    /// 64-bit, unsigned.
    Unsigned64,
    /// 8-bit, signed.
    Signed8,
    /// 16-bit, signed.
    Signed16,
    /// 32-bit, signed.
    Signed32,
    /// 64-bit, signed.
    Signed64,
    /// Size of a pointer on the build architecture, unsigned.
    UnsignedPointer,
    /// Size of a pointer on the build architecture, signed.
    SignedPointer,
}

#[non_exhaustive]
#[derive(Debug, Clone, PartialEq, Eq)]
/// A statement. May be an expression, like `5 + 3`, or a control flow block, like `if`.
pub enum Statement {
    /// An expression wrapped as a statement.
    Expression(Expression),
    /// An if block.
    If {
        /// Each potential case of the if statement, in order.
        cases: Vec<(Expression, Block)>,
        /// The fallback case of the if statement, if there is one.
        fallback: Option<Block>,
    },
    /// A for loop.
    For {
        /// The statement to run at the start of the loop.
        init: Option<Box<Statement>>,
        /// The expression to check every iteration.
        check: Option<Expression>,
        /// The expression to run every iteration.
        update: Option<Expression>,
        /// The block to run every iteration.
        inner: Block,
    },
    /// A while loop.
    While {
        /// The expression to check every iteration.
        check: Expression,
        /// The block to run every iteration.
        inner: Block,
    },
    /// An infinite loop.
    Forever {
        /// The block to run every iteration.
        inner: Block
    },
    /// Break the current loop.
    Break,
    /// Break the current iteration and continue to the next.
    Continue,
    /// Return a value from this function.
    Return {
        /// The expression to return, if any.
        expr: Option<Expression>
    },
    /// Drop a value, freeing its memory.
    Drop {
        /// The value to drop.
        expr: Expression
    },
    /// Initialize a value.
    Initialize {
        /// The type of the new value.
        ty: Type,
        /// The expression to initialize the new value with, if any.
        expr: Option<Expression>,
    },
}

type BoxedExp = Box<Expression>;

#[derive(Debug, Clone, PartialEq, Eq)]
/// An expression - that is, an aggregation of binary and unary operators between [atoms](Atom).
pub enum Expression {
    /// A binary expression, having a left and right side with an infix joining them.
    Binary {
        /// The left-hand side of the expression.
        lhs: BoxedExp,
        /// The infix for this binary expression.
        opr: Infix,
        /// The right-hand side of the expression.
        rhs: BoxedExp,
    },
    /// An expression with an operand either prefixing or suffixing it.
    Unary {
        /// The prefix or postfix for this expression.
        opr: UnaryOperand,
        /// The expression to which the unary operator is being applied.
        expr: BoxedExp,
    },
    /// An atomic value with no operands attached.
    Atom(Atom),
}

/// Represents an infix operand for an expression.
#[non_exhaustive]
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Infix {
    /// Assign the right hand side to the value at the left hand side.
    Assign,
    /// Takes the value on the left hand side if the expression evaluates to true, elsewise the right hand side.
    Ternary(BoxedExp),
    /// Takes the logical OR of the left and right hand sides, short circuting if the left hand is true.
    LogicalOr,
    /// Takes the logical AND of the left and right hand sides, short circuting if the left hand is false.
    LogicalAnd,
    /// Takes the bitwise OR of the left and right hand sides.
    BitwiseOr,
    /// Takes the bitwise AND of the left and right hand sides.
    BitwiseAnd,
    /// Takes the bitwise XOR of the left and right hand sides.
    BitwiseXor,
    /// Checks whether the left and right hand sides are equal.
    Equal,
    /// Checks whether the left and right hand sides aren't equal.
    NotEqual,
    /// Checks whether the left hand side is less than the right hand side.
    Less,
    /// Checks whether the left hand side is less than or equal to the right hand side.
    LessOrEqual,
    /// Checks whether the left hand side is greater than the right hand side.
    Greater,
    /// Checks whether the left hand side is greater than or equal to the right hand side.
    GreaterOrEqual,
    /// Compares the two values, returning an `int8` where:
    /// - `-1` means the left hand is less,
    /// - `1` means the left hand is greater,
    /// - `0` means they're equal, and
    /// - `127` means they're otherwise not equal (NaN).
    /// For non-NaN numbers, this is equivalent to `sign(lhs - rhs)`.
    Spaceship,
    /// Bit-shifts the left hand side to the left by the right hand side.
    ShiftLeft,
    /// Bit-shifts the left hand side to the right by the right hand side.
    /// For unsigned types, this is a logical shift.
    /// For signed types, this is an arithmetic shift.
    ShiftRight,
    /// Adds the left and right hand sides.
    Add,
    /// Subtracts the left hand side from the right hand side.
    Subtract,
    /// Multiplies the left hand side by the right hand side.
    Multiply,
    /// Divides the left hand side by the right hand side.
    Divide,
    /// Takes the remainder of dividing the left hand side by the right hand side.
    Remainder,
    /// Accesses a member of the left hand side dictated by the right hand side.
    Access,
}

impl Infix {
    /// Gets the precedence of this infix.
    fn precedence(&self) -> usize {
        use Infix::*;
        match self {
            Access => 0,
            Multiply | Divide | Remainder => 1,
            Add | Subtract => 2,
            ShiftLeft | ShiftRight => 3,
            Less | LessOrEqual | Greater | GreaterOrEqual | Spaceship => 4,
            Equal | NotEqual => 5,
            BitwiseXor => 6,
            BitwiseAnd => 7,
            BitwiseOr => 8,
            LogicalAnd => 9,
            LogicalOr => 10,
            Ternary(..) => 11,
            Assign => 12
        }
    }
}

impl Ord for Infix {
    /// Gets the ordering of this infix, comparing by operator precedence.
    /// Operators processed first will be marked as less than operators processed last.
    /// Operator precedence is **guaranteed** to be stable across minor versions.
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.precedence().cmp(&other.precedence())
    }
}

impl PartialOrd for Infix {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

/// Represents either a prefix or postfix operand for an expression.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub enum UnaryOperand {
    /// Taking the arithmetic negation of the expression's value.
    Negation,
    /// Taking the bitwise negation of the expression's value.
    Not,
    /// Taking a reference to the expression's value.
    Reference,
    /// Dereferencing a pointer.
    Dereference,
    /// Calling the value with the given list of arguments.
    Call(Vec<Expression>),
    /// Indexing the expression with another expression.
    Index(BoxedExp),
    /// Casting the expression to another type.
    Cast(Type),
}

/// TODO
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Atom;

#[non_exhaustive]
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
/// A visibility specifier for an element.
pub enum Visibility {
    #[default]
    /// Restricted to this module.
    Private,
    /// Restricted to this module and its children.
    Internal,
    /// Unrestricted access.
    Public,
}


#[derive(Debug, Clone, PartialEq, Eq)]
/// A specified type.
pub struct Type {
    /// The preceding tags of this type.
    pub tags: Vec<TypeTag>,
    /// The type's name.
    pub name: String,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
/// A tag prefixing a type specification.
pub enum TypeTag {
    /// Type is a pointer to a value.
    Pointer,
    /// Type is an array of values with a length.
    Array {
        /// The length of the array.
        length: u64
    },
}

macro_rules! display_impl {
    ($(
        impl Display for $name: ident {
            $($tt:tt)*
        }
    )+) => {$(
        impl Display for $name {
            fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
                self.display(f, 0)
            }
        }

        impl $name {
            $($tt)*
        }
    )+};
}

macro_rules! write_indented {
    ($f: ident, $indent: ident, $str: literal $(, $($tt:tt)*)?) => {{
        write!(
            $f, concat!("{}", $str), "\t".repeat($indent) $(, $($tt)+)?
        )
    }};
}

macro_rules! writeln_indented {
    ($f: ident, $indent: ident, $str: literal $(, $($tt:tt)*)?) => {{
        writeln!(
            $f, concat!("{}", $str), "\t".repeat($indent) $(, $($tt)+)?
        )
    }};
}

display_impl! {

    impl Display for Element {
        fn display(&self, f: &mut Formatter<'_>, mut indent: usize) -> fmt::Result {
            match self {
                Element::Import{vis, path } =>
                    write_indented!(f, indent, "{}import {}", vis, path.join("::")),
                Element::ExternalImport{vis, path } =>
                    write_indented!(f, indent, "{}import {}", vis, path.escape_default()),
                Element::Struct{vis, name, fields } => {
                    writeln_indented!(
                        f, indent, "{}struct {} {{", vis, name
                    )?;
                    indent += 1;
                    for (vis, ty, name) in fields {
                        writeln_indented!(
                            f, indent, "{}{} {}", vis, ty, name
                        )?;
                    }
                    indent -= 1;
                    write_indented!(f, indent, "}}")
                },
                Element::Constant{vis, ty, name, value } =>
                    write_indented!(f, indent, "{}constant {} {} = {};", vis, ty, name, value),
                Element::Static{vis, ty, name, value} =>
                    write_indented!(f, indent, "{}static {} {} = {};", vis, ty, name, value),
                Element::Enum{vis, repr, name, variants} => {
                    writeln_indented!(
                        f, indent, "{}enum {} {} {{", vis, repr, name
                    )?;
                    indent += 1;
                    let mut last_repr = 0;
                    for (vis, name, repr) in variants {
                        if repr.saturating_sub(1) == last_repr {
                            writeln_indented!(f, indent, "{}{},", vis, name)?;
                        } else {
                            writeln_indented!(f, indent, "{}{} = {},", vis, name, repr)?;
                        }
                        last_repr = *repr;
                    }
                    indent -= 1;
                    write_indented!(f, indent, "}}")
                },
                Element::Union{ name, representations, vis } => {
                    writeln_indented!(
                        f, indent, "{}union {} {{", vis, name
                    )?;
                    indent += 1;
                    for (vis, ty, name) in representations {
                        writeln_indented!(
                            f, indent, "{}{} {}", vis, ty, name
                        )?;
                    }
                    indent -= 1;
                    write_indented!(f, indent, "}}")
                },
                Element::Function{vis,constant,inline,ty,path,arguments,block  } => {
                    write_indented!(f, indent, "{}", vis)?;
                    if *constant {
                        write!(f, "constant ")?;
                    }
                    if *inline {
                        write!(f, "inline ")?;
                    }
                    write!(
                        f, "{ty} {} ({}) {{",
                        path.join("::"),
                        Itertools::intersperse(
                            arguments.iter().map(|(ty, name)| {
                                format!("{ty} {name}")
                            }),
                            ", ".to_string()
                        ).collect::<String>()
                    )?;
                    indent += 1;
                    writeln!(f)?;
                    for statement in block {
                        writeln_indented!(f, indent, "{}", statement)?;
                    }
                    indent -= 1;
                    write_indented!(f, indent, "}}")
                },
            }
        }
    }

    impl Display for Visibility {
        // This isn't ACTUALLY a trait, so we can drop the & out front for performance
        fn display(self, f: &mut Formatter<'_>, _indent: usize) -> fmt::Result {
            match self {
                Visibility::Private => Ok(()),
                Visibility::Internal => write!(f, "internal "),
                Visibility::Public => write!(f, "public ")
            }
        }
    }

    impl Display for Type {
        fn display(&self, f: &mut Formatter<'_>, _indent: usize) -> fmt::Result {
            let mut array_counts = Vec::new();
            for tag in &self.tags {
                match tag {
                    TypeTag::Pointer => write!(f, "*")?,
                    TypeTag::Array {length} => {
                        array_counts.push(length);
                        write!(f, "[")?;
                    }
                }
            }
            write!(f, "{}", self.name)?;
            for count in array_counts {
                write!(f, "; {count}]")?;
            }
            Ok(())
        }
    }

    impl Display for EnumRepr {
        fn display(self, f: &mut Formatter<'_>, _indent: usize) -> fmt::Result {
            write!(f, "{}", match self {
                EnumRepr::Unsigned8 => "uint8",
                EnumRepr::Unsigned16 => "uint16",
                EnumRepr::Unsigned32 => "uint32",
                EnumRepr::Unsigned64 => "uint64",
                EnumRepr::Signed8 => "int8",
                EnumRepr::Signed16 => "int16",
                EnumRepr::Signed32 => "int32",
                EnumRepr::Signed64 => "int64",
                EnumRepr::UnsignedPointer => "uptr",
                EnumRepr::SignedPointer => "ptr"
            })
        }
    }


    impl Display for Statement {
        fn display(&self, f: &mut Formatter<'_>, mut indent: usize) -> fmt::Result {
            match self {
                Statement::Expression(expr) =>
                    write_indented!(f, indent, "{};", expr),
                Statement::If { cases, fallback } => {
                    let mut first_case = true;
                    for (expr, block) in cases {
                        if !first_case {
                            writeln!(f, " else if {} {{", expr)?;
                        } else {
                            writeln_indented!(f, indent, "if {} {{", expr)?;
                            indent += 1;
                        }
                        indent += 1;
                        
                        for statement in block {
                            writeln_indented!(f, indent, "{}", statement)?;
                        }
                        indent -= 1;
                        write_indented!(f, indent, "}}")?;
                        first_case = false;
                    }
                    if let Some(fallback) = fallback {
                        writeln!(f, " else {{")?;
                        indent += 1;
                        for statement in fallback {
                            writeln_indented!(f, indent, "{}", statement)?;
                        }
                        indent -= 1;
                        write_indented!(f, indent, "}}")?;
                    }
                    Ok(())
                }
                Statement::For { init, check, update, inner } => todo!(),
                Statement::While { .. } => todo!(),
                Statement::Forever { .. } => todo!(),
                Statement::Break => todo!(),
                Statement::Continue => todo!(),
                Statement::Return { .. } => todo!(),
                Statement::Drop { .. } => todo!(),
                Statement::Initialize { .. } => todo!()
            }
        }
    }

    impl Display for Expression {
        fn display(&self, f: &mut Formatter<'_>, _indent: usize) -> fmt::Result {
            write!(f, "<expr: TODO>")
        }
    }
}






fn main() {
    let tree = Element::Function {
        vis: Visibility::Public,
        constant: true,
        inline: true,
        ty: Type {
            tags: vec![TypeTag::Pointer, TypeTag::Array { length: 8 }, TypeTag::Pointer],
            name: "uint8".into()
        },
        path: vec!["Struct".into(), "function".into()],
        arguments: vec![
            (
                Type {
                    tags: vec![TypeTag::Pointer],
                    name: "uint8".into()
                },
                "arg1".to_string()
            ),
            (
                Type {
                    tags: vec![TypeTag::Array { length: 8 }],
                    name: "float32".into()
                },
                "arg2".to_string()
            )
        ],
        block: vec![
            Statement::Expression(Expression::Atom(Atom)),
            Statement::Expression(Expression::Atom(Atom)),
            Statement::Expression(Expression::Atom(Atom)),
            Statement::If {
                cases: vec![
                    (
                        Expression::Binary { lhs: Box::new(Expression::Atom(Atom)), opr: Infix::Equal, rhs: Box::new(Expression::Atom(Atom)) },
                        vec![Statement::Expression(Expression::Atom(Atom)), Statement::Expression(Expression::Atom(Atom))]
                    ),
                    (
                        Expression::Unary { opr: UnaryOperand::Not, expr: Box::new(Expression::Atom(Atom)), },
                        vec![Statement::Expression(Expression::Atom(Atom)), Statement::Expression(Expression::Atom(Atom))]
                    )
                ],
                fallback: Some(vec![Statement::Expression(Expression::Atom(Atom)), Statement::Expression(Expression::Atom(Atom))])
            }
        ],
    };

    println!("{tree:#}")
}

