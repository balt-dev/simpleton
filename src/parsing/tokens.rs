//! Language constructs defining the AST of the language.

/// Alias for referencing a block of statements.
pub type Block = Vec<Statement>;

#[derive(Debug, Clone, PartialEq)]
/// A single top-level language element.
pub enum Element {
    /// Import a module from a path.
    Import {
        /// This import's visibility rule.
        vis: Visibility,
        /// This import's module path.
        path: Vec<String>
    },
    /// Import code from an object file relative to this file.
    /// This may be a `.so` or a `.dll`, depending on the platform.
    ExternalImport {
        /// This external import's visibility rule.
        vis: Visibility,
        /// This external import's file path.
        path: String
    },
    /// A struct.
    Struct {
        /// This struct's visibility rule.
        vis: Visibility,
        /// This struct's name.
        name: String,
        /// This struct's fields.
        fields: Vec<(Visibility, Type, String)>
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
        value: Expression
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
        value: Expression
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
        variants: (String, u64)
    },
    /// A union.
    Union {
        /// This union's visibility rule.
        vis: Visibility,
        /// This union's name.
        name: String,
        /// This union's representations.
        reprs: Vec<(Visibility, Type, String)>
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
        /// This function's name.
        name: String,
        /// This function's arguments.
        arguments: Vec<(Type, String)>,
        /// This function's body.
        block: Block
    }
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
        fallback: Option<Block>
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
        inner: Block
    },
    /// A while loop.
    While {
        /// The expression to check every iteration.
        check: Expression,
        /// The block to run every iteration.
        inner: Block
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
        expr: Option<Expression>
    }
}

type BoxedExp = Box<Expression>;

#[derive(Debug, Clone, PartialEq, Eq)]
/// An expression - that is, an aggregation of binary and unary operators between [atoms](Atom).
pub enum Expression {
    Binary {
        /// The left-hand side of the expression.
        lhs: BoxedExp,
        /// The infix for this binary expression.
        opr: Infix,
        /// The right-hand side of the expression.
        rhs: BoxedExp
    },
    Unary {
        /// The prefix or postfix for this expression.
        opr: UnaryOperand,
        /// The expression to which the unary operator is being applied.
        expr: BoxedExp
    },
    Atom(Atom)
}

/// Represents an infix operand for an expression.
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
    /// Compares the two values, returning an `int8` where `-1` means the left hand is less, 
    /// `1` means the left hand is greater, `0` means they're equal,
    /// and `127` means they're otherwise not equal (e.g. NaN).
    /// For non-NaN numbers, this is equivalent to `sign(lhs - rhs)`.
    Spaceship,
    /// Bit-shifts the left hand side to the left by the right hand side.
    ShiftLeft,
    /// Bit-shifts the left hand side to the right by the right hand side.
    /// For unsigned types, this is a logical shift.
    /// For signed types, this is an arithmetic shift.
    ShiftRight
    
}

/// Represents either a prefix or postfix operand for an expression.
#[derive(Debug, Clone, PartialEq, Eq)]
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
    Cast(Type)
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
/// A visibility specifier for an element.
pub enum Visibility {
    #[default]
    /// Restricted to this module.
    Private,
    /// Unrestricted access.
    Public
}


#[derive(Debug, Clone, PartialEq, Eq)]
/// A specified type.
pub struct Type {
    /// The preceding tags of this type.
    pub tags: Vec<TypeTag>,
    /// The type's name.
    pub name: String
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
/// A tag prefixing a type specification.
pub enum TypeTag {
    /// Type is a pointer to a value.
    Pointer,
    /// Type is an array of values with a length.
    Array { length: u64 },
}
