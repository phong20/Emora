#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Span {
    pub start: u32,
    pub end: u32,
}

impl Span {
    pub const fn new(start: u32, end: u32) -> Self {
        Self { start, end }
    }
}

#[derive(Debug, Clone)]
pub struct Program {
    pub statements: Vec<Statement>,
    pub strict: bool,
    pub imports: Vec<ImportDeclaration>,
    pub exports: Vec<ExportBinding>,
    pub export_all: Vec<String>,
}

#[derive(Debug, Clone)]
pub struct ImportDeclaration {
    pub source: String,
    pub specifiers: Vec<ImportSpecifier>,
}

#[derive(Debug, Clone)]
pub enum ImportSpecifier {
    Named { imported: String, local: String },
    Default { local: String },
    Namespace { local: String },
}

#[derive(Debug, Clone)]
pub struct ExportBinding {
    pub local: String,
    pub exported: String,
    /// Present for `export { value } from "./module.js"`.
    pub source: Option<String>,
}

#[derive(Debug, Clone)]
pub struct Statement {
    pub kind: StatementKind,
    pub span: Span,
}

#[derive(Debug, Clone)]
pub enum StatementKind {
    Expression(Expression),
    VariableDeclaration {
        kind: VariableKind,
        declarations: Vec<VariableDeclarator>,
    },
    Block(Vec<Statement>),
    If {
        test: Expression,
        consequent: Box<Statement>,
        alternate: Option<Box<Statement>>,
    },
    While {
        test: Expression,
        body: Box<Statement>,
    },
    DoWhile {
        body: Box<Statement>,
        test: Expression,
    },
    For {
        init: Option<ForInit>,
        test: Option<Expression>,
        update: Option<Expression>,
        body: Box<Statement>,
    },
    ForIn {
        name: String,
        kind: VariableKind,
        right: Expression,
        body: Box<Statement>,
    },
    ForOf {
        name: String,
        kind: VariableKind,
        right: Expression,
        body: Box<Statement>,
    },
    Switch {
        discriminant: Expression,
        cases: Vec<SwitchCase>,
    },
    FunctionDeclaration(Function),
    Return(Option<Expression>),
    Throw(Expression),
    Break,
    Continue,
}

#[derive(Debug, Clone)]
pub enum ForInit {
    VariableDeclaration {
        kind: VariableKind,
        declarations: Vec<VariableDeclarator>,
    },
    Expression(Expression),
}

#[derive(Debug, Clone)]
pub struct SwitchCase {
    pub test: Option<Expression>,
    pub consequent: Vec<Statement>,
    pub span: Span,
}

#[derive(Debug, Clone)]
pub struct VariableDeclarator {
    pub name: String,
    pub init: Option<Expression>,
    pub span: Span,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum VariableKind {
    Const,
    Let,
}

#[derive(Debug, Clone)]
pub struct Expression {
    pub kind: ExpressionKind,
    pub span: Span,
}

#[derive(Debug, Clone)]
pub enum ExpressionKind {
    String(String),
    Number(f64),
    Bool(bool),
    Null,
    Global(String),
    Member {
        object: Box<Expression>,
        property: MemberProperty,
    },
    Object(Vec<ObjectEntry>),
    Array(Vec<ArrayElement>),
    Conditional {
        test: Box<Expression>,
        consequent: Box<Expression>,
        alternate: Box<Expression>,
    },
    Unary {
        operator: UnaryOperator,
        argument: Box<Expression>,
    },
    Binary {
        left: Box<Expression>,
        operator: BinaryOperator,
        right: Box<Expression>,
    },
    Logical {
        left: Box<Expression>,
        operator: LogicalOperator,
        right: Box<Expression>,
    },
    Assignment {
        target: AssignmentTarget,
        operator: AssignmentOperator,
        value: Box<Expression>,
    },
    Update {
        target: AssignmentTarget,
        operator: UpdateOperator,
        prefix: bool,
    },
    Call {
        callee: Box<Expression>,
        arguments: Vec<Expression>,
    },
    New {
        callee: Box<Expression>,
        arguments: Vec<Expression>,
    },
    Function(Function),
    Await(Box<Expression>),
}

#[derive(Debug, Clone)]
pub enum ArrayElement {
    Expression(Expression),
    Spread(Expression),
    Hole,
}

#[derive(Debug, Clone)]
pub struct Function {
    pub name: Option<String>,
    pub parameters: Vec<String>,
    pub body: Vec<Statement>,
    pub r#async: bool,
    pub arrow: bool,
    /// Function bodies are lowered lazily from the native pipeline's point of
    /// view. Unsupported syntax in an unreachable function must not force the
    /// whole module into compatibility mode.
    pub lowering_error: Option<String>,
}

#[derive(Debug, Clone)]
pub enum MemberProperty {
    Static(String),
    Computed(Box<Expression>),
}

#[derive(Debug, Clone)]
pub struct ObjectProperty {
    pub key: MemberProperty,
    pub value: Expression,
}

#[derive(Debug, Clone)]
pub enum ObjectEntry {
    Property(ObjectProperty),
    Spread(Expression),
    Accessor {
        key: String,
        get: Option<Expression>,
        set: Option<Expression>,
    },
}

#[derive(Debug, Clone)]
pub enum AssignmentTarget {
    Identifier(String),
    Member {
        object: Box<Expression>,
        property: MemberProperty,
    },
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum UpdateOperator {
    Increment,
    Decrement,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum UnaryOperator {
    Plus,
    Minus,
    Not,
    BitwiseNot,
    Typeof,
    Void,
    Delete,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum BinaryOperator {
    Add,
    Subtract,
    Multiply,
    Divide,
    Remainder,
    Exponential,
    Equal,
    NotEqual,
    StrictEqual,
    StrictNotEqual,
    LessThan,
    LessEqual,
    GreaterThan,
    GreaterEqual,
    ShiftLeft,
    ShiftRight,
    ShiftRightZeroFill,
    BitwiseOr,
    BitwiseXor,
    BitwiseAnd,
    In,
    InstanceOf,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum LogicalOperator {
    Or,
    And,
    Nullish,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum AssignmentOperator {
    Assign,
    Add,
    Subtract,
    Multiply,
    Divide,
    Remainder,
    Exponential,
    ShiftLeft,
    ShiftRight,
    ShiftRightZeroFill,
    BitwiseOr,
    BitwiseXor,
    BitwiseAnd,
    LogicalOr,
    LogicalAnd,
    LogicalNullish,
}
