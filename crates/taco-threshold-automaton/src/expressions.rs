//! Type definitions for arithmetic and boolean expressions over components
//! of a threshold automaton
//!
//! This module contains the low-level expressions that make up a threshold
//! automaton. These expressions are for example, what here is named `Atomic`
//! expressions, such as
//! - [`Parameter`]s
//! - [`Location`]s, and
//! - [`Variable`]s.
//!
//! These expressions all have to implement the `Atomic` trait, which allows
//! them to be used in constraints.
//!
//! Constraints, in the most general form are represented by
//! [`IntegerExpression`]s that are combined into [`BooleanExpression`]s by
//! comparing them using Comparison operators ([`ComparisonOp`]).
//!
//! Note that the expressions defined here, are more general than what is
//! allowed in the theoretical threshold automaton framework, which is why most
//! model checkers work on a transformed version.

use std::{
    fmt::{Debug, Display},
    hash::Hash,
};

pub mod fraction;
pub mod properties;

/// Trait for expressions that support conjunctions
///
/// This trait is implemented by expressions that support conjunctions, like
/// boolean expressions over variables or parameters
pub trait And {
    /// Get the conjunction of `self` and `other`
    fn and(self, other: Self) -> Self;
}

/// Implements `BitAnd` for type by delegating to [`And::and`]
///
/// A blanket `impl<T: And> BitAnd for T` is not allowed, therefore
/// implementations can be derived using this macros instead
#[macro_export]
macro_rules! impl_bitand {
    ($($ty:ty),+ $(,)?) => {
        $(
            impl std::ops::BitAnd for $ty {
                type Output = Self;

                fn bitand(self, rhs: Self) -> Self::Output {
                    self.and(rhs)
                }
            }
        )+
    };
}

/// Trait for expressions that support building disjunctions
///
/// This trait is implemented by expressions that support disjunctions, like
/// boolean expressions over variables or parameters
pub trait Or {
    /// Get the disjunction of `self` and `other`
    fn or(self, other: Self) -> Self;
}

/// Implements `BitOr` for type by delegating to [`Or::or`]
///
/// A blanket `impl<T: Or> BitOr for T` is not allowed, therefore
/// implementations can be derived using this macros instead
#[macro_export]
macro_rules! impl_bitor {
    ($($ty:ty),+ $(,)?) => {
        $(
            impl std::ops::BitOr for $ty {
                type Output = Self;

                fn bitor(self, rhs: Self) -> Self::Output {
                    self.or(rhs)
                }
            }
        )+
    };
}

/// Atomic trait implemented by atomic expressions
///
/// This trait is implemented by types that can be used in atomic expressions,
/// i.e., for threshold automata these can be parameters, variables, and
/// locations.
///
/// All atomic expressions have a name associated with them, that must be unique
/// within the threshold automaton.
pub trait Atomic: Debug + Display + Hash + Clone + Eq + for<'a> From<&'a str> + Ord {
    /// Returns the name of the atom
    fn name(&self) -> &str;
}

/// Trait for checking if an object of type `T` has already been declared
///
/// Objects implementing this trait can be used during parsing to check if
/// a location, variable or parameter is known. This is useful to validate
/// parsed expressions, e.g., LTL expressions or update expressions, to ensure
/// that expressions only reference known locations, variables and parameters.
pub trait IsDeclared<T> {
    /// Check if object of type T is declared
    fn is_declared(&self, obj: &T) -> bool;
}

/// Parameter appearing in a threshold automaton
///
/// Parameters are used to represent for example the number of processes and
/// faulty processes. They are constrained by the resilience conditions and do
/// not change during execution. Typical parameter names are n, t and f.
#[derive(Debug, PartialEq, Eq, Hash, Clone, PartialOrd, Ord)]
pub struct Parameter(String);
impl Parameter {
    /// Create a new parameter with given name
    pub fn new(name: impl ToString) -> Self {
        Parameter(name.to_string())
    }
}

impl From<&str> for Parameter {
    fn from(s: &str) -> Self {
        Parameter::new(s)
    }
}

impl Atomic for Parameter {
    fn name(&self) -> &str {
        &self.0
    }
}

/// Shared variable used in a threshold automaton
///
/// Transitions in a threshold automaton can be guarded with constraints over a
/// shared variable valuation and can be updated when taking a transition.
#[derive(Debug, PartialEq, Eq, Hash, Clone, PartialOrd, Ord)]
pub struct Variable(String);
impl Variable {
    /// Create a new variable with given name
    pub fn new(name: impl ToString) -> Self {
        Variable(name.to_string())
    }
}

impl From<&str> for Variable {
    fn from(value: &str) -> Self {
        Variable::new(value)
    }
}

impl Atomic for Variable {
    fn name(&self) -> &str {
        &self.0
    }
}

/// Location of a threshold automaton
///
/// A location is a state in the threshold automaton template.
#[derive(Debug, PartialEq, Eq, Hash, Clone, PartialOrd, Ord)]
pub struct Location(String);

impl Location {
    /// Create a new location with given name
    pub fn new(name: impl ToString) -> Self {
        Location(name.to_string())
    }
}

impl From<&str> for Location {
    fn from(value: &str) -> Self {
        Location::new(value)
    }
}

impl Atomic for Location {
    fn name(&self) -> &str {
        &self.0
    }
}

/// Boolean constraint over type T
///
/// This enum represents a boolean expression over integer expressions and
/// can be used to for example guards in rules of a threshold automaton.
///
/// # Example
///
/// ```
/// use taco_threshold_automaton::expressions::*;
///
/// // y > 0
/// let _ = BooleanExpression::ComparisonExpression(
///     Box::new(IntegerExpression::Atom(Variable::new("y"))),
///     ComparisonOp::Gt,
///     Box::new(IntegerExpression::Const(0))
/// );
///
/// // x > 0 && y < 10
/// let _ = BooleanExpression::ComparisonExpression(
///           Box::new(IntegerExpression::Atom(Variable::new("x"))),
///           ComparisonOp::Gt,
///           Box::new(IntegerExpression::Const(0)),
///    ) & BooleanExpression::ComparisonExpression(
///           Box::new(IntegerExpression::Atom(Variable::new("y"))),
///           ComparisonOp::Lt,
///           Box::new(IntegerExpression::Const(10)),
///     );
/// ```
#[derive(Debug, PartialEq, Eq, Hash, Clone, PartialOrd, Ord)]
pub enum BooleanExpression<T: Atomic> {
    /// Comparison between two integer expressions
    ComparisonExpression(
        Box<IntegerExpression<T>>,
        ComparisonOp,
        Box<IntegerExpression<T>>,
    ),
    /// Boolean expressions combined through boolean connective
    BinaryExpression(
        Box<BooleanExpression<T>>,
        BooleanConnective,
        Box<BooleanExpression<T>>,
    ),
    /// Negation of boolean expression
    Not(Box<BooleanExpression<T>>),
    /// true
    True,
    /// false
    False,
}

/// Integer expressions over objects of type T, parameters and integers
///
/// This enum represents integer expressions over objects of type T, parameters and integers.
///
/// # Example
///
/// ```
/// use taco_threshold_automaton::expressions::*;
///
/// // x + 5
/// let _ = IntegerExpression::Atom(Variable::new("x"))
///             + IntegerExpression::Const(5);
///
/// // -x
/// let _ = -IntegerExpression::Atom(Variable::new("x"));
/// ```
#[derive(Debug, PartialEq, Eq, Hash, Clone, PartialOrd, Ord)]
pub enum IntegerExpression<T: Atomic> {
    /// Atomic of type T
    Atom(T),
    /// Integer constant
    Const(u32),
    /// Parameter
    Param(Parameter),
    /// Integer expression combining two Integer expressions through an arithmetic operator
    BinaryExpr(
        Box<IntegerExpression<T>>,
        IntegerOp,
        Box<IntegerExpression<T>>,
    ),
    /// Negated expression
    Neg(Box<IntegerExpression<T>>),
}

/// Operators for comparing integer values
#[derive(Debug, PartialEq, Eq, Hash, Clone, Copy, PartialOrd, Ord)]
pub enum ComparisonOp {
    /// Greater
    Gt,
    /// Greater equal
    Geq,
    /// Equal
    Eq,
    /// Not equal
    Neq,
    /// Less equal
    Leq,
    /// Less
    Lt,
}

/// Connectives for boolean expressions
#[derive(Debug, PartialEq, Eq, Hash, Clone, Copy, PartialOrd, Ord)]
pub enum BooleanConnective {
    /// And
    And,
    /// Or
    Or,
}

/// Binary operators for Integer expressions
#[derive(Debug, PartialEq, Eq, Hash, Clone, Copy, PartialOrd, Ord)]
pub enum IntegerOp {
    /// Addition
    Add,
    /// Subtraction
    Sub,
    /// Multiplication
    Mul,
    /// Division
    Div,
}

impl Display for Parameter {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.0)
    }
}

impl Display for Location {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.0)
    }
}

impl Display for Variable {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.0)
    }
}

impl<T: Atomic> Display for BooleanExpression<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            BooleanExpression::ComparisonExpression(lhs, op, rhs) => {
                write!(f, "{lhs} {op} {rhs}")
            }
            BooleanExpression::BinaryExpression(lhs, op, rhs) => {
                write!(f, "({lhs} {op} {rhs})")
            }
            BooleanExpression::True => write!(f, "true"),
            BooleanExpression::False => write!(f, "false"),
            BooleanExpression::Not(b) => write!(f, "!{b}"),
        }
    }
}

impl<T: Atomic> Display for IntegerExpression<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            IntegerExpression::Atom(a) => write!(f, "{a}"),
            IntegerExpression::Const(c) => write!(f, "{c}"),
            IntegerExpression::Param(p) => write!(f, "{p}"),
            IntegerExpression::BinaryExpr(lhs, op, rhs) => write!(f, "({lhs} {op} {rhs})"),
            IntegerExpression::Neg(ex) => write!(f, "-{ex}"),
        }
    }
}

impl Display for ComparisonOp {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            ComparisonOp::Gt => write!(f, ">"),
            ComparisonOp::Geq => write!(f, ">="),
            ComparisonOp::Eq => write!(f, "=="),
            ComparisonOp::Neq => write!(f, "!="),
            ComparisonOp::Leq => write!(f, "<="),
            ComparisonOp::Lt => write!(f, "<"),
        }
    }
}

impl Display for BooleanConnective {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            BooleanConnective::And => write!(f, "&&"),
            BooleanConnective::Or => write!(f, "||"),
        }
    }
}

impl Display for IntegerOp {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            IntegerOp::Add => write!(f, "+"),
            IntegerOp::Sub => write!(f, "-"),
            IntegerOp::Mul => write!(f, "*"),
            IntegerOp::Div => write!(f, "/"),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_parameter_new() {
        let param = Parameter::new("n");
        assert_eq!(param.0, "n");
    }

    #[test]
    fn test_variable_new() {
        let var = Variable::new("x");
        assert_eq!(var.0, "x");
    }

    #[test]
    fn test_location_new() {
        let loc = Location::new("start");
        assert_eq!(loc.0, "start");
    }

    #[test]
    fn test_constraint_display() {
        let lhs = IntegerExpression::Atom(Variable::new("x"));
        let rhs = IntegerExpression::Const(5);
        let constraint = BooleanExpression::ComparisonExpression(
            Box::new(lhs),
            ComparisonOp::Geq,
            Box::new(rhs),
        );
        assert_eq!(constraint.to_string(), "x >= 5");
    }

    #[test]
    fn test_integer_expression_display() {
        let lhs = IntegerExpression::Atom(Variable::new("x"));
        let rhs = IntegerExpression::Const(5);
        let expr = IntegerExpression::BinaryExpr(Box::new(lhs), IntegerOp::Add, Box::new(rhs));
        assert_eq!(expr.to_string(), "(x + 5)");
    }

    #[test]
    fn test_comparison_op_display() {
        assert_eq!(ComparisonOp::Gt.to_string(), ">");
        assert_eq!(ComparisonOp::Geq.to_string(), ">=");
        assert_eq!(ComparisonOp::Eq.to_string(), "==");
        assert_eq!(ComparisonOp::Neq.to_string(), "!=");
        assert_eq!(ComparisonOp::Leq.to_string(), "<=");
        assert_eq!(ComparisonOp::Lt.to_string(), "<");
    }

    #[test]
    fn test_boolean_connective_display() {
        assert_eq!(BooleanConnective::And.to_string(), "&&");
        assert_eq!(BooleanConnective::Or.to_string(), "||");
    }

    #[test]
    fn test_arithmetic_op_display() {
        assert_eq!(IntegerOp::Add.to_string(), "+");
        assert_eq!(IntegerOp::Sub.to_string(), "-");
        assert_eq!(IntegerOp::Mul.to_string(), "*");
        assert_eq!(IntegerOp::Div.to_string(), "/");
    }

    #[test]
    fn test_negated_expression_display() {
        let expr = -IntegerExpression::Atom(Variable::new("x"));
        assert_eq!(expr.to_string(), "-x");
    }

    #[test]
    fn test_binary_boolean_expression_display() {
        let lhs = BooleanExpression::ComparisonExpression(
            Box::new(IntegerExpression::Atom(Variable::new("x"))),
            ComparisonOp::Gt,
            Box::new(IntegerExpression::Const(0)),
        );
        let rhs = BooleanExpression::ComparisonExpression(
            Box::new(IntegerExpression::Atom(Variable::new("y"))),
            ComparisonOp::Lt,
            Box::new(IntegerExpression::Const(10)),
        );
        let expr = lhs & rhs;
        assert_eq!(expr.to_string(), "(x > 0 && y < 10)");
    }

    #[test]
    fn test_true_boolean_expression_display() {
        let expr: BooleanExpression<Location> = BooleanExpression::True;
        assert_eq!(expr.to_string(), "true");
    }

    #[test]
    fn test_false_boolean_expression_display() {
        let expr: BooleanExpression<Location> = BooleanExpression::False;
        assert_eq!(expr.to_string(), "false");
    }

    #[test]
    fn test_not_boolean_expression_display() {
        let expr: BooleanExpression<Location> = !BooleanExpression::True;
        assert_eq!(expr.to_string(), "!true");
    }
}
