//! Restricted version of LTL expressions without negations and implications.
//!
//! This module contains the logic to convert general LTL expressions into a
//! more restricted form, which does not contain negations and implications.
//!
//! Negations are pushed down to the atomic expressions, and implications are
//! transformed into disjunctions.
//!
//! This type is a more restricted version of LTL expressions, yet is equally
//! expressive. Therefore, it is easier to work with and to implement algorithms
//! for.

use std::fmt;

use taco_threshold_automaton::expressions::{
    ComparisonOp, IntegerExpression, Location, Parameter, Variable,
};

use super::ELTLExpression;

/// LTL Expression without negations and implications
#[derive(Debug, PartialEq, Clone)]
pub enum NonNegatedELTLExpression {
    /// Globally □
    Globally(Box<NonNegatedELTLExpression>),
    /// Eventually ◇
    Eventually(Box<NonNegatedELTLExpression>),
    /// And ∧
    And(Box<NonNegatedELTLExpression>, Box<NonNegatedELTLExpression>),
    /// Or ∨
    Or(Box<NonNegatedELTLExpression>, Box<NonNegatedELTLExpression>),
    /// Boolean constraint over the number of processes in a location
    LocationExpr(
        Box<IntegerExpression<Location>>,
        ComparisonOp,
        Box<IntegerExpression<Location>>,
    ),
    /// Boolean constraint over the value of a variable
    VariableExpr(
        Box<IntegerExpression<Variable>>,
        ComparisonOp,
        Box<IntegerExpression<Variable>>,
    ),
    /// Boolean constraint over parameters
    ParameterExpr(
        Box<IntegerExpression<Parameter>>,
        ComparisonOp,
        Box<IntegerExpression<Parameter>>,
    ),
    /// Always true
    True,
    /// Always false
    False,
}

impl ELTLExpression {
    /// Remove boolean negations from an expression, transforming the expression
    /// into a `NonNegatedELTLExpression` expression.
    ///
    /// This method is used to remove negations and implications from an LTL
    /// expression. Implications are simply transformed into disjunctions, and
    /// negations are pushed down to the atomic expressions.
    ///
    /// # Example
    ///
    /// ```rust
    /// use taco_model_checker::eltl::ELTLExpression;
    /// use taco_threshold_automaton::expressions::{ComparisonOp, Variable, IntegerExpression};
    /// use taco_model_checker::eltl::remove_negations::NonNegatedELTLExpression;
    ///
    /// // (1 = 2) => (x = 1)
    /// let ltl = ELTLExpression::Implies(
    ///     Box::new(ELTLExpression::LocationExpr(
    ///         Box::new(IntegerExpression::Const(1)),
    ///         ComparisonOp::Eq,
    ///         Box::new(IntegerExpression::Const(2)),
    ///     )),
    ///     Box::new(ELTLExpression::VariableExpr(
    ///         Box::new(IntegerExpression::Atom(Variable::new("x"))),
    ///         ComparisonOp::Eq,
    ///         Box::new(IntegerExpression::Const(1)),
    ///     )),
    /// );
    ///
    /// let non_negated_ltl = ltl.remove_negations();
    ///
    /// // (1 != 2) ∨ (x = 1)
    /// let expected = NonNegatedELTLExpression::Or(
    ///     Box::new(NonNegatedELTLExpression::LocationExpr(
    ///         Box::new(IntegerExpression::Const(1)),
    ///         ComparisonOp::Neq,
    ///         Box::new(IntegerExpression::Const(2)),
    ///     )),
    ///     Box::new(NonNegatedELTLExpression::VariableExpr(
    ///         Box::new(IntegerExpression::Atom(Variable::new("x"))),
    ///         ComparisonOp::Eq,
    ///         Box::new(IntegerExpression::Const(1)),
    ///    )),
    /// );
    ///
    /// assert_eq!(non_negated_ltl, expected);
    /// ```
    pub fn remove_negations(&self) -> NonNegatedELTLExpression {
        match self {
            ELTLExpression::Implies(lhs, rhs) => {
                // (a → b) ≡ ¬a ∨ b
                let lhs = lhs.negate_expression();
                let rhs = rhs.remove_negations();

                NonNegatedELTLExpression::Or(Box::new(lhs), Box::new(rhs))
            }
            ELTLExpression::Globally(expr) => {
                let expr = expr.remove_negations();
                NonNegatedELTLExpression::Globally(Box::new(expr))
            }
            ELTLExpression::Eventually(expr) => {
                let expr = expr.remove_negations();
                NonNegatedELTLExpression::Eventually(Box::new(expr))
            }
            ELTLExpression::And(lhs, rhs) => {
                let lhs = lhs.remove_negations();
                let rhs = rhs.remove_negations();
                NonNegatedELTLExpression::And(Box::new(lhs), Box::new(rhs))
            }
            ELTLExpression::Or(lhs, rhs) => {
                let lhs = lhs.remove_negations();
                let rhs = rhs.remove_negations();
                NonNegatedELTLExpression::Or(Box::new(lhs), Box::new(rhs))
            }
            ELTLExpression::Not(expr) => expr.negate_expression(),
            ELTLExpression::LocationExpr(lhs, comparison_op, rhs) => {
                let lhs = lhs.clone();
                let rhs = rhs.clone();
                NonNegatedELTLExpression::LocationExpr(lhs, *comparison_op, rhs)
            }
            ELTLExpression::VariableExpr(lhs, comparison_op, rhs) => {
                let lhs = lhs.clone();
                let rhs = rhs.clone();
                NonNegatedELTLExpression::VariableExpr(lhs, *comparison_op, rhs)
            }
            ELTLExpression::ParameterExpr(lhs, comparison_op, rhs) => {
                let lhs = lhs.clone();
                let rhs = rhs.clone();
                NonNegatedELTLExpression::ParameterExpr(lhs, *comparison_op, rhs)
            }
            ELTLExpression::True => NonNegatedELTLExpression::True,
            ELTLExpression::False => NonNegatedELTLExpression::False,
        }
    }

    fn negate_expression(&self) -> NonNegatedELTLExpression {
        match self {
            ELTLExpression::Implies(lhs, rhs) => {
                // ¬(a → b) ≡ a ∧ ¬b
                let lhs = lhs.remove_negations();
                let rhs = rhs.negate_expression();

                NonNegatedELTLExpression::And(Box::new(lhs), Box::new(rhs))
            }
            ELTLExpression::Globally(expr) => {
                let expr = expr.negate_expression();
                NonNegatedELTLExpression::Eventually(Box::new(expr))
            }
            ELTLExpression::Eventually(expr) => {
                let expr = expr.negate_expression();
                NonNegatedELTLExpression::Globally(Box::new(expr))
            }
            ELTLExpression::And(lhs, rhs) => {
                let lhs = lhs.negate_expression();
                let rhs = rhs.negate_expression();
                NonNegatedELTLExpression::Or(Box::new(lhs), Box::new(rhs))
            }
            ELTLExpression::Or(lhs, rhs) => {
                let lhs = lhs.negate_expression();
                let rhs = rhs.negate_expression();
                NonNegatedELTLExpression::And(Box::new(lhs), Box::new(rhs))
            }
            ELTLExpression::Not(expr) => expr.remove_negations(),
            ELTLExpression::LocationExpr(lhs, op, rhs) => {
                let lhs = lhs.clone();
                let rhs = rhs.clone();
                NonNegatedELTLExpression::LocationExpr(lhs, op.invert(), rhs)
            }
            ELTLExpression::VariableExpr(lhs, op, rhs) => {
                let lhs = lhs.clone();
                let rhs = rhs.clone();
                NonNegatedELTLExpression::VariableExpr(lhs, op.invert(), rhs)
            }
            ELTLExpression::ParameterExpr(lhs, op, rhs) => {
                let lhs = lhs.clone();
                let rhs = rhs.clone();
                NonNegatedELTLExpression::ParameterExpr(lhs, op.invert(), rhs)
            }
            ELTLExpression::True => NonNegatedELTLExpression::False,
            ELTLExpression::False => NonNegatedELTLExpression::True,
        }
    }
}

impl From<ELTLExpression> for NonNegatedELTLExpression {
    fn from(value: ELTLExpression) -> Self {
        value.remove_negations()
    }
}

impl fmt::Display for NonNegatedELTLExpression {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            NonNegatedELTLExpression::Globally(expression) => write!(f, "[]({expression})"),
            NonNegatedELTLExpression::Eventually(expression) => write!(f, "<>({expression})"),
            NonNegatedELTLExpression::And(lhs, rhs) => write!(f, "({lhs}) && ({rhs})"),
            NonNegatedELTLExpression::Or(lhs, rhs) => write!(f, "({lhs}) || ({rhs})"),
            NonNegatedELTLExpression::LocationExpr(lhs, op, rhs) => write!(f, "{lhs} {op} {rhs}"),
            NonNegatedELTLExpression::VariableExpr(lhs, op, rhs) => write!(f, "{lhs} {op} {rhs}"),
            NonNegatedELTLExpression::ParameterExpr(lhs, op, rhs) => write!(f, "{lhs} {op} {rhs}"),
            NonNegatedELTLExpression::True => write!(f, "true"),
            NonNegatedELTLExpression::False => write!(f, "false"),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use taco_threshold_automaton::expressions::{ComparisonOp, IntegerExpression, Variable};

    #[test]
    fn test_remove_negations_trivial() {
        let ltl = ELTLExpression::True;
        let non_negated_ltl = ltl.remove_negations();
        let expected = NonNegatedELTLExpression::True;
        assert_eq!(non_negated_ltl, expected);

        let ltl = ELTLExpression::False;
        let non_negated_ltl = ltl.remove_negations();
        let expected = NonNegatedELTLExpression::False;
        assert_eq!(non_negated_ltl, expected);

        let ltl = ELTLExpression::Not(Box::new(ELTLExpression::False));
        let non_negated_ltl = ltl.remove_negations();
        let expected = NonNegatedELTLExpression::True;
        assert_eq!(non_negated_ltl, expected);

        let ltl = ELTLExpression::Not(Box::new(ELTLExpression::True));
        let non_negated_ltl = ltl.remove_negations();
        let expected = NonNegatedELTLExpression::False;
        assert_eq!(non_negated_ltl, expected);
    }

    #[test]
    fn test_remove_negations() {
        // (1 = 2) => (x = 1)
        let ltl = ELTLExpression::Implies(
            Box::new(ELTLExpression::LocationExpr(
                Box::new(IntegerExpression::Const(1)),
                ComparisonOp::Eq,
                Box::new(IntegerExpression::Const(2)),
            )),
            Box::new(ELTLExpression::VariableExpr(
                Box::new(IntegerExpression::Atom(Variable::new("x"))),
                ComparisonOp::Eq,
                Box::new(IntegerExpression::Const(1)),
            )),
        );

        let non_negated_ltl = ltl.remove_negations();

        // (1 != 2) ∨ (x = 1)
        let expected = NonNegatedELTLExpression::Or(
            Box::new(NonNegatedELTLExpression::LocationExpr(
                Box::new(IntegerExpression::Const(1)),
                ComparisonOp::Neq,
                Box::new(IntegerExpression::Const(2)),
            )),
            Box::new(NonNegatedELTLExpression::VariableExpr(
                Box::new(IntegerExpression::Atom(Variable::new("x"))),
                ComparisonOp::Eq,
                Box::new(IntegerExpression::Const(1)),
            )),
        );

        assert_eq!(non_negated_ltl, expected);
    }

    #[test]
    fn test_remove_negations_nested() {
        // ¬(□(1 = 2) ∧ ◇(x = 1))
        let ltl = ELTLExpression::Not(Box::new(ELTLExpression::And(
            Box::new(ELTLExpression::Globally(Box::new(
                ELTLExpression::LocationExpr(
                    Box::new(IntegerExpression::Const(1)),
                    ComparisonOp::Eq,
                    Box::new(IntegerExpression::Const(2)),
                ),
            ))),
            Box::new(ELTLExpression::Eventually(Box::new(
                ELTLExpression::VariableExpr(
                    Box::new(IntegerExpression::Atom(Variable::new("x"))),
                    ComparisonOp::Eq,
                    Box::new(IntegerExpression::Const(1)),
                ),
            ))),
        )));

        let non_negated_ltl = ltl.remove_negations();

        // (◇(1 != 2) ∨ □(x != 1))
        let expected = NonNegatedELTLExpression::Or(
            Box::new(NonNegatedELTLExpression::Eventually(Box::new(
                NonNegatedELTLExpression::LocationExpr(
                    Box::new(IntegerExpression::Const(1)),
                    ComparisonOp::Neq,
                    Box::new(IntegerExpression::Const(2)),
                ),
            ))),
            Box::new(NonNegatedELTLExpression::Globally(Box::new(
                NonNegatedELTLExpression::VariableExpr(
                    Box::new(IntegerExpression::Atom(Variable::new("x"))),
                    ComparisonOp::Neq,
                    Box::new(IntegerExpression::Const(1)),
                ),
            ))),
        );

        assert_eq!(non_negated_ltl, expected);
    }

    #[test]
    fn test_negated_or() {
        // □(◇(¬((1 = 2) ∨ ¬(x = 1)))
        let ltl = ELTLExpression::Globally(Box::new(ELTLExpression::Eventually(Box::new(
            ELTLExpression::Not(Box::new(ELTLExpression::Or(
                Box::new(ELTLExpression::LocationExpr(
                    Box::new(IntegerExpression::Const(1)),
                    ComparisonOp::Eq,
                    Box::new(IntegerExpression::Const(2)),
                )),
                Box::new(ELTLExpression::Not(Box::new(ELTLExpression::LocationExpr(
                    Box::new(IntegerExpression::Atom(Location::new("x"))),
                    ComparisonOp::Eq,
                    Box::new(IntegerExpression::Const(1)),
                )))),
            ))),
        ))));
        let non_negated_ltl = ltl.remove_negations();

        // □(◇(1 != 2 ∧ x = 1))
        let expected = NonNegatedELTLExpression::Globally(Box::new(
            NonNegatedELTLExpression::Eventually(Box::new(NonNegatedELTLExpression::And(
                Box::new(NonNegatedELTLExpression::LocationExpr(
                    Box::new(IntegerExpression::Const(1)),
                    ComparisonOp::Neq,
                    Box::new(IntegerExpression::Const(2)),
                )),
                Box::new(NonNegatedELTLExpression::LocationExpr(
                    Box::new(IntegerExpression::Atom(Location::new("x"))),
                    ComparisonOp::Eq,
                    Box::new(IntegerExpression::Const(1)),
                )),
            ))),
        ));

        assert_eq!(non_negated_ltl, expected);
    }

    #[test]
    fn test_and_or() {
        // ((1 = 2) ∧ (x = 1)) ∨ (y = 2)
        let ltl = ELTLExpression::Or(
            Box::new(ELTLExpression::And(
                Box::new(ELTLExpression::LocationExpr(
                    Box::new(IntegerExpression::Const(1)),
                    ComparisonOp::Eq,
                    Box::new(IntegerExpression::Const(2)),
                )),
                Box::new(ELTLExpression::VariableExpr(
                    Box::new(IntegerExpression::Atom(Variable::new("x"))),
                    ComparisonOp::Eq,
                    Box::new(IntegerExpression::Const(1)),
                )),
            )),
            Box::new(ELTLExpression::LocationExpr(
                Box::new(IntegerExpression::Atom(Location::new("y"))),
                ComparisonOp::Eq,
                Box::new(IntegerExpression::Const(2)),
            )),
        );

        let non_negated_ltl = ltl.remove_negations();

        // ((1 = 2) ∧ (x = 1)) ∨  (y = 2)
        let expected = NonNegatedELTLExpression::Or(
            Box::new(NonNegatedELTLExpression::And(
                Box::new(NonNegatedELTLExpression::LocationExpr(
                    Box::new(IntegerExpression::Const(1)),
                    ComparisonOp::Eq,
                    Box::new(IntegerExpression::Const(2)),
                )),
                Box::new(NonNegatedELTLExpression::VariableExpr(
                    Box::new(IntegerExpression::Atom(Variable::new("x"))),
                    ComparisonOp::Eq,
                    Box::new(IntegerExpression::Const(1)),
                )),
            )),
            Box::new(NonNegatedELTLExpression::LocationExpr(
                Box::new(IntegerExpression::Atom(Location::new("y"))),
                ComparisonOp::Eq,
                Box::new(IntegerExpression::Const(2)),
            )),
        );

        assert_eq!(non_negated_ltl, expected);
    }

    #[test]
    fn test_double_neg() {
        // !(!((l < 1) && (v < 3)))
        let eltl = ELTLExpression::Not(Box::new(ELTLExpression::Not(Box::new(
            ELTLExpression::And(
                Box::new(ELTLExpression::LocationExpr(
                    Box::new(IntegerExpression::Atom(Location::new("l"))),
                    ComparisonOp::Lt,
                    Box::new(IntegerExpression::Const(1)),
                )),
                Box::new(ELTLExpression::VariableExpr(
                    Box::new(IntegerExpression::Atom(Variable::new("v"))),
                    ComparisonOp::Lt,
                    Box::new(IntegerExpression::Const(3)),
                )),
            ),
        ))));

        let non_negated_ltl = eltl.remove_negations();

        //(l < 1) && (v < 3)
        let expected = NonNegatedELTLExpression::And(
            Box::new(NonNegatedELTLExpression::LocationExpr(
                Box::new(IntegerExpression::Atom(Location::new("l"))),
                ComparisonOp::Lt,
                Box::new(IntegerExpression::Const(1)),
            )),
            Box::new(NonNegatedELTLExpression::VariableExpr(
                Box::new(IntegerExpression::Atom(Variable::new("v"))),
                ComparisonOp::Lt,
                Box::new(IntegerExpression::Const(3)),
            )),
        );

        assert_eq!(non_negated_ltl, expected);
    }
}
