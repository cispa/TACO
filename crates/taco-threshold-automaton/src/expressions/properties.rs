//! This module implements functionality for expressions, such as evaluations
//! under environments, and interfaces for expressions

use core::fmt;
use std::{collections::HashMap, error, ops};

use crate::expressions::{And, IntegerExpression, Location, Or, Variable};

use super::{Atomic, ComparisonOp, Parameter};
use super::{BooleanConnective, BooleanExpression, IntegerOp};

impl<T: Atomic> IntegerExpression<T> {
    /// Check whether the constraint is a parameter or atomic
    ///
    /// # Example
    ///
    /// ```
    /// use taco_threshold_automaton::expressions::{IntegerExpression, Parameter, Variable};
    ///
    /// let expr : IntegerExpression<Variable> = IntegerExpression::Param(Parameter::new("x"));
    /// assert_eq!(expr.is_atomic(), true);
    ///
    /// let expr : IntegerExpression<Variable> = IntegerExpression::Atom(Variable::new("x"));
    /// assert_eq!(expr.is_atomic(), true);
    ///
    /// let expr : IntegerExpression<Variable> = IntegerExpression::Const(1);
    /// assert_eq!(expr.is_atomic(), false);
    /// ```
    pub fn is_atomic(&self) -> bool {
        match self {
            IntegerExpression::Param(_) => true,
            IntegerExpression::Atom(_) => true,
            IntegerExpression::Const(_) => false,
            IntegerExpression::BinaryExpr(_, _, _) => false,
            IntegerExpression::Neg(_) => false,
        }
    }

    /// Recursively check if the expression contains some atom
    ///
    /// # Example
    ///
    /// ```
    /// use taco_threshold_automaton::expressions::{IntegerExpression, Parameter, Variable};
    ///
    /// let expr : IntegerExpression<Variable> = IntegerExpression::Atom(Variable::new("x"));
    /// assert_eq!(expr.contains_atom(), true);
    ///
    /// let expr : IntegerExpression<Variable> = IntegerExpression::Param(Parameter::new("x"));
    /// assert_eq!(expr.contains_atom(), false);
    ///
    /// let expr : IntegerExpression<Variable> = IntegerExpression::Param(Parameter::new("x"))
    ///     + IntegerExpression::Atom(Variable::new("x"));
    /// assert_eq!(expr.contains_atom(), true);
    /// ```
    pub fn contains_atom(&self) -> bool {
        match self {
            IntegerExpression::Atom(_) => true,
            IntegerExpression::Const(_) => false,
            IntegerExpression::Param(_) => false,
            IntegerExpression::Neg(ex) => ex.contains_atom(),
            IntegerExpression::BinaryExpr(lhs, _, rhs) => {
                lhs.contains_atom() || rhs.contains_atom()
            }
        }
    }

    /// Recursively check if the expression references the atom `a`
    ///
    /// # Example
    ///
    /// ```
    /// use taco_threshold_automaton::expressions::{IntegerExpression, Parameter, Variable};
    ///
    /// let expr : IntegerExpression<Variable> = IntegerExpression::Atom(Variable::new("x"));
    /// assert_eq!(expr.contains_atom_a(&Variable::new("x")), true);
    /// assert_eq!(expr.contains_atom_a(&Variable::new("y")), false);
    ///
    /// let expr : IntegerExpression<Variable> = IntegerExpression::Param(Parameter::new("x"));
    /// assert_eq!(expr.contains_atom_a(&Variable::new("x")), false);
    ///
    /// let expr : IntegerExpression<Variable> = IntegerExpression::Param(Parameter::new("x"))
    ///     + IntegerExpression::Atom(Variable::new("x"));
    /// assert_eq!(expr.contains_atom_a(&Variable::new("x")), true);
    /// assert_eq!(expr.contains_atom_a(&Variable::new("y")), false);
    /// ```
    pub fn contains_atom_a(&self, a: &T) -> bool {
        match self {
            IntegerExpression::Atom(at) => at == a,
            IntegerExpression::Const(_) => false,
            IntegerExpression::Param(_) => false,
            IntegerExpression::Neg(ex) => ex.contains_atom_a(a),
            IntegerExpression::BinaryExpr(lhs, _, rhs) => {
                lhs.contains_atom_a(a) || rhs.contains_atom_a(a)
            }
        }
    }

    /// Try to evaluate the integer expression to a constant
    ///
    /// This function succeeds if all sub-expressions are constants, otherwise
    /// it returns None.
    ///
    /// > **Note:** This function uses integer division (e.g. 5 / 2 = 2), be
    /// > careful when using for simplification.
    ///
    /// # Example
    ///
    /// ```
    /// use crate::taco_threshold_automaton::expressions::*;
    ///
    /// let expr = IntegerExpression::<Location>::Const(5)
    ///     + IntegerExpression::Const(3);
    /// assert_eq!(expr.try_to_evaluate_to_const(), Some(8));
    ///
    /// let expr = IntegerExpression::<Location>::Param(Parameter::new("n"));
    /// assert_eq!(expr.try_to_evaluate_to_const(), None);
    ///
    /// let expr = IntegerExpression::<Location>::Const(5)
    ///    / IntegerExpression::Const(2);
    /// assert_eq!(expr.try_to_evaluate_to_const(), Some(2));
    /// ```
    pub fn try_to_evaluate_to_const(&self) -> Option<i64> {
        self.try_to_evaluate_to_const_with_env(
            &HashMap::<T, u32>::new(),
            &HashMap::<Parameter, u32>::new(),
        )
        .ok()
    }

    /// Try to evaluate the integer expression in a given environment to a
    /// constant
    ///
    /// This function succeeds if all sub-expressions are constants, parameters
    /// or atoms with a value specified in environment `env` or `param_env`.
    ///
    /// If a parameter or atom is not found in the environment, an error is
    /// returned.
    ///
    /// > **Note:** This function uses integer division (e.g. 5 / 2 = 2), be
    /// > careful when using for simplification.
    ///
    /// # Example
    ///
    /// ```
    /// use crate::taco_threshold_automaton::expressions::*;
    /// use std::collections::HashMap;
    ///
    /// let env = HashMap::from([(Location::new("loc"), 1)]);
    /// let param_env = HashMap::from([(Parameter::new("n"), 1)]);
    ///
    /// let expr = IntegerExpression::<Location>::Const(5)
    ///    + IntegerExpression::Const(3);
    /// assert_eq!(expr.try_to_evaluate_to_const_with_env(&env, &param_env), Ok(8));
    ///
    /// let expr = IntegerExpression::<Location>::Const(5)
    ///    - IntegerExpression::Atom(Location::new("loc"));
    /// assert_eq!(expr.try_to_evaluate_to_const_with_env(&env, &param_env), Ok(4));
    ///
    /// let expr = IntegerExpression::<Location>::Const(5)
    ///    - IntegerExpression::Atom(Location::new("loc"))
    ///    - IntegerExpression::Param(Parameter::new("n"));
    /// assert_eq!(expr.try_to_evaluate_to_const_with_env(&env, &param_env), Ok(3));
    /// ```
    pub fn try_to_evaluate_to_const_with_env(
        &self,
        env: &HashMap<T, u32>,
        param_env: &HashMap<Parameter, u32>,
    ) -> Result<i64, EvaluationError<T>> {
        match self {
            IntegerExpression::Const(c) => Ok(*c as i64),
            IntegerExpression::Param(p) => {
                if param_env.contains_key(p) {
                    Ok(*param_env.get(p).unwrap() as i64)
                } else {
                    Err(EvaluationError::ParameterNotFound(p.clone()))
                }
            }
            IntegerExpression::Atom(a) => {
                if env.contains_key(a) {
                    Ok(*env.get(a).unwrap() as i64)
                } else {
                    Err(EvaluationError::AtomicNotFound(a.clone()))
                }
            }
            IntegerExpression::BinaryExpr(lhs, op, rhs) => {
                let lhs = lhs.try_to_evaluate_to_const_with_env(env, param_env)?;
                let rhs = rhs.try_to_evaluate_to_const_with_env(env, param_env)?;
                match op {
                    IntegerOp::Add => Ok(lhs + rhs),
                    IntegerOp::Sub => Ok(lhs - rhs),
                    IntegerOp::Mul => Ok(lhs * rhs),
                    IntegerOp::Div => Ok(lhs / rhs),
                }
            }
            IntegerExpression::Neg(ex) => ex
                .try_to_evaluate_to_const_with_env(env, param_env)
                .map(|c| -c),
        }
    }

    /// Substitute `to_replace` in this integer expression with integer
    /// expression `replace_with`
    ///
    /// # Example
    ///
    /// ```
    /// use crate::taco_threshold_automaton::expressions::*;
    ///
    /// let mut expr = IntegerExpression::Const(5)
    ///     + IntegerExpression::Atom(Location::new("l"));
    /// expr.substitute_atom_with(&Location::new("l"), &IntegerExpression::Const(3));
    ///
    /// let expected_expr = IntegerExpression::Const(5)
    ///     + IntegerExpression::Const(3);
    /// assert_eq!(expr, expected_expr);
    /// ```
    pub fn substitute_atom_with(&mut self, to_replace: &T, replace_with: &Self) {
        match self {
            IntegerExpression::Atom(a) => {
                if *a == *to_replace {
                    *self = replace_with.clone();
                }
            }

            IntegerExpression::BinaryExpr(lhs, _, rhs) => {
                lhs.substitute_atom_with(to_replace, replace_with);
                rhs.substitute_atom_with(to_replace, replace_with);
            }
            IntegerExpression::Neg(e) => e.substitute_atom_with(to_replace, replace_with),

            IntegerExpression::Const(_) | IntegerExpression::Param(_) => (),
        }
    }

    /// Check whether the expressions contains a [`IntegerExpression::Param`]
    /// clause
    ///
    /// This function checks whether an [`IntegerExpression`] contains a
    /// parameter.
    ///
    /// **Important**: For expressions of type [`IntegerExpression<Parameter>`]
    /// one needs to additionally check whether the expression contains an atom
    /// using [`IntegerExpression::contains_atom`].
    ///
    /// # Example
    ///
    /// ```
    /// use taco_threshold_automaton::expressions::{IntegerExpression, Parameter, Variable};
    ///
    /// let expr : IntegerExpression<Variable> = IntegerExpression::Param(Parameter::new("x"));
    /// assert_eq!(expr.contains_parameter(), true);
    ///
    /// let expr : IntegerExpression<Variable> = IntegerExpression::Const(1);
    /// assert_eq!(expr.contains_parameter(), false);
    ///
    /// // careful when using with `IntegerExpression<Parameter>`
    /// let expr : IntegerExpression<Parameter> = IntegerExpression::Atom(Parameter::new("x"));
    /// assert_eq!(expr.contains_parameter(), false);
    /// ```
    pub fn contains_parameter(&self) -> bool {
        match self {
            IntegerExpression::Atom(_) | IntegerExpression::Const(_) => false,
            IntegerExpression::Param(_) => true,
            IntegerExpression::BinaryExpr(lhs, _op, rhs) => {
                lhs.contains_parameter() || rhs.contains_parameter()
            }
            IntegerExpression::Neg(expr) => expr.contains_parameter(),
        }
    }
}

impl From<IntegerExpression<Parameter>> for IntegerExpression<Location> {
    fn from(value: IntegerExpression<Parameter>) -> Self {
        match value {
            IntegerExpression::Param(p) | IntegerExpression::Atom(p) => IntegerExpression::Param(p),
            IntegerExpression::Const(c) => IntegerExpression::Const(c),
            IntegerExpression::BinaryExpr(lhs, op, rhs) => {
                let lhs = Box::new((*lhs).into());
                let rhs = Box::new((*rhs).into());

                IntegerExpression::BinaryExpr(lhs, op, rhs)
            }
            IntegerExpression::Neg(integer_expression) => {
                IntegerExpression::Neg(Box::new((*integer_expression).into()))
            }
        }
    }
}

impl From<IntegerExpression<Parameter>> for IntegerExpression<Variable> {
    fn from(value: IntegerExpression<Parameter>) -> Self {
        match value {
            IntegerExpression::Param(p) | IntegerExpression::Atom(p) => IntegerExpression::Param(p),
            IntegerExpression::Const(c) => IntegerExpression::Const(c),
            IntegerExpression::BinaryExpr(lhs, op, rhs) => {
                let lhs = Box::new((*lhs).into());
                let rhs = Box::new((*rhs).into());

                IntegerExpression::BinaryExpr(lhs, op, rhs)
            }
            IntegerExpression::Neg(integer_expression) => {
                IntegerExpression::Neg(Box::new((*integer_expression).into()))
            }
        }
    }
}

/// Evaluation error of an expression
///
/// Error that can occur during the evaluation of an expression in an
/// environment.
#[derive(Debug, Clone, PartialEq)]
pub enum EvaluationError<T: fmt::Display + PartialEq + fmt::Debug> {
    /// Atomic was not found in the environment
    AtomicNotFound(T),
    /// Parameter was not found in the environment
    ParameterNotFound(Parameter),
}

impl<T: fmt::Display + PartialEq + fmt::Debug> error::Error for EvaluationError<T> {}

impl<T: fmt::Display + PartialEq + fmt::Debug> fmt::Display for EvaluationError<T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            EvaluationError::AtomicNotFound(t) => {
                write!(f, "Atomic {t} not found in environment")
            }
            EvaluationError::ParameterNotFound(p) => {
                write!(f, "Parameter {p} not found in environment")
            }
        }
    }
}

impl<T: Atomic> BooleanExpression<T> {
    /// Check whether the constraint is satisfied in the given environment
    ///
    /// This function evaluates the boolean expression in the given environment
    /// and returns whether the expression is satisfied.
    ///
    /// # Example
    ///
    /// ```
    /// use crate::taco_threshold_automaton::expressions::*;
    /// use std::collections::HashMap;
    /// use taco_threshold_automaton::expressions::properties::EvaluationError;
    ///
    /// let env = HashMap::from([(Location::new("loc"), 1)]);
    /// let param_env = HashMap::from([(Parameter::new("n"), 1)]);
    ///
    /// let expr: BooleanExpression<Location> = BooleanExpression::ComparisonExpression(
    ///     Box::new(IntegerExpression::Const(5)),
    ///     ComparisonOp::Eq,
    ///     Box::new(IntegerExpression::Const(5)),
    /// );
    /// assert_eq!(expr.check_satisfied(&env, &param_env), Ok(true));
    ///
    /// let expr = BooleanExpression::ComparisonExpression(
    ///     Box::new(IntegerExpression::Atom(Location::new("loc"))),
    ///     ComparisonOp::Eq,
    ///     Box::new(IntegerExpression::Const(1)),
    /// );
    /// assert_eq!(expr.check_satisfied(&env, &param_env), Ok(true));
    ///
    /// let expr = BooleanExpression::ComparisonExpression(
    ///     Box::new(IntegerExpression::Atom(Location::new("loc"))),
    ///     ComparisonOp::Gt,
    ///     Box::new(IntegerExpression::Const(1)),
    /// );
    /// assert_eq!(expr.check_satisfied(&env, &param_env), Ok(false));
    ///
    /// let expr = BooleanExpression::ComparisonExpression(
    ///     Box::new(IntegerExpression::Atom(Location::new("otherloc"))),
    ///     ComparisonOp::Gt,
    ///     Box::new(IntegerExpression::Const(1)),
    /// );
    /// assert_eq!(expr.check_satisfied(&env, &param_env), Err(EvaluationError::AtomicNotFound(Location::new("otherloc"))));
    /// ```
    pub fn check_satisfied(
        &self,
        env: &HashMap<T, u32>,
        param_env: &HashMap<Parameter, u32>,
    ) -> Result<bool, EvaluationError<T>> {
        match self {
            BooleanExpression::ComparisonExpression(rhs, op, lhs) => {
                let rhs = rhs
                    .as_ref()
                    .try_to_evaluate_to_const_with_env(env, param_env)?;
                let lhs = lhs
                    .as_ref()
                    .try_to_evaluate_to_const_with_env(env, param_env)?;
                match op {
                    ComparisonOp::Eq => Ok(rhs == lhs),
                    ComparisonOp::Neq => Ok(rhs != lhs),
                    ComparisonOp::Lt => Ok(rhs < lhs),
                    ComparisonOp::Leq => Ok(rhs <= lhs),
                    ComparisonOp::Gt => Ok(rhs > lhs),
                    ComparisonOp::Geq => Ok(rhs >= lhs),
                }
            }
            BooleanExpression::BinaryExpression(rhs, op, lhs) => {
                let rhs = rhs.check_satisfied(env, param_env)?;
                let lhs = lhs.check_satisfied(env, param_env)?;
                match op {
                    BooleanConnective::And => Ok(rhs && lhs),
                    BooleanConnective::Or => Ok(rhs || lhs),
                }
            }
            BooleanExpression::Not(expr) => Ok(!expr.check_satisfied(env, param_env)?),
            BooleanExpression::True => Ok(true),
            BooleanExpression::False => Ok(false),
        }
    }

    /// Recursively check whether the expression contains the atom `a`
    ///
    /// # Example
    ///
    /// ```
    /// use crate::taco_threshold_automaton::expressions::*;
    ///
    /// let expr = BooleanExpression::ComparisonExpression(
    ///     Box::new(IntegerExpression::Atom(Location::new("loc"))),
    ///     ComparisonOp::Eq,
    ///     Box::new(IntegerExpression::Const(1)),
    /// );
    /// assert_eq!(expr.contains_atom_a(&Location::new("loc")), true);
    /// assert_eq!(expr.contains_atom_a(&Location::new("otherloc")), false);
    /// ```
    pub fn contains_atom_a(&self, a: &T) -> bool {
        match self {
            BooleanExpression::ComparisonExpression(lhs, _, rhs) => {
                lhs.contains_atom_a(a) || rhs.contains_atom_a(a)
            }
            BooleanExpression::BinaryExpression(lhs, _, rhs) => {
                lhs.contains_atom_a(a) || rhs.contains_atom_a(a)
            }
            BooleanExpression::Not(expr) => expr.contains_atom_a(a),
            BooleanExpression::True => false,
            BooleanExpression::False => false,
        }
    }

    /// Substitute `to_replace` in this integer expression with integer
    /// expression `replace_with`
    ///
    /// # Example
    ///
    /// ```
    /// use crate::taco_threshold_automaton::expressions::*;
    ///
    /// let mut expr = BooleanExpression::ComparisonExpression(
    ///     Box::new(IntegerExpression::Const(1)),
    ///     ComparisonOp::Eq,
    ///     Box::new(IntegerExpression::Atom(Location::new("l"))),
    /// );
    /// expr.substitute_atom_with(&Location::new("l"),  &IntegerExpression::Const(3));
    ///
    /// let expected_expr = BooleanExpression::ComparisonExpression(
    ///     Box::new(IntegerExpression::Const(1)),
    ///     ComparisonOp::Eq,
    ///     Box::new(IntegerExpression::Const(3)),
    /// );
    /// assert_eq!(expr, expected_expr);
    /// ```
    pub fn substitute_atom_with(&mut self, to_replace: &T, replace_with: &IntegerExpression<T>) {
        match self {
            BooleanExpression::ComparisonExpression(lhs, _, rhs) => {
                lhs.substitute_atom_with(to_replace, replace_with);
                rhs.substitute_atom_with(to_replace, replace_with);
            }
            BooleanExpression::BinaryExpression(lhs, _, rhs) => {
                lhs.substitute_atom_with(to_replace, replace_with);
                rhs.substitute_atom_with(to_replace, replace_with);
            }
            BooleanExpression::Not(expr) => expr.substitute_atom_with(to_replace, replace_with),
            BooleanExpression::True | BooleanExpression::False => (),
        }
    }

    /// Check whether this expression is a constraint forces the atom to be
    /// equal to 0
    ///
    /// **Note:** This function is not complete ! It only checks for simple
    /// syntactic cases, as otherwise an SMT solver would be required.
    ///
    /// The function covers the following cases:
    ///  - `atom == 0`
    ///  - `atom < 1`
    ///  - `atom <= 0`
    ///
    /// (and these cases appearing in a conjunction, or if they appear in both
    /// sides of a disjunction)
    ///
    /// # Example
    ///
    /// ```
    /// use crate::taco_threshold_automaton::expressions::*;
    ///
    /// let atom = Location::new("loc");
    /// let expr = BooleanExpression::ComparisonExpression(
    ///    Box::new(IntegerExpression::Atom(atom.clone())),
    ///   ComparisonOp::Eq,
    ///   Box::new(IntegerExpression::Const(0)),
    /// );
    /// assert_eq!(expr.try_check_expr_constraints_to_zero(&atom), true);
    ///
    ///
    /// let expr = BooleanExpression::ComparisonExpression(
    ///   Box::new(IntegerExpression::Atom(atom.clone())),
    ///   ComparisonOp::Geq,
    ///   Box::new(IntegerExpression::Const(0)),
    /// );
    /// assert_eq!(expr.try_check_expr_constraints_to_zero(&atom), false);
    ///
    /// let expr = BooleanExpression::ComparisonExpression(
    ///    Box::new(IntegerExpression::Atom(Location::new("otherloc"))),
    ///    ComparisonOp::Eq,
    ///    Box::new(IntegerExpression::Const(0)),
    /// );
    /// assert_eq!(expr.try_check_expr_constraints_to_zero(&atom), false);
    ///
    /// let expr = !BooleanExpression::ComparisonExpression(
    ///   Box::new(IntegerExpression::Atom(atom.clone())),
    ///   ComparisonOp::Gt,
    ///   Box::new(IntegerExpression::Const(1)),
    /// );
    /// assert_eq!(expr.try_check_expr_constraints_to_zero(&atom), false);
    /// ```
    pub fn try_check_expr_constraints_to_zero(&self, atom: &T) -> bool {
        match self {
            BooleanExpression::ComparisonExpression(lhs, op, rhs) => {
                let mut atom_expr = lhs;
                let mut const_expr = rhs;
                let mut op = *op;

                if matches!(rhs.as_ref(), IntegerExpression::Atom(_)) {
                    atom_expr = rhs;
                    const_expr = lhs;
                    op = op.get_swap_side();
                }

                if let (IntegerExpression::Atom(a), Some(c)) =
                    (atom_expr.as_ref(), const_expr.try_to_evaluate_to_const())
                    && a == atom
                {
                    return match op {
                        ComparisonOp::Eq | ComparisonOp::Leq => c == 0,
                        ComparisonOp::Lt => c == 1,
                        _ => false,
                    };
                }

                false
            }
            BooleanExpression::BinaryExpression(rhs, BooleanConnective::And, lhs) => {
                lhs.try_check_expr_constraints_to_zero(atom)
                    || rhs.try_check_expr_constraints_to_zero(atom)
            }
            BooleanExpression::BinaryExpression(rhs, BooleanConnective::Or, lhs) => {
                lhs.try_check_expr_constraints_to_zero(atom)
                    && rhs.try_check_expr_constraints_to_zero(atom)
            }
            BooleanExpression::Not(_) | BooleanExpression::True | BooleanExpression::False => false,
        }
    }
}

impl<T> From<Parameter> for IntegerExpression<T>
where
    T: Atomic,
{
    fn from(value: Parameter) -> Self {
        IntegerExpression::Param(value)
    }
}

impl From<Variable> for IntegerExpression<Variable> {
    fn from(value: Variable) -> Self {
        IntegerExpression::Atom(value)
    }
}

impl From<Location> for IntegerExpression<Location> {
    fn from(value: Location) -> Self {
        IntegerExpression::Atom(value)
    }
}

impl<S> From<u32> for IntegerExpression<S>
where
    S: Atomic,
{
    fn from(value: u32) -> Self {
        IntegerExpression::Const(value)
    }
}

impl From<BooleanExpression<Parameter>> for BooleanExpression<Location> {
    fn from(value: BooleanExpression<Parameter>) -> Self {
        match value {
            BooleanExpression::ComparisonExpression(lhs, op, rhs) => {
                let lhs = Box::new((*lhs).into());
                let rhs = Box::new((*rhs).into());
                BooleanExpression::ComparisonExpression(lhs, op, rhs)
            }
            BooleanExpression::BinaryExpression(lhs, conn, rhs) => {
                let lhs = Box::new((*lhs).into());
                let rhs = Box::new((*rhs).into());
                BooleanExpression::BinaryExpression(lhs, conn, rhs)
            }
            BooleanExpression::Not(expr) => BooleanExpression::Not(Box::new((*expr).into())),
            BooleanExpression::True => BooleanExpression::True,
            BooleanExpression::False => BooleanExpression::False,
        }
    }
}

impl From<BooleanExpression<Parameter>> for BooleanExpression<Variable> {
    fn from(value: BooleanExpression<Parameter>) -> Self {
        match value {
            BooleanExpression::ComparisonExpression(lhs, op, rhs) => {
                let lhs = Box::new((*lhs).into());
                let rhs = Box::new((*rhs).into());
                BooleanExpression::ComparisonExpression(lhs, op, rhs)
            }
            BooleanExpression::BinaryExpression(lhs, conn, rhs) => {
                let lhs = Box::new((*lhs).into());
                let rhs = Box::new((*rhs).into());
                BooleanExpression::BinaryExpression(lhs, conn, rhs)
            }
            BooleanExpression::Not(expr) => BooleanExpression::Not(Box::new((*expr).into())),
            BooleanExpression::True => BooleanExpression::True,
            BooleanExpression::False => BooleanExpression::False,
        }
    }
}

// Overload operators for easier construction of expressions

impl<T> ops::Add for IntegerExpression<T>
where
    T: Atomic,
{
    type Output = IntegerExpression<T>;

    fn add(self, other: IntegerExpression<T>) -> IntegerExpression<T> {
        IntegerExpression::BinaryExpr(Box::new(self), IntegerOp::Add, Box::new(other))
    }
}

impl<T> ops::Sub for IntegerExpression<T>
where
    T: Atomic,
{
    type Output = IntegerExpression<T>;

    fn sub(self, other: IntegerExpression<T>) -> IntegerExpression<T> {
        IntegerExpression::BinaryExpr(Box::new(self), IntegerOp::Sub, Box::new(other))
    }
}

impl<T> ops::Mul for IntegerExpression<T>
where
    T: Atomic,
{
    type Output = IntegerExpression<T>;

    fn mul(self, other: IntegerExpression<T>) -> IntegerExpression<T> {
        IntegerExpression::BinaryExpr(Box::new(self), IntegerOp::Mul, Box::new(other))
    }
}

impl<T> ops::Div for IntegerExpression<T>
where
    T: Atomic,
{
    type Output = IntegerExpression<T>;

    fn div(self, other: IntegerExpression<T>) -> IntegerExpression<T> {
        IntegerExpression::BinaryExpr(Box::new(self), IntegerOp::Div, Box::new(other))
    }
}

impl<T> ops::Neg for IntegerExpression<T>
where
    T: Atomic,
{
    type Output = IntegerExpression<T>;

    fn neg(self) -> IntegerExpression<T> {
        IntegerExpression::Neg(Box::new(self))
    }
}

impl<T> ops::Not for BooleanExpression<T>
where
    T: Atomic,
{
    type Output = BooleanExpression<T>;

    fn not(self) -> BooleanExpression<T> {
        BooleanExpression::Not(Box::new(self))
    }
}

impl<T: Atomic> And for BooleanExpression<T> {
    fn and(self, other: Self) -> Self {
        BooleanExpression::BinaryExpression(
            Box::new(self),
            super::BooleanConnective::And,
            Box::new(other),
        )
    }
}
impl<T> ops::BitAnd for BooleanExpression<T>
where
    T: Atomic,
{
    type Output = BooleanExpression<T>;

    // Overload the `&` operator to represent the logical AND operation
    fn bitand(self, other: BooleanExpression<T>) -> BooleanExpression<T> {
        self.and(other)
    }
}

impl<T: Atomic> Or for BooleanExpression<T> {
    fn or(self, other: Self) -> Self {
        BooleanExpression::BinaryExpression(
            Box::new(self),
            super::BooleanConnective::Or,
            Box::new(other),
        )
    }
}

impl<T> ops::BitOr for BooleanExpression<T>
where
    T: Atomic,
{
    type Output = BooleanExpression<T>;

    // Overload the `|` operator to represent the logical OR operation
    fn bitor(self, other: BooleanExpression<T>) -> BooleanExpression<T> {
        self.or(other)
    }
}

impl ComparisonOp {
    /// Invert the operation
    ///
    /// This function can for example be useful when negating a comparison
    /// expression
    ///
    /// # Example
    ///
    /// ```
    /// use taco_threshold_automaton::expressions::ComparisonOp;
    ///
    /// assert_eq!(ComparisonOp::Eq.invert(), ComparisonOp::Neq);
    /// assert_eq!(ComparisonOp::Lt.invert(), ComparisonOp::Geq);
    /// ```
    pub fn invert(self) -> Self {
        match self {
            ComparisonOp::Eq => ComparisonOp::Neq,
            ComparisonOp::Neq => ComparisonOp::Eq,
            ComparisonOp::Lt => ComparisonOp::Geq,
            ComparisonOp::Leq => ComparisonOp::Gt,
            ComparisonOp::Gt => ComparisonOp::Leq,
            ComparisonOp::Geq => ComparisonOp::Lt,
        }
    }

    /// Swap the side of the comparison operator
    ///
    /// This is for example required when multiplying with negative constants
    ///
    /// # Example
    ///
    /// ```
    /// use taco_threshold_automaton::expressions::ComparisonOp;
    ///
    /// assert_eq!(ComparisonOp::Eq.get_swap_side(), ComparisonOp::Eq);
    /// assert_eq!(ComparisonOp::Lt.get_swap_side(), ComparisonOp::Gt);
    /// ```
    pub fn get_swap_side(self) -> Self {
        match self {
            ComparisonOp::Gt => ComparisonOp::Lt,
            ComparisonOp::Geq => ComparisonOp::Leq,
            ComparisonOp::Eq => ComparisonOp::Eq,
            ComparisonOp::Neq => ComparisonOp::Neq,
            ComparisonOp::Leq => ComparisonOp::Geq,
            ComparisonOp::Lt => ComparisonOp::Gt,
        }
    }
}

impl BooleanConnective {
    /// Get the dual operator of the connective
    ///
    /// # Example
    ///
    /// ```
    /// use taco_threshold_automaton::expressions::*;
    ///
    /// assert_eq!(BooleanConnective::And.invert(), BooleanConnective::Or);
    /// assert_eq!(BooleanConnective::Or.invert(), BooleanConnective::And);
    /// ```
    pub fn invert(self) -> Self {
        match self {
            BooleanConnective::And => BooleanConnective::Or,
            BooleanConnective::Or => BooleanConnective::And,
        }
    }
}

#[cfg(test)]
mod tests {
    use std::collections::HashMap;

    use crate::expressions::{
        BooleanConnective, BooleanExpression, ComparisonOp, IntegerExpression, IntegerOp, Location,
        Parameter, Variable, properties::EvaluationError,
    };

    #[test]
    fn test_is_atomic() {
        let expr: IntegerExpression<Variable> = IntegerExpression::Param(Parameter::new("x"));
        assert!(expr.is_atomic());

        let expr: IntegerExpression<Variable> = IntegerExpression::Atom(Variable::new("x"));
        assert!(expr.is_atomic());

        let expr: IntegerExpression<Variable> = IntegerExpression::Const(1);
        assert!(!expr.is_atomic());

        let expr: IntegerExpression<Variable> = IntegerExpression::BinaryExpr(
            Box::new(IntegerExpression::Const(1)),
            IntegerOp::Add,
            Box::new(IntegerExpression::Const(1)),
        );
        assert!(!expr.is_atomic());

        let expr: IntegerExpression<Variable> =
            IntegerExpression::Neg(Box::new(IntegerExpression::Const(1)));
        assert!(!expr.is_atomic());
    }

    #[test]
    fn test_is_param_to_var() {
        let expr: IntegerExpression<Parameter> = IntegerExpression::Atom(Parameter::new("x"));
        let expected_expr: IntegerExpression<Variable> =
            IntegerExpression::Param(Parameter::new("x"));
        assert_eq!(
            Into::<IntegerExpression<Variable>>::into(expr),
            expected_expr
        );

        let expr: IntegerExpression<Parameter> = IntegerExpression::Param(Parameter::new("x"));
        let expected_expr: IntegerExpression<Variable> =
            IntegerExpression::Param(Parameter::new("x"));
        assert_eq!(
            Into::<IntegerExpression<Variable>>::into(expr),
            expected_expr
        );

        let expr: IntegerExpression<Parameter> =
            IntegerExpression::Neg(Box::new(IntegerExpression::Atom(Parameter::new("x"))));
        let expected_expr: IntegerExpression<Variable> =
            IntegerExpression::Neg(Box::new(IntegerExpression::Param(Parameter::new("x"))));
        assert_eq!(
            Into::<IntegerExpression<Variable>>::into(expr),
            expected_expr
        );

        let expr: IntegerExpression<Parameter> = IntegerExpression::BinaryExpr(
            Box::new(IntegerExpression::Atom(Parameter::new("x"))),
            IntegerOp::Add,
            Box::new(IntegerExpression::Const(1)),
        );
        let expected_expr: IntegerExpression<Variable> = IntegerExpression::BinaryExpr(
            Box::new(IntegerExpression::Param(Parameter::new("x"))),
            IntegerOp::Add,
            Box::new(IntegerExpression::Const(1)),
        );
        assert_eq!(
            Into::<IntegerExpression<Variable>>::into(expr),
            expected_expr
        );
    }

    #[test]
    fn test_is_param_to_loc() {
        let expr: IntegerExpression<Parameter> = IntegerExpression::Atom(Parameter::new("x"));
        let expected_expr: IntegerExpression<Location> =
            IntegerExpression::Param(Parameter::new("x"));
        assert_eq!(
            Into::<IntegerExpression<Location>>::into(expr),
            expected_expr
        );

        let expr: IntegerExpression<Parameter> = IntegerExpression::Param(Parameter::new("x"));
        let expected_expr: IntegerExpression<Location> =
            IntegerExpression::Param(Parameter::new("x"));
        assert_eq!(
            Into::<IntegerExpression<Location>>::into(expr),
            expected_expr
        );

        let expr: IntegerExpression<Parameter> =
            IntegerExpression::Neg(Box::new(IntegerExpression::Atom(Parameter::new("x"))));
        let expected_expr: IntegerExpression<Location> =
            IntegerExpression::Neg(Box::new(IntegerExpression::Param(Parameter::new("x"))));
        assert_eq!(
            Into::<IntegerExpression<Location>>::into(expr),
            expected_expr
        );

        let expr: IntegerExpression<Parameter> = IntegerExpression::BinaryExpr(
            Box::new(IntegerExpression::Atom(Parameter::new("x"))),
            IntegerOp::Add,
            Box::new(IntegerExpression::Const(1)),
        );
        let expected_expr: IntegerExpression<Location> = IntegerExpression::BinaryExpr(
            Box::new(IntegerExpression::Param(Parameter::new("x"))),
            IntegerOp::Add,
            Box::new(IntegerExpression::Const(1)),
        );
        assert_eq!(
            Into::<IntegerExpression<Location>>::into(expr),
            expected_expr
        );
    }

    #[test]
    fn test_integer_expression_addition() {
        let expr1: IntegerExpression<Variable> = IntegerExpression::Const(1);
        let expr2: IntegerExpression<Variable> = IntegerExpression::Const(2);
        let result = expr1 + expr2;
        assert_eq!(
            result,
            IntegerExpression::BinaryExpr(
                Box::new(IntegerExpression::Const(1)),
                IntegerOp::Add,
                Box::new(IntegerExpression::Const(2)),
            )
        );
    }

    #[test]
    fn test_integer_expression_subtraction() {
        let expr1: IntegerExpression<Variable> = IntegerExpression::Const(3);
        let expr2: IntegerExpression<Variable> = IntegerExpression::Const(2);
        let result = expr1 - expr2;
        assert_eq!(
            result,
            IntegerExpression::BinaryExpr(
                Box::new(IntegerExpression::Const(3)),
                IntegerOp::Sub,
                Box::new(IntegerExpression::Const(2)),
            )
        );
    }

    #[test]
    fn test_integer_expression_multiplication() {
        let expr1: IntegerExpression<Variable> = IntegerExpression::Const(4);
        let expr2: IntegerExpression<Variable> = IntegerExpression::Const(5);
        let result = expr1 * expr2;
        assert_eq!(
            result,
            IntegerExpression::BinaryExpr(
                Box::new(IntegerExpression::Const(4)),
                IntegerOp::Mul,
                Box::new(IntegerExpression::Const(5)),
            )
        );
    }

    #[test]
    fn test_integer_expression_division() {
        let expr1: IntegerExpression<Variable> = IntegerExpression::Const(10);
        let expr2: IntegerExpression<Variable> = IntegerExpression::Const(2);
        let result = expr1 / expr2;
        assert_eq!(
            result,
            IntegerExpression::BinaryExpr(
                Box::new(IntegerExpression::Const(10)),
                IntegerOp::Div,
                Box::new(IntegerExpression::Const(2)),
            )
        );
    }

    #[test]
    fn test_integer_expression_negation() {
        let expr: IntegerExpression<Variable> = IntegerExpression::Const(5);
        let result = -expr;
        assert_eq!(
            result,
            IntegerExpression::Neg(Box::new(IntegerExpression::Const(5)))
        );
    }

    #[test]
    fn test_boolean_expression_negation() {
        let expr: BooleanExpression<Variable> = BooleanExpression::True;
        let result = !expr;
        assert_eq!(
            result,
            BooleanExpression::Not(Box::new(BooleanExpression::True))
        );
    }

    #[test]
    fn test_boolean_expression_and() {
        let expr1: BooleanExpression<Variable> = BooleanExpression::True;
        let expr2: BooleanExpression<Variable> = BooleanExpression::True;
        let result = expr1 & expr2;
        assert_eq!(
            result,
            BooleanExpression::BinaryExpression(
                Box::new(BooleanExpression::True),
                BooleanConnective::And,
                Box::new(BooleanExpression::True),
            )
        );
    }

    #[test]
    fn test_boolean_expression_or() {
        let expr1: BooleanExpression<Variable> = BooleanExpression::True;
        let expr2: BooleanExpression<Variable> = BooleanExpression::True;
        let result = expr1 | expr2;
        assert_eq!(
            result,
            BooleanExpression::BinaryExpression(
                Box::new(BooleanExpression::True),
                BooleanConnective::Or,
                Box::new(BooleanExpression::True),
            )
        );
    }

    #[test]
    fn test_boolean_expr_param_to_loc() {
        let expr: BooleanExpression<Parameter> = BooleanExpression::True;
        let expected_expr: BooleanExpression<Location> = BooleanExpression::True;
        assert_eq!(
            Into::<BooleanExpression<Location>>::into(expr),
            expected_expr
        );

        let expr: BooleanExpression<Parameter> = BooleanExpression::False;
        let expected_expr: BooleanExpression<Location> = BooleanExpression::False;
        assert_eq!(
            Into::<BooleanExpression<Location>>::into(expr),
            expected_expr
        );

        let expr: BooleanExpression<Parameter> =
            BooleanExpression::Not(Box::new(BooleanExpression::True));
        let expected_expr: BooleanExpression<Location> =
            BooleanExpression::Not(Box::new(BooleanExpression::True));
        assert_eq!(
            Into::<BooleanExpression<Location>>::into(expr),
            expected_expr
        );

        let expr: BooleanExpression<Parameter> = BooleanExpression::BinaryExpression(
            Box::new(BooleanExpression::True),
            BooleanConnective::And,
            Box::new(BooleanExpression::False),
        );
        let expected_expr: BooleanExpression<Location> = BooleanExpression::BinaryExpression(
            Box::new(BooleanExpression::True),
            BooleanConnective::And,
            Box::new(BooleanExpression::False),
        );
        assert_eq!(
            Into::<BooleanExpression<Location>>::into(expr),
            expected_expr
        );

        let expr: BooleanExpression<Parameter> = BooleanExpression::ComparisonExpression(
            Box::new(IntegerExpression::Const(42)),
            ComparisonOp::Leq,
            Box::new(IntegerExpression::Atom(Parameter::new("n"))),
        );
        let expected_expr: BooleanExpression<Location> = BooleanExpression::ComparisonExpression(
            Box::new(IntegerExpression::Const(42)),
            ComparisonOp::Leq,
            Box::new(IntegerExpression::Param(Parameter::new("n"))),
        );
        assert_eq!(
            Into::<BooleanExpression<Location>>::into(expr),
            expected_expr
        );
    }

    #[test]
    fn test_boolean_expr_param_to_var() {
        let expr: BooleanExpression<Parameter> = BooleanExpression::True;
        let expected_expr: BooleanExpression<Variable> = BooleanExpression::True;
        assert_eq!(
            Into::<BooleanExpression<Variable>>::into(expr),
            expected_expr
        );

        let expr: BooleanExpression<Parameter> = BooleanExpression::False;
        let expected_expr: BooleanExpression<Variable> = BooleanExpression::False;
        assert_eq!(
            Into::<BooleanExpression<Variable>>::into(expr),
            expected_expr
        );

        let expr: BooleanExpression<Parameter> =
            BooleanExpression::Not(Box::new(BooleanExpression::True));
        let expected_expr: BooleanExpression<Variable> =
            BooleanExpression::Not(Box::new(BooleanExpression::True));
        assert_eq!(
            Into::<BooleanExpression<Variable>>::into(expr),
            expected_expr
        );

        let expr: BooleanExpression<Parameter> = BooleanExpression::BinaryExpression(
            Box::new(BooleanExpression::True),
            BooleanConnective::And,
            Box::new(BooleanExpression::False),
        );
        let expected_expr: BooleanExpression<Variable> = BooleanExpression::BinaryExpression(
            Box::new(BooleanExpression::True),
            BooleanConnective::And,
            Box::new(BooleanExpression::False),
        );
        assert_eq!(
            Into::<BooleanExpression<Variable>>::into(expr),
            expected_expr
        );

        let expr: BooleanExpression<Parameter> = BooleanExpression::ComparisonExpression(
            Box::new(IntegerExpression::Const(42)),
            ComparisonOp::Leq,
            Box::new(IntegerExpression::Atom(Parameter::new("n"))),
        );
        let expected_expr: BooleanExpression<Variable> = BooleanExpression::ComparisonExpression(
            Box::new(IntegerExpression::Const(42)),
            ComparisonOp::Leq,
            Box::new(IntegerExpression::Param(Parameter::new("n"))),
        );
        assert_eq!(
            Into::<BooleanExpression<Variable>>::into(expr),
            expected_expr
        );
    }

    #[test]
    fn test_integer_expression_contains_atom() {
        let expr1: IntegerExpression<Variable> = IntegerExpression::Atom(Variable::new("x"));
        assert!(expr1.contains_atom());

        let expr2: IntegerExpression<Variable> = IntegerExpression::Const(1);
        assert!(!expr2.contains_atom());

        let expr3: IntegerExpression<Variable> = IntegerExpression::Param(Parameter::new("y"));
        assert!(!expr3.contains_atom());

        let expr4: IntegerExpression<Variable> =
            IntegerExpression::Neg(Box::new(IntegerExpression::Atom(Variable::new("z"))));
        assert!(expr4.contains_atom());

        let expr5: IntegerExpression<Variable> = IntegerExpression::BinaryExpr(
            Box::new(IntegerExpression::Atom(Variable::new("a"))),
            IntegerOp::Add,
            Box::new(IntegerExpression::Const(1)),
        );
        assert!(expr5.contains_atom());
    }

    #[test]
    fn test_swap_side_comp_op() {
        assert_eq!(ComparisonOp::Eq.get_swap_side(), ComparisonOp::Eq);
        assert_eq!(ComparisonOp::Neq.get_swap_side(), ComparisonOp::Neq);
        assert_eq!(ComparisonOp::Lt.get_swap_side(), ComparisonOp::Gt);
        assert_eq!(ComparisonOp::Leq.get_swap_side(), ComparisonOp::Geq);
        assert_eq!(ComparisonOp::Gt.get_swap_side(), ComparisonOp::Lt);
        assert_eq!(ComparisonOp::Geq.get_swap_side(), ComparisonOp::Leq);
    }

    #[test]
    fn test_invert_comp_op() {
        assert_eq!(ComparisonOp::Eq.invert(), ComparisonOp::Neq);
        assert_eq!(ComparisonOp::Neq.invert(), ComparisonOp::Eq);
        assert_eq!(ComparisonOp::Lt.invert(), ComparisonOp::Geq);
        assert_eq!(ComparisonOp::Leq.invert(), ComparisonOp::Gt);
        assert_eq!(ComparisonOp::Gt.invert(), ComparisonOp::Leq);
        assert_eq!(ComparisonOp::Geq.invert(), ComparisonOp::Lt);
    }

    #[test]
    fn test_invert_boolean_connective() {
        assert_eq!(BooleanConnective::And.invert(), BooleanConnective::Or);
        assert_eq!(BooleanConnective::Or.invert(), BooleanConnective::And);
    }

    #[test]
    fn test_try_to_evaluate_to_const() {
        let expr = IntegerExpression::<Location>::Const(5) + IntegerExpression::Const(3);
        assert_eq!(expr.try_to_evaluate_to_const(), Some(8));

        let expr = IntegerExpression::<Location>::Const(5) - IntegerExpression::Const(3);
        assert_eq!(expr.try_to_evaluate_to_const(), Some(2));

        let expr = IntegerExpression::<Location>::Const(10) / IntegerExpression::Const(5);
        assert_eq!(expr.try_to_evaluate_to_const(), Some(2));

        let expr = -IntegerExpression::Const(42) / IntegerExpression::<Location>::Const(2);
        assert_eq!(expr.try_to_evaluate_to_const(), Some(-21));

        let expr = -IntegerExpression::<Location>::Const(42) * IntegerExpression::Const(2);
        assert_eq!(expr.try_to_evaluate_to_const(), Some(-84));

        let expr = IntegerExpression::<Location>::Param(Parameter::new("n"));
        assert_eq!(expr.try_to_evaluate_to_const(), None);

        let expr = -IntegerExpression::Const(42) / IntegerExpression::Atom(Location::new("loc"));
        assert_eq!(expr.try_to_evaluate_to_const(), None);
    }

    #[test]
    fn test_try_to_evaluate_to_const_with_env() {
        let env = HashMap::from([(Location::new("loc"), 1)]);
        let param_env = HashMap::from([(Parameter::new("n"), 1)]);

        let expr = IntegerExpression::<Location>::Const(5) + IntegerExpression::Const(3);
        assert_eq!(
            expr.try_to_evaluate_to_const_with_env(&env, &param_env),
            Ok(8)
        );

        let expr = IntegerExpression::<Location>::Const(5) - IntegerExpression::Const(3);
        assert_eq!(
            expr.try_to_evaluate_to_const_with_env(&env, &param_env),
            Ok(2)
        );

        let expr = IntegerExpression::<Location>::Const(10) / IntegerExpression::Const(5);
        assert_eq!(
            expr.try_to_evaluate_to_const_with_env(&env, &param_env),
            Ok(2)
        );

        let expr = -IntegerExpression::Const(42) / IntegerExpression::<Location>::Const(2);
        assert_eq!(
            expr.try_to_evaluate_to_const_with_env(&env, &param_env),
            Ok(-21)
        );

        let expr = -IntegerExpression::<Location>::Const(42) * IntegerExpression::Const(2);
        assert_eq!(
            expr.try_to_evaluate_to_const_with_env(&env, &param_env),
            Ok(-84)
        );

        let expr = IntegerExpression::Atom(Location::new("loc"));
        assert_eq!(
            expr.try_to_evaluate_to_const_with_env(&env, &param_env),
            Ok(1)
        );

        let expr = -IntegerExpression::Const(42) / IntegerExpression::Atom(Location::new("loc"));
        assert_eq!(
            expr.try_to_evaluate_to_const_with_env(&env, &param_env),
            Ok(-42)
        );

        let expr = IntegerExpression::<Location>::Param(Parameter::new("n"));
        assert_eq!(
            expr.try_to_evaluate_to_const_with_env(&HashMap::new(), &param_env),
            Ok(1)
        );

        let expr = IntegerExpression::<Location>::Param(Parameter::new("n"));
        assert_eq!(
            expr.try_to_evaluate_to_const_with_env(&env, &HashMap::new()),
            Err(EvaluationError::ParameterNotFound(Parameter::new("n")))
        );

        let expr = IntegerExpression::Atom(Location::new("loc"));
        assert_eq!(
            expr.try_to_evaluate_to_const_with_env(&HashMap::new(), &param_env),
            Err(EvaluationError::AtomicNotFound(Location::new("loc")))
        );
    }

    #[test]
    fn test_boolean_expr_check_satisfied() {
        let env = HashMap::from([(Location::new("loc"), 1)]);
        let param_env = HashMap::from([(Parameter::new("n"), 1)]);

        let expr = BooleanExpression::ComparisonExpression(
            Box::new(IntegerExpression::Const(5)),
            ComparisonOp::Eq,
            Box::new(IntegerExpression::Const(5)),
        );
        assert_eq!(expr.check_satisfied(&env, &param_env), Ok(true));

        let expr = BooleanExpression::ComparisonExpression(
            Box::new(IntegerExpression::Const(5)),
            ComparisonOp::Eq,
            Box::new(IntegerExpression::Const(3)),
        );
        assert_eq!(expr.check_satisfied(&env, &param_env), Ok(false));

        let expr = BooleanExpression::ComparisonExpression(
            Box::new(IntegerExpression::Const(5)),
            ComparisonOp::Lt,
            Box::new(IntegerExpression::Const(3)),
        );
        assert_eq!(expr.check_satisfied(&env, &param_env), Ok(false));

        let expr = BooleanExpression::ComparisonExpression(
            Box::new(IntegerExpression::Const(5)),
            ComparisonOp::Lt,
            Box::new(IntegerExpression::Const(10)),
        );
        assert_eq!(expr.check_satisfied(&env, &param_env), Ok(true));

        let expr = BooleanExpression::ComparisonExpression(
            Box::new(IntegerExpression::Const(5)),
            ComparisonOp::Leq,
            Box::new(IntegerExpression::Const(5)),
        );
        assert_eq!(expr.check_satisfied(&env, &param_env), Ok(true));

        let expr = BooleanExpression::ComparisonExpression(
            Box::new(IntegerExpression::Const(5)),
            ComparisonOp::Leq,
            Box::new(IntegerExpression::Const(3)),
        );
        assert_eq!(expr.check_satisfied(&env, &param_env), Ok(false));

        let expr = BooleanExpression::ComparisonExpression(
            Box::new(IntegerExpression::Const(5)),
            ComparisonOp::Gt,
            Box::new(IntegerExpression::Const(3)),
        );
        assert_eq!(expr.check_satisfied(&env, &param_env), Ok(true));

        let expr = BooleanExpression::ComparisonExpression(
            Box::new(IntegerExpression::Const(5)),
            ComparisonOp::Gt,
            Box::new(IntegerExpression::Const(10)),
        );
        assert_eq!(expr.check_satisfied(&env, &param_env), Ok(false));

        let expr = BooleanExpression::ComparisonExpression(
            Box::new(IntegerExpression::Const(5)),
            ComparisonOp::Neq,
            Box::new(IntegerExpression::Const(5)),
        );
        assert_eq!(expr.check_satisfied(&env, &param_env), Ok(false));

        let expr = BooleanExpression::ComparisonExpression(
            Box::new(IntegerExpression::Const(5)),
            ComparisonOp::Neq,
            Box::new(IntegerExpression::Const(3)),
        );
        assert_eq!(expr.check_satisfied(&env, &param_env), Ok(true));

        let expr = BooleanExpression::ComparisonExpression(
            Box::new(IntegerExpression::Const(5)),
            ComparisonOp::Geq,
            Box::new(IntegerExpression::Const(3)),
        );
        assert_eq!(expr.check_satisfied(&env, &param_env), Ok(true));

        let expr = BooleanExpression::ComparisonExpression(
            Box::new(IntegerExpression::Const(5)),
            ComparisonOp::Geq,
            Box::new(IntegerExpression::Const(10)),
        );
        assert_eq!(expr.check_satisfied(&env, &param_env), Ok(false));

        let expr = BooleanExpression::BinaryExpression(
            Box::new(BooleanExpression::True),
            BooleanConnective::And,
            Box::new(BooleanExpression::True),
        );
        assert_eq!(expr.check_satisfied(&env, &param_env), Ok(true));

        let expr = BooleanExpression::BinaryExpression(
            Box::new(BooleanExpression::True),
            BooleanConnective::Or,
            Box::new(BooleanExpression::False),
        );
        assert_eq!(expr.check_satisfied(&env, &param_env), Ok(true));

        let expr = !BooleanExpression::False;
        assert_eq!(expr.check_satisfied(&env, &param_env), Ok(true));

        let expr = BooleanExpression::False;
        assert_eq!(expr.check_satisfied(&env, &param_env), Ok(false));
    }

    #[test]
    fn test_display_evaluation_error() {
        let error = EvaluationError::AtomicNotFound(Location::new("loc"));
        assert!(
            error
                .to_string()
                .contains(&Location::new("loc").to_string())
        );

        let error: EvaluationError<Location> =
            EvaluationError::ParameterNotFound(Parameter::new("n"));
        assert!(error.to_string().contains("n"));
    }

    #[test]
    fn test_contains_atom_a_integer_expr() {
        let atom = Variable::new("x");

        let expr1: IntegerExpression<Variable> = IntegerExpression::Atom(atom.clone());
        assert!(expr1.contains_atom_a(&atom));

        let expr2: IntegerExpression<Variable> = IntegerExpression::Const(1);
        assert!(!expr2.contains_atom_a(&atom));

        let expr3: IntegerExpression<Variable> = IntegerExpression::Param(Parameter::new("y"));
        assert!(!expr3.contains_atom_a(&atom));

        let expr4: IntegerExpression<Variable> =
            IntegerExpression::Neg(Box::new(IntegerExpression::Atom(atom.clone())));
        assert!(expr4.contains_atom_a(&atom));

        let expr5: IntegerExpression<Variable> = IntegerExpression::BinaryExpr(
            Box::new(IntegerExpression::Atom(atom.clone())),
            IntegerOp::Add,
            Box::new(IntegerExpression::Const(1)),
        );
        assert!(expr5.contains_atom_a(&atom));

        let expr6: IntegerExpression<Variable> = IntegerExpression::BinaryExpr(
            Box::new(IntegerExpression::Const(1)),
            IntegerOp::Add,
            Box::new(IntegerExpression::Const(2)),
        );
        assert!(!expr6.contains_atom_a(&atom));
    }

    #[test]
    fn test_contains_atom_a_boolean_expr() {
        let atom = Variable::new("x");

        let expr1: BooleanExpression<Variable> = BooleanExpression::ComparisonExpression(
            Box::new(IntegerExpression::Atom(atom.clone())),
            ComparisonOp::Eq,
            Box::new(IntegerExpression::Const(1)),
        );
        assert!(expr1.contains_atom_a(&atom));

        let expr2: BooleanExpression<Variable> = BooleanExpression::ComparisonExpression(
            Box::new(IntegerExpression::Atom(Variable::new("y"))),
            ComparisonOp::Eq,
            Box::new(IntegerExpression::Const(2)),
        );
        assert!(!expr2.contains_atom_a(&atom));

        let expr3: BooleanExpression<Variable> = BooleanExpression::BinaryExpression(
            Box::new(BooleanExpression::ComparisonExpression(
                Box::new(IntegerExpression::Atom(atom.clone())),
                ComparisonOp::Eq,
                Box::new(IntegerExpression::Const(1)),
            )),
            BooleanConnective::And,
            Box::new(BooleanExpression::True),
        );
        assert!(expr3.contains_atom_a(&atom));

        let expr4: BooleanExpression<Variable> =
            BooleanExpression::Not(Box::new(BooleanExpression::ComparisonExpression(
                Box::new(IntegerExpression::Atom(atom.clone())),
                ComparisonOp::Eq,
                Box::new(IntegerExpression::Const(1)),
            )));
        assert!(expr4.contains_atom_a(&atom));

        let expr5: BooleanExpression<Variable> = BooleanExpression::True;
        assert!(!expr5.contains_atom_a(&atom));

        let expr6: BooleanExpression<Variable> = BooleanExpression::False;
        assert!(!expr6.contains_atom_a(&atom));
    }

    #[test]
    fn test_boolean_expression_complex() {
        let env = HashMap::from([(Location::new("loc"), 1)]);
        let param_env = HashMap::from([(Parameter::new("n"), 1)]);

        let expr = BooleanExpression::BinaryExpression(
            Box::new(BooleanExpression::ComparisonExpression(
                Box::new(IntegerExpression::Const(5)),
                ComparisonOp::Eq,
                Box::new(IntegerExpression::Const(5)),
            )),
            BooleanConnective::And,
            Box::new(BooleanExpression::ComparisonExpression(
                Box::new(IntegerExpression::Const(3)),
                ComparisonOp::Lt,
                Box::new(IntegerExpression::Const(10)),
            )),
        );
        assert_eq!(expr.check_satisfied(&env, &param_env), Ok(true));

        let expr = BooleanExpression::BinaryExpression(
            Box::new(BooleanExpression::ComparisonExpression(
                Box::new(IntegerExpression::Const(5)),
                ComparisonOp::Eq,
                Box::new(IntegerExpression::Const(3)),
            )),
            BooleanConnective::Or,
            Box::new(BooleanExpression::ComparisonExpression(
                Box::new(IntegerExpression::Const(3)),
                ComparisonOp::Lt,
                Box::new(IntegerExpression::Const(10)),
            )),
        );
        assert_eq!(expr.check_satisfied(&env, &param_env), Ok(true));

        let expr = BooleanExpression::Not(Box::new(BooleanExpression::ComparisonExpression(
            Box::new(IntegerExpression::Const(5)),
            ComparisonOp::Eq,
            Box::new(IntegerExpression::Const(3)),
        )));
        assert_eq!(expr.check_satisfied(&env, &param_env), Ok(true));
    }

    #[test]
    fn test_integer_expression_substitute_atom() {
        let atom = Variable::new("x");
        let replacement = IntegerExpression::Const(42);

        let expr1: IntegerExpression<Variable> = IntegerExpression::Atom(atom.clone());
        let mut result = expr1.clone();
        result.substitute_atom_with(&atom, &replacement);
        assert_eq!(result, replacement);

        let expr2: IntegerExpression<Variable> = IntegerExpression::Const(1);
        let mut result = expr2.clone();
        result.substitute_atom_with(&atom, &replacement);
        assert_eq!(result, expr2);

        let expr3: IntegerExpression<Variable> = IntegerExpression::Param(Parameter::new("y"));
        let mut result = expr3.clone();
        result.substitute_atom_with(&atom, &replacement);
        assert_eq!(result, expr3);

        let expr4: IntegerExpression<Variable> =
            IntegerExpression::Neg(Box::new(IntegerExpression::Atom(atom.clone())));
        let expected = IntegerExpression::Neg(Box::new(replacement.clone()));
        let mut result = expr4;
        result.substitute_atom_with(&atom, &replacement);
        assert_eq!(result, expected);

        let expr5: IntegerExpression<Variable> = IntegerExpression::BinaryExpr(
            Box::new(IntegerExpression::Atom(atom.clone())),
            IntegerOp::Add,
            Box::new(IntegerExpression::Const(1)),
        );
        let expected = IntegerExpression::BinaryExpr(
            Box::new(replacement.clone()),
            IntegerOp::Add,
            Box::new(IntegerExpression::Const(1)),
        );
        let mut result = expr5.clone();
        result.substitute_atom_with(&atom, &replacement);
        assert_eq!(result, expected);

        let expr6: IntegerExpression<Variable> = IntegerExpression::BinaryExpr(
            Box::new(IntegerExpression::Const(1)),
            IntegerOp::Add,
            Box::new(IntegerExpression::Const(2)),
        );
        let mut result = expr6.clone();
        result.substitute_atom_with(&atom, &replacement);
        assert_eq!(result, expr6);
    }

    #[test]
    fn test_boolean_expr_substitute_atom() {
        let atom = Variable::new("x");
        let replacement = IntegerExpression::Const(42);

        let expr1: BooleanExpression<Variable> = BooleanExpression::ComparisonExpression(
            Box::new(IntegerExpression::Atom(atom.clone())),
            ComparisonOp::Eq,
            Box::new(IntegerExpression::Const(1)),
        );
        let expected = BooleanExpression::ComparisonExpression(
            Box::new(replacement.clone()),
            ComparisonOp::Eq,
            Box::new(IntegerExpression::Const(1)),
        );
        let mut result = expr1.clone();
        result.substitute_atom_with(&atom, &replacement);
        assert_eq!(result, expected);

        let expr2: BooleanExpression<Variable> = BooleanExpression::BinaryExpression(
            Box::new(BooleanExpression::ComparisonExpression(
                Box::new(IntegerExpression::Atom(atom.clone())),
                ComparisonOp::Eq,
                Box::new(IntegerExpression::Const(1)),
            )),
            BooleanConnective::And,
            Box::new(BooleanExpression::True),
        );
        let expected = BooleanExpression::BinaryExpression(
            Box::new(BooleanExpression::ComparisonExpression(
                Box::new(replacement.clone()),
                ComparisonOp::Eq,
                Box::new(IntegerExpression::Const(1)),
            )),
            BooleanConnective::And,
            Box::new(BooleanExpression::True),
        );
        let mut result = expr2.clone();
        result.substitute_atom_with(&atom, &replacement);
        assert_eq!(result, expected);

        let expr3: BooleanExpression<Variable> =
            BooleanExpression::Not(Box::new(BooleanExpression::ComparisonExpression(
                Box::new(IntegerExpression::Atom(atom.clone())),
                ComparisonOp::Eq,
                Box::new(IntegerExpression::Const(1)),
            )));
        let expected = BooleanExpression::Not(Box::new(BooleanExpression::ComparisonExpression(
            Box::new(replacement.clone()),
            ComparisonOp::Eq,
            Box::new(IntegerExpression::Const(1)),
        )));
        let mut result = expr3.clone();
        result.substitute_atom_with(&atom, &replacement);
        assert_eq!(result, expected);

        let expr4: BooleanExpression<Variable> = BooleanExpression::True;
        let mut result = expr4.clone();
        result.substitute_atom_with(&atom, &replacement);
        assert_eq!(result, expr4);

        let expr5: BooleanExpression<Variable> = BooleanExpression::False;
        let mut result = expr5.clone();
        result.substitute_atom_with(&atom, &replacement);
        assert_eq!(result, expr5);
    }

    #[test]
    fn test_try_check_expr_constraints_to_zero() {
        let atom = Location::new("loc");
        let expr = BooleanExpression::ComparisonExpression(
            Box::new(IntegerExpression::Atom(atom.clone())),
            ComparisonOp::Eq,
            Box::new(IntegerExpression::Const(0)),
        );
        assert!(expr.try_check_expr_constraints_to_zero(&atom));

        let expr = BooleanExpression::ComparisonExpression(
            Box::new(IntegerExpression::Atom(atom.clone())),
            ComparisonOp::Leq,
            Box::new(IntegerExpression::Const(0)),
        );
        assert!(expr.try_check_expr_constraints_to_zero(&atom));

        let expr = BooleanExpression::ComparisonExpression(
            Box::new(IntegerExpression::Atom(atom.clone())),
            ComparisonOp::Lt,
            Box::new(IntegerExpression::Const(1)),
        );
        assert!(expr.try_check_expr_constraints_to_zero(&atom));

        let expr = BooleanExpression::ComparisonExpression(
            Box::new(IntegerExpression::Atom(atom.clone())),
            ComparisonOp::Geq,
            Box::new(IntegerExpression::Const(0)),
        );
        assert!(!expr.try_check_expr_constraints_to_zero(&atom));

        let expr = BooleanExpression::ComparisonExpression(
            Box::new(IntegerExpression::Atom(Location::new("otherloc"))),
            ComparisonOp::Eq,
            Box::new(IntegerExpression::Const(0)),
        );
        assert!(!expr.try_check_expr_constraints_to_zero(&atom));

        let expr = !BooleanExpression::ComparisonExpression(
            Box::new(IntegerExpression::Atom(atom.clone())),
            ComparisonOp::Gt,
            Box::new(IntegerExpression::Const(1)),
        );
        assert!(!expr.try_check_expr_constraints_to_zero(&atom));

        let atom = Location::new("loc");
        let expr = BooleanExpression::ComparisonExpression(
            Box::new(IntegerExpression::Const(0)),
            ComparisonOp::Eq,
            Box::new(IntegerExpression::Atom(atom.clone())),
        );
        assert!(expr.try_check_expr_constraints_to_zero(&atom));
    }

    #[test]
    fn test_try_const_from_integer() {
        let expr: IntegerExpression<Location> = 1_u32.into();
        assert_eq!(expr, IntegerExpression::Const(1));
    }

    #[test]
    fn test_integer_expr_from_location() {
        let loc = Location::new("loc");
        let expected_expr = IntegerExpression::Atom(Location::new("loc"));
        assert_eq!(IntegerExpression::from(loc), expected_expr);
    }

    #[test]
    fn test_contains_parameter() {
        // Parameter inside an IntegerExpression over Variables
        let expr1: IntegerExpression<Variable> = IntegerExpression::Param(Parameter::new("x"));
        assert!(expr1.contains_parameter());

        // No parameter present
        let expr2: IntegerExpression<Variable> = IntegerExpression::Const(1);
        assert!(!expr2.contains_parameter());

        // Parameter nested in a binary expression lhs
        let expr3: IntegerExpression<Variable> =
            IntegerExpression::Param(Parameter::new("n")) + IntegerExpression::Const(2);
        assert!(expr3.contains_parameter());

        // Parameter nested in a binary expression rhs
        let expr4: IntegerExpression<Variable> =
            IntegerExpression::Const(2) + IntegerExpression::Param(Parameter::new("n"));
        assert!(expr4.contains_parameter());

        // No parameter in binary expression
        let expr5: IntegerExpression<Variable> =
            IntegerExpression::Const(2) + IntegerExpression::Const(2);
        assert!(!expr5.contains_parameter());

        // Parameter in neg
        let expr6: IntegerExpression<Variable> =
            IntegerExpression::Neg(Box::new(IntegerExpression::Param(Parameter::new("n"))));
        assert!(expr6.contains_parameter());

        // No parameter in neg
        let expr7: IntegerExpression<Variable> =
            IntegerExpression::Neg(Box::new(IntegerExpression::Const(1)));
        assert!(!expr7.contains_parameter());

        // When the expression is over `Parameter` as the atomic type,
        // an `Atom(Parameter)` is NOT a parameter node and should return false.
        let expr8: IntegerExpression<Parameter> = IntegerExpression::Atom(Parameter::new("x"));
        assert!(!expr8.contains_parameter());

        // But an explicit Param node still counts as a parameter.
        let expr9: IntegerExpression<Parameter> = IntegerExpression::Param(Parameter::new("y"));
        assert!(expr9.contains_parameter());
    }
}
