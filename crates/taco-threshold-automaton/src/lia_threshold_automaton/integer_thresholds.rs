//! This module defines abstract types for linear arithmetic constraints over
//! parameters, variables and other [`Atomic`] values, that can be safely
//! encoded into integer arithmetic SMT constraints.
//!
//! A type that can be safely encoded into integer constraints will implement
//! the [`IntoNoDivBooleanExpr`] trait. Expressions implementing this trait will
//! always be expanded to the least common multiple of the denominators
//! appearing in the expression, thus removing the rational constants in the
//! encoded expression while preserving the satisfying assignments-
//!
//! This is important as SMTLIB-2 defines integer division analog to how integer
//! division is usually implemented on a computer
//! (see [Theory of `Ints`](https://smt-lib.org/theories-Ints.shtml)).
//!
//! This means for example that the expressions `1 / 2 == 0` is `True`. In our
//! case, this is not the intended definition. Therefore, if fractions appear as
//! part of boolean expressions, these expressions are expanded until all
//! fractions can be represented as an integer.
//!
//! For example, an expression of the form `x = 1/3 * n` will be encoded as
//! `3 * x = n`.

use std::{
    collections::{BTreeMap, HashMap},
    error::Error,
    fmt::{self},
    hash::Hash,
    ops,
};

use crate::{
    expressions::{
        And, Atomic, BooleanExpression, ComparisonOp, IntegerExpression, Location, Or, Parameter,
        Variable, fraction::Fraction,
    },
    lia_threshold_automaton::ConstraintRewriteError,
    lia_threshold_automaton::general_to_lia::classify_into_lia::split_pairs_into_atom_and_threshold,
};

/// Weighted sum of [`Atomic`] values
///
/// A weighted sum is an expression of the form `c_1 * v_1 + ... + c_n * v_n`
/// where `v_1, ..., v_n` are atomic values and `c_1, ..., c_n` are real
/// valued coefficients to these variables.
#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct WeightedSum<T>
where
    T: Atomic,
{
    /// Map of atomic values and their weights
    weight_map: BTreeMap<T, Fraction>,
}

impl<T: Atomic> WeightedSum<T> {
    /// Check if the weighted sum is empty / equal to 0
    pub fn is_zero(&self) -> bool {
        self.weight_map.is_empty()
    }

    /// Check whether all coefficients are already integers
    ///
    /// This checks whether all coefficients in the weighted sum are integers,
    /// i.e., they can be converted to integer values without a loss in
    /// precision.
    ///
    /// # Example
    ///
    ///
    /// ```rust
    /// use taco_threshold_automaton::{
    ///     expressions::{Variable, fraction::Fraction},
    ///     lia_threshold_automaton::integer_thresholds::WeightedSum
    /// };
    ///
    /// let ws : WeightedSum<Variable> = WeightedSum::new([
    ///     (Variable::new("var2"), 1),
    /// ]);
    /// assert!(ws.is_integer_form());
    ///
    /// let ws : WeightedSum<Variable> = WeightedSum::new([
    ///     (Variable::new("var2"), Fraction::new(1, 2, false)),
    /// ]);
    /// assert!(!ws.is_integer_form());
    /// ```
    pub fn is_integer_form(&self) -> bool {
        self.weight_map.values().all(|coef| coef.is_integer())
    }

    /// Create a new [`WeightedSum`]
    ///
    /// Creates a new [`WeightedSum`], filtering all components with a factor of `0`
    pub fn new<F, I, V>(weight_map: I) -> Self
    where
        F: Into<Fraction>,
        V: Into<T>,
        I: IntoIterator<Item = (V, F)>,
    {
        // remove all entries with a coefficient of zero
        let weight_map = weight_map
            .into_iter()
            .map(|(v, c)| (v.into(), c.into()))
            .filter(|(_, coef)| *coef != Fraction::from(0))
            .collect();

        Self { weight_map }
    }

    /// Create a new empty [`WeightedSum`]
    pub fn new_empty() -> Self {
        Self {
            weight_map: BTreeMap::new(),
        }
    }

    /// Get the factor for `v` if it exists
    ///
    /// # Example
    ///
    /// ```
    /// use taco_threshold_automaton::{
    ///     expressions::{Variable, fraction::Fraction},
    ///     lia_threshold_automaton::integer_thresholds::WeightedSum
    /// };
    ///
    /// let ws : WeightedSum<Variable> = WeightedSum::new([
    ///     (Variable::new("var1"), 1),
    /// ]);
    /// assert_eq!(ws.get_factor(&Variable::new("var1")), Some(&Fraction::from(1)));
    /// ```
    pub fn get_factor(&self, v: &T) -> Option<&Fraction> {
        self.weight_map.get(v)
    }

    /// Get the least common multiple across all denominators of the
    /// coefficients
    ///
    /// The least common multiple is computed across all denominators of the
    /// coefficients in the [`WeightedSum`].
    ///
    /// This can be useful for scaling such that all coefficients are integers.
    ///
    /// # Example
    ///
    /// ```
    /// use taco_threshold_automaton::{
    ///     expressions::{Variable, fraction::Fraction},
    ///     lia_threshold_automaton::integer_thresholds::WeightedSum
    /// };
    ///
    /// let ws : WeightedSum<Variable> = WeightedSum::new([
    ///     (Variable::new("var1"), 1),
    /// ]);
    /// assert_eq!(ws.get_lcm_of_denominators(), 1);
    ///
    /// let ws : WeightedSum<Variable> = WeightedSum::new([
    ///     (Variable::new("var1"), Fraction::from(1)),
    ///     (Variable::new("var2"), Fraction::new(1, 2, false)),
    /// ]);
    /// assert_eq!(ws.get_lcm_of_denominators(), 2);
    /// ```
    pub fn get_lcm_of_denominators(&self) -> u32 {
        self.weight_map
            .values()
            .fold(1, |acc, coef| num::Integer::lcm(&acc, &coef.denominator()))
    }

    /// Scale the weighted sum by a factor
    ///
    /// # Example
    ///
    /// ```rust
    /// use taco_threshold_automaton::{
    ///     expressions::Variable,
    ///     lia_threshold_automaton::integer_thresholds::WeightedSum
    /// };
    ///
    /// let mut ws : WeightedSum<Variable> = WeightedSum::new([
    ///     (Variable::new("var2"), 1),
    ///     (Variable::new("var2"), 3),
    /// ]);
    /// let scaled_ws = WeightedSum::new([
    ///     (Variable::new("var2"), 3),
    ///     (Variable::new("var2"), 9),
    /// ]);
    ///
    /// ws.scale(3.into());
    ///
    /// assert_eq!(ws, scaled_ws);
    /// ```
    pub fn scale(&mut self, factor: Fraction) {
        if factor == Fraction::from(0) {
            self.weight_map.clear();
            return;
        }

        for coef in self.weight_map.values_mut() {
            *coef *= factor;
        }
    }

    /// Check whether `t` is part of the [`WeightedSum`] (and the factor is not 0)
    ///
    /// # Example
    ///
    /// ```rust
    /// use taco_threshold_automaton::{
    ///     expressions::Variable,
    ///     lia_threshold_automaton::integer_thresholds::WeightedSum
    /// };
    ///
    /// let ws = WeightedSum::new([
    ///     (Variable::new("var"), 1),
    ///     (Variable::new("zvar"), 0),
    /// ]);
    ///
    /// assert!(ws.contains(&Variable::new("var")));
    /// assert!(!ws.contains(&Variable::new("unknown")));
    /// assert!(!ws.contains(&Variable::new("zvar")));
    /// ```
    pub fn contains(&self, t: &T) -> bool {
        self.weight_map.contains_key(t)
    }

    /// Encode the weighted sum into an [`IntegerExpression`]
    ///
    /// This method will return the [`WeightedSum`] encoded as an
    /// [`IntegerExpression`]. In case the weighted sum contains a fraction that
    /// is not in an integer form this function **will encode the fraction**
    /// without panicking or returning an error
    fn get_integer_expression<S>(&self) -> IntegerExpression<S>
    where
        T: Into<IntegerExpression<S>>,
        S: Atomic,
    {
        self.weight_map
            .iter()
            .fold(IntegerExpression::Const(0), |acc, (v, c)| {
                debug_assert!(c != &Fraction::from(0));
                debug_assert!(c.is_integer());

                let mut expr = v.clone().into();
                if *c != Fraction::from(1) {
                    expr = IntegerExpression::from(*c) * expr;
                }

                // remove initial accumulator value
                if acc == IntegerExpression::Const(0) {
                    return expr;
                }
                acc + expr
            })
    }

    /// Returns an iterator over all atoms in the weighted sum
    pub fn get_atoms_appearing(&self) -> impl Iterator<Item = &T> {
        self.weight_map.keys()
    }
}

impl<T, F, I> From<I> for WeightedSum<T>
where
    T: Atomic,
    F: Into<Fraction> + Clone,
    I: IntoIterator<Item = (T, F)>,
{
    fn from(value: I) -> Self {
        Self::new(value)
    }
}

impl<T: Atomic> fmt::Display for WeightedSum<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        //? This works but is not very nice: we make the string representation
        //? deterministic by sorting by their string representation.
        let mut it = self.weight_map.iter().collect::<Vec<_>>();
        it.sort_by_key(|(v, _)| v.to_string());
        let mut it = it.into_iter();

        if let Some((v, coef)) = it.next() {
            display_factor_pair_omit_one(f, coef, v)?;
        }

        it.try_for_each(|(v, coef)| {
            write!(f, " + ")?;
            display_factor_pair_omit_one(f, coef, v)
        })?;

        Ok(())
    }
}

impl<'a, T: Atomic> IntoIterator for &'a WeightedSum<T> {
    type Item = (&'a T, &'a Fraction);

    type IntoIter = std::collections::btree_map::Iter<'a, T, Fraction>;

    fn into_iter(self) -> Self::IntoIter {
        self.weight_map.iter()
    }
}

/// Display a scaled pair but omit factor if it is one
///
/// This function converts the pair `factor` * `x` to the string `factor * x`
/// but will omit `factor *` if factor is equal to one
fn display_factor_pair_omit_one<T: fmt::Display>(
    f: &mut std::fmt::Formatter<'_>,
    factor: &Fraction,
    x: &T,
) -> std::fmt::Result {
    if factor == &1.into() {
        write!(f, "{x}")
    } else {
        write!(f, "{factor} * {x}")
    }
}

/// [`WeightedSum`] of [`Parameter`]s with additional constant summand
///
/// This struct represents a sum over [`Parameter`] of the form
/// `c_1 * p_1 + ... + c_n * p_n + c`
/// where p_1, ..., p_n are [`Parameter`] and c_1,..,c_n, c are rational numbers
/// represented by [`Fraction`]s.
#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct Threshold {
    weighted_parameters: WeightedSum<Parameter>,
    constant: Fraction,
}

impl Threshold {
    /// Create a new [`Threshold`]
    pub fn new<S, T>(weighted_parameters: S, constant: T) -> Self
    where
        S: Into<WeightedSum<Parameter>>,
        T: Into<Fraction>,
    {
        Self {
            weighted_parameters: weighted_parameters.into(),
            constant: constant.into(),
        }
    }

    /// Create a new [`Threshold`] from a constant without any parameters
    pub fn from_const<T: Into<Fraction>>(c: T) -> Self {
        Self {
            weighted_parameters: WeightedSum::new_empty(),
            constant: c.into(),
        }
    }

    /// Scale the [`Threshold`] by a rational factor
    pub fn scale<T: Into<Fraction>>(&mut self, factor: T) {
        let factor = factor.into();
        self.weighted_parameters.scale(factor);
        self.constant *= factor;
    }

    /// Check whether the [`Threshold`] only contains a constant
    pub fn is_constant(&self) -> bool {
        self.weighted_parameters.is_zero()
    }

    /// Check whether the [`Threshold`] always evaluates to 0, i.e. there are no
    /// scaled [`Parameter`] and the constant is 0
    pub fn is_zero(&self) -> bool {
        self.weighted_parameters.is_zero() && self.constant == Fraction::from(0)
    }

    /// If the threshold is constant, return the constant
    ///
    /// Returns `None` otherwise
    pub fn get_const(&self) -> Option<Fraction> {
        if self.weighted_parameters.is_zero() {
            return Some(self.constant);
        }

        None
    }

    /// Add a constant to the threshold
    pub fn add_const<F: Into<Fraction>>(&mut self, c: F) {
        self.constant += c.into()
    }

    /// Subtract a constant from the threshold
    pub fn sub_const<F: Into<Fraction>>(&mut self, c: F) {
        self.constant -= c.into()
    }
}

impl ops::Add for Threshold {
    type Output = Threshold;

    fn add(self, rhs: Self) -> Self::Output {
        let constant = self.constant + rhs.constant;
        let mut ws = self.weighted_parameters;

        rhs.weighted_parameters
            .weight_map
            .into_iter()
            .for_each(|(p, s)| {
                ws.weight_map
                    .entry(p)
                    .and_modify(|existing| *existing += s)
                    .or_insert(s);
            });

        ws.weight_map.retain(|_, f| !f.is_zero());

        Self {
            weighted_parameters: ws,
            constant,
        }
    }
}

impl ops::Sub for Threshold {
    type Output = Threshold;

    fn sub(self, rhs: Self) -> Self::Output {
        let constant = self.constant - rhs.constant;
        let mut ws = self.weighted_parameters;

        rhs.weighted_parameters
            .weight_map
            .into_iter()
            .for_each(|(p, s)| {
                ws.weight_map
                    .entry(p)
                    .and_modify(|existing| *existing -= s)
                    .or_insert(-s);
            });

        ws.weight_map.retain(|_, f| !f.is_zero());

        Self {
            weighted_parameters: ws,
            constant,
        }
    }
}

impl fmt::Display for Threshold {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.weighted_parameters.is_zero() {
            return write!(f, "{}", self.constant);
        }

        write!(f, "{}", self.weighted_parameters)?;
        if self.constant != Fraction::from(0) {
            write!(f, " + {}", self.constant)?;
        }

        Ok(())
    }
}

/// Restricted form of [`ComparisonOp`]
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum ThresholdCompOp {
    /// >=
    Geq,
    /// >
    Gt,
    /// <
    Lt,
    /// <=
    Leq,
}

impl ThresholdCompOp {
    /// Check whether the operator is not satisfied exactly at the threshold
    /// but at its neighbors (`>` and `<=`), i.e., whether an interval
    /// abstraction needs an exact interval `[t, t]` for the threshold `t`
    pub fn needs_exact_interval(&self) -> bool {
        matches!(self, ThresholdCompOp::Gt | ThresholdCompOp::Leq)
    }
}

impl From<ThresholdCompOp> for ComparisonOp {
    fn from(value: ThresholdCompOp) -> Self {
        match value {
            ThresholdCompOp::Geq => ComparisonOp::Geq,
            ThresholdCompOp::Lt => ComparisonOp::Lt,
            ThresholdCompOp::Gt => ComparisonOp::Gt,
            ThresholdCompOp::Leq => ComparisonOp::Leq,
        }
    }
}

impl fmt::Display for ThresholdCompOp {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            ThresholdCompOp::Geq => write!(f, ">="),
            ThresholdCompOp::Lt => write!(f, "<"),
            ThresholdCompOp::Gt => write!(f, ">"),
            ThresholdCompOp::Leq => write!(f, "<="),
        }
    }
}

/// [`Threshold`] in combination with a comparison operator
///
/// A [`ThresholdConstraint`] represents a [`Threshold`] in combination with a
/// comparison operator. Thus it can be used to represent equations of the form
///  `<COMPOP> c_1 * p_1 + ... + c_n * p_n + c`
/// where `<COMPOP>` is one of the comparison operators `==`, `!=`, `<`, `>`,
/// `<=`, `>=` (represented by [`ComparisonOp`]).
///
/// Most importantly, this struct implements operations like scaling by a
/// negative number faithfully. Thus it can be useful when transforming
/// threshold guards.
#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct ThresholdConstraint(ThresholdCompOp, Threshold);

impl ThresholdConstraint {
    /// Create a new threshold constraint
    pub fn new<S, T>(op: ThresholdCompOp, weighted_parameters: S, constant: T) -> Self
    where
        S: Into<WeightedSum<Parameter>>,
        T: Into<Fraction>,
    {
        let thr = Threshold::new(weighted_parameters, constant);
        Self(op, thr)
    }

    /// Create a new threshold constraint
    pub fn new_from_thr(op: ThresholdCompOp, thr: Threshold) -> Self {
        Self(op, thr)
    }

    /// Scale the threshold constraint by a fraction
    pub fn scale<T: Into<Fraction>>(&mut self, factor: T) {
        let factor = factor.into();
        // first execute * -1, then scale
        if factor.is_negative() {
            match self.0 {
                ThresholdCompOp::Geq => {
                    self.0 = ThresholdCompOp::Leq;
                }
                ThresholdCompOp::Lt => {
                    self.0 = ThresholdCompOp::Gt;
                }
                ThresholdCompOp::Gt => {
                    self.0 = ThresholdCompOp::Lt;
                }
                ThresholdCompOp::Leq => {
                    self.0 = ThresholdCompOp::Geq;
                }
            }
        }

        self.1.scale(factor);
    }

    /// Get the [`ComparisonOp`] used in the threshold
    pub fn get_op(&self) -> ThresholdCompOp {
        self.0
    }

    /// Get the [`Threshold`] of the threshold constraint
    pub fn get_threshold(&self) -> &Threshold {
        &self.1
    }
}

impl fmt::Display for ThresholdConstraint {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{} {}", self.0, self.1)
    }
}

/// Trait that needs to implemented by expressions which can be derived from
/// thresholds and scaled expressions of type `T`
pub trait DeriveFromIntegerComp<T: Atomic, E: Error + From<ConstraintRewriteError>>
where
    Self: Sized + And + Or,
{
    /// Derive from threshold and map scaled values of `T`
    fn form_ordered_constr(
        scaled_t: HashMap<T, Fraction>,
        thr_c: ThresholdConstraint,
    ) -> Result<Self, E>;

    /// Derive the the type T from the integer expression
    fn from_integer_expr(
        lhs: IntegerExpression<T>,
        op: ComparisonOp,
        rhs: IntegerExpression<T>,
    ) -> Result<Self, E> {
        match op {
            ComparisonOp::Gt => {
                let op = ThresholdCompOp::Gt;

                let (variables, thr) = split_pairs_into_atom_and_threshold(lhs, rhs)?;
                let thr_c = ThresholdConstraint::new_from_thr(op, thr);
                Self::form_ordered_constr(variables, thr_c)
            }
            ComparisonOp::Geq => {
                let (variables, thr) = split_pairs_into_atom_and_threshold(lhs, rhs)?;
                let thr_c = ThresholdConstraint::new_from_thr(ThresholdCompOp::Geq, thr);
                Self::form_ordered_constr(variables, thr_c)
            }
            ComparisonOp::Leq => {
                let op = ThresholdCompOp::Leq;

                let (variables, thr) = split_pairs_into_atom_and_threshold(lhs, rhs)?;
                let thr_c = ThresholdConstraint::new_from_thr(op, thr);

                Self::form_ordered_constr(variables, thr_c)
            }
            ComparisonOp::Lt => {
                let (variables, thr) = split_pairs_into_atom_and_threshold(lhs, rhs)?;
                let thr_c = ThresholdConstraint::new_from_thr(ThresholdCompOp::Lt, thr);
                Self::form_ordered_constr(variables, thr_c)
            }
            ComparisonOp::Eq => {
                let lower_constr =
                    Self::from_integer_expr(lhs.clone(), ComparisonOp::Leq, rhs.clone())?;
                let upper_constr =
                    Self::from_integer_expr(lhs.clone(), ComparisonOp::Geq, rhs.clone())?;

                Ok(lower_constr.and(upper_constr))
            }
            ComparisonOp::Neq => {
                let lower_constr =
                    Self::from_integer_expr(lhs.clone(), ComparisonOp::Lt, rhs.clone())?;
                let upper_constr =
                    Self::from_integer_expr(lhs.clone(), ComparisonOp::Gt, rhs.clone())?;

                Ok(lower_constr.or(upper_constr))
            }
        }
    }
}

/// This struct represents a [`Threshold`] constraint over an object of type T
///
/// It is used to, for example, represent a threshold guard over a variable
#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub(crate) struct ThresholdConstraintOver<T> {
    t: T,
    thr_constr: ThresholdConstraint,
}

impl<T> ThresholdConstraintOver<T> {
    /// Create a new symbolic constraint over an object of type `T`
    pub fn new(t: T, thr_constr: ThresholdConstraint) -> Self {
        Self { t, thr_constr }
    }

    /// Check whether the constraint is an upper guard
    ///
    /// An upper guard is a guard of the form `< t` or `<= t` or `!= t` or
    /// `== t`, as it can become disabled when the threshold is reached.
    pub fn is_upper_guard(&self) -> bool {
        matches!(
            self.thr_constr.get_op(),
            ThresholdCompOp::Lt | ThresholdCompOp::Leq
        )
    }

    /// Check whether the constraint is a lower guard
    ///
    /// A lower guard is a guard of the form `> t` or `>= t` or `!= t` or
    /// `== t`, as it can become enabled when the threshold is reached.
    pub fn is_lower_guard(&self) -> bool {
        matches!(
            self.thr_constr.get_op(),
            ThresholdCompOp::Geq | ThresholdCompOp::Gt
        )
    }

    /// Get the subject of the constraint
    pub fn get_t(&self) -> &T {
        &self.t
    }

    /// Get the threshold of the constraint
    pub fn get_threshold(&self) -> &Threshold {
        self.thr_constr.get_threshold()
    }

    /// Get the threshold constraint of this constraint
    pub fn get_threshold_constraint(&self) -> &ThresholdConstraint {
        &self.thr_constr
    }

    /// Encode the constraint into a BooleanExpression
    ///
    /// This encoding will be guaranteed to not include rational constants
    pub fn encode_to_boolean_expr<S>(&self) -> BooleanExpression<S>
    where
        S: Atomic,
        T: IntoNoDivBooleanExpr<S>,
        Threshold: IntoNoDivBooleanExpr<S>,
    {
        self.t.encode_comparison_to_boolean_expression(
            self.thr_constr.get_op().into(),
            self.thr_constr.get_threshold(),
        )
    }
}

impl<S, T> From<ThresholdConstraintOver<T>> for BooleanExpression<S>
where
    S: Atomic,
    T: IntoNoDivBooleanExpr<S>,
    Threshold: IntoNoDivBooleanExpr<S>,
{
    fn from(val: ThresholdConstraintOver<T>) -> Self {
        val.encode_to_boolean_expr()
    }
}

impl<T> fmt::Display for ThresholdConstraintOver<T>
where
    T: fmt::Display,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{} {}", self.t, self.thr_constr)
    }
}

/// Trait for objects that can be encoded into boolean expressions that
/// do not contain any integer divisions or real numbers.
///
/// When using this trait all expressions will be scaled such that there are no
/// longer real coefficients appearing in the expression, but the set of
/// satisfying (integer) solutions will stay the same.
///
/// This is done by computing the least common multiple (LCM) of all
/// denominators of rational coefficients and then scaling both sides of a
/// `ComparisonExpr` to obtain an equivalent expression only containing integers.
///
/// Note that using this trait might result in a lot of LCM computations.
pub trait IntoNoDivBooleanExpr<T>
where
    T: Atomic,
{
    /// Get the scaled integer expression
    ///
    /// **Important:** The scaling factor supplied will be a multiple of the
    /// least common multiple (LCM) of the expression. That is the relation
    /// `scaling_factor % self.get_lcm_of_denominators() == 0` must hold.
    ///
    /// This function converts the object into an integer expression without any
    /// divisions or real numbers. To eliminate rational coefficients, the
    /// expression is therefore scaled by the given factor.    
    fn get_scaled_integer_expression(&self, scaling_factor: u32) -> IntegerExpression<T>;

    /// Get the lcm across all denominators in the object
    ///
    /// This is useful to determine the (least) scaling factor needed to scale
    /// this expressions such that it does not contain any real numbers.
    fn get_lcm_of_denominators(&self) -> u32;

    /// Encode the comparison of two expressions into a boolean expression with a
    /// that does not contain any real numbers.
    ///
    /// This functions scales the given thresholds such that in both thresholds
    /// all factors are integers. The scaling is done by computing the least
    /// common multiple (LCM) of the denominators.
    ///
    /// Resulting comparison: `self <OP> other`
    fn encode_comparison_to_boolean_expression<Q>(
        &self,
        comparison_op: ComparisonOp,
        other: &Q,
    ) -> BooleanExpression<T>
    where
        Q: IntoNoDivBooleanExpr<T>,
    {
        let lcm_self = self.get_lcm_of_denominators();
        let lcm_other = other.get_lcm_of_denominators();
        let lcm = num::integer::lcm(lcm_self, lcm_other);

        let self_s = self.get_scaled_integer_expression(lcm);
        let other_s = other.get_scaled_integer_expression(lcm);

        BooleanExpression::ComparisonExpression(Box::new(self_s), comparison_op, Box::new(other_s))
    }
}

impl<T> IntoNoDivBooleanExpr<T> for Parameter
where
    Self: Into<IntegerExpression<T>>,
    T: Atomic,
{
    fn get_scaled_integer_expression(&self, scaling_factor: u32) -> IntegerExpression<T> {
        if scaling_factor == 0 {
            return IntegerExpression::Const(0);
        }
        if scaling_factor == 1 {
            return IntegerExpression::from(self.clone());
        }

        IntegerExpression::from(scaling_factor) * IntegerExpression::from(self.clone())
    }

    fn get_lcm_of_denominators(&self) -> u32 {
        1 // Parameters do not have denominators
    }
}

impl<T> IntoNoDivBooleanExpr<T> for Location
where
    T: Atomic,
    IntegerExpression<T>: From<Self>,
    IntegerExpression<T>: From<u32>,
{
    fn get_scaled_integer_expression(&self, scaling_factor: u32) -> IntegerExpression<T> {
        if scaling_factor == 0 {
            return IntegerExpression::Const(0);
        }
        if scaling_factor == 1 {
            return IntegerExpression::from(self.clone());
        }

        IntegerExpression::<T>::from(scaling_factor) * IntegerExpression::<T>::from(self.clone())
    }

    fn get_lcm_of_denominators(&self) -> u32 {
        1 // Locations do not have denominators
    }
}

impl<T> IntoNoDivBooleanExpr<T> for Variable
where
    T: Atomic,
    IntegerExpression<T>: From<Self>,
    IntegerExpression<T>: From<u32>,
{
    fn get_scaled_integer_expression(&self, scaling_factor: u32) -> IntegerExpression<T> {
        if scaling_factor == 0 {
            return IntegerExpression::Const(0);
        }
        if scaling_factor == 1 {
            return IntegerExpression::from(self.clone());
        }

        IntegerExpression::<T>::from(scaling_factor) * IntegerExpression::<T>::from(self.clone())
    }

    fn get_lcm_of_denominators(&self) -> u32 {
        1 // Variables do not have denominators
    }
}

impl<T, S> IntoNoDivBooleanExpr<S> for WeightedSum<T>
where
    T: Atomic + IntoNoDivBooleanExpr<S>,
    S: Atomic,
    IntegerExpression<S>: From<T>,
{
    fn get_scaled_integer_expression(&self, scaling_factor: u32) -> IntegerExpression<S> {
        let mut scaled = self.clone();
        scaled.scale(Fraction::from(scaling_factor));
        debug_assert!(
            scaled.is_integer_form(),
            "Scaled weighted sum is not in integer form"
        );

        scaled.get_integer_expression()
    }

    fn get_lcm_of_denominators(&self) -> u32 {
        self.get_lcm_of_denominators()
    }
}

impl<T> IntoNoDivBooleanExpr<T> for Threshold
where
    WeightedSum<Parameter>: IntoNoDivBooleanExpr<T>,
    T: Atomic,
{
    fn get_scaled_integer_expression(&self, scaling_factor: u32) -> IntegerExpression<T> {
        let scaled_constant = self.constant * Fraction::from(scaling_factor);
        debug_assert!(
            scaled_constant.is_integer(),
            "Scaled constant is not an integer"
        );

        if self.weighted_parameters.is_zero() {
            return IntegerExpression::from(scaled_constant);
        }

        let intexpr_ws = self
            .weighted_parameters
            .get_scaled_integer_expression(scaling_factor);

        if scaled_constant == Fraction::from(0) {
            return intexpr_ws;
        }

        intexpr_ws + IntegerExpression::from(scaled_constant)
    }

    fn get_lcm_of_denominators(&self) -> u32 {
        let lcm_ws = self.weighted_parameters.get_lcm_of_denominators();
        let lcm_const = self.constant.denominator();
        num::integer::lcm(lcm_ws, lcm_const)
    }
}

#[cfg(test)]
mod tests {
    use std::collections::{BTreeMap, HashSet};

    use crate::{
        expressions::{
            BooleanExpression, ComparisonOp, IntegerExpression, Location, Parameter, Variable,
            fraction::Fraction,
        },
        lia_threshold_automaton::integer_thresholds::{
            IntoNoDivBooleanExpr, Threshold, ThresholdCompOp, ThresholdConstraint,
            ThresholdConstraintOver, WeightedSum,
        },
    };

    #[test]
    fn test_threshold_is_zero() {
        let thr = Threshold::new(Vec::<(Parameter, Fraction)>::new(), 0);
        assert!(thr.is_zero());

        let thr = Threshold::new(BTreeMap::from([(Parameter::new("n"), 1)]), 0);
        assert!(!thr.is_zero());

        let thr = Threshold::new(Vec::<(Parameter, Fraction)>::new(), 1);
        assert!(!thr.is_zero());

        let thr = Threshold::new(
            BTreeMap::from([(Parameter::new("n"), 1)]),
            -Fraction::from(1),
        );
        assert!(!thr.is_zero());
    }

    #[test]
    fn test_threshold_is_constant() {
        let thr = Threshold::new(Vec::<(Parameter, Fraction)>::new(), 0);
        assert!(thr.is_constant());

        let thr = Threshold::new(BTreeMap::from([(Parameter::new("n"), 1)]), 0);
        assert!(!thr.is_constant());

        let thr = Threshold::new(Vec::<(Parameter, Fraction)>::new(), 1);
        assert!(thr.is_constant());

        let thr = Threshold::new(
            BTreeMap::from([(Parameter::new("n"), 1)]),
            -Fraction::from(1),
        );
        assert!(!thr.is_constant());
    }

    #[test]
    fn test_threshold_scale() {
        let mut thr = Threshold::new(BTreeMap::from([(Parameter::new("n"), 1)]), 0);
        thr.scale(2);

        let expected = Threshold::new(BTreeMap::from([(Parameter::new("n"), 2)]), 0);
        assert_eq!(thr, expected);

        let mut thr = Threshold::new(BTreeMap::from([(Parameter::new("n"), 0)]), 1);
        thr.scale(-Fraction::from(2));

        let expected = Threshold::new(
            BTreeMap::from([(Parameter::new("n"), Fraction::from(0))]),
            -Fraction::from(2),
        );
        assert_eq!(thr, expected);

        let mut thr = Threshold::new(BTreeMap::from([(Parameter::new("n"), 1)]), 0);
        thr.scale(0);

        let expected = Threshold::new(BTreeMap::from([(Parameter::new("n"), 0)]), 0);
        assert_eq!(thr, expected);
    }

    #[test]
    fn test_threshold_add_cons() {
        let mut thr = Threshold::new(Vec::<(Parameter, Fraction)>::new(), 0);
        assert!(thr.is_constant());

        thr.add_const(1);
        assert_eq!(thr.get_const().unwrap(), Fraction::from(1));

        thr.sub_const(1);
        assert_eq!(thr.get_const().unwrap(), Fraction::from(0));

        let mut thr = Threshold::new(BTreeMap::from([(Parameter::new("n"), 1)]), 0);
        thr.add_const(1);
        assert_eq!(thr.get_const(), None);

        thr.sub_const(1);
        assert_eq!(thr.get_const(), None);
    }

    #[test]
    fn test_threshold_add() {
        // disjoint parameters are combined
        let thr = Threshold::new(BTreeMap::from([(Parameter::new("n"), 1)]), 1)
            + Threshold::new(BTreeMap::from([(Parameter::new("m"), 2)]), 2);

        let expected = Threshold::new(
            BTreeMap::from([(Parameter::new("n"), 1), (Parameter::new("m"), 2)]),
            3,
        );
        assert_eq!(thr, expected);

        // coefficients of parameters appearing in both summands accumulate
        let thr = Threshold::new(BTreeMap::from([(Parameter::new("n"), 2)]), 1)
            + Threshold::new(BTreeMap::from([(Parameter::new("n"), 3)]), 2);

        let expected = Threshold::new(BTreeMap::from([(Parameter::new("n"), 5)]), 3);
        assert_eq!(thr, expected);

        // coefficients canceling out to 0 are removed
        let thr = Threshold::new(BTreeMap::from([(Parameter::new("n"), 1)]), 1)
            + Threshold::new(
                BTreeMap::from([(Parameter::new("n"), -Fraction::from(1))]),
                2,
            );

        let expected = Threshold::from_const(3);
        assert_eq!(thr, expected);
        assert!(thr.is_constant());

        // adding pure constants
        let thr = Threshold::from_const(1) + Threshold::from_const(2);
        assert_eq!(thr.get_const().unwrap(), Fraction::from(3));
    }

    #[test]
    fn test_threshold_sub() {
        // disjoint parameters: coefficients of the rhs are subtracted
        let thr = Threshold::new(BTreeMap::from([(Parameter::new("n"), 1)]), 1)
            - Threshold::new(BTreeMap::from([(Parameter::new("m"), 2)]), 3);

        let expected = Threshold::new(
            BTreeMap::from([
                (Parameter::new("n"), Fraction::from(1)),
                (Parameter::new("m"), -Fraction::from(2)),
            ]),
            -Fraction::from(2),
        );
        assert_eq!(thr, expected);

        // coefficients of parameters appearing in both are subtracted
        let thr = Threshold::new(BTreeMap::from([(Parameter::new("n"), 5)]), 3)
            - Threshold::new(BTreeMap::from([(Parameter::new("n"), 2)]), 1);

        let expected = Threshold::new(BTreeMap::from([(Parameter::new("n"), 3)]), 2);
        assert_eq!(thr, expected);

        // subtracting a threshold from itself yields 0
        let thr = Threshold::new(BTreeMap::from([(Parameter::new("n"), 1)]), 1)
            - Threshold::new(BTreeMap::from([(Parameter::new("n"), 1)]), 1);
        assert!(thr.is_zero());

        // resulting coefficients may become negative
        let thr = Threshold::new(BTreeMap::from([(Parameter::new("n"), 1)]), 0)
            - Threshold::new(BTreeMap::from([(Parameter::new("n"), 2)]), 0);

        let expected = Threshold::new(
            BTreeMap::from([(Parameter::new("n"), -Fraction::from(1))]),
            0,
        );
        assert_eq!(thr, expected);
    }

    #[test]
    fn test_threshold_constr_getters() {
        let thrc = ThresholdConstraint::new(
            ThresholdCompOp::Geq,
            BTreeMap::from([
                (Parameter::new("n"), Fraction::from(1)),
                (Parameter::new("m"), -Fraction::from(2)),
            ]),
            1,
        );

        let thr = Threshold::new(
            [
                (Parameter::new("n"), Fraction::from(1)),
                (Parameter::new("m"), -Fraction::from(2)),
            ],
            1,
        );

        assert_eq!(thrc.get_threshold(), &thr)
    }

    #[test]
    fn test_threshold_constr_scale() {
        let mut thrc = ThresholdConstraint::new(
            ThresholdCompOp::Gt,
            BTreeMap::from([
                (Parameter::new("n"), Fraction::from(1)),
                (Parameter::new("m"), -Fraction::from(2)),
            ]),
            1,
        );
        thrc.scale(Fraction::from(1));

        let expected = ThresholdConstraint::new(
            ThresholdCompOp::Gt,
            BTreeMap::from([
                (Parameter::new("n"), Fraction::from(1)),
                (Parameter::new("m"), -Fraction::from(2)),
            ]),
            Fraction::from(1),
        );

        assert_eq!(thrc, expected);

        thrc.scale(Fraction::from(2));

        let expected = ThresholdConstraint::new(
            ThresholdCompOp::Gt,
            BTreeMap::from([
                (Parameter::new("n"), Fraction::from(2)),
                (Parameter::new("m"), -Fraction::from(4)),
            ]),
            Fraction::from(2),
        );

        assert_eq!(thrc, expected);

        thrc.scale(Fraction::new(1, 2, false));

        let expected = ThresholdConstraint::new(
            ThresholdCompOp::Gt,
            BTreeMap::from([
                (Parameter::new("n"), Fraction::from(1)),
                (Parameter::new("m"), -Fraction::from(2)),
            ]),
            1,
        );

        assert_eq!(thrc, expected);
    }

    #[test]
    fn test_threshold_constr_scale_with_negative() {
        let mut thrc = ThresholdConstraint::new(
            ThresholdCompOp::Gt,
            BTreeMap::from([
                (Parameter::new("n"), Fraction::from(1)),
                (Parameter::new("m"), -Fraction::from(2)),
            ]),
            1,
        );

        thrc.scale(-Fraction::from(2));

        let expected = ThresholdConstraint::new(
            ThresholdCompOp::Lt,
            BTreeMap::from([
                (Parameter::new("n"), -Fraction::from(2)),
                (Parameter::new("m"), Fraction::from(4)),
            ]),
            -Fraction::from(2),
        );

        assert_eq!(thrc, expected);

        let mut thrc = ThresholdConstraint::new(
            ThresholdCompOp::Leq,
            BTreeMap::from([
                (Parameter::new("n"), Fraction::from(1)),
                (Parameter::new("m"), -Fraction::from(2)),
            ]),
            1,
        );

        thrc.scale(-Fraction::from(2));

        let expected = ThresholdConstraint::new(
            ThresholdCompOp::Geq,
            BTreeMap::from([
                (Parameter::new("n"), -Fraction::from(2)),
                (Parameter::new("m"), Fraction::from(4)),
            ]),
            -Fraction::from(2),
        );

        assert_eq!(thrc, expected);

        let mut thrc = ThresholdConstraint::new(
            ThresholdCompOp::Lt,
            BTreeMap::from([
                (Parameter::new("n"), Fraction::from(1)),
                (Parameter::new("m"), -Fraction::from(2)),
            ]),
            1,
        );

        thrc.scale(-Fraction::from(2));

        let expected = ThresholdConstraint::new(
            ThresholdCompOp::Gt,
            BTreeMap::from([
                (Parameter::new("n"), -Fraction::from(2)),
                (Parameter::new("m"), Fraction::from(4)),
            ]),
            -Fraction::from(2),
        );

        assert_eq!(thrc, expected);

        let mut thrc = ThresholdConstraint::new(
            ThresholdCompOp::Leq,
            BTreeMap::from([
                (Parameter::new("n"), Fraction::from(1)),
                (Parameter::new("m"), -Fraction::from(2)),
            ]),
            1,
        );

        thrc.scale(-Fraction::from(2));

        let expected = ThresholdConstraint::new(
            ThresholdCompOp::Geq,
            BTreeMap::from([
                (Parameter::new("n"), -Fraction::from(2)),
                (Parameter::new("m"), Fraction::from(4)),
            ]),
            -Fraction::from(2),
        );

        assert_eq!(thrc, expected);
    }

    #[test]
    fn test_threshold_display() {
        let thr = ThresholdConstraint::new(
            ThresholdCompOp::Geq,
            BTreeMap::from([
                (Parameter::new("n"), Fraction::from(1)),
                (Parameter::new("m"), -Fraction::from(2)),
            ]),
            1,
        );

        let expected = ">= -2 * m + n + 1";
        assert_eq!(thr.to_string(), expected);

        let thr =
            ThresholdConstraint::new(ThresholdCompOp::Geq, Vec::<(Parameter, Fraction)>::new(), 0);
        assert_eq!(thr.to_string(), ">= 0");
    }

    #[test]
    fn test_contains_weighted_sum() {
        let ws = WeightedSum::new(BTreeMap::from([
            (Variable::new("var1"), 1),
            (Variable::new("var2"), 2),
        ]));

        assert!(ws.contains(&Variable::new("var1")));
        assert!(!ws.contains(&Variable::new("var3")));
    }

    #[test]
    fn test_get_atoms_appearing_ws() {
        let ws = WeightedSum::new(BTreeMap::from([
            (Variable::new("var1"), 1),
            (Variable::new("var2"), 2),
        ]));

        let got_atoms: HashSet<_> = ws.get_atoms_appearing().cloned().collect();
        let expected_atoms = HashSet::from([Variable::new("var1"), Variable::new("var2")]);
        assert_eq!(got_atoms, expected_atoms)
    }

    #[test]
    fn test_into_scaled_integer_expression_weighted_sum() {
        let ws: WeightedSum<Parameter> = WeightedSum::new(BTreeMap::from([
            (Parameter::new("var1"), 1),
            (Parameter::new("var2"), 2),
            (Parameter::new("var3"), 0),
        ]));

        let expected: IntegerExpression<Parameter> =
            IntegerExpression::Param(Parameter::new("var1"))
                + (IntegerExpression::Const(2) * IntegerExpression::Param(Parameter::new("var2")));

        let ws = ws.get_scaled_integer_expression(1);

        assert_eq!(ws, expected);

        let ws: WeightedSum<Parameter> = WeightedSum::new(BTreeMap::from([
            (Parameter::new("var1"), 1),
            (Parameter::new("var2"), 2),
            (Parameter::new("var3"), 0),
        ]));

        let expected: IntegerExpression<Parameter> = (IntegerExpression::Const(5)
            * IntegerExpression::Param(Parameter::new("var1")))
            + (IntegerExpression::Const(10) * IntegerExpression::Param(Parameter::new("var2")));

        let ws = ws.get_scaled_integer_expression(5);

        assert_eq!(ws, expected);
    }

    #[test]
    fn test_weighted_sum_into_iter() {
        let ws: WeightedSum<Variable> = WeightedSum::new([
            (Variable::new("var1"), 1),
            (Variable::new("var2"), 2),
            (Variable::new("var3"), 0),
        ]);

        let expected: Vec<(Variable, Fraction)> = vec![
            (Variable::new("var1"), 1.into()),
            (Variable::new("var2"), 2.into()),
        ];

        let result: Vec<(Variable, Fraction)> =
            (&ws).into_iter().map(|(a, b)| (a.clone(), *b)).collect();
        assert_eq!(result, expected);
    }

    #[test]
    fn test_to_boolean_expr_thr_constr_over_var() {
        let constr = ThresholdConstraintOver::new(
            Variable::new("v"),
            ThresholdConstraint::new(ThresholdCompOp::Geq, [(Parameter::new("n"), 1)], 1),
        );

        let b_expr = BooleanExpression::from(constr);

        let expected_b_expr = BooleanExpression::ComparisonExpression(
            Box::new(IntegerExpression::Atom(Variable::new("v"))),
            ComparisonOp::Geq,
            Box::new(IntegerExpression::Param(Parameter::new("n")) + IntegerExpression::Const(1)),
        );

        assert_eq!(b_expr, expected_b_expr)
    }

    #[test]
    fn test_into_no_div_for_param() {
        let param = Parameter::new("n");

        assert_eq!(
            <Parameter as IntoNoDivBooleanExpr<Parameter>>::get_lcm_of_denominators(&param),
            1
        );

        let expected_int_expr: IntegerExpression<Parameter> =
            IntegerExpression::Const(42) * IntegerExpression::Param(param.clone());
        assert_eq!(param.get_scaled_integer_expression(42), expected_int_expr)
    }

    #[test]
    fn test_into_no_div_for_loc() {
        let loc = Location::new("n");

        assert_eq!(
            <Location as IntoNoDivBooleanExpr<Location>>::get_lcm_of_denominators(&loc),
            1
        );

        let expected_int_expr: IntegerExpression<Location> =
            IntegerExpression::Const(42) * IntegerExpression::Atom(loc.clone());
        assert_eq!(loc.get_scaled_integer_expression(42), expected_int_expr)
    }

    #[test]
    fn test_into_no_div_for_var() {
        let var = Variable::new("n");

        assert_eq!(
            <Variable as IntoNoDivBooleanExpr<Variable>>::get_lcm_of_denominators(&var),
            1
        );

        let expected_int_expr: IntegerExpression<Variable> =
            IntegerExpression::Const(42) * IntegerExpression::Atom(var.clone());
        assert_eq!(var.get_scaled_integer_expression(42), expected_int_expr)
    }
}
