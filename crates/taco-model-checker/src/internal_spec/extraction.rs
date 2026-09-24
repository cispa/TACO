//! Module implementing the extraction of internal specification type from
//! general LTL formulas

use core::{error, fmt};
use std::ops::Not;

use taco_threshold_automaton::{
    expressions::BooleanExpression,
    lia_threshold_automaton::{
        ConstraintRewriteError, LIAVariableConstraint, integer_thresholds::DeriveFromIntegerComp,
    },
};

use crate::{
    eltl::{ELTLExpression, remove_negations::NonNegatedELTLExpression},
    internal_spec::{
        Disjunction, ErrorAtom, ErrorFormula, ErrorSpec,
        ErrorTarget::{self, Ensure, Invariant, Reach, Repeat, Top},
        InitRestriction,
        extraction::ExtractionError::NestedTemporalOperator,
        upwards_closed_set::{UpwardsClosedSet, UpwardsClosedSetExtractionError},
    },
};

impl ErrorSpec {
    /// Error specification of a named ELTL formula
    ///
    /// `property` describes the erroneous behavior and is not negated here.
    /// Negations are pushed to the atoms, then the formula is transformed into
    /// an [`ErrorFormula`]. Temporal operators at the top level become
    /// targets. Atoms at the top level restrict the initial configuration.
    pub fn from_named_eltl<S: Into<String>>(
        name: S,
        property: ELTLExpression,
    ) -> Result<Self, ExtractionError> {
        let ef = extract_error_formula(property.clone().not().into())?;

        Ok(Self {
            name: name.into(),
            source: Box::new(property),
            ef,
        })
    }
}

impl ErrorFormula {
    /// Create a new Error formula for the specific target
    pub fn new(init: InitRestriction, tgt: ErrorTarget) -> Self {
        Disjunction::from([ErrorAtom::new(init, tgt)])
    }
}

impl ErrorAtom {
    /// Conjunction of two atoms that are the operands of one `&&`
    ///
    /// Create conjunction of initial constraints and check whether targets can
    /// be unified with [`ErrorTarget::try_unify_and`].
    /// Otherwise throws [`ExtractionError::UnsupportedConjunction`]
    fn try_and(self, other: Self) -> Result<Self, ExtractionError> {
        let target = self
            .target
            .try_unify_and(&other.target)
            .ok_or_else(|| ExtractionError::UnsupportedConjunction(self.target, other.target))?;

        Ok(Self::new(
            self.init_restriction & other.init_restriction,
            target,
        ))
    }

    /// Disjunction of two atoms if a sound merge exists
    fn try_unify_or(&self, other: &Self) -> Option<Self> {
        // `(i && t) || (j && t)` is equal to `(i || j) && t`
        if self.target == other.target {
            let init = self.init_restriction.try_or(&other.init_restriction)?;
            return Some(Self::new(init, self.target.clone()));
        }

        // `(i && t) || (i && u)` is equal to `i && (t || u)`
        if self.init_restriction == other.init_restriction {
            let target = self.target.try_unify_or(&other.target)?;
            return Some(Self::new(self.init_restriction.clone(), target));
        }

        None
    }
}

impl ErrorTarget {
    /// Merge two targets that are the operands of one `&&`, if possible
    fn try_unify_and(&self, other: &Self) -> Option<Self> {
        // Distributivity only holds for []
        match (self, other) {
            (Top, tgt) | (tgt, Top) => Some(tgt.clone()),
            (Invariant(l), Invariant(r)) => Some(Invariant(l.clone() & r.clone())),
            // `[](a) && [](pre && <>(inv))` is equal to `[](a && pre && <>(inv))`
            (Invariant(a), Repeat { pre, inv }) | (Repeat { pre, inv }, Invariant(a)) => {
                Some(Repeat {
                    pre: pre.clone() & a.clone(),
                    inv: inv.clone(),
                })
            }
            // `<>` and `[]<>` do not distribute over `&&`
            (_, _) => None,
        }
    }

    /// Merge two targets that are the operands of one `||`, if possible
    fn try_unify_or(&self, other: &Self) -> Option<Self> {
        match (self, other) {
            (Reach(l), Reach(r)) => Some(Self::Reach(l.clone() | r.clone())),
            (
                Ensure {
                    pre: pre_l,
                    inv: inv_l,
                },
                Ensure {
                    pre: pre_r,
                    inv: inv_r,
                },
            ) => {
                if inv_l != inv_r {
                    return None;
                }

                let pre = pre_l.clone() | pre_r.clone();
                Some(Ensure {
                    pre,
                    inv: inv_l.clone(),
                })
            }
            (_, _) => None,
        }
    }

    /// Extract the invariant or repeat target of a formula inside a `[]`
    fn extract_from_inner_globally(
        expr: NonNegatedELTLExpression,
    ) -> Result<ErrorTarget, ExtractionError> {
        extract_from_inner_globally_helper(expr, true)
    }

    /// Extract the reach and repeat targets of a formula inside an `<>`
    fn extract_from_inner_eventually(
        expr: NonNegatedELTLExpression,
    ) -> Result<Disjunction<ErrorTarget>, ExtractionError> {
        extract_from_inner_eventually_helper(expr, true)
    }
}

/// Error formula of an ELTL formula without negations
///
/// Temporal operators at the top level become targets. Atoms at the top level
/// restrict the initial configuration. `&&` distributes over the disjunction
/// of atoms. Atoms of one `||` are merged where a sound merge exists.
fn extract_error_formula(expr: NonNegatedELTLExpression) -> Result<ErrorFormula, ExtractionError> {
    match expr {
        NonNegatedELTLExpression::Globally(inner) => {
            let tgt = ErrorTarget::extract_from_inner_globally(*inner)?;
            Ok(ErrorFormula::new(InitRestriction::new_top(), tgt))
        }
        NonNegatedELTLExpression::Eventually(inner) => {
            let tgts = ErrorTarget::extract_from_inner_eventually(*inner)?;
            Ok(tgts
                .into_iter()
                .map(|tgt| ErrorAtom::new(InitRestriction::new_top(), tgt))
                .collect())
        }
        // `(a || b) && (c || d)` is equal to
        // `(a && c) || (a && d) || (b && c) || (b && d)`
        NonNegatedELTLExpression::And(lhs, rhs) => {
            let lhs = extract_error_formula(*lhs)?;
            let rhs = extract_error_formula(*rhs)?;

            lhs.into_iter()
                .flat_map(|l| rhs.iter().map(move |r| l.clone().try_and(r.clone())))
                .collect()
        }
        NonNegatedELTLExpression::Or(lhs, rhs) => {
            let lhs = extract_error_formula(*lhs)?;
            let rhs = extract_error_formula(*rhs)?;

            Ok(unify_all_possible(lhs, rhs, ErrorAtom::try_unify_or))
        }
        // Atoms hold at the first position of the run. Because of this, they
        // restrict the initial configuration.
        NonNegatedELTLExpression::LocationExpr(lhs, op, rhs) => {
            let constr = BooleanExpression::ComparisonExpression(lhs, op, rhs);
            let init = InitRestriction::new_location_constraint(constr);
            Ok(ErrorFormula::new(init, Top))
        }
        NonNegatedELTLExpression::VariableExpr(lhs, op, rhs) => {
            let constr = BooleanExpression::ComparisonExpression(lhs, op, rhs);
            let init = InitRestriction::new_variable_constraint(constr);
            Ok(ErrorFormula::new(init, Top))
        }
        NonNegatedELTLExpression::ParameterExpr(lhs, op, rhs) => {
            let constr = BooleanExpression::ComparisonExpression(lhs, op, rhs);
            let init = InitRestriction::new_parameter_constraint(constr);
            Ok(ErrorFormula::new(init, Top))
        }
        NonNegatedELTLExpression::True => Ok(ErrorFormula::new(InitRestriction::new_top(), Top)),
        // The empty disjunction is `false`
        NonNegatedELTLExpression::False => Ok(ErrorFormula::new_bot()),
    }
}

/// Extract the targets of an ELTL formula that is inside an outer `<>`
///
/// The result is a disjunction of [`Reach`] and [`Repeat`] targets.
/// `ev_not_in_conj` is `true` if until now, constraints inside the eventually
/// have not yet appeared in a conjunction. Only then can we apply
/// distributivity and remove nested `<>`
fn extract_from_inner_eventually_helper(
    expr: NonNegatedELTLExpression,
    ev_not_in_conj: bool,
) -> Result<Disjunction<ErrorTarget>, ExtractionError> {
    match expr {
        NonNegatedELTLExpression::Globally(expr) => {
            match ErrorTarget::extract_from_inner_globally(*expr)? {
                // `<>([](inv))` -> `<>(true && [](inv))`
                Invariant(inv) => {
                    let tgt = ErrorTarget::new_ensure(UpwardsClosedSet::new_top(), inv);
                    Ok([tgt].into())
                }
                // `<>([](pre && <>(inv)))` cannot be translated
                _ => Err(NestedTemporalOperator),
            }
        }
        NonNegatedELTLExpression::Eventually(expr) => {
            // Distributivity does not apply
            if !ev_not_in_conj {
                return Err(ExtractionError::NestedTemporalOperator);
            }
            extract_from_inner_eventually_helper(*expr, true)
        }
        // Both operands hold at the same position of the run. Because of this,
        // each target of `lhs` is combined with each target of `rhs`.
        NonNegatedELTLExpression::And(lhs, rhs) => {
            let lhs = extract_from_inner_eventually_helper(*lhs, false)?;
            let rhs = extract_from_inner_eventually_helper(*rhs, false)?;

            // Note: Here we know that lhs and rhs do not contain a nested <>,
            // and they can only contain Reach and Repeat specifications
            // This means that any

            Ok(lhs
                .into_iter()
                .flat_map(|l| {
                    rhs.iter()
                        .map(move |r| and_inside_eventually(l.clone(), r.clone()))
                })
                .collect())
        }

        NonNegatedELTLExpression::Or(lhs, rhs) => {
            let lhs = extract_from_inner_eventually_helper(*lhs, ev_not_in_conj)?;
            let rhs = extract_from_inner_eventually_helper(*rhs, ev_not_in_conj)?;

            let tgts = unify_all_possible(lhs, rhs, ErrorTarget::try_unify_or);

            Ok(tgts)
        }
        s => Ok([Reach(extract_atom_helper(s)?)].into()),
    }
}

/// Helper function to extract the target of an ELTL formula that appears
/// inside of an outer []
///
/// The result is an [`Invariant`] or a [`Repeat`] target.
/// `appears_in_conj` specifies whether inner constraints have until now
/// only appeared in a conjunction. Only if this is the case, distributivity
/// holds and an inner globally operator can be parsed as a simple conjunct
fn extract_from_inner_globally_helper(
    expr: NonNegatedELTLExpression,
    appears_in_conj: bool,
) -> Result<ErrorTarget, ExtractionError> {
    match expr {
        NonNegatedELTLExpression::Globally(expr) => {
            if !appears_in_conj {
                return Err(ExtractionError::NestedTemporalOperator);
            }

            extract_from_inner_globally_helper(*expr, true)
        }

        NonNegatedELTLExpression::Eventually(expr) => {
            let tgts = ErrorTarget::extract_from_inner_eventually(*expr)?;
            let inv = tgts
                .into_iter()
                // `<>(a || b)` is equal to `<>(a) || <>(b)`
                .try_fold(UpwardsClosedSet::new_bot(), |acc, tgt| match tgt {
                    Reach(set) => Ok(acc | set),
                    _ => Err(NestedTemporalOperator),
                })?;

            Ok(Repeat {
                pre: UpwardsClosedSet::new_top(),
                inv,
            })
        }
        NonNegatedELTLExpression::And(lhs, rhs) => {
            let lhs = extract_from_inner_globally_helper(*lhs, appears_in_conj)?;
            let rhs = extract_from_inner_globally_helper(*rhs, appears_in_conj)?;

            lhs.try_unify_and(&rhs)
                .ok_or(ExtractionError::UnsupportedConjunction(lhs, rhs))
        }
        NonNegatedELTLExpression::Or(lhs, rhs) => {
            let lhs = extract_from_inner_globally_helper(*lhs, false)?;
            let rhs = extract_from_inner_globally_helper(*rhs, false)?;

            or_inside_globally(lhs, rhs)
        }
        // The remaining cases are atoms
        s => Ok(Invariant(extract_atom_helper(s)?)),
    }
}

/// Disjunction of two targets that are the operands of one `||` inside an
/// outer `[]`
///
/// `[]` does not distribute over `||`. Because of this, the operands are merged
/// below the `[]` into a single target.
fn or_inside_globally(l: ErrorTarget, r: ErrorTarget) -> Result<ErrorTarget, ExtractionError> {
    match (l, r) {
        (Invariant(a), Invariant(b)) => Ok(Invariant(a | b)),
        // `(p && <>(a)) || (p && <>(b))` is equal to `p && <>(a || b)`
        (
            Repeat {
                pre: pre_l,
                inv: inv_l,
            },
            Repeat {
                pre: pre_r,
                inv: inv_r,
            },
        ) if pre_l == pre_r => Ok(Repeat {
            pre: pre_l,
            inv: inv_l | inv_r,
        }),
        // `a || <>(b)` and `(p && <>(a)) || (q && <>(b))` have no single target
        (_, _) => Err(NestedTemporalOperator),
    }
}

/// Helper function to and constraints inside an eventually specification
///
/// Note that this function does only compute correct results if no nested <>
/// appeared while parsing the inner constraints.
/// This is necessary, because otherwise would need distributivity, which does
/// not hold in the and case for <>
fn and_inside_eventually(l: ErrorTarget, r: ErrorTarget) -> ErrorTarget {
    match (l, r) {
        (Top, o) | (o, Top) => o,
        (Reach(r1), Reach(r2)) => Reach(r1 & r2),
        (Reach(r), Ensure { pre, inv }) | (Ensure { pre, inv }, Reach(r)) => {
            Ensure { pre: pre & r, inv }
        }
        (
            Ensure {
                pre: pre1,
                inv: inv1,
            },
            Ensure {
                pre: pre2,
                inv: inv2,
            },
        ) => Ensure {
            pre: pre1 & pre2,
            inv: inv1 & inv2,
        },
        (_, _) => unreachable!("No other target should have been parsed"),
    }
}

/// Upwards closed set of a single atom
fn extract_atom_helper(
    expr: NonNegatedELTLExpression,
) -> Result<UpwardsClosedSet, ExtractionError> {
    match expr {
        NonNegatedELTLExpression::LocationExpr(lhs, op, rhs) => {
            Ok(UpwardsClosedSet::from_integer_expr(*lhs, op, *rhs)?)
        }
        NonNegatedELTLExpression::VariableExpr(lhs, op, rhs) => {
            let var = LIAVariableConstraint::from_integer_expr(*lhs, op, *rhs)?;

            Ok(UpwardsClosedSet::new_var_constraint(var))
        }
        NonNegatedELTLExpression::True => Ok(UpwardsClosedSet::new_top()),
        NonNegatedELTLExpression::False => Ok(UpwardsClosedSet::new_bot()),
        NonNegatedELTLExpression::ParameterExpr(_, _, _) => unreachable!(
            "This case should have been filtered out when validating the specification"
        ),

        NonNegatedELTLExpression::And(_, _)
        | NonNegatedELTLExpression::Or(_, _)
        | NonNegatedELTLExpression::Globally(_)
        | NonNegatedELTLExpression::Eventually(_) => {
            unreachable!("This helper should only be used for atoms")
        }
    }
}

/// Helper function for combining two disjunctions into one
///
/// This function will try to unify as many disjuncts of `lhs` with disjuncts
/// of `rhs` as possible, using `try_unify`
fn unify_all_possible<T: PartialEq>(
    mut lhs: Disjunction<T>,
    mut rhs: Disjunction<T>,
    try_unify: impl Fn(&T, &T) -> Option<T>,
) -> Disjunction<T> {
    let mut lhs_idx = 0;
    let mut rhs_idx = 0;

    while lhs_idx < lhs.len() && rhs_idx < rhs.len() {
        if let Some(unified) = try_unify(&lhs[lhs_idx], &rhs[rhs_idx]) {
            lhs.0.remove(lhs_idx);
            rhs.0.remove(rhs_idx);

            lhs.0.push(unified);
            rhs_idx = 0;
            continue;
        }

        if rhs_idx + 1 < rhs.len() {
            rhs_idx += 1;
            continue;
        }

        lhs_idx += 1;
        rhs_idx = 0;
    }

    lhs.into_iter().chain(rhs).collect::<Vec<_>>().into()
}

#[derive(Debug, Clone, PartialEq)]
pub enum ExtractionError {
    NestedTemporalOperator,
    /// Two targets of one `&&` that have no single target, e.g. `<>(a) && <>(b)`
    UnsupportedConjunction(ErrorTarget, ErrorTarget),
    LocationConstraintNotUpwardsClosed(UpwardsClosedSetExtractionError),
    VariableExprNonLinear(ConstraintRewriteError),
}

impl fmt::Display for ExtractionError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            NestedTemporalOperator => write!(f, "Temporal Operator alternation"),
            ExtractionError::UnsupportedConjunction(a, b) => {
                write!(f, "Unsupported Conjunction between'{a}' and {b}")
            }
            ExtractionError::LocationConstraintNotUpwardsClosed(err) => {
                write!(f, "Unsupported Specification: {err}")
            }
            ExtractionError::VariableExprNonLinear(err) => {
                write!(f, "Unsupported Specification: {err}")
            }
        }
    }
}

impl error::Error for ExtractionError {}

impl From<UpwardsClosedSetExtractionError> for ExtractionError {
    fn from(value: UpwardsClosedSetExtractionError) -> Self {
        Self::LocationConstraintNotUpwardsClosed(value)
    }
}

impl From<ConstraintRewriteError> for ExtractionError {
    fn from(value: ConstraintRewriteError) -> Self {
        Self::VariableExprNonLinear(value)
    }
}

#[cfg(test)]
mod test {
    use taco_threshold_automaton::{
        expressions::{
            BooleanExpression, ComparisonOp, IntegerExpression, Location, Parameter, Variable,
        },
        lia_threshold_automaton::{
            LIAVariableConstraint, integer_thresholds::DeriveFromIntegerComp,
        },
    };

    use crate::{
        eltl::ELTLExpression,
        internal_spec::{
            ErrorAtom, ErrorFormula, ErrorSpec, ErrorTarget, InitRestriction,
            extraction::ExtractionError, upwards_closed_set::UpwardsClosedSet,
        },
    };

    #[test]
    fn simple_ensure() {
        // [](loc0 > 1 && loc1 = 0 || var = 1)
        let eltl = !ELTLExpression::Globally(Box::new(ELTLExpression::Or(
            Box::new(ELTLExpression::And(
                Box::new(ELTLExpression::LocationExpr(
                    Box::new(IntegerExpression::Atom(Location::new("loc0"))),
                    ComparisonOp::Gt,
                    Box::new(IntegerExpression::Const(1)),
                )),
                Box::new(ELTLExpression::LocationExpr(
                    Box::new(IntegerExpression::Atom(Location::new("loc1"))),
                    ComparisonOp::Eq,
                    Box::new(IntegerExpression::Const(0)),
                )),
            )),
            Box::new(ELTLExpression::VariableExpr(
                Box::new(IntegerExpression::Atom(Variable::new("var"))),
                ComparisonOp::Eq,
                Box::new(IntegerExpression::Const(1)),
            )),
        )));

        let got = ErrorSpec::from_named_eltl("test", eltl.clone());

        // `[](loc0 > 1 && loc1 = 0 || var = 1)` is an ensure target with the
        // upwards closed set `(loc0 > 1 && loc1 = 0) || var = 1`.
        let loc0_gt_1 = UpwardsClosedSet::from_integer_expr(
            IntegerExpression::Atom(Location::new("loc0")),
            ComparisonOp::Gt,
            IntegerExpression::Const(1),
        )
        .unwrap();
        let loc1_eq_0 = UpwardsClosedSet::from_integer_expr(
            IntegerExpression::Atom(Location::new("loc1")),
            ComparisonOp::Eq,
            IntegerExpression::Const(0),
        )
        .unwrap();
        let var_eq_1 = LIAVariableConstraint::from_integer_expr(
            IntegerExpression::Atom(Variable::new("var")),
            ComparisonOp::Eq,
            IntegerExpression::Const(1),
        )
        .unwrap();
        let inv = (loc0_gt_1 & loc1_eq_0) | UpwardsClosedSet::new_var_constraint(var_eq_1);

        let expected = ErrorSpec {
            name: "test".to_string(),
            source: Box::new(eltl.clone()),
            ef: ErrorFormula::new(InitRestriction::new_top(), ErrorTarget::Invariant(inv)),
        };

        assert!(got.is_ok(), "Error:{}", got.unwrap_err());
        let got = got.unwrap();

        assert_eq!(got, expected, "Expected:{expected}\nGot:{got}");
    }

    #[test]
    fn simple_ensure_distributivity() {
        // [](loc0 > 1 && [](loc1 = 0))
        let eltl = !ELTLExpression::Globally(Box::new(ELTLExpression::And(
            Box::new(ELTLExpression::LocationExpr(
                Box::new(IntegerExpression::Atom(Location::new("loc0"))),
                ComparisonOp::Gt,
                Box::new(IntegerExpression::Const(1)),
            )),
            Box::new(ELTLExpression::Globally(Box::new(
                ELTLExpression::LocationExpr(
                    Box::new(IntegerExpression::Atom(Location::new("loc1"))),
                    ComparisonOp::Eq,
                    Box::new(IntegerExpression::Const(0)),
                ),
            ))),
        )));

        let got = ErrorSpec::from_named_eltl("test", eltl.clone());

        // `loc0 > 1 && loc1 = 0`.
        let loc0_gt_1 = UpwardsClosedSet::from_integer_expr(
            IntegerExpression::Atom(Location::new("loc0")),
            ComparisonOp::Gt,
            IntegerExpression::Const(1),
        )
        .unwrap();
        let loc1_eq_0 = UpwardsClosedSet::from_integer_expr(
            IntegerExpression::Atom(Location::new("loc1")),
            ComparisonOp::Eq,
            IntegerExpression::Const(0),
        )
        .unwrap();

        let inv = loc0_gt_1 & loc1_eq_0;

        let expected = ErrorSpec {
            name: "test".to_string(),
            source: Box::new(eltl.clone()),
            ef: ErrorFormula::new(InitRestriction::new_top(), ErrorTarget::Invariant(inv)),
        };

        assert!(got.is_ok(), "Error:{}", got.unwrap_err());
        let got = got.unwrap();

        assert_eq!(got, expected, "Expected:{expected}\nGot:{got}");
    }

    #[test]
    fn simple_ensure_not_distributive() {
        // [](loc0 > 1 || [](loc1 = 0))
        let eltl = !ELTLExpression::Globally(Box::new(ELTLExpression::Or(
            Box::new(ELTLExpression::LocationExpr(
                Box::new(IntegerExpression::Atom(Location::new("loc0"))),
                ComparisonOp::Gt,
                Box::new(IntegerExpression::Const(1)),
            )),
            Box::new(ELTLExpression::Globally(Box::new(
                ELTLExpression::LocationExpr(
                    Box::new(IntegerExpression::Atom(Location::new("loc1"))),
                    ComparisonOp::Eq,
                    Box::new(IntegerExpression::Const(0)),
                ),
            ))),
        )));

        let got = ErrorSpec::from_named_eltl("test", eltl.clone());

        assert!(
            !got.is_ok(),
            "Unexpectedly extracted specification:{}",
            got.unwrap()
        );
        let got = got.unwrap_err();

        let expected = ExtractionError::NestedTemporalOperator;

        assert_eq!(got, expected, "Expected:{expected}\nGot:{got}");
    }

    #[test]
    fn simple_ensure_with_init_constr() {
        // loc0 > 1 && [](loc1 = 0)
        let ltl = !ELTLExpression::And(
            Box::new(ELTLExpression::LocationExpr(
                Box::new(IntegerExpression::Atom(Location::new("loc0"))),
                ComparisonOp::Gt,
                Box::new(IntegerExpression::Const(1)),
            )),
            Box::new(ELTLExpression::Globally(Box::new(
                ELTLExpression::LocationExpr(
                    Box::new(IntegerExpression::Atom(Location::new("loc1"))),
                    ComparisonOp::Eq,
                    Box::new(IntegerExpression::Const(0)),
                ),
            ))),
        );

        let got = ErrorSpec::from_named_eltl("test", ltl.clone());

        // The atom `loc0 > 1` restricts the initial configuration, the
        // `[](loc1 = 0)` part becomes an ensure target.
        let init =
            InitRestriction::new_location_constraint(BooleanExpression::ComparisonExpression(
                Box::new(IntegerExpression::Atom(Location::new("loc0"))),
                ComparisonOp::Gt,
                Box::new(IntegerExpression::Const(1)),
            ));
        let inv = UpwardsClosedSet::from_integer_expr(
            IntegerExpression::Atom(Location::new("loc1")),
            ComparisonOp::Eq,
            IntegerExpression::Const(0),
        )
        .unwrap();

        let expected = ErrorSpec {
            name: "test".to_string(),
            source: Box::new(ltl.clone()),
            ef: ErrorFormula::new(init, ErrorTarget::Invariant(inv)),
        };

        assert!(got.is_ok(), "Error:{}", got.unwrap_err());
        let got = got.unwrap();

        assert_eq!(got, expected, "Expected:{expected}\nGot:{got}");
    }

    #[test]
    fn simple_ensure_with_init_constr_two() {
        // (loc3 = 0 || loc2 = 0) && loc0 > 1 && [](loc1 = 0)
        let ltl = !ELTLExpression::And(
            Box::new(ELTLExpression::Or(
                Box::new(ELTLExpression::LocationExpr(
                    Box::new(IntegerExpression::Atom(Location::new("loc3"))),
                    ComparisonOp::Eq,
                    Box::new(IntegerExpression::Const(0)),
                )),
                Box::new(ELTLExpression::LocationExpr(
                    Box::new(IntegerExpression::Atom(Location::new("loc2"))),
                    ComparisonOp::Eq,
                    Box::new(IntegerExpression::Const(0)),
                )),
            )),
            Box::new(ELTLExpression::And(
                Box::new(ELTLExpression::LocationExpr(
                    Box::new(IntegerExpression::Atom(Location::new("loc0"))),
                    ComparisonOp::Gt,
                    Box::new(IntegerExpression::Const(1)),
                )),
                Box::new(ELTLExpression::Globally(Box::new(
                    ELTLExpression::LocationExpr(
                        Box::new(IntegerExpression::Atom(Location::new("loc1"))),
                        ComparisonOp::Eq,
                        Box::new(IntegerExpression::Const(0)),
                    ),
                ))),
            )),
        );

        let got = ErrorSpec::from_named_eltl("test", ltl.clone());

        let loc3_eq_0 = BooleanExpression::ComparisonExpression(
            Box::new(IntegerExpression::Atom(Location::new("loc3"))),
            ComparisonOp::Eq,
            Box::new(IntegerExpression::Const(0)),
        );

        let loc2_eq_0 = BooleanExpression::ComparisonExpression(
            Box::new(IntegerExpression::Atom(Location::new("loc2"))),
            ComparisonOp::Eq,
            Box::new(IntegerExpression::Const(0)),
        );
        let loc0_gt_1 = BooleanExpression::ComparisonExpression(
            Box::new(IntegerExpression::Atom(Location::new("loc0"))),
            ComparisonOp::Gt,
            Box::new(IntegerExpression::Const(1)),
        );
        let init = InitRestriction::new_location_constraint(loc3_eq_0 | loc2_eq_0)
            & InitRestriction::new_location_constraint(loc0_gt_1);
        let inv = UpwardsClosedSet::from_integer_expr(
            IntegerExpression::Atom(Location::new("loc1")),
            ComparisonOp::Eq,
            IntegerExpression::Const(0),
        )
        .unwrap();

        let expected = ErrorSpec {
            name: "test".to_string(),
            source: Box::new(ltl.clone()),
            ef: ErrorFormula::new(init, ErrorTarget::Invariant(inv)),
        };

        assert!(got.is_ok(), "Error:{}", got.unwrap_err());
        let got = got.unwrap();

        assert_eq!(got, expected, "Expected:{}\nGot:{}", expected.ef, got.ef);
    }

    #[test]
    fn reachability_true() {
        // true -> false -> empty disjunction
        let eltl = !ELTLExpression::Not(Box::new(ELTLExpression::True));

        let got = ErrorSpec::from_named_eltl("test", eltl).unwrap().ef;

        assert_eq!(got, ErrorFormula::new_bot());
    }

    #[test]
    fn reachability_false() {
        // false -> true -> every run
        let eltl = ELTLExpression::False;

        let got = ErrorSpec::from_named_eltl("test", eltl).unwrap().ef;

        let expected = ErrorFormula::new(InitRestriction::new_top(), ErrorTarget::Top);
        assert_eq!(got, expected);
    }

    #[test]
    fn reachability_parameter_atom() {
        // n == 3 -> n != 3
        let eltl = ELTLExpression::ParameterExpr(
            Box::new(IntegerExpression::Param(Parameter::new("n"))),
            ComparisonOp::Eq,
            Box::new(IntegerExpression::Const(3)),
        );

        let got = ErrorSpec::from_named_eltl("test", eltl).unwrap().ef;

        let init =
            InitRestriction::new_parameter_constraint(BooleanExpression::ComparisonExpression(
                Box::new(IntegerExpression::Param(Parameter::new("n"))),
                ComparisonOp::Neq,
                Box::new(IntegerExpression::Const(3)),
            ));
        let expected = ErrorFormula::new(init, ErrorTarget::Top);
        assert_eq!(got, expected);
    }

    #[test]
    fn reachability_variable_atom() {
        // v < n -> v >= n
        let eltl = ELTLExpression::VariableExpr(
            Box::new(IntegerExpression::Atom(Variable::new("v"))),
            ComparisonOp::Lt,
            Box::new(IntegerExpression::Param(Parameter::new("n"))),
        );

        let got = ErrorSpec::from_named_eltl("test", eltl).unwrap().ef;

        let init =
            InitRestriction::new_variable_constraint(BooleanExpression::ComparisonExpression(
                Box::new(IntegerExpression::Atom(Variable::new("v"))),
                ComparisonOp::Geq,
                Box::new(IntegerExpression::Param(Parameter::new("n"))),
            ));
        let expected = ErrorFormula::new(init, ErrorTarget::Top);
        assert_eq!(got, expected);
    }

    #[test]
    fn reachability_location_atom() {
        // l < n -> l >= n
        let eltl = ELTLExpression::LocationExpr(
            Box::new(IntegerExpression::Atom(Location::new("l"))),
            ComparisonOp::Lt,
            Box::new(IntegerExpression::Param(Parameter::new("n"))),
        );

        let got = ErrorSpec::from_named_eltl("test", eltl).unwrap().ef;

        let init =
            InitRestriction::new_location_constraint(BooleanExpression::ComparisonExpression(
                Box::new(IntegerExpression::Atom(Location::new("l"))),
                ComparisonOp::Geq,
                Box::new(IntegerExpression::Param(Parameter::new("n"))),
            ));
        let expected = ErrorFormula::new(init, ErrorTarget::Top);
        assert_eq!(got, expected);
    }

    #[test]
    fn reachability_and_of_atoms() {
        // (l < 1) && (v < 3) -> (l >= 1) || (v >= 3)
        let eltl = ELTLExpression::And(
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
        );

        let got = ErrorSpec::from_named_eltl("test", eltl).unwrap().ef;

        // The two restrictions differ in two kinds of atoms. Because of this,
        // they stay two atoms.
        let init_l =
            InitRestriction::new_location_constraint(BooleanExpression::ComparisonExpression(
                Box::new(IntegerExpression::Atom(Location::new("l"))),
                ComparisonOp::Geq,
                Box::new(IntegerExpression::Const(1)),
            ));
        let init_v =
            InitRestriction::new_variable_constraint(BooleanExpression::ComparisonExpression(
                Box::new(IntegerExpression::Atom(Variable::new("v"))),
                ComparisonOp::Geq,
                Box::new(IntegerExpression::Const(3)),
            ));
        let expected = ErrorFormula::from([
            ErrorAtom::new(init_l, ErrorTarget::Top),
            ErrorAtom::new(init_v, ErrorTarget::Top),
        ]);
        assert_eq!(got, expected);
    }

    #[test]
    fn reachability_or_of_atoms() {
        // (l < 1) || (v < 3) -> (l >= 1) && (v >= 3)

        let eltl = ELTLExpression::Or(
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
        );

        let got = ErrorSpec::from_named_eltl("test", eltl).unwrap().ef;

        let init =
            InitRestriction::new_location_constraint(BooleanExpression::ComparisonExpression(
                Box::new(IntegerExpression::Atom(Location::new("l"))),
                ComparisonOp::Geq,
                Box::new(IntegerExpression::Const(1)),
            )) & InitRestriction::new_variable_constraint(BooleanExpression::ComparisonExpression(
                Box::new(IntegerExpression::Atom(Variable::new("v"))),
                ComparisonOp::Geq,
                Box::new(IntegerExpression::Const(3)),
            ));
        let expected = ErrorFormula::new(init, ErrorTarget::Top);
        assert_eq!(got, expected);
    }

    #[test]
    fn reachability_negated_and_of_atoms() {
        // !((l < 1) && (v < 3)) -> (l < 1) && (v < 3)
        let eltl = ELTLExpression::Not(Box::new(ELTLExpression::And(
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
        )));

        let got = ErrorSpec::from_named_eltl("test", eltl).unwrap().ef;

        let init =
            InitRestriction::new_location_constraint(BooleanExpression::ComparisonExpression(
                Box::new(IntegerExpression::Atom(Location::new("l"))),
                ComparisonOp::Lt,
                Box::new(IntegerExpression::Const(1)),
            )) & InitRestriction::new_variable_constraint(BooleanExpression::ComparisonExpression(
                Box::new(IntegerExpression::Atom(Variable::new("v"))),
                ComparisonOp::Lt,
                Box::new(IntegerExpression::Const(3)),
            ));
        let expected = ErrorFormula::new(init, ErrorTarget::Top);
        assert_eq!(got, expected);
    }

    #[test]
    fn reachability_globally_true() {
        // [](true) -> <>(false)
        let eltl = ELTLExpression::Globally(Box::new(ELTLExpression::True));

        let got = ErrorSpec::from_named_eltl("test", eltl).unwrap().ef;

        let expected = ErrorFormula::new(
            InitRestriction::new_top(),
            ErrorTarget::Reach(UpwardsClosedSet::new_bot()),
        );
        assert_eq!(got, expected);
    }

    #[test]
    fn reachability_globally_false() {
        // [](false) -> <>(true)
        let eltl = ELTLExpression::Globally(Box::new(ELTLExpression::False));

        let got = ErrorSpec::from_named_eltl("test", eltl).unwrap().ef;

        let expected = ErrorFormula::new(
            InitRestriction::new_top(),
            ErrorTarget::Reach(UpwardsClosedSet::new_top()),
        );
        assert_eq!(got, expected);
    }

    #[test]
    fn reachability_globally_variable() {
        // [](v < n) -> <>(v >= n)
        let eltl = ELTLExpression::Globally(Box::new(ELTLExpression::VariableExpr(
            Box::new(IntegerExpression::Atom(Variable::new("v"))),
            ComparisonOp::Lt,
            Box::new(IntegerExpression::Param(Parameter::new("n"))),
        )));

        let got = ErrorSpec::from_named_eltl("test", eltl).unwrap().ef;

        let target = UpwardsClosedSet::new_var_constraint(
            LIAVariableConstraint::from_integer_expr(
                IntegerExpression::Atom(Variable::new("v")),
                ComparisonOp::Geq,
                IntegerExpression::Param(Parameter::new("n")),
            )
            .unwrap(),
        );
        let expected = ErrorFormula::new(InitRestriction::new_top(), ErrorTarget::Reach(target));
        assert_eq!(got, expected);
    }

    #[test]
    fn reachability_globally_location() {
        // [](l == 0) -> <>(l != 0)
        let eltl = ELTLExpression::Globally(Box::new(ELTLExpression::LocationExpr(
            Box::new(IntegerExpression::Atom(Location::new("l"))),
            ComparisonOp::Eq,
            Box::new(IntegerExpression::Const(0)),
        )));

        let got = ErrorSpec::from_named_eltl("test", eltl).unwrap().ef;

        let target = UpwardsClosedSet::new_cover([Location::new("l")]);
        let expected = ErrorFormula::new(InitRestriction::new_top(), ErrorTarget::Reach(target));
        assert_eq!(got, expected);
    }

    #[test]
    fn reachability_globally_or() {
        // [](l1 == 0 || l2 != 0) -> <>(l1 != 0 && l2 == 0)
        let eltl = ELTLExpression::Globally(Box::new(ELTLExpression::Or(
            Box::new(ELTLExpression::LocationExpr(
                Box::new(IntegerExpression::Atom(Location::new("l1"))),
                ComparisonOp::Eq,
                Box::new(IntegerExpression::Const(0)),
            )),
            Box::new(ELTLExpression::LocationExpr(
                Box::new(IntegerExpression::Atom(Location::new("l2"))),
                ComparisonOp::Neq,
                Box::new(IntegerExpression::Const(0)),
            )),
        )));

        let got = ErrorSpec::from_named_eltl("test", eltl).unwrap().ef;

        let target = UpwardsClosedSet::new_reach([(Location::new("l1"), 1)], [Location::new("l2")]);
        let expected = ErrorFormula::new(InitRestriction::new_top(), ErrorTarget::Reach(target));
        assert_eq!(got, expected);
    }

    #[test]
    fn reachability_globally_and() {
        // [](l1 == 0 && l2 != 0) -> <>(l1 != 0 || l2 == 0)
        let eltl = ELTLExpression::Globally(Box::new(ELTLExpression::And(
            Box::new(ELTLExpression::LocationExpr(
                Box::new(IntegerExpression::Atom(Location::new("l1"))),
                ComparisonOp::Eq,
                Box::new(IntegerExpression::Const(0)),
            )),
            Box::new(ELTLExpression::LocationExpr(
                Box::new(IntegerExpression::Atom(Location::new("l2"))),
                ComparisonOp::Neq,
                Box::new(IntegerExpression::Const(0)),
            )),
        )));

        let got = ErrorSpec::from_named_eltl("test", eltl).unwrap().ef;

        // `<>(a) || <>(b)` is equal to `<>(a || b)`, so this is one atom
        let target = UpwardsClosedSet::new_cover([Location::new("l1")])
            | UpwardsClosedSet::new_reach([], [Location::new("l2")]);
        let expected = ErrorFormula::new(InitRestriction::new_top(), ErrorTarget::Reach(target));
        assert_eq!(got, expected);
    }

    #[test]
    fn reachability_nested_globally() {
        // []([](l1 == 0 || l2 != 0)) -> <>(<>(l1 != 0 && l2 == 0))
        let eltl = ELTLExpression::Globally(Box::new(ELTLExpression::Globally(Box::new(
            ELTLExpression::Or(
                Box::new(ELTLExpression::LocationExpr(
                    Box::new(IntegerExpression::Atom(Location::new("l1"))),
                    ComparisonOp::Eq,
                    Box::new(IntegerExpression::Const(0)),
                )),
                Box::new(ELTLExpression::LocationExpr(
                    Box::new(IntegerExpression::Atom(Location::new("l2"))),
                    ComparisonOp::Neq,
                    Box::new(IntegerExpression::Const(0)),
                )),
            ),
        ))));

        let got = ErrorSpec::from_named_eltl("test", eltl).unwrap().ef;

        let target = UpwardsClosedSet::new_reach([(Location::new("l1"), 1)], [Location::new("l2")]);
        let expected = ErrorFormula::new(InitRestriction::new_top(), ErrorTarget::Reach(target));
        assert_eq!(got, expected);
    }

    #[test]
    fn reachability_globally_or_nested_globally() {
        // [](l1 == 0 || [](l2 != 0)) -> <>(l1 != 0 && <>(l2 == 0))
        //
        // The old extraction returned `<>(l1 != 0 && l2 == 0)`, which is not
        // equal to the error formula. `<>` does not distribute over `&&`, so
        // the new extraction rejects the nested `<>`.
        let eltl = ELTLExpression::Globally(Box::new(ELTLExpression::Or(
            Box::new(ELTLExpression::LocationExpr(
                Box::new(IntegerExpression::Atom(Location::new("l1"))),
                ComparisonOp::Eq,
                Box::new(IntegerExpression::Const(0)),
            )),
            Box::new(ELTLExpression::Globally(Box::new(
                ELTLExpression::LocationExpr(
                    Box::new(IntegerExpression::Atom(Location::new("l2"))),
                    ComparisonOp::Neq,
                    Box::new(IntegerExpression::Const(0)),
                ),
            ))),
        )));

        let got = ErrorSpec::from_named_eltl("test", eltl);

        assert_eq!(got, Err(ExtractionError::NestedTemporalOperator));
    }

    #[test]
    fn reachability_implies_globally_or_nested_globally() {
        // (v == 0) => [](l1 == 0 || [](l2 != 0))
        //   -> v == 0 && <>(l1 != 0 && <>(l2 == 0))
        //
        // --> Reject because of missing distributivity
        let eltl = ELTLExpression::Implies(
            Box::new(ELTLExpression::VariableExpr(
                Box::new(IntegerExpression::Atom(Variable::new("v"))),
                ComparisonOp::Eq,
                Box::new(IntegerExpression::Const(0)),
            )),
            Box::new(ELTLExpression::Globally(Box::new(ELTLExpression::Or(
                Box::new(ELTLExpression::LocationExpr(
                    Box::new(IntegerExpression::Atom(Location::new("l1"))),
                    ComparisonOp::Eq,
                    Box::new(IntegerExpression::Const(0)),
                )),
                Box::new(ELTLExpression::Globally(Box::new(
                    ELTLExpression::LocationExpr(
                        Box::new(IntegerExpression::Atom(Location::new("l2"))),
                        ComparisonOp::Neq,
                        Box::new(IntegerExpression::Const(0)),
                    ),
                ))),
            )))),
        );

        let got = ErrorSpec::from_named_eltl("test", eltl);

        assert_eq!(got, Err(ExtractionError::NestedTemporalOperator));
    }

    #[test]
    fn reachability_or_negated_and_globally() {
        // !(l1 == 0 && l2 == 0) || [](l2 == 0)
        //   -> (l1 == 0 && l2 == 0) && <>(l2 != 0)
        let eltl = ELTLExpression::Or(
            Box::new(ELTLExpression::Not(Box::new(ELTLExpression::And(
                Box::new(ELTLExpression::LocationExpr(
                    Box::new(IntegerExpression::Atom(Location::new("l1"))),
                    ComparisonOp::Eq,
                    Box::new(IntegerExpression::Const(0)),
                )),
                Box::new(ELTLExpression::LocationExpr(
                    Box::new(IntegerExpression::Atom(Location::new("l2"))),
                    ComparisonOp::Eq,
                    Box::new(IntegerExpression::Const(0)),
                )),
            )))),
            Box::new(ELTLExpression::Globally(Box::new(
                ELTLExpression::LocationExpr(
                    Box::new(IntegerExpression::Atom(Location::new("l2"))),
                    ComparisonOp::Eq,
                    Box::new(IntegerExpression::Const(0)),
                ),
            ))),
        );

        let got = ErrorSpec::from_named_eltl("test", eltl).unwrap().ef;

        let init =
            InitRestriction::new_location_constraint(BooleanExpression::ComparisonExpression(
                Box::new(IntegerExpression::Atom(Location::new("l1"))),
                ComparisonOp::Eq,
                Box::new(IntegerExpression::Const(0)),
            )) & InitRestriction::new_location_constraint(BooleanExpression::ComparisonExpression(
                Box::new(IntegerExpression::Atom(Location::new("l2"))),
                ComparisonOp::Eq,
                Box::new(IntegerExpression::Const(0)),
            ));
        let target = UpwardsClosedSet::new_cover([Location::new("l2")]);
        let expected = ErrorFormula::new(init, ErrorTarget::Reach(target));
        assert_eq!(got, expected);
    }

    // The `ensure_*` and `repeat_*` tests take the expression as the error
    // formula, i.e., it is not negated.

    #[test]
    fn ensure_true_and_false() {
        // [](true)
        let eltl = !ELTLExpression::Globally(Box::new(ELTLExpression::True));

        let got = ErrorSpec::from_named_eltl("test", eltl).unwrap().ef;

        let expected = ErrorFormula::new(
            InitRestriction::new_top(),
            ErrorTarget::Invariant(UpwardsClosedSet::new_top()),
        );
        assert_eq!(got, expected);

        // [](false)
        let eltl = !ELTLExpression::Globally(Box::new(ELTLExpression::False));

        let got = ErrorSpec::from_named_eltl("test", eltl).unwrap().ef;

        let expected = ErrorFormula::new(
            InitRestriction::new_top(),
            ErrorTarget::Invariant(UpwardsClosedSet::new_bot()),
        );
        assert_eq!(got, expected);
    }

    #[test]
    fn ensure_and_of_globally() {
        // [](l0 > 1) && [](l1 = 0) is equal to [](l0 > 1 && l1 = 0)
        let eltl = !ELTLExpression::And(
            Box::new(ELTLExpression::Globally(Box::new(
                ELTLExpression::LocationExpr(
                    Box::new(IntegerExpression::Atom(Location::new("l0"))),
                    ComparisonOp::Gt,
                    Box::new(IntegerExpression::Const(1)),
                ),
            ))),
            Box::new(ELTLExpression::Globally(Box::new(
                ELTLExpression::LocationExpr(
                    Box::new(IntegerExpression::Atom(Location::new("l1"))),
                    ComparisonOp::Eq,
                    Box::new(IntegerExpression::Const(0)),
                ),
            ))),
        );

        let got = ErrorSpec::from_named_eltl("test", eltl).unwrap().ef;

        let l0_gt_1 = UpwardsClosedSet::from_integer_expr(
            IntegerExpression::Atom(Location::new("l0")),
            ComparisonOp::Gt,
            IntegerExpression::Const(1),
        )
        .unwrap();
        let l1_eq_0 = UpwardsClosedSet::from_integer_expr(
            IntegerExpression::Atom(Location::new("l1")),
            ComparisonOp::Eq,
            IntegerExpression::Const(0),
        )
        .unwrap();
        let expected = ErrorFormula::new(
            InitRestriction::new_top(),
            ErrorTarget::Invariant(l0_gt_1 & l1_eq_0),
        );
        assert_eq!(got, expected);
    }

    #[test]
    fn ensure_or_of_globally() {
        // [](l0 > 1) || [](l1 = 0)
        let eltl = !ELTLExpression::Or(
            Box::new(ELTLExpression::Globally(Box::new(
                ELTLExpression::LocationExpr(
                    Box::new(IntegerExpression::Atom(Location::new("l0"))),
                    ComparisonOp::Gt,
                    Box::new(IntegerExpression::Const(1)),
                ),
            ))),
            Box::new(ELTLExpression::Globally(Box::new(
                ELTLExpression::LocationExpr(
                    Box::new(IntegerExpression::Atom(Location::new("l1"))),
                    ComparisonOp::Eq,
                    Box::new(IntegerExpression::Const(0)),
                ),
            ))),
        );

        let got = ErrorSpec::from_named_eltl("test", eltl).unwrap().ef;

        let l0_gt_1 = UpwardsClosedSet::from_integer_expr(
            IntegerExpression::Atom(Location::new("l0")),
            ComparisonOp::Gt,
            IntegerExpression::Const(1),
        )
        .unwrap();
        let l1_eq_0 = UpwardsClosedSet::from_integer_expr(
            IntegerExpression::Atom(Location::new("l1")),
            ComparisonOp::Eq,
            IntegerExpression::Const(0),
        )
        .unwrap();
        let expected = ErrorFormula::from([
            ErrorAtom::new(InitRestriction::new_top(), ErrorTarget::Invariant(l0_gt_1)),
            ErrorAtom::new(InitRestriction::new_top(), ErrorTarget::Invariant(l1_eq_0)),
        ]);
        assert_eq!(got, expected);
    }

    #[test]
    fn ensure_or_with_init_atom() {
        // [](l0 > 1) || v = 1
        let eltl = !ELTLExpression::Or(
            Box::new(ELTLExpression::Globally(Box::new(
                ELTLExpression::LocationExpr(
                    Box::new(IntegerExpression::Atom(Location::new("l0"))),
                    ComparisonOp::Gt,
                    Box::new(IntegerExpression::Const(1)),
                ),
            ))),
            Box::new(ELTLExpression::VariableExpr(
                Box::new(IntegerExpression::Atom(Variable::new("v"))),
                ComparisonOp::Eq,
                Box::new(IntegerExpression::Const(1)),
            )),
        );

        let got = ErrorSpec::from_named_eltl("test", eltl).unwrap().ef;

        let l0_gt_1 = UpwardsClosedSet::from_integer_expr(
            IntegerExpression::Atom(Location::new("l0")),
            ComparisonOp::Gt,
            IntegerExpression::Const(1),
        )
        .unwrap();
        let init_v =
            InitRestriction::new_variable_constraint(BooleanExpression::ComparisonExpression(
                Box::new(IntegerExpression::Atom(Variable::new("v"))),
                ComparisonOp::Eq,
                Box::new(IntegerExpression::Const(1)),
            ));
        let expected = ErrorFormula::from([
            ErrorAtom::new(InitRestriction::new_top(), ErrorTarget::Invariant(l0_gt_1)),
            ErrorAtom::new(init_v, ErrorTarget::Top),
        ]);
        assert_eq!(got, expected);
    }

    #[test]
    fn ensure_with_init_or_of_two_kinds() {
        // (l0 > 1 || v = 1) && [](l1 = 0): the init restrictions differ in two
        // kinds of atoms, so the disjunction is split into two atoms
        let eltl = !ELTLExpression::And(
            Box::new(ELTLExpression::Or(
                Box::new(ELTLExpression::LocationExpr(
                    Box::new(IntegerExpression::Atom(Location::new("l0"))),
                    ComparisonOp::Gt,
                    Box::new(IntegerExpression::Const(1)),
                )),
                Box::new(ELTLExpression::VariableExpr(
                    Box::new(IntegerExpression::Atom(Variable::new("v"))),
                    ComparisonOp::Eq,
                    Box::new(IntegerExpression::Const(1)),
                )),
            )),
            Box::new(ELTLExpression::Globally(Box::new(
                ELTLExpression::LocationExpr(
                    Box::new(IntegerExpression::Atom(Location::new("l1"))),
                    ComparisonOp::Eq,
                    Box::new(IntegerExpression::Const(0)),
                ),
            ))),
        );

        let got = ErrorSpec::from_named_eltl("test", eltl).unwrap().ef;

        let l1_eq_0 = UpwardsClosedSet::from_integer_expr(
            IntegerExpression::Atom(Location::new("l1")),
            ComparisonOp::Eq,
            IntegerExpression::Const(0),
        )
        .unwrap();
        let init_l0 =
            InitRestriction::new_location_constraint(BooleanExpression::ComparisonExpression(
                Box::new(IntegerExpression::Atom(Location::new("l0"))),
                ComparisonOp::Gt,
                Box::new(IntegerExpression::Const(1)),
            ));
        let init_v =
            InitRestriction::new_variable_constraint(BooleanExpression::ComparisonExpression(
                Box::new(IntegerExpression::Atom(Variable::new("v"))),
                ComparisonOp::Eq,
                Box::new(IntegerExpression::Const(1)),
            ));
        let expected = ErrorFormula::from([
            ErrorAtom::new(init_l0, ErrorTarget::Invariant(l1_eq_0.clone())),
            ErrorAtom::new(init_v, ErrorTarget::Invariant(l1_eq_0)),
        ]);
        assert_eq!(got, expected);
    }

    #[test]
    fn ensure_or_below_and_with_nested_globally() {
        // []((l0 > 1 || l1 = 0) && [](v = 1)) is equal to
        // []((l0 > 1 || l1 = 0) && v = 1)
        let eltl = !ELTLExpression::Globally(Box::new(ELTLExpression::And(
            Box::new(ELTLExpression::Or(
                Box::new(ELTLExpression::LocationExpr(
                    Box::new(IntegerExpression::Atom(Location::new("l0"))),
                    ComparisonOp::Gt,
                    Box::new(IntegerExpression::Const(1)),
                )),
                Box::new(ELTLExpression::LocationExpr(
                    Box::new(IntegerExpression::Atom(Location::new("l1"))),
                    ComparisonOp::Eq,
                    Box::new(IntegerExpression::Const(0)),
                )),
            )),
            Box::new(ELTLExpression::Globally(Box::new(
                ELTLExpression::VariableExpr(
                    Box::new(IntegerExpression::Atom(Variable::new("v"))),
                    ComparisonOp::Eq,
                    Box::new(IntegerExpression::Const(1)),
                ),
            ))),
        )));

        let got = ErrorSpec::from_named_eltl("test", eltl).unwrap().ef;

        let l0_gt_1 = UpwardsClosedSet::from_integer_expr(
            IntegerExpression::Atom(Location::new("l0")),
            ComparisonOp::Gt,
            IntegerExpression::Const(1),
        )
        .unwrap();
        let l1_eq_0 = UpwardsClosedSet::from_integer_expr(
            IntegerExpression::Atom(Location::new("l1")),
            ComparisonOp::Eq,
            IntegerExpression::Const(0),
        )
        .unwrap();
        let v_eq_1 = UpwardsClosedSet::new_var_constraint(
            LIAVariableConstraint::from_integer_expr(
                IntegerExpression::Atom(Variable::new("v")),
                ComparisonOp::Eq,
                IntegerExpression::Const(1),
            )
            .unwrap(),
        );
        let expected = ErrorFormula::new(
            InitRestriction::new_top(),
            ErrorTarget::Invariant((l0_gt_1 | l1_eq_0) & v_eq_1),
        );
        assert_eq!(got, expected);
    }

    #[test]
    fn ensure_and_below_or_with_nested_globally() {
        // [](l0 > 1 || (l1 = 0 && [](v = 1))) has no single set
        let eltl = !ELTLExpression::Globally(Box::new(ELTLExpression::Or(
            Box::new(ELTLExpression::LocationExpr(
                Box::new(IntegerExpression::Atom(Location::new("l0"))),
                ComparisonOp::Gt,
                Box::new(IntegerExpression::Const(1)),
            )),
            Box::new(ELTLExpression::And(
                Box::new(ELTLExpression::LocationExpr(
                    Box::new(IntegerExpression::Atom(Location::new("l1"))),
                    ComparisonOp::Eq,
                    Box::new(IntegerExpression::Const(0)),
                )),
                Box::new(ELTLExpression::Globally(Box::new(
                    ELTLExpression::VariableExpr(
                        Box::new(IntegerExpression::Atom(Variable::new("v"))),
                        ComparisonOp::Eq,
                        Box::new(IntegerExpression::Const(1)),
                    ),
                ))),
            )),
        )));

        let got = ErrorSpec::from_named_eltl("test", eltl);

        assert_eq!(got, Err(ExtractionError::NestedTemporalOperator));
    }

    #[test]
    fn ensure_and_reach_unsupported() {
        // [](l0 > 1) && <>(l1 = 0) has no single target
        let eltl = !ELTLExpression::And(
            Box::new(ELTLExpression::Globally(Box::new(
                ELTLExpression::LocationExpr(
                    Box::new(IntegerExpression::Atom(Location::new("l0"))),
                    ComparisonOp::Gt,
                    Box::new(IntegerExpression::Const(1)),
                ),
            ))),
            Box::new(ELTLExpression::Eventually(Box::new(
                ELTLExpression::LocationExpr(
                    Box::new(IntegerExpression::Atom(Location::new("l1"))),
                    ComparisonOp::Eq,
                    Box::new(IntegerExpression::Const(0)),
                ),
            ))),
        );

        let got = ErrorSpec::from_named_eltl("test", eltl);

        let l0_gt_1 = UpwardsClosedSet::from_integer_expr(
            IntegerExpression::Atom(Location::new("l0")),
            ComparisonOp::Gt,
            IntegerExpression::Const(1),
        )
        .unwrap();
        let l1_eq_0 = UpwardsClosedSet::from_integer_expr(
            IntegerExpression::Atom(Location::new("l1")),
            ComparisonOp::Eq,
            IntegerExpression::Const(0),
        )
        .unwrap();
        let expected = ExtractionError::UnsupportedConjunction(
            ErrorTarget::Invariant(l0_gt_1),
            ErrorTarget::Reach(l1_eq_0),
        );
        assert_eq!(got, Err(expected));
    }

    #[test]
    fn repeat_simple() {
        // <>(l0 > 1 && [](l1 = 0))
        let eltl = !ELTLExpression::Eventually(Box::new(ELTLExpression::And(
            Box::new(ELTLExpression::LocationExpr(
                Box::new(IntegerExpression::Atom(Location::new("l0"))),
                ComparisonOp::Gt,
                Box::new(IntegerExpression::Const(1)),
            )),
            Box::new(ELTLExpression::Globally(Box::new(
                ELTLExpression::LocationExpr(
                    Box::new(IntegerExpression::Atom(Location::new("l1"))),
                    ComparisonOp::Eq,
                    Box::new(IntegerExpression::Const(0)),
                ),
            ))),
        )));

        let got = ErrorSpec::from_named_eltl("test", eltl).unwrap().ef;

        let l0_gt_1 = UpwardsClosedSet::from_integer_expr(
            IntegerExpression::Atom(Location::new("l0")),
            ComparisonOp::Gt,
            IntegerExpression::Const(1),
        )
        .unwrap();
        let l1_eq_0 = UpwardsClosedSet::from_integer_expr(
            IntegerExpression::Atom(Location::new("l1")),
            ComparisonOp::Eq,
            IntegerExpression::Const(0),
        )
        .unwrap();
        let expected = ErrorFormula::new(
            InitRestriction::new_top(),
            ErrorTarget::new_ensure(l0_gt_1, l1_eq_0),
        );
        assert_eq!(got, expected);
    }

    #[test]
    fn repeat_globally_only() {
        // <>([](l1 = 0)) has the precondition `true`
        let eltl = !ELTLExpression::Eventually(Box::new(ELTLExpression::Globally(Box::new(
            ELTLExpression::LocationExpr(
                Box::new(IntegerExpression::Atom(Location::new("l1"))),
                ComparisonOp::Eq,
                Box::new(IntegerExpression::Const(0)),
            ),
        ))));

        let got = ErrorSpec::from_named_eltl("test", eltl).unwrap().ef;

        let l1_eq_0 = UpwardsClosedSet::from_integer_expr(
            IntegerExpression::Atom(Location::new("l1")),
            ComparisonOp::Eq,
            IntegerExpression::Const(0),
        )
        .unwrap();
        let expected = ErrorFormula::new(
            InitRestriction::new_top(),
            ErrorTarget::new_ensure(UpwardsClosedSet::new_top(), l1_eq_0),
        );
        assert_eq!(got, expected);
    }

    #[test]
    fn repeat_with_init() {
        // v = 1 && <>(l0 > 1 && [](l1 = 0))
        let eltl = !ELTLExpression::And(
            Box::new(ELTLExpression::VariableExpr(
                Box::new(IntegerExpression::Atom(Variable::new("v"))),
                ComparisonOp::Eq,
                Box::new(IntegerExpression::Const(1)),
            )),
            Box::new(ELTLExpression::Eventually(Box::new(ELTLExpression::And(
                Box::new(ELTLExpression::LocationExpr(
                    Box::new(IntegerExpression::Atom(Location::new("l0"))),
                    ComparisonOp::Gt,
                    Box::new(IntegerExpression::Const(1)),
                )),
                Box::new(ELTLExpression::Globally(Box::new(
                    ELTLExpression::LocationExpr(
                        Box::new(IntegerExpression::Atom(Location::new("l1"))),
                        ComparisonOp::Eq,
                        Box::new(IntegerExpression::Const(0)),
                    ),
                ))),
            )))),
        );

        let got = ErrorSpec::from_named_eltl("test", eltl).unwrap().ef;

        let init =
            InitRestriction::new_variable_constraint(BooleanExpression::ComparisonExpression(
                Box::new(IntegerExpression::Atom(Variable::new("v"))),
                ComparisonOp::Eq,
                Box::new(IntegerExpression::Const(1)),
            ));
        let l0_gt_1 = UpwardsClosedSet::from_integer_expr(
            IntegerExpression::Atom(Location::new("l0")),
            ComparisonOp::Gt,
            IntegerExpression::Const(1),
        )
        .unwrap();
        let l1_eq_0 = UpwardsClosedSet::from_integer_expr(
            IntegerExpression::Atom(Location::new("l1")),
            ComparisonOp::Eq,
            IntegerExpression::Const(0),
        )
        .unwrap();
        let expected = ErrorFormula::new(init, ErrorTarget::new_ensure(l0_gt_1, l1_eq_0));
        assert_eq!(got, expected);
    }

    #[test]
    fn repeat_and_of_two_globally() {
        // <>(l0 > 1 && [](l1 = 0) && [](v = 1)) is equal to
        // <>(l0 > 1 && [](l1 = 0 && v = 1))
        let eltl = !ELTLExpression::Eventually(Box::new(ELTLExpression::And(
            Box::new(ELTLExpression::LocationExpr(
                Box::new(IntegerExpression::Atom(Location::new("l0"))),
                ComparisonOp::Gt,
                Box::new(IntegerExpression::Const(1)),
            )),
            Box::new(ELTLExpression::And(
                Box::new(ELTLExpression::Globally(Box::new(
                    ELTLExpression::LocationExpr(
                        Box::new(IntegerExpression::Atom(Location::new("l1"))),
                        ComparisonOp::Eq,
                        Box::new(IntegerExpression::Const(0)),
                    ),
                ))),
                Box::new(ELTLExpression::Globally(Box::new(
                    ELTLExpression::VariableExpr(
                        Box::new(IntegerExpression::Atom(Variable::new("v"))),
                        ComparisonOp::Eq,
                        Box::new(IntegerExpression::Const(1)),
                    ),
                ))),
            )),
        )));

        let got = ErrorSpec::from_named_eltl("test", eltl).unwrap().ef;

        let l0_gt_1 = UpwardsClosedSet::from_integer_expr(
            IntegerExpression::Atom(Location::new("l0")),
            ComparisonOp::Gt,
            IntegerExpression::Const(1),
        )
        .unwrap();
        let l1_eq_0 = UpwardsClosedSet::from_integer_expr(
            IntegerExpression::Atom(Location::new("l1")),
            ComparisonOp::Eq,
            IntegerExpression::Const(0),
        )
        .unwrap();
        let v_eq_1 = UpwardsClosedSet::new_var_constraint(
            LIAVariableConstraint::from_integer_expr(
                IntegerExpression::Atom(Variable::new("v")),
                ComparisonOp::Eq,
                IntegerExpression::Const(1),
            )
            .unwrap(),
        );
        let expected = ErrorFormula::new(
            InitRestriction::new_top(),
            ErrorTarget::new_ensure(l0_gt_1, l1_eq_0 & v_eq_1),
        );
        assert_eq!(got, expected);
    }

    #[test]
    fn repeat_nested_globally_in_globally() {
        // <>(l0 > 1 && [](l1 = 0 && [](v = 1))) is equal to
        // <>(l0 > 1 && [](l1 = 0 && v = 1))
        let eltl = !ELTLExpression::Eventually(Box::new(ELTLExpression::And(
            Box::new(ELTLExpression::LocationExpr(
                Box::new(IntegerExpression::Atom(Location::new("l0"))),
                ComparisonOp::Gt,
                Box::new(IntegerExpression::Const(1)),
            )),
            Box::new(ELTLExpression::Globally(Box::new(ELTLExpression::And(
                Box::new(ELTLExpression::LocationExpr(
                    Box::new(IntegerExpression::Atom(Location::new("l1"))),
                    ComparisonOp::Eq,
                    Box::new(IntegerExpression::Const(0)),
                )),
                Box::new(ELTLExpression::Globally(Box::new(
                    ELTLExpression::VariableExpr(
                        Box::new(IntegerExpression::Atom(Variable::new("v"))),
                        ComparisonOp::Eq,
                        Box::new(IntegerExpression::Const(1)),
                    ),
                ))),
            )))),
        )));

        let got = ErrorSpec::from_named_eltl("test", eltl).unwrap().ef;

        let l0_gt_1 = UpwardsClosedSet::from_integer_expr(
            IntegerExpression::Atom(Location::new("l0")),
            ComparisonOp::Gt,
            IntegerExpression::Const(1),
        )
        .unwrap();
        let l1_eq_0 = UpwardsClosedSet::from_integer_expr(
            IntegerExpression::Atom(Location::new("l1")),
            ComparisonOp::Eq,
            IntegerExpression::Const(0),
        )
        .unwrap();
        let v_eq_1 = UpwardsClosedSet::new_var_constraint(
            LIAVariableConstraint::from_integer_expr(
                IntegerExpression::Atom(Variable::new("v")),
                ComparisonOp::Eq,
                IntegerExpression::Const(1),
            )
            .unwrap(),
        );
        let expected = ErrorFormula::new(
            InitRestriction::new_top(),
            ErrorTarget::new_ensure(l0_gt_1, l1_eq_0 & v_eq_1),
        );
        assert_eq!(got, expected);
    }

    #[test]
    fn repeat_or_of_same_invariant() {
        // <>((l0 > 1 && [](v = 1)) || (l1 = 0 && [](v = 1))) is equal to
        // <>((l0 > 1 || l1 = 0) && [](v = 1))
        let eltl = !ELTLExpression::Eventually(Box::new(ELTLExpression::Or(
            Box::new(ELTLExpression::And(
                Box::new(ELTLExpression::LocationExpr(
                    Box::new(IntegerExpression::Atom(Location::new("l0"))),
                    ComparisonOp::Gt,
                    Box::new(IntegerExpression::Const(1)),
                )),
                Box::new(ELTLExpression::Globally(Box::new(
                    ELTLExpression::VariableExpr(
                        Box::new(IntegerExpression::Atom(Variable::new("v"))),
                        ComparisonOp::Eq,
                        Box::new(IntegerExpression::Const(1)),
                    ),
                ))),
            )),
            Box::new(ELTLExpression::And(
                Box::new(ELTLExpression::LocationExpr(
                    Box::new(IntegerExpression::Atom(Location::new("l1"))),
                    ComparisonOp::Eq,
                    Box::new(IntegerExpression::Const(0)),
                )),
                Box::new(ELTLExpression::Globally(Box::new(
                    ELTLExpression::VariableExpr(
                        Box::new(IntegerExpression::Atom(Variable::new("v"))),
                        ComparisonOp::Eq,
                        Box::new(IntegerExpression::Const(1)),
                    ),
                ))),
            )),
        )));

        let got = ErrorSpec::from_named_eltl("test", eltl).unwrap().ef;

        let l0_gt_1 = UpwardsClosedSet::from_integer_expr(
            IntegerExpression::Atom(Location::new("l0")),
            ComparisonOp::Gt,
            IntegerExpression::Const(1),
        )
        .unwrap();
        let l1_eq_0 = UpwardsClosedSet::from_integer_expr(
            IntegerExpression::Atom(Location::new("l1")),
            ComparisonOp::Eq,
            IntegerExpression::Const(0),
        )
        .unwrap();
        let v_eq_1 = UpwardsClosedSet::new_var_constraint(
            LIAVariableConstraint::from_integer_expr(
                IntegerExpression::Atom(Variable::new("v")),
                ComparisonOp::Eq,
                IntegerExpression::Const(1),
            )
            .unwrap(),
        );
        let expected = ErrorFormula::new(
            InitRestriction::new_top(),
            ErrorTarget::new_ensure(l0_gt_1 | l1_eq_0, v_eq_1),
        );
        assert_eq!(got, expected);
    }

    #[test]
    fn repeat_or_of_different_invariants() {
        // <>([](l0 > 1) || [](l1 = 0)) stays two atoms
        let eltl = !ELTLExpression::Eventually(Box::new(ELTLExpression::Or(
            Box::new(ELTLExpression::Globally(Box::new(
                ELTLExpression::LocationExpr(
                    Box::new(IntegerExpression::Atom(Location::new("l0"))),
                    ComparisonOp::Gt,
                    Box::new(IntegerExpression::Const(1)),
                ),
            ))),
            Box::new(ELTLExpression::Globally(Box::new(
                ELTLExpression::LocationExpr(
                    Box::new(IntegerExpression::Atom(Location::new("l1"))),
                    ComparisonOp::Eq,
                    Box::new(IntegerExpression::Const(0)),
                ),
            ))),
        )));

        let got = ErrorSpec::from_named_eltl("test", eltl).unwrap().ef;

        let l0_gt_1 = UpwardsClosedSet::from_integer_expr(
            IntegerExpression::Atom(Location::new("l0")),
            ComparisonOp::Gt,
            IntegerExpression::Const(1),
        )
        .unwrap();
        let l1_eq_0 = UpwardsClosedSet::from_integer_expr(
            IntegerExpression::Atom(Location::new("l1")),
            ComparisonOp::Eq,
            IntegerExpression::Const(0),
        )
        .unwrap();
        let expected = ErrorFormula::from([
            ErrorAtom::new(
                InitRestriction::new_top(),
                ErrorTarget::new_ensure(UpwardsClosedSet::new_top(), l0_gt_1),
            ),
            ErrorAtom::new(
                InitRestriction::new_top(),
                ErrorTarget::new_ensure(UpwardsClosedSet::new_top(), l1_eq_0),
            ),
        ]);
        assert_eq!(got, expected);
    }

    #[test]
    fn repeat_and_distributes_over_or() {
        // <>(l0 > 1 && (l1 = 0 || [](v = 1))) is equal to
        // <>(l0 > 1 && l1 = 0) || <>(l0 > 1 && [](v = 1))
        let eltl = !ELTLExpression::Eventually(Box::new(ELTLExpression::And(
            Box::new(ELTLExpression::LocationExpr(
                Box::new(IntegerExpression::Atom(Location::new("l0"))),
                ComparisonOp::Gt,
                Box::new(IntegerExpression::Const(1)),
            )),
            Box::new(ELTLExpression::Or(
                Box::new(ELTLExpression::LocationExpr(
                    Box::new(IntegerExpression::Atom(Location::new("l1"))),
                    ComparisonOp::Eq,
                    Box::new(IntegerExpression::Const(0)),
                )),
                Box::new(ELTLExpression::Globally(Box::new(
                    ELTLExpression::VariableExpr(
                        Box::new(IntegerExpression::Atom(Variable::new("v"))),
                        ComparisonOp::Eq,
                        Box::new(IntegerExpression::Const(1)),
                    ),
                ))),
            )),
        )));

        let got = ErrorSpec::from_named_eltl("test", eltl).unwrap().ef;

        let l0_gt_1 = UpwardsClosedSet::from_integer_expr(
            IntegerExpression::Atom(Location::new("l0")),
            ComparisonOp::Gt,
            IntegerExpression::Const(1),
        )
        .unwrap();
        let l1_eq_0 = UpwardsClosedSet::from_integer_expr(
            IntegerExpression::Atom(Location::new("l1")),
            ComparisonOp::Eq,
            IntegerExpression::Const(0),
        )
        .unwrap();
        let v_eq_1 = UpwardsClosedSet::new_var_constraint(
            LIAVariableConstraint::from_integer_expr(
                IntegerExpression::Atom(Variable::new("v")),
                ComparisonOp::Eq,
                IntegerExpression::Const(1),
            )
            .unwrap(),
        );
        let expected = ErrorFormula::from([
            ErrorAtom::new(
                InitRestriction::new_top(),
                ErrorTarget::Reach(l0_gt_1.clone() & l1_eq_0),
            ),
            ErrorAtom::new(
                InitRestriction::new_top(),
                ErrorTarget::new_ensure(l0_gt_1, v_eq_1),
            ),
        ]);
        assert_eq!(got, expected);
    }

    #[test]
    fn repeat_product_of_two_ors() {
        // <>(([](l0 > 1) || l1 = 0) && ([](v = 1) || l2 > 0))
        let eltl = !ELTLExpression::Eventually(Box::new(ELTLExpression::And(
            Box::new(ELTLExpression::Or(
                Box::new(ELTLExpression::Globally(Box::new(
                    ELTLExpression::LocationExpr(
                        Box::new(IntegerExpression::Atom(Location::new("l0"))),
                        ComparisonOp::Gt,
                        Box::new(IntegerExpression::Const(1)),
                    ),
                ))),
                Box::new(ELTLExpression::LocationExpr(
                    Box::new(IntegerExpression::Atom(Location::new("l1"))),
                    ComparisonOp::Eq,
                    Box::new(IntegerExpression::Const(0)),
                )),
            )),
            Box::new(ELTLExpression::Or(
                Box::new(ELTLExpression::Globally(Box::new(
                    ELTLExpression::VariableExpr(
                        Box::new(IntegerExpression::Atom(Variable::new("v"))),
                        ComparisonOp::Eq,
                        Box::new(IntegerExpression::Const(1)),
                    ),
                ))),
                Box::new(ELTLExpression::LocationExpr(
                    Box::new(IntegerExpression::Atom(Location::new("l2"))),
                    ComparisonOp::Gt,
                    Box::new(IntegerExpression::Const(0)),
                )),
            )),
        )));

        let got = ErrorSpec::from_named_eltl("test", eltl).unwrap().ef;

        let l0_gt_1 = UpwardsClosedSet::from_integer_expr(
            IntegerExpression::Atom(Location::new("l0")),
            ComparisonOp::Gt,
            IntegerExpression::Const(1),
        )
        .unwrap();
        let l1_eq_0 = UpwardsClosedSet::from_integer_expr(
            IntegerExpression::Atom(Location::new("l1")),
            ComparisonOp::Eq,
            IntegerExpression::Const(0),
        )
        .unwrap();
        let v_eq_1 = UpwardsClosedSet::new_var_constraint(
            LIAVariableConstraint::from_integer_expr(
                IntegerExpression::Atom(Variable::new("v")),
                ComparisonOp::Eq,
                IntegerExpression::Const(1),
            )
            .unwrap(),
        );
        let l2_gt_0 = UpwardsClosedSet::from_integer_expr(
            IntegerExpression::Atom(Location::new("l2")),
            ComparisonOp::Gt,
            IntegerExpression::Const(0),
        )
        .unwrap();
        let expected = ErrorFormula::from([
            // [](l0 > 1) && [](v = 1)
            ErrorAtom::new(
                InitRestriction::new_top(),
                ErrorTarget::new_ensure(
                    UpwardsClosedSet::new_top(),
                    l0_gt_1.clone() & v_eq_1.clone(),
                ),
            ),
            // [](l0 > 1) && l2 > 0
            ErrorAtom::new(
                InitRestriction::new_top(),
                ErrorTarget::new_ensure(l2_gt_0.clone(), l0_gt_1),
            ),
            // l1 = 0 && [](v = 1)
            ErrorAtom::new(
                InitRestriction::new_top(),
                ErrorTarget::new_ensure(l1_eq_0.clone(), v_eq_1),
            ),
            // l1 = 0 && l2 > 0
            ErrorAtom::new(
                InitRestriction::new_top(),
                ErrorTarget::Reach(l1_eq_0 & l2_gt_0),
            ),
        ]);
        assert_eq!(got, expected);
    }

    #[test]
    fn repeat_nested_eventually_in_or() {
        // <>(l0 > 1 || <>(l1 = 0 && [](v = 1))) is equal to
        // <>(l0 > 1) || <>(l1 = 0 && [](v = 1))
        let eltl = !ELTLExpression::Eventually(Box::new(ELTLExpression::Or(
            Box::new(ELTLExpression::LocationExpr(
                Box::new(IntegerExpression::Atom(Location::new("l0"))),
                ComparisonOp::Gt,
                Box::new(IntegerExpression::Const(1)),
            )),
            Box::new(ELTLExpression::Eventually(Box::new(ELTLExpression::And(
                Box::new(ELTLExpression::LocationExpr(
                    Box::new(IntegerExpression::Atom(Location::new("l1"))),
                    ComparisonOp::Eq,
                    Box::new(IntegerExpression::Const(0)),
                )),
                Box::new(ELTLExpression::Globally(Box::new(
                    ELTLExpression::VariableExpr(
                        Box::new(IntegerExpression::Atom(Variable::new("v"))),
                        ComparisonOp::Eq,
                        Box::new(IntegerExpression::Const(1)),
                    ),
                ))),
            )))),
        )));

        let got = ErrorSpec::from_named_eltl("test", eltl).unwrap().ef;

        let l0_gt_1 = UpwardsClosedSet::from_integer_expr(
            IntegerExpression::Atom(Location::new("l0")),
            ComparisonOp::Gt,
            IntegerExpression::Const(1),
        )
        .unwrap();
        let l1_eq_0 = UpwardsClosedSet::from_integer_expr(
            IntegerExpression::Atom(Location::new("l1")),
            ComparisonOp::Eq,
            IntegerExpression::Const(0),
        )
        .unwrap();
        let v_eq_1 = UpwardsClosedSet::new_var_constraint(
            LIAVariableConstraint::from_integer_expr(
                IntegerExpression::Atom(Variable::new("v")),
                ComparisonOp::Eq,
                IntegerExpression::Const(1),
            )
            .unwrap(),
        );
        let expected = ErrorFormula::from([
            ErrorAtom::new(InitRestriction::new_top(), ErrorTarget::Reach(l0_gt_1)),
            ErrorAtom::new(
                InitRestriction::new_top(),
                ErrorTarget::new_ensure(l1_eq_0, v_eq_1),
            ),
        ]);
        assert_eq!(got, expected);
    }

    #[test]
    fn repeat_nested_eventually_in_and() {
        // <>(l0 > 1 && <>([](l1 = 0))) is not a repeat target
        let eltl = !ELTLExpression::Eventually(Box::new(ELTLExpression::And(
            Box::new(ELTLExpression::LocationExpr(
                Box::new(IntegerExpression::Atom(Location::new("l0"))),
                ComparisonOp::Gt,
                Box::new(IntegerExpression::Const(1)),
            )),
            Box::new(ELTLExpression::Eventually(Box::new(
                ELTLExpression::Globally(Box::new(ELTLExpression::LocationExpr(
                    Box::new(IntegerExpression::Atom(Location::new("l1"))),
                    ComparisonOp::Eq,
                    Box::new(IntegerExpression::Const(0)),
                ))),
            ))),
        )));

        let got = ErrorSpec::from_named_eltl("test", eltl);

        assert_eq!(got, Err(ExtractionError::NestedTemporalOperator));
    }

    #[test]
    fn repeat_or_below_globally() {
        // <>(l0 > 1 && [](l1 = 0 || [](v = 1))) has no single invariant
        let eltl = !ELTLExpression::Eventually(Box::new(ELTLExpression::And(
            Box::new(ELTLExpression::LocationExpr(
                Box::new(IntegerExpression::Atom(Location::new("l0"))),
                ComparisonOp::Gt,
                Box::new(IntegerExpression::Const(1)),
            )),
            Box::new(ELTLExpression::Globally(Box::new(ELTLExpression::Or(
                Box::new(ELTLExpression::LocationExpr(
                    Box::new(IntegerExpression::Atom(Location::new("l1"))),
                    ComparisonOp::Eq,
                    Box::new(IntegerExpression::Const(0)),
                )),
                Box::new(ELTLExpression::Globally(Box::new(
                    ELTLExpression::VariableExpr(
                        Box::new(IntegerExpression::Atom(Variable::new("v"))),
                        ComparisonOp::Eq,
                        Box::new(IntegerExpression::Const(1)),
                    ),
                ))),
            )))),
        )));

        let got = ErrorSpec::from_named_eltl("test", eltl);

        assert_eq!(got, Err(ExtractionError::NestedTemporalOperator));
    }

    #[test]
    fn repeat_globally_eventually() {
        // <>([](<>(l0 > 1))) is not supported
        let eltl = !ELTLExpression::Eventually(Box::new(ELTLExpression::Globally(Box::new(
            ELTLExpression::Eventually(Box::new(ELTLExpression::LocationExpr(
                Box::new(IntegerExpression::Atom(Location::new("l0"))),
                ComparisonOp::Gt,
                Box::new(IntegerExpression::Const(1)),
            ))),
        ))));

        let got = ErrorSpec::from_named_eltl("test", eltl);

        assert_eq!(got, Err(ExtractionError::NestedTemporalOperator));
    }

    #[test]
    fn repeat_and_repeat_unsupported() {
        // <>(l0 > 1 && [](l1 = 0)) && <>(v = 1 && [](l2 > 0)) has no single
        // target
        let eltl = !ELTLExpression::And(
            Box::new(ELTLExpression::Eventually(Box::new(ELTLExpression::And(
                Box::new(ELTLExpression::LocationExpr(
                    Box::new(IntegerExpression::Atom(Location::new("l0"))),
                    ComparisonOp::Gt,
                    Box::new(IntegerExpression::Const(1)),
                )),
                Box::new(ELTLExpression::Globally(Box::new(
                    ELTLExpression::LocationExpr(
                        Box::new(IntegerExpression::Atom(Location::new("l1"))),
                        ComparisonOp::Eq,
                        Box::new(IntegerExpression::Const(0)),
                    ),
                ))),
            )))),
            Box::new(ELTLExpression::Eventually(Box::new(ELTLExpression::And(
                Box::new(ELTLExpression::VariableExpr(
                    Box::new(IntegerExpression::Atom(Variable::new("v"))),
                    ComparisonOp::Eq,
                    Box::new(IntegerExpression::Const(1)),
                )),
                Box::new(ELTLExpression::Globally(Box::new(
                    ELTLExpression::LocationExpr(
                        Box::new(IntegerExpression::Atom(Location::new("l2"))),
                        ComparisonOp::Gt,
                        Box::new(IntegerExpression::Const(0)),
                    ),
                ))),
            )))),
        );

        let got = ErrorSpec::from_named_eltl("test", eltl);

        let l0_gt_1 = UpwardsClosedSet::from_integer_expr(
            IntegerExpression::Atom(Location::new("l0")),
            ComparisonOp::Gt,
            IntegerExpression::Const(1),
        )
        .unwrap();
        let l1_eq_0 = UpwardsClosedSet::from_integer_expr(
            IntegerExpression::Atom(Location::new("l1")),
            ComparisonOp::Eq,
            IntegerExpression::Const(0),
        )
        .unwrap();
        let v_eq_1 = UpwardsClosedSet::new_var_constraint(
            LIAVariableConstraint::from_integer_expr(
                IntegerExpression::Atom(Variable::new("v")),
                ComparisonOp::Eq,
                IntegerExpression::Const(1),
            )
            .unwrap(),
        );
        let l2_gt_0 = UpwardsClosedSet::from_integer_expr(
            IntegerExpression::Atom(Location::new("l2")),
            ComparisonOp::Gt,
            IntegerExpression::Const(0),
        )
        .unwrap();
        let expected = ExtractionError::UnsupportedConjunction(
            ErrorTarget::new_ensure(l0_gt_1, l1_eq_0),
            ErrorTarget::new_ensure(v_eq_1, l2_gt_0),
        );
        assert_eq!(got, Err(expected));
    }

    #[test]
    fn repeat_and_ensure_unsupported() {
        // [](l0 > 1) && <>(l1 = 0 && [](v = 1)) has no single target
        let eltl = !ELTLExpression::And(
            Box::new(ELTLExpression::Globally(Box::new(
                ELTLExpression::LocationExpr(
                    Box::new(IntegerExpression::Atom(Location::new("l0"))),
                    ComparisonOp::Gt,
                    Box::new(IntegerExpression::Const(1)),
                ),
            ))),
            Box::new(ELTLExpression::Eventually(Box::new(ELTLExpression::And(
                Box::new(ELTLExpression::LocationExpr(
                    Box::new(IntegerExpression::Atom(Location::new("l1"))),
                    ComparisonOp::Eq,
                    Box::new(IntegerExpression::Const(0)),
                )),
                Box::new(ELTLExpression::Globally(Box::new(
                    ELTLExpression::VariableExpr(
                        Box::new(IntegerExpression::Atom(Variable::new("v"))),
                        ComparisonOp::Eq,
                        Box::new(IntegerExpression::Const(1)),
                    ),
                ))),
            )))),
        );

        let got = ErrorSpec::from_named_eltl("test", eltl);

        let l0_gt_1 = UpwardsClosedSet::from_integer_expr(
            IntegerExpression::Atom(Location::new("l0")),
            ComparisonOp::Gt,
            IntegerExpression::Const(1),
        )
        .unwrap();
        let l1_eq_0 = UpwardsClosedSet::from_integer_expr(
            IntegerExpression::Atom(Location::new("l1")),
            ComparisonOp::Eq,
            IntegerExpression::Const(0),
        )
        .unwrap();
        let v_eq_1 = UpwardsClosedSet::new_var_constraint(
            LIAVariableConstraint::from_integer_expr(
                IntegerExpression::Atom(Variable::new("v")),
                ComparisonOp::Eq,
                IntegerExpression::Const(1),
            )
            .unwrap(),
        );
        let expected = ExtractionError::UnsupportedConjunction(
            ErrorTarget::Invariant(l0_gt_1),
            ErrorTarget::new_ensure(l1_eq_0, v_eq_1),
        );
        assert_eq!(got, Err(expected));
    }

    #[test]
    fn repeat_or_ensure() {
        // [](l0 > 1) || <>(l1 = 0 && [](v = 1)) stays two atoms
        let eltl = !ELTLExpression::Or(
            Box::new(ELTLExpression::Globally(Box::new(
                ELTLExpression::LocationExpr(
                    Box::new(IntegerExpression::Atom(Location::new("l0"))),
                    ComparisonOp::Gt,
                    Box::new(IntegerExpression::Const(1)),
                ),
            ))),
            Box::new(ELTLExpression::Eventually(Box::new(ELTLExpression::And(
                Box::new(ELTLExpression::LocationExpr(
                    Box::new(IntegerExpression::Atom(Location::new("l1"))),
                    ComparisonOp::Eq,
                    Box::new(IntegerExpression::Const(0)),
                )),
                Box::new(ELTLExpression::Globally(Box::new(
                    ELTLExpression::VariableExpr(
                        Box::new(IntegerExpression::Atom(Variable::new("v"))),
                        ComparisonOp::Eq,
                        Box::new(IntegerExpression::Const(1)),
                    ),
                ))),
            )))),
        );

        let got = ErrorSpec::from_named_eltl("test", eltl).unwrap().ef;

        let l0_gt_1 = UpwardsClosedSet::from_integer_expr(
            IntegerExpression::Atom(Location::new("l0")),
            ComparisonOp::Gt,
            IntegerExpression::Const(1),
        )
        .unwrap();
        let l1_eq_0 = UpwardsClosedSet::from_integer_expr(
            IntegerExpression::Atom(Location::new("l1")),
            ComparisonOp::Eq,
            IntegerExpression::Const(0),
        )
        .unwrap();
        let v_eq_1 = UpwardsClosedSet::new_var_constraint(
            LIAVariableConstraint::from_integer_expr(
                IntegerExpression::Atom(Variable::new("v")),
                ComparisonOp::Eq,
                IntegerExpression::Const(1),
            )
            .unwrap(),
        );
        let expected = ErrorFormula::from([
            ErrorAtom::new(InitRestriction::new_top(), ErrorTarget::Invariant(l0_gt_1)),
            ErrorAtom::new(
                InitRestriction::new_top(),
                ErrorTarget::new_ensure(l1_eq_0, v_eq_1),
            ),
        ]);
        assert_eq!(got, expected);
    }

    #[test]
    fn globally_eventually_simple() {
        // [](l0 > 1 && <>(l1 = 0))
        let eltl = !ELTLExpression::Globally(Box::new(ELTLExpression::And(
            Box::new(ELTLExpression::LocationExpr(
                Box::new(IntegerExpression::Atom(Location::new("l0"))),
                ComparisonOp::Gt,
                Box::new(IntegerExpression::Const(1)),
            )),
            Box::new(ELTLExpression::Eventually(Box::new(
                ELTLExpression::LocationExpr(
                    Box::new(IntegerExpression::Atom(Location::new("l1"))),
                    ComparisonOp::Eq,
                    Box::new(IntegerExpression::Const(0)),
                ),
            ))),
        )));

        let got = ErrorSpec::from_named_eltl("test", eltl).unwrap().ef;

        let l0_gt_1 = UpwardsClosedSet::from_integer_expr(
            IntegerExpression::Atom(Location::new("l0")),
            ComparisonOp::Gt,
            IntegerExpression::Const(1),
        )
        .unwrap();
        let l1_eq_0 = UpwardsClosedSet::from_integer_expr(
            IntegerExpression::Atom(Location::new("l1")),
            ComparisonOp::Eq,
            IntegerExpression::Const(0),
        )
        .unwrap();
        let expected = ErrorFormula::new(
            InitRestriction::new_top(),
            ErrorTarget::Repeat {
                pre: l0_gt_1,
                inv: l1_eq_0,
            },
        );
        assert_eq!(got, expected);
    }

    #[test]
    fn globally_eventually_only() {
        // [](<>(l1 = 0)) has the invariant `true`
        let eltl = !ELTLExpression::Globally(Box::new(ELTLExpression::Eventually(Box::new(
            ELTLExpression::LocationExpr(
                Box::new(IntegerExpression::Atom(Location::new("l1"))),
                ComparisonOp::Eq,
                Box::new(IntegerExpression::Const(0)),
            ),
        ))));

        let got = ErrorSpec::from_named_eltl("test", eltl).unwrap().ef;

        let l1_eq_0 = UpwardsClosedSet::from_integer_expr(
            IntegerExpression::Atom(Location::new("l1")),
            ComparisonOp::Eq,
            IntegerExpression::Const(0),
        )
        .unwrap();
        let expected = ErrorFormula::new(
            InitRestriction::new_top(),
            ErrorTarget::Repeat {
                pre: UpwardsClosedSet::new_top(),
                inv: l1_eq_0,
            },
        );
        assert_eq!(got, expected);
    }

    #[test]
    fn globally_eventually_or_of_eventually() {
        // [](<>(l0 > 1) || <>(l1 = 0)) is equal to [](<>(l0 > 1 || l1 = 0))
        let eltl = !ELTLExpression::Globally(Box::new(ELTLExpression::Or(
            Box::new(ELTLExpression::Eventually(Box::new(
                ELTLExpression::LocationExpr(
                    Box::new(IntegerExpression::Atom(Location::new("l0"))),
                    ComparisonOp::Gt,
                    Box::new(IntegerExpression::Const(1)),
                ),
            ))),
            Box::new(ELTLExpression::Eventually(Box::new(
                ELTLExpression::LocationExpr(
                    Box::new(IntegerExpression::Atom(Location::new("l1"))),
                    ComparisonOp::Eq,
                    Box::new(IntegerExpression::Const(0)),
                ),
            ))),
        )));

        let got = ErrorSpec::from_named_eltl("test", eltl).unwrap().ef;

        let l0_gt_1 = UpwardsClosedSet::from_integer_expr(
            IntegerExpression::Atom(Location::new("l0")),
            ComparisonOp::Gt,
            IntegerExpression::Const(1),
        )
        .unwrap();
        let l1_eq_0 = UpwardsClosedSet::from_integer_expr(
            IntegerExpression::Atom(Location::new("l1")),
            ComparisonOp::Eq,
            IntegerExpression::Const(0),
        )
        .unwrap();
        let expected = ErrorFormula::new(
            InitRestriction::new_top(),
            ErrorTarget::Repeat {
                pre: UpwardsClosedSet::new_top(),
                inv: l0_gt_1 | l1_eq_0,
            },
        );
        assert_eq!(got, expected);
    }

    #[test]
    fn globally_eventually_nested_eventually() {
        // [](l0 > 1 && <>(<>(l1 = 0))) is equal to [](l0 > 1 && <>(l1 = 0))
        let eltl = !ELTLExpression::Globally(Box::new(ELTLExpression::And(
            Box::new(ELTLExpression::LocationExpr(
                Box::new(IntegerExpression::Atom(Location::new("l0"))),
                ComparisonOp::Gt,
                Box::new(IntegerExpression::Const(1)),
            )),
            Box::new(ELTLExpression::Eventually(Box::new(
                ELTLExpression::Eventually(Box::new(ELTLExpression::LocationExpr(
                    Box::new(IntegerExpression::Atom(Location::new("l1"))),
                    ComparisonOp::Eq,
                    Box::new(IntegerExpression::Const(0)),
                ))),
            ))),
        )));

        let got = ErrorSpec::from_named_eltl("test", eltl).unwrap().ef;

        let l0_gt_1 = UpwardsClosedSet::from_integer_expr(
            IntegerExpression::Atom(Location::new("l0")),
            ComparisonOp::Gt,
            IntegerExpression::Const(1),
        )
        .unwrap();
        let l1_eq_0 = UpwardsClosedSet::from_integer_expr(
            IntegerExpression::Atom(Location::new("l1")),
            ComparisonOp::Eq,
            IntegerExpression::Const(0),
        )
        .unwrap();
        let expected = ErrorFormula::new(
            InitRestriction::new_top(),
            ErrorTarget::Repeat {
                pre: l0_gt_1,
                inv: l1_eq_0,
            },
        );
        assert_eq!(got, expected);
    }

    #[test]
    fn globally_eventually_and_of_globally_top_level() {
        // [](l0 > 1) && [](<>(l1 = 0)) is equal to [](l0 > 1 && <>(l1 = 0))
        let eltl = !ELTLExpression::And(
            Box::new(ELTLExpression::Globally(Box::new(
                ELTLExpression::LocationExpr(
                    Box::new(IntegerExpression::Atom(Location::new("l0"))),
                    ComparisonOp::Gt,
                    Box::new(IntegerExpression::Const(1)),
                ),
            ))),
            Box::new(ELTLExpression::Globally(Box::new(
                ELTLExpression::Eventually(Box::new(ELTLExpression::LocationExpr(
                    Box::new(IntegerExpression::Atom(Location::new("l1"))),
                    ComparisonOp::Eq,
                    Box::new(IntegerExpression::Const(0)),
                ))),
            ))),
        );

        let got = ErrorSpec::from_named_eltl("test", eltl).unwrap().ef;

        let l0_gt_1 = UpwardsClosedSet::from_integer_expr(
            IntegerExpression::Atom(Location::new("l0")),
            ComparisonOp::Gt,
            IntegerExpression::Const(1),
        )
        .unwrap();
        let l1_eq_0 = UpwardsClosedSet::from_integer_expr(
            IntegerExpression::Atom(Location::new("l1")),
            ComparisonOp::Eq,
            IntegerExpression::Const(0),
        )
        .unwrap();
        let expected = ErrorFormula::new(
            InitRestriction::new_top(),
            ErrorTarget::Repeat {
                pre: l0_gt_1,
                inv: l1_eq_0,
            },
        );
        assert_eq!(got, expected);
    }

    #[test]
    fn globally_eventually_or_of_same_invariant() {
        // []((v = 1 && <>(l0 > 1)) || (v = 1 && <>(l1 = 0))) is equal to
        // [](v = 1 && <>(l0 > 1 || l1 = 0))
        let eltl = !ELTLExpression::Globally(Box::new(ELTLExpression::Or(
            Box::new(ELTLExpression::And(
                Box::new(ELTLExpression::VariableExpr(
                    Box::new(IntegerExpression::Atom(Variable::new("v"))),
                    ComparisonOp::Eq,
                    Box::new(IntegerExpression::Const(1)),
                )),
                Box::new(ELTLExpression::Eventually(Box::new(
                    ELTLExpression::LocationExpr(
                        Box::new(IntegerExpression::Atom(Location::new("l0"))),
                        ComparisonOp::Gt,
                        Box::new(IntegerExpression::Const(1)),
                    ),
                ))),
            )),
            Box::new(ELTLExpression::And(
                Box::new(ELTLExpression::VariableExpr(
                    Box::new(IntegerExpression::Atom(Variable::new("v"))),
                    ComparisonOp::Eq,
                    Box::new(IntegerExpression::Const(1)),
                )),
                Box::new(ELTLExpression::Eventually(Box::new(
                    ELTLExpression::LocationExpr(
                        Box::new(IntegerExpression::Atom(Location::new("l1"))),
                        ComparisonOp::Eq,
                        Box::new(IntegerExpression::Const(0)),
                    ),
                ))),
            )),
        )));

        let got = ErrorSpec::from_named_eltl("test", eltl).unwrap().ef;

        let v_eq_1 = UpwardsClosedSet::new_var_constraint(
            LIAVariableConstraint::from_integer_expr(
                IntegerExpression::Atom(Variable::new("v")),
                ComparisonOp::Eq,
                IntegerExpression::Const(1),
            )
            .unwrap(),
        );
        let l0_gt_1 = UpwardsClosedSet::from_integer_expr(
            IntegerExpression::Atom(Location::new("l0")),
            ComparisonOp::Gt,
            IntegerExpression::Const(1),
        )
        .unwrap();
        let l1_eq_0 = UpwardsClosedSet::from_integer_expr(
            IntegerExpression::Atom(Location::new("l1")),
            ComparisonOp::Eq,
            IntegerExpression::Const(0),
        )
        .unwrap();
        let expected = ErrorFormula::new(
            InitRestriction::new_top(),
            ErrorTarget::Repeat {
                pre: v_eq_1,
                inv: l0_gt_1 | l1_eq_0,
            },
        );
        assert_eq!(got, expected);
    }

    #[test]
    fn globally_eventually_two_eventually_unsupported() {
        // [](<>(l0 > 1) && <>(l1 = 0)) has no single target
        let eltl = !ELTLExpression::Globally(Box::new(ELTLExpression::And(
            Box::new(ELTLExpression::Eventually(Box::new(
                ELTLExpression::LocationExpr(
                    Box::new(IntegerExpression::Atom(Location::new("l0"))),
                    ComparisonOp::Gt,
                    Box::new(IntegerExpression::Const(1)),
                ),
            ))),
            Box::new(ELTLExpression::Eventually(Box::new(
                ELTLExpression::LocationExpr(
                    Box::new(IntegerExpression::Atom(Location::new("l1"))),
                    ComparisonOp::Eq,
                    Box::new(IntegerExpression::Const(0)),
                ),
            ))),
        )));

        let got = ErrorSpec::from_named_eltl("test", eltl);

        let l0_gt_1 = UpwardsClosedSet::from_integer_expr(
            IntegerExpression::Atom(Location::new("l0")),
            ComparisonOp::Gt,
            IntegerExpression::Const(1),
        )
        .unwrap();
        let l1_eq_0 = UpwardsClosedSet::from_integer_expr(
            IntegerExpression::Atom(Location::new("l1")),
            ComparisonOp::Eq,
            IntegerExpression::Const(0),
        )
        .unwrap();
        let expected = ExtractionError::UnsupportedConjunction(
            ErrorTarget::Repeat {
                pre: UpwardsClosedSet::new_top(),
                inv: l0_gt_1,
            },
            ErrorTarget::Repeat {
                pre: UpwardsClosedSet::new_top(),
                inv: l1_eq_0,
            },
        );
        assert_eq!(got, Err(expected));
    }

    #[test]
    fn globally_eventually_atom_or_eventually() {
        // [](l0 > 1 || <>(l1 = 0)) has no single target
        let eltl = !ELTLExpression::Globally(Box::new(ELTLExpression::Or(
            Box::new(ELTLExpression::LocationExpr(
                Box::new(IntegerExpression::Atom(Location::new("l0"))),
                ComparisonOp::Gt,
                Box::new(IntegerExpression::Const(1)),
            )),
            Box::new(ELTLExpression::Eventually(Box::new(
                ELTLExpression::LocationExpr(
                    Box::new(IntegerExpression::Atom(Location::new("l1"))),
                    ComparisonOp::Eq,
                    Box::new(IntegerExpression::Const(0)),
                ),
            ))),
        )));

        let got = ErrorSpec::from_named_eltl("test", eltl);

        assert_eq!(got, Err(ExtractionError::NestedTemporalOperator));
    }

    #[test]
    fn globally_eventually_globally_below_eventually() {
        // [](<>(l0 > 1 && [](l1 = 0))) has no single target
        let eltl = !ELTLExpression::Globally(Box::new(ELTLExpression::Eventually(Box::new(
            ELTLExpression::And(
                Box::new(ELTLExpression::LocationExpr(
                    Box::new(IntegerExpression::Atom(Location::new("l0"))),
                    ComparisonOp::Gt,
                    Box::new(IntegerExpression::Const(1)),
                )),
                Box::new(ELTLExpression::Globally(Box::new(
                    ELTLExpression::LocationExpr(
                        Box::new(IntegerExpression::Atom(Location::new("l1"))),
                        ComparisonOp::Eq,
                        Box::new(IntegerExpression::Const(0)),
                    ),
                ))),
            ),
        ))));

        let got = ErrorSpec::from_named_eltl("test", eltl);

        assert_eq!(got, Err(ExtractionError::NestedTemporalOperator));
    }

    #[test]
    fn globally_eventually_below_eventually_unsupported() {
        // <>(l0 > 1 && [](<>(l1 = 0))) has no single target
        let eltl = !ELTLExpression::Eventually(Box::new(ELTLExpression::And(
            Box::new(ELTLExpression::LocationExpr(
                Box::new(IntegerExpression::Atom(Location::new("l0"))),
                ComparisonOp::Gt,
                Box::new(IntegerExpression::Const(1)),
            )),
            Box::new(ELTLExpression::Globally(Box::new(
                ELTLExpression::Eventually(Box::new(ELTLExpression::LocationExpr(
                    Box::new(IntegerExpression::Atom(Location::new("l1"))),
                    ComparisonOp::Eq,
                    Box::new(IntegerExpression::Const(0)),
                ))),
            ))),
        )));

        let got = ErrorSpec::from_named_eltl("test", eltl);

        assert_eq!(got, Err(ExtractionError::NestedTemporalOperator));
    }
}
