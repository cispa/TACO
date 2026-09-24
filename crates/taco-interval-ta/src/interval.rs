//! Interval module defining intervals and interval order functionality
//!
//! This module defines the `Interval` struct representing an interval and the
//! `IntervalOrder` trait for accessing an interval order.

use std::fmt::Debug;
use std::fmt::{self};

use taco_smt_encoder::SMTSolverContext;
use taco_smt_encoder::expression_encoding::StaticSMTContext;
use taco_threshold_automaton::expressions::{
    Atomic, BooleanConnective, BooleanExpression, ComparisonOp, Parameter, fraction::Fraction,
};
use taco_threshold_automaton::lia_threshold_automaton::integer_thresholds::{
    IntoNoDivBooleanExpr, Threshold, ThresholdConstraint, WeightedSum,
};

use super::HasAssociatedIntervals;

/// Trait for types that define an order among intervals
///
/// This trait is implemented by types that define an order among intervals.
/// This trait provides functions to access the order, e.g., to check if one
/// interval is before another in the order, get the next interval, etc.
pub trait IntervalOrderFor<T>: IntervalOrder
where
    T: HasAssociatedIntervals,
{
    /// Check if in the interval order for `t` the intervals are
    /// ordered `i1 < i2`
    ///
    /// Return `true` if `i1` is before `i2` in the order, `false` otherwise.
    ///
    /// The function returns an error if the `t` is not found, or any of the
    /// intervals `i1`, `i2` do not appear in the interval order for `t`
    fn lt(&self, t: &T, i1: &Interval, i2: &Interval) -> Result<bool, IntervalOrderError<T>>;

    /// Check if in the interval order for `t` it holds that `i1 > i2`
    ///
    /// Return `true` if `i1` appears after `i2` in the order, `false`
    /// otherwise.
    ///
    /// The function returns an error if the `t` is not found, or any of the
    /// intervals `i1`, `i2` do not appear in the interval order for `t`.
    fn gt(&self, t: &T, i1: &Interval, i2: &Interval) -> Result<bool, IntervalOrderError<T>>;

    /// Get the zero interval of `t`
    fn get_zero_interval(&self, t: &T) -> Result<&Interval, IntervalOrderError<T>>;

    /// Get the next interval appearing after `i`  in the order for `t`
    ///
    /// Return `None` if `i` is the last interval, or `i` is not in the order
    /// for `var`
    fn get_next_interval<'a>(
        &'a self,
        t: &T,
        i: &Interval,
    ) -> Result<Option<&'a Interval>, IntervalOrderError<T>>;

    /// Get the previous interval of `i` for variable `var`
    ///
    /// Return `None` if `i` is the first interval, or `i` is not in the order
    /// for `var`
    fn get_previous_interval<'a>(
        &'a self,
        var: &T,
        i: &Interval,
    ) -> Result<Option<&'a Interval>, IntervalOrderError<T>>;

    /// Get all intervals associated with `t`
    ///
    /// Return an error if the variable `t` is not found in the interval order,
    /// otherwise returns the intervals associated with `t`
    fn get_all_intervals_of_t(&self, t: &T) -> Result<&Vec<Interval>, IntervalOrderError<T>>;

    /// Get the number of intervals associated with `t`
    fn get_number_of_intervals(&self, t: &T) -> Result<usize, IntervalOrderError<T>>;

    /// Get the intervals of `t` where `thr` is enabled
    fn compute_enabled_intervals_of_threshold(
        &self,
        t: &T,
        thr: &ThresholdConstraint,
    ) -> Result<Vec<Interval>, IntervalOrderError<T>>;

    /// Check whether the interval order replaces the interval boundary
    ///
    /// This method checks if the interval boundary `ib` is replaced by the
    /// interval order. If the interval boundary is replaced, the method returns
    /// the new interval boundary that replaces `ib`. If the interval boundary
    /// is not replaced, the method returns the original interval boundary.
    ///
    /// An interval might have been replaced if the interval boundary is
    /// considered equal to another boundary in the order.
    fn check_interval_replaced(&self, ib: IntervalBoundary) -> IntervalBoundary;
}

/// Common trait of interval orders
pub trait IntervalOrder {
    /// Convert the order to a boolean expression
    ///
    /// This method converts the interval order to a boolean expression. This
    /// constraint can for example be appended to the resilience condition of a
    /// threshold automaton to ensure that the assumed order is satisfied.
    fn order_to_boolean_expr<T: Atomic>(&self) -> Vec<BooleanExpression<T>>;
}

/// Error that can occur when accessing interval order
#[derive(Debug, Clone, PartialEq)]
pub enum IntervalOrderError<T>
where
    T: HasAssociatedIntervals,
{
    /// Interval was not found in the interval order for variable
    IntervalNotFound {
        /// Variable for which the lookup failed
        var: T,
        /// Interval for which the lookup failed
        interval: Interval,
    },
    /// Variable was not found in the interval order
    VariableNotFound {
        /// Variable for which the lookup failed
        var: T,
    },

    /// Error while extracting intervals from threshold, the associated interval has not been found in the order
    ThresholdExtractionError {
        /// Variable for which the lookup failed
        var: T,
        /// Threshold for which the lookup failed
        thr: ThresholdConstraint,
    },
}

impl<T: HasAssociatedIntervals> std::error::Error for IntervalOrderError<T> {}

impl<T: HasAssociatedIntervals> fmt::Display for IntervalOrderError<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "Error when accessing interval order: ")?;

        match self {
            IntervalOrderError::IntervalNotFound { var, interval } => write!(
                f,
                "The interval {interval} has not been found in the interval order for {var}"
            ),
            IntervalOrderError::VariableNotFound { var } => write!(
                f,
                "The variable {var} has not been found in the interval order"
            ),
            IntervalOrderError::ThresholdExtractionError { var, thr } => write!(
                f,
                "Extraction of threshold from order failed: For variable {var} and threshold {thr} no interval matches the threshold"
            ),
        }
    }
}

/// Interval
#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct Interval {
    /// Lower / left boundary of the interval
    lb: IntervalBoundary,
    /// Lower / left boundary of the interval is open / closed
    lb_open: bool,
    /// Upper / right boundary of the interval
    ub: IntervalBoundary,
    /// Upper / right boundary of the interval is open / closed
    ub_open: bool,
}

impl Interval {
    /// Create a new interval
    pub fn new(
        lb: IntervalBoundary,
        mut lb_open: bool,
        ub: IntervalBoundary,
        mut ub_open: bool,
    ) -> Self {
        if lb == IntervalBoundary::Infty {
            lb_open = true;
        }

        if ub == IntervalBoundary::Infty {
            ub_open = true;
        }

        Self {
            lb,
            lb_open,
            ub,
            ub_open,
        }
    }

    /// Check if the interval is left open, i.e., the lower boundary is not included
    pub fn is_left_open(&self) -> bool {
        self.lb_open
    }

    /// Check if the interval is right open, i.e., the upper boundary is not included
    pub fn is_right_open(&self) -> bool {
        self.ub_open
    }

    /// Returns the left IntervalBoundary
    pub fn lb(&self) -> &IntervalBoundary {
        &self.lb
    }

    /// Returns the right IntervalBoundary
    pub fn ub(&self) -> &IntervalBoundary {
        &self.ub
    }

    /// Return the interval `[0, 1[`
    pub fn zero() -> Self {
        Self::new_constant(0, 1)
    }

    /// Create a new interval of the form `[ c_lower_bound, c_upper_bound [` where `c_lower_bound` and `c_upper_bound`
    /// are constants
    pub fn new_constant<T: Into<Fraction>, U: Into<Fraction>>(
        c_lower_bound: T,
        c_upper_bound: U,
    ) -> Self {
        Self {
            lb: IntervalBoundary::from_const(c_lower_bound),
            lb_open: false,
            ub: IntervalBoundary::from_const(c_upper_bound),
            ub_open: true,
        }
    }

    /// Check if the given interval boundary is contained in the interval
    ///
    /// This method *does not* do any mathematical / symbolical
    /// checks to determine if the interval boundary is contained in the
    /// interval. It only checks if the one of the boundaries of the interval is
    /// equal to the given interval boundary and that this boundary is not open.
    pub fn check_is_contained(&self, ib: &IntervalBoundary) -> bool {
        (self.lb == *ib && !self.lb_open) || (self.ub == *ib && !self.ub_open)
    }

    /// Check whether the interval is inhabited for the current order
    ///
    /// This function will check that there is at least one integer solution
    /// lies within the interval borders. This function will only work for
    /// integers
    pub(crate) fn is_inhabited(&self, ctx: &mut StaticSMTContext) -> bool {
        // This function depends on the fact that if lb != ub, then lb < ib in
        // the interval ordering.
        // Specifically, this means that there exists an r > 0 such that
        // lb + r = ub (by definition of < on for *integers*)
        //
        // Assuming both interval borders are open, we can check this by
        // checking whether ub - lb > 1 is satisfiable (since if this not
        // possible) there is no solution
        if let (IntervalBoundary::Bound(lb), IntervalBoundary::Bound(ub)) =
            (self.lb.clone(), self.ub.clone())
        {
            ctx.get_smt_solver_mut()
                .push()
                .expect("Failed to check inhabitance of interval");
            let comp_thr = ub - lb;
            let one = Threshold::from_const(1);

            let inh_query: BooleanExpression<Parameter> =
                comp_thr.encode_comparison_to_boolean_expression(ComparisonOp::Gt, &one);

            let inh_query = ctx
                .encode_to_smt(&inh_query)
                .expect("Failed to check inhabitance of interval");

            let inh = ctx
                .assert_and_check_expr(inh_query)
                .expect("Failed to check inhabitance of interval")
                .is_sat();

            ctx.get_smt_solver_mut()
                .pop()
                .expect("Failed to check inhabitance of interval");
            return inh;
        }

        // If the interval has a closed side, there will always be an integer
        // in it (assuming the bounds have an integer solution)
        true
    }

    /// Checks whether an addition of `c` to the interval must always leave the
    /// interval
    ///
    /// This function will first check whether both intervals are constants, if
    /// this is not the case, it returns false, as we cannot statically
    /// determine the size of the interval.
    /// If both are constant, it will check whether adding `c` to the lower
    /// bound will be sufficient to move past the upper bound.
    pub fn check_add_always_out_of_interval(&self, c: u32) -> bool {
        if let (Some(lc), Some(uc)) = (self.lb.try_is_constant(), self.ub.try_is_constant()) {
            let res = lc + c.into();
            if self.ub_open || self.lb_open {
                return res >= uc;
            }

            return res > uc;
        }
        false
    }

    /// Checks whether an subtraction of `c` from the interval must always leave
    /// the interval
    ///
    /// This function will first check whether both intervals are constants, if
    /// this is not the case, it returns false, as we cannot statically
    /// determine the size of the interval.
    /// If both are constant, it will check whether subtracting `c` from the
    /// upper bound will be sufficient to move below the lower bound.
    pub fn check_sub_always_out_of_interval(&self, c: u32) -> bool {
        if let (Some(lc), Some(uc)) = (self.lb.try_is_constant(), self.ub.try_is_constant()) {
            let res = uc - c.into();
            if self.ub_open || self.lb_open {
                return res <= lc;
            }

            return res < lc;
        }
        false
    }

    /// Encode the interval as a boolean expression on a variable
    ///
    /// This method encodes the interval as a boolean expression on a variable
    /// `var`. The boolean expression is true if the variable is in the interval
    /// and false otherwise.
    pub fn encode_into_boolean_expr<S, T>(&self, var: &S) -> BooleanExpression<T>
    where
        S: IntoNoDivBooleanExpr<T> + Clone,
        T: Atomic,
    {
        // encode the lower bound of the interval
        let lb = match &self.lb {
            IntervalBoundary::Bound(lb) => {
                let op = if self.lb_open {
                    ComparisonOp::Gt
                } else {
                    ComparisonOp::Geq
                };

                var.encode_comparison_to_boolean_expression(op, lb)
            }
            IntervalBoundary::Infty => return BooleanExpression::False,
        };

        // encode the upper bound of the interval
        let ub = match &self.ub {
            IntervalBoundary::Bound(ub) => {
                let op = if self.ub_open {
                    ComparisonOp::Lt
                } else {
                    ComparisonOp::Leq
                };

                var.encode_comparison_to_boolean_expression(op, ub)
            }
            IntervalBoundary::Infty => BooleanExpression::True,
        };

        BooleanExpression::BinaryExpression(Box::new(lb), BooleanConnective::And, Box::new(ub))
    }
}

/// Boundary of an interval
#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum IntervalBoundary {
    /// Infinite boundary
    Infty,
    /// Bound of an interval
    Bound(Threshold),
}

impl IntervalBoundary {
    /// Create a new interval boundary representing the unbounded interval
    /// border `∞`
    pub fn new_infty() -> IntervalBoundary {
        IntervalBoundary::Infty
    }

    /// Create a new interval boundary representing a bound
    /// `param * x + constant`
    pub fn new_bound<T: Into<WeightedSum<Parameter>>, U: Into<Fraction>>(
        param: T,
        constant: U,
    ) -> IntervalBoundary {
        IntervalBoundary::Bound(Threshold::new(param, constant))
    }

    /// Create a new interval boundary representing a constant
    pub fn from_const<T: Into<Fraction>>(constant: T) -> IntervalBoundary {
        IntervalBoundary::Bound(Threshold::from_const(constant))
    }

    /// If the interval boundary is a constant without parameters, this
    /// function returns the constant
    pub fn try_is_constant(&self) -> Option<Fraction> {
        match self {
            IntervalBoundary::Infty => None,
            IntervalBoundary::Bound(thr) => thr.get_const(),
        }
    }

    /// Get the integer expression of the interval boundary
    ///
    /// Returns `None` if the boundary is infinite, otherwise returns the
    /// threshold
    pub fn get_threshold(&self) -> Option<&Threshold> {
        match self {
            IntervalBoundary::Infty => None,
            IntervalBoundary::Bound(threshold) => Some(threshold),
        }
    }

    /// Extract the interval boundary from a threshold
    pub fn from_threshold_constraint(trc: &ThresholdConstraint) -> IntervalBoundary {
        let tr = trc.get_threshold().clone();

        IntervalBoundary::Bound(tr)
    }
}

impl fmt::Display for Interval {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.lb_open {
            write!(f, "]")?;
        } else {
            write!(f, "[")?;
        }

        write!(f, "{}, {}", self.lb, self.ub)?;

        if self.ub_open {
            write!(f, "[")
        } else {
            write!(f, "]")
        }
    }
}

impl fmt::Display for IntervalBoundary {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            IntervalBoundary::Infty => write!(f, "∞"),
            IntervalBoundary::Bound(tr) => {
                write!(f, "{tr}")
            }
        }
    }
}

#[cfg(test)]
mod tests {

    use taco_smt_encoder::{SMTSolverBuilder, expression_encoding::StaticSMTContext};
    use taco_threshold_automaton::{
        expressions::{
            BooleanExpression, ComparisonOp, IntegerExpression, Parameter, Variable,
            fraction::Fraction,
        },
        lia_threshold_automaton::integer_thresholds::{
            Threshold, ThresholdCompOp, ThresholdConstraint, WeightedSum,
        },
    };

    use crate::interval::{Interval, IntervalBoundary, IntervalOrderError};

    #[allow(clippy::cognitive_complexity)]
    #[test]
    fn test_check_add_always_out_of_interval() {
        let lb = IntervalBoundary::from_const(1);
        let ub = IntervalBoundary::from_const(42);

        let i = Interval::new(lb.clone(), false, ub.clone(), false);
        assert!(!i.check_add_always_out_of_interval(0));
        assert!(!i.check_add_always_out_of_interval(1));
        assert!(!i.check_add_always_out_of_interval(41));
        assert!(i.check_add_always_out_of_interval(42));
        assert!(i.check_add_always_out_of_interval(43));
        assert!(i.check_add_always_out_of_interval(100));

        let i = Interval::new(lb.clone(), true, ub.clone(), false);
        assert!(!i.check_add_always_out_of_interval(0));
        assert!(!i.check_add_always_out_of_interval(1));
        assert!(i.check_add_always_out_of_interval(41));
        assert!(i.check_add_always_out_of_interval(42));
        assert!(i.check_add_always_out_of_interval(43));
        assert!(i.check_add_always_out_of_interval(100));

        let i = Interval::new(lb.clone(), false, ub.clone(), true);
        assert!(!i.check_add_always_out_of_interval(0));
        assert!(!i.check_add_always_out_of_interval(1));
        assert!(i.check_add_always_out_of_interval(41));
        assert!(i.check_add_always_out_of_interval(42));
        assert!(i.check_add_always_out_of_interval(43));
        assert!(i.check_add_always_out_of_interval(100));

        let i = Interval::new(lb.clone(), true, ub.clone(), true);
        assert!(!i.check_add_always_out_of_interval(0));
        assert!(!i.check_add_always_out_of_interval(1));
        assert!(i.check_add_always_out_of_interval(41));
        assert!(i.check_add_always_out_of_interval(42));
        assert!(i.check_add_always_out_of_interval(43));
        assert!(i.check_add_always_out_of_interval(100));

        let ub = IntervalBoundary::from_threshold_constraint(&ThresholdConstraint::new(
            ThresholdCompOp::Lt,
            WeightedSum::new([(Parameter::new("n"), 1)]),
            0,
        ));
        let i = Interval::new(lb.clone(), true, ub.clone(), true);
        assert!(!i.check_add_always_out_of_interval(0));
        assert!(!i.check_add_always_out_of_interval(1));
        assert!(!i.check_add_always_out_of_interval(41));
        assert!(!i.check_add_always_out_of_interval(42));
        assert!(!i.check_add_always_out_of_interval(43));
        assert!(!i.check_add_always_out_of_interval(100));
    }

    #[allow(clippy::cognitive_complexity)]
    #[test]
    fn test_check_sub_always_out_of_interval() {
        let lb = IntervalBoundary::from_const(1);
        let ub = IntervalBoundary::from_const(42);

        let i = Interval::new(lb.clone(), false, ub.clone(), false);
        assert!(!i.check_sub_always_out_of_interval(0));
        assert!(!i.check_sub_always_out_of_interval(1));
        assert!(!i.check_sub_always_out_of_interval(41));
        assert!(i.check_sub_always_out_of_interval(42));
        assert!(i.check_sub_always_out_of_interval(43));
        assert!(i.check_sub_always_out_of_interval(100));

        let i = Interval::new(lb.clone(), true, ub.clone(), false);
        assert!(!i.check_sub_always_out_of_interval(0));
        assert!(!i.check_sub_always_out_of_interval(1));
        assert!(i.check_sub_always_out_of_interval(41));
        assert!(i.check_sub_always_out_of_interval(42));
        assert!(i.check_sub_always_out_of_interval(43));
        assert!(i.check_sub_always_out_of_interval(100));

        let i = Interval::new(lb.clone(), false, ub.clone(), true);
        assert!(!i.check_sub_always_out_of_interval(0));
        assert!(!i.check_sub_always_out_of_interval(1));
        assert!(i.check_sub_always_out_of_interval(41));
        assert!(i.check_sub_always_out_of_interval(42));
        assert!(i.check_sub_always_out_of_interval(43));
        assert!(i.check_sub_always_out_of_interval(100));

        let i = Interval::new(lb.clone(), true, ub.clone(), true);
        assert!(!i.check_sub_always_out_of_interval(0));
        assert!(!i.check_sub_always_out_of_interval(1));
        assert!(i.check_sub_always_out_of_interval(41));
        assert!(i.check_sub_always_out_of_interval(42));
        assert!(i.check_sub_always_out_of_interval(43));
        assert!(i.check_sub_always_out_of_interval(100));

        let ub = IntervalBoundary::from_threshold_constraint(&ThresholdConstraint::new(
            ThresholdCompOp::Lt,
            WeightedSum::new([(Parameter::new("n"), 1)]),
            0,
        ));
        let i = Interval::new(lb.clone(), true, ub.clone(), true);
        assert!(!i.check_sub_always_out_of_interval(0));
        assert!(!i.check_sub_always_out_of_interval(1));
        assert!(!i.check_sub_always_out_of_interval(41));
        assert!(!i.check_sub_always_out_of_interval(42));
        assert!(!i.check_sub_always_out_of_interval(43));
        assert!(!i.check_sub_always_out_of_interval(100));

        let lb = IntervalBoundary::from_const(1);
        let ub = IntervalBoundary::from_const(3);
        let i = Interval::new(lb.clone(), false, ub.clone(), true);
        assert!(!i.check_sub_always_out_of_interval(1));
    }

    #[test]
    fn test_new_interval() {
        let lb = IntervalBoundary::Bound(Threshold::new(WeightedSum::new_empty(), 1));
        let ub = IntervalBoundary::Infty;

        let interval = Interval::new(lb.clone(), false, ub.clone(), true);
        assert_eq!(interval.lb, lb);
        assert!(!interval.lb_open);
        assert_eq!(interval.ub, ub);
        assert!(interval.ub_open);

        let interval = Interval::new(lb.clone(), true, ub.clone(), false);
        assert_eq!(interval.lb, lb);
        assert!(interval.lb_open);
        assert_eq!(interval.ub, ub);
        assert!(interval.ub_open);
    }

    #[test]
    fn test_get_threshold_interval() {
        let lb = IntervalBoundary::Bound(Threshold::new(WeightedSum::new_empty(), 42));
        let ub = IntervalBoundary::Infty;

        assert_eq!(lb.get_threshold(), Some(&Threshold::from_const(42)));
        assert_eq!(ub.get_threshold(), None);
    }

    #[test]
    fn test_is_open_methods() {
        let interval = Interval::new_constant(0, 1);
        assert!(!interval.is_left_open());
        assert!(interval.is_right_open());

        let interval = Interval::new_constant(0, 1);
        assert!(!interval.is_left_open());
        assert!(interval.is_right_open());

        let interval = Interval::new_constant(0, 1);
        assert!(!interval.is_left_open());
        assert!(interval.is_right_open());

        let interval = Interval::new_constant(0, 1);
        assert!(!interval.is_left_open());
        assert!(interval.is_right_open());
    }

    #[test]
    fn test_interval_lookup_error_display() {
        let var = Variable::new("x");
        let interval = Interval {
            lb: IntervalBoundary::Bound(Threshold::new(WeightedSum::new_empty(), 1)),
            lb_open: false,
            ub: IntervalBoundary::Infty,
            ub_open: true,
        };

        let error = IntervalOrderError::IntervalNotFound {
            var: var.clone(),
            interval: interval.clone(),
        };
        assert!(error.to_string().contains(&var.to_string()));
        assert!(error.to_string().contains(&interval.to_string()));

        let error = IntervalOrderError::VariableNotFound { var: var.clone() };
        assert!(error.to_string().contains(&var.to_string()));

        let thr =
            ThresholdConstraint::new(ThresholdCompOp::Geq, Vec::<(Parameter, Fraction)>::new(), 2);
        let error = IntervalOrderError::ThresholdExtractionError {
            var: var.clone(),
            thr: thr.clone(),
        };
        assert!(error.to_string().contains(&var.to_string()));
        assert!(error.to_string().contains(&thr.to_string()));
    }

    #[test]
    fn test_interval_display() {
        let interval1 = Interval {
            lb: IntervalBoundary::Bound(Threshold::new(WeightedSum::new_empty(), 1)),
            lb_open: false,
            ub: IntervalBoundary::Infty,
            ub_open: true,
        };
        let interval2 = Interval {
            lb: IntervalBoundary::Bound(Threshold::new(WeightedSum::new_empty(), 2)),
            lb_open: true,
            ub: IntervalBoundary::Bound(Threshold::new(WeightedSum::new_empty(), 3)),
            ub_open: false,
        };

        assert_eq!(interval1.to_string(), "[1, ∞[");
        assert_eq!(interval2.to_string(), "]2, 3]");
    }

    #[test]
    fn test_interval_boundary_display() {
        let boundary1 = IntervalBoundary::Infty;
        let boundary2 = IntervalBoundary::Bound(Threshold::new(WeightedSum::new_empty(), 5));
        let boundary3 = IntervalBoundary::Bound(Threshold::new(
            WeightedSum::new_empty(),
            -(Fraction::from(3)),
        ));
        let boundary4 = IntervalBoundary::Bound(Threshold::new(
            WeightedSum::new([(Parameter::new("x"), 1)]),
            0,
        ));
        let boundary5 = IntervalBoundary::Bound(Threshold::new(
            WeightedSum::new([(Parameter::new("x"), 2)]),
            5,
        ));

        assert_eq!(boundary1.to_string(), "∞");
        assert_eq!(boundary2.to_string(), "5");
        assert_eq!(boundary3.to_string(), "-3");
        assert_eq!(boundary4.to_string(), "x");
        assert_eq!(boundary5.to_string(), "2 * x + 5")
    }

    #[test]
    fn test_new_methods() {
        let ifty = IntervalBoundary::new_infty();
        assert_eq!(ifty, IntervalBoundary::Infty);

        let b = IntervalBoundary::new_bound(WeightedSum::new_empty(), 1);
        assert_eq!(
            b,
            IntervalBoundary::Bound(Threshold::new(WeightedSum::new_empty(), 1,))
        );

        let c_i = Interval::new_constant(0, 1);
        assert_eq!(
            c_i,
            Interval {
                lb: IntervalBoundary::Bound(Threshold::new(WeightedSum::new_empty(), 0)),
                lb_open: false,
                ub: IntervalBoundary::Bound(Threshold::new(WeightedSum::new_empty(), 1,)),
                ub_open: true
            }
        );
    }

    #[test]
    fn test_encode_interval_as_boolean_expr() {
        let interval = Interval::new_constant(0, 1);
        let var = Variable::new("x");
        let expr = interval.encode_into_boolean_expr(&var);

        let expected = BooleanExpression::ComparisonExpression(
            Box::new(IntegerExpression::Atom(var.clone())),
            ComparisonOp::Geq,
            Box::new(IntegerExpression::Const(0)),
        ) & BooleanExpression::ComparisonExpression(
            Box::new(IntegerExpression::Atom(var.clone())),
            ComparisonOp::Lt,
            Box::new(IntegerExpression::Const(1)),
        );
        assert_eq!(expr, expected);

        let interval = Interval::new(
            IntervalBoundary::from_const(0),
            false,
            IntervalBoundary::new_infty(),
            true,
        );
        let var = Variable::new("x");
        let expr = interval.encode_into_boolean_expr(&var);

        let expected = BooleanExpression::ComparisonExpression(
            Box::new(IntegerExpression::Atom(var.clone())),
            ComparisonOp::Geq,
            Box::new(IntegerExpression::Const(0)),
        ) & BooleanExpression::True;
        assert_eq!(expr, expected);

        let interval = Interval::new(
            IntervalBoundary::from_const(0),
            true,
            IntervalBoundary::from_const(1),
            false,
        );
        let var = Variable::new("x");
        let expr = interval.encode_into_boolean_expr(&var);

        let expected = BooleanExpression::ComparisonExpression(
            Box::new(IntegerExpression::Atom(var.clone())),
            ComparisonOp::Gt,
            Box::new(IntegerExpression::Const(0)),
        ) & BooleanExpression::ComparisonExpression(
            Box::new(IntegerExpression::Atom(var.clone())),
            ComparisonOp::Leq,
            Box::new(IntegerExpression::Const(1)),
        );
        assert_eq!(expr, expected);
    }

    #[test]
    fn test_is_contained() {
        let interval = Interval::new_constant(0, 1);
        assert!(interval.check_is_contained(&IntervalBoundary::from_const(0)));
        assert!(!interval.check_is_contained(&IntervalBoundary::from_const(1)));
        assert!(!interval.check_is_contained(&IntervalBoundary::from_const(2)));

        let interval = Interval::new(
            IntervalBoundary::new_bound(
                WeightedSum::new([
                    (Parameter::new("F"), -Fraction::from(4)),
                    (Parameter::new("N"), 2.into()),
                    (Parameter::new("T"), 6.into()),
                ]),
                2,
            ),
            false,
            IntervalBoundary::new_infty(),
            true,
        );

        let ib = IntervalBoundary::new_bound(
            WeightedSum::new([
                (Parameter::new("F"), -Fraction::from(4)),
                (Parameter::new("N"), Fraction::from(2)),
                (Parameter::new("T"), Fraction::from(6)),
            ]),
            2,
        );

        assert!(interval.check_is_contained(&ib));
    }

    #[test]
    fn test_is_inhabited() {
        // Context without parameters for constant bounds
        let mut ctx = StaticSMTContext::new(SMTSolverBuilder::default(), [], [], [])
            .expect("Failed to create SMT context");

        // Unbounded interval with a closed side is always inhabited
        let interval = Interval::new(
            IntervalBoundary::from_const(0),
            false,
            IntervalBoundary::new_infty(),
            true,
        );
        assert!(interval.is_inhabited(&mut ctx));

        // Unbounded interval with an open side is always inhabited
        let interval = Interval::new(
            IntervalBoundary::from_const(0),
            true,
            IntervalBoundary::new_infty(),
            true,
        );
        assert!(interval.is_inhabited(&mut ctx));

        // Open interval with more than one integer between the borders
        let interval = Interval::new(
            IntervalBoundary::from_const(0),
            true,
            IntervalBoundary::from_const(2),
            true,
        );
        assert!(interval.is_inhabited(&mut ctx));

        // Open interval without an integer between the borders
        let interval = Interval::new(
            IntervalBoundary::from_const(0),
            true,
            IntervalBoundary::from_const(1),
            true,
        );
        assert!(!interval.is_inhabited(&mut ctx));

        // Empty open interval
        let interval = Interval::new(
            IntervalBoundary::from_const(1),
            true,
            IntervalBoundary::from_const(1),
            true,
        );
        assert!(!interval.is_inhabited(&mut ctx));
    }

    #[test]
    fn test_is_inhabited_with_parameters() {
        let n = Parameter::new("n");
        let mut ctx = StaticSMTContext::new(SMTSolverBuilder::default(), [n.clone()], [], [])
            .expect("Failed to create SMT context");

        let ub = IntervalBoundary::new_bound(WeightedSum::new([(n.clone(), 1)]), 1);

        // ]n, n + 1[ does not contain an integer
        let interval = Interval::new(
            IntervalBoundary::new_bound(WeightedSum::new([(n.clone(), 1)]), 0),
            true,
            ub.clone(),
            true,
        );
        assert!(!interval.is_inhabited(&mut ctx));

        // ]n, n + 2[ contains the integer n + 1
        let ub = IntervalBoundary::new_bound(WeightedSum::new([(n.clone(), 1)]), 2);
        let interval = Interval::new(
            IntervalBoundary::new_bound(WeightedSum::new([(n, 1)]), 0),
            true,
            ub,
            true,
        );
        assert!(interval.is_inhabited(&mut ctx));
    }
}
