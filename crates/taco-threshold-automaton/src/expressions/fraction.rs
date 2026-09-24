//! This module contains the implementation of the [`Fraction`] type and its
//! operations.
//!
//! Fractions are used to represent rational numbers in the threshold automaton,
//! for example, in [`crate::lia_threshold_automaton::LIAThresholdAutomaton`]
//! Fractions are always stored in their simplified form.

use std::{
    cmp::Ordering,
    fmt::{Debug, Display},
    ops::{self, Add, AddAssign, Div, DivAssign, Mul, MulAssign, Sub, SubAssign},
};

use crate::expressions::{Atomic, IntegerExpression};

/// Type to representing a fraction
#[derive(Debug, Clone, Copy, PartialEq, Hash)]
pub struct Fraction {
    /// True if the fraction is smaller than 0
    negated: bool,
    /// Numerator
    numerator: u32,
    /// Denominator
    denominator: u32,
}

impl Display for Fraction {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        debug_assert!(self.is_simplified());

        if let Ok(c) = i64::try_from(*self) {
            write!(f, "{c}")
        } else {
            if self.negated {
                write!(f, "-")?;
            }
            write!(f, "{}/{}", self.numerator, self.denominator)
        }
    }
}

impl Fraction {
    /// Returns true if the fraction is smaller than 0
    ///
    /// # Example
    ///
    /// ```rust
    /// use taco_threshold_automaton::expressions::fraction::Fraction;
    ///
    /// // 1/2
    /// let f = Fraction::new(1, 2, false);
    /// assert_eq!(f.is_negative(), false);
    ///
    /// // -1/2
    /// let f = Fraction::new(1, 2, true);
    /// assert_eq!(f.is_negative(), true);
    /// ```
    pub fn is_negative(&self) -> bool {
        debug_assert!(self.is_simplified());
        self.negated
    }

    /// Check whether the fraction is equal to 0
    ///
    /// # Example
    ///
    /// ```rust
    /// use taco_threshold_automaton::expressions::fraction::Fraction;
    ///
    /// // 0/5 is simplified to 0/1 upon creation
    /// let f = Fraction::new(0, 5, false);
    /// assert_eq!(f.is_zero(), true);
    ///
    /// let f = Fraction::new(1, 2, false);
    /// assert_eq!(f.is_zero(), false);
    /// ```
    pub fn is_zero(&self) -> bool {
        self.numerator == 0
    }

    /// Check whether the fraction represents an integer
    ///
    /// # Example
    ///
    /// ```rust
    /// use taco_threshold_automaton::expressions::fraction::Fraction;
    ///
    /// // 1/2 cannot be represented as an integer
    /// let f = Fraction::new(1, 2, false);
    /// assert_eq!(f.is_integer(), false);
    ///
    /// // 2/2 -> 1
    /// let f = Fraction::new(2, 2, false);
    /// assert_eq!(f.is_integer(), true);
    /// ```
    pub fn is_integer(&self) -> bool {
        self.numerator.is_multiple_of(self.denominator)
    }

    /// Check if the fraction is simplified
    fn is_simplified(&self) -> bool {
        num::integer::gcd(self.numerator, self.denominator) == 1
    }

    /// Create a new fraction
    ///
    /// Create a new fraction with the given numerator and denominator. Upon
    /// creation, the fraction is simplified to the maximal possible extent.
    ///
    /// # Example
    ///
    /// ```rust
    /// use taco_threshold_automaton::expressions::fraction::Fraction;
    ///
    /// let f = Fraction::new(42, 2, false);
    ///
    /// assert_eq!(i64::try_from(f).unwrap(), 21);
    /// assert_eq!(f.is_negative(), false);
    /// assert_eq!(f.numerator(), 21);
    /// assert_eq!(f.denominator(), 1);
    /// ```
    pub fn new(numerator: u32, denominator: u32, negated: bool) -> Self {
        Self {
            negated,
            numerator,
            denominator,
        }
        .canonicalize()
    }

    /// Simplify the fraction to the maximal possible extent and canonicalize its representation
    fn canonicalize(self) -> Self {
        // canonicalize when numerator = 0
        if self.numerator == 0 {
            return Self {
                negated: false,
                numerator: 0,
                denominator: 1,
            };
        }

        // canonicalize when denominator = 0
        if self.denominator == 0 {
            return Self {
                negated: false,
                numerator: 1,
                denominator: 0,
            };
        }

        // simplify the fraction
        let mut numerator = self.numerator;
        let mut denominator = self.denominator;
        let gcd = num::integer::gcd(self.numerator, self.denominator);

        numerator /= gcd;
        denominator /= gcd;

        Self {
            negated: self.negated,
            numerator,
            denominator,
        }
    }

    /// Compute the inverse of the fraction
    ///
    /// Panics if the numerator of the fraction is 0
    ///
    /// # Example
    ///
    /// ```rust
    /// use taco_threshold_automaton::expressions::fraction::Fraction;
    ///
    /// let f1 = Fraction::new(13, 2, false).inverse();
    /// let f2 = Fraction::new(2, 13, false);
    /// assert_eq!(f1, f2);
    /// ```
    pub fn inverse(&self) -> Self {
        if self.numerator() == 0 {
            panic!("Division by zero undefined!");
        }

        Self {
            negated: self.negated,
            numerator: self.denominator,
            denominator: self.numerator,
        }
    }

    /// Get the denominator of the fraction
    ///
    /// # Example
    ///
    /// ```rust
    /// use taco_threshold_automaton::expressions::fraction::Fraction;
    ///
    /// let f = Fraction::new(13, 2, false);
    /// assert_eq!(f.denominator(), 2);
    /// ```
    pub fn denominator(&self) -> u32 {
        debug_assert!(self.is_simplified());
        self.denominator
    }

    /// Get the numerator of the fraction
    ///
    /// # Example
    ///
    /// ```rust
    /// use taco_threshold_automaton::expressions::fraction::Fraction;
    ///
    /// let f = Fraction::new(42, 1, false);
    /// assert_eq!(f.numerator(), 42);
    /// ```
    pub fn numerator(&self) -> u32 {
        debug_assert!(self.is_simplified());
        self.numerator
    }

    /// Get the next closest integer while always rounding up
    ///
    /// Returns `None` for negative fractions
    ///
    /// # Example
    ///
    /// ```rust
    /// use taco_threshold_automaton::expressions::fraction::Fraction;
    ///
    /// // ceil(5/2) = 3
    /// let f = Fraction::new(5, 2, false);
    /// assert_eq!(f.get_ceil(), Some(3));
    ///
    /// // ceil(6/2) = 3
    /// let f = Fraction::new(6, 2, false);
    /// assert_eq!(f.get_ceil(), Some(3));
    ///
    /// // negative fractions cannot be rounded to a non-negative integer
    /// let f = Fraction::new(5, 2, true);
    /// assert_eq!(f.get_ceil(), None);
    /// ```
    pub fn get_ceil(&self) -> Option<u32> {
        debug_assert!(self.is_simplified());
        if self.is_negative() {
            return None;
        }

        let mut c = self.numerator / self.denominator;
        if !self.numerator.is_multiple_of(self.denominator) {
            c += 1;
        }

        Some(c)
    }

    /// Get the next closest integer while always rounding down
    ///
    /// Returns `None` for negative fractions
    ///
    /// # Example
    ///
    /// ```rust
    /// use taco_threshold_automaton::expressions::fraction::Fraction;
    ///
    /// // floor(5/2) = 2
    /// let f = Fraction::new(5, 2, false);
    /// assert_eq!(f.get_floor(), Some(2));
    ///
    /// // floor(6/2) = 3
    /// let f = Fraction::new(6, 2, false);
    /// assert_eq!(f.get_floor(), Some(3));
    ///
    /// // negative fractions cannot be rounded to a non-negative integer
    /// let f = Fraction::new(5, 2, true);
    /// assert_eq!(f.get_floor(), None);
    /// ```
    pub fn get_floor(&self) -> Option<u32> {
        debug_assert!(self.is_simplified());
        if self.is_negative() {
            return None;
        }

        Some(self.numerator / self.denominator)
    }
}

impl ops::Neg for Fraction {
    type Output = Self;

    fn neg(self) -> Self::Output {
        debug_assert!(self.is_simplified());
        Self {
            negated: !self.negated,
            numerator: self.numerator,
            denominator: self.denominator,
        }
    }
}

impl Eq for Fraction {}

impl Add for Fraction {
    type Output = Self;

    fn add(self, rhs: Self) -> Self::Output {
        if self.negated == rhs.negated {
            Fraction::new(
                self.numerator * rhs.denominator + rhs.numerator * self.denominator,
                self.denominator * rhs.denominator,
                self.negated,
            )
        } else {
            let denominator = self.denominator * rhs.denominator;
            let (negated, non_negated) = if self.negated {
                (self, rhs)
            } else {
                (rhs, self)
            };

            if non_negated.numerator * negated.denominator
                >= negated.numerator * non_negated.denominator
            {
                Fraction::new(
                    non_negated.numerator * negated.denominator
                        - negated.numerator * non_negated.denominator,
                    denominator,
                    false,
                )
            } else {
                Fraction::new(
                    negated.numerator * non_negated.denominator
                        - non_negated.numerator * negated.denominator,
                    denominator,
                    true,
                )
            }
        }
    }
}

impl AddAssign for Fraction {
    fn add_assign(&mut self, rhs: Self) {
        *self = *self + rhs;
    }
}

impl Sub for Fraction {
    type Output = Self;

    fn sub(self, rhs: Self) -> Self::Output {
        self + (-rhs)
    }
}

impl SubAssign for Fraction {
    fn sub_assign(&mut self, rhs: Self) {
        *self = *self - rhs;
    }
}

impl Mul for Fraction {
    type Output = Self;

    fn mul(self, rhs: Self) -> Self::Output {
        Fraction::new(
            self.numerator * rhs.numerator,
            self.denominator * rhs.denominator,
            self.negated ^ rhs.negated,
        )
    }
}

impl MulAssign for Fraction {
    fn mul_assign(&mut self, rhs: Self) {
        *self = *self * rhs;
    }
}

impl Div for Fraction {
    type Output = Self;

    #[allow(clippy::suspicious_arithmetic_impl)]
    fn div(self, rhs: Self) -> Self::Output {
        self * Fraction::new(rhs.denominator, rhs.numerator, rhs.negated)
    }
}

impl DivAssign for Fraction {
    fn div_assign(&mut self, rhs: Self) {
        *self = *self / rhs;
    }
}

impl From<u32> for Fraction {
    fn from(value: u32) -> Self {
        Fraction {
            negated: false,
            numerator: value,
            denominator: 1,
        }
    }
}

impl PartialOrd for Fraction {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for Fraction {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        let a = self.numerator * other.denominator;
        let b = other.numerator * self.denominator;

        if self.negated && !other.negated {
            return Ordering::Less;
        }

        if !self.negated && other.negated {
            return Ordering::Greater;
        }

        if self.negated && other.negated {
            // For negative fractions, reverse the comparison
            return a.cmp(&b).reverse();
        }
        a.cmp(&b)
    }
}

impl TryFrom<Fraction> for i64 {
    type Error = ();

    /// Try to convert the fraction into an integer    
    fn try_from(value: Fraction) -> Result<Self, Self::Error> {
        if value.numerator.is_multiple_of(value.denominator) {
            let mut res = value.numerator as i64 / value.denominator as i64;

            if value.negated {
                res = -res;
            }

            Ok(res)
        } else {
            Err(())
        }
    }
}

impl<T: Atomic> From<Fraction> for IntegerExpression<T> {
    fn from(value: Fraction) -> Self {
        // attempt conversion into an integer value first
        if let Ok(c) = i64::try_from(value) {
            if c < 0 {
                return -IntegerExpression::Const(-c as u32);
            } else {
                return IntegerExpression::Const(c as u32);
            }
        }

        // only return fractions when necessary
        let mut expr =
            IntegerExpression::Const(value.numerator) / IntegerExpression::Const(value.denominator);

        if value.negated {
            expr = -expr;
        }

        expr
    }
}

#[cfg(test)]
mod tests {

    use crate::expressions::Variable;

    use super::*;

    #[test]
    fn test_fraction_getters() {
        let f = Fraction::new(4, 8, false);
        assert_eq!(f.numerator(), 1);
        assert_eq!(f.denominator(), 2);
        assert!(!f.is_negative());

        let f = Fraction::new(12, 9, true);
        assert_eq!(f.numerator(), 4);
        assert_eq!(f.denominator(), 3);
    }

    #[test]
    fn test_fraction_get_ceil() {
        // exact integers are returned unchanged
        let f = Fraction::new(6, 2, false);
        assert_eq!(f.get_ceil(), Some(3));

        let f = Fraction::new(4, 2, true);
        assert_eq!(f.get_ceil(), None);

        // fractional parts are rounded up
        let f = Fraction::new(5, 2, false);
        assert_eq!(f.get_ceil(), Some(3));

        let f = Fraction::new(1, 3, false);
        assert_eq!(f.get_ceil(), Some(1));

        let f = Fraction::new(7, 3, false);
        assert_eq!(f.get_ceil(), Some(3));

        let f = Fraction::new(2, 3, false);
        assert_eq!(f.get_ceil(), Some(1));

        // zero
        let f = Fraction::new(0, 1, false);
        assert_eq!(f.get_ceil(), Some(0));

        // negative fractions
        let f = Fraction::new(1, 2, true);
        assert_eq!(f.get_ceil(), None);
    }

    #[test]
    fn test_fraction_get_floor() {
        // exact integers are returned unchanged
        let f = Fraction::new(6, 2, false);
        assert_eq!(f.get_floor(), Some(3));

        let f = Fraction::new(4, 2, true);
        assert_eq!(f.get_floor(), None);

        // fractional parts are rounded down
        let f = Fraction::new(5, 2, false);
        assert_eq!(f.get_floor(), Some(2));

        let f = Fraction::new(1, 3, false);
        assert_eq!(f.get_floor(), Some(0));

        let f = Fraction::new(7, 3, false);
        assert_eq!(f.get_floor(), Some(2));

        // zero
        let f = Fraction::new(0, 1, false);
        assert_eq!(f.get_floor(), Some(0));

        // negative fractions
        let f = Fraction::new(1, 2, true);
        assert_eq!(f.get_floor(), None);

        // floor and ceil coincide for integers
        let f = Fraction::new(9, 3, false);
        assert_eq!(f.get_floor(), f.get_ceil());
    }

    #[test]
    fn test_fraction_is_zero() {
        // zero values
        let f = Fraction::new(0, 1, false);
        assert!(f.is_zero());

        let f = Fraction::new(0, 1, true);
        assert!(f.is_zero());

        let f = Fraction::new(0, 5, false);
        assert!(f.is_zero());

        // non-zero values
        let f = Fraction::new(1, 2, false);
        assert!(!f.is_zero());

        let f = Fraction::new(42, 7, false);
        assert!(!f.is_zero());

        let f = Fraction::new(1, 2, true);
        assert!(!f.is_zero());

        // canonicalize maps zero to 0/1 with negated = false
        let f = Fraction::new(0, 5, true);
        assert!(f.is_zero());
        assert_eq!(f.numerator(), 0);
        assert_eq!(f.denominator(), 1);
        assert!(!f.is_negative());
    }

    #[test]
    fn test_fraction_is_integer() {
        let f1 = Fraction::new(4, 2, false);
        assert!(f1.is_integer());
        let f2 = Fraction::new(5, 2, false);
        assert!(!f2.is_integer());
        let f3 = Fraction::new(0, 1, false);
        assert!(f3.is_integer());
        let f4 = Fraction::new(0, 0, false);
        assert!(f4.is_integer()); // 0 is considered an integer
    }

    #[test]
    fn test_simplification_for_div_by_zero() {
        let f1 = Fraction::new(42, 0, true);
        let f2 = Fraction::new(1, 0, false);
        assert_eq!(f1, f2);
    }

    #[test]
    fn test_fraction_addition() {
        let f1 = Fraction::new(1, 2, false);
        let f2 = Fraction::new(1, 3, false);
        let result = f1 + f2;
        assert_eq!(result.numerator, 5);
        assert_eq!(result.denominator, 6);
        assert!(!result.negated);

        let f1 = Fraction::new(5, 10, false);
        let f2 = Fraction::new(10, 30, true);
        let result = f1 + f2;
        assert_eq!(result.numerator, 1);
        assert_eq!(result.denominator, 6);
        assert!(!result.negated);

        let f1 = Fraction::new(3, 6, true);
        let f2 = Fraction::new(1, 3, false);
        let result = f1 + f2;
        assert_eq!(result.numerator, 1);
        assert_eq!(result.denominator, 6);
        assert!(result.negated);

        let mut f1 = Fraction::new(3, 6, true);
        let f2 = Fraction::new(2, 8, true);
        f1 += f2;
        assert_eq!(f1.numerator, 3);
        assert_eq!(f1.denominator, 4);
        assert!(f1.negated);
    }

    #[test]
    fn test_fraction_subtraction() {
        let f1 = Fraction::new(100, 200, false);
        let f2 = Fraction::new(10, 30, false);
        let result = f1 - f2;
        assert_eq!(result.numerator, 1);
        assert_eq!(result.denominator, 6);
        assert!(!result.negated);

        let f1 = Fraction::new(9, 18, false);
        let f2 = Fraction::new(1, 3, true);
        let result = f1 - f2;
        assert_eq!(result.numerator, 5);
        assert_eq!(result.denominator, 6);
        assert!(!result.negated);

        let mut f1 = Fraction::new(3, 6, true);
        let f2 = Fraction::new(1, 3, false);
        f1 -= f2;
        assert_eq!(f1.numerator, 5);
        assert_eq!(f1.denominator, 6);
        assert!(f1.negated);
    }

    #[test]
    fn test_fraction_multiplication() {
        let f1 = Fraction::new(1, 2, false);
        let f2 = Fraction::new(1, 3, false);
        let result = f1 * f2;
        assert_eq!(result.numerator, 1);
        assert_eq!(result.denominator, 6);
        assert!(!result.negated);

        let f1 = Fraction::new(1, 2, false);
        let f2 = Fraction::new(5, 15, true);
        let result = f1 * f2;
        assert_eq!(result.numerator, 1);
        assert_eq!(result.denominator, 6);
        assert!(result.negated);

        let f1 = Fraction::new(1, 2, true);
        let f2 = Fraction::new(1, 3, true);
        let result = f1 * f2;
        assert_eq!(result.numerator, 1);
        assert_eq!(result.denominator, 6);
        assert!(!result.negated);

        let mut f1 = Fraction::new(1, 2, false);
        let f2 = Fraction::new(1, 3, true);
        f1 *= f2;
        assert_eq!(f1.numerator, 1);
        assert_eq!(f1.denominator, 6);
        assert!(f1.negated);
    }

    #[test]
    fn test_fraction_division() {
        let f1 = Fraction::new(1, 2, false);
        let f2 = Fraction::new(1, 3, false);
        let result = f1 / f2;
        assert_eq!(result.numerator, 3);
        assert_eq!(result.denominator, 2);
        assert!(!result.negated);

        let f1 = Fraction::new(5, 10, false);
        let f2 = Fraction::new(20, 40, false);
        let result = f1 / f2;
        assert_eq!(result.numerator, 1);
        assert_eq!(result.denominator, 1);

        let mut f1 = Fraction::new(1, 2, false);
        let f2 = Fraction::new(1, 3, true);
        f1 /= f2;
        assert_eq!(f1.numerator, 3);
        assert_eq!(f1.denominator, 2);
        assert!(f1.negated);
    }

    #[test]
    fn test_fraction_negation() {
        let f1 = Fraction::new(1, 2, false);
        let result = -f1;
        assert_eq!(result.numerator, 1);
        assert_eq!(result.denominator, 2);
        assert!(result.negated);
    }

    #[test]
    fn test_fraction_addition_with_negation() {
        let f1 = Fraction::new(1, 2, false);
        let f2 = Fraction::new(1, 3, true);
        let result = f1 + f2;
        assert_eq!(result.numerator, 1);
        assert_eq!(result.denominator, 6);
        assert!(!result.negated);
    }

    #[test]
    fn test_fraction_subtraction_with_negation() {
        let f1 = Fraction::new(1, 2, false);
        let f2 = Fraction::new(1, 3, true);
        let result = f1 - f2;
        assert_eq!(result.numerator, 5);
        assert_eq!(result.denominator, 6);
        assert!(!result.negated);
    }

    #[test]
    fn test_fraction_multiplication_with_negation() {
        let f1 = Fraction::new(1, 2, false);
        let f2 = Fraction::new(1, 3, true);
        let result = f1 * f2;
        assert_eq!(result.numerator, 1);
        assert_eq!(result.denominator, 6);
        assert!(result.negated);
    }

    #[test]
    fn test_fraction_division_with_negation() {
        let f1 = Fraction::new(1, 2, false);
        let f2 = Fraction::new(1, 3, true);
        let result = f1 / f2;
        assert_eq!(result.numerator, 3);
        assert_eq!(result.denominator, 2);
        assert!(result.negated);
    }

    #[test]
    fn test_fraction_simplification() {
        let f = Fraction::new(4, 8, false).canonicalize();
        assert_eq!(f.numerator, 1);
        assert_eq!(f.denominator, 2);
        assert!(!f.negated);
    }

    #[test]
    fn test_fraction_eq() {
        let f1 = Fraction::new(1, 2, false);
        let f2 = Fraction::new(1, 2, false);
        assert_eq!(f1, f2);

        let f1 = Fraction::new(1, 2, false);
        let f2 = Fraction::new(1, 2, true);
        assert_ne!(f1, f2);

        let f1 = Fraction::new(1, 2, false);
        let f2 = Fraction::new(2, 4, false);
        assert_eq!(f1, f2);

        let f1 = Fraction::new(1, 2, false);
        let f2 = Fraction::new(2, 4, true);
        assert_ne!(f1, f2);

        let f1 = Fraction::new(0, 2, true);
        let f2 = Fraction::new(0, 2, false);
        assert_eq!(f1, f2);

        let f1 = Fraction::new(0, 2, true);
        let f2 = Fraction::new(0, 3, true);
        assert_eq!(f1, f2);
    }

    #[test]
    fn test_fraction_simplification_with_negation() {
        let f = Fraction::new(4, 8, true).canonicalize();
        assert_eq!(f.numerator, 1);
        assert_eq!(f.denominator, 2);
        assert!(f.negated);
    }

    #[test]
    fn test_fraction_from_u32() {
        let f: Fraction = 5u32.into();
        assert_eq!(f.numerator, 5);
        assert_eq!(f.denominator, 1);
        assert!(!f.negated);
    }

    #[test]
    fn test_fraction_try_into_i64_success() {
        let f = Fraction::new(4, 2, false);
        let result: Result<i64, ()> = f.try_into();
        assert_eq!(result.unwrap(), 2);
    }

    #[test]
    fn test_fraction_try_into_i64_failure() {
        let f = Fraction::new(5, 2, false);
        let result: Result<i64, ()> = f.try_into();
        assert!(result.is_err());
    }

    #[test]
    fn test_fraction_try_into_i64_negated() {
        let f = Fraction::new(4, 2, true);
        let result: Result<i64, ()> = f.try_into();
        assert_eq!(result.unwrap(), -2);
    }

    #[test]
    fn test_fraction_display() {
        let f = Fraction::new(1, 2, false);
        assert_eq!(f.to_string(), "1/2");

        let f = Fraction::new(1, 2, true);
        assert_eq!(f.to_string(), "-1/2");

        let f = Fraction::new(1, 1, false);
        assert_eq!(f.to_string(), "1");
    }

    #[test]
    fn test_fraction_into_integer_expression() {
        let f = Fraction::new(1, 2, false);
        let expr: IntegerExpression<Variable> = f.into();
        assert_eq!(
            expr,
            IntegerExpression::Const(1) / IntegerExpression::Const(2)
        );

        let f = Fraction::new(1, 2, true);
        let expr: IntegerExpression<Variable> = f.into();
        assert_eq!(
            expr,
            -(IntegerExpression::Const(1) / IntegerExpression::Const(2))
        );

        let f = Fraction::new(1, 1, false);
        let expr: IntegerExpression<Variable> = f.into();
        assert_eq!(expr, IntegerExpression::Const(1));

        let f = Fraction::new(1, 1, true);
        let expr: IntegerExpression<Variable> = f.into();
        assert_eq!(expr, -IntegerExpression::Const(1));
    }

    #[test]
    fn test_inverse() {
        let f = Fraction::new(1, 2, true);
        let expected = Fraction::new(2, 1, true);
        assert_eq!(f.inverse(), expected);

        let f = Fraction::new(1, 2, false);
        let expected = Fraction::new(2, 1, false);
        assert_eq!(f.inverse(), expected);
    }

    #[test]
    #[should_panic]
    fn test_inverse_panics_on_0_numerator() {
        let f = Fraction::new(0, 2, true);
        let _ = f.inverse();
    }

    #[test]
    fn test_fraction_ord() {
        let f1 = Fraction::new(1, 2, false);
        let f2 = Fraction::new(1, 2, false);
        assert_eq!(f1.cmp(&f2), Ordering::Equal);
        assert_eq!(f2.cmp(&f1), Ordering::Equal);

        let f1 = Fraction::new(1, 2, true);
        let f2 = Fraction::new(1, 2, true);
        assert_eq!(f1.cmp(&f2), Ordering::Equal);
        assert_eq!(f2.cmp(&f1), Ordering::Equal);

        let f1 = Fraction::new(1, 2, true);
        let f2 = Fraction::new(1, 2, false);
        assert_eq!(f1.cmp(&f2), Ordering::Less);
        assert_eq!(f2.cmp(&f1), Ordering::Greater);

        let f1 = Fraction::new(1, 2, false);
        let f2 = Fraction::new(2, 2, false);
        assert_eq!(f1.cmp(&f2), Ordering::Less);
        assert_eq!(f2.cmp(&f1), Ordering::Greater);

        let f1 = Fraction::new(1, 4, false);
        let f2 = Fraction::new(1, 2, false);
        assert_eq!(f1.cmp(&f2), Ordering::Less);
        assert_eq!(f2.cmp(&f1), Ordering::Greater);
    }
}
