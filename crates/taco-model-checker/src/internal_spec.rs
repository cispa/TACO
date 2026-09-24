//! Internal specification types
//!
//! This module defines the specification format that model checkers in TACO
//! operate on. An [`ErrorSpec`] describes the *erroneous* behavior of a threshold
//! automaton, i.e., it is the negation of an ELTL property. A property is
//! violated if there exists a run of the threshold automaton satisfying the
//! error formula.

use core::fmt;
use core::ops::{Index, IndexMut};

use log::{debug, warn};
use taco_display_utils::join_iterator;
use taco_threshold_automaton::ModifiableThresholdAutomaton;
use taco_threshold_automaton::lia_threshold_automaton::LIAVariableConstraint;
use taco_threshold_automaton::{
    expressions::{
        And, Atomic, BooleanConnective, BooleanExpression, Location, Or, Parameter, Variable,
    },
    impl_bitand,
};

use crate::internal_spec::extraction::ExtractionError;
use crate::{ModelCheckerContext, SpecificationTrait, TASpecification};
use crate::{
    eltl::{ELTLExpression, remove_negations::NonNegatedELTLExpression},
    internal_spec::upwards_closed_set::UpwardsClosedSet,
};

mod extraction;
pub mod upwards_closed_set;

/// Named specification of erroneous behavior
///
/// An [`ErrorSpec`] pairs the original ELTL property with the [`ErrorFormula`]
/// describing its violations. The threshold automaton violates the property if
/// and only if there exists a run satisfying the error formula.
#[derive(Debug, Clone, PartialEq)]
pub struct ErrorSpec {
    /// Name of the property
    name: String,
    /// The ELTL property this error specification was derived from
    source: Box<ELTLExpression>,
    /// Formula describing the violations of the property
    ef: ErrorFormula,
}

impl ErrorSpec {
    /// Get the name of the specification
    pub fn name(&self) -> &str {
        &self.name
    }

    /// Get the ELTL property this specification was derived from
    pub fn source(&self) -> &ELTLExpression {
        &self.source
    }

    /// Get the formula describing the violations of the property
    pub fn error_formula(&self) -> &ErrorFormula {
        &self.ef
    }

    /// Create the threshold automata that need to be checked
    pub fn create_tas_to_check<T: ModifiableThresholdAutomaton>(
        &self,
        ta: &T,
    ) -> impl Iterator<Item = (ErrorTarget, T)> {
        self.ef.iter().map(move |at| {
            let mut ta = ta.clone();

            ta.add_initial_location_constraints(
                at.init_restriction().location_constraints().iter().cloned(),
            );
            ta.add_initial_variable_constraints(
                at.init_restriction().variable_constraints().iter().cloned(),
            );
            ta.add_resilience_conditions(
                at.init_restriction()
                    .parameter_constraints()
                    .iter()
                    .cloned(),
            );

            (at.target.clone(), ta)
        })
    }
}

impl fmt::Display for ErrorSpec {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}: {}", self.name, self.ef)
    }
}

impl<C: ModelCheckerContext> SpecificationTrait<C> for ErrorSpec {
    type TransformationError = ExtractionError;
    type InternalSpecType = ErrorTarget;

    fn try_from_eltl(
        spec: impl Iterator<Item = (String, ELTLExpression)>,
        _ctx: &C,
    ) -> Result<(Vec<Self>, Vec<String>), Self::TransformationError> {
        let mut res_properties = Vec::new();
        let mut untranslatable = Vec::new();

        for (name, expr) in spec {
            let res = ErrorSpec::from_named_eltl(name.clone(), expr.clone());

            if matches!(&res, &Err(ExtractionError::NestedTemporalOperator))
                || matches!(&res, &Err(ExtractionError::UnsupportedConjunction(_, _)))
            {
                warn!(
                    "Specification '{name}' contains an operator nesting not yet supported by TACO. It will be reported as unknown."
                );
                debug!(
                    "Classified property '{name}' as requiring operator nesting. Expression: {expr}"
                );
                untranslatable.push(name);
                continue;
            }

            // Liveness properties that cannot be translated are reported as
            // unknown, errors in safety properties abort the setup
            if let Err(err) = &res
                && contains_globally(&(!expr.clone()).into())
            {
                warn!(
                    "Liveness specification '{name}' is not supported by TACO ({err}). It will be reported as unknown."
                );
                debug!("Failed to translate liveness property '{name}'. Expression: {expr}");
                untranslatable.push(name);
                continue;
            }

            let res = res?;
            res_properties.push(res);
        }

        Ok((res_properties, untranslatable))
    }

    fn transform_threshold_automaton<
        TA: taco_threshold_automaton::ThresholdAutomaton
            + taco_threshold_automaton::ModifiableThresholdAutomaton,
    >(
        ta: TA,
        specs: Vec<Self>,
        _ctx: &C,
    ) -> Vec<(String, Self::InternalSpecType, TA)> {
        specs
            .into_iter()
            .flat_map(|spec| {
                spec.create_tas_to_check(&ta)
                    .map(|(target, ta)| {
                        // A target without temporal part is violated if an
                        // initial configuration satisfies the restriction
                        let target = match target {
                            ErrorTarget::Top => ErrorTarget::Reach(UpwardsClosedSet::new_top()),
                            t => t,
                        };
                        (spec.name.clone(), target, ta)
                    })
                    .collect::<Vec<_>>()
            })
            .collect::<Vec<_>>()
    }
}

/// Check whether the expression contains a `[]` operator
fn contains_globally(expr: &NonNegatedELTLExpression) -> bool {
    match expr {
        NonNegatedELTLExpression::Globally(_) => true,
        NonNegatedELTLExpression::Eventually(e) => contains_globally(e),
        NonNegatedELTLExpression::And(l, r) | NonNegatedELTLExpression::Or(l, r) => {
            contains_globally(l) || contains_globally(r)
        }
        _ => false,
    }
}

/// Boolean combination of [`ErrorAtom`]s
///
/// A disjunction is satisfied if a run satisfying one of the disjuncts exists,
/// therefore, the disjuncts can be checked in independent model checker runs.
/// A conjunction requires a *single* run satisfying both conjuncts. Conjunctions
/// for which a sound merge exists are already merged into a single atom during
/// extraction (e.g., `[](a) && [](b)` becomes `[](a && b)`), the remaining
/// conjunctions (e.g., `<>(a) && <>(b)`) need to be handled by the model
/// checker.
pub type ErrorFormula = Disjunction<ErrorAtom>;

/// Specification that can be checked in a single model checker run
///
/// An atom is of the form `init && target`, where `init` restricts the initial
/// configuration (and parameters) of the runs to consider and `target` is the
/// temporal part of the specification.
#[derive(Debug, Clone, PartialEq)]
pub struct ErrorAtom {
    /// Restriction on the initial configuration
    init_restriction: InitRestriction,
    /// Temporal part of the atom
    target: ErrorTarget,
}

impl ErrorAtom {
    /// Create a new atom
    pub fn new(init_restriction: InitRestriction, target: ErrorTarget) -> Self {
        Self {
            init_restriction,
            target,
        }
    }

    /// Get the restriction on the initial configuration
    pub fn init_restriction(&self) -> &InitRestriction {
        &self.init_restriction
    }

    /// Get the temporal part of the atom
    pub fn target(&self) -> &ErrorTarget {
        &self.target
    }

    /// Check whether this atom is trivially satisfied by every run
    pub fn is_top(&self) -> bool {
        self.init_restriction.is_top() && matches!(self.target, ErrorTarget::Top)
    }

    /// Check whether this atom is unsatisfiable
    pub fn is_bot(&self) -> bool {
        self.target.is_bot()
    }

    /// The upwards closed sets appearing in the temporal part of this atom
    fn targets(&self) -> impl Iterator<Item = &UpwardsClosedSet> {
        self.target.sets()
    }
}

impl TASpecification for ErrorAtom {
    fn locs_appearing(&self) -> impl IntoIterator<Item = &Location> {
        self.targets().flat_map(|set| set.locs_appearing())
    }

    fn var_constraint(&self) -> impl IntoIterator<Item = &LIAVariableConstraint> {
        self.targets().flat_map(|set| set.var_constraint())
    }
}

impl TASpecification for ErrorFormula {
    /// Locations appearing in any of the disjuncts
    ///
    /// Used by the preprocessing to ensure that no location mentioned in the
    /// specification is removed, so taking the union over all disjuncts is
    /// sound.
    fn locs_appearing(&self) -> impl IntoIterator<Item = &Location> {
        self.iter().flat_map(|atom| atom.locs_appearing())
    }

    /// Variable constraints appearing in any of the disjuncts
    ///
    /// Used by the interval abstraction to compute the relevant bounds for the
    /// shared variables, so taking the union over all disjuncts is sound.
    fn var_constraint(&self) -> impl IntoIterator<Item = &LIAVariableConstraint> {
        self.iter().flat_map(|atom| atom.var_constraint())
    }
}

impl TASpecification for ErrorTarget {
    /// Locations appearing in the temporal part of the target
    fn locs_appearing(&self) -> impl IntoIterator<Item = &Location> {
        self.sets().flat_map(|set| set.locs_appearing())
    }

    /// Variable constraints appearing in the temporal part of the target
    fn var_constraint(&self) -> impl IntoIterator<Item = &LIAVariableConstraint> {
        self.sets().flat_map(|set| set.var_constraint())
    }
}

impl fmt::Display for ErrorAtom {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if !self.init_restriction.is_top() {
            write!(f, "({}) && ", self.init_restriction)?;
        }

        write!(f, "({})", self.target)
    }
}

/// Temporal part of an [`ErrorAtom`]
#[derive(Debug, Clone, PartialEq)]
pub enum ErrorTarget {
    /// `<>(set)`: some configuration in the set is reachable
    Reach(UpwardsClosedSet),
    /// `[](set)`: there is an (infinite) run that never leaves the set
    Invariant(UpwardsClosedSet),
    /// `<>(pre && [](inv))`: there is an (infinite) run that reaches a
    /// configuration in `pre` and never leaves `inv` afterwards
    Ensure {
        /// Set of configurations to reach
        pre: UpwardsClosedSet,
        /// Set of configurations that is never left after reaching `pre`
        inv: UpwardsClosedSet,
    },
    /// `[](pre && <>(inv))`: there is an (infinite) run that never leaves
    /// `pre` and visits `inv` infinitely often
    Repeat {
        /// Set of configurations that is never left
        pre: UpwardsClosedSet,
        /// Set of configurations that is visited infinitely often
        inv: UpwardsClosedSet,
    },
    /// No temporal part: the atom is only a restriction on the initial
    /// configuration
    Top,
}

impl ErrorTarget {
    /// Check whether the target is unsatisfiable
    pub fn is_bot(&self) -> bool {
        match self {
            ErrorTarget::Reach(set) | ErrorTarget::Invariant(set) => set.is_bot(),
            ErrorTarget::Ensure { pre, inv } | ErrorTarget::Repeat { pre, inv } => {
                pre.is_bot() || inv.is_bot()
            }
            ErrorTarget::Top => false,
        }
    }

    /// Check whether the target is always satisfiable
    pub fn is_top(&self) -> bool {
        match self {
            ErrorTarget::Reach(s) | ErrorTarget::Invariant(s) => s.is_top(),
            ErrorTarget::Ensure { pre, inv } | ErrorTarget::Repeat { pre, inv } => {
                pre.is_top() && inv.is_top()
            }
            ErrorTarget::Top => true,
        }
    }

    /// Create a new atom requiring to reach an upwards closed set of locations
    pub fn new_reach(tgt: UpwardsClosedSet) -> Self {
        Self::Reach(tgt)
    }

    /// Create a new atom requiring to never leave an upwards closed set of
    /// locations
    pub fn new_invariant(tgt: UpwardsClosedSet) -> Self {
        Self::Invariant(tgt)
    }

    /// Create a new atom requiring to reach a configuration in `pre` while
    /// never leaving `inv` afterwards
    pub fn new_ensure(pre: UpwardsClosedSet, inv: UpwardsClosedSet) -> Self {
        Self::Ensure { pre, inv }
    }

    /// Create a new atom requiring to ensure that a run never leaves `pre`
    /// while eventually reaching `inv`
    pub fn new_repeat(pre: UpwardsClosedSet, inv: UpwardsClosedSet) -> Self {
        Self::Repeat { pre, inv }
    }

    /// Check whether specification contains a reachability constraint where at
    /// least one location needs to be empty
    ///
    /// Only [`ErrorTarget::Reach`] targets are considered, the other temporal
    /// targets always return `false`.
    pub fn contains_reachability_constraint(&self) -> bool {
        match self {
            ErrorTarget::Reach(s) => s.contains_reachability_constraint(),
            _ => false,
        }
    }

    /// The upwards closed sets appearing in this target
    fn sets(&self) -> impl Iterator<Item = &UpwardsClosedSet> {
        let (pre, inv) = match self {
            ErrorTarget::Reach(set) | ErrorTarget::Invariant(set) => (Some(set), None),
            ErrorTarget::Ensure { pre, inv } | ErrorTarget::Repeat { pre, inv } => {
                (Some(pre), Some(inv))
            }
            ErrorTarget::Top => (None, None),
        };

        [pre, inv].into_iter().flatten()
    }
}

impl fmt::Display for ErrorTarget {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            ErrorTarget::Reach(set) => write!(f, "<>({set})"),
            ErrorTarget::Invariant(set) => write!(f, "[]({set})"),
            ErrorTarget::Ensure { pre, inv } => write!(f, "<>(({pre}) && []({inv}))"),
            ErrorTarget::Repeat { pre, inv } => write!(f, "[](({pre}) && <>({inv}))"),
            ErrorTarget::Top => write!(f, "true"),
        }
    }
}

/// Restriction on the initial configuration of a run
///
/// The restriction is a conjunction of arbitrary boolean constraints, split by
/// the kind of atoms they range over. Constraints on parameters are rigid,
/// i.e., they hold at every position of a run.
#[derive(Debug, Clone, PartialEq, Default)]
pub struct InitRestriction {
    /// Conjunction of conditions on the parameters
    precondition_par: Conjunction<BooleanExpression<Parameter>>,
    /// Conjunction of conditions on the initial distribution of processes in
    /// the threshold automaton
    precondition_loc: Conjunction<BooleanExpression<Location>>,
    /// Conjunction of conditions on the initial valuation of the shared
    /// variables
    precondition_var: Conjunction<BooleanExpression<Variable>>,
}

impl InitRestriction {
    /// Create a restriction that allows every initial configuration
    pub fn new_top() -> Self {
        Self::default()
    }

    /// Create a restriction consisting of a single parameter constraint
    pub fn new_parameter_constraint(constr: BooleanExpression<Parameter>) -> Self {
        Self {
            precondition_par: [constr].into(),
            ..Default::default()
        }
    }

    /// Create a restriction consisting of a single constraint on the initial
    /// distribution of processes
    pub fn new_location_constraint(constr: BooleanExpression<Location>) -> Self {
        Self {
            precondition_loc: [constr].into(),
            ..Default::default()
        }
    }

    /// Create a restriction consisting of a single constraint on the initial
    /// valuation of the shared variables
    pub fn new_variable_constraint(constr: BooleanExpression<Variable>) -> Self {
        Self {
            precondition_var: [constr].into(),
            ..Default::default()
        }
    }

    /// Check whether the restriction allows every initial configuration
    pub fn is_top(&self) -> bool {
        self.precondition_par.is_empty()
            && self.precondition_loc.is_empty()
            && self.precondition_var.is_empty()
    }

    /// Disjunction of two restrictions, if a sound merge exists
    ///
    /// The restriction is a conjunction of one condition per kind of atom.
    /// Because of this, the disjunction is only representable if both
    /// restrictions differ in at most one kind:
    /// `(p && l1 && v) || (p && l2 && v)` is equal to `p && (l1 || l2) && v`.
    pub fn try_or(&self, other: &Self) -> Option<Self> {
        let differing = [
            self.precondition_par != other.precondition_par,
            self.precondition_loc != other.precondition_loc,
            self.precondition_var != other.precondition_var,
        ]
        .into_iter()
        .filter(|differs| *differs)
        .count();

        if differing > 1 {
            return None;
        }

        // Equal kinds are unchanged by `or_conjunctions`
        Some(Self {
            precondition_par: or_conjunctions(
                self.precondition_par.clone(),
                other.precondition_par.clone(),
            ),
            precondition_loc: or_conjunctions(
                self.precondition_loc.clone(),
                other.precondition_loc.clone(),
            ),
            precondition_var: or_conjunctions(
                self.precondition_var.clone(),
                other.precondition_var.clone(),
            ),
        })
    }

    /// Conditions on the parameters
    pub fn parameter_constraints(&self) -> &Conjunction<BooleanExpression<Parameter>> {
        &self.precondition_par
    }

    /// Conditions on the initial distribution of processes
    pub fn location_constraints(&self) -> &Conjunction<BooleanExpression<Location>> {
        &self.precondition_loc
    }

    /// Conditions on the initial valuation of the shared variables
    pub fn variable_constraints(&self) -> &Conjunction<BooleanExpression<Variable>> {
        &self.precondition_var
    }
}

/// Build the disjunction of two conjunctions of boolean expressions as a single
/// boolean expression
fn or_conjunctions<T: Atomic>(
    lhs: Conjunction<BooleanExpression<T>>,
    rhs: Conjunction<BooleanExpression<T>>,
) -> Conjunction<BooleanExpression<T>> {
    // `x || x` is `x`
    if lhs == rhs {
        return lhs;
    }

    // `true || x` is `true`
    if lhs.is_empty() || rhs.is_empty() {
        return Conjunction::default();
    }

    let fold = |conj: Conjunction<BooleanExpression<T>>| {
        conj.into_iter()
            .reduce(|acc, c| {
                BooleanExpression::BinaryExpression(
                    Box::new(acc),
                    BooleanConnective::And,
                    Box::new(c),
                )
            })
            .expect("conjunction is not empty")
    };

    [BooleanExpression::BinaryExpression(
        Box::new(fold(lhs)),
        BooleanConnective::Or,
        Box::new(fold(rhs)),
    )]
    .into()
}

impl And for InitRestriction {
    fn and(self, other: Self) -> Self {
        Self {
            precondition_par: self.precondition_par.and(other.precondition_par),
            precondition_loc: self.precondition_loc.and(other.precondition_loc),
            precondition_var: self.precondition_var.and(other.precondition_var),
        }
    }
}
impl_bitand!(InitRestriction);

impl fmt::Display for InitRestriction {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.is_top() {
            return write!(f, "true");
        }

        let parts = [
            self.precondition_par.to_string(),
            self.precondition_loc.to_string(),
            self.precondition_var.to_string(),
        ];

        write!(
            f,
            "{}",
            join_iterator(parts.iter().filter(|p| !p.is_empty()), " && ")
        )
    }
}

/// Disjunction of `T`.
#[derive(Debug, Clone)]
pub struct Disjunction<T: PartialEq>(Vec<T>);

/// Conjunction of `T`
#[derive(Debug, Clone)]
pub struct Conjunction<T: PartialEq>(Vec<T>);

/// Remove duplicate elements from a vector in place
fn dedup<T: PartialEq>(vec: &mut Vec<T>) {
    let mut write = 0;
    for read in 0..vec.len() {
        // Keep the element only if it does not already occur in the kept prefix
        if !vec[..write].contains(&vec[read]) {
            vec.swap(write, read);
            write += 1;
        }
    }
    vec.truncate(write);
}

impl<T: PartialEq> Disjunction<T> {
    /// Check whether the disjunction has no disjuncts, i.e., is `false`
    pub fn is_empty(&self) -> bool {
        self.0.is_empty()
    }

    /// Returns the number of elements in the disjunction
    pub fn len(&self) -> usize {
        self.0.len()
    }

    /// Create a new empty formula (which is equivalent to `false`)
    pub fn new_bot() -> Self {
        Self(Vec::new())
    }

    /// Check whether the formula is trivially equivalent to false
    pub fn is_bot(&self) -> bool {
        self.0.is_empty()
    }

    /// Get a reference to the disjunct at `index`
    ///
    /// Returns `None` if `index` is out of bounds.
    pub fn get(&self, index: usize) -> Option<&T> {
        self.0.get(index)
    }

    /// Get a mutable reference to the disjunct at `index`
    ///
    /// Returns `None` if `index` is out of bounds.
    pub fn get_mut(&mut self, index: usize) -> Option<&mut T> {
        self.0.get_mut(index)
    }
}

impl<T: PartialEq> Index<usize> for Disjunction<T> {
    type Output = T;

    /// Access the disjunct at the given index
    ///
    /// # Panics
    ///
    /// Panics if `index` is out of bounds.
    fn index(&self, index: usize) -> &Self::Output {
        &self.0[index]
    }
}

impl<T: PartialEq> IndexMut<usize> for Disjunction<T> {
    /// Mutably access the disjunct at the given index
    ///
    /// # Panics
    ///
    /// Panics if `index` is out of bounds.
    fn index_mut(&mut self, index: usize) -> &mut Self::Output {
        &mut self.0[index]
    }
}

impl<T: PartialEq> AsRef<[T]> for Disjunction<T> {
    fn as_ref(&self) -> &[T] {
        &self.0
    }
}

impl<T: PartialEq> AsMut<[T]> for Disjunction<T> {
    fn as_mut(&mut self) -> &mut [T] {
        &mut self.0
    }
}

impl<T: PartialEq> Default for Disjunction<T> {
    /// The empty disjunction, i.e., `false`
    fn default() -> Self {
        Self(Vec::new())
    }
}

impl<T: PartialEq> PartialEq for Disjunction<T> {
    /// Set equality: two disjunctions are equal if they contain the same
    /// disjuncts, regardless of order or duplicates.
    fn eq(&self, other: &Self) -> bool {
        self.0.iter().all(|d| other.0.contains(d)) && other.0.iter().all(|d| self.0.contains(d))
    }
}

impl<T: PartialEq> Or for Disjunction<T> {
    fn or(mut self, other: Self) -> Self {
        self.0.extend(other.0);
        dedup(&mut self.0);
        self
    }
}

impl<T: fmt::Display + PartialEq> fmt::Display for Disjunction<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", join_iterator(self.0.iter(), " || "))
    }
}

impl<T: PartialEq, S: Into<Vec<T>>> From<S> for Disjunction<T> {
    fn from(value: S) -> Self {
        Self(value.into())
    }
}

impl<T: PartialEq> Disjunction<T> {
    /// Iterate over the disjuncts
    pub fn iter(&self) -> std::slice::Iter<'_, T> {
        self.0.iter()
    }

    /// Iterate over the disjuncts, allowing them to be modified
    pub fn iter_mut(&mut self) -> std::slice::IterMut<'_, T> {
        self.0.iter_mut()
    }
}

impl<T: PartialEq> IntoIterator for Disjunction<T> {
    type Item = T;

    type IntoIter = <Vec<T> as IntoIterator>::IntoIter;

    fn into_iter(self) -> Self::IntoIter {
        self.0.into_iter()
    }
}

impl<'a, T: PartialEq> IntoIterator for &'a Disjunction<T> {
    type Item = &'a T;

    type IntoIter = std::slice::Iter<'a, T>;

    fn into_iter(self) -> Self::IntoIter {
        self.0.iter()
    }
}

impl<'a, T: PartialEq> IntoIterator for &'a mut Disjunction<T> {
    type Item = &'a mut T;

    type IntoIter = std::slice::IterMut<'a, T>;

    fn into_iter(self) -> Self::IntoIter {
        self.0.iter_mut()
    }
}

impl<T: PartialEq> FromIterator<T> for Disjunction<T> {
    fn from_iter<I: IntoIterator<Item = T>>(iter: I) -> Self {
        Self(iter.into_iter().collect())
    }
}

impl<T: PartialEq> Conjunction<T> {
    /// Check whether the conjunction has no conjuncts, i.e., is `true`
    pub fn is_empty(&self) -> bool {
        self.0.is_empty()
    }

    /// Returns the number of elements in the conjunction
    pub fn len(&self) -> usize {
        self.0.len()
    }

    /// Get a reference to the conjunct at `index`
    ///
    /// Returns `None` if `index` is out of bounds.
    pub fn get(&self, index: usize) -> Option<&T> {
        self.0.get(index)
    }

    /// Get a mutable reference to the conjunct at `index`
    ///
    /// Returns `None` if `index` is out of bounds.
    pub fn get_mut(&mut self, index: usize) -> Option<&mut T> {
        self.0.get_mut(index)
    }
}

impl<T: PartialEq> Index<usize> for Conjunction<T> {
    type Output = T;

    /// Access the conjunct at the given index
    ///
    /// # Panics
    ///
    /// Panics if `index` is out of bounds.
    fn index(&self, index: usize) -> &Self::Output {
        &self.0[index]
    }
}

impl<T: PartialEq> IndexMut<usize> for Conjunction<T> {
    /// Mutably access the conjunct at the given index
    ///
    /// # Panics
    ///
    /// Panics if `index` is out of bounds.
    fn index_mut(&mut self, index: usize) -> &mut Self::Output {
        &mut self.0[index]
    }
}

impl<T: PartialEq> AsRef<[T]> for Conjunction<T> {
    fn as_ref(&self) -> &[T] {
        &self.0
    }
}

impl<T: PartialEq> AsMut<[T]> for Conjunction<T> {
    fn as_mut(&mut self) -> &mut [T] {
        &mut self.0
    }
}

impl<T: PartialEq> Default for Conjunction<T> {
    /// The empty conjunction, i.e., `true`
    fn default() -> Self {
        Self(Vec::new())
    }
}

impl<T: PartialEq> PartialEq for Conjunction<T> {
    /// Set equality: two conjunctions are equal if they contain the same
    /// conjuncts, regardless of order or duplicates.
    fn eq(&self, other: &Self) -> bool {
        self.0.iter().all(|d| other.0.contains(d)) && other.0.iter().all(|d| self.0.contains(d))
    }
}

impl<T: PartialEq> And for Conjunction<T> {
    fn and(mut self, other: Self) -> Self {
        self.0.extend(other.0);
        dedup(&mut self.0);
        self
    }
}
impl<T: fmt::Display + PartialEq> fmt::Display for Conjunction<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", join_iterator(self.0.iter(), " && "))
    }
}

impl<T: PartialEq, S: Into<Vec<T>>> From<S> for Conjunction<T> {
    fn from(value: S) -> Self {
        Self(value.into())
    }
}

impl<T: PartialEq> Conjunction<T> {
    /// Iterate over the conjuncts
    pub fn iter(&self) -> std::slice::Iter<'_, T> {
        self.0.iter()
    }

    /// Iterate over the conjuncts, allowing them to be modified
    pub fn iter_mut(&mut self) -> std::slice::IterMut<'_, T> {
        self.0.iter_mut()
    }
}

impl<T: PartialEq> IntoIterator for Conjunction<T> {
    type Item = T;

    type IntoIter = <Vec<T> as IntoIterator>::IntoIter;

    fn into_iter(self) -> Self::IntoIter {
        self.0.into_iter()
    }
}

impl<'a, T: PartialEq> IntoIterator for &'a Conjunction<T> {
    type Item = &'a T;

    type IntoIter = std::slice::Iter<'a, T>;

    fn into_iter(self) -> Self::IntoIter {
        self.0.iter()
    }
}

impl<'a, T: PartialEq> IntoIterator for &'a mut Conjunction<T> {
    type Item = &'a mut T;

    type IntoIter = std::slice::IterMut<'a, T>;

    fn into_iter(self) -> Self::IntoIter {
        self.0.iter_mut()
    }
}

impl<T: PartialEq> FromIterator<T> for Conjunction<T> {
    fn from_iter<I: IntoIterator<Item = T>>(iter: I) -> Self {
        Self(iter.into_iter().collect())
    }
}

#[cfg(test)]
mod tests {
    use taco_smt_encoder::SMTSolverBuilder;
    use taco_threshold_automaton::{
        ThresholdAutomaton,
        expressions::{
            And, BooleanConnective, BooleanExpression, ComparisonOp, IntegerExpression, Location,
            Or, Parameter, Variable,
        },
        general_threshold_automaton::builder::GeneralThresholdAutomatonBuilder,
        lia_threshold_automaton::{
            LIAVariableConstraint, integer_thresholds::DeriveFromIntegerComp,
        },
    };

    use crate::{
        SpecificationTrait, TASpecification,
        eltl::ELTLExpression,
        internal_spec::{
            Conjunction, Disjunction, ErrorAtom, ErrorFormula, ErrorSpec, ErrorTarget,
            InitRestriction, upwards_closed_set::UpwardsClosedSet,
        },
    };

    #[test]
    fn test_try_from_eltl_untranslatable_atom() {
        // l1 * l2 is not linear
        let non_linear = |op| {
            Box::new(ELTLExpression::LocationExpr(
                Box::new(
                    IntegerExpression::Atom(Location::new("l1"))
                        * IntegerExpression::Atom(Location::new("l2")),
                ),
                op,
                Box::new(IntegerExpression::Const(1)),
            ))
        };
        let safety = ELTLExpression::Globally(non_linear(ComparisonOp::Lt));
        let liveness = ELTLExpression::Eventually(non_linear(ComparisonOp::Gt));

        // Liveness properties are reported as unknown
        let (specs, unknown) = <ErrorSpec as SpecificationTrait<SMTSolverBuilder>>::try_from_eltl(
            [("live".to_string(), liveness)].into_iter(),
            &SMTSolverBuilder::default(),
        )
        .unwrap();
        assert!(specs.is_empty());
        assert_eq!(unknown, vec!["live".to_string()]);

        // Errors in safety properties abort
        let res = <ErrorSpec as SpecificationTrait<SMTSolverBuilder>>::try_from_eltl(
            [("safe".to_string(), safety)].into_iter(),
            &SMTSolverBuilder::default(),
        );
        assert!(res.is_err());
    }

    #[test]
    fn test_error_spec_accessors_and_display() {
        // [](l1 == 0)
        let eltl = ELTLExpression::Globally(Box::new(ELTLExpression::LocationExpr(
            Box::new(IntegerExpression::Atom(Location::new("l1"))),
            ComparisonOp::Eq,
            Box::new(IntegerExpression::Const(0)),
        )));

        // Violation: <>(l1 >= 1)
        let ef = ErrorFormula::new(
            InitRestriction::new_top(),
            ErrorTarget::new_reach(UpwardsClosedSet::new_cover([Location::new("l1")])),
        );

        let spec = ErrorSpec {
            name: "safety".to_string(),
            source: Box::new(eltl.clone()),
            ef: ef.clone(),
        };

        assert_eq!(spec.name(), "safety");
        assert_eq!(spec.source(), &eltl);
        assert_eq!(spec.error_formula(), &ef);
        assert_eq!(spec.to_string(), "safety: (<>((l1 >= 1)))");
    }

    #[test]
    fn test_create_tas_to_check() {
        let l1 = Location::new("l1");
        let l2 = Location::new("l2");
        let x = Variable::new("x");
        let n = Parameter::new("n");

        let ta = GeneralThresholdAutomatonBuilder::new("ta".to_string())
            .with_parameter(n.clone())
            .unwrap()
            .with_variable(x.clone())
            .unwrap()
            .with_locations([l1.clone(), l2.clone()])
            .unwrap()
            .initialize()
            .build();

        // n > 1
        let par_constr = BooleanExpression::ComparisonExpression(
            Box::new(IntegerExpression::Atom(n.clone())),
            ComparisonOp::Gt,
            Box::new(IntegerExpression::Const(1)),
        );
        // l1 == 0
        let loc_constr = BooleanExpression::ComparisonExpression(
            Box::new(IntegerExpression::Atom(l1.clone())),
            ComparisonOp::Eq,
            Box::new(IntegerExpression::Const(0)),
        );
        // x == 0
        let var_constr = BooleanExpression::ComparisonExpression(
            Box::new(IntegerExpression::Atom(x.clone())),
            ComparisonOp::Eq,
            Box::new(IntegerExpression::Const(0)),
        );

        // (n > 1 && l1 == 0 && x == 0 && <>(l2 >= 1)) || [](l1 >= 1)
        let restricted = ErrorAtom::new(
            InitRestriction::new_parameter_constraint(par_constr.clone())
                & InitRestriction::new_location_constraint(loc_constr.clone())
                & InitRestriction::new_variable_constraint(var_constr.clone()),
            ErrorTarget::new_reach(UpwardsClosedSet::new_cover([l2.clone()])),
        );
        let unrestricted = ErrorAtom::new(
            InitRestriction::new_top(),
            ErrorTarget::new_invariant(UpwardsClosedSet::new_cover([l1.clone()])),
        );

        let spec = ErrorSpec {
            name: "spec".to_string(),
            source: Box::new(ELTLExpression::True),
            ef: Disjunction::from([restricted.clone(), unrestricted.clone()]),
        };

        let got: Vec<_> = spec.create_tas_to_check(&ta).collect();
        assert_eq!(got.len(), 2);

        // The first atom adds its initial restriction to the automaton
        let (target, restricted_ta) = &got[0];
        assert_eq!(target, restricted.target());
        assert_eq!(restricted_ta.name(), "ta");
        assert_eq!(
            restricted_ta.resilience_conditions().collect::<Vec<_>>(),
            vec![&par_constr]
        );
        assert_eq!(
            restricted_ta
                .initial_location_constraints()
                .collect::<Vec<_>>(),
            vec![&loc_constr]
        );
        assert_eq!(
            restricted_ta
                .initial_variable_constraints()
                .collect::<Vec<_>>(),
            vec![&var_constr]
        );

        // The second atom leaves the automaton unchanged
        let (target, unrestricted_ta) = &got[1];
        assert_eq!(target, unrestricted.target());
        assert_eq!(unrestricted_ta, &ta);

        // `transform_threshold_automaton` pairs every atom of every
        // specification with a copy of the automaton
        let got =
            <ErrorSpec as SpecificationTrait<SMTSolverBuilder>>::transform_threshold_automaton(
                ta.clone(),
                vec![spec.clone(), spec],
                &SMTSolverBuilder::default(),
            );
        assert_eq!(got.len(), 4);
        assert_eq!(
            (got[0].0.as_str(), &got[0].1),
            ("spec", restricted.target())
        );
        assert_eq!(
            (got[1].0.as_str(), &got[1].1),
            ("spec", unrestricted.target())
        );
        assert_eq!(
            (got[2].0.as_str(), &got[2].1),
            ("spec", restricted.target())
        );
        assert_eq!(
            (got[3].0.as_str(), &got[3].1),
            ("spec", unrestricted.target())
        );
    }

    #[test]
    fn test_error_atom_accessors_and_predicates() {
        // l1 == 0
        let loc_constr = BooleanExpression::ComparisonExpression(
            Box::new(IntegerExpression::Atom(Location::new("l1"))),
            ComparisonOp::Eq,
            Box::new(IntegerExpression::Const(0)),
        );
        let init = InitRestriction::new_location_constraint(loc_constr);
        let target = ErrorTarget::new_reach(UpwardsClosedSet::new_cover([Location::new("l2")]));

        let atom = ErrorAtom::new(init.clone(), target.clone());
        assert_eq!(atom.init_restriction(), &init);
        assert_eq!(atom.target(), &target);
        assert!(!atom.is_top());
        assert!(!atom.is_bot());

        // Only an atom without restriction and without temporal part is top
        assert!(ErrorAtom::new(InitRestriction::new_top(), ErrorTarget::Top).is_top());
        assert!(!ErrorAtom::new(init.clone(), ErrorTarget::Top).is_top());
        assert!(
            !ErrorAtom::new(
                InitRestriction::new_top(),
                ErrorTarget::new_reach(UpwardsClosedSet::new_top())
            )
            .is_top()
        );

        // An atom is bot if the temporal part is unsatisfiable
        assert!(
            ErrorAtom::new(
                InitRestriction::new_top(),
                ErrorTarget::new_reach(UpwardsClosedSet::new_bot())
            )
            .is_bot()
        );
    }

    #[test]
    fn test_error_atom_display() {
        let target = ErrorTarget::new_reach(UpwardsClosedSet::new_cover([Location::new("l2")]));

        // Restriction is omitted if it is top
        let atom = ErrorAtom::new(InitRestriction::new_top(), target.clone());
        assert_eq!(atom.to_string(), "(<>((l2 >= 1)))");

        // l1 == 0
        let loc_constr = BooleanExpression::ComparisonExpression(
            Box::new(IntegerExpression::Atom(Location::new("l1"))),
            ComparisonOp::Eq,
            Box::new(IntegerExpression::Const(0)),
        );
        let atom = ErrorAtom::new(InitRestriction::new_location_constraint(loc_constr), target);
        assert_eq!(atom.to_string(), "(l1 == 0) && (<>((l2 >= 1)))");
    }

    #[test]
    fn test_ta_specification_for_atom_formula_and_target() {
        // x >= 1
        let x_geq_1 = LIAVariableConstraint::from_integer_expr(
            IntegerExpression::Atom(Variable::new("x")),
            ComparisonOp::Geq,
            IntegerExpression::Const(1),
        )
        .unwrap();
        // y >= 2
        let y_geq_2 = LIAVariableConstraint::from_integer_expr(
            IntegerExpression::Atom(Variable::new("y")),
            ComparisonOp::Geq,
            IntegerExpression::Const(2),
        )
        .unwrap();

        let pre = UpwardsClosedSet::new_cover([Location::new("l1")])
            & UpwardsClosedSet::new_var_constraint(x_geq_1.clone());
        let inv = UpwardsClosedSet::new_cover([Location::new("l2")])
            & UpwardsClosedSet::new_var_constraint(y_geq_2.clone());

        // Target with two sets: both are reported
        let target = ErrorTarget::new_ensure(pre.clone(), inv.clone());
        let mut locs: Vec<_> = target.locs_appearing().into_iter().collect();
        locs.sort();
        assert_eq!(locs, vec![&Location::new("l1"), &Location::new("l2")]);
        assert_eq!(
            target.var_constraint().into_iter().collect::<Vec<_>>(),
            vec![&x_geq_1, &y_geq_2]
        );

        // Target with one set reports that set
        let reach = ErrorTarget::new_reach(pre.clone());
        assert_eq!(
            reach.locs_appearing().into_iter().collect::<Vec<_>>(),
            vec![&Location::new("l1")]
        );
        assert_eq!(
            reach.var_constraint().into_iter().collect::<Vec<_>>(),
            vec![&x_geq_1]
        );

        // Target without temporal part reports nothing
        assert_eq!(ErrorTarget::Top.locs_appearing().into_iter().count(), 0);
        assert_eq!(ErrorTarget::Top.var_constraint().into_iter().count(), 0);
        let atom = ErrorAtom::new(InitRestriction::new_top(), ErrorTarget::Top);
        assert_eq!(atom.locs_appearing().into_iter().count(), 0);
        assert_eq!(atom.var_constraint().into_iter().count(), 0);

        // The atom delegates to its target
        let atom = ErrorAtom::new(InitRestriction::new_top(), target);
        let mut locs: Vec<_> = atom.locs_appearing().into_iter().collect();
        locs.sort();
        assert_eq!(locs, vec![&Location::new("l1"), &Location::new("l2")]);
        assert_eq!(
            atom.var_constraint().into_iter().collect::<Vec<_>>(),
            vec![&x_geq_1, &y_geq_2]
        );

        // The formula takes the union over all disjuncts
        let formula: ErrorFormula = Disjunction::from([
            ErrorAtom::new(InitRestriction::new_top(), ErrorTarget::new_reach(pre)),
            ErrorAtom::new(InitRestriction::new_top(), ErrorTarget::new_invariant(inv)),
        ]);
        let mut locs: Vec<_> = formula.locs_appearing().into_iter().collect();
        locs.sort();
        assert_eq!(locs, vec![&Location::new("l1"), &Location::new("l2")]);
        assert_eq!(
            formula.var_constraint().into_iter().collect::<Vec<_>>(),
            vec![&x_geq_1, &y_geq_2]
        );
    }

    #[test]
    fn test_error_target_constructors() {
        let a = UpwardsClosedSet::new_cover([Location::new("l1")]);
        let b = UpwardsClosedSet::new_cover([Location::new("l2")]);

        assert_eq!(
            ErrorTarget::new_reach(a.clone()),
            ErrorTarget::Reach(a.clone())
        );
        assert_eq!(
            ErrorTarget::new_invariant(a.clone()),
            ErrorTarget::Invariant(a.clone())
        );
        assert_eq!(
            ErrorTarget::new_ensure(a.clone(), b.clone()),
            ErrorTarget::Ensure {
                pre: a.clone(),
                inv: b.clone()
            }
        );
        assert_eq!(
            ErrorTarget::new_repeat(a.clone(), b.clone()),
            ErrorTarget::Repeat { pre: a, inv: b }
        );
    }

    #[test]
    fn test_error_target_is_bot() {
        let set = UpwardsClosedSet::new_cover([Location::new("l1")]);
        let bot = UpwardsClosedSet::new_bot();

        assert!(!ErrorTarget::new_reach(set.clone()).is_bot());
        assert!(ErrorTarget::new_reach(bot.clone()).is_bot());

        assert!(!ErrorTarget::new_invariant(set.clone()).is_bot());
        assert!(ErrorTarget::new_invariant(bot.clone()).is_bot());

        // A target with two sets is bot if one of them is bot
        assert!(!ErrorTarget::new_ensure(set.clone(), set.clone()).is_bot());
        assert!(ErrorTarget::new_ensure(bot.clone(), set.clone()).is_bot());
        assert!(ErrorTarget::new_ensure(set.clone(), bot.clone()).is_bot());

        assert!(!ErrorTarget::new_repeat(set.clone(), set.clone()).is_bot());
        assert!(ErrorTarget::new_repeat(bot.clone(), set.clone()).is_bot());
        assert!(ErrorTarget::new_repeat(set, bot).is_bot());

        assert!(!ErrorTarget::Top.is_bot());
    }

    #[test]
    fn test_error_target_is_top() {
        let set = UpwardsClosedSet::new_cover([Location::new("l1")]);
        let top = UpwardsClosedSet::new_top();

        assert!(!ErrorTarget::new_reach(set.clone()).is_top());
        assert!(ErrorTarget::new_reach(top.clone()).is_top());

        assert!(!ErrorTarget::new_invariant(set.clone()).is_top());
        assert!(ErrorTarget::new_invariant(top.clone()).is_top());

        // A target with two sets is top only if both of them are top
        assert!(ErrorTarget::new_ensure(top.clone(), top.clone()).is_top());
        assert!(!ErrorTarget::new_ensure(set.clone(), top.clone()).is_top());
        assert!(!ErrorTarget::new_ensure(top.clone(), set.clone()).is_top());

        assert!(ErrorTarget::new_repeat(top.clone(), top.clone()).is_top());
        assert!(!ErrorTarget::new_repeat(set.clone(), top.clone()).is_top());
        assert!(!ErrorTarget::new_repeat(top, set).is_top());

        assert!(ErrorTarget::Top.is_top());
    }

    #[test]
    fn test_error_target_contains_reachability_constraint() {
        // l1 >= 1 && l2 == 0
        let reach = UpwardsClosedSet::new_reach([(Location::new("l1"), 1)], [Location::new("l2")]);
        // l1 >= 1
        let cover = UpwardsClosedSet::new_cover([Location::new("l1")]);

        assert!(ErrorTarget::new_reach(reach.clone()).contains_reachability_constraint());
        assert!(!ErrorTarget::new_reach(cover.clone()).contains_reachability_constraint());

        // Not implemented for the other temporal targets
        assert!(!ErrorTarget::new_invariant(reach.clone()).contains_reachability_constraint());
        assert!(
            !ErrorTarget::new_ensure(reach.clone(), reach.clone())
                .contains_reachability_constraint()
        );
        assert!(!ErrorTarget::new_repeat(reach.clone(), reach).contains_reachability_constraint());

        assert!(!ErrorTarget::Top.contains_reachability_constraint());
    }

    #[test]
    fn test_error_target_display() {
        let a = UpwardsClosedSet::new_cover([Location::new("l1")]);
        let b = UpwardsClosedSet::new_cover([Location::new("l2")]);

        assert_eq!(
            ErrorTarget::new_reach(a.clone()).to_string(),
            "<>((l1 >= 1))"
        );
        assert_eq!(
            ErrorTarget::new_invariant(a.clone()).to_string(),
            "[]((l1 >= 1))"
        );
        assert_eq!(
            ErrorTarget::new_ensure(a.clone(), b.clone()).to_string(),
            "<>(((l1 >= 1)) && []((l2 >= 1)))"
        );
        assert_eq!(
            ErrorTarget::new_repeat(a, b).to_string(),
            "[](((l1 >= 1)) && <>((l2 >= 1)))"
        );
        assert_eq!(ErrorTarget::Top.to_string(), "true");
    }

    #[test]
    fn test_init_restriction_constructors_and_accessors() {
        let top = InitRestriction::new_top();
        assert!(top.is_top());
        assert!(top.parameter_constraints().is_empty());
        assert!(top.location_constraints().is_empty());
        assert!(top.variable_constraints().is_empty());

        // n > 1
        let par_constr = BooleanExpression::ComparisonExpression(
            Box::new(IntegerExpression::Atom(Parameter::new("n"))),
            ComparisonOp::Gt,
            Box::new(IntegerExpression::Const(1)),
        );
        let par = InitRestriction::new_parameter_constraint(par_constr.clone());
        assert!(!par.is_top());
        assert_eq!(
            par.parameter_constraints(),
            &Conjunction::from([par_constr])
        );
        assert!(par.location_constraints().is_empty());
        assert!(par.variable_constraints().is_empty());

        // l1 == 0
        let loc_constr = BooleanExpression::ComparisonExpression(
            Box::new(IntegerExpression::Atom(Location::new("l1"))),
            ComparisonOp::Eq,
            Box::new(IntegerExpression::Const(0)),
        );
        let loc = InitRestriction::new_location_constraint(loc_constr.clone());
        assert!(!loc.is_top());
        assert!(loc.parameter_constraints().is_empty());
        assert_eq!(loc.location_constraints(), &Conjunction::from([loc_constr]));
        assert!(loc.variable_constraints().is_empty());

        // x == 0
        let var_constr = BooleanExpression::ComparisonExpression(
            Box::new(IntegerExpression::Atom(Variable::new("x"))),
            ComparisonOp::Eq,
            Box::new(IntegerExpression::Const(0)),
        );
        let var = InitRestriction::new_variable_constraint(var_constr.clone());
        assert!(!var.is_top());
        assert!(var.parameter_constraints().is_empty());
        assert!(var.location_constraints().is_empty());
        assert_eq!(var.variable_constraints(), &Conjunction::from([var_constr]));
    }

    #[test]
    fn test_init_restriction_and() {
        // n > 1
        let par_constr = BooleanExpression::ComparisonExpression(
            Box::new(IntegerExpression::Atom(Parameter::new("n"))),
            ComparisonOp::Gt,
            Box::new(IntegerExpression::Const(1)),
        );
        // l1 == 0
        let loc_constr = BooleanExpression::ComparisonExpression(
            Box::new(IntegerExpression::Atom(Location::new("l1"))),
            ComparisonOp::Eq,
            Box::new(IntegerExpression::Const(0)),
        );
        // l2 == 0
        let loc_constr_2 = BooleanExpression::ComparisonExpression(
            Box::new(IntegerExpression::Atom(Location::new("l2"))),
            ComparisonOp::Eq,
            Box::new(IntegerExpression::Const(0)),
        );

        let got = InitRestriction::new_parameter_constraint(par_constr.clone())
            .and(InitRestriction::new_location_constraint(loc_constr.clone()))
            & InitRestriction::new_location_constraint(loc_constr_2.clone());

        let expected = InitRestriction {
            precondition_par: [par_constr].into(),
            precondition_loc: [loc_constr.clone(), loc_constr_2].into(),
            precondition_var: Conjunction::default(),
        };
        assert_eq!(got, expected);

        // Conjunction with top and with itself changes nothing
        let loc = InitRestriction::new_location_constraint(loc_constr);
        assert_eq!(loc.clone() & InitRestriction::new_top(), loc);
        assert_eq!(loc.clone() & loc.clone(), loc);
    }

    #[test]
    fn test_init_restriction_try_or() {
        // n > 1
        let par_constr = BooleanExpression::ComparisonExpression(
            Box::new(IntegerExpression::Atom(Parameter::new("n"))),
            ComparisonOp::Gt,
            Box::new(IntegerExpression::Const(1)),
        );
        // l1 == 0
        let loc_constr_1 = BooleanExpression::ComparisonExpression(
            Box::new(IntegerExpression::Atom(Location::new("l1"))),
            ComparisonOp::Eq,
            Box::new(IntegerExpression::Const(0)),
        );
        // l2 == 0
        let loc_constr_2 = BooleanExpression::ComparisonExpression(
            Box::new(IntegerExpression::Atom(Location::new("l2"))),
            ComparisonOp::Eq,
            Box::new(IntegerExpression::Const(0)),
        );
        // x == 0
        let var_constr = BooleanExpression::ComparisonExpression(
            Box::new(IntegerExpression::Atom(Variable::new("x"))),
            ComparisonOp::Eq,
            Box::new(IntegerExpression::Const(0)),
        );

        let par = InitRestriction::new_parameter_constraint(par_constr.clone());
        let loc_1 = InitRestriction::new_location_constraint(loc_constr_1.clone());
        let loc_2 = InitRestriction::new_location_constraint(loc_constr_2.clone());
        let var = InitRestriction::new_variable_constraint(var_constr.clone());

        // `x || x` is `x`
        assert_eq!(loc_1.try_or(&loc_1), Some(loc_1.clone()));

        // `(p && l1) || (p && l2)` is `p && (l1 || l2)`
        let got = (par.clone() & loc_1.clone()).try_or(&(par.clone() & loc_2.clone()));
        let expected = InitRestriction {
            precondition_par: [par_constr].into(),
            precondition_loc: [BooleanExpression::BinaryExpression(
                Box::new(loc_constr_1.clone()),
                BooleanConnective::Or,
                Box::new(loc_constr_2.clone()),
            )]
            .into(),
            precondition_var: Conjunction::default(),
        };
        assert_eq!(got, Some(expected));

        // `(l1 && l2) || l1` is `(l1 && l2) || l1`, the conjunction is folded
        // into a single expression
        let got = (loc_1.clone() & loc_2.clone()).try_or(&loc_1);
        let expected = InitRestriction {
            precondition_par: Conjunction::default(),
            precondition_loc: [BooleanExpression::BinaryExpression(
                Box::new(BooleanExpression::BinaryExpression(
                    Box::new(loc_constr_1.clone()),
                    BooleanConnective::And,
                    Box::new(loc_constr_2.clone()),
                )),
                BooleanConnective::Or,
                Box::new(loc_constr_1.clone()),
            )]
            .into(),
            precondition_var: Conjunction::default(),
        };
        assert_eq!(got, Some(expected));

        // `true || l1` is `true`
        assert_eq!(
            InitRestriction::new_top().try_or(&loc_1),
            Some(InitRestriction::new_top())
        );
        assert_eq!(
            loc_1.try_or(&InitRestriction::new_top()),
            Some(InitRestriction::new_top())
        );

        // `(l1 && x) || (l2 && p)` differs in more than one kind
        assert_eq!((loc_1.clone() & var.clone()).try_or(&(loc_2 & par)), None);

        // `l1 || x` differs in two kinds as well
        assert_eq!(loc_1.try_or(&var), None);
    }

    #[test]
    fn test_init_restriction_display() {
        assert_eq!(InitRestriction::new_top().to_string(), "true");

        // n > 1
        let par_constr = BooleanExpression::ComparisonExpression(
            Box::new(IntegerExpression::Atom(Parameter::new("n"))),
            ComparisonOp::Gt,
            Box::new(IntegerExpression::Const(1)),
        );
        // l1 == 0
        let loc_constr = BooleanExpression::ComparisonExpression(
            Box::new(IntegerExpression::Atom(Location::new("l1"))),
            ComparisonOp::Eq,
            Box::new(IntegerExpression::Const(0)),
        );
        // x == 0
        let var_constr = BooleanExpression::ComparisonExpression(
            Box::new(IntegerExpression::Atom(Variable::new("x"))),
            ComparisonOp::Eq,
            Box::new(IntegerExpression::Const(0)),
        );

        assert_eq!(
            InitRestriction::new_location_constraint(loc_constr.clone()).to_string(),
            "l1 == 0"
        );

        // Empty kinds are skipped
        let all = InitRestriction::new_parameter_constraint(par_constr)
            & InitRestriction::new_location_constraint(loc_constr)
            & InitRestriction::new_variable_constraint(var_constr);
        assert_eq!(all.to_string(), "n > 1 && l1 == 0 && x == 0");
    }

    #[test]
    fn test_disjunction_construction_and_predicates() {
        let bot: Disjunction<i32> = Disjunction::new_bot();
        assert!(bot.is_bot());
        assert!(bot.is_empty());
        assert_eq!(bot.len(), 0);
        assert_eq!(bot, Disjunction::default());

        let disj = Disjunction::from([1, 2, 3]);
        assert!(!disj.is_bot());
        assert!(!disj.is_empty());
        assert_eq!(disj.len(), 3);

        // `From` and `FromIterator` give the same result
        assert_eq!(disj, [1, 2, 3].into_iter().collect::<Disjunction<_>>());
    }

    #[test]
    fn test_disjunction_element_access() {
        let mut disj = Disjunction::from([1, 2, 3]);

        assert_eq!(disj.get(1), Some(&2));
        assert_eq!(disj.get(3), None);
        assert_eq!(disj[0], 1);
        assert_eq!(disj.as_ref(), &[1, 2, 3]);

        *disj.get_mut(1).unwrap() = 20;
        assert_eq!(disj.get_mut(3), None);
        disj[0] = 10;
        disj.as_mut()[2] = 30;
        assert_eq!(disj.as_ref(), &[10, 20, 30]);
    }

    #[test]
    fn test_disjunction_iteration() {
        let mut disj = Disjunction::from([1, 2, 3]);

        assert_eq!(disj.iter().copied().collect::<Vec<_>>(), vec![1, 2, 3]);
        assert_eq!(
            (&disj).into_iter().copied().collect::<Vec<_>>(),
            vec![1, 2, 3]
        );

        disj.iter_mut().for_each(|d| *d += 1);
        assert_eq!(disj.as_ref(), &[2, 3, 4]);

        (&mut disj).into_iter().for_each(|d| *d *= 10);
        assert_eq!(disj.as_ref(), &[20, 30, 40]);

        assert_eq!(disj.into_iter().collect::<Vec<_>>(), vec![20, 30, 40]);
    }

    #[test]
    fn test_disjunction_eq_or_and_display() {
        // Equality ignores order and duplicates
        assert_eq!(Disjunction::from([1, 2]), Disjunction::from([2, 1, 1]));
        assert_ne!(Disjunction::from([1, 2]), Disjunction::from([1]));

        // `Or` concatenates and removes duplicates, keeping the first occurrence
        let got = Disjunction::from([1, 2]).or(Disjunction::from([2, 3]));
        assert_eq!(got.as_ref(), &[1, 2, 3]);

        assert_eq!(Disjunction::from([1, 2, 3]).to_string(), "1 || 2 || 3");
        assert_eq!(Disjunction::<i32>::new_bot().to_string(), "");
    }

    #[test]
    fn test_conjunction_construction_and_predicates() {
        let top: Conjunction<i32> = Conjunction::default();
        assert!(top.is_empty());
        assert_eq!(top.len(), 0);

        let conj = Conjunction::from([1, 2, 3]);
        assert!(!conj.is_empty());
        assert_eq!(conj.len(), 3);

        // `From` and `FromIterator` give the same result
        assert_eq!(conj, [1, 2, 3].into_iter().collect::<Conjunction<_>>());
    }

    #[test]
    fn test_conjunction_element_access() {
        let mut conj = Conjunction::from([1, 2, 3]);

        assert_eq!(conj.get(1), Some(&2));
        assert_eq!(conj.get(3), None);
        assert_eq!(conj[0], 1);
        assert_eq!(conj.as_ref(), &[1, 2, 3]);

        *conj.get_mut(1).unwrap() = 20;
        assert_eq!(conj.get_mut(3), None);
        conj[0] = 10;
        conj.as_mut()[2] = 30;
        assert_eq!(conj.as_ref(), &[10, 20, 30]);
    }

    #[test]
    fn test_conjunction_iteration() {
        let mut conj = Conjunction::from([1, 2, 3]);

        assert_eq!(conj.iter().copied().collect::<Vec<_>>(), vec![1, 2, 3]);
        assert_eq!(
            (&conj).into_iter().copied().collect::<Vec<_>>(),
            vec![1, 2, 3]
        );

        conj.iter_mut().for_each(|c| *c += 1);
        assert_eq!(conj.as_ref(), &[2, 3, 4]);

        (&mut conj).into_iter().for_each(|c| *c *= 10);
        assert_eq!(conj.as_ref(), &[20, 30, 40]);

        assert_eq!(conj.into_iter().collect::<Vec<_>>(), vec![20, 30, 40]);
    }

    #[test]
    fn test_conjunction_eq_and_and_display() {
        // Equality ignores order and duplicates
        assert_eq!(Conjunction::from([1, 2]), Conjunction::from([2, 1, 1]));
        assert_ne!(Conjunction::from([1, 2]), Conjunction::from([1]));

        // `And` concatenates and removes duplicates, keeping the first occurrence
        let got = Conjunction::from([1, 2]).and(Conjunction::from([2, 3]));
        assert_eq!(got.as_ref(), &[1, 2, 3]);

        assert_eq!(Conjunction::from([1, 2, 3]).to_string(), "1 && 2 && 3");
        assert_eq!(Conjunction::<i32>::default().to_string(), "");
    }
}
