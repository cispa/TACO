//! Encoding of expressions into [`SMTExpr`]
//!
//! This module provides traits and types to encode boolean or integer
//! expressions into SMT expressions. The encoding is done using the `easy-smt`
//! crate, therefore the expressions are encoded into `SExpr` types.

use std::{collections::HashMap, fmt, io};

use std::hash::Hash;

use easy_smt::SExpr;
use taco_threshold_automaton::{
    RuleDefinition,
    expressions::{
        Atomic, BooleanConnective, BooleanExpression, ComparisonOp, IntegerExpression, IntegerOp,
        Location, Parameter, Variable,
    },
    general_threshold_automaton::Rule,
};

use crate::{SMTExpr, SMTSolution, SMTSolver, SMTSolverBuilder, SMTSolverContext};

pub mod config_ctx;
pub mod ctx_mgr;
pub mod step_ctx;
pub mod ta_encoding;

/// Trait defining the encoding of type `T` into an S[`SMTExpr`] given a context
///
/// If this trait is implemented for a type `T`, expressions of type `T` can be
/// encoded into an SMT expression, using the given SMT solver and context of
/// type `C`. This trait does not restrict the type of the context.
pub trait EncodeToSMT<T, C> {
    /// Encode the type into an SMT expression
    ///
    /// Encode the expression of type `T` into an SMT expression using the
    /// given SMT solver and context of type `C`.
    fn encode_to_smt_with_ctx(
        &self,
        solver: &SMTSolver,
        ctx: &C,
    ) -> Result<SMTExpr, SMTSolverError>;
}

/// Trait of a context that provides mapping from type declaring SMT variables
/// `T` to  associated SMT expression
///
/// This trait is implemented by contexts that can provide the corresponding
/// [`SMTExpr`] for a given expression stored in the context. Implementing
/// this trait allows to encode integer and boolean expressions into
/// [`SMTExpr`]s.
pub trait SMTVariableContext<T> {
    /// Get the corresponding [`SMTExpr`] for the given expression of type
    /// `T`
    ///
    /// This function returns an error if the expression is not stored in the
    /// context, or it tried to declare a variable and the connection to the
    /// SMT solver broke.
    fn get_expr_for(&self, expr: &T) -> Result<SMTExpr, SMTSolverError>;

    /// Get all expressions for which the current context holds an assignment
    fn get_exprs<'a>(&'a self) -> impl IntoIterator<Item = &'a T>
    where
        T: 'a;

    /// Get the solution assignment
    fn get_solution<'a>(
        &'a self,
        solver: &mut SMTSolver,
        res: SMTSolution,
    ) -> Result<HashMap<T, u32>, SMTSolverError>
    where
        T: 'a + Eq + Hash + Clone,
    {
        match res {
            SMTSolution::UNSAT => Err(SMTSolverError::ExtractionFromUnsat),
            SMTSolution::SAT => {
                let expr_vec = self
                    .get_exprs()
                    .into_iter()
                    .map(|t| self.get_expr_for(t))
                    .collect::<Result<Vec<_>, _>>()?;

                let solution = solver.get_value(expr_vec)?;

                solution
                    .into_iter()
                    .zip(self.get_exprs())
                    .map(|((_, sol), t)| {
                        let solution_value = solver.get_u32(sol).ok_or_else(|| {
                            let sol = solver.display(sol);
                            SMTSolverError::SolutionExtractionParseIntError(sol.to_string())
                        })?;

                        Ok((t.clone(), solution_value))
                    })
                    .collect::<Result<HashMap<T, u32>, SMTSolverError>>()
            }
        }
    }
}

impl<T: Hash + Eq + DeclaresVariable> SMTVariableContext<T> for HashMap<T, SExpr> {
    fn get_expr_for(&self, expr: &T) -> Result<SMTExpr, SMTSolverError> {
        self.get(expr)
            .ok_or_else(|| expr.get_undeclared_error())
            .copied()
    }

    fn get_exprs<'a>(&'a self) -> impl IntoIterator<Item = &'a T>
    where
        T: 'a,
    {
        self.keys()
    }
}

/// Trait for types that have associated SMT variables
///
/// This trait is implemented by types that are usually encoded as variables
/// when constructing formulas over threshold automata. A type implementing this
/// trait needs to provide a naming scheme for the smt variables associated with
/// the type and a method to construct an error if the variable is not declared.
pub trait DeclaresVariable {
    /// Get the name of the associated variable for the given index
    ///
    /// This function should return the name of the variable associated with
    /// the type for the given index. The naming scheme **must** result in a
    /// unique name across all variables used in the SMT solver.
    ///
    /// The `index` field is used for variables that are usually indexed. For
    /// example, along a path, the location variable (representing the number of
    /// processes in this location) is usually indexed by the configuration.
    fn get_name(&self, index: u32) -> String;

    /// Declare the variable in the SMT solver
    ///
    /// This function declares the variable in the SMT solver and returns the
    /// SMT expression. Returns an error if the connection to the SMT solver
    /// broke.
    fn declare_variable(
        &self,
        solver: &mut SMTSolver,
        index: u32,
    ) -> Result<SMTExpr, SMTSolverError> {
        let name = self.get_name(index);
        Ok(solver.declare_const(&name, solver.int_sort())?)
    }

    /// Returns an error indicating that `self` was not declared in the current
    /// SMT context.
    fn get_undeclared_error(&self) -> SMTSolverError;
}

impl DeclaresVariable for Location {
    fn get_name(&self, index: u32) -> String {
        format!("loc_{}_{}", self.name(), index)
    }

    fn get_undeclared_error(&self) -> SMTSolverError {
        SMTSolverError::UndeclaredLocation(self.clone())
    }
}

impl DeclaresVariable for Parameter {
    fn get_name(&self, _index: u32) -> String {
        format!("param_{}", self.name())
    }

    fn get_undeclared_error(&self) -> SMTSolverError {
        SMTSolverError::UndeclaredParameter(self.clone())
    }
}

impl DeclaresVariable for Variable {
    fn get_name(&self, index: u32) -> String {
        format!("var_{}_{}", self.name(), index)
    }

    fn get_undeclared_error(&self) -> SMTSolverError {
        SMTSolverError::UndeclaredVariable(self.clone())
    }
}

impl DeclaresVariable for Rule {
    fn get_name(&self, index: u32) -> String {
        format!("rule_{}_{}", self.id(), index)
    }

    fn get_undeclared_error(&self) -> SMTSolverError {
        SMTSolverError::UndeclaredRule(self.clone())
    }
}

/// Trait that allows to extract the assignment of a variable from the solution
/// found by the SMT solver
///
/// This trait is implemented by contexts allowing to extract the solution found
/// by the SMT solver for a given variable.
pub trait GetAssignment<T>: SMTVariableContext<T> + SMTSolverContext
where
    T: DeclaresVariable,
{
    /// Get the assigned solution of the variable
    ///
    /// This function returns the assignment of the variable from the SMT
    /// solver. If the query is unsatisfiable, it returns `None`. If the query
    /// is satisfiable, it returns the assigned value.
    ///
    /// Returns an error if the connection to the SMT solver broke.
    fn get_assignment(&mut self, res: SMTSolution, var: &T) -> Result<Option<u64>, SMTSolverError> {
        match res {
            SMTSolution::SAT => {
                let expr = self.get_expr_for(var)?;
                let solver = self.get_smt_solver_mut();

                let solution = solver.get_value(vec![expr])?;
                debug_assert!(solution.len() == 1);
                debug_assert!(solution[0].0 == expr);

                let solution_int = solver.get_u64(solution[0].1);

                let sol = solution_int.ok_or_else(|| {
                    let sol = solver.display(expr);
                    SMTSolverError::SolutionExtractionParseIntError(sol.to_string())
                })?;

                Ok(Some(sol))
            }
            SMTSolution::UNSAT => Err(SMTSolverError::ExtractionFromUnsat),
        }
    }
}

impl<T, U> EncodeToSMT<IntegerExpression<T>, U> for IntegerExpression<T>
where
    U: SMTVariableContext<T> + SMTVariableContext<Parameter>,
    T: DeclaresVariable + Atomic,
{
    fn encode_to_smt_with_ctx(&self, solver: &SMTSolver, ctx: &U) -> Result<SExpr, SMTSolverError> {
        match self {
            IntegerExpression::Atom(a) => ctx.get_expr_for(a),
            IntegerExpression::Const(c) => Ok(solver.numeral(*c)),
            IntegerExpression::Param(parameter) => ctx.get_expr_for(parameter),
            IntegerExpression::BinaryExpr(lhs, op, rhs) => {
                let lhs = lhs.encode_to_smt_with_ctx(solver, ctx)?;
                let rhs = rhs.encode_to_smt_with_ctx(solver, ctx)?;

                Ok(match op {
                    IntegerOp::Add => solver.plus(lhs, rhs),
                    IntegerOp::Sub => solver.sub(lhs, rhs),
                    IntegerOp::Mul => solver.times(lhs, rhs),
                    IntegerOp::Div => solver.div(lhs, rhs),
                })
            }
            IntegerExpression::Neg(expr) => {
                let expr = expr.encode_to_smt_with_ctx(solver, ctx)?;
                Ok(solver.negate(expr))
            }
        }
    }
}

impl<T, U> EncodeToSMT<BooleanExpression<T>, U> for BooleanExpression<T>
where
    U: SMTVariableContext<T> + SMTVariableContext<Parameter>,
    T: DeclaresVariable + Atomic,
{
    fn encode_to_smt_with_ctx(&self, solver: &SMTSolver, ctx: &U) -> Result<SExpr, SMTSolverError> {
        match self {
            BooleanExpression::ComparisonExpression(lhs, op, rhs) => {
                let lhs = lhs.encode_to_smt_with_ctx(solver, ctx)?;
                let rhs = rhs.encode_to_smt_with_ctx(solver, ctx)?;

                Ok(match op {
                    ComparisonOp::Gt => solver.gt(lhs, rhs),
                    ComparisonOp::Geq => solver.gte(lhs, rhs),
                    ComparisonOp::Eq => solver.eq(lhs, rhs),
                    ComparisonOp::Neq => solver.not(solver.eq(lhs, rhs)),
                    ComparisonOp::Leq => solver.lte(lhs, rhs),
                    ComparisonOp::Lt => solver.lt(lhs, rhs),
                })
            }
            BooleanExpression::BinaryExpression(lhs, op, rhs) => {
                let lhs = lhs.encode_to_smt_with_ctx(solver, ctx)?;
                let rhs = rhs.encode_to_smt_with_ctx(solver, ctx)?;

                Ok(match op {
                    BooleanConnective::And => solver.and(lhs, rhs),
                    BooleanConnective::Or => solver.or(lhs, rhs),
                })
            }
            BooleanExpression::Not(expr) => {
                let expr = expr.encode_to_smt_with_ctx(solver, ctx)?;

                Ok(solver.not(expr))
            }
            BooleanExpression::True => Ok(solver.true_()),
            BooleanExpression::False => Ok(solver.false_()),
        }
    }
}

/// Error occurring in the interaction with the SMT solver
#[derive(Debug)]
pub enum SMTSolverError {
    /// Error from the SMT solver
    EasySMTErr(io::Error),
    /// Timeout in the SMT solver
    SolverTimeout,
    /// Undeclared Parameter accessed
    UndeclaredParameter(Parameter),
    /// Undeclared Location accessed
    UndeclaredLocation(Location),
    /// Undeclared Variable accessed
    UndeclaredVariable(Variable),
    /// Failed to parse integer from solution
    SolutionExtractionParseIntError(String),
    /// Undeclared Rule accessed
    UndeclaredRule(Rule),
    /// Attempted to extract solution from an unsatisfiable expression
    ExtractionFromUnsat,
    /// Specification is trivially unsatisfiable, reason in spec
    TriviallyUnsat(String),
}

impl std::error::Error for SMTSolverError {}

impl fmt::Display for SMTSolverError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            SMTSolverError::EasySMTErr(err) => {
                write!(f, "Error from connection to SMT solver: {err}")
            }
            SMTSolverError::UndeclaredParameter(param) => {
                write!(f, "Undeclared parameter: {param}")
            }
            SMTSolverError::UndeclaredLocation(location) => {
                write!(f, "Undeclared location: {location}")
            }
            SMTSolverError::UndeclaredVariable(variable) => {
                write!(f, "Undeclared variable: {variable}")
            }
            SMTSolverError::SolverTimeout => write!(f, "Timeout in SMT solver"),
            SMTSolverError::SolutionExtractionParseIntError(s) => write!(
                f,
                "Failed to parse SMT solver supplied solution into integer: {s} not an integer"
            ),
            SMTSolverError::UndeclaredRule(rule) => write!(f, "Undeclared rule: {rule}"),
            SMTSolverError::ExtractionFromUnsat => write!(
                f,
                "Attempted to extract the solution assignment from an unsatisfiable expression"
            ),
            SMTSolverError::TriviallyUnsat(r) => {
                write!(f, "Specification can never be true. Reason: {r}")
            }
        }
    }
}

impl From<io::Error> for SMTSolverError {
    fn from(error: io::Error) -> Self {
        SMTSolverError::EasySMTErr(error)
    }
}

/// A simple static context for encoding expressions related to threshold
/// automata into SMT constraints and checking satisfiability
///
/// This context is used to encode expressions into SMT constraints and check
/// their satisfiability. It should be only used to encode simple expressions,
/// and is not designed to handle expressions over multiple configurations.
pub struct StaticSMTContext {
    solver: SMTSolver,
    params: HashMap<Parameter, SMTExpr>,
    locs: HashMap<Location, SMTExpr>,
    vars: HashMap<Variable, Vec<SMTExpr>>,
}

impl StaticSMTContext {
    /// Create a new static SMT context
    ///
    /// This function creates a new static SMT context with the given solver
    /// builder and declares variables for the given parameters, locations, and
    /// variables.
    pub fn new(
        solver_builder: SMTSolverBuilder,
        params: impl IntoIterator<Item = Parameter>,
        locs: impl IntoIterator<Item = Location>,
        vars: impl IntoIterator<Item = Variable>,
    ) -> Result<Self, SMTSolverError> {
        let mut solver = solver_builder.new_solver();

        let params = params
            .into_iter()
            .map(|p| {
                let expr = p.declare_variable(&mut solver, 0)?;
                Ok((p, expr))
            })
            .collect::<Result<HashMap<_, _>, SMTSolverError>>()?;

        let locs = locs
            .into_iter()
            .map(|l| {
                let expr = l.declare_variable(&mut solver, 0)?;
                Ok((l, expr))
            })
            .collect::<Result<HashMap<_, _>, SMTSolverError>>()?;

        let vars = vars
            .into_iter()
            .map(|v| {
                let expr = v.declare_variable(&mut solver, 0)?;
                Ok((v, vec![expr]))
            })
            .collect::<Result<HashMap<_, _>, SMTSolverError>>()?;

        Ok(StaticSMTContext {
            solver,
            params,
            locs,
            vars,
        })
    }

    /// Get the SMT expression for the `true` value
    pub fn get_true(&self) -> SMTExpr {
        self.solver.true_()
    }

    /// Declare a fresh variable
    pub fn declare_new_int(&mut self, name: &str) -> Result<SMTExpr, SMTSolverError> {
        let int_sort = self.solver.int_sort();
        self.solver
            .declare_const(name, int_sort)
            .map_err(|e| e.into())
    }

    /// Encode the given expression into an SMT expression and return the
    /// expression
    pub fn encode_to_smt<T>(&self, expr: &T) -> Result<SMTExpr, SMTSolverError>
    where
        T: EncodeToSMT<T, Self>,
    {
        expr.encode_to_smt_with_ctx(&self.solver, self)
    }
}

impl SMTSolverContext for StaticSMTContext {
    fn get_smt_solver_mut(&mut self) -> &mut SMTSolver {
        &mut self.solver
    }

    fn get_smt_solver(&self) -> &SMTSolver {
        &self.solver
    }
}

impl SMTVariableContext<Parameter> for StaticSMTContext {
    fn get_expr_for(&self, param: &Parameter) -> Result<SMTExpr, SMTSolverError> {
        self.params
            .get(param)
            .cloned()
            .ok_or_else(|| SMTSolverError::UndeclaredParameter(param.clone()))
    }

    fn get_exprs<'a>(&'a self) -> impl IntoIterator<Item = &'a Parameter>
    where
        Parameter: 'a,
    {
        self.params.keys()
    }
}

impl SMTVariableContext<Location> for StaticSMTContext {
    fn get_expr_for(&self, loc: &Location) -> Result<SMTExpr, SMTSolverError> {
        self.locs
            .get(loc)
            .cloned()
            .ok_or_else(|| SMTSolverError::UndeclaredLocation(loc.clone()))
    }

    fn get_exprs<'a>(&'a self) -> impl IntoIterator<Item = &'a Location>
    where
        Location: 'a,
    {
        self.locs.keys()
    }
}

impl SMTVariableContext<Variable> for StaticSMTContext {
    fn get_expr_for(&self, var: &Variable) -> Result<SMTExpr, SMTSolverError> {
        self.vars
            .get(var)
            .and_then(|v| v.first().cloned())
            .ok_or_else(|| SMTSolverError::UndeclaredVariable(var.clone()))
    }

    fn get_exprs<'a>(&'a self) -> impl IntoIterator<Item = &'a Variable>
    where
        Variable: 'a,
    {
        self.vars.keys()
    }
}

impl GetAssignment<Parameter> for StaticSMTContext {}
impl GetAssignment<Variable> for StaticSMTContext {}
impl GetAssignment<Location> for StaticSMTContext {}

#[cfg(test)]
mod tests {
    use std::vec;

    use easy_smt::Response;
    use taco_threshold_automaton::general_threshold_automaton::builder::RuleBuilder;

    use super::*;

    #[test]
    fn test_get_true() {
        let builder = SMTSolverBuilder::default();

        let mut ctx = StaticSMTContext::new(
            builder,
            vec![Parameter::new("p")],
            vec![Location::new("loc")],
            vec![Variable::new("x")],
        )
        .unwrap();

        let top = ctx.get_true();

        assert_eq!(top, ctx.get_smt_solver_mut().true_())
    }

    #[test]
    fn test_rule_variable_name() {
        let r = RuleBuilder::new(42, Location::new("src"), Location::new("tgt")).build();

        assert!(r.get_name(0).contains("rule"));
        assert!(r.get_name(0).contains("42"));
        assert!(r.get_name(0).contains("0"));
    }

    #[test]
    fn test_boolean_expr_encoding_true_false() {
        let builder = SMTSolverBuilder::default();

        let true_expr: BooleanExpression<Variable> = BooleanExpression::True;
        let false_expr: BooleanExpression<Variable> = BooleanExpression::False;

        let mut ctx = StaticSMTContext::new(
            builder,
            vec![Parameter::new("p")],
            vec![Location::new("loc")],
            vec![Variable::new("x")],
        )
        .unwrap();

        let true_encoded = ctx.encode_to_smt(&true_expr).unwrap();
        let false_encoded = ctx.encode_to_smt(&false_expr).unwrap();

        let solver = ctx.get_smt_solver_mut();
        let true_str = solver.display(true_encoded).to_string();
        let false_str = solver.display(false_encoded).to_string();
        assert_eq!(true_str, "true");
        assert_eq!(false_str, "false");

        solver.assert(true_encoded).unwrap();
        assert_eq!(solver.check().unwrap(), Response::Sat);

        solver.assert(false_encoded).unwrap();
        assert_eq!(solver.check().unwrap(), Response::Unsat);
    }

    #[test]
    fn test_boolean_expr_encoding_two_var_gt() {
        let builder = SMTSolverBuilder::default();

        let expr = BooleanExpression::ComparisonExpression(
            Box::new(IntegerExpression::Atom(Variable::new("x"))),
            ComparisonOp::Gt,
            Box::new(IntegerExpression::Atom(Variable::new("y"))),
        );

        let mut ctx = StaticSMTContext::new(
            builder,
            vec![Parameter::new("p")],
            vec![Location::new("loc")],
            vec![Variable::new("x"), Variable::new("y")],
        )
        .unwrap();

        let encoded_expr = ctx.encode_to_smt(&expr).unwrap();

        let solver = ctx.get_smt_solver_mut();
        let encoded_str = solver.display(encoded_expr).to_string();
        assert_eq!(encoded_str, "(> var_x_0 var_y_0)");

        solver.assert(encoded_expr).unwrap();
        assert_eq!(solver.check().unwrap(), Response::Sat);
    }

    #[test]
    fn test_boolean_expr_encoding_var_eq_const() {
        let builder = SMTSolverBuilder::default();

        let expr = BooleanExpression::ComparisonExpression(
            Box::new(IntegerExpression::Atom(Variable::new("x"))),
            ComparisonOp::Eq,
            Box::new(IntegerExpression::Const(5)),
        );

        let mut ctx = StaticSMTContext::new(
            builder,
            vec![Parameter::new("p")],
            vec![Location::new("loc")],
            vec![Variable::new("x")],
        )
        .unwrap();

        let encoded_expr = ctx.encode_to_smt(&expr).unwrap();

        let solver = ctx.get_smt_solver_mut();
        let encoded_str = solver.display(encoded_expr).to_string();
        assert_eq!(encoded_str, "(= var_x_0 5)");

        solver.assert(encoded_expr).unwrap();
        assert_eq!(solver.check().unwrap(), Response::Sat);
    }

    #[test]
    fn test_boolean_expr_encoding_var_and_const() {
        let builder = SMTSolverBuilder::default();

        let expr = BooleanExpression::BinaryExpression(
            Box::new(BooleanExpression::ComparisonExpression(
                Box::new(IntegerExpression::Atom(Variable::new("x"))),
                ComparisonOp::Geq,
                Box::new(IntegerExpression::Const(5)),
            )),
            BooleanConnective::And,
            Box::new(BooleanExpression::ComparisonExpression(
                Box::new(IntegerExpression::Atom(Variable::new("y"))),
                ComparisonOp::Lt,
                Box::new(IntegerExpression::Const(10)),
            )),
        );

        let mut ctx = StaticSMTContext::new(
            builder,
            vec![Parameter::new("p")],
            vec![Location::new("loc")],
            vec![Variable::new("x"), Variable::new("y")],
        )
        .unwrap();

        let encoded_expr = ctx.encode_to_smt(&expr).unwrap();

        let solver = ctx.get_smt_solver_mut();
        let encoded_str = solver.display(encoded_expr).to_string();
        assert_eq!(encoded_str, "(and (>= var_x_0 5) (< var_y_0 10))");

        solver.assert(encoded_expr).unwrap();
        assert_eq!(solver.check().unwrap(), Response::Sat);
    }

    #[test]
    fn test_boolean_expr_encoding_var_or_const() {
        let builder = SMTSolverBuilder::default();

        let expr = BooleanExpression::BinaryExpression(
            Box::new(BooleanExpression::ComparisonExpression(
                Box::new(IntegerExpression::Atom(Variable::new("x"))),
                ComparisonOp::Leq,
                Box::new(IntegerExpression::Const(5)),
            )),
            BooleanConnective::Or,
            Box::new(BooleanExpression::ComparisonExpression(
                Box::new(IntegerExpression::Param(Parameter::new("p"))),
                ComparisonOp::Neq,
                Box::new(IntegerExpression::Const(10)),
            )),
        );

        let mut ctx = StaticSMTContext::new(
            builder,
            vec![Parameter::new("p")],
            vec![Location::new("loc")],
            vec![Variable::new("x"), Variable::new("y")],
        )
        .unwrap();

        let encoded_expr = ctx.encode_to_smt(&expr).unwrap();

        let solver = ctx.get_smt_solver_mut();
        let encoded_str = solver.display(encoded_expr).to_string();
        assert_eq!(encoded_str, "(or (<= var_x_0 5) (not (= param_p 10)))");

        solver.assert(encoded_expr).unwrap();
        assert_eq!(solver.check().unwrap(), Response::Sat);
    }

    #[test]
    fn test_boolean_expr_encoding_not_var() {
        let builder = SMTSolverBuilder::default();

        let expr = BooleanExpression::Not(Box::new(BooleanExpression::ComparisonExpression(
            Box::new(IntegerExpression::Atom(Location::new("loc"))),
            ComparisonOp::Eq,
            Box::new(IntegerExpression::Const(5)),
        )));

        let mut ctx = StaticSMTContext::new(
            builder,
            vec![Parameter::new("p")],
            vec![Location::new("loc")],
            vec![Variable::new("x")],
        )
        .unwrap();

        let encoded_expr = ctx.encode_to_smt(&expr).unwrap();

        let solver = ctx.get_smt_solver_mut();
        let encoded_str = solver.display(encoded_expr).to_string();
        assert_eq!(encoded_str, "(not (= loc_loc_0 5))");

        solver.assert(encoded_expr).unwrap();
        assert_eq!(solver.check().unwrap(), Response::Sat);
    }

    #[test]
    fn test_integer_expr_encoding_add() {
        let builder = SMTSolverBuilder::default();

        let expr = IntegerExpression::BinaryExpr(
            Box::new(IntegerExpression::Atom(Parameter::new("p"))),
            IntegerOp::Add,
            Box::new(IntegerExpression::Const(5)),
        );

        let mut ctx = StaticSMTContext::new(
            builder,
            vec![Parameter::new("p")],
            vec![Location::new("loc")],
            vec![Variable::new("x")],
        )
        .unwrap();

        let encoded_expr = ctx.encode_to_smt(&expr).unwrap();

        let solver = ctx.get_smt_solver_mut();
        let encoded_str = solver.display(encoded_expr).to_string();
        assert_eq!(encoded_str, "(+ param_p 5)");
    }

    #[test]
    fn test_integer_expr_encoding_sub() {
        let builder = SMTSolverBuilder::default();

        let expr = IntegerExpression::BinaryExpr(
            Box::new(IntegerExpression::Atom(Parameter::new("p"))),
            IntegerOp::Sub,
            Box::new(IntegerExpression::Const(3)),
        );

        let mut ctx = StaticSMTContext::new(
            builder,
            vec![Parameter::new("p")],
            vec![Location::new("loc")],
            vec![Variable::new("x")],
        )
        .unwrap();

        let encoded_expr = ctx.encode_to_smt(&expr).unwrap();

        let solver = ctx.get_smt_solver_mut();
        let encoded_str = solver.display(encoded_expr).to_string();
        assert_eq!(encoded_str, "(- param_p 3)");
    }

    #[test]
    fn test_integer_expr_encoding_mul() {
        let builder = SMTSolverBuilder::default();

        let expr = IntegerExpression::BinaryExpr(
            Box::new(IntegerExpression::Atom(Parameter::new("p"))),
            IntegerOp::Mul,
            Box::new(IntegerExpression::Const(2)),
        );

        let mut ctx = StaticSMTContext::new(
            builder,
            vec![Parameter::new("p")],
            vec![Location::new("loc")],
            vec![Variable::new("x")],
        )
        .unwrap();

        let encoded_expr = ctx.encode_to_smt(&expr).unwrap();

        let solver = ctx.get_smt_solver_mut();
        let encoded_str = solver.display(encoded_expr).to_string();
        assert_eq!(encoded_str, "(* param_p 2)");
    }

    #[test]
    fn test_integer_expr_encoding_div() {
        let builder = SMTSolverBuilder::default();

        let expr = IntegerExpression::BinaryExpr(
            Box::new(IntegerExpression::Atom(Variable::new("x"))),
            IntegerOp::Div,
            Box::new(IntegerExpression::Const(4)),
        );

        let mut ctx = StaticSMTContext::new(
            builder,
            vec![Parameter::new("p")],
            vec![Location::new("loc")],
            vec![Variable::new("x")],
        )
        .unwrap();

        let encoded_expr = ctx.encode_to_smt(&expr).unwrap();

        let solver = ctx.get_smt_solver_mut();
        let encoded_str = solver.display(encoded_expr).to_string();
        assert_eq!(encoded_str, "(div var_x_0 4)");
    }

    #[test]
    fn test_integer_expr_encoding_neg() {
        let builder = SMTSolverBuilder::default();

        let expr = IntegerExpression::Neg(Box::new(IntegerExpression::Atom(Parameter::new("p"))));

        let mut ctx = StaticSMTContext::new(
            builder,
            vec![Parameter::new("p")],
            vec![Location::new("loc")],
            vec![Variable::new("x")],
        )
        .unwrap();

        let encoded_expr = ctx.encode_to_smt(&expr).unwrap();

        let solver = ctx.get_smt_solver_mut();
        let encoded_str = solver.display(encoded_expr).to_string();
        assert_eq!(encoded_str, "(- param_p)");
    }

    #[test]
    fn test_get_assignment_sat() {
        let builder = SMTSolverBuilder::default();

        let expr = BooleanExpression::BinaryExpression(
            Box::new(BooleanExpression::ComparisonExpression(
                Box::new(IntegerExpression::Atom(Variable::new("x"))),
                ComparisonOp::Leq,
                Box::new(IntegerExpression::Const(5)),
            )),
            BooleanConnective::And,
            Box::new(BooleanExpression::ComparisonExpression(
                Box::new(IntegerExpression::Atom(Variable::new("x"))),
                ComparisonOp::Gt,
                Box::new(IntegerExpression::Const(4)),
            )),
        );

        let mut ctx = StaticSMTContext::new(
            builder,
            vec![Parameter::new("p")],
            vec![Location::new("loc")],
            vec![Variable::new("x"), Variable::new("y")],
        )
        .unwrap();

        let encoded_expr = ctx.encode_to_smt(&expr).unwrap();
        let res = ctx.assert_and_check_expr(encoded_expr).unwrap();

        let assignment = ctx.get_assignment(res, &Variable::new("x")).unwrap();

        assert_eq!(assignment, Some(5));
    }

    #[test]
    fn test_get_assignment_unsat() {
        let builder = SMTSolverBuilder::default();

        let expr = BooleanExpression::BinaryExpression(
            Box::new(BooleanExpression::ComparisonExpression(
                Box::new(IntegerExpression::Atom(Variable::new("x"))),
                ComparisonOp::Leq,
                Box::new(IntegerExpression::Const(5)),
            )),
            BooleanConnective::And,
            Box::new(BooleanExpression::ComparisonExpression(
                Box::new(IntegerExpression::Atom(Variable::new("x"))),
                ComparisonOp::Gt,
                Box::new(IntegerExpression::Const(5)),
            )),
        );

        let mut ctx = StaticSMTContext::new(
            builder,
            vec![Parameter::new("p")],
            vec![Location::new("loc")],
            vec![Variable::new("x"), Variable::new("y")],
        )
        .unwrap();

        let encoded_expr = ctx.encode_to_smt(&expr).unwrap();
        let res = ctx.assert_and_check_expr(encoded_expr).unwrap();

        let assignment = ctx.get_assignment(res, &Variable::new("x"));

        assert!(assignment.is_err());
        assert!(matches!(
            assignment.unwrap_err(),
            SMTSolverError::ExtractionFromUnsat
        ));
    }

    #[test]
    fn test_get_expr_smt_context() {
        let builder = SMTSolverBuilder::default();

        let ctx = StaticSMTContext::new(
            builder,
            vec![Parameter::new("p")],
            vec![Location::new("loc")],
            vec![Variable::new("x")],
        )
        .unwrap();

        let exprs = SMTVariableContext::<Parameter>::get_exprs(&ctx)
            .into_iter()
            .cloned()
            .collect::<Vec<Parameter>>();
        assert_eq!(exprs.len(), 1);
        assert!(exprs.contains(&Parameter::new("p")));

        let exprs = SMTVariableContext::<Location>::get_exprs(&ctx)
            .into_iter()
            .cloned()
            .collect::<Vec<Location>>();
        assert_eq!(exprs.len(), 1);
        assert!(exprs.contains(&Location::new("loc")));

        let exprs = SMTVariableContext::<Variable>::get_exprs(&ctx)
            .into_iter()
            .cloned()
            .collect::<Vec<Variable>>();
        assert_eq!(exprs.len(), 1);
        assert!(exprs.contains(&Variable::new("x")));
    }

    #[test]
    fn test_get_assignment_no_solution() {
        let builder = SMTSolverBuilder::default();

        let mut solver = builder.new_solver();

        let vars = vec![Variable::new("x")];
        let vars_smt = vars
            .into_iter()
            .map(|v| (v.clone(), v.declare_variable(&mut solver, 0).unwrap()))
            .collect::<HashMap<_, _>>();

        let res = solver.assert_and_check_expr(solver.false_());
        let sol = vars_smt.get_solution(&mut solver, res.unwrap());

        assert!(sol.is_err());
        assert!(matches!(
            sol.unwrap_err(),
            SMTSolverError::ExtractionFromUnsat
        ));
    }

    #[test]
    fn test_parse_int_err_get_sol() {
        let builder = SMTSolverBuilder::default();

        let mut solver = builder.new_solver();

        let vars = vec![Variable::new("x")];
        let vars_smt = vars
            .into_iter()
            .map(|v| (v.clone(), v.declare_variable(&mut solver, 0).unwrap()))
            .collect::<HashMap<_, _>>();

        let expr = solver.lt(vars_smt[&Variable::new("x")], solver.numeral(0));

        let res = solver.assert_and_check_expr(expr);
        let sol = vars_smt.get_solution(&mut solver, res.unwrap());

        assert!(sol.is_err());
        assert!(matches!(
            sol.unwrap_err(),
            SMTSolverError::SolutionExtractionParseIntError(_)
        ));
    }

    #[test]
    fn test_parse_int_err_get_assignment() {
        let builder = SMTSolverBuilder::default();

        let expr = BooleanExpression::ComparisonExpression(
            Box::new(IntegerExpression::Atom(Variable::new("x"))),
            ComparisonOp::Lt,
            Box::new(IntegerExpression::Const(0)),
        );

        let mut ctx = StaticSMTContext::new(
            builder,
            vec![Parameter::new("p")],
            vec![Location::new("loc")],
            vec![Variable::new("x"), Variable::new("y")],
        )
        .unwrap();

        let encoded_expr = ctx.encode_to_smt(&expr).unwrap();
        let res = ctx.assert_and_check_expr(encoded_expr).unwrap();

        let sol = ctx.get_assignment(res, &Variable::new("x"));

        assert!(sol.is_err());
        assert!(matches!(
            sol.unwrap_err(),
            SMTSolverError::SolutionExtractionParseIntError(_)
        ));
    }

    #[test]
    fn test_get_undeclared_error() {
        let loc = Location::new("loc");
        let param = Parameter::new("param");
        let var = Variable::new("var");
        let rule = RuleBuilder::new(42, loc.clone(), loc.clone()).build();

        assert!(matches!(
            loc.get_undeclared_error(),
            SMTSolverError::UndeclaredLocation(_)
        ));
        assert!(matches!(
            param.get_undeclared_error(),
            SMTSolverError::UndeclaredParameter(_)
        ));
        assert!(matches!(
            var.get_undeclared_error(),
            SMTSolverError::UndeclaredVariable(_)
        ));
        assert!(matches!(
            rule.get_undeclared_error(),
            SMTSolverError::UndeclaredRule(_)
        ));
    }

    #[test]
    fn test_from_io_error() {
        let io_error = io::Error::other("Some error");
        let err = SMTSolverError::from(io_error);

        assert!(matches!(err, SMTSolverError::EasySMTErr(_)));
    }

    #[test]
    fn test_display_smt_err() {
        let err = SMTSolverError::EasySMTErr(io::Error::other("Some error"));
        let display = err.to_string();
        assert!(display.contains("Error from connection to SMT solver"));

        let err = SMTSolverError::UndeclaredParameter(Parameter::new("p"));
        let display = err.to_string();
        assert!(display.contains("Undeclared parameter"));
        assert!(display.contains(Parameter::new("p").name()));

        let err = SMTSolverError::UndeclaredLocation(Location::new("loc"));
        let display = err.to_string();
        assert!(display.contains("Undeclared location"));
        assert!(display.contains(Location::new("loc").name()));

        let err = SMTSolverError::UndeclaredVariable(Variable::new("x"));
        let display = err.to_string();
        assert!(display.contains("Undeclared variable"));
        assert!(display.contains(Variable::new("x").name()));

        let err = SMTSolverError::SolverTimeout;
        let display = err.to_string();
        assert!(display.contains("Timeout in SMT solver"));

        let err = SMTSolverError::SolutionExtractionParseIntError("not_an_int".to_string());
        let display = err.to_string();
        assert!(display.contains("Failed to parse SMT solver supplied solution into integer"));
        assert!(display.contains("not_an_int"));

        let err = SMTSolverError::UndeclaredRule(
            RuleBuilder::new(42, Location::new("src"), Location::new("tgt")).build(),
        );
        let display = err.to_string();
        assert!(display.contains("Undeclared rule"));
        assert!(display.contains("42"));

        let err = SMTSolverError::ExtractionFromUnsat;
        let display = err.to_string();
        assert!(display.contains(
            "Attempted to extract the solution assignment from an unsatisfiable expression"
        ));

        let err = SMTSolverError::TriviallyUnsat("Some reason".to_string());
        let display = err.to_string();
        assert!(display.contains("Specification can never be true"));
        assert!(display.contains("Some reason"));
    }
}
