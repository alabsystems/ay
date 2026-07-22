// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Canonical MIP/LP model produced by the parsers.
//!
//! Both the MPS and the CPLEX LP parser normalize to this shape so the solver
//! driver sees a single representation.

/// Objective sense.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub enum Sense {
    /// Minimize the objective.
    #[default]
    Min,
    /// Maximize the objective.
    Max,
}

/// The row type of a constraint.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum RowKind {
    /// `<=` constraint.
    Le,
    /// `>=` constraint.
    Ge,
    /// `=` constraint.
    Eq,
}

/// Variable domain.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub enum VarKind {
    /// Continuous (real-valued) variable.
    #[default]
    Continuous,
    /// Integer variable.
    Integer,
    /// Binary (0/1) variable.
    Binary,
}

/// A single variable in the model.
#[derive(Debug, Clone)]
pub struct Variable {
    /// Printable name from the source file.
    pub name: String,
    /// Coefficient in the objective (0 if unused).
    pub obj_coeff: f64,
    /// Lower bound. Default 0 for MPS, -inf for FR, etc.
    pub lower: f64,
    /// Upper bound. Default +inf.
    pub upper: f64,
    /// Continuous / integer / binary.
    pub kind: VarKind,
}

impl Variable {
    /// Builds a variable with the default MPS bounds `[0, +inf)`.
    #[must_use]
    pub fn new(name: impl Into<String>) -> Self {
        Self {
            name: name.into(),
            obj_coeff: 0.0,
            lower: 0.0,
            upper: f64::INFINITY,
            kind: VarKind::Continuous,
        }
    }

    /// Returns true if this is an integer or binary variable.
    #[must_use]
    pub fn is_integral(&self) -> bool {
        matches!(self.kind, VarKind::Integer | VarKind::Binary)
    }
}

/// A single linear constraint.
///
/// Represents `coeffs . x  <kind>  rhs`. `coeffs` is sparse: a vector of
/// `(variable_index, coefficient)` pairs.
#[derive(Debug, Clone)]
pub struct Constraint {
    /// Human-readable row name.
    pub name: String,
    /// `<=`, `>=`, or `=`.
    pub kind: RowKind,
    /// Sparse coefficients: `(var_idx, coeff)`.
    pub coeffs: Vec<(usize, f64)>,
    /// Right-hand side constant.
    pub rhs: f64,
}

/// A complete MIP/LP problem.
///
/// Parsers populate this and the solver driver consumes it.
#[derive(Debug, Clone, Default)]
pub struct Problem {
    /// Name of the problem as declared in the file (may be empty).
    pub name: String,
    /// Minimize or maximize.
    pub sense: Sense,
    /// Constant added to the objective value. MPS encodes this via the RHS of
    /// the objective row; LP files may carry it explicitly.
    pub obj_constant: f64,
    /// Variables in declaration order.
    pub variables: Vec<Variable>,
    /// Constraints in declaration order.
    pub constraints: Vec<Constraint>,
}

impl Problem {
    /// Constructs an empty problem.
    #[must_use]
    pub fn new() -> Self {
        Self::default()
    }

    /// Returns true if any variable is integer or binary.
    #[must_use]
    pub fn has_integer_vars(&self) -> bool {
        self.variables.iter().any(Variable::is_integral)
    }

    /// Looks up a variable by name.
    #[must_use]
    pub fn var_index(&self, name: &str) -> Option<usize> {
        self.variables.iter().position(|v| v.name == name)
    }
}

/// A solved assignment + objective value.
#[derive(Debug, Clone)]
pub struct Solution {
    /// Final objective value.
    pub objective: f64,
    /// `x[i]` corresponds to `problem.variables[i]`.
    pub values: Vec<f64>,
}

impl Solution {
    /// Formats a solution in the canonical `name = value` form.
    #[must_use]
    pub fn format(&self, problem: &Problem) -> String {
        let mut out = String::new();
        out.push_str(&format!("objective = {}\n", self.objective));
        for (var, &val) in problem.variables.iter().zip(self.values.iter()) {
            out.push_str(&format!("{} = {}\n", var.name, val));
        }
        out
    }
}
