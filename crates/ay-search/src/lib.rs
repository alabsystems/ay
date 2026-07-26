// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#![forbid(unsafe_code)]

//! High-level, typed finite-domain search powered by AY CP-SAT.
//!
//! `ay-search` is for programs that are easier to describe as choices plus
//! constraints than as hand-written backtracking. It provides model-scoped
//! integer and Boolean handles, linear expressions, global constraints,
//! complete/capped enumeration, sound optimization, SMT-LIB export, and a
//! portable JSON specification with a deliberately small expression grammar.

mod error;
mod expr;
mod model;
mod spec;

pub use error::SearchError;
pub use expr::{BoolVar, IntVar, LinearExpr};
pub use model::{
    Domain, EnumerationResult, Model, OptimizationResult, Solution, SolveOptions, SolveResult,
    MAX_BACKEND_WORK, MAX_CP_SAFE_MAGNITUDE, MAX_ENCODED_DOMAIN_SPAN, MAX_MODEL_CONSTRAINTS,
    MAX_MODEL_VARIABLES, MAX_TABLE_CELLS, MAX_TOTAL_ENCODED_VALUES,
};
pub use spec::{
    ConstraintSpec, DomainSpec, ElementSpec, LimitsSpec, ObjectiveSense, ObjectiveSpec,
    SearchProblem, SearchRunResult, SearchSpec, TableSpec, VariableSpec, MAX_EXPRESSION_BYTES,
    MAX_EXPRESSION_TOKENS, MAX_SEARCH_SPEC_RESULT_BYTES, MAX_SEARCH_SPEC_RESULT_CELLS,
    MAX_SEARCH_SPEC_SMT_BYTES, MAX_SEARCH_SPEC_SOLUTIONS,
};
