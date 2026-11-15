// `clippy::restriction` is a menu of house styles, not a soundness group, and
// is allowed wholesale in the four crates that carry this attribute; the
// reasoning, the measurement command, and what the allow costs are recorded
// once, at the top of `veripb-checker/src/lib.rs`. The two members already at
// zero across those crates are re-enabled by name so they cannot come back.
#![allow(clippy::restriction)]
#![warn(clippy::unimplemented, clippy::todo)]

//! Traits and basic implementations for variables, literals, constraints and formulas for combinatorial solvers.
//!
//! # Supported Types
//! The current focus of this library is on pseudo-Boolean optimization problems problems. However, the library is designed to be extensible to support different combinatorial optimization problems.
//!
//! A variable [`VarIdx`](var_type::VarIdx) is just an index and has type [`VarType`](var_type::VarType), where the special case is the boolean variable type [`BooleanVar`](boolean_var::BooleanVar). A literal is represented as [`Lit`](lit::Lit). An [`Assignment`](assignment::Assignment) maps variables to values and a [`Substitution`](substitution) maps variables to literals or values.
//!
//! The only supported constraint type is a [`PBConstraint`](pb_constraint::PBConstraint). A [`Formula`](formula::Formula) is a collection of [`PBConstraint`](pb_constraint::PBConstraint) with a [`PBObjective`](pb_objective::PBObjective).
//!
//! ## Pseudo-Boolean Constraints
//! There are data structures for three types of pseudo-Boolean constraints:
//! - [`Clause`](clause::Clause): all coefficients and the right-hand side are 1.
//! - [`Cardinality`](cardinality::Cardinality): all coefficients are 1 and the right hand side can be any integer.
//! - [`GeneralPBConstraint`](general_pb_constraint::GeneralPBConstraint): all coefficients and the right-hand side can be any ointeger.
//!
//! # Design Philosophy
//! This crate is designed to be as general purpose and generic as possible (with the trade-off for performance).
//!

pub mod assignment;
pub mod boolean_var;
pub mod cardinality;
pub mod clause;
pub mod db_constraint;
// Since fat/expanded PB constraint s are currently not used, it is disabled.
// pub mod fat_pb_constraint;
pub mod formula;
pub mod general_pb_constraint;
pub mod general_pb_term;
mod helper;
pub mod lit;
pub mod pb_constraint;
pub mod pb_objective;
pub mod pb_term;
pub mod prelude;
pub mod propagation;
pub mod substitution;
mod to_pretty_string;
pub mod var_name_manager;
pub mod var_type;
