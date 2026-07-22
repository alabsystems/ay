// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

#![forbid(unsafe_code)]

//! DRAT/DRUP proof-checking library used by `ay check drat`.
//!
//! Verifies DRAT (Deletion Resolution Asymmetric Tautology) and DRUP
//! (Deletion Reverse Unit Propagation) proofs for SAT solver UNSAT results.
//! Supports both text and binary DRAT formats, forward and backward checking.
//!
//! # Usage
//!
//! ```no_run
//! use ay_drat_check::checker::DratChecker;
//! use ay_drat_check::drat_parser;
//!
//! let cnf = ay_drat_check::cnf_parser::parse_cnf(
//!     &b"p cnf 2 2\n1 2 0\n-1 -2 0\n"[..],
//! ).expect("valid CNF");
//! let proof = drat_parser::parse_drat(b"1 0\n-2 0\n0\n").expect("valid DRAT");
//! let mut checker = DratChecker::new(cnf.num_vars, true);
//! let result = checker.verify(&cnf.clauses, &proof);
//! assert!(result.is_ok());
//! ```

pub mod checker;
pub mod cnf_parser;
pub mod drat_parser;
pub mod error;
pub mod literal;

pub use checker::{ConcludeFailure, ConcludeResult, SrChecker, Stats};
pub use error::{DratCheckError, DratParseError};
