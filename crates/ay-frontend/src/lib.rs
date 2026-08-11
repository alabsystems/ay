// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#![forbid(unsafe_code)]

//! AY Frontend - SMT-LIB 2.7 parser and preprocessor
//!
//! Parses SMT-LIB input and converts it to the internal representation.
//!
//! # Example
//!
//! ```
//! use ay_frontend::{parse, Command};
//!
//! let input = r#"
//!     (set-logic QF_LIA)
//!     (declare-const x Int)
//!     (assert (> x 0))
//!     (check-sat)
//! "#;
//!
//! let commands = parse(input).unwrap();
//! assert_eq!(commands.len(), 4);
//! assert!(matches!(&commands[0], Command::SetLogic(logic) if logic == "QF_LIA"));
//! ```

#![warn(missing_docs)]
#![warn(clippy::all)]

pub mod command;
pub(crate) mod elaborate;
pub(crate) mod lexer;
pub(crate) mod parser;
pub mod sexp;
pub mod stats;

pub use command::{
    ApplyTactic, Command, Constant, Index, MatchPattern, ParamValue, ParsedConstant, ParsedSort,
    Probe, ProbeCmp, QualifiedIdentifier, Sort, SygusGrammar, SygusGrammarRule, Term,
    SUPPORTED_TACTIC_NAMES,
};
pub use elaborate::{
    is_canonical_theory_operator_identity, is_reserved_op_name, is_reserved_symbol,
    AuthoredAssertionRef, CheckedProjectionBinding, CheckedProjectionBindings, CommandResult,
    Context, DeclarationId, DeclarationKind, ElaborateError, FiniteSetOp, FiniteSetTermMetadata,
    FiniteSetTypingMode, IntroKind, Objective, ObjectiveDirection, OptionValue,
    ProjectionBindingRejection, ProjectionBindingRequest, PublicAssertionMetadata, PublicSort,
    PublicSymbolSignature, PublicTermMetadata, SoftAssertion, SourceContextStamp, SymbolInfo,
};
pub use parser::{parse, CommandStream, CommandStreamItem};
pub use sexp::{ParseError, SExpr};
pub use stats::{collect_formula_stats, FormulaStats};
