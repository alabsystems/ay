// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! CDCL(T) kernel: the engine of the development design notes.
//!
//! Production (design §10, stage 0 of the strangler): in the `--z3-mode`
//! posture with no proof demand, the executor's non-incremental QF_LRA
//! check-sats are the kernel's, and the QF_LRA lane answers only where the
//! kernel answers `unknown` (`ay-dpll` `executor/engine_route.rs`). Elsewhere
//! the executor can run it in shadow (`--engine=shadow`, §10.1) beside a lane
//! and record both answers without printing the kernel's.
//!
//! What it does, and where the design names it:
//! - The engine borrows no store (KC2): [`Engine::check`] is lent the term
//!   store, the assumptions and a [`Guard`], and answers an owned
//!   [`CheckOutcome`] (verdict, failed assumptions, level-0 units, Σ, reason,
//!   counters, recorded proof). An engine and its plug-ins are `Send` (KC7).
//! - One [`Engine::check`] makes exactly one ay-sat search (K1). Theory splits,
//!   model equalities and branch-and-bound become in-search lemmas over atoms
//!   minted during that search (§3.3, §3.5); nothing leaves the search.
//! - Minting is safe in `propagate` and in the final check (ay-sat G3), and
//!   minted variables are frozen. Final-check lemmas continue the search at
//!   the current level (G2). `Definitional` lemmas are irredundant (G1).
//! - Plug-ins never hold a borrow of the `TermStore`; every callback receives
//!   a [`Ctx`] that lends it (K3). [`LraPlugin`] brackets the LRA solver's
//!   raw term pointer inside each callback.
//! - Every conflict, lemma and explanation carries a [`ProofHint`], recorded
//!   when the kernel turns it into a SAT clause (P1). With recording on, an
//!   `unsat` answer's refutation is one DAG-shared proof
//!   ([`Refutation::assemble`], D3): assumptions, clausification, the
//!   recorded theory steps, and the resolution chains of ay-sat's learned
//!   clauses.
//! - Registration is by term content, not by declared logic (H2); an atom no
//!   plug-in owns makes the check `unknown` before the search starts.
//! - A `sat` answer can be checked exactly and independently of the search
//!   ([`Engine::check_model`], P3).
//!
//! - The hub (H1) is one e-graph per check: uninterpreted applications, their
//!   arguments and the equalities between them are nodes; congruence closure,
//!   interpreted values and explanations live there; plug-ins carry theory
//!   variables on nodes and receive `new_eq` / `new_diseq`. EUF is the plug-in
//!   that owns uninterpreted atoms on it; LRA is attached through it.
//! - Theory combination is model-based and in the search (H3): shared
//!   arithmetic terms with equal values in different classes get their
//!   equality minted and decided true first.
//!
//! What it does not have yet: one LIRA tableau (mixed Int and Real atoms give
//! up), and every plug-in but arithmetic and EUF.

#![forbid(unsafe_code)]

mod arith_defs;
mod atoms;
mod content;
mod dl;
mod dl_shape;
mod engine;
mod euf;
mod hub;
mod hub_layout;
mod internalize;
mod kernel;
mod linear;
mod lra;
mod lra_certify;
mod lra_lemmas;
mod model_check;
mod plugin;
mod proof;
mod reserved;
mod shared;
mod term_key;

pub use dl::DlPlugin;
pub use engine::{
    CheckOutcome, Engine, EngineConfig, EngineStats, EnodeMode, Exhausted, Guard, RecordedStep,
    Refutation, SearchProfile, Verdict,
};
pub use euf::EufPlugin;
pub use lra::LraPlugin;
pub use model_check::ModelVerdict;
pub use plugin::{
    Conflict, Ctx, Explanation, Final, GiveUp, HintPremise, Justification, Lemma, LemmaTier,
    ProofHint, ThId, ThVar, TheoryPlugin,
};
pub use proof::{KernelProof, ProofFailure, ProofStats};
pub use reserved::{AsyncJob, AtomSet, ConjCore, Share};
