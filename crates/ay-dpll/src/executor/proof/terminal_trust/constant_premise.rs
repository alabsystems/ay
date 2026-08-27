// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Authored-surface provenance for Boolean constant premises.
//!
//! `#rewritten-constant-premise` is applied to the finished legitimate-assume
//! set because none of its provenance sources is the authored text, and several
//! can contribute a Boolean constant.
//!
//! Preprocessing rewrites `ctx.assertions` in place, and when
//! `proof_problem_assertion_provenance` is absent,
//! `proof_original_problem_assertions` falls back to exactly that rewritten
//! stack. This is the hazard
//! `rebuild_trust_leaf_proof_from_original_assertions` already documents:
//! preprocessing may rewrite `ctx.assertions` in place, so the raw stack is not
//! a usable original source. An assertion the solver discharges collapses to
//! `false` in that stack, and the constant then enters the accept set as if the
//! file had asserted it.
//!
//! Measured at 55e938d90 on `benchmarks/smt/QF_AX/storeinv_minimal.smt2`, whose
//! one authored assertion is `(not (= (store a i (select a i)) a))`. Both lists
//! arrive as the single term `false` while the parsed surface still holds the
//! real assertion, and AY published:
//!
//! ```text
//! c ay.proof.certificate unproved_steps=0 foreign_assumes=no
//!   trust_free=yes ay_self_checkable=yes
//! unsat
//! ```
//!
//! beside the three-line artifact `(assume t0 false)` /
//! `(step t1 (cl (not false)) :rule false)` /
//! `(step t2 (cl) :rule resolution :premises (t0 t1))`. Carcara rejects it at
//! the first step: "could not match term to any of the original problem
//! premises: false". All three disclosures were therefore false and the empty
//! clause rested on nothing. This is the same class as the finite-enum
//! pigeonhole defect: prove the assertion contradictory, discard the argument,
//! and assert bare `false`. It is also the artifact shape that got the QF_DT
//! poison removal rejected.
//!
//! A Boolean constant is therefore admitted only when the parsed surface — the
//! one stack preprocessing never rewrites — literally asserts that constant. A
//! file that really says `(assert false)` keeps working because the constant is
//! a premise an external checker can match. Everything else fails closed to
//! `unknown`, which is what a refutation with no argument is worth. The
//! degenerate-assume repair in `build_unsat_proof` already rebuilds from the
//! original assertions when every assume leaf is a Boolean constant, and
//! `#bv-forall-const-expansion` refuses a constant expansion for the same reason.
//!
//! Each constant earns its own authorization: a file that says `(assert true)`
//! authorizes `true` and nothing else. Asking only "is some Boolean constant
//! authored?" let one `(assert true)` line re-authorize `false`, reopening the
//! exact hole `boolean_constant_premises_authored` closes: an
//! `(assume t0 false)` artifact certified while Carcara called it invalid.
//! Adversarial review found that defect one line away from the original canary.

use ay_frontend::command::Term as FrontendTerm;

use super::super::super::Executor;

impl Executor {
    /// Whether a Boolean constant may enter the leak-2 accept set as a premise
    /// (see `#rewritten-constant-premise`).
    ///
    /// Two ways to earn it, and only two:
    ///
    /// * the PARSED assertion surface — the one stack preprocessing never
    ///   rewrites in place — literally carries `(assert false)` / `(assert
    ///   true)`; or
    /// * exact compact provenance records a literal-false assertion or a
    ///   literal-false assumption from the external native/text query boundary.
    ///
    /// The programmatic assertion route (`Solver::assert_term(bool_const(false))`,
    /// and the named / unsat-core transport over it) records
    ///   `ParsedTerm::Symbol(NATIVE_API_ASSERTION_PLACEHOLDER)` for every
    ///   assertion — a placeholder, never the term. A stack that is empty or
    ///   entirely placeholders carries no authored text, so the claim this guard
    ///   polices — "an external checker will match this `assume` against the
    ///   input file" — is not being made, and the native route stays
    ///   byte-identical to before. The same placeholder test already gates
    ///   surface authority in `proof_rewrite`, `proof_original_rebuild` and the
    ///   trust-surgery quant plans.
    ///
    /// Top-level only, deliberately: a constant buried inside an `and` reaches
    /// the proof through and-flattening, which an external checker does not
    /// replay, so leaving it unauthorized fails closed rather than shipping an
    /// artifact carcara refuses. Only `Const` is accepted: a quoted identifier
    /// such as `|false|` is a `Symbol("false")`, but it does not author the
    /// Boolean constant `false`.
    pub(in crate::executor) fn boolean_constant_premises_authored(&self) -> (bool, bool) {
        let parsed = self.ctx.assertions_parsed();
        let false_term = self.ctx.terms.false_term();
        let authored_false = self
            .ctx
            .concrete_authored_literal_false_terms()
            .contains(&false_term)
            || self.unsat_query_has_literal_false_assumption_source();
        let has_authored_surface = parsed.iter().any(|term| {
            !matches!(
                term,
                FrontendTerm::Symbol(name)
                    if name == crate::executor::NATIVE_API_ASSERTION_PLACEHOLDER
            )
        });
        if !has_authored_surface {
            // Native-API carve-out: there is no parsed surface to match
            // against. `true` retains that compatibility carve-out; `false`
            // additionally needs exact compact source provenance because a
            // folded composite can share its canonical TermId.
            return (true, authored_false);
        }
        let mut authored_true = false;
        for term in parsed.iter() {
            if let FrontendTerm::Const(ay_frontend::command::Constant::True) = term {
                authored_true = true;
            }
        }
        (authored_true, authored_false)
    }
}
