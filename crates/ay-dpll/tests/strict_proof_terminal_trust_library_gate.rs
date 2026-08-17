// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! CONTROL for the strict-proof terminal-trust gate at the LIBRARY boundary.
//!
//! ay 0.5 carried `UnknownReason::ProofTrusted`, the typed reason for
//! "strict proofs refused this UNSAT because its terminal derivation chain is
//! not trust-free". 0.6 removed it (66538b006) and reimplemented the gate as a
//! driver-level downgrade inside the `ay` BINARY, publishing the *generic*
//! `UnknownReason::Incomplete`. Two regressions followed, and this file fences
//! both:
//!
//! 1. **The taxonomy collapsed.** A withheld trust-tainted UNSAT became
//!    byte-identical, at `unknown_reason()`, to an unsupported solver lane. The
//!    only surviving evidence was a free-form string on the CLI transcript.
//!    `SelfCheckRejected` exists precisely because that conflation once hid 13
//!    wrong answers; its doc comment says "Never fold this back into
//!    `Incomplete`". The strict-proof gate was left in exactly that state.
//!
//! 2. **The gate was not enforced in the library at all.** The downgrade lived
//!    only in `crates/ay/src/run.rs`. On [`SEQ_LEN_UNCHECKABLE_UNSAT`] below,
//!    `ay --strict-proofs` printed
//!    `unknown` / `(:reason-unknown (incomplete proof-trusted))` while a
//!    consumer linking `ay-dpll` with `:check-proofs-strict true` received a
//!    raw `unsat` for the same problem. Downstream consumers use the library.
//!
//! Every test here drives the ay-dpll library API. None shells out to the `ay`
//! binary — the binary is not where the gap was.

use ay_core::Sort;
use ay_dpll::api::{Logic, Solver};
use ay_dpll::{Executor, UnknownOrigin, UnknownReason};
use ay_frontend::parse;
use ntest::timeout;

/// A sequence problem whose refutation is *clean* — zero `trust`/`hole` steps,
/// no provenance-unbacked `assume` — and yet is NOT independently checkable:
/// carcara hard-rejects the `Seq` sort at parse time, no firewall-Lean lemma
/// covers sequences, and there is no DRAT lane. `seq.len s` pinned to two
/// distinct integers collapses to a bare `la_generic`/`resolution` chain.
///
/// This is the TIER-0 leak documented on
/// [`Executor::unsat_proof_references_uncheckable_seq_theory`]. Because the
/// proof carries no trust step, the mandatory certification funnel mints a
/// certificate and publishes `unsat`. Only the terminal-trust gate refuses it,
/// and before this fix that gate existed only in the CLI driver.
const SEQ_LEN_UNCHECKABLE_UNSAT: &str = "\
(set-logic ALL)
(declare-const s (Seq Int))
(assert (= (seq.len s) 1))
(assert (= (seq.len s) 2))
(check-sat)
";

/// A sequence problem AY refutes only by ASSUMING an injected `seq.len`
/// additivity axiom the problem never asserted. Its trust step is caught by the
/// mandatory certification funnel, which publishes `SelfCheckRejected`. Used
/// below to prove the restored reason is a *distinct* third value, not a rename
/// of an existing one.
const SEQ_INJECTED_AXIOM_UNSAT: &str = "\
(set-logic ALL)
(declare-const s (Seq Int))
(declare-const t (Seq Int))
(assert (= (seq.len (seq.++ s t)) (+ (seq.len s) (seq.len t) 1)))
(check-sat)
";

/// Strict proofs on, expressed the only way a library consumer can express it.
const STRICT: &str = "(set-option :produce-proofs true)\n(set-option :check-proofs-strict true)\n";

/// Strict proofs on without requesting a user-visible proof artifact.
const STRICT_ONLY: &str = "(set-option :check-proofs-strict true)\n";

/// Proofs on, strict OFF — the baseline the gate must not disturb.
const PLAIN: &str = "(set-option :produce-proofs true)\n";

fn solve(prefix: &str, script: &str) -> (String, Executor) {
    let commands = parse(&format!("{prefix}{script}")).expect("parse probe script");
    let mut executor = Executor::new();
    let outputs = executor
        .execute_all(&commands)
        .expect("execute probe script");
    let verdict = outputs.last().cloned().unwrap_or_else(|| "<none>".into());
    (verdict, executor)
}

/// CONTROL part (a) — the verdict.
///
/// Under strict proofs, an UNSAT whose terminal derivation chain is not
/// trust-free must not reach a library consumer as UNSAT.
#[test]
#[timeout(120_000)]
fn library_strict_proofs_withholds_terminal_trust_unsat() {
    let (verdict, executor) = solve(STRICT, SEQ_LEN_UNCHECKABLE_UNSAT);
    assert!(
        executor.unsat_proof_terminal_trust_detected() || !executor.last_result_is_unsat(),
        "fixture drifted: this problem must still exercise the terminal-trust predicate"
    );
    assert_ne!(
        verdict, "unsat",
        "strict proofs accepted an UNSAT whose terminal derivation chain is not \
         trust-free, at the LIBRARY boundary. `ay --strict-proofs` refuses this \
         exact problem with `(incomplete proof-trusted)`; a consumer linking \
         ay-dpll must not get a different answer from the same solver."
    );
    assert_eq!(verdict, "unknown", "expected a fail-closed downgrade");
    assert!(
        !executor.last_result_is_unsat(),
        "executor state must agree with the published verdict"
    );
}

/// Strict-only library mode must inspect the mandatory hidden proof rather
/// than the public artifact accessor, which intentionally returns `None`.
#[test]
#[timeout(120_000)]
fn library_strict_option_alone_withholds_hidden_terminal_trust_unsat() {
    let (verdict, executor) = solve(STRICT_ONLY, SEQ_LEN_UNCHECKABLE_UNSAT);
    assert!(
        !executor.is_producing_proofs(),
        "fixture must exercise strict-only hidden proof tracking"
    );
    assert!(executor.last_proof().is_none());
    assert_eq!(verdict, "unknown");
    assert_eq!(executor.unknown_reason(), Some(UnknownReason::ProofTrusted));
}

/// CONTROL part (b) — the reason must be DISTINGUISHABLE.
///
/// A caught soundness gate and an unsupported lane are different facts. If both
/// publish `Incomplete`, the gate is invisible to any consumer that does not
/// scrape CLI stderr.
#[test]
#[timeout(120_000)]
fn library_terminal_trust_reason_is_not_generic_incomplete() {
    let (_, executor) = solve(STRICT, SEQ_LEN_UNCHECKABLE_UNSAT);
    let reason = executor.unknown_reason();
    assert_ne!(
        reason,
        Some(UnknownReason::Incomplete),
        "the strict-proof trust rejection published the GENERIC incomplete \
         reason, making a withheld unsound UNSAT indistinguishable from an \
         unsupported solver lane — the exact conflation `SelfCheckRejected`'s \
         doc comment forbids"
    );
    assert_eq!(
        reason,
        Some(UnknownReason::ProofTrusted),
        "expected the typed terminal-trust reason"
    );
    assert_eq!(
        reason.map(|r| r.code()),
        Some("proof_trusted"),
        "the stable evidence code must name the gate"
    );
    assert_eq!(
        executor.unknown_origin(),
        Some(UnknownOrigin::TerminalTrust),
        "the reason must be published through its own registered origin"
    );
}

/// The restored reason is a THIRD value, not a rename.
///
/// A trust step caught by the mandatory certification funnel is
/// `SelfCheckRejected`; a terminal chain refused by the strict-proof gate is
/// `ProofTrusted`; an unsupported lane is `Incomplete`. Collapsing any pair
/// re-creates the defect in a different place.
#[test]
#[timeout(120_000)]
fn terminal_trust_is_distinct_from_self_check_rejection() {
    let (_, gated) = solve(STRICT, SEQ_LEN_UNCHECKABLE_UNSAT);
    let (_, refuted) = solve(STRICT, SEQ_INJECTED_AXIOM_UNSAT);
    assert_eq!(gated.unknown_reason(), Some(UnknownReason::ProofTrusted));
    assert_eq!(
        refuted.unknown_reason(),
        Some(UnknownReason::SelfCheckRejected)
    );
    assert_ne!(
        gated.unknown_reason(),
        refuted.unknown_reason(),
        "a strict-proof gate rejection and a certification refutation are \
         different facts and must not share a reason"
    );
}

/// The control's own control: the gate is opt-in.
///
/// If this problem stopped being UNSAT for unrelated reasons, part (a) would
/// pass for the wrong reason and prove nothing. This pins that the strict-proof
/// gate — not a regression in the seq lane — is what moved the verdict.
#[test]
#[timeout(120_000)]
fn default_mode_verdict_is_unchanged_by_the_gate() {
    let (verdict, executor) = solve(PLAIN, SEQ_LEN_UNCHECKABLE_UNSAT);
    assert_eq!(
        verdict, "unsat",
        "without strict proofs the verdict must be untouched; otherwise part (a) \
         is not measuring the gate"
    );
    assert!(
        executor.unsat_proof_terminal_trust_detected(),
        "and the same problem must still carry the terminal-trust property, so \
         part (a)'s downgrade is attributable to the gate alone"
    );
}

/// The same gate through `Solver::check_sat` / `Solver::unknown_reason`.
///
/// The Executor tests above go through SMT-LIB command execution. This one
/// builds the identical problem with native term constructors and consumes the
/// verdict as `VerifiedSolveResult`, because that is the surface a Rust
/// consumer of `ay-dpll` actually links against — and it is the surface that
/// silently returned a trust-bearing UNSAT.
#[test]
#[timeout(120_000)]
fn native_solver_check_sat_reflects_the_gate() {
    let mut solver = Solver::new(Logic::All);
    solver
        .try_set_option(":produce-proofs", "true")
        .expect("enable proof production");
    solver
        .try_set_option(":check-proofs-strict", "true")
        .expect("enable strict proofs");

    let s = solver.declare_const("s", Sort::Seq(Box::new(Sort::Int)));
    let len = solver.seq_len(s);
    let one = solver.int_const(1);
    let two = solver.int_const(2);
    let len_is_one = solver.eq(len, one);
    let len_is_two = solver.eq(len, two);
    solver.assert_term(len_is_one);
    solver.assert_term(len_is_two);

    let result = solver.check_sat();
    assert!(
        !result.is_unsat(),
        "Solver::check_sat handed a consumer an UNSAT whose refutation no \
         checker can confirm"
    );
    assert!(result.is_unknown(), "expected a fail-closed downgrade");
    assert_eq!(
        solver.unknown_reason(),
        Some(UnknownReason::ProofTrusted),
        "Solver::unknown_reason must carry the gate, not a generic incomplete"
    );
    assert_eq!(
        solver.reason_unknown_smtlib().as_deref(),
        Some("(incomplete proof-trusted)"),
        "the SMT-LIB rendering must match the string the CLI has always printed"
    );
}

/// The taxonomy is closed on purpose; a restored variant must be registered at
/// every site or it is a silent hole.
#[test]
fn restored_reason_round_trips_through_its_origin() {
    for reason in UnknownReason::ALL {
        assert_eq!(
            reason.origin().reason(),
            reason,
            "reason -> origin -> reason must be the identity for {reason:?}"
        );
    }
    for origin in UnknownOrigin::ALL {
        assert_eq!(
            origin.reason().origin(),
            origin,
            "origin -> reason -> origin must be the identity for {origin:?}"
        );
    }
    assert!(
        UnknownReason::ALL.contains(&UnknownReason::ProofTrusted),
        "the restored reason must be registered in the closed inventory"
    );
    assert!(
        UnknownOrigin::ALL.contains(&UnknownOrigin::TerminalTrust),
        "the origin must be registered in the closed inventory"
    );
    assert_eq!(
        UnknownReason::ALL.len(),
        UnknownOrigin::ALL.len(),
        "the inventories must stay the same length"
    );
}
