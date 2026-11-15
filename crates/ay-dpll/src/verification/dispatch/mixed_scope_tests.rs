// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The scoped-first mixed re-check against the full-store re-check it fronts,
//! and the per-query gate that decides whether it runs
//! (#combiner-verify-scope).

use ay_core::kani_compat::DetHashMap;
use ay_core::term::Symbol;
use ay_core::{Sort, TermId, TermStore, TheoryLit, TheorySolver};
use num_bigint::BigInt;
use num_rational::BigRational;

use super::super::{
    verification_combiner_kind, verify_conflict_semantic_memoized, verify_mixed_conflict_semantic,
    verify_mixed_conflict_semantic_with_gate, ConflictSemanticVerdict, ConflictSemanticVerifyMemo,
};
use super::gate_tests::closed_gate;
use super::{
    decide_scoped_first, recheck_mixed_context_in, recheck_under_gate, reproved_verdict,
    CongruenceScope, ScopedRecheckGate,
};
use crate::combined_solvers::combiner::TheoryCombiner;
use crate::verification::VerificationError;

type Verdict = Result<ConflictSemanticVerdict, VerificationError>;

/// The re-check of `context` under `scope` alone, with the inputs
/// `verify_mixed_conflict_semantic` hands it (a combined, linear, single-sort
/// context).
fn recheck_under(scope: CongruenceScope, terms: &TermStore, context: &[TheoryLit]) -> Verdict {
    let trail: DetHashMap<TermId, bool> = context.iter().map(|lit| (lit.term, lit.value)).collect();
    let kind = verification_combiner_kind(terms, context.iter().map(|lit| lit.term));
    recheck_mixed_context_in(scope, terms, context, trail, kind, reproved_verdict(kind))
}

fn same(a: &Verdict, b: &Verdict) -> bool {
    format!("{a:?}") == format!("{b:?}")
}

fn int(terms: &mut TermStore, value: i64) -> TermId {
    terms.mk_int(BigInt::from(value))
}

fn app(terms: &mut TermStore, name: &str, args: Vec<TermId>, sort: Sort) -> TermId {
    terms.mk_app(Symbol::named(name), args, sort)
}

/// Function applications that are NOT in any context below but are congruent
/// to context terms once the context's equalities hold: exactly what the
/// full-store e-graph registers and the scoped one leaves out.
fn pollute_int(terms: &mut TermStore, x: TermId, y: TermId, z: TermId) {
    let fy = app(terms, "f", vec![y], Sort::Int);
    let fx = app(terms, "f", vec![x], Sort::Int);
    let one = int(terms, 1);
    let x1 = terms.mk_add(vec![x, one]);
    let _ = app(terms, "g", vec![fx], Sort::Int);
    let _ = app(terms, "g", vec![fy], Sort::Int);
    let _ = app(terms, "f", vec![x1], Sort::Int);
    let _ = app(terms, "f", vec![fx], Sort::Int);
    let _ = app(terms, "h", vec![x, z], Sort::Int);
    let _ = app(terms, "h", vec![y, z], Sort::Int);
}

/// A battery of combined contexts: valid conflicts and satisfiable (spurious)
/// ones over UF+LIA, UF+LRA and arrays, in a store polluted with congruent
/// applications outside every context.
fn battery(terms: &mut TermStore) -> Vec<(&'static str, Vec<TheoryLit>, bool)> {
    let x = terms.mk_var("x", Sort::Int);
    let y = terms.mk_var("y", Sort::Int);
    let z = terms.mk_var("z", Sort::Int);
    pollute_int(terms, x, y, z);
    let three = int(terms, 3);
    let four = int(terms, 4);
    let five = int(terms, 5);
    let ten = int(terms, 10);
    let fx = app(terms, "f", vec![x], Sort::Int);
    let fy = app(terms, "f", vec![y], Sort::Int);
    let fz = app(terms, "f", vec![z], Sort::Int);
    let x_eq_y = terms.mk_eq(x, y);
    let fx_3 = terms.mk_eq(fx, three);
    let fy_4 = terms.mk_eq(fy, four);
    let fz_4 = terms.mk_eq(fz, four);
    let x_le_5 = terms.mk_le(x, five);
    let x_ge_10 = terms.mk_ge(x, ten);
    let fx_10 = terms.mk_eq(fx, ten);

    let r = terms.mk_var("r", Sort::Real);
    let s = terms.mk_var("s", Sort::Real);
    let half = terms.mk_rational(BigRational::new(BigInt::from(1), BigInt::from(2)));
    let two = terms.mk_rational(BigRational::new(BigInt::from(2), BigInt::from(1)));
    let fr = app(terms, "fr", vec![r], Sort::Real);
    let fs = app(terms, "fr", vec![s], Sort::Real);
    let _ = app(terms, "gr", vec![fr], Sort::Real);
    let r_eq_s = terms.mk_eq(r, s);
    let fr_half = terms.mk_eq(fr, half);
    let fs_two = terms.mk_eq(fs, two);
    let fs_half = terms.mk_eq(fs, half);

    let arr = Sort::array(Sort::Int, Sort::Int);
    let a = terms.mk_var("a", arr.clone());
    let b = terms.mk_var("b", arr);
    let i = terms.mk_var("i", Sort::Int);
    let j = terms.mk_var("j", Sort::Int);
    let v = terms.mk_var("v", Sort::Int);
    let st = terms.mk_store(b, i, v);
    let _row_term = terms.mk_select(st, j);
    let a_eq_st = terms.mk_eq(a, st);
    let i_eq_j = terms.mk_eq(i, j);
    let sel_aj = terms.mk_select(a, j);
    let sel_bj = terms.mk_select(b, j);
    let sel_ai = terms.mk_select(a, i);
    let aj_eq_bj = terms.mk_eq(sel_aj, sel_bj);
    let ai_eq_v = terms.mk_eq(sel_ai, v);

    let t = TheoryLit::new;
    vec![
        (
            "uflia congruence",
            vec![t(x_eq_y, true), t(fx_3, true), t(fy_4, true)],
            true,
        ),
        (
            "uflia spurious",
            vec![t(x_eq_y, true), t(fx_3, true), t(fz_4, true)],
            false,
        ),
        (
            "lia bounds + uf",
            vec![t(x_le_5, true), t(x_ge_10, true), t(fx_10, true)],
            true,
        ),
        (
            "uflra congruence",
            vec![t(r_eq_s, true), t(fr_half, true), t(fs_two, true)],
            true,
        ),
        (
            "uflra spurious",
            vec![t(r_eq_s, true), t(fr_half, true), t(fs_half, true)],
            false,
        ),
        (
            "row2",
            vec![t(a_eq_st, true), t(i_eq_j, false), t(aj_eq_bj, false)],
            true,
        ),
        (
            "row1 spurious",
            vec![t(a_eq_st, true), t(ai_eq_v, true)],
            false,
        ),
    ]
}

/// The verdict the mixed verifier publishes through a fresh query's gate
/// (which admits the scoped run) is the full-store verdict on every shape of
/// the battery, valid or spurious; the valid ones are re-proved by the scoped
/// run itself (the fast path is taken). Outside a query it is the full-store
/// verdict too.
#[test]
fn scoped_first_recheck_publishes_the_full_store_verdict() {
    let mut terms = TermStore::new();
    for (name, context, valid) in battery(&mut terms) {
        let full = recheck_under(CongruenceScope::FullStore, &terms, &context);
        let scoped = recheck_under(CongruenceScope::Context, &terms, &context);
        let mut gate = ScopedRecheckGate::default();
        let published =
            verify_mixed_conflict_semantic_with_gate(&context, &terms, &[], Some(&mut gate));
        assert!(
            same(&published, &full),
            "{name}: published {published:?} but the full-store re-check says {full:?}"
        );
        assert_ne!(
            gate,
            ScopedRecheckGate::default(),
            "{name}: the scoped run was booked"
        );
        let outside_query = verify_mixed_conflict_semantic(&context, &terms, &[]);
        assert!(
            same(&outside_query, &full),
            "{name}: outside a query {outside_query:?}"
        );
        if valid {
            assert!(
                matches!(
                    full,
                    Ok(ConflictSemanticVerdict::Reproved
                        | ConflictSemanticVerdict::ReprovedByArrayTheory)
                ),
                "{name}: the battery's valid conflicts are re-proved: {full:?}"
            );
            assert!(
                same(&scoped, &full),
                "{name}: the scoped run re-proves it too: {scoped:?}"
            );
        } else {
            // Negative twin: a satisfiable context stays rejected, and the
            // scoped run never re-proves it.
            assert!(
                matches!(full, Err(VerificationError::ConflictIsSat)),
                "{name}: the full store rejects the spurious conflict: {full:?}"
            );
            assert!(
                !matches!(
                    scoped,
                    Ok(ConflictSemanticVerdict::Reproved
                        | ConflictSemanticVerdict::ReprovedByArrayTheory)
                ),
                "{name}: the scoped run must not re-prove a satisfiable context: {scoped:?}"
            );
        }
    }
}

/// Every verification combiner kind installs the scope on a fresh combiner,
/// so the scoped run really skips the store-wide registration.
#[test]
fn every_verification_combiner_kind_takes_the_congruence_scope_when_fresh() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Int);
    let fx = app(&mut terms, "f", vec![x], Sort::Int);
    let lit = terms.mk_eq(fx, x);
    for kind in 0..5 {
        let mut combiner = match kind {
            0 => TheoryCombiner::uf_lia(&terms),
            1 => TheoryCombiner::uf_lra(&terms),
            2 => TheoryCombiner::auf_lia(&terms),
            3 => TheoryCombiner::auf_lra(&terms),
            _ => TheoryCombiner::array_euf(&terms),
        };
        combiner.scope_congruence_to_roots([lit]);
        assert!(combiner.has_congruence_scope(), "combiner kind {kind}");
    }
}

/// Negative twin: once the e-graph is initialized the scope can no longer
/// change what was registered, so a late scope request is ignored and the
/// combiner keeps the full-store registration (never a half-scoped e-graph).
#[test]
fn a_late_congruence_scope_request_is_ignored() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Int);
    let fx = app(&mut terms, "f", vec![x], Sort::Int);
    let lit = terms.mk_eq(fx, x);
    let mut combiner = TheoryCombiner::uf_lia(&terms);
    combiner.register_atom(lit);
    combiner.assert_literal(lit, true);
    let _ = combiner.check();
    combiner.scope_congruence_to_roots([lit]);
    assert!(!combiner.has_congruence_scope());
}

type Runs = (Vec<CongruenceScope>, Verdict);

/// A stub re-check answering `scoped` and `full`, recording which scopes ran.
fn stub<'a>(
    scoped: Verdict,
    full: Verdict,
    runs: &'a mut Vec<CongruenceScope>,
    trail: &'a DetHashMap<TermId, bool>,
) -> impl FnMut(CongruenceScope, DetHashMap<TermId, bool>) -> Verdict + 'a {
    let mut answers = [Some(scoped), Some(full)];
    move |scope, run_trail| {
        assert_eq!(&run_trail, trail, "every run starts from the same trail");
        runs.push(scope);
        let slot = match scope {
            CongruenceScope::Context => 0,
            CongruenceScope::FullStore => 1,
        };
        answers[slot].take().expect("each scope runs at most once")
    }
}

fn stub_trail() -> DetHashMap<TermId, bool> {
    let mut trail: DetHashMap<TermId, bool> = DetHashMap::default();
    trail.insert(TermId(7), true);
    trail
}

/// Run the decision rule over stub re-checks that answer `scoped` and `full`,
/// recording which scopes it ran.
fn decide_with(scoped: Verdict, full: Verdict) -> Runs {
    let mut runs = Vec::new();
    let trail = stub_trail();
    let scoped_reproved = matches!(scoped, Ok(ConflictSemanticVerdict::Reproved));
    let (verdict, reported) = decide_scoped_first(
        ConflictSemanticVerdict::Reproved,
        trail.clone(),
        stub(scoped, full, &mut runs, &trail),
    );
    assert_eq!(
        reported, scoped_reproved,
        "the rule reports the scoped outcome"
    );
    (runs, verdict)
}

/// Run the gated re-check over the same stubs.
fn gated_with(gate: Option<&mut ScopedRecheckGate>, scoped: Verdict, full: Verdict) -> Runs {
    let mut runs = Vec::new();
    let trail = stub_trail();
    let verdict = recheck_under_gate(
        ConflictSemanticVerdict::Reproved,
        trail.clone(),
        gate,
        stub(scoped, full, &mut runs, &trail),
    );
    (runs, verdict)
}

fn reproved() -> Verdict {
    Ok(ConflictSemanticVerdict::Reproved)
}

fn unchecked() -> Verdict {
    Ok(ConflictSemanticVerdict::AcceptedUnchecked)
}

fn rejected() -> Verdict {
    Err(VerificationError::ConflictIsSat)
}

/// Any scoped outcome other than a re-proof is discarded: the full-store
/// verdict is published, in particular its rejection. Negative twin of the
/// fast path: a rule that kept a non-rejecting scoped verdict would publish
/// `AcceptedUnchecked` for the (scoped inconclusive, full Sat) row.
#[test]
fn a_scoped_run_that_does_not_reprove_defers_to_the_full_store_verdict() {
    for scoped in [unchecked, rejected] {
        for full in [reproved, unchecked, rejected] {
            let (runs, verdict) = decide_with(scoped(), full());
            assert!(
                same(&verdict, &full()),
                "scoped {:?}, full {:?}: published {verdict:?}",
                scoped(),
                full()
            );
            assert_eq!(runs, [CongruenceScope::Context, CongruenceScope::FullStore]);
        }
    }
}

/// A scoped re-proof is published as is; only debug builds also run the
/// full-store re-check, as an oracle.
#[test]
fn a_scoped_reproof_is_published() {
    let (runs, verdict) = decide_with(reproved(), reproved());
    assert!(same(&verdict, &reproved()));
    let expected_runs: &[CongruenceScope] = if cfg!(debug_assertions) {
        &[CongruenceScope::Context, CongruenceScope::FullStore]
    } else {
        &[CongruenceScope::Context]
    };
    assert_eq!(runs, expected_runs);
}

/// The debug oracle trips if the full-store re-check ever calls a literal set
/// `Sat` that the scoped run re-proved.
#[cfg(debug_assertions)]
#[test]
#[should_panic(expected = "the full-store re-check calls Sat")]
fn the_debug_oracle_rejects_a_scoped_reproof_the_full_store_calls_sat() {
    let _ = decide_with(reproved(), rejected());
}

/// A closed gate (and no gate at all) runs the full-store re-check alone and
/// publishes exactly its verdict, rejection included; only a skipped call is
/// counted. Negative twin of the scoped path: a rule that consulted the
/// scoped stub here would trip the run log.
#[test]
fn without_an_admitting_gate_only_the_full_store_recheck_runs() {
    for full in [reproved, unchecked, rejected] {
        let mut gate = closed_gate();
        let (runs, verdict) = gated_with(Some(&mut gate), reproved(), full());
        assert_eq!(runs, [CongruenceScope::FullStore]);
        assert!(same(&verdict, &full()), "closed gate published {verdict:?}");
        assert_eq!((gate.credit, gate.calls_without_scoped_run), (0, 1));

        let (runs, verdict) = gated_with(None, reproved(), full());
        assert_eq!(runs, [CongruenceScope::FullStore]);
        assert!(same(&verdict, &full()), "no gate published {verdict:?}");
    }
}

/// An admitting gate runs the scoped-first rule and books its outcome.
#[test]
fn an_admitting_gate_runs_the_scoped_first_rule_and_books_it() {
    let mut gate = ScopedRecheckGate::default();
    let (runs, verdict) = gated_with(Some(&mut gate), unchecked(), rejected());
    assert_eq!(runs, [CongruenceScope::Context, CongruenceScope::FullStore]);
    assert!(same(&verdict, &rejected()));
    assert_eq!(
        gate.credit,
        ScopedRecheckGate::START_CREDIT - ScopedRecheckGate::MISS_COST
    );

    let (_, verdict) = gated_with(Some(&mut gate), reproved(), reproved());
    assert!(same(&verdict, &reproved()));
    assert_eq!(
        gate.credit,
        ScopedRecheckGate::START_CREDIT - ScopedRecheckGate::MISS_COST + 1
    );
}

/// The memoized production path books its scoped runs in the memo's gate, and
/// clearing the memo starts a fresh gate.
#[test]
fn the_memoized_verifier_uses_the_memo_gate_and_clear_restarts_it() {
    let mut terms = TermStore::new();
    let (_, row2, _) = battery(&mut terms)
        .into_iter()
        .find(|(name, _, _)| *name == "row2")
        .expect("battery has row2");
    let mut memo = ConflictSemanticVerifyMemo::default();
    assert!(verify_conflict_semantic_memoized(&mut memo, &row2, &terms, &[]).is_ok());
    assert_eq!(memo.len(), 1);
    assert_eq!(
        memo.scoped_recheck_gate().credit,
        ScopedRecheckGate::START_CREDIT + 1,
        "the array conflict was re-proved by the scoped run of the memo's gate"
    );
    *memo.scoped_recheck_gate() = closed_gate();
    memo.clear();
    assert!(memo.is_empty());
    assert_eq!(*memo.scoped_recheck_gate(), ScopedRecheckGate::default());
}
