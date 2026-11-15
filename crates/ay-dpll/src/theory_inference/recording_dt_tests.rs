// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The conflict recorder's payload-free integer residual
//! (`integer_residual_kind`).
//!
//! * the lattice-closure core of the `ring_2exp16` cascade variants is
//!   recorded as `IntCgCutChain` when it is reported, not `Generic`;
//! * NEGATIVE TWINS: a core with an integer model, a divisibility conflict
//!   (left to the finalize divisibility pass) and a `Real` core keep the
//!   historical `Generic` label, and a rationally refutable equality pair
//!   keeps its Farkas label.

use super::*;
use num_bigint::BigInt;

/// A conflict over `(atom, value)` pairs and the negation cache the recorder
/// reads, spelling every negation as the raw `not` the solver uses.
fn conflict_of(terms: &mut TermStore, lits: &[(TermId, bool)]) -> ConflictInput {
    let mut negations = HashMap::default();
    let mut conflict = Vec::with_capacity(lits.len());
    for &(atom, value) in lits {
        if value {
            let negated = terms.mk_not_raw(atom);
            negations.insert(atom, negated);
        }
        conflict.push(TheoryLit::new(atom, value));
    }
    (negations, conflict)
}

type ConflictInput = (HashMap<TermId, TermId>, Vec<TheoryLit>);

/// The thirteen literals the lia-mod lattice closure reports on the
/// `ring_2exp16` cascade variant with a disjunctive multiple of three
/// (`(or (= (* 3 m1) x1) (< m1 0))`), in the solver's spelling: the carry
/// chain over `x1 = 3·m1`, `s3 + 3·m5 = 65536·c4 + tail`, and `c_i ≤ 1` with
/// the level-0 implied `¬(c_i ≤ 0)`. With `tail = 1` the bounds force
/// `Σ c_i = 4` and `3·Σ m_i = 262145`, which is no multiple of three, while
/// `Σ m_i = 262145/3` satisfies it over ℚ. With `tail = 2` it is satisfied by
/// `c_i = 1`, `x1 = m1 = m2 = m3 = m4 = 0`, `s = (-65536, -131072, -196608)`,
/// `m5 = 87382` (the core carries no bounds on `m`, `s` or `x`).
fn lattice_core(terms: &mut TermStore, tail: i64) -> Vec<(TermId, bool)> {
    let int = |terms: &mut TermStore, value: i64| terms.mk_int(BigInt::from(value));
    let var = |terms: &mut TermStore, name: &str| terms.mk_var(name, Sort::Int);
    let c: Vec<TermId> = ["c1", "c2", "c3", "c4"]
        .iter()
        .map(|n| var(terms, n))
        .collect();
    let s: Vec<TermId> = ["s1", "s2", "s3"].iter().map(|n| var(terms, n)).collect();
    let x1 = var(terms, "x1");
    let m: Vec<TermId> = ["m1", "m2", "m3", "m4", "m5"]
        .iter()
        .map(|n| var(terms, n))
        .collect();
    let (zero, one, three, word) = (
        int(terms, 0),
        int(terms, 1),
        int(terms, 3),
        int(terms, 65536),
    );
    let tail = int(terms, tail);
    let m3: Vec<TermId> = m.iter().map(|&mi| terms.mk_mul(vec![mi, three])).collect();
    let c16: Vec<TermId> = c.iter().map(|&ci| terms.mk_mul(vec![ci, word])).collect();
    let mut lits = Vec::new();
    for (lhs, rhs) in [
        (vec![s[2], m3[4]], vec![c16[3], tail]),
        (vec![c16[1], s[1]], vec![s[0], m3[2]]),
        (vec![c16[2], s[2]], vec![s[1], m3[3]]),
        (vec![c16[0], s[0]], vec![x1, m3[1]]),
    ] {
        let lhs = terms.mk_add(lhs);
        let rhs = terms.mk_add(rhs);
        lits.push((terms.mk_eq(lhs, rhs), true));
    }
    lits.push((terms.mk_eq(x1, m3[0]), true));
    for &ci in &c {
        lits.push((terms.mk_le(ci, one), true));
        lits.push((terms.mk_le(ci, zero), false));
    }
    lits
}

fn record(
    terms: &TermStore,
    negations: &HashMap<TermId, TermId>,
    conflict: &[TheoryLit],
) -> (TheoryLemmaKind, Vec<TermId>) {
    let mut tracker = ProofTracker::new();
    tracker.enable();
    let (id, annotation) = record_theory_conflict_unsat_with_annotation(
        &mut tracker,
        Some(terms),
        negations,
        conflict,
    );
    let id = id.expect("an enabled tracker records the conflict");
    let annotation = annotation.expect("a whole-conflict recording is annotated");
    let proof = tracker.take_proof();
    let Some(ay_core::ProofStep::TheoryLemma { kind, clause, .. }) = proof.get_step(id) else {
        panic!("the recorded step is a theory lemma");
    };
    assert_eq!(
        *kind, annotation.kind,
        "tracker and annotation agree on the kind"
    );
    assert_eq!(
        *clause, annotation.clause,
        "tracker and annotation agree on the clause"
    );
    (annotation.kind, annotation.clause)
}

/// The closure's core is certified when it is recorded: `IntCgCutChain`, in
/// the caller's order, and the strict checker's own recognizer accepts
/// exactly the recorded clause. Before, it was `Generic`, which the level-0
/// reconstruction closers skip.
#[test]
fn the_lattice_closure_core_is_recorded_as_a_cut_chain() {
    let mut terms = TermStore::new();
    let lits = lattice_core(&mut terms, 1);
    let (negations, conflict) = conflict_of(&mut terms, &lits);
    let (kind, clause) = record(&terms, &negations, &conflict);
    assert_eq!(kind, TheoryLemmaKind::IntCgCutChain);
    assert_eq!(
        Some(clause.clone()),
        build_blocking_clause_terms(&negations, &conflict),
        "the integer residual never reorders"
    );
    assert!(ay_core::proof_validation::recognize_int_cg_cut_chain(
        &terms, &clause
    ));
}

/// NEGATIVE TWIN: the same core with an integer model is not certified.
#[test]
fn a_lattice_core_with_an_integer_model_stays_generic() {
    let mut terms = TermStore::new();
    let lits = lattice_core(&mut terms, 2);
    let (negations, conflict) = conflict_of(&mut terms, &lits);
    let (kind, clause) = record(&terms, &negations, &conflict);
    assert_eq!(kind, TheoryLemmaKind::Generic);
    assert!(!ay_core::proof_validation::recognize_int_cg_cut_chain(
        &terms, &clause
    ));
}

/// NEGATIVE TWIN: `x = 1 ∧ x = 2` is also a guarded split the payload-free
/// funnel would type, but it is rationally refutable, and the record-time
/// rational arms keep the certificate route: the integer residual only ever
/// takes what they decline.
#[test]
fn a_rationally_refutable_equality_pair_keeps_the_farkas_route() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Int);
    let one = terms.mk_int(BigInt::from(1));
    let two = terms.mk_int(BigInt::from(2));
    let eq_one = terms.mk_eq(x, one);
    let eq_two = terms.mk_eq(x, two);
    let (negations, conflict) = conflict_of(&mut terms, &[(eq_one, true), (eq_two, true)]);
    let clause = build_blocking_clause_terms(&negations, &conflict).expect("negations cached");
    let (funnel_kind, _) =
        infer_theory_lemma_kind_from_clause_terms_and_farkas(&terms, &clause, None, None);
    assert_eq!(funnel_kind, TheoryLemmaKind::IntGuardedSplitGap);
    let (kind, _) = record(&terms, &negations, &conflict);
    assert_eq!(kind, TheoryLemmaKind::LraFarkas);
}

/// NEGATIVE TWIN: `2y = 7` is a guarded split too, but the finalize
/// divisibility pass upgrades it to the certificate-bearing `LiaGeneric` +
/// `Divisibility`, so the recorder leaves it `Generic` for that pass
/// (`test_nia_integer_divisibility_conflict_is_trust_free_and_strict_checkable`
/// pins the published label).
#[test]
fn a_divisibility_conflict_is_left_to_the_divisibility_promotion() {
    let mut terms = TermStore::new();
    let y = terms.mk_var("y", Sort::Int);
    let two = terms.mk_int(BigInt::from(2));
    let seven = terms.mk_int(BigInt::from(7));
    let two_y = terms.mk_mul(vec![two, y]);
    let equality = terms.mk_eq(two_y, seven);
    let (negations, conflict) = conflict_of(&mut terms, &[(equality, true)]);
    let clause = build_blocking_clause_terms(&negations, &conflict).expect("negation cached");
    let (funnel_kind, _) =
        infer_theory_lemma_kind_from_clause_terms_and_farkas(&terms, &clause, None, None);
    assert_eq!(funnel_kind, TheoryLemmaKind::IntGuardedSplitGap);
    assert!(ay_core::proof_validation::recognize_lia_divisibility(
        &terms, &clause
    ));
    let (kind, _) = record(&terms, &negations, &conflict);
    assert_eq!(kind, TheoryLemmaKind::Generic);
}

/// NEGATIVE TWIN: `2r = 2s + 1` has no integer model but is satisfiable over
/// `Real`; the integer residual never runs on a conflict that is not pure
/// integer arithmetic.
#[test]
fn a_real_core_stays_generic() {
    let mut terms = TermStore::new();
    let r = terms.mk_var("r", Sort::Real);
    let s = terms.mk_var("s", Sort::Real);
    let two = terms.mk_rational(num_rational::BigRational::from_integer(BigInt::from(2)));
    let one = terms.mk_rational(num_rational::BigRational::from_integer(BigInt::from(1)));
    let two_r = terms.mk_mul(vec![two, r]);
    let two_s = terms.mk_mul(vec![two, s]);
    let rhs = terms.mk_add(vec![two_s, one]);
    let equality = terms.mk_eq(two_r, rhs);
    let (negations, conflict) = conflict_of(&mut terms, &[(equality, true)]);
    let (kind, _) = record(&terms, &negations, &conflict);
    assert_eq!(kind, TheoryLemmaKind::Generic);
}

/// The record-time residual BEFORE the integer-arm gate: the whole funnel,
/// adopted only for a payload-free integer kind in the caller's order. Kept
/// here as the reference the gated recorder must agree with on every clause.
fn ungated_residual_kind(
    terms: &TermStore,
    conflict: &[TheoryLit],
    clause: &[TermId],
) -> TheoryLemmaKind {
    if !arith_conflict_is_integer(terms, conflict) {
        return TheoryLemmaKind::Generic;
    }
    let (kind, ordered) =
        infer_theory_lemma_kind_from_clause_terms_and_farkas(terms, clause, None, None);
    let adopt = matches!(ordered, Cow::Borrowed(_))
        && match kind {
            TheoryLemmaKind::IntBoundLatticeGap | TheoryLemmaKind::IntCgCutChain => true,
            TheoryLemmaKind::IntGuardedSplitGap => {
                !ay_core::proof_validation::recognize_lia_divisibility(terms, clause)
            }
            _ => false,
        };
    if adopt {
        kind
    } else {
        TheoryLemmaKind::Generic
    }
}

/// The NIA conflict shape of the `u64` square-overflow query
/// `0 <= g <= 2^64-1 ∧ (g·g < 0 ∨ g·g > 2^64-1)`: a decision bound
/// `g <= 2^32-1` with the bounds and `g·g > 2^64-1` has no model. It is
/// all-integer, so it reaches the integer residual, and it is univariate, so
/// the funnel's NRA root isolation decides it before the integer arms run.
fn square_overflow_core(terms: &mut TermStore) -> Vec<(TermId, bool)> {
    let g = terms.mk_var("g", Sort::Int);
    let zero = terms.mk_int(BigInt::from(0));
    let u64_max = terms.mk_int(BigInt::from(u64::MAX));
    let u32_max = terms.mk_int(BigInt::from(u32::MAX));
    let square = terms.mk_mul(vec![g, g]);
    vec![
        (terms.mk_le(zero, g), true),
        (terms.mk_le(g, u64_max), true),
        (terms.mk_le(g, u32_max), true),
        (terms.mk_le(square, u64_max), false),
    ]
}

/// Every clause above, through the gated recorder and the ungated
/// reference: the gate changes no label.
#[test]
fn the_integer_arm_gate_changes_no_label() {
    let mut terms = TermStore::new();
    let mut cases = vec![
        lattice_core(&mut terms, 1),
        lattice_core(&mut terms, 2),
        square_overflow_core(&mut terms),
    ];
    let x = terms.mk_var("x", Sort::Int);
    let y = terms.mk_var("y", Sort::Int);
    let (one, two, seven) = (
        terms.mk_int(BigInt::from(1)),
        terms.mk_int(BigInt::from(2)),
        terms.mk_int(BigInt::from(7)),
    );
    let two_y = terms.mk_mul(vec![two, y]);
    cases.push(vec![
        (terms.mk_eq(x, one), true),
        (terms.mk_eq(x, two), true),
    ]);
    cases.push(vec![(terms.mk_eq(two_y, seven), true)]);
    for lits in cases {
        let (negations, conflict) = conflict_of(&mut terms, &lits);
        let clause = build_blocking_clause_terms(&negations, &conflict).expect("negations cached");
        let gated = integer_residual_kind(&terms, &conflict, &clause, None);
        let reference = ungated_residual_kind(&terms, &conflict, &clause);
        assert_eq!(gated, reference, "the gate relabelled {lits:?}");
    }
}

/// REGRESSION (ay 01b58012 vs 630e4d62, QF_NIA `u64` square overflow 0.05 s
/// -> 1.1 s): a NIA conflict no integer arm takes is recorded `Generic`
/// without asking the funnel, whose univariate NRA root isolation over
/// 64-bit bounds ran on every conflict of a SAT query.
#[test]
fn a_nia_conflict_no_integer_arm_takes_never_asks_the_funnel() {
    let mut terms = TermStore::new();
    let lits = square_overflow_core(&mut terms);
    let (negations, conflict) = conflict_of(&mut terms, &lits);
    let clause = build_blocking_clause_terms(&negations, &conflict).expect("negations cached");
    assert!(
        arith_conflict_is_integer(&terms, &conflict),
        "the conflict reaches the integer residual, so the gate is what declines it"
    );
    let kind = integer_residual_kind_with(&terms, &conflict, &clause, || {
        panic!("the funnel was asked for a clause no integer arm takes")
    });
    assert_eq!(kind, TheoryLemmaKind::Generic);
    let (recorded, _) = record(&terms, &negations, &conflict);
    assert_eq!(recorded, TheoryLemmaKind::Generic);
}

/// The gate's other side: a clause an integer arm takes still asks the whole
/// funnel exactly once and adopts its answer.
#[test]
fn a_clause_an_integer_arm_takes_asks_the_funnel_once() {
    let mut terms = TermStore::new();
    let lits = lattice_core(&mut terms, 1);
    let (negations, conflict) = conflict_of(&mut terms, &lits);
    let clause = build_blocking_clause_terms(&negations, &conflict).expect("negations cached");
    let mut asked = 0;
    let kind = integer_residual_kind_with(&terms, &conflict, &clause, || {
        asked += 1;
        (TheoryLemmaKind::IntCgCutChain, true)
    });
    assert_eq!((kind, asked), (TheoryLemmaKind::IntCgCutChain, 1));
}
