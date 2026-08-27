// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! `SemanticChargeClass::ClauseIdentityRoute` — the syntax-only clause-identity
//! rules `reordering`, `weakening` and `eq_reflexive`.
//!
//! # What is being pinned
//!
//! The `General` product bills these three the SQUARE of the TREE-unfolded step
//! payload, while every one of their validators reads clause literals as opaque
//! `TermId`s and never descends into one. On a heavily shared `store` chain the
//! two differ astronomically, and that difference converted a correct `unsat`
//! into `unknown (self-check-rejected)` on
//! `benchmarks/smt/QF_AUFLIA/storeinv_nf_size7.smt2`.
//!
//! The replacement charge has to be BOTH:
//!
//!  1. an UPPER BOUND on what the validators actually do — pinned here against
//!     payloads produced by the real metering walk over real terms, not against
//!     hand-written `PayloadStats`; and
//!  2. a TIGHTENING of the charge it replaces, so no proof that fits the
//!     caller's envelope today can stop fitting it and the corpus-wide
//!     `ResourceLimit` count cannot rise.
//!
//! Every adversarial case below names its concrete input and checks the CHARGE
//! in-test.

use super::*;

/// Run ONE step through the real strict validator, with the premise clauses the
/// meter saw. The tests below use this to establish that each adversarial step
/// is genuinely VALID, so what they measure is a metering question and not a
/// validity one.
fn validate_one(
    terms: &TermStore,
    step: &ProofStep,
    derived: &[Option<Vec<TermId>>],
) -> Result<(), ProofCheckError> {
    let mut table: Vec<Option<Vec<TermId>>> = derived.to_vec();
    let step_id = ProofId(table.len() as u32);
    let mut unbounded = |_: usize, _: usize| true;
    validate_step_with_datatypes_and_progress(
        terms,
        &mut table,
        step_id,
        step,
        true,
        None,
        None,
        None,
        None,
        None,
        None,
        None,
        &mut unbounded,
    )
}

/// The charge main took for these steps BEFORE this class existed: the
/// `General` recursive-tree product with no private per-rule scale (all three
/// rules fall through `private_validator_charge`'s `_ => (0, 0)` arm).
fn legacy_general_charge(stats: PayloadStats) -> usize {
    let named = stats.work.saturating_mul(stats.unfolded_work);
    let paired = stats.unfolded_work.saturating_mul(stats.unfolded_work);
    named.max(paired)
}

fn clause_identity_step(rule: &AletheRule, clause: Vec<TermId>, premises: usize) -> ProofStep {
    ProofStep::Step {
        rule: rule.clone(),
        clause,
        premises: (0..premises).map(|index| ProofId(index as u32)).collect(),
        args: Vec::new(),
    }
}

fn payload(work: usize, unfolded: usize) -> PayloadStats {
    PayloadStats {
        work,
        bytes: 64,
        unfolded_work: unfolded,
        order_assignments: 0,
    }
}

fn charge(step: &ProofStep, stats: PayloadStats) -> (usize, usize) {
    semantic_validator_charge(step, stats, SemanticChargeClass::ClauseIdentityRoute)
        .expect("the modelled charge stays far below usize overflow")
}

/// Build a `store` chain whose VALUE at each level reads the chain below it, so
/// the reachable DAG grows LINEARLY while the tree unfolding DOUBLES per level.
///
/// This is the exact shape of `storeinv_nf_size7.smt2`'s clauses and of
/// `ay-dpll`'s `a_rewrite_that_would_cost_a_certification_is_reverted`.
fn shared_store_chain(terms: &mut TermStore, tag: &str, depth: usize) -> TermId {
    let element = Sort::Uninterpreted("Elem".to_string());
    let array = Sort::Array(Box::new(ay_core::ArraySort {
        index_sort: Sort::Int,
        element_sort: element.clone(),
    }));
    let key = terms.mk_var(format!("{tag}_k"), Sort::Int);
    let mut chain = terms.mk_var(format!("{tag}_a"), array.clone());
    for level in 0..depth {
        let index = terms.mk_var(format!("{tag}_i{level}"), Sort::Int);
        let value = terms.mk_app(Symbol::named("select"), vec![chain, key], element.clone());
        chain = terms.mk_app(
            Symbol::named("store"),
            vec![chain, index, value],
            array.clone(),
        );
    }
    chain
}

/// Run the REAL per-step metering walk and return the payload it produces, so
/// the tests below are pinned against production `PayloadStats` rather than
/// against numbers chosen to make the assertion pass.
fn measured_payload(
    step: &ProofStep,
    terms: &TermStore,
    derived: &[Option<Vec<TermId>>],
) -> PayloadStats {
    let mut memo = TermCostMemo::default();
    let mut unbounded = |_: usize, _: usize| true;
    meter_step_term_payload(step, terms, derived, &mut memo, &mut unbounded)
        .expect("an unbounded envelope always completes the payload walk")
}

/// The three rules route to the DAG-bounded class, and the rules deliberately
/// left OUT of it do not.
///
/// `contraction` is the named exclusion: its validator runs three nested
/// `contains` scans over the clause and the premise, so it is genuinely
/// quadratic in the clause length and the `General` product already models it
/// with the right SHAPE.
#[test]
fn clause_identity_family_routes_to_the_dag_bounded_class() {
    let terms = TermStore::new();
    for rule in [
        AletheRule::Reordering,
        AletheRule::Weakening,
        AletheRule::EqReflexive,
    ] {
        let label = format!("{rule:?}");
        let step = clause_identity_step(&rule, Vec::new(), 1);
        assert_eq!(
            select_semantic_charge_class(&step, &terms),
            SemanticChargeClass::ClauseIdentityRoute,
            "{label} must use the DAG-bounded clause-identity route"
        );
    }
    for rule in [
        AletheRule::Contraction,
        AletheRule::EqSymmetric,
        AletheRule::And,
        AletheRule::NotOr,
    ] {
        let label = format!("{rule:?}");
        let step = clause_identity_step(&rule, Vec::new(), 1);
        assert_eq!(
            select_semantic_charge_class(&step, &terms),
            SemanticChargeClass::General,
            "{label} must NOT be admitted to the clause-identity route"
        );
    }
    // The classes that must keep winning the ordering race in
    // `select_semantic_charge_class`.
    let or_step = clause_identity_step(&AletheRule::Or, Vec::new(), 1);
    assert_eq!(
        select_semantic_charge_class(&or_step, &terms),
        SemanticChargeClass::UnorderedClauseMatch
    );
    let trans = clause_identity_step(&AletheRule::EqTransitive, Vec::new(), 1);
    assert_eq!(
        select_semantic_charge_class(&trans, &terms),
        SemanticChargeClass::EufIdentityRoute
    );
}

/// TIGHTENING: over a wide payload sweep the class never charges more than the
/// `General` product it replaces, on either limb. This is the property that
/// makes the corpus-wide `ResourceLimit` count unable to RISE.
#[test]
fn clause_identity_never_charges_more_than_the_general_product() {
    let mut strictly_cheaper = 0_usize;
    for rule in [
        AletheRule::Reordering,
        AletheRule::Weakening,
        AletheRule::EqReflexive,
    ] {
        let step = clause_identity_step(&rule, Vec::new(), 1);
        for unfolded in [
            1_usize, 2, 3, 8, 16, 64, 733, 1_169, 4_096, 18_708, 100_000, 20_000_000,
        ] {
            for work in [1_usize, 2, unfolded / 2 + 1, unfolded, unfolded * 4 + 7] {
                let stats = payload(work, unfolded);
                let (tight, bytes) = charge(&step, stats);
                let legacy = legacy_general_charge(stats);
                assert!(
                    tight <= legacy,
                    "tightening must never charge more: {rule:?} unfolded={unfolded} \
                     work={work} tight={tight} legacy={legacy}"
                );
                assert_eq!(
                    bytes, stats.bytes,
                    "the byte limb must stay exactly where `General` left it"
                );
                if tight < legacy {
                    strictly_cheaper += 1;
                }
            }
        }
    }
    assert!(
        strictly_cheaper > 0,
        "the class must actually be cheaper somewhere, else it is a no-op"
    );
}

/// ADVERSARIAL 1 — DEEP SHARING, the reproducer's own shape.
///
/// A 40-level `store` chain whose value at each level reads the chain below it:
/// the reachable DAG is linear in the depth, the tree unfolding is exponential.
/// The clause is `(cl (= left right) (not (= left right)))`, a `reordering`
/// premise/conclusion pair over those chains.
///
/// Checks, on the payload the REAL metering walk produces for that step:
///  * the tree-unfolded payload is astronomically larger than the DAG, so the
///    input really is adversarial;
///  * the `General` product alone exceeds the whole 350M envelope;
///  * the new charge fits the envelope with orders of magnitude to spare; and
///  * the new charge is STILL an upper bound on the validator's own work —
///    `payload.work >= 2n` for the literal count `n` the validator sorts, so
///    the modelled sort bound dominates it.
#[test]
fn a_deeply_shared_store_chain_is_charged_on_its_dag_and_still_bounds_the_sort() {
    const PRODUCTION_ENVELOPE: usize = 350_000_000;
    let mut terms = TermStore::new();
    let left = shared_store_chain(&mut terms, "deep_left", 40);
    let right = shared_store_chain(&mut terms, "deep_right", 40);
    let equality = terms.mk_app(Symbol::named("="), vec![left, right], Sort::Bool);
    let negated = terms.mk_not_raw(equality);
    let premise_clause = vec![equality, negated];
    let clause = vec![negated, equality];
    let derived = vec![Some(premise_clause.clone())];
    let step = clause_identity_step(&AletheRule::Reordering, clause.clone(), 1);
    let stats = measured_payload(&step, &terms, &derived);

    assert!(
        stats.unfolded_work > 1_000_000_000,
        "the input must really unfold exponentially: unfolded={}",
        stats.unfolded_work
    );
    assert!(
        stats.work < stats.unfolded_work / 1_000_000,
        "the reachable DAG must stay tiny beside it: work={} unfolded={}",
        stats.work,
        stats.unfolded_work
    );

    // The step is VALID — this is a permutation of its premise — so what
    // follows is a metering question, not a validity one.
    validate_one(&terms, &step, &derived).expect("the conclusion IS a permutation of the premise");

    let legacy = legacy_general_charge(stats);
    assert!(
        legacy > PRODUCTION_ENVELOPE,
        "the `General` product must reproduce the measured refusal: {legacy}"
    );
    let (tight, _) = charge(&step, stats);
    assert!(
        tight < PRODUCTION_ENVELOPE / 100,
        "the DAG-bounded charge must fit the envelope with room: {tight}"
    );
    assert!(
        legacy / tight > 1_000_000,
        "and it must be orders of magnitude below the product it replaces: \
         legacy={legacy} tight={tight}"
    );

    // The upper-bound argument, checked rather than asserted: the literal count
    // the validator sorts is bounded by half the metered DAG payload, and the
    // charge dominates a comparison-sort bound over it.
    let literals = clause.len() + premise_clause.len();
    assert!(
        stats.work >= 2 * literals,
        "the payload walk must debit at least two units per metered literal: \
         work={} literals={literals}",
        stats.work
    );
    assert!(
        tight >= CLAUSE_IDENTITY_WORK_FACTOR * comparison_sort_bound(literals),
        "the charge must dominate a comparison sort over the clause and its \
         premise: charge={tight} literals={literals}"
    );
}

/// ADVERSARIAL 2 — WIDE FAN-OUT.
///
/// One `reordering` step over a 4_096-literal clause and its 4_096-literal
/// premise, every literal a distinct variable. There is no sharing to exploit
/// here; the point is that the charge must still dominate the two real sorts,
/// and that `payload.work >= 2n` still holds when `n` is large.
#[test]
fn a_wide_fan_out_clause_is_still_charged_above_its_two_sorts() {
    const WIDTH: usize = 4_096;
    let mut terms = TermStore::new();
    let premise_clause: Vec<TermId> = (0..WIDTH)
        .map(|index| terms.mk_var(format!("wide_lit_{index}"), Sort::Bool))
        .collect();
    let mut clause = premise_clause.clone();
    clause.reverse();
    let derived = vec![Some(premise_clause.clone())];
    let step = clause_identity_step(&AletheRule::Reordering, clause.clone(), 1);
    let stats = measured_payload(&step, &terms, &derived);

    validate_one(&terms, &step, &derived).expect("a reversal IS a permutation");

    let literals = clause.len() + premise_clause.len();
    assert_eq!(literals, 2 * WIDTH);
    assert!(
        stats.work >= 2 * literals,
        "work={} literals={literals}",
        stats.work
    );
    let (tight, _) = charge(&step, stats);
    assert!(
        tight >= CLAUSE_IDENTITY_WORK_FACTOR * comparison_sort_bound(literals),
        "charge={tight} literals={literals}"
    );
    // And it is genuinely cheaper than the product it replaces, which on this
    // shape is quadratic in the whole term payload.
    assert!(tight < legacy_general_charge(stats));
}

/// ADVERSARIAL 3 — the other two validators, on the same deep-sharing input.
///
/// `weakening` compares a prefix and `eq_reflexive` decodes one literal; both
/// must be charged above their own work and below the envelope even when the
/// literal they carry unfolds exponentially.
#[test]
fn weakening_and_eq_reflexive_over_exponential_literals_stay_bounded() {
    const PRODUCTION_ENVELOPE: usize = 350_000_000;
    let mut terms = TermStore::new();
    let chain = shared_store_chain(&mut terms, "wk", 40);
    let reflexive = terms.mk_app(Symbol::named("="), vec![chain, chain], Sort::Bool);
    let extra = terms.mk_var("wk_extra", Sort::Bool);

    // weakening: premise `(cl reflexive)`, conclusion `(cl reflexive extra)`.
    let premise_clause = vec![reflexive];
    let clause = vec![reflexive, extra];
    let derived = vec![Some(premise_clause.clone())];
    let weakening = clause_identity_step(&AletheRule::Weakening, clause.clone(), 1);
    validate_one(&terms, &weakening, &derived).expect("the premise IS a prefix of the conclusion");
    let stats = measured_payload(&weakening, &terms, &derived);
    assert!(stats.unfolded_work > 1_000_000_000);
    assert!(legacy_general_charge(stats) > PRODUCTION_ENVELOPE);
    let (tight, _) = charge(&weakening, stats);
    assert!(
        tight < PRODUCTION_ENVELOPE / 100,
        "weakening charge must fit the envelope: {tight}"
    );
    let literals = clause.len() + premise_clause.len();
    assert!(stats.work >= 2 * literals);
    assert!(tight >= CLAUSE_IDENTITY_WORK_FACTOR * comparison_sort_bound(literals));

    // eq_reflexive: a premiseless unit `(cl (= chain chain))`.
    let unit = vec![reflexive];
    let step = clause_identity_step(&AletheRule::EqReflexive, unit.clone(), 0);
    validate_one(&terms, &step, &[]).expect("the equality IS reflexive");
    let stats = measured_payload(&step, &terms, &[]);
    assert!(stats.unfolded_work > 1_000_000_000);
    assert!(legacy_general_charge(stats) > PRODUCTION_ENVELOPE);
    let (tight, _) = charge(&step, stats);
    assert!(
        tight < PRODUCTION_ENVELOPE / 100,
        "eq_reflexive charge must fit the envelope: {tight}"
    );
    assert!(
        tight >= CLAUSE_IDENTITY_WORK_FACTOR,
        "even an O(1) validator is charged for its constant-time guards: {tight}"
    );
}

/// PARITY: the route is not a blanket exemption. A step whose REACHABLE DAG is
/// genuinely enormous still grows its charge and is still refused before the
/// validator runs, so admission stays an a-priori reservation.
#[test]
fn a_genuinely_huge_dag_payload_is_still_refused_up_front() {
    const PRODUCTION_ENVELOPE: usize = 350_000_000;
    let step = clause_identity_step(&AletheRule::Reordering, Vec::new(), 1);
    let narrow = charge(&step, payload(1_000, 1_000_000)).0;
    let wide = charge(&step, payload(1_000_000, 1_000_000)).0;
    assert!(
        wide > narrow,
        "the charge must grow with the step's real DAG work: {narrow} -> {wide}"
    );
    // 20M reachable nodes, each of which the payload walk really did visit.
    let huge = charge(&step, payload(20_000_000, 20_000_000)).0;
    assert!(
        huge > PRODUCTION_ENVELOPE,
        "a genuinely huge DAG payload must still exhaust the envelope: {huge}"
    );
}

/// The end-to-end refusal, through the production entry point rather than the
/// charge function: a `reordering` step whose payload the caller's envelope
/// cannot afford is declined with `ResourceLimit`, and the same proof under an
/// unbounded envelope validates. Without the second half the first proves
/// nothing about the METER.
#[test]
fn the_metering_still_refuses_an_oversized_clause_identity_proof() {
    let mut terms = TermStore::new();
    let literals: Vec<TermId> = (0..2_048)
        .map(|index| terms.mk_var(format!("refuse_lit_{index}"), Sort::Bool))
        .collect();
    let mut reordered = literals.clone();
    reordered.reverse();
    let mut proof = Proof::new();
    proof.add_step(ProofStep::Step {
        rule: AletheRule::Trust,
        clause: literals.clone(),
        premises: Vec::new(),
        args: Vec::new(),
    });
    proof.add_step(ProofStep::Step {
        rule: AletheRule::Reordering,
        clause: reordered,
        premises: vec![ProofId(0)],
        args: Vec::new(),
    });

    let mut spent = 0_usize;
    let mut tiny = |work: usize, _bytes: usize| {
        spent += work;
        spent <= 64
    };
    let refused =
        check_proof_strict_with_context_and_progress(&proof, &terms, None, None, None, &mut tiny)
            .expect_err("a 64-unit envelope cannot afford a 2048-literal reordering");
    assert_eq!(refused, ProofCheckError::ResourceLimit);

    let mut unbounded = |_: usize, _: usize| true;
    let accepted = check_proof_strict_with_context_and_progress(
        &proof,
        &terms,
        None,
        None,
        None,
        &mut unbounded,
    );
    assert!(
        !matches!(accepted, Err(ProofCheckError::ResourceLimit)),
        "the same proof must not be resource-refused under an unbounded \
         envelope, or the test above proves nothing about the METER: {accepted:?}"
    );
}

/// `ceil(log2(n))`, computed by search rather than by bit tricks so it is an
/// INDEPENDENT witness for the property below.
fn ceil_log2(n: usize) -> usize {
    let mut bits = 0_usize;
    while (1_usize << bits) < n {
        bits += 1;
    }
    bits
}

/// [`comparison_sort_bound`] is at least `n + n*log2(n)` at every `n` a proof
/// can carry — one linear pass plus one `O(n log n)` sort. That inequality is
/// what the whole upper-bound argument rests on, so it is checked here against
/// an independently computed `ceil(log2(n))` (which dominates `log2(n)`) rather
/// than against the implementation's own bit arithmetic.
#[test]
fn comparison_sort_bound_dominates_n_plus_n_log2_n() {
    assert_eq!(comparison_sort_bound(0), 0);
    assert_eq!(ceil_log2(1), 0);
    assert_eq!(ceil_log2(2), 1);
    assert_eq!(ceil_log2(3), 2);
    for shift in 0..40_u32 {
        for offset in [0_usize, 1, 7] {
            let n = (1_usize << shift) + offset;
            let bound = comparison_sort_bound(n);
            let sort = n.saturating_mul(ceil_log2(n));
            assert!(
                bound >= sort.saturating_add(n),
                "n={n} bound={bound} sort={sort}: the bound must cover one \
                 O(n log n) sort AND one linear pass"
            );
        }
    }
    // Saturating, not wrapping, at the top of the range.
    assert_eq!(comparison_sort_bound(usize::MAX), usize::MAX);
}

/// Where the tightening cap BINDS, and what it costs.
///
/// The cap can only ever select the value the shipped `General` model already
/// charges, so the charge is never larger than today's. It binds only when the
/// tree-unfolded payload is SMALL relative to the DAG payload — i.e. for steps
/// carrying at most a few dozen literals, where the modelled work is a few
/// hundred operations. This test measures the crossover rather than asserting
/// it, so a future change to either side shows up here.
#[test]
fn the_tightening_cap_binds_only_on_tiny_unfolded_payloads() {
    let step = clause_identity_step(&AletheRule::Reordering, Vec::new(), 1);
    let work = 4_096_usize;
    let modelled =
        CLAUSE_IDENTITY_WORK_FACTOR * comparison_sort_bound(work) + CLAUSE_IDENTITY_WORK_FACTOR;
    let mut crossover = None;
    for unfolded in 1..=512_usize {
        let stats = payload(work, unfolded);
        let (tight, _) = charge(&step, stats);
        let capped = tight < modelled;
        if !capped && crossover.is_none() {
            crossover = Some(unfolded);
        }
        assert_eq!(
            tight,
            modelled.min(legacy_general_charge(stats)),
            "unfolded={unfolded}"
        );
    }
    let crossover = crossover.expect("the model must win somewhere in the sweep");
    // The `+ CLAUSE_IDENTITY_WORK_FACTOR` tail is what pays for `eq_reflexive`'s
    // constant-time guards when the sort bound itself is zero. It is visible
    // only where the cap does not already zero the charge, which the production
    // walk cannot reach (a `work = 0` payload has no roots, hence
    // `unfolded_work = 0` too) — so it is pinned here directly.
    assert_eq!(charge(&step, payload(0, 0)).0, 0);
    assert_eq!(
        charge(&step, payload(0, 3)).0,
        CLAUSE_IDENTITY_WORK_FACTOR,
        "an empty sort bound must still pay for the validator's O(1) guards"
    );
    assert!(
        (2..=128).contains(&crossover),
        "the cap must stop binding while the step is still tiny: crossover={crossover}"
    );
    // Above the crossover the charge is the model and no longer tracks the
    // unfolded payload at all — the whole point of the class.
    assert_eq!(charge(&step, payload(work, 100_000)).0, modelled);
    assert_eq!(charge(&step, payload(work, 100_000_000)).0, modelled);
}

/// Each guard deleted or weakened, `ay-proof --lib` re-run, the named test
/// OBSERVED failing, then restored. Run recorded 2026-08-22, one mutation at a
/// time. `NEGATIVE` rows are results, not omissions.
pub(super) const CLAUSE_IDENTITY_GUARD_LEDGER: &[(&str, &str)] = &[
    (
        "is_clause_identity_route: Reordering in the rule list",
        "RED — clause_identity_family_routes_to_the_dag_bounded_class",
    ),
    (
        "is_clause_identity_route: Weakening in the rule list",
        "RED — clause_identity_family_routes_to_the_dag_bounded_class",
    ),
    (
        "is_clause_identity_route: EqReflexive in the rule list",
        "RED — clause_identity_family_routes_to_the_dag_bounded_class",
    ),
    (
        "is_clause_identity_route: Contraction NOT in the rule list",
        "RED — clause_identity_family_routes_to_the_dag_bounded_class. \
         SOUNDNESS-RELEVANT: `validate_contraction` runs three nested `contains` \
         scans over the clause and the premise, so its real work is QUADRATIC \
         in the clause length and a linearithmic charge would not bound it.",
    ),
    (
        "clause_identity_route_charge: the `.min(replaced_general_product)` cap",
        "RED — clause_identity_never_charges_more_than_the_general_product and \
         the_tightening_cap_binds_only_on_tiny_unfolded_payloads. The cap is \
         what makes the corpus-wide `ResourceLimit` count unable to RISE.",
    ),
    (
        "clause_identity_route_charge: the `+ CLAUSE_IDENTITY_WORK_FACTOR` tail",
        "RED — the_tightening_cap_binds_only_on_tiny_unfolded_payloads. The tail \
         pays for `eq_reflexive`'s O(1) guards when the sort bound is zero. \
         MEASURED SCOPE: it cannot change a production charge, because a \
         `work = 0` payload has no roots and therefore `unfolded_work = 0` too, \
         at which point the tightening cap zeroes the charge anyway. Kept and \
         pinned so the model stays an upper bound if either side moves.",
    ),
    (
        "comparison_sort_bound: the `bits + 1` multiplier",
        "RED — comparison_sort_bound_dominates_n_plus_n_log2_n. Dropping the \
         `+ 1` leaves `n * ceil(log2 n)`, which covers the SORT but not the \
         linear clone/compare passes on top of it. Recorded as a first-pass \
         NEGATIVE: the original assertion only required `n * (floor(log2 n)+1)` \
         and the mutation passed it, so the test was strengthened to compare \
         against an independently computed `ceil_log2`.",
    ),
    (
        "comparison_sort_bound: `saturating_mul`",
        "RED — comparison_sort_bound_dominates_n_plus_n_log2_n, via its \
         `usize::MAX` assertion (`wrapping_mul` returns `usize::MAX - 63`). \
         Saturation is the CONSERVATIVE direction for a value used only as a \
         bound: growing it can never undercharge.",
    ),
    (
        "select_semantic_charge_class: the clause-identity probe placed AFTER \
         every other modelled route",
        "NEGATIVE — hoisting the probe to the TOP of the function (ahead of \
         `ResolutionRoute`) fails no test, because no other route's predicate \
         can match `Reordering` / `Weakening` / `EqReflexive`: the resolution, \
         datatype, array, Farkas, EUF-identity, bool-tautology, `or` and \
         trust-kind arms all key on disjoint rules or on `TheoryLemma`. \
         Ordering is kept because it is the function's stated convention — \
         every kind with its own modelled route keeps it — not because it is \
         load-bearing.",
    ),
    (
        "ay-dpll `rewrite_loses_certification` (the congruence lane's revert \
         gate, which this change stops triggering on \
         `reordering`/`weakening`/`eq_reflexive`)",
        "RED — ay-dpll's a_rewrite_that_would_cost_a_certification_is_reverted, \
         after retargeting that fixture onto `contraction`, the one rule the \
         derivation emits that is still `class=General`. Verified by returning \
         `false` unconditionally from the gate.",
    ),
];

#[test]
fn clause_identity_guard_ledger_is_present() {
    assert!(CLAUSE_IDENTITY_GUARD_LEDGER.len() >= 8);
}
