// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Every guard of the congruence-explanation lowering, and the proof that each
//! leaves its lemma BYTE-IDENTICAL.
//!
//! **Every proof here is a COMPLETE refutation.** That is load-bearing: the
//! lane's last backstop reverts wholesale when `check_proof` refuses the
//! rebuilt proof, and a truncated fixture is refused for THAT reason — so a
//! guard test built on one would pass with its guard deleted, and the mutation
//! ledger would be worthless. Measured: eight of these tests were green under
//! their own mutations until the fixtures were completed.
//!
//! Split out of `congruence_explanation_tests` so each file stays inside the
//! repository's per-file line ceiling; the `GUARD_MUTATION_LEDGER` for these
//! tests is in that file's module documentation.

use super::*;

use ay_core::kani_compat::DetHashMap;
use ay_core::{ArraySort, Sort, Symbol};

fn unchanged(executor: &mut Executor, proof: &mut Proof) {
    let before = format!("{:?}", proof.steps);
    assert_eq!(executor.derive_congruence_explanations(proof), 0);
    assert_eq!(
        format!("{:?}", proof.steps),
        before,
        "a declined lemma must be left byte-identical"
    );
}

/// The FLAT complete refutation of `a = b ∧ f(a) ≠ f(b)`, with `leaf` in place
/// of its explanation lemma.
fn flat_refutation(link: &Congruence, leaf: ProofStep) -> Proof {
    let mut proof = Proof::new();
    proof.add_step(ProofStep::Assume(link.eq_ab)); // t0
    proof.add_step(ProofStep::Assume(link.not_fab)); // t1
    proof.add_step(leaf); // t2
    proof.add_step(ProofStep::Resolution {
        clause: vec![link.eq_fab],
        pivot: link.eq_ab,
        clause1: ProofId(2),
        clause2: ProofId(0),
    }); // t3
    proof.add_step(ProofStep::Resolution {
        clause: Vec::new(),
        pivot: link.eq_fab,
        clause1: ProofId(3),
        clause2: ProofId(1),
    }); // t4
    proof
}

/// PRECONDITION for every test below: the same fixture WITHOUT its
/// malformation is lowered. A guard test only means something if the lane
/// would otherwise fire.
#[test]
fn the_guard_fixture_is_lowered_when_nothing_is_malformed() {
    let mut executor = Executor::new();
    let link = congruence(&mut executor, "fixture");
    let mut flat = flat_refutation(&link, explanation_lemma(vec![link.not_ab, link.eq_fab]));
    assert_eq!(executor.derive_congruence_explanations(&mut flat), 1);
    let (mut packed, _children) = packed_refutation(&mut executor, &link);
    assert_eq!(executor.derive_congruence_explanations(&mut packed), 1);
}

#[test]
fn a_proof_carrying_an_anchor_is_left_alone() {
    let mut executor = Executor::new();
    let link = congruence(&mut executor, "anchor");
    let (mut proof, _flat) = packed_refutation(&mut executor, &link);
    proof.add_step(ProofStep::Anchor {
        end_step: ProofId(5),
        variables: Vec::new(),
    });
    unchanged(&mut executor, &mut proof);
}

#[test]
fn a_lemma_that_still_carries_a_farkas_payload_is_left_alone() {
    let mut executor = Executor::new();
    let link = congruence(&mut executor, "farkas");
    // A surviving POSITIONAL certificate is consumed by trace rebinding and
    // the printer, not by these validators: splitting the step would strand
    // it.
    let mut proof = flat_refutation(
        &link,
        ProofStep::TheoryLemma {
            theory: "EUF".to_string(),
            clause: vec![link.not_ab, link.eq_fab],
            farkas: Some(ay_core::FarkasAnnotation {
                coefficients: vec![1i64.into(), 1i64.into()],
            }),
            kind: TheoryLemmaKind::EufCongruenceExplanation,
            lia: None,
        },
    );
    unchanged(&mut executor, &mut proof);
}

/// The three fixtures below were `*_is_left_alone` guards until the RE-PACK
/// arm landed, and the change is recorded rather than hidden: the flat path
/// still requires exactly one matching `or` consumer, and everything else now
/// takes an arm that REBUILDS the packed unit, so no consumer is touched at
/// all. What those guards protected — "a consumer must never see a clause it
/// did not see before" — is now pinned DIRECTLY and more strongly, by
/// `repacked`: the fragment's last clause is byte-identical to the lemma's,
/// every consumer step keeps its rule and its clause, and the rebuilt proof
/// still checks.
fn repacked(executor: &mut Executor, proof: &mut Proof, packed: TermId) {
    let consumers: Vec<(String, Vec<TermId>)> = proof
        .steps
        .iter()
        .filter_map(|step| match step {
            ProofStep::Step {
                rule,
                clause,
                premises,
                ..
            } if premises.contains(&ProofId(2)) => Some((rule.name().to_string(), clause.clone())),
            _ => None,
        })
        .collect();
    assert!(!consumers.is_empty(), "the fixture must have a consumer");
    assert_eq!(executor.derive_congruence_explanations(proof), 1);
    assert!(
        !proof.steps.iter().any(|step| matches!(
            step,
            ProofStep::TheoryLemma {
                kind: TheoryLemmaKind::EufCongruenceExplanation,
                ..
            }
        )),
        "the lemma must be gone"
    );
    assert!(
        proof.steps.iter().any(|step| matches!(
            step,
            ProofStep::Step { clause, .. } if clause.as_slice() == [packed]
        )),
        "the fragment must end on the lemma's own clause, byte for byte"
    );
    for (rule, clause) in consumers {
        assert!(
            proof.steps.iter().any(|step| matches!(
                step,
                ProofStep::Step { rule: other, clause: other_clause, .. }
                    if other.name() == rule && *other_clause == clause
            )),
            "consumer {rule} lost its clause"
        );
    }
    assert!(
        ay_proof::check_proof(proof, &executor.ctx.terms).is_ok(),
        "the rebuilt proof must check"
    );
}

#[test]
fn a_packed_leaf_whose_consumer_is_not_an_or_step_is_repacked_in_place() {
    let mut executor = Executor::new();
    let link = congruence(&mut executor, "consumer");
    let (mut proof, flat) = packed_refutation(&mut executor, &link);
    let packed = or_term(&mut executor, flat.clone());
    proof.steps[3] = ProofStep::Step {
        rule: AletheRule::Contraction,
        clause: flat,
        premises: vec![ProofId(2)],
        args: Vec::new(),
    };
    repacked(&mut executor, &mut proof, packed);
}

#[test]
fn a_consumer_whose_clause_is_not_the_flattened_children_is_repacked_in_place() {
    let mut executor = Executor::new();
    let link = congruence(&mut executor, "children");
    let (mut proof, flat) = packed_refutation(&mut executor, &link);
    let packed = or_term(&mut executor, flat);
    proof.steps[3] = or_step(vec![link.eq_fab, link.not_ab], 2);
    repacked(&mut executor, &mut proof, packed);
}

#[test]
fn a_packed_leaf_with_a_second_consumer_is_repacked_in_place() {
    let mut executor = Executor::new();
    let link = congruence(&mut executor, "second");
    let flat = vec![link.not_ab, link.eq_fab];
    let packed = or_term(&mut executor, flat.clone());
    let mut proof = Proof::new();
    proof.add_step(ProofStep::Assume(link.eq_ab)); // t0
    proof.add_step(ProofStep::Assume(link.not_fab)); // t1
    proof.add_step(explanation_lemma(vec![packed])); // t2
    proof.add_step(or_step(flat, 2)); // t3
                                      // A SECOND reference to the leaf, still inside the refutation.
    proof.add_step(ProofStep::Step {
        rule: AletheRule::Contraction,
        clause: vec![packed],
        premises: vec![ProofId(2)],
        args: Vec::new(),
    }); // t4
    proof.add_step(ProofStep::Resolution {
        clause: vec![link.eq_fab],
        pivot: link.eq_ab,
        clause1: ProofId(3),
        clause2: ProofId(0),
    }); // t5
    proof.add_step(ProofStep::Resolution {
        clause: Vec::new(),
        pivot: link.eq_fab,
        clause1: ProofId(5),
        clause2: ProofId(1),
    }); // t6
    repacked(&mut executor, &mut proof, packed);
}

/// A VALID explanation the lowering has no rule for — `not` is a function, so
/// the clause is a theorem, but `eq_congruent` needs two APPLICATIONS.
#[test]
fn an_underivable_explanation_is_left_alone() {
    let mut executor = Executor::new();
    let p = executor.ctx.terms.mk_var("p", Sort::Bool);
    let q = executor.ctx.terms.mk_var("q", Sort::Bool);
    let not_p = executor.ctx.terms.mk_not_raw(p);
    let not_q = executor.ctx.terms.mk_not_raw(q);
    let eq_pq = executor
        .ctx
        .terms
        .mk_app(Symbol::named("="), vec![p, q], Sort::Bool);
    let not_pq = executor.ctx.terms.mk_not_raw(eq_pq);
    let eq_nots = executor
        .ctx
        .terms
        .mk_app(Symbol::named("="), vec![not_p, not_q], Sort::Bool);
    let not_eq_nots = executor.ctx.terms.mk_not_raw(eq_nots);
    assert!(
        ay_proof::recognize_euf_congruence_explanation(&executor.ctx.terms, &[not_pq, eq_nots]),
        "precondition: the checker CERTIFIES this clause"
    );
    let mut proof = Proof::new();
    proof.add_step(ProofStep::Assume(eq_pq)); // t0
    proof.add_step(ProofStep::Assume(not_eq_nots)); // t1
    proof.add_step(explanation_lemma(vec![not_pq, eq_nots])); // t2
    proof.add_step(ProofStep::Resolution {
        clause: vec![eq_nots],
        pivot: eq_pq,
        clause1: ProofId(2),
        clause2: ProofId(0),
    }); // t3
    proof.add_step(ProofStep::Resolution {
        clause: Vec::new(),
        pivot: eq_nots,
        clause1: ProofId(3),
        clause2: ProofId(1),
    }); // t4
    unchanged(&mut executor, &mut proof);
}

#[test]
fn a_lemma_whose_hypothesis_prints_unrenderably_is_left_alone() {
    let mut executor = Executor::new();
    let link = congruence(&mut executor, "surface");
    // A boolean wrapper re-spells the hypothesis as `(= (= a b) false)`, which
    // the printer renders happily and an external checker then rejects.
    let mut overrides = DetHashMap::default();
    overrides.insert(link.not_ab, "(= (= a b) false)".to_string());
    executor.last_proof_term_overrides = Some(overrides);
    let mut proof = flat_refutation(&link, explanation_lemma(vec![link.not_ab, link.eq_fab]));
    unchanged(&mut executor, &mut proof);
}

/// A step the PRINTER refuses would make the whole export refuse to publish,
/// turning a published `unsat` into no answer at all. Measured on
/// `smt/QF_AUFLIA/storeinv_nf_size2.smt2` before this guard existed:
/// `refusing to write unverifiable proof ... invalid surface congruence step
/// t10: surface eq_congruent arity no longer matches its equality hypotheses`.
#[test]
fn a_lemma_whose_congruence_step_the_printer_refuses_is_left_alone() {
    let mut executor = Executor::new();
    let link = congruence(&mut executor, "render");
    let sort = Sort::Uninterpreted("EufSort".to_string());
    let a = executor.ctx.terms.mk_var("render_a", sort.clone());
    let fa = executor.ctx.terms.mk_app(Symbol::named("f"), vec![a], sort);
    // A surface override that re-spells one congruence operand at a DIFFERENT
    // arity: the printer's `eq_congruent` bridge refuses the step outright.
    let mut overrides = DetHashMap::default();
    overrides.insert(fa, "(f render_a render_b)".to_string());
    executor.last_proof_term_overrides = Some(overrides);
    let mut proof = flat_refutation(&link, explanation_lemma(vec![link.not_ab, link.eq_fab]));
    unchanged(&mut executor, &mut proof);
}

/// The rewrite must not cost the MANDATORY gate a proof it certified before.
///
/// The `EufCongruenceExplanation` validator debits its ACTUAL work over the
/// reachable DAG (`quality.rs`'s `strict_semantic_charge` gives it a `(0, 0)`
/// precharge by name), while `contraction` — the one rule the derivation emits
/// that is still `class=General` — is billed the SQUARE of the TREE-unfolded
/// payload. On a shared `store` chain the two differ astronomically, so
/// replacing the lemma with the derivation can exhaust the envelope even though
/// every emitted step is individually valid.
///
/// This is not hypothetical, and `contraction` is the SECOND rule family to
/// show it. The first was `reordering` / `weakening` / `eq_reflexive`, measured
/// on `smt/QF_AUFLIA/storeinv_nf_size7.smt2`: `unsat` became
/// `unknown (self-check-rejected)`, with `--probe-strict-check` reporting
/// `budget: work 343617891+103266260 of 350000000` and 45 `reordering` steps
/// precharging 3_685_418_580 between them. Those three now route to
/// `ay_proof`'s `SemanticChargeClass::ClauseIdentityRoute` and are charged on
/// their DAG, so this test drives the same gate through `contraction` instead —
/// which the derivation emits whenever one hypothesis equality serves two
/// argument positions (`(= (g a b) (g b a))` under `a = b`).
#[test]
fn a_rewrite_that_would_cost_a_certification_is_reverted() {
    let mut executor = Executor::new();
    let element = Sort::Uninterpreted("Elem".to_string());
    let array = Sort::Array(Box::new(ArraySort {
        index_sort: Sort::Int,
        element_sort: element.clone(),
    }));
    let key = executor.ctx.terms.mk_var("deep_k", Sort::Int);
    let mut left = executor.ctx.terms.mk_var("deep_a", array.clone());
    let mut right = executor.ctx.terms.mk_var("deep_b", array.clone());
    // Each store's VALUE reads the chain below it, so the DAG stays tiny while
    // the TREE unfolding DOUBLES per level — the sharing that makes a
    // `class=General` precharge (the SQUARE of the unfolded payload)
    // astronomically larger than the work the validator actually does.
    for step in 0..14 {
        let index = executor
            .ctx
            .terms
            .mk_var(format!("deep_i{step}"), Sort::Int);
        let left_value =
            executor
                .ctx
                .terms
                .mk_app(Symbol::named("select"), vec![left, key], element.clone());
        let right_value =
            executor
                .ctx
                .terms
                .mk_app(Symbol::named("select"), vec![right, key], element.clone());
        left = executor.ctx.terms.mk_app(
            Symbol::named("store"),
            vec![left, index, left_value],
            array.clone(),
        );
        right = executor.ctx.terms.mk_app(
            Symbol::named("store"),
            vec![right, index, right_value],
            array.clone(),
        );
    }
    // `deep_g` takes BOTH chains, in both orders. `eq_congruent` consumes one
    // premise per differing argument position, so the tautology repeats the
    // SAME hypothesis twice and the derivation must emit `contraction`.
    let g_left =
        executor
            .ctx
            .terms
            .mk_app(Symbol::named("deep_g"), vec![left, right], element.clone());
    let g_right = executor
        .ctx
        .terms
        .mk_app(Symbol::named("deep_g"), vec![right, left], element);
    let chains = executor.ctx.terms.mk_eq(left, right);
    let not_chains = executor.ctx.terms.mk_not_raw(chains);
    let reads = executor.ctx.terms.mk_eq(g_left, g_right);
    let not_reads = executor.ctx.terms.mk_not_raw(reads);
    // Authorize the two leaves as authored premises, so the executor's own
    // certification gate — the one the revert consults — can accept them.
    executor.self_check_authored_assertions = Some(vec![chains, not_reads]);
    let mut proof = Proof::new();
    proof.add_step(ProofStep::Assume(chains)); // t0
    proof.add_step(ProofStep::Assume(not_reads)); // t1
    proof.add_step(explanation_lemma(vec![not_chains, reads])); // t2
    proof.add_step(ProofStep::Resolution {
        clause: vec![reads],
        pivot: chains,
        clause1: ProofId(2),
        clause2: ProofId(0),
    }); // t3
    proof.add_step(ProofStep::Resolution {
        clause: Vec::new(),
        pivot: reads,
        clause1: ProofId(3),
        clause2: ProofId(1),
    }); // t4

    assert!(
        executor.check_proof_strict_with_datatypes(&proof).is_ok(),
        "precondition: the certified lemma must make this proof CERTIFY, or the \
         test proves nothing about losing a certification"
    );
    unchanged(&mut executor, &mut proof);
    assert!(
        executor.check_proof_strict_with_datatypes(&proof).is_ok(),
        "the reverted proof must still certify"
    );
}

/// The same override on a derivation that emits NO `eq_congruent` step: a pure
/// transitivity chain. The printer has no surface check for `eq_transitive`
/// (it renders the re-spelled hypothesis happily and an external checker then
/// rejects it), so the shared unrenderability predicate — the one
/// `demote_unrenderable_eq_transitive_lemmas` uses — is the only thing that
/// can refuse this fragment.
#[test]
fn a_transitivity_only_derivation_with_an_unrenderable_hypothesis_is_left_alone() {
    let mut executor = Executor::new();
    let sort = Sort::Uninterpreted("EufSort".to_string());
    let a = executor.ctx.terms.mk_var("chain_a", sort.clone());
    let b = executor.ctx.terms.mk_var("chain_b", sort.clone());
    let c = executor.ctx.terms.mk_var("chain_c", sort);
    let eq_ab = executor.ctx.terms.mk_eq(a, b);
    let eq_bc = executor.ctx.terms.mk_eq(b, c);
    let eq_ac = executor.ctx.terms.mk_eq(a, c);
    let not_ab = executor.ctx.terms.mk_not_raw(eq_ab);
    let not_bc = executor.ctx.terms.mk_not_raw(eq_bc);
    let not_ac = executor.ctx.terms.mk_not_raw(eq_ac);
    let mut overrides = DetHashMap::default();
    overrides.insert(not_ab, "(= (= chain_a chain_b) false)".to_string());
    executor.last_proof_term_overrides = Some(overrides);
    let mut proof = Proof::new();
    proof.add_step(ProofStep::Assume(eq_ab)); // t0
    proof.add_step(ProofStep::Assume(eq_bc)); // t1
    proof.add_step(ProofStep::Assume(not_ac)); // t2
                                               // The conclusion FIRST, so the clause is not already in `eq_transitive`
                                               // order and the lowering has real work to do.
    proof.add_step(explanation_lemma(vec![eq_ac, not_ab, not_bc])); // t3
    proof.add_step(ProofStep::Resolution {
        clause: vec![eq_ac, not_bc],
        pivot: eq_ab,
        clause1: ProofId(3),
        clause2: ProofId(0),
    }); // t4
    proof.add_step(ProofStep::Resolution {
        clause: vec![eq_ac],
        pivot: eq_bc,
        clause1: ProofId(4),
        clause2: ProofId(1),
    }); // t5
    proof.add_step(ProofStep::Resolution {
        clause: Vec::new(),
        pivot: eq_ac,
        clause1: ProofId(5),
        clause2: ProofId(2),
    }); // t6
    unchanged(&mut executor, &mut proof);
}
