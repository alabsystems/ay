// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Native implication must keep its exact source spelling and use the existing
//! Alethe implication tautologies, not an unchecked rewrite to disjunction.

use super::*;
use ay_core::{AletheRule, Proof, ProofStep, TheoryLemmaKind};
use std::cell::Cell;

fn implication(f: &mut Fixture, a: TermId, b: TermId) -> TermId {
    f.terms.mk_app(Symbol::named("=>"), [a, b], Sort::Bool)
}

fn checked_planned_rules(blaster: &Blaster<'_, '_>, bindings: &[(u32, TermId)]) {
    let mut terms = blaster.printer.terms.clone();
    let mut seen = Vec::new();
    for planned in &blaster.planned {
        let ClauseEmit::Rule { rule, .. } = &planned.emit else {
            continue;
        };
        let kind = match *rule {
            "implies_pos" => AletheRule::ImpliesPos,
            "implies_neg1" => AletheRule::ImpliesNeg1,
            "implies_neg2" => AletheRule::ImpliesNeg2,
            _ => continue,
        };
        seen.push(*rule);
        let clause = planned
            .lits
            .iter()
            .map(|reference| {
                let mut term = bindings
                    .iter()
                    .find(|(gate, _)| *gate == reference.gate)
                    .unwrap()
                    .1;
                for _ in 0..reference.nots {
                    term = terms.mk_not_raw(term);
                }
                term
            })
            .collect();
        let step = ProofStep::Step {
            rule: kind,
            clause,
            premises: vec![],
            args: vec![],
        };
        crate::checker::validate_step(&terms, &mut Vec::new(), ProofId(0), &step, true, None)
            .expect("the exact planned clause must pass the existing strict rule checker");
    }
    assert_eq!(seen, ["implies_pos", "implies_neg1", "implies_neg2"]);
}

#[test]
fn implication_plans_match_every_valuation_and_checked_rule_with_signed_operands() {
    for negate_a in [false, true] {
        for negate_b in [false, true] {
            let mut f = Fixture::new();
            let a = f.boolean("a");
            let b = f.boolean("b");
            let antecedent = if negate_a { f.not(a) } else { a };
            let consequent = if negate_b { f.not(b) } else { b };
            let formula = implication(&mut f, antecedent, consequent);
            let printer = AlethePrinter::new(&f.terms);
            let mut blaster = Blaster::new(&printer, ProofId(1), "@ay_imp_".into());
            let root = blaster.prepare(formula).expect("native typed implication");
            blaster.plan_structural_clauses().unwrap();
            let left = blaster.bool_of[&a];
            let right = blaster.bool_of[&b];
            assert_eq!(
                blaster.circuit.definition(root.gate),
                Some(printer.format_term(formula)),
            );
            checked_planned_rules(
                &blaster,
                &[(left.gate, a), (right.gate, b), (root.gate, formula)],
            );
            for av in [false, true] {
                for bv in [false, true] {
                    for proposed in [false, true] {
                        let mut values = vec![false; blaster.circuit.len()];
                        for gate in 0..blaster.circuit.len() as u32 {
                            if let circuit::GateKind::Const(value) = blaster.circuit.kind(gate) {
                                values[gate as usize] = *value;
                            }
                        }
                        values[left.gate as usize] = av;
                        values[right.gate as usize] = bv;
                        values[root.gate as usize] = proposed;
                        let accepted = blaster.planned.iter().all(|clause| {
                            clause
                                .lits
                                .iter()
                                .any(|lit| values[lit.gate as usize] != lit.negative())
                        });
                        assert_eq!(accepted, proposed == (!(av ^ negate_a) || (bv ^ negate_b)));
                    }
                }
            }
        }
    }
}

#[test]
fn implication_ground_gate_values_and_negations_are_exact() {
    for a in [false, true] {
        for b in [false, true] {
            let mut circuit = Circuit::new("@ay_imp_".into());
            let left = circuit.constant(a);
            let right = circuit.constant(b);
            let root = circuit.implies(left, right);
            assert_eq!(
                super::super::ground::constant_values(&circuit, &[root, root.not().unwrap()]),
                Some(vec![!a || b, a && !b]),
            );
        }
    }
}

/// The exact guard shape from rem_u32_digits' reported wire hole. Each case
/// needs one of the three implication clauses, including both negative rules.
fn contradiction(case: usize) -> (Fixture, TermId) {
    let mut f = Fixture::new();
    let a = f.boolean("rem_u32_digits::local_5_0");
    let b = f.boolean("rem_u32_digits::local_7_0");
    let antecedent = f.not(a);
    let imp = implication(&mut f, antecedent, b);
    let args = match case {
        0 => vec![imp, antecedent, f.not(b)],
        1 => vec![f.not(imp), a],
        2 => vec![f.not(imp), b],
        _ => unreachable!("three rule controls"),
    };
    let assertion = f.terms.mk_app(Symbol::named("and"), args, Sort::Bool);
    (f, assertion)
}

#[test]
fn implication_refutations_and_public_export_retain_the_original_native_guard() {
    for (case, rule) in ["implies_pos", "implies_neg1", "implies_neg2"]
        .into_iter()
        .enumerate()
    {
        let (mut f, assertion) = contradiction(case);
        // The native BvBitBlast rule requires genuine BV content. Keep this
        // reflexive equality raw: it is harmless, so the original implication
        // remains necessary to refute each of the three Boolean cases.
        let bits = f.bv("implication_control_bits", 4);
        let reflexive = f.terms.mk_app(Symbol::named("="), [bits, bits], Sort::Bool);
        assert!(f.refute(reflexive).is_none());
        let assertion = f
            .terms
            .mk_app(Symbol::named("and"), [assertion, reflexive], Sort::Bool);
        let document = f
            .refute(assertion)
            .expect("the implication contradiction is refutable");
        assert_complete(&document);
        assert!(document.contains(&format!(":rule {rule}")), "{document}");
        assert!(
            document.contains("(=> (not |rem_u32_digits::local_5_0|) |rem_u32_digits::local_7_0|)")
        );

        let lemma = f.not(assertion);
        let mut proof = Proof::new();
        let assume = proof.add_assume(assertion, None);
        let refutation =
            proof.add_theory_lemma_with_kind("bv", vec![lemma], TheoryLemmaKind::BvBitBlast);
        proof.add_resolution(Vec::new(), assertion, assume, refutation);
        crate::check_proof_strict_with_context(&proof, &f.terms, None, None, Some(&[assertion]))
            .expect("native original-clause proof remains strictly checked");
        let exported = crate::try_export_alethe_with_authored_surfaces(
            &proof,
            &f.terms,
            &[assertion],
            None,
            crate::AletheAuthoredSurfaces::default(),
            Some(16 * 1024 * 1024),
        )
        .expect("public wire export");
        assert_complete(&exported);
        assert!(exported.contains("(step t2 (cl) :rule resolution"));
    }
}

#[test]
fn false_implication_lemmas_and_malformed_dead_children_still_decline() {
    let mut f = Fixture::new();
    let a = f.boolean("a");
    let b = f.boolean("b");
    let bits = f.bv("bits", 8);
    let imp = implication(&mut f, a, b);
    assert!(
        f.refute(imp).is_none(),
        "implication has satisfying assignments"
    );
    let negated = f.not(imp);
    assert!(
        f.refute(negated).is_none(),
        "implication also has a falsifying assignment"
    );
    let no = f.terms.mk_bool(false);
    for args in [
        vec![],
        vec![a],
        vec![a, b, a],
        vec![a, bits],
        vec![bits, b],
        vec![bits, bits],
    ] {
        let malformed = f.terms.mk_app(Symbol::named("=>"), args, Sort::Bool);
        let dead = f
            .terms
            .mk_app(Symbol::named("and"), [no, malformed], Sort::Bool);
        assert!(
            f.refute(dead).is_none(),
            "a false sibling must not hide an invalid implication"
        );
    }
}

#[test]
fn implication_sweep_uses_the_same_signed_gate_semantics_and_original_cnf() {
    let (f, assertion) = contradiction(0);
    let printer = AlethePrinter::new(&f.terms);
    let mut blaster = Blaster::new(&printer, ProofId(1), "@ay_imp_".into());
    let root = blaster.prepare(assertion).unwrap();
    let (cnf, root_id) = blaster.planned_cnf(root).unwrap();
    let proof = super::super::sweep::refute_directly(
        &printer,
        &blaster.circuit,
        &blaster.guarded_ites,
        &cnf,
        root_id,
    )
    .expect("the sweep's simulation of implication agrees with its defining CNF");
    proof
        .validate()
        .expect("independent resolution-DAG validation");
}

#[test]
fn implication_rendering_keeps_exact_short_and_zero_work_boundaries() {
    let (mut f, assertion) = contradiction(0);
    let lemma = f.not(assertion);
    let render = |budget| {
        let printer = AlethePrinter::new_with_overrides_and_budget(&f.terms, None, budget);
        let result = printer.format_bv_complete_blast_refutation(ProofId(1), &[lemma]);
        (result, printer.work_used())
    };
    assert!(render(None).0.is_some()); // Warm only optional reuse, never a work grant.
    let (expected, work) = render(None);
    assert!(expected.is_some() && work > 1);
    assert_eq!(render(Some(work)).0, expected);
    for budget in [0, 1, work - 1] {
        assert!(render(Some(budget)).0.is_none(), "budget {budget}/{work}");
    }
}

#[test]
fn implication_refusal_at_original_emission_polls_is_terminal() {
    let (mut f, assertion) = contradiction(0);
    let lemma = f.not(assertion);
    assert!(f.refute(assertion).is_some());
    let polls = Cell::new(0usize);
    let mut progress = || {
        polls.set(polls.get() + 1);
        true
    };
    let printer = AlethePrinter::new(&f.terms).with_emission_progress(&mut progress);
    assert!(printer
        .format_bv_complete_blast_refutation(ProofId(1), &[lemma])
        .is_some());
    let total = polls.get();
    assert!(total > 2);
    drop(printer);
    for stop in [1, total / 2, total] {
        let calls = Cell::new(0usize);
        let mut progress = || {
            calls.set(calls.get() + 1);
            calls.get() != stop
        };
        let printer = AlethePrinter::new(&f.terms).with_emission_progress(&mut progress);
        assert!(printer
            .format_bv_complete_blast_refutation(ProofId(1), &[lemma])
            .is_none());
        assert_eq!(calls.get(), stop);
        assert!(printer
            .format_bv_complete_blast_refutation(ProofId(1), &[lemma])
            .is_none());
        assert_eq!(
            calls.get(),
            stop,
            "a one-shot refusal cannot revive the same owner"
        );
    }
}
