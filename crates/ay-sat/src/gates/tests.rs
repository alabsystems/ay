// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;
use crate::kitten::Kitten;
use crate::test_util::lit;

#[test]
fn test_find_gate_for_congruence_detects_ite_gate() {
    // y ↔ ITE(c, t, e):
    // (y ∨ c ∨ ¬e), (y ∨ ¬c ∨ ¬t), (¬y ∨ c ∨ e), (¬y ∨ ¬c ∨ t)
    let mut clauses = ClauseArena::new();
    let c0 = clauses.add(&[lit(0, true), lit(1, true), lit(3, false)], false);
    let c1 = clauses.add(&[lit(0, true), lit(1, false), lit(2, false)], false);
    let c2 = clauses.add(&[lit(0, false), lit(1, true), lit(3, true)], false);
    let c3 = clauses.add(&[lit(0, false), lit(1, false), lit(2, true)], false);

    let pos_occs = vec![c0, c1];
    let neg_occs = vec![c2, c3];
    let mut extractor = GateExtractor::new(4);
    let mut marks = LitMarks::new(4);

    let gate = extractor
        .find_gate_for_congruence_with_marks(
            Variable(0),
            &clauses,
            &pos_occs,
            &neg_occs,
            true,
            &[],
            &mut marks,
        )
        .expect("congruence extraction should find ITE gate");

    assert_eq!(gate.gate_type, GateType::Ite);
    assert_eq!(gate.output, Variable(0));
    assert_eq!(gate.inputs, vec![lit(1, true), lit(2, true), lit(3, true)]);
    assert_eq!(gate.defining_clauses.len(), 4);
    for expected in [c0, c1, c2, c3] {
        assert!(gate.defining_clauses.contains(&expected));
    }
    assert_eq!(extractor.stats().ite_gates, 1);
}

#[test]
fn test_find_gate_for_bve_with_vals_recovers_effective_and_gate() {
    // y ↔ (a ∧ b) with extra literals that are currently falsified.
    // Without `vals`, this is not syntactically an AND gate:
    //   (~y ∨ a ∨ j1), (~y ∨ b), (y ∨ ~a ∨ ~b ∨ j2)
    // With j1/j2 falsified AND a side clause for ~j2, it becomes effectively:
    //   (~y ∨ a), (~y ∨ b), (~y ∨ ~j2), (y ∨ ~a ∨ ~b)
    //
    // Note (#8477): root-false literals in the base clause are only skipped
    // when a corresponding side clause exists. Without `(~y ∨ ~j2)`, the
    // root-false j2 in the base clause would be left in place, causing the
    // mark check to fail and gate detection to correctly refuse the
    // incomplete gate.
    let mut clauses = ClauseArena::new();
    let c0 = clauses.add(&[lit(0, false), lit(1, true), lit(3, true)], false);
    let c1 = clauses.add(&[lit(0, false), lit(2, true)], false);
    // Side clause for the root-false literal j2 (var 4): (~y ∨ ~j2)
    let c_j2_side = clauses.add(&[lit(0, false), lit(4, false)], false);
    let c2 = clauses.add(
        &[lit(0, true), lit(1, false), lit(2, false), lit(4, true)],
        false,
    );

    let pos_occs = vec![c2];
    let neg_occs = vec![c0, c1, c_j2_side];

    let mut extractor = GateExtractor::new(5);
    assert!(
        extractor
            .find_gate_for_bve_with_vals(Variable(0), &clauses, &pos_occs, &neg_occs, &[])
            .is_none(),
        "syntactic detection should fail before effective-binary filtering",
    );

    let mut vals = vec![0i8; 10];
    vals[lit(3, true).index()] = -1; // j1 falsified
    vals[lit(4, true).index()] = -1; // j2 falsified

    let gate = extractor
        .find_gate_for_bve_with_vals(Variable(0), &clauses, &pos_occs, &neg_occs, &vals)
        .expect("effective-binary detection should recover AND gate");
    assert_eq!(gate.gate_type, GateType::And);
    assert_eq!(gate.output, Variable(0));
    // Defining clauses: base clause + side clauses for a, b (not ~j2 since
    // j2 is root-false and skipped in the base clause, so ~j2's side clause
    // mark is not promoted).
    assert_eq!(gate.defining_clauses.len(), 3);
    assert!(gate.defining_clauses.contains(&c0));
    assert!(gate.defining_clauses.contains(&c1));
    assert!(gate.defining_clauses.contains(&c2));
}

#[test]
fn test_find_gate_for_bve_with_vals_rejects_incomplete_gate_without_side_clause() {
    // Same shape as the effective AND gate test above, but WITHOUT the side
    // clause for the root-false base literal j2. Without a corresponding
    // side clause (~y ∨ ~j2), skipping j2 in the base clause would produce
    // an incomplete gate that misses a constraint needed for
    // equisatisfiability during BVE. (#8477)
    //
    // This is the CaDiCaL-divergent path: CaDiCaL's elim_propagate keeps
    // vals and occ lists synchronized so this case cannot arise. AY removed
    // elim_propagate (#8356), so we must guard against it explicitly.
    let mut clauses = ClauseArena::new();
    let c0 = clauses.add(&[lit(0, false), lit(1, true), lit(3, true)], false);
    let c1 = clauses.add(&[lit(0, false), lit(2, true)], false);
    // No side clause for j2 -- that's the point of this test
    let c2 = clauses.add(
        &[lit(0, true), lit(1, false), lit(2, false), lit(4, true)],
        false,
    );

    let pos_occs = vec![c2];
    let neg_occs = vec![c0, c1];

    let mut extractor = GateExtractor::new(5);
    let mut vals = vec![0i8; 10];
    vals[lit(3, true).index()] = -1; // j1 falsified
    vals[lit(4, true).index()] = -1; // j2 falsified

    let gate =
        extractor.find_gate_for_bve_with_vals(Variable(0), &clauses, &pos_occs, &neg_occs, &vals);
    assert!(
        gate.is_none(),
        "gate detection must reject base clause with root-false literal lacking a side clause (#8477)",
    );
}

#[test]
fn test_find_gate_for_bve_with_vals_ignores_satisfied_side_clause() {
    // Same shape as AND gate, but one side clause has a satisfied literal.
    // That clause must not count as an effective binary side-clause.
    let mut clauses = ClauseArena::new();
    let c0 = clauses.add(&[lit(0, false), lit(1, true), lit(3, true)], false);
    let c1 = clauses.add(&[lit(0, false), lit(2, true)], false);
    let c2 = clauses.add(&[lit(0, true), lit(1, false), lit(2, false)], false);

    let pos_occs = vec![c2];
    let neg_occs = vec![c0, c1];

    let mut vals = vec![0i8; 8];
    vals[lit(3, true).index()] = 1; // satisfied literal in side clause

    let mut extractor = GateExtractor::new(4);
    let gate =
        extractor.find_gate_for_bve_with_vals(Variable(0), &clauses, &pos_occs, &neg_occs, &vals);
    assert!(
        gate.is_none(),
        "satisfied side-clauses must not be used for effective-binary gates",
    );
}

#[test]
fn test_find_gate_for_bve_excludes_stray_binary_side_clauses() {
    // y ↔ (a ∧ b) plus an unrelated side-clause (~y ∨ c).
    //
    // CaDiCaL's mark-promotion step is required here:
    // only literals seen in the long clause (a,b) should survive filtering.
    let mut clauses = ClauseArena::new();
    let c0 = clauses.add(&[lit(0, false), lit(1, true)], false); // (~y ∨ a)
    let c1 = clauses.add(&[lit(0, false), lit(2, true)], false); // (~y ∨ b)
    let c2 = clauses.add(&[lit(0, false), lit(3, true)], false); // (~y ∨ c) stray
    let c3 = clauses.add(&[lit(0, true), lit(1, false), lit(2, false)], false); // (y ∨ ~a ∨ ~b)

    let pos_occs = vec![c3];
    let neg_occs = vec![c0, c1, c2];

    let mut extractor = GateExtractor::new(4);
    let gate = extractor
        .find_gate_for_bve_with_vals(Variable(0), &clauses, &pos_occs, &neg_occs, &[])
        .expect("AND gate should still be detected");

    assert_eq!(gate.gate_type, GateType::And);
    assert_eq!(gate.output, Variable(0));
    assert_eq!(
        gate.defining_clauses.len(),
        3,
        "defining clauses must include only long clause + matching side clauses",
    );
    assert!(gate.defining_clauses.contains(&c3));
    assert!(gate.defining_clauses.contains(&c0));
    assert!(gate.defining_clauses.contains(&c1));
    assert!(
        !gate.defining_clauses.contains(&c2),
        "stray side-clause must be excluded by mark promotion filtering",
    );
}

#[test]
fn test_xor_gate_arity2() {
    // Binary XOR: y = x1 ⊕ x2
    // Even-parity clauses over (y=0, x1=1, x2=2):
    //   (y,  x1,  x2)  — signs 000
    //   (y, ~x1, ~x2)  — signs 011
    //   (~y, x1, ~x2)  — signs 101
    //   (~y, ~x1, x2)  — signs 110
    let mut clauses = ClauseArena::new();
    let c0 = clauses.add(&[lit(0, true), lit(1, true), lit(2, true)], false);
    let c1 = clauses.add(&[lit(0, true), lit(1, false), lit(2, false)], false);
    let c2 = clauses.add(&[lit(0, false), lit(1, true), lit(2, false)], false);
    let c3 = clauses.add(&[lit(0, false), lit(1, false), lit(2, true)], false);

    let pos_occs = vec![c0, c1];
    let neg_occs = vec![c2, c3];
    let mut extractor = GateExtractor::new(3);
    let gate = extractor
        .find_gate_for_bve_with_vals(Variable(0), &clauses, &pos_occs, &neg_occs, &[])
        .expect("should detect arity-2 XOR gate");
    assert_eq!(gate.gate_type, GateType::Xor);
    assert_eq!(gate.output, Variable(0));
    assert_eq!(gate.defining_clauses.len(), 4);
}

#[test]
fn test_xor_gate_arity3() {
    // Ternary XOR: y = x1 ⊕ x2 ⊕ x3
    // Even-parity clauses over (y=0, x1=1, x2=2, x3=3):
    // 8 clauses, all sign patterns with even popcount.
    let mut clauses = ClauseArena::new();
    // signs 0000: ( y,  x1,  x2,  x3)
    let c0 = clauses.add(
        &[lit(0, true), lit(1, true), lit(2, true), lit(3, true)],
        false,
    );
    // signs 0011: ( y,  x1, ~x2, ~x3)
    let c1 = clauses.add(
        &[lit(0, true), lit(1, true), lit(2, false), lit(3, false)],
        false,
    );
    // signs 0101: ( y, ~x1,  x2, ~x3)
    let c2 = clauses.add(
        &[lit(0, true), lit(1, false), lit(2, true), lit(3, false)],
        false,
    );
    // signs 0110: ( y, ~x1, ~x2,  x3)
    let c3 = clauses.add(
        &[lit(0, true), lit(1, false), lit(2, false), lit(3, true)],
        false,
    );
    // signs 1001: (~y,  x1,  x2, ~x3)
    let c4 = clauses.add(
        &[lit(0, false), lit(1, true), lit(2, true), lit(3, false)],
        false,
    );
    // signs 1010: (~y,  x1, ~x2,  x3)
    let c5 = clauses.add(
        &[lit(0, false), lit(1, true), lit(2, false), lit(3, true)],
        false,
    );
    // signs 1100: (~y, ~x1,  x2,  x3)
    let c6 = clauses.add(
        &[lit(0, false), lit(1, false), lit(2, true), lit(3, true)],
        false,
    );
    // signs 1111: (~y, ~x1, ~x2, ~x3)
    let c7 = clauses.add(
        &[lit(0, false), lit(1, false), lit(2, false), lit(3, false)],
        false,
    );

    let pos_occs = vec![c0, c1, c2, c3];
    let neg_occs = vec![c4, c5, c6, c7];
    let mut extractor = GateExtractor::new(4);
    let gate = extractor
        .find_gate_for_bve_with_vals(Variable(0), &clauses, &pos_occs, &neg_occs, &[])
        .expect("should detect arity-3 XOR gate");
    assert_eq!(gate.gate_type, GateType::Xor);
    assert_eq!(gate.output, Variable(0));
    assert_eq!(gate.inputs.len(), 3);
    assert_eq!(gate.defining_clauses.len(), 8);
}

#[test]
fn test_xor_gate_incomplete_clauses_fails() {
    // Missing one clause from arity-2 XOR — should not detect gate.
    let mut clauses = ClauseArena::new();
    clauses.add(&[lit(0, true), lit(1, true), lit(2, true)], false);
    clauses.add(&[lit(0, true), lit(1, false), lit(2, false)], false);
    clauses.add(&[lit(0, false), lit(1, true), lit(2, false)], false);
    // Missing: (~y, ~x1, x2) — signs 110

    let pos_occs = vec![0, 1];
    let neg_occs = vec![2];
    let mut extractor = GateExtractor::new(3);
    let gate =
        extractor.find_gate_for_bve_with_vals(Variable(0), &clauses, &pos_occs, &neg_occs, &[]);
    assert!(gate.is_none(), "incomplete XOR should not be detected");
}

#[test]
fn test_find_extraction_for_bve_with_marks_returns_failed_literal_for_one_sided_core() {
    let mut clauses = ClauseArena::new();
    let c0 = clauses.add(&[lit(0, true), lit(1, true)], false);
    let c1 = clauses.add(&[lit(0, true), lit(1, false)], false);
    let c2 = clauses.add(&[lit(0, false), lit(2, true)], false);

    let pos_occs = vec![c0, c1];
    let neg_occs = vec![c2];

    let mut extractor = GateExtractor::new(3);
    let mut kitten = Kitten::new();
    kitten.enable_antecedent_tracking();
    let mut marks = LitMarks::new(3);

    let extraction = extractor
        .find_extraction_for_bve_with_marks(
            &mut kitten,
            Variable(0),
            &clauses,
            &pos_occs,
            &neg_occs,
            &[],
            &mut marks,
        )
        .expect("semantic extraction should detect a one-sided failed literal");

    assert_eq!(
        extraction,
        BveExtraction::FailedLiteral { unit: lit(0, true) }
    );
}

#[test]
fn test_find_extraction_for_bve_with_marks_structural_gate_skips_gate_pairs() {
    let mut clauses = ClauseArena::new();
    let c0 = clauses.add(&[lit(0, true), lit(1, false)], false);
    let c1 = clauses.add(&[lit(0, false), lit(1, true)], false);

    let pos_occs = vec![c0];
    let neg_occs = vec![c1];

    let mut extractor = GateExtractor::new(2);
    let mut kitten = Kitten::new();
    kitten.enable_antecedent_tracking();
    let mut marks = LitMarks::new(2);

    let extraction = extractor
        .find_extraction_for_bve_with_marks(
            &mut kitten,
            Variable(0),
            &clauses,
            &pos_occs,
            &neg_occs,
            &[],
            &mut marks,
        )
        .expect("structural gate should be extracted for BVE");

    assert_eq!(
        extraction,
        BveExtraction::RestrictResolution {
            defining_clauses: vec![c0, c1],
            resolve_gate_pairs: false,
        }
    );
}

#[test]
fn test_find_extraction_for_bve_with_marks_returns_definition_core() {
    let mut clauses = ClauseArena::new();
    let c0 = clauses.add(&[lit(0, true), lit(1, true), lit(2, true)], false);
    let c1 = clauses.add(&[lit(0, true), lit(1, true), lit(2, false)], false);
    let c2 = clauses.add(&[lit(0, false), lit(1, false)], false);

    let pos_occs = vec![c0, c1];
    let neg_occs = vec![c2];

    let mut extractor = GateExtractor::new(3);
    let mut kitten = Kitten::new();
    kitten.enable_antecedent_tracking();
    let mut marks = LitMarks::new(3);

    let extraction = extractor.find_extraction_for_bve_with_marks(
        &mut kitten,
        Variable(0),
        &clauses,
        &pos_occs,
        &neg_occs,
        &[],
        &mut marks,
    );

    match extraction {
        Some(BveExtraction::RestrictResolution {
            defining_clauses,
            resolve_gate_pairs,
        }) => {
            assert!(
                resolve_gate_pairs,
                "kitten both-sided definition must enable gate×gate resolution"
            );
            assert!(
                defining_clauses.iter().any(|&idx| idx == c0 || idx == c1),
                "core should include at least one positive-side defining clause"
            );
            assert!(
                defining_clauses.contains(&c2),
                "core should include the negative-side defining clause"
            );
        }
        _ => panic!(
            "kitten both-sided definition should use restricted resolution with gate pairs, got {extraction:?}"
        ),
    }
}
