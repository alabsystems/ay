// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The finite-domain expansion lane derives its own instances
//! (#fde-forall-provenance), observed at the lane itself: right after
//! `process_quantifiers`, before any solve, proof reconstruction or authored
//! replacement cascade has run. A cascade member that later rebuilds the same
//! `forall_inst` cannot make these pass, so they pin the wiring the
//! carcara-checked twins in `group_proofs` only observe end to end.

use ay_core::{AletheRule, ProofStep};
use ay_frontend::parse;

use super::*;

const UNIVERSAL: &str =
    "(forall ((i (_ BitVec 8))) (=> (bvult i (_ bv9 8)) (= (select a i) (f x))))";

/// The pinned fixture with `roots` as its universal assertions.
fn script(prelude: &str, roots: &[&str]) -> String {
    let mut script = format!(
        "(set-logic ALL)\n{prelude}\
         (declare-fun f ((_ BitVec 8)) (_ BitVec 8))\n\
         (declare-const x (_ BitVec 8))\n\
         (declare-const k (_ BitVec 8))\n\
         (declare-const a (Array (_ BitVec 8) (_ BitVec 8)))\n\
         (assert (= k (_ bv4 8)))\n"
    );
    for root in roots {
        script.push_str(&format!("(assert {root})\n"));
    }
    script.push_str("(assert (distinct (select a k) (f x)))\n");
    script
}

/// Run the quantifier pass on `script` with a proof-tracking solve's posture
/// (the tracker armed, parsed assertions retained).
fn expanded(script: &str) -> Executor {
    let commands = parse(script).expect("fixture parses");
    let mut exec = Executor::new();
    exec.set_produce_proofs(true);
    assert_eq!(
        exec.execute_all(&commands)
            .expect("fixture declarations and assertions run"),
        [] as [String; 0]
    );
    exec.proof_tracker.enable();
    let _ = exec.process_quantifiers();
    assert!(
        !exec.quant_expansion_records.is_empty(),
        "the finite-domain lane must expand the guarded universal"
    );
    exec
}

/// For every recorded instance, whether the tracker resolves it to a derived
/// step (not an `Assume`), and every `forall_inst` argument vector recorded.
fn derived_instances(exec: &mut Executor) -> (Vec<bool>, Vec<Vec<TermId>>) {
    let terms: Vec<TermId> = exec
        .quant_expansion_records
        .iter()
        .flat_map(|record| record.instances.iter().map(|(_, instance)| *instance))
        .collect();
    let ids: Vec<_> = terms
        .iter()
        .map(|&term| {
            exec.proof_tracker
                .add_assumption(term, None)
                .expect("tracking is enabled")
        })
        .collect();
    let proof = exec.proof_tracker.take_proof();
    let derived = ids
        .iter()
        .map(|id| !matches!(proof.steps[id.0 as usize], ProofStep::Assume(_)))
        .collect();
    let arguments = proof
        .steps
        .iter()
        .filter_map(|step| match step {
            ProofStep::Step {
                rule: AletheRule::ForallInst,
                args,
                ..
            } => Some(args.clone()),
            _ => None,
        })
        .collect();
    (derived, arguments)
}

#[test]
fn the_lane_derives_every_instance_at_its_recorded_values() {
    let mut exec = expanded(&script("", &[UNIVERSAL]));
    let [record] = exec.quant_expansion_records.as_slice() else {
        panic!("expected one expansion record");
    };
    assert_eq!(record.instances.len(), 9, "cells #x00..#x08");
    let values: Vec<Vec<TermId>> = record.instances.iter().map(|(v, _)| v.clone()).collect();
    let (derived, arguments) = derived_instances(&mut exec);
    assert!(
        derived.iter().all(|&derived| derived),
        "every folded instance must resolve to its forall_inst derivation: {derived:?}"
    );
    for value in &values {
        assert!(
            arguments.contains(value),
            "no forall_inst at the recorded values {value:?}"
        );
    }
}

#[test]
fn the_lane_derives_nothing_for_a_surface_the_printer_cannot_restore() {
    for (label, script) in [
        (
            "define-fun bound",
            script(
                "(define-fun lim () (_ BitVec 8) #x09)\n",
                &["(forall ((i (_ BitVec 8))) (=> (bvult i lim) (= (select a i) (f x))))"],
            ),
        ),
        (
            "alpha-renamed respelling",
            script(
                "",
                &[
                    "(forall ((j (_ BitVec 8))) (=> (bvult j (_ bv9 8)) (= (select a j) (f x))))",
                    UNIVERSAL,
                ],
            ),
        ),
        (
            "Boolean wrapper",
            script("", &[&format!("(=> true {UNIVERSAL})")]),
        ),
    ] {
        let mut exec = expanded(&script);
        let values: Vec<Vec<TermId>> = exec
            .quant_expansion_records
            .iter()
            .flat_map(|record| record.instances.iter().map(|(v, _)| v.clone()))
            .collect();
        let (derived, arguments) = derived_instances(&mut exec);
        assert!(
            derived.iter().all(|&derived| !derived),
            "{label}: the lane must decline, leaving every instance underived: {derived:?}"
        );
        assert!(
            values.iter().all(|value| !arguments.contains(value)),
            "{label}: no forall_inst may be recorded at an expansion's values"
        );
    }
}

/// The solve-wide cap: universals over separate arrays, 255 instances each,
/// one more than [`MAX_DERIVED_SOLVE_INSTANCES`] admits. The ones that fit
/// are derived in assertion order; the one that would cross the cap stays
/// underived (unbounded, 32 such universals pushed a valid refutation that
/// used none of them past the printer's override table).
#[test]
fn the_lane_stops_deriving_at_the_solve_wide_cap() {
    const PER_UNIVERSAL: usize = 255;
    let fitting = MAX_DERIVED_SOLVE_INSTANCES / PER_UNIVERSAL;
    let mut script = String::from(
        "(set-logic ALL)\n\
         (declare-fun f ((_ BitVec 8)) (_ BitVec 8))\n\
         (declare-const x (_ BitVec 8))\n",
    );
    for array in 0..=fitting {
        script.push_str(&format!(
            "(declare-const a{array} (Array (_ BitVec 8) (_ BitVec 8)))\n\
             (assert (forall ((i (_ BitVec 8))) (=> (bvult i #xff) (= (select a{array} i) (f x)))))\n"
        ));
    }
    let mut exec = expanded(&script);
    let counts: Vec<usize> = exec
        .quant_expansion_records
        .iter()
        .map(|record| record.instances.len())
        .collect();
    assert_eq!(counts, vec![PER_UNIVERSAL; fitting + 1]);
    let (derived, _) = derived_instances(&mut exec);
    let (within, beyond) = derived.split_at(fitting * PER_UNIVERSAL);
    assert!(
        within.iter().all(|&derived| derived),
        "the universals within the cap must be derived"
    );
    assert!(
        beyond.iter().all(|&derived| !derived),
        "the universal crossing the cap must stay underived"
    );
}
