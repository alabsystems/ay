// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

fn proposed(input: &str) -> (Executor, Option<Proof>) {
    let mut exec = Executor::new();
    exec.execute_all(&parse(input).unwrap()).unwrap();
    let source = exec.ctx.assertions_parsed()[0].clone();
    let root = exec.raw_intern_surface(&source).unwrap();
    let candidate = exec.early_ground_closure_memory_candidate(root);
    assert_eq!(exec.last_proof_raw_original_assertions, [] as [TermId; 0]);
    assert!(exec.last_proof.is_none());
    (exec, candidate)
}

#[test]
fn a_geometry_fact_reaches_its_boolean_congruent_goal_through_checked_rules() {
    let (exec, candidate) = proposed(
        r#"
(set-logic QF_BV)
(declare-const x (_ BitVec 64))
(declare-const y (_ BitVec 64))
(assert (and (= x y) (bvule x (_ bv16 64))
             (not (= true (bvule y (_ bv16 64))))))
"#,
    );
    let proof = candidate.unwrap();
    assert!(exec
        .check_proof_strict_derivation_with_datatypes(&proof)
        .unwrap()
        .is_complete());
    let text = ay_proof::try_export_alethe(&proof, &exec.ctx.terms).unwrap();
    assert!(text.contains(":rule equiv_pos2"));
    assert!(!text.contains(":rule hole") && !text.contains(":rule trust"));
}

#[test]
fn nested_disjunction_membership_uses_the_proved_guard_equality() {
    let (exec, candidate) = proposed(
        r#"
(set-logic ALL)
(declare-const a Bool)
(declare-const b Bool)
(declare-const c Bool)
(assert (and (= a b) (not (= true (or (not a) (or false (or c b)))))))
"#,
    );
    let proof = candidate.unwrap();
    assert!(exec
        .check_proof_strict_derivation_with_datatypes(&proof)
        .unwrap()
        .is_complete());
    let text = ay_proof::try_export_alethe(&proof, &exec.ctx.terms).unwrap();
    assert!(text.contains(":rule or_neg"));
    assert!(!text.contains(":rule hole") && !text.contains(":rule trust"));
}

#[test]
fn a_missing_member_or_unrelated_geometry_remains_satisfiable() {
    for source in [
        r#"
(set-logic ALL)
(declare-const a Bool)
(declare-const b Bool)
(declare-const c Bool)
(assert (and (= a b) (not (= true (or (not a) (or false c))))))
"#,
        r#"
(set-logic QF_BV)
(declare-const x (_ BitVec 64))
(declare-const y (_ BitVec 64))
(assert (and (bvule x (_ bv16 64)) (not (= true (bvule y (_ bv16 64))))))
"#,
    ] {
        let (mut exec, candidate) = proposed(source);
        assert!(candidate.is_none());
        let outputs = exec.execute_all(&parse("(check-sat)").unwrap()).unwrap();
        assert_eq!(outputs, ["sat"]);
    }
}

#[test]
fn a_proved_equality_entails_a_guarded_or_in_either_position() {
    for goal in [
        "(= true (or guard (= x z)))",
        "(or (= x z) guard)",
        "(= (or guard (or other (= x z))) true)",
    ] {
        let source = format!(
            "(set-logic QF_BV)(declare-const x (_ BitVec 64))\
             (declare-const y (_ BitVec 64))(declare-const z (_ BitVec 64))\
             (declare-const guard Bool)(declare-const other Bool)\
             (assert (and (= x y) (= y z) (not {goal})))"
        );
        let (exec, candidate) = proposed(&source);
        let proof = candidate.expect("proved disjunct needs no guard assumption");
        assert!(exec
            .check_proof_strict_derivation_with_datatypes(&proof)
            .unwrap()
            .is_complete());
        let text = ay_proof::try_export_alethe(&proof, &exec.ctx.terms).unwrap();
        assert!(text.contains(":rule or_neg"));
        assert!(!text.contains(":rule hole") && !text.contains(":rule trust"));
    }
}

#[test]
fn an_unproved_disjunct_cannot_be_introduced_as_a_fact() {
    let (mut exec, candidate) = proposed(
        "(set-logic QF_BV)(declare-const x (_ BitVec 64))\
         (declare-const y (_ BitVec 64))(declare-const z (_ BitVec 64))\
         (declare-const guard Bool)\
         (assert (and (= x y) (not (= true (or guard (= x z))))))",
    );
    assert!(candidate.is_none());
    assert_eq!(
        exec.execute_all(&parse("(check-sat)").unwrap()).unwrap(),
        ["sat"]
    );
}

#[test]
fn modular_range_guards_cover_writes_through_actual_array_and_offset_aliases() {
    for width in [4, 8, 64, 128] {
        let source = format!(
            "(set-logic QF_ABV)\
             (declare-const original (Array (_ BitVec {width}) (_ BitVec 8)))\
             (declare-const first (Array (_ BitVec {width}) (_ BitVec 8)))\
             (declare-const last (Array (_ BitVec {width}) (_ BitVec 8)))\
             (declare-const base (_ BitVec {width}))\
             (declare-const shifted (_ BitVec {width}))\
             (declare-const observe (_ BitVec {width}))\
             (declare-const guard Bool)\
             (assert (and (= shifted (bvadd base (_ bv1 {width})))\
               (and (= first (store original base #x11))\
               (and (= last (store first shifted #x22))\
               (not (= (or (not guard)\
                 (or (bvult (bvsub observe base) (_ bv2 {width}))\
                     (= (select last observe) (select original observe)))) true))))))"
        );
        let (mut exec, candidate) = proposed(&source);
        let proof =
            candidate.expect("conditional range coverage is a theorem, without a guard premise");
        let checked = exec.check_proof_strict_derivation_with_datatypes(&proof);
        let root = proof
            .steps
            .iter()
            .find_map(|step| match step {
                ProofStep::Assume(root) => Some(*root),
                _ => None,
            })
            .expect("the proof retains its actual source root");
        assert!(proof
            .steps
            .iter()
            .all(|step| !matches!(step, ProofStep::Assume(term) if *term != root)));
        exec.set_alethe_dialect(ay_proof::AletheDialect::Clean);
        let overrides = exec.proof_export_term_overrides();
        let surfaces = exec.authored_export_surfaces();
        let text = exec
            .in_alethe_dialect(|| {
                ay_proof::try_export_alethe_with_authored_surfaces(
                    &proof,
                    &exec.ctx.terms,
                    &[root],
                    overrides.as_ref(),
                    surfaces.channels(),
                    None,
                )
            })
            .expect("the actual source-scoped range proof exports");
        let scope = ay_proof::ProblemScope::from_smtlib_source(&source);
        ay_proof::check_alethe_document_in_dialect(&text, &scope, exec.alethe_dialect())
            .expect("the checker-facing proof retains the exact original source scope");
        assert!(!text.contains("(declare-"));
        {
            let scratch = std::env::temp_dir().join(".ubd");
            std::fs::create_dir_all(&scratch).unwrap();
            let path = scratch.join(format!(
                "ay-range-compose-width{width}-{}.json",
                std::process::id()
            ));
            std::fs::write(
                &path,
                serde_json::to_vec(&serde_json::json!({
                    "type":"alethe_certificate", "version":"1.0", "problem":source, "proof":text,
                    "native_error":checked.as_ref().err().map(|error| format!("{error:?}")),
                    "native_steps":format!("{:?}",proof.steps)
                }))
                .unwrap(),
            )
            .unwrap();
            eprintln!(
                "range composition width{width} verdict={:?}; capture={}",
                checked.as_ref().map(|quality| quality.is_complete()),
                path.display()
            );
        }
        assert!(checked.unwrap().is_complete());
        if width > u64::BITS {
            assert_eq!(
                lemma_count(&proof, |kind, _| matches!(
                    kind,
                    TheoryLemmaKind::BvBitBlast
                )),
                0
            );
            assert!(proof.steps.iter().any(|step| matches!(
                step,
                ProofStep::Step {
                    rule: AletheRule::Evaluate,
                    ..
                }
            )));
        }
        assert!(!text.contains(":rule hole") && !text.contains(":rule trust"));
    }
}

#[test]
fn a_direct_store_needs_no_array_alias_premise_for_range_coverage() {
    let (exec, candidate) = proposed(
        "(set-logic QF_ABV)\
         (declare-const original (Array (_ BitVec 8) (_ BitVec 8)))\
         (declare-const base (_ BitVec 8))(declare-const observe (_ BitVec 8))\
         (assert (not (= true (or (bvult (bvsub observe base) #x01)\
          (= (select (store original base #x44) observe) (select original observe))))))",
    );
    let proof = candidate.unwrap();
    assert!(exec
        .check_proof_strict_derivation_with_datatypes(&proof)
        .unwrap()
        .is_complete());
    let text = ay_proof::try_export_alethe(&proof, &exec.ctx.terms).unwrap();
    assert!(!text.contains(":rule hole") && !text.contains(":rule trust"));
}

#[test]
fn a_store_at_the_range_boundary_or_on_an_unrelated_base_stays_satisfiable() {
    for index in ["(bvadd base #x02)", "other"] {
        let source = format!(
            "(set-logic QF_ABV)\
             (declare-const original (Array (_ BitVec 8) (_ BitVec 8)))\
             (declare-const last (Array (_ BitVec 8) (_ BitVec 8)))\
             (declare-const base (_ BitVec 8))(declare-const other (_ BitVec 8))\
             (declare-const observe (_ BitVec 8))\
             (assert (and (= last (store original {index} #x44))\
                (not (= true (or (bvult (bvsub observe base) #x02)\
                    (= (select last observe) (select original observe)))))))"
        );
        let (mut exec, candidate) = proposed(&source);
        assert!(candidate.is_none());
        assert_eq!(
            exec.execute_all(&parse("(check-sat)").unwrap()).unwrap(),
            ["sat"]
        );
    }
}

#[test]
fn a_held_read_disjunct_keeps_its_existing_cheap_proof() {
    let source = "(set-logic QF_ABV)\
        (declare-const original (Array (_ BitVec 8) (_ BitVec 8)))\
        (declare-const base (_ BitVec 8))(declare-const observe (_ BitVec 8))\
        (assert (and (= (select (store original base #x44) observe)\
                       (select original observe))\
          (= observe (bvadd base #x08))\
          (not (= true (or (bvult (bvsub observe base) #x01)\
             (= (select (store original base #x44) observe)\
                (select original observe)))))))";
    assert_cheap_read_disjunct(source);
}

#[test]
fn ordinary_read_reasoning_precedes_conditional_range_proposals() {
    assert_cheap_read_disjunct(
        "(set-logic QF_ABV)\
         (declare-const original (Array (_ BitVec 8) (_ BitVec 8)))\
         (declare-const base (_ BitVec 8))(declare-const observe (_ BitVec 8))\
         (assert (and (= observe (bvadd base #x08))\
           (not (= true (or (bvult (bvsub observe base) #x01)\
              (= (select (store original base #x44) observe)\
                 (select original observe)))))))",
    );
}

#[test]
fn a_later_held_fact_precedes_a_nested_conditional_range_proof() {
    assert_cheap_read_disjunct(
        "(set-logic QF_ABV)\
         (declare-const original (Array (_ BitVec 8) (_ BitVec 8)))\
         (declare-const base (_ BitVec 8))(declare-const observe (_ BitVec 8))\
         (declare-const p Bool)\
         (assert (and p\
           (not (= true (or (or (bvult (bvsub observe base) #x01)\
              (= (select (store original base #x44) observe)\
                 (select original observe))) p)))))",
    );
}

fn assert_cheap_read_disjunct(source: &str) {
    let mut exec = Executor::new();
    exec.set_alethe_dialect(ay_proof::AletheDialect::Clean);
    exec.execute_all(&parse(source).unwrap()).unwrap();
    let source = exec.ctx.assertions_parsed()[0].clone();
    let root = exec.raw_intern_surface(&source).unwrap();
    let proof = exec.early_ground_closure_memory_candidate(root).unwrap();
    assert!(exec
        .check_proof_strict_derivation_with_datatypes(&proof)
        .unwrap()
        .is_complete());
    assert_eq!(
        lemma_count(&proof, |kind, _| matches!(
            kind,
            TheoryLemmaKind::BvBitBlast
        )),
        0
    );
}

#[test]
fn denied_or_cancelled_range_emission_does_not_grow_the_term_arena() {
    use super::super::emit::ClosureEmitter;

    let mut exec = Executor::new();
    exec.execute_all(
        &parse(
            "(set-logic QF_ABV)\
         (declare-const original (Array (_ BitVec 8) (_ BitVec 8)))\
         (declare-const base (_ BitVec 8))(declare-const observe (_ BitVec 8))\
         (assert (not (= true (or (bvult (bvsub observe base) #x01)\
          (= (select (store original base #x44) observe) (select original observe))))))",
        )
        .unwrap(),
    )
    .unwrap();
    let source = exec.ctx.assertions_parsed()[0].clone();
    let root = exec.raw_intern_surface(&source).unwrap();
    let TermData::Not(equality) = exec.ctx.terms.get(root) else {
        panic!("negated source goal");
    };
    let goal = exec.true_equality_body(*equality).unwrap();
    let mut search = GroundSearch::default();
    exec.register_ground_subterms(&mut search.closure, root)
        .unwrap();
    let mut work = goal::MAX_GOAL_WORK;
    let plan = exec
        .ground_read_range_plan(&search.closure, goal, &mut work)
        .unwrap()
        .unwrap();
    let mut full = ClosureEmitter::new(&search);
    while full.admit_steps(1).is_some() {
        full.proof.add_assume(root, None);
    }
    let arena = exec.ctx.terms.len();
    let steps = full.proof.steps.len();
    assert!(exec.emit_ground_read_range(&mut full, plan).is_none());
    assert_eq!(exec.ctx.terms.len(), arena);
    assert_eq!(full.proof.steps.len(), steps);

    let mut work = goal::MAX_GOAL_WORK;
    let plan = exec
        .ground_read_range_plan(&search.closure, goal, &mut work)
        .unwrap()
        .unwrap();
    exec.set_interrupt(std::sync::Arc::new(std::sync::atomic::AtomicBool::new(
        true,
    )));
    let mut stopped = ClosureEmitter::new(&search);
    assert!(exec.emit_ground_read_range(&mut stopped, plan).is_none());
    assert_eq!(stopped.proof.steps, [] as [ProofStep; 0]);
    assert_eq!(exec.ctx.terms.len(), arena);
}
