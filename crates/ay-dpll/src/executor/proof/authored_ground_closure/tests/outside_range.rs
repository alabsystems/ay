// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

fn source(width: u32, length: u128, offset: u128, alias: bool, inside: bool) -> String {
    let start = if alias { "other" } else { "base" };
    let window = format!("(bvult (bvsub point base) (_ bv{length} {width}))");
    let condition = if inside {
        format!("(not {window})")
    } else {
        window
    };
    let equality = format!("(= (select (store memory (bvadd {start} (_ bv{offset} {width})) #x35) point) (select memory point))");
    let goal = format!("(not (= (or {condition} {equality}) true))");
    let root = if alias {
        format!("(and (= other base) {goal})")
    } else {
        goal
    };
    format!("(set-option :produce-proofs true)\n(set-logic QF_ABV)\n(declare-const memory (Array (_ BitVec {width}) (_ BitVec 8)))\n(declare-const point (_ BitVec {width}))\n(declare-const base (_ BitVec {width}))\n(declare-const other (_ BitVec {width}))\n(assert {root})\n(check-sat)\n")
}

fn prepared(input: &str) -> (Executor, TermId) {
    let mut exec = Executor::new();
    for command in parse(input).unwrap() {
        if !matches!(command, Command::CheckSat | Command::Exit) {
            exec.execute_authored(&command).unwrap();
        }
    }
    let surface = exec.ctx.assertions_parsed()[0].clone();
    let root = exec.raw_intern_ground_bv_surface(&surface).unwrap();
    exec.set_alethe_dialect(ay_proof::AletheDialect::Clean);
    (exec, root)
}

#[test]
fn modular_range_misses_are_checked_at_small_and_actual_widths() {
    for (width, length, offset, alias) in [
        (1, 1, 0, false),
        (2, 3, 2, false),
        (4, 4, 3, false),
        (8, 16, 15, true),
        (64, 16, 7, false),
    ] {
        let input = source(width, length, offset, alias, false);
        checked_control(
            &input,
            &format!("width{width}-length{length}-offset{offset}-alias{alias}"),
        );
    }
}

#[test]
fn source_range_miss_transports_both_original_index_and_point() {
    let input = r#"
        (set-option :produce-proofs true)
        (set-logic QF_ABV)
        (declare-const memory (Array (_ BitVec 8) (_ BitVec 8)))
        (declare-const base (_ BitVec 8))
        (declare-const point (_ BitVec 8))
        (declare-const key (_ BitVec 8))
        (declare-const index (_ BitVec 8))
        (assert (and
            (= key point)
            (= index (bvadd base #x03))
            (not (bvult (bvsub point base) #x10))
            (not (= (select (store memory index #x35) key)
                    (select memory key)))))
        (check-sat)
    "#;
    checked_control(input, "range-both-source-images");
    for equality in ["(= key point)", "(= index (bvadd base #x03))"] {
        let missing = input.replacen(equality, "true", 1);
        let (mut exec, root) = prepared(&missing);
        assert!(
            exec.early_ground_closure_memory_candidate(root).is_none(),
            "a missing source path cannot authorize the range miss: {equality}"
        );
    }
}

fn checked_control(input: &str, name: &str) {
    let (mut exec, root) = prepared(input);
    let candidate = exec
        .early_ground_closure_memory_candidate(root)
        .expect("source range proof");
    assert!(exec
        .check_proof_strict_derivation_with_datatypes(&candidate)
        .unwrap()
        .is_complete());
    assert!(candidate
        .steps
        .iter()
        .all(|step| !matches!(step, ProofStep::Assume(term) if *term != root)));
    let overrides = exec.proof_export_term_overrides();
    let surfaces = exec.authored_export_surfaces();
    let text = exec
        .in_alethe_dialect(|| {
            ay_proof::try_export_alethe_with_authored_surfaces(
                &candidate,
                &exec.ctx.terms,
                &[root],
                overrides.as_ref(),
                surfaces.channels(),
                None,
            )
        })
        .unwrap();
    let directory =
        std::env::temp_dir().join(format!("ay-outside-range-controls-{}", std::process::id()));
    std::fs::create_dir_all(&directory).unwrap();
    std::fs::write(directory.join(format!("{name}.smt2")), &input).unwrap();
    std::fs::write(directory.join(format!("{name}.alethe")), &text).unwrap();
    println!(
        "OUTSIDE_RANGE_CONTROL {name} steps={} bytes={} capture={}",
        candidate.steps.len(),
        text.len(),
        directory.display()
    );
    assert!(!text.contains(":rule hole") && !text.contains(":rule trust"));
}

#[test]
fn uncovered_or_unknown_range_relations_stay_satisfiable() {
    let mut inputs = Vec::new();
    for (length, offset, inside) in [(3, 3, false), (0, 0, false), (4, 0, true)] {
        inputs.push((
            format!("length{length}-offset{offset}-inside{inside}"),
            source(4, length, offset, false, inside),
        ));
    }
    inputs.push((
        "unknown-base-alias".to_string(),
        source(4, 3, 0, true, false).replace("(= other base)", "true"),
    ));
    inputs.push((
        "unknown-window".to_string(),
        source(4, 3, 0, false, false)
            .replace("(assert ", "(declare-const window (_ BitVec 4))\n(assert ")
            .replace("(_ bv3 4)", "window"),
    ));
    for (label, input) in inputs {
        let (mut exec, root) = prepared(&input);
        assert!(
            exec.early_ground_closure_memory_candidate(root).is_none(),
            "{label}"
        );
        let directory =
            std::env::temp_dir().join(format!("ay-outside-range-controls-{}", std::process::id()));
        std::fs::create_dir_all(&directory).unwrap();
        std::fs::write(directory.join(format!("sat-{label}.smt2")), &input).unwrap();
        let mut public = Executor::new();
        assert_eq!(
            public.execute_all(&parse(&input).unwrap()).unwrap(),
            ["sat"],
            "{label}"
        );
    }
}

#[test]
fn forced_negative_boolean_projection_never_splits_a_false_conjunction() {
    let input = "(set-logic QF_UF)(declare-const p Bool)(declare-const q Bool)(declare-const a Bool)(declare-const b Bool)(assert (and (not (= (or p q) true)) (not (and a b))))";
    let (mut exec, root) = prepared(input);
    let mut search = GroundSearch::default();
    exec.seed_ground_root_facts(&mut search, &[root]).unwrap();
    let mut work = SharedGroundWork::new(work::MAX_SHARED_WORK);
    exec.expand_ground_negative_boolean_facts(&mut search, &mut work)
        .unwrap();
    let find = |name: &str| {
        search
            .facts
            .facts()
            .iter()
            .any(|fact| match exec.ctx.terms.get(fact.literal) {
                TermData::Not(atom) => {
                    matches!(exec.ctx.terms.get(*atom), TermData::Var(actual, _) if actual == name)
                }
                _ => false,
            })
    };
    assert!(find("p") && find("q"));
    assert!(!find("a") && !find("b"));
    let remaining = work.remaining();
    let terms = exec.ctx.terms.len();
    exec.expand_ground_negative_boolean_facts(&mut search, &mut work)
        .unwrap();
    assert_eq!(work.remaining(), remaining);
    assert_eq!(exec.ctx.terms.len(), terms);
}

#[test]
fn negative_projection_work_refusal_adds_no_term_or_fact() {
    let input = "(set-logic QF_UF)(declare-const p Bool)(declare-const q Bool)(assert (not (= (or p q) true)))";
    let (mut exec, root) = prepared(input);
    let mut search = GroundSearch::default();
    exec.seed_ground_root_facts(&mut search, &[root]).unwrap();
    let terms = exec.ctx.terms.len();
    let facts = search.facts.facts().len();
    let mut work = SharedGroundWork::new(0);
    assert!(exec
        .expand_ground_negative_boolean_facts(&mut search, &mut work)
        .is_none());
    assert!(work.refused());
    assert_eq!(exec.ctx.terms.len(), terms);
    assert_eq!(search.facts.facts().len(), facts);
}

#[test]
fn a_wrong_proposed_range_offset_is_not_proof_authority() {
    let input = source(4, 3, 0, false, false);
    let (mut exec, root) = prepared(&input);
    let mut search = GroundSearch::default();
    exec.register_ground_subterms(&mut search.closure, root)
        .unwrap();
    let conflict = exec
        .saturate_ground_search(&mut search, &[root], &[])
        .unwrap();
    let guard = search
        .read_chains
        .witnesses
        .iter_mut()
        .flat_map(|w| w.skipped.iter_mut())
        .find_map(|skip| skip.range.as_mut())
        .unwrap();
    guard.offset = 1; // still within the window, but not this actual store index
    let forged = exec
        .emit_ground_closure_refutation(&search, conflict)
        .unwrap();
    assert!(exec
        .check_proof_strict_derivation_with_datatypes(&forged)
        .is_err());
}

#[test]
fn reversed_true_equality_and_wrapping_constant_start_are_checked() {
    let reversed = source(4, 3, 1, false, false)
        .replace("(not (= ", "(not (= true ")
        .replace(" true))", "))");
    checked_control(&reversed, "true-on-left");
    let wrapped = source(4, 4, 3, false, false)
        .replace("(bvsub point base)", "(bvsub point (_ bv14 4))")
        .replace("(bvadd base (_ bv3 4))", "(_ bv1 4)");
    checked_control(&wrapped, "constant-start-wrap");
}

#[test]
fn range_witnesses_from_a_foreign_arena_are_refused() {
    let input = source(4, 3, 0, false, false);
    let (mut exec, root) = prepared(&input);
    let mut search = GroundSearch::default();
    exec.register_ground_subterms(&mut search.closure, root)
        .unwrap();
    let conflict = exec
        .saturate_ground_search(&mut search, &[root], &[])
        .unwrap();
    assert!(search
        .read_chains
        .witnesses
        .iter()
        .any(|w| w.skipped.iter().any(|s| s.range.is_some())));
    let (mut foreign, _) = prepared(&input.replace("#x35", "#x36"));
    assert!(foreign
        .emit_ground_closure_refutation(&search, conflict)
        .is_none());
}

#[test]
fn an_actual_range_congruence_still_refuses_a_wrong_printed_arity() {
    let input = source(4, 3, 0, false, false);
    let (mut exec, root) = prepared(&input);
    let proof = exec.early_ground_closure_memory_candidate(root).unwrap();
    let delta = proof
        .steps
        .iter()
        .find_map(|step| {
            let ProofStep::TheoryLemma {
                clause,
                kind: TheoryLemmaKind::EufCongruent,
                ..
            } = step
            else {
                return None;
            };
            let (left, _) = decode_eq_local(&exec.ctx.terms, *clause.last()?)?;
            matches!(exec.ctx.terms.get(left),TermData::App(Symbol::Named(head),_) if head=="bvsub")
                .then_some(left)
        })
        .unwrap();
    let mut overrides = ay_core::kani_compat::DetHashMap::default();
    overrides.insert(delta, "(bvsub point base (_ bv0 4))".to_string());
    let surfaces = exec.authored_export_surfaces();
    assert!(exec
        .in_alethe_dialect(|| ay_proof::try_export_alethe_with_authored_surfaces(
            &proof,
            &exec.ctx.terms,
            &[root],
            Some(&overrides),
            surfaces.channels(),
            None
        ))
        .is_err());
}
