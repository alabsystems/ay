// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;
use ay_core::{FarkasAnnotation, Sort, TheoryLemmaKind};

struct Fixture {
    terms: TermStore,
    clause: Vec<TermId>,
    vars: [TermId; 5],
}

impl Fixture {
    fn new() -> Self {
        let mut terms = TermStore::new();
        let vars = ["d", "u0", "u1", "c", "v3"].map(|name| terms.mk_var(name, Sort::Int));
        let one = terms.mk_int(1.into());
        let d1 = terms.mk_app(Symbol::named("+"), [vars[0], one], Sort::Int);
        let c1 = terms.mk_app(Symbol::named("+"), [vars[3], one], Sort::Int);
        let mut clause = Vec::new();
        for (left, right) in [
            (vars[0], vars[2]),
            (vars[1], vars[2]),
            (vars[1], d1),
            (vars[3], vars[4]),
        ] {
            let equality = terms.mk_app(Symbol::named("="), [left, right], Sort::Bool);
            clause.push(terms.mk_not_raw(equality));
        }
        clause.push(terms.mk_app(Symbol::named("="), [vars[4], c1], Sort::Bool));
        Self {
            terms,
            clause,
            vars,
        }
    }

    fn step(&self) -> ProofStep {
        ProofStep::TheoryLemma {
            theory: "arith".into(),
            clause: self.clause.clone(),
            farkas: Some(FarkasAnnotation::from_ints(&[999])),
            kind: TheoryLemmaKind::LiaGeneric,
            lia: None,
        }
    }

    fn supported(&self, overrides: Option<&HashMap<TermId, String>>) -> bool {
        let mut work = SCREEN_WORK;
        checked_affine_equality_cycle_lowering_supported(
            &self.terms,
            &TheoryLemmaKind::LiaGeneric,
            &self.clause,
            overrides,
            &mut work,
        )
    }

    fn rendered(&self, overrides: Option<&HashMap<TermId, String>>) -> String {
        AlethePrinter::new_with_overrides_and_budget(&self.terms, overrides, Some(SCREEN_WORK))
            .format_step(&self.step(), ProofId(7))
            .unwrap()
    }
}

#[test]
fn affine_equality_cycle_reproves_the_subset_and_preserves_all_original_literals() {
    let fixture = Fixture::new();
    assert!(fixture.supported(None));
    let text = fixture.rendered(None);
    assert!(text.contains(":rule la_generic"), "{text}");
    assert!(text.contains(":rule or_neg"), "{text}");
    assert!(text.contains(":rule resolution"), "{text}");
    assert!(text.contains(":rule or :premises"), "{text}");
    assert!(!text.contains(":rule hole"), "{text}");
    let original = AlethePrinter::new(&fixture.terms).format_clause(&fixture.clause);
    assert!(text.lines().last().unwrap().contains(&original), "{text}");
    assert!(original.contains("v3"));
    assert!(
        !text.contains("999"),
        "producer hints are not a certificate"
    );
}

#[test]
fn affine_equality_cycle_exact_orientation_flips_are_independently_rechecked() {
    let fixture = Fixture::new();
    for (index, text) in [
        (0, "(not (= u1 d))"),
        (1, "(not (= u1 u0))"),
        (2, "(not (= (+ d 1) u0))"),
    ] {
        let overrides = HashMap::from_iter([(fixture.clause[index], text.into())]);
        assert!(fixture.supported(Some(&overrides)));
        let text = fixture.rendered(Some(&overrides));
        assert!(!text.contains(":rule hole"), "{text}");
    }
}

#[test]
fn affine_equality_cycle_consistent_rows_and_positive_premises_do_not_gain_credit() {
    let mut fixture = Fixture::new();
    let consistent = fixture.terms.mk_app(
        Symbol::named("="),
        [fixture.vars[1], fixture.vars[0]],
        Sort::Bool,
    );
    fixture.clause[2] = fixture.terms.mk_not_raw(consistent);
    assert!(!fixture.supported(None));
    let mut fixture = Fixture::new();
    let TermData::Not(atom) = fixture.terms.get(fixture.clause[0]) else {
        unreachable!()
    };
    fixture.clause[0] = *atom;
    assert!(!fixture.supported(None));
}

#[test]
fn affine_equality_cycle_changed_selected_atoms_and_interiors_decline() {
    let fixture = Fixture::new();
    for (term, text) in [
        (fixture.vars[0], "true"),
        (fixture.clause[0], "(= d u1)"),
        (fixture.clause[0], "(not (= d u0))"),
        (fixture.clause[2], "(not (= u0 (+ d 2)))"),
        (fixture.clause[4], "1"),
    ] {
        let overrides = HashMap::from_iter([(term, text.into())]);
        assert!(!fixture.supported(Some(&overrides)));
    }
}

#[test]
fn affine_equality_cycle_forged_printed_coefficients_fail_the_same_byte_judge() {
    let fixture = Fixture::new();
    let printer = AlethePrinter::new(&fixture.terms);
    let text = fixture.rendered(None);
    let first = text.lines().next().unwrap();
    let start = first.find(":args (").unwrap() + ":args (".len();
    let forged = format!(
        "{}0 0 0))\n{}",
        &first[..start],
        text.lines().skip(1).collect::<Vec<_>>().join("\n")
    );
    let checked = printer
        .judge_printed_la_generic(&fixture.step(), ProofId(7), forged)
        .unwrap();
    assert!(checked.contains(":rule hole"), "{checked}");
}

#[test]
fn affine_equality_cycle_active_local_ledger_refuses_forged_boolean_premises_and_literals() {
    let fixture = Fixture::new();
    let printer = AlethePrinter::new(&fixture.terms);
    printer.printed_clause_ledger_active.set(true);
    let text = printer.format_step(&fixture.step(), ProofId(7)).unwrap();
    assert!(!text.contains(":rule hole"), "{text}");
    for forged in [
        text.replace(":premises (t7.cycle.weak)", ":premises (t7.missing)"),
        text.replace("(step t7 (cl (not (= d u1))", "(step t7 (cl (not (= d u0))"),
    ] {
        assert_ne!(forged, text);
        let checked = printer
            .judge_printed_premise_rules(&fixture.step(), ProofId(7), forged)
            .unwrap();
        assert!(checked.contains(":rule hole"), "{checked}");
    }
}

#[test]
fn affine_equality_cycle_generic_kind_malformed_ids_and_budget_remain_fail_closed() {
    let fixture = Fixture::new();
    let mut work = SCREEN_WORK;
    assert!(!checked_affine_equality_cycle_lowering_supported(
        &fixture.terms,
        &TheoryLemmaKind::Generic,
        &fixture.clause,
        None,
        &mut work
    ));
    let mut no_work = 0;
    assert!(!checked_affine_equality_cycle_lowering_supported(
        &fixture.terms,
        &TheoryLemmaKind::LiaGeneric,
        &fixture.clause,
        None,
        &mut no_work
    ));
    let mut work = 1;
    assert!(!checked_affine_equality_cycle_lowering_supported(
        &fixture.terms,
        &TheoryLemmaKind::LiaGeneric,
        &fixture.clause,
        None,
        &mut work
    ));
    assert_eq!(work, 0);
    let mut bad = fixture.clause.clone();
    bad[0] = TermId(u32::MAX);
    let mut work = SCREEN_WORK;
    assert!(!checked_affine_equality_cycle_lowering_supported(
        &fixture.terms,
        &TheoryLemmaKind::LiaGeneric,
        &bad,
        None,
        &mut work
    ));
}

#[test]
fn affine_equality_cycle_stop_authority_is_preserved_before_elimination_and_emission() {
    let fixture = Fixture::new();
    let _stop = ay_core::resource::enter_check_stop(std::sync::Arc::new(|| true));
    assert!(!fixture.supported(None));
    let mut proceed = || false;
    let printer = AlethePrinter::new(&fixture.terms).with_emission_progress(&mut proceed);
    assert!(printer
        .format_affine_equality_cycle(ProofId(7), &TheoryLemmaKind::LiaGeneric, &fixture.clause)
        .is_none());
    assert!(printer.emission_progress.refused());
}

#[test]
fn affine_equality_cycle_oversized_selected_and_unselected_channels_are_bounded() {
    let fixture = Fixture::new();
    for term in [fixture.vars[0], fixture.clause[4]] {
        let overrides = HashMap::from_iter([(term, "huge".repeat(2 * 1024 * 1024))]);
        assert!(!fixture.supported(Some(&overrides)));
    }
}

fn carcara(case: &str, problem: &str, proof: &str) {
    ay_core::pinned_carcara::pinned_carcara_can_judge(problem, proof)
        .expect("standard checked dialect");
    if !std::process::Command::new("carcara")
        .arg("--version")
        .output()
        .is_ok_and(|out| out.status.success())
    {
        eprintln!("carcara unavailable: skipping affine cycle {case}");
        return;
    }
    let directory =
        std::env::temp_dir().join(format!("ay-affine-cycle-{}-{case}", std::process::id()));
    std::fs::create_dir_all(&directory).unwrap();
    std::fs::write(directory.join("query.smt2"), problem).unwrap();
    std::fs::write(directory.join("proof.alethe"), proof).unwrap();
    let result = std::process::Command::new("carcara")
        .args(["check", "--"])
        .arg(directory.join("proof.alethe"))
        .arg(directory.join("query.smt2"))
        .output()
        .unwrap();
    let _ = std::fs::remove_dir_all(directory);
    assert_eq!(
        String::from_utf8_lossy(&result.stdout).trim(),
        "valid",
        "{}\n{proof}",
        String::from_utf8_lossy(&result.stderr)
    );
}

#[test]
fn affine_equality_cycle_whole_carcara_keeps_original_assumptions_when_one_row_flips() {
    let fixture = Fixture::new();
    let overrides = HashMap::from_iter([(fixture.clause[0], "(not (= u1 d))".into())]);
    let text = fixture.rendered(Some(&overrides));
    assert!(!text.contains(":rule hole"), "{text}");
    let problem = "(set-logic QF_LIA)\n\
        (declare-const d Int)\n(declare-const u0 Int)\n(declare-const u1 Int)\n\
        (declare-const c Int)\n(declare-const v3 Int)\n\
        (assert (= d u1))\n(assert (= u0 u1))\n(assert (= u0 (+ d 1)))\n\
        (assert (= c v3))\n(assert (not (= v3 (+ c 1))))\n(check-sat)\n";
    let proof = format!(
        "(assume h0 (= d u1))\n(assume h1 (= u0 u1))\n\
         (assume h2 (= u0 (+ d 1)))\n(assume h3 (= c v3))\n\
         (assume h4 (not (= v3 (+ c 1))))\n{text}\n\
         (step sy (cl (= (= d u1) (= u1 d))) :rule eq_symmetric)\n\
         (step sp (cl (not (= (= d u1) (= u1 d))) (not (= d u1)) (= u1 d)) :rule equiv_pos2)\n\
         (step hs (cl (= u1 d)) :rule resolution :premises (h0 sy sp))\n\
         (step t8 (cl) :rule resolution :premises (hs h1 h2 h3 h4 t7))\n"
    );
    carcara("single-orientation", problem, &proof);
}

#[test]
fn affine_equality_cycle_whole_carcara_checks_rational_source_weights() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Int);
    let y = terms.mk_var("y", Sort::Int);
    let z = terms.mk_var("z", Sort::Int);
    let one = terms.mk_int(1.into());
    let two = terms.mk_int(2.into());
    let three = terms.mk_int(3.into());
    let x2 = terms.mk_app(Symbol::named("*"), [two, x], Sort::Int);
    let y3 = terms.mk_app(Symbol::named("*"), [three, y], Sort::Int);
    let z2 = terms.mk_app(Symbol::named("*"), [two, z], Sort::Int);
    let x3 = terms.mk_app(Symbol::named("*"), [three, x], Sort::Int);
    let x31 = terms.mk_app(Symbol::named("+"), [x3, one], Sort::Int);
    let mut clause = Vec::new();
    for (left, right) in [(x2, y), (y3, z2), (z, x31)] {
        let atom = terms.mk_app(Symbol::named("="), [left, right], Sort::Bool);
        clause.push(terms.mk_not_raw(atom));
    }
    let witness =
        ay_core::proof_validation::arith_inconsistent_equality_subset_witness(&terms, &clause)
            .unwrap();
    assert!(witness
        .coefficients
        .iter()
        .any(|weight| weight.denom() == &num_bigint::BigInt::from(2)));
    let step = ProofStep::TheoryLemma {
        theory: "arith".into(),
        clause,
        farkas: None,
        kind: TheoryLemmaKind::LiaGeneric,
        lia: None,
    };
    let text = AlethePrinter::new(&terms)
        .format_step(&step, ProofId(7))
        .unwrap();
    assert!(!text.contains(":rule hole"), "{text}");
    let problem = "(set-logic QF_LIA)\n(declare-const x Int)\n(declare-const y Int)\n(declare-const z Int)\n\
        (assert (= (* 2 x) y))\n(assert (= (* 3 y) (* 2 z)))\n(assert (= z (+ (* 3 x) 1)))\n(check-sat)\n";
    let proof = format!(
        "(assume h0 (= (* 2 x) y))\n(assume h1 (= (* 3 y) (* 2 z)))\n\
        (assume h2 (= z (+ (* 3 x) 1)))\n{text}\n\
        (step t8 (cl) :rule resolution :premises (h0 h1 h2 t7))\n"
    );
    carcara("rational-weights", problem, &proof);
}
