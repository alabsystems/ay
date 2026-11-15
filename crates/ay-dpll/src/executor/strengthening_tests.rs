// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Evidence policy P1 (2026-10-02): every re-solve used as evidence runs with
//! every satisfiability-preserving strengthening off.

use super::{
    override_global_switches_for_test, Strengthening, StrengtheningPolicy, StrengtheningSet,
};
use crate::executor::unsat_cert::CommandUnsatAdmission;
use crate::executor::{CorroborationMethod, Executor, UnsatCorroboration, UnsatEvidenceLevel};
use ay_frontend::parse;

/// The E13 audit's 13-line LNH witness (`l02_lnh_compound_domain_uf`): z3
/// 5.1.0 answers `sat`, and so does AY with LNH off. On main `a68e18a38f`
/// the default posture published `unsat`, admitted as `discharged-trust`,
/// because the corroborating re-solve ran the same symmetry breaking.
const LNH_COMPOUND_DOMAIN_SAT: &str = r"
(set-logic QF_UF)
(declare-sort U 0)
(declare-fun f (U) U)
(declare-const e U) (declare-const c U) (declare-const b U) (declare-const b2 U)
(declare-const a0 U) (declare-const a1 U) (declare-const a2 U) (declare-const a3 U) (declare-const a4 U)
(assert (or (= e (f a0)) (= e (f a1)) (= e (f a2)) (= e (f a3)) (= e (f a4))))
(assert (or (= a0 b) (= a0 b2)))
(assert (= (f b) c))
(assert (= (f b2) c))
(assert (not (= e c)))
(check-sat)
";

/// Pigeonhole 7 into 6 over declared constants (main's LNH on/off agreement
/// fixture `php7_6_symmetric_unsat`; z3 5.1.0: unsat): the shape LNH exists
/// for, and one it still engages on after its domain fix limited it to
/// declared free constants (on which it no longer engages the witness above).
const LNH_PIGEONHOLE_UNSAT: &str = r"
(set-logic QF_UF)
(declare-sort U 0)
(declare-const c0 U) (declare-const c1 U) (declare-const c2 U)
(declare-const c3 U) (declare-const c4 U) (declare-const c5 U)
(declare-const x0 U) (declare-const x1 U) (declare-const x2 U) (declare-const x3 U)
(declare-const x4 U) (declare-const x5 U) (declare-const x6 U)
(assert (distinct c0 c1 c2 c3 c4 c5))
(assert (or (= x0 c0) (= x0 c1) (= x0 c2) (= x0 c3) (= x0 c4) (= x0 c5)))
(assert (or (= x1 c0) (= x1 c1) (= x1 c2) (= x1 c3) (= x1 c4) (= x1 c5)))
(assert (or (= x2 c0) (= x2 c1) (= x2 c2) (= x2 c3) (= x2 c4) (= x2 c5)))
(assert (or (= x3 c0) (= x3 c1) (= x3 c2) (= x3 c3) (= x3 c4) (= x3 c5)))
(assert (or (= x4 c0) (= x4 c1) (= x4 c2) (= x4 c3) (= x4 c4) (= x4 c5)))
(assert (or (= x5 c0) (= x5 c1) (= x5 c2) (= x5 c3) (= x5 c4) (= x5 c5)))
(assert (or (= x6 c0) (= x6 c1) (= x6 c2) (= x6 c3) (= x6 c4) (= x6 c5)))
(assert (distinct x0 x1 x2 x3 x4 x5 x6))
(check-sat)
";

/// `(= a b)` and `(not (= (f a) (f b)))` over a fresh uninterpreted sort.
pub(in crate::executor) fn congruence_clash(
    exec: &mut Executor,
    prefix: &str,
) -> (ay_core::TermId, ay_core::TermId) {
    let sort = ay_core::Sort::Uninterpreted(format!("{prefix}_U"));
    let a = exec.ctx.terms.mk_var(&format!("{prefix}_a"), sort.clone());
    let b = exec.ctx.terms.mk_var(&format!("{prefix}_b"), sort.clone());
    let f = ay_core::term::Symbol::named(&format!("{prefix}_f"));
    let fa = exec.ctx.terms.mk_app(f.clone(), [a], sort.clone());
    let fb = exec.ctx.terms.mk_app(f, [b], sort);
    let a_eq_b = exec.ctx.terms.mk_eq(a, b);
    let fa_eq_fb = exec.ctx.terms.mk_eq(fa, fb);
    let fa_ne_fb = exec.ctx.terms.mk_not(fa_eq_fb);
    (a_eq_b, fa_ne_fb)
}

fn run(exec: &mut Executor, script: &str) -> Vec<String> {
    let commands = parse(script).expect("parse");
    exec.execute_all(&commands).expect("execute")
}

#[test]
fn strengthening_set_spells_none_and_its_members() {
    assert_eq!(StrengtheningSet::EMPTY.tags(), "none");
    assert!(StrengtheningSet::EMPTY.is_empty());
    let lnh = StrengtheningSet::EMPTY.with(Strengthening::LnhSymmetry);
    assert!(lnh.contains(Strengthening::LnhSymmetry));
    assert_eq!(lnh.tags(), "lnh-symmetry");
    for strengthening in Strengthening::ALL {
        assert!(!StrengtheningSet::EMPTY.contains(strengthening));
    }
}

/// The per-executor half of the gate: a public solve may run what the CLI
/// enables; the executor every certification re-solve runs in may run none.
#[test]
fn a_derived_query_executor_runs_no_strengthening() {
    let parent = Executor::new();
    assert_eq!(parent.strengthening_policy, StrengtheningPolicy::Permitted);
    let derived = parent.new_derived_query_executor();
    assert_eq!(derived.strengthening_policy, StrengtheningPolicy::ForcedOff);
    for strengthening in Strengthening::ALL {
        assert!(
            !derived.strengthening_permitted(strengthening),
            "{} must never run in a checking re-solve",
            strengthening.tag()
        );
    }
}

/// A checking re-solve's nested probes are fresh executors (`Permitted` by
/// default); the checking-solve scope its `check_sat` holds turns them off
/// too. Shown with the strengthenings globally ON whatever the CLI default is,
/// so this never passes vacuously.
#[test]
fn every_executor_inside_a_checking_solve_runs_no_strengthening() {
    override_global_switches_for_test(Some(true));
    let parent = Executor::new();
    let derived = parent.new_derived_query_executor();
    for strengthening in Strengthening::ALL {
        assert!(parent.strengthening_permitted(strengthening));
        assert!(!derived.strengthening_permitted(strengthening));
    }
    assert!(
        parent.enter_checking_solve_scope().is_none(),
        "a public solve marks nothing"
    );
    {
        let _scope = derived
            .enter_checking_solve_scope()
            .expect("a checking solve");
        let nested_probe = Executor::new();
        for strengthening in Strengthening::ALL {
            assert!(
                !nested_probe.strengthening_permitted(strengthening),
                "{} ran in a probe nested inside a checking re-solve",
                strengthening.tag()
            );
            assert!(!parent.strengthening_permitted(strengthening));
        }
    }
    for strengthening in Strengthening::ALL {
        assert!(
            Executor::new().strengthening_permitted(strengthening),
            "the scope ends with the checking solve"
        );
    }
    override_global_switches_for_test(None);
}

/// P1 with LNH globally ON (as it is by default since its domain fix landed):
/// the public solve of the pigeonhole witness applies the symmetry breaking,
/// its LNH facts reach the refutation as trust steps, and the re-solve that
/// corroborates them runs without it — the label says so
/// (`disabled=lnh-symmetry`) — and still refutes the problem. Removing the
/// per-executor gate makes the derived re-solve apply LNH and this test fail.
#[test]
fn with_lnh_globally_on_a_checking_resolve_still_runs_without_it() {
    override_global_switches_for_test(Some(true));
    let mut public = Executor::new();
    let outputs = run(&mut public, LNH_PIGEONHOLE_UNSAT);
    assert!(
        public
            .strengthenings_applied()
            .contains(Strengthening::LnhSymmetry),
        "the witness must engage LNH when it is globally on, or this test shows nothing"
    );
    assert_eq!(outputs, ["unsat"], "z3 5.1.0 answers unsat");
    if let Some(corroboration) = public.last_unsat_corroboration() {
        if matches!(
            corroboration.method(),
            CorroborationMethod::Resolve | CorroborationMethod::Entailment
        ) {
            assert!(
                corroboration
                    .disabled()
                    .contains(Strengthening::LnhSymmetry),
                "the re-solve ran without LNH and its label must say so: {corroboration:?}"
            );
        }
    }

    let mut derived = public.new_derived_query_executor();
    derived.begin_public_solve(false);
    let verdict = derived.check_sat().expect("derived re-solve");
    assert!(
        derived.strengthenings_applied().is_empty(),
        "a checking re-solve applied {:?}",
        derived.strengthenings_applied()
    );
    assert!(
        verdict.is_unsat(),
        "the LNH-free re-solve still refutes the pigeonhole, got {verdict:?}"
    );
    override_global_switches_for_test(None);
}

/// End to end: the corroborating re-solve of the LNH witness, run in the
/// derived executor, applies no strengthening and finds the model; and the
/// default posture therefore never publishes the wrong `unsat`, whether or
/// not LNH is enabled for the public solve.
#[test]
fn a_corroborating_resolve_of_the_lnh_witness_runs_without_lnh() {
    let mut exec = Executor::new();
    let outputs = run(&mut exec, LNH_COMPOUND_DOMAIN_SAT);
    assert!(
        !outputs.iter().any(|line| line == "unsat"),
        "z3 5.1.0 answers sat; the default posture must never publish unsat: {outputs:?}"
    );

    let mut derived = exec.new_derived_query_executor();
    derived.begin_public_solve(false);
    let verdict = derived.check_sat().expect("derived re-solve");
    assert!(
        derived.strengthenings_applied().is_empty(),
        "a checking re-solve recorded a strengthening: {:?}",
        derived.strengthenings_applied()
    );
    assert!(
        verdict.is_sat(),
        "without symmetry breaking the witness is satisfiable, got {verdict:?}"
    );
}

/// The ledger records what a public query applied, names it on a re-solve
/// corroboration (`disabled=`), and starts empty for every public query.
#[test]
fn the_strengthening_ledger_labels_a_resolve_and_resets_per_query() {
    let mut exec = Executor::new();
    exec.begin_public_solve(false);
    assert!(exec.strengthenings_applied().is_empty());
    exec.record_strengthening_applied(Strengthening::LnhSymmetry);
    let corroboration = UnsatCorroboration::resolve(exec.strengthenings_applied());
    assert_eq!(corroboration.disabled().tags(), "lnh-symmetry");
    exec.begin_public_solve(false);
    assert!(
        exec.strengthenings_applied().is_empty(),
        "the ledger describes one public decision"
    );
}

/// Through the funnel: a trust-bearing refutation is admitted as
/// `discharged-trust` at E1 and names its corroboration. A re-solve names the
/// strengthenings the solve applied and it ran without; a standalone check
/// runs no solve that could disable one, so it reads `disabled=none`.
#[test]
fn a_discharged_trust_admission_names_its_corroboration() {
    for applied in [false, true] {
        let mut exec = Executor::new();
        let (a_eq_b, fa_ne_fb) = congruence_clash(&mut exec, "p1_label");
        exec.ctx.assertions = vec![a_eq_b, fa_ne_fb];
        exec.begin_public_solve(false);
        exec.bind_unsat_query_assumptions(&[]);
        assert!(exec.check_sat().expect("solve").is_unsat());
        // Force the trust-discharge funnel: no SAT sidecar, and a proof whose
        // one step is a terminal trust.
        exec.last_checked_sat_refutation = None;
        let mut trust_proof = ay_core::Proof::new();
        trust_proof.add_rule_step(
            ay_core::AletheRule::Trust,
            Vec::new(),
            Vec::new(),
            Vec::new(),
        );
        exec.last_proof = Some(trust_proof);
        if applied {
            exec.record_strengthening_applied(Strengthening::LnhSymmetry);
        }
        let published =
            exec.certify_unsat_for_publication(crate::executor_types::SolveResult::unsat(), &[]);
        assert!(published.is_unsat());
        let certificate = exec.take_unsat_certificate().expect("token");
        assert_eq!(
            certificate.command_admission(),
            CommandUnsatAdmission::DischargedTrust
        );
        let evidence = certificate.evidence();
        assert_eq!(evidence.level(), UnsatEvidenceLevel::E1);
        let corroboration = evidence.corroboration().expect("corroboration");
        let expected = match corroboration.method() {
            CorroborationMethod::Resolve | CorroborationMethod::Entailment if applied => {
                StrengtheningSet::EMPTY.with(Strengthening::LnhSymmetry)
            }
            CorroborationMethod::Resolve
            | CorroborationMethod::Entailment
            | CorroborationMethod::StandaloneTautology => StrengtheningSet::EMPTY,
        };
        assert_eq!(corroboration.disabled(), expected);
    }
}
