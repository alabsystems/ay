// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Tests for the div/mod purification promotion lane.
//!
//! The local validity of one atom is tested in `ay-core`'s
//! `divmod_def_tests.rs`, the whole-proof conditions in `ay-proof`'s
//! `fresh_def` divmod tests. What is pinned HERE is the producer: which steps
//! the lane rewrites, which it must leave alone, and that a real solve's
//! refutation is strictly admitted afterwards while a renderable authored
//! certificate an earlier route built is never displaced.

use ay_core::term::DivModPurification;
use ay_core::{AletheRule, Proof, ProofStep, Sort, TermId, TheoryLemmaKind};
use ay_frontend::parse;
use num_bigint::BigInt;

use crate::Executor;

/// `(assert (< 100 (div x 2))) (assert (< x 10))`: refuted only through the
/// purification `x = 2*q + r`, `0 <= r`.
const SYMBOLIC_DIV_UNSAT: &str = r#"
    (set-logic QF_LIA)
    (declare-const x Int)
    (assert (< 100 (div x 2)))
    (assert (< x 10))
    (check-sat)
"#;

/// The purification pair and the trust leaves `mod_div_elim` leaves behind.
struct Fixture {
    exec: Executor,
    x: TermId,
    q: TermId,
    r: TermId,
}

/// A pair for `(div x 2)` / `(mod x 2)`, minted AND recorded as
/// `mod_div_elim` mints and records one.
fn fixture() -> Fixture {
    let mut f = unrecorded_fixture();
    let divisor = f.int(2);
    f.exec
        .ctx
        .terms
        .register_divmod_purification(DivModPurification {
            quotient: f.q,
            remainder: f.r,
            dividend: f.x,
            divisor,
        });
    f
}

/// The same symbols with NO mint-site record: names alone grant nothing.
fn unrecorded_fixture() -> Fixture {
    let mut exec = Executor::new();
    let x = exec.ctx.terms.mk_var("x".to_string(), Sort::Int);
    let q = exec.ctx.terms.mk_fresh_var("_divmod_q", Sort::Int);
    let r = exec.ctx.terms.mk_fresh_var("_divmod_r", Sort::Int);
    Fixture { exec, x, q, r }
}

impl Fixture {
    fn int(&mut self, value: i64) -> TermId {
        self.exec.ctx.terms.mk_int(BigInt::from(value))
    }

    fn equation(&mut self) -> TermId {
        let two = self.int(2);
        let terms = &mut self.exec.ctx.terms;
        let scaled = terms.mk_mul(vec![two, self.q]);
        let sum = terms.mk_add(vec![scaled, self.r]);
        terms.mk_eq(self.x, sum)
    }

    fn lower(&mut self) -> TermId {
        let zero = self.int(0);
        self.exec.ctx.terms.mk_ge(self.r, zero)
    }

    fn upper(&mut self, bound: i64) -> TermId {
        let bound = self.int(bound);
        self.exec.ctx.terms.mk_lt(self.r, bound)
    }

    fn authored(&mut self) -> TermId {
        let ten = self.int(10);
        self.exec.ctx.terms.mk_lt(self.x, ten)
    }

    fn promote(&mut self, proof: &mut Proof, authored: TermId) -> bool {
        self.exec
            .promote_divmod_purification_definitions(proof, &[authored])
    }
}

fn trust(proof: &mut Proof, atom: TermId) {
    proof.add_rule_step(AletheRule::Trust, vec![atom], Vec::new(), Vec::new());
}

fn rule_at(proof: &Proof, index: usize) -> &AletheRule {
    match &proof.steps[index] {
        ProofStep::Step { rule, .. } => rule,
        other => panic!("step {index} is not a rule step: {other:?}"),
    }
}

#[test]
fn the_purification_triple_is_promoted_and_the_registry_accepts_it() {
    let mut f = fixture();
    let authored = f.authored();
    let (equation, lower, upper) = (f.equation(), f.lower(), f.upper(2));
    let mut proof = Proof::new();
    proof.add_assume(authored, None);
    trust(&mut proof, equation);
    trust(&mut proof, lower);
    trust(&mut proof, upper);
    assert!(f.promote(&mut proof, authored));
    for index in 1..=3 {
        assert_eq!(
            rule_at(&proof, index),
            &AletheRule::DivModDef,
            "step {index}"
        );
    }
    let registry =
        ay_proof::FreshDefRegistry::collect(&proof, &f.exec.ctx.terms, Some(&[authored]))
            .expect("q := (div x 2), r := (mod x 2) is a conservative extension");
    assert_eq!(registry.len(), 2);
}

#[test]
fn a_pair_is_recovered_from_its_remainder_alone() {
    // Mint-site provenance: the refutation used only the bounds, so neither
    // the quotient nor the equation is in the proof. The pair is still found
    // from `r`, and both bounds are promoted.
    let mut f = fixture();
    let authored = f.authored();
    let (lower, upper) = (f.lower(), f.upper(2));
    let mut proof = Proof::new();
    proof.add_assume(authored, None);
    trust(&mut proof, lower);
    trust(&mut proof, upper);
    assert!(f.promote(&mut proof, authored));
    assert_eq!(rule_at(&proof, 1), &AletheRule::DivModDef);
    assert_eq!(rule_at(&proof, 2), &AletheRule::DivModDef);
    ay_proof::FreshDefRegistry::collect(&proof, &f.exec.ctx.terms, Some(&[authored]))
        .expect("q := (div x 2), r := (mod x 2) is a conservative extension");
}

#[test]
fn a_pair_without_a_mint_site_record_is_never_promoted() {
    // NEGATIVE TWIN of the recovery: the same `_divmod_q`/`_divmod_r` symbols
    // and the same valid triple, but nothing recorded them as a purification.
    // The names choose nothing, so every atom stays `trust`.
    let mut f = unrecorded_fixture();
    let authored = f.authored();
    let (equation, lower, upper) = (f.equation(), f.lower(), f.upper(2));
    let mut proof = Proof::new();
    proof.add_assume(authored, None);
    trust(&mut proof, equation);
    trust(&mut proof, lower);
    trust(&mut proof, upper);
    assert!(!f.promote(&mut proof, authored));
    for index in 1..=3 {
        assert_eq!(rule_at(&proof, index), &AletheRule::Trust, "step {index}");
    }
}

#[test]
fn the_bound_lanes_definition_by_zero_is_reclaimed() {
    // The bound lane reads `(<= 0 r)` as `r := 0`, a definiens the remainder's
    // real definition contradicts; the atom is valid under `r := (mod x 2)`,
    // so it is reclaimed rather than left as a second definition.
    let mut f = fixture();
    let authored = f.authored();
    let (equation, lower) = (f.equation(), f.lower());
    let mut proof = Proof::new();
    proof.add_assume(authored, None);
    trust(&mut proof, equation);
    proof.add_rule_step(
        AletheRule::FreshDefBound,
        vec![lower],
        Vec::new(),
        vec![f.r],
    );
    assert!(f.promote(&mut proof, authored));
    assert_eq!(rule_at(&proof, 1), &AletheRule::DivModDef);
    assert_eq!(rule_at(&proof, 2), &AletheRule::DivModDef);
}

#[test]
fn a_wrong_bound_stays_trust_while_the_valid_atoms_are_promoted() {
    // NEGATIVE TWIN. `r < 1` is FALSE at `x = 1` (`(mod 1 2) = 1`).
    let mut f = fixture();
    let authored = f.authored();
    let (equation, lower, wrong) = (f.equation(), f.lower(), f.upper(1));
    let mut proof = Proof::new();
    proof.add_assume(authored, None);
    trust(&mut proof, equation);
    trust(&mut proof, lower);
    trust(&mut proof, wrong);
    assert!(f.promote(&mut proof, authored));
    assert_eq!(rule_at(&proof, 1), &AletheRule::DivModDef);
    assert_eq!(rule_at(&proof, 2), &AletheRule::DivModDef);
    assert_eq!(
        rule_at(&proof, 3),
        &AletheRule::Trust,
        "an invalid bound is never promoted"
    );
}

#[test]
fn a_quotient_an_assume_mentions_is_not_fresh_and_nothing_is_promoted() {
    // FALSIFYING ASSIGNMENT. `A = {q = 5, x < 10}` is satisfied by `q = 5,
    // x = 0`; `x = 2*q + r, 0 <= r` would force `x >= 10`.
    let mut f = fixture();
    let authored = f.authored();
    let five = f.int(5);
    let pinned = f.exec.ctx.terms.mk_eq(f.q, five);
    let (equation, lower) = (f.equation(), f.lower());
    let mut proof = Proof::new();
    proof.add_assume(authored, None);
    proof.add_assume(pinned, None);
    trust(&mut proof, equation);
    trust(&mut proof, lower);
    assert!(!f.promote(&mut proof, authored));
    assert_eq!(rule_at(&proof, 2), &AletheRule::Trust);
    assert_eq!(rule_at(&proof, 3), &AletheRule::Trust);
}

#[test]
fn a_rewritten_leaf_read_as_a_definition_is_demoted_back_to_trust() {
    // The equality lane reads the rewritten authored leaf `(= r 1)` as the
    // definition `r := 1`: a SECOND definiens for the remainder, and not valid
    // under `r := (mod x 2)` (false at `x = 0`). It goes back to the `trust`
    // it was (for the congruence bridges to derive) instead of costing the
    // pair, and the registry accepts the result.
    let mut f = fixture();
    let authored = f.authored();
    let (equation, lower) = (f.equation(), f.lower());
    let one = f.int(1);
    let rebound = f.exec.ctx.terms.mk_eq(f.r, one);
    let mut proof = Proof::new();
    proof.add_assume(authored, None);
    trust(&mut proof, equation);
    trust(&mut proof, lower);
    proof.add_rule_step(AletheRule::FreshDefEq, vec![rebound], Vec::new(), vec![f.r]);
    assert!(f.promote(&mut proof, authored));
    assert_eq!(rule_at(&proof, 1), &AletheRule::DivModDef);
    assert_eq!(rule_at(&proof, 2), &AletheRule::DivModDef);
    assert_eq!(rule_at(&proof, 3), &AletheRule::Trust);
    ay_proof::FreshDefRegistry::collect(&proof, &f.exec.ctx.terms, Some(&[authored]))
        .expect("one definiens per symbol after the demotion");
}

#[test]
fn a_divmod_definition_with_other_definientia_declines_the_pair() {
    // An existing `divmod_def` binds the remainder to `(mod x 3)`; the
    // mint-site record would bind it to `(mod x 2)`. Two definientia: the
    // pair is declined and nothing changes.
    let mut f = fixture();
    let authored = f.authored();
    let (equation, lower) = (f.equation(), f.lower());
    let three = f.int(3);
    let terms = &mut f.exec.ctx.terms;
    let other_q = terms.mk_intdiv(f.x, three);
    let other_r = terms.mk_mod(f.x, three);
    let mut proof = Proof::new();
    proof.add_assume(authored, None);
    trust(&mut proof, equation);
    proof.add_rule_step(
        AletheRule::DivModDef,
        vec![lower],
        Vec::new(),
        vec![f.q, other_q, f.r, other_r],
    );
    assert!(!f.promote(&mut proof, authored));
    assert_eq!(rule_at(&proof, 1), &AletheRule::Trust);
}

#[test]
fn an_invalid_trust_atom_over_the_remainder_stays_trust() {
    // `(= r 1)` as a demoted leaf is not a definition at all; it simply stays
    // `trust` while the triple is promoted.
    let mut f = fixture();
    let authored = f.authored();
    let (equation, lower) = (f.equation(), f.lower());
    let one = f.int(1);
    let leaf = f.exec.ctx.terms.mk_eq(f.r, one);
    let mut proof = Proof::new();
    proof.add_assume(authored, None);
    trust(&mut proof, equation);
    trust(&mut proof, lower);
    trust(&mut proof, leaf);
    assert!(f.promote(&mut proof, authored));
    assert_eq!(rule_at(&proof, 1), &AletheRule::DivModDef);
    assert_eq!(rule_at(&proof, 2), &AletheRule::DivModDef);
    assert_eq!(rule_at(&proof, 3), &AletheRule::Trust);
}

/// Run `smt` through the caller-authored boundary the CLI uses, configured as
/// the CLI configures `--rigor certified`: fail-closed self-check plus the
/// mandatory proof collection it certifies `unsat` from.
fn solve_authored_self_check(smt: &str) -> (Executor, Vec<String>) {
    let commands = parse(smt).expect("parse");
    let mut exec = Executor::new();
    exec.set_self_check(true);
    exec.set_mandatory_proof_collection();
    let mut out = Vec::new();
    for command in &commands {
        if let Some(line) = exec.execute_authored(command).expect("exec") {
            out.push(line);
        }
    }
    (exec, out)
}

fn has_rule(proof: &Proof, wanted: &AletheRule) -> bool {
    proof
        .steps
        .iter()
        .any(|step| matches!(step, ProofStep::Step { rule, .. } if rule == wanted))
}

#[test]
fn a_symbolic_div_refutation_is_strictly_admitted_under_self_check() {
    // Before the lane: `unknown (incomplete self-check-rejected)`, `step t0
    // uses unverified trust rule`.
    let (exec, out) = solve_authored_self_check(SYMBOLIC_DIV_UNSAT);
    assert_eq!(out, vec!["unsat"]);
    assert_eq!(
        exec.last_command_unsat_admission_tag(),
        Some("strict-proof")
    );
    let proof = exec
        .last_proof
        .as_ref()
        .expect("the admitted refutation is retained");
    assert!(
        has_rule(proof, &AletheRule::DivModDef),
        "the purification reaches the proof as checked definitions"
    );
    assert!(
        !has_rule(proof, &AletheRule::Trust),
        "no trust step remains"
    );
}

#[test]
fn an_authored_mod_range_certificate_is_not_displaced() {
    // `(= (mod x 3) 4)` already has a complete, RENDERABLE authored proof
    // (`lia_mod_range`). The lane runs last and must leave it alone: a
    // `divmod_def` proof would be strict too, but no checker could read it.
    let (exec, out) = solve_authored_self_check(
        "(set-logic QF_LIA)(declare-const x Int)(assert (= (mod x 3) 4))(check-sat)",
    );
    assert_eq!(out, vec!["unsat"]);
    let proof = exec.last_proof.as_ref().expect("retained refutation");
    assert!(!has_rule(proof, &AletheRule::DivModDef));
    assert!(proof.steps.iter().any(|step| matches!(
        step,
        ProofStep::TheoryLemma {
            kind: TheoryLemmaKind::LiaModRange,
            ..
        }
    )));
}

#[test]
fn negative_divisor_remainder_bounds_are_strictly_admitted() {
    // Each is refuted through a remainder BOUND and the rewritten authored
    // leaf alone (`(< r 3)` with `(< 2 r)`, ...), so no purification equation
    // is in the proof: only the mint-site record finds the pair. A positive
    // divisor is answered earlier by `lia_mod_range`.
    for smt in [
        "(set-logic QF_LIA)(declare-const x Int)(assert (< 2 (mod x (- 3))))(check-sat)",
        "(set-logic QF_LIA)(declare-const x Int)(assert (< (mod x (- 3)) 0))(check-sat)",
        "(set-logic QF_LIA)(declare-const x Int)(assert (< 4 (mod x (- 5))))(check-sat)",
    ] {
        let (exec, out) = solve_authored_self_check(smt);
        assert_eq!(out, vec!["unsat"], "{smt}");
        assert_eq!(
            exec.last_command_unsat_admission_tag(),
            Some("strict-proof"),
            "{smt}"
        );
        let proof = exec.last_proof.as_ref().expect("retained refutation");
        assert!(has_rule(proof, &AletheRule::DivModDef), "{smt}");
        assert!(!has_rule(proof, &AletheRule::Trust), "{smt}");
    }
}

#[test]
fn satisfiable_div_mod_problems_are_not_refuted() {
    // PIPELINE SANITY, not a negative twin of the lane: the lane runs only
    // while an UNSAT proof is assembled, so it cannot reach a satisfiable
    // problem. The lane's negative twins are the wrong-bound and unrecorded
    // tests above, the checker-level tests, and the tampered-atom test below.
    for smt in [
        "(set-logic QF_LIA)(declare-const x Int)(assert (< 100 (div x 2)))(assert (< x 300))(check-sat)",
        "(set-logic QF_LIA)(declare-const x Int)(assert (= (mod x 2) 1))(assert (> x 4))(assert (< x 7))(check-sat)",
        "(set-logic QF_LIA)(declare-const x Int)(assert (= (div x (- 3)) 2))(assert (= (mod x (- 3)) 2))(check-sat)",
        "(set-logic QF_LIA)(declare-const x Int)(assert (< 1 (mod x (- 3))))(check-sat)",
        "(set-logic QF_LIA)(declare-const x Int)(assert (<= 0 (mod x (- 3))))(check-sat)",
    ] {
        let (_, out) = solve_authored_self_check(smt);
        assert_eq!(out, vec!["sat"], "{smt}");
    }
}

#[test]
fn an_incomplete_promotion_is_restored_byte_identically() {
    // The last-resort pass commits only a strictly COMPLETE proof. Here the
    // triple is promotable but the proof derives no empty clause, so the
    // strict check is incomplete and every step must come back unchanged.
    let mut f = fixture();
    let authored = f.authored();
    let (equation, lower, upper) = (f.equation(), f.lower(), f.upper(2));
    let mut proof = Proof::new();
    proof.add_assume(authored, None);
    trust(&mut proof, equation);
    trust(&mut proof, lower);
    trust(&mut proof, upper);
    let before = format!("{:?}", proof.steps);
    f.exec.promote_divmod_definitions_last_resort(&mut proof);
    assert_eq!(format!("{:?}", proof.steps), before);
    // The same proof IS promotable: the restore, not a decline, kept it.
    assert!(f.promote(&mut proof, authored));
}

#[test]
fn rewritten_mod_leaves_are_bridged_from_their_authored_roots() {
    // `(= (mod x 2) 1)` and `(= (mod x 4) 0)` reach the refutation as the
    // rewritten leaves `(= r 1)` / `(= r' 0)`; only the `divmod_def` bindings
    // offered to the congruence bridge as `fresh_def_eq` hypotheses derive
    // them from their authored roots.
    for smt in [
        "(set-logic QF_LIA)(declare-const x Int)(assert (= (mod x 2) 1))(assert (= (mod x 4) 0))(check-sat)",
        "(set-logic QF_LIA)(declare-const x Int)(declare-const y Int)(assert (= (mod x 3) 1))(assert (= (* 3 y) x))(check-sat)",
    ] {
        let (exec, out) = solve_authored_self_check(smt);
        assert_eq!(out, vec!["unsat"], "{smt}");
        assert_eq!(
            exec.last_command_unsat_admission_tag(),
            Some("strict-proof"),
            "{smt}"
        );
    }
}

#[test]
fn a_tampered_purification_atom_in_the_real_proof_is_refused() {
    // END-TO-END NEGATIVE TWIN at the checker boundary the pipeline uses:
    // take the admitted refutation and replace one `divmod_def` atom by an
    // invalid one with the SAME `:args` (`1 <= r`, FALSE at `x = 0`). The
    // strict checker must refuse it for that reason, not for another.
    let (mut exec, out) = solve_authored_self_check(SYMBOLIC_DIV_UNSAT);
    assert_eq!(out, vec!["unsat"]);
    let mut proof = exec.last_proof.clone().expect("retained refutation");
    assert!(exec
        .check_proof_strict_with_datatypes(&proof)
        .is_ok_and(|quality| quality.is_complete()));
    let index = proof
        .steps
        .iter()
        .position(|step| {
            matches!(
                step,
                ProofStep::Step {
                    rule: AletheRule::DivModDef,
                    ..
                }
            )
        })
        .expect("a divmod_def step");
    let ProofStep::Step { args, .. } = &proof.steps[index] else {
        unreachable!()
    };
    let remainder = args[2];
    let one = exec.ctx.terms.mk_int(BigInt::from(1));
    let wrong = exec.ctx.terms.mk_le(one, remainder);
    if let ProofStep::Step { clause, .. } = &mut proof.steps[index] {
        *clause = vec![wrong];
    }
    let error = exec
        .check_proof_strict_with_datatypes(&proof)
        .expect_err("an invalid purification atom is never admitted");
    assert!(format!("{error:?}").contains("not valid"), "{error:?}");
}
