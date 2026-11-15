// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#![allow(clippy::panic)]

//! Capability regression: AY must DERIVE `unsat` on a quantified UFBV `fixpoint`
//! check whose universal is genuinely violated (#quantified-premise-forced).
//!
//! Minimized from the SV-COMP `wintersteiger fmsd13 fixpoint` benchmarks (20
//! UFBV + 1 UFNIRA of which AY once answered a wrong `sat` — see the sibling
//! `ufbv_deferred_selfcheck_failclosed` soundness test). The body is
//! `∀xs. (premise(xs) ⟹ conclusion(xs, UF))`: the `premise` is an SSA equality
//! chain that PINS the binders (a0=1, a1=2, a2=3), and the `conclusion` defines
//! uninterpreted functions pointwise (fa0/fa1/fa2 = the same computation) and
//! then asserts a FIXPOINT disjunction `(or (= a2 (fa0 …)) (= a2 (fa1 …)))`.
//! At the pinned point a2=3 equals neither fa0=1 nor fa1=2, so the universal is
//! false ⇒ UNSAT (z3 and cvc5 agree).
//!
//! Root cause of the former wrong `sat`: the UF-completion SAT certificate
//! (`quantifiers_supported_by_uf_completion`) materialized the pointwise UF
//! definitions and granted `sat`; its MBQI validator
//! (`disambiguate_cegqi_valid_via_mbqi`) only instantiated single-`Int`-binder
//! foralls over a value window, so it silently skipped this multi-`BitVec`-binder
//! shape and never found the refuting instance. Fixed by
//! `premise_forced_binder_refutation`: use the recovered premise only to obtain
//! concrete BitVector model values, substitute those exact literals into the
//! whole universal body, and independently refute that standalone ground
//! instance. The premise is never added to the proof problem. Default mode must
//! now DECIDE `unsat`; `--self-check` may stay `unknown` until the proof lane
//! certifies the reduction.

/// The fully-collapsing fixpoint check MUST be decided `unsat` in default mode.
#[test]
fn ufbv_fixpoint_premise_forced_is_unsat() {
    let smt = r#"
        (set-logic UFBV)
        (declare-fun fa0 ((_ BitVec 8) (_ BitVec 8) (_ BitVec 8)) (_ BitVec 8))
        (declare-fun fa1 ((_ BitVec 8) (_ BitVec 8) (_ BitVec 8)) (_ BitVec 8))
        (declare-fun fa2 ((_ BitVec 8) (_ BitVec 8) (_ BitVec 8)) (_ BitVec 8))
        (assert (forall ((a0 (_ BitVec 8)) (a1 (_ BitVec 8)) (a2 (_ BitVec 8)))
          (=> (and (= a0 #x01) (= a1 (bvadd a0 #x01)) (= a2 (bvadd a1 #x01)))
              (and (= (fa0 a2 a1 a0) #x01)
                   (= (fa1 a2 a1 a0) (bvadd (fa0 a2 a1 a0) #x01))
                   (= (fa2 a2 a1 a0) (bvadd (fa1 a2 a1 a0) #x01))
                   (or (= a2 (fa0 a2 a1 a0)) (= a2 (fa1 a2 a1 a0)))))))
        (check-sat)
    "#;
    let results = crate::common::solve_vec(smt);
    assert!(
        results.iter().any(|r| r == "unsat"),
        "quantified UFBV fixpoint check is UNSAT (z3, cvc5 agree; the universal \
         is violated at the premise-pinned point a2=3 ≠ fa0=1, fa1=2) — AY must \
         derive it via premise-forced refutation, not answer a wrong `sat`; \
         got {results:?}"
    );
}

/// SOUNDNESS guard: the SAME shape made GENUINELY SAT (the fixpoint disjunction
/// now includes the reached value, `(= a2 (fa2 …))` with a2=fa2=3) must NEVER be
/// refuted — the premise-forced refutation must not manufacture a wrong `unsat`.
#[test]
fn ufbv_fixpoint_satisfiable_variant_is_never_unsat() {
    let smt = r#"
        (set-logic UFBV)
        (declare-fun fa0 ((_ BitVec 8) (_ BitVec 8) (_ BitVec 8)) (_ BitVec 8))
        (declare-fun fa1 ((_ BitVec 8) (_ BitVec 8) (_ BitVec 8)) (_ BitVec 8))
        (declare-fun fa2 ((_ BitVec 8) (_ BitVec 8) (_ BitVec 8)) (_ BitVec 8))
        (assert (forall ((a0 (_ BitVec 8)) (a1 (_ BitVec 8)) (a2 (_ BitVec 8)))
          (=> (and (= a0 #x01) (= a1 (bvadd a0 #x01)) (= a2 (bvadd a1 #x01)))
              (and (= (fa0 a2 a1 a0) #x01)
                   (= (fa1 a2 a1 a0) (bvadd (fa0 a2 a1 a0) #x01))
                   (= (fa2 a2 a1 a0) (bvadd (fa1 a2 a1 a0) #x01))
                   (or (= a2 (fa0 a2 a1 a0)) (= a2 (fa2 a2 a1 a0)))))))
        (check-sat)
    "#;
    let results = crate::common::solve_vec(smt);
    assert!(
        !results.iter().any(|r| r == "unsat"),
        "this fixpoint check IS satisfiable (a2=3 = fa2=3 witnesses the \
         disjunction) — the premise-forced refutation must never manufacture a \
         wrong `unsat`; got {results:?}"
    );
}

/// SOUNDNESS guard: an uninterpreted function whose user-visible name merely
/// starts with `bv` is not a BitVector theory operator.  The ground assertions
/// make `bvshadow` constantly zero over the complete one-bit domain, so the
/// universal's premise is always false and the formula is satisfiable.
///
/// A premise-refutation classifier that trusts the `bv*` spelling instead of
/// declaration identity can incorrectly treat `(bvshadow x)` as interpreted,
/// assert the otherwise-vacuous premise at a fresh constant, and manufacture
/// `unsat`.
#[test]
fn user_declared_bv_prefix_in_premise_is_never_refuted() {
    let smt = r#"
        (set-logic UFBV)
        (declare-fun bvshadow ((_ BitVec 1)) (_ BitVec 1))
        (assert (= (bvshadow #b0) #b0))
        (assert (= (bvshadow #b1) #b0))
        (assert (forall ((x (_ BitVec 1)))
          (=> (= (bvshadow x) #b1) false)))
        (check-sat)
    "#;
    let results = crate::common::solve_vec(smt);
    assert!(
        !results.iter().any(|r| r == "unsat"),
        "the exhaustive ground table makes the universal vacuously true; a \
         user-declared `bvshadow` must not be classified as an interpreted BV \
         operator by spelling alone; got {results:?}"
    );
}

/// Stronger declaration-identity adversary: the body also carries a genuine UF
/// conclusion, ensuring the UF-completion validation path examines the
/// universal.  `bvtrap` is false at every value of the complete one-bit domain,
/// so this formula is satisfiable.
#[test]
fn user_declared_bv_prefix_with_uf_conclusion_is_never_refuted() {
    let smt = r#"
        (set-logic UFBV)
        (declare-fun bvtrap ((_ BitVec 1)) Bool)
        (declare-fun p ((_ BitVec 1)) Bool)
        (assert (not (bvtrap #b0)))
        (assert (not (bvtrap #b1)))
        (assert (forall ((x (_ BitVec 1)))
          (=> (bvtrap x) (p x))))
        (check-sat)
    "#;
    let results = crate::common::solve_vec(smt);
    assert!(
        !results.iter().any(|r| r == "unsat"),
        "`bvtrap` is a user UF that is false on the complete one-bit domain, \
         making the universal vacuously true; got {results:?}"
    );
}

/// SOUNDNESS guard: integer division by zero has a fixed-but-arbitrary value in
/// each SMT model.  The ground assertion chooses `(div 0 0) != 0`, making the
/// universal premise false at its only pinned point and the whole formula SAT.
/// An isolated premise solve may choose the different legal value zero, but
/// that model cannot be mixed with the ground model to manufacture UNSAT.
#[test]
fn underspecified_division_in_premise_is_never_refuted() {
    let smt = r#"
        (set-logic UFNIA)
        (declare-fun p (Int) Bool)
        (assert (distinct (div 0 0) 0))
        (assert (forall ((x Int))
          (=> (and (= x 0) (= (div x 0) 0)) (p x))))
        (check-sat)
    "#;
    let results = crate::common::solve_vec(smt);
    assert!(
        !results.iter().any(|r| r == "unsat"),
        "div-by-zero is underspecified and the asserted interpretation makes \
         the universal vacuous; got {results:?}"
    );
}

/// SOUNDNESS guard: isolated premise satisfiability over an uninterpreted sort
/// may choose a larger carrier than the original model.  Here a singleton
/// carrier satisfies both universals because every `distinct x y` premise is
/// false.  A premise probe must not borrow a two-element carrier and combine it
/// with the singleton-only outer problem.
#[test]
fn model_varying_binder_carrier_is_never_refuted() {
    let smt = r#"
        (set-logic UF)
        (declare-sort U 0)
        (declare-const a U)
        (declare-fun p (U U) Bool)
        (assert (forall ((z U)) (= z a)))
        (assert (forall ((x U) (y U))
          (=> (distinct x y) (and (p x y) (not (p x y))))))
        (check-sat)
    "#;
    let results = crate::common::solve_vec(smt);
    assert!(
        !results.iter().any(|r| r == "unsat"),
        "a singleton U is a model, so an isolated premise probe must not assume \
         a larger uninterpreted carrier; got {results:?}"
    );
}

/// SOUNDNESS guard: a universal below a disjunction is not entailed by the
/// problem.  Choosing `g = true` satisfies the assertion regardless of the
/// deliberately contradictory universal branch.
#[test]
fn nonconjunctive_forall_is_never_refuted() {
    let smt = r#"
        (set-logic UFBV)
        (declare-const g Bool)
        (declare-fun p ((_ BitVec 1)) Bool)
        (assert (or g
          (forall ((x (_ BitVec 1)))
            (=> (= x x) (and (p x) (not (p x)))))))
        (check-sat)
    "#;
    let results = crate::common::solve_vec(smt);
    assert!(
        !results.iter().any(|r| r == "unsat"),
        "g=true satisfies the disjunction; a nested forall is not a top-level \
         consequence and its instance cannot justify UNSAT; got {results:?}"
    );
}

/// Exercise the De Morgan candidate-extraction arm explicitly. `bvtrap` is a
/// user UF, not an interpreted BV operator, and is false over the complete
/// one-bit domain. The disjunction is therefore true for every binder value.
#[test]
fn de_morgan_user_bv_prefix_candidate_is_never_refuted() {
    let smt = r#"
        (set-logic UFBV)
        (declare-fun bvtrap ((_ BitVec 1)) Bool)
        (declare-fun p ((_ BitVec 1)) Bool)
        (assert (not (bvtrap #b0)))
        (assert (not (bvtrap #b1)))
        (assert (forall ((x (_ BitVec 1)))
          (or (not (bvtrap x)) (p x))))
        (check-sat)
    "#;
    let results = crate::common::solve_vec(smt);
    assert!(
        !results.iter().any(|r| r == "unsat"),
        "the De Morgan partition is candidate synthesis only; a user `bv*` UF \
         cannot justify UNSAT; got {results:?}"
    );
}

/// Declarations shared by the repeated-check scripts below.
const FIXPOINT_DECLS: &str = "
(declare-fun fa0 ((_ BitVec 8) (_ BitVec 8) (_ BitVec 8)) (_ BitVec 8))
(declare-fun fa1 ((_ BitVec 8) (_ BitVec 8) (_ BitVec 8)) (_ BitVec 8))
(declare-fun fa2 ((_ BitVec 8) (_ BitVec 8) (_ BitVec 8)) (_ BitVec 8))";

/// The satisfiable variant's body over the binders `a0 a1 a2` (z3 4.12.5:
/// sat). Its premise holds only at `(a2, a1, a0) = (#x03, #x02, #x01)`, where
/// it needs `fa0`, `fa1`, `fa2` to be `#x01`, `#x02`, `#x03`.
const PINNED_SAT_BODY: &str = "
(=> (and (= a0 #x01) (= a1 (bvadd a0 #x01)) (= a2 (bvadd a1 #x01)))
    (and (= (fa0 a2 a1 a0) #x01)
         (= (fa1 a2 a1 a0) (bvadd (fa0 a2 a1 a0) #x01))
         (= (fa2 a2 a1 a0) (bvadd (fa1 a2 a1 a0) #x01))
         (or (= a2 (fa0 a2 a1 a0)) (= a2 (fa2 a2 a1 a0)))))";

/// `fa0`, `fa1`, `fa2` at [`PINNED_SAT_BODY`]'s only binding point.
const BINDING_VALUES: &str =
    "(get-value ((fa0 #x03 #x02 #x01) (fa1 #x03 #x02 #x01) (fa2 #x03 #x02 #x01)))";

/// The ways a caller reaches `check-sat`, as `(name, authored, self_check)`:
/// the generic adapter (`execute_all`) or the caller-authored CLI boundary
/// (`execute_authored`), each with and without `--self-check`.
const POSTURES: [(&str, bool, bool); 4] = [
    ("default", false, false),
    ("self-check", false, true),
    ("authored", true, false),
    ("authored self-check", true, true),
];

/// `(check-sat) (get-model)` twice on `forall a0 a1 a2. body`, then `tail`.
fn repeated_check_script(body: &str, tail: &str) -> String {
    format!(
        "(set-logic UFBV)\n(set-option :produce-models true)\n{FIXPOINT_DECLS}\n\
         (assert (forall ((a0 (_ BitVec 8)) (a1 (_ BitVec 8)) (a2 (_ BitVec 8))) {body}))\n\
         (check-sat)\n(get-model)\n(check-sat)\n(get-model)\n{tail}\n"
    )
}

/// The output of `smt` in one posture, plus the quantified SAT-evidence label
/// (`model_check_gate.quantified`) the last `check-sat` recorded.
fn solve_in_posture(smt: &str, authored: bool, self_check: bool) -> (Vec<String>, Option<String>) {
    let commands = ay_frontend::parse(smt).unwrap_or_else(|err| panic!("parse failed: {err}"));
    let mut exec = ay_dpll::Executor::new();
    exec.set_self_check(self_check);
    let output = if authored {
        let mut lines = Vec::new();
        for command in &commands {
            lines.extend(
                exec.execute_authored(command)
                    .unwrap_or_else(|err| panic!("execution failed: {err}")),
            );
        }
        lines
    } else {
        exec.execute_all(&commands)
            .unwrap_or_else(|err| panic!("execution failed: {err}"))
    };
    let label = exec
        .statistics()
        .get_string("model_check_gate.quantified")
        .map(str::to_owned);
    (output, label)
}

/// z3's first answer line, or `None` after a visible skip when no oracle exists.
fn z3_verdict(smt: &str) -> Option<String> {
    if !crate::common::check_z3_or_skip() {
        return None;
    }
    let output = crate::common::solve_with_z3(smt)
        .unwrap_or_else(|err| panic!("z3 failed on the replay: {err}\n{smt}"));
    Some(output.lines().next().unwrap_or_default().trim().to_string())
}

/// Independently, under the model `defs`: z3 must accept the universal over
/// `body` and refute its negated body at fresh binder constants.
fn assert_z3_validates(defs: &str, body: &str) {
    let replay = format!(
        "(set-logic UFBV)\n{defs}\n(assert (forall ((a0 (_ BitVec 8)) (a1 (_ BitVec 8)) \
         (a2 (_ BitVec 8))) {body}))\n(check-sat)\n"
    );
    if let Some(verdict) = z3_verdict(&replay) {
        assert_eq!(verdict, "sat", "z3 rejects the model:\n{replay}");
    }
    let negation = format!(
        "(set-logic UFBV)\n{defs}\n(declare-const a0 (_ BitVec 8))\n\
         (declare-const a1 (_ BitVec 8))\n(declare-const a2 (_ BitVec 8))\n\
         (assert (not {body}))\n(check-sat)\n"
    );
    if let Some(verdict) = z3_verdict(&negation) {
        assert_eq!(
            verdict, "unsat",
            "a binder point falsifies the model:\n{negation}"
        );
    }
}

/// PIN REFRESH, tightening ad4d58fcc (which accepted `unknown` or `sat`).
/// This pinned `unknown` "until a total model certificate exists" (80b9777a4).
/// The generic quantified model check (ecc040bff, `finite_model_mbqi/generic.rs`)
/// is that certificate: every function is a table plus an else value, the
/// universal is decided true by a checked refutation of its Skolemized
/// negation under that interpretation, and the published model is the staged
/// one bound to the grant. So in every posture the pin demands two `sat`
/// answers publishing one model, recorded on checked quantified evidence
/// (never `deferred-discharged-trust-*`), defining every function, with no
/// private qpf symbol, whose values at the only binding point satisfy the
/// body; and z3 must accept each published model on replay and refute the
/// negated body under it.
#[test]
fn repeated_sat_checks_publish_a_replay_checked_model_without_qpf_symbols() {
    let script = repeated_check_script(PINNED_SAT_BODY, BINDING_VALUES);
    let mut models: Vec<String> = Vec::new();
    for (posture, authored, self_check) in POSTURES {
        let (results, evidence) = solve_in_posture(&script, authored, self_check);
        assert_eq!(results.len(), 5, "{posture}: {results:?}");
        assert_eq!(
            [results[0].as_str(), results[2].as_str()],
            ["sat", "sat"],
            "{posture}: the certified total model decides both checks; got {results:?}"
        );
        assert!(
            evidence.as_deref().is_some_and(
                |label| label == "confirmed" || label.starts_with("deferred-certified-")
            ),
            "{posture}: the sat must rest on checked quantified evidence, not a trust \
             discharge; got {evidence:?}"
        );
        assert_eq!(
            results[1], results[3],
            "{posture}: repeated checks must publish one model"
        );
        assert!(
            results.iter().all(|r| !r.contains("__ay_qpf")),
            "{posture}: disposable premise symbols must never escape into a visible model; \
             got {results:?}"
        );
        // The premise holds only at (a2, a1, a0) = (#x03, #x02, #x01), so these
        // three values decide the universal: a complete check that needs no z3.
        assert_eq!(
            results[4],
            "(((fa0 #x03 #x02 #x01) #x01) ((fa1 #x03 #x02 #x01) #x02) ((fa2 #x03 #x02 #x01) #x03))",
            "{posture}: the published model must satisfy the universal at its only binding"
        );
        let defs = results[1]
            .trim()
            .strip_prefix("(model")
            .and_then(|rest| rest.strip_suffix(')'))
            .unwrap_or_else(|| panic!("{posture}: get-model must print a model: {results:?}"));
        for name in ["fa0", "fa1", "fa2"] {
            assert!(
                defs.contains(&format!("(define-fun {name} ")),
                "{posture}: the model must define {name} totally: {defs}"
            );
        }
        if !models.iter().any(|seen| seen == defs) {
            models.push(defs.to_owned());
        }
    }
    for defs in &models {
        assert_z3_validates(defs, PINNED_SAT_BODY);
    }
}

/// Fail-closed twin the model check cannot cover. With `a0` unpinned the
/// formula is still satisfiable (`fa0 = x2`, `fa1 = x2+1`, `fa2 = x2+2`; z3
/// checks that witness below), but `fa0` must take 256 different values, which
/// no table plus else value reachable within the refinement rounds
/// (`MAX_FINITE_MODEL_ROUNDS`) represents. Without a checked total model every
/// posture stays `unknown` with the model unavailable. This is also the
/// negative twin of the acceptance: a model check that skipped its checked
/// refutation would publish a wrong constant model here. If a checked lane
/// later constructs this model, flip the pin to the replay-checked form above;
/// never to a bare `sat`.
#[test]
fn unrepresentable_fixpoint_model_fails_closed_in_every_posture() {
    let body = "
(=> (and (= a1 (bvadd a0 #x01)) (= a2 (bvadd a1 #x01)))
    (and (= (fa0 a2 a1 a0) a0)
         (= (fa1 a2 a1 a0) (bvadd (fa0 a2 a1 a0) #x01))
         (= (fa2 a2 a1 a0) (bvadd (fa1 a2 a1 a0) #x01))
         (or (= a2 (fa0 a2 a1 a0)) (= a2 (fa2 a2 a1 a0)))))";
    let script = repeated_check_script(body, "");
    for (posture, authored, self_check) in POSTURES {
        let (results, _) = solve_in_posture(&script, authored, self_check);
        assert_eq!(
            results,
            [
                "unknown",
                "(error \"model is not available\")",
                "unknown",
                "(error \"model is not available\")",
            ],
            "{posture}: a satisfiable variant with no checked total model must fail closed"
        );
    }
    let witness = "(define-fun fa0 ((x0 (_ BitVec 8)) (x1 (_ BitVec 8)) (x2 (_ BitVec 8))) \
                   (_ BitVec 8) x2)\n\
                   (define-fun fa1 ((x0 (_ BitVec 8)) (x1 (_ BitVec 8)) (x2 (_ BitVec 8))) \
                   (_ BitVec 8) (bvadd x2 #x01))\n\
                   (define-fun fa2 ((x0 (_ BitVec 8)) (x1 (_ BitVec 8)) (x2 (_ BitVec 8))) \
                   (_ BitVec 8) (bvadd x2 #x02))";
    assert_z3_validates(witness, body);
}

/// Proof/self-check mode must never emit a satisfiable answer for the false
/// fixpoint universal. It may remain `unknown` until this reduction has an
/// authored `forall_inst` proof, or emit `unsat` only through the strict
/// self-certification funnel.
#[test]
fn fixpoint_selfcheck_never_emits_sat() {
    let smt = r#"
        (set-logic UFBV)
        (declare-fun fa0 ((_ BitVec 8) (_ BitVec 8) (_ BitVec 8)) (_ BitVec 8))
        (declare-fun fa1 ((_ BitVec 8) (_ BitVec 8) (_ BitVec 8)) (_ BitVec 8))
        (declare-fun fa2 ((_ BitVec 8) (_ BitVec 8) (_ BitVec 8)) (_ BitVec 8))
        (assert (forall ((a0 (_ BitVec 8)) (a1 (_ BitVec 8)) (a2 (_ BitVec 8)))
          (=> (and (= a0 #x01) (= a1 (bvadd a0 #x01)) (= a2 (bvadd a1 #x01)))
              (and (= (fa0 a2 a1 a0) #x01)
                   (= (fa1 a2 a1 a0) (bvadd (fa0 a2 a1 a0) #x01))
                   (= (fa2 a2 a1 a0) (bvadd (fa1 a2 a1 a0) #x01))
                   (or (= a2 (fa0 a2 a1 a0)) (= a2 (fa1 a2 a1 a0)))))))
        (check-sat)
    "#;
    let results = crate::common::solve_selfcheck_vec(smt);
    assert!(
        !results.iter().any(|r| r == "sat"),
        "self-check may certify UNSAT or fail closed to unknown, never claim SAT \
         for the false universal; got {results:?}"
    );
}
