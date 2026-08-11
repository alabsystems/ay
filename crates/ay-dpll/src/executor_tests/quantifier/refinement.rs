// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

/// Phase B1c (#3325): E-matching refinement with theory-provided model.
///
/// This test exercises the Phase B1c refinement loop: after the theory solver
/// returns SAT, E-matching runs again with the fresh EUF model. The model's
/// congruence classes may enable trigger matches that weren't available during
/// preprocessing (which used the model from the previous check-sat, or None).
///
/// The formula:
///   (forall x. P(x) => Q(x))   ; trigger: P(x)
///   P(a)                         ; ground term for trigger matching
///   (not (Q a))                  ; contradicts P(a) => Q(a)
///
/// E-matching in preprocessing matches P(x) against P(a), producing P(a)=>Q(a).
/// Combined with (not (Q a)), this is UNSAT.
///
/// This test verifies the refinement infrastructure doesn't break existing UNSAT.
/// A deeper B1c test would require congruence-derived triggers, which need
/// multi-check-sat to have a prior EUF model.
#[test]
fn test_ematching_refinement_basic_unsat() {
    let input = r#"
        (set-logic UF)
        (declare-sort U 0)
        (declare-fun P (U) Bool)
        (declare-fun Q (U) Bool)
        (declare-fun a () U)
        (assert (forall ((x U)) (! (=> (P x) (Q x)) :pattern ((P x)))))
        (assert (P a))
        (assert (not (Q a)))
        (check-sat)
    "#;

    let commands = parse(input).expect("valid SMT-LIB input");
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).expect("execution succeeds");

    assert_eq!(outputs, vec!["unsat"]);
}
/// Phase B1c (#3325): Multi-check-sat with refinement.
///
/// Exercises Phase B1c across two check-sat calls. The first call establishes
/// an EUF model. The second call's preprocessing uses that model (Phase B1b),
/// and any SAT result triggers refinement (Phase B1c) with the fresh model.
///
/// First check-sat: P(a) is SAT (no quantifiers).
/// Second check-sat: adds forall x. P(x) => Q(x), with P(a) already true.
/// E-matching matches P(x) against P(a), producing P(a) => Q(a).
/// With (not (Q a)), this is UNSAT.
#[test]
fn test_ematching_refinement_multi_checksat() {
    let input = r#"
        (set-logic UF)
        (declare-sort U 0)
        (declare-fun P (U) Bool)
        (declare-fun Q (U) Bool)
        (declare-fun a () U)
        (assert (P a))
        (check-sat)
        (assert (forall ((x U)) (! (=> (P x) (Q x)) :pattern ((P x)))))
        (assert (not (Q a)))
        (check-sat)
    "#;

    let commands = parse(input).expect("valid SMT-LIB input");
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).expect("execution succeeds");

    assert_eq!(outputs[0], "sat"); // First check-sat: just P(a)
    assert_eq!(outputs[1], "unsat"); // Second: P(a), forall P=>Q, not Q(a)
}
/// Phase B1c (#3325): Congruence-derived trigger matching.
///
/// This tests the core B1c capability: trigger matching that requires functional
/// congruence information from the EUF solver, unavailable from explicit equality
/// assertions alone.
///
/// Formula:
///   (forall x. not (P x x))           trigger: (P x x)
///   (P (f a) (f b))                   ground fact
///   (= a b)                           explicit equality
///
/// Preprocessing E-matching:
///   - `from_assertions` sees `(= a b)` → knows a ≡ b
///   - Does NOT derive f(a) ≡ f(b) (requires congruence closure on f)
///   - Trigger `(P x x)` against `P(f(a), f(b))`:
///     x = f(a) from arg1, x = f(b) from arg2, but f(a) ≢ f(b) → NO MATCH
///   - Ground formula (without quantifier) is SAT
///
/// Phase B1c (after theory solve):
///   - EUF solver processes `(= a b)` → congruence closure: f(a) = f(b)
///   - Fresh EUF model: f(a) and f(b) in same congruence class
///   - E-matching re-runs: `(P x x)` matches `P(f(a), f(b))` with x=f(a)
///   - Instantiation: `(not (P (f a) (f a)))`
///   - Re-solve: `P(f(a), f(b)) ∧ f(a)=f(b) ∧ ¬P(f(a), f(a))` → UNSAT
#[test]
fn test_ematching_congruence_derived_trigger_match() {
    let input = r#"
        (set-logic UF)
        (declare-sort U 0)
        (declare-fun f (U) U)
        (declare-fun P (U U) Bool)
        (declare-fun a () U)
        (declare-fun b () U)
        (assert (forall ((x U)) (! (not (P x x)) :pattern ((P x x)))))
        (assert (P (f a) (f b)))
        (assert (= a b))
        (check-sat)
    "#;

    let commands = parse(input).expect("valid SMT-LIB input");
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).expect("execution succeeds");

    // With B1c congruence-derived matching: UNSAT
    // Without B1c: would be Unknown (trigger requires f(a) ≡ f(b) from congruence closure)
    assert!(
        outputs == vec!["unsat"],
        "Expected UNSAT from congruence-derived trigger match, got: {outputs:?}",
    );
}
/// Phase B1c (#3325): Congruence-derived matching via multi-check-sat.
///
/// First check-sat establishes an EUF model. Second check-sat uses B1b
/// (preprocessing with prior model) and B1c (refinement with fresh model)
/// together.
///
/// First check-sat: `(= a b), P(f(a), f(b))` → SAT, EUF model has f(a)≡f(b)
/// Second check-sat: adds `forall x. not (P x x)` with trigger `(P x x)`.
///   B1b: preprocessing uses prior EUF model → f(a)≡f(b) already known →
///   match found during preprocessing → UNSAT.
#[test]
fn test_ematching_congruence_multi_checksat() {
    let input = r#"
        (set-logic UF)
        (declare-sort U 0)
        (declare-fun f (U) U)
        (declare-fun P (U U) Bool)
        (declare-fun a () U)
        (declare-fun b () U)
        (assert (= a b))
        (assert (P (f a) (f b)))
        (check-sat)
        (assert (forall ((x U)) (! (not (P x x)) :pattern ((P x x)))))
        (check-sat)
    "#;

    let commands = parse(input).expect("valid SMT-LIB input");
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).expect("execution succeeds");

    assert_eq!(outputs[0], "sat"); // Ground-only: consistent
                                   // Second check-sat: B1b uses prior model (f(a)≡f(b)) for preprocessing match
    assert!(
        outputs[1] == "unsat",
        "Expected UNSAT from congruence-derived match (B1b or B1c), got: {:?}",
        outputs[1],
    );
}
/// #5927: DPLL(T)-interleaved E-matching — congruence-dependent multi-step chain.
///
/// This tests the interleaved E-matching refinement loop. The pattern matches
/// require congruence equalities that are only available after the theory solver
/// runs:
///
/// Formula:
///   (forall x. (=> (P x) (Q (f x))))   trigger: (P x)
///   (forall y. (=> (Q y) (R y)))        trigger: (Q y)
///   (P a)
///   (= (f a) b)
///   (not (R b))
///
/// Step 1 (preprocessing E-matching):
///   - Match P(x) against P(a) → Q(f(a))
///   - Q(y) trigger needs Q(something), but Q(f(a)) just produced
///   - Multi-round preprocessing: match Q(y) against Q(f(a)) → R(f(a))
///
/// Step 2 (initial solve): ground problem includes Q(f(a)), R(f(a)), (= (f a) b).
///   - If congruence closure derives f(a) = b, then R(f(a)) and R(b) are the same.
///   - With (not (R b)), this should be UNSAT.
///
/// The interleaved loop ensures that after the theory solver establishes
/// congruence equalities, E-matching can discover new matches.
#[test]
fn test_interleaved_ematching_congruence_chain_5927() {
    let input = r#"
        (set-logic UF)
        (declare-sort U 0)
        (declare-fun f (U) U)
        (declare-fun P (U) Bool)
        (declare-fun Q (U) Bool)
        (declare-fun R (U) Bool)
        (declare-fun a () U)
        (declare-fun b () U)
        (assert (forall ((x U)) (! (=> (P x) (Q (f x))) :pattern ((P x)))))
        (assert (forall ((y U)) (! (=> (Q y) (R y)) :pattern ((Q y)))))
        (assert (P a))
        (assert (= (f a) b))
        (assert (not (R b)))
        (check-sat)
    "#;

    let commands = parse(input).expect("valid SMT-LIB input");
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).expect("execution succeeds");

    // Without interleaved E-matching: might return Unknown if congruence
    // equality f(a)=b is needed to connect R(f(a)) to (not (R b)).
    // With interleaved E-matching: UNSAT (congruence closure + E-matching chain).
    assert_eq!(
        outputs,
        vec!["unsat"],
        "Interleaved E-matching should derive UNSAT via congruence chain"
    );
}

/// RED suite S2 closure (2026-07-08): `forall x. x*x >= 0` is a VALID sentence,
/// so the assertion set is SAT. The infeasible-linear-eq probe used to compute a
/// fake "coefficient" `d[x:=1] - d[x:=0] = 1` for the QUADRATIC occurrence and
/// collapsed the whole forall to `false` — a spurious refutation (wrong-UNSAT,
/// the ex-falso direction). The probe now demands AFFINE occurrences.
#[test]
fn test_forall_square_nonneg_is_sat_s2() {
    let input = r#"
        (set-logic NIA)
        (assert (forall ((x Int)) (>= (* x x) 0)))
        (check-sat)
    "#;
    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();
    assert_ne!(outputs, vec!["unsat"], "valid forall must never be refuted");
    assert_eq!(outputs, vec!["sat"]);
}

/// Same disease, `abs`: `forall x. abs(x) >= 0` is valid (SAT), but the probe's
/// difference on the clamped term is 1 — a fake coefficient.
#[test]
fn test_forall_abs_nonneg_is_sat() {
    let input = r#"
        (set-logic NIA)
        (assert (forall ((x Int)) (>= (abs x) 0)))
        (check-sat)
    "#;
    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();
    assert_ne!(outputs, vec!["unsat"], "valid forall must never be refuted");
    assert_eq!(outputs, vec!["sat"]);
}

/// Same disease, `mod`: SMT-LIB `mod` is always non-negative, so
/// `forall x. (mod x 3) >= 0` is valid (SAT); the bounded term has a fake
/// difference-coefficient of 1.
#[test]
fn test_forall_mod_nonneg_is_sat() {
    let input = r#"
        (set-logic NIA)
        (assert (forall ((x Int)) (>= (mod x 3) 0)))
        (check-sat)
    "#;
    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();
    assert_ne!(outputs, vec!["unsat"], "valid forall must never be refuted");
    assert_eq!(outputs, vec!["sat"]);
}

/// CONTROL (the probe's genuine firing must survive the affinity fix): a truly
/// false linear universal — `4x = 7` has no integer solution for ANY x… rather,
/// it FAILS at some x (the coefficient argument applies: 4·x − 7 is affine,
/// nonzero coefficient, crosses any value) — so the assertion set is UNSAT.
#[test]
fn test_forall_infeasible_linear_eq_still_unsat() {
    let input = r#"
        (set-logic LIA)
        (assert (forall ((x Int)) (= (* 4 x) 7)))
        (check-sat)
    "#;
    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();
    assert_eq!(outputs, vec!["unsat"]);
}

/// RED suite S3 closure (2026-07-08) → DECIDED UNSAT (#quantified-ce-lemma):
/// `forall x. exists y. y*y = x` is FALSE (x = 2 is not a perfect square), so
/// the assertion set is UNSAT — matching z3. The CEGQI unsat-disambiguation
/// used to flip "ground-minus-CE-lemma is Sat" straight to SAT; that wrong-sat
/// stays closed (the flip demands the CE obligation itself be refuted, which
/// for this alternation it cannot be: `forall y. y*y != e` is satisfiable — S3
/// doubles as the SAT-leg negative control). The UNSAT verdict comes from the
/// decider's ground-witness leg: the conjunctive-position universal
/// `forall x. sk(x)*sk(x) = x` is instantiated at the residue-guided witness
/// x := 2 and the ISOLATED instance `(= (* (sk 2) (sk 2)) 2)` is ground-NIA
/// UNSAT, refuting the whole problem (universal instantiation + skolemization
/// preserving satisfiability).
#[test]
fn test_forall_exists_perfect_square_unsat_s3() {
    let input = r#"
        (set-logic NIA)
        (assert (forall ((x Int)) (exists ((y Int)) (= (* y y) x))))
        (check-sat)
    "#;
    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();
    assert_ne!(
        outputs,
        vec!["sat"],
        "a false ∀∃ sentence must never answer sat"
    );
    assert_eq!(
        outputs,
        vec!["unsat"],
        "the ∀∃ perfect-square alternation is decidably unsat"
    );
}

/// End-to-end fixture pin via `Executor`: the committed NIA script must decide
/// `unsat`. This guards the parser, quantifier loop, CEGQI
/// unsat-disambiguation, and quantified-CE decider against drift between the
/// in-crate formula above and the standalone regression input.
#[test]
fn test_s3_fixture_file_end_to_end_unsat() {
    let input = include_str!(concat!(
        env!("CARGO_MANIFEST_DIR"),
        "/tests/fixtures/quantifier/forall_exists_perfect_square_unsat.smt2"
    ));
    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();
    assert_ne!(outputs, vec!["sat"], "S3 fixture must never answer sat");
    assert_eq!(
        outputs,
        vec!["unsat"],
        "S3 fixture is decidably unsat (matching z3)"
    );
}

/// The VALID alternation → DECIDED SAT (#quantified-ce-lemma):
/// `forall x. exists y. y > x` is TRUE, so the assertion set is SAT — matching
/// z3. The stored CE lemma `¬(sk(e) > e)` keeps the Skolem application free
/// and is always satisfiable, so the legacy ground refutation fails; the
/// decider's SAT leg rebuilds the DE-SKOLEMIZED obligation
/// `forall y. ¬(y > e)` and refutes it at the isolated instance y := e + 1
/// (`e+1 <= e` is ground-UNSAT), certifying the universal VALID; with the
/// ground remainder satisfiable the problem is SAT.
#[test]
fn test_forall_exists_greater_sat() {
    let input = r#"
        (set-logic LIA)
        (assert (forall ((x Int)) (exists ((y Int)) (> y x))))
        (check-sat)
    "#;
    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();
    assert_ne!(
        outputs,
        vec!["unsat"],
        "a valid ∀∃ sentence must never answer unsat"
    );
    assert_eq!(
        outputs,
        vec!["sat"],
        "the valid ∀∃ alternation is decidably sat"
    );
}

/// NEGATIVE CONTROL for the SAT leg (doctrine: every new verdict needs a false
/// variant): `forall x. exists y. (y <= x and y >= x+1)` is FALSE (no witness
/// exists for ANY x). Its de-Skolemized obligation
/// `forall y. ¬(y <= e ∧ y >= e+1)` is VALID — every instance of it is
/// satisfiable, so the SAT leg can never fire and this must NEVER answer sat.
/// (It IS decidable unsat: the standalone instance
/// `sk(c) <= c ∧ sk(c) >= c+1` is ground-UNSAT at any witness c.)
#[test]
fn test_forall_exists_empty_witness_never_sat() {
    let input = r#"
        (set-logic LIA)
        (assert (forall ((x Int)) (exists ((y Int)) (and (<= y x) (>= y (+ x 1))))))
        (check-sat)
    "#;
    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();
    assert_ne!(
        outputs,
        vec!["sat"],
        "a false ∀∃ sentence must never answer sat"
    );
    assert_eq!(outputs, vec!["unsat"]);
}

/// FUZZ COUNTEREXAMPLE (alternation differential fuzz, seed 42, 2026-07-09):
/// `forall x. exists y. (y*y > -3 and y = x - 2)` is VALID (y := x-2 satisfies
/// both conjuncts — a square is always > -3), so this must answer sat, never
/// unsat. The quantified-CE-lemma SAT leg correctly certifies the universal
/// VALID, but the disambiguation cross-validation's Fourier-Motzkin projection
/// then WRONGLY refuted it: its `d[sk:=1] - d[sk:=0]` difference probe folded
/// the QUADRATIC occurrence in `sk² + 3 > 0` to a fake unit coefficient (the
/// S2 disease) and minted the hard bound `sk >= -2`, projecting a VALID
/// universal to the falsifiable `forall x. x >= 0`. All four probe sites
/// (exact single-Skolem FM, DNF FM, multi-Skolem relaxation,
/// equality-determined substitution) now demand AFFINE occurrences via
/// `var_under_nonarith` — exactly the S2 closure applied to the projectors.
#[test]
fn test_forall_exists_square_conjunct_affine_probe_sat() {
    let input = r#"
        (set-logic NIA)
        (assert (forall ((x Int)) (exists ((y Int)) (and (> (* y y) -3) (= y (+ x -2))))))
        (check-sat)
    "#;
    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();
    assert_ne!(
        outputs,
        vec!["unsat"],
        "a valid ∀∃ sentence must never answer unsat"
    );
    assert_eq!(outputs, vec!["sat"]);
}

/// NEGATIVE MUTANT for the raw-Unknown quantified-CE SAT completion above.
/// Changing `-3` to `3` makes the sentence FALSE: at `x = 2`, the equality
/// forces `y = 0`, contradicting `y*y > 3`.  The shape, NIA routing, affine
/// witness equality, and quantifier prefix are otherwise identical to the
/// positive fixture, so a route that treated the preceding CEGQI `Unknown` or
/// the synthesized term itself as authority would answer wrong-SAT here.  The
/// checked counterexample obligation remains satisfiable and must decline.
#[test]
fn test_forall_exists_square_conjunct_affine_probe_mutant_never_sat() {
    let input = r#"
        (set-logic NIA)
        (assert (forall ((x Int)) (exists ((y Int)) (and (> (* y y) 3) (= y (+ x -2))))))
        (check-sat)
    "#;
    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();
    assert_ne!(
        outputs,
        vec!["sat"],
        "the checked SAT completion must reject the falsifying threshold mutant"
    );
}

/// UNWITNESSABLE NIA control for the same routing site.  The square conjunct
/// keeps the temporary CE window in the nonlinear family, while `y <= x` and
/// `y >= x+1` make the existential body impossible for every `x`.  No
/// synthesized witness can turn a satisfiable negated obligation into theorem
/// authority; the public answer may be UNSAT or conservatively Unknown, never
/// SAT.
#[test]
fn test_forall_exists_square_conjunct_unwitnessable_never_sat() {
    let input = r#"
        (set-logic NIA)
        (assert (forall ((x Int)) (exists ((y Int))
            (and (> (* y y) -3) (<= y x) (>= y (+ x 1))))))
        (check-sat)
    "#;
    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();
    assert_ne!(
        outputs,
        vec!["sat"],
        "an unwitnessable existential must never pass the checked SAT completion"
    );
}

/// NEGATIVE CONTROL for the UNSAT leg: `forall x. exists y. y*y >= x` is VALID
/// (y := |x| works for every x), so it must NEVER answer unsat: every
/// standalone instance `sk(c)*sk(c) >= c` is satisfiable, so no ground-witness
/// candidate can verify. (The SAT leg decides it sat: the de-Skolemized
/// obligation `forall y. y*y < e` is refuted at the isolated instance y := e,
/// `e*e < e` being ground-NIA UNSAT. z3 times out on this fixture.)
#[test]
fn test_forall_exists_square_ge_never_unsat() {
    let input = r#"
        (set-logic NIA)
        (assert (forall ((x Int)) (exists ((y Int)) (>= (* y y) x))))
        (check-sat)
    "#;
    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();
    assert_ne!(
        outputs,
        vec!["unsat"],
        "a valid ∀∃ sentence must never answer unsat"
    );
    assert_eq!(outputs, vec!["sat"]);
}
