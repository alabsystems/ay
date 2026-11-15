// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! z3 binds a `:named` label when it reads it and stops a command at its
//! first error. A label's state matches z3's only when z3 surely reaches it,
//! every subterm before it accepted (`named_labels::z3_reach`). The scripts
//! include the z3-mode conformance review's repros; the CLI tests pin their
//! answers.

use super::*;

/// Each command's result and the label outcome read after it.
type Outcomes = Vec<(Result<()>, Option<LabelFailure>)>;

/// Process every command under `--z3-mode` (`z3`) or not.
fn run_with(z3: bool, input: &str) -> (Context, Outcomes) {
    let mut ctx = Context::new();
    ctx.set_z3_mode(z3);
    let results = parse(input)
        .unwrap()
        .iter()
        .map(|cmd| {
            let result = ctx.process_command(cmd).map(|_| ());
            (result, ctx.take_label_failure())
        })
        .collect();
    (ctx, results)
}

/// The outcome of the last command, in z3 mode and outside it.
fn last_outcomes(input: &str) -> [(bool, Option<LabelFailure>); 2] {
    [true, false].map(|z3| {
        let (_, results) = run_with(z3, input);
        let (result, failure) = results.last().unwrap();
        (result.is_ok(), *failure)
    })
}

const PRELUDE: &str = "(declare-datatypes ((P 0)) (((mk (fst Int)) (nothing))))\
     (declare-const p Bool)(declare-const q Bool)(declare-const x Int)\
     (declare-const r Real)(declare-const s String)(declare-const b (_ BitVec 8))\
     (declare-const arr (Array Int Int))";

/// Subterms this frontend rejects and z3 4.12.5 accepts (an arity it reads
/// as a chain, a Real where it coerces, a builtin this frontend lacks), in
/// skipped and taken positions. The label after one is bound by z3 and not
/// here, so a rejection diverges: it used to be read as z3's own error,
/// which left `a` free for a later definition (wrong unsat). Where this
/// frontend accepts the subterm, z3 mode cannot vouch for it, so the label
/// it binds may be one z3 does not.
#[test]
fn an_error_z3_may_not_raise_before_a_label_diverges() {
    for subterm in [
        "(> x)",
        "(str.++ s)",
        "(bvadd b)",
        "(div r 2)",
        "(select arr r)",
        "(bvumul_noovfl b b)",
        "(ite true true (> x))",
        "(ite false (= (str.++ s) s) true)",
        "(let ((d (div r 2))) true)",
        "(match (mk 1) (((mk v) true) (nothing (bvumul_noovfl b b))))",
        "(match nothing ((_ true) ((mk v) (> v))))",
    ] {
        let input = format!("{PRELUDE}(assert (or {subterm} (! p :named a)))");
        let [(z3_accepted, z3), (plain_accepted, plain)] = last_outcomes(&input);
        // z3 mode never vouches for these subterms, accepted or not.
        let z3_expected = if z3_accepted {
            LabelFailure::Unvouched
        } else {
            LabelFailure::Diverged
        };
        assert_eq!(z3, Some(z3_expected), "{subterm}");
        if !plain_accepted {
            assert_eq!(plain, Some(LabelFailure::Diverged), "{subterm}");
        }
    }
}

/// Constructs this frontend accepts outside z3 mode and some z3 rejects,
/// before a label: a quantifier with no bound variable and a pattern that is
/// a variable or a quantifier (every z3), a Bool beside an Int in `distinct`
/// or `ite` and an SMT-LIB 2.7 conversion (z3 4.12.5; z3 5 reads them), a
/// bit-vector operand of arithmetic and an operator no z3 knows (every z3).
/// z3 may drop the whole assertion there, which this frontend's dialect
/// keeps, so the outcome diverges in skipped and taken positions. z3 mode
/// rejects each of them, which diverges too.
#[test]
fn a_construct_z3_rejects_before_a_label_diverges() {
    for construct in [
        "(exists () p)",
        "(forall ((z Int)) (! p :pattern (z)))",
        "(forall ((z Int)) (! p :pattern ((forall ((y Int)) p))))",
        "(distinct p 1)",
        "(= (ite q x p) 1)",
        "(= (ubv_to_int b) 1)",
        "(= (sbv_to_int b) 1)",
        "(> b x)",
        "(= (min x 1) x)",
    ] {
        for position in [
            format!("(or true (ite false (and {construct} (! false :named a)) true))"),
            format!("(or true (ite true true (and {construct} (! false :named a))))"),
            format!("(or true (and {construct} (! false :named a)))"),
        ] {
            let input = format!("{PRELUDE}(assert {position})");
            let [(z3_accepted, z3), (plain_accepted, plain)] = last_outcomes(&input);
            assert!(!z3_accepted, "z3 mode: {position}");
            assert_eq!(z3, Some(LabelFailure::Diverged), "z3 mode: {position}");
            assert!(plain_accepted, "plain: {position}");
            assert_eq!(plain, Some(LabelFailure::Diverged), "plain: {position}");
        }
    }
}

/// A construct z3 versions read differently in a label-free skipped subterm
/// (checked in the shared scratch copy) still decides the labels after it.
#[test]
fn a_version_dependent_construct_in_a_label_free_skipped_subterm_diverges() {
    for skipped in ["(= p 1)", "(= (ubv_to_int b) 1)"] {
        let input = format!("{PRELUDE}(assert (and (ite true true {skipped}) (! q :named a)))");
        let [(_, z3), (plain_accepted, plain)] = last_outcomes(&input);
        assert_eq!(z3, Some(LabelFailure::Diverged), "{skipped}");
        assert!(plain_accepted, "{skipped}");
        assert_eq!(plain, Some(LabelFailure::Diverged), "{skipped}");
    }
}

/// The review's wrong sat: z3 may stop at the construct, before `a`, and
/// then bind `a` in the second assertion. Binding `a` here and rejecting the
/// second assertion as exact answered sat where z3 4.12.5 answers unsat. The
/// first assertion now diverges, which withholds every later answer in z3
/// mode.
#[test]
fn a_label_after_an_unvouched_construct_diverges_before_a_rejection() {
    for construct in ["(exists () p)", "(distinct p 1)", "(bvumul_noovfl b b)"] {
        let input = format!(
            "{PRELUDE}(assert (or true (ite true true (and {construct} (! true :named a)))))"
        );
        let (_, results) = run_with(true, &input);
        let (_, failure) = results.last().unwrap();
        assert_eq!(*failure, Some(LabelFailure::Diverged), "{construct}");
    }
}

/// z3 reaches a label after well-sorted core terms, so a rejection there
/// stays exact in z3 mode and keeps the labels before it.
#[test]
fn a_label_rejection_after_vouched_terms_stays_exact() {
    let input = format!(
        "{PRELUDE}(declare-const c Bool)(declare-fun f (Int) Int)\
         (assert (and (! p :named a) (ite true true (> (f x) (+ x 1))) \
         (let ((t (bvadd b #x01))) (bvult t b)) (= (select (store arr x 1) x) 1) \
         (forall ((k Int)) (! (> (f k) k) :pattern ((f k)) :qid q1)) (! q :named c)))"
    );
    let (ctx, results) = run_with(true, &input);
    let (result, failure) = results.last().unwrap();
    assert!(result.is_err());
    assert_eq!(*failure, Some(LabelFailure::Exact));
    assert!(ctx.fun_defs.contains_key("a"));
}

/// The one label Verus writes, on a prelude axiom over declared sorts,
/// binds with no divergence in z3 mode.
#[test]
fn the_verus_prelude_label_is_reached() {
    let input = "(declare-sort %%Function%% 0)(declare-sort Poly 0)(declare-sort Type 0)\
         (declare-sort Dcr 0)(declare-fun I (Int) Poly)(declare-fun CONST_INT (Int) Type)\
         (declare-const $ Dcr)(declare-fun array_new (Dcr Type Int %%Function%%) Poly)\
         (declare-fun array_index (Dcr Type Dcr Type %%Function%% Poly) Poly)\
         (declare-fun %%apply%%1 (%%Function%% Int) Poly)\
         (assert (! (forall ((Tdcr Dcr) (T Type) (N Int) (Fn %%Function%%) (i Int)) (! \
           (= (array_index Tdcr T $ (CONST_INT N) Fn (I i)) (%%apply%%1 Fn i)) \
           :pattern ((array_new Tdcr T N Fn) (%%apply%%1 Fn i)) \
           :qid prelude_array_index_trigger :skolemid skolem_prelude_array_index_trigger)) \
         :named prelude_axiom_array_index))";
    for z3 in [true, false] {
        let (ctx, results) = run_with(z3, input);
        assert!(
            results
                .iter()
                .all(|(result, failure)| result.is_ok() && failure.is_none()),
            "z3 mode {z3}: {results:?}"
        );
        assert!(ctx.fun_defs.contains_key("prelude_axiom_array_index"));
    }
}

/// z3 mode rejects what every z3 rejects; outside it the quantifier reads as
/// its body and the pattern is kept.
#[test]
fn z3_mode_rejects_empty_binders_and_variable_patterns() {
    for assertion in [
        "(assert (exists () p))",
        "(assert (forall () p))",
        "(assert (or false (and (exists () p) false)))",
        "(assert (forall ((z Int)) (! p :pattern (z))))",
        "(assert (forall ((z Int)) (! (> z 0) :pattern ((f z) z))))",
        "(assert (forall ((z Int)) (! p :pattern ((forall ((y Int)) p)))))",
    ] {
        let input = format!("{PRELUDE}(declare-fun f (Int) Int){assertion}");
        let [(z3_accepted, _), (plain_accepted, _)] = last_outcomes(&input);
        assert!(!z3_accepted, "{assertion}");
        assert!(plain_accepted, "{assertion}");
    }
    let input = format!(
        "{PRELUDE}(declare-fun f (Int) Int)\
         (assert (forall ((z Int)) (! (> (f z) 0) :pattern ((f z)))))"
    );
    let [(z3_accepted, _), (plain_accepted, _)] = last_outcomes(&input);
    assert!(z3_accepted && plain_accepted);
}

/// z3 4.12.5 rejects a Bool beside an Int or a Real in `=`, `distinct` and
/// `ite`, and the SMT-LIB 2.7 conversions; z3 5 reads both. z3 mode rejects
/// them, which drops the assertion against either. Arithmetic coerces the
/// Bool in both. `divisible` is an unknown function to z3 unless
/// `:smtlib2_compliant` is set.
#[test]
fn z3_mode_rejects_a_bool_beside_a_number_and_divisible() {
    for assertion in [
        "(assert (= p 1))",
        "(assert (= x x p))",
        "(assert (distinct p p x))",
        "(assert (= p r))",
        "(assert (= x (ite q x p)))",
        "(assert ((_ divisible 3) x))",
        "(assert (= (ubv_to_int b) 1))",
        "(assert (= (sbv_to_int b) 1))",
    ] {
        let input = format!("{PRELUDE}{assertion}");
        let [(z3_accepted, _), (plain_accepted, _)] = last_outcomes(&input);
        assert!(!z3_accepted, "{assertion}");
        assert!(plain_accepted, "{assertion}");
    }
    for assertion in [
        "(assert (= (+ x p) 1))",
        "(assert (< p x))",
        "(assert (= (to_real x) r))",
        "(assert (= x (ite q x 1)))",
    ] {
        let input = format!("{PRELUDE}{assertion}");
        let [(z3_accepted, _), (plain_accepted, _)] = last_outcomes(&input);
        assert!(z3_accepted && plain_accepted, "{assertion}");
    }
    let input =
        format!("(set-option :smtlib2_compliant true){PRELUDE}(assert ((_ divisible 3) x))");
    let [(z3_accepted, _), (plain_accepted, _)] = last_outcomes(&input);
    assert!(z3_accepted && plain_accepted);
}

/// Under a quantifier z3 binds a label whose term has no bound variable,
/// and rejects one whose term has; both are reached in z3 mode. A label over
/// a Real compared with a numeral is outside the vouched fragment.
#[test]
fn labels_under_a_quantifier_are_reached() {
    let input = format!("{PRELUDE}(assert (forall ((z Int)) (or (> z 0) (! p :named a))))");
    assert_eq!(last_outcomes(&input), [(true, None), (true, None)]);
    let input = format!("{PRELUDE}(assert (forall ((z Int)) (! (> z 0) :named a)))");
    assert_eq!(
        last_outcomes(&input),
        [
            (false, Some(LabelFailure::Exact)),
            (false, Some(LabelFailure::Exact))
        ]
    );
    let input = format!("{PRELUDE}(assert (! (> r 1) :named a))");
    assert_eq!(
        last_outcomes(&input),
        [(true, Some(LabelFailure::Unvouched)), (true, None)]
    );
}

/// z3 mode survives `(reset)`.
#[test]
fn z3_mode_survives_reset() {
    let (ctx, results) = run_with(
        true,
        "(declare-const p Bool)(reset)(declare-const p Bool)\
         (assert (exists () p))",
    );
    assert!(ctx.z3_mode());
    assert!(results.last().unwrap().0.is_err());
}
