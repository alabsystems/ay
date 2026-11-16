// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Subterms elaboration passes over (the untaken branch of an `ite` with a
//! constant condition, an unused `let` value, a `match` case that cannot be
//! taken) are read by z3, which raises errors and binds labels there. They
//! are checked where z3 reads them. The scripts include the z3-mode
//! conformance review's repros, whose z3 answers the CLI tests pin.

use super::*;

/// Each command's result and the label outcome read after it.
type Outcomes = Vec<(Result<()>, Option<LabelFailure>)>;

/// Process every command, returning each result and the label outcome read
/// after it.
fn run(input: &str) -> (Context, Outcomes) {
    run_in_mode(false, input)
}

/// [`run`] under `--z3-mode` (`z3`) or not.
fn run_in_mode(z3: bool, input: &str) -> (Context, Outcomes) {
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

const PRELUDE: &str = "(declare-datatypes ((P 0)) (((mk (fst Int)) (nothing))))\
     (declare-const p Bool)(declare-const q Bool)(declare-const c Bool)";

/// The skipped subterms that hold an error z3 raises.
const SKIPPED_ERRORS: [&str; 5] = [
    "(ite true true undefined_sym)",
    "(ite (= 1 1) true (not p q))",
    "(let ((l0 undefined_sym)) true)",
    "(match (mk 1) (((mk v) true) (nothing undefined_sym)))",
    "(match (mk 1) ((_ true) ((mk v) (not p q))))",
];

/// z3 rejects the assertion at the error, before label `a`, so it binds no
/// label and accepts a later `(! (not p) :named a)`. The rejection used to
/// come only at label `c`, with `a` bound. An error that is not a label's
/// leaves z3's labels unknown here (z3 may not raise it), so the outcome is
/// [`LabelFailure::Diverged`].
#[test]
fn an_error_in_a_skipped_subterm_rejects_before_later_labels() {
    for skipped in SKIPPED_ERRORS {
        let (ctx, results) = run(&format!(
            "{PRELUDE}(assert (and {skipped} (! p :named a) (! q :named c)))\
             (assert (! (not p) :named a))"
        ));
        let [.., (first, first_failure), (second, second_failure)] = results.as_slice() else {
            unreachable!();
        };
        assert!(first.is_err(), "{skipped}");
        assert_eq!(*first_failure, Some(LabelFailure::Diverged), "{skipped}");
        assert!(second.is_ok(), "{skipped}: {second:?}");
        assert_eq!(*second_failure, None, "{skipped}");
        assert!(ctx.fun_defs.contains_key("a"), "{skipped}");
    }
}

/// z3 accepts these assertions and binds `a`: `bvumul_noovfl` and
/// `ext_rotate_left` are z3 builtins, which this frontend reads as undefined
/// symbols. So a rejection for a name, sort or constant error before a label
/// is not z3's, whether the error stands in a skipped subterm or a live one:
/// the outcome is `Diverged`, never one that lets a later reuse of `a` count
/// as matching z3 (it answered unsat where z3 answers sat).
#[test]
fn a_z3_builtin_the_frontend_lacks_before_a_label_diverges() {
    for unsupported in [
        "(ite true true (bvumul_noovfl b b))",
        "(match (mk 1) (((mk v) true) (nothing (bvumul_noovfl b b))))",
        "(let ((l0 (ext_rotate_left b b))) true)",
        "(bvumul_noovfl b b)",
    ] {
        let (_, results) = run(&format!(
            "{PRELUDE}(declare-const b (_ BitVec 8))\
             (assert (and {unsupported} (! p :named a)))"
        ));
        let (result, failure) = results.last().unwrap();
        assert!(result.is_err(), "{unsupported}");
        assert_eq!(*failure, Some(LabelFailure::Diverged), "{unsupported}");
    }
}

/// z3 binds `b` in the skipped branch before it rejects the assertion at
/// `c`, and then rejects `(! p :named b)`. `--z3-mode` follows it, since its
/// walk vouches for every subterm before `c`; plain mode's dialect leaves
/// the outcome unknown and binds nothing.
#[test]
fn a_label_in_a_skipped_subterm_is_bound_where_z3_binds_it() {
    let input = format!(
        "{PRELUDE}(assert (or (ite true true (! false :named b)) (! p :named c)))\
         (assert (or (! p :named b) (not p)))"
    );
    let (ctx, results) = run_in_mode(true, &input);
    let [.., (first, first_failure), (second, second_failure)] = results.as_slice() else {
        unreachable!();
    };
    assert!(first.is_err());
    assert_eq!(*first_failure, Some(LabelFailure::Exact));
    assert!(second.is_err());
    assert_eq!(*second_failure, Some(LabelFailure::Exact));
    assert_eq!(
        ctx.fun_defs.get("b").map(|(_, _, body)| body.clone()),
        Some(ParsedTerm::Const(crate::command::ParsedConstant::False))
    );

    let (_, results) = run(&input);
    let [.., (first, first_failure), _] = results.as_slice() else {
        unreachable!();
    };
    assert!(first.is_err());
    assert_eq!(*first_failure, Some(LabelFailure::Diverged));
}

/// An accepted assertion binds the labels of its skipped subterms too.
#[test]
fn an_accepted_assertion_binds_skipped_labels() {
    let (ctx, results) = run(&format!(
        "{PRELUDE}(declare-const x Int)\
         (assert (and (ite (not false) p (! (> x 0) :named b)) (let ((l0 (! q :named d))) p)))"
    ));
    let (result, failure) = results.last().unwrap();
    assert!(result.is_ok(), "{result:?}");
    // The `let` value's label is reached, but out of z3's parse order.
    assert_eq!(*failure, Some(LabelFailure::Diverged));
    assert!(ctx.fun_defs.contains_key("b"));
    assert!(ctx.fun_defs.contains_key("d"));
}

/// z3 rejects these commands at the error in the skipped subterm. They used
/// to be kept here, which answered unsat where z3 answers sat.
#[test]
fn an_error_in_a_skipped_subterm_rejects_the_command() {
    for command in [
        "(assert (ite true p undefined_sym))",
        "(assert (let ((l0 undefined_sym)) p))",
        "(assert (match (mk 1) (((mk v) p) (nothing undefined_sym))))",
        "(assert (match nothing (((mk v) undefined_sym) (nothing p))))",
        "(assert (match (mk 1) (((mk v) p) (_ false) ((mk w) undefined_sym))))",
        "(assert (ite true p (ite true (= #x00 #x01) undefined_sym)))",
        "(assert (forall ((k Int)) (ite true p (> k undefined_sym))))",
        "(define-fun f () Bool (ite false undefined_sym p))",
        "(define-fun g ((z Int)) Bool (let ((unused (+ z undefined_sym))) p))",
        "(assert (let ((t undefined_sym)) (let ((u t)) p)))",
        "(assert (let ((t p)) (let ((u (bvadd t #x01))) p)))",
    ] {
        let (ctx, results) = run(&format!("{PRELUDE}{command}"));
        let (result, failure) = results.last().unwrap();
        assert!(result.is_err(), "{command}");
        assert_eq!(*failure, None, "{command}");
        assert!(ctx.assertions.is_empty(), "{command}");
        assert!(!ctx.fun_defs.contains_key("f") && !ctx.fun_defs.contains_key("g"));
    }
}

/// Well-sorted skipped subterms change nothing, whether the read-only check
/// vouches for them or the scratch elaboration does.
#[test]
fn a_well_sorted_skipped_subterm_is_accepted() {
    let prelude = format!(
        "{PRELUDE}(declare-const x Int)(declare-const y Real)(declare-const b (_ BitVec 8))\
         (declare-const m (Array Int Int))\
         (declare-fun g (Int) Bool)(define-fun h ((z Int)) Int (+ z 1))"
    );
    for command in [
        "(assert (ite true p (and (g (h x)) (< (to_real x) y) (distinct x 2))))",
        "(assert (let ((t x) (u (bvadd b #x01))) (= x 0)))",
        "(assert (match nothing (((mk v) (> v x)) (nothing p))))",
        "(assert (match (mk x) ((w p) ((mk v) (> v 0)) (nothing q))))",
        "(assert (ite false (= (bvadd b #x01) #x00) p))",
        "(assert (forall ((k Int)) (ite true (> k x) (< k (h x)))))",
        "(define-fun f () Bool (ite true p (= (bvadd b #x01) #x00)))",
        // A dead value may name an earlier dead binding.
        "(assert (let ((t x)) (let ((u (+ t 1))) p)))",
        "(assert (let ((t b)) (let ((u (bvadd t #x01))) p)))",
        "(assert (let ((t b)) (let ((t x) (u (bvadd t #x01))) (let ((v (+ t 1))) p))))",
        "(assert (let ((t (concat b #b1010)) (u (bvult (bvneg b) #x7f))) p))",
        "(assert (let ((t (select (store m x 1) x))) p))",
        // An Int and a Real branch join at Real.
        "(assert (= (ite true 1.5 x) 1.5))",
        "(assert (= (ite false 1.5 x) 1.5))",
    ] {
        let (_, results) = run(&format!("{prelude}{command}"));
        let (result, failure) = results.last().unwrap();
        assert!(result.is_ok(), "{command}: {result:?}");
        assert_eq!(*failure, None, "{command}");
    }
}

/// A skipped subterm with no error keeps a label rejection exact: z3 binds
/// `a`, reads the skipped subterm and rejects the assertion at `c`.
#[test]
fn a_well_sorted_skipped_subterm_keeps_a_label_rejection_exact() {
    for skipped in [
        "(> (+ x 1) 0)",
        "(let ((l0 (- x -1)) (l1 a)) (and l1 (distinct l0 x 2)))",
        "(forall ((k Int) (r Real)) (or a (< (to_real k) r)))",
        "(= (bvadd b #x01) #x00)",
        "(let ((v (fst (mk x)))) (and ((_ is mk) nothing) (= v (fst (mk 1)))))",
    ] {
        let (ctx, results) = run(&format!(
            "{PRELUDE}(declare-const x Int)(declare-const b (_ BitVec 8))\
             (assert (and (! p :named a) (ite true true {skipped}) (! q :named c)))"
        ));
        let (result, failure) = results.last().unwrap();
        assert!(result.is_err(), "{skipped}");
        assert_eq!(*failure, Some(LabelFailure::Exact), "{skipped}");
        assert!(ctx.fun_defs.contains_key("a"), "{skipped}");
    }
}

/// z3 checks that both branches of an `ite` have one sort, and that the
/// bodies of a `match` do, whichever is taken.
#[test]
fn skipped_branches_and_cases_are_sort_checked() {
    for command in [
        "(assert (ite true p 1))",
        "(assert (ite false 1 p))",
        "(assert (= (ite true (_ bv0 8) 0) (_ bv0 8)))",
        "(assert (match (mk 1) (((mk v) p) (nothing 1))))",
        "(assert (match (mk 1) ((w p) (nothing 1))))",
    ] {
        let (_, results) = run(&format!("{PRELUDE}{command}"));
        assert!(results.last().unwrap().0.is_err(), "{command}");
    }
}

/// A later case of a `match` is never taken, but z3 checks its pattern.
#[test]
fn a_pattern_after_a_catch_all_is_checked() {
    for case in ["((bogus w) true)", "((mk v w) true)", "(mk true)"] {
        let (_, results) = run(&format!(
            "{PRELUDE}(declare-const x P)(assert (match x (((mk v) true) (_ false) {case})))"
        ));
        assert!(results.last().unwrap().0.is_err(), "{case}");
    }
}

/// An error z3 may not raise, before labels this context never reached:
/// z3 goes on to bind those labels, so the outcome is not exact.
#[test]
fn a_frontend_limit_before_unreached_labels_diverges() {
    let (_, results) = run(&format!(
        "{PRELUDE}(assert (and (ite true p (ite true p 1)) (! p :named a)))"
    ));
    let (result, failure) = results.last().unwrap();
    assert!(result.is_err());
    assert_eq!(*failure, Some(LabelFailure::Diverged));
}

/// The skipped subterms of one command share a scratch copy. A name bound
/// after the copy was made is checked there by its sort.
#[test]
fn a_shared_scratch_checks_later_names_by_sort() {
    let prelude = "(declare-const p Bool)(declare-const b (_ BitVec 8))";
    let well_sorted = "(assert (let ((d1 (bvmul b b)) (a (bvadd b #x01))) \
                       (let ((d2 (bvmul a a))) (bvult a b))))";
    let (_, results) = run(&format!("{prelude}{well_sorted}"));
    let (result, failure) = results.last().unwrap();
    assert!(result.is_ok(), "{result:?}");
    assert_eq!(*failure, None);
    let ill_sorted = "(assert (let ((d1 (bvmul b b)) (a (bvadd b #x01))) \
                      (let ((d2 (bvmul a p))) (bvult a b))))";
    let (ctx, results) = run(&format!("{prelude}{ill_sorted}"));
    assert!(results.last().unwrap().0.is_err());
    assert_eq!(ctx.assertions.len(), 0);
}

/// The shared scratch copy follows declarations, definitions and labels made
/// after it.
#[test]
fn a_shared_scratch_sees_later_declarations() {
    let (_, results) = run("(declare-const s String)(declare-const p Bool)\
         (assert (let ((d (str.len s))) p))\
         (declare-const t String)(assert (let ((d (str.++ s t))) p))\
         (define-fun u () String \"a\")(assert (let ((d (str.len u))) p))\
         (assert (! p :named lab))(assert (let ((d (ite lab s t))) p))\
         (push)(declare-const v String)(assert (let ((d (str.len v))) p))(pop)\
         (assert (let ((d (str.len v))) p))");
    // Only the last assertion, whose `v` was popped, is rejected.
    let errors = results.iter().filter(|(result, _)| result.is_err()).count();
    assert_eq!(errors, 1, "{results:?}");
    assert!(results.last().unwrap().0.is_err());
}

/// The scratch elaboration of a skipped subterm never reaches the real term
/// store.
#[test]
fn a_skipped_subterm_is_not_interned() {
    let (ctx, results) = run("(declare-const p Bool)(declare-const b (_ BitVec 8))\
         (declare-fun f ((_ BitVec 8)) Bool)(assert (ite true p (f (bvadd b #x01))))\
         (assert (let ((dead (f b))) p))");
    assert!(results
        .iter()
        .all(|(result, failure)| result.is_ok() && failure.is_none()));
    let interned_f = ctx
        .terms
        .term_ids()
        .any(|id| matches!(ctx.terms.get(id), TermData::App(symbol, _) if symbol.name() == "f"));
    assert!(!interned_f);
}

/// Each dead value of a `let` chain is checked with only the earlier dead
/// bindings it names. Standing in every earlier one for every value grew the
/// shared scratch copy with the square of the chain's length: a 4,000-level
/// chain over a Real reached 1.4 GB and answered `unknown` (memout).
#[test]
fn a_dead_let_chain_grows_the_shared_scratch_linearly() {
    const LEVELS: usize = 2_000;
    let mut assertion = String::new();
    for level in 0..LEVELS {
        let previous = if level == 0 {
            "x".to_string()
        } else {
            format!("d{}", level - 1)
        };
        assertion.push_str(&format!("(let ((d{level} (+ {previous} 1))) "));
    }
    assertion.push('p');
    assertion.push_str(&")".repeat(LEVELS));
    let (ctx, results) = run(&format!(
        "(declare-const x Real)(declare-const p Bool)(assert {assertion})"
    ));
    let (result, failure) = results.last().unwrap();
    assert!(result.is_ok(), "{result:?}");
    assert_eq!(*failure, None);
    let scratch = ctx
        .shared_scratch_term_count()
        .expect("the dead values were elaborated in the shared scratch copy");
    let grown = scratch.saturating_sub(ctx.terms.len());
    assert!(
        grown < 10 * LEVELS,
        "{grown} terms for {LEVELS} dead values"
    );
}

/// The shared scratch copy is a full copy of the context, so it is dropped
/// before a query is solved rather than held while the solver runs.
#[test]
fn the_shared_scratch_is_dropped_at_a_query() {
    let script = "(declare-const x Real)(declare-const p Bool)(assert (let ((d (+ x 1))) p))";
    let (ctx, _) = run(script);
    assert!(ctx.shared_scratch_term_count().is_some());
    for query in ["(check-sat)", "(check-sat-assuming (p))"] {
        let (ctx, results) = run(&format!("{script}{query}"));
        assert!(results.iter().all(|(result, _)| result.is_ok()), "{query}");
        assert!(ctx.shared_scratch_term_count().is_none(), "{query}");
    }
}
