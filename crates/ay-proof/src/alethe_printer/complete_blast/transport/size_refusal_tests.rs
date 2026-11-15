// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! A swept refutation refused only by its size settles its lemma
//! (`size_refusal.rs`), on the definitional signed division of model-checker-consumer's
//! `sdiv64_or2` at a width small enough to test: the counted text bound, or
//! the consumer's line, is lowered here below the document the sweep prints
//! at the real ones.

use super::super::super::lane::{self, Lane, Plan};
use super::super::super::lazy::Planned;
use super::super::super::{AlethePrinter, Blaster, SRef};
use super::super::Target;
use crate::resolution_dag_memo::{
    reset_resolution_dag_memo, resolution_dag_is_memoized_by, resolution_dag_memo_counters,
};
use ay_core::{ProofId, Sort, Symbol, TermId, TermStore};
use num_bigint::BigInt;
use std::cell::Cell;
use std::thread::LocalKey;

thread_local! {
    /// The bound `swept_text_bound` returns on this thread, when set.
    pub(super) static SWEPT_TEXT_BOUND: Cell<Option<usize>> = const { Cell::new(None) };
    /// The byte line `consumer_takes` holds a document to on this thread, in
    /// place of `consumer_accepts`, when set.
    pub(super) static CONSUMER_LINE: Cell<Option<usize>> = const { Cell::new(None) };
}

/// The width of the fixture: its blast is a large circuit, and its lazy plan
/// leaves the two dead divisions opaque.
const WIDTH: u32 = 16;

/// `(not (= (bvsdiv x -1) (bvsub 0 x)))` at `width` bits, `bvsdiv` spelled
/// by its SMT-LIB definition through `bvudiv`, as model-checker-consumer exports it: a
/// four-way `ite` over the operand signs, two of whose divisions the constant
/// divisor leaves dead.
fn definitional_negation(terms: &mut TermStore, width: u32) -> TermId {
    let bv = Sort::bitvec(width);
    let x = terms.mk_var("x", bv.clone());
    let ones = (BigInt::from(1) << width) - 1;
    let divisor = terms.mk_bitvec(ones, width);
    let zero = terms.mk_bitvec(BigInt::from(0), width);
    let app = |terms: &mut TermStore, name: &str, args: &[TermId], sort: &Sort| {
        terms.mk_app(Symbol::named(name), args, sort.clone())
    };
    let sign = |terms: &mut TermStore, word: TermId, bit: u32| {
        let top = width - 1;
        let extract = terms.mk_app(
            Symbol::indexed("extract", vec![top, top]),
            [word],
            Sort::bitvec(1),
        );
        let value = terms.mk_bitvec(BigInt::from(bit), 1);
        terms.mk_app(Symbol::named("="), [extract, value], Sort::Bool)
    };
    let neg_x = app(terms, "bvneg", &[x], &bv);
    let neg_divisor = app(terms, "bvneg", &[divisor], &bv);
    let guard = |terms: &mut TermStore, x_bit: u32, d_bit: u32| {
        let left = sign(terms, x, x_bit);
        let right = sign(terms, divisor, d_bit);
        terms.mk_app(Symbol::named("and"), [left, right], Sort::Bool)
    };
    let both_nonneg = guard(terms, 0, 0);
    let x_neg = guard(terms, 1, 0);
    let d_neg = guard(terms, 0, 1);
    let q0 = app(terms, "bvudiv", &[x, divisor], &bv);
    let q1 = app(terms, "bvudiv", &[neg_x, divisor], &bv);
    let q1 = app(terms, "bvneg", &[q1], &bv);
    let q2 = app(terms, "bvudiv", &[x, neg_divisor], &bv);
    let q2 = app(terms, "bvneg", &[q2], &bv);
    let q3 = app(terms, "bvudiv", &[neg_x, neg_divisor], &bv);
    let inner = terms.mk_ite_raw(d_neg, q2, q3);
    let middle = terms.mk_ite_raw(x_neg, q1, inner);
    let quotient = terms.mk_ite_raw(both_nonneg, q0, middle);
    let negation = app(terms, "bvsub", &[zero, x], &bv);
    let equality = terms.mk_app(Symbol::named("="), [quotient, negation], Sort::Bool);
    terms.mk_not_raw(equality)
}

/// The complete blast's render of the lemma `(cl (not assertion))`.
fn render(terms: &TermStore, assertion: TermId) -> Option<String> {
    let mut terms = terms.clone();
    let literal = terms.mk_not_raw(assertion);
    let printer = AlethePrinter::new(&terms);
    printer.format_bv_complete_blast_refutation(ProofId(1), &[literal])
}

/// `run` with the line `seam` holds set to `bound`, unset again however
/// `run` ends.
fn with_line<T>(
    seam: &'static LocalKey<Cell<Option<usize>>>,
    bound: usize,
    run: impl FnOnce() -> T,
) -> T {
    struct Unset(&'static LocalKey<Cell<Option<usize>>>);
    impl Drop for Unset {
        fn drop(&mut self) {
            self.0.with(|cell| cell.set(None));
        }
    }
    seam.with(|cell| cell.set(Some(bound)));
    let _unset = Unset(seam);
    run()
}

/// `run` with the swept refutation's bound lowered to `bound`.
fn with_swept_bound<T>(bound: usize, run: impl FnOnce() -> T) -> T {
    with_line(&SWEPT_TEXT_BOUND, bound, run)
}

/// `run` with the consumer's line lowered to `bound` bytes.
fn with_consumer_line<T>(bound: usize, run: impl FnOnce() -> T) -> T {
    with_line(&CONSUMER_LINE, bound, run)
}

/// The plan of the lemma's root, lazily (`lazy`) or with every division
/// exact, as the render plans it: its gate count and CNF.
fn plan(terms: &TermStore, assertion: TermId, lazy: bool) -> (usize, Vec<Vec<ay_sat::Literal>>) {
    let printer = AlethePrinter::new(terms);
    let orient = |_: &mut Blaster<'_, '_>, prepared: &[SRef]| prepared.first().copied();
    let Planned { blaster, cnf, .. } = Blaster::plan_lemma(
        &printer,
        ProofId(1),
        "@ay_cbb_t1_0_",
        &[assertion],
        &orient,
        lazy,
        None,
    )
    .expect("the lemma plans");
    (blaster.circuit.len(), cnf)
}

/// The lazy plan, sent straight to the sweep as a render that already
/// printed it there would be (`lane.rs`): at this width the direct lane
/// prints the lemma on its own, and the sweep is the lane under test.
fn sent_to_the_sweep(terms: &TermStore, assertion: TermId) -> (usize, Vec<Vec<ay_sat::Literal>>) {
    let (gates, cnf) = plan(terms, assertion, true);
    lane::remember(Some(Plan::of(gates, &cnf)), Lane::Sweep);
    (gates, cnf)
}

/// Whether some lane retained a refutation of the plan `(gates, cnf)`.
fn asked(gates: usize, cnf: &[Vec<ay_sat::Literal>]) -> bool {
    ["direct", "sweep"]
        .iter()
        .any(|lane| resolution_dag_is_memoized_by(gates, cnf, lane))
}

/// `run` from a cold refutation memo, and how many refutations it asked the
/// memo for that it did not hold: every lane's search goes through it.
fn cold<T>(run: impl FnOnce() -> T) -> (T, u64) {
    reset_resolution_dag_memo();
    let result = run();
    (result, resolution_dag_memo_counters().1)
}

/// The lemma's render from a cold memo with `lowered` in place, against
/// the render that printed in `printed_asks` searches: it declines, asks
/// for no search that render did not ask for (neither the monolithic search
/// nor the plan with every division exact runs after the sweep), and leaves
/// the sweep's refutation retained.
fn assert_settled(
    terms: &TermStore,
    assertion: TermId,
    printed_asks: u64,
    lowered: impl FnOnce(&dyn Fn() -> Option<String>) -> Option<String>,
) {
    let (lazy_gates, lazy_cnf) = plan(terms, assertion, true);
    let (exact_gates, exact_cnf) = plan(terms, assertion, false);
    let (declined, declined_asks) = cold(|| lowered(&|| render(terms, assertion)));
    assert!(
        declined.is_none(),
        "a swept document refused by its size must decline the lemma"
    );
    assert!(
        declined_asks <= printed_asks,
        "the settle must ask for no search the printing render did not: \
         {declined_asks} against {printed_asks}"
    );
    assert!(
        !asked(exact_gates, &exact_cnf),
        "the plan with every division exact must not be asked after the settle"
    );
    assert!(resolution_dag_is_memoized_by(
        lazy_gates, &lazy_cnf, "sweep"
    ));
}

/// The sweep refutes the lazily planned lemma and its document prints at the
/// counted bound. Past a lowered bound the render declines, and neither the
/// monolithic search nor the plan with every division exact runs after the
/// sweep, although the monolithic search refutes the same plan and prints it
/// within the counted bound: before `size_refusal.rs`, the lowered bound fell
/// through to it and the render printed.
#[test]
fn a_swept_refutation_past_the_counted_bound_settles_the_lemma() {
    let mut terms = TermStore::new();
    let assertion = definitional_negation(&mut terms, WIDTH);
    let (exact_gates, _) = plan(&terms, assertion, false);
    let (lazy_gates, lazy_cnf) = sent_to_the_sweep(&terms, assertion);
    assert!(
        lazy_gates < exact_gates,
        "the lazy plan must leave divisions opaque: {lazy_gates} against {exact_gates} gates"
    );

    let (document, printed_asks) = cold(|| render(&terms, assertion));
    let document = document.expect("the swept refutation prints");
    assert!(!document.contains(":rule hole") && !document.contains(":rule trust"));
    assert!(resolution_dag_is_memoized_by(
        lazy_gates, &lazy_cnf, "sweep"
    ));
    assert_settled(&terms, assertion, printed_asks, |render| {
        with_swept_bound(document.len() / 2, render)
    });

    // The counterfactual, each with the counted bound: the lazy plan's
    // monolithic search refutes it and prints, and the plan with every
    // division exact prints. Before the settle, the render reached both.
    let printer = AlethePrinter::new(&terms);
    let orient = |_: &mut Blaster<'_, '_>, prepared: &[SRef]| prepared.first().copied();
    let planned = |lazy: bool| {
        Blaster::plan_lemma(
            &printer,
            ProofId(1),
            "@ay_cbb_t1_0_",
            &[assertion],
            &orient,
            lazy,
            None,
        )
        .expect("the lemma plans")
    };
    let Planned {
        blaster,
        root,
        cnf,
        root_clause_id,
        ..
    } = planned(true);
    let dag = blaster
        .monolithic_refutation_planned(blaster.circuit.len(), &cnf)
        .expect("the monolithic search refutes the lazy plan");
    let target = Target {
        cnf: &cnf,
        root_clause_id,
        root,
        unit: "t1",
        final_clause: "(cl)",
    };
    assert!(blaster.print_refutation(&dag, &target).is_some());
    let Planned {
        mut blaster,
        root,
        cnf,
        root_clause_id,
        ..
    } = planned(false);
    assert!(blaster
        .finish_planned(&cnf, root_clause_id, root, "t1", "(cl)")
        .is_some());
}

/// The same settle when the swept document is within the counted bound but
/// outside the consumer's budget (`consumer_accepts`): before the consumer's
/// refusal counted as one, the render fell through to the monolithic search
/// and then planned the lemma again with every division exact, as
/// `sdiv56_or2` did for minutes.
#[test]
fn a_swept_refutation_the_consumer_refuses_settles_the_lemma() {
    let mut terms = TermStore::new();
    let assertion = definitional_negation(&mut terms, WIDTH);
    sent_to_the_sweep(&terms, assertion);
    let (document, printed_asks) = cold(|| render(&terms, assertion));
    let document = document.expect("the swept refutation prints");
    assert_settled(&terms, assertion, printed_asks, |render| {
        with_consumer_line(document.len() / 2, render)
    });
}

/// A document within both lines is untouched: the same render, with either
/// line just above the swept document, prints the same document.
#[test]
fn a_swept_refutation_within_the_lines_still_prints() {
    let mut terms = TermStore::new();
    let assertion = definitional_negation(&mut terms, WIDTH);
    sent_to_the_sweep(&terms, assertion);
    reset_resolution_dag_memo();
    let document = render(&terms, assertion).expect("the swept refutation prints");
    let above = document.len() + 4096;
    reset_resolution_dag_memo();
    let bounded = with_swept_bound(above, || render(&terms, assertion));
    assert_eq!(bounded.as_deref(), Some(document.as_str()));
    reset_resolution_dag_memo();
    let taken = with_consumer_line(above, || render(&terms, assertion));
    assert_eq!(taken.as_deref(), Some(document.as_str()));
}
