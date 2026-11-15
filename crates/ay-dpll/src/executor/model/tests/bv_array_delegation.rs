// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Bit-blast coverage is no evidence for an array assertion that the emitted
//! model evaluates to false or Unknown (#bv-array-delegation).
//!
//! The shape is the one the QF_AUFBV reproducer `invalid_model_min1` reached:
//! the model is BV-backed, no array is withheld (`read_conflicted` is empty),
//! and an assertion that is not a direct `select` observation is recorded in
//! `model_validation_delegated_assertions` (its bit-blast literal was true in
//! the SAT assignment). The observation pipeline used to count it as verified
//! although the model it judges falsifies it or cannot evaluate it. Such a
//! model is constructed here directly, without a solve, so the fixtures do
//! not depend on whether a search ever produces it. One test does solve: a
//! candidate refused here must still arm the re-solve that the emission
//! gate's refutation used to arm, or a recoverable `sat` is lost.

use super::*;
use ay_arrays::ArrayInterpretation;

/// A total interpretation of an `(Array (_ BitVec 4) (_ BitVec 3))`.
fn bv4_to_bv3(stores: &[(&str, &str)]) -> ArrayInterpretation {
    ArrayInterpretation {
        index_sort: Some(Sort::bitvec(4)),
        element_sort: Some(Sort::bitvec(3)),
        default: Some("#b000".to_string()),
        stores: stores
            .iter()
            .map(|&(index, value)| (index.to_string(), value.to_string()))
            .collect(),
    }
}

/// `u`, `w`: BV arrays with total interpretations. `m`, `n`: arrays of arrays,
/// which the select scan gives no interpretation, so they have no model value.
struct Fixture {
    executor: Executor,
    u: TermId,
    w: TermId,
    m: TermId,
    n: TermId,
}

impl Fixture {
    fn new() -> Self {
        let mut executor = Executor::new();
        let cells = Sort::array(Sort::bitvec(4), Sort::bitvec(3));
        let rows = Sort::array(Sort::bitvec(4), cells.clone());
        let u = executor.ctx.terms.mk_var("u", cells.clone());
        let w = executor.ctx.terms.mk_var("w", cells);
        let m = executor.ctx.terms.mk_var("m", rows.clone());
        let n = executor.ctx.terms.mk_var("n", rows);
        Self {
            executor,
            u,
            w,
            m,
            n,
        }
    }

    /// Install `assertion` as the only assertion, SAT-assigned true together
    /// with `bools`, over a BV-backed model holding `u_cells` and `w_cells`.
    /// `covered` records it as bit-blast covered; `withheld` marks `m`
    /// read-conflicted, the state that arms `arrays-read-conflict-uneval`.
    fn install(
        &mut self,
        assertion: TermId,
        bools: &[(TermId, bool)],
        u_cells: &[(&str, &str)],
        w_cells: &[(&str, &str)],
        covered: bool,
        withheld: bool,
    ) {
        let executor = &mut self.executor;
        executor.ctx.assertions.push(assertion);
        if covered {
            executor
                .model_validation_delegated_assertions
                .insert(assertion);
        }
        executor.last_result = Some(SolveResult::Sat);
        let mut assignments = vec![(assertion, true)];
        assignments.extend_from_slice(bools);
        let mut model = model_with_sat_assignments(&assignments);
        let mut array_model = ArrayModel {
            array_values: HashMap::from_iter([
                (self.u, bv4_to_bv3(u_cells)),
                (self.w, bv4_to_bv3(w_cells)),
            ]),
            ..Default::default()
        };
        if withheld {
            array_model.read_conflicted.insert(self.m);
        }
        model.array_model = Some(array_model);
        model.bv_model = Some(BvModel {
            values: HashMap::default(),
            term_to_bits: HashMap::default(),
            bool_overrides: bools.iter().copied().collect(),
        });
        executor.last_model = Some(model);
    }

    /// `(or (= (select u #x0) #b000) flag)`, installed with `flag` false, so
    /// with `u[0] = #b100` the model concretely falsifies it.
    fn install_false_clause(&mut self) -> TermId {
        let terms = &mut self.executor.ctx.terms;
        let flag = terms.mk_var("flag", Sort::Bool);
        let zero_index = terms.mk_bitvec(BigInt::zero(), 4);
        let zero_cell = terms.mk_bitvec(BigInt::zero(), 3);
        let read = terms.mk_select(self.u, zero_index);
        let read_is_zero = terms.mk_eq(read, zero_cell);
        let assertion = terms.mk_or(vec![read_is_zero, flag]);
        self.install(assertion, &[(flag, false)], U_CELLS, W_CELLS, true, false);
        assertion
    }

    /// `(or (= u w) (not (= m n)))`: one clause of the reproducer's
    /// `(ite (= m (store n ..)) (= u w) ..)`.
    fn unknown_clause(&mut self) -> TermId {
        let terms = &mut self.executor.ctx.terms;
        let same_cells = terms.mk_eq(self.u, self.w);
        let same_rows = terms.mk_eq(self.m, self.n);
        let rows_differ = terms.mk_not(same_rows);
        terms.mk_or(vec![same_cells, rows_differ])
    }
}

/// `u` and `w` differ at index 0 under the model.
const U_CELLS: &[(&str, &str)] = &[("#x0", "#b100")];
const W_CELLS: &[(&str, &str)] = &[("#x5", "#b100")];

fn assert_incomplete(result: std::result::Result<ValidationStats, ModelValidationError>) {
    match result {
        Err(ModelValidationError::Incomplete(failure)) => assert!(
            failure.detail.contains("BV-backed array assertion"),
            "unexpected incomplete detail: {}",
            failure.detail
        ),
        other => panic!("covered array assertion must fail closed, got {other:?}"),
    }
}

/// The reproducer's state: no array withheld, and a covered non-observation
/// array assertion the model cannot evaluate (`m`, `n` carry no value). Coverage
/// used to make it a verified delegated check (`array_delegated = 3` on the
/// reproducer).
#[test]
fn covered_unknown_array_assertion_with_nothing_withheld_fails_closed() {
    let mut fixture = Fixture::new();
    let assertion = fixture.unknown_clause();
    fixture.install(assertion, &[], U_CELLS, W_CELLS, true, false);
    let model = fixture
        .executor
        .last_model
        .as_ref()
        .expect("model installed");
    assert!(
        matches!(
            fixture.executor.evaluate_term(model, assertion),
            EvalValue::Unknown
        ),
        "fixture must exercise the Unknown arm"
    );

    assert_incomplete(fixture.executor.validate_model());
}

/// Acceptance must not depend on whether something is withheld. The
/// dependence lived in the SAT funnel, not in `validate_model`: before
/// #bv-array-delegation this candidate ended `Sat` with nothing withheld
/// (observation delegated it and `arrays-read-conflict-uneval` was unarmed)
/// but `Unknown` with `m` read-conflicted (the oracle fired). Both must now
/// fail closed, at the observation stage and at the end of the funnel.
#[test]
fn covered_unknown_array_assertion_fails_closed_whether_or_not_withheld() {
    for withheld in [false, true] {
        let mut fixture = Fixture::new();
        let assertion = fixture.unknown_clause();
        fixture.install(assertion, &[], U_CELLS, W_CELLS, true, withheld);
        assert_incomplete(fixture.executor.validate_model());
        let result = fixture
            .executor
            .finalize_sat_model_validation()
            .expect("a covered array assertion the model cannot evaluate degrades");
        assert_eq!(result, SolveResult::Unknown, "withheld = {withheld}");
    }
}

/// The Bool(false) arm: the model concretely falsifies a covered
/// non-observation array assertion, `(or (= (select u #x0) #b000) flag)` with
/// `u[0] = #b100` and `flag` false. No coverage makes that verified, and the
/// full SAT funnel (completion, the independent-gate array handoff) must end in
/// Unknown, never Sat.
#[test]
fn covered_false_array_assertion_fails_closed() {
    let mut fixture = Fixture::new();
    let assertion = fixture.install_false_clause();
    let model = fixture
        .executor
        .last_model
        .as_ref()
        .expect("model installed");
    assert!(
        matches!(
            fixture.executor.evaluate_term(model, assertion),
            EvalValue::Bool(false)
        ),
        "fixture must exercise the Bool(false) arm"
    );

    assert_incomplete(fixture.executor.validate_model());

    let result = fixture
        .executor
        .finalize_sat_model_validation()
        .expect("a falsified covered array assertion degrades, it does not error");
    assert_eq!(result, SolveResult::Unknown);
    assert_eq!(fixture.executor.last_result, Some(SolveResult::Unknown));
}

/// `r1_and_nestedconst_sat` (QF_AUFBV, z3: sat). The first candidate has no
/// value for the array of arrays `m` and leaves `y` at 0: the canonical
/// evaluator stops at `(= m ...)` (Unknown) and the independent gate, resolving
/// `m` through that definition, refutes `(= y (select (select m k) ..))`.
/// Coverage used to carry this candidate to the emission gate, whose
/// refutation armed the preprocessing-free re-solve (#abv-subst-model-retry)
/// that publishes a valid model. Refused at the handoff instead, the candidate
/// must arm the same re-solve, or this `sat` is lost (it was, before
/// `independent_handoff_confirms` armed it).
#[test]
fn nested_const_definition_keeps_its_sat_through_the_substitution_retry() {
    const SCRIPT: &str = "
        (set-option :produce-models true)
        (set-logic QF_AUFBV)
        (declare-const m (Array (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 8))))
        (declare-const k (_ BitVec 64))
        (declare-const p Bool)
        (declare-const y (_ BitVec 8))
        (assert (and p (= m ((as const (Array (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 8))))
                             ((as const (Array (_ BitVec 64) (_ BitVec 8))) #x2a)))))
        (assert (= y (select (select m k) #x0000000000000003)))
        (check-sat)
    ";
    let commands = ay_frontend::parse(SCRIPT).expect("valid SMT-LIB input");
    let mut executor = Executor::new();
    let outputs = executor.execute_all(&commands).expect("script executes");
    assert_eq!(outputs[0], "sat");
    assert!(executor.last_model_validated);
    assert!(matches!(
        executor.confirm_sat_with_independent_gate(),
        ay_model_check::GateVerdict::ConfirmedSat
    ));
    assert_eq!(
        executor
            .statistics()
            .get_int("model_validation.bv.subst_retry"),
        Some(1)
    );
}

/// Negative twin: the same covered shape, now TRUE under the model (`u` and
/// `w` agree), is verified by evaluation alone, with no delegated check. The
/// refusals above come from the evaluation, not from the shape or coverage.
#[test]
fn covered_array_assertion_true_under_the_model_is_verified_independently() {
    let mut fixture = Fixture::new();
    let assertion = fixture.unknown_clause();
    fixture.install(assertion, &[], U_CELLS, U_CELLS, true, false);

    let stats = fixture
        .executor
        .validate_model()
        .expect("an assertion the model satisfies validates");
    assert_eq!(stats.checked, 1);
    assert_eq!(stats.delegated_checks, 0);
    assert_eq!(stats.array_delegated_checks, 0);
}

/// The release of a nested-only array (`theories/bv_model/live_definitions.rs`)
/// is guarded here, not by withholding. `n`'s only definition sits under the
/// asserted `(not (= n (store n0 #x1 ((as const ..) #b000))))`, whose atom the
/// SAT assignment set false, and the reads `n[1][2] = n0[1][2] = 0` make both
/// sides one array once `n` is published with the interpretation its reads
/// give it: the model holds the definition the SAT assignment refused. While
/// coverage was evidence, releasing this shape confirmed models z3 rejects
/// (the fzM fuzz family); with nothing withheld it must fail closed.
#[test]
fn released_array_of_arrays_holding_its_refused_definition_fails_closed() {
    let mut executor = Executor::new();
    let terms = &mut executor.ctx.terms;
    let row = Sort::array(Sort::bitvec(4), Sort::bitvec(3));
    let rows = Sort::array(Sort::bitvec(4), row);
    let n = terms.mk_var("n", rows.clone());
    let n0 = terms.mk_var("n0", rows);
    let one = terms.mk_bitvec(BigInt::one(), 4);
    let two = terms.mk_bitvec(BigInt::from(2u8), 4);
    let zero = terms.mk_bitvec(BigInt::zero(), 3);
    let zero_row = terms.mk_const_array(Sort::bitvec(4), zero);
    let refused = terms.mk_store(n0, one, zero_row);
    let definition = terms.mk_eq(n, refused);
    let assertion = terms.mk_not(definition);
    let mut read = |array: TermId| {
        let row = terms.mk_select(array, one);
        terms.mk_select(row, two)
    };
    let reads = [read(n), read(n0)];
    let bv_model = BvModel {
        values: reads.iter().map(|&read| (read, BigInt::zero())).collect(),
        term_to_bits: HashMap::default(),
        bool_overrides: HashMap::from_iter([(definition, false)]),
    };
    let arrays = Executor::extract_array_model_from_bv_model(
        &executor.ctx.terms,
        &bv_model,
        &[assertion],
        &Default::default(),
    );
    assert!(arrays.read_conflicted.is_empty(), "nothing is withheld");
    assert!(arrays.array_values.contains_key(&n), "n is published");

    executor.ctx.assertions.push(assertion);
    executor
        .model_validation_delegated_assertions
        .insert(assertion);
    executor.last_result = Some(SolveResult::Sat);
    let mut model = model_with_sat_assignments(&[(assertion, true), (definition, false)]);
    model.array_model = Some(arrays);
    model.bv_model = Some(bv_model);
    executor.last_model = Some(model);
    let model = executor.last_model.as_ref().expect("model installed");
    assert!(
        !matches!(
            executor.evaluate_term(model, assertion),
            EvalValue::Bool(true)
        ),
        "fixture: the published model must hold the refused definition"
    );

    assert_incomplete(executor.validate_model());
    let result = executor
        .finalize_sat_model_validation()
        .expect("a covered array assertion the model does not satisfy degrades");
    assert_eq!(result, SolveResult::Unknown);
}
