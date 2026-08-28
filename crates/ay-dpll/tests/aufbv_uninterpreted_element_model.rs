// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! SAT-direction model construction for BV-indexed arrays whose ELEMENT sort is
//! an uninterpreted (free) sort, and for non-bit-blastable (Bool) array reads
//! anchored by a head equality (#aufbv-uninterp-elem / #aufbv-nonbv-elem).
//!
//! Before this capability the eager QF_AUFBV bit-blast produced only a `bv_model`
//! for the index structure; `(select arr i)` over an uninterpreted/Bool element
//! had NO value, so an equality `(= seed (select arr i))` evaluated to Unknown
//! and the model validator fail-closed — a genuinely SAT query was reported
//! `unknown`. The model-completion pass now synthesizes element values from the
//! SAT-true equality atoms (congruence over `=`), so these queries return `sat`
//! with a concrete model. Soundness is preserved by the full model validation
//! that runs immediately afterward (a mis-synthesis degrades to Unknown, never a
//! wrong SAT).

use ay_dpll::Executor;
use ay_frontend::parse;

fn verdict(smt: &str) -> String {
    let commands = parse(smt).expect("parse ok");
    let mut executor = Executor::new();
    executor
        .execute_all(&commands)
        .expect("exec ok")
        .into_iter()
        .find(|l| matches!(l.trim(), "sat" | "unsat" | "unknown"))
        .unwrap_or_else(|| "NORESULT".into())
}

/// An equality between an uninterpreted-sort array read and a same-sort const is
/// satisfiable; the solver must produce a concrete element model, not `unknown`.
#[test]
fn uninterpreted_element_array_select_equality_is_sat() {
    assert_eq!(
        verdict(
            r#"
        (set-logic ALL)
        (declare-sort U 0)
        (declare-const arr (Array (_ BitVec 64) U))
        (declare-const seed U)
        (assert (= (select arr #x0000000000000000) seed))
        (check-sat)
    "#
        ),
        "sat"
    );
}

/// The optimum-gate drop-floor refutation shape: a Bool UF over array arguments
/// must be made TRUE while `value > floor`, with the array heads anchored to
/// seeds over BOTH an uninterpreted-element array and a Bool-element array. This
/// is the QF_AUFBV analogue of the ay-pb `optimum_upgrade_guard_drop_floor`
/// negative control that deductive-checks discharges; it must be `sat` (a concrete
/// counterexample), not `unknown`.
#[test]
fn drop_floor_gate_refutation_is_sat() {
    assert_eq!(
        verdict(
            r#"
        (set-logic ALL)
        (declare-sort PbConstraint 0)
        (declare-const constraints (Array (_ BitVec 64) PbConstraint))
        (declare-const __ground_seed_constraints PbConstraint)
        (declare-const result Bool)
        (declare-const assignment (Array (_ BitVec 64) Bool))
        (declare-const __ground_seed_assignment Bool)
        (declare-const value (_ BitVec 128))
        (declare-const floor (_ BitVec 128))
        (declare-fun verify_all_constraints
            ((Array (_ BitVec 64) PbConstraint) (Array (_ BitVec 64) Bool)) Bool)
        (assert (= result
            (and (bvsle value floor) (verify_all_constraints constraints assignment))))
        (assert (= (select assignment #x0000000000000000) __ground_seed_assignment))
        (assert (= (select constraints #x0000000000000000) __ground_seed_constraints))
        (assert (not (= (verify_all_constraints constraints assignment)
            (and (bvsle value floor) (verify_all_constraints constraints assignment)))))
        (check-sat)
    "#
        ),
        "sat"
    );
}

// ---------------------------------------------------------------------------
// SAT-direction DATATYPE model distinguishability (#dt-opaque-diseq /
// assumption-rooted element synthesis).
//
// The deductive-checks `eval_objective_exact` saturating-substitution control discharges
// the obligation negation `eval_terms_saturating(t,a) != eval_terms_checked(t,a)`
// — a DISEQUALITY between two DISTINCT datatype-valued (`Result<i128,_>`)
// uninterpreted-function applications — while the body binding
// `result == eval_terms_saturating(t,a)` is carried as a `check_sat_assuming`
// ASSUMPTION. Before this capability AY returned `unknown`: (1) model completion
// gathered candidate datatype terms only from the top-level assertions, so the
// `result` operand reachable only through the assumption got NO synthesized
// element and the assumption evaluated to Unknown; and (2) the datatype
// disequality fail-closed because only a positive opaque equality was accepted.
// Now completion also roots on the assumptions (merging the asserted-true body
// binding), and an opaque disequality over a non-degenerate datatype is accepted
// (`dt_diseq_opaque_satisfiable`), so the query is `sat` with a concrete model.
// ---------------------------------------------------------------------------

use ay_dpll::api::{DatatypeConstructor, DatatypeField, DatatypeSort, Logic, Solver, Sort, Term};

fn datatype_valued_uf_problem() -> (Solver, Term, Term) {
    let mut s = Solver::new(Logic::All);
    // ObjectiveEvalError (sole nullary ctor) and Result<i128, _> (Ok(BV128)|Err).
    s.try_declare_datatype(&DatatypeSort::new(
        "ObjectiveEvalError",
        vec![DatatypeConstructor::new(
            "ObjectiveEvalError_Overflow",
            vec![],
        )],
    ))
    .unwrap();
    let res_name = "Result<i128, ObjectiveEvalError>";
    s.try_declare_datatype(&DatatypeSort::new(
        res_name,
        vec![
            DatatypeConstructor::new(
                "Result_Ok",
                vec![DatatypeField::new("Result_Ok_0", Sort::bitvec(128))],
            ),
            DatatypeConstructor::new(
                "Result_Err",
                vec![DatatypeField::new(
                    "Result_Err_0",
                    Sort::Uninterpreted("ObjectiveEvalError".to_string()),
                )],
            ),
        ],
    ))
    .unwrap();
    // Exact TrustVC carrier topology: `PbTerm` contains a nested BV-indexed
    // array of `PbLit`, and the outer terms slice is another BV-indexed array.
    // Keeping the inner datatype array is load-bearing: a scalar-only PbTerm
    // missed the model-completion collision exercised by the real proof.
    s.try_declare_datatype(&DatatypeSort::new(
        "PbLit",
        vec![DatatypeConstructor::new(
            "PbLit_PbLit",
            vec![
                DatatypeField::new("PbLit_PbLit_var", Sort::bitvec(32)),
                DatatypeField::new("PbLit_PbLit_negated", Sort::Bool),
            ],
        )],
    ))
    .unwrap();
    let lits_array = Sort::array(Sort::bitvec(64), Sort::Uninterpreted("PbLit".to_string()));
    s.try_declare_datatype(&DatatypeSort::new(
        "PbTerm",
        vec![DatatypeConstructor::new(
            "PbTerm_PbTerm",
            vec![
                DatatypeField::new("PbTerm_PbTerm_coeff", Sort::bitvec(128)),
                DatatypeField::new("PbTerm_PbTerm_lits", lits_array),
            ],
        )],
    ))
    .unwrap();

    let res_sort = Sort::Uninterpreted(res_name.to_string());
    let terms_arr = Sort::array(Sort::bitvec(64), Sort::Uninterpreted("PbTerm".to_string()));
    let assign_arr = Sort::array(Sort::bitvec(64), Sort::Bool);

    let terms = s.declare_const("terms", terms_arr.clone());
    let assignment = s.declare_const("assignment", assign_arr.clone());
    let result = s.declare_const("result", res_sort.clone());
    let seed_terms = s.declare_const("__seed_terms", Sort::Uninterpreted("PbTerm".to_string()));
    let seed_assign = s.declare_const("__seed_assignment", Sort::Bool);
    let checked = s.declare_fun(
        "eval_terms_checked",
        &[terms_arr.clone(), assign_arr.clone()],
        res_sort.clone(),
    );
    let saturating = s.declare_fun(
        "eval_terms_saturating",
        &[terms_arr.clone(), assign_arr.clone()],
        res_sort.clone(),
    );

    let sat_app = s.apply(&saturating, &[terms, assignment]);
    let chk_app = s.apply(&checked, &[terms, assignment]);

    // Top-level assertions: ground seeds and the concrete body binding.
    let i0 = s.bv_const_u64(0, 64);
    let sel_a = s.select(assignment, i0);
    let ga = s.eq(sel_a, seed_assign);
    s.assert_term(ga);
    let sel_t = s.select(terms, i0);
    let gt = s.eq(sel_t, seed_terms);
    s.assert_term(gt);
    let eqd = s.eq(sat_app, chk_app);
    let diseq = s.not(eqd);

    let body_binding = s.eq(result, sat_app);
    (s, body_binding, diseq)
}

#[test]
fn datatype_valued_uf_disequality_with_assumption_binding_is_sat() {
    let (mut pushed_solver, pushed_body, pushed_diseq) = datatype_valued_uf_problem();
    pushed_solver.assert_term(pushed_body);

    // TrustVC's ordinary obligation path carries the body at base scope, then
    // asserts the refutation in a pushed frame.  Exercise that incremental
    // publication path before the assumption control below: both authored
    // equalities validate, and the independent gate must read the same concrete
    // constructor-valued ground-UF table that `(get-model)` publishes.
    pushed_solver.try_push().unwrap();
    pushed_solver.assert_term(pushed_diseq);
    let pushed = pushed_solver.check_sat_with_details();
    assert!(
        pushed.result.result().is_sat(),
        "pushed datatype-UF distinguishability must retain its genuine SAT; got {:?} ({:?})",
        pushed.result.result(),
        pushed.unknown_diagnostic,
    );
    assert!(
        pushed.verification.sat_model_validated,
        "pushed SAT must carry sealed model-validation evidence: {pushed:#?}"
    );
    pushed_solver.try_pop().unwrap();

    // Preserve the original assumption-rooted completion control in a fresh
    // context: the `result == saturating(..)` body binding exists only in the
    // assumption, while the distinct checked result is a base assertion.
    let (mut s, body_binding, diseq) = datatype_valued_uf_problem();
    s.assert_term(diseq);
    let r = s.check_sat_assuming(&[body_binding]);
    assert_eq!(
        format!("{:?}", r.result()),
        "Sat",
        "two distinct Result-valued UF applications must be distinguishable (concrete \
         datatype model), not unknown"
    );
    assert!(
        r.was_model_validated(),
        "SAT must carry sealed model-validation evidence for TrustVC consumers"
    );
    drop(r);

    let model = s
        .try_get_model_str()
        .expect("accepted SAT must retain a printable concrete model");
    assert!(
        model.contains("Result_Ok") || model.contains("Result_Err"),
        "model must contain a concrete Result constructor: {model}"
    );
    assert!(
        model.contains("(define-fun eval_terms_saturating"),
        "model omitted the saturating UF interpretation: {model}"
    );
    assert!(
        model.contains("(define-fun eval_terms_checked"),
        "model omitted the checked UF interpretation: {model}"
    );
    assert!(
        !model.contains("@Result"),
        "opaque Result carrier token leaked into the public model: {model}"
    );
}

/// A pushed, redundant positive equality can become structurally ground only
/// after datatype model completion.  The datatype-array performance shortcut
/// must not mask that final independent observation: strict consumers require
/// a sealed SAT witness even when either operand is selector-observed.
#[test]
fn pushed_observed_datatype_uf_equality_is_validated_sat() {
    let mut s = Solver::new(Logic::All);
    s.try_declare_datatype(&DatatypeSort::new(
        "ObservedArg",
        vec![DatatypeConstructor::new(
            "ObservedArg_mk",
            vec![DatatypeField::new("ObservedArg_value", Sort::bitvec(8))],
        )],
    ))
    .unwrap();
    s.try_declare_datatype(&DatatypeSort::new(
        "ObservedResult",
        vec![
            DatatypeConstructor::new(
                "ObservedResult_ok",
                vec![DatatypeField::new(
                    "ObservedResult_value",
                    Sort::bitvec(128),
                )],
            ),
            DatatypeConstructor::new("ObservedResult_err", vec![]),
        ],
    ))
    .unwrap();

    let arg_sort = Sort::array(
        Sort::bitvec(64),
        Sort::Uninterpreted("ObservedArg".to_string()),
    );
    let bools_sort = Sort::array(Sort::bitvec(64), Sort::Bool);
    let result_sort = Sort::Uninterpreted("ObservedResult".to_string());
    let args = s.declare_const("observed_args", arg_sort.clone());
    let bools = s.declare_const("observed_bools", bools_sort.clone());
    let result = s.declare_const("observed_result", result_sort.clone());
    let checked = s.declare_fun("observed_checked", &[arg_sort, bools_sort], result_sort);
    let checked_app = s.apply(&checked, &[args, bools]);

    // Make `result` non-opaque to the datatype discipline while keeping the
    // query satisfiable.  This is the shape that reaches TrustVC from a real
    // Result-returning body whose constructor payload is observable.
    let observed_value = s.datatype_selector("ObservedResult_value", result, Sort::bitvec(128));
    let zero = s.bv_const_u64(0, 128);
    let value_is_zero = s.eq(observed_value, zero);
    s.assert_term(value_is_zero);

    let body = s.eq(result, checked_app);
    s.assert_term(body);
    s.try_push().unwrap();
    s.assert_term(body);
    let details = s.check_sat_with_details();
    assert!(
        details.result.result().is_sat(),
        "completed pushed equality must remain SAT, got {:?} ({:?})",
        details.result.result(),
        details.unknown_diagnostic,
    );
    assert!(
        details.verification.sat_model_validated,
        "completed pushed equality must carry sealed validation: {details:#?}"
    );
    s.try_pop().unwrap();
}

/// SOUNDNESS: applications of one datatype-valued UF must obey congruence.
/// Equal arguments can never be completed to distinct datatype values.
#[test]
fn same_datatype_uf_at_equal_bv_arguments_is_not_false_sat() {
    assert_ne!(
        verdict(
            r#"
        (set-logic ALL)
        (declare-datatypes ((D 0)) (((D0) (D1))))
        (declare-fun f ((_ BitVec 2)) D)
        (declare-const i (_ BitVec 2))
        (declare-const j (_ BitVec 2))
        (assert (= i j))
        (assert (not (= (f i) (f j))))
        (check-sat)
    "#
        ),
        "sat",
        "congruent applications of one UF head cannot be distinguished"
    );
}

/// SOUNDNESS: two syntactically different reads at model-equal indices denote
/// one array cell and cannot be colored independently.
#[test]
fn datatype_selects_at_equal_bv_indices_are_not_false_sat() {
    assert_ne!(
        verdict(
            r#"
        (set-logic ALL)
        (declare-datatypes ((D 0)) (((D0) (D1))))
        (declare-const a (Array (_ BitVec 2) D))
        (declare-const i (_ BitVec 2))
        (declare-const j (_ BitVec 2))
        (declare-const x D)
        (declare-const y D)
        (assert (= i j))
        (assert (= x (select a i)))
        (assert (= y (select a j)))
        (assert (not (= x y)))
        (check-sat)
    "#
        ),
        "sat",
        "equal-index reads from one array cannot be completed independently"
    );
}

/// SOUNDNESS: a singleton datatype has exactly one inhabitant even when two
/// distinct UF heads make its values opaque to the eager BV path.
#[test]
fn singleton_datatype_uf_disequality_is_not_false_sat() {
    assert_ne!(
        verdict(
            r#"
        (set-logic ALL)
        (declare-datatypes ((Only 0)) (((only))))
        (declare-fun f ((_ BitVec 1)) Only)
        (declare-fun g ((_ BitVec 1)) Only)
        (assert (not (= (f #b0) (g #b0))))
        (check-sat)
    "#
        ),
        "sat",
        "completion cannot fabricate two inhabitants of a singleton datatype"
    );
}

/// A completion value for a datatype-returning UF is still governed by UF
/// congruence. Equal arguments make the two applications equal, so a
/// disequality between them must never be published as SAT.
#[test]
fn datatype_valued_congruent_uf_apps_not_false_sat() {
    let mut s = Solver::new(Logic::All);
    let dt_name = "CongruenceBox";
    s.try_declare_datatype(&DatatypeSort::new(
        dt_name,
        vec![DatatypeConstructor::new(
            "CongruenceBox_mk",
            vec![DatatypeField::new("CongruenceBox_value", Sort::bitvec(8))],
        )],
    ))
    .unwrap();

    let box_sort = Sort::Uninterpreted(dt_name.to_string());
    let x = s.declare_const("congruence_x", Sort::bitvec(8));
    let y = s.declare_const("congruence_y", Sort::bitvec(8));
    let f = s.declare_fun("congruence_box_f", &[Sort::bitvec(8)], box_sort.clone());
    let fx = s.apply(&f, &[x]);
    let fy = s.apply(&f, &[y]);
    let args_equal = s.eq(x, y);
    s.assert_term(args_equal);
    let results_equal = s.eq(fx, fy);
    let results_distinct = s.not(results_equal);
    s.assert_term(results_distinct);

    let result = s.check_sat();
    assert_ne!(
        format!("{:?}", result.result()),
        "Sat",
        "datatype completion must preserve congruence for equal UF arguments"
    );
}

/// A single-constructor datatype is injective in its observed field. The
/// completion pass may choose values only for genuinely free fields; it must
/// not overwrite two equal selector observations to manufacture a UF-result
/// disequality.
#[test]
fn datatype_valued_uf_disequality_with_equal_observed_fields_not_false_sat() {
    let mut s = Solver::new(Logic::All);
    let dt_name = "ObservedBox";
    s.try_declare_datatype(&DatatypeSort::new(
        dt_name,
        vec![DatatypeConstructor::new(
            "ObservedBox_mk",
            vec![DatatypeField::new("ObservedBox_value", Sort::bitvec(8))],
        )],
    ))
    .unwrap();

    let box_sort = Sort::Uninterpreted(dt_name.to_string());
    let arg = s.bv_const_u64(0, 8);
    let f = s.declare_fun("observed_box_f", &[Sort::bitvec(8)], box_sort.clone());
    let g = s.declare_fun("observed_box_g", &[Sort::bitvec(8)], box_sort);
    let fx = s.apply(&f, &[arg]);
    let gx = s.apply(&g, &[arg]);
    let f_value = s.datatype_selector("ObservedBox_value", fx, Sort::bitvec(8));
    let g_value = s.datatype_selector("ObservedBox_value", gx, Sort::bitvec(8));
    let zero = s.bv_const_u64(0, 8);
    let f_is_zero = s.eq(f_value, zero);
    let g_is_zero = s.eq(g_value, zero);
    s.assert_term(f_is_zero);
    s.assert_term(g_is_zero);
    let results_equal = s.eq(fx, gx);
    let results_distinct = s.not(results_equal);
    s.assert_term(results_distinct);

    let result = s.check_sat();
    assert_ne!(
        format!("{:?}", result.result()),
        "Sat",
        "datatype completion must not fabricate differences in observed fields"
    );
}

/// #array-select-congruence-gate — SOUNDNESS. The general model-based
/// select-congruence gate closes the eager array encoding's derived-equal-index
/// hole for an UNINTERPRETED element sort. `(bvadd i 1) = (bvadd j 1)` forces
/// `i = j`, so `(select A i)` and `(select A j)` denote the SAME cell and
/// `(not (= (select A i) (select A j)))` is UNSAT. The eager bit-blast does not
/// tie the two reads at the DERIVED-equal index, so it previously returned a
/// select-congruence-violating model and reported `sat` — a false SAT. The gate
/// now detects the definite violation (two reads on one array identity class at
/// one evaluated index with incompatible element values) and degrades to a
/// sound `unknown`; ay must NEVER answer `sat` here.
#[test]
fn uninterpreted_element_derived_index_select_congruence_not_false_sat() {
    let v = verdict(
        r#"
        (set-logic ALL)
        (declare-sort E 0)
        (declare-const A (Array (_ BitVec 3) E))
        (declare-const i (_ BitVec 3))
        (declare-const j (_ BitVec 3))
        (assert (= (bvadd i #b001) (bvadd j #b001)))
        (assert (not (= (select A i) (select A j))))
        (check-sat)
    "#,
    );
    assert_ne!(
        v, "sat",
        "select-congruence violation at a derived-equal index must not be reported sat"
    );
}

/// #dt-array-cegar — COMPLETENESS. The CEGAR refine loop drives the
/// uninterpreted-element derived-index disequality to a PROVEN `unsat`: the
/// general select-congruence gate distills the tautology
/// `(=> (= i j) (= (select A i) (select A j)))`, and re-solving with it
/// installed contradicts the asserted `(select A i) != (select A j)` (since
/// `(bvadd i 1) = (bvadd j 1)` forces `i = j`). This was a sound `unknown`
/// before CEGAR. Runs in non-proof mode (the test harness default), where the
/// refine loop is active.
#[test]
fn uninterpreted_element_derived_index_cegar_proves_unsat() {
    let v = verdict(
        r#"
        (set-logic ALL)
        (declare-sort E 0)
        (declare-const A (Array (_ BitVec 3) E))
        (declare-const i (_ BitVec 3))
        (declare-const j (_ BitVec 3))
        (assert (= (bvadd i #b001) (bvadd j #b001)))
        (assert (not (= (select A i) (select A j))))
        (check-sat)
    "#,
    );
    assert_eq!(
        v, "unsat",
        "CEGAR must refine the derived-index disequality to a proven unsat"
    );
}

/// Datatype cells obey the same derived-index select congruence as scalar and
/// free-sort cells. Opaque datatype completion must not turn the impossible
/// disequality into a published SAT witness.
#[test]
fn datatype_element_derived_index_select_congruence_not_false_sat() {
    let v = verdict(
        r#"
        (set-logic ALL)
        (declare-datatype IndexCell ((IndexCell_mk (IndexCell_value (_ BitVec 8)))))
        (declare-const A (Array (_ BitVec 3) IndexCell))
        (declare-const i (_ BitVec 3))
        (declare-const j (_ BitVec 3))
        (assert (= (bvadd i #b001) (bvadd j #b001)))
        (assert (not (= (select A i) (select A j))))
        (check-sat)
    "#,
    );
    assert_ne!(
        v, "sat",
        "datatype reads at derived-equal indices must remain congruent"
    );
}

/// A field observed through a datatype-valued array read is semantic authority,
/// not completion slack. The structured array cell must round-trip with that
/// exact observed field and permit the genuine model.
#[test]
fn datatype_array_observed_field_read_is_sat() {
    assert_eq!(
        verdict(
            r#"
        (set-logic ALL)
        (declare-datatype ReadCell ((ReadCell_mk (ReadCell_value (_ BitVec 8)))))
        (declare-const A (Array (_ BitVec 3) ReadCell))
        (declare-const seed ReadCell)
        (assert (= seed (select A #b000)))
        (assert (= (ReadCell_value seed) #x2a))
        (check-sat)
    "#,
        ),
        "sat"
    );
}
