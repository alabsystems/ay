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

use ay_dpll::api::{DatatypeConstructor, DatatypeField, DatatypeSort, Logic, Solver, Sort};

#[test]
fn datatype_valued_uf_disequality_with_assumption_binding_is_sat() {
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
    // PbTerm datatype (the array element sort) + ground-seeded element arrays.
    s.try_declare_datatype(&DatatypeSort::new(
        "PbTerm",
        vec![DatatypeConstructor::new(
            "PbTerm_PbTerm",
            vec![DatatypeField::new("PbTerm_PbTerm_coeff", Sort::bitvec(128))],
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

    // Top-level assertions: ground seeds + the datatype disequality.
    let i0 = s.bv_const_u64(0, 64);
    let sel_a = s.select(assignment, i0);
    let ga = s.eq(sel_a, seed_assign);
    s.assert_term(ga);
    let sel_t = s.select(terms, i0);
    let gt = s.eq(sel_t, seed_terms);
    s.assert_term(gt);
    let eqd = s.eq(sat_app, chk_app);
    let diseq = s.not(eqd);
    s.assert_term(diseq);

    // The body binding `result == eval_terms_saturating(..)` as a check_sat_assuming
    // ASSUMPTION (exactly how deductive-checks carries the return-value binding).
    let body_binding = s.eq(result, sat_app);
    let r = s.check_sat_assuming(&[body_binding]);
    assert_eq!(
        format!("{:?}", r.result()),
        "Sat",
        "two distinct Result-valued UF applications must be distinguishable (concrete \
         datatype model), not unknown"
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
