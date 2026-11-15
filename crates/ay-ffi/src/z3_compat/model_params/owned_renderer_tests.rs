// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
use super::*;

fn decision(ctx: &mut Z3Context) -> ay_dpll::api::TacticDecision {
    let no = ctx.solver.bool_const(false);
    let operation = ctx.solver.begin_tactic_operation_for_check().unwrap();
    let goal = ctx
        .solver
        .apply_tactic_subgoals_in_operation(
            &operation,
            &ay_dpll::api::Tactic::FieldSat,
            &[no],
            0,
            None,
        )
        .unwrap()
        .remove(0);
    ctx.solver
        .check_converted_tactic_goal_in_operation(
            operation,
            goal.model_converter.as_ref().unwrap(),
            &goal.formulas,
            &[],
        )
        .unwrap()
}

#[test]
fn converted_renderer_metadata_uses_original_stop_and_exact_source() {
    // SAFETY: this test exclusively owns the context and destroys it only
    // after all native decision/read guards and references have been dropped.
    unsafe {
        let cfg = super::super::Z3_mk_config();
        let raw = super::super::Z3_mk_context(cfg);
        super::super::Z3_del_config(cfg);
        {
            let ctx = &mut *raw;
            let nested = Sort::array(Sort::bitvec(8), Sort::array(Sort::Int, Sort::Real));
            ctx.solver.declare_const("nested", nested.clone());
            let first = decision(ctx);
            assert!(first.result.is_unsat());
            let copied = counted_declared_sorts(ctx, &first).unwrap();
            assert_eq!(copied.get("nested"), Some(&nested));
            drop(copied);
            ctx.solver.interrupt();
            assert!(counted_declared_sorts(ctx, &first).is_none());
            ctx.solver.clear_interrupt();
            assert!(
                counted_declared_sorts(ctx, &first).is_none(),
                "same owner cannot renew"
            );
            drop(first);
            let fresh = decision(ctx);
            assert_eq!(
                counted_declared_sorts(ctx, &fresh).unwrap().get("nested"),
                Some(&nested)
            );
            ctx.solver.declare_const("later", Sort::Bool);
            assert!(
                counted_declared_sorts(ctx, &fresh).is_none(),
                "foreign source is not adopted"
            );
            drop(fresh);
            let final_read = decision(ctx);
            assert_eq!(
                counted_declared_sorts(ctx, &final_read)
                    .unwrap()
                    .get("later"),
                Some(&Sort::Bool)
            );
        }
        super::super::Z3_del_context(raw);
    }
}

#[test]
fn converted_renderer_keeps_internal_model_keys_and_authored_public_names() {
    use super::super::*;
    use std::ffi::CStr;
    // SAFETY: the test exclusively owns all handles and the context; cached
    // strings remain live until its final context destruction.
    unsafe {
        let cfg = Z3_mk_config();
        let raw = Z3_mk_context(cfg);
        Z3_del_config(cfg);
        let simp = Z3_mk_simplifier(raw, c"solve-eqs".as_ptr());
        let solver = Z3_solver_add_simplifier(raw, Z3_mk_solver(raw), simp);
        let ints = Z3_mk_int_sort(raw);
        let x = Z3_mk_const(raw, Z3_mk_string_symbol(raw, c"__db0".as_ptr()), ints);
        let three = Z3_mk_int(raw, 3, ints);
        let original = Z3_mk_eq(raw, x, three);
        Z3_solver_assert(raw, solver, original);
        assert_eq!(Z3_solver_check(raw, solver), Z3_L_TRUE);
        let stored = &*solver;
        let (identity, _) = stored
            .last_model
            .as_ref()
            .unwrap()
            .iter_ints()
            .next()
            .unwrap();
        let snapshot = stored.last_model_text.as_ref().unwrap();
        let parsed = ay_frontend::sexp::parse_sexp(snapshot).unwrap();
        let row = parsed
            .as_list()
            .unwrap()
            .iter()
            .find(|row| define_fun_name(row) == Some(identity))
            .unwrap()
            .as_list()
            .unwrap();
        assert_eq!(row[1].to_raw_string(), ay_core::quote_symbol(identity));
        let model = Z3_solver_get_model(raw, solver);
        let mut value = 0;
        assert!(Z3_model_eval(raw, model, original, false, &mut value));
        assert_eq!(Z3_get_bool_value(raw, value), Z3_L_TRUE);
        let output = Z3_model_to_string(raw, model);
        assert!(!output.is_null());
        let output = CStr::from_ptr(output).to_str().unwrap();
        assert!(output.contains("__db0"), "{output}");
        assert!(!output.contains("(:var "), "{output}");
        Z3_del_context(raw);
    }
}
