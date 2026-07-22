// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Bridge between CHC expression types and the ay-jit expression evaluator.
//!
//! Implements the `ExprLike` trait for `ChcExpr`, enabling JIT compilation
//! of CHC expression evaluation. This is the glue between ay-chc expression
//! ASTs and ay-jit native code generation.

use std::sync::Arc;

use ay_jit::expr_eval::{ExprLike, ExprOpcode, VarMapping};

use super::{maybe_grow_expr_stack, ChcExpr, ChcOp, ChcSort};

impl ExprLike for ChcExpr {
    fn is_jit_compilable(&self) -> bool {
        maybe_grow_expr_stack(|| match self {
            Self::Bool(_) | Self::Int(_) => true,
            Self::Var(v) => matches!(v.sort, ChcSort::Bool | ChcSort::Int),
            Self::Op(op, args) => {
                if !is_compilable_op(op) {
                    return false;
                }
                args.iter().all(|a| a.is_jit_compilable())
            }
            // BitVec, Real, PredicateApp, FuncApp, arrays etc. are not compilable
            _ => false,
        })
    }

    fn flatten_into(&self, opcodes: &mut Vec<ExprOpcode>, var_mapping: &mut VarMapping) -> bool {
        flatten_expr(self, opcodes, var_mapping)
    }

    fn is_boolean(&self) -> bool {
        match self {
            Self::Bool(_) => true,
            Self::Var(v) => v.sort == ChcSort::Bool,
            Self::Op(op, _) => matches!(
                op,
                ChcOp::Not
                    | ChcOp::And
                    | ChcOp::Or
                    | ChcOp::Implies
                    | ChcOp::Iff
                    | ChcOp::Eq
                    | ChcOp::Ne
                    | ChcOp::Lt
                    | ChcOp::Le
                    | ChcOp::Gt
                    | ChcOp::Ge
            ),
            _ => false,
        }
    }
}

/// Check if a ChcOp is supported by the JIT compiler.
fn is_compilable_op(op: &ChcOp) -> bool {
    matches!(
        op,
        ChcOp::Not
            | ChcOp::And
            | ChcOp::Or
            | ChcOp::Implies
            | ChcOp::Iff
            | ChcOp::Add
            | ChcOp::Sub
            | ChcOp::Mul
            | ChcOp::Neg
            | ChcOp::Eq
            | ChcOp::Ne
            | ChcOp::Lt
            | ChcOp::Le
            | ChcOp::Gt
            | ChcOp::Ge
            | ChcOp::Ite
    )
}

/// Flatten a ChcExpr into a post-order opcode sequence.
///
/// Returns false if the expression contains unsupported operations.
fn flatten_expr(
    expr: &ChcExpr,
    opcodes: &mut Vec<ExprOpcode>,
    var_mapping: &mut VarMapping,
) -> bool {
    maybe_grow_expr_stack(|| flatten_expr_inner(expr, opcodes, var_mapping))
}

fn flatten_expr_inner(
    expr: &ChcExpr,
    opcodes: &mut Vec<ExprOpcode>,
    var_mapping: &mut VarMapping,
) -> bool {
    match expr {
        ChcExpr::Bool(b) => {
            opcodes.push(ExprOpcode::PushBool(*b));
            true
        }

        ChcExpr::Int(n) => {
            // i128-lockstep: the JIT evaluates in i64; constants beyond i64
            // range decline compilation (fail-closed fallback to the
            // interpreter), never truncate.
            match i64::try_from(*n) {
                Ok(v) => {
                    opcodes.push(ExprOpcode::PushInt(v));
                    true
                }
                Err(_) => false,
            }
        }

        ChcExpr::Var(v) => match v.sort {
            ChcSort::Int => {
                let idx = var_mapping.get_or_insert_int(&v.name);
                opcodes.push(ExprOpcode::LoadIntVar(idx));
                true
            }
            ChcSort::Bool => {
                let idx = var_mapping.get_or_insert_bool(&v.name);
                opcodes.push(ExprOpcode::LoadBoolVar(idx));
                true
            }
            _ => false,
        },

        ChcExpr::Op(ChcOp::Not, args) if args.len() == 1 => {
            if !flatten_expr(&args[0], opcodes, var_mapping) {
                return false;
            }
            opcodes.push(ExprOpcode::Not);
            true
        }

        // n-ary connectives: the opcode arity is u16, so wider connectives
        // must fail flattening (interpreter fallback) instead of silently
        // truncating the operand count.
        ChcExpr::Op(ChcOp::And, args) => {
            let Ok(arity) = u16::try_from(args.len()) else {
                return false;
            };
            flatten_nary_bool(args, ExprOpcode::And(arity), opcodes, var_mapping)
        }

        ChcExpr::Op(ChcOp::Or, args) => {
            let Ok(arity) = u16::try_from(args.len()) else {
                return false;
            };
            flatten_nary_bool(args, ExprOpcode::Or(arity), opcodes, var_mapping)
        }

        ChcExpr::Op(ChcOp::Implies, args) if args.len() == 2 => {
            if !flatten_expr(&args[0], opcodes, var_mapping) {
                return false;
            }
            if !flatten_expr(&args[1], opcodes, var_mapping) {
                return false;
            }
            opcodes.push(ExprOpcode::Implies);
            true
        }

        ChcExpr::Op(ChcOp::Iff, args) if args.len() == 2 => {
            // a <=> b is (a = b) for booleans
            if !flatten_expr(&args[0], opcodes, var_mapping) {
                return false;
            }
            if !flatten_expr(&args[1], opcodes, var_mapping) {
                return false;
            }
            opcodes.push(ExprOpcode::CmpEq);
            true
        }

        ChcExpr::Op(ChcOp::Eq, args) if args.len() == 2 => {
            flatten_binary_cmp(&args[0], &args[1], ExprOpcode::CmpEq, opcodes, var_mapping)
        }

        ChcExpr::Op(ChcOp::Ne, args) if args.len() == 2 => {
            flatten_binary_cmp(&args[0], &args[1], ExprOpcode::CmpNe, opcodes, var_mapping)
        }

        ChcExpr::Op(ChcOp::Lt, args) if args.len() == 2 => {
            flatten_binary_cmp(&args[0], &args[1], ExprOpcode::CmpLt, opcodes, var_mapping)
        }

        ChcExpr::Op(ChcOp::Le, args) if args.len() == 2 => {
            flatten_binary_cmp(&args[0], &args[1], ExprOpcode::CmpLe, opcodes, var_mapping)
        }

        ChcExpr::Op(ChcOp::Gt, args) if args.len() == 2 => {
            flatten_binary_cmp(&args[0], &args[1], ExprOpcode::CmpGt, opcodes, var_mapping)
        }

        ChcExpr::Op(ChcOp::Ge, args) if args.len() == 2 => {
            flatten_binary_cmp(&args[0], &args[1], ExprOpcode::CmpGe, opcodes, var_mapping)
        }

        ChcExpr::Op(ChcOp::Add, args) => {
            flatten_nary_arith(args, ExprOpcode::Add, opcodes, var_mapping)
        }

        ChcExpr::Op(ChcOp::Sub, args) if !args.is_empty() => {
            if args.len() == 1 {
                // Unary minus
                if !flatten_expr(&args[0], opcodes, var_mapping) {
                    return false;
                }
                opcodes.push(ExprOpcode::Neg);
                return true;
            }
            // Binary/n-ary: a - b - c = (a - b) - c
            if !flatten_expr(&args[0], opcodes, var_mapping) {
                return false;
            }
            for arg in &args[1..] {
                if !flatten_expr(arg, opcodes, var_mapping) {
                    return false;
                }
                opcodes.push(ExprOpcode::Sub);
            }
            true
        }

        ChcExpr::Op(ChcOp::Mul, args) => {
            flatten_nary_arith(args, ExprOpcode::Mul, opcodes, var_mapping)
        }

        ChcExpr::Op(ChcOp::Neg, args) if args.len() == 1 => {
            if !flatten_expr(&args[0], opcodes, var_mapping) {
                return false;
            }
            opcodes.push(ExprOpcode::Neg);
            true
        }

        ChcExpr::Op(ChcOp::Div, args) if args.len() == 2 => {
            if !flatten_expr(&args[0], opcodes, var_mapping) {
                return false;
            }
            if !flatten_expr(&args[1], opcodes, var_mapping) {
                return false;
            }
            opcodes.push(ExprOpcode::Div);
            true
        }

        ChcExpr::Op(ChcOp::Mod, args) if args.len() == 2 => {
            if !flatten_expr(&args[0], opcodes, var_mapping) {
                return false;
            }
            if !flatten_expr(&args[1], opcodes, var_mapping) {
                return false;
            }
            opcodes.push(ExprOpcode::Mod);
            true
        }

        ChcExpr::Op(ChcOp::Ite, args) if args.len() == 3 => {
            // Push cond, then_val, else_val in order
            if !flatten_expr(&args[0], opcodes, var_mapping) {
                return false;
            }
            if !flatten_expr(&args[1], opcodes, var_mapping) {
                return false;
            }
            if !flatten_expr(&args[2], opcodes, var_mapping) {
                return false;
            }
            opcodes.push(ExprOpcode::Ite);
            true
        }

        _ => false, // Unsupported expression type
    }
}

/// Flatten n-ary boolean connective (AND/OR).
fn flatten_nary_bool(
    args: &[Arc<ChcExpr>],
    op: ExprOpcode,
    opcodes: &mut Vec<ExprOpcode>,
    var_mapping: &mut VarMapping,
) -> bool {
    for arg in args {
        if !flatten_expr(arg, opcodes, var_mapping) {
            return false;
        }
    }
    opcodes.push(op);
    true
}

/// Flatten binary comparison.
fn flatten_binary_cmp(
    a: &ChcExpr,
    b: &ChcExpr,
    op: ExprOpcode,
    opcodes: &mut Vec<ExprOpcode>,
    var_mapping: &mut VarMapping,
) -> bool {
    if !flatten_expr(a, opcodes, var_mapping) {
        return false;
    }
    if !flatten_expr(b, opcodes, var_mapping) {
        return false;
    }
    opcodes.push(op);
    true
}

/// Flatten n-ary arithmetic (Add/Mul).
fn flatten_nary_arith(
    args: &[Arc<ChcExpr>],
    op: ExprOpcode,
    opcodes: &mut Vec<ExprOpcode>,
    var_mapping: &mut VarMapping,
) -> bool {
    if args.is_empty() {
        // Identity: Add() = 0, Mul() = 1
        opcodes.push(match op {
            ExprOpcode::Add => ExprOpcode::PushInt(0),
            ExprOpcode::Mul => ExprOpcode::PushInt(1),
            _ => return false,
        });
        return true;
    }

    if !flatten_expr(&args[0], opcodes, var_mapping) {
        return false;
    }
    for arg in &args[1..] {
        if !flatten_expr(arg, opcodes, var_mapping) {
            return false;
        }
        opcodes.push(op.clone());
    }
    true
}

#[cfg(test)]
#[cfg(any(target_arch = "aarch64", target_arch = "x86_64"))]
mod tests {
    use super::*;
    use crate::expr::ChcVar;
    use ay_jit::expr_eval::{compile_expr, compile_expr_portable};

    fn make_int_var(name: &str) -> ChcExpr {
        ChcExpr::Var(ChcVar::new(name, ChcSort::Int))
    }

    fn arc(e: ChcExpr) -> Arc<ChcExpr> {
        Arc::new(e)
    }

    #[test]
    fn test_jit_simple_comparison() {
        // x <= 10
        let expr = ChcExpr::Op(
            ChcOp::Le,
            vec![arc(make_int_var("x")), arc(ChcExpr::Int(10))],
        );

        let compiled = compile_expr(&expr)
            .expect("compile error")
            .expect("not compilable");

        // x = 5: 5 <= 10 = true
        let idx = compiled.var_mapping().get("x").expect("x not in mapping");
        let mut vars = vec![0i64; compiled.var_mapping().total_vars() as usize];
        vars[idx as usize] = 5;
        assert_eq!(compiled.evaluate_bool_checked(&vars), Some(true));

        // x = 15: 15 <= 10 = false
        vars[idx as usize] = 15;
        assert_eq!(compiled.evaluate_bool_checked(&vars), Some(false));
    }

    #[test]
    fn test_jit_and_expression() {
        // (x <= 10) AND (y > 0)
        let expr = ChcExpr::Op(
            ChcOp::And,
            vec![
                arc(ChcExpr::Op(
                    ChcOp::Le,
                    vec![arc(make_int_var("x")), arc(ChcExpr::Int(10))],
                )),
                arc(ChcExpr::Op(
                    ChcOp::Gt,
                    vec![arc(make_int_var("y")), arc(ChcExpr::Int(0))],
                )),
            ],
        );

        let compiled = compile_expr(&expr)
            .expect("compile error")
            .expect("not compilable");

        let x_idx = compiled.var_mapping().get("x").expect("x") as usize;
        let y_idx = compiled.var_mapping().get("y").expect("y") as usize;
        let mut vars = vec![0i64; compiled.var_mapping().total_vars() as usize];

        // x=5, y=3: true AND true = true
        vars[x_idx] = 5;
        vars[y_idx] = 3;
        assert_eq!(compiled.evaluate_bool_checked(&vars), Some(true));

        // x=15, y=3: false AND true = false
        vars[x_idx] = 15;
        assert_eq!(compiled.evaluate_bool_checked(&vars), Some(false));
    }

    #[test]
    fn test_jit_arithmetic_expression() {
        // (x + y) * 2 - 1
        let expr = ChcExpr::Op(
            ChcOp::Sub,
            vec![
                arc(ChcExpr::Op(
                    ChcOp::Mul,
                    vec![
                        arc(ChcExpr::Op(
                            ChcOp::Add,
                            vec![arc(make_int_var("x")), arc(make_int_var("y"))],
                        )),
                        arc(ChcExpr::Int(2)),
                    ],
                )),
                arc(ChcExpr::Int(1)),
            ],
        );

        let compiled = compile_expr(&expr)
            .expect("compile error")
            .expect("not compilable");

        let x_idx = compiled.var_mapping().get("x").expect("x") as usize;
        let y_idx = compiled.var_mapping().get("y").expect("y") as usize;
        let mut vars = vec![0i64; compiled.var_mapping().total_vars() as usize];

        // (3 + 5) * 2 - 1 = 15
        vars[x_idx] = 3;
        vars[y_idx] = 5;
        assert_eq!(compiled.evaluate_checked(&vars), Some(15));
    }

    #[test]
    fn test_jit_deep_sum_falls_back_and_evaluates_correctly() {
        // Regression for the aarch64 JIT stack-corruption crash, updated for the
        // 4f94f913 register-allocation rewrite.
        //
        // Native codegen now assigns scratch registers by operand-stack POSITION
        // (reusing them after pops) and fails closed only when the peak
        // operand-stack depth exceeds the scratch file
        // (`NATIVE_EVAL_MAX_OPERAND_DEPTH` == 17 on aarch64). A *wide, shallow*
        // left-deep sum `((v0+v1)+v2)+...` has peak depth 2, so it now compiles
        // NATIVELY and correctly — it is no longer a fallback case.
        //
        // To keep exercising the fail-closed fallback path we use a genuinely
        // DEEP, RIGHT-nested chain `v0 + (v1 + (v2 + ... + v_{N-1}))`: every
        // right operand is evaluated with all its ancestors' results still live,
        // so the peak operand-stack depth equals N. With N well above the
        // 17-register scratch file, native codegen must bail (there is NO spill
        // path — the pre-fix spill is exactly what corrupted the frame record),
        // and `compile_expr_portable` must fall back to the sound interpreter.
        const N: usize = 25; // peak operand-stack depth 25 > 17 (and > 10 on x86_64)
        let mut expr = make_int_var(&format!("v{}", N - 1));
        for i in (0..N - 1).rev() {
            expr = ChcExpr::Op(
                ChcOp::Add,
                vec![arc(make_int_var(&format!("v{i}"))), arc(expr)],
            );
        }

        let evaluator = compile_expr_portable(&expr)
            .expect("portable evaluator should be produced (interpreter fallback)");

        // Must NOT be native: the depth guard fails closed on this deep chain, so
        // the portable evaluator drops to the interpreter rather than emitting
        // spill code that would corrupt the frame record (aarch64) / miscompile
        // (x86_64).
        assert!(
            !evaluator.is_native(),
            "deep expression (peak operand depth {N} > native scratch file) must fall \
             back to the interpreter, not run miscompiled native code"
        );

        // All vars = 1 => sum == N. Must evaluate correctly without crashing.
        let total = evaluator.var_mapping().total_vars() as usize;
        let vars = vec![1i64; total];
        assert_eq!(evaluator.evaluate_checked(&vars), Some(N as i64));
    }

    #[test]
    fn test_jit_not_compilable_bitvec() {
        // BitVec expressions should not be compilable
        let expr = ChcExpr::BitVec(42, 8);
        assert!(!expr.is_jit_compilable());
        let result = compile_expr(&expr).expect("compile error");
        assert!(result.is_none());
    }

    #[test]
    fn test_jit_not_compilable_div_mod() {
        let x = arc(make_int_var("x"));
        let y = arc(make_int_var("y"));

        let div_expr = ChcExpr::Op(ChcOp::Div, vec![x.clone(), y.clone()]);
        assert!(!div_expr.is_jit_compilable());
        assert!(compile_expr(&div_expr).expect("compile error").is_none());

        let mod_expr = ChcExpr::Op(ChcOp::Mod, vec![x, y]);
        assert!(!mod_expr.is_jit_compilable());
        assert!(compile_expr(&mod_expr).expect("compile error").is_none());
    }

    #[test]
    fn test_jit_not_compilable_uninterpreted_applications() {
        let pred_expr = ChcExpr::PredicateApp(
            "Inv".to_string(),
            crate::PredicateId::new(0),
            vec![arc(make_int_var("x"))],
        );
        assert!(!pred_expr.is_jit_compilable());
        assert!(compile_expr(&pred_expr).expect("compile error").is_none());

        let func_expr =
            ChcExpr::FuncApp("f".to_string(), ChcSort::Int, vec![arc(make_int_var("x"))]);
        assert!(!func_expr.is_jit_compilable());
        assert!(compile_expr(&func_expr).expect("compile error").is_none());
    }

    #[test]
    fn test_jit_matches_interpreter() {
        use crate::pdr::implication_cache::SmallModel;
        use crate::smt::SmtValue;
        use ay_core::kani_compat::DetHashMap as FxHashMap;

        // Build expression: (x + y) <= 10 AND (x > 0)
        let expr = ChcExpr::Op(
            ChcOp::And,
            vec![
                arc(ChcExpr::Op(
                    ChcOp::Le,
                    vec![
                        arc(ChcExpr::Op(
                            ChcOp::Add,
                            vec![arc(make_int_var("x")), arc(make_int_var("y"))],
                        )),
                        arc(ChcExpr::Int(10)),
                    ],
                )),
                arc(ChcExpr::Op(
                    ChcOp::Gt,
                    vec![arc(make_int_var("x")), arc(ChcExpr::Int(0))],
                )),
            ],
        );

        // Build SmallModel for interpreter
        let mut smt_model = FxHashMap::default();
        smt_model.insert("x".to_string(), SmtValue::Int(3));
        smt_model.insert("y".to_string(), SmtValue::Int(5));
        let small_model = SmallModel::from_smt_model(&smt_model);

        // Interpreter result
        let interp_result = small_model.evaluate(&expr);

        // JIT result
        let compiled = compile_expr(&expr)
            .expect("compile error")
            .expect("not compilable");
        let x_idx = compiled.var_mapping().get("x").expect("x") as usize;
        let y_idx = compiled.var_mapping().get("y").expect("y") as usize;
        let mut vars = vec![0i64; compiled.var_mapping().total_vars() as usize];
        vars[x_idx] = 3;
        vars[y_idx] = 5;
        let jit_result = compiled.evaluate_bool_checked(&vars);

        assert_eq!(interp_result, jit_result);
    }
}
