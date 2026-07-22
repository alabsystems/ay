// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! API compatibility canary tests for ay downstream consumers.
//!
//! These tests assert the stable shape of public types that downstream consumers depend on. Any change to variant names, field names,
//! or type signatures on these types will cause a canary test failure BEFORE
//! the change reaches consumers.
//!
//! Part of #3030: downstream API canary for public-result changes.

use ay_bindings::{AYProgram, Constraint, Expr, ExprValue, Sort, SortInner};

// ── ay-bindings public types ──────────────────────────────────────────

/// Canary: Sort constructors and SortInner variants that consumers use.
#[test]
fn canary_sort_variants() {
    let _bool = Sort::bool();
    let _int = Sort::int();
    let _real = Sort::real();
    let _bv32 = Sort::bv32();
    let _bv64 = Sort::bv64();
    let _bv = Sort::bitvec(8);
    let _arr = Sort::array(Sort::int(), Sort::bool());
    let _string = Sort::string();
    let _reglan = Sort::reglan();

    match _bool.inner() {
        SortInner::Bool => {}
        SortInner::Int => {}
        SortInner::Real => {}
        SortInner::BitVec(_) => {}
        SortInner::Array(_) => {}
        SortInner::String => {}
        SortInner::RegLan => {}
        SortInner::Datatype(_) => {}
        SortInner::FloatingPoint(_, _) => {}
        SortInner::Uninterpreted(_) => {}
        SortInner::Seq(_) => {}
        _ => {} // non_exhaustive forward-compatible
    }
}

/// Canary: ExprValue variants that consumers construct/match.
#[test]
fn canary_expr_value_variants() {
    let x = Expr::bool_const(true);
    match x.value() {
        ExprValue::Var { .. } => {}
        ExprValue::BoolConst(_) => {}
        ExprValue::IntConst(_) => {}
        ExprValue::RealConst(_) => {}
        ExprValue::BitVecConst { .. } => {}
        ExprValue::Not(_) => {}
        ExprValue::And(_) => {}
        ExprValue::Or(_) => {}
        ExprValue::Implies(_, _) => {}
        ExprValue::Eq(_, _) => {}
        ExprValue::Distinct(_) => {}
        ExprValue::Ite { .. } => {}
        _ => {} // non_exhaustive forward-compatible
    }
}

/// Canary: Constraint constructors that consumers use.
#[test]
fn canary_constraint_api() {
    let _set_logic = Constraint::set_logic("QF_BV");
    let _declare = Constraint::declare_const("x", Sort::bv32());
    let _assert = Constraint::assert(Expr::bool_const(true));
    let _check_sat = Constraint::check_sat();
    let _push = Constraint::push();
    let _pop = Constraint::pop(1);
}

/// Canary: AYProgram construction and methods.
#[test]
fn canary_ayprogram_api() {
    let mut prog = AYProgram::qf_bv();
    let x = prog.declare_const("x", Sort::bv32());
    prog.assert(x.eq(Expr::bitvec_const(0i32, 32)));
    prog.check_sat();
    let smt2 = prog.to_string();
    assert!(smt2.contains("(check-sat)"));

    let _horn = AYProgram::horn();
    let _lia = AYProgram::qf_lia();
    let _lra = AYProgram::qf_lra();
}

/// Canary: format_symbol re-export works.
#[test]
fn canary_format_symbol() {
    assert_eq!(ay_bindings::format_symbol("test"), "test");
}

/// Canary: panic_payload_to_string re-export works.
#[test]
fn canary_panic_payload_reexport() {
    let payload: Box<dyn std::any::Any + Send> = Box::new("test error");
    let msg = ay_bindings::panic_payload_to_string(&*payload);
    assert_eq!(msg, "test error");
}

// ── ay-bindings execute_direct types (model-checker-consumer consumer) ──────────────────

#[cfg(feature = "direct")]
mod direct_canary {
    use ay_bindings::execute_direct::{
        ExecuteCounterexample, ExecuteResult, ExecuteTypedResult, ExecuteValueMap, ModelValue,
    };

    /// Canary: ExecuteResult variants that model-checker-consumer matches on.
    #[test]
    fn canary_execute_result_variants() {
        let verified = ExecuteResult::Verified;
        let cex = ExecuteResult::Counterexample {
            model: ExecuteValueMap::default(),
            values: ExecuteValueMap::default(),
        };
        let fallback = ExecuteResult::NeedsFallback("reason".into());
        let unknown = ExecuteResult::Unknown("reason".into());

        match &verified {
            ExecuteResult::Verified => {}
            ExecuteResult::Counterexample { model, values } => {
                let _ = (model, values);
            }
            ExecuteResult::NeedsFallback(reason) => {
                let _ = reason;
            }
            ExecuteResult::Unknown(reason) => {
                let _ = reason;
            }
            _ => {} // non_exhaustive forward-compatible
        }

        // Verify Debug is implemented (consumers log results)
        let _ = format!("{:?}", verified);
        let _ = format!("{:?}", cex);
        let _ = format!("{:?}", fallback);
        let _ = format!("{:?}", unknown);
    }

    /// Canary: typed execute_direct result and model-value re-export stay stable.
    #[test]
    fn canary_execute_typed_result_variants() {
        let typed_cex = ExecuteCounterexample::new(
            [("x".to_string(), ModelValue::Bool(true))]
                .into_iter()
                .collect(),
            ExecuteValueMap::default(),
        );
        let verified = ExecuteTypedResult::Verified;
        let cex = ExecuteTypedResult::Counterexample(typed_cex);
        let fallback = ExecuteTypedResult::NeedsFallback("reason".into());
        let unknown = ExecuteTypedResult::Unknown("reason".into());

        match &verified {
            ExecuteTypedResult::Verified => {}
            ExecuteTypedResult::Counterexample(counterexample) => {
                let _ = (&counterexample.model, &counterexample.values);
            }
            ExecuteTypedResult::NeedsFallback(reason) => {
                let _ = reason;
            }
            ExecuteTypedResult::Unknown(reason) => {
                let _ = reason;
            }
            _ => {}
        }

        match &cex {
            ExecuteTypedResult::Counterexample(counterexample) => {
                assert!(matches!(
                    counterexample.model.get("x"),
                    Some(ModelValue::Bool(true))
                ));
            }
            other => panic!("expected typed counterexample variant, got {other:?}"),
        }

        let _ = format!("{:?}", verified);
        let _ = format!("{:?}", cex);
        let _ = format!("{:?}", fallback);
        let _ = format!("{:?}", unknown);
    }
}
