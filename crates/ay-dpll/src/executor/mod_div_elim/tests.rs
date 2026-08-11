// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;
use crate::executor::Executor;
use ay_frontend::parse;
use num_bigint::BigInt;

fn setup_term_store() -> TermStore {
    TermStore::new()
}

// ===== Tests for contains_int_mod_div_by_constant =====

#[test]
fn test_contains_mod_div_empty_formulas() {
    let terms = setup_term_store();
    assert!(!contains_int_mod_div_by_constant(&terms, &[]));
}

#[test]
fn test_contains_mod_div_no_mod_div() {
    let mut terms = setup_term_store();
    let x = terms.mk_fresh_var("x", Sort::Int);
    let y = terms.mk_fresh_var("y", Sort::Int);
    let sum = terms.mk_add(vec![x, y]);

    assert!(!contains_int_mod_div_by_constant(&terms, &[sum]));
}

#[test]
fn test_contains_mod_with_constant_divisor() {
    let mut terms = setup_term_store();
    let x = terms.mk_fresh_var("x", Sort::Int);
    let three = terms.mk_int(BigInt::from(3));
    let mod_expr = terms.mk_mod(x, three);

    assert!(contains_int_mod_div_by_constant(&terms, &[mod_expr]));
}

#[test]
fn test_contains_div_with_constant_divisor() {
    let mut terms = setup_term_store();
    let x = terms.mk_fresh_var("x", Sort::Int);
    let five = terms.mk_int(BigInt::from(5));
    let div_expr = terms.mk_intdiv(x, five);

    assert!(contains_int_mod_div_by_constant(&terms, &[div_expr]));
}

#[test]
fn test_contains_mod_with_variable_divisor_returns_false() {
    let mut terms = setup_term_store();
    let x = terms.mk_fresh_var("x", Sort::Int);
    let y = terms.mk_fresh_var("y", Sort::Int);
    let mod_expr = terms.mk_mod(x, y);

    // mod by variable, not constant - should return false
    assert!(!contains_int_mod_div_by_constant(&terms, &[mod_expr]));
}

#[test]
fn test_contains_nested_mod_div() {
    let mut terms = setup_term_store();
    let x = terms.mk_fresh_var("x", Sort::Int);
    let two = terms.mk_int(BigInt::from(2));
    let mod_expr = terms.mk_mod(x, two);

    // Wrap mod in another expression
    let y = terms.mk_fresh_var("y", Sort::Int);
    let sum = terms.mk_add(vec![mod_expr, y]);

    assert!(contains_int_mod_div_by_constant(&terms, &[sum]));
}

#[test]
fn test_contains_mod_in_ite() {
    let mut terms = setup_term_store();
    let x = terms.mk_fresh_var("x", Sort::Int);
    let three = terms.mk_int(BigInt::from(3));
    let mod_expr = terms.mk_mod(x, three);

    let cond = terms.mk_fresh_var("c", Sort::Bool);
    let zero = terms.mk_int(BigInt::from(0));
    let ite = terms.mk_ite(cond, mod_expr, zero);

    assert!(contains_int_mod_div_by_constant(&terms, &[ite]));
}

// ===== Tests for eliminate_int_mod_div_by_constant =====

#[test]
fn test_eliminate_no_mod_div_unchanged() {
    let mut terms = setup_term_store();
    let x = terms.mk_fresh_var("x", Sort::Int);
    let y = terms.mk_fresh_var("y", Sort::Int);
    let sum = terms.mk_add(vec![x, y]);

    let result = eliminate_int_mod_div_by_constant(&mut terms, &[sum]);

    assert!(result.constraints.is_empty());
    assert_eq!(result.rewritten.len(), 1);
    assert_eq!(result.rewritten[0], sum);
}

#[test]
fn test_eliminate_mod_generates_constraints() {
    let mut terms = setup_term_store();
    let x = terms.mk_fresh_var("x", Sort::Int);
    let three = terms.mk_int(BigInt::from(3));
    let mod_expr = terms.mk_mod(x, three);

    let result = eliminate_int_mod_div_by_constant(&mut terms, &[mod_expr]);

    // Should generate 3 constraints: x = k*q + r, 0 <= r, r < |k|
    assert_eq!(result.constraints.len(), 3);
    assert_eq!(result.rewritten.len(), 1);
    // The rewritten expression should be the remainder variable, not the original
    assert_ne!(result.rewritten[0], mod_expr);
}

#[test]
fn test_eliminate_div_generates_constraints() {
    let mut terms = setup_term_store();
    let x = terms.mk_fresh_var("x", Sort::Int);
    let five = terms.mk_int(BigInt::from(5));
    let div_expr = terms.mk_intdiv(x, five);

    let result = eliminate_int_mod_div_by_constant(&mut terms, &[div_expr]);

    // Should generate 3 constraints: x = k*q + r, 0 <= r, r < |k|
    assert_eq!(result.constraints.len(), 3);
    assert_eq!(result.rewritten.len(), 1);
    // The rewritten expression should be the quotient variable, not the original
    assert_ne!(result.rewritten[0], div_expr);
}

#[test]
fn test_eliminate_mod_by_zero_returns_unconstrained_fresh_var() {
    let mut terms = setup_term_store();
    let x = terms.mk_fresh_var("x", Sort::Int);
    let zero = terms.mk_int(BigInt::from(0));
    let mod_expr = terms.mk_mod(x, zero);

    let result = eliminate_int_mod_div_by_constant(&mut terms, &[mod_expr]);

    // SMT-LIB Ints: `(mod x 0)` is TOTAL but UNCONSTRAINED (a single consistent
    // but unspecified value). We model it as a FRESH Int variable with NO
    // constraints — NOT pinned to `x`, which would wrongly refute models that
    // assign it any other value (#div0).
    assert!(result.constraints.is_empty());
    assert_eq!(result.rewritten.len(), 1);
    assert!(result.introduced_unconstrained_div_mod);
    // The result is a fresh variable, not the dividend and not a constant.
    assert_ne!(result.rewritten[0], x);
    assert!(matches!(
        terms.get(result.rewritten[0]),
        TermData::Var(_, _)
    ));
}

#[test]
fn test_eliminate_div_by_zero_returns_unconstrained_fresh_var() {
    let mut terms = setup_term_store();
    let x = terms.mk_fresh_var("x", Sort::Int);
    let zero = terms.mk_int(BigInt::from(0));
    let div_expr = terms.mk_intdiv(x, zero);

    let result = eliminate_int_mod_div_by_constant(&mut terms, &[div_expr]);

    // SMT-LIB Ints: `(div x 0)` is TOTAL but UNCONSTRAINED. We model it as a
    // FRESH Int variable with NO constraints — NOT pinned to 0, which would
    // wrongly refute models that assign it any other value (#div0).
    assert!(result.constraints.is_empty());
    assert_eq!(result.rewritten.len(), 1);
    assert!(result.introduced_unconstrained_div_mod);
    // The result is a fresh variable, not the constant 0.
    assert!(matches!(
        terms.get(result.rewritten[0]),
        TermData::Var(_, _)
    ));
}

#[test]
fn test_literal_zero_divisor_aux_cannot_alias_single_underscore_user_symbol() {
    let mut terms = setup_term_store();
    let x = terms.mk_fresh_var("x", Sort::Int);
    let zero = terms.mk_int(BigInt::from(0));

    // A single-underscore name is legal user input. It matched AY's former
    // witness spelling exactly, so hash-consing could make `(div x 0)` reuse
    // the user variable and silently strengthen the formula.
    let user = terms.mk_var(format!("_ay_zerodiv_div_{}", x.index()), Sort::Int);
    let div_expr = terms.mk_intdiv(x, zero);
    let result = eliminate_int_mod_div_by_constant(&mut terms, &[div_expr]);

    let witness = result.rewritten[0];
    assert_ne!(
        witness, user,
        "an internal witness must not alias user input"
    );
    let TermData::Var(name, _) = terms.get(witness) else {
        panic!("expected an integer witness variable");
    };
    assert!(name.starts_with("__ay_zerodiv_div_"));
}

#[test]
fn test_symbolic_divisor_aux_cannot_alias_single_underscore_user_symbol() {
    let mut terms = setup_term_store();
    let x = terms.mk_fresh_var("x", Sort::Int);
    let y = terms.mk_fresh_var("y", Sort::Int);

    // The symbolic-divisor witness used to occupy this user-declarable name.
    // Pre-intern it to reproduce the collision that the reserved prefix avoids.
    let user = terms.mk_var(
        format!("_ay_symdiv_q_{}_{}", x.index(), y.index()),
        Sort::Int,
    );
    let div_expr = terms.mk_intdiv(x, y);
    let result = eliminate_int_mod_div(&mut terms, &[div_expr]);

    let witness = result.rewritten[0];
    assert_ne!(
        witness, user,
        "an internal witness must not alias user input"
    );
    let TermData::Var(name, _) = terms.get(witness) else {
        panic!("expected an integer witness variable");
    };
    assert!(name.starts_with("__ay_symdiv_q_"));
}

#[test]
fn test_frontend_single_underscore_literal_witness_name_cannot_capture_internal_aux() {
    let mut exec = Executor::new();
    let declarations = parse("(set-logic QF_NIA)(declare-const x Int)")
        .expect("initial declarations should parse");
    assert!(exec
        .execute_all(&declarations)
        .expect("initial declarations should execute")
        .is_empty());
    let x = exec
        .ctx
        .symbol_info("x")
        .and_then(|info| info.term)
        .expect("x should have a core term identity");
    let user_name = format!("_ay_zerodiv_div_{}", x.index());

    // The old single-underscore spelling remains legal user input, but it can
    // no longer constrain the reserved witness for `(div x 0)`.
    let commands = parse(&format!(
        "(declare-const {user_name} Int)\
         (assert (= {user_name} 0))\
         (assert (> (div x 0) 0))\
         (check-sat)"
    ))
    .expect("the former internal spelling should remain valid SMT-LIB");
    let outputs = exec
        .execute_all(&commands)
        .expect("single-underscore declaration should execute");

    assert!(exec.ctx.symbol_info(&user_name).is_some());
    assert_eq!(outputs, vec!["sat"]);
}

#[test]
fn test_frontend_single_underscore_symbolic_witness_name_cannot_capture_internal_aux() {
    let mut exec = Executor::new();
    let declarations = parse(
        "(set-logic QF_NIA)\
         (declare-const x Int)\
         (declare-const y Int)",
    )
    .expect("initial declarations should parse");
    assert!(exec
        .execute_all(&declarations)
        .expect("initial declarations should execute")
        .is_empty());
    let x = exec
        .ctx
        .symbol_info("x")
        .and_then(|info| info.term)
        .expect("x should have a core term identity");
    let y = exec
        .ctx
        .symbol_info("y")
        .and_then(|info| info.term)
        .expect("y should have a core term identity");
    let user_name = format!("_ay_symdiv_q_{}_{}", x.index(), y.index());

    // Pinning the former symbolic-quotient spelling must not pin the actual
    // under-specified `(div x y)` result when `y = 0`.
    let commands = parse(&format!(
        "(declare-const {user_name} Int)\
         (assert (= {user_name} 0))\
         (assert (= y 0))\
         (assert (= (div x y) 9))\
         (check-sat)"
    ))
    .expect("the former internal spelling should remain valid SMT-LIB");
    let outputs = exec
        .execute_all(&commands)
        .expect("single-underscore declaration should execute");

    assert!(exec.ctx.symbol_info(&user_name).is_some());
    assert_eq!(outputs, vec!["sat"]);
}

#[test]
fn test_frontend_rejects_reserved_div_witness_names() {
    for name in ["__ay_zerodiv_div_0", "__ay_symdiv_q_0_1"] {
        let commands = parse(&format!("(declare-const {name} Int)"))
            .expect("reserved name should still be syntactically valid");
        let mut exec = Executor::new();
        assert!(
            exec.execute_all(&commands).is_err(),
            "frontend accepted reserved solver name {name}"
        );
    }
}

#[test]
fn test_zero_vs_symbolic_divisor_cross_congruence_emitted() {
    // `(div x 0)` (literal-zero divisor) and `(div (* x x) x)` (symbolic divisor)
    // both denote `div(0,0)` when `x = 0`, so they must be congruent. The two
    // elimination paths build SEPARATE result vars; the cross-class congruence
    // emitter must add the linking implication
    // `(=> (and (= x (* x x)) (= x 0)) (= zerodiv_var sym_result))`
    // so a model cannot give them different values (#nia-zero-vs-symbolic-divisor).
    let mut terms = setup_term_store();
    let x = terms.mk_fresh_var("x", Sort::Int);
    let zero = terms.mk_int(BigInt::from(0));
    let xx = terms.mk_mul(vec![x, x]);
    let div_x0 = terms.mk_intdiv(x, zero); // literal zero divisor
    let div_xx_x = terms.mk_intdiv(xx, x); // symbolic divisor

    // Use the symbolic-divisor variant so the symbolic term is eliminated to a
    // fresh result var and the cross-class congruence runs.
    let result = eliminate_int_mod_div(&mut terms, &[div_x0, div_xx_x]);
    assert!(result.introduced_unconstrained_div_mod);

    // Identify the literal-zero-divisor var (name `__ay_zerodiv_div_*`) and the
    // symbolic-divisor result var. The cross-class congruence emitter must have
    // added a constraint that transitively mentions BOTH of them (the linking
    // implication `(=> (and (= d x) (= y 0)) (= v r))`). Neither the zero-divisor
    // congruence nor the symbolic congruence pairs these two distinct vars, so a
    // single constraint referencing both can only come from the new emitter.
    let mut zero_var: Option<TermId> = None;
    for idx in 0..terms.len() {
        let t = TermId::new(idx as u32);
        if let TermData::Var(name, _) = terms.get(t) {
            if name.starts_with("__ay_zerodiv_div_") {
                zero_var = Some(t);
            }
        }
    }
    let zero_var = zero_var.expect("expected a literal-zero-divisor var to be created");

    // The symbolic result var is the rewritten form of `(div (* x x) x)`.
    let sym_result = result.rewritten[1];
    assert!(matches!(terms.get(sym_result), TermData::Var(_, _)));
    assert_ne!(zero_var, sym_result);

    // Collect the leaf var set of each constraint; the cross-congruence
    // implication is the (only) constraint whose leaves include BOTH the
    // zero-divisor var and the symbolic result var.
    fn leaves(terms: &TermStore, t: TermId, out: &mut Vec<TermId>) {
        match terms.get(t) {
            TermData::App(_, args) => {
                for &a in args {
                    leaves(terms, a, out);
                }
            }
            TermData::Not(i) => leaves(terms, *i, out),
            TermData::Ite(c, th, el) => {
                leaves(terms, *c, out);
                leaves(terms, *th, out);
                leaves(terms, *el, out);
            }
            TermData::Var(_, _) => out.push(t),
            _ => {}
        }
    }
    let found = result.constraints.iter().any(|&c| {
        let mut vs = Vec::new();
        leaves(&terms, c, &mut vs);
        vs.contains(&zero_var) && vs.contains(&sym_result)
    });
    assert!(
        found,
        "expected a cross-class congruence constraint mentioning both the \
         literal-zero-divisor var and the symbolic-divisor result var"
    );
}

#[test]
fn test_eliminate_with_negative_divisor() {
    let mut terms = setup_term_store();
    let x = terms.mk_fresh_var("x", Sort::Int);
    let neg_three = terms.mk_int(BigInt::from(-3));
    let mod_expr = terms.mk_mod(x, neg_three);

    let result = eliminate_int_mod_div_by_constant(&mut terms, &[mod_expr]);

    // Should generate constraints with |k| = 3
    assert_eq!(result.constraints.len(), 3);

    // Verify that one constraint has r < 3 (not r < -3)
    let mut found_r_lt_abs_k = false;
    for constraint in &result.constraints {
        if let TermData::App(Symbol::Named(name), args) = terms.get(*constraint) {
            if name == "<" && args.len() == 2 {
                if let TermData::Const(Constant::Int(n)) = terms.get(args[1]) {
                    if *n == BigInt::from(3) {
                        found_r_lt_abs_k = true;
                    }
                }
            }
        }
    }
    assert!(found_r_lt_abs_k, "Expected constraint r < |k| = 3");
}

#[test]
fn test_eliminate_nested_mod_div() {
    let mut terms = setup_term_store();
    let x = terms.mk_fresh_var("x", Sort::Int);
    let two = terms.mk_int(BigInt::from(2));
    let three = terms.mk_int(BigInt::from(3));

    // (mod (div x 3) 2)
    let div_expr = terms.mk_intdiv(x, three);
    let mod_expr = terms.mk_mod(div_expr, two);

    let result = eliminate_int_mod_div_by_constant(&mut terms, &[mod_expr]);

    // Should generate constraints for both div and mod
    // div: 3 constraints, mod: 3 constraints = 6 total
    assert_eq!(result.constraints.len(), 6);
}

#[test]
fn test_eliminate_multiple_formulas() {
    let mut terms = setup_term_store();
    let x = terms.mk_fresh_var("x", Sort::Int);
    let y = terms.mk_fresh_var("y", Sort::Int);
    let two = terms.mk_int(BigInt::from(2));
    let three = terms.mk_int(BigInt::from(3));

    let mod_x = terms.mk_mod(x, two);
    let div_y = terms.mk_intdiv(y, three);

    let result = eliminate_int_mod_div_by_constant(&mut terms, &[mod_x, div_y]);

    // 3 constraints for mod + 3 constraints for div = 6 total
    assert_eq!(result.constraints.len(), 6);
    assert_eq!(result.rewritten.len(), 2);
}

#[test]
fn test_eliminate_preserves_other_terms() {
    let mut terms = setup_term_store();
    let x = terms.mk_fresh_var("x", Sort::Int);
    let y = terms.mk_fresh_var("y", Sort::Int);
    let three = terms.mk_int(BigInt::from(3));

    // Mix of mod and non-mod expressions
    let mod_expr = terms.mk_mod(x, three);
    let plain_add = terms.mk_add(vec![x, y]);

    let result = eliminate_int_mod_div_by_constant(&mut terms, &[mod_expr, plain_add]);

    assert_eq!(result.constraints.len(), 3); // Only mod generates constraints
    assert_eq!(result.rewritten.len(), 2);
    assert_eq!(result.rewritten[1], plain_add); // Plain add unchanged
}

// ===== Tests for constraint correctness =====

#[test]
fn test_mod_constraints_structure() {
    let mut terms = setup_term_store();
    let x = terms.mk_fresh_var("x", Sort::Int);
    let five = terms.mk_int(BigInt::from(5));
    let mod_expr = terms.mk_mod(x, five);

    let result = eliminate_int_mod_div_by_constant(&mut terms, &[mod_expr]);

    // Verify constraint structure:
    // 1. Equality constraint: x = k*q + r
    // 2. Lower bound: 0 <= r (mk_ge(r, zero) normalizes to mk_le(zero, r))
    // 3. Upper bound: r < |k|

    let mut has_eq = false;
    let mut has_le = false; // mk_ge(r, zero) normalized to mk_le(zero, r)
    let mut has_lt = false;

    for constraint in &result.constraints {
        if let TermData::App(Symbol::Named(name), _) = terms.get(*constraint) {
            match name.as_str() {
                "=" => has_eq = true,
                "<=" => has_le = true,
                "<" => has_lt = true,
                _ => {}
            }
        }
    }

    assert!(has_eq, "Missing equality constraint x = k*q + r");
    assert!(has_le, "Missing lower bound constraint 0 <= r");
    assert!(has_lt, "Missing upper bound constraint r < |k|");
}

#[test]
fn test_mod_div_same_expression_share_constraints() {
    let mut terms = setup_term_store();
    let x = terms.mk_fresh_var("x", Sort::Int);
    let three = terms.mk_int(BigInt::from(3));

    // (mod x 3) and (div x 3) on the same dividend
    let mod_expr = terms.mk_mod(x, three);
    let div_expr = terms.mk_intdiv(x, three);

    let result = eliminate_int_mod_div_by_constant(&mut terms, &[mod_expr, div_expr]);

    // `(div x 3)` and `(mod x 3)` over the SAME dividend now SHARE one canonical
    // `(q, r)` pair, so the defining constraint `x = 3*q + r ∧ 0 <= r < 3` is
    // emitted ONCE (3 constraints), not duplicated per op (was 6). Sharing is
    // sound — both ops denote the unique Euclidean `(q, r)` — and it makes the
    // identity `x = 3*(div x 3) + (mod x 3)` directly derivable instead of
    // requiring a uniqueness deduction the LIA layer otherwise left as `unknown`.
    assert_eq!(result.constraints.len(), 3);
}

#[test]
fn test_not_wrapping_preserved() {
    let mut terms = setup_term_store();
    let x = terms.mk_fresh_var("x", Sort::Int);
    let three = terms.mk_int(BigInt::from(3));
    let mod_expr = terms.mk_mod(x, three);
    let zero = terms.mk_int(BigInt::from(0));
    let eq = terms.mk_eq(mod_expr, zero);
    let not_eq = terms.mk_not(eq);

    let result = eliminate_int_mod_div_by_constant(&mut terms, &[not_eq]);

    // Should rewrite the inner mod but preserve the not structure
    assert_eq!(result.constraints.len(), 3);

    // Check that the result is a Not node
    if let TermData::Not(_) = terms.get(result.rewritten[0]) {
        // Good - Not structure preserved
    } else {
        panic!("Expected Not wrapper to be preserved");
    }
}

#[test]
fn test_ite_preserved() {
    let mut terms = setup_term_store();
    let cond = terms.mk_fresh_var("c", Sort::Bool);
    let x = terms.mk_fresh_var("x", Sort::Int);
    let three = terms.mk_int(BigInt::from(3));
    let mod_expr = terms.mk_mod(x, three);
    let one = terms.mk_int(BigInt::from(1));

    let ite = terms.mk_ite(cond, mod_expr, one);

    let result = eliminate_int_mod_div_by_constant(&mut terms, &[ite]);

    // Should rewrite the mod in the then branch
    assert_eq!(result.constraints.len(), 3);

    // Check that the result is still an ITE
    if let TermData::Ite(_, _, _) = terms.get(result.rewritten[0]) {
        // Good - ITE structure preserved
    } else {
        panic!("Expected ITE wrapper to be preserved");
    }
}

#[test]
fn test_memoization_prevents_duplicate_constraints() {
    let mut terms = setup_term_store();
    let x = terms.mk_fresh_var("x", Sort::Int);
    let three = terms.mk_int(BigInt::from(3));
    let mod_expr = terms.mk_mod(x, three);

    // Use the same mod expression twice
    let sum = terms.mk_add(vec![mod_expr, mod_expr]);

    let result = eliminate_int_mod_div_by_constant(&mut terms, &[sum]);

    // Should only generate 3 constraints (memoization)
    assert_eq!(result.constraints.len(), 3);
}

// ===== Tests for `rem` elimination (#nia-symbolic-rem-wrong-sat) =====

/// True if `root` (or any constraint subtree) contains a raw `rem` application.
/// `rem` is NOT in the LIA/NIA `div`/`mod` support set, so any surviving `rem`
/// app is treated as a free uninterpreted integer — exactly the wrong-SAT this
/// elimination removes.
fn term_mentions_rem(terms: &TermStore, root: TermId) -> bool {
    let mut stack = vec![root];
    let mut seen: std::collections::HashSet<TermId> = std::collections::HashSet::new();
    while let Some(t) = stack.pop() {
        if !seen.insert(t) {
            continue;
        }
        match terms.get(t) {
            TermData::App(sym, args) => {
                if sym.name() == "rem" {
                    return true;
                }
                stack.extend(args.iter().copied());
            }
            TermData::Not(inner) => stack.push(*inner),
            TermData::Ite(c, a, b) => {
                stack.push(*c);
                stack.push(*a);
                stack.push(*b);
            }
            TermData::Let(bindings, body) => {
                for (_, v) in bindings {
                    stack.push(*v);
                }
                stack.push(*body);
            }
            TermData::Forall(_, body, _) | TermData::Exists(_, body, _) => stack.push(*body),
            _ => {}
        }
    }
    false
}

#[test]
fn test_eliminate_symbolic_rem_left_as_app_no_bypass() {
    let mut terms = setup_term_store();
    let x = terms.mk_fresh_var("x", Sort::Int);
    let y = terms.mk_fresh_var("y", Sort::Int);
    let rem_expr = terms.mk_rem(x, y);
    assert!(term_mentions_rem(&terms, rem_expr));

    let result = eliminate_int_mod_div(&mut terms, &[rem_expr]);
    assert_eq!(result.rewritten.len(), 1);

    // A symbolic-divisor `rem` is intentionally NOT eliminated (lowering it to
    // `mod`/`ite` was path-fragile). It is left as a `rem` application — the
    // executor degrades such a formula to a sound `unknown` universally in
    // `route_to_solver` (#nia-symbolic-rem-bypass) — and crucially does NOT set
    // the #div0 model-validation bypass, so an unsolved `rem` can never be waved
    // through as a wrong-SAT.
    assert!(
        term_mentions_rem(&terms, result.rewritten[0]),
        "symbolic rem should be left as a `rem` application (degraded to unknown later)"
    );
    assert!(
        !result.introduced_unconstrained_div_mod,
        "symbolic rem must NOT request the #div0 SAT-validation bypass"
    );
}

#[test]
fn test_eliminate_zero_divisor_rem_distinct_from_mod() {
    let mut terms = setup_term_store();
    let x = terms.mk_fresh_var("x", Sort::Int);
    let zero = terms.mk_int(BigInt::from(0));
    // `(rem x 0)` and `(mod x 0)` are both kept as zero-divisor applications.
    let rem0 = terms.mk_rem(x, zero);
    let mod0 = terms.mk_mod(x, zero);

    let result = eliminate_int_mod_div_by_constant(&mut terms, &[rem0, mod0]);
    assert_eq!(result.rewritten.len(), 2);

    // Z3 #9140: `(rem x 0)` and `(mod x 0)` are INDEPENDENT under-specified
    // values, so they lower to DISTINCT vars and no congruence forces them
    // equal — `(distinct (rem x 0) (mod x 0))` must stay satisfiable.
    assert_ne!(
        result.rewritten[0], result.rewritten[1],
        "rem(x,0) and mod(x,0) must lower to distinct unconstrained vars"
    );
    assert!(!term_mentions_rem(&terms, result.rewritten[0]));
    assert!(result.introduced_unconstrained_div_mod);
}
