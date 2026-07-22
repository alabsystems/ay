// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;
use ay_core::Sort;

#[test]
fn test_is_cegqi_candidate_forall() {
    let mut terms = TermStore::new();

    // Create: forall x. x >= 0
    let x_var = terms.mk_var("x", Sort::Int);
    let zero = terms.mk_int(0.into());
    let body = terms.mk_ge(x_var, zero);
    let forall = terms.mk_forall(vec![("x".to_string(), Sort::Int)], body);

    assert!(is_cegqi_candidate(&terms, forall));
}

/// UF-only quantifier with arithmetic-sorted variables IS a CEGQI candidate
/// after #5888 fix. `forall x:Int. f(x) = x` is an arithmetic equality over
/// Int-sorted terms, so CEGQI may instantiate `x` while treating `f(x)` as an
/// opaque arithmetic term.
#[test]
fn test_is_cegqi_candidate_accepts_uf_with_arith_sort() {
    let mut terms = TermStore::new();

    // Create: forall x:Int. f(x) = x
    let x_var = terms.mk_var("x", Sort::Int);
    let f_x = terms.mk_app(Symbol::Named("f".to_string()), vec![x_var], Sort::Int);
    let body = terms.mk_eq(f_x, x_var);
    let forall = terms.mk_forall(vec![("x".to_string(), Sort::Int)], body);

    assert!(
        is_cegqi_candidate(&terms, forall),
        "UF quantifier with Int-sorted variable should be CEGQI candidate (#5888)"
    );
}

/// Pure UF quantifier with non-arithmetic sort should NOT be a CEGQI candidate.
/// `forall x:Bool. f(x)` has no arithmetic content.
#[test]
fn test_is_cegqi_candidate_rejects_pure_uf_bool_sort() {
    let mut terms = TermStore::new();

    // Create: forall x:Bool. f(x)
    let x_var = terms.mk_var("x", Sort::Bool);
    let f_x = terms.mk_app(Symbol::Named("f".to_string()), vec![x_var], Sort::Bool);
    let forall = terms.mk_forall(vec![("x".to_string(), Sort::Bool)], f_x);

    assert!(
        !is_cegqi_candidate(&terms, forall),
        "pure UF with Bool sort should not be CEGQI candidate"
    );
}

/// #2864: exists over pure equality with arithmetic-sorted variables should
/// be a CEGQI candidate (no UF, involves arithmetic via variable sort).
#[test]
fn test_is_cegqi_candidate_exists_pure_equality_2864() {
    let mut terms = TermStore::new();

    let x_var = terms.mk_var("x", Sort::Real);
    let y_var = terms.mk_var("y", Sort::Real);
    let body = terms.mk_eq(y_var, x_var);
    let exists = terms.mk_exists(vec![("y".to_string(), Sort::Real)], body);

    assert!(
        is_cegqi_candidate(&terms, exists),
        "exists over pure arithmetic equality should be a CEGQI candidate"
    );
}

/// #5888: forall with UF and arithmetic vars SHOULD be a CEGQI candidate.
/// CEGQI partially handles mixed formulas when every bound variable is
/// arithmetic-sorted: arithmetic variables get instantiated, UF terms are
/// treated as opaque arithmetic subterms.
#[test]
fn test_is_cegqi_candidate_accepts_mixed_uf_arith() {
    let mut terms = TermStore::new();

    let x_var = terms.mk_var("x", Sort::Int);
    let f_x = terms.mk_app(Symbol::Named("f".to_string()), vec![x_var], Sort::Int);
    let one = terms.mk_int(1.into());
    let sum = terms.mk_add(vec![f_x, one]);
    let zero = terms.mk_int(0.into());
    let body = terms.mk_gt(sum, zero);
    let forall = terms.mk_forall(vec![("x".to_string(), Sort::Int)], body);

    assert!(
        is_cegqi_candidate(&terms, forall),
        "mixed UF+arith quantifier should be CEGQI candidate (#5888)"
    );
}

#[test]
fn test_is_cegqi_candidate_rejects_non_arith_seq_binder_7883() {
    let mut terms = TermStore::new();
    let seq_sort = Sort::Uninterpreted("Seq".to_string());

    let s_var = terms.mk_var("s", seq_sort.clone());
    let seq_len_s = terms.mk_app(Symbol::Named("seq_len".to_string()), vec![s_var], Sort::Int);
    let zero = terms.mk_int(0.into());
    let body = terms.mk_ge(seq_len_s, zero);
    let forall = terms.mk_forall(vec![("s".to_string(), seq_sort)], body);

    assert!(
        !is_cegqi_candidate(&terms, forall),
        "triggerless seq axioms with non-arithmetic binders must not enter arithmetic CEGQI"
    );
}

#[test]
fn test_is_cegqi_candidate_rejects_mixed_seq_and_int_binders_7883() {
    let mut terms = TermStore::new();
    let seq_sort = Sort::Uninterpreted("Seq".to_string());

    let s_var = terms.mk_var("s", seq_sort.clone());
    let i_var = terms.mk_var("i", Sort::Int);
    let seq_len_s = terms.mk_app(Symbol::Named("seq_len".to_string()), vec![s_var], Sort::Int);
    let body = terms.mk_lt(i_var, seq_len_s);
    let forall = terms.mk_forall(
        vec![("s".to_string(), seq_sort), ("i".to_string(), Sort::Int)],
        body,
    );

    assert!(
        !is_cegqi_candidate(&terms, forall),
        "mixed Seq/Int binders are outside the arithmetic CEGQI fragment"
    );
}

#[test]
fn test_is_cegqi_candidate_rejects_pure_bool_predicate_on_int_var_7883() {
    let mut terms = TermStore::new();

    let x_var = terms.mk_var("x", Sort::Int);
    let pred = terms.mk_app(Symbol::Named("p".to_string()), vec![x_var], Sort::Bool);
    let forall = terms.mk_forall(vec![("x".to_string(), Sort::Int)], pred);

    assert!(
        !is_cegqi_candidate(&terms, forall),
        "pure Boolean predicates over Int binders are not in the arithmetic CEGQI fragment"
    );
}

#[test]
fn test_is_cegqi_candidate_rejects_guarded_bool_predicate_on_int_var_9227() {
    let mut terms = TermStore::new();

    let x_var = terms.mk_var("x", Sort::Int);
    let pred = terms.mk_app(Symbol::Named("p".to_string()), vec![x_var], Sort::Bool);
    let zero = terms.mk_int(0.into());
    let len = terms.mk_var("len", Sort::Int);
    let in_lower = terms.mk_le(zero, x_var);
    let in_upper = terms.mk_lt(x_var, len);
    let not_in_lower = terms.mk_not(in_lower);
    let not_in_upper = terms.mk_not(in_upper);
    let body = terms.mk_or(vec![pred, not_in_lower, not_in_upper]);
    let forall = terms.mk_forall(vec![("x".to_string(), Sort::Int)], body);

    assert!(
        !is_cegqi_candidate(&terms, forall),
        "range-guarded Boolean UF obligations are handled by E-matching/enumeration, not arithmetic CEGQI"
    );
}

#[test]
fn test_cegqi_instantiator_creation() {
    let mut terms = TermStore::new();

    // Create: forall x. x >= 0
    let x_var = terms.mk_var("x", Sort::Int);
    let zero = terms.mk_int(0.into());
    let body = terms.mk_ge(x_var, zero);
    let forall = terms.mk_forall(vec![("x".to_string(), Sort::Int)], body);

    let inst = CegqiInstantiator::new(forall, &mut terms);
    assert!(inst.is_some());

    let inst = inst.unwrap();
    assert_eq!(inst.bound_to_ce.len(), 1);
}

#[test]
fn test_ce_lemma_creation() {
    let mut terms = TermStore::new();

    // Create: forall x. x >= 0
    let x_var = terms.mk_var("x", Sort::Int);
    let zero = terms.mk_int(0.into());
    let body = terms.mk_ge(x_var, zero);
    let forall = terms.mk_forall(vec![("x".to_string(), Sort::Int)], body);

    let inst = CegqiInstantiator::new(forall, &mut terms).unwrap();
    let ce_lemma = inst.create_ce_lemma(&mut terms);

    assert!(ce_lemma.is_some());
    let ce_lemma = ce_lemma.unwrap();

    // The CE lemma should be: Not(__ce_x >= 0)
    // Note: mk_ge(a, b) creates (<= b a), so we check for either >= or <=
    let data = terms.get(ce_lemma);
    match data {
        TermData::Not(inner) => {
            // Expected: negation of substituted body
            let inner_data = terms.get(*inner);
            match inner_data {
                TermData::App(sym, args) if args.len() == 2 => {
                    // mk_ge creates either >= or <= (args may be swapped)
                    assert!(
                        sym.name() == ">=" || sym.name() == "<=",
                        "Expected comparison, got {}",
                        sym.name()
                    );
                    // One arg should be __ce_x, the other should be 0
                    let has_ce_var = args.iter().any(|&arg| {
                        matches!(terms.get(arg), TermData::Var(name, _) if name.starts_with("__ce_"))
                    });
                    let has_zero = args.iter().any(|&arg| {
                        matches!(terms.get(arg), TermData::Const(ay_core::term::Constant::Int(n)) if *n == 0.into())
                    });
                    assert!(has_ce_var, "Expected a CE variable in args");
                    assert!(has_zero, "Expected 0 in args");
                }
                _ => panic!("Expected comparison App, got {inner_data:?}"),
            }
        }
        _ => panic!("Expected Not, got {data:?}"),
    }
}

#[test]
fn test_ce_lemma_reflexive() {
    let mut terms = TermStore::new();

    // Create: forall x. x >= x (trivially valid)
    let x_var = terms.mk_var("x", Sort::Int);
    let body = terms.mk_ge(x_var, x_var); // x >= x
    let forall = terms.mk_forall(vec![("x".to_string(), Sort::Int)], body);

    let inst = CegqiInstantiator::new(forall, &mut terms).unwrap();
    let ce_lemma = inst.create_ce_lemma(&mut terms);

    assert!(ce_lemma.is_some());
    let ce_lemma = ce_lemma.unwrap();

    // The CE lemma is: Not(__ce_x >= __ce_x)
    // But the term store simplifies x >= x to true, so Not(true) = false
    // This is actually correct! Asserting false makes the problem UNSAT.
    let data = terms.get(ce_lemma);
    match data {
        // Simplified case: x >= x is true, so Not(true) = false
        TermData::Const(ay_core::term::Constant::Bool(false)) => {
            // This is expected: the CE lemma simplified to false
            // Asserting false will make the solver return UNSAT
        }
        // Non-simplified case: Not(>= ce_x ce_x)
        TermData::Not(inner) => {
            let inner_data = terms.get(*inner);
            match inner_data {
                TermData::App(sym, args) if args.len() == 2 => {
                    // mk_ge(a, b) creates (a <= b) swapped as (<= b a)
                    // or (>= a b) - depends on implementation
                    assert!(
                        sym.name() == ">=" || sym.name() == "<=",
                        "Expected comparison, got {}",
                        sym.name()
                    );
                }
                _ => panic!("Expected comparison, got {inner_data:?}"),
            }
        }
        _ => panic!("Expected Not or false, got {data:?}"),
    }
}

#[test]
fn test_let_binding_with_shadowing() {
    // Test capture-avoiding substitution:
    // forall x. (let ((x (+ x 1))) (> x 0))
    //
    // The binding expression should substitute the outer x, and let inlining
    // should preserve the shadowed body semantics without leaving the outer x.
    fn term_contains(terms: &TermStore, root: TermId, needle: TermId) -> bool {
        if root == needle {
            return true;
        }
        match terms.get(root) {
            TermData::App(_, args) => args.iter().any(|&arg| term_contains(terms, arg, needle)),
            TermData::Not(inner) => term_contains(terms, *inner, needle),
            TermData::Ite(c, t, e) => {
                term_contains(terms, *c, needle)
                    || term_contains(terms, *t, needle)
                    || term_contains(terms, *e, needle)
            }
            TermData::Let(bindings, body) => {
                bindings
                    .iter()
                    .any(|(_, value)| term_contains(terms, *value, needle))
                    || term_contains(terms, *body, needle)
            }
            TermData::Forall(_, body, _) | TermData::Exists(_, body, _) => {
                term_contains(terms, *body, needle)
            }
            _ => false,
        }
    }

    let mut terms = TermStore::new();

    // Create: (let ((x (+ x 1))) (> x 0))
    let x_var = terms.mk_var("x", Sort::Int);
    let one = terms.mk_int(1.into());
    let zero = terms.mk_int(0.into());
    let binding_expr = terms.mk_add(vec![x_var, one]); // (+ x 1)
    let gt = terms.mk_gt(x_var, zero); // x > 0 (normalized to (< 0 x))
    let let_expr = terms.mk_let(vec![("x".to_string(), binding_expr)], gt);

    // Create: forall x. (let ((x (+ x 1))) (> x 0))
    let forall = terms.mk_forall(vec![("x".to_string(), Sort::Int)], let_expr);

    let inst = CegqiInstantiator::new(forall, &mut terms).unwrap();
    let ce_var = *inst.bound_to_ce.get("x").unwrap();
    assert!(
        matches!(terms.get(ce_var), TermData::Var(name, _) if name == "__ce_x"),
        "Expected CE variable __ce_x"
    );
    let ce_lemma = inst.create_ce_lemma(&mut terms);

    // CE lemma should be equivalent to:
    // Not(let ((x (+ __ce_x 1))) (> x 0))
    // The shared substitution helper may inline the let, so assert semantic
    // content instead of the exact Let node shape.
    assert!(ce_lemma.is_some());
    let ce_lemma = ce_lemma.unwrap();

    let TermData::Not(inner) = terms.get(ce_lemma) else {
        panic!("Expected Not(let ...), got {:?}", terms.get(ce_lemma));
    };

    assert!(
        term_contains(&terms, *inner, ce_var),
        "Expected CE var in substituted let expression"
    );
    assert!(
        !term_contains(&terms, *inner, x_var),
        "Did not expect original outer x after capture-avoiding let substitution"
    );

    let TermData::App(sym, _) = terms.get(*inner) else {
        panic!(
            "Expected inlined comparison App, got {:?}",
            terms.get(*inner)
        );
    };
    assert!(matches!(sym.name(), "<" | ">"));
}

#[test]
fn test_exists_quantifier_is_forall_flag() {
    let mut terms = TermStore::new();

    // Create: exists x. x > 0
    let x_var = terms.mk_var("x", Sort::Int);
    let zero = terms.mk_int(0.into());
    let body = terms.mk_gt(x_var, zero);
    let exists = terms.mk_exists(vec![("x".to_string(), Sort::Int)], body);

    let inst = CegqiInstantiator::new(exists, &mut terms).unwrap();

    // Should be marked as exists (not forall)
    assert!(
        !inst.is_forall(),
        "exists quantifier should have is_forall = false"
    );

    let ce_lemma = inst.create_ce_lemma(&mut terms);
    assert!(ce_lemma.is_some());

    // For exists, CE lemma should NOT be negated: phi(__ce_x) directly
    let ce_lemma = ce_lemma.unwrap();
    let data = terms.get(ce_lemma);

    // Should NOT be wrapped in Not (unlike forall)
    match data {
        TermData::Not(_) => panic!("exists CE lemma should not be negated"),
        TermData::App(sym, args) => {
            // Should be the comparison operator directly (> or <)
            assert!(
                sym.name() == ">" || sym.name() == "<",
                "Expected comparison, got {}",
                sym.name()
            );
            assert_eq!(args.len(), 2);
            // One arg should be __ce_x
            let has_ce_var = args.iter().any(|&arg| {
                matches!(terms.get(arg), TermData::Var(name, _) if name.starts_with("__ce_"))
            });
            assert!(has_ce_var, "Expected CE variable in exists lemma");
        }
        _ => panic!("Expected App for exists CE lemma, got {data:?}"),
    }
}

#[test]
fn test_forall_vs_exists_ce_lemma_polarity() {
    let mut terms = TermStore::new();

    // Create same body for both: x >= 0
    let x_var = terms.mk_var("x", Sort::Int);
    let zero = terms.mk_int(0.into());
    let body = terms.mk_ge(x_var, zero);

    // Create forall x. x >= 0
    let forall = terms.mk_forall(vec![("x".to_string(), Sort::Int)], body);
    let forall_inst = CegqiInstantiator::new(forall, &mut terms).unwrap();
    assert!(forall_inst.is_forall());
    let forall_lemma = forall_inst.create_ce_lemma(&mut terms).unwrap();

    // Create exists x. x >= 0
    let exists = terms.mk_exists(vec![("x".to_string(), Sort::Int)], body);
    let exists_inst = CegqiInstantiator::new(exists, &mut terms).unwrap();
    assert!(!exists_inst.is_forall());
    let exists_lemma = exists_inst.create_ce_lemma(&mut terms).unwrap();

    // Forall CE lemma should be negated
    assert!(
        matches!(terms.get(forall_lemma), TermData::Not(_)),
        "forall CE lemma should be negated"
    );

    // Exists CE lemma should NOT be negated
    assert!(
        !matches!(terms.get(exists_lemma), TermData::Not(_)),
        "exists CE lemma should not be negated"
    );
}
