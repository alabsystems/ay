// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;
use ay_core::term::Symbol;
use ay_core::Sort;
use num_bigint::BigInt;

/// Helper: create `(exists ((x Int)) (= x 5))` and Skolemize it.
#[test]
fn test_skolemize_simple_exists() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Int);
    let five = terms.mk_int(BigInt::from(5));
    let eq = terms.mk_eq(x, five);
    let exists = terms.mk_exists(vec![("x".to_string(), Sort::Int)], eq);

    let result = skolemize(&mut terms, exists, false);
    assert!(result.is_some(), "positive Exists should Skolemize");

    let body = result.unwrap();
    // Body should be (= sk!x_N 5) — an equality with a fresh Skolem constant.
    // The Skolem constant name starts with "sk!x_".
    match terms.get(body).clone() {
        TermData::App(sym, args) if sym.name() == "=" => {
            assert_eq!(args.len(), 2);
            // One of the arguments should be a fresh Skolem var, the other should be 5
            let is_skolem = |id: TermId| -> bool {
                matches!(terms.get(id), TermData::Var(name, _) if name.starts_with("sk!x_"))
            };
            assert!(
                is_skolem(args[0]) || is_skolem(args[1]),
                "expected a Skolem constant in equality"
            );
        }
        other => panic!("expected equality App, got: {other:?}"),
    }
}

/// Negative Forall should Skolemize: ¬(∀x. P(x)) ≡ ∃x. ¬P(x) → ¬P(sk_x)
#[test]
fn test_skolemize_negative_forall() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Int);
    let p_sym = Symbol::named("P");
    let px = terms.mk_app(p_sym, vec![x], Sort::Bool);
    let forall = terms.mk_forall(vec![("x".to_string(), Sort::Int)], px);

    let result = skolemize(&mut terms, forall, true);
    assert!(result.is_some(), "negated Forall should Skolemize");

    let body = result.unwrap();
    // Body should be (not (P sk!x_N)) — negation of body with Skolem substitution.
    // mk_not may simplify, so check that the body references a Skolem constant.
    match terms.get(body).clone() {
        TermData::Not(inner) => {
            // inner should be (P sk!x_N)
            match terms.get(inner).clone() {
                TermData::App(sym, args) if sym.name() == "P" => {
                    assert_eq!(args.len(), 1);
                    let is_skolem = |id: TermId| -> bool {
                        matches!(
                            terms.get(id),
                            TermData::Var(name, _) if name.starts_with("sk!x_")
                        )
                    };
                    assert!(is_skolem(args[0]), "arg should be Skolem constant");
                }
                other => panic!("expected P App inside Not, got: {other:?}"),
            }
        }
        other => panic!("expected Not(...), got: {other:?}"),
    }
}

/// Positive Forall is NOT a Skolemization target — it goes to E-matching.
#[test]
fn test_positive_forall_returns_none() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Int);
    let zero = terms.mk_int(BigInt::from(0));
    let geq = terms.mk_app(Symbol::named(">="), vec![x, zero], Sort::Bool);
    let forall = terms.mk_forall(vec![("x".to_string(), Sort::Int)], geq);

    assert!(
        skolemize(&mut terms, forall, false).is_none(),
        "positive Forall should not Skolemize"
    );
}

/// Negative Exists is NOT a Skolemization target.
#[test]
fn test_negative_exists_returns_none() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Int);
    let five = terms.mk_int(BigInt::from(5));
    let eq = terms.mk_eq(x, five);
    let exists = terms.mk_exists(vec![("x".to_string(), Sort::Int)], eq);

    assert!(
        skolemize(&mut terms, exists, true).is_none(),
        "negated Exists should not Skolemize"
    );
}

/// Multiple bound variables should all be Skolemized.
#[test]
fn test_skolemize_multi_variable_exists() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Int);
    let y = terms.mk_var("y", Sort::Int);
    // body: (= x y)
    let eq = terms.mk_eq(x, y);
    let exists = terms.mk_exists(
        vec![("x".to_string(), Sort::Int), ("y".to_string(), Sort::Int)],
        eq,
    );

    let result = skolemize(&mut terms, exists, false);
    assert!(result.is_some(), "multi-var Exists should Skolemize");

    let body = result.unwrap();
    // Body should be (= sk!x_N sk!y_M) — both variables replaced
    match terms.get(body).clone() {
        TermData::App(sym, args) if sym.name() == "=" => {
            assert_eq!(args.len(), 2);
            let is_skolem_x = |id: TermId| -> bool {
                matches!(terms.get(id), TermData::Var(name, _) if name.starts_with("sk!x_"))
            };
            let is_skolem_y = |id: TermId| -> bool {
                matches!(terms.get(id), TermData::Var(name, _) if name.starts_with("sk!y_"))
            };
            assert!(
                (is_skolem_x(args[0]) && is_skolem_y(args[1]))
                    || (is_skolem_y(args[0]) && is_skolem_x(args[1])),
                "expected both Skolem constants in equality"
            );
        }
        other => panic!("expected equality App, got: {other:?}"),
    }
}

/// Non-quantifier terms return None.
#[test]
fn test_non_quantifier_returns_none() {
    let mut terms = TermStore::new();
    let five = terms.mk_int(BigInt::from(5));

    assert!(skolemize(&mut terms, five, false).is_none());
    assert!(skolemize(&mut terms, five, true).is_none());
}

/// Skolem constants get unique names (no collision between separate calls).
#[test]
fn test_skolem_constants_are_unique() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Int);
    let five = terms.mk_int(BigInt::from(5));
    let eq = terms.mk_eq(x, five);

    let exists1 = terms.mk_exists(vec![("x".to_string(), Sort::Int)], eq);
    let result1 = skolemize(&mut terms, exists1, false).unwrap();

    // Create a second exists with the same structure
    let x2 = terms.mk_var("x", Sort::Int);
    let eq2 = terms.mk_eq(x2, five);
    let exists2 = terms.mk_exists(vec![("x".to_string(), Sort::Int)], eq2);
    let result2 = skolemize(&mut terms, exists2, false).unwrap();

    // The two Skolemized bodies should have different Skolem constants
    // (because mk_fresh_var generates unique names via var_counter).
    // They could be the same TermId if the hash-cons deduplicates, but
    // the Skolem variable names should differ.
    fn extract_skolem_name(terms: &TermStore, eq_id: TermId) -> String {
        match terms.get(eq_id).clone() {
            TermData::App(sym, args) if sym.name() == "=" => {
                for &arg in &args {
                    if let TermData::Var(name, _) = terms.get(arg) {
                        if name.starts_with("sk!") {
                            return name.clone();
                        }
                    }
                }
                panic!("no Skolem var found");
            }
            _ => panic!("expected equality"),
        }
    }

    let name1 = extract_skolem_name(&terms, result1);
    let name2 = extract_skolem_name(&terms, result2);
    assert_ne!(name1, name2, "Skolem constants should have unique names");
}

// ---- skolemize_deep tests ----

/// Helper: check if a term contains any Skolem variable (name starts with "sk!").
fn has_skolem_var(terms: &TermStore, id: TermId) -> bool {
    match terms.get(id).clone() {
        TermData::Var(name, _) => name.starts_with("sk!"),
        TermData::App(_, args) => args.iter().any(|&a| has_skolem_var(terms, a)),
        TermData::Not(inner) => has_skolem_var(terms, inner),
        TermData::Ite(c, t, e) => {
            has_skolem_var(terms, c) || has_skolem_var(terms, t) || has_skolem_var(terms, e)
        }
        _ => false,
    }
}

fn flatten_or_terms(terms: &TermStore, id: TermId, out: &mut Vec<TermId>) {
    match terms.get(id).clone() {
        TermData::App(sym, args) if sym.name() == "or" => {
            for arg in args {
                flatten_or_terms(terms, arg, out);
            }
        }
        _ => out.push(id),
    }
}

fn is_skolem_function_app(terms: &TermStore, id: TermId) -> bool {
    match terms.get(id).clone() {
        TermData::App(sym, _) => sym.name().starts_with("__ay_sk_"),
        _ => false,
    }
}

fn is_negated_skolem_predicate(terms: &TermStore, id: TermId, pred: &str) -> bool {
    match terms.get(id).clone() {
        TermData::Not(inner) => match terms.get(inner).clone() {
            TermData::App(sym, args) if sym.name() == pred && args.len() == 1 => {
                matches!(terms.get(args[0]), TermData::Var(name, _) if name.starts_with("sk!"))
            }
            _ => false,
        },
        _ => false,
    }
}

/// Exists inside AND at positive polarity should be Skolemized.
#[test]
fn test_deep_exists_in_and() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Int);
    let five = terms.mk_int(BigInt::from(5));
    let eq = terms.mk_eq(x, five);
    let exists = terms.mk_exists(vec![("x".to_string(), Sort::Int)], eq);
    let y = terms.mk_var("y", Sort::Int);
    let zero = terms.mk_int(BigInt::from(0));
    let gt = terms.mk_app(Symbol::named(">"), vec![y, zero], Sort::Bool);
    let and = terms.mk_and(vec![exists, gt]);

    let result = skolemize_deep(&mut terms, and, true);
    assert!(result.is_some(), "exists inside and should be Skolemized");
    assert!(
        has_skolem_var(&terms, result.unwrap()),
        "result should contain Skolem variable"
    );
    // The result should not contain any Exists quantifier
    let r = result.unwrap();
    match terms.get(r).clone() {
        TermData::App(sym, args) if sym.name() == "and" => {
            for &arg in &args {
                assert!(
                    !matches!(terms.get(arg), TermData::Exists(..)),
                    "conjunct should not be an Exists after Skolemization"
                );
            }
        }
        _ => panic!("expected And"),
    }
}

/// Exists inside OR at positive polarity should be Skolemized.
#[test]
fn test_deep_exists_in_or() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Int);
    let five = terms.mk_int(BigInt::from(5));
    let eq = terms.mk_eq(x, five);
    let exists = terms.mk_exists(vec![("x".to_string(), Sort::Int)], eq);
    // Use a non-trivial disjunct (mk_or simplifies away `true`)
    let y = terms.mk_var("y", Sort::Int);
    let zero = terms.mk_int(BigInt::from(0));
    let gt = terms.mk_app(Symbol::named(">"), vec![y, zero], Sort::Bool);
    let or = terms.mk_or(vec![exists, gt]);

    let result = skolemize_deep(&mut terms, or, true);
    assert!(result.is_some(), "exists inside or should be Skolemized");
    assert!(has_skolem_var(&terms, result.unwrap()));
}

/// Not(Forall) inside AND at positive polarity: the Not flips polarity,
/// so the Forall is at negative polarity → Skolemize.
#[test]
fn test_deep_neg_forall_in_and() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Int);
    let zero = terms.mk_int(BigInt::from(0));
    let gt = terms.mk_app(Symbol::named(">"), vec![x, zero], Sort::Bool);
    let forall = terms.mk_forall(vec![("x".to_string(), Sort::Int)], gt);
    let not_forall = terms.mk_not(forall);
    let t = terms.mk_bool(true);
    let and = terms.mk_and(vec![not_forall, t]);

    let result = skolemize_deep(&mut terms, and, true);
    assert!(
        result.is_some(),
        "not(forall) inside and should Skolemize the forall"
    );
    assert!(has_skolem_var(&terms, result.unwrap()));
}

/// Positive Forall should recurse so nested positive Exists can become
/// Skolem functions of the visible universal binders.
#[test]
fn test_deep_positive_forall_skolemizes_nested_exists_with_universal_dependency() {
    let mut terms = TermStore::new();
    let y = terms.mk_var("y", Sort::Int);
    let x = terms.mk_var("x", Sort::Int);
    let gt = terms.mk_gt(x, y);
    let exists = terms.mk_exists(vec![("x".to_string(), Sort::Int)], gt);
    let forall = terms.mk_forall(vec![("y".to_string(), Sort::Int)], exists);

    let result = skolemize_deep(&mut terms, forall, true)
        .expect("nested exists should rewrite under positive forall");
    match terms.get(result).clone() {
        TermData::Forall(vars, body, _) => {
            assert_eq!(vars[0].0, "y");
            match terms.get(body).clone() {
                TermData::App(sym, args) if sym.name() == "<" && args.len() == 2 => {
                    assert_eq!(args[0], y, "rewriter normalizes x > y into y < x");
                    match terms.get(args[1]).clone() {
                        TermData::App(sk_sym, sk_args) => {
                            assert!(
                                sk_sym.name().starts_with("__ay_sk_"),
                                "expected Skolem function application, got {sk_sym:?}"
                            );
                            assert_eq!(
                                sk_args,
                                vec![y],
                                "Skolem function must depend on the outer universal"
                            );
                        }
                        other => panic!("expected Skolem app, got {other:?}"),
                    }
                }
                other => panic!("expected gt body, got {other:?}"),
            }
        }
        other => panic!("expected Forall after rewrite, got {other:?}"),
    }
}

/// The Skolem function argument must stay bound to the outer universal,
/// not be captured by an inner shadowing binder.
#[test]
fn test_deep_positive_forall_renames_shadowing_inner_binder_for_skolem_function() {
    let mut terms = TermStore::new();
    let outer_y = terms.mk_var("y", Sort::Int);
    let x = terms.mk_var("x", Sort::Int);
    let inner_y = terms.mk_var("y", Sort::Int);
    let outer_guard = terms.mk_gt(x, outer_y);
    let sum = terms.mk_add(vec![x, inner_y]);
    let zero = terms.mk_int(BigInt::from(0));
    let gt = terms.mk_gt(sum, zero);
    let inner_forall = terms.mk_forall(vec![("y".to_string(), Sort::Int)], gt);
    let body = terms.mk_and(vec![outer_guard, inner_forall]);
    let exists = terms.mk_exists(vec![("x".to_string(), Sort::Int)], body);
    let outer_forall = terms.mk_forall(vec![("y".to_string(), Sort::Int)], exists);

    let rewritten = skolemize_deep(&mut terms, outer_forall, true)
        .expect("nested forall/exists should rewrite");
    match terms.get(rewritten).clone() {
        TermData::Forall(outer_vars, outer_body, _) => {
            assert_eq!(outer_vars[0].0, "y");
            match terms.get(outer_body).clone() {
                TermData::App(and_sym, outer_conjuncts)
                    if and_sym.name() == "and" && outer_conjuncts.len() == 2 =>
                {
                    let inner_forall = outer_conjuncts
                        .iter()
                        .copied()
                        .find(|term| matches!(terms.get(*term), TermData::Forall(..)))
                        .expect("rewritten body should keep the inner forall");
                    let outer_relation = outer_conjuncts
                        .iter()
                        .copied()
                        .find(|term| !matches!(terms.get(*term), TermData::Forall(..)))
                        .expect("rewritten body should keep the outer free-y guard");

                    match terms.get(outer_relation).clone() {
                        TermData::App(sym, args) if sym.name() == "<" && args.len() == 2 => {
                            assert_eq!(args[0], outer_y);
                            assert!(
                                is_skolem_function_app(&terms, args[1]),
                                "outer guard should use a Skolem function of outer y"
                            );
                        }
                        other => panic!("expected normalized outer guard, got {other:?}"),
                    }

                    match terms.get(inner_forall).clone() {
                        TermData::Forall(inner_vars, inner_body, _) => {
                            assert_ne!(
                                inner_vars[0].0, "y",
                                "inner binder must be alpha-renamed to avoid capture"
                            );
                            match terms.get(inner_body).clone() {
                                TermData::App(sym, args)
                                    if sym.name() == "<" && args.len() == 2 =>
                                {
                                    assert_eq!(args[0], zero);
                                    match terms.get(args[1]).clone() {
                                        TermData::App(sum_sym, sum_args)
                                            if sum_sym.name() == "+" && sum_args.len() == 2 =>
                                        {
                                            assert!(
                                                is_skolem_function_app(&terms, sum_args[0]),
                                                "expected Skolem function in rewritten sum"
                                            );
                                            match terms.get(sum_args[0]).clone() {
                                                TermData::App(_, sk_args) => {
                                                    assert_eq!(sk_args, vec![outer_y]);
                                                }
                                                _ => unreachable!("checked by helper"),
                                            }
                                            match terms.get(sum_args[1]).clone() {
                                                TermData::Var(name, _) => {
                                                    assert_eq!(name, inner_vars[0].0)
                                                }
                                                other => panic!(
                                                    "expected renamed inner binder in sum, got {other:?}"
                                                ),
                                            }
                                        }
                                        other => {
                                            panic!("expected normalized sum rhs, got {other:?}")
                                        }
                                    }
                                }
                                other => {
                                    panic!("expected normalized inner body, got {other:?}")
                                }
                            }
                        }
                        other => panic!("expected nested forall, got {other:?}"),
                    }
                }
                other => panic!("expected conjunction body, got {other:?}"),
            }
        }
        other => panic!("expected outer forall, got {other:?}"),
    }
}

/// Negative Exists: ¬(∃x. P) is converted via NNF to ∀x. ¬P.
/// This is NOT Skolemization — it converts an unhandled negative Exists
/// into a Forall that CEGQI/E-matching can process.
#[test]
fn test_deep_negative_exists_becomes_forall() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Int);
    let five = terms.mk_int(BigInt::from(5));
    let eq = terms.mk_eq(x, five);
    let exists = terms.mk_exists(vec![("x".to_string(), Sort::Int)], eq);
    terms.set_quantifier_id(exists, "qid-negative-exists".to_string());
    terms.set_skolem_id(exists, "skid-negative-exists".to_string());
    terms.set_quantifier_weight(exists, 9);
    terms.set_quantifier_no_patterns(exists, vec![eq]);
    let not_exists = terms.mk_not(exists);

    let result = skolemize_deep(&mut terms, not_exists, true);
    // NNF rewrites ¬(∃x. x=5) → ∀x. ¬(x=5)
    assert!(
        result.is_some(),
        "negative Exists should be converted to Forall via NNF"
    );
    let rewritten = result.unwrap();
    assert_eq!(terms.quantifier_id(rewritten), Some("qid-negative-exists"));
    assert_eq!(terms.skolem_id(rewritten), Some("skid-negative-exists"));
    assert_eq!(terms.quantifier_weight(rewritten), 9);
    assert_eq!(terms.quantifier_no_patterns(rewritten), &[eq]);
    match terms.get(rewritten) {
        TermData::Forall(vars, body, _) => {
            assert_eq!(vars.len(), 1);
            assert_eq!(vars[0].0, "x");
            // Body should be ¬(x = 5)
            match terms.get(*body) {
                TermData::Not(_inner) => {} // ¬(x=5) — correct
                other => panic!("expected Not(...), got {other:?}"),
            }
        }
        other => panic!("expected Forall, got {other:?}"),
    }
}

/// No quantifiers → None.
#[test]
fn test_deep_no_quantifiers() {
    let mut terms = TermStore::new();
    let a = terms.mk_bool(true);
    let b = terms.mk_bool(false);
    let and = terms.mk_and(vec![a, b]);

    assert!(
        skolemize_deep(&mut terms, and, true).is_none(),
        "no quantifiers means no Skolemization"
    );
}

#[test]
fn test_skolemize_implication_antecedent_forall_to_negated_witness_6481() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Int);
    let px = terms.mk_app(Symbol::named("P"), vec![x], Sort::Bool);
    let forall = terms.mk_forall(vec![("x".to_string(), Sort::Int)], px);
    let implication = terms.mk_app(
        Symbol::named("=>"),
        vec![forall, terms.false_term()],
        Sort::Bool,
    );

    let rewritten = skolemize_deep(&mut terms, implication, true)
        .expect("negative-polarity forall in implication antecedent should rewrite");

    let mut disjuncts = Vec::new();
    flatten_or_terms(&terms, rewritten, &mut disjuncts);
    assert!(
        disjuncts
            .iter()
            .copied()
            .any(|id| is_negated_skolem_predicate(&terms, id, "P")),
        "rewritten implication should contain not(P(sk))"
    );
    assert!(
        !disjuncts.iter().copied().any(|id| matches!(
            terms.get(id).clone(),
            TermData::App(sym, args)
                if sym.name() == "P"
                    && args.len() == 1
                    && matches!(terms.get(args[0]), TermData::Var(name, _) if name.starts_with("sk!"))
        )),
        "rewritten implication must not contain positive P(sk)"
    );
}

#[test]
fn test_skolemize_ground_and_forall_antecedent_6481() {
    let mut terms = TermStore::new();
    let a = terms.mk_var("A", Sort::Bool);
    let b = terms.mk_var("B", Sort::Bool);
    let x = terms.mk_var("x", Sort::Int);
    let px = terms.mk_app(Symbol::named("P"), vec![x], Sort::Bool);
    let forall = terms.mk_forall(vec![("x".to_string(), Sort::Int)], px);
    let antecedent = terms.mk_and(vec![a, forall]);
    let implication = terms.mk_app(Symbol::named("=>"), vec![antecedent, b], Sort::Bool);

    let rewritten = skolemize_deep(&mut terms, implication, true)
        .expect("implication antecedent should rewrite under NNF skolemization");

    let mut disjuncts = Vec::new();
    flatten_or_terms(&terms, rewritten, &mut disjuncts);
    let not_a = terms.mk_not(a);
    assert!(
        disjuncts.contains(&not_a),
        "rewritten implication should contain not(A)"
    );
    assert!(
        disjuncts.contains(&b),
        "rewritten implication should contain B"
    );
    assert!(
        disjuncts
            .iter()
            .copied()
            .any(|id| is_negated_skolem_predicate(&terms, id, "P")),
        "rewritten implication should contain not(P(sk))"
    );
}

#[test]
fn test_skolemize_negative_ground_literal_in_changed_antecedent_6481() {
    let mut terms = TermStore::new();
    let a = terms.mk_var("A", Sort::Bool);
    let b = terms.mk_var("B", Sort::Bool);
    let x = terms.mk_var("x", Sort::Int);
    let px = terms.mk_app(Symbol::named("P"), vec![x], Sort::Bool);
    let forall = terms.mk_forall(vec![("x".to_string(), Sort::Int)], px);
    let antecedent = terms.mk_and(vec![a, forall]);
    let implication = terms.mk_app(Symbol::named("=>"), vec![antecedent, b], Sort::Bool);

    let rewritten = skolemize_deep(&mut terms, implication, true)
        .expect("implication antecedent should rewrite under NNF skolemization");

    let not_a = terms.mk_not(a);
    assert_ne!(rewritten, implication, "rewritten term must change shape");
    let mut disjuncts = Vec::new();
    flatten_or_terms(&terms, rewritten, &mut disjuncts);
    assert!(
        disjuncts.contains(&not_a),
        "adjacent ground literal in antecedent must become negated when the implication is rewritten"
    );
}

// ---- Finite domain expansion tests (#5848) ----

/// forall ((b Bool)) body → expand and simplify.
/// `(forall ((b Bool)) (or b (not b)))` is a tautology — expansion produces
/// `(and (or true false) (or false true))` which simplifies to `true`.
#[test]
fn test_finite_domain_forall_bool() {
    let mut terms = TermStore::new();
    let b = terms.mk_var("b", Sort::Bool);
    // body: (or b (not b))
    let not_b = terms.mk_not(b);
    let body = terms.mk_or(vec![b, not_b]);
    let forall = terms.mk_forall(vec![("b".to_string(), Sort::Bool)], body);

    let result = finite_domain_expand(&mut terms, forall);
    assert!(result.is_some(), "forall Bool should expand");
    // Tautology should simplify to true
    let expanded = result.unwrap();
    match terms.get(expanded).clone() {
        TermData::Const(ay_core::Constant::Bool(true)) => {} // expected
        other => panic!("expected true constant, got {other:?}"),
    }
}

/// exists ((b Bool)) body → expand to (or body[b:=true] body[b:=false]).
#[test]
fn test_finite_domain_exists_bool() {
    let mut terms = TermStore::new();
    let b = terms.mk_var("b", Sort::Bool);
    let exists = terms.mk_exists(vec![("b".to_string(), Sort::Bool)], b);

    let result = finite_domain_expand(&mut terms, exists);
    assert!(result.is_some(), "exists Bool should expand");
}

/// Int variable → not finite → returns None.
#[test]
fn test_finite_domain_int_not_expanded() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Int);
    let five = terms.mk_int(BigInt::from(5));
    let eq = terms.mk_eq(x, five);
    let forall = terms.mk_forall(vec![("x".to_string(), Sort::Int)], eq);

    assert!(
        finite_domain_expand(&mut terms, forall).is_none(),
        "Int var should not be expanded"
    );
}

/// Non-quantifier → returns None.
#[test]
fn test_finite_domain_non_quantifier() {
    let mut terms = TermStore::new();
    let t = terms.mk_bool(true);

    assert!(
        finite_domain_expand(&mut terms, t).is_none(),
        "non-quantifier should return None"
    );
}

/// Bounded integer forall: `(forall ((i Int)) (=> (and (<= 0 i) (<= i 2)) (< i 10)))`
/// The body `(< i 10)` does not overlap with the guard, so De Morgan
/// simplification won't collapse the implies.
#[test]
fn test_finite_domain_bounded_int_forall() {
    let mut terms = TermStore::new();
    let i = terms.mk_var("i", Sort::Int);
    let zero = terms.mk_int(BigInt::from(0));
    let two = terms.mk_int(BigInt::from(2));
    let ten = terms.mk_int(BigInt::from(10));
    // guard: (and (<= 0 i) (<= i 2))
    let le_0_i = terms.mk_le(zero, i);
    let le_i_2 = terms.mk_le(i, two);
    let guard = terms.mk_and(vec![le_0_i, le_i_2]);
    // body: (< i 10) — not part of the guard
    let lt_i_10 = terms.mk_lt(i, ten);
    let implies = terms.mk_implies(guard, lt_i_10);
    let forall = terms.mk_forall(vec![("i".to_string(), Sort::Int)], implies);

    let result = finite_domain_expand(&mut terms, forall);
    assert!(result.is_some(), "bounded int forall [0,2] should expand");
}

/// Bounded integer forall with strict less-than:
/// `(forall ((i Int)) (=> (and (<= 0 i) (< i 3)) (< i 10)))` → range [0,2]
#[test]
fn test_finite_domain_bounded_int_strict_lt() {
    let mut terms = TermStore::new();
    let i = terms.mk_var("i", Sort::Int);
    let zero = terms.mk_int(BigInt::from(0));
    let three = terms.mk_int(BigInt::from(3));
    let ten = terms.mk_int(BigInt::from(10));
    let le_0_i = terms.mk_le(zero, i);
    let lt_i_3 = terms.mk_lt(i, three);
    let guard = terms.mk_and(vec![le_0_i, lt_i_3]);
    let lt_i_10 = terms.mk_lt(i, ten);
    let implies = terms.mk_implies(guard, lt_i_10);
    let forall = terms.mk_forall(vec![("i".to_string(), Sort::Int)], implies);

    let result = finite_domain_expand(&mut terms, forall);
    assert!(
        result.is_some(),
        "bounded int forall [0,2] with strict lt should expand"
    );
}

/// Exists with bounded integer:
/// `(exists ((i Int)) (and (<= 0 i) (<= i 5) (= i 3)))` → expand to disjunction
#[test]
fn test_finite_domain_bounded_int_exists() {
    let mut terms = TermStore::new();
    let i = terms.mk_var("i", Sort::Int);
    let zero = terms.mk_int(BigInt::from(0));
    let five = terms.mk_int(BigInt::from(5));
    let three = terms.mk_int(BigInt::from(3));
    let le_0_i = terms.mk_le(zero, i);
    let le_i_5 = terms.mk_le(i, five);
    let eq_i_3 = terms.mk_eq(i, three);
    let body = terms.mk_and(vec![le_0_i, le_i_5, eq_i_3]);
    let exists = terms.mk_exists(vec![("i".to_string(), Sort::Int)], body);

    let result = finite_domain_expand(&mut terms, exists);
    assert!(result.is_some(), "bounded int exists [0,5] should expand");
}

// --- classA_residual_halfbounded: half-bounded existential fold + miniscope ---

/// `(exists ((X Int)) (<= X 4))` folds to `true` (the half-line is non-empty).
#[test]
fn test_fold_half_bounded_exists_to_true() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("X0", Sort::Int);
    let four = terms.mk_int(BigInt::from(4));
    let le = terms.mk_le(x, four);
    let exists = terms.mk_exists(vec![("X0".to_string(), Sort::Int)], le);

    let folded = expand_finite_domain_subterms(&mut terms, exists);
    assert!(
        matches!(
            terms.get(folded),
            TermData::Const(ay_core::Constant::Bool(true))
        ),
        "half-bounded `(exists X. X<=4)` must fold to true, got {:?}",
        terms.get(folded)
    );
}

/// The residual fix end-to-end at the term level:
/// `(not (exists X. (<= X 4)))` collapses to `false` (so the disjunct vanishes,
/// not a spurious refutation of the residual).
#[test]
fn test_fold_not_half_bounded_exists_to_false() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("X0", Sort::Int);
    let four = terms.mk_int(BigInt::from(4));
    let le = terms.mk_le(x, four);
    let exists = terms.mk_exists(vec![("X0".to_string(), Sort::Int)], le);
    let not_exists = terms.mk_not(exists);

    let folded = expand_finite_domain_subterms(&mut terms, not_exists);
    assert!(
        matches!(
            terms.get(folded),
            TermData::Const(ay_core::Constant::Bool(false))
        ),
        "`(not (exists X. X<=4))` must fold to false, got {:?}",
        terms.get(folded)
    );
}

/// UNSOUNDNESS GUARD: `(exists X. (< X X))` is UNSATISFIABLE and must NOT be
/// folded to true (both operands mention the bound variable).
#[test]
fn test_fold_rejects_reflexive_unsat_exists() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("X0", Sort::Int);
    let lt = terms.mk_lt(x, x);
    let exists = terms.mk_exists(vec![("X0".to_string(), Sort::Int)], lt);

    let out = expand_finite_domain_subterms(&mut terms, exists);
    assert_eq!(
        out, exists,
        "`(exists X. (< X X))` is UNSAT and must be left intact (not folded to true)"
    );
}

/// MINISCOPE: `(exists X. (and (<= X 4) p))` pulls the X-free conjunct `p` OUT,
/// becoming `(and <exists-core> p)`, and the half-bounded core then folds to
/// true so the whole reduces to `p` (the residual survives).
#[test]
fn test_miniscope_exists_over_and_preserves_residual() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("X0", Sort::Int);
    let four = terms.mk_int(BigInt::from(4));
    let p = terms.mk_var("p", Sort::Bool);
    let le = terms.mk_le(x, four);
    let body = terms.mk_and(vec![le, p]);
    let exists = terms.mk_exists(vec![("X0".to_string(), Sort::Int)], body);

    let out = expand_finite_domain_subterms(&mut terms, exists);
    // After miniscoping the X-free `p` out and folding `(exists X. X<=4)` to
    // true, the result is `(and true p)` (the recursive App rebuild interns
    // without Boolean simplification; the SAT layer treats it as `p`). The key
    // soundness property is: the residual `p` SURVIVED (it is no longer trapped
    // inside the existential) and no spurious refutation was introduced.
    let true_t = terms.mk_bool(true);
    match terms.get(out).clone() {
        TermData::App(Symbol::Named(op), args) if op == "and" => {
            assert!(
                args.contains(&p),
                "residual `p` must survive miniscoping, got {:?}",
                terms.get(out)
            );
            assert!(
                args.iter().all(|&a| a == p || a == true_t),
                "miniscope core must fold to `true`, got {:?}",
                terms.get(out)
            );
        }
        // If a future simplification collapses `(and true p)` to `p`, accept it.
        _ => assert_eq!(
            out,
            p,
            "miniscope+fold must reduce to (and true p) or p, got {:?}",
            terms.get(out)
        ),
    }
}

/// The `forall`-over-`OR` direction is NOT rewritten: `(forall X. (or (> X 4) p))`
/// is left intact (it is SAT; forall does not distribute over OR, and the prior
/// unsound implementation of that rewrite is deliberately absent).
#[test]
fn test_no_forall_over_or_rewrite() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("X0", Sort::Int);
    let four = terms.mk_int(BigInt::from(4));
    let p = terms.mk_var("p", Sort::Bool);
    let gt = terms.mk_gt(x, four);
    let body = terms.mk_or(vec![gt, p]);
    let forall = terms.mk_forall(vec![("X0".to_string(), Sort::Int)], body);

    let out = expand_finite_domain_subterms(&mut terms, forall);
    assert_eq!(
        out, forall,
        "`(forall X. (or (> X 4) p))` must be left intact (no forall-over-OR rewrite)"
    );
}

/// Rank-9 step 1: a provably-EMPTY bounded-Int `exists` folds to `false`
/// (`(exists ((x Int)) (and (<= 5 x) (<= x 3) p))` has an empty range).
#[test]
fn test_finite_domain_empty_range_exists_folds_false() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Int);
    let five = terms.mk_int(BigInt::from(5));
    let three = terms.mk_int(BigInt::from(3));
    let p = terms.mk_var("p", Sort::Bool);
    let lo = terms.mk_le(five, x);
    let hi = terms.mk_le(x, three);
    let body = terms.mk_and(vec![lo, hi, p]);
    let exists = terms.mk_exists(vec![("x".to_string(), Sort::Int)], body);

    let result = finite_domain_expand(&mut terms, exists).expect("empty range should fold");
    match terms.get(result).clone() {
        TermData::Const(ay_core::Constant::Bool(false)) => {}
        other => panic!("expected false constant, got {other:?}"),
    }
}

/// Rank-9 step 1: a `forall` whose recognized guard range is empty folds to
/// `true` (`(forall ((x Int)) (or (not (<= 5 x)) (not (<= x 3)) p))`).
#[test]
fn test_finite_domain_empty_range_forall_folds_true() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Int);
    let five = terms.mk_int(BigInt::from(5));
    let three = terms.mk_int(BigInt::from(3));
    let p = terms.mk_var("p", Sort::Bool);
    let lo = terms.mk_le(five, x);
    let hi = terms.mk_le(x, three);
    let not_lo = terms.mk_not(lo);
    let not_hi = terms.mk_not(hi);
    let body = terms.mk_or(vec![not_lo, not_hi, p]);
    let forall = terms.mk_forall(vec![("x".to_string(), Sort::Int)], body);

    let result = finite_domain_expand(&mut terms, forall).expect("empty range should fold");
    match terms.get(result).clone() {
        TermData::Const(ay_core::Constant::Bool(true)) => {}
        other => panic!("expected true constant, got {other:?}"),
    }
}

/// Rank-9 step 1: the extended budget applies ONLY to bodies with a
/// bound-dependent Bool UF. A 300-wide range with a Bool UF expands; the same
/// range with a pure-arith body keeps the 256 budget (returns None).
#[test]
fn test_finite_domain_extended_budget_gated_on_bool_uf() {
    let mut terms = TermStore::new();
    // With Bool UF: expands (301 <= 512).
    let x = terms.mk_var("x", Sort::Int);
    let zero = terms.mk_int(BigInt::from(0));
    let three_hundred = terms.mk_int(BigInt::from(300));
    let lo = terms.mk_le(zero, x);
    let hi = terms.mk_le(x, three_hundred);
    let p_of_x = terms.mk_app(Symbol::Named("P".to_string()), vec![x], Sort::Bool);
    let body = terms.mk_and(vec![lo, hi, p_of_x]);
    let exists = terms.mk_exists(vec![("x".to_string(), Sort::Int)], body);
    assert!(
        finite_domain_expand(&mut terms, exists).is_some(),
        "301-wide Bool-UF-dependent exists should use the extended budget"
    );

    // Pure arithmetic body at the same width: stays with the 256 budget.
    let y = terms.mk_var("y", Sort::Int);
    let lo_y = terms.mk_le(zero, y);
    let hi_y = terms.mk_le(y, three_hundred);
    let seven = terms.mk_int(BigInt::from(7));
    let eq = terms.mk_eq(y, seven);
    let body_y = terms.mk_and(vec![lo_y, hi_y, eq]);
    let exists_y = terms.mk_exists(vec![("y".to_string(), Sort::Int)], body_y);
    assert!(
        finite_domain_expand(&mut terms, exists_y).is_none(),
        "301-wide pure-arith exists must keep the 256 budget (CEGQI handles it)"
    );
}

/// Rank-9 step 1: past the extended 512 budget even Bool-UF bodies fall back
/// (Skolemization / certificate route), and extreme i64 bounds do not
/// overflow the width computation.
#[test]
fn test_finite_domain_extended_budget_cap_and_i64_extremes() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Int);
    let zero = terms.mk_int(BigInt::from(0));
    let wide = terms.mk_int(BigInt::from(600));
    let lo = terms.mk_le(zero, x);
    let hi = terms.mk_le(x, wide);
    let p_of_x = terms.mk_app(Symbol::Named("P".to_string()), vec![x], Sort::Bool);
    let body = terms.mk_and(vec![lo, hi, p_of_x]);
    let exists = terms.mk_exists(vec![("x".to_string(), Sort::Int)], body);
    assert!(
        finite_domain_expand(&mut terms, exists).is_none(),
        "601-wide exists exceeds the extended budget"
    );

    // i64::MIN / i64::MAX bounds: width overflows i64 subtraction — must be
    // computed in i128 and simply exceed the budget (None), not panic.
    let y = terms.mk_var("y", Sort::Int);
    let min = terms.mk_int(BigInt::from(i64::MIN));
    let max = terms.mk_int(BigInt::from(i64::MAX));
    let lo_y = terms.mk_le(min, y);
    let hi_y = terms.mk_le(y, max);
    let p_of_y = terms.mk_app(Symbol::Named("P".to_string()), vec![y], Sort::Bool);
    let body_y = terms.mk_and(vec![lo_y, hi_y, p_of_y]);
    let exists_y = terms.mk_exists(vec![("y".to_string(), Sort::Int)], body_y);
    assert!(
        finite_domain_expand(&mut terms, exists_y).is_none(),
        "i64-extreme bounds must not overflow and must exceed the budget"
    );
}

// ---- Bounded BV-guard forall expansion tests (#seq-from-fn discharge) ----

/// `(forall ((i (_ BitVec 64))) (=> (bvult i 2) (= (select s i) i)))` with a
/// LITERAL bound expands to the exact conjunction of the two guarded
/// instances — the deductive-checks `seq_from_fn` axiom shape.
#[test]
fn test_finite_domain_bounded_bv_forall_bvult_literal() {
    let mut terms = TermStore::new();
    let bv64 = Sort::bitvec(64);
    let i = terms.mk_var("i", bv64.clone());
    let two = terms.mk_bitvec(BigInt::from(2), 64);
    let guard = terms.mk_bvult(i, two);
    let body_app = terms.mk_app(Symbol::Named("P".to_string()), vec![i], Sort::Bool);
    let implies = terms.mk_implies(guard, body_app);
    let forall = terms.mk_forall(vec![("i".to_string(), bv64)], implies);

    let result = finite_domain_expand(&mut terms, forall);
    assert!(
        result.is_some(),
        "bvult-literal-bounded BV64 forall must expand"
    );
    // Every conjunct must be ground (no residual quantifier / bound var).
    let expanded = result.unwrap();
    assert!(
        !crate::ematching::contains_quantifier(&terms, expanded),
        "expansion must discharge the quantifier"
    );
}

/// A symbolic (non-literal) bound must NOT expand: enumerating a superset of
/// the guarded region would be strictly stronger than the quantifier
/// (#guard-must-bind).
#[test]
fn test_finite_domain_bounded_bv_forall_symbolic_bound_rejected() {
    let mut terms = TermStore::new();
    let bv64 = Sort::bitvec(64);
    let i = terms.mk_var("i", bv64.clone());
    let n = terms.mk_var("n", bv64.clone());
    let guard = terms.mk_bvult(i, n);
    let body_app = terms.mk_app(Symbol::Named("P".to_string()), vec![i], Sort::Bool);
    let implies = terms.mk_implies(guard, body_app);
    let forall = terms.mk_forall(vec![("i".to_string(), bv64)], implies);

    assert!(
        finite_domain_expand(&mut terms, forall).is_none(),
        "symbolic BV bound must not expand"
    );
}

/// A guard range wider than the combo budget must not expand.
#[test]
fn test_finite_domain_bounded_bv_forall_wide_range_rejected() {
    let mut terms = TermStore::new();
    let bv64 = Sort::bitvec(64);
    let i = terms.mk_var("i", bv64.clone());
    let wide = terms.mk_bitvec(BigInt::from(100_000), 64);
    let guard = terms.mk_bvult(i, wide);
    let body_app = terms.mk_app(Symbol::Named("P".to_string()), vec![i], Sort::Bool);
    let implies = terms.mk_implies(guard, body_app);
    let forall = terms.mk_forall(vec![("i".to_string(), bv64)], implies);

    assert!(
        finite_domain_expand(&mut terms, forall).is_none(),
        "100000-wide BV guard range exceeds the budget"
    );
}

/// `(and (bvult 5 i) (bvult i 2))` pins the binder to a provably-empty range
/// (lo 6 > hi 1): the forall is vacuously true.
#[test]
fn test_finite_domain_bounded_bv_forall_empty_range_vacuous_true() {
    let mut terms = TermStore::new();
    let bv64 = Sort::bitvec(64);
    let i = terms.mk_var("i", bv64.clone());
    let five = terms.mk_bitvec(BigInt::from(5), 64);
    let two = terms.mk_bitvec(BigInt::from(2), 64);
    let g_lo = terms.mk_bvult(five, i);
    let g_hi = terms.mk_bvult(i, two);
    let guard = terms.mk_and(vec![g_lo, g_hi]);
    let body_app = terms.mk_app(Symbol::Named("P".to_string()), vec![i], Sort::Bool);
    let implies = terms.mk_implies(guard, body_app);
    let forall = terms.mk_forall(vec![("i".to_string(), bv64)], implies);

    let result = finite_domain_expand(&mut terms, forall);
    assert!(result.is_some(), "empty BV guard range must fold");
    match terms.get(result.unwrap()).clone() {
        TermData::Const(ay_core::Constant::Bool(true)) => {}
        other => panic!("expected vacuous true, got {other:?}"),
    }
}

// --- Hilbert-choice provenance of a Skolem CONSTANT
// --- (`register_skolem_choice_provenance`).
//
// The proof exporter needs to spell `sk!x` as the term it DENOTES. Only the
// mint site knows that term, so it is recorded here and nowhere else. Scope is
// deliberately narrow — see the function's own docs — and an unregistered
// witness costs a printable proof, never a verdict.

/// The witness of `∃x. B` denotes `εx. B`, so its recorded body is `B` itself.
#[test]
fn positive_exists_records_the_choice_body_verbatim() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Int);
    let five = terms.mk_int(BigInt::from(5));
    let eq = terms.mk_eq(x, five);
    let exists = terms.mk_exists(vec![("x".to_string(), Sort::Int)], eq);

    let body = skolemize(&mut terms, exists, false).expect("positive Exists Skolemizes");
    let TermData::App(_, args) = terms.get(body).clone() else {
        panic!("expected the substituted equality")
    };
    let witness = args
        .iter()
        .copied()
        .find(|&id| matches!(terms.get(id), TermData::Var(name, _) if name.starts_with("sk!x_")))
        .expect("a Skolem witness");

    let choice = terms
        .skolem_choice(witness)
        .expect("the mint site must record what the witness denotes");
    assert_eq!(choice.binder, "x");
    assert_eq!(choice.sort, Sort::Int);
    assert_eq!(
        choice.body, eq,
        "the choice body is the SOURCE body, still mentioning the binder — not \
         the substituted instance"
    );
}

/// `¬∀x. B ≡ ∃x. ¬B`, so the witness denotes `εx. ¬B` — the NEGATED body.
/// Recording `B` here would state the opposite of what the proof uses.
#[test]
fn negative_forall_records_the_negated_choice_body() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Int);
    let px = terms.mk_app(Symbol::named("P"), vec![x], Sort::Bool);
    let forall = terms.mk_forall(vec![("x".to_string(), Sort::Int)], px);

    let body = skolemize(&mut terms, forall, true).expect("negated Forall Skolemizes");
    let TermData::Not(inner) = terms.get(body).clone() else {
        panic!("expected a negated instance")
    };
    let TermData::App(_, args) = terms.get(inner).clone() else {
        panic!("expected the substituted application")
    };
    let witness = args[0];

    let choice = terms
        .skolem_choice(witness)
        .expect("the mint site must record what the witness denotes");
    assert_eq!(choice.binder, "x");
    let TermData::Not(negated_of) = terms.get(choice.body).clone() else {
        panic!(
            "the recorded choice body must be a negation, got {:?}",
            terms.get(choice.body)
        )
    };
    assert_eq!(negated_of, px);
}

/// A MULTI-binder quantifier's correct witnesses are nested choices
/// (`sk₁ = εx₁. ∃x₂. B`, `sk₂ = (εx₂. B)[x₁ := sk₁]`), which this site does not
/// build. Registering the one-binder form would state something false, so
/// nothing is registered and the Alethe export DECLINES rather than spelling a
/// witness it cannot justify.
#[test]
fn multi_binder_exists_registers_no_choice() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Int);
    let y = terms.mk_var("y", Sort::Int);
    let body = terms.mk_app(Symbol::named("R"), vec![x, y], Sort::Bool);
    let exists = terms.mk_exists(
        vec![("x".to_string(), Sort::Int), ("y".to_string(), Sort::Int)],
        body,
    );

    let instance = skolemize(&mut terms, exists, false).expect("Skolemizes");
    let TermData::App(_, args) = terms.get(instance).clone() else {
        panic!("expected the substituted application")
    };
    for witness in args {
        assert!(
            terms.skolem_choice(witness).is_none(),
            "a multi-binder witness has no single-binder choice term"
        );
    }
}

/// A witness that DEPENDS on enclosing universals is a Skolem FUNCTION
/// application, not a constant, and denotes no single choice term.
#[test]
fn dependent_skolem_function_registers_no_choice() {
    let mut terms = TermStore::new();
    let y = terms.mk_var("y", Sort::Int);
    let x = terms.mk_var("x", Sort::Int);
    let body = terms.mk_app(Symbol::named("R"), vec![x, y], Sort::Bool);
    let inner = terms.mk_exists(vec![("x".to_string(), Sort::Int)], body);
    let outer = terms.mk_forall(vec![("y".to_string(), Sort::Int)], inner);

    let (rewritten, _) = skolemize_deep_with_provenance(&mut terms, outer, true);
    let rewritten = rewritten.expect("the nested existential Skolemizes");
    let TermData::Forall(_, forall_body, _) = terms.get(rewritten).clone() else {
        panic!("the universal must survive")
    };
    let TermData::App(_, args) = terms.get(forall_body).clone() else {
        panic!("expected the substituted application")
    };
    let witness = args[0];
    assert!(
        matches!(terms.get(witness), TermData::App(..)),
        "a dependent witness is a Skolem function application"
    );
    assert!(terms.skolem_choice(witness).is_none());
}
