// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Unit tests for the `reduce-args` pass.

use super::*;
use ay_core::Sort;
use num_bigint::BigInt;
use std::collections::BTreeSet;

fn int(t: &mut TermStore, n: i64) -> TermId {
    t.mk_int(BigInt::from(n))
}

/// Collect every App-symbol name and Var name reachable from `root`.
fn names(t: &TermStore, root: TermId, out: &mut BTreeSet<String>) {
    match t.get(root).clone() {
        TermData::Const(_) => {}
        TermData::Var(n, _) => {
            out.insert(n);
        }
        TermData::Not(i) => names(t, i, out),
        TermData::Ite(a, b, c) => {
            names(t, a, out);
            names(t, b, out);
            names(t, c, out);
        }
        TermData::App(s, args) => {
            out.insert(s.name().to_string());
            for a in args {
                names(t, a, out);
            }
        }
        TermData::Let(bs, b) => {
            for (_, v) in bs {
                names(t, v, out);
            }
            names(t, b, out);
        }
        TermData::Forall(_, b, _) | TermData::Exists(_, b, _) => names(t, b, out),
        _ => {}
    }
}

fn all_names(t: &TermStore, assertions: &[TermId]) -> BTreeSet<String> {
    let mut out = BTreeSet::new();
    for &a in assertions {
        names(t, a, &mut out);
    }
    out
}

/// Does any App applying `name` (arity ≥ 1) appear in the assertions?
fn has_app(t: &TermStore, assertions: &[TermId], name: &str) -> bool {
    fn go(t: &TermStore, r: TermId, name: &str) -> bool {
        match t.get(r).clone() {
            TermData::App(s, args) => {
                (s.name() == name && !args.is_empty()) || args.iter().any(|&a| go(t, a, name))
            }
            TermData::Not(i) => go(t, i, name),
            TermData::Ite(a, b, c) => go(t, a, name) || go(t, b, name) || go(t, c, name),
            TermData::Let(bs, b) => bs.iter().any(|(_, v)| go(t, *v, name)) || go(t, b, name),
            TermData::Forall(_, b, _) | TermData::Exists(_, b, _) => go(t, b, name),
            _ => false,
        }
    }
    assertions.iter().any(|&a| go(t, a, name))
}

#[test]
fn reduce_shared_constant_position() {
    // (= (f 1 x) 3), (= (f 1 5) 7): position 0 always 1 ==> single f!0 (arity 1).
    let mut t = TermStore::new();
    let x = t.mk_var("x", Sort::Int);
    let one = int(&mut t, 1);
    let five = int(&mut t, 5);
    let three = int(&mut t, 3);
    let seven = int(&mut t, 7);
    let f1x = t.mk_app(Symbol::named("f"), vec![one, x], Sort::Int);
    let f15 = t.mk_app(Symbol::named("f"), vec![one, five], Sort::Int);
    let e1 = t.mk_eq(f1x, three);
    let e2 = t.mk_eq(f15, seven);

    let mut a = vec![e1, e2];
    assert!(ReduceArgs::new().apply(&mut t, &mut a));
    assert!(has_app(&t, &a, "f!0"), "specialized f!0 present");
    assert!(!has_app(&t, &a, "f"), "original f dropped");
    assert!(!has_app(&t, &a, "f!1"), "one tuple => only f!0");
}

#[test]
fn reduce_distinct_tuples_get_distinct_symbols() {
    // (= (f 1 x) 3), (= (f 2 5) 7): tuples (1) and (2) ==> f!0 and f!1.
    let mut t = TermStore::new();
    let x = t.mk_var("x", Sort::Int);
    let one = int(&mut t, 1);
    let two = int(&mut t, 2);
    let five = int(&mut t, 5);
    let three = int(&mut t, 3);
    let seven = int(&mut t, 7);
    let f1x = t.mk_app(Symbol::named("f"), vec![one, x], Sort::Int);
    let f25 = t.mk_app(Symbol::named("f"), vec![two, five], Sort::Int);
    let e1 = t.mk_eq(f1x, three);
    let e2 = t.mk_eq(f25, seven);

    let mut a = vec![e1, e2];
    assert!(ReduceArgs::new().apply(&mut t, &mut a));
    assert!(has_app(&t, &a, "f!0"));
    assert!(has_app(&t, &a, "f!1"));
    assert!(!has_app(&t, &a, "f"));
}

#[test]
fn reduce_predicate() {
    // (p x true), (not (p 3 true)): position 1 always true ==> p!0.
    let mut t = TermStore::new();
    let x = t.mk_var("x", Sort::Int);
    let three = int(&mut t, 3);
    let tt = t.mk_bool(true);
    let px = t.mk_app(Symbol::named("p"), vec![x, tt], Sort::Bool);
    let p3 = t.mk_app(Symbol::named("p"), vec![three, tt], Sort::Bool);
    let np3 = t.mk_not(p3);

    let mut a = vec![px, np3];
    assert!(ReduceArgs::new().apply(&mut t, &mut a));
    assert!(has_app(&t, &a, "p!0"));
    assert!(!has_app(&t, &a, "p"));
}

#[test]
fn reduce_all_const_to_nullary_constant() {
    // (> (f 1) 5) with f arity 1, always 1 ==> f!0 as a 0-ary constant (a Var).
    let mut t = TermStore::new();
    let one = int(&mut t, 1);
    let five = int(&mut t, 5);
    let f1 = t.mk_app(Symbol::named("f"), vec![one], Sort::Int);
    let gt = t.mk_app(Symbol::named(">"), vec![f1, five], Sort::Bool);

    let mut a = vec![gt];
    assert!(ReduceArgs::new().apply(&mut t, &mut a));
    // No App named "f" survives; f!0 exists as a nullary Var.
    assert!(!has_app(&t, &a, "f"));
    assert!(!has_app(&t, &a, "f!0"), "nullary => not an application");
    assert!(
        all_names(&t, &a).contains("f!0"),
        "f!0 present as a constant"
    );
}

#[test]
fn reduce_collision_with_user_symbol_advances_name() {
    // A user-declared const `f!0` must NOT be aliased by the specialization —
    // interned-by-name mk_var would otherwise capture it. reduce-args skips to
    // f!1.
    let mut t = TermStore::new();
    let user_f0 = t.mk_var("f!0", Sort::Int); // user's declared constant
    let x = t.mk_var("x", Sort::Int);
    let one = int(&mut t, 1);
    let five = int(&mut t, 5);
    let seven = int(&mut t, 7);
    let f1x = t.mk_app(Symbol::named("f"), vec![one, x], Sort::Int);
    let f15 = t.mk_app(Symbol::named("f"), vec![one, five], Sort::Int);
    let e1 = t.mk_eq(f1x, user_f0); // (= (f 1 x) f!0)
    let e2 = t.mk_eq(f15, seven);

    let mut a = vec![e1, e2];
    assert!(ReduceArgs::new().apply(&mut t, &mut a));
    // The specialized function is f!1 (f!0 is the user's constant), and the
    // user's f!0 Var still appears.
    assert!(
        has_app(&t, &a, "f!1"),
        "specialization dodged the collision"
    );
    assert!(
        !has_app(&t, &a, "f!0"),
        "f!0 name is the user's, not a function"
    );
    assert!(
        all_names(&t, &a).contains("f!0"),
        "user f!0 constant preserved"
    );
}

#[test]
fn reduce_traverses_quantifier_bodies_symmetrically() {
    // f occurs inside a forall AND outside; both must be specialized to f!0.
    let mut t = TermStore::new();
    let x = t.mk_var("x", Sort::Int);
    let y = t.mk_var("y", Sort::Int);
    let one = int(&mut t, 1);
    let three = int(&mut t, 3);
    let f1x = t.mk_app(Symbol::named("f"), vec![one, x], Sort::Int);
    let outside = t.mk_eq(f1x, three);
    let f1y = t.mk_app(Symbol::named("f"), vec![one, y], Sort::Int);
    let inner = t.mk_eq(f1y, y);
    let fa = t.mk_forall(vec![("y".into(), Sort::Int)], inner);

    let mut a = vec![outside, fa];
    assert!(ReduceArgs::new().apply(&mut t, &mut a));
    assert!(!has_app(&t, &a, "f"), "no un-specialized f remains");
    assert!(has_app(&t, &a, "f!0"), "both occurrences use f!0");
}

#[test]
fn reduce_is_identity_when_no_position_is_always_constant() {
    // (= (f x 5) 3), (= (f 5 y) 7): neither position is const in all occurrences.
    let mut t = TermStore::new();
    let x = t.mk_var("x", Sort::Int);
    let y = t.mk_var("y", Sort::Int);
    let five = int(&mut t, 5);
    let three = int(&mut t, 3);
    let seven = int(&mut t, 7);
    let fx5 = t.mk_app(Symbol::named("f"), vec![x, five], Sort::Int);
    let f5y = t.mk_app(Symbol::named("f"), vec![five, y], Sort::Int);
    let e1 = t.mk_eq(fx5, three);
    let e2 = t.mk_eq(f5y, seven);

    let mut a = vec![e1, e2];
    assert!(
        !ReduceArgs::new().apply(&mut t, &mut a),
        "no mask => no change"
    );
    assert_eq!(a, vec![e1, e2]);
}
