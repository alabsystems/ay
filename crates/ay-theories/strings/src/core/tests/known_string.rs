// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Explained ground values (`known_string_with_reasons`): a query reuses each
//! equivalence class's member scan per depth instead of walking it again per
//! visit, and keeps the depth cap.
//!
//! Regression for a hang: the resolver recursed from every member of a class
//! back into the members of the same class with `depth + 1`, so a class of
//! `k` members with no constant cost `(k-1)^16` calls before the depth cap.
//! `check_regex_membership_violations` asks it on every check, and on cvc5
//! `issue8481` (60 s test) and the #3890 `replace_re_all` membership (10 s
//! test) one call outlived the executor's 10 s budget.

use super::*;
use crate::core::explanation::known_string::KnownStringResolver;
use ay_core::TheoryResult;

fn string_vars(terms: &mut TermStore, names: &[&str]) -> Vec<TermId> {
    names
        .iter()
        .map(|n| terms.mk_var(*n, Sort::String))
        .collect()
}

fn concat(terms: &mut TermStore, args: Vec<TermId>) -> TermId {
    terms.mk_app(Symbol::named("str.++"), args, Sort::String)
}

/// Assert `a = b` and return its literal.
fn assert_equal(terms: &mut TermStore, state: &mut SolverState, a: TermId, b: TermId) -> TheoryLit {
    let eq = terms.mk_eq(a, b);
    state.assert_literal(terms, eq, true);
    TheoryLit::new(eq, true)
}

/// Assert `t ∈ "Z"` and run the ground membership check.
fn membership_check_fires(terms: &mut TermStore, state: &mut SolverState, t: TermId) -> bool {
    let z = terms.mk_string("Z".to_string());
    let re = terms.mk_app(Symbol::named("str.to_re"), vec![z], Sort::RegLan);
    let in_re = terms.mk_app(Symbol::named("str.in_re"), vec![t, re], Sort::Bool);
    state.assert_literal(terms, in_re, true);
    let mut infer = InferenceManager::new();
    CoreSolver::new().check_regex_membership_violations(terms, state, &mut infer)
}

/// `x = y1 = … = y6` with no constant: the class has seven members and no
/// value. The query scans the class once and answers `None`; the old
/// resolver made 6^16 calls here and never returned.
#[test]
fn unresolved_wide_class_is_scanned_once() {
    let mut terms = TermStore::new();
    let vars = string_vars(&mut terms, &["x", "y1", "y2", "y3", "y4", "y5", "y6"]);
    let mut state = SolverState::new();
    for pair in vars.windows(2) {
        assert_equal(&mut terms, &mut state, pair[0], pair[1]);
    }

    let mut resolver = KnownStringResolver::new(&terms, &state);
    assert_eq!(resolver.resolve(vars[0]), None);
    assert_eq!(resolver.scans, 1, "one class, one member scan");
}

/// The same wide class through the ground membership check, which is where
/// the hang surfaced: no value, so no conflict, and the call returns.
#[test]
fn membership_check_over_wide_unresolved_class_returns() {
    let mut terms = TermStore::new();
    let vars = string_vars(&mut terms, &["x", "y1", "y2", "y3", "y4", "y5", "y6"]);
    let mut state = SolverState::new();
    for pair in vars.windows(2) {
        assert_equal(&mut terms, &mut state, pair[0], pair[1]);
    }
    assert!(!membership_check_fires(&mut terms, &mut state, vars[0]));
}

/// `x = y1 = … = y5 = "ab"·v·"cd"` with `v = ""`: the value comes from the
/// concat member, and the reasons name every equality on the chain plus
/// `v = ""`.
#[test]
fn wide_class_resolves_through_its_concat_member() {
    let mut terms = TermStore::new();
    let vars = string_vars(&mut terms, &["x", "y1", "y2", "y3", "y4", "y5", "v"]);
    let (chain, v) = (&vars[..6], vars[6]);
    let ab = terms.mk_string("ab".to_string());
    let cd = terms.mk_string("cd".to_string());
    let empty = terms.mk_string(String::new());
    let member = concat(&mut terms, vec![ab, v, cd]);
    let mut state = SolverState::new();
    let mut expected: Vec<TheoryLit> = Vec::new();
    for pair in chain.windows(2) {
        expected.push(assert_equal(&mut terms, &mut state, pair[0], pair[1]));
    }
    expected.push(assert_equal(&mut terms, &mut state, chain[5], member));
    expected.push(assert_equal(&mut terms, &mut state, v, empty));

    let mut resolver = KnownStringResolver::new(&terms, &state);
    let (value, reasons) = resolver
        .resolve(chain[0])
        .expect("x = \"abcd\" is entailed");
    assert_eq!(value, "abcd");
    for lit in expected {
        assert!(
            reasons.contains(&lit),
            "every literal behind x = \"abcd\" must be named: {reasons:?}"
        );
    }
}

/// `z_i = z_{i+1}·z_{i+1}` for `i < 7` and `z_7 = "a"`: each class is
/// scanned once although every level names the next class twice (the old
/// resolver doubled its work per level), and the reasons name each of the
/// eight literals once (without deduplication `z_7 = "a"` alone would
/// appear 128 times).
#[test]
fn shared_classes_are_scanned_once() {
    let mut terms = TermStore::new();
    let names = ["z0", "z1", "z2", "z3", "z4", "z5", "z6", "z7"];
    let z = string_vars(&mut terms, &names);
    let a = terms.mk_string("a".to_string());
    let mut state = SolverState::new();
    for i in 0..7 {
        let doubled = concat(&mut terms, vec![z[i + 1], z[i + 1]]);
        assert_equal(&mut terms, &mut state, z[i], doubled);
    }
    assert_equal(&mut terms, &mut state, z[7], a);

    let mut resolver = KnownStringResolver::new(&terms, &state);
    let (value, reasons) = resolver.resolve(z[0]).expect("z0 = a^128 is entailed");
    assert_eq!(value, "a".repeat(128));
    assert_eq!(resolver.scans, 7, "z0..z6 are scanned once each");
    assert_eq!(
        reasons.len(),
        8,
        "the seven doubling equalities and z7 = a, each once: {reasons:?}"
    );
}

/// The memo does not reach past `MAX_RESOLVE_DEPTH`: `z_i = z_{i+1}·z_{i+1}`
/// for `i < 40`, `z_40 = "a"`. From depth 1, `z33` (7 levels above the
/// constant) is in reach and `z26` (14 levels) is not, so `z33·z26` has no
/// value. A value cache that ignored depth would answer `2^7 + 2^14` chars
/// out of `z33`'s cached chain, and every further entry seven levels up
/// multiplies the string by 128 (`z33·z26·z19·z12` needs over 8 GB).
#[test]
fn cached_class_values_keep_the_depth_cap() {
    let mut terms = TermStore::new();
    let names: Vec<String> = (0..=40).map(|i| format!("z{i}")).collect();
    let names: Vec<&str> = names.iter().map(String::as_str).collect();
    let z = string_vars(&mut terms, &names);
    let a = terms.mk_string("a".to_string());
    let mut state = SolverState::new();
    for i in 0..40 {
        let doubled = concat(&mut terms, vec![z[i + 1], z[i + 1]]);
        assert_equal(&mut terms, &mut state, z[i], doubled);
    }
    assert_equal(&mut terms, &mut state, z[40], a);

    let in_reach = concat(&mut terms, vec![z[33], z[33]]);
    let (value, _) = KnownStringResolver::new(&terms, &state)
        .resolve(in_reach)
        .expect("z33 = a^128 is within the depth cap");
    assert_eq!(value.len(), 256);
    let probe = concat(&mut terms, vec![z[33], z[26]]);
    assert_eq!(
        KnownStringResolver::new(&terms, &state).resolve(probe),
        None
    );
}

/// `x = y·w`, `y = x·w`, `y = u·v`, `u = "a"`, `v = "b"`, `w = ""`: the
/// cycle between the classes of `x` and `y` is unfolded only down to the
/// depth cap, and `y` resolves through `u·v`. Without `y = u·v` nothing
/// resolves and the query still returns.
#[test]
fn cyclic_classes_terminate() {
    for with_exit in [true, false] {
        let mut terms = TermStore::new();
        let vars = string_vars(&mut terms, &["x", "y", "w", "u", "v"]);
        let (x, y, w, u, v) = (vars[0], vars[1], vars[2], vars[3], vars[4]);
        let (sa, sb, empty) = (
            terms.mk_string("a".to_string()),
            terms.mk_string("b".to_string()),
            terms.mk_string(String::new()),
        );
        let y_w = concat(&mut terms, vec![y, w]);
        let x_w = concat(&mut terms, vec![x, w]);
        let u_v = concat(&mut terms, vec![u, v]);
        let mut state = SolverState::new();
        let mut expected = vec![
            assert_equal(&mut terms, &mut state, x, y_w),
            assert_equal(&mut terms, &mut state, y, x_w),
            assert_equal(&mut terms, &mut state, w, empty),
        ];
        if with_exit {
            expected.push(assert_equal(&mut terms, &mut state, y, u_v));
            expected.push(assert_equal(&mut terms, &mut state, u, sa));
            expected.push(assert_equal(&mut terms, &mut state, v, sb));
        }

        let got = KnownStringResolver::new(&terms, &state).resolve(x);
        if !with_exit {
            assert_eq!(got, None, "nothing outside the cycle gives x a value");
            continue;
        }
        let (value, reasons) = got.expect("x = \"ab\" is entailed through y = u.v");
        assert_eq!(value, "ab");
        for lit in [
            expected[0],
            expected[2],
            expected[3],
            expected[4],
            expected[5],
        ] {
            assert!(
                reasons.contains(&lit),
                "the reasons must name {lit:?}: {reasons:?}"
            );
        }
    }
}

/// `a = b·w = u·w`, `b = a·z`, `u = "q"`, `w = z = ""` (satisfiable:
/// `a = b = "q"`): the cycle between the classes of `a` and `b` is walked
/// only down to the depth cap, and both resolve through `u·w`, each naming
/// the literals behind its value.
#[test]
fn cyclic_concat_classes_resolve_through_their_exit() {
    let mut terms = TermStore::new();
    let vars = string_vars(&mut terms, &["a", "b", "u", "w", "z"]);
    let (a, b, u, w, z) = (vars[0], vars[1], vars[2], vars[3], vars[4]);
    let (sq, empty) = (
        terms.mk_string("q".to_string()),
        terms.mk_string(String::new()),
    );
    let b_w = concat(&mut terms, vec![b, w]);
    let u_w = concat(&mut terms, vec![u, w]);
    let a_z = concat(&mut terms, vec![a, z]);
    let mut state = SolverState::new();
    assert_equal(&mut terms, &mut state, a, b_w);
    let a_uw = assert_equal(&mut terms, &mut state, a, u_w);
    let b_az = assert_equal(&mut terms, &mut state, b, a_z);
    let u_q = assert_equal(&mut terms, &mut state, u, sq);
    let w_e = assert_equal(&mut terms, &mut state, w, empty);
    let z_e = assert_equal(&mut terms, &mut state, z, empty);
    let members = &state
        .get_eqc(&state.find(a))
        .expect("a has a class")
        .members;
    let at = |t: TermId| members.iter().position(|&m| m == t);
    assert!(
        at(b_w) < at(u_w),
        "precondition: the scan of a's class meets b.w (the cycle) before u.w"
    );

    for (t, must) in [
        (a, vec![a_uw, u_q, w_e]),
        (b, vec![b_az, a_uw, u_q, w_e, z_e]),
    ] {
        let (value, reasons) = KnownStringResolver::new(&terms, &state)
            .resolve(t)
            .expect("a = b = \"q\" is entailed");
        assert_eq!(value, "q");
        for lit in must {
            assert!(
                reasons.contains(&lit),
                "the reasons must name {lit:?}: {reasons:?}"
            );
        }
    }
}

/// `x = u·"a" = u1·"a" = u2·"a"` with `u = u1 = u2` unresolved: `u`'s
/// class fails once at its depth, and that failure answers the two later
/// visits at the same depth.
#[test]
fn failed_class_is_not_rescanned_at_the_same_depth() {
    let mut terms = TermStore::new();
    let vars = string_vars(&mut terms, &["x", "u", "u1", "u2"]);
    let x = vars[0];
    let tail = terms.mk_string("a".to_string());
    let mut state = SolverState::new();
    assert_equal(&mut terms, &mut state, vars[1], vars[2]);
    assert_equal(&mut terms, &mut state, vars[2], vars[3]);
    for &u in &vars[1..] {
        let member = concat(&mut terms, vec![u, tail]);
        assert_equal(&mut terms, &mut state, x, member);
    }

    let mut resolver = KnownStringResolver::new(&terms, &state);
    assert_eq!(resolver.resolve(x), None);
    assert_eq!(resolver.scans, 2, "x once, u once");
}

/// `x = m1 = m2`: `m1` nests `b` fifteen concats deep, so its visit of `b`
/// runs out of depth budget and fails; `m2 = b·""` then visits `b` shallowly,
/// where `b = u·w = "q"` resolves. A failure recorded at a deep visit must
/// not answer a shallower one.
#[test]
fn deep_failure_does_not_answer_a_shallower_visit() {
    let mut terms = TermStore::new();
    let vars = string_vars(&mut terms, &["x", "b", "u", "w"]);
    let (x, b, u, w) = (vars[0], vars[1], vars[2], vars[3]);
    let q = terms.mk_string("q".to_string());
    let empty = terms.mk_string(String::new());
    let u_w = concat(&mut terms, vec![u, w]);
    let mut deep = b;
    for _ in 0..15 {
        deep = concat(&mut terms, vec![empty, deep]);
    }
    let shallow = concat(&mut terms, vec![b, empty]);
    let mut state = SolverState::new();
    assert_equal(&mut terms, &mut state, x, deep);
    assert_equal(&mut terms, &mut state, x, shallow);
    assert_equal(&mut terms, &mut state, b, u_w);
    assert_equal(&mut terms, &mut state, u, q);
    assert_equal(&mut terms, &mut state, w, empty);
    let members = &state
        .get_eqc(&state.find(x))
        .expect("x has a class")
        .members;
    let at = |t: TermId| members.iter().position(|&m| m == t);
    assert!(
        at(deep) < at(shallow),
        "precondition: the deep member is scanned first"
    );

    let resolved = KnownStringResolver::new(&terms, &state).resolve(x);
    assert_eq!(resolved.map(|(s, _)| s).as_deref(), Some("q"));
}

/// Forty classes `A_i = A_j·w_i` for every `j > i`, each also tied back by
/// `A_i = A_{i-1}·w_i`, with no constant anywhere: the work stays at most
/// one scan per class per depth. A resolver that re-opened a class each
/// time a cycle through it closed made about 32 million scans here.
#[test]
fn dense_cyclic_classes_scan_each_class_at_most_once_per_depth() {
    const N: usize = 40;
    let mut terms = TermStore::new();
    let names: Vec<String> = (0..N).map(|i| format!("A{i}")).collect();
    let names: Vec<&str> = names.iter().map(String::as_str).collect();
    let classes = string_vars(&mut terms, &names);
    let names: Vec<String> = (0..N).map(|i| format!("w{i}")).collect();
    let names: Vec<&str> = names.iter().map(String::as_str).collect();
    let tails = string_vars(&mut terms, &names);
    let mut state = SolverState::new();
    for i in 0..N {
        let back = i.checked_sub(1);
        for j in back.into_iter().chain(i + 1..N) {
            let member = concat(&mut terms, vec![classes[j], tails[i]]);
            assert_equal(&mut terms, &mut state, classes[i], member);
        }
    }

    let mut resolver = KnownStringResolver::new(&terms, &state);
    assert_eq!(resolver.resolve(classes[0]), None);
    let bound = (CoreSolver::MAX_RESOLVE_DEPTH + 1) * N;
    assert!(
        resolver.scans <= bound,
        "{} scans exceed one per class per depth ({bound})",
        resolver.scans
    );
}

/// `x` joined to `"ab"·v` by a merge with NO reason, `v = ""` asserted: the
/// link `x = "ab"·v` is unexplained, so `x` must not resolve and the ground
/// membership check must not fire (empty-explanation laundering is a
/// false-UNSAT, #3826/#6273). Negative twin of `explained_links_resolve`.
#[test]
fn unexplained_member_link_fails_closed() {
    let mut terms = TermStore::new();
    let vars = string_vars(&mut terms, &["x", "v"]);
    let (x, v) = (vars[0], vars[1]);
    let ab = terms.mk_string("ab".to_string());
    let empty = terms.mk_string(String::new());
    let member = concat(&mut terms, vec![ab, v]);
    let mut state = SolverState::new();
    state.register_term(&terms, x);
    state.register_term(&terms, member);
    let _ = state.merge_with_explanation(x, member, &[]);
    assert_eq!(state.find(x), state.find(member));
    assert!(
        state.explain(x, member).is_empty(),
        "precondition: the link is unexplained"
    );
    assert_equal(&mut terms, &mut state, v, empty);
    assert_eq!(KnownStringResolver::new(&terms, &state).resolve(x), None);
    assert!(!membership_check_fires(&mut terms, &mut state, x));
}

/// `y` joined to `"ab"` by a merge with no reason, `x = y·"c"` asserted: `x`
/// must not resolve through the unexplained `y = "ab"`.
#[test]
fn unexplained_constant_link_fails_closed() {
    let mut terms = TermStore::new();
    let vars = string_vars(&mut terms, &["x", "y"]);
    let (x, y) = (vars[0], vars[1]);
    let ab = terms.mk_string("ab".to_string());
    let c = terms.mk_string("c".to_string());
    let y_c = concat(&mut terms, vec![y, c]);
    let mut state = SolverState::new();
    state.register_term(&terms, y);
    state.register_term(&terms, ab);
    let _ = state.merge_with_explanation(y, ab, &[]);
    assert!(
        state.explain(y, ab).is_empty(),
        "precondition: the link is unexplained"
    );
    assert_equal(&mut terms, &mut state, x, y_c);
    assert_eq!(KnownStringResolver::new(&terms, &state).resolve(x), None);
}

/// Positive control for the two fail-closed tests: the same links asserted
/// as literals resolve.
#[test]
fn explained_links_resolve() {
    let mut terms = TermStore::new();
    let vars = string_vars(&mut terms, &["x", "v", "y", "w"]);
    let (x, v, y, w) = (vars[0], vars[1], vars[2], vars[3]);
    let ab = terms.mk_string("ab".to_string());
    let c = terms.mk_string("c".to_string());
    let empty = terms.mk_string(String::new());
    let member = concat(&mut terms, vec![ab, v]);
    let y_c = concat(&mut terms, vec![y, c]);
    let mut state = SolverState::new();
    assert_equal(&mut terms, &mut state, x, member);
    assert_equal(&mut terms, &mut state, v, empty);
    assert_equal(&mut terms, &mut state, y, ab);
    assert_equal(&mut terms, &mut state, w, y_c);
    let mut resolver = KnownStringResolver::new(&terms, &state);
    assert_eq!(resolver.resolve(x).map(|(s, _)| s).as_deref(), Some("ab"));
    assert_eq!(resolver.resolve(w).map(|(s, _)| s).as_deref(), Some("abc"));
}

/// The ground membership conflict built on a wide class still names every
/// literal behind the value (caching a class value must not drop the
/// explanation of how this term reaches it).
#[test]
fn membership_conflict_through_wide_class_names_the_chain() {
    let mut terms = TermStore::new();
    let vars = string_vars(&mut terms, &["x", "y1", "y2", "y3", "v"]);
    let (chain, v) = (&vars[..4], vars[4]);
    let ab = terms.mk_string("ab".to_string());
    let empty = terms.mk_string(String::new());
    let member = concat(&mut terms, vec![ab, v]);
    let mut state = SolverState::new();
    let mut expected: Vec<TheoryLit> = Vec::new();
    for pair in chain.windows(2) {
        expected.push(assert_equal(&mut terms, &mut state, pair[0], pair[1]));
    }
    expected.push(assert_equal(&mut terms, &mut state, chain[3], member));
    expected.push(assert_equal(&mut terms, &mut state, v, empty));
    let z = terms.mk_string("Z".to_string());
    let re = terms.mk_app(Symbol::named("str.to_re"), vec![z], Sort::RegLan);
    let in_re = terms.mk_app(Symbol::named("str.in_re"), vec![chain[0], re], Sort::Bool);
    state.assert_literal(&terms, in_re, true);
    expected.push(TheoryLit::new(in_re, true));

    let mut infer = InferenceManager::new();
    let mut core = CoreSolver::new();
    assert!(core.check_regex_membership_violations(&terms, &state, &mut infer));
    let TheoryResult::Unsat(conflict) = infer.to_theory_result() else {
        panic!("a fired membership check must yield Unsat");
    };
    for lit in expected {
        assert!(
            conflict.contains(&lit),
            "x = \"ab\" is outside \"Z\" only because of {lit:?}: {conflict:?}"
        );
    }
}
