// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The kernel gaps the hub's verifiers found (K2), one regression each:
//! - assumptions are internalized and scanned like assertions;
//! - difference logic is chosen only when it can carry every hub term;
//! - a user declaration's private identity (`__ay_overload_N`) is
//!   uninterpreted, an unregistered internal name still is not;
//! - the search does not follow `TermId`s (KC9; an end-to-end smoke check,
//!   the regressions are unit tests in `internalize.rs`, `hub/tests.rs` and
//!   `term_key.rs`);
//! - an equality minted over an `ite` stays an atom (lia-on-lra's ite links),
//!   and every check starts with the links (their conditions have variables);
//! - the kernel never has to catch up with an unannounced backjump.

use ay_cdclt::{CheckOutcome, Engine, EngineConfig, Guard, ModelVerdict, Verdict};
use ay_core::{Sort, Symbol, TermId, TermStore};
use num_bigint::BigInt;

fn app(terms: &mut TermStore, f: &str, args: Vec<TermId>, sort: Sort) -> TermId {
    terms.mk_app(Symbol::named(f), args, sort)
}

fn u() -> Sort {
    Sort::Uninterpreted("U".to_string())
}

fn int(terms: &mut TermStore, n: i64) -> TermId {
    terms.mk_int(BigInt::from(n))
}

/// One check of `asserts` under `assumptions`; with a `sat` verdict, the
/// exact model check of the assertions and the assumptions.
fn run(
    terms: &mut TermStore,
    asserts: &[TermId],
    assumptions: &[TermId],
    cfg: EngineConfig,
) -> (CheckOutcome, Option<ModelVerdict>, Vec<&'static str>) {
    let mut engine = Engine::new(cfg);
    for &a in asserts {
        engine.assert(a);
    }
    let outcome = engine.check(terms, assumptions, &Guard::new());
    let model = (outcome.verdict == Verdict::Sat)
        .then(|| engine.check_model(terms, &[asserts, assumptions].concat()));
    (outcome, model, engine.plugin_names())
}

/// An application, a term-level `ite` or a `distinct` that only an
/// assumption holds is registered with the hub: `p(f(a))` assumed with
/// `¬p(f(b)) ∧ a = b` asserted is refuted by congruence, and the assumption
/// is the failed one.
#[test]
fn assumptions_are_internalized_like_assertions() {
    let mut terms = TermStore::new();
    let [a, b, c] = ["a", "b", "c"].map(|n| terms.mk_var(n, u()));
    let fa = app(&mut terms, "f", vec![a], u());
    let fb = app(&mut terms, "f", vec![b], u());
    let pfa = app(&mut terms, "p", vec![fa], Sort::Bool);
    let pfb = app(&mut terms, "p", vec![fb], Sort::Bool);
    let not_pfb = terms.mk_not(pfb);
    let ab = terms.mk_eq(a, b);
    let (out, _, _) = run(&mut terms, &[not_pfb, ab], &[pfa], EngineConfig::default());
    assert_eq!(out.verdict, Verdict::Unsat, "{:?}", out.reason);
    assert_eq!(out.failed, vec![pfa]);

    // `f(a) = c` only in the assumption, `f(b) ≠ c` asserted: unsat.
    let fa_c = terms.mk_eq(fa, c);
    let fb_c = terms.mk_eq(fb, c);
    let not_fb_c = terms.mk_not(fb_c);
    let (out, _, _) = run(
        &mut terms,
        &[not_fb_c, ab],
        &[fa_c],
        EngineConfig::default(),
    );
    assert_eq!(out.verdict, Verdict::Unsat, "{:?}", out.reason);
    // Without `a = b` it is sat, and the model satisfies the assumption.
    let (out, model, _) = run(&mut terms, &[not_fb_c], &[fa_c], EngineConfig::default());
    assert_eq!(out.verdict, Verdict::Sat, "{:?}", out.reason);
    assert_eq!(model, Some(ModelVerdict::Satisfied));

    // A term-level ite only in the assumption: `f(ite(k, a, b)) = c` with
    // `k` and `f(a) ≠ c` asserted is unsat; with `¬k` it is sat.
    let k = terms.mk_var("k", Sort::Bool);
    let ite = terms.mk_ite(k, a, b);
    let fi = app(&mut terms, "f", vec![ite], u());
    let fi_c = terms.mk_eq(fi, c);
    let not_fa_c = terms.mk_not(fa_c);
    let (out, _, _) = run(&mut terms, &[k, not_fa_c], &[fi_c], EngineConfig::default());
    assert_eq!(out.verdict, Verdict::Unsat, "{:?}", out.reason);
    let not_k = terms.mk_not(k);
    let (out, model, _) = run(
        &mut terms,
        &[not_k, not_fa_c],
        &[fi_c],
        EngineConfig::default(),
    );
    assert_eq!(out.verdict, Verdict::Sat, "{:?}", out.reason);
    assert_eq!(model, Some(ModelVerdict::Satisfied));

    // A distinct only in the assumption.
    let d = terms.mk_app(Symbol::named("distinct"), vec![a, b, c], Sort::Bool);
    let (out, _, _) = run(&mut terms, &[ab], &[d], EngineConfig::default());
    assert_eq!(out.verdict, Verdict::Unsat, "{:?}", out.reason);
    assert_eq!(out.failed, vec![d]);
}

/// `f(x) = 1 ∧ x ≠ x + y`: the hub watches `x = x + y` (one side is a node)
/// and so holds `x + y`, which difference logic cannot carry. The atoms
/// alone are difference atoms; the check goes to the simplex before the
/// search instead of giving up in it. A shared term DL can carry keeps DL.
#[test]
fn difference_logic_is_chosen_only_for_hub_terms_it_carries() {
    for sort in [Sort::Int, Sort::Real] {
        let mut terms = TermStore::new();
        let x = terms.mk_var("x", sort.clone());
        let y = terms.mk_var("y", sort.clone());
        let fx = app(&mut terms, "f", vec![x], sort.clone());
        let one = if sort == Sort::Int {
            int(&mut terms, 1)
        } else {
            terms.mk_rational(num_rational::BigRational::from_integer(BigInt::from(1)))
        };
        let f1 = terms.mk_eq(fx, one);
        let sum = terms.mk_add(vec![x, y]);
        let eq = terms.mk_app(Symbol::named("="), vec![x, sum], Sort::Bool);
        let ne = terms.mk_not(eq);
        let (out, model, plugins) = run(&mut terms, &[f1, ne], &[], EngineConfig::default());
        assert_eq!(out.verdict, Verdict::Sat, "{sort:?}: {:?}", out.reason);
        assert_eq!(model, Some(ModelVerdict::Satisfied));
        assert!(
            !plugins.iter().any(|p| p.starts_with("dl")),
            "{sort:?}: {plugins:?}"
        );
    }
    // `x = y + 1` beside `f(x) = 1`: `y + 1` is a vertex plus a constant.
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Int);
    let y = terms.mk_var("y", Sort::Int);
    let fx = app(&mut terms, "f", vec![x], Sort::Int);
    let one = int(&mut terms, 1);
    let f1 = terms.mk_eq(fx, one);
    let y1 = terms.mk_add(vec![y, one]);
    let eq = terms.mk_app(Symbol::named("="), vec![x, y1], Sort::Bool);
    let (out, model, plugins) = run(&mut terms, &[f1, eq], &[], EngineConfig::default());
    assert_eq!(out.verdict, Verdict::Sat, "{:?}", out.reason);
    assert_eq!(model, Some(ModelVerdict::Satisfied));
    assert!(plugins.contains(&"dl-int"), "{plugins:?}");
}

/// A function re-declared after `pop`, or declared under a builtin's name,
/// reaches the store under a private identity the declaring layer
/// registers: the kernel decides it as an uninterpreted function. An
/// internal name nobody registered still gives up before the search.
#[test]
fn registered_private_identities_are_uninterpreted() {
    let mut terms = TermStore::new();
    terms.register_declared_function("__ay_overload_0");
    let [a, b] = ["a", "b"].map(|n| terms.mk_var(n, u()));
    let gab = app(&mut terms, "__ay_overload_0", vec![a, b], Sort::Bool);
    let gba = app(&mut terms, "__ay_overload_0", vec![b, a], Sort::Bool);
    let not_gba = terms.mk_not(gba);
    let ab = terms.mk_eq(a, b);
    let (out, _, _) = run(&mut terms, &[gab, not_gba], &[], EngineConfig::default());
    assert_eq!(out.verdict, Verdict::Sat, "{:?}", out.reason);
    let (out, _, _) = run(
        &mut terms,
        &[gab, not_gba, ab],
        &[],
        EngineConfig::default(),
    );
    assert_eq!(out.verdict, Verdict::Unsat, "{:?}", out.reason);

    // A user `abs : Real -> Real` (renamed): `abs(x) > 1 ∧ x = y ∧ abs(y) < 0`.
    terms.register_declared_function("__ay_overload_1");
    let x = terms.mk_var("x", Sort::Real);
    let y = terms.mk_var("y", Sort::Real);
    let hx = app(&mut terms, "__ay_overload_1", vec![x], Sort::Real);
    let hy = app(&mut terms, "__ay_overload_1", vec![y], Sort::Real);
    let one = terms.mk_rational(num_rational::BigRational::from_integer(BigInt::from(1)));
    let zero = terms.mk_rational(num_rational::BigRational::from_integer(BigInt::from(0)));
    let gt = terms.mk_gt(hx, one);
    let lt = terms.mk_lt(hy, zero);
    let xy = terms.mk_eq(x, y);
    let (out, _, _) = run(&mut terms, &[gt, lt, xy], &[], EngineConfig::default());
    assert_eq!(out.verdict, Verdict::Unsat, "{:?}", out.reason);

    let hidden = app(&mut terms, "__ay_internal_g", vec![a], Sort::Bool);
    let (out, _, _) = run(&mut terms, &[hidden], &[], EngineConfig::default());
    assert_eq!(out.verdict, Verdict::Unknown);
    let reason = out.reason.unwrap_or_default();
    assert!(reason.contains("no plug-in owns operator"), "{reason}");
}

/// The hub audit's KC9 probe: term-level ites under applications, built in
/// two stores whose `TermId`s differ by an offset (unrelated terms interned
/// first). Names, node order and explanations follow content, so the two
/// searches are the same search. (An end-to-end smoke check: an offset keeps
/// the relative order of `TermId`s, so the kernel before K2 passed it too.
/// The regressions are the unit tests `ite_names_follow_content_not_term_ids`,
/// `explanations_follow_node_order_not_term_ids` and
/// `equality_keys_ignore_side_order`.)
#[test]
fn the_search_does_not_follow_term_ids() {
    let build = |pad: usize| {
        let mut terms = TermStore::new();
        for i in 0..pad {
            let p = terms.mk_var(format!("pad{i}"), Sort::Bool);
            let _ = terms.mk_not(p);
        }
        let asserts = diamond_ites(&mut terms, 10);
        let (out, _, _) = run(&mut terms, &asserts, &[], EngineConfig::lane_parity());
        assert_ne!(out.verdict, Verdict::Unknown, "{:?}", out.reason);
        (
            out.verdict,
            out.stats.sat_conflicts,
            out.stats.sat_decisions,
            out.stats.hub_merges,
        )
    };
    let plain = build(0);
    assert!(plain.1 > 0, "the probe must search: {plain:?}");
    for pad in [3, 17, 40] {
        assert_eq!(build(pad), plain, "padding {pad} changed the search");
    }
}

/// The audit's `kc9/a.smt2`, for `n` variables.
fn diamond_ites(terms: &mut TermStore, n: usize) -> Vec<TermId> {
    let f1 = |terms: &mut TermStore, x| app(terms, "f", vec![x], u());
    let g2 = |terms: &mut TermStore, x, y| app(terms, "g", vec![x, y], u());
    let x: Vec<TermId> = (0..n).map(|i| terms.mk_var(format!("x{i}"), u())).collect();
    let y: Vec<TermId> = (0..n).map(|i| terms.mk_var(format!("y{i}"), u())).collect();
    let c: Vec<TermId> = (0..n)
        .map(|i| terms.mk_var(format!("c{i}"), Sort::Bool))
        .collect();
    let mut out = Vec::new();
    for i in 0..n {
        let (i1, i2, i3, i5) = ((i + 1) % n, (i + 2) % n, (i + 3) % n, (i + 5) % n);
        let ite = terms.mk_ite(c[i], x[i], y[i]);
        let (fi, fx) = (f1(terms, ite), f1(terms, x[i1]));
        let left = terms.mk_eq(fi, fx);
        let ite2 = terms.mk_ite(c[i3], y[i], x[i]);
        let gi = g2(terms, ite2, x[i2]);
        let right = terms.mk_eq(gi, y[i5]);
        out.push(terms.mk_or(vec![left, right]));
        let xy = terms.mk_eq(x[i], y[(3 * i) % n]);
        let nxy = terms.mk_not(xy);
        let (fxi, gyi) = (f1(terms, x[i]), g2(terms, y[i], x[(i + 4) % n]));
        let fg = terms.mk_eq(fxi, gyi);
        out.push(terms.mk_or(vec![nxy, c[i1], fg]));
    }
    for i in 0..n {
        let fx = f1(terms, x[i]);
        let ffx = f1(terms, fx);
        let d = terms.mk_eq(ffx, y[(i + 7) % n]);
        out.push(terms.mk_not(d));
    }
    out
}

/// lia-on-lra links an arithmetic `ite` to its branches with
/// `¬c ∨ (= (ite c x y) x)`. The equality must be minted as an atom: the
/// store's `mk_eq` rewrites it to `(or ...)`, which no plug-in owns (the
/// BRP give-up).
#[test]
fn ite_link_equalities_stay_atoms() {
    let mut terms = TermStore::new();
    let k = terms.mk_var("k", Sort::Bool);
    let x = terms.mk_var("x", Sort::Int);
    let y = terms.mk_var("y", Sort::Int);
    let ite = terms.mk_ite(k, x, y);
    let three = int(&mut terms, 3);
    let five = int(&mut terms, 5);
    let small = terms.mk_le(ite, three);
    let big = terms.mk_ge(x, five);
    let (out, _, plugins) = run(&mut terms, &[small, k, big], &[], EngineConfig::default());
    assert_eq!(out.verdict, Verdict::Unsat, "{:?}", out.reason);
    assert!(plugins.contains(&"lia-on-lra"), "{plugins:?}");
    let (out, model, _) = run(&mut terms, &[small, big], &[], EngineConfig::default());
    assert_eq!(out.verdict, Verdict::Sat, "{:?}", out.reason);
    assert_eq!(model, Some(ModelVerdict::Satisfied));
}

/// Every check starts with the link definitions of its arithmetic ites
/// (`¬c ∨ (= (ite c x y) x)`, `c ∨ (= (ite c x y) y)`):
/// - the condition has a SAT variable even when it occurs nowhere else
///   (BRP1's `(ite (and ..) ..)` under a comparison: an `and` minted as an
///   atom has no owner, the give-up after the `or` one);
/// - the links hold in a second check on the same store: the LRA lane asks
///   for a link only while the store lacks its equality, so after a first
///   check had made them the `ite` was a free variable (`sat`, with a model
///   that violates the assertions).
#[test]
fn ite_links_hold_in_every_check() {
    let mut terms = TermStore::new();
    let [p, q] = ["p", "q"].map(|n| terms.mk_var(n, Sort::Bool));
    let x = terms.mk_var("x", Sort::Int);
    let y = terms.mk_var("y", Sort::Int);
    let both = terms.mk_and(vec![p, q]);
    let ite = terms.mk_ite(both, x, y);
    let three = int(&mut terms, 3);
    let five = int(&mut terms, 5);
    let small = terms.mk_le(ite, three);
    let big = terms.mk_ge(x, five);
    for round in 0..2 {
        let (out, _, plugins) = run(
            &mut terms,
            &[small, p, q, big],
            &[],
            EngineConfig::default(),
        );
        assert_eq!(
            out.verdict,
            Verdict::Unsat,
            "round {round}: {:?}",
            out.reason
        );
        assert!(plugins.contains(&"lia-on-lra"), "{plugins:?}");
        assert!(out.stats.definitions >= 2, "round {round}: {:?}", out.stats);
    }
    let not_q = terms.mk_not(q);
    let (out, model, _) = run(
        &mut terms,
        &[small, p, not_q, big],
        &[],
        EngineConfig::default(),
    );
    assert_eq!(out.verdict, Verdict::Sat, "{:?}", out.reason);
    assert_eq!(model, Some(ModelVerdict::Satisfied));
}

/// ay-sat announces every backjump (its reduction's jump to level 0 for
/// out-of-order units included), so the kernel's fail-safe never runs: on
/// the transitivity diamond, which used to need it, `resyncs` reads 0.
#[test]
fn the_kernel_never_catches_up_with_an_unannounced_backjump() {
    for n in [12, 20] {
        let mut terms = TermStore::new();
        let x: Vec<TermId> = (0..=n)
            .map(|i| terms.mk_var(format!("x{i}"), u()))
            .collect();
        let mut asserts = Vec::new();
        for i in 0..n {
            let y = terms.mk_var(format!("y{i}"), u());
            let z = terms.mk_var(format!("z{i}"), u());
            let up = [terms.mk_eq(x[i], y), terms.mk_eq(y, x[i + 1])];
            let down = [terms.mk_eq(x[i], z), terms.mk_eq(z, x[i + 1])];
            let (up, down) = (terms.mk_and(up.to_vec()), terms.mk_and(down.to_vec()));
            asserts.push(terms.mk_or(vec![up, down]));
        }
        let fx0 = app(&mut terms, "f", vec![x[0]], u());
        let fxn = app(&mut terms, "f", vec![x[n]], u());
        let ends = terms.mk_eq(fx0, fxn);
        asserts.push(terms.mk_not(ends));
        for cfg in [EngineConfig::default(), EngineConfig::lane_parity()] {
            let (out, _, _) = run(&mut terms, &asserts, &[], cfg);
            assert_eq!(out.verdict, Verdict::Unsat, "{:?}", out.reason);
            assert_eq!(out.stats.resyncs, 0, "n = {n}: {:?}", out.stats);
        }
    }
}
