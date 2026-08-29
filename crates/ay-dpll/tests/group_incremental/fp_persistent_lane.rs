// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Barriers for the persistent incremental FP lane
//! (`executor::theories::fp::incremental`).
//!
//! Before it existed, `solve_fp` built `Tseitin::new`,
//! `FpSolver::new_with_tseitin` and `SatSolver::new` function-locally on every
//! check-sat, so push/pop never reached the FP lane at all. Making one SAT
//! solver serve the session introduces four ways to publish a WRONG answer,
//! and there is one test here per way:
//!
//! 1. an assertion activated inside a push must not survive the pop;
//! 2. an assertion re-asserted after a pop must be re-ACTIVATED;
//! 3. the FP variable offset must be frozen, or the circuit constraining a bit
//!    and the clause reading it name different SAT variables;
//! 4. a Bool that is named only by a LATER assertion must be tied to the FP
//!    proxy literal an earlier `ite` decomposition froze into the mux.
//!
//! Plus one mechanism barrier proving the session really is one solver, and
//! one barrier on the decline path.
//!
//! Every verdict asserted here was independently confirmed with bitwuzla 0.9.1
//! and cvc5 1.3.0.

use crate::common::solve_authored_vec;

/// Every script in this file, plus the two mechanism scripts, run under BOTH
/// settings of `--no-fp-incremental`. Used by the equivalence barrier below.
fn lane_scripts() -> Vec<(&'static str, String)> {
    vec![
        (
            "scoped contradiction",
            format!(
                "{DECLS}(assert (fp.lt x y))\n(push 1)\n(assert (fp.gt x y))\n\
                 (check-sat)\n(pop 1)\n(check-sat)\n(push 1)\n\
                 (assert (fp.isNormal x))\n(check-sat)\n"
            ),
        ),
        (
            "reactivation",
            format!(
                "{DECLS}(assert (fp.lt x y))\n(push 1)\n(assert (fp.gt x y))\n\
                 (check-sat)\n(pop 1)\n(check-sat)\n(push 1)\n\
                 (assert (fp.gt x y))\n(check-sat)\n"
            ),
        ),
        (
            "frontier moved by Boolean structure",
            format!(
                "{DECLS}(declare-fun p () Bool)\n(declare-fun q () Bool)\n\
                 (push 1)\n(assert (fp.lt x y))\n(check-sat)\n(push 1)\n\
                 (assert (and p q))\n(assert (fp.geq x y))\n(check-sat)\n"
            ),
        ),
        (
            "ite bool condition named later",
            format!(
                "{DECLS}(declare-fun b () Bool)\n(push 1)\n\
                 (assert (fp.lt (ite b x y) z))\n(check-sat)\n(push 1)\n\
                 (assert b)\n(assert (fp.geq x z))\n(check-sat)\n"
            ),
        ),
        (
            "arithmetic across scopes",
            format!(
                "{DECLS}(assert (fp.lt (fp.add RNE x y) z))\n(push 1)\n\
                 (assert (fp.gt (fp.mul RNE x y) z))\n(check-sat)\n(pop 1)\n\
                 (check-sat)\n(push 1)\n(assert (fp.isNegative z))\n(check-sat)\n"
            ),
        ),
    ]
}

/// EQUIVALENCE BARRIER: the persistent lane must not change any verdict, and
/// `--no-fp-incremental` must genuinely reach it.
///
/// `--no-fp-incremental` restores the stateless pipeline that predates this
/// subsystem — a fresh `Tseitin`, `FpSolver` and `SatSolver` per `check-sat`.
/// It is also the A/B control for the performance measurement, so it must be a
/// REAL control. Comparing verdicts alone is not enough: a switch that never
/// reached the lane would run the lane on both sides, agree with itself, and
/// pass. So each script is also required to engage the lane with the switch off
/// (`:fp-incremental.solves`, published only by the persistent lane) and to
/// leave it untouched with the switch on. That makes one test cover three
/// failure modes — a changed verdict, a dead switch, and a lane that silently
/// stopped engaging at all.
#[test]
fn fp_incremental_lane_never_changes_a_verdict() {
    for (name, smt) in lane_scripts() {
        // Statistics after every check-sat, so lane engagement is observable.
        let instrumented = smt.replace("(check-sat)", "(check-sat)\n(get-info :all-statistics)");
        let engaged = |out: &[String]| out.iter().any(|l| l.contains("fp-incremental.solves"));

        let guard = ay_core::misc_test_override::set(ay_core::MiscCliFlags {
            no_fp_incremental: true,
            ..Default::default()
        });
        let stateless_out = solve_authored_vec(&instrumented);
        drop(guard);
        let persistent_out = solve_authored_vec(&instrumented);

        let pick = |out: &[String]| -> Vec<String> {
            out.iter()
                .filter(|l| matches!(l.trim(), "sat" | "unsat" | "unknown"))
                .cloned()
                .collect()
        };
        let stateless = pick(&stateless_out);
        let persistent = pick(&persistent_out);

        assert!(
            !stateless.is_empty(),
            "`{name}`: produced no verdicts at all"
        );
        assert_eq!(
            persistent, stateless,
            "`{name}`: the persistent FP lane disagreed with the stateless \
             pipeline (persistent={persistent:?} stateless={stateless:?})"
        );
        assert!(
            engaged(&persistent_out),
            "`{name}`: the persistent lane never engaged, so the agreement \
             above compares the stateless pipeline with itself"
        );
        assert!(
            !engaged(&stateless_out),
            "`{name}`: --no-fp-incremental did not reach the lane, so it is \
             not a control and every A/B number measured with it is void"
        );
    }
}

/// Float32 declarations shared by the scripts below.
const DECLS: &str = "(set-logic QF_FP)\n\
                     (declare-fun x () Float32)\n\
                     (declare-fun y () Float32)\n\
                     (declare-fun z () Float32)\n";

fn verdicts(smt: &str) -> Vec<String> {
    solve_authored_vec(smt)
        .into_iter()
        .filter(|line| matches!(line.trim(), "sat" | "unsat" | "unknown"))
        .collect()
}

/// (1) A contradiction asserted INSIDE a scope must be retracted by `pop`.
///
/// The activation unit on an assertion's Tseitin root is the ONLY scoped clause
/// this lane installs. Route it through `add_clause_global` instead of
/// `add_clause` and it becomes a permanent unit: the post-pop check-sat is
/// still solved under the popped assertion and reports a wrong `unsat`.
#[test]
fn fp_incremental_scoped_contradiction_does_not_survive_pop() {
    let smt = format!(
        "{DECLS}\
         (assert (fp.lt x y))\n\
         (push 1)\n\
         (assert (fp.gt x y))\n\
         (check-sat)\n\
         (pop 1)\n\
         (check-sat)\n\
         (push 1)\n\
         (assert (fp.isNormal x))\n\
         (check-sat)\n"
    );
    assert_eq!(
        verdicts(&smt),
        vec!["unsat", "sat", "sat"],
        "an FP assertion activated inside a push leaked past its pop"
    );
}

/// (2) An assertion re-asserted after a pop must be RE-ACTIVATED.
///
/// `encoded_assertions` caches the Tseitin root literal, so the second
/// `(assert (fp.gt x y))` re-encodes nothing. What makes it constrain the
/// formula again is `IncrementalFpState::pop` dropping activation records
/// deeper than the new scope depth (#2822). Without that `retain`, the stale
/// record says "already active at depth 1", no unit is installed, the
/// assertion is inert, and the final check-sat reports a wrong `sat`.
#[test]
fn fp_incremental_reasserted_conflict_is_reactivated_after_pop() {
    let smt = format!(
        "{DECLS}\
         (assert (fp.lt x y))\n\
         (push 1)\n\
         (assert (fp.gt x y))\n\
         (check-sat)\n\
         (pop 1)\n\
         (check-sat)\n\
         (push 1)\n\
         (assert (fp.gt x y))\n\
         (check-sat)\n"
    );
    assert_eq!(
        verdicts(&smt),
        vec!["unsat", "sat", "unsat"],
        "an FP assertion re-asserted after a pop was never re-activated"
    );
}

/// (3) The FP variable offset must be FROZEN for the whole session.
///
/// The second scope adds a purely Boolean assertion, which allocates new
/// Tseitin variables and so MOVES `tseitin_result.num_vars` — the quantity the
/// stateless path recomputes `var_offset` from on every call. If the offset is
/// recomputed rather than frozen, `fp.geq`'s freshly emitted circuit lands on
/// different SAT variables than the cached bits `fp.lt` already constrained.
/// The two predicates then talk about disjoint bit sets, nothing contradicts,
/// and the solve reports a wrong `sat`.
#[test]
fn fp_incremental_frozen_offset_keeps_cached_bits_wired() {
    let smt = format!(
        "(set-logic QF_FP)\n\
         (declare-fun x () Float32)\n\
         (declare-fun y () Float32)\n\
         (declare-fun p () Bool)\n\
         (declare-fun q () Bool)\n\
         (push 1)\n\
         (assert (fp.lt x y))\n\
         (check-sat)\n\
         (push 1)\n\
         (assert (and p q))\n\
         (assert (fp.geq x y))\n\
         (check-sat)\n"
    );
    assert_eq!(
        verdicts(&smt),
        vec!["sat", "unsat"],
        "FP bits from an earlier check-sat were re-wired by a moving var_offset"
    );
}

/// (4) A Bool named only by a LATER assertion must be tied to the FP proxy
/// literal the earlier `ite` decomposition froze into the mux.
///
/// On the first check-sat `b` occurs only below an FP `ite`, so the Tseitin
/// walk never names it and `encode_bool_condition` falls to `bool_input_lit` —
/// an UNCONSTRAINED fresh literal. Sound in isolation. On the second check-sat
/// `(assert b)` gives `b` a Tseitin variable, but `term_to_fp` has cached the
/// `ite` decomposition, so `get_fp` returns immediately and the mux is never
/// re-encoded: it stays wired to the unlinked literal. Without the repair pass
/// the SAT solver satisfies `(assert b)` through the Tseitin variable while the
/// mux takes the ELSE branch through the independent FP literal — a wrong `sat`
/// that the model gate cannot see, because the published FP value is internally
/// consistent and the disagreement is between two names for `b`.
///
/// Note the leading `(push 1)`: the first check-sat must run on the
/// PERSISTENT lane for the stale-cache hazard to exist at all.
#[test]
fn fp_incremental_ite_bool_condition_is_linked_when_later_named() {
    let smt = format!(
        "(set-logic QF_FP)\n\
         (declare-fun x () Float32)\n\
         (declare-fun y () Float32)\n\
         (declare-fun z () Float32)\n\
         (declare-fun b () Bool)\n\
         (push 1)\n\
         (assert (fp.lt (ite b x y) z))\n\
         (check-sat)\n\
         (push 1)\n\
         (assert b)\n\
         (assert (fp.geq x z))\n\
         (check-sat)\n"
    );
    assert_eq!(
        verdicts(&smt),
        vec!["sat", "unsat"],
        "an FP `ite` condition stayed wired to an unlinked literal after the \
         same Bool was given a Tseitin variable"
    );
}

/// Mechanism barrier: the session really is served by ONE SAT solver.
///
/// `:decisions` and `:propagations` are lifetime-inclusive per solver instance
/// (`collect_sat_stats!` reads `total_num_*`), and `Solver::pop` melts a scope
/// selector but never decrements `num_vars`. So on a persistent lane every one
/// of these is monotone and the post-pop check-sat cannot reproduce the base
/// check-sat exactly. On the old per-call pipeline `:num-vars` FELL across the
/// pop and check-sat #3 reproduced #1 to the digit — the same search re-run
/// from scratch on a brand-new solver.
///
/// The first check-sat is deliberately excluded: it runs before any `push`, so
/// `incremental_mode` is still false and it takes the stateless path.
#[test]
fn fp_incremental_session_uses_one_persistent_sat_solver() {
    let smt = format!(
        "{DECLS}\
         (assert (not (= (fp.add RNE (fp.add RNE x y) z)\n\
                         (fp.add RNE x (fp.add RNE y z)))))\n\
         (push 1)\n\
         (assert (fp.isNormal x))\n\
         (check-sat)\n\
         (get-info :all-statistics)\n\
         (pop 1)\n\
         (check-sat)\n\
         (get-info :all-statistics)\n\
         (push 1)\n\
         (assert (fp.isPositive z))\n\
         (check-sat)\n\
         (get-info :all-statistics)\n"
    );
    let out = solve_authored_vec(&smt).join("\n");

    let series = |key: &str| -> Vec<u64> {
        out.lines()
            .filter_map(|line| {
                let idx = line.find(key)?;
                line[idx + key.len()..]
                    .split_whitespace()
                    .next()?
                    .trim_end_matches(')')
                    .parse::<u64>()
                    .ok()
            })
            .collect()
    };

    let vars = series(":num-vars");
    let decisions = series(":decisions");
    let props = series(":propagations");
    assert_eq!(vars.len(), 3, "expected three statistics blocks: {out}");

    for w in vars.windows(2) {
        assert!(
            w[1] >= w[0],
            "`:num-vars` fell across a pop ({w:?}) — only a fresh SAT solver \
             can do that; `Solver::pop` never decrements num_vars"
        );
    }
    for (name, series) in [("decisions", &decisions), ("propagations", &props)] {
        assert_eq!(series.len(), 3, "expected three `{name}` samples: {out}");
        for w in series.windows(2) {
            assert!(
                w[1] > w[0],
                "`:{name}` is lifetime-inclusive, so a persistent solver can \
                 only grow it; got {series:?}"
            );
        }
    }
}

/// ay#8870, INCREMENTAL: two `fp.to_ubv` sites created on DIFFERENT check-sats
/// must still be Ackermann-congruent.
///
/// `register_to_bv_unspec_site` relates each new site to all PRIOR ones, and
/// the conversion of a NaN is fixed-but-unspecified — so without the pairwise
/// guard `(= x y)` can be satisfied by two distinct NaN encodings whose
/// conversions differ. On the stateless path every site is created inside one
/// solver lifetime and the vector is trivially complete. Under persistence it
/// is complete only because `to_bv_unspec_sites` rides across check-sats in
/// `FpEncodingCache`: here the `x` site is created on check-sat #1 and the `y`
/// site only on check-sat #2, so dropping the vector between calls leaves the
/// two conversions free to differ and the refutation is lost to a wrong `sat`.
///
/// This is the guard the design named as primary, and it did not exist: the
/// brief recorded it as already landed, but no such test is on this tree.
///
/// HONEST SCOPE. As shipped, the lane DECLINES any encoding that produced an
/// `fp.to_{s,u}bv` site (see `incremental.rs`, the measured completeness
/// decline), so today this test pins the decline rather than the persistence:
/// it proves the conversion shape still refutes, whichever pipeline answers.
/// It becomes a live guard on `to_bv_unspec_sites` riding in
/// `FpEncodingCache` the moment that decline is lifted — which is exactly when
/// it is needed, and why the cache field is kept.
///
/// Only the SECOND verdict is pinned; the first is left free because it is
/// `unknown` or `sat` depending on which pipeline answers, and neither is what
/// this canary is about.
#[test]
fn fp_incremental_to_ubv_congruence_survives_a_push_8870() {
    let smt = "(set-logic QF_BVFP)\n\
               (declare-const x (_ FloatingPoint 5 11))\n\
               (declare-const y (_ FloatingPoint 5 11))\n\
               (push 1)\n\
               (assert (= x y))\n\
               (assert (bvule ((_ fp.to_ubv 8) RNE x) (_ bv200 8)))\n\
               (check-sat)\n\
               (push 1)\n\
               (assert (not (= ((_ fp.to_ubv 8) RNE x) ((_ fp.to_ubv 8) RNE y))))\n\
               (check-sat)\n";
    let got = verdicts(smt);
    assert_eq!(got.len(), 2, "expected two verdicts, got {got:?}");
    assert_eq!(
        got[1], "unsat",
        "an `fp.to_ubv` site created on a LATER check-sat was never made \
         congruent with the site from an earlier one (ay#8870, incremental)"
    );
}

/// A `check-sat-assuming` hypothesis must constrain ONLY its own query.
///
/// `solve_scoped_assumptions` merges the assumptions INTO `ctx.assertions` and
/// re-enters the FP pipeline. A persistent lane that encoded them would install
/// each assumption's activation unit at the current scope depth — a unit no
/// `pop` ever retracts, because the frontend never pushed a scope for it. The
/// next plain `check-sat` is then solved under the previous query's hypothesis:
/// a wrong `unsat` immediately, and a wrong `sat` once a negated assumption is
/// retained.
///
/// Both assumption polarities are exercised, and a plain `check-sat` follows
/// each, so a leak in either direction shows up as a flipped verdict rather
/// than as a coincidence. Confirmed against bitwuzla 0.9.1 and cvc5 1.3.0.
///
/// This file is the one the brief recorded as `fp_scoped_assumption_isolation.rs`
/// and "already landed"; no such file exists on this tree.
#[test]
fn fp_incremental_scoped_assumption_does_not_outlive_its_query() {
    let smt = "(set-logic QF_FP)\n\
               (declare-const x (_ FloatingPoint 5 11))\n\
               (declare-const y (_ FloatingPoint 5 11))\n\
               (declare-const a Bool)\n\
               (assert (=> a (fp.lt x y)))\n\
               (push 1)\n\
               (assert (fp.gt x y))\n\
               (check-sat)\n\
               (check-sat-assuming (a))\n\
               (check-sat)\n\
               (check-sat-assuming ((not a)))\n\
               (check-sat)\n";
    assert_eq!(
        verdicts(smt),
        vec!["sat", "unsat", "sat", "sat", "sat"],
        "a `check-sat-assuming` hypothesis outlived its own query on the FP lane"
    );
}

/// The lane DECLINES on uninterpreted structure rather than guessing.
///
/// `plan_congruence` is driven by a scan of the assertion set, and keeping its
/// Ackermann pairs correct incrementally means never dropping a pair that a new
/// assertion introduced. This lane does not attempt that: it tears its state
/// down and hands the whole session back to the stateless pipeline, which
/// already does congruence properly. The verdicts must therefore be exactly the
/// ones the stateless pipeline produces — in particular `(= x y)` must still
/// force `(= (f x) (f y))`.
#[test]
fn fp_incremental_declines_on_uninterpreted_structure() {
    let smt = "(set-logic QF_FP)\n\
               (declare-fun x () Float32)\n\
               (declare-fun y () Float32)\n\
               (declare-fun f (Float32) Float32)\n\
               (push 1)\n\
               (assert (= x y))\n\
               (check-sat)\n\
               (push 1)\n\
               (assert (not (= (f x) (f y))))\n\
               (check-sat)\n";
    assert_eq!(
        verdicts(smt),
        vec!["sat", "unsat"],
        "congruence over an uninterpreted symbol was lost on the FP lane"
    );
}
