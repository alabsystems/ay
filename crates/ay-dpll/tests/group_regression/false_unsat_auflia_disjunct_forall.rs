// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#![allow(clippy::panic)]

//! Cardinal soundness spec for the DISJUNCT-POSITION `forall` wrong REFUTATION
//! (#auflia-disjunct-forall-false-unsat).
//!
//! # The defect
//!
//! Six `AUFLIA/20170829-Rodin` benchmarks answered `unsat` where the file's own
//! `(set-info :status sat)`, z3, and `cvc5 --finite-model-find` all say `sat`:
//!
//! ```text
//! smt2339071716448149054  smt3849844051417415002  smt4436712082235129487
//! smt6733391339078477137  smt7017482563060634855  smt7663344132518650672
//! ```
//!
//! Exit code 0, `conflicts=0 decisions=0` — a clean, confident, WRONG answer
//! produced entirely by level-0 propagation over conjoined instances, not by
//! search. This is the dangerous direction: a wrong `sat` yields a witness a
//! consumer can re-check, a wrong `unsat` silently discharges a satisfiable
//! obligation and nothing downstream can detect it.
//!
//! # The invariant that was violated
//!
//! > A ground instance `body[t/x]` of `Q = ∀x. body` may be conjoined into the
//! > assertion set as a TOP-LEVEL CONJUNCT only when the assertion set entails
//! > `Q` itself.
//!
//! `∀x.body ⊨ body[t/x]` is a consequence of the QUANTIFIER, not of the
//! PROBLEM. When `Q` occurs only as a DISJUNCT the problem entails just the
//! enclosing disjunction, and the "instance" is a fabricated fact.
//!
//! Skolemization is what puts a `forall` there: `¬∃` rewrites to `∀¬`, so
//! `(forall x. ¬(p x ∧ ∃y. r y x))` becomes
//! `(forall x. (or (not (p x)) (forall y. (not (r y x)))))` — the INNER
//! universal is a disjunct. Instantiating the (entailed) outer universal at `a`
//! makes `(or (not (p a)) (forall y. (not (r y a))))` a top-level assertion;
//! two lanes then instantiated the inner universal from there and conjoined
//! `(not (r a a))`, contradicting the asserted `(r a a)`.
//!
//! # The repair
//!
//! Both lanes now consult `ematching::collect_entailed_foralls` (polarity-aware
//! NNF-conjunct walk) before instantiating:
//!   * `ematching::perform_ematching_with_generations` skips a non-entailed
//!     `forall` exactly as it already skipped a bare `Exists`
//!     (#auflia-exists-eq-false-unsat) — fail-closed in BOTH directions, since
//!     the quantifier then lands in `uninstantiated_quantifiers` and blocks the
//!     SAT certificates too;
//!   * `setup_cegqi_for_unhandled` withholds a non-entailed `forall` from
//!     enumerative instantiation and CEGQI, routing it to the unhandled/MBQI
//!     lane instead.
//!
//! Gating only ONE lane flipped just 3 of the 6 files — the other lane
//! re-derived the same fabricated literal — so both guards are load-bearing.
//! (The MBQI lane was already gated, by `forall_ids_in_conjunctive_position`
//! under #quant-alternation; the diagonal-instance lane by #p2-diag-position.
//! This closes the general `forall` case those two left open.)
//!
//! # Ground truth
//!
//! Every fixture below is satisfied by interpreting the guard predicate as
//! universally FALSE, which makes the universal vacuous. z3 4.15.4 and cvc5
//! 1.3.0 independently answer `sat` on all of them. So `sat` is correct,
//! `unknown` is a sound incompleteness, and `unsat` is a wrong refutation.
//!
//! Measured at `0.5.0+build.6317.5a5633a7d`: fixtures 1-3 answered `unsat`
//! before the repair and `unknown` after; the logically-equivalent control
//! answered `sat` both before and after.

/// Reduced from `smt7663344132518650672` (the smallest of the six) by delta
/// debugging, then re-authored here so the workspace does not vendor a
/// CC BY-NC input. `mAckn ≡ false` is a model.
const RODIN_SHAPE: &str = r#"
(set-logic AUFLIA)
(declare-sort D 0)
(declare-fun dap (D D) Bool)
(declare-fun mAckn (D) Bool)
(declare-fun a () D)
(assert (forall ((x D)) (not (and (mAckn x) (exists ((x0 D)) (dap x0 x))))))
(assert (not (mAckn a)))
(assert (dap a a))
(check-sat)
"#;

/// The same shape in PURE UF — no arrays, no arithmetic. Proves the defect is
/// not AUFLIA-specific. `a ≡ false, b ≡ true, dap ≡ true` is a model.
const PURE_UF_SHAPE: &str = r#"
(set-logic UF)
(declare-sort D 0)
(declare-fun dap (D D) Bool)
(declare-fun a (D) Bool)
(declare-fun b (D) Bool)
(assert (forall ((x D)) (not (and (a x) (exists ((y D)) (dap y x))))))
(assert (exists ((u D)) (and (or (a u) (b u)) (exists ((v D)) (dap v u)))))
(check-sat)
"#;

/// Sharpest form: the guard atom is EXPLICITLY asserted false, so `a ≡ false`
/// is a model by inspection and the universal is vacuous — yet the fabricated
/// instance `(not (dap k2 k1))` still refuted it.
///
/// Both ground assertions are load-bearing: `(dap k2 k1)` makes the inner
/// existential TRUE under the ground atoms (pointing `dap` at an unrelated
/// constant yields a sound `unknown` instead), and `(not (a k1))` supplies the
/// ground guard term the trigger matches on — its POLARITY is irrelevant, the
/// refutation appeared whether it was asserted, disjoined, or negated.
const EXPLICIT_FALSE_GUARD: &str = r#"
(set-logic UF)
(declare-sort D 0)
(declare-fun dap (D D) Bool)
(declare-fun a (D) Bool)
(declare-fun k1 () D)
(declare-fun k2 () D)
(assert (forall ((x D)) (not (and (a x) (exists ((y D)) (dap y x))))))
(assert (dap k2 k1))
(assert (not (a k1)))
(check-sat)
"#;

/// PAIRED CONTROL. Logically EQUIVALENT to [`RODIN_SHAPE`] — the same formula
/// hand-NNF'd into a single two-binder universal, so no `forall` ever lands in
/// a disjunctive position. Everything else is byte-identical. It answered `sat`
/// before the repair and must keep answering `sat` after: this is the guard
/// that the fix removed a WRONG refutation rather than the engine's ability to
/// reason about this family at all.
const EQUIVALENT_CONTROL: &str = r#"
(set-logic AUFLIA)
(declare-sort D 0)
(declare-fun dap (D D) Bool)
(declare-fun mAckn (D) Bool)
(declare-fun a () D)
(assert (forall ((x D) (x0 D)) (not (and (mAckn x) (dap x0 x)))))
(assert (not (mAckn a)))
(assert (dap a a))
(check-sat)
"#;

fn assert_never_unsat(name: &str, smt: &str) {
    let results = crate::common::solve_vec(smt);
    assert!(
        !results.iter().any(|r| r == "unsat"),
        "WRONG REFUTATION ({name}): this problem is satisfiable (interpreting \
         the guard predicate as universally false is a model; z3 4.15.4 and \
         cvc5 1.3.0 both answer `sat`) — `unsat` silently discharges a \
         satisfiable obligation. `sat` or `unknown` are both acceptable; got \
         {results:?}"
    );
}

#[test]
fn rodin_disjunct_position_forall_is_never_unsat() {
    assert_never_unsat("rodin shape", RODIN_SHAPE);
}

#[test]
fn pure_uf_disjunct_position_forall_is_never_unsat() {
    assert_never_unsat("pure UF shape", PURE_UF_SHAPE);
}

#[test]
fn explicit_false_guard_disjunct_position_forall_is_never_unsat() {
    assert_never_unsat("explicit-false guard", EXPLICIT_FALSE_GUARD);
}

/// `--self-check` was already sound on this family (it withholds the verdict:
/// "computed UNSAT is not backed by a fully-checked refutation proof"). Pin it
/// so a future change cannot regress the fail-closed mode into the wrong
/// refutation that default mode used to ship.
#[test]
fn disjunct_position_forall_selfcheck_is_never_unsat() {
    for (name, smt) in [
        ("rodin shape", RODIN_SHAPE),
        ("pure UF shape", PURE_UF_SHAPE),
        ("explicit-false guard", EXPLICIT_FALSE_GUARD),
    ] {
        let results = crate::common::solve_selfcheck_vec(smt);
        assert!(
            !results.iter().any(|r| r == "unsat"),
            "`--self-check` must not certify a wrong refutation ({name}); got \
             {results:?}"
        );
    }
}

/// The equivalent single-universal encoding must stay DECIDED. A guard that
/// bought soundness by making the whole family `unknown` would pass every
/// assertion above; this is what stops that.
#[test]
fn equivalent_single_universal_control_stays_sat() {
    let results = crate::common::solve_vec(EQUIVALENT_CONTROL);
    assert!(
        results.iter().any(|r| r == "sat"),
        "the logically-equivalent two-binder encoding of the same formula must \
         still be decided `sat` — losing it would mean the entailment gate is \
         over-broad, not that the wrong refutation was repaired; got {results:?}"
    );
}

/// The six real benchmarks, end to end. Not vendored: `AUFLIA/20170829-Rodin`
/// is licensed CC BY-NC 4.0, which does not fit this Apache-2.0 workspace, so
/// this follows the repo's existing corpus convention (`benchmarks/…` + skip
/// when absent, as in `false_unsat_auflia_rodin.rs`). The reduced fixtures
/// above cannot prove the ORIGINAL files are decided soundly, which is why this
/// guard exists in addition to them.
#[test]
fn six_rodin_benchmarks_are_never_unsat() {
    const NAMES: [&str; 6] = [
        "smt2339071716448149054",
        "smt3849844051417415002",
        "smt4436712082235129487",
        "smt6733391339078477137",
        "smt7017482563060634855",
        "smt7663344132518650672",
    ];
    let mut checked = 0usize;
    for name in NAMES {
        let Some(smt) = read_rodin_benchmark(name) else {
            continue;
        };
        // Guard against a silently-changed corpus file: the ground truth this
        // test asserts against must be the file's own declaration.
        assert!(
            smt.contains("(set-info :status sat)"),
            "corpus file {name} no longer declares `:status sat` — re-derive \
             the ground truth before trusting this guard"
        );
        let results = crate::common::solve_vec(&smt);
        assert!(
            !results.iter().any(|r| r == "unsat"),
            "WRONG REFUTATION on {name}: declared `:status sat`, and z3 and \
             `cvc5 --finite-model-find` independently agree. `sat` or \
             `unknown` are both acceptable; got {results:?}"
        );
        checked += 1;
    }
    if checked == 0 {
        eprintln!(
            "SKIP: none of the six AUFLIA/20170829-Rodin corpus files are \
             present. Fetch with `ay-z3-parity fetch benchmarks/smtlib-all \
             --divisions AUFLIA`."
        );
    }
}

/// Locate one of the six by name across the two corpus layouts this workspace
/// uses (`smtlib-2025` from the SMT-COMP selection tarballs, `smtlib-all` from
/// `ay-z3-parity fetch`). Returns `None` when the file is not on disk.
fn read_rodin_benchmark(name: &str) -> Option<String> {
    let candidates = [
        crate::common::workspace_path(format!(
            "benchmarks/smtlib-2025/non-incremental/AUFLIA/20170829-Rodin/{name}.smt2"
        )),
        crate::common::workspace_path(format!(
            "benchmarks/smtlib-all/AUFLIA/non-incremental__AUFLIA__20170829-Rodin__{name}.smt2"
        )),
    ];
    candidates
        .iter()
        .find(|p| p.exists())
        .and_then(|p| std::fs::read_to_string(p).ok())
}
