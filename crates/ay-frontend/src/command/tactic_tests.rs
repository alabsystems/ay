// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Tests for parsing `(apply <tactic>)` tactic expressions.

use super::{ApplyTactic, ParamValue, Probe, ProbeCmp};
use crate::sexp::parse_sexp;

fn parse(src: &str) -> Result<ApplyTactic, String> {
    let sexpr = parse_sexp(src).expect("test tactic must be a valid s-expression");
    ApplyTactic::parse(&sexpr).map_err(|e| e.to_string())
}

#[test]
fn bare_primitive_names_parse() {
    assert_eq!(parse("skip"), Ok(ApplyTactic::Skip));
    assert_eq!(parse("simplify"), Ok(ApplyTactic::Simplify));
    assert_eq!(parse("solve-eqs"), Ok(ApplyTactic::SolveEqs));
    assert_eq!(parse("propagate-values"), Ok(ApplyTactic::PropagateValues));
    assert_eq!(parse("elim-and"), Ok(ApplyTactic::ElimAnd));
    assert_eq!(parse("qe-light"), Ok(ApplyTactic::QeLight));
    assert_eq!(parse("tseitin-cnf"), Ok(ApplyTactic::TseitinCnf));
}

#[test]
fn tseitin_cnf_parses_and_non_z3_cnf_alias_is_rejected() {
    // Z3 5.0.0 exposes `tseitin-cnf` and rejects the short `cnf` spelling.
    assert_eq!(parse("tseitin-cnf"), Ok(ApplyTactic::TseitinCnf));
    assert!(parse("cnf").is_err());
    assert_eq!(ApplyTactic::TseitinCnf.depth(), 1);
}

#[test]
fn propagate_ineqs_parses_to_its_own_tactic_not_an_alias() {
    // `propagate-ineqs` was historically (and wrongly) aliased to
    // `propagate-values`; z3's propagate-ineqs does bound subsumption, not
    // value propagation. Lock the dedicated variant in.
    assert_eq!(parse("propagate-ineqs"), Ok(ApplyTactic::PropagateIneqs));
    assert_eq!(ApplyTactic::PropagateIneqs.depth(), 1);
}

#[test]
fn transform_tactic_batch_names_parse() {
    // The z3-compatible transform batch: each bare name maps to its own tactic
    // (depth 1), and `cofactor-term-ite` is an ALIAS of `blast-term-ite` (the
    // same Shannon ITE lift).
    assert_eq!(parse("elim-term-ite"), Ok(ApplyTactic::ElimTermIte));
    assert_eq!(parse("blast-term-ite"), Ok(ApplyTactic::BlastTermIte));
    assert_eq!(parse("cofactor-term-ite"), Ok(ApplyTactic::BlastTermIte));
    assert_eq!(parse("der"), Ok(ApplyTactic::Der));
    assert_eq!(
        parse("distribute-forall"),
        Ok(ApplyTactic::DistributeForall)
    );
    assert_eq!(parse("reduce-args"), Ok(ApplyTactic::ReduceArgs));
    for t in [
        ApplyTactic::ElimTermIte,
        ApplyTactic::BlastTermIte,
        ApplyTactic::Der,
        ApplyTactic::DistributeForall,
        ApplyTactic::ReduceArgs,
    ] {
        assert_eq!(t.depth(), 1);
    }
}

#[test]
fn lift_if_is_not_a_z3_tactic_and_is_rejected() {
    // Z3 5.0.0 rejects `(apply lift-if)` with "unknown tactic"; AY must too —
    // real-z3-names-only policy (a near-neighbor of the batch's ite tactics).
    assert!(
        parse("lift-if").is_err(),
        "lift-if is not a z3 tactic and must be rejected, not silently accepted"
    );
    // And a typo of a real batch name must still be an honest error.
    assert!(parse("reduce-arg").is_err());
    assert!(parse("blast-term-it").is_err());
}

#[test]
fn every_supported_name_parses_to_a_supported_tactic() {
    // The shared registry [`SUPPORTED_TACTIC_NAMES`] must stay in lock-step with
    // the parser: every advertised name parses to a concrete `ApplyTactic`.
    for name in crate::command::SUPPORTED_TACTIC_NAMES {
        assert!(
            parse(name).is_ok(),
            "advertised tactic name {name:?} must parse"
        );
    }
}

#[test]
fn qe_light_parses_to_the_qe_light_tactic() {
    // qe-light is a real z3 tactic backed by AY's Cooper `QeLight` pass, which
    // replaces each in-fragment `(exists ((x Int)) φ)` subterm *in place* with a
    // quantifier-free equivalent (verified by Cooper's self-check). Because the
    // whole existential node is swapped for a formula over its FREE variables,
    // the rewrite is equivalence-preserving even under negation, so it belongs in
    // the shared printable registry alongside the other tactics.
    assert_eq!(parse("qe-light"), Ok(ApplyTactic::QeLight));
    assert_eq!(ApplyTactic::QeLight.depth(), 1);
}

#[test]
fn qe_parses_to_the_qe_tactic() {
    // `qe` is a real z3 tactic (full LIA quantifier elimination). AY realizes it
    // with the same Cooper pass as `qe-light`: in-fragment single-Int-variable
    // existentials are eliminated (each substitution gated by Cooper's
    // independent equivalence self-check), out-of-fragment quantifiers are kept
    // verbatim — a documented sound divergence from z3's LIA-complete qe
    // (coverage, never soundness). One primitive, depth 1, like z3's (apply qe).
    assert_eq!(parse("qe"), Ok(ApplyTactic::Qe));
    assert_eq!(ApplyTactic::Qe.depth(), 1);
}

#[test]
fn bit_blast_parses_to_the_bit_blast_tactic() {
    // bit-blast is a real z3 tactic backed by AY's `BitBlast` pass, which rewrites
    // a QF_BV goal into an equisatisfiable pure-Boolean goal. It is a single
    // primitive (depth 1) on both tactic surfaces.
    assert_eq!(parse("bit-blast"), Ok(ApplyTactic::BitBlast));
    assert_eq!(ApplyTactic::BitBlast.depth(), 1);
}

#[test]
fn ctx_solver_simplify_parses_to_the_ctx_solver_simplify_tactic() {
    // ctx-solver-simplify is a real z3 tactic backed by AY's solver-driven
    // contextual simplification pass (drop assertions the context proves
    // redundant; collapse a contradictory goal to false). A single primitive
    // (depth 1) on both tactic surfaces.
    assert_eq!(
        parse("ctx-solver-simplify"),
        Ok(ApplyTactic::CtxSolverSimplify)
    );
    assert_eq!(ApplyTactic::CtxSolverSimplify.depth(), 1);
}

#[test]
fn flatten_and_is_not_a_z3_tactic_and_is_rejected() {
    // Z3 has no `flatten-and` tactic (its and-elimination surface name is
    // `elim-and`). A Z3 replacement must reject the non-existent name exactly as
    // Z3 does — never recognize an AY-only alias.
    let err = parse("flatten-and").unwrap_err();
    assert!(
        err.contains("unknown tactic") && err.contains("flatten-and"),
        "flatten-and must be an unknown-tactic error like z3, got: {err}"
    );
}

#[test]
fn unknown_tactic_name_is_an_error_not_a_silent_accept() {
    let err = parse("no-such-tactic").unwrap_err();
    assert!(
        err.contains("unknown tactic"),
        "expected an unknown-tactic error, got: {err}"
    );
    assert!(
        err.contains("no-such-tactic"),
        "error should name the tactic: {err}"
    );
}

#[test]
fn then_combinator_parses_children() {
    assert_eq!(
        parse("(then simplify solve-eqs)"),
        Ok(ApplyTactic::Then(vec![
            ApplyTactic::Simplify,
            ApplyTactic::SolveEqs
        ]))
    );
    // `and-then` is an alias for `then`.
    assert_eq!(
        parse("(and-then simplify solve-eqs)"),
        Ok(ApplyTactic::Then(vec![
            ApplyTactic::Simplify,
            ApplyTactic::SolveEqs
        ]))
    );
}

#[test]
fn then_of_a_single_tactic_collapses() {
    assert_eq!(parse("(then simplify)"), Ok(ApplyTactic::Simplify));
}

#[test]
fn unknown_tactic_inside_combinator_errors() {
    let err = parse("(then simplify bogus)").unwrap_err();
    assert!(err.contains("unknown tactic"), "got: {err}");
}

#[test]
fn unknown_combinator_head_errors() {
    // A genuinely unknown combinator head is still an honest error (`or-else` is
    // now a real combinator, so it can no longer be the negative example).
    let err = parse("(no-such-combinator simplify skip)").unwrap_err();
    assert!(err.contains("unknown tactic"), "got: {err}");
}

#[test]
fn fail_and_split_clause_are_bare_names() {
    assert_eq!(parse("fail"), Ok(ApplyTactic::Fail));
    assert_eq!(parse("split-clause"), Ok(ApplyTactic::SplitClause));
}

#[test]
fn or_else_and_par_or_parse() {
    assert_eq!(
        parse("(or-else fail simplify)"),
        Ok(ApplyTactic::OrElse(vec![
            ApplyTactic::Fail,
            ApplyTactic::Simplify
        ]))
    );
    assert_eq!(
        parse("(par-or fail simplify)"),
        Ok(ApplyTactic::ParOr(vec![
            ApplyTactic::Fail,
            ApplyTactic::Simplify
        ]))
    );
    // Singleton composition collapses to the single tactic.
    assert_eq!(parse("(or-else simplify)"), Ok(ApplyTactic::Simplify));
}

#[test]
fn par_then_parses_like_then() {
    assert_eq!(
        parse("(par-then elim-and simplify)"),
        Ok(ApplyTactic::ParThen(vec![
            ApplyTactic::ElimAnd,
            ApplyTactic::Simplify
        ]))
    );
}

#[test]
fn repeat_parses_with_and_without_bound() {
    assert_eq!(
        parse("(repeat elim-and)"),
        Ok(ApplyTactic::Repeat(Box::new(ApplyTactic::ElimAnd), None))
    );
    assert_eq!(
        parse("(repeat elim-and 3)"),
        Ok(ApplyTactic::Repeat(Box::new(ApplyTactic::ElimAnd), Some(3)))
    );
}

#[test]
fn try_for_parses_the_timeout() {
    assert_eq!(
        parse("(try-for simplify 1000)"),
        Ok(ApplyTactic::TryFor(Box::new(ApplyTactic::Simplify), 1000))
    );
}

#[test]
fn using_params_and_with_parse_params() {
    let expected = ApplyTactic::UsingParams(
        Box::new(ApplyTactic::Simplify),
        vec![("elim_and".to_string(), ParamValue::Bool(true))],
    );
    assert_eq!(
        parse("(using-params simplify :elim_and true)"),
        Ok(expected.clone())
    );
    assert_eq!(parse("(with simplify :elim_and true)"), Ok(expected));
}

#[test]
fn when_and_fail_if_parse_probes() {
    assert_eq!(
        parse("(when (> num-consts 0) simplify)"),
        Ok(ApplyTactic::When(
            Probe::Cmp(
                ProbeCmp::Gt,
                Box::new(Probe::NumConsts),
                Box::new(Probe::Const("0".to_string()))
            ),
            Box::new(ApplyTactic::Simplify)
        ))
    );
    assert_eq!(
        parse("(fail-if (> size 5))"),
        Ok(ApplyTactic::FailIf(Probe::Cmp(
            ProbeCmp::Gt,
            Box::new(Probe::Size),
            Box::new(Probe::Const("5".to_string()))
        )))
    );
}

#[test]
fn unknown_probe_is_an_error() {
    let err = parse("(when (> no-such-probe 0) simplify)").unwrap_err();
    assert!(err.contains("unknown probe"), "got: {err}");
}

#[test]
fn solve_tactics_smt_default_sat_parse_as_identity() {
    // z3's `smt`/`sat` engines and `default` strategy are terminal solve tactics.
    // As a goal transform they are the identity (`Skip`); turned into a solver
    // they run AY's real engine. They must PARSE (so `Then('simplify','smt')` is
    // buildable — the standard z3py custom-solver idiom) and map to Skip.
    for name in ["smt", "default", "sat"] {
        assert_eq!(
            parse(name).unwrap_or_else(|e| panic!("{name} must parse: {e}")),
            ApplyTactic::Skip,
            "{name} is a terminal solve tactic, realized as the identity goal transform"
        );
    }
}

#[test]
fn then_simplify_smt_builds_the_canonical_z3py_solver_chain() {
    // `Then('simplify','smt')` — the everyday z3py `Tactic`/`.solver()` pattern —
    // must build. Before `smt` existed as a tactic it was unbuildable.
    let t = parse("(then simplify smt)").expect("then simplify smt must parse");
    assert_eq!(
        t,
        ApplyTactic::Then(vec![ApplyTactic::Simplify, ApplyTactic::Skip])
    );
}

// ---------------------------------------------------------------------------
// P3 tactics batch N+1: full z3-4.15.4 registry (91 added names), if/cond/`!`
// combinators, and full probe-name coverage. Class facts measured against
// z3 4.15.4 with an internal registry-probe sweep.
// ---------------------------------------------------------------------------

/// The 91 tactic names this batch adds, exactly the z3-4.15.4 names AY was
/// missing (`comm -23 z3-tactics ay-known`). Guards set-equality with the
/// classification arms: every name parses, and parses to its class's
/// realization.
const BATCH_NAMES: &[&str] = &[
    // CLASS S (35)
    "auflia",
    "auflira",
    "aufnira",
    "bv",
    "lia",
    "lira",
    "lra",
    "nlsat",
    "nra",
    "pqffd",
    "psat",
    "psmt",
    "qfaufbv",
    "qfauflia",
    "qfbv",
    "qfbv-sls",
    "qffd",
    "qffp",
    "qffpbv",
    "qffplra",
    "qfidl",
    "qflia",
    "qflra",
    "qfnia",
    "qfnra",
    "qfnra-nlsat",
    "qfuf",
    "qfufbv",
    "qfufbv_ackr",
    "qsat",
    "sls-smt",
    "smtfd",
    "ufbv",
    "uflra",
    "ufnia",
    // CLASS A (14)
    "propagate-values2",
    "reduce-args2",
    "elim-uncnstr2",
    "tseitin-cnf-core",
    "sat-preprocess",
    "qe2",
    "qe_rec",
    "ctx-simplify",
    "unit-subsume-simplify",
    "solver-subsumption",
    "dom-simplify",
    "degree-shift",
    "fm",
    "card2bv",
    // CLASS N (35, incl. collect-statistics)
    "ackermannize_bv",
    "add-bounds",
    "aig",
    "bv_bound_chk",
    "bv-slice",
    "bvarray2uf",
    "collect-statistics",
    "demodulator",
    "dt2bv",
    "elim-predicates",
    "elim-small-bv",
    "eq2bv",
    "euf-completion",
    "factor",
    "fix-dl-var",
    "fpa2bv",
    "injectivity",
    "lia2card",
    "lia2pb",
    "macro-finder",
    "max-bv-sharing",
    "nla2bv",
    "normalize-bounds",
    "occf",
    "pb-preprocess",
    "propagate-bv-bounds",
    "propagate-bv-bounds2",
    "quasi-macros",
    "recover-01",
    "reduce-bv-size",
    "snf",
    "special-relations",
    "subpaving",
    "symmetry-reduce",
    "ufbv-rewriter",
    // CLASS F (6)
    "diff-neq",
    "nlqsat",
    "pb2bv",
    "horn",
    "horn-simplify",
    "bv1-blast",
    // CLASS C (1)
    "fail-if-undecided",
];

#[test]
fn the_batch_registers_exactly_91_names_and_all_parse() {
    assert_eq!(
        BATCH_NAMES.len(),
        91,
        "the batch is exactly the 91 missing z3 names"
    );
    for name in BATCH_NAMES {
        assert!(
            parse(name).is_ok(),
            "pinned Z3 tactic name {name:?} must parse (registered by this batch)"
        );
        assert!(
            crate::command::SUPPORTED_TACTIC_NAMES.contains(name),
            "{name:?} must be advertised in SUPPORTED_TACTIC_NAMES"
        );
    }
}

#[test]
fn class_s_and_n_names_parse_to_the_identity() {
    // Solver strategies (S) and no-op-safe transforms (N) are the truthful
    // identity as a goal transform — the same realization as smt/default/sat.
    for name in [
        "qflia",
        "qfbv",
        "smtfd",
        "nlsat",
        "pqffd",
        "ackermannize_bv",
        "fpa2bv",
        "subpaving",
        "collect-statistics",
        "nla2bv",
    ] {
        assert_eq!(
            parse(name),
            Ok(ApplyTactic::Skip),
            "{name} must be the identity realization"
        );
    }
}

#[test]
fn class_a_alias_names_parse_to_their_verified_pass() {
    assert_eq!(parse("propagate-values2"), Ok(ApplyTactic::PropagateValues));
    assert_eq!(parse("reduce-args2"), Ok(ApplyTactic::ReduceArgs));
    assert_eq!(parse("elim-uncnstr2"), Ok(ApplyTactic::SolveEqs));
    assert_eq!(parse("tseitin-cnf-core"), Ok(ApplyTactic::TseitinCnf));
    assert_eq!(parse("sat-preprocess"), Ok(ApplyTactic::TseitinCnf));
    assert_eq!(parse("qe2"), Ok(ApplyTactic::Qe));
    assert_eq!(parse("qe_rec"), Ok(ApplyTactic::Qe));
    assert_eq!(parse("ctx-simplify"), Ok(ApplyTactic::CtxSolverSimplify));
    assert_eq!(
        parse("unit-subsume-simplify"),
        Ok(ApplyTactic::CtxSolverSimplify)
    );
    assert_eq!(
        parse("solver-subsumption"),
        Ok(ApplyTactic::CtxSolverSimplify)
    );
    assert_eq!(parse("dom-simplify"), Ok(ApplyTactic::Simplify));
    assert_eq!(parse("degree-shift"), Ok(ApplyTactic::Simplify));
    assert_eq!(parse("fm"), Ok(ApplyTactic::Simplify));
    assert_eq!(parse("card2bv"), Ok(ApplyTactic::Simplify));
}

#[test]
fn class_f_names_parse_to_honest_failures_with_z3_byte_texts() {
    // z3 byte texts measured 2026-07-18 (z3 4.15.4 apply sweep).
    assert_eq!(
        parse("diff-neq"),
        Ok(ApplyTactic::Unsupported {
            name: "diff-neq",
            message: "goal is not diff neq",
        })
    );
    assert_eq!(
        parse("nlqsat"),
        Ok(ApplyTactic::Unsupported {
            name: "nlqsat",
            message: "not NRA",
        })
    );
    assert_eq!(
        parse("pb2bv"),
        Ok(ApplyTactic::Unsupported {
            name: "pb2bv",
            message: "goal is in a fragment not supported by pb2bv",
        })
    );
    assert!(matches!(
        parse("horn"),
        Ok(ApplyTactic::Unsupported { name: "horn", .. })
    ));
    assert!(matches!(
        parse("horn-simplify"),
        Ok(ApplyTactic::Unsupported {
            name: "horn-simplify",
            ..
        })
    ));
    // bv1-blast is NOT an unconditional failure: z3 succeeds on BV-free goals
    // (measured), so it has its own conditional realization.
    assert_eq!(parse("bv1-blast"), Ok(ApplyTactic::Bv1Blast));
    assert_eq!(ApplyTactic::Bv1Blast.depth(), 1);
    // fail-if-undecided wires to the real engine primitive.
    assert_eq!(parse("fail-if-undecided"), Ok(ApplyTactic::FailIfUndecided));
}

#[test]
fn if_and_cond_parse_as_three_argument_synonyms() {
    let expected = ApplyTactic::Cond(
        Probe::Cmp(
            ProbeCmp::Gt,
            Box::new(Probe::NumConsts),
            Box::new(Probe::Const("0".to_string())),
        ),
        Box::new(ApplyTactic::Simplify),
        Box::new(ApplyTactic::Skip),
    );
    assert_eq!(
        parse("(if (> num-consts 0) simplify skip)"),
        Ok(expected.clone())
    );
    assert_eq!(parse("(cond (> num-consts 0) simplify skip)"), Ok(expected));
}

#[test]
fn if_and_cond_reject_wrong_arity_with_the_z3_byte_text() {
    // z3 4.15.4 (measured): 2 args -> "invalid if/conditional combinator,
    // three arguments expected", rc=1.
    for src in [
        "(if (> num-consts 0) skip)",
        "(cond (> num-consts 0) skip)",
        "(if (> num-consts 0) skip skip skip)",
    ] {
        let err = parse(src).unwrap_err();
        assert!(
            err.contains("invalid if/conditional combinator, three arguments expected"),
            "{src}: got {err}"
        );
    }
}

#[test]
fn bang_is_the_using_params_spelling() {
    // `(! t :k v)` ≡ `(using-params t :k v)` (z3 accepts it in both apply and
    // check-sat-using — measured c4/cbang probes).
    assert_eq!(
        parse("(! simplify :arith_lhs true)"),
        parse("(using-params simplify :arith_lhs true)")
    );
    assert!(parse("(! smt :random-seed 7)").is_ok());
}

#[test]
fn every_z3_probe_name_parses() {
    // The full z3-4.15.4 probe set (z3 -probes, 42 names): a z3-valid
    // `(when <probe> …)` / `(if <probe> …)` script must never be a parse
    // error (the regression class the csu strictness fix must not introduce).
    const ALL_Z3_PROBES: &[&str] = &[
        "ackr-bound-probe",
        "arith-avg-bw",
        "arith-avg-deg",
        "arith-max-bw",
        "arith-max-deg",
        "depth",
        "has-patterns",
        "has-quantifiers",
        "is-ilp",
        "is-lia",
        "is-lira",
        "is-lra",
        "is-nia",
        "is-nira",
        "is-nra",
        "is-pb",
        "is-propositional",
        "is-qfaufbv",
        "is-qfauflia",
        "is-qfbv",
        "is-qfbv-eq",
        "is-qffp",
        "is-qffpbv",
        "is-qffplra",
        "is-qflia",
        "is-qflira",
        "is-qflra",
        "is-qfnia",
        "is-qfnra",
        "is-qfufnra",
        "is-quasi-pb",
        "is-unbounded",
        "memory",
        "num-arith-consts",
        "num-bool-consts",
        "num-bv-consts",
        "num-consts",
        "num-exprs",
        "produce-model",
        "produce-proofs",
        "produce-unsat-cores",
        "size",
    ];
    assert_eq!(ALL_Z3_PROBES.len(), 42);
    for name in ALL_Z3_PROBES {
        assert!(
            parse(&format!("(when {name} skip)")).is_ok(),
            "z3 probe {name:?} must parse inside when"
        );
    }
    // An unknown probe name is still an honest error.
    assert!(parse("(when zz-not-a-probe skip)").is_err());
}

#[test]
fn near_miss_batch_names_are_still_rejected() {
    // Typos/near-neighbors of batch names must stay honest errors — the batch
    // must not loosen the unknown-name contract.
    for bogus in ["qflia2", "diffneq", "bv1blast", "horn2", "qfbv-eq"] {
        assert!(
            parse(bogus).is_err(),
            "{bogus:?} is not a z3 tactic and must be rejected"
        );
    }
}

#[test]
fn depth_counts_primitive_applications() {
    assert_eq!(ApplyTactic::Skip.depth(), 0);
    assert_eq!(ApplyTactic::Simplify.depth(), 1);
    assert_eq!(
        ApplyTactic::Then(vec![ApplyTactic::Skip, ApplyTactic::Simplify]).depth(),
        1
    );
    assert_eq!(
        ApplyTactic::Then(vec![ApplyTactic::Simplify, ApplyTactic::SolveEqs]).depth(),
        2
    );
}
