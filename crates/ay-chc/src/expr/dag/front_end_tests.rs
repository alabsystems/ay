// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! WP-F F0b/F0c on rewrites and real inputs: `eliminate_ite`, the
//! normalisation passes and `convert_expr` agree with their tree forms, on
//! random DAGs and on vendored CHC-COMP-26 sally/oral_messages clauses; plus
//! the per-pass front-end micro-benchmark.

use std::hash::Hash;
use std::sync::Arc;
use std::time::{Duration, Instant};

use ay_core::kani_compat::DetHashSet;
use proptest::prelude::*;

use super::test_support::*;
use super::*;
use crate::expr::{ChcOp, ChcSort, ChcVar};

pub(super) fn assert_fast(what: &str, start: Instant) {
    assert!(
        start.elapsed() < Duration::from_secs(5),
        "{what} took {:?}",
        start.elapsed()
    );
}

// ---------------------------------------------------------------------------
// F0c: eliminate_ite on the DAG, convert_expr memo
// ---------------------------------------------------------------------------

/// Undo `eliminate_ite`: substitute every fresh variable by the `ite` its two
/// definitional implications describe, latest first (an outer `ite`'s branches
/// mention inner variables). Returns the reconstructed expression and the
/// number of fresh variables.
fn reinline_ite(eliminated: &ChcExpr) -> (ChcExpr, usize) {
    let fresh_vars = eliminated
        .vars()
        .iter()
        .filter(|v| v.name.starts_with("_ite_"))
        .count();
    if fresh_vars == 0 {
        return (eliminated.clone(), 0);
    }
    // `and_vec(definitions ++ [body])`: exactly two implications per variable.
    let ChcExpr::Op(ChcOp::And, parts) = eliminated else {
        panic!("fresh variables without a definition conjunction");
    };
    assert_eq!(parts.len(), 2 * fresh_vars + 1, "definitions come in pairs");
    let (defs, body) = parts.split_at(parts.len() - 1);
    let mut body = body[0].as_ref().clone();
    let mut fresh = 0;
    for pair in defs.chunks(2).rev() {
        let (ChcExpr::Op(ChcOp::Implies, a), ChcExpr::Op(ChcOp::Implies, b)) =
            (pair[0].as_ref(), pair[1].as_ref())
        else {
            panic!("definition pair must be two implications");
        };
        let (ChcExpr::Op(ChcOp::Eq, then_eq), ChcExpr::Op(ChcOp::Eq, else_eq)) =
            (a[1].as_ref(), b[1].as_ref())
        else {
            panic!("definition conclusions must be equalities");
        };
        let ChcExpr::Var(v) = then_eq[0].as_ref() else {
            panic!("definition must bind a fresh variable");
        };
        let ite = ChcExpr::ite(
            a[0].as_ref().clone(),
            then_eq[1].as_ref().clone(),
            else_eq[1].as_ref().clone(),
        );
        body = body.substitute(&[(v.clone(), ite)]);
        fresh += 1;
    }
    (body, fresh)
}

fn arith_ite_nodes(e: &ChcExpr) -> usize {
    let mut seen = DetHashSet::<*const ChcExpr>::default();
    let mut stack = vec![e];
    let mut count = 0;
    while let Some(n) = stack.pop() {
        if let ChcExpr::Op(ChcOp::Ite, args) = n {
            if args.len() == 3
                && args[1].sort() == args[2].sort()
                && matches!(args[1].sort(), ChcSort::Int | ChcSort::Real)
            {
                count += 1;
            }
        }
        for c in children(n) {
            if seen.insert(Arc::as_ptr(c)) {
                stack.push(c.as_ref());
            }
        }
    }
    count
}

#[test]
fn eliminate_ite_dag_path_reinlines_to_the_input() {
    // 2^40 tree: forces the DAG path; one fresh variable per DISTINCT ite.
    let chain = ite_chain(40, "");
    let root = ChcExpr::eq(
        ChcExpr::var(ChcVar::new("y", ChcSort::Real)),
        chain.as_ref().clone(),
    );
    let t = Instant::now();
    let out = root.eliminate_ite();
    assert_fast("eliminate_ite", t);
    let (back, fresh) = reinline_ite(&out);
    assert_eq!(fresh, arith_ite_nodes(&root));
    assert_eq!(fresh, 40);
    assert!(
        back == root,
        "re-inlining the definitions restores the input"
    );
    assert!(!out.scan_features().has_ite || arith_ite_nodes(&out) == 0);
}

proptest! {
    #![proptest_config(ProptestConfig::with_cases(64))]

    /// Small inputs keep the historical per-path rewrite, and both paths
    /// re-inline to the input.
    #[test]
    fn eliminate_ite_both_paths_reinline(seed in any::<u64>(), n in 1usize..120) {
        for cap in [2_000u128, 2_000_000] {
            let e = random_dag(seed, n, cap);
            let out = e.eliminate_ite();
            let (back, _) = reinline_ite(&out);
            prop_assert!(back == e);
            prop_assert_eq!(arith_ite_nodes(&out), 0);
        }
    }
}

#[test]
fn convert_expr_memo_is_exact_and_counts_distinct_nodes() {
    use crate::smt::SmtContext;
    let a = ite_chain(60, "");
    let b = ite_chain(60, "");
    let fa = ChcExpr::le(a.as_ref().clone(), ChcExpr::Real(5, 1));
    let fb = ChcExpr::le(b.as_ref().clone(), ChcExpr::Real(5, 1));
    let mut ctx = SmtContext::new();
    let t = Instant::now();
    let ta = ctx.convert_expr(&fa);
    assert_fast("convert_expr", t);
    assert!(!ctx.conversion_budget_exceeded());
    let tb = ctx.convert_expr(&fb);
    assert_eq!(ta, tb, "pointer-distinct copies convert to the same term");
    // A small, unshared expression: identical to the plain walk.
    let small = ite_chain(6, "s");
    let mut plain = SmtContext::new();
    let ts = plain.convert_expr(&small);
    let ts2 = ctx.convert_expr(&small);
    assert_eq!(plain.terms.sort(ts), ctx.terms.sort(ts2));
}

// ---------------------------------------------------------------------------
// Real instances: vendored CHC-COMP-26 sally/oral_messages fixtures
// ---------------------------------------------------------------------------

const OM_4_6_AGREEMENT: &str = include_str!(
    "../../../tests/fixtures/chc_comp/sally/oral_messages/om1_with_relays_general_4_6_agreement_000.smt2"
);
const OM_3_10_AGREEMENT: &str = include_str!(
    "../../../tests/fixtures/chc_comp/sally/oral_messages/om1_with_relays_general_3_10_agreement_000.smt2"
);

/// Every expression a clause carries: constraint, body and head arguments.
fn clause_exprs(problem: &crate::ChcProblem) -> Vec<ChcExpr> {
    let mut out = Vec::new();
    for clause in problem.clauses() {
        if let Some(c) = &clause.body.constraint {
            out.push(c.clone());
        }
        for (_, args) in &clause.body.predicates {
            out.extend(args.iter().cloned());
        }
        if let crate::ClauseHead::Predicate(_, args) = &clause.head {
            out.extend(args.iter().cloned());
        }
    }
    out
}

/// On a real ITE-heavy transition system small enough for the tree walks to
/// finish, every DAG pass returns what the corresponding tree walk returns.
#[test]
fn real_instance_dag_passes_equal_tree_walks() {
    let problem = crate::ChcParser::parse(OM_4_6_AGREEMENT).expect("fixture parses");
    let again = crate::ChcParser::parse(OM_4_6_AGREEMENT).expect("fixture parses");
    let exprs = clause_exprs(&problem);
    let copies = clause_exprs(&again);
    let mut largest_tree = 0u128;
    for (e, copy) in exprs.iter().zip(&copies) {
        let (dag, tree) = dag_and_tree_size(e);
        largest_tree = largest_tree.max(tree);
        assert!(
            tree <= 2_000_000,
            "fixture exceeds the reference range: tree {tree} dag {dag}"
        );
        // Hash/Eq: pointer-distinct reparse is equal and hashes equal; small
        // expressions hash exactly as the former derive.
        assert!(e == copy);
        assert_eq!(e.structural_hash(), copy.structural_hash());
        if tree <= crate::expr::structural::HASH_EXACT_CHILD_VISITS as u128 {
            let mut r = Recorder::default();
            e.hash(&mut r);
            assert_eq!(r.0, mirror_bytes(e));
        }
        assert_eq!(e.vars(), reference_vars(e));
        assert_eq!(features_tuple(&e.scan_features()), reference_scan(e));
        assert!(
            crate::expr::normalize::NegationsDag::run(e) == e.normalize_negations_tree(),
            "normalize_negations: DAG and tree forms differ"
        );
        assert!(
            crate::expr::normalize::StrictDag::run(e) == e.normalize_strict_int_comparisons_tree(),
            "normalize_strict_int_comparisons: DAG and tree forms differ"
        );
        for eliminated in [e.eliminate_ite_dag(), e.eliminate_ite_tree()] {
            let (back, _) = reinline_ite(&eliminated);
            assert!(back == *e, "eliminate_ite must re-inline to its input");
        }
        let mut ctx = crate::smt::SmtContext::new();
        let memoised = ctx.convert_expr(e);
        assert!(!ctx.conversion_budget_exceeded());
        ctx.reset_conversion_budget();
        let plain = ctx.convert_expr_unmemoised(e);
        assert_eq!(
            memoised, plain,
            "convert_expr memo must return the tree walk's term"
        );
    }
    assert!(
        largest_tree > 100_000,
        "the fixture exercises the DAG paths"
    );
    // and_all over the transition's conjuncts equals the pre-F0 flattening.
    let transition = exprs
        .iter()
        .max_by_key(|e| dag_and_tree_size(e).1)
        .expect("clauses");
    let parts: Vec<ChcExpr> = transition.conjuncts().into_iter().cloned().collect();
    assert!(reference_eq(
        &ChcExpr::and_all(parts.clone()),
        &reference_connective(ChcOp::And, parts)
    ));
}

/// Per-pass micro-benchmark on om1_with_relays_general_3_10_agreement (tree
/// ~3.9e8, where every pre-F0 tree walk ran for minutes): prints DAG vs tree
/// size and the time of each pass, and bounds the whole front end.
#[test]
fn real_instance_front_end_micro_benchmark() {
    let t = Instant::now();
    let problem = crate::ChcParser::parse(OM_3_10_AGREEMENT).expect("fixture parses");
    let parse = t.elapsed();
    let again = crate::ChcParser::parse(OM_3_10_AGREEMENT).expect("fixture parses");
    let exprs = clause_exprs(&problem);
    let copies = clause_exprs(&again);
    let (idx, e) = exprs
        .iter()
        .enumerate()
        .max_by_key(|(_, e)| dag_and_tree_size(e).1)
        .expect("clauses");
    let copy = &copies[idx];
    let (dag, tree) = dag_and_tree_size(e);
    let mut rows: Vec<(&str, Duration)> = vec![("parse", parse)];
    let mut time = |name: &'static str, f: &mut dyn FnMut()| {
        let t = Instant::now();
        f();
        rows.push((name, t.elapsed()));
    };
    time("hash", &mut || {
        std::hint::black_box(e.structural_hash());
    });
    time("eq (reparsed copy)", &mut || assert!(e == copy));
    time("vars", &mut || {
        std::hint::black_box(e.vars());
    });
    time("scan_features", &mut || {
        std::hint::black_box(e.scan_features());
    });
    time("contains_nonlinear_mul", &mut || {
        std::hint::black_box(e.contains_nonlinear_mul());
    });
    time("and_all(conjuncts)", &mut || {
        std::hint::black_box(ChcExpr::and_all(e.conjuncts().into_iter().cloned()));
    });
    time("simplify_constants", &mut || {
        std::hint::black_box(e.simplify_constants());
    });
    time("eliminate_ite", &mut || {
        std::hint::black_box(e.eliminate_ite());
    });
    time("normalize_negations", &mut || {
        std::hint::black_box(e.normalize_negations());
    });
    time("normalize_strict_int_comparisons", &mut || {
        std::hint::black_box(e.normalize_strict_int_comparisons());
    });
    time("executor sort guard", &mut || {
        std::hint::black_box(crate::smt::executor_sort_guard::unsupported_executor_expr_reason(e));
    });
    time("convert_expr", &mut || {
        let mut ctx = crate::smt::SmtContext::new();
        let _ = std::hint::black_box(ctx.convert_expr(e));
        assert!(!ctx.conversion_budget_exceeded());
    });
    eprintln!("WSF-MICRO om1_with_relays_general_3_10_agreement: dag={dag} tree={tree}");
    for (name, d) in &rows {
        eprintln!("WSF-MICRO {name:<34} {:>10.3} ms", d.as_secs_f64() * 1e3);
    }
    assert!(tree > 100_000_000 && dag < 200_000, "dag {dag} tree {tree}");
    let total: Duration = rows.iter().map(|(_, d)| *d).sum();
    assert!(
        total < Duration::from_secs(20),
        "front-end passes must stay DAG-linear: {total:?}"
    );
}

/// `ChcProblem::validate` (run at every PDR start) on a clause whose
/// constraint is a 2^60-tree DAG containing an uninterpreted function: linear.
#[test]
fn problem_validate_is_linear_on_shared_constraints() {
    use crate::{ChcProblem, ClauseBody, ClauseHead, HornClause};
    let chain = ite_chain(60, "v");
    let f = ChcExpr::FuncApp("f".to_owned(), ChcSort::Real, vec![Arc::clone(&chain)]);
    let constraint = ChcExpr::le(f, ChcExpr::Real(0, 1));
    let mut problem = ChcProblem::new();
    problem.add_clause(HornClause::new(
        ClauseBody::constraint(constraint),
        ClauseHead::False,
    ));
    let t = Instant::now();
    assert!(problem.validate().is_ok());
    assert_fast("ChcProblem::validate", t);
}
