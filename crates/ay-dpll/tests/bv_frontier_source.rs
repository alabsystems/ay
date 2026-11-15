// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! external-codegen's `SMULL` obligation (gate row 2049): a product of two spelled-out
//! sign extensions against the product of the two `sign_extend`s. The
//! identity is decided by congruence once the spelling is recognized, and its
//! certificate proves only the two operand identities by bit-blasting: the
//! shared 64-bit `bvmul` is never blasted, because a miter of two multipliers
//! is what ran the row out of its 130 s budget.
//!
//! Two collapse routes print such a certificate, and this test pins the
//! property, not the route: the congruence walker's bounded leaf
//! (`bvand_commutative_congruence`, tried first) lifts the joint operand lemma
//! through the product with `cong`; the congruence frontier
//! (`bv_identity_promotion/frontier.rs`, which its own unit tests call
//! directly) closes it with an `eq_congruent` clause and resolution. Both
//! routes match a `bvadd` or `bvmul` node crosswise when one side writes its
//! operands in the other order (the walker's `crossed` module).

use std::collections::HashSet;
use std::io::ErrorKind;
use std::path::PathBuf;
use std::process::Command;
use std::time::{Duration, Instant};

use ay_core::{ProofStep, TermData, TermId, TermStore, TheoryLemmaKind};
use ay_dpll::Executor;
use ay_frontend::parse;

const SMULL: &str = "(set-logic QF_BV)
(declare-const x7 (_ BitVec 64))
(declare-const x12 (_ BitVec 64))
(assert (not (= (bvmul (concat (ite (= ((_ extract 31 31) ((_ extract 31 0) x12)) (_ bv1 1)) (_ bv4294967295 32) (_ bv0 32)) ((_ extract 31 0) x12)) (concat (ite (= ((_ extract 31 31) ((_ extract 31 0) x7)) (_ bv1 1)) (_ bv4294967295 32) (_ bv0 32)) ((_ extract 31 0) x7))) (bvmul ((_ sign_extend 32) ((_ extract 31 0) x12)) ((_ sign_extend 32) ((_ extract 31 0) x7))))))
(check-sat)
";

fn solve(input: &str, proofs: bool) -> (Executor, Vec<String>) {
    let query = if proofs {
        format!("{input}(get-proof)\n")
    } else {
        input.to_string()
    };
    let mut executor = Executor::new();
    executor.set_produce_proofs(proofs);
    let outputs = executor.execute_all(&parse(&query).unwrap()).unwrap();
    (executor, outputs)
}

/// The rule a printed step line names, if any.
fn rule_of(line: &str) -> Option<&str> {
    let rest = &line[line.find(":rule ")? + ":rule ".len()..];
    rest.split([' ', ')']).next()
}

fn mentions(terms: &TermStore, root: TermId, name: &str) -> bool {
    let mut seen = HashSet::new();
    let mut pending = vec![root];
    while let Some(term) = pending.pop() {
        if !seen.insert(term) {
            continue;
        }
        if matches!(terms.get(term), TermData::App(symbol, _) if symbol.name() == name) {
            return true;
        }
        pending.extend(terms.children(term));
    }
    false
}

/// Pinned Carcara must answer exactly `valid` (not `holey`) in both of its
/// invocations. With no `carcara` on `PATH` (and no `CARCARA_PATH`) the
/// external check is skipped, except under CI.
fn assert_carcara_valid(problem: &str, proof: &str) {
    if let Err(misjudged) = ay_core::pinned_carcara::pinned_carcara_can_judge(problem, proof) {
        panic!("{misjudged}\n{proof}");
    }
    let configured = std::env::var_os("CARCARA_PATH").map(PathBuf::from);
    let may_skip = configured.is_none() && std::env::var_os("CI").is_none();
    let checker = configured.unwrap_or_else(|| "carcara".into());
    let directory = tempfile::tempdir().expect("temporary Carcara directory");
    let problem_path = directory.path().join("problem.smt2");
    let proof_path = directory.path().join("proof.alethe");
    std::fs::write(&problem_path, problem).expect("write problem");
    std::fs::write(&proof_path, proof).expect("write proof");
    for flags in [
        &["--no-color"][..],
        &["--no-color", "--expand-let-bindings"],
    ] {
        let run = Command::new(&checker)
            .arg("check")
            .args(flags)
            .arg("--")
            .arg(&proof_path)
            .arg(&problem_path)
            .output();
        let output = match run {
            Ok(output) => output,
            Err(error) if error.kind() == ErrorKind::NotFound && may_skip => {
                eprintln!("carcara not found, skipping the external Alethe check");
                return;
            }
            Err(error) => panic!("run {}: {error}", checker.display()),
        };
        let stdout = String::from_utf8_lossy(&output.stdout);
        assert!(
            output.status.success() && stdout.trim() == "valid",
            "carcara check {flags:?}: {stdout}{}\n{proof}",
            String::from_utf8_lossy(&output.stderr)
        );
    }
}

#[test]
fn a_product_of_spelled_sign_extensions_has_a_congruence_certificate() {
    let (executor, outputs) = solve(SMULL, true);
    assert_eq!(
        outputs.first().map(String::as_str),
        Some("unsat"),
        "{outputs:?}"
    );
    let proof = outputs.get(1).expect("published proof");
    assert!(!proof.contains(":rule hole") && !proof.contains(":rule trust"));

    // The product equality is concluded by congruence, and no multiplier
    // circuit is printed: only the operand identities are bit-blasted.
    assert!(
        proof
            .lines()
            .any(|line| line.contains("bvmul")
                && matches!(rule_of(line), Some("cong" | "eq_congruent"))),
        "{proof}"
    );
    assert!(
        !proof.contains("bitblast_mult"),
        "a multiplier circuit was printed:\n{proof}"
    );

    let refutation = executor.last_proof().expect("retained refutation");
    let blasted_products = refutation
        .steps
        .iter()
        .filter(|step| {
            matches!(step, ProofStep::TheoryLemma { kind: TheoryLemmaKind::BvBitBlast, clause, .. }
                if clause.iter().any(|&literal| mentions(executor.terms(), literal, "bvmul")))
        })
        .count();
    assert_eq!(blasted_products, 0, "the multiplier is never bit-blasted");
    let quality = ay_proof::check_proof_strict(refutation, executor.terms())
        .expect("the SMULL certificate must pass strict replay");
    assert_eq!(
        (
            quality.trust_count,
            quality.trust_fallback_count,
            quality.hole_count
        ),
        (0, 0, 0)
    );
    // The dialect-aware verdict on the exported bytes, which the public
    // reader returns too (its UMULL `zero_extend` twin is `CleanDialect` on
    // both: group_proofs `surface_accessor_dialect`).
    let (exported, surface) = executor
        .try_export_last_proof_alethe_for_problem_scope_with_carcara_surface()
        .expect("retained UNSAT proof")
        .expect("problem-scoped export");
    assert_eq!(&exported, proof);
    assert_eq!(surface, ay_proof::CarcaraSurface::Supported);
    assert_eq!(
        executor.last_unsat_proof_carcara_surface(),
        Some(ay_proof::CarcaraSurface::Supported)
    );
    assert_carcara_valid(SMULL, proof);
}

#[test]
fn a_sign_test_on_the_wrong_bit_is_refuted() {
    // `bit 30` is not the sign of the 32-bit operand: the spelled extension
    // disagrees with `sign_extend` whenever bits 30 and 31 differ.
    let input = SMULL.replacen(
        "((_ extract 31 31) ((_ extract 31 0) x12))",
        "((_ extract 30 30) ((_ extract 31 0) x12))",
        1,
    );
    assert_ne!(input, SMULL);
    let (_, outputs) = solve(&input, false);
    assert_eq!(
        outputs.first().map(String::as_str),
        Some("sat"),
        "{outputs:?}"
    );
}

const LEFT_PRODUCT: &str = "(bvmul (concat (ite (= ((_ extract 31 31) ((_ extract 31 0) x12)) (_ bv1 1)) (_ bv4294967295 32) (_ bv0 32)) ((_ extract 31 0) x12)) (concat (ite (= ((_ extract 31 31) ((_ extract 31 0) x7)) (_ bv1 1)) (_ bv4294967295 32) (_ bv0 32)) ((_ extract 31 0) x7)))";
const RIGHT_PRODUCT: &str =
    "(bvmul ((_ sign_extend 32) ((_ extract 31 0) x12)) ((_ sign_extend 32) ((_ extract 31 0) x7)))";

/// `(f a b)` respelled as `(f b a)`, for one of the row's two products.
fn commute(product: &str) -> String {
    let body = product
        .strip_prefix("(bvmul ")
        .and_then(|rest| rest.strip_suffix(')'))
        .expect("a product");
    let mut depth = 0usize;
    let split = body
        .char_indices()
        .find(|&(_, c)| {
            depth = match c {
                '(' => depth + 1,
                ')' => depth - 1,
                _ => depth,
            };
            c == ' ' && depth == 0
        })
        .map(|(at, _)| at)
        .expect("two operands");
    format!("(bvmul {} {})", &body[split + 1..], &body[..split])
}

/// The row with one product's operands swapped (`side` is `"left"` or
/// `"right"`), optionally under external-codegen's `SMULH` high-half `extract`.
fn commuted_smull(side: &str, high_half: bool) -> String {
    let (mut left, mut right) = (LEFT_PRODUCT.to_string(), RIGHT_PRODUCT.to_string());
    match side {
        "left" => left = commute(&left),
        _ => right = commute(&right),
    }
    if high_half {
        left = format!("((_ extract 63 32) {left})");
        right = format!("((_ extract 63 32) {right})");
    }
    let assertion = format!("(assert (not (= {LEFT_PRODUCT} {RIGHT_PRODUCT})))");
    assert!(SMULL.contains(&assertion));
    let input = SMULL.replacen(&assertion, &format!("(assert (not (= {left} {right})))"), 1);
    assert_ne!(input, SMULL);
    input
}

/// The query's own budget: a regression answers `unknown` inside it rather
/// than running into the strict producer's 300 s hang guard.
const WALL: Duration = Duration::from_secs(45);

fn solve_within(input: &str, proofs: bool, wall: Duration) -> (Executor, Vec<String>) {
    let query = if proofs {
        format!("{input}(get-proof)\n")
    } else {
        input.to_string()
    };
    let mut executor = Executor::new();
    executor.set_produce_proofs(proofs);
    executor.set_timeout(Some(wall));
    let started = Instant::now();
    let outputs = executor.execute_all(&parse(&query).unwrap()).unwrap();
    let elapsed = started.elapsed();
    assert!(
        elapsed < wall + Duration::from_secs(30),
        "the verdict must arrive inside the query's budget, took {elapsed:?}"
    );
    (executor, outputs)
}

/// Swapping one product's operands used to defeat both collapse routes,
/// which matched operands by position: the folded identity fell through to
/// the whole-identity bit-blast, a miter of two 64-bit multipliers, which
/// swept until the strict producer's 300 s hang guard and published
/// `unknown` (measured 2026-10-06), and the same under the high-half
/// `extract`. A commuted product is now matched crosswise. The swap itself is
/// the ring lane's `ArithClauseTautology`, printed `poly_simp`. Transitivity
/// joins it to the congruence (`trans` from the walker, `eq_transitive` from
/// the frontier). No multiplier is priced as a proof-producing lemma.
#[test]
fn commuted_products_of_spelled_sign_extensions_are_certified_crosswise() {
    for (side, high_half) in [
        ("right", false),
        ("left", false),
        ("right", true),
        ("left", true),
    ] {
        let input = commuted_smull(side, high_half);
        let (executor, outputs) = solve_within(&input, true, WALL);
        let case = format!("{side} product commuted, high half {high_half}");
        assert_eq!(
            outputs.first().map(String::as_str),
            Some("unsat"),
            "{case}: {outputs:?}"
        );
        let proof = outputs.get(1).expect("published proof");
        assert!(
            !proof.contains(":rule hole") && !proof.contains(":rule trust"),
            "{case}:\n{proof}"
        );
        assert!(
            !proof.contains("bitblast_mult"),
            "{case}: a multiplier circuit was printed:\n{proof}"
        );
        let swaps: Vec<&str> = proof
            .lines()
            .filter(|line| rule_of(line) == Some("poly_simp"))
            .collect();
        assert!(
            matches!(swaps.as_slice(), [swap] if swap.contains("bvmul")),
            "{case}:\n{proof}"
        );
        assert!(
            proof
                .lines()
                .any(|line| matches!(rule_of(line), Some("trans" | "eq_transitive"))),
            "{case}:\n{proof}"
        );

        let refutation = executor.last_proof().expect("retained refutation");
        let priced_products = refutation
            .steps
            .iter()
            .filter(|step| {
                matches!(step, ProofStep::TheoryLemma { kind: TheoryLemmaKind::BvBitBlast, clause, .. }
                    if clause.iter().any(|&literal| mentions(executor.terms(), literal, "bvmul"))
                        && ay_proof::bv_bitblast_requires_proof_producer(executor.terms(), clause))
            })
            .count();
        assert_eq!(
            priced_products, 0,
            "{case}: the multiplier is never bit-blasted"
        );
        let quality = ay_proof::check_proof_strict(refutation, executor.terms())
            .expect("the commuted certificate must pass strict replay");
        assert_eq!(
            (
                quality.trust_count,
                quality.trust_fallback_count,
                quality.hole_count
            ),
            (0, 0, 0),
            "{case}"
        );
        assert_carcara_valid(&input, proof);
    }
}

/// NEGATIVE twins of the crossed match: with bit 30 tested, the commuted
/// spelling is no sign extension, and the row is refuted, whole or high half.
#[test]
fn a_commuted_sign_test_on_the_wrong_bit_is_refuted() {
    for high_half in [false, true] {
        let commuted = commuted_smull("right", high_half);
        let input = commuted.replacen(
            "((_ extract 31 31) ((_ extract 31 0) x12))",
            "((_ extract 30 30) ((_ extract 31 0) x12))",
            1,
        );
        assert_ne!(input, commuted);
        let (_, outputs) = solve_within(&input, false, WALL);
        assert_eq!(
            outputs.first().map(String::as_str),
            Some("sat"),
            "high half {high_half}: {outputs:?}"
        );
    }
}

/// A pure ring identity keeps the ring lane's single `poly_simp` lemma:
/// twenty products, each with its operands swapped. The crosswise walk runs
/// only after the ring lane. Tried first, it crossed every product, its
/// certificate exceeded the printer's `poly_simp` cap, and the wire-gap repair
/// that followed ran past 100 s on a 10 s budget (measured 2026-10-07).
#[test]
fn a_sum_of_commuted_products_keeps_its_single_ring_lemma() {
    let mut input = String::from("(set-logic QF_BV)\n");
    let (mut left, mut right) = (String::new(), String::new());
    for i in 0..20 {
        input +=
            &format!("(declare-const a{i} (_ BitVec 64))\n(declare-const b{i} (_ BitVec 64))\n");
        (left, right) = if i == 0 {
            ("(bvmul a0 b0)".into(), "(bvmul b0 a0)".into())
        } else {
            (
                format!("(bvadd (bvmul a{i} b{i}) {left})"),
                format!("(bvadd (bvmul b{i} a{i}) {right})"),
            )
        };
    }
    input += &format!("(assert (not (= {left} {right})))\n(check-sat)\n");
    let (_, outputs) = solve_within(&input, true, WALL);
    assert_eq!(
        outputs.first().map(String::as_str),
        Some("unsat"),
        "{outputs:?}"
    );
    let proof = outputs.get(1).expect("published proof");
    assert!(!proof.contains(":rule hole") && !proof.contains(":rule trust"));
    let lemmas = proof
        .lines()
        .filter(|line| rule_of(line) == Some("poly_simp"))
        .count();
    assert_eq!(lemmas, 1, "{proof}");
    assert_carcara_valid(&input, proof);
}

/// A folded identity no structural route closes still reaches the
/// whole-identity bit-blast: a product regrouped across a third register, and
/// a commuted product under more crossed sums than the printer can typeset
/// swaps for. That fallback is stopped by the query's budget and fails
/// closed: never `sat`, and never past the budget.
#[test]
fn an_unrouted_product_identity_is_bounded_by_the_query_budget() {
    let regrouped = SMULL
        .replacen(
            "(declare-const x12 (_ BitVec 64))",
            "(declare-const x12 (_ BitVec 64))\n(declare-const x3 (_ BitVec 64))",
            1,
        )
        .replacen("(bvmul (concat", "(bvmul (bvmul (concat", 1)
        .replacen(
            "((_ extract 31 0) x7))) (bvmul ((_ sign_extend 32) ((_ extract 31 0) x12)) ((_ sign_extend 32) ((_ extract 31 0) x7)))",
            "((_ extract 31 0) x7))) x3) (bvmul ((_ sign_extend 32) ((_ extract 31 0) x12)) (bvmul ((_ sign_extend 32) ((_ extract 31 0) x7)) x3))",
            1,
        );
    assert_eq!(regrouped.matches("x3").count(), 3, "{regrouped}");
    let (mut left, mut right) = (LEFT_PRODUCT.to_string(), commute(RIGHT_PRODUCT));
    for _ in 0..ay_proof::MAX_ARITH_POLY_SIMP_PROMOTIONS_PER_PROOF {
        left = format!("(bvadd {left} x9)");
        right = format!("(bvadd x9 {right})");
    }
    let crossed = SMULL
        .replacen(
            "(declare-const x12 (_ BitVec 64))",
            "(declare-const x12 (_ BitVec 64))\n(declare-const x9 (_ BitVec 64))",
            1,
        )
        .replacen(
            &format!("(assert (not (= {LEFT_PRODUCT} {RIGHT_PRODUCT})))"),
            &format!("(assert (not (= {left} {right})))"),
            1,
        );
    assert!(crossed.contains("(bvadd x9"), "{crossed}");
    for input in [regrouped, crossed] {
        let budget = Duration::from_secs(3);
        let (_, outputs) = solve_within(&input, true, budget);
        assert!(
            matches!(
                outputs.first().map(String::as_str),
                Some("unsat" | "unknown")
            ),
            "{outputs:?}"
        );
    }
}
