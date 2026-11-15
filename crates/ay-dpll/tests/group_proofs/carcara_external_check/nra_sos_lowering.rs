// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Pinned-carcara replay of the checked native SOS lowering.
//!
//! The printer renders a strict-checked `NraSos` certificate as `la_mult_pos` /
//! `la_mult_neg` products, `poly_simp` normal forms and one `la_generic` with
//! the certificate's own coefficients. These fixtures run that rendering past
//! carcara 1.1.0 with NO allowance: the corpus row, clauses printed through
//! the problem's authored spellings, a hand-built Real certificate exercising
//! a Gram square with a rational `L·D·Lᵀ` multiplier, a strict-by-nonstrict
//! product and an unused positive equality, a strict-by-strict product, a
//! factor times itself, an Int square, and the negative twin — a certificate
//! the strict checker refuses stays a disclosed `hole`, which carcara reports
//! as `holey`, never `valid`.

use super::{
    benchmark_content, carcara_verdict_without_allowances, require_carcara_or_skip,
    solve_unsat_and_get_proof, CarcaraVerdict,
};
use ay_core::{
    NraSosCertificate, NraSosOrigin, NraSosRational, NraSosTerm, Proof, ProofStep, Sort, Symbol,
    TermData, TermId, TermStore,
};
use ntest::timeout;
use num_bigint::BigInt;
use num_rational::BigRational;

fn rational(numerator: i64, denominator: i64) -> NraSosRational {
    NraSosRational {
        numerator: BigInt::from(numerator),
        denominator: BigInt::from(denominator),
    }
}

fn term(origin: NraSosOrigin, multiplier: NraSosRational) -> NraSosTerm {
    NraSosTerm { origin, multiplier }
}

fn app(terms: &mut TermStore, op: &str, args: &[TermId], sort: Sort) -> TermId {
    terms.mk_app(Symbol::named(op), args, sort)
}

/// Export the SOS lemma refuted against the negated source of every literal,
/// and the problem whose assertions are exactly those `assume` leaves.
fn exported(
    terms: &mut TermStore,
    clause: Vec<TermId>,
    certificate: NraSosCertificate,
    logic: &str,
) -> (String, String) {
    let mut proof = Proof::new();
    let mut current = proof.add_step(ProofStep::NraSos {
        clause: clause.clone(),
        certificate,
    });
    for (index, &literal) in clause.iter().enumerate() {
        let (pivot, source) = match terms.get(literal) {
            TermData::Not(inner) => (*inner, *inner),
            _ => (literal, terms.mk_not(literal)),
        };
        let assume = proof.add_assume(source, None);
        current = proof.add_resolution(clause[index + 1..].to_vec(), pivot, current, assume);
    }
    let document = ay_proof::try_export_alethe(&proof, terms).expect("SOS document");
    let mut problem = format!("(set-logic {logic})\n");
    let mut alethe = String::new();
    for line in document.lines() {
        if line.starts_with("(declare-") {
            problem.push_str(line);
            problem.push('\n');
        } else {
            alethe.push_str(line);
            alethe.push('\n');
        }
    }
    for line in document.lines() {
        if let Some((_, assumed)) = line
            .strip_prefix("(assume ")
            .and_then(|rest| rest.split_once(' '))
        {
            problem.push_str(&format!("(assert {assumed}\n"));
        }
    }
    problem.push_str("(check-sat)\n");
    (problem, alethe)
}

fn assert_valid(label: &str, problem: &str, proof: &str) {
    assert!(!proof.contains(":rule hole"), "{label}:\n{proof}");
    assert!(!proof.contains(":rule trust"), "{label}:\n{proof}");
    assert!(proof.contains("ay-nra-sos:"), "{label}:\n{proof}");
    let Some(carcara) = require_carcara_or_skip() else {
        return;
    };
    assert_eq!(
        carcara_verdict_without_allowances(&carcara, label, problem, proof),
        CarcaraVerdict::Valid,
        "{label}: the lowered SOS certificate must be re-derived by pinned carcara"
    );
}

#[test]
#[timeout(60_000)]
fn simple_product_corpus_row_lowers_to_a_carcara_valid_proof() {
    let problem = benchmark_content("benchmarks/smt/QF_NIA/simple_product_unsat.smt2")
        .lines()
        .filter(|line| line.trim() != "(exit)")
        .collect::<Vec<_>>()
        .join("\n");
    let proof = solve_unsat_and_get_proof(&problem, "nra_sos_simple_product");
    assert!(proof.contains(":rule la_mult_pos"), "{proof}");
    assert_valid("nra_sos_simple_product", &problem, &proof);
}

/// A certificate whose lowering is ONE `la_generic` refutation. Before the fix
/// the printer closed it with `(step t4 .. :rule resolution :premises
/// (t4.sos.g0))`, a one-premise `resolution` pinned carcara rejects ("expected
/// at least 2 premises, got 1"), while the header said `trust_free=yes`; the
/// strict route published it as well. The lone refutation now closes with
/// `reordering` (after `weakening` when unused literals were dropped).
#[test]
#[timeout(60_000)]
fn a_lone_la_generic_refutation_closes_without_a_one_premise_resolution() {
    let problem = "(set-logic QF_LIA)
(declare-fun a () Int)
(declare-fun b () Int)
(declare-fun c () Int)
(assert (= a 1))
(assert (= b 1))
(assert (= c 1))
(assert (= (- a b c) 7))
(check-sat)";
    let proof = solve_unsat_and_get_proof(problem, "nra_sos_lone_refutation");
    assert!(proof.contains(":rule reordering"), "{proof}");
    for line in proof
        .lines()
        .filter(|line| line.contains(":rule resolution"))
    {
        let premises = line.split(":premises (").nth(1).map_or(0, |rest| {
            rest.trim_end_matches(')').split_whitespace().count()
        });
        assert!(
            premises >= 2,
            "a one-premise resolution was printed: {line}"
        );
    }
    assert_valid("nra_sos_lone_refutation", problem, &proof);
}

/// The SOS clause of each of these prints through the problem's AUTHORED
/// spelling (measured: it reaches the printer's override channel, so its text
/// differs from the term DAG's), and the lowering derives every row from that
/// text: a Gram square `(x - y)²` against `(* 2.0 x y)`, a shifted square
/// against `(- (* 2.0 x) 1.0)`, a bounded product against `(> (* y x) 5.0)`,
/// and the corpus's own Int strict-by-strict product `sign_consistency`.
#[test]
#[timeout(60_000)]
fn authored_spellings_lower_to_carcara_valid_proofs() {
    let reals = "(set-logic QF_NRA)\n(declare-fun x () Real)\n(declare-fun y () Real)\n";
    let sign_consistency = benchmark_content("benchmarks/smt/QF_NIA/sign_consistency.smt2")
        .lines()
        .filter(|line| line.trim() != "(exit)")
        .collect::<Vec<_>>()
        .join("\n");
    for (label, problem) in [
        (
            "nra_sos_authored_square",
            format!("{reals}(assert (< (+ (* x x) (* y y)) (* 2.0 x y)))\n(check-sat)\n"),
        ),
        (
            "nra_sos_authored_shifted_square",
            format!("{reals}(assert (<= (+ (* x x) 1.0) (- (* 2.0 x) 1.0)))\n(check-sat)\n"),
        ),
        (
            "nra_sos_authored_product",
            format!(
                "{reals}(assert (>= x 0.0))\n(assert (>= y 0.0))\n(assert (<= x 2.0))\n\
                 (assert (<= y 2.0))\n(assert (> (* y x) 5.0))\n(check-sat)\n"
            ),
        ),
        ("nra_sos_sign_consistency", sign_consistency),
        // The equality's constant `2` is interned by an earlier bound, so the
        // term DAG orders the source `(= 2 (* x y))` while the problem prints
        // `(= (* x y) 2)`: the row the pinned checker reads is negated.
        (
            "nra_sos_reversed_equality",
            "(set-logic QF_NIA)\n(declare-fun x () Int)\n(declare-fun y () Int)\n\
             (assert (>= x 1))\n(assert (<= x 2))\n(assert (>= y 3))\n(assert (<= y 4))\n\
             (assert (= (* x y) 2))\n(check-sat)\n"
                .to_string(),
        ),
    ] {
        let proof = solve_unsat_and_get_proof(&problem, label);
        assert!(proof.contains(":rule la_mult_"), "{label}:\n{proof}");
        assert_valid(label, &problem, &proof);
    }
}

/// Real `0 < x`, `0 <= y`, `x*x + y*y + y*x < 0` and an unused `(= x y)`:
/// `(x - y/2)² + (3/4)·y² + 2·(x·y) = x² + xy + y²`.
#[test]
#[timeout(60_000)]
fn gram_square_and_strict_product_lower_to_a_carcara_valid_proof() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Real);
    let y = terms.mk_var("y", Sort::Real);
    let zero = terms.mk_rational(BigRational::from_integer(BigInt::from(0)));
    let xx = app(&mut terms, "*", &[x, x], Sort::Real);
    let yy = app(&mut terms, "*", &[y, y], Sort::Real);
    let yx = app(&mut terms, "*", &[y, x], Sort::Real);
    let sum = app(&mut terms, "+", &[xx, yy, yx], Sort::Real);
    let sources = [
        app(&mut terms, "<", &[zero, x], Sort::Bool),
        app(&mut terms, "<=", &[zero, y], Sort::Bool),
        app(&mut terms, "<", &[sum, zero], Sort::Bool),
    ];
    let mut clause: Vec<TermId> = sources.into_iter().map(|s| terms.mk_not(s)).collect();
    clause.push(app(&mut terms, "=", &[x, y], Sort::Bool));
    let certificate = NraSosCertificate {
        basis: vec![vec![], vec![x], vec![y]],
        gram: vec![
            vec![rational(0, 1), rational(0, 1), rational(0, 1)],
            vec![rational(0, 1), rational(1, 1), rational(-1, 2)],
            vec![rational(0, 1), rational(-1, 2), rational(1, 1)],
        ],
        terms: vec![
            term(NraSosOrigin::Product { left: 0, right: 1 }, rational(2, 1)),
            term(NraSosOrigin::ClauseLiteral { position: 2 }, rational(1, 1)),
        ],
        rhs: rational(0, 1),
    };
    let (problem, proof) = exported(&mut terms, clause, certificate, "QF_NRA");
    assert!(proof.contains(":rule la_mult_neg"), "{proof}");
    assert_valid("nra_sos_gram_product", &problem, &proof);
}

fn real(terms: &mut TermStore, value: i64) -> TermId {
    terms.mk_rational(BigRational::from_integer(BigInt::from(value)))
}

/// Real `1 < x`, `2 < y`, `x*y < 2`: the strict-by-strict product
/// `(x-1)(y-2) > 0` plus `2(x-1) + (y-2) + (2-xy) = 0`.
#[test]
#[timeout(60_000)]
fn strict_product_lowers_to_a_carcara_valid_proof() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Real);
    let y = terms.mk_var("y", Sort::Real);
    let [one, two] = [1, 2].map(|value| real(&mut terms, value));
    let xy = app(&mut terms, "*", &[x, y], Sort::Real);
    let sources = [
        app(&mut terms, "<", &[one, x], Sort::Bool),
        app(&mut terms, "<", &[two, y], Sort::Bool),
        app(&mut terms, "<", &[xy, two], Sort::Bool),
    ];
    let clause = sources.into_iter().map(|s| terms.mk_not(s)).collect();
    let literal =
        |position, value| term(NraSosOrigin::ClauseLiteral { position }, rational(value, 1));
    let certificate = NraSosCertificate {
        basis: vec![vec![]],
        gram: vec![vec![rational(0, 1)]],
        terms: vec![
            term(NraSosOrigin::Product { left: 0, right: 1 }, rational(1, 1)),
            literal(0, 2),
            literal(1, 1),
            literal(2, 1),
        ],
        rhs: rational(0, 1),
    };
    let (problem, proof) = exported(&mut terms, clause, certificate, "QF_NRA");
    assert!(proof.contains(":rule la_mult_pos"), "{proof}");
    assert_valid("nra_sos_strict_product", &problem, &proof);
}

/// Real `1 <= x`, `x*x < 1`: a nonstrict factor times itself,
/// `(x-1)² + 2(x-1) + (1-x²) = 0`.
#[test]
#[timeout(60_000)]
fn self_product_lowers_to_a_carcara_valid_proof() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Real);
    let one = real(&mut terms, 1);
    let xx = app(&mut terms, "*", &[x, x], Sort::Real);
    let sources = [
        app(&mut terms, "<=", &[one, x], Sort::Bool),
        app(&mut terms, "<", &[xx, one], Sort::Bool),
    ];
    let clause = sources.into_iter().map(|s| terms.mk_not(s)).collect();
    let certificate = NraSosCertificate {
        basis: vec![vec![]],
        gram: vec![vec![rational(0, 1)]],
        terms: vec![
            term(NraSosOrigin::Product { left: 0, right: 0 }, rational(1, 1)),
            term(NraSosOrigin::ClauseLiteral { position: 0 }, rational(2, 1)),
            term(NraSosOrigin::ClauseLiteral { position: 1 }, rational(1, 1)),
        ],
        rhs: rational(0, 1),
    };
    let (problem, proof) = exported(&mut terms, clause, certificate, "QF_NRA");
    assert!(proof.contains(":rule la_mult_pos"), "{proof}");
    assert_valid("nra_sos_self_product", &problem, &proof);
}

fn int_square(rhs: i64) -> (String, String) {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Int);
    let zero = terms.mk_int(BigInt::from(0));
    let square = app(&mut terms, "*", &[x, x], Sort::Int);
    let negative = app(&mut terms, "<", &[square, zero], Sort::Bool);
    let clause = vec![terms.mk_not(negative)];
    let certificate = NraSosCertificate {
        basis: vec![vec![], vec![x]],
        gram: vec![
            vec![rational(0, 1), rational(0, 1)],
            vec![rational(0, 1), rational(1, 1)],
        ],
        terms: vec![term(
            NraSosOrigin::ClauseLiteral { position: 0 },
            rational(1, 1),
        )],
        rhs: rational(rhs, 1),
    };
    exported(&mut terms, clause, certificate, "QF_NIA")
}

#[test]
#[timeout(60_000)]
fn int_square_lowers_to_a_carcara_valid_proof() {
    let (problem, proof) = int_square(0);
    assert_valid("nra_sos_int_square", &problem, &proof);
}

/// NEGATIVE TWIN: a misstated `rhs` is refused by the strict checker ALONE —
/// the rows still refute the clause, so the pinned replay would accept a
/// rendering — and the printer keeps its honest hole, which pinned carcara
/// reports as `holey`, never as verification.
#[test]
#[timeout(60_000)]
fn a_certificate_the_strict_checker_refuses_is_never_lowered() {
    let (problem, proof) = int_square(-1);
    assert!(proof.contains(":rule hole"), "{proof}");
    assert!(!proof.contains(":rule la_mult_neg"), "{proof}");
    let Some(carcara) = require_carcara_or_skip() else {
        return;
    };
    assert_eq!(
        carcara_verdict_without_allowances(&carcara, "nra_sos_refused", &problem, &proof),
        CarcaraVerdict::Holey
    );
}
