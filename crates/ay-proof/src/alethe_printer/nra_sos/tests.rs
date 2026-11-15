// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The checked SOS lowering renders exactly the certificates the strict
//! checker accepts, and nothing else. Pinned-carcara replays of the same
//! fixtures live in ay-dpll's `carcara_external_check/nra_sos_lowering.rs`.

use super::*;
use ay_core::{NraSosRational, NraSosTerm, Proof, Symbol};
use num_bigint::BigInt;
use num_rational::BigRational;

fn rational(numerator: i64, denominator: i64) -> NraSosRational {
    NraSosRational {
        numerator: BigInt::from(numerator),
        denominator: BigInt::from(denominator),
    }
}

fn term(origin: NraSosOrigin, multiplier: i64) -> NraSosTerm {
    NraSosTerm {
        origin,
        multiplier: rational(multiplier, 1),
    }
}

fn literal(position: u32) -> NraSosOrigin {
    NraSosOrigin::ClauseLiteral { position }
}

fn app(terms: &mut TermStore, op: &str, args: &[TermId], sort: Sort) -> TermId {
    terms.mk_app(Symbol::named(op), args, sort)
}

/// The SOS lemma, the negated source of every literal as an `assume`, and
/// the resolution chain to the empty clause.
fn refutation(terms: &mut TermStore, clause: Vec<TermId>, certificate: NraSosCertificate) -> Proof {
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
    proof
}

/// `1 <= x <= 2`, `1 <= y <= 2`, `x*y = 7` over Int: the corpus row
/// `QF_NIA_simple_product_unsat`, refuted by `(x-1)(2-y) >= 0`.
fn simple_product(
    multiplier_of_upper_x: i64,
    rhs: i64,
) -> (TermStore, Vec<TermId>, NraSosCertificate) {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Int);
    let y = terms.mk_var("y", Sort::Int);
    let [one, two, seven] = [1, 2, 7].map(|value| terms.mk_int(BigInt::from(value)));
    let sources = [
        app(&mut terms, "<=", &[one, x], Sort::Bool),
        app(&mut terms, "<=", &[x, two], Sort::Bool),
        app(&mut terms, "<=", &[one, y], Sort::Bool),
        app(&mut terms, "<=", &[y, two], Sort::Bool),
    ];
    let product = app(&mut terms, "*", &[x, y], Sort::Int);
    let equality = app(&mut terms, "=", &[product, seven], Sort::Bool);
    let clause = sources
        .into_iter()
        .chain([equality])
        .map(|source| terms.mk_not(source))
        .collect();
    let certificate = NraSosCertificate {
        basis: vec![vec![]],
        gram: vec![vec![rational(0, 1)]],
        terms: vec![
            term(NraSosOrigin::Product { left: 0, right: 3 }, 1),
            term(literal(1), multiplier_of_upper_x),
            term(literal(3), 1),
            term(literal(4), 1),
        ],
        rhs: rational(rhs, 1),
    };
    (terms, clause, certificate)
}

/// Real `x > 0`, `y >= 0`, `x*x + y*y + y*x < 0`, plus an unused positive
/// equality literal: a strict-by-nonstrict product, a Gram matrix whose
/// `L·D·Lᵀ` has a rational multiplier, and a product atom spelled `(* y x)`.
fn gram_and_product() -> (TermStore, Vec<TermId>, NraSosCertificate) {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Real);
    let y = terms.mk_var("y", Sort::Real);
    let zero = terms.mk_rational(BigRational::from_integer(BigInt::from(0)));
    let xx = app(&mut terms, "*", &[x, x], Sort::Real);
    let yy = app(&mut terms, "*", &[y, y], Sort::Real);
    let yx = app(&mut terms, "*", &[y, x], Sort::Real);
    let sum = app(&mut terms, "+", &[xx, yy, yx], Sort::Real);
    let positive_x = app(&mut terms, "<", &[zero, x], Sort::Bool);
    let nonnegative_y = app(&mut terms, "<=", &[zero, y], Sort::Bool);
    let negative_sum = app(&mut terms, "<", &[sum, zero], Sort::Bool);
    let clause = vec![
        terms.mk_not(positive_x),
        terms.mk_not(nonnegative_y),
        terms.mk_not(negative_sum),
        app(&mut terms, "=", &[x, y], Sort::Bool),
    ];
    let certificate = NraSosCertificate {
        basis: vec![vec![], vec![x], vec![y]],
        gram: vec![
            vec![rational(0, 1), rational(0, 1), rational(0, 1)],
            vec![rational(0, 1), rational(1, 1), rational(-1, 2)],
            vec![rational(0, 1), rational(-1, 2), rational(1, 1)],
        ],
        terms: vec![
            term(NraSosOrigin::Product { left: 0, right: 1 }, 2),
            term(literal(2), 1),
        ],
        rhs: rational(0, 1),
    };
    (terms, clause, certificate)
}

fn real(terms: &mut TermStore, value: i64) -> TermId {
    terms.mk_rational(BigRational::from_integer(BigInt::from(value)))
}

/// Real `1 < x`, `2 < y`, `x*y < 2`: the strict-by-strict product
/// `(x-1)(y-2) > 0` plus `2(x-1) + (y-2) + (2-xy) = 0`.
fn strict_product() -> (TermStore, Vec<TermId>, NraSosCertificate) {
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
    let certificate = NraSosCertificate {
        basis: vec![vec![]],
        gram: vec![vec![rational(0, 1)]],
        terms: vec![
            term(NraSosOrigin::Product { left: 0, right: 1 }, 1),
            term(literal(0), 2),
            term(literal(1), 1),
            term(literal(2), 1),
        ],
        rhs: rational(0, 1),
    };
    (terms, clause, certificate)
}

/// Real `1 <= x`, `x*x < 1`: a nonstrict factor times itself,
/// `(x-1)² + 2(x-1) + (1-x²) = 0`.
fn self_product() -> (TermStore, Vec<TermId>, NraSosCertificate) {
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
            term(NraSosOrigin::Product { left: 0, right: 0 }, 1),
            term(literal(0), 2),
            term(literal(1), 1),
        ],
        rhs: rational(0, 1),
    };
    (terms, clause, certificate)
}

fn strictly_checked(terms: &TermStore, clause: &[TermId], certificate: &NraSosCertificate) -> bool {
    crate::checker::validate_nra_sos_with_progress(
        terms,
        ProofId(0),
        clause,
        certificate,
        &mut |_, _| true,
    )
    .is_ok()
}

fn lowered_document(
    terms: &mut TermStore,
    clause: Vec<TermId>,
    certificate: NraSosCertificate,
) -> String {
    assert!(strictly_checked(terms, &clause, &certificate));
    assert!(nra_sos_lowering_supported(
        terms,
        &clause,
        &certificate,
        None
    ));
    let proof = refutation(terms, clause, certificate);
    let document = crate::try_export_alethe(&proof, terms).expect("lowered SOS document");
    // AY's own document reader accepts every command the lowering writes.
    let steps: String = document
        .lines()
        .filter(|line| !line.starts_with("(declare-"))
        .flat_map(|line| [line, "\n"])
        .collect();
    crate::check_alethe_document(&steps, &crate::ProblemScope::from_symbols(["x", "y"]))
        .unwrap_or_else(|defect| panic!("{defect:?}\n{steps}"));
    document
}

#[test]
fn product_certificate_lowers_to_checked_multiplication_steps() {
    let (mut terms, clause, certificate) = simple_product(2, -3);
    let document = lowered_document(&mut terms, clause, certificate);
    assert!(!document.contains(":rule hole"), "{document}");
    assert!(!document.contains(":rule trust"), "{document}");
    assert!(document.contains(":rule la_mult_pos"), "{document}");
    assert!(document.contains(":rule poly_simp"), "{document}");
    assert!(
        document.contains(
            "(step t0 (cl (not (<= 1 x)) (not (<= x 2)) (not (<= 1 y)) (not (<= y 2)) \
             (not (= (* x y) 7))) :rule resolution"
        ),
        "the id binds exactly the SOS clause:\n{document}"
    );
}

#[test]
fn gram_square_and_strict_product_lower_to_checked_steps() {
    let (mut terms, clause, certificate) = gram_and_product();
    let document = lowered_document(&mut terms, clause, certificate);
    assert!(!document.contains(":rule hole"), "{document}");
    assert!(document.contains(":rule la_mult_neg"), "{document}");
    // L·D·Lᵀ multiplier 1/2, printed over integral coefficients.
    assert!(document.contains("(+ (* 2.0 x) (- y))"), "{document}");
    assert!(document.contains(":args ("), "{document}");
    assert!(document.contains("(/ 1.0 4.0)"), "{document}");
}

#[test]
fn strict_and_self_products_lower_to_checked_steps() {
    for (mut terms, clause, certificate) in [strict_product(), self_product()] {
        let document = lowered_document(&mut terms, clause, certificate);
        assert!(!document.contains(":rule hole"), "{document}");
        assert!(document.contains(":rule la_mult_pos"), "{document}");
    }
}

/// NEGATIVE TWIN: a certificate the strict checker refuses is never rendered
/// as checked steps, however printable it is; it stays the honest hole. The
/// wrong multiplier `3` leaves an uncancelled `x` (refused by both the checker
/// and the pinned replay). The misstated `rhs = -4` is refused ONLY by the
/// strict checker: the rows themselves still combine to a contradiction the
/// pinned replay would accept, so that case fails if the lowering stops
/// asking the checker first.
#[test]
fn certificate_the_strict_checker_refuses_stays_a_hole() {
    for (multiplier, rhs) in [(3, -3), (2, -4)] {
        certificate_the_strict_checker_refuses_stays_a_hole_for(multiplier, rhs);
    }
}

fn certificate_the_strict_checker_refuses_stays_a_hole_for(multiplier: i64, rhs: i64) {
    let (mut terms, clause, certificate) = simple_product(multiplier, rhs);
    assert!(!strictly_checked(&terms, &clause, &certificate));
    assert!(!nra_sos_lowering_supported(
        &terms,
        &clause,
        &certificate,
        None
    ));
    let printer = AlethePrinter::new(&terms);
    assert!(printer
        .format_nra_sos_lowering(ProofId(0), &clause, &certificate)
        .is_none());
    let rendered = printer
        .format_nra_sos_step(ProofId(0), &clause, &certificate)
        .expect("shape-valid payload renders its diagnostic");
    assert!(rendered.contains("ay-nra-sos: native certificate retained"));
    assert!(rendered.contains(":rule hole"));
    assert!(!rendered.contains("la_mult_pos"));
    let proof = refutation(&mut terms, clause, certificate);
    assert!(crate::try_export_alethe(&proof, &terms)
        .expect("hole document")
        .contains(":rule hole"));
}

/// A checked certificate outside the lowering's one-sort envelope (a product
/// of a `Real` and an `Int` factor) is declined, not guessed at.
#[test]
fn mixed_sort_product_is_declined_to_the_hole() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Real);
    let n = terms.mk_var("n", Sort::Int);
    let [real_zero, real_one] =
        [0, 1].map(|value| terms.mk_rational(BigRational::from_integer(BigInt::from(value))));
    let [int_zero, int_one] = [0, 1].map(|value| terms.mk_int(BigInt::from(value)));
    let sources = [
        app(&mut terms, "<=", &[real_one, x], Sort::Bool),
        app(&mut terms, "<=", &[x, real_zero], Sort::Bool),
        app(&mut terms, "<=", &[int_one, n], Sort::Bool),
        app(&mut terms, "<=", &[n, int_zero], Sort::Bool),
    ];
    let clause: Vec<TermId> = sources.into_iter().map(|s| terms.mk_not(s)).collect();
    let certificate = NraSosCertificate {
        basis: vec![vec![]],
        gram: vec![vec![rational(0, 1)]],
        terms: vec![
            term(NraSosOrigin::Product { left: 0, right: 2 }, 1),
            term(NraSosOrigin::Product { left: 1, right: 2 }, 1),
            term(literal(2), 2),
            term(literal(3), 1),
        ],
        rhs: rational(-1, 1),
    };
    assert!(strictly_checked(&terms, &clause, &certificate));
    assert!(!nra_sos_lowering_supported(
        &terms,
        &clause,
        &certificate,
        None
    ));
    let proof = refutation(&mut terms, clause, certificate);
    assert!(crate::try_export_alethe(&proof, &terms)
        .expect("hole document")
        .contains(":rule hole"));
}

/// The corpus clause with its `1 <= x` and `x*y = c` sources respelled
/// through the override channel, as the problem's authored assertions are.
fn respelled(clause: &[TermId], terms: &TermStore, product: i64) -> HashMap<TermId, String> {
    let source = |literal: TermId| match terms.get(literal) {
        TermData::Not(inner) => *inner,
        _ => panic!("the corpus clause negates each source"),
    };
    let mut overrides = HashMap::default();
    overrides.insert(source(clause[0]), "(>= x 1)".to_string());
    overrides.insert(source(clause[4]), format!("(= (* y x) {product})"));
    overrides
}

/// Authored respellings: the step's clause prints as the problem spelled it
/// (`(>= x 1)`, `(* y x)`), not as the term DAG does. The lowering derives
/// every row from that printed text, so it still lowers, and binds exactly
/// the printed clause the `hole` would otherwise have asserted.
#[test]
fn respelled_clause_lowers_over_its_printed_text() {
    let (terms, clause, certificate) = simple_product(2, -3);
    let overrides = respelled(&clause, &terms, 7);
    assert!(nra_sos_lowering_supported(
        &terms,
        &clause,
        &certificate,
        Some(&overrides)
    ));
    let printer = AlethePrinter::new_with_overrides(&terms, Some(&overrides));
    let rendered = printer
        .format_nra_sos_step(ProofId(0), &clause, &certificate)
        .expect("respelled clause renders");
    assert!(!rendered.contains(":rule hole"), "{rendered}");
    assert!(rendered.contains(":rule la_mult_pos"), "{rendered}");
    assert!(
        rendered.contains(
            "(step t0 (cl (not (>= x 1)) (not (<= x 2)) (not (<= 1 y)) (not (<= y 2)) \
             (not (= (* y x) 7))) :rule resolution"
        ),
        "{rendered}"
    );
}

/// An authored spelling that states the equality source's sides the other
/// way round (`(= 7 (* x y))` for the DAG's `(= (* x y) 7)`) negates the row
/// the pinned `la_generic` reads, so the lowering negates the certificate's
/// multiplier with it: the step lowers and binds exactly the printed clause.
/// A reversed spelling that ALSO changes the proposition (`(= 3 (* x y))`) is
/// no exact negation, keeps its sign, and is declined to the hole.
#[test]
fn reversed_equality_spelling_lowers_with_its_multiplier_negated() {
    let (terms, clause, certificate) = simple_product(2, -3);
    let TermData::Not(equality) = terms.get(clause[4]) else {
        panic!("the corpus clause negates its equality source")
    };
    for (spelling, lowers) in [("(= 7 (* x y))", true), ("(= 3 (* x y))", false)] {
        let mut overrides = respelled(&clause, &terms, 7);
        overrides.insert(*equality, spelling.to_string());
        assert_eq!(
            nra_sos_lowering_supported(&terms, &clause, &certificate, Some(&overrides)),
            lowers,
            "{spelling}"
        );
        let printer = AlethePrinter::new_with_overrides(&terms, Some(&overrides));
        let rendered = printer
            .format_nra_sos_step(ProofId(0), &clause, &certificate)
            .expect("shape-valid payload renders");
        assert_eq!(!rendered.contains(":rule hole"), lowers, "{rendered}");
        if lowers {
            assert!(
                rendered.contains(&format!("(not {spelling})) :rule resolution")),
                "{rendered}"
            );
        }
    }
}

/// NEGATIVE TWIN of the respelled path: a spelling channel that changes the
/// proposition (`x*y = 3`, which this certificate does not refute: its rows
/// now sum to `0 >= -1`) is never rendered as checked steps; the printer
/// keeps the honest hole over the printed clause.
#[test]
fn unfaithful_respelling_is_declined_to_the_hole() {
    let (terms, clause, certificate) = simple_product(2, -3);
    let overrides = respelled(&clause, &terms, 3);
    assert!(!nra_sos_lowering_supported(
        &terms,
        &clause,
        &certificate,
        Some(&overrides)
    ));
    let printer = AlethePrinter::new_with_overrides(&terms, Some(&overrides));
    let rendered = printer
        .format_nra_sos_step(ProofId(0), &clause, &certificate)
        .expect("shape-valid payload renders its diagnostic");
    assert!(rendered.contains(":rule hole"), "{rendered}");
    assert!(!rendered.contains("la_mult_pos"), "{rendered}");
}
