// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Per-family coverage and fail-closed tests for the complete bit-blast
//! refutation.
//!
//! Every test asserts on the EMITTED DOCUMENT, not on an internal flag: a
//! family is covered only when its `bitblast_*` rule is actually printed, and
//! the document contains no `hole` and no `trust` anywhere.

use super::*;
use ay_core::{Sort, Symbol, TermStore};
use num_bigint::BigInt;

#[path = "ask_tests.rs"]
mod ask_tests;
#[path = "constant_product_tests.rs"]
mod constant_product_tests;
#[path = "ground_tests.rs"]
mod ground_tests;
#[path = "implication_tests.rs"]
mod implication_tests;
#[path = "sweep_tests.rs"]
mod sweep_tests;
#[path = "wide_words_tests.rs"]
mod wide_words_tests;
#[path = "zero_extend_zero_tests.rs"]
mod zero_extend_zero_tests;

#[path = "opaque_array_read_tests.rs"]
mod opaque_array_read_tests;

struct Fixture {
    terms: TermStore,
}

impl Fixture {
    fn new() -> Self {
        Self {
            terms: TermStore::new(),
        }
    }

    fn bv(&mut self, name: &str, width: u32) -> TermId {
        self.terms.mk_var(name, Sort::bitvec(width))
    }

    fn boolean(&mut self, name: &str) -> TermId {
        self.terms.mk_var(name, Sort::Bool)
    }

    fn constant(&mut self, value: u32, width: u32) -> TermId {
        self.terms.mk_bitvec(BigInt::from(value), width)
    }

    /// Raw application: the folding builders would rewrite exactly the shapes
    /// these tests are here to exercise.
    fn op(&mut self, name: &str, args: &[TermId], width: u32) -> TermId {
        self.terms
            .mk_app(Symbol::named(name), args, Sort::bitvec(width))
    }

    fn indexed(&mut self, name: &str, indices: Vec<u32>, arg: TermId, width: u32) -> TermId {
        self.terms
            .mk_app(Symbol::indexed(name, indices), [arg], Sort::bitvec(width))
    }

    fn equals(&mut self, left: TermId, right: TermId) -> TermId {
        self.terms
            .mk_app(Symbol::named("="), [left, right], Sort::Bool)
    }

    fn predicate(&mut self, name: &str, left: TermId, right: TermId) -> TermId {
        self.terms
            .mk_app(Symbol::named(name), [left, right], Sort::Bool)
    }

    fn not(&mut self, arg: TermId) -> TermId {
        self.terms.mk_not_raw(arg)
    }

    /// Render the theory lemma `(cl (not assertion))`.
    fn refute(&self, assertion: TermId) -> Option<String> {
        let mut terms = self.terms.clone();
        let literal = terms.mk_not_raw(assertion);
        let printer = AlethePrinter::new(&terms);
        printer.format_bv_complete_blast_refutation(ProofId(1), &[literal])
    }
}

/// Every proof-local name must be DEFINED before its first use.
///
/// Words and gates reference each other in both directions, so emitting the
/// two tables as blocks puts a forward reference in the document and the
/// checker rejects the whole file at parse time — strictly worse than the
/// hole it replaced. This invariant is what keeps the single creation-ordered
/// definition list honest.
fn assert_definitions_precede_uses(document: &str) {
    let mut defined: std::collections::HashSet<&str> = std::collections::HashSet::new();
    for line in document.lines() {
        let introduced = line.strip_prefix("(define-fun ").map(|rest| {
            rest.split_whitespace()
                .next()
                .expect("a define-fun names a symbol")
        });
        for token in line.split(|c: char| !(c.is_alphanumeric() || c == '_' || c == '@')) {
            if !token.starts_with("@ay_cbb_") || Some(token) == introduced {
                continue;
            }
            assert!(
                defined.contains(token),
                "{token} is used before it is defined, in:\n{line}"
            );
        }
        if let Some(name) = introduced {
            defined.insert(name);
        }
    }
}

fn assert_complete(document: &str) {
    assert_definitions_precede_uses(document);
    assert!(
        !document.contains(":rule hole"),
        "a complete refutation must contain no hole:\n{document}"
    );
    assert!(
        !document.contains(":rule trust"),
        "a complete refutation must contain no trust step:\n{document}"
    );
    assert!(
        !document.contains(":rule lia_generic"),
        "a complete refutation must contain no semantically unchecked rule"
    );
    assert!(
        document.contains(":rule resolution"),
        "the transported refutation must be present"
    );
}

#[test]
fn addition_commutativity_is_refuted_without_a_hole() {
    let mut f = Fixture::new();
    let a = f.bv("a", 4);
    let b = f.bv("b", 4);
    let a = f.op("bvand", &[a, b], 4);
    let left = f.op("bvadd", &[a, b], 4);
    let right = f.op("bvadd", &[b, a], 4);
    let equality = f.equals(left, right);
    let assertion = f.not(equality);
    let document = f.refute(assertion).expect("the lemma is refutable");
    assert_complete(&document);
    assert!(document.contains(":rule bitblast_add"));
    assert!(document.contains(":rule bitblast_var"));
    assert!(document.contains(":rule bitblast_equal"));
}

#[test]
fn every_supported_family_is_rendered_and_never_holed() {
    // (family name, expected rule, builder)
    let cases: Vec<(&str, &str, fn(&mut Fixture) -> TermId)> = vec![
        ("add", "bitblast_add", |f| {
            let a = f.bv("a", 4);
            let b = f.bv("b", 4);
            let a = f.op("bvand", &[a, b], 4);
            let left = f.op("bvadd", &[a, b], 4);
            let right = f.op("bvadd", &[b, a], 4);
            let equality = f.equals(left, right);
            f.not(equality)
        }),
        ("and", "bitblast_and", |f| {
            let a = f.bv("a", 4);
            let left = f.op("bvand", &[a, a], 4);
            let equality = f.equals(left, a);
            f.not(equality)
        }),
        ("or", "bitblast_or", |f| {
            let a = f.bv("a", 4);
            let left = f.op("bvor", &[a, a], 4);
            let equality = f.equals(left, a);
            f.not(equality)
        }),
        ("xor", "bitblast_xor", |f| {
            let a = f.bv("a", 4);
            let b = f.bv("b", 4);
            let left = f.op("bvxor", &[a, b], 4);
            let right = f.op("bvxor", &[b, a], 4);
            let equality = f.equals(left, right);
            f.not(equality)
        }),
        ("not", "bitblast_not", |f| {
            let a = f.bv("a", 4);
            let left = f.op("bvnot", &[a], 4);
            let right = f.op("bvnot", &[a], 4);
            let equality = f.equals(left, right);
            f.not(equality)
        }),
        ("neg", "bitblast_neg", |f| {
            let a = f.bv("a", 4);
            let a = f.op("bvand", &[a, a], 4);
            let left = f.op("bvneg", &[a], 4);
            let right = f.op("bvneg", &[a], 4);
            let equality = f.equals(left, right);
            f.not(equality)
        }),
        ("concat", "bitblast_concat", |f| {
            let a = f.bv("a", 4);
            let b = f.bv("b", 4);
            let joined = f.op("concat", &[a, b], 8);
            let low = f.indexed("extract", vec![3, 0], joined, 4);
            let equality = f.equals(low, b);
            f.not(equality)
        }),
        ("extract", "bitblast_extract", |f| {
            let a = f.bv("a", 8);
            let low = f.indexed("extract", vec![3, 0], a, 4);
            let again = f.indexed("extract", vec![3, 0], a, 4);
            let equality = f.equals(low, again);
            f.not(equality)
        }),
        ("sign_extend", "bitblast_sign_extend", |f| {
            let a = f.bv("a", 4);
            let wide = f.indexed("sign_extend", vec![4], a, 8);
            let narrow = f.indexed("extract", vec![3, 0], wide, 4);
            let equality = f.equals(narrow, a);
            f.not(equality)
        }),
        ("zero_extend", "bitblast_concat", |f| {
            let a = f.bv("a", 4);
            let wide = f.indexed("zero_extend", vec![4], a, 8);
            let narrow = f.indexed("extract", vec![3, 0], wide, 4);
            let equality = f.equals(narrow, a);
            f.not(equality)
        }),
        ("shl", "bitblast_shl", |f| {
            let a = f.bv("a", 4);
            let b = f.bv("b", 4);
            let left = f.op("bvshl", &[a, b], 4);
            let right = f.op("bvshl", &[a, b], 4);
            let equality = f.equals(left, right);
            f.not(equality)
        }),
        ("lshr", "bitblast_lshr", |f| {
            let a = f.bv("a", 4);
            let b = f.bv("b", 4);
            let left = f.op("bvlshr", &[a, b], 4);
            let right = f.op("bvlshr", &[a, b], 4);
            let equality = f.equals(left, right);
            f.not(equality)
        }),
        // A CONSTANT shift amount: a symbolic one over a possibly-negative
        // operand lies outside the domain where the pinned zero fill is true;
        // see `an_arithmetic_shift_outside_the_consumer_domain_fails_closed`.
        ("ashr", "bitblast_ashr", |f| {
            let a = f.bv("a", 4);
            let two = f.constant(2, 4);
            let left = f.op("bvashr", &[a, two], 4);
            let right = f.op("bvashr", &[a, two], 4);
            let equality = f.equals(left, right);
            f.not(equality)
        }),
        ("ult", "bitblast_ult", |f| {
            let a = f.bv("a", 4);
            let b = f.bv("b", 4);
            let left = f.predicate("bvult", a, b);
            let right = f.predicate("bvult", b, a);
            f.terms
                .mk_app(Symbol::named("and"), [left, right], Sort::Bool)
        }),
        ("mult", "bitblast_mult", |f| {
            let a = f.bv("a", 4);
            let b = f.bv("b", 4);
            let left = f.op("bvmul", &[a, b], 4);
            let right = f.op("bvmul", &[b, a], 4);
            let equality = f.equals(left, right);
            f.not(equality)
        }),
        // `bvsub` has no bit-blasting rule: it is re-spelled through the
        // checker's own bit-vector polynomial normalizer.
        ("sub", "poly_simp", |f| {
            let a = f.bv("a", 4);
            let b = f.bv("b", 4);
            let difference = f.op("bvsub", &[a, b], 4);
            let negated = f.op("bvneg", &[b], 4);
            let sum = f.op("bvadd", &[a, negated], 4);
            let equality = f.equals(difference, sum);
            f.not(equality)
        }),
        // A power-of-two multiplication takes the same route.
        ("mul_pow2", "poly_simp", |f| {
            let a = f.bv("a", 4);
            let four = f.constant(4, 4);
            let two = f.constant(2, 4);
            let product = f.op("bvmul", &[a, four], 4);
            let shifted = f.op("bvshl", &[a, two], 4);
            let equality = f.equals(product, shifted);
            f.not(equality)
        }),
        // A bit-vector `ite` has no rule at all; its semantics are derived.
        ("bv_ite", "ite_intro", |f| {
            let a = f.bv("a", 4);
            let b = f.bv("b", 4);
            let p = f.boolean("p");
            let left = f.terms.mk_ite_raw(p, a, b);
            let right = f.terms.mk_ite_raw(p, a, b);
            let equality = f.equals(left, right);
            f.not(equality)
        }),
    ];

    for (family, rule, build) in cases {
        let mut f = Fixture::new();
        let assertion = build(&mut f);
        let document = f
            .refute(assertion)
            .unwrap_or_else(|| panic!("{family} must render a complete refutation"));
        assert_complete(&document);
        assert!(
            document.contains(&format!(":rule {rule}")),
            "{family} must reach {rule}:\n{}",
            &document[..document.len().min(4000)]
        );
    }
}

#[test]
fn a_satisfiable_lemma_is_refused_rather_than_printed() {
    // `(bvadd a b)` and `(bvsub a b)` differ for almost every assignment, so
    // the "lemma" is false. Nothing may be emitted.
    let mut f = Fixture::new();
    let a = f.bv("a", 4);
    let b = f.bv("b", 4);
    let left = f.op("bvadd", &[a, b], 4);
    let right = f.op("bvsub", &[a, b], 4);
    let equality = f.equals(left, right);
    let assertion = f.not(equality);
    assert!(
        f.refute(assertion).is_none(),
        "a false lemma must never produce an accepted document"
    );
}

#[test]
fn unsigned_division_renders_through_the_checkers_divider() {
    // `bvudiv` / `bvurem` blast through the pinned checker's own long-division
    // circuit (clean `5390f432b8`): a power-of-two divisor against its shift
    // and mask is refuted without a hole.
    for (head, rule, other) in [
        ("bvudiv", "bitblast_udiv", "bvlshr"),
        ("bvurem", "bitblast_urem", "bvand"),
    ] {
        let mut f = Fixture::new();
        let x = f.bv("x", 8);
        let four = f.constant(4, 8);
        let divided = f.op(head, &[x, four], 8);
        let operand = if head == "bvudiv" {
            f.constant(2, 8)
        } else {
            f.constant(3, 8)
        };
        let reference = f.op(other, &[x, operand], 8);
        let equality = f.equals(divided, reference);
        let assertion = f.not(equality);
        let document = f
            .refute(assertion)
            .unwrap_or_else(|| panic!("{head} by a power of two must render"));
        assert_complete(&document);
        assert!(
            document.contains(&format!(":rule {rule}")),
            "{head} needs {rule}"
        );
    }
}

#[test]
fn an_uninterpreted_operator_is_an_opaque_word() {
    // `bvsdiv` has no bit-blasting rule here. The SAME term on both sides is
    // an opaque word whose bits `bitblast_var` projects, so the structural
    // identity still renders ...
    let mut f = Fixture::new();
    let a = f.bv("a", 4);
    let b = f.bv("b", 4);
    let quotient = f.op("bvsdiv", &[a, b], 4);
    let again = f.op("bvsdiv", &[a, b], 4);
    let equality = f.equals(quotient, again);
    let assertion = f.not(equality);
    let document = f
        .refute(assertion)
        .expect("an opaque word refutes structurally");
    assert_complete(&document);
    assert!(document.contains(":rule bitblast_var"));

    // ... while a lemma that needs the operator's MEANING is satisfiable over
    // the opaque bits and is declined, never printed.
    let mut f = Fixture::new();
    let a = f.bv("a", 4);
    let one = f.constant(1, 4);
    let quotient = f.op("bvsdiv", &[a, one], 4);
    let equality = f.equals(quotient, a);
    let assertion = f.not(equality);
    assert!(
        f.refute(assertion).is_none(),
        "an opaque word cannot prove what only the operator's semantics decides"
    );
}

/// The divider's MEANING, checked exhaustively at 8 bits by evaluating the
/// gate DAG: quotient and remainder for every dividend and divisor, with
/// SMT-LIB's zero-divisor results (all ones, and the dividend).
#[test]
fn the_divider_circuit_computes_unsigned_quotient_and_remainder() {
    fn value(circuit: &Circuit, r: SRef, inputs: &[bool], memo: &mut Vec<Option<bool>>) -> bool {
        let gate = r.gate as usize;
        let base = match memo[gate] {
            Some(v) => v,
            None => {
                let v = match circuit.kind(r.gate).clone() {
                    circuit::GateKind::Const(v) => v,
                    circuit::GateKind::Atom(name) => {
                        let index: usize = name[1..].parse().expect("atom index");
                        inputs[index]
                    }
                    circuit::GateKind::And(args) => {
                        args.iter().all(|a| value(circuit, *a, inputs, memo))
                    }
                    circuit::GateKind::Or(args) => {
                        args.iter().any(|a| value(circuit, *a, inputs, memo))
                    }
                    circuit::GateKind::Xor(a, b) => {
                        value(circuit, a, inputs, memo) != value(circuit, b, inputs, memo)
                    }
                    circuit::GateKind::Implies(a, b) => {
                        !value(circuit, a, inputs, memo) || value(circuit, b, inputs, memo)
                    }
                    circuit::GateKind::Iff(a, b) => {
                        value(circuit, a, inputs, memo) == value(circuit, b, inputs, memo)
                    }
                    circuit::GateKind::Ite(c, a, b) => {
                        if value(circuit, c, inputs, memo) {
                            value(circuit, a, inputs, memo)
                        } else {
                            value(circuit, b, inputs, memo)
                        }
                    }
                    circuit::GateKind::Theory(_) => unreachable!("no theory atoms here"),
                };
                memo[gate] = Some(v);
                v
            }
        };
        base != r.negative()
    }

    let mut circuit = Circuit::new("t.".to_string());
    // Atoms `x0..x7` are dividend bits 0..7, `x8..x15` divisor bits 0..7.
    let x: Vec<SRef> = (0..8).map(|i| circuit.atom(format!("x{i}"))).collect();
    let y: Vec<SRef> = (8..16).map(|i| circuit.atom(format!("x{i}"))).collect();
    let (quot, rem) = circuit
        .udiv_urem_spelled(&x, &y, circuit::Divider::Clean)
        .expect("8-bit divider");
    for dividend in 0u32..256 {
        for divisor in 0u32..256 {
            let inputs: Vec<bool> = (0..16)
                .map(|i| {
                    if i < 8 {
                        dividend >> i & 1 == 1
                    } else {
                        divisor >> (i - 8) & 1 == 1
                    }
                })
                .collect();
            let mut memo = vec![None; circuit.len()];
            let read = |bits: &[SRef], memo: &mut Vec<Option<bool>>| {
                bits.iter().enumerate().fold(0u32, |acc, (i, bit)| {
                    acc | u32::from(value(&circuit, *bit, &inputs, memo)) << i
                })
            };
            let (want_q, want_r) = if divisor == 0 {
                (255, dividend)
            } else {
                (dividend / divisor, dividend % divisor)
            };
            assert_eq!(read(&quot, &mut memo), want_q, "{dividend} / {divisor}");
            assert_eq!(read(&rem, &mut memo), want_r, "{dividend} % {divisor}");
        }
    }
}

#[test]
fn an_over_wide_word_fails_closed() {
    let mut f = Fixture::new();
    let a = f.bv("a", MAX_WIDTH + 1);
    let b = f.bv("b", MAX_WIDTH + 1);
    let equality = f.equals(a, b);
    let assertion = f.not(equality);
    assert!(f.refute(assertion).is_none());
}

#[test]
fn a_non_bitvector_lemma_is_declined() {
    let mut f = Fixture::new();
    let p = f.boolean("p");
    let q = f.boolean("q");
    // Purely propositional, with no bit-vector atom to blast: the lowering
    // still declines rather than inventing a bit-level derivation.
    let conjunction = f.terms.mk_app(Symbol::named("and"), [p, q], Sort::Bool);
    let negated = f.not(conjunction);
    let assertion = f
        .terms
        .mk_app(Symbol::named("and"), [conjunction, negated], Sort::Bool);
    // This one IS refutable propositionally, so it may render; what must never
    // happen is a hole.
    if let Some(document) = f.refute(assertion) {
        assert_complete(&document);
    }
}

#[test]
fn a_bitvector_ite_word_defines_its_condition_gate_first() {
    // The word `(ite g a b)` names a GATE in its body while a bit atom of the
    // same word names the WORD, so the two definition tables interleave. This
    // is the shape that produced a parse-time forward reference.
    let mut f = Fixture::new();
    let a = f.bv("a", 4);
    let b = f.bv("b", 4);
    let c = f.bv("c", 4);
    let guard = f.predicate("bvult", a, b);
    let selected = f.terms.mk_ite_raw(guard, a, c);
    let again = f.terms.mk_ite_raw(guard, a, c);
    let equality = f.equals(selected, again);
    let assertion = f.not(equality);
    let document = f.refute(assertion).expect("refutable");
    assert_complete(&document);
    assert!(document.contains("(define-fun"));
}

#[test]
fn sixty_four_bit_shifts_and_products_render() {
    // Width 64 is the corpus width, and it is where a 32-bit shift in the
    // width-constant derivation overflowed. Exercise every width-sensitive
    // family there.
    for (family, rule, build) in [
        ("shl64", "bitblast_shl", 0_u8),
        ("lshr64", "bitblast_lshr", 1),
        ("mul64", "poly_simp", 2),
    ] {
        let _ = build;
        let mut f = Fixture::new();
        let a = f.bv("a", 64);
        let b = f.bv("b", 64);
        let assertion = match family {
            "shl64" => {
                let left = f.op("bvshl", &[a, b], 64);
                let right = f.op("bvshl", &[a, b], 64);
                let equality = f.equals(left, right);
                f.not(equality)
            }
            "lshr64" => {
                let left = f.op("bvlshr", &[a, b], 64);
                let right = f.op("bvlshr", &[a, b], 64);
                let equality = f.equals(left, right);
                f.not(equality)
            }
            _ => {
                let four = f.constant(4, 64);
                let left = f.op("bvmul", &[a, four], 64);
                let right = f.op("bvmul", &[a, four], 64);
                let equality = f.equals(left, right);
                f.not(equality)
            }
        };
        let document = f
            .refute(assertion)
            .unwrap_or_else(|| panic!("{family} must render at width 64"));
        assert_complete(&document);
        assert!(
            document.contains(&format!(":rule {rule}")),
            "{family} needs {rule}"
        );
    }
}

#[test]
fn a_large_power_of_two_product_renders_one_monomial_per_doubling() {
    // `x * 2^32` at 64 bits: past the old 16-doubling cap. Every running
    // product is named `(bvmul 2^i x)`, so each `poly_simp` step is one
    // monomial to the checker and the chain may be as long as the width.
    let mut f = Fixture::new();
    let x = f.bv("x", 64);
    let big = f.terms.mk_bitvec(BigInt::from(1u64 << 32), 64);
    let product = f.op("bvmul", &[x, big], 64);
    let thirty_two = f.constant(32, 64);
    let shifted = f.op("bvshl", &[x, thirty_two], 64);
    let equality = f.equals(product, shifted);
    let assertion = f.not(equality);
    let document = f.refute(assertion).expect("x * 2^32 = x << 32 renders");
    assert_complete(&document);
    assert!(document.contains(":rule poly_simp"));
    assert!(
        document.contains("(bvmul (_ bv2147483648 64) "),
        "the last named running product"
    );
    // Multiplication by one is a single `poly_simp` step onto `x` itself.
    let mut f = Fixture::new();
    let x = f.bv("x", 8);
    let one = f.constant(1, 8);
    let product = f.op("bvmul", &[one, x], 8);
    let equality = f.equals(product, x);
    let assertion = f.not(equality);
    let document = f.refute(assertion).expect("1 * x = x renders");
    assert_complete(&document);
}

#[test]
fn an_arithmetic_shift_outside_the_consumer_domain_fails_closed() {
    // A symbolic shift amount over a possibly-negative operand is outside the
    // domain where the pinned zero-filled circuit is true, and pinned Carcara
    // would accept that false conclusion, so the guard is load-bearing. It is
    // never spelled `bitblast_ashr`: the word becomes OPAQUE (`bitblast_var`),
    // which still refutes a structural identity over it without the rule ...
    let mut f = Fixture::new();
    let a = f.bv("a", 8);
    let b = f.bv("b", 8);
    let left = f.op("bvashr", &[a, b], 8);
    let right = f.op("bvashr", &[a, b], 8);
    let equality = f.equals(left, right);
    let assertion = f.not(equality);
    let document = f
        .refute(assertion)
        .expect("an opaque word refutes structurally");
    assert_complete(&document);
    assert!(!document.contains(":rule bitblast_ashr"));

    // ... and a lemma that needs the shift's MEANING at such an instance is
    // declined, never printed.
    let mut f = Fixture::new();
    let a = f.bv("a", 8);
    let b = f.bv("b", 8);
    let shifted = f.op("bvashr", &[a, b], 8);
    let equality = f.equals(shifted, a);
    let assertion = f.not(equality);
    assert!(f.refute(assertion).is_none());

    // A constant amount below the width is admissible and must still render,
    // with Clean's sign fill by default (`AletheDialect`); no amount reaches it.
    let mut f = Fixture::new();
    let a = f.bv("a", 8);
    let two = f.constant(2, 8);
    let left = f.op("bvashr", &[a, two], 8);
    let right = f.op("bvashr", &[a, two], 8);
    let equality = f.equals(left, right);
    let assertion = f.not(equality);
    let document = f.refute(assertion).expect("a bounded shift renders");
    assert_complete(&document);
    assert!(document.contains(":rule bitblast_ashr"));
}

/// Every transported step must be one the consumer REPLAYS, never one it has
/// to search for: a binary resolution, or an n-ary one carrying an explicit
/// pivot and polarity for every link.
///
/// The defect this guards is the ORIGINAL transport, which printed one n-ary
/// step per derived clause and left the consumer to reconstruct the chain from
/// a RUP hint list. A hint list is not always reconstructible: the pinned
/// checker answered `rule validation failed` — nondeterministically — on a
/// document AY had already disclosed as hole-free. `:args` carries the chain
/// explicitly, so there is nothing left to guess; the binary form remains for
/// the clauses whose printed negations only the parity path reads as this
/// transport does.
#[test]
fn every_transported_step_carries_the_pivots_it_is_checked_on() {
    let mut f = Fixture::new();
    let a = f.bv("a", 8);
    let b = f.bv("b", 8);
    let left = f.op("bvadd", &[a, b], 8);
    let right = f.op("bvadd", &[b, a], 8);
    let equality = f.equals(left, right);
    let assertion = f.not(equality);
    let document = f.refute(assertion).expect("the lemma is refutable");
    assert_complete(&document);

    let mut resolutions = 0_usize;
    let mut with_pivots = 0_usize;
    for line in document.lines() {
        if !line.contains(":rule resolution") {
            continue;
        }
        resolutions += 1;
        let premises = line
            .split(":premises (")
            .nth(1)
            .and_then(|rest| rest.split(')').next())
            .unwrap_or_else(|| panic!("a resolution step names its premises:\n{line}"))
            .split_whitespace()
            .count();
        let Some(at) = line.find(":args (") else {
            assert_eq!(
                premises, 2,
                "a step carrying no pivots must be a binary resolution:\n{line}"
            );
            continue;
        };
        with_pivots += 1;
        // A pivot may be a compound term containing spaces, so the argument
        // list is split on balanced parentheses, never on whitespace.
        let group = selfcheck::balanced(&line[at + ":args ".len()..])
            .unwrap_or_else(|| panic!("the :args list must be balanced:\n{line}"));
        let args = selfcheck::tokens(&group[1..group.len() - 1])
            .unwrap_or_else(|| panic!("the :args list must parse:\n{line}"));
        assert!(premises >= 2, "an n-ary step needs two premises:\n{line}");
        assert_eq!(
            args.len(),
            (premises - 1) * 2,
            "one pivot and one polarity per link:\n{line}"
        );
    }
    assert!(resolutions > 0, "the refutation must be transported");
    assert!(
        with_pivots > 0,
        "the chain must reach the consumer as n-ary steps carrying their pivots"
    );
}

/// The document is replayed from its own printed text before it is disclosed,
/// and the replay is decisive: corrupt any transported clause and it fails.
#[test]
fn the_printed_chain_is_replayed_before_it_is_disclosed() {
    let mut f = Fixture::new();
    let a = f.bv("a", 4);
    let b = f.bv("b", 4);
    let left = f.op("bvadd", &[a, b], 4);
    let right = f.op("bvadd", &[b, a], 4);
    let equality = f.equals(left, right);
    let assertion = f.not(equality);
    let document = f.refute(assertion).expect("the lemma is refutable");

    // The final step prints the WORD-level lemma clause, so the replay is
    // handed the circuit-level spelling of the same literal; recover it from
    // the step that concludes it.
    let chain: Vec<&str> = document
        .lines()
        .filter(|line| line.contains(":rule resolution"))
        .collect();
    let last = chain.last().expect("a transported chain");
    assert!(
        last.starts_with("(step t1 "),
        "the lemma step is last:\n{last}"
    );

    // Widening any transported clause by a literal it does not contain breaks
    // the replay, which is what keeps a disclosed certificate honest.
    let widened = document.replacen(".cbbr1 (cl", ".cbbr1 (cl (not true)", 1);
    assert_ne!(widened, document, "the chain must name its steps `cbbr`");
    assert!(
        !selfcheck::chain_replays(&widened, "t1", "(cl)"),
        "a widened transported clause must fail the replay"
    );
}

/// Count the printed steps of `document` that use `rule`.
fn rule_count(document: &str, rule: &str) -> usize {
    document
        .lines()
        .filter(|line| line.contains(&format!(":rule {rule}")) && line.starts_with("(step "))
        .count()
}

/// REGRESSION (external-codegen `StrengthReduce: x * 4 == x << 2`, and the
/// `MUL #4 ≡ LSL #2` peephole): a power-of-two product against the shift it
/// reduces to, at 64 bits. Its and_neg/or_neg input clauses print literals
/// under two `not`s, which the consumer's `:args` path reads differently, so
/// every chain through one used to be printed as binary steps with every
/// intermediate resolvent: 537 RUP steps became 51,045 printed resolutions,
/// the document crossed `MAX_TEXT_BYTES`, and the lemma kept its `hole`.
/// `normalize` re-derives each such input clause once (a parity-path
/// resolution against `not_not`, then `contraction`), so the chains are
/// `:args` steps.
#[test]
fn a_power_of_two_product_against_its_shift_renders_at_sixty_four_bits() {
    let mut f = Fixture::new();
    let x = f.bv("x", 64);
    let four = f.constant(4, 64);
    let two = f.constant(2, 64);
    let product = f.op("bvmul", &[four, x], 64);
    let shifted = f.op("bvshl", &[x, two], 64);
    let equality = f.equals(product, shifted);
    let assertion = f.not(equality);
    let document = f
        .refute(assertion)
        .expect("x * 4 == x << 2 must render at width 64");
    assert_complete(&document);
    assert!(
        document.len() < MAX_TEXT_BYTES / 4,
        "the normalized document is far inside the budget: {} bytes",
        document.len()
    );
    assert!(
        rule_count(&document, "not_not") > 0,
        "doubled negations are re-derived"
    );
    // Each normalized clause's LAST step (`.cbbn{index}.c`, else the
    // `.cbbn{index}.{n}` with the largest `n`; a `…t` name is the `not_not`
    // tautology) concludes the copy the chains use: every literal under at
    // most one `not`, none printed twice.
    let mut last: std::collections::BTreeMap<&str, (u32, &str)> = Default::default();
    for line in document.lines() {
        let Some(name) = line
            .strip_prefix("(step ")
            .and_then(|rest| rest.split_once(' '))
            .map(|(name, _)| name)
        else {
            continue;
        };
        let Some((clause, step)) = name
            .split_once(".cbbn")
            .and_then(|(_, suffix)| suffix.split_once('.'))
        else {
            continue;
        };
        let order = match step {
            "c" => u32::MAX,
            _ if step.ends_with('t') => continue,
            _ => step.parse().expect("a numbered normalization step"),
        };
        let entry = last.entry(clause).or_insert((order, line));
        if order >= entry.0 {
            *entry = (order, line);
        }
    }
    assert!(!last.is_empty(), "input clauses are normalized");
    for (_, line) in last.values() {
        let clause = line
            .split_once(" (cl ")
            .and_then(|(_, rest)| rest.split_once(" :rule "))
            .map(|(clause, _)| clause.strip_suffix(')').expect("a closed clause"))
            .expect("a step prints its clause");
        let literals = selfcheck::tokens(clause).expect("a well-formed clause");
        let mut seen = std::collections::BTreeSet::new();
        for literal in &literals {
            assert!(!literal.starts_with("(not (not "), "a deep literal: {line}");
            assert!(seen.insert(*literal), "{literal} repeats: {line}");
        }
    }
    // The chains reach the consumer as `:args` steps, not as binary runs.
    let resolutions = rule_count(&document, "resolution");
    let with_pivots = document
        .lines()
        .filter(|line| line.contains(":rule resolution") && line.contains(":args ("))
        .count();
    assert!(
        with_pivots * 2 > resolutions,
        "{with_pivots} of {resolutions} resolutions carry pivots"
    );
}
