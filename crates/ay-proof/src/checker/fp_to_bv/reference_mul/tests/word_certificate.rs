// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! The producer fixture emits the canonical WORD recipe, never a proof permit.
//! Correct rounding is separately checked by the exact-rational controls.
//! Independent replay/source-mutation controls verify complete clause binding.

use super::*;
use ay_core::{FpOp, Proof, ProofId, ProofStep, TheoryLemmaKind};
use graph::{Binary, Node, Operation};

mod mutations;

pub(super) fn app(terms: &mut TermStore, name: &str, args: &[TermId], sort: Sort) -> TermId {
    terms.mk_app(Symbol::named(name), args, sort)
}

fn word(terms: &mut TermStore, value: BigInt, width: u32) -> TermId {
    terms.mk_bitvec(value, width)
}

fn ite(terms: &mut TermStore, test: TermId, yes: TermId, no: TermId, width: u32) -> TermId {
    // Avoid producer-side folding: the proof checker matches complete,
    // typed canonical terms rather than trusting a normalizer.
    assert_eq!(terms.sort(yes), &Sort::bitvec(width), "fixture word width");
    terms.mk_ite_raw(test, yes, no)
}

fn rm_code(terms: &mut TermStore, source: TermId) -> TermId {
    let mut next = word(terms, BigInt::from(4u8), 3);
    for (number, name) in ["RNE", "RNA", "RTP", "RTN"].iter().enumerate().rev() {
        let literal = app(terms, name, &[], Sort::Uninterpreted("RoundingMode".into()));
        let test = app(terms, "=", &[source, literal], Sort::Bool);
        let code = word(terms, BigInt::from(number), 3);
        next = ite(terms, test, code, next, 3);
    }
    next
}

fn emit_binary(
    terms: &mut TermStore,
    operation: Binary,
    a: TermId,
    b: TermId,
    width: u32,
) -> TermId {
    let name = match operation {
        Binary::Add => "bvadd",
        Binary::Sub => "bvsub",
        Binary::Mul => "bvmul",
        Binary::And => "bvand",
        Binary::Or => "bvor",
        Binary::Xor => "bvxor",
        Binary::Eq => "=",
        Binary::Ult => "bvult",
        Binary::Shl => "bvshl",
        Binary::Lshr => "bvlshr",
    };
    let compare = matches!(operation, Binary::Eq | Binary::Ult);
    let sort = if compare {
        Sort::Bool
    } else {
        Sort::bitvec(width)
    };
    let result = app(terms, name, &[a, b], sort);
    if compare {
        let one = word(terms, BigInt::one(), 1);
        let zero = word(terms, BigInt::zero(), 1);
        ite(terms, result, one, zero, 1)
    } else {
        result
    }
}

fn emit(terms: &mut TermStore, nodes: &[Node]) -> Vec<TermId> {
    let mut terms_by_node = Vec::new();
    for node in nodes {
        let sort = Sort::bitvec(node.width);
        let id = match node.operation {
            Operation::Input(source) => {
                if matches!(terms.sort(source), Sort::Uninterpreted(name) if name == "RoundingMode")
                {
                    rm_code(terms, source)
                } else {
                    source
                }
            }
            Operation::Small(value) => word(terms, BigInt::from(value), node.width),
            Operation::Ones => word(terms, (BigInt::one() << node.width) - 1u8, node.width),
            Operation::Not(inner) => app(terms, "bvnot", &[terms_by_node[inner.0]], sort),
            Operation::Resize(inner) => {
                let old = nodes[inner.0].width;
                let symbol = if old < node.width {
                    Symbol::indexed("zero_extend", vec![node.width - old])
                } else {
                    Symbol::indexed("extract", vec![node.width - 1, 0])
                };
                terms.mk_app(symbol, [terms_by_node[inner.0]], sort)
            }
            Operation::Extract(inner, high, low) => terms.mk_app(
                Symbol::indexed("extract", vec![high, low]),
                [terms_by_node[inner.0]],
                sort,
            ),
            Operation::Select(condition, yes, no) => {
                let one = word(terms, BigInt::one(), 1);
                let test = app(terms, "=", &[terms_by_node[condition.0], one], Sort::Bool);
                ite(
                    terms,
                    test,
                    terms_by_node[yes.0],
                    terms_by_node[no.0],
                    node.width,
                )
            }
            Operation::Binary(operation, a, b) => emit_binary(
                terms,
                operation,
                terms_by_node[a.0],
                terms_by_node[b.0],
                node.width,
            ),
        };
        terms_by_node.push(id);
    }
    terms_by_node
}

pub(super) struct CertificateFixture {
    pub(super) fixture: Fixture,
    pub(super) theorem: TermId,
    pub(super) lowered: TermId,
    pub(super) nodes: Vec<Node>,
    pub(super) emitted: Vec<TermId>,
    pub(super) operation: Arithmetic,
}

impl CertificateFixture {
    fn new(eb: u32, p: u32) -> Self {
        Self::from_fixture(Fixture::new(eb, p))
    }

    fn from_fixture(fixture: Fixture) -> Self {
        Self::from_operation_fixture(fixture, Arithmetic::Mul)
    }

    pub(super) fn from_operation_fixture(mut fixture: Fixture, operation: Arithmetic) -> Self {
        let (eb, p) = fixture.format;
        let mut progress = |_, _| true;
        let reference =
            Reference::build_operation(&fixture.terms, fixture.source, operation, &mut progress)
                .expect("reference recipe");
        let nodes = reference.nodes.clone();
        let output = reference.output.expect("complete output");
        drop(reference);
        let emitted = emit(&mut fixture.terms, &nodes);
        let lowered = app(
            &mut fixture.terms,
            "fp",
            &[
                emitted[output.sign.0],
                emitted[output.exponent.0],
                emitted[output.fraction.0],
            ],
            Sort::FloatingPoint(eb, p),
        );
        let theorem = app(
            &mut fixture.terms,
            "=",
            &[fixture.source, lowered],
            Sort::Bool,
        );
        Self {
            fixture,
            theorem,
            lowered,
            nodes,
            emitted,
            operation,
        }
    }

    pub(super) fn accepts(&self) -> bool {
        recognizes_arithmetic(
            &self.fixture.terms,
            &[self.theorem],
            self.operation,
            &mut |_, _| true,
        )
        .expect("original control live")
    }
}

#[test]
fn whole_symbolic_mul_schema_accepts_all_five_modes_and_standard_formats() {
    for (eb, p) in [(2, 2), (5, 11), (8, 24), (11, 53), (15, 113)] {
        assert!(CertificateFixture::new(eb, p).accepts());
    }
}

#[test]
fn literal_rounding_modes_and_long_aliases_bind_the_same_complete_word_recipe() {
    for name in [
        "RNE",
        "RNA",
        "RTP",
        "RTN",
        "RTZ",
        "roundNearestTiesToEven",
        "roundNearestTiesToAway",
        "roundTowardPositive",
        "roundTowardNegative",
        "roundTowardZero",
    ] {
        let mut fixture = Fixture::new(3, 4);
        let literal = app(
            &mut fixture.terms,
            name,
            &[],
            Sort::Uninterpreted("RoundingMode".into()),
        );
        let TermData::App(_, source_args) = fixture.terms.get(fixture.source) else {
            panic!("fixture has the actual fp.mul source");
        };
        let [_, x, y]: [TermId; 3] = source_args
            .as_slice()
            .try_into()
            .expect("actual complete operands");
        fixture.source = app(
            &mut fixture.terms,
            "fp.mul",
            &[literal, x, y],
            Sort::FloatingPoint(3, 4),
        );
        assert!(
            CertificateFixture::from_fixture(fixture).accepts(),
            "actual literal {name}"
        );
    }
}

#[test]
fn actual_strict_proof_dispatcher_accepts_only_the_full_mul_word_recipe() {
    let mut f = CertificateFixture::new(8, 24);
    let negated = f.fixture.terms.mk_not(f.theorem);
    let mut proof = Proof::new();
    let premise = proof.add_assume(negated, None);
    let theorem = proof.add_theory_lemma_with_kind(
        "FP",
        vec![f.theorem],
        TheoryLemmaKind::FpToBv {
            operation: FpOp::Mul,
        },
    );
    proof.add_step(ProofStep::Resolution {
        clause: vec![],
        pivot: f.theorem,
        clause1: theorem,
        clause2: premise,
    });
    crate::check_proof_strict(&proof, &f.fixture.terms)
        .expect("actual independent strict theorem route");
    assert!(super::super::super::validate_fp_to_bv(
        &f.fixture.terms,
        ProofId(0),
        &[f.theorem],
        FpOp::Add,
        &mut |_, _| true
    )
    .is_err());
    // This is an interpreted SMT theorem, not an original Rust/script premise
    // certificate or captured native FP SAT trace.
}

#[test]
fn complete_unit_equality_orientation_is_supported_without_literal_weakening() {
    let mut f = CertificateFixture::new(3, 4);
    let reversed = app(
        &mut f.fixture.terms,
        "=",
        &[f.lowered, f.fixture.source],
        Sort::Bool,
    );
    assert!(recognizes(&f.fixture.terms, &[reversed], &mut |_, _| true).expect("reverse equality"));
    let unrelated = f.fixture.terms.mk_var("unrelated", Sort::Bool);
    assert!(
        !recognizes(&f.fixture.terms, &[f.theorem, unrelated], &mut |_, _| true)
            .expect("no weakening")
    );
    assert!(
        !recognizes(&f.fixture.terms, &[f.fixture.source], &mut |_, _| true)
            .expect("no missing equality")
    );
}
