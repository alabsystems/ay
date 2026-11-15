// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use ay_core::{Proof, ProofStep, TheoryLemmaKind};
use num_bigint::BigInt;

use super::*;

mod ownership;
mod refusal;
mod signed_normalization;

struct Fixture {
    terms: TermStore,
    fields: Fields,
    value: TermId,
}

impl Fixture {
    fn new(eb: u32, sb: u32) -> Self {
        let mut terms = TermStore::new();
        let sign = terms.mk_var("source_sign", Sort::bitvec(1));
        let exponent = terms.mk_var("source_exponent", Sort::bitvec(eb));
        let fraction = terms.mk_var("source_fraction", Sort::bitvec(sb - 1));
        let fields = Fields {
            sign,
            exponent,
            fraction,
            eb,
            sb,
        };
        let value = terms.mk_app(
            Symbol::named("fp"),
            [sign, exponent, fraction],
            Sort::FloatingPoint(eb, sb),
        );
        Self {
            terms,
            fields,
            value,
        }
    }

    fn app(&mut self, name: &str, args: &[TermId], sort: Sort) -> TermId {
        self.terms.mk_app(Symbol::named(name), args, sort)
    }

    fn eq(&mut self, left: TermId, right: TermId) -> TermId {
        self.app("=", &[left, right], Sort::Bool)
    }

    fn and(&mut self, left: TermId, right: TermId) -> TermId {
        self.app("and", &[left, right], Sort::Bool)
    }

    fn test_field(
        &mut self,
        field: TermId,
        width: u32,
        pattern: WordConstant,
        sense: EqualitySense,
    ) -> TermId {
        let value = if matches!(pattern, WordConstant::Ones) {
            (BigInt::from(1u8) << width) - 1u8
        } else {
            BigInt::from(0u8)
        };
        let constant = self.terms.mk_bitvec(value, width);
        let equality = self.eq(field, constant);
        if matches!(sense, EqualitySense::Different) {
            self.terms.mk_not(equality)
        } else {
            equality
        }
    }

    fn predicate(&mut self, op: FpOp) -> TermId {
        let f = self.fields;
        let (left, right) = match op {
            FpOp::IsNaN => (
                self.test_field(f.exponent, f.eb, WordConstant::Ones, EqualitySense::Equal),
                self.test_field(
                    f.fraction,
                    f.sb - 1,
                    WordConstant::Zero,
                    EqualitySense::Different,
                ),
            ),
            FpOp::IsInfinite => (
                self.test_field(f.exponent, f.eb, WordConstant::Ones, EqualitySense::Equal),
                self.test_field(
                    f.fraction,
                    f.sb - 1,
                    WordConstant::Zero,
                    EqualitySense::Equal,
                ),
            ),
            FpOp::IsZero => (
                self.test_field(f.exponent, f.eb, WordConstant::Zero, EqualitySense::Equal),
                self.test_field(
                    f.fraction,
                    f.sb - 1,
                    WordConstant::Zero,
                    EqualitySense::Equal,
                ),
            ),
            FpOp::IsNormal => (
                self.test_field(
                    f.exponent,
                    f.eb,
                    WordConstant::Zero,
                    EqualitySense::Different,
                ),
                self.test_field(
                    f.exponent,
                    f.eb,
                    WordConstant::Ones,
                    EqualitySense::Different,
                ),
            ),
            FpOp::IsSubnormal => (
                self.test_field(f.exponent, f.eb, WordConstant::Zero, EqualitySense::Equal),
                self.test_field(
                    f.fraction,
                    f.sb - 1,
                    WordConstant::Zero,
                    EqualitySense::Different,
                ),
            ),
            FpOp::IsPositive | FpOp::IsNegative => {
                let nan = self.predicate(FpOp::IsNaN);
                (
                    self.terms.mk_not(nan),
                    self.test_field(
                        f.sign,
                        1,
                        if op == FpOp::IsNegative {
                            WordConstant::Ones
                        } else {
                            WordConstant::Zero
                        },
                        EqualitySense::Equal,
                    ),
                )
            }
            _ => panic!("fixture requires a classification"),
        };
        self.and(left, right)
    }

    fn theorem(&mut self, op: FpOp) -> TermId {
        let f = self.fields;
        let name = match op {
            FpOp::IsNaN => "fp.isNaN",
            FpOp::IsInfinite => "fp.isInfinite",
            FpOp::IsZero => "fp.isZero",
            FpOp::IsNormal => "fp.isNormal",
            FpOp::IsSubnormal => "fp.isSubnormal",
            FpOp::IsPositive => "fp.isPositive",
            FpOp::IsNegative => "fp.isNegative",
            FpOp::Neg => "fp.neg",
            FpOp::Abs => "fp.abs",
            _ => panic!("fixture operation unsupported"),
        };
        let unary = matches!(op, FpOp::Neg | FpOp::Abs);
        let sort = if unary {
            Sort::FloatingPoint(f.eb, f.sb)
        } else {
            Sort::Bool
        };
        let source = self.app(name, &[self.value], sort.clone());
        let lowered = if unary {
            let sign = if op == FpOp::Neg {
                self.app("bvnot", &[f.sign], Sort::bitvec(1))
            } else {
                self.terms.mk_bitvec(BigInt::from(0u8), 1)
            };
            self.app("fp", &[sign, f.exponent, f.fraction], sort)
        } else {
            self.predicate(op)
        };
        self.eq(source, lowered)
    }

    fn validate(&self, theorem: TermId, op: FpOp) -> Result<(), ProofCheckError> {
        super::super::validate_fp_to_bv(&self.terms, ProofId(0), &[theorem], op, &mut |_, _| true)
    }
}

fn accepts_symbolic(op: FpOp) {
    for (eb, sb) in [(2, 2), (5, 11), (8, 24), (11, 53), (15, 113)] {
        let mut fixture = Fixture::new(eb, sb);
        let theorem = fixture.theorem(op);
        fixture
            .validate(theorem, op)
            .expect("whole symbolic schema is valid at every admitted format");
    }
}

#[test]
fn fp_namespace_registered_constructor_is_not_an_ieee_lowering() {
    for name in ["fp", "fp.isNaN", "and", "="] {
        let mut fixture = Fixture::new(8, 24);
        let theorem = fixture.theorem(FpOp::IsNaN);
        fixture.validate(theorem, FpOp::IsNaN).unwrap();
        fixture.terms.register_declared_function(name);
        assert!(fixture.validate(theorem, FpOp::IsNaN).is_err(), "{name}");
    }
}

#[test]
fn symbolic_nan_complete_lowering() {
    accepts_symbolic(FpOp::IsNaN);
}
#[test]
fn symbolic_infinity_complete_lowering() {
    accepts_symbolic(FpOp::IsInfinite);
}
#[test]
fn symbolic_zero_complete_lowering() {
    accepts_symbolic(FpOp::IsZero);
}
#[test]
fn symbolic_normal_complete_lowering() {
    accepts_symbolic(FpOp::IsNormal);
}
#[test]
fn symbolic_subnormal_complete_lowering() {
    accepts_symbolic(FpOp::IsSubnormal);
}
#[test]
fn symbolic_positive_excludes_nan() {
    accepts_symbolic(FpOp::IsPositive);
}
#[test]
fn symbolic_negative_excludes_nan() {
    accepts_symbolic(FpOp::IsNegative);
}
#[test]
fn symbolic_negation_preserves_exponent_fraction() {
    accepts_symbolic(FpOp::Neg);
}
#[test]
fn symbolic_absolute_preserves_exponent_fraction() {
    accepts_symbolic(FpOp::Abs);
}

#[test]
fn actual_strict_proof_route_rechecks_whole_symbolic_clause() {
    let mut fixture = Fixture::new(11, 53);
    let theorem = fixture.theorem(FpOp::IsNaN);
    let negated = fixture.terms.mk_not(theorem);
    let mut proof = Proof::new();
    let premise = proof.add_assume(negated, None);
    let axiom = proof.add_theory_lemma_with_kind(
        "FP",
        vec![theorem],
        TheoryLemmaKind::FpToBv {
            operation: FpOp::IsNaN,
        },
    );
    proof.add_step(ProofStep::Resolution {
        clause: vec![],
        pivot: theorem,
        clause1: axiom,
        clause2: premise,
    });
    crate::check_proof_strict(&proof, &fixture.terms)
        .expect("strict dispatcher accepts only the actual symbolic axiom");
}

#[test]
fn equality_orientation_and_wide_exponent_have_no_enumeration_ceiling() {
    let mut fixture = Fixture::new(8320, 24);
    let theorem = fixture.theorem(FpOp::IsNaN);
    let TermData::App(_, args) = fixture.terms.get(theorem) else {
        panic!("fixture equality");
    };
    let [left, right] = args.as_slice() else {
        panic!("fixture equality arity");
    };
    let reversed = fixture.eq(*right, *left);
    fixture
        .validate(reversed, FpOp::IsNaN)
        .expect("exact borrowed all-ones walk has no guessed format ceiling");
}
