// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use ay_core::{Constant, Sort, Symbol, TermData};
use num_bigint::{BigInt, BigUint};
use num_traits::{One, ToPrimitive, Zero};

use super::*;

mod addition;
mod arithmetic;
mod evaluate;
mod oracle;
mod ownership;
mod refusal;
mod word_certificate;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct Raw {
    sign: u64,
    exponent: u64,
    fraction: u128,
}

fn raw(sign: u64, exponent: u64, fraction: u128) -> Raw {
    Raw {
        sign,
        exponent,
        fraction,
    }
}

struct Fixture {
    terms: TermStore,
    source: TermId,
    rm: TermId,
    x: Fields,
    y: Fields,
    format: (u32, u32),
}

#[test]
fn fp_namespace_word_reference_requires_interpreted_source_heads() {
    for name in ["fp.mul", "fp"] {
        let mut fixture = Fixture::new(3, 5);
        assert!(Reference::build(&fixture.terms, fixture.source, &mut |_, _| true).is_ok());
        fixture.terms.register_declared_function(name);
        assert!(Reference::build(&fixture.terms, fixture.source, &mut |_, _| true).is_err());
    }
}

impl Fixture {
    fn new(eb: u32, p: u32) -> Self {
        let mut terms = TermStore::new();
        let rm = terms.mk_var("original_rm", Sort::Uninterpreted("RoundingMode".into()));
        let x = Fields {
            sign: terms.mk_var("original_x_sign", Sort::bitvec(1)),
            exponent: terms.mk_var("original_x_exp", Sort::bitvec(eb)),
            fraction: terms.mk_var("original_x_fraction", Sort::bitvec(p - 1)),
        };
        let y = Fields {
            sign: terms.mk_var("original_y_sign", Sort::bitvec(1)),
            exponent: terms.mk_var("original_y_exp", Sort::bitvec(eb)),
            fraction: terms.mk_var("original_y_fraction", Sort::bitvec(p - 1)),
        };
        let sort = Sort::FloatingPoint(eb, p);
        let xt = terms.mk_app(
            Symbol::named("fp"),
            [x.sign, x.exponent, x.fraction],
            sort.clone(),
        );
        let yt = terms.mk_app(
            Symbol::named("fp"),
            [y.sign, y.exponent, y.fraction],
            sort.clone(),
        );
        let source = terms.mk_app(Symbol::named("fp.mul"), [rm, xt, yt], sort);
        Self {
            terms,
            source,
            rm,
            x,
            y,
            format: (eb, p),
        }
    }

    fn assignments(&self, x: Raw, y: Raw, mode: u64) -> Vec<(TermId, BigUint)> {
        [
            (self.rm, BigUint::from(mode)),
            (self.x.sign, BigUint::from(x.sign)),
            (self.x.exponent, BigUint::from(x.exponent)),
            (self.x.fraction, BigUint::from(x.fraction)),
            (self.y.sign, BigUint::from(y.sign)),
            (self.y.exponent, BigUint::from(y.exponent)),
            (self.y.fraction, BigUint::from(y.fraction)),
        ]
        .into_iter()
        .collect()
    }

    fn compare(&self, x: Raw, y: Raw) {
        let mut progress = |_, _| true;
        let mut reference = Reference::build(&self.terms, self.source, &mut progress)
            .expect("actual complete fp.mul has an independent reference");
        for mode in 0..5 {
            let assignment = self.assignments(x, y, mode);
            let (actual, domain) = reference
                .evaluate(&assignment)
                .expect("same-owner model evaluation");
            assert!(domain, "five actual RM values are admitted");
            let expected = oracle::multiply(self.format, x, y, mode);
            assert_eq!(
                actual, expected,
                "format {:?}, x {x:?}, y {y:?}, RM {mode}",
                self.format
            );
        }
    }
}
