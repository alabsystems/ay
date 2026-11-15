// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Exact-rational regression and COMPLETE symbolic source-schema controls.
//! Finite evaluation is never production theorem authority.

use super::word_certificate::{app, CertificateFixture};
use super::*;

mod arithmetic;
mod ownership;
mod signatures;
mod wide;
mod word;

struct SumFixture {
    fixture: Fixture,
    operation: Arithmetic,
}

impl SumFixture {
    fn new(eb: u32, p: u32, operation: Arithmetic) -> Self {
        assert!(matches!(operation, Arithmetic::Add | Arithmetic::Sub));
        let mut fixture = Fixture::new(eb, p);
        let TermData::App(_, args) = fixture.terms.get(fixture.source) else {
            panic!("original source");
        };
        let args = args.clone();
        fixture.source = app(
            &mut fixture.terms,
            operation.name(),
            &args,
            Sort::FloatingPoint(eb, p),
        );
        Self { fixture, operation }
    }

    fn evaluate(&self, x: Raw, y: Raw, mode: u64) -> Raw {
        let mut progress = |_, _| true;
        let mut reference = Reference::build_operation(
            &self.fixture.terms,
            self.fixture.source,
            self.operation,
            &mut progress,
        )
        .expect("actual complete sum source");
        let (value, domain) = reference
            .evaluate(&self.fixture.assignments(x, y, mode))
            .expect("same original owner");
        assert!(domain);
        value
    }

    fn compare(&self, x: Raw, y: Raw) {
        let mut progress = |_, _| true;
        let mut reference = Reference::build_operation(
            &self.fixture.terms,
            self.fixture.source,
            self.operation,
            &mut progress,
        )
        .expect("independent exact sum");
        for mode in 0..5 {
            let (value, domain) = reference
                .evaluate(&self.fixture.assignments(x, y, mode))
                .expect("original owner evaluation");
            assert!(domain);
            assert_eq!(
                value,
                oracle::add_sub(self.fixture.format, x, y, mode, self.operation),
                "{:?}, format {:?}, x{x:?}, y{y:?}, RM{mode}",
                self.operation,
                self.fixture.format
            );
        }
    }

    fn certificate(self) -> CertificateFixture {
        CertificateFixture::from_operation_fixture(self.fixture, self.operation)
    }
}
