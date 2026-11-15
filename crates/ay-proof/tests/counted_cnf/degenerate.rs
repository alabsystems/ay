// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
#![cfg(test)]

use super::*;

#[test]
fn empty_and_unary_connectives_replay_native_rules_from_original_roots() {
    for op in [CountedBuiltin::And, CountedBuiltin::Or] {
        for arity in 0..=1 {
            for input in [false, true] {
                let original = owner();
                let mut terms = TermStore::try_new_with_admission(&original).unwrap();
                // Authored legacy-source fixture, not counted construction:
                // CountedTermBuilder intentionally admits And/Or arity >= 2,
                // while the encoder also accepts these native raw forms.
                let a = terms.mk_var("a", Sort::Bool);
                let args = [a];
                let name = if op == CountedBuiltin::And {
                    "and"
                } else {
                    "or"
                };
                let gate = terms.mk_app(
                    ay_core::Symbol::named(name),
                    args[..arity].to_vec(),
                    Sort::Bool,
                );
                let mut builder = CountedTermBuilder::new(&mut terms, &original).unwrap();
                let value = if arity == 0 {
                    op == CountedBuiltin::And
                } else {
                    input
                };
                let contradiction = if value {
                    builder.apply(CountedBuiltin::Not, &[gate]).unwrap()
                } else {
                    gate
                };
                let assignment = if input {
                    a
                } else {
                    builder.apply(CountedBuiltin::Not, &[a]).unwrap()
                };
                builder.finish().unwrap();
                let cnf = CountedCnf::encode(&mut terms, &[contradiction, assignment], &original)
                    .unwrap();
                let expected = if op == CountedBuiltin::And {
                    AletheRule::AndNeg
                } else {
                    AletheRule::OrPos(0)
                };
                assert!(cnf
                    .steps()
                    .iter()
                    .any(|step| step.rule() == &expected && step.source() == gate));
                let mut native = Native::from_cnf(&cnf);
                native.close_by_units();
                native.require_valid();
                drop(native);
                cnf.finish().unwrap();
                drop(terms);
                original.check().unwrap();
            }
        }
    }
}

#[test]
fn literal_constants_replay_native_rules_without_synthetic_assumptions() {
    for value in [false, true] {
        let original = owner();
        let mut terms = TermStore::try_new_with_admission(&original).unwrap();
        let mut builder = CountedTermBuilder::new(&mut terms, &original).unwrap();
        let constant = builder.boolean(value).unwrap();
        let root = if value {
            builder.apply(CountedBuiltin::Not, &[constant]).unwrap()
        } else {
            constant
        };
        builder.finish().unwrap();
        let cnf = CountedCnf::encode(&mut terms, &[root], &original).unwrap();
        let expected = if value {
            AletheRule::True
        } else {
            AletheRule::False
        };
        assert!(cnf
            .steps()
            .iter()
            .any(|step| step.rule() == &expected && step.source() == constant));
        assert_eq!(cnf.roots(), &[root]);
        let mut native = Native::from_cnf(&cnf);
        assert_eq!(native.assumptions.len(), 1);
        native.close_by_units();
        native.require_valid();
        drop(native);
        cnf.finish().unwrap();
        drop(terms);
        original.check().unwrap();
    }
}
