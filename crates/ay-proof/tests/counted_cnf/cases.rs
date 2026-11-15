// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
#![cfg(test)]

use super::*;

pub(super) fn with_gate(op: CountedBuiltin, assignment: u8, check: impl FnOnce(Native<'_, '_>)) {
    let original = owner();
    let mut terms = TermStore::try_new_with_admission(&original).unwrap();
    let mut builder = CountedTermBuilder::new(&mut terms, &original).unwrap();
    let a = builder.variable("a", &Sort::Bool).unwrap();
    let b = builder.variable("b", &Sort::Bool).unwrap();
    let c = builder.variable("c", &Sort::Bool).unwrap();
    let args: &[TermId] = match op {
        CountedBuiltin::Not => &[a],
        CountedBuiltin::Ite => &[a, b, c],
        _ => &[a, b],
    };
    let gate = builder.apply(op, args).unwrap();
    let (av, bv, cv) = (
        assignment & 1 != 0,
        assignment & 2 != 0,
        assignment & 4 != 0,
    );
    let value = match op {
        CountedBuiltin::Not => !av,
        CountedBuiltin::And => av && bv,
        CountedBuiltin::Or => av || bv,
        CountedBuiltin::Implies => !av || bv,
        CountedBuiltin::Xor | CountedBuiltin::Distinct => av != bv,
        CountedBuiltin::Eq | CountedBuiltin::Iff => av == bv,
        CountedBuiltin::Ite => {
            if av {
                bv
            } else {
                cv
            }
        }
        _ => panic!("unsupported test gate"),
    };
    let contradiction = if value {
        builder.apply(CountedBuiltin::Not, &[gate]).unwrap()
    } else {
        gate
    };
    let mut roots = vec![contradiction];
    for (var, value) in [(a, av), (b, bv), (c, cv)] {
        roots.push(if value {
            var
        } else {
            builder.apply(CountedBuiltin::Not, &[var]).unwrap()
        });
    }
    builder.finish().unwrap();
    let cnf = CountedCnf::encode(&mut terms, &roots, &original).unwrap();
    check(Native::from_cnf(&cnf));
    cnf.finish().unwrap();
    drop(terms);
    original.check().unwrap();
}

pub(super) fn with_distinct(case: u8, check: impl FnOnce(Native<'_, '_>)) {
    let original = owner();
    let mut terms = TermStore::try_new_with_admission(&original).unwrap();
    let mut builder = CountedTermBuilder::new(&mut terms, &original).unwrap();
    let a = builder.variable("a", &Sort::Bool).unwrap();
    let b = builder.variable("b", &Sort::Bool).unwrap();
    let not_a = builder.apply(CountedBuiltin::Not, &[a]).unwrap();
    let args = match case {
        1 => [a, a],
        2 => [a, not_a],
        3 => [not_a, not_a],
        _ => [a, b],
    };
    let d = builder.apply(CountedBuiltin::Distinct, &args).unwrap();
    let e = builder.apply(CountedBuiltin::Eq, &args).unwrap();
    let n = builder.apply(CountedBuiltin::Not, &[e]).unwrap();
    let q = builder.apply(CountedBuiltin::Eq, &[d, n]).unwrap();
    builder.finish().unwrap();
    // Q is a derived theorem, NOT an assumption: only authored D and E enter.
    let cnf = CountedCnf::encode(&mut terms, &[d, e], &original).unwrap();
    let bridge = cnf.bridges()[0];
    assert_eq!(
        (
            bridge.source,
            bridge.equality,
            bridge.negation,
            bridge.equivalence
        ),
        (d, e, n, q)
    );
    let index = cnf
        .steps()
        .iter()
        .position(|step| {
            step.rule() == &AletheRule::Resolution
                && step.clause()
                    == [
                        SourceLit {
                            term: d,
                            positive: false,
                        },
                        SourceLit {
                            term: n,
                            positive: true,
                        },
                    ]
        })
        .unwrap();
    let mut native = Native::from_cnf(&cnf);
    let not_e = native.proof.add_resolution(
        vec![n],
        d,
        native.assumptions[0],
        native.source_steps[index],
    );
    native
        .proof
        .add_resolution(vec![], e, native.assumptions[1], not_e);
    check(native);
    cnf.finish().unwrap();
    drop(terms);
    original.check().unwrap();
}
