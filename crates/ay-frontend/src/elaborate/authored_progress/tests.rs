// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use crate::command::{Constant, Term};

fn fixture() -> Context {
    let mut ctx = Context::new();
    let false_term = ctx.terms.false_term();
    ctx.authored_assertions = vec![
        AuthoredAssertion::Concrete {
            term: false_term,
            origin: super::super::AuthoredAssertionOrigin::Text,
            parsed_index: None,
            source_is_literal_false: false,
        },
        AuthoredAssertion::Schematic(Term::Const(Constant::False)),
        AuthoredAssertion::Concrete {
            term: false_term,
            origin: super::super::AuthoredAssertionOrigin::Text,
            parsed_index: None,
            source_is_literal_false: true,
        },
    ];
    ctx
}

#[test]
fn lookup_matches_owning_oracle_without_inventing_literal_source() {
    let mut ctx = fixture();
    for retained in (0..=ctx.authored_assertions.len()).rev() {
        ctx.authored_assertions.truncate(retained);
        for term in [
            ctx.terms.false_term(),
            ctx.terms.true_term(),
            TermId::SENTINEL,
        ] {
            let expected = ctx.concrete_authored_literal_false_terms().contains(&term);
            let actual = ctx
                .concrete_authored_literal_false_contains_with_progress(term, &mut || {
                    Ok::<(), ()>(())
                })
                .unwrap();
            assert_eq!(actual, expected);
            assert_eq!(actual, retained == 3 && term == ctx.terms.false_term());
        }
    }
}

#[test]
fn every_checkpoint_refuses_without_later_poll_or_source_mutation() {
    let ctx = fixture();
    for term in [ctx.terms.false_term(), ctx.terms.true_term()] {
        let before = ctx.concrete_authored_literal_false_terms();
        let mut polls = 0;
        ctx.concrete_authored_literal_false_contains_with_progress(term, &mut || {
            polls += 1;
            Ok::<(), usize>(())
        })
        .unwrap();
        assert_eq!(polls, 5);
        for stop in 1..=polls {
            let mut calls = 0;
            let result =
                ctx.concrete_authored_literal_false_contains_with_progress(term, &mut || {
                    calls += 1;
                    if calls == stop {
                        Err(stop)
                    } else {
                        Ok(())
                    }
                });
            assert_eq!(result, Err(stop));
            assert_eq!(calls, stop);
        }
        assert_eq!(ctx.concrete_authored_literal_false_terms(), before);
        assert_eq!(
            ctx.concrete_authored_literal_false_contains_with_progress(term, &mut || Ok::<(), ()>(
                ()
            ),),
            Ok(before.contains(&term)),
        );
    }
}
