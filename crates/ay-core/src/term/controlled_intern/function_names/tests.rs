// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use crate::Symbol;

#[test]
fn owned_function_name_every_retained_data_namespace_refuses_adoption() {
    for kind in 0..7 {
        let mut terms = TermStore::new();
        let truth = terms.true_term();
        match kind {
            0 => {
                terms.mk_var("occupied_function", Sort::Int);
            }
            1 => {
                terms.mk_app(Symbol::named("occupied_function"), [], Sort::Int);
            }
            2 => {
                terms.mk_let(vec![("occupied_function".into(), truth)], truth);
            }
            3 => {
                terms.mk_forall(vec![("occupied_function".into(), Sort::Int)], truth);
            }
            4 => {
                terms.mk_exists(vec![("occupied_function".into(), Sort::Int)], truth);
            }
            5 => terms.mark_skolem_symbol("occupied_function"),
            _ => terms.register_declared_function("occupied_function"),
        }
        let before = terms.len();
        assert_eq!(
            terms.native_function_name_is_available_with_progress(
                "occupied_function",
                &mut |_, _| true
            ),
            Ok(false)
        );
        assert_eq!(
            terms.try_register_new_function_name_with_progress("occupied_function", &mut |_, _| {
                true
            }),
            Err(Error::InvalidInput)
        );
        assert_eq!(terms.len(), before);
    }
}

#[test]
fn owned_function_name_terminal_refusal_never_publishes_registry_identity() {
    let mut baseline = TermStore::new();
    let mut count = 0;
    baseline
        .try_register_new_function_name_with_progress("function_fence", &mut |_, _| {
            count += 1;
            true
        })
        .unwrap();
    assert!(baseline.is_declared_function("function_fence"));
    let mut terms = TermStore::new();
    let mut seen = 0;
    assert_eq!(
        terms.try_register_new_function_name_with_progress("function_fence", &mut |_, _| {
            seen += 1;
            seen != count
        }),
        Err(Error::ResourceLimit)
    );
    assert_eq!(seen, count);
    assert!(!terms.is_declared_function("function_fence"));
}

#[test]
fn owned_function_name_long_history_is_priced_before_comparison_and_copy() {
    let mut terms = TermStore::new();
    let long = "retained_".repeat(2048);
    terms.mk_var(&long, Sort::Int);
    let mut largest = 0;
    assert_eq!(
        terms.try_register_new_function_name_with_progress("fresh_function", &mut |work, _| {
            largest = largest.max(work);
            work < 1024
        }),
        Err(Error::ResourceLimit)
    );
    assert!(largest >= 1024);
    assert!(!terms.is_declared_function("fresh_function"));
    terms
        .try_register_new_function_name_with_progress("fresh_function", &mut |_, _| true)
        .unwrap();
    assert!(terms.is_declared_function("fresh_function"));
}
