// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

#[test]
fn both_owned_nested_guards_admit_before_their_first_application_copy() {
    let nested = "(and p q)".to_string();
    let guard_charge = (nested.len() as u64) * 64 + 64;
    for operands in [vec![nested.clone()], vec![nested.clone(), TRUE.to_string()]] {
        let mut calls = Vec::new();
        let result = and_or_simplify_with_progress(&operands, true, &mut |amount| {
            calls.push(amount);
            amount != guard_charge
        });
        assert!(result.is_none());
        assert_eq!(calls.first(), Some(&(operands.len() as u64)));
        assert_eq!(calls.last(), Some(&guard_charge));
        assert_eq!(
            calls
                .iter()
                .filter(|&&amount| amount == guard_charge)
                .count(),
            1
        );
        if operands.len() == 1 {
            assert_eq!(calls, [1, guard_charge]);
        }
    }
}
