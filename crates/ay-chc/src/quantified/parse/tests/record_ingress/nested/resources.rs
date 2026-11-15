// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

#![cfg(test)]

use super::*;

fn dependency_group(depth: usize, fanout: usize) -> String {
    let names = (0..=depth)
        .rev()
        .map(|n| format!("(R{n} 0)"))
        .collect::<Vec<_>>()
        .join(" ");
    let definitions = (0..=depth)
        .rev()
        .map(|n| {
            let fields = if n == 0 {
                "(flag Bool)".to_owned()
            } else {
                (0..fanout)
                    .map(|i| format!("(f{i} R{})", n - 1))
                    .collect::<Vec<_>>()
                    .join(" ")
            };
            format!("((mkR{n} {fields}))")
        })
        .collect::<Vec<_>>()
        .join(" ");
    format!("(declare-datatypes ({names}) ({definitions}))(declare-rel error ())(query error)")
}

#[test]
fn nested_dependency_depth_and_expanded_leaf_limits_refuse_with_fresh_retry() {
    let live = parsed(&dependency_group(8, 2));
    assert_eq!(live.source_problem().datatype_defs().len(), 9);
    fixtures::refuses(&dependency_group(9, 2));
    fixtures::refuses(&dependency_group(
        crate::quantified::records::MAX_RECORD_DEPTH + 2,
        1,
    ));
    assert_eq!(
        parsed(&dependency_group(4, 1))
            .source_problem()
            .datatype_defs()
            .len(),
        5
    );
}
