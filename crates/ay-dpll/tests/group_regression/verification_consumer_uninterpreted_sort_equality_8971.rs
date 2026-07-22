// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Regression guard for #8971: verification-consumer hashmap VCs mix integer side
//! conditions with equality chains over an uninterpreted collection sort.

#[test]
fn uflia_uninterpreted_sort_equality_chain_not_narrowed_to_lia_8971() {
    let smt = r#"
(set-logic UFLIA)
(declare-sort MyHashMap 0)
(declare-const self MyHashMap)
(declare-const self_current_view MyHashMap)
(declare-const self_current MyHashMap)
(declare-const result MyHashMap)
(declare-const result_view MyHashMap)
(declare-const __quantifier_consumer_num_coerce_0 Int)
(declare-const __quantifier_consumer_num_coerce_1 Int)
(assert (= self_current_view self_current))
(assert (<= 0 __quantifier_consumer_num_coerce_0))
(assert (<= __quantifier_consumer_num_coerce_1 18446744073709551615))
(assert (= self result))
(assert (= self self_current))
(assert (= self result_view))
(assert (= self self_current))
(assert (not (= self_current_view result_view)))
(check-sat)
"#;
    let output = crate::common::solve(smt);
    let result = crate::common::sat_result(&output);

    assert_eq!(
        result,
        Some("unsat"),
        "#8971 verification-consumer hashmap equality chain should use EUF, got {output}"
    );
}
