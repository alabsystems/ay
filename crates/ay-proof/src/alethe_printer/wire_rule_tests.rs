// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

#[test]
fn every_checkable_name_round_trips_to_the_canonical_static_entry() {
    assert_eq!(CHECKABLE_RULE_NAMES, ay_core::CHECKABLE_ALETHE_RULES);
    for (index, name) in CHECKABLE_RULE_NAMES.iter().enumerate() {
        let rule = CheckableRule::new(name).expect("table member");
        assert_eq!(rule.as_str(), *name);
        assert_eq!(rule.as_str().as_ptr(), name.as_ptr(), "table entry {index}");
        assert_eq!(rule.to_string(), *name);
    }
}

#[test]
fn names_outside_the_checkable_vocabulary_are_refused() {
    for name in ["", "trust", "invented_rule"] {
        assert_eq!(CheckableRule::new(name), None, "{name:?}");
    }
}

#[test]
fn fallback_is_the_canonical_admitted_hole() {
    let hole = CheckableRule::new(ay_core::UNPROVED_STEP_RULE).expect("hole is checkable");
    assert_eq!(hole.as_str(), ay_core::UNPROVED_STEP_RULE);
    assert_eq!(CheckableRule::or_hole("invented_rule"), hole);
    assert_eq!(CheckableRule::or_hole("trans").as_str(), "trans");
}
