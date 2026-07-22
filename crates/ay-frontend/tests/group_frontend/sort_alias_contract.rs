// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Public import contract for the parsed sort alias.

use ay_core::Sort as CoreSort;
use ay_frontend::{ParsedSort, Sort as FrontendSort};

fn assert_same_type<T>(value: T) -> T {
    value
}

#[test]
fn parsed_sort_alias_disambiguates_frontend_from_core_sort() {
    let core_sort = CoreSort::Int;
    let parsed_sort = ParsedSort::Simple("Int".to_string());

    assert_eq!(core_sort, CoreSort::Int);
    assert_eq!(parsed_sort, FrontendSort::Simple("Int".to_string()));
    assert_eq!(
        assert_same_type::<FrontendSort>(parsed_sort.clone()),
        parsed_sort
    );
}
