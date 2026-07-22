// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Facade import contract for parsed SMT-LIB sort names (#543).

use ay::{Command, ParsedSort, Sort};

fn assert_same_type<T>(value: T) -> T {
    value
}

#[test]
fn facade_exports_parsed_sort_without_renaming_native_sort() {
    let native_sort = Sort::Int;
    let parsed_sort = ParsedSort::Simple("Int".to_string());
    let command = Command::DeclareConst("x".to_string(), parsed_sort.clone());

    assert_eq!(native_sort, Sort::Int);
    assert!(matches!(
        command,
        Command::DeclareConst(_, ParsedSort::Simple(ref name)) if name == "Int"
    ));
    assert_eq!(
        assert_same_type::<ay_frontend::Sort>(parsed_sort.clone()),
        parsed_sort
    );
}

#[test]
fn api_and_prelude_expose_parsed_sort_alias() {
    use ay::api::ParsedSort as ApiParsedSort;
    use ay::prelude::ParsedSort as PreludeParsedSort;

    assert_eq!(
        ApiParsedSort::Simple("Bool".to_string()),
        ParsedSort::Simple("Bool".to_string())
    );
    assert_eq!(
        PreludeParsedSort::Simple("Real".to_string()),
        ParsedSort::Simple("Real".to_string())
    );
}
