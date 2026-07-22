// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Facade import contract for parsed SMT-LIB constants (#544).

use ay::{Command, ParsedConstant};
use ay_core::Constant as CoreConstant;

fn assert_same_type<T>(value: T) -> T {
    value
}

#[test]
fn facade_exports_parsed_constant_without_shadowing_core_constant() {
    let core_constant = CoreConstant::Bool(true);
    let parsed_constant = ParsedConstant::True;
    let command = Command::Assert(ay_frontend::Term::Const(parsed_constant.clone()));

    assert_eq!(core_constant, CoreConstant::Bool(true));
    assert!(matches!(
        command,
        Command::Assert(ay_frontend::Term::Const(ParsedConstant::True))
    ));
    assert_eq!(
        assert_same_type::<ay_frontend::Constant>(parsed_constant.clone()),
        parsed_constant
    );
}

#[test]
fn api_and_prelude_expose_parsed_constant_alias() {
    use ay::api::ParsedConstant as ApiParsedConstant;
    use ay::prelude::ParsedConstant as PreludeParsedConstant;

    assert_eq!(ApiParsedConstant::False, ParsedConstant::False);
    assert_eq!(
        PreludeParsedConstant::Numeral("1".to_string()),
        ParsedConstant::Numeral("1".to_string())
    );
}
