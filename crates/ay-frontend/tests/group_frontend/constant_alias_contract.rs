// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Public import contract for the parsed constant alias.

use ay_core::Constant as CoreConstant;
use ay_frontend::{Constant as FrontendConstant, ParsedConstant};

fn assert_same_type<T>(value: T) -> T {
    value
}

#[test]
fn parsed_constant_alias_disambiguates_frontend_from_core_constant() {
    let core_constant = CoreConstant::Bool(true);
    let parsed_constant = ParsedConstant::True;

    assert_eq!(core_constant, CoreConstant::Bool(true));
    assert_eq!(parsed_constant, FrontendConstant::True);
    assert_eq!(
        assert_same_type::<FrontendConstant>(parsed_constant.clone()),
        parsed_constant
    );
}
