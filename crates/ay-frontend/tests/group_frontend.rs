// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Consolidated ay-frontend integration tests.
//!
//! Covers S-expression parsing, regex elaboration, and string sort rejection
//! contract tests.
//!
//! Each submodule was previously a standalone integration test binary.
//! Grouping them into one binary reduces compilation overhead (#8604).

#[path = "group_frontend/constant_alias_contract.rs"]
mod constant_alias_contract;
#[path = "group_frontend/parse_sexp_contract.rs"]
mod parse_sexp_contract;
#[path = "group_frontend/regex_elaboration_contract.rs"]
mod regex_elaboration_contract;
#[path = "group_frontend/sort_alias_contract.rs"]
mod sort_alias_contract;
#[path = "group_frontend/string_sort_rejection_contract.rs"]
mod string_sort_rejection_contract;
