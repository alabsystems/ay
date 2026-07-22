// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Term analysis helper functions for the executor.
//!
//! This module provides utility functions for analyzing term structure,
//! detecting arithmetic operations, and pattern matching on equality chains.

mod arithmetic;
mod euf_patterns;
mod interface_terms;
#[cfg(test)]
mod tests;

pub(crate) use arithmetic::{
    arg_involves_select_or_store, contains_arithmetic_ops, contains_seq_len_ops,
    contains_string_ops, has_substantive_int_constraints, int_constraints_are_constants_only,
    involves_array, involves_int_arithmetic, involves_real_arithmetic, is_pure_arithmetic_term,
    is_select_or_store,
};
pub(crate) use euf_patterns::{
    collect_bool_arg_congruence_lemmas, decode_non_bool_eq, is_pure_uf_uf_int_equality,
    is_select_real_equality, is_uf_int_equality, is_uf_real_equality, or_implies_eq_endpoints,
};
pub(crate) use interface_terms::{
    extract_interface_arith_term, extract_uf_mixed_eq_operands, extract_uf_mixed_interface_term,
};

#[cfg(test)]
use arithmetic::is_absorbing_concat_eq;
#[cfg(test)]
use euf_patterns::{chain_endpoints, decode_and_two_eqs};
#[cfg(test)]
use interface_terms::involves_uninterpreted_function;
