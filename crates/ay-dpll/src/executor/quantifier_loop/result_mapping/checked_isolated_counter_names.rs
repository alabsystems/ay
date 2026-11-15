// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The internal spellings whose digits are PROVEN to be an allocator counter,
//! exempt from the arena-prune veto (`carries_name_encoded_term_ids`).

use crate::executor::theories::bv_lia_aux_vars::is_bv_lia_aux_var_name;

/// Private declaration identity: `Context::fresh_private_declaration_core_identity`.
pub(super) const PRIVATE_DECLARATION_IDENTITY_PREFIX: &str = "__ay_overload_";

/// Array-extensionality witness: `ArrayExtWitnessCache::mint` via
/// `TermStore::mk_internal_symbol("ext_diff")`. Test builds pin it equal to
/// `theories::ARRAY_EXT_WITNESS_PREFIX`, which exists only under `cfg(test)`.
pub(super) const ARRAY_EXT_WITNESS_SPELLING: &str = "__ay_ext_diff!";

/// Equality-difference variable: `preprocess::eq_diffvar` via
/// `TermStore::mk_internal_symbol(EQ_DIFF_VARIABLE_PURPOSE)`. Test builds pin
/// it to that purpose and to the pass's own output.
pub(super) const EQ_DIFF_VARIABLE_SPELLING: &str = "__ay_eqdv!";

/// Whether `name` is one of the EXACT internal spellings whose digits are
/// PROVEN to be an allocator counter, never a `TermId`.
///
/// An allow-list of proofs, not a relaxation of the property test it exempts
/// from: each entry is a fixed prefix with ONE producer, followed by a
/// non-empty all-digit tail and nothing else.
///
///  * `__ay_overload_{n}`: `n` is `Context::next_overload_identity`, a
///    per-context counter shared by ordinary overloads and datatype members (two
///    datatypes that both declare `fld_len` give the second one this identity).
///    `api::solving::native_replay` already reads the same grammar as an
///    allocator identity (`is_allocator_private_declaration_identity`).
///  * `__ay_ext_diff!{n}`: `n` is `TermStore::var_counter` (`mk_internal_symbol`
///    formats `__ay_{purpose}!{next_var_id}`), which `mark_and_compact` does not
///    relabel.
///  * `__ay_eqdv!{n}`: the same counter; `preprocess::eq_diffvar` is the one
///    producer of its difference variables. The strict checker reads their
///    DEFINITIONS (`ay_proof` `fresh_def`, which says it never looks at the
///    name), and model validation tests only the prefix.
///  * `__ay_bv_lia_{cong,i,q,ib,ir}_{n}`: the same counter (`mk_fresh_var`
///    formats `{prefix}_{next_var_id}`); `bv_lia_aux_vars::mint_bv_lia_aux_var`
///    is the one producer, and its own [`is_bv_lia_aux_var_name`] is the
///    grammar read here, so the two cannot drift apart. Those names used to
///    spell the `TermId` they stood for; the measurement is on that module.
///
/// Nothing parses any of these tails back: each decoder listed on
/// `carries_name_encoded_term_ids` owns a DIFFERENT prefix, and the map
/// carriers are `__ay_map_dom!` / `__ay_map_dom_free!`. The frontend refuses
/// every `__ay_` source symbol, so no user can spell one either. Every producer
/// points back here: the tests pin each SPELLING against its real producer, and
/// a change that made a tail carry a `TermId` must remove its entry.
///
/// Why it matters: one overloaded datatype field vetoed the prune, and the
/// unpruned clone carried the enclosing solve's whole scratch. On
/// `model_checker_consumer_quantified_counterexample/nested_query_false_unsat` the
/// authored-ground-core probe received 25,826 terms, built 4.27M clauses and
/// overran `GROUND_CORE_PROBE_BUDGET_MS`; pruned it holds 50 terms and decides
/// in milliseconds. A longer or mixed tail (`__ay_ext_diff_1_2`,
/// `__ay_overload_7x`, `__ay_bv_lia_cong_k4_w64_14`) or any other internal
/// prefix with a digit still vetoes.
pub(super) fn is_counter_only_internal_name(name: &str) -> bool {
    let counter_tail =
        |tail: &str| !tail.is_empty() && tail.bytes().all(|byte| byte.is_ascii_digit());
    [
        PRIVATE_DECLARATION_IDENTITY_PREFIX,
        ARRAY_EXT_WITNESS_SPELLING,
        EQ_DIFF_VARIABLE_SPELLING,
    ]
    .iter()
    .any(|prefix| name.strip_prefix(prefix).is_some_and(counter_tail))
        || is_bv_lia_aux_var_name(name)
}
