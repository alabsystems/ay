// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Incremental split-loop pipeline macro dispatcher for DPLL(T) solving.
//!
//! Public entry points for [`solve_incremental_split_loop_pipeline`] and
//! [`solve_incremental_assume_split_loop_pipeline`]. Each entry variant
//! dispatches to a mode-specific arm macro in a dedicated file (#6680):
//!
//! - Lazy arm: [`pipeline_incremental_split_lazy_macros`]
//! - Eager arm: [`pipeline_incremental_split_eager_macros`]
//! - Eager-persistent arm: [`pipeline_incremental_split_eager_persistent_macros`]
//! - Assumption arm: [`pipeline_incremental_split_assume_macros`]
//!
//! The non-split incremental variant is in [`pipeline_incremental_macros`].

/// Incremental theory pipeline with branch-and-bound split handling.
///
/// Combines `solve_incremental_theory_pipeline!` setup (persistent SAT, scope
/// management, assertion activation) with branch-and-bound split handling
/// (NeedSplit, NeedDisequalitySplit, NeedExpressionSplit, incremental Tseitin
/// encoding via `encode_split_pair_incremental`).
///
/// # Parameters
/// - `$self`: the Executor instance
/// - `tag`: string label for debug messages
/// - `persistent_sat_field`: field on IncrementalTheoryState to store persistent SAT solver
/// - `create_theory`: expression producing a fresh theory solver each iteration
/// - `extract_models`: closure `|theory: &mut T| -> TheoryModels`
/// - `max_splits`: maximum branch-and-bound iterations
/// - `pre_theory_import`: closure `|theory: &mut T, lc, hc, ds|` to import learned state
/// - `post_theory_export`: closure `|theory: &mut T| -> (lc, hc, ds)` to export learned state
/// - `pre_iter_check`: (optional) closure `|&self|` returning true to abort
/// - `on_sat_model_adjust`: (optional) closure `|theory: &mut T| -> Option<LiaModel>` for LIA model
#[allow(unused_macro_rules)]
macro_rules! solve_incremental_split_loop_pipeline {
    // Eager variant (#6582, #4919): uses TheoryExtension for inline theory
    // propagation during BCP. This enables theory-SAT interleaving within
    // each solve call, matching the standard DPLL(T) architecture used by Z3.
    ($self:ident,
        tag: $tag:expr,
        persistent_sat_field: $sat_field:ident,
        create_theory: $create_theory:expr,
        extract_models: |$theory_var:ident| $extract:expr,
        max_splits: $max_splits:expr,
        pre_theory_import: |$import_theory:ident, $import_lc:ident, $import_hc:ident, $import_ds:ident| $import_expr:expr,
        post_theory_export: |$export_theory:ident| $export_expr:expr,
        eager_extension: true
        $(, disable_preprocess: $disable_preprocess:expr)?
        $(, pre_iter_check: |$pic_self:ident| $pic_expr:expr)?
        $(, verify_unsat_after_splits: $verify_unsat:expr)?
        $(, skip_arith_triangle: $skip_tri:expr)?
        $(, max_string_lemma_requests: $max_slr:expr,
           handle_string_lemma: |$sl_lemma:ident, $sl_negations:ident| $sl_handler:expr)?
    ) => {{
        pipeline_incremental_split_eager_arm!($self,
            tag: $tag,
            persistent_sat_field: $sat_field,
            tseitin_field: tseitin_state,
            encoded_field: encoded_assertions,
            activation_scope_field: assertion_activation_scope,
            create_theory: $create_theory,
            extract_models: |$theory_var| $extract,
            max_splits: $max_splits,
            pre_theory_import: |$import_theory, $import_lc, $import_hc, $import_ds| $import_expr,
            post_theory_export: |$export_theory| $export_expr
            $(, disable_preprocess: $disable_preprocess)?
            $(, pre_iter_check: |$pic_self| $pic_expr)?
            $(, verify_unsat_after_splits: $verify_unsat)?
            $(, skip_arith_triangle: $skip_tri)?
            $(, max_string_lemma_requests: $max_slr,
               handle_string_lemma: |$sl_lemma, $sl_negations| $sl_handler)?
        )
    }};
    // Eager + persistent theory variant (#6590 Packet 3): theory solver is
    // created once before the loop and warm-reset each iteration instead of
    // recreated. Preserves simplex basis and variable values across iterations,
    // matching Z3's persistent lar_solver architecture.
    ($self:ident,
        tag: $tag:expr,
        persistent_sat_field: $sat_field:ident,
        create_theory: $create_theory:expr,
        extract_models: |$theory_var:ident| $extract:expr,
        max_splits: $max_splits:expr,
        pre_theory_import: |$import_theory:ident, $import_lc:ident, $import_hc:ident, $import_ds:ident| $import_expr:expr,
        post_theory_export: |$export_theory:ident| $export_expr:expr,
        persistent_theory: true,
        eager_extension: true
        $(, pre_iter_check: |$pic_self:ident| $pic_expr:expr)?
    ) => {{
        pipeline_incremental_split_eager_persistent_arm!($self,
            tag: $tag,
            persistent_sat_field: $sat_field,
            tseitin_field: tseitin_state,
            encoded_field: encoded_assertions,
            activation_scope_field: assertion_activation_scope,
            create_theory: $create_theory,
            extract_models: |$theory_var| $extract,
            max_splits: $max_splits,
            pre_theory_import: |$import_theory, $import_lc, $import_hc, $import_ds| $import_expr,
            post_theory_export: |$export_theory| $export_expr
            $(, pre_iter_check: |$pic_self| $pic_expr)?
        )
    }};
    // Eager variant with explicit Tseitin/encoding/activation fields.
    // Used by QF_LIA, which keeps an isolated `lia_*` SAT/Tseitin state because
    // preprocessing can change the assertion shape between check-sats (#6853).
    ($self:ident,
        tag: $tag:expr,
        persistent_sat_field: $sat_field:ident,
        tseitin_field: $tseitin_field:ident,
        encoded_field: $encoded_field:ident,
        activation_scope_field: $activation_scope_field:ident,
        create_theory: $create_theory:expr,
        extract_models: |$theory_var:ident| $extract:expr,
        max_splits: $max_splits:expr,
        pre_theory_import: |$import_theory:ident, $import_lc:ident, $import_hc:ident, $import_ds:ident| $import_expr:expr,
        post_theory_export: |$export_theory:ident| $export_expr:expr,
        eager_extension: true
        $(, disable_preprocess: $disable_preprocess:expr)?
        $(, pre_iter_check: |$pic_self:ident| $pic_expr:expr)?
        $(, accept_unsat_after_splits: $accept_unsat:expr)?
        $(, max_string_lemma_requests: $max_slr:expr,
           handle_string_lemma: |$sl_lemma:ident, $sl_negations:ident| $sl_handler:expr)?
    ) => {{
        pipeline_incremental_split_eager_arm!($self,
            tag: $tag,
            persistent_sat_field: $sat_field,
            tseitin_field: $tseitin_field,
            encoded_field: $encoded_field,
            activation_scope_field: $activation_scope_field,
            create_theory: $create_theory,
            extract_models: |$theory_var| $extract,
            max_splits: $max_splits,
            pre_theory_import: |$import_theory, $import_lc, $import_hc, $import_ds| $import_expr,
            post_theory_export: |$export_theory| $export_expr
            $(, disable_preprocess: $disable_preprocess)?
            $(, pre_iter_check: |$pic_self| $pic_expr)?
            $(, accept_unsat_after_splits: $accept_unsat)?
            $(, max_string_lemma_requests: $max_slr,
               handle_string_lemma: |$sl_lemma, $sl_negations| $sl_handler)?
        )
    }};
    // Lazy variant (original): SAT solves to completion, then theory checks
    // the full model. Used by LIA and other theories that don't yet benefit
    // from eager propagation.
    ($self:ident,
        tag: $tag:expr,
        persistent_sat_field: $sat_field:ident,
        create_theory: $create_theory:expr,
        extract_models: |$theory_var:ident| $extract:expr,
        max_splits: $max_splits:expr,
        pre_theory_import: |$import_theory:ident, $import_lc:ident, $import_hc:ident, $import_ds:ident| $import_expr:expr,
        post_theory_export: |$export_theory:ident| $export_expr:expr
        $(, pre_iter_check: |$pic_self:ident| $pic_expr:expr)?
        $(, per_round_shadow: |$sh_result:ident, $sh_lits:ident, $sh_atoms:ident, $sh_lemmas:ident| $sh_expr:expr)?
        $(, max_string_lemma_requests: $max_slr:expr,
           handle_string_lemma: |$sl_lemma:ident, $sl_negations:ident| $sl_handler:expr)?
    ) => {{
        pipeline_incremental_split_lazy_arm!($self,
            tag: $tag,
            persistent_sat_field: $sat_field,
            tseitin_field: tseitin_state,
            encoded_field: encoded_assertions,
            activation_scope_field: assertion_activation_scope,
            create_theory: $create_theory,
            extract_models: |$theory_var| $extract,
            max_splits: $max_splits,
            pre_theory_import: |$import_theory, $import_lc, $import_hc, $import_ds| $import_expr,
            post_theory_export: |$export_theory| $export_expr
            $(, pre_iter_check: |$pic_self| $pic_expr)?
            $(, per_round_shadow: |$sh_result, $sh_lits, $sh_atoms, $sh_lemmas| $sh_expr)?
            $(, max_string_lemma_requests: $max_slr,
               handle_string_lemma: |$sl_lemma, $sl_negations| $sl_handler)?
        )
    }};
    // Lazy variant with explicit Tseitin/encoding/activation fields (#6853).
    // Used by LIA which needs its own isolated state because preprocessing
    // changes assertions between check-sats. Accumulated global Tseitin
    // definitions from prior check-sats conflict with new formulas.
    ($self:ident,
        tag: $tag:expr,
        persistent_sat_field: $sat_field:ident,
        tseitin_field: $tseitin_field:ident,
        encoded_field: $encoded_field:ident,
        activation_scope_field: $activation_scope_field:ident,
        create_theory: $create_theory:expr,
        extract_models: |$theory_var:ident| $extract:expr,
        max_splits: $max_splits:expr,
        pre_theory_import: |$import_theory:ident, $import_lc:ident, $import_hc:ident, $import_ds:ident| $import_expr:expr,
        post_theory_export: |$export_theory:ident| $export_expr:expr
        $(, pre_iter_check: |$pic_self:ident| $pic_expr:expr)?
        $(, max_string_lemma_requests: $max_slr:expr,
           handle_string_lemma: |$sl_lemma:ident, $sl_negations:ident| $sl_handler:expr)?
    ) => {{
        pipeline_incremental_split_lazy_arm!($self,
            tag: $tag,
            persistent_sat_field: $sat_field,
            tseitin_field: $tseitin_field,
            encoded_field: $encoded_field,
            activation_scope_field: $activation_scope_field,
            create_theory: $create_theory,
            extract_models: |$theory_var| $extract,
            max_splits: $max_splits,
            pre_theory_import: |$import_theory, $import_lc, $import_hc, $import_ds| $import_expr,
            post_theory_export: |$export_theory| $export_expr
            $(, pre_iter_check: |$pic_self| $pic_expr)?
            $(, max_string_lemma_requests: $max_slr,
               handle_string_lemma: |$sl_lemma, $sl_negations| $sl_handler)?
        )
    }};
}

/// Incremental assumption-based split-loop pipeline (#6689).
///
/// Assumption-aware counterpart of `solve_incremental_split_loop_pipeline!`
/// (lazy arm). Keeps one persistent SAT solver alive across split iterations
/// and uses `solve_with_assumptions` instead of `solve`.
#[allow(unused_macro_rules)]
macro_rules! solve_incremental_assume_split_loop_pipeline {
    ($self:ident,
        tag: $tag:expr,
        persistent_sat_field: $sat_field:ident,
        assumptions: $assumptions:expr,
        create_theory: $create_theory:expr,
        extract_models: |$theory_var:ident| $extract:expr,
        max_splits: $max_splits:expr,
        pre_theory_import: |$import_theory:ident, $import_lc:ident, $import_hc:ident, $import_ds:ident| $import_expr:expr,
        post_theory_export: |$export_theory:ident| $export_expr:expr
        $(, pre_iter_check: |$pic_self:ident| $pic_expr:expr)?
    ) => {{
        pipeline_incremental_split_assume_arm!($self,
            tag: $tag,
            persistent_sat_field: $sat_field,
            assumptions: $assumptions,
            create_theory: $create_theory,
            extract_models: |$theory_var| $extract,
            max_splits: $max_splits,
            pre_theory_import: |$import_theory, $import_lc, $import_hc, $import_ds| $import_expr,
            post_theory_export: |$export_theory| $export_expr
            $(, pre_iter_check: |$pic_self| $pic_expr)?
        )
    }};
}
