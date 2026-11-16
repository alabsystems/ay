// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Storage-only transactions over genuine independent completion DATA.

use super::*;
use ay_core::{DatatypeConstructor, DatatypeField, DatatypeSort, Symbol};
use ay_model_check::{GateVerdict, ModelView};

struct Unpinned;

impl ModelView for Unpinned {
    fn leaf_value(&self, _: TermId) -> Option<ModelValue> {
        None
    }
}

struct Source {
    ctx: Context,
    array: TermId,
    roots: Vec<TermId>,
}

impl Source {
    fn new() -> Self {
        let mut ctx = Context::new();
        let cell = Sort::Datatype(DatatypeSort::new(
            "Cell",
            vec![DatatypeConstructor::new(
                "mkCell",
                vec![DatatypeField::new("length", Sort::bitvec(64))],
            )],
        ));
        let array = ctx
            .terms
            .mk_var("array", Sort::array(Sort::bitvec(64), cell.clone()));
        let index = ctx.terms.mk_bitvec(9.into(), 64);
        let selected = ctx
            .terms
            .mk_app(Symbol::named("select"), [array, index], cell);
        let length = ctx
            .terms
            .mk_app(Symbol::named("length"), [selected], Sort::bitvec(64));
        let five = ctx.terms.mk_bitvec(5.into(), 64);
        let equation = ctx
            .terms
            .mk_app(Symbol::named("="), [length, five], Sort::Bool);
        Self {
            ctx,
            array,
            roots: vec![equation],
        }
    }

    fn extract(&self) -> Vec<CompletedArrayAssignment> {
        let model = Unpinned;
        let (verdict, data) = ay_model_check::confirm_model_with_array_completion(
            &self.ctx.terms,
            &model,
            &self.roots,
        )
        .into_parts();
        assert!(matches!(verdict, GateVerdict::ConfirmedSat));
        let assignments = data.unwrap().into_assignments().unwrap();
        assert_eq!(assignments.len(), 1);
        assignments
    }

    fn model(&self) -> Model {
        let mut model = Model::empty();
        model
            .install_residual_arrays(&self.ctx, self.extract())
            .unwrap();
        model
    }
}

fn retained(model: &Model) -> Arc<ModelValue> {
    Arc::clone(&model.residual_arrays.as_ref().unwrap().entries[0].2)
}

#[test]
fn empty_duplicate_and_oversized_transactions_preserve_payload_and_seals() {
    let source = Source::new();
    let mut model = source.model();
    let original = retained(&model);
    let confirmation = model.seal_quantified_confirmation();
    let grant = model.seal_quantified_grant_model();
    assert!(matches!(
        model.install_residual_arrays(&source.ctx, vec![]),
        Err(ResidualCompletionError::Empty)
    ));
    let mut duplicated = source.extract();
    duplicated.extend(source.extract());
    assert!(matches!(
        model.install_residual_arrays(&source.ctx, duplicated),
        Err(ResidualCompletionError::DuplicateMember)
    ));
    let mut oversized = Vec::new();
    for _ in 0..=MAX_MEMBERS {
        oversized.extend(source.extract());
    }
    // The size gate precedes allocation/sorting and therefore duplicate checks.
    assert!(matches!(
        model.install_residual_arrays(&source.ctx, oversized),
        Err(ResidualCompletionError::TooManyMembers)
    ));
    assert!(Arc::ptr_eq(&original, &retained(&model)));
    assert!(model.carries_quantified_confirmation(&confirmation));
    assert!(model.carries_quantified_grant_model(&grant));
    assert!(model.residual_arrays_are_current(&source.ctx));
}

#[test]
fn matching_numeric_ids_in_a_foreign_context_do_not_replace_the_model() {
    let source = Source::new();
    let foreign = Source::new();
    assert_eq!(source.array, foreign.array);
    assert_ne!(
        source.ctx.terms.entry_stamp(source.array),
        foreign.ctx.terms.entry_stamp(foreign.array)
    );
    let mut model = source.model();
    let original = retained(&model);
    let confirmation = model.seal_quantified_confirmation();
    let grant = model.seal_quantified_grant_model();
    assert!(matches!(
        model.install_residual_arrays(&source.ctx, foreign.extract()),
        Err(ResidualCompletionError::InvalidMember)
    ));
    assert!(Arc::ptr_eq(&original, &retained(&model)));
    assert!(model.carries_quantified_confirmation(&confirmation));
    assert!(model.carries_quantified_grant_model(&grant));
    assert!(model
        .residual_array_value(&source.ctx, source.array)
        .unwrap()
        .is_some());
}

#[test]
fn successful_replacement_revokes_old_model_identity_without_minting_new_proof() {
    let source = Source::new();
    let mut model = source.model();
    let original = retained(&model);
    let confirmation = model.seal_quantified_confirmation();
    let grant = model.seal_quantified_grant_model();
    model
        .install_residual_arrays(&source.ctx, source.extract())
        .unwrap();
    assert!(!Arc::ptr_eq(&original, &retained(&model)));
    assert!(model.residual_arrays_are_current(&source.ctx));
    assert!(!model.carries_quantified_confirmation(&confirmation));
    assert!(!model.carries_quantified_grant_model(&grant));
}

#[test]
fn semantic_model_clone_shares_immutable_data_but_drops_identity_seals() {
    let source = Source::new();
    let mut model = source.model();
    let confirmation = model.seal_quantified_confirmation();
    let grant = model.seal_quantified_grant_model();
    let clone = model.clone();
    assert!(Arc::ptr_eq(&retained(&model), &retained(&clone)));
    assert!(clone.residual_arrays_are_current(&source.ctx));
    assert!(!clone.carries_quantified_confirmation(&confirmation));
    assert!(!clone.carries_quantified_grant_model(&grant));
    assert!(model.carries_quantified_confirmation(&confirmation));
    assert!(model.carries_quantified_grant_model(&grant));
}

#[test]
fn fresh_query_terms_preserve_data_but_scope_roundtrip_never_revives_old_package() {
    let mut source = Source::new();
    let model = source.model();
    let before = source.ctx.source_context_stamp();
    let scalar = source.ctx.terms.mk_bitvec(11.into(), 64);
    let _ = source
        .ctx
        .terms
        .mk_app(Symbol::named("bvadd"), [scalar, scalar], Sort::bitvec(64));
    assert_eq!(source.ctx.source_context_stamp(), before);
    assert!(model.residual_arrays_are_current(&source.ctx));
    for text in ["(push 1)", "(pop 1)"] {
        for command in ay_frontend::parse(text).unwrap() {
            source.ctx.process_command(&command).unwrap();
        }
        assert_ne!(source.ctx.source_context_stamp(), before);
        assert!(!model.residual_arrays_are_current(&source.ctx));
        assert!(model
            .residual_array_value(&source.ctx, source.array)
            .is_err());
    }
}
