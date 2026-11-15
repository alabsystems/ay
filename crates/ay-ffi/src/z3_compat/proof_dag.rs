// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Authenticated applications projected from supported native proof rules.
use super::{
    cache_func_decl, decode_indexed_ast, encode_indexed_ast, term_to_ast, SymbolKey, Z3Context,
    Z3_ast, Z3_func_decl, PROOF_AST_TAG,
};
use ay_dpll::api::{FuncDecl, NativeProofApplication, NativeProofDag, Sort};

pub(super) const ASSERTED: u32 = 0x502;
pub(super) const MODUS_PONENS: u32 = 0x504;
pub(super) const UNIT_RESOLUTION: u32 = 0x518;
const TEXT_LIMIT: usize = 1_048_576;

#[derive(Clone, Debug)]
pub(crate) struct ProofApplication {
    pub declaration: Z3_func_decl,
    pub arguments: Vec<Z3_ast>,
}

pub(crate) fn proof_sort() -> Sort {
    // A C string cannot name this private sort. Its public display symbol is
    // Proof; it is not an ordinary user uninterpreted sort.
    Sort::Uninterpreted("\0ay.proof".to_owned())
}

pub(crate) fn application(ctx: &Z3Context, ast: Z3_ast) -> Option<&ProofApplication> {
    let index = decode_indexed_ast(ctx, ast, PROOF_AST_TAG)?;
    ctx.proof_applications.get(&index)
}

/// Only native rule projections can mint these read-only proof applications.
/// No solver verdict, opaque proof string or user declaration is sufficient.
pub(crate) fn materialize(ctx: &mut Z3Context, dag: &NativeProofDag) -> Option<Z3_ast> {
    let sort = proof_sort();
    ctx.ffi_sort_symbols
        .insert(sort.clone(), SymbolKey::String("Proof".to_owned()));
    let mut handles = Vec::new();
    let mut total_text = 0usize;
    for node in &dag.applications {
        let (kind, name, mut arguments, conclusion) = match node {
            NativeProofApplication::Asserted(term) => {
                if ctx.solver.try_term_sort(*term).ok()? != Sort::Bool {
                    return None;
                }
                (ASSERTED, "asserted", Vec::new(), *term)
            }
            NativeProofApplication::UnitResolution {
                premises,
                conclusion,
            } => {
                let arguments = premises
                    .iter()
                    .map(|index| handles.get(*index).copied())
                    .collect::<Option<Vec<_>>>()?;
                let conclusion = ctx.solver.try_or_many(conclusion).ok()?;
                (UNIT_RESOLUTION, "unit-resolution", arguments, conclusion)
            }
            NativeProofApplication::ModusPonens {
                premises,
                conclusion,
            } => {
                let arguments = premises
                    .iter()
                    .map(|index| handles.get(*index).copied())
                    .collect::<Option<Vec<_>>>()?;
                (MODUS_PONENS, "mp", arguments, *conclusion)
            }
        };
        arguments.push(term_to_ast(ctx, conclusion));
        let key = (kind, arguments.clone());
        if let Some(handle) = ctx.proof_application_intern.get(&key) {
            let index = decode_indexed_ast(ctx, *handle, PROOF_AST_TAG)?;
            total_text = total_text.checked_add(ctx.proof_texts.get(index)?.len())?;
            if total_text > TEXT_LIMIT {
                return None;
            }
            handles.push(*handle);
            continue;
        }
        let mut pieces = Vec::new();
        for handle in &arguments[..arguments.len().checked_sub(1)?] {
            let index = decode_indexed_ast(ctx, *handle, PROOF_AST_TAG)?;
            pieces.push(ctx.proof_texts.get(index)?.as_str());
        }
        let conclusion_text = ctx.solver.try_render_term_canonical(conclusion).ok()?;
        let size = pieces
            .iter()
            .try_fold(name.len() + conclusion_text.len() + 3, |sum, piece| {
                sum.checked_add(piece.len() + 1)
            })?;
        total_text = total_text.checked_add(size)?;
        if size > TEXT_LIMIT || total_text > TEXT_LIMIT {
            return None;
        }
        let mut text = String::with_capacity(size);
        text.push('(');
        text.push_str(name);
        for piece in pieces {
            text.push(' ');
            text.push_str(piece);
        }
        text.push(' ');
        text.push_str(&conclusion_text);
        text.push(')');
        let mut domain = vec![sort.clone(); arguments.len().checked_sub(1)?];
        domain.push(Sort::Bool);
        let declaration =
            cache_func_decl(ctx, FuncDecl::new(name.to_owned(), domain, sort.clone()));
        ctx.proof_declarations.insert(declaration, kind);
        let index = ctx.proof_texts.len();
        let handle = encode_indexed_ast(ctx, PROOF_AST_TAG, index)?;
        ctx.proof_texts.push(text);
        ctx.proof_applications.insert(
            index,
            ProofApplication {
                declaration,
                arguments,
            },
        );
        ctx.proof_application_intern.insert(key, handle);
        handles.push(handle);
    }
    handles.get(dag.root).copied()
}

/// Materialize only recorded insertion and retirement events. A missing local certificate
/// stays absent, as upstream mk_clause_trail_elem permits.
pub(crate) fn materialize_clause_trail(
    ctx: &mut Z3Context,
    trail: &ay_dpll::api::NativeClauseTrail,
) -> Option<Z3_ast> {
    use ay_dpll::api::NativeClauseOrigin;
    ctx.ffi_sort_symbols
        .insert(proof_sort(), SymbolKey::String("Proof".into()));
    let mut arguments = Vec::with_capacity(trail.events.len().checked_add(1)?);
    let mut texts = Vec::with_capacity(trail.events.len());
    let mut bytes = 0usize;
    for event in &trail.events {
        let (kind, name) = match event.origin {
            NativeClauseOrigin::Assumption => (0x51d, "assumption"),
            NativeClauseOrigin::Lemma => (0x51e, "lemma"),
            NativeClauseOrigin::TheoryAssumption => (0x52a, "th-assume"),
            NativeClauseOrigin::TheoryLemma => (0x52b, "th-lemma"),
            NativeClauseOrigin::Deleted => (0x51f, "del"),
        };
        let fact = ctx.solver.try_or_many(&event.literals).ok()?;
        let fact_text = ctx.solver.try_render_term_canonical(fact).ok()?;
        bytes = bytes.checked_add(fact_text.len().checked_add(name.len() + 3)?)?;
        if bytes > TEXT_LIMIT {
            return None;
        }
        let text = format!("({name} {fact_text})");
        let fact_ast = term_to_ast(ctx, fact);
        let ast = store_trail_application(
            ctx,
            kind,
            name,
            vec![fact_ast],
            vec![Sort::Bool],
            text.clone(),
        )?;
        arguments.push(ast);
        texts.push(text);
    }
    let false_term = ctx.solver.try_or_many(&[]).ok()?;
    arguments.push(term_to_ast(ctx, false_term));
    let mut domain = vec![proof_sort(); texts.len()];
    domain.push(Sort::Bool);
    let text = format!("(clause-trail {} false)", texts.join(" "));
    store_trail_application(ctx, 0x520, "clause-trail", arguments, domain, text)
}

fn store_trail_application(
    ctx: &mut Z3Context,
    kind: u32,
    name: &str,
    arguments: Vec<Z3_ast>,
    domain: Vec<Sort>,
    text: String,
) -> Option<Z3_ast> {
    let key = (kind, arguments.clone());
    if let Some(handle) = ctx.proof_application_intern.get(&key) {
        return Some(*handle);
    }
    let declaration = cache_func_decl(ctx, FuncDecl::new(name.to_owned(), domain, proof_sort()));
    ctx.proof_declarations.insert(declaration, kind);
    let index = ctx.proof_texts.len();
    let handle = encode_indexed_ast(ctx, PROOF_AST_TAG, index)?;
    ctx.proof_texts.push(text);
    ctx.proof_applications.insert(
        index,
        ProofApplication {
            declaration,
            arguments,
        },
    );
    ctx.proof_application_intern.insert(key, handle);
    Some(handle)
}
