// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Rewriting a scoped parse's terms onto the context's API declarations (see
//! the parent module).

use std::collections::HashMap;

use ay_dpll::api::{FuncDecl, Sort, Term, TermKind};

use super::super::{ffi_try_declare_function, SymbolKey, Z3Context};
use super::{GivenDeclaration, ParsedDeclaration};

/// Rewrites parsed terms so every symbol the parse declared is the context's
/// API declaration of the same name and signature.
pub(super) struct Rebinder<'a> {
    /// Core identity of a parse-declared symbol -> its declaration.
    pub(super) identities: HashMap<String, ParsedDeclaration>,
    /// Caller-named declarations by text name.
    pub(super) given: HashMap<String, &'a GivenDeclaration>,
    /// Helper name of a recursive definition's parameter -> its display name:
    /// a private constant of its own, never a context declaration.
    pub(super) rec_params: HashMap<String, String>,
    /// Core identity -> the API constant it is rebound to.
    pub(super) constants: HashMap<String, Term>,
    /// (core identity, arity) -> the API function it is rebound to.
    pub(super) functions: HashMap<(String, usize), FuncDecl>,
    /// Rebound terms, per enclosing binder names.
    pub(super) memo: HashMap<(Term, Vec<String>), Term>,
}

impl Rebinder<'_> {
    pub(super) fn rebind(
        &mut self,
        ctx: &mut Z3Context,
        term: Term,
        bound: &mut Vec<String>,
    ) -> Result<Term, String> {
        let key = (term, bound.clone());
        if let Some(&done) = self.memo.get(&key) {
            return Ok(done);
        }
        let result = match ctx.solver.term_kind(term) {
            TermKind::Const => term,
            TermKind::Var { name } => {
                if bound.contains(&name) {
                    term
                } else if let Some(declaration) = self.identities.get(&name).cloned() {
                    self.constant(ctx, &name, &declaration, term)?
                } else {
                    term
                }
            }
            TermKind::Let => return Err("a let binding is not rebound".to_string()),
            TermKind::Forall | TermKind::Exists => {
                let vars = ctx
                    .solver
                    .quantifier_bound_vars(term)
                    .ok_or_else(|| "a quantifier without binders".to_string())?;
                let depth = bound.len();
                bound.extend(vars.into_iter().map(|(name, _)| name));
                let children = ctx.solver.term_children(term);
                let mut rebound = Vec::with_capacity(children.len());
                for child in &children {
                    rebound.push(self.rebind(ctx, *child, bound)?);
                }
                bound.truncate(depth);
                self.update(ctx, term, &children, &rebound)?
            }
            TermKind::App { name, num_args } => {
                let children = ctx.solver.term_children(term);
                let mut rebound = Vec::with_capacity(children.len());
                for child in &children {
                    rebound.push(self.rebind(ctx, *child, bound)?);
                }
                match self.identities.get(&name).cloned() {
                    Some(declaration) if num_args > 0 => {
                        let decl = self.function(ctx, &name, &declaration, term, &children)?;
                        ctx.solver
                            .try_apply(&decl, &rebound)
                            .map_err(|e| format!("cannot rebind {}: {e}", declaration.name))?
                    }
                    _ => self.update(ctx, term, &children, &rebound)?,
                }
            }
            TermKind::Not | TermKind::Ite => {
                let children = ctx.solver.term_children(term);
                let mut rebound = Vec::with_capacity(children.len());
                for child in &children {
                    rebound.push(self.rebind(ctx, *child, bound)?);
                }
                self.update(ctx, term, &children, &rebound)?
            }
            _ => return Err("an unsupported term kind is not rebound".to_string()),
        };
        self.memo.insert(key, result);
        Ok(result)
    }

    fn update(
        &self,
        ctx: &mut Z3Context,
        term: Term,
        children: &[Term],
        rebound: &[Term],
    ) -> Result<Term, String> {
        if children == rebound {
            return Ok(term);
        }
        ctx.solver
            .try_update_term(term, rebound)
            .map_err(|e| format!("cannot rebuild a parsed term: {e}"))
    }

    /// The API constant for the parse-declared constant `identity`.
    fn constant(
        &mut self,
        ctx: &mut Z3Context,
        identity: &str,
        declaration: &ParsedDeclaration,
        term: Term,
    ) -> Result<Term, String> {
        if let Some(&api) = self.constants.get(identity) {
            return Ok(api);
        }
        let sort = ctx.solver.term_sort(term);
        if !declaration.domain.is_empty() || !same_sort(ctx, &sort, &declaration.range) {
            return Err(format!(
                "the declaration of {} has no API counterpart",
                declaration.name
            ));
        }
        let api = if let Some(display) = self.rec_params.get(&declaration.name) {
            // A recursive definition's parameter: bound by the definition,
            // so a private constant (as the caller's `Z3_add_rec_def`
            // arguments are), never the context's constant of that name.
            let private = format!("!ay.z3-const!{}", ctx.next_ffi_fresh_id);
            ctx.next_ffi_fresh_id += 1;
            ctx.solver
                .try_declare_const_with_fresh_identity(display, &private, sort.clone())
                .map_err(|e| format!("cannot declare a parameter of a recursive definition: {e}"))?
        } else {
            match self.given.get(&declaration.name) {
                Some(GivenDeclaration::Constant(given)) => *given,
                Some(GivenDeclaration::Function(_)) => {
                    return Err(format!("{} is not a constant", declaration.name));
                }
                None => {
                    // The context's constant of this name whose sort is this
                    // one: a datatype sort the caller built and the one the
                    // parse resolved can differ in representation only.
                    let symbol = SymbolKey::String(declaration.name.clone());
                    let existing = ctx
                        .ffi_const_cache
                        .iter()
                        .filter(|((key, _), _)| *key == symbol)
                        .map(|((_, api_sort), &api)| (api_sort.clone(), api))
                        .collect::<Vec<_>>()
                        .into_iter()
                        .find(|(api_sort, _)| same_sort(ctx, api_sort, &sort))
                        .map(|(_, api)| api);
                    match existing {
                        Some(api) => api,
                        None => super::super::terms::ffi_api_constant(ctx, &symbol, &sort)
                            .ok_or_else(|| {
                                ctx.error_msg.clone().unwrap_or_else(|| {
                                    format!("cannot declare {}", declaration.name)
                                })
                            })?,
                    }
                }
            }
        };
        let api_sort = ctx.solver.term_sort(api);
        if !same_sort(ctx, &api_sort, &sort) {
            return Err(format!(
                "{} is declared with another sort",
                declaration.name
            ));
        }
        self.constants.insert(identity.to_string(), api);
        Ok(api)
    }

    /// The API function for the parse-declared function `identity`, applied
    /// in `term` to `children`.
    fn function(
        &mut self,
        ctx: &mut Z3Context,
        identity: &str,
        declaration: &ParsedDeclaration,
        term: Term,
        children: &[Term],
    ) -> Result<FuncDecl, String> {
        let key = (identity.to_string(), children.len());
        if let Some(decl) = self.functions.get(&key) {
            return Ok(decl.clone());
        }
        let domain: Vec<Sort> = children.iter().map(|&c| ctx.solver.term_sort(c)).collect();
        let range = ctx.solver.term_sort(term);
        if domain.len() != declaration.domain.len()
            || !domain
                .iter()
                .zip(&declaration.domain)
                .all(|(a, b)| same_sort(ctx, a, b))
            || !same_sort(ctx, &range, &declaration.range)
        {
            return Err(format!(
                "the declaration of {} has no API counterpart",
                declaration.name
            ));
        }
        let decl = match self.given.get(&declaration.name) {
            Some(GivenDeclaration::Function(given)) => given.clone(),
            Some(GivenDeclaration::Constant(_)) => {
                return Err(format!("{} is not a function", declaration.name));
            }
            None => {
                let symbol = SymbolKey::String(declaration.name.clone());
                let existing = ctx
                    .ffi_func_decls
                    .iter()
                    .filter(|((key, d, _), _)| *key == symbol && d.len() == domain.len())
                    .map(|((_, d, r), decl)| (d.clone(), r.clone(), decl.clone()))
                    .collect::<Vec<_>>()
                    .into_iter()
                    .find(|(d, r, _)| {
                        d.iter().zip(&domain).all(|(a, b)| same_sort(ctx, a, b))
                            && same_sort(ctx, r, &range)
                    })
                    .map(|(_, _, decl)| decl);
                match existing {
                    Some(decl) => decl,
                    None => ffi_try_declare_function(ctx, &symbol, &domain, &range)
                        .map_err(|e| format!("cannot declare {}: {e}", declaration.name))?,
                }
            }
        };
        if decl.domain().len() != domain.len()
            || !decl
                .domain()
                .iter()
                .zip(&domain)
                .all(|(a, b)| same_sort(ctx, a, b))
            || !same_sort(ctx, decl.range(), &range)
        {
            return Err(format!(
                "{} is declared with another signature",
                declaration.name
            ));
        }
        ctx.ffi_used_decl_names.insert(declaration.name.clone());
        self.functions.insert(key, decl.clone());
        Ok(decl)
    }

    /// The API function a rebound application of the text's `name` with
    /// `arity` arguments resolved to.
    pub(super) fn function_named(&self, name: &str, arity: usize) -> Option<FuncDecl> {
        self.functions.iter().find_map(|((identity, n), decl)| {
            (*n == arity
                && self
                    .identities
                    .get(identity)
                    .is_some_and(|declaration| declaration.name == name))
            .then(|| decl.clone())
        })
    }
}

/// Whether two sorts are the same sort of the context: equal, or equal once
/// lowered as a native declaration over them is (a datatype the caller built
/// and the one a parse resolved by name differ in representation only).
fn same_sort(ctx: &Z3Context, a: &Sort, b: &Sort) -> bool {
    a == b || ctx.solver.live_sort(a) == ctx.solver.live_sort(b)
}
