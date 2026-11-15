// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Ground instances of single-binder authored universals, as clauses.
//!
//! Each universal is instantiated at the registered ground terms of its binder
//! sort (bit-vector constants first) with the literal substitution
//! `forall_inst` accepts, and the instance is clausified by `or` or `implies`.
//! The values are proposals only: `validate_forall_inst` re-derives every
//! substitution, and an instance matters only if unit propagation over it
//! (`facts.rs`) reaches a conflict the strict checker then replays.

use super::facts::{literal_atom, GroundSearch};
use super::*;

/// Universal instances one search may take.
const MAX_INSTANCES: usize = 64;
/// Ground values proposed per universal.
const MAX_VALUES_PER_BINDER: usize = 16;
/// Surface nodes one source-macro scan may visit.
const MAX_SURFACE_WORK: usize = 4_096;

/// How an instance becomes its clause.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) enum InstanceShape {
    /// The instance is itself the one literal.
    Unit,
    /// `(or l1 .. ln)` clausified by `or`.
    Or,
    /// `(=> a b)` clausified by `implies` into `(not a) b`.
    Implies,
}

/// One ground instance of an authored universal, as a clause.
#[derive(Clone, Debug)]
pub(super) struct InstanceClause {
    pub(super) forall_root: TermId,
    pub(super) value: TermId,
    pub(super) instance: TermId,
    pub(super) shape: InstanceShape,
    pub(super) literals: Vec<TermId>,
}

/// A single-binder authored universal with a quantifier-free body.
pub(super) struct FlatForall {
    pub(super) root: TermId,
    pub(super) binder: String,
    pub(super) sort: Sort,
    pub(super) body: TermId,
}

impl Executor {
    /// Single-binder, quantifier-free-body universals of the authored scope
    /// that a top-level parsed assertion states without a source macro.
    ///
    /// The instance's Alethe spelling is re-derived from the AUTHORED body at
    /// publication; a `define-fun` the elaborator expanded there prints as
    /// its symbol, and the instance would no longer print the clause checked.
    pub(super) fn flat_ground_closure_foralls(&mut self) -> Vec<FlatForall> {
        let parsed: Vec<FrontendTerm> = self.ctx.raw_reinternable_parsed_assertions().to_vec();
        let mut authored: Vec<TermId> = Vec::new();
        for assertion in &parsed {
            let stripped =
                crate::executor::proof_surface_syntax::strip_frontend_annotations(assertion);
            if matches!(stripped, FrontendTerm::Forall(..)) && !self.mentions_source_macro(stripped)
            {
                authored.extend(self.ctx.elaborate_surface_subterm(stripped));
            }
        }
        self.exact_concrete_authored_scope()
            .into_iter()
            .filter(|root| authored.contains(root))
            .filter_map(|root| {
                let TermData::Forall(bindings, body, _) = self.ctx.terms.get(root) else {
                    return None;
                };
                let [(binder, sort)] = bindings.as_slice() else {
                    return None;
                };
                if matches!(
                    self.ctx.terms.get(*body),
                    TermData::Forall(..) | TermData::Exists(..) | TermData::Let(..)
                ) {
                    return None;
                }
                Some(FlatForall {
                    root,
                    binder: binder.clone(),
                    sort: sort.clone(),
                    body: *body,
                })
            })
            .collect()
    }

    /// Instantiate each universal at the registered ground terms of its
    /// binder sort (constants first) and record the instance clauses.
    pub(super) fn seed_ground_instances(
        &mut self,
        search: &mut GroundSearch,
        foralls: &[FlatForall],
    ) -> Option<()> {
        for forall in foralls {
            let mut values: Vec<TermId> = search
                .closure
                .nodes()
                .iter()
                .copied()
                .filter(|&node| self.ctx.terms.sort(node) == &forall.sort)
                .collect();
            values.sort_by_key(|&value| !Self::is_bitvec_constant(&self.ctx.terms, value));
            values.truncate(MAX_VALUES_PER_BINDER);
            for value in values {
                if search.facts.clauses().len() >= MAX_INSTANCES {
                    return Some(());
                }
                let Some(instance) = Self::substitute_single_binder_structurally(
                    &mut self.ctx.terms,
                    forall.body,
                    &forall.binder,
                    value,
                ) else {
                    continue;
                };
                let (shape, literals) = self.instance_literals(instance);
                for &literal in &literals {
                    self.register_literal_operands(&mut search.closure, literal)?;
                }
                search.facts.push_clause(InstanceClause {
                    forall_root: forall.root,
                    value,
                    instance,
                    shape,
                    literals,
                });
            }
        }
        Some(())
    }

    /// The clause an instance clausifies to.
    pub(super) fn instance_literals(&mut self, instance: TermId) -> (InstanceShape, Vec<TermId>) {
        match self.ctx.terms.get(instance).clone() {
            TermData::App(symbol, args) if symbol.name() == "or" && args.len() >= 2 => {
                (InstanceShape::Or, args)
            }
            TermData::App(symbol, args) if symbol.name() == "=>" && args.len() == 2 => {
                let antecedent = self.ctx.terms.mk_not_raw(args[0]);
                (InstanceShape::Implies, vec![antecedent, args[1]])
            }
            _ => (InstanceShape::Unit, vec![instance]),
        }
    }

    /// Whether `surface` names or applies a source `define-fun` (or an adopted
    /// definitional macro), within [`MAX_SURFACE_WORK`] nodes; an oversized or
    /// unrecognized shape answers `true`, which only declines.
    pub(super) fn mentions_source_macro(&self, surface: &FrontendTerm) -> bool {
        let is_macro = |name: &str| {
            self.ctx.is_defined_fun(name) || self.ctx.adopted_macro_interp(name).is_some()
        };
        let mut pending = vec![surface];
        let mut work = MAX_SURFACE_WORK;
        while let Some(term) = pending.pop() {
            let Some(remaining) = work.checked_sub(1) else {
                return true;
            };
            work = remaining;
            match term {
                FrontendTerm::Const(_) => {}
                FrontendTerm::Symbol(name) if is_macro(name) => return true,
                FrontendTerm::Symbol(_) => {}
                FrontendTerm::App(name, _) if is_macro(name) => return true,
                FrontendTerm::App(_, args)
                | FrontendTerm::IndexedApp(_, _, args)
                | FrontendTerm::QualifiedApp(_, _, args) => pending.extend(args),
                FrontendTerm::Forall(_, body)
                | FrontendTerm::Exists(_, body)
                | FrontendTerm::Lambda(_, body)
                | FrontendTerm::Annotated(body, _) => pending.push(body),
                _ => return true,
            }
        }
        false
    }

    /// Register the operands of a literal's atom: both sides of an equality,
    /// the arguments of any other application.
    fn register_literal_operands(
        &self,
        closure: &mut GroundClosure,
        literal: TermId,
    ) -> Option<()> {
        let (atom, _) = literal_atom(&self.ctx.terms, literal);
        if let TermData::App(_, args) = self.ctx.terms.get(atom) {
            for argument in args.clone() {
                self.register_ground_subterms(closure, argument)?;
            }
        }
        Some(())
    }
}
