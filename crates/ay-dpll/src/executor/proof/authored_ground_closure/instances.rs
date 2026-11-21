// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Ground clauses with explicit authored or universal-instance provenance.
//!
//! Each universal is instantiated at the registered ground terms of its binder
//! sort (bit-vector constants first) with the literal substitution
//! `forall_inst` accepts, and the instance is clausified by `or` or `implies`.
//! The values are proposals only: `validate_forall_inst_with_progress` re-derives every
//! substitution, and an instance matters only if unit propagation over it
//! (`facts.rs`) reaches a conflict the strict checker then replays.

use super::facts::{literal_atom, GroundSearch};
use super::*;
use crate::executor::proof::native_universal_lineage::{
    NativeUniversalSource, NativeUniversalWitness,
};
use std::sync::Arc;

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

/// The original proof-producing source of a clause.
#[derive(Clone, Debug)]
pub(super) enum ClauseOrigin {
    Forall {
        root: TermId,
        value: TermId,
        exact: TermId,
    },
    /// An initial authored root or conjunction projection. It precedes every
    /// propagated fact, so emission cannot form a fact dependency cycle.
    AuthoredFact(usize),
    NativeWitness(NativeUniversalWitness),
}

/// One ground clause with an explicit proof-producing origin.
#[derive(Clone, Debug)]
pub(super) struct InstanceClause {
    pub(super) origin: ClauseOrigin,
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
    pub(super) native: Option<Arc<NativeUniversalSource>>,
}

impl Executor {
    /// Prepay the old emitter before entering it, including spare vector/map
    /// capacity. Each path contains at most MAX_EDGES; each congruence/goal
    /// call recurses through checked edge/fact memoization. The emitter checks
    /// its 16k step ceiling before every recursive edge/fact/goal, so even its
    /// final unchecked resolution/projection tail fits the conservative 64k
    /// step allowance below. Clauses/args are bounded by an actual path or an
    /// actual source application, never by the whole arena's arbitrary data.
    pub(super) fn reserve_native_ground_emission(&self, search: &GroundSearch) -> Option<()> {
        self.charge_native_universal(search.closure.nodes().len(), 0)?;
        let mut width = search.closure.edges().len().checked_add(3)?;
        for &term in search.closure.nodes() {
            if let TermData::App(_, args) = self.ctx.terms.get(term) {
                width = width.max(args.len().checked_add(2)?);
            }
        }
        for clause in search.facts.clauses() {
            width = width.max(clause.literals.len().checked_add(2)?);
        }
        self.charge_native_universal(
            search.facts.facts().len(),
            search.facts.facts().len().checked_mul(8)?,
        )?;
        let mut pending: Vec<_> = search.facts.facts().iter().map(|f| f.literal).collect();
        let mut left = 4096usize;
        while let Some(term) = pending.pop() {
            left = left.checked_sub(1)?;
            self.charge_native_universal(1, 0)?;
            let children: &[TermId] = match self.ctx.terms.get(term) {
                TermData::App(_, args) => {
                    width = width.max(args.len().checked_add(2)?);
                    args
                }
                TermData::Not(child) => std::slice::from_ref(child),
                TermData::Ite(c, t, e) => {
                    self.charge_native_universal(3, 24)?;
                    if pending.len().checked_add(3)? > left {
                        return None;
                    }
                    pending.extend([*c, *t, *e]);
                    continue;
                }
                _ => &[],
            };
            if pending.len().checked_add(children.len())? > left {
                return None;
            }
            self.charge_native_universal(children.len(), children.len().checked_mul(8)?)?;
            pending.extend(children.iter().copied());
        }
        let steps = 65_536usize;
        let slots = width.checked_add(2)?.checked_mul(8)?;
        let bytes = steps
            .checked_mul(
                std::mem::size_of::<ProofStep>()
                    .checked_add(slots.checked_mul(std::mem::size_of::<TermId>())?)?,
            )?
            .checked_add((MAX_NODES + MAX_EDGES).checked_mul(256)?)?;
        let work = steps.checked_mul(width.checked_add(4)?.checked_pow(2)?)?;
        self.charge_native_universal(work, bytes)
    }

    /// Single-binder, quantifier-free-body universals of the authored scope
    /// that a top-level parsed assertion states without a source macro.
    ///
    /// The instance's Alethe spelling is re-derived from the AUTHORED body at
    /// publication; a `define-fun` the elaborator expanded there prints as
    /// its symbol, and the instance would no longer print the clause checked.
    pub(super) fn flat_ground_closure_foralls(&mut self) -> Vec<FlatForall> {
        if let Some(source) = NativeUniversalSource::capture(self) {
            let source = Arc::new(source);
            return source
                .roots()
                .iter()
                .filter_map(|&root| {
                    let TermData::Forall(bindings, body, _) = self.ctx.terms.get(root) else {
                        return None;
                    };
                    let [(binder, sort)] = bindings.as_slice() else {
                        return None;
                    };
                    if crate::ematching::contains_quantifier(&self.ctx.terms, *body) {
                        return None;
                    }
                    Some(FlatForall {
                        root,
                        binder: binder.clone(),
                        sort: sort.clone(),
                        body: *body,
                        native: Some(Arc::clone(&source)),
                    })
                })
                .collect();
        }
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
                    native: None,
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
        let mut instances = 0usize;
        if let Some(source) = foralls.iter().find_map(|f| f.native.as_ref()) {
            for plan in self.native_universal_witnesses(source)? {
                let instance = plan.asserted;
                let (shape, literals) = self.instance_literals(instance);
                self.register_ground_subterms(&mut search.closure, instance)?;
                search.facts.push_clause(InstanceClause {
                    origin: ClauseOrigin::NativeWitness(plan),
                    instance,
                    shape,
                    literals,
                });
                instances += 1;
            }
        }
        for forall in foralls {
            if let Some(source) = &forall.native {
                if !source.admits(self, forall.root) {
                    return None;
                }
                // Each sort comparison below may traverse a nested nominal/
                // array/sequence sort. Admit actual borrowed candidate data,
                // not only the expected binder sort, before that first use.
                self.admit_native_universal_terms(search.closure.nodes())?;
            }
            let mut values: Vec<TermId> = search
                .closure
                .nodes()
                .iter()
                .copied()
                .filter(|&node| self.ctx.terms.sort(node) == &forall.sort)
                .collect();
            if forall.native.is_some() {
                self.seed_native_universal_values(&forall.sort, &mut values)?;
            }
            if let Some(source) = &forall.native {
                self.seed_native_universal_source_values(source, &forall.sort, &mut values)?;
            }
            values.sort_by_key(|&value| !Self::is_bitvec_constant(&self.ctx.terms, value));
            values.truncate(MAX_VALUES_PER_BINDER);
            for value in values {
                if instances >= MAX_INSTANCES {
                    return Some(());
                }
                let exact = if let Some(source) = &forall.native {
                    self.native_universal_instance(source, forall.root, &[value])
                } else {
                    Self::substitute_single_binder_structurally(
                        &mut self.ctx.terms,
                        forall.body,
                        &forall.binder,
                        value,
                    )
                };
                let Some(exact) = exact else {
                    continue;
                };
                let instance = if forall.native.is_some() {
                    self.admit_native_universal_terms(&[exact])?;
                    self.normalize_native_universal_boolean(exact, 0)?
                } else {
                    exact
                };
                let (shape, literals) = self.instance_literals(instance);
                for &literal in &literals {
                    self.register_literal_operands(&mut search.closure, literal)?;
                }
                search.facts.push_clause(InstanceClause {
                    origin: ClauseOrigin::Forall {
                        root: forall.root,
                        value,
                        exact,
                    },
                    instance,
                    shape,
                    literals,
                });
                instances += 1;
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
    pub(super) fn register_literal_operands(
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
