// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Exact substitutions are proposals. Before indexing a folded native unit,
//! the independent premise checker validates its entire forall/Boolean proof
//! against the receipt's complete original root window, with the SAME meter.

use super::NativeUniversalSource;
use crate::executor::Executor;
use ay_core::kani_compat::DetHashMap;
use ay_core::{AletheRule, Proof, ProofId, Sort, Symbol, TermData, TermId, TheoryLemmaKind};

impl Executor {
    /// Original closed subterms are ordinary SMT values, even when their
    /// carrier has no constructor seed. Their occurrence supplies only a
    /// proposed instantiation value: the FULL original membership guard still
    /// has to be derived by the finished proof.
    pub(in crate::executor) fn seed_native_universal_source_values(
        &mut self,
        source: &NativeUniversalSource,
        sort: &Sort,
        values: &mut Vec<TermId>,
    ) -> Option<()> {
        if !source.is_current(self) {
            return None;
        }
        // The shared census admits every physical edge/sort/name first. This
        // walk borrows lexical names: the legacy ground collector owns a copy
        // of every enclosing name-prefix key at each nested binder.
        self.admit_native_universal_terms(source.roots())?;
        let mut left = 4096usize;
        for &root in source.roots() {
            closed_source_values(self, root, sort, &[], values, 0, &mut left)?;
        }
        source.is_current(self).then_some(())
    }

    /// Propose ordinary SMT values without adding a premise. A nominal seed
    /// must be an actual live, nullary native constructor of this exact sort;
    /// an opaque carrier alone never supplies a Rust-domain inhabitant.
    pub(in crate::executor) fn seed_native_universal_values(
        &mut self,
        sort: &Sort,
        values: &mut Vec<TermId>,
    ) -> Option<()> {
        self.charge_native_universal(values.len().checked_mul(2)?, 32)?;
        if sort == &Sort::Bool {
            for seed in [self.ctx.terms.false_term(), self.ctx.terms.true_term()] {
                if !values.contains(&seed) {
                    values.push(seed);
                }
            }
            return Some(());
        }
        let scalar = match sort {
            Sort::Int => Some(self.ctx.terms.mk_int(0.into())),
            Sort::Real => Some(
                self.ctx
                    .terms
                    .mk_rational(num_rational::BigRational::from_integer(0.into())),
            ),
            Sort::BitVec(bits) if (1..=4096).contains(&bits.width) => {
                Some(self.ctx.terms.mk_bitvec(0.into(), bits.width))
            }
            _ => None,
        };
        if let Some(seed) = scalar {
            if !values.contains(&seed) {
                values.push(seed);
            }
            return Some(());
        }
        let Sort::Uninterpreted(carrier) = sort else {
            return Some(());
        };
        if carrier.len() > 4096 {
            return None;
        }
        self.charge_native_universal(self.ctx.native_datatype_seed_iteration_work()?, 0)?;
        self.charge_native_universal(self.ctx.native_datatype_seed_lookup_work(carrier, None)?, 0)?;
        if !self.ctx.is_live_datatype_carrier(carrier) {
            return Some(());
        }
        let constructors = self.ctx.datatype_constructors(carrier)?;
        if constructors.len() > 16 {
            return None;
        }
        let mut seeds = Vec::new();
        for name in constructors {
            if name.len() > 4096 {
                return None;
            }
            let lookup = self
                .ctx
                .native_datatype_seed_lookup_work(carrier, Some(name))?
                .checked_add(carrier.len().checked_mul(4)?)?;
            self.charge_native_universal(
                lookup,
                name.len().checked_add(carrier.len())?.checked_add(128)?,
            )?;
            let info = self.ctx.exact_datatype_member_info(name)?;
            let (owner, _) = self.ctx.constructor_metadata(name)?;
            if owner == carrier && info.arg_sorts.is_empty() && &info.sort == sort {
                // Reuse the actual registered nullary binding. A second App[]
                // is a supported logical form, but adds an unnecessary engine
                // representation and carries no stronger source identity.
                let seed = info.term?;
                self.ctx.terms.entry_stamp(seed)?;
                if self.ctx.terms.sort(seed) != sort
                    || !matches!(self.ctx.terms.get(seed), TermData::Var(actual, _) if actual == name)
                {
                    return None;
                }
                self.reserve_native_source_vector(&mut seeds)?;
                seeds.push(seed);
            }
        }
        for seed in seeds {
            self.charge_native_universal(values.len(), 0)?;
            if !values.contains(&seed) {
                self.reserve_native_source_vector(values)?;
                values.push(seed);
            }
        }
        Some(())
    }

    /// Optional Boolean normalization, whose implication is emitted as a
    /// checked BoolTautology. It preserves theory atoms and membership guards;
    /// normalization itself is not proof credit.
    pub(in crate::executor) fn normalize_native_universal_boolean(
        &mut self,
        term: TermId,
        depth: usize,
    ) -> Option<TermId> {
        if depth > 64 {
            return None;
        }
        self.charge_native_universal(1, 128)?;
        match self.ctx.terms.get(term).clone() {
            TermData::Not(inner) => {
                let inner = self.normalize_native_universal_boolean(inner, depth + 1)?;
                Some(self.ctx.terms.mk_not(inner))
            }
            TermData::Ite(c, t, e) if self.ctx.terms.sort(term) == &Sort::Bool => {
                let c = self.normalize_native_universal_boolean(c, depth + 1)?;
                let t = self.normalize_native_universal_boolean(t, depth + 1)?;
                let e = self.normalize_native_universal_boolean(e, depth + 1)?;
                Some(self.ctx.terms.mk_ite(c, t, e))
            }
            TermData::App(symbol, children)
                if matches!(symbol.name(), "and" | "or" | "=>" | "=")
                    && children
                        .iter()
                        .all(|&c| self.ctx.terms.sort(c) == &Sort::Bool) =>
            {
                let args = children
                    .into_iter()
                    .map(|c| self.normalize_native_universal_boolean(c, depth + 1))
                    .collect::<Option<Vec<_>>>()?;
                match (symbol.name(), args.as_slice()) {
                    ("and", _) => Some(self.ctx.terms.mk_and(args)),
                    ("or", _) => Some(self.ctx.terms.mk_or(args)),
                    ("=>", [a, b]) => Some(self.ctx.terms.mk_implies(*a, *b)),
                    ("=", [a, b]) => Some(self.ctx.terms.mk_eq(*a, *b)),
                    _ => Some(term),
                }
            }
            _ => Some(term),
        }
    }

    pub(in crate::executor) fn native_universal_instance(
        &mut self,
        source: &NativeUniversalSource,
        root: TermId,
        values: &[TermId],
    ) -> Option<TermId> {
        if !source.admits(self, root) {
            return None;
        }
        self.admit_native_universal_terms(&[root])?;
        self.admit_native_universal_terms(values)?;
        let TermData::Forall(bindings, body, _) = self.ctx.terms.get(root) else {
            return None;
        };
        if bindings.len() != values.len() {
            return None;
        }
        let mut replacement = DetHashMap::default();
        for ((name, sort), &value) in bindings.iter().zip(values) {
            if self.ctx.terms.sort(value) != sort
                || replacement.insert(name.clone(), value).is_some()
            {
                return None;
            }
        }
        let body = *body;
        let instance =
            crate::ematching::subst_vars_exact_qf(&mut self.ctx.terms, body, &replacement)?;
        (self.ctx.terms.sort(instance) == &Sort::Bool && source.is_current(self))
            .then_some(instance)
    }

    /// Reconstruct the raw negative-forall instance BEFORE inspecting a
    /// simplifying Skolem record. This is a source-bound diagnostic/proposal,
    /// never a registration or a grant to the normalized working term.
    pub(in crate::executor) fn native_negative_universal_instance(
        &mut self,
        source: &NativeUniversalSource,
        original: TermId,
        quantified: TermId,
        witness: TermId,
    ) -> Option<TermId> {
        if !source.is_current(self) || !source.roots().contains(&original) {
            return None;
        }
        self.admit_native_universal_terms(&[original, quantified, witness])?;
        if !matches!(self.ctx.terms.get(original), TermData::Not(q) if *q == quantified) {
            return None;
        }
        let TermData::Forall(bindings, body, _) = self.ctx.terms.get(quantified) else {
            return None;
        };
        let [(name, sort)] = bindings.as_slice() else {
            return None;
        };
        if self.ctx.terms.sort(witness) != sort {
            return None;
        }
        let mut replacement = DetHashMap::default();
        replacement.insert(name.clone(), witness);
        let body = *body;
        let exact = crate::ematching::subst_vars_exact_qf(&mut self.ctx.terms, body, &replacement)?;
        self.admit_native_universal_terms(&[exact])?;
        source.is_current(self).then_some(exact)
    }

    /// Candidate emission only; callers must authenticate the finished proof.
    pub(super) fn emit_native_forall_unit(
        &mut self,
        proof: &mut Proof,
        root: TermId,
        values: &[TermId],
        instance: TermId,
    ) -> ProofId {
        let negative = self.ctx.terms.mk_not_raw(root);
        let implication =
            self.ctx
                .terms
                .mk_app(Symbol::named("or"), [negative, instance], Sort::Bool);
        let source = proof.add_assume(root, None);
        let forall = proof.add_rule_step(
            AletheRule::ForallInst,
            vec![implication],
            Vec::new(),
            values.to_vec(),
        );
        let clause = proof.add_rule_step(
            AletheRule::Or,
            vec![negative, instance],
            vec![forall],
            Vec::new(),
        );
        proof.add_resolution(vec![instance], root, clause, source)
    }

    /// Derive even a constant-folded Boolean target without confusing it with
    /// the literal forall_inst conclusion. A false implication simply fails
    /// the independent checker and leaves the target unregistered.
    pub(in crate::executor) fn derive_native_universal_target(
        &mut self,
        source: &NativeUniversalSource,
        root: TermId,
        values: &[TermId],
        target: TermId,
    ) -> Option<ProofId> {
        self.admit_native_universal_terms(&[target])?;
        let exact = self.native_universal_instance(source, root, values)?;
        self.admit_native_universal_terms(&[exact])?;
        // Four forall steps plus an optional checked Boolean implication and
        // resolution. This prepays all small candidate vectors before copy.
        self.charge_native_universal(256 + values.len(), 4096 + values.len().checked_mul(8)?)?;
        let mut candidate = Proof::new();
        let unit = self.emit_native_forall_unit(&mut candidate, root, values, exact);
        let negative = self.ctx.terms.mk_not_raw(exact);
        if target != exact {
            let lemma = candidate.add_theory_lemma_with_kind(
                "bool",
                vec![negative, target],
                TheoryLemmaKind::BoolTautology,
            );
            candidate.add_resolution(vec![target], exact, unit, lemma);
        }
        ay_proof::authenticate_premise_clauses_strict_with_context_and_progress(
            &candidate,
            &self.ctx.terms,
            None,
            None,
            source.roots(),
            &mut |work, bytes| self.charge_native_universal(work, bytes).is_some(),
        )
        .ok()?;
        if !source.is_current(self) {
            return None;
        }
        // The tracker re-emits the same exact substitution; its generic-unit
        // index now points at a derivation, never an added problem assumption.
        let unit = self.proof_tracker.add_forall_instantiated_assertion(
            &mut self.ctx.terms,
            root,
            values,
            exact,
        )?;
        if target == exact {
            return Some(unit);
        }
        self.proof_tracker.add_derived_unit_lemma(
            vec![negative, target],
            TheoryLemmaKind::BoolTautology,
            &[(negative, exact, unit)],
            target,
        )
    }
}

/// One expanded occurrence walk, with no TermId-only memo that can confuse
/// the same variable under two different lexical scopes. Every child is
/// visited even if another child is bound, so independent closed subterms
/// remain usable. This creates values only, never premise or member facts.
fn closed_source_values<'a>(
    exec: &'a Executor,
    term: TermId,
    requested: &Sort,
    bound: &[&'a str],
    values: &mut Vec<TermId>,
    depth: usize,
    left: &mut usize,
) -> Option<bool> {
    *left = left.checked_sub(1)?;
    if depth > 64 {
        return None;
    }
    exec.charge_native_universal(1, 0)?;
    exec.ctx.terms.entry_stamp(term)?;
    let ground = match exec.ctx.terms.get(term) {
        TermData::Const(_) => true,
        TermData::Var(name, _) => {
            let mut free = true;
            for &binder in bound {
                exec.charge_native_universal(
                    name.len().checked_add(binder.len())?.checked_add(1)?,
                    0,
                )?;
                free &= binder != name.as_str();
            }
            free
        }
        TermData::App(_, children) => {
            exec.charge_native_universal(children.len(), 0)?;
            let mut ground = true;
            for &child in children {
                ground &=
                    closed_source_values(exec, child, requested, bound, values, depth + 1, left)?;
            }
            ground
        }
        TermData::Not(child) => {
            closed_source_values(exec, *child, requested, bound, values, depth + 1, left)?
        }
        TermData::Ite(c, t, e) => {
            let mut ground = true;
            for child in [*c, *t, *e] {
                ground &=
                    closed_source_values(exec, child, requested, bound, values, depth + 1, left)?;
            }
            ground
        }
        TermData::Forall(bindings, body, _) | TermData::Exists(bindings, body, _) => {
            let width = bound.len().checked_add(bindings.len())?;
            exec.charge_native_universal(
                width,
                width
                    .checked_mul(std::mem::size_of::<&str>())?
                    .checked_mul(2)?
                    .checked_add(std::mem::size_of::<Vec<&str>>())?,
            )?;
            let mut nested = Vec::new();
            nested.try_reserve_exact(width).ok()?;
            nested.extend_from_slice(bound);
            nested.extend(bindings.iter().map(|(name, _)| name.as_str()));
            closed_source_values(exec, *body, requested, &nested, values, depth + 1, left)?;
            // Quantifiers are not ground argument proposals for this QF
            // instantiation route, even when they bind no occurring variable.
            return Some(false);
        }
        _ => return None,
    };
    if ground && closed_source_sorts_equal(exec, exec.ctx.terms.sort(term), requested, 0)? {
        exec.charge_native_universal(values.len(), 0)?;
        if !values.contains(&term) {
            if values.len() == values.capacity() {
                let capacity = values.len().checked_mul(2)?.max(4);
                exec.charge_native_universal(
                    values.len().checked_add(capacity)?,
                    capacity
                        .checked_mul(std::mem::size_of::<TermId>())?
                        .checked_mul(2)?,
                )?;
                values
                    .try_reserve_exact(capacity.checked_sub(values.len())?)
                    .ok()?;
            }
            values.push(term);
        }
    }
    Some(ground)
}

/// Compare borrowed descriptors before a value enters the proposed pool.
/// Neither a long incoming name nor a deep nested requested sort gets a fixed
/// scalar fee or an owned copy merely because the source sort was admitted.
pub(super) fn closed_source_sorts_equal(
    exec: &Executor,
    source: &Sort,
    requested: &Sort,
    depth: usize,
) -> Option<bool> {
    if depth > 32 {
        return None;
    }
    exec.charge_native_universal(1, 0)?;
    Some(match (source, requested) {
        (Sort::Bool, Sort::Bool) | (Sort::Int, Sort::Int) | (Sort::Real, Sort::Real) => true,
        (Sort::BitVec(a), Sort::BitVec(b)) => a.width == b.width,
        (Sort::Uninterpreted(a), Sort::Uninterpreted(b)) => {
            exec.charge_native_universal(a.len().checked_add(b.len())?.checked_add(1)?, 0)?;
            a == b
        }
        (Sort::Array(a), Sort::Array(b)) => {
            closed_source_sorts_equal(exec, &a.index_sort, &b.index_sort, depth + 1)?
                && closed_source_sorts_equal(exec, &a.element_sort, &b.element_sort, depth + 1)?
        }
        (Sort::Seq(a), Sort::Seq(b)) => closed_source_sorts_equal(exec, a, b, depth + 1)?,
        _ => false,
    })
}
