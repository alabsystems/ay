// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Recover a proof of a computed UNSAT from exact native original sources.
//! Working instances are never Assumes here. Every leaf comes from the same
//! source fragment producer as the working offers, and the complete candidate
//! is checked against ALL original roots before replacing a defective proof.

use super::*;
use ay_core::ProofStep;

#[cfg(test)]
mod tests;

const MAX_CLAUSES: usize = 4096;

impl Executor {
    pub(in crate::executor) fn replace_with_native_source_quantifier_refutation(
        &mut self,
        incumbent: &mut Proof,
    ) -> bool {
        // Cheap bounded routing only; the opaque receipt below remains the
        // authority. The cascade has already classified this incumbent as
        // unpublishable. Do not repeat its whole-proof screen outside this
        // producer's shared owner and one-attempt gate.
        let Some((_, _, roots)) = self.bounded_plain_unsat_query_scope(super::super::MAX_ROOTS)
        else {
            return false;
        };
        if self
            .charge_native_universal(roots.len().saturating_add(1), 0)
            .is_none()
            || !self
                .ctx
                .native_authored_originals_match_bounded(roots, super::super::MAX_ROOTS)
        {
            return false;
        }
        // This entry is in the computed-UNSAT repair cascade, not a decision
        // or model lane. The caller retains publishable incumbents unchanged.
        if let Some(candidate) = self.native_source_quantifier_refutation() {
            *incumbent = candidate;
            self.last_proof_term_overrides = None;
            // The prior proof may have had a translated assumption with no
            // authenticated spelling. Its replacement has different premises.
            // Let the ordinary authored surface gate check the actual document.
            self.publish_replacement_over_withheld_derivation(incumbent);
            return true;
        }
        false
    }

    fn native_source_quantifier_refutation(&mut self) -> Option<Proof> {
        self.native_universal_budget
            .borrow_mut()
            .claim_source_refutation()?;
        let initial = NativeUniversalSource::capture(self)?;
        let (source, choices, universals) = self.plan_native_source_offers(initial, false)?;
        if choices.is_empty() && universals.is_empty() {
            return None;
        }
        let mut closure = Closure::new(self);
        for &root in source.roots() {
            let ground = closure.exec.native_source_produce(|terms, _, progress| {
                contains_quantifier(terms, root, progress, 0, &mut 4096).map(|found| !found)
            })?;
            if ground {
                closure
                    .exec
                    .charge_native_universal(1, std::mem::size_of::<ProofStep>())?;
                let mut fragment = Proof::new();
                fragment.steps.try_reserve_exact(1).ok()?;
                fragment.add_assume(root, None);
                closure.fragment(fragment, root)?;
            }
        }
        for choice in &choices {
            closure.exec.charge_native_universal(1024, 16 * 1024)?;
            let (fragment, literal) =
                closure.exec.native_source_produce(|terms, _, progress| {
                    choice_fragment(terms, choice, progress)
                })?;
            closure.fragment(fragment, literal)?;
        }
        let mut count = choices.len();
        for universal in &universals {
            let q = universal.quantified();
            let (data, _) = closure.exec.native_source_produce(|terms, _, progress| {
                terms
                    .try_copy_native_proof_node_with_progress(q, progress)
                    .ok()
            })?;
            let TermData::Forall(bindings, body, _) = data else {
                return None;
            };
            let [(binder, sort)] = bindings.as_slice() else {
                return None;
            };
            let mut values = Vec::new();
            closure
                .exec
                .seed_native_source_offer_values(sort, &mut values)?;
            closure
                .exec
                .seed_native_universal_source_values(&source, sort, &mut values)?;
            // The negative goal's witness is a proposed value, never evidence
            // that its full membership guard holds.
            for choice in &choices {
                closure.exec.charge_native_universal(values.len(), 0)?;
                if super::super::instances::closed_source_sorts_equal(
                    closure.exec,
                    closure.exec.ctx.terms.sort(choice.witness),
                    sort,
                    0,
                )? && !values.contains(&choice.witness)
                {
                    closure.exec.reserve_native_source_vector(&mut values)?;
                    values.push(choice.witness);
                }
            }
            closure.choice_values(&choices, sort, &mut values)?;
            for value in values.into_iter().take(16) {
                if count >= 64 {
                    break;
                }
                closure.exec.charge_native_universal(1024, 16 * 1024)?;
                let (fragment, exact) =
                    closure.exec.native_source_produce(|terms, _, progress| {
                        universal_fragment(terms, universal, q, body, binder, value, progress)
                    })?;
                closure.fragment(fragment, exact)?;
                count += 1;
            }
        }
        if !source.is_current(closure.exec) {
            return None;
        }
        closure.clausify()?;
        closure.propagate()?;
        let Closure {
            exec,
            proof: candidate,
            clauses,
            roots,
            visited,
        } = closure;
        // Drop temporary planning storage before the final checked/current
        // bookends; no plan-local heap escapes with the proof.
        drop((clauses, roots, visited));
        let declarations = exec
            .datatype_decls_for_strict_proof_with_progress(&mut |w, b| {
                exec.charge_native_universal(w, b).is_some()
            })
            .ok()?;
        let selectors = exec
            .ctor_selector_decls_for_strict_proof_with_progress(&mut |w, b| {
                exec.charge_native_universal(w, b).is_some()
            })
            .ok()?;
        let signatures = exec
            .datatype_member_signatures_for_strict_proof_with_progress(&mut |w, b| {
                exec.charge_native_universal(w, b).is_some()
            })
            .ok()??;
        let quality = ay_proof::check_proof_strict_with_typed_context_and_progress(
            &candidate,
            &exec.ctx.terms,
            Some(&declarations),
            Some(&selectors),
            &signatures,
            Some(source.roots()),
            &mut |w, b| exec.charge_native_universal(w, b).is_some(),
        )
        .ok()?;
        (quality.is_complete() && source.is_current(exec)).then_some(candidate)
    }
}

struct Clause {
    literals: Vec<TermId>,
    id: ProofId,
}

struct Closure<'e> {
    exec: &'e mut Executor,
    proof: Proof,
    clauses: Vec<Clause>,
    roots: Vec<TermId>,
    visited: Vec<TermId>,
}

impl<'e> Closure<'e> {
    fn new(exec: &'e mut Executor) -> Self {
        Self {
            exec,
            proof: Proof::new(),
            clauses: Vec::new(),
            roots: Vec::new(),
            visited: Vec::new(),
        }
    }

    fn pay(&self, work: usize, bytes: usize) -> Option<()> {
        self.exec.charge_native_universal(work, bytes)
    }

    fn ids<T: Copy>(&self, values: &[T]) -> Option<Vec<T>> {
        self.pay(
            values.len(),
            values.len().checked_mul(std::mem::size_of::<T>())?,
        )?;
        let mut result = Vec::new();
        result.try_reserve_exact(values.len()).ok()?;
        result.extend_from_slice(values);
        Some(result)
    }

    fn step(&mut self, step: ProofStep) -> Option<ProofId> {
        self.exec
            .reserve_native_source_vector(&mut self.proof.steps)?;
        u32::try_from(self.proof.steps.len()).ok()?;
        Some(self.proof.add_step(step))
    }

    fn rule(
        &mut self,
        rule: AletheRule,
        literals: &[TermId],
        premises: &[ProofId],
        args: &[TermId],
    ) -> Option<ProofId> {
        let clause = self.ids(literals)?;
        let premises = self.ids(premises)?;
        let args = self.ids(args)?;
        self.step(ProofStep::Step {
            rule,
            clause,
            premises,
            args,
        })
    }

    fn resolve(
        &mut self,
        literals: &[TermId],
        pivot: TermId,
        left: ProofId,
        right: ProofId,
    ) -> Option<ProofId> {
        let clause = self.ids(literals)?;
        self.step(ProofStep::Resolution {
            clause,
            pivot,
            clause1: left,
            clause2: right,
        })
    }

    fn negative(&mut self, term: TermId) -> Option<TermId> {
        self.exec
            .native_source_produce(|terms, _, progress| not(terms, term, progress))
    }

    fn complement(&mut self, term: TermId) -> Option<TermId> {
        self.pay(1, 0)?;
        match self.exec.ctx.terms.get(term) {
            TermData::Not(inner) => Some(*inner),
            _ => self.negative(term),
        }
    }

    /// Leaves are borrowed identities, not payloads to pass through the
    /// compound-node copy API. Reuse the paid raw admission for exact stored
    /// scalar kind/sort/name validity, including malformed checker snapshots.
    fn borrowed_leaf(&self, term: TermId) -> Option<bool> {
        self.pay(1, 0)?;
        self.exec.ctx.terms.entry_stamp(term)?;
        match self.exec.ctx.terms.get(term) {
            TermData::Var(..) | TermData::Const(..) => {
                self.exec.admit_native_universal_terms(&[term])?;
                Some(true)
            }
            _ => Some(false),
        }
    }

    /// Ground terms of the independently emitted witness matrix may select
    /// further universal values (for example f(w)). They are proposals only;
    /// no function value or membership fact is inferred by this walk.
    fn choice_values(
        &mut self,
        choices: &[Choice],
        expected: &Sort,
        values: &mut Vec<TermId>,
    ) -> Option<()> {
        let mut pending = Vec::new();
        for choice in choices {
            self.exec.admit_native_universal_terms(&[choice.raw])?;
            self.exec.reserve_native_source_vector(&mut pending)?;
            pending.push((choice.raw, 0usize));
        }
        let mut left = 4096usize;
        while let Some((term, depth)) = pending.pop() {
            left = left.checked_sub(1)?;
            if depth > 64 {
                return None;
            }
            // Classify/validate borrowed leaves before selecting a value or
            // invoking the intentionally compound-only owned-copy API.
            let leaf = self.borrowed_leaf(term)?;
            self.pay(values.len().checked_add(1)?, 0)?;
            if super::super::instances::closed_source_sorts_equal(
                self.exec,
                self.exec.ctx.terms.sort(term),
                expected,
                0,
            )? && !values.contains(&term)
            {
                self.exec.reserve_native_source_vector(values)?;
                values.push(term);
            }
            if leaf {
                continue;
            }
            let (data, _) = self.exec.native_source_produce(|terms, _, progress| {
                terms
                    .try_copy_native_proof_node_with_progress(term, progress)
                    .ok()
            })?;
            let mut push = |child| -> Option<()> {
                self.exec.reserve_native_source_vector(&mut pending)?;
                pending.push((child, depth + 1));
                Some(())
            };
            match data {
                TermData::App(_, children) => {
                    for child in children {
                        push(child)?;
                    }
                }
                TermData::Not(child) => push(child)?,
                TermData::Ite(c, t, e) => {
                    for child in [c, t, e] {
                        push(child)?;
                    }
                }
                TermData::Var(..) | TermData::Const(..) => {}
                _ => return None,
            }
        }
        Some(())
    }

    fn fragment(&mut self, mut fragment: Proof, target: TermId) -> Option<()> {
        self.exec.admit_native_universal_terms(&[target])?;
        if !fragment.named_steps.is_empty() {
            return None;
        }
        let offset = u32::try_from(self.proof.steps.len()).ok()?;
        let last = fragment.steps.len().checked_sub(1)?;
        // All fragments have exact last units; the whole candidate remains
        // untrusted planning data until the full typed original-scope replay.
        let terminal_matches = match &fragment.steps[last] {
            ProofStep::Assume(root) => *root == target,
            ProofStep::Resolution { clause, .. } | ProofStep::Step { clause, .. } => {
                clause.as_slice() == [target]
            }
            _ => false,
        };
        if !terminal_matches {
            return None;
        }
        for (index, step) in fragment.steps.iter_mut().enumerate() {
            self.pay(1, 0)?;
            match step {
                ProofStep::Assume(_) | ProofStep::TheoryLemma { .. } => {}
                ProofStep::Resolution {
                    clause,
                    clause1,
                    clause2,
                    ..
                } => {
                    self.pay(clause.len().checked_add(2)?, 0)?;
                    if clause1.0 as usize >= index || clause2.0 as usize >= index {
                        return None;
                    }
                    clause1.0 = clause1.0.checked_add(offset)?;
                    clause2.0 = clause2.0.checked_add(offset)?;
                }
                ProofStep::Step {
                    clause,
                    premises,
                    args,
                    ..
                } => {
                    self.pay(
                        clause
                            .len()
                            .checked_add(premises.len())?
                            .checked_add(args.len())?,
                        0,
                    )?;
                    for id in premises {
                        if id.0 as usize >= index {
                            return None;
                        }
                        id.0 = id.0.checked_add(offset)?;
                    }
                }
                _ => return None,
            }
        }
        for step in fragment.steps {
            self.step(step)?;
        }
        let id = ProofId(offset.checked_add(u32::try_from(last).ok()?)?);
        self.record(&[target], id)?;
        self.exec.reserve_native_source_vector(&mut self.roots)?;
        self.roots.push(target);
        Some(())
    }

    fn record(&mut self, input: &[TermId], mut id: ProofId) -> Option<()> {
        if self.clauses.len() >= MAX_CLAUSES {
            return None;
        }
        let mut clause = self.ids(input)?;
        // Normalize only raw double-negation shells, with an explicit checked
        // propositional bridge. Theory atoms remain opaque and byte-identical.
        loop {
            let mut pair = None;
            for (index, &literal) in clause.iter().enumerate() {
                self.pay(1, 0)?;
                if let TermData::Not(inner) = self.exec.ctx.terms.get(literal) {
                    if let TermData::Not(atom) = self.exec.ctx.terms.get(*inner) {
                        pair = Some((index, literal, *atom));
                        break;
                    }
                }
            }
            let Some((_index, literal, atom)) = pair else {
                break;
            };
            let negative = self.negative(literal)?;
            let bridge_clause = self.ids(&[negative, atom])?;
            self.pay(4, 4)?;
            let bridge = self.step(ProofStep::TheoryLemma {
                theory: "bool".into(),
                clause: bridge_clause,
                farkas: None,
                kind: TheoryLemmaKind::BoolTautology,
                lia: None,
            })?;
            for value in &mut clause {
                self.pay(1, 0)?;
                if *value == literal {
                    *value = atom;
                }
            }
            id = self.resolve(&clause, literal, id, bridge)?;
        }
        let mut unique = self.ids::<TermId>(&[])?;
        for &literal in &clause {
            self.pay(unique.len().checked_add(1)?, 0)?;
            if !unique.contains(&literal) {
                self.exec.reserve_native_source_vector(&mut unique)?;
                unique.push(literal);
            }
        }
        if unique.len() != clause.len() {
            id = self.rule(AletheRule::Contraction, &unique, &[id], &[])?;
        }
        self.exec.reserve_native_source_vector(&mut self.clauses)?;
        self.clauses.push(Clause {
            literals: unique,
            id,
        });
        Some(())
    }

    fn seed(&mut self, rule: AletheRule, literals: &[TermId], args: &[TermId]) -> Option<()> {
        let id = self.rule(rule, literals, &[], args)?;
        self.record(literals, id)
    }

    fn clausify(&mut self) -> Option<()> {
        let roots = self.ids(&self.roots)?;
        let mut left = 4096;
        for root in roots {
            self.walk(root, 0, &mut left)?;
        }
        let yes = boolean_id(&self.exec.ctx.terms, true)?;
        let no = boolean_id(&self.exec.ctx.terms, false)?;
        let negative_false = self.negative(no)?;
        self.seed(AletheRule::True, &[yes], &[])?;
        self.seed(AletheRule::False, &[negative_false], &[])
    }

    fn walk(&mut self, term: TermId, depth: usize, left: &mut usize) -> Option<()> {
        *left = left.checked_sub(1)?;
        if depth > 64 {
            return None;
        }
        self.pay(1, 0)?;
        self.exec.ctx.terms.entry_stamp(term)?;
        if self.exec.ctx.terms.sort(term) != &Sort::Bool {
            return None;
        }
        if self.borrowed_leaf(term)? {
            return Some(());
        }
        self.pay(self.visited.len().checked_add(1)?, 0)?;
        if self.visited.contains(&term) {
            return Some(());
        }
        self.exec.reserve_native_source_vector(&mut self.visited)?;
        self.visited.push(term);
        let (data, sort) = self.exec.native_source_produce(|terms, _, progress| {
            terms
                .try_copy_native_proof_node_with_progress(term, progress)
                .ok()
        })?;
        if sort != Sort::Bool {
            return None;
        }
        match data {
            TermData::Not(child) => self.walk(child, depth + 1, left)?,
            TermData::Ite(c, t, e) => {
                for child in [c, t, e] {
                    self.walk(child, depth + 1, left)?;
                }
                let nt = self.complement(t)?;
                let ne = self.complement(e)?;
                let nc = self.complement(c)?;
                let nn = self.negative(term)?;
                for (rule, clause) in [
                    (AletheRule::ItePos1, [nn, c, e]),
                    (AletheRule::ItePos2, [nn, nc, t]),
                    (AletheRule::IteNeg1, [term, c, ne]),
                    (AletheRule::IteNeg2, [term, nc, nt]),
                ] {
                    self.seed(rule, &clause, &[])?;
                }
            }
            TermData::App(Symbol::Named(name), args) if name == "and" || name == "or" => {
                for &child in &args {
                    self.walk(child, depth + 1, left)?;
                }
                let nn = self.negative(term)?;
                if name == "and" {
                    for (i, &child) in args.iter().enumerate() {
                        self.seed(
                            AletheRule::AndPos(u32::try_from(i).ok()?),
                            &[nn, child],
                            &[term],
                        )?;
                    }
                    let mut clause = self.ids(&[term])?;
                    for &child in &args {
                        let n = self.complement(child)?;
                        self.exec.reserve_native_source_vector(&mut clause)?;
                        clause.push(n);
                    }
                    self.seed(AletheRule::AndNeg, &clause, &[term])?;
                } else {
                    let mut clause = self.ids(&[nn])?;
                    for &child in &args {
                        self.exec.reserve_native_source_vector(&mut clause)?;
                        clause.push(child);
                    }
                    self.seed(AletheRule::OrPos(0), &clause, &[])?;
                    for &child in &args {
                        let n = self.complement(child)?;
                        self.seed(AletheRule::OrNeg, &[term, n], &[])?;
                    }
                }
            }
            TermData::App(Symbol::Named(name), args) if name == "=>" && args.len() == 2 => {
                let (a, b) = (args[0], args[1]);
                for child in [a, b] {
                    self.walk(child, depth + 1, left)?;
                }
                let nn = self.negative(term)?;
                let na = self.complement(a)?;
                let nb = self.complement(b)?;
                self.seed(AletheRule::ImpliesPos, &[nn, na, b], &[])?;
                self.seed(AletheRule::ImpliesNeg1, &[term, a], &[])?;
                self.seed(AletheRule::ImpliesNeg2, &[term, nb], &[])?;
            }
            TermData::App(Symbol::Named(name), args)
                if name == "="
                    && args.len() == 2
                    && self.exec.ctx.terms.sort(args[0]) == &Sort::Bool
                    && self.exec.ctx.terms.sort(args[1]) == &Sort::Bool =>
            {
                let (a, b) = (args[0], args[1]);
                for child in [a, b] {
                    self.walk(child, depth + 1, left)?;
                }
                let nn = self.negative(term)?;
                let na = self.complement(a)?;
                let nb = self.complement(b)?;
                for (rule, clause) in [
                    (AletheRule::EquivPos1, [nn, a, nb]),
                    (AletheRule::EquivPos2, [nn, na, b]),
                    (AletheRule::EquivNeg1, [term, a, b]),
                    (AletheRule::EquivNeg2, [term, na, nb]),
                ] {
                    self.seed(rule, &clause, &[])?;
                }
            }
            TermData::Forall(..) | TermData::Exists(..) | TermData::Let(..) => return None,
            _ => {} // Exact QF theory atoms receive no extra law.
        }
        Some(())
    }

    fn opposite(&self, a: TermId, b: TermId) -> bool {
        matches!(self.exec.ctx.terms.get(a), TermData::Not(inner) if *inner==b)
            || matches!(self.exec.ctx.terms.get(b), TermData::Not(inner) if *inner==a)
    }

    fn propagate(&mut self) -> Option<()> {
        let mut units: Vec<(TermId, ProofId)> = Vec::new();
        loop {
            let mut changed = false;
            for index in 0..self.clauses.len() {
                self.pay(1, 0)?;
                if self.clauses[index].literals.is_empty() {
                    return Some(());
                }
                if self.clauses[index].literals.len() == 1 {
                    let literal = self.clauses[index].literals[0];
                    self.pay(units.len(), 0)?;
                    if !units.iter().any(|&(old, _)| old == literal) {
                        for &(old, id) in &units {
                            self.pay(1, 0)?;
                            if self.opposite(old, literal) {
                                self.resolve(&[], old, id, self.clauses[index].id)?;
                                return Some(());
                            }
                        }
                        self.exec.reserve_native_source_vector(&mut units)?;
                        units.push((literal, self.clauses[index].id));
                        changed = true;
                    }
                    continue;
                }
                for &(unit, unit_id) in &units {
                    self.pay(self.clauses[index].literals.len(), 0)?;
                    if let Some(position) = self.clauses[index]
                        .literals
                        .iter()
                        .position(|&lit| self.opposite(lit, unit))
                    {
                        let mut next = self.ids(&self.clauses[index].literals)?;
                        self.pay(next.len(), 0)?;
                        next.remove(position);
                        let id = self.resolve(&next, unit, self.clauses[index].id, unit_id)?;
                        self.clauses[index] = Clause { literals: next, id };
                        changed = true;
                        if self.clauses[index].literals.is_empty() {
                            return Some(());
                        }
                    }
                }
            }
            if !changed {
                return None;
            }
        }
    }
}
