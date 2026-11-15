// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Guarded ground instances of an authored universal, derived for producers
//! that assert the instance with its closed guards already discharged.
//!
//! THE GAP. The finite-domain expander (`expand_finite_domains`) replaces an
//! authored top-level `forall` by the conjunction of its instances over the
//! guard range, each folded by the simplifying constructors: under
//! `(forall ((i (_ BitVec 8))) (=> (bvult i #x09) (= (select a i) (f x))))`
//! the instance at `#x04` is asserted as `(= (f x) (select a #x04))`, its
//! closed guard `(bvult #x04 #x09)` evaluated away. That lane recorded the
//! instance values (`QuantExpansionRecord`) but no derivation, so the ground
//! refutation assumed the expansion and strict certification withheld the
//! verdict: the refuting lane ended in an underived `trust`, and only the
//! authored replacement cascade could rebuild a certificate afterwards
//! (9896793af).
//!
//! THE DERIVATION. Each folded instance is derived the way the E-matching
//! lane derives an exact one (`add_forall_instantiated_assertion`, which an
//! unguarded instance goes through), and with the same guard-discharge steps
//! the cascade's instance closure emits:
//!
//! * `forall_inst` of the authored universal at the recorded values. Its
//!   conclusion is the exact raw substitution `subst_vars_exact_qf`, so the
//!   strict checker's `forall_inst` validator re-derives the instance from the
//!   universal and the values; nothing is recorded as `forall_inst` that is
//!   not literally an instance;
//! * `or`, then one resolution per disjunct other than the asserted one,
//!   each refuted by `evaluate` of a closed comparison over LITERAL operands
//!   the checker's own ground evaluator re-derives
//!   ([`closed_comparison_over_literals`], [`emit_evaluated_unit`]);
//! * `symm`, when the simplifying constructors oriented the asserted equality
//!   the other way round (`(= #x00 (f #x04))` for the body's `(= (f i) #x00)`),
//!   or a checked linear implication when ground arithmetic was folded.
//!
//! Anything else declines before a step is emitted
//! ([`GuardedInstance::plan`]): a term that is neither the instance nor one
//! of its disjuncts up to that orientation, a duplicate disjunct, or a guard
//! that is not a closed literal comparison (an open bound, a signed or nested
//! operator). The producer keeps its assertion either way; a declined
//! instance only stays underived, which is what every instance was before.

use super::*;

impl ProofTracker {
    /// Derive the asserted term of `instance` (a checked plan, see
    /// [`GuardedInstance::plan`]) from its authored universal, and index it
    /// as a `Generic` singleton so that `add_assumption` of that term reuses
    /// the derivation instead of assuming it.
    ///
    /// An unguarded instance goes through
    /// [`Self::add_forall_instantiated_assertion`], the E-matching lane's own
    /// entry; a guarded one gets [`GuardedInstance::emit`]. Returns the unit's
    /// step, or `None` when tracking is off or the universal has no `assume`.
    pub(crate) fn add_forall_guarded_instance_assertion(
        &mut self,
        terms: &mut TermStore,
        instance: &GuardedInstance,
    ) -> Option<ProofId> {
        if !self.enabled {
            return None;
        }
        if let Some(id) = self
            .lemma_map
            .get(TheoryLemmaKind::Generic, &[instance.target], None)
        {
            return Some(id);
        }
        let derived = if instance.guards.is_empty() {
            let unit = self.add_forall_instantiated_assertion(
                terms,
                instance.quantified,
                &instance.values,
                instance.instance,
            )?;
            instance.derive_target(&mut self.proof, terms, unit)
        } else {
            let source = self.add_assumption(instance.quantified, None)?;
            instance.emit(&mut self.proof, terms, source)
        };
        self.lemma_map.insert(
            LemmaKey::new(TheoryLemmaKind::Generic, &[instance.target], None),
            derived,
        );
        Some(derived)
    }

    /// Derive the conjunction `conjunction` from its conjuncts when every one
    /// of them is already a derived `Generic` unit: `and_neg` plus one
    /// resolution per conjunct. Indexed like every derived unit, so that
    /// `add_assumption(conjunction)` reuses it.
    ///
    /// Returns `None` (emitting nothing) unless `conjunction` is an `and` of
    /// distinct conjuncts that all have a derivation.
    pub(crate) fn add_conjunction_of_derived_units(
        &mut self,
        terms: &mut TermStore,
        conjunction: TermId,
    ) -> Option<ProofId> {
        if !self.enabled {
            return None;
        }
        if let Some(id) = self
            .lemma_map
            .get(TheoryLemmaKind::Generic, &[conjunction], None)
        {
            return Some(id);
        }
        let TermData::App(sym, conjuncts) = terms.get(conjunction).clone() else {
            return None;
        };
        if sym.name() != "and" || conjuncts.len() < 2 {
            return None;
        }
        let mut units = Vec::with_capacity(conjuncts.len());
        for (position, &conjunct) in conjuncts.iter().enumerate() {
            if conjuncts[..position].contains(&conjunct) {
                return None;
            }
            units.push(
                self.lemma_map
                    .get(TheoryLemmaKind::Generic, &[conjunct], None)?,
            );
        }
        let mut clause = Vec::with_capacity(conjuncts.len() + 1);
        clause.push(conjunction);
        for &conjunct in &conjuncts {
            clause.push(terms.mk_not_raw(conjunct));
        }
        let mut current = self.proof.add_rule_step(
            AletheRule::AndNeg,
            clause.clone(),
            Vec::new(),
            vec![conjunction],
        );
        for (&conjunct, unit) in conjuncts.iter().zip(units) {
            let _ = clause.remove(1);
            current = self
                .proof
                .add_resolution(clause.clone(), conjunct, current, unit);
        }
        self.lemma_map.insert(
            LemmaKey::new(TheoryLemmaKind::Generic, &[conjunction], None),
            current,
        );
        Some(current)
    }
}

/// How one disjunct of an instance is removed by resolution.
#[derive(Clone, Debug)]
struct ClosedGuard {
    /// The instance disjunct being removed.
    disjunct: TermId,
    /// Resolution pivot: the atom of `disjunct`.
    pivot: TermId,
    /// The closed literal refuting `disjunct`, derived by `evaluate`.
    complement: TermId,
}

/// A checked plan deriving an asserted term from one exact instance of an
/// authored universal.
#[derive(Clone, Debug)]
pub(crate) struct GuardedInstance {
    /// The universal (a `forall`), assumed as the derivation's only source.
    quantified: TermId,
    /// Binder values in binding order (`forall_inst` `:args`).
    values: Vec<TermId>,
    /// The exact raw substitution of the body at `values`.
    instance: TermId,
    /// The asserted term being derived.
    target: TermId,
    /// The raw instance itself or the disjunct its closed guards leave.
    kept: TermId,
    /// Empty exactly when `kept` is the whole instance.
    guards: Vec<ClosedGuard>,
    conclusion: ConclusionBridge,
}

#[derive(Clone, Copy, Debug)]
enum ConclusionBridge {
    Exact,
    SymmetricEquality,
    LinearArithmetic,
}

impl GuardedInstance {
    /// Plan the derivation of `target` from the exact instance of
    /// `quantified` at `values`: `target` is that instance, or one of its
    /// disjuncts whose other disjuncts are closed literal comparisons that
    /// evaluate to `false`, in either case possibly with its equality's two
    /// sides swapped.
    ///
    /// `None` when `quantified` is not a `forall` whose binders `values`
    /// match in number and sort, when the substituted body is not
    /// quantifier-free, when `target` is neither the instance nor one of its
    /// disjuncts (up to the orientation of an equality), when the disjuncts
    /// are not distinct, or when some other disjunct is not refuted by a
    /// closed literal comparison. Nothing here is authority: the strict
    /// checker re-derives the substitution, every `evaluate` and every
    /// resolution of the emitted steps.
    pub(crate) fn plan(
        terms: &mut TermStore,
        quantified: TermId,
        values: &[TermId],
        target: TermId,
    ) -> Option<Self> {
        let TermData::Forall(bindings, body, _) = terms.get(quantified).clone() else {
            return None;
        };
        if bindings.is_empty() || bindings.len() != values.len() {
            return None;
        }
        let mut substitution = HashMap::default();
        for ((name, sort), &value) in bindings.iter().zip(values) {
            if terms.sort(value) != sort || substitution.insert(name.clone(), value).is_some() {
                return None;
            }
        }
        let instance = crate::ematching::subst_vars_exact_qf(terms, body, &substitution)?;
        let swapped = swapped_equality(terms, target);
        let unguarded = |kept, conclusion| Self {
            quantified,
            values: values.to_vec(),
            instance,
            target,
            kept,
            guards: Vec::new(),
            conclusion,
        };
        if let Some(bridge) = conclusion_bridge(terms, instance, target, swapped) {
            return Some(unguarded(instance, bridge));
        }
        let TermData::App(sym, disjuncts) = terms.get(instance).clone() else {
            return None;
        };
        if sym.name() != "or" || disjuncts.len() < 2 {
            return None;
        }
        for (position, disjunct) in disjuncts.iter().enumerate() {
            if disjuncts[..position].contains(disjunct) {
                return None;
            }
        }
        let (kept, bridge) = if disjuncts.contains(&target) {
            (target, ConclusionBridge::Exact)
        } else if let Some(swapped) = swapped.filter(|swapped| disjuncts.contains(swapped)) {
            (swapped, ConclusionBridge::SymmetricEquality)
        } else {
            disjuncts.iter().find_map(|&disjunct| {
                conclusion_bridge(terms, disjunct, target, None).map(|bridge| (disjunct, bridge))
            })?
        };
        let mut guards = Vec::with_capacity(disjuncts.len() - 1);
        for &disjunct in &disjuncts {
            if disjunct == kept {
                continue;
            }
            let (pivot, complement) = match terms.get(disjunct) {
                TermData::Not(atom) => (*atom, *atom),
                _ => (disjunct, terms.mk_not_raw(disjunct)),
            };
            if !closed_guard_over_literals(terms, complement)
                || !ay_proof::recognize_ground_evaluate(terms, complement)
            {
                return None;
            }
            guards.push(ClosedGuard {
                disjunct,
                pivot,
                complement,
            });
        }
        Some(Self {
            guards,
            ..unguarded(kept, bridge)
        })
    }

    /// Emit the derivation into `proof`, whose step `source` is the unit
    /// clause of the universal: `forall_inst`, `or`, resolution against
    /// `source`; then, for a guarded instance, `or` and one resolution per
    /// guard against its `evaluate`d complement; finally `symm` when the
    /// asserted equality is the swapped one. Returns the unit of `target`.
    pub(crate) fn emit(
        &self,
        proof: &mut Proof,
        terms: &mut TermStore,
        source: ProofId,
    ) -> ProofId {
        let not_quantified = terms.mk_not_raw(self.quantified);
        let implication = terms.mk_app(
            Symbol::named("or"),
            [not_quantified, self.instance],
            Sort::Bool,
        );
        let instantiated = proof.add_rule_step(
            AletheRule::ForallInst,
            vec![implication],
            Vec::new(),
            self.values.clone(),
        );
        let clausified = proof.add_rule_step(
            AletheRule::Or,
            vec![not_quantified, self.instance],
            vec![instantiated],
            Vec::new(),
        );
        let mut current =
            proof.add_resolution(vec![self.instance], self.quantified, clausified, source);
        if let TermData::App(_, disjuncts) = terms.get(self.instance).clone() {
            if !self.guards.is_empty() {
                let mut residual = disjuncts;
                current = proof.add_rule_step(
                    AletheRule::Or,
                    residual.clone(),
                    vec![current],
                    Vec::new(),
                );
                for guard in &self.guards {
                    let refuted = emit_evaluated_unit(proof, terms, guard.complement);
                    residual.retain(|&literal| literal != guard.disjunct);
                    current = proof.add_resolution(residual.clone(), guard.pivot, current, refuted);
                }
                debug_assert_eq!(residual, [self.kept]);
            }
        }
        self.derive_target(proof, terms, current)
    }

    fn derive_target(&self, proof: &mut Proof, terms: &mut TermStore, kept: ProofId) -> ProofId {
        match self.conclusion {
            ConclusionBridge::Exact => kept,
            ConclusionBridge::SymmetricEquality => {
                proof.add_rule_step(AletheRule::Symm, vec![self.target], vec![kept], Vec::new())
            }
            ConclusionBridge::LinearArithmetic => {
                let complement = terms.mk_not_raw(self.kept);
                let implication = proof.add_theory_lemma_with_farkas(
                    "LRA",
                    vec![complement, self.target],
                    FarkasAnnotation::from_ints(&[1, 1]),
                );
                proof.add_resolution(vec![self.target], self.kept, implication, kept)
            }
        }
    }
}

fn conclusion_bridge(
    terms: &TermStore,
    from: TermId,
    to: TermId,
    swapped: Option<TermId>,
) -> Option<ConclusionBridge> {
    if from == to {
        return Some(ConclusionBridge::Exact);
    }
    if Some(from) == swapped {
        return Some(ConclusionBridge::SymmetricEquality);
    }
    for term in [from, to] {
        let TermData::App(Symbol::Named(name), args) = terms.get(term) else {
            return None;
        };
        let [left, right] = args.as_slice() else {
            return None;
        };
        if !matches!(name.as_str(), "<=" | "<" | ">=" | ">")
            || terms.sort(*left) != &Sort::Int
            || terms.sort(*right) != &Sort::Int
        {
            return None;
        }
    }
    ay_core::proof_validation::verify_farkas_conflict_lits_linear(
        terms,
        &[TheoryLit::new(from, true), TheoryLit::new(to, false)],
        &FarkasAnnotation::from_ints(&[1, 1]),
    )
    .ok()?;
    Some(ConclusionBridge::LinearArithmetic)
}

fn closed_guard_over_literals(terms: &TermStore, literal: TermId) -> bool {
    if let TermData::App(Symbol::Named(name), conjuncts) = terms.get(literal) {
        if name == "and" {
            return conjuncts.len() >= 2
                && conjuncts
                    .iter()
                    .all(|&atom| closed_comparison_over_literals(terms, atom));
        }
    }
    closed_comparison_over_literals(terms, literal)
}

/// `(= b a)` for an equality `(= a b)` between two distinct terms, built raw
/// so the swap survives: the `symm` step concluding it is re-derived by the
/// strict checker from its premise.
fn swapped_equality(terms: &mut TermStore, term: TermId) -> Option<TermId> {
    let TermData::App(sym, args) = terms.get(term) else {
        return None;
    };
    let [a, b] = args.as_slice() else {
        return None;
    };
    if sym.name() != "=" || a == b {
        return None;
    }
    let (a, b) = (*a, *b);
    Some(terms.mk_app(Symbol::named("="), [b, a], Sort::Bool))
}

/// Whether `literal` (or its atom, under one negation) is a comparison applied
/// directly to literal constants: the only closed guards a guarded instance
/// refutes by `evaluate`. Pinned carcara 1.1.0 evaluates exactly these as
/// SMT-LIB defines them (unsigned `bvult`/`bvule`/`bvugt`/`bvuge` over the
/// stored value, `=`/`distinct` by constant identity, arithmetic comparisons
/// over exact numerals). Refusing nested operators keeps every signed
/// operation and `extract` — which it evaluates wrongly — out of the emitted
/// steps, even where AY's own evaluator would accept them.
pub(crate) fn closed_comparison_over_literals(terms: &TermStore, literal: TermId) -> bool {
    let atom = match terms.get(literal) {
        TermData::Not(atom) => *atom,
        _ => literal,
    };
    let TermData::App(Symbol::Named(name), args) = terms.get(atom) else {
        return false;
    };
    matches!(
        name.as_str(),
        "=" | "distinct" | "bvult" | "bvule" | "bvugt" | "bvuge" | "<" | "<=" | ">" | ">="
    ) && args.len() >= 2
        && args
            .iter()
            .all(|&arg| matches!(terms.get(arg), TermData::Const(_)))
}

/// `(cl literal)` for a closed literal: `evaluate` of its atom to `true` or
/// `false`, then `equiv_pos1`/`equiv_pos2` and the `true`/`false` axiom.
pub(crate) fn emit_evaluated_unit(
    proof: &mut Proof,
    terms: &mut TermStore,
    literal: TermId,
) -> ProofId {
    if let TermData::Not(atom) = terms.get(literal) {
        let atom = *atom;
        let false_term = terms.false_term();
        let equality = terms.mk_app(Symbol::named("="), [atom, false_term], Sort::Bool);
        let evaluated =
            proof.add_rule_step(AletheRule::Evaluate, vec![equality], Vec::new(), Vec::new());
        let not_equality = terms.mk_not_raw(equality);
        let tautology = proof.add_rule_step(
            AletheRule::EquivPos2,
            vec![not_equality, literal, false_term],
            Vec::new(),
            Vec::new(),
        );
        let with_false =
            proof.add_resolution(vec![literal, false_term], equality, tautology, evaluated);
        let not_false = terms.mk_not_raw(false_term);
        let axiom = proof.add_rule_step(AletheRule::False, vec![not_false], Vec::new(), Vec::new());
        return proof.add_resolution(vec![literal], false_term, axiom, with_false);
    }
    let true_term = terms.true_term();
    let equality = terms.mk_app(Symbol::named("="), [literal, true_term], Sort::Bool);
    let evaluated =
        proof.add_rule_step(AletheRule::Evaluate, vec![equality], Vec::new(), Vec::new());
    let not_equality = terms.mk_not_raw(equality);
    let not_true = terms.mk_not_raw(true_term);
    let tautology = proof.add_rule_step(
        AletheRule::EquivPos1,
        vec![not_equality, literal, not_true],
        Vec::new(),
        Vec::new(),
    );
    let with_true = proof.add_resolution(vec![literal, not_true], equality, tautology, evaluated);
    let axiom = proof.add_rule_step(AletheRule::True, vec![true_term], Vec::new(), Vec::new());
    proof.add_resolution(vec![literal], true_term, with_true, axiom)
}

#[cfg(test)]
mod tests;
