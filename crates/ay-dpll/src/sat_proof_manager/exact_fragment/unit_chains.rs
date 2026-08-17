// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use ay_core::kani_compat::DetHashMap as HashMap;
use ay_core::{
    AletheRule, Constant, Proof, ProofId, ProofStep, Sort, Symbol, TermData, TermId, TermStore,
    TheoryLemmaKind,
};
use ay_sat::{ResolutionValidationError, ResolutionValidationResource};

use super::types::OrFoldUnitPlan;
use super::{exact_checked_add, exact_checked_mul};
use crate::sat_proof_manager::{
    FragmentInstanceDerivation, FragmentSkolemDerivation, SatProofManager,
};

const MAX_OR_FOLD_UNITS: usize = 1024;
const MAX_OR_FOLD_HOPS: usize = 8;

impl SatProofManager<'_> {
    pub(in crate::sat_proof_manager) fn unit_chain_charge(
        steps: usize,
        retained_term_slots: usize,
    ) -> Result<(usize, usize), ResolutionValidationError> {
        let work = exact_checked_add(
            exact_checked_mul(retained_term_slots, 4, ResolutionValidationResource::Work)?,
            steps,
            ResolutionValidationResource::Work,
        )?;
        let bytes = exact_checked_add(
            exact_checked_mul(
                retained_term_slots,
                256,
                ResolutionValidationResource::Bytes,
            )?,
            exact_checked_mul(steps, 512, ResolutionValidationResource::Bytes)?,
            ResolutionValidationResource::Bytes,
        )?;
        Ok((work, bytes))
    }

    /// Exact closed Boolean tautology unit: `true` or `(not false)`. The
    /// emitted premiseless step is independently re-validated by the strict
    /// checker's exhaustive bounded evaluator, so recognition here is only a
    /// cheap producer-side filter, never authority.
    pub(in crate::sat_proof_manager) fn is_closed_bool_tautology_unit(
        terms: &TermStore,
        unit: TermId,
    ) -> bool {
        match terms.get(unit) {
            TermData::Const(Constant::Bool(true)) => true,
            TermData::Not(inner) => {
                matches!(terms.get(*inner), TermData::Const(Constant::Bool(false)))
            }
            _ => false,
        }
    }

    /// Cheap syntactic screen for the closed-ground-comparison channel: the
    /// unit (or its negation) is a `<`/`<=`/`>`/`>=`/`=` application whose
    /// arguments are all literal constants. Validity is NOT decided here — the
    /// strict checker's directional `evaluate` validator re-evaluates the
    /// term; a wrong guess fails authentication exactly like today's refusal.
    pub(in crate::sat_proof_manager) fn is_closed_ground_comparison_unit(
        terms: &TermStore,
        unit: TermId,
    ) -> bool {
        let atom = match terms.get(unit) {
            TermData::Not(inner) => *inner,
            _ => unit,
        };
        let TermData::App(Symbol::Named(name), args) = terms.get(atom) else {
            return false;
        };
        matches!(name.as_str(), "<" | "<=" | ">" | ">=" | "=")
            && !args.is_empty()
            && args
                .iter()
                .all(|&arg| matches!(terms.get(arg), TermData::Const(_)))
    }

    /// Emit `evaluate` + equivalence elimination deriving one closed ground
    /// comparison unit:
    ///
    /// ```text
    /// positive U:            negated U = (not A):
    /// t1: evaluate (cl (= U true))     t1: evaluate (cl (= A false))
    /// t2: equiv_pos1                    t2: equiv_pos2
    /// t3: resolution (cl U (not true))  t3: resolution (cl (not A) false)
    /// t4: true (cl true)                t4: true (cl (not false))
    /// t5: resolution (cl U)             t5: resolution (cl (not A))
    /// ```
    pub(in crate::sat_proof_manager) fn emit_closed_eval_unit_chain(
        terms: &mut TermStore,
        proof: &mut Proof,
        unit: TermId,
    ) -> ProofId {
        let (atom, negated) = match terms.get(unit) {
            TermData::Not(inner) => (*inner, true),
            _ => (unit, false),
        };
        if negated {
            let false_term = terms.false_term();
            let equality = terms.mk_app(Symbol::named("="), [atom, false_term], Sort::Bool);
            let evaluated =
                proof.add_rule_step(AletheRule::Evaluate, vec![equality], Vec::new(), Vec::new());
            let not_equality = terms.mk_not_raw(equality);
            let not_atom = terms.mk_not_raw(atom);
            let tautology = proof.add_rule_step(
                AletheRule::EquivPos2,
                vec![not_equality, not_atom, false_term],
                Vec::new(),
                Vec::new(),
            );
            let elided =
                proof.add_resolution(vec![not_atom, false_term], equality, tautology, evaluated);
            let not_false = terms.mk_not_raw(false_term);
            let false_taut =
                proof.add_rule_step(AletheRule::True, vec![not_false], Vec::new(), Vec::new());
            proof.add_resolution(vec![not_atom], false_term, false_taut, elided)
        } else {
            let true_term = terms.true_term();
            let equality = terms.mk_app(Symbol::named("="), [atom, true_term], Sort::Bool);
            let evaluated =
                proof.add_rule_step(AletheRule::Evaluate, vec![equality], Vec::new(), Vec::new());
            let not_equality = terms.mk_not_raw(equality);
            let not_true = terms.mk_not_raw(true_term);
            let tautology = proof.add_rule_step(
                AletheRule::EquivPos1,
                vec![not_equality, atom, not_true],
                Vec::new(),
                Vec::new(),
            );
            let elided = proof.add_resolution(vec![atom, not_true], equality, tautology, evaluated);
            let true_taut =
                proof.add_rule_step(AletheRule::True, vec![true_term], Vec::new(), Vec::new());
            proof.add_resolution(vec![atom], true_term, elided, true_taut)
        }
    }

    /// Emit the authored-rooted instantiation chain for one ground unit:
    ///
    /// ```text
    /// a1: assume  F                                  ; authored forall
    /// t1: forall_inst (cl (or (not F) I)) :args values
    /// t2: or          (cl (not F) I)      :premises t1
    /// t3: resolution  (cl I)              ; pivot F with a1
    /// ```
    ///
    /// Mirrors `ProofTracker::add_forall_instantiated_assertion`; every step is
    /// strict-checker validated downstream (`forall_inst` replays the exact
    /// substitution; resolution is replayed literally).
    pub(in crate::sat_proof_manager) fn emit_forall_inst_unit_chain(
        terms: &mut TermStore,
        proof: &mut Proof,
        derivation: &FragmentInstanceDerivation,
        unit: TermId,
        progress: &mut dyn FnMut(usize, usize) -> Result<(), ResolutionValidationError>,
    ) -> Result<ProofId, ResolutionValidationError> {
        let retained_slots = exact_checked_add(
            5,
            derivation.values.len(),
            ResolutionValidationResource::Bytes,
        )?;
        let (work, bytes) = Self::unit_chain_charge(4, retained_slots)?;
        progress(work, bytes)?;
        let quantifier = derivation.quantifier;
        let instance = derivation.instance;
        let source_id = proof.add_assume(quantifier, None);
        let not_quantified = terms.mk_not_raw(quantifier);
        let implication = terms.mk_app(Symbol::named("or"), [not_quantified, instance], Sort::Bool);
        let forall_inst = proof.add_rule_step(
            AletheRule::ForallInst,
            vec![implication],
            Vec::new(),
            derivation.values.clone(),
        );
        let clausified = proof.add_rule_step(
            AletheRule::Or,
            vec![not_quantified, instance],
            vec![forall_inst],
            Vec::new(),
        );
        let derived_id = proof.add_resolution(vec![instance], quantifier, clausified, source_id);
        if instance == unit {
            return Ok(derived_id);
        }

        // The sole supported folded target is literal `false`; the sealed
        // evidence already replayed the raw evaluation, and this bridge is
        // independently re-proved by the strict checker.
        let (bridge_work, bridge_bytes) = Self::unit_chain_charge(4, 6)?;
        progress(bridge_work, bridge_bytes)?;
        let false_term = terms.false_term();
        let not_instance = terms.mk_not_raw(instance);
        let not_false = terms.mk_not_raw(false_term);
        let not_not_false = terms.mk_not_raw(not_false);
        let bv_refutation = proof.add_step(ProofStep::TheoryLemma {
            theory: "theory".to_owned(),
            clause: vec![not_instance, not_not_false],
            farkas: None,
            kind: TheoryLemmaKind::BvLiaTautology,
            lia: None,
        });
        let elided = proof.add_resolution(vec![not_not_false], instance, derived_id, bv_refutation);
        let not_not_not_false = terms.mk_not_raw(not_not_false);
        let fold_tautology = proof.add_step(ProofStep::TheoryLemma {
            theory: "theory".to_owned(),
            clause: vec![not_not_not_false, false_term],
            farkas: None,
            kind: TheoryLemmaKind::BoolTautology,
            lia: None,
        });
        Ok(proof.add_resolution(vec![false_term], not_not_false, elided, fold_tautology))
    }

    /// Emit the authored-rooted single-binder Skolemization chain for one
    /// asserted unit, with an optional strict-evaluator bridge when Boolean
    /// folding changed the raw substituted form (e.g. `(not true)` → `false`).
    ///
    /// Positive source `E = exists x. B`:
    /// ```text
    /// a1: assume E
    /// t1: sko (cl (= E B[sk])) :args sk
    /// t2: equiv_pos2 (cl (not (= E B[sk])) (not E) B[sk])
    /// t3: resolution (cl (not E) B[sk])   ; pivot (= E B[sk])
    /// t4: resolution (cl B[sk])           ; pivot E with a1
    /// ```
    /// Negative source `not F`, `F = forall x. B`:
    /// ```text
    /// a1: assume (not F)
    /// t1: sko (cl (= F B[sk])) :args sk
    /// t2: equiv_pos1 (cl (not (= F B[sk])) F (not B[sk]))
    /// t3: resolution (cl F (not B[sk]))   ; pivot (= F B[sk])
    /// t4: resolution (cl (not B[sk]))     ; pivot F with a1
    /// ```
    /// Bridge from derived literal `d` to asserted unit `u` (only if `d != u`):
    /// ```text
    /// t5: true       (cl (= d u))         ; exhaustively evaluated
    /// t6: equiv_pos2 (cl (not (= d u)) (not d) u)
    /// t7: resolution (cl (not d) u)       ; pivot (= d u)
    /// t8: resolution (cl u)               ; pivot d with t4
    /// ```
    ///
    /// Self-metering: the 5-step base chain (a1,t1..t4; 9 retained term
    /// slots: 1 assume + 1 sko clause + 1 sko witness arg + 3 tautology + 2
    /// elided + 1 final) is charged before any base emission, and the 4-step
    /// bridge (t5..t8; 7 retained slots: 1 + 3 + 2 + 1) is charged only when
    /// the bridge is ACTUALLY needed, immediately before it is emitted — the
    /// meter therefore tracks the exact step count of the chain produced.
    /// Interned helper terms are reconciled by the caller against real
    /// term-store growth.
    pub(in crate::sat_proof_manager) fn emit_skolem_unit_chain(
        terms: &mut TermStore,
        proof: &mut Proof,
        derivation: &FragmentSkolemDerivation,
        unit: TermId,
        progress: &mut dyn FnMut(usize, usize) -> Result<(), ResolutionValidationError>,
    ) -> Result<ProofId, ResolutionValidationError> {
        let (base_work, base_bytes) = Self::unit_chain_charge(5, 9)?;
        progress(base_work, base_bytes)?;
        let assume_id = proof.add_assume(derivation.source, None);
        let equality = terms.mk_app(
            Symbol::named("="),
            [derivation.quantified, derivation.instance],
            Sort::Bool,
        );
        let sko = proof.add_rule_step(
            AletheRule::Skolem,
            vec![equality],
            Vec::new(),
            vec![derivation.witness],
        );
        let not_equality = terms.mk_not_raw(equality);
        let derived_id;
        let derived_literal;
        if derivation.positive {
            let not_quantified = terms.mk_not_raw(derivation.quantified);
            let tautology = proof.add_rule_step(
                AletheRule::EquivPos2,
                vec![not_equality, not_quantified, derivation.instance],
                Vec::new(),
                Vec::new(),
            );
            let elided = proof.add_resolution(
                vec![not_quantified, derivation.instance],
                equality,
                tautology,
                sko,
            );
            derived_id = proof.add_resolution(
                vec![derivation.instance],
                derivation.quantified,
                elided,
                assume_id,
            );
            derived_literal = derivation.instance;
        } else {
            let not_instance = terms.mk_not_raw(derivation.instance);
            let tautology = proof.add_rule_step(
                AletheRule::EquivPos1,
                vec![not_equality, derivation.quantified, not_instance],
                Vec::new(),
                Vec::new(),
            );
            let elided = proof.add_resolution(
                vec![derivation.quantified, not_instance],
                equality,
                tautology,
                sko,
            );
            derived_id =
                proof.add_resolution(vec![not_instance], derivation.quantified, assume_id, elided);
            derived_literal = not_instance;
        }
        if derived_literal == unit {
            return Ok(derived_id);
        }
        // Boolean-fold bridge, re-validated by the strict bounded evaluator.
        let (bridge_work, bridge_bytes) = Self::unit_chain_charge(4, 7)?;
        progress(bridge_work, bridge_bytes)?;
        let bridge_equality = terms.mk_app(Symbol::named("="), [derived_literal, unit], Sort::Bool);
        let bridge = proof.add_rule_step(
            AletheRule::True,
            vec![bridge_equality],
            Vec::new(),
            Vec::new(),
        );
        let not_bridge_equality = terms.mk_not_raw(bridge_equality);
        let not_derived = terms.mk_not_raw(derived_literal);
        let tautology = proof.add_rule_step(
            AletheRule::EquivPos2,
            vec![not_bridge_equality, not_derived, unit],
            Vec::new(),
            Vec::new(),
        );
        let elided =
            proof.add_resolution(vec![not_derived, unit], bridge_equality, tautology, bridge);
        Ok(proof.add_resolution(vec![unit], derived_literal, elided, derived_id))
    }

    /// Recognize `(or S false ... false)` with one repeated non-false
    /// survivor and at least one literal-false position.
    pub(in crate::sat_proof_manager) fn or_fold_survivor(
        terms: &TermStore,
        term: TermId,
    ) -> Option<TermId> {
        let TermData::App(Symbol::Named(name), args) = terms.get(term) else {
            return None;
        };
        if name != "or" || args.len() < 2 {
            return None;
        }
        let mut survivor = None;
        let mut saw_false = false;
        for &arg in args {
            if matches!(terms.get(arg), TermData::Const(Constant::Bool(false))) {
                saw_false = true;
                continue;
            }
            match survivor {
                None => survivor = Some(arg),
                Some(existing) if existing == arg => {}
                Some(_) => return None,
            }
        }
        saw_false.then_some(survivor).flatten()
    }

    /// Build exact fold plans for the survivor and its bounded transitive
    /// `and`-conjunct closure.
    pub(in crate::sat_proof_manager) fn build_or_fold_unit_plans(
        &self,
        candidates: &[TermId],
        progress: &mut dyn FnMut(usize, usize) -> Result<(), ResolutionValidationError>,
    ) -> Result<HashMap<TermId, OrFoldUnitPlan>, ResolutionValidationError> {
        let mut plans = HashMap::default();
        let mut pending_visits = 0usize;
        for &or_root in candidates {
            if plans.len() >= MAX_OR_FOLD_UNITS {
                break;
            }
            let Some(survivor) = Self::or_fold_survivor(self.terms, or_root) else {
                continue;
            };
            let TermData::App(_, args) = self.terms.get(or_root) else {
                continue;
            };
            let disjuncts = args.clone();
            let mut stack = vec![(survivor, Vec::<(TermId, u32)>::new())];
            while let Some((node, hops)) = stack.pop() {
                pending_visits += 1;
                if pending_visits >= 256 {
                    progress(pending_visits, 0)?;
                    pending_visits = 0;
                }
                if plans.len() >= MAX_OR_FOLD_UNITS {
                    break;
                }
                if !plans.contains_key(&node) {
                    let entry_bytes = exact_checked_add(
                        exact_checked_add(
                            64,
                            exact_checked_mul(
                                disjuncts.len(),
                                16,
                                ResolutionValidationResource::Bytes,
                            )?,
                            ResolutionValidationResource::Bytes,
                        )?,
                        exact_checked_mul(hops.len(), 32, ResolutionValidationResource::Bytes)?,
                        ResolutionValidationResource::Bytes,
                    )?;
                    progress(4, entry_bytes)?;
                    plans.insert(
                        node,
                        OrFoldUnitPlan {
                            or_root,
                            disjuncts: disjuncts.clone(),
                            survivor,
                            hops: hops.clone(),
                        },
                    );
                }
                if hops.len() >= MAX_OR_FOLD_HOPS {
                    continue;
                }
                let TermData::App(Symbol::Named(name), children) = self.terms.get(node) else {
                    continue;
                };
                if name != "and" {
                    continue;
                }
                let children = children.clone();
                progress(
                    children.len(),
                    exact_checked_mul(children.len(), 192, ResolutionValidationResource::Bytes)?,
                )?;
                for (index, &child) in children.iter().enumerate() {
                    let Ok(index) = u32::try_from(index) else {
                        continue;
                    };
                    let mut child_hops = hops.clone();
                    child_hops.push((node, index));
                    stack.push((child, child_hops));
                }
            }
        }
        progress(pending_visits, 0)?;
        Ok(plans)
    }

    /// Emit `Assume + or + false-resolution + and_pos` for one fold plan.
    pub(in crate::sat_proof_manager) fn emit_or_fold_unit_chain(
        terms: &mut TermStore,
        proof: &mut Proof,
        plan: &OrFoldUnitPlan,
        unit: TermId,
        progress: &mut dyn FnMut(usize, usize) -> Result<(), ResolutionValidationError>,
    ) -> Result<ProofId, ResolutionValidationError> {
        let steps = exact_checked_add(
            3,
            exact_checked_mul(plan.hops.len(), 2, ResolutionValidationResource::Work)?,
            ResolutionValidationResource::Work,
        )?;
        let slots = exact_checked_add(
            exact_checked_add(3, plan.disjuncts.len(), ResolutionValidationResource::Bytes)?,
            exact_checked_mul(plan.hops.len(), 4, ResolutionValidationResource::Bytes)?,
            ResolutionValidationResource::Bytes,
        )?;
        let (work, bytes) = Self::unit_chain_charge(steps, slots)?;
        progress(work, bytes)?;

        let assume_id = proof.add_assume(plan.or_root, None);
        let clausified = proof.add_rule_step(
            AletheRule::Or,
            plan.disjuncts.clone(),
            vec![assume_id],
            Vec::new(),
        );
        let false_term = terms.false_term();
        let not_false = terms.mk_not_raw(false_term);
        let false_tautology =
            proof.add_rule_step(AletheRule::False, vec![not_false], Vec::new(), Vec::new());
        let mut derived_id =
            proof.add_resolution(vec![plan.survivor], false_term, clausified, false_tautology);
        let mut derived_term = plan.survivor;
        for &(and_term, index) in &plan.hops {
            let TermData::App(_, children) = terms.get(and_term) else {
                return Ok(derived_id);
            };
            let Some(&conjunct) = children.get(index as usize) else {
                return Ok(derived_id);
            };
            let not_and = terms.mk_not_raw(and_term);
            let tautology = proof.add_rule_step(
                AletheRule::AndPos(index),
                vec![not_and, conjunct],
                Vec::new(),
                vec![and_term],
            );
            derived_id = proof.add_resolution(vec![conjunct], and_term, tautology, derived_id);
            derived_term = conjunct;
        }
        debug_assert_eq!(derived_term, unit);
        Ok(derived_id)
    }
}
