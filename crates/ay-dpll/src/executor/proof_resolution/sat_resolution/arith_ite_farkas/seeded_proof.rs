// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Checked proof emission for the arithmetic-ITE seeded clause database.

use ay_core::term::TermData as Td;
use ay_core::{AletheRule, Proof, ProofId, Sort, Symbol, TermId};

use super::{ite_free, mk_lit, usable_atom, ArithIteSeeding};
use crate::executor::proof_trust_surgery_ite::ProvenanceItePlan;
use crate::executor::Executor;

/// Path clauses emitted per ITE tree. `2^k` paths for `k` nested conditions;
/// the wrapping-arithmetic family needs 3 per side.
const MAX_ITE_PATH_CLAUSES: usize = 64;

/// Append `lit` unless present — path clauses must stay duplicate-free so both
/// the resolution set-compare and the closer's propagation see each literal
/// once.
fn push_unique(clause: &mut Vec<TermId>, lit: TermId) {
    if !clause.contains(&lit) {
        clause.push(lit);
    }
}

impl Executor {
    /// Peel a formula-level ITE tree — proved as the unit clause `unit` — into
    /// ITE-free PATH clauses via the premise-free `ite_pos1`/`ite_pos2`
    /// tautologies, each resolved on its ITE literal:
    ///
    /// ```text
    /// (cl … T …)  +  ite_pos2 ⊢ (cl (not T) (not c) t)   →  (cl … (not c) t …)
    /// (cl … T …)  +  ite_pos1 ⊢ (cl (not T) c e)         →  (cl … c e …)
    /// ```
    ///
    /// A SINGLE-LEVEL ITE instead seeds the classic premise-carrying
    /// implication clauses (`ite2` ⊢ `(cl (not c) t)`, `ite1` ⊢ `(cl c e)`) —
    /// the exact steps the pre-nesting lane emitted and the trust-surgery
    /// fixtures assert on; the path prefix only exists for nested trees.
    ///
    /// Only fully peeled clauses whose every literal is a usable atom are
    /// seeded; anything else is dropped (a subset of derivable consequences,
    /// always sound). A negated-condition ITE is dropped at the usability
    /// check exactly as the previous single-level seeding declined it.
    pub(super) fn seed_ite_path_clauses(
        &mut self,
        seeding: &mut ArithIteSeeding,
        candidate: &mut Proof,
        ite_term: TermId,
        unit: ProofId,
    ) {
        if let Td::Ite(cond, then_b, else_b) = self.ctx.terms.get(ite_term) {
            let (cond, then_b, else_b) = (*cond, *then_b, *else_b);
            let nested = [then_b, else_b].iter().any(|&branch| {
                matches!(self.ctx.terms.get(branch), Td::Ite(..))
                    && matches!(self.ctx.terms.sort(branch), Sort::Bool)
            });
            if !nested {
                self.seed_single_level_ite(seeding, candidate, unit, cond, then_b, else_b);
                return;
            }
        }
        let mut stack: Vec<(Vec<TermId>, ProofId)> = vec![(vec![ite_term], unit)];
        let mut emitted = 0usize;
        while let Some((clause, proof_id)) = stack.pop() {
            if !seeding.charge() {
                return;
            }
            // A positive Bool-sorted ITE literal still to peel?
            let position = clause.iter().position(|&lit| {
                matches!(self.ctx.terms.get(lit), Td::Ite(..))
                    && matches!(self.ctx.terms.sort(lit), Sort::Bool)
            });
            let Some(position) = position else {
                if let Some(sat) = seeding.sat_clause(&self.ctx.terms, &clause) {
                    if !clause.is_empty() {
                        seeding.clause_versions.push((sat, proof_id));
                        seeding.seeded_ite = true;
                    }
                }
                continue;
            };
            emitted += 2;
            if emitted > MAX_ITE_PATH_CLAUSES {
                return;
            }
            let peeled = clause[position];
            let Td::Ite(cond, then_branch, else_branch) = self.ctx.terms.get(peeled) else {
                unreachable!("position selected a non-ITE literal");
            };
            let (cond, then_branch, else_branch) = (*cond, *then_branch, *else_branch);
            let not_peeled = self.ctx.terms.mk_not_raw(peeled);
            let not_cond = self.ctx.terms.mk_not_raw(cond);
            // The path prefix minus EVERY occurrence of the peeled literal:
            // resolution removes the pivot as a set operation, so a duplicate
            // left behind would make the recorded conclusion clause invalid.
            let rest: Vec<TermId> = clause
                .iter()
                .copied()
                .filter(|&lit| lit != peeled)
                .collect();

            // ite_pos2: ⊢ (cl (not T) (not c) t); resolve on T.
            let ite_pos2 = candidate.add_rule_step(
                AletheRule::ItePos2,
                vec![not_peeled, not_cond, then_branch],
                Vec::new(),
                Vec::new(),
            );
            let mut then_clause = rest.clone();
            push_unique(&mut then_clause, not_cond);
            push_unique(&mut then_clause, then_branch);
            let then_id = candidate.add_resolution(then_clause.clone(), peeled, ite_pos2, proof_id);
            stack.push((then_clause, then_id));

            // ite_pos1: ⊢ (cl (not T) c e); resolve on T.
            let ite_pos1 = candidate.add_rule_step(
                AletheRule::ItePos1,
                vec![not_peeled, cond, else_branch],
                Vec::new(),
                Vec::new(),
            );
            let mut else_clause = rest;
            push_unique(&mut else_clause, cond);
            push_unique(&mut else_clause, else_branch);
            let else_id = candidate.add_resolution(else_clause.clone(), peeled, ite_pos1, proof_id);
            stack.push((else_clause, else_id));
        }
    }

    /// Seed a single-level formula-level ITE — proved as the unit clause
    /// `unit` — as its two GENUINE implication clauses. Declines (seeding
    /// nothing) unless the condition is a POSITIVE usable atom and both
    /// branches are usable, so the SAT variables map back to the exact terms
    /// `lit_to_term` renders.
    fn seed_single_level_ite(
        &mut self,
        seeding: &mut ArithIteSeeding,
        candidate: &mut Proof,
        unit: ProofId,
        cond: TermId,
        then_b: TermId,
        else_b: TermId,
    ) {
        let (Some((cond_atom, true)), Some((then_atom, then_val)), Some((else_atom, else_val))) = (
            usable_atom(&self.ctx.terms, cond),
            usable_atom(&self.ctx.terms, then_b),
            usable_atom(&self.ctx.terms, else_b),
        ) else {
            return;
        };
        if cond_atom != cond {
            return;
        }
        // `mk_not_raw` matches `SatProofManager::negate_term`, so the clause
        // literal `(not cond)` equals `lit_to_term` of the negative condition
        // literal.
        let not_cond = self.ctx.terms.mk_not_raw(cond);
        // ite2: `(cl (ite c t e))` ⊢ `(cl (not c) t)`.
        let ite2 = candidate.add_rule_step(
            AletheRule::Ite2,
            vec![not_cond, then_b],
            vec![unit],
            Vec::new(),
        );
        // ite1: `(cl (ite c t e))` ⊢ `(cl c e)`.
        let ite1 =
            candidate.add_rule_step(AletheRule::Ite1, vec![cond, else_b], vec![unit], Vec::new());
        let cond_var = seeding.intern(cond_atom);
        let then_var = seeding.intern(then_atom);
        let else_var = seeding.intern(else_atom);
        seeding.clause_versions.push((
            vec![mk_lit(cond_var, false), mk_lit(then_var, then_val)],
            ite2,
        ));
        seeding.clause_versions.push((
            vec![mk_lit(cond_var, true), mk_lit(else_var, else_val)],
            ite1,
        ));
        seeding.seeded_ite = true;
    }

    /// Seed a substitution-derived formula-level ITE root from its provenance
    /// plan: the checked branch derivation (`ite1`/`ite2` over the exact
    /// authored source, plus independently replayed Farkas implications)
    /// concludes the two implication clauses the direct lane would have taken
    /// from an `assume` this root is not entitled to. Returns `false` (abort
    /// the whole attempt) when the planned emission fails mid-candidate;
    /// unusable root atoms merely skip the root, exactly like the direct lane.
    pub(super) fn seed_provenance_ite_root(
        &mut self,
        seeding: &mut ArithIteSeeding,
        candidate: &mut Proof,
        root: TermId,
        plan: &ProvenanceItePlan,
    ) -> bool {
        // The plan proves exactly this root; anything else would seed clauses
        // the emitted derivation does not conclude.
        if plan.goal() != root {
            return false;
        }
        let Td::Ite(cond, then_b, else_b) = *self.ctx.terms.get(root) else {
            return false;
        };
        // The seeded branch clauses ride the ROOT's atoms, so the condition
        // and branches must be usable and the condition a POSITIVE atom (its
        // SAT variable must map back to `cond` itself so the implication
        // clauses stay consistent with `lit_to_term`).
        let (Some((cond_atom, true)), Some((then_atom, then_val)), Some((else_atom, else_val))) = (
            usable_atom(&self.ctx.terms, cond),
            usable_atom(&self.ctx.terms, then_b),
            usable_atom(&self.ctx.terms, else_b),
        ) else {
            return true;
        };
        if cond_atom != cond {
            return true;
        }
        // Authored assumes for the plan's exact sources — deduplicated, since
        // a support can coincide with another seeded root.
        for term in plan.authored_assumption_terms() {
            seeding.assume_once(candidate, term);
        }
        let Some((ite2, ite1)) =
            self.emit_provenance_ite_seed_branches(candidate, plan, &seeding.authored_assumes)
        else {
            return false;
        };
        let cond_var = seeding.intern(cond_atom);
        let then_var = seeding.intern(then_atom);
        let else_var = seeding.intern(else_atom);
        // ite2 ⊢ `(cl (not c) t)`, ite1 ⊢ `(cl c e)`.
        seeding.clause_versions.push((
            vec![mk_lit(cond_var, false), mk_lit(then_var, then_val)],
            ite2,
        ));
        seeding.clause_versions.push((
            vec![mk_lit(cond_var, true), mk_lit(else_var, else_val)],
            ite1,
        ));
        seeding.seeded_ite = true;
        true
    }

    /// For a seeded unit `(not (= a b))` over Int/Real operands, derive and
    /// seed the complementary-bound split `(cl (not (<= a b)) (not (<= b a)))`:
    ///
    /// ```text
    /// la_disequality ⊢ (cl (or (= a b) (not (<= a b)) (not (<= b a))))
    /// or             ⊢ (cl (= a b) (not (<= a b)) (not (<= b a)))
    /// resolution with (cl (not (= a b))) on the equality
    /// ```
    ///
    /// The LRA oracle deliberately refuses to assert a disequality (it is not
    /// a linear bound), so without this split every branch conflict resting on
    /// the refuted identity stalls the closer. Both negated `<=` literals ARE
    /// assertable bounds. Everything here is re-derived by the strict checker
    /// (`la_disequality` is validated positionally, `or` against the packed
    /// term, the resolution as a set operation); a shape this helper declines
    /// simply seeds nothing.
    pub(super) fn seed_la_disequality_split(
        &mut self,
        seeding: &mut ArithIteSeeding,
        candidate: &mut Proof,
        lit_term: TermId,
        unit: ProofId,
    ) {
        let Td::Not(inner) = self.ctx.terms.get(lit_term) else {
            return;
        };
        let equality = *inner;
        let Td::App(Symbol::Named(name), operands) = self.ctx.terms.get(equality) else {
            return;
        };
        if name != "=" || operands.len() != 2 {
            return;
        }
        let (lhs, rhs) = (operands[0], operands[1]);
        // A reflexive disequality collapses both bounds onto one atom; that
        // degenerate root belongs to `eq_reflexive`, not this split.
        if lhs == rhs {
            return;
        }
        let lhs_sort = self.ctx.terms.sort(lhs).clone();
        if !matches!(lhs_sort, Sort::Int | Sort::Real) || self.ctx.terms.sort(rhs) != &lhs_sort {
            return;
        }
        if !ite_free(&self.ctx.terms, lhs) || !ite_free(&self.ctx.terms, rhs) {
            return;
        }

        let le_forward = self
            .ctx
            .terms
            .mk_app(Symbol::named("<="), vec![lhs, rhs], Sort::Bool);
        let le_reverse = self
            .ctx
            .terms
            .mk_app(Symbol::named("<="), vec![rhs, lhs], Sort::Bool);
        let not_le_forward = self.ctx.terms.mk_not_raw(le_forward);
        let not_le_reverse = self.ctx.terms.mk_not_raw(le_reverse);
        let packed_or = self.ctx.terms.mk_app(
            Symbol::named("or"),
            vec![equality, not_le_forward, not_le_reverse],
            Sort::Bool,
        );
        let la_disequality = candidate.add_rule_step(
            AletheRule::LaDisequality,
            vec![packed_or],
            Vec::new(),
            Vec::new(),
        );
        let clausified = candidate.add_rule_step(
            AletheRule::Or,
            vec![equality, not_le_forward, not_le_reverse],
            vec![la_disequality],
            Vec::new(),
        );
        let split = candidate.add_resolution(
            vec![not_le_forward, not_le_reverse],
            equality,
            clausified,
            unit,
        );
        let forward_var = seeding.intern(le_forward);
        let reverse_var = seeding.intern(le_reverse);
        seeding.clause_versions.push((
            vec![mk_lit(forward_var, false), mk_lit(reverse_var, false)],
            split,
        ));
    }
}
