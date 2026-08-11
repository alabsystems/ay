// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Rendered-role authentication for copied Boolean ITE CNF axioms.

use ay_core::kani_compat::DetHashSet as HashSet;
use ay_core::term::TermData;
use ay_core::{AletheRule, Sort, Symbol, TermId, TermStore};

use super::super::complement_of;
use super::ProvenanceSurfaceAudit;

fn exact_clause_permutation(clause: &[TermId], expected: [TermId; 3]) -> bool {
    if clause.len() != expected.len() {
        return false;
    }
    let mut actual = clause.to_vec();
    actual.sort_unstable();
    let mut expected = expected;
    expected.sort_unstable();
    actual == expected
}

/// Recover and register the one Boolean ITE whose exact canonical
/// three-literal axiom is named by `rule`. The native strict checker validates
/// the same four tuples. Registering the parent with the existing rendered ITE
/// composition role makes it safe for this copied step alone to bypass the
/// blanket descendant-intersection veto.
pub(super) fn protect_copied_formula_ite_role(
    audit: &mut ProvenanceSurfaceAudit,
    terms: &mut TermStore,
    rule: &AletheRule,
    clause: &[TermId],
    args: &[TermId],
) -> bool {
    if clause.len() != 3 {
        return false;
    }
    let positive_parent = matches!(rule, AletheRule::IteNeg1 | AletheRule::IteNeg2);
    let mut candidates = HashSet::default();
    for &literal in clause {
        let parent = if positive_parent {
            literal
        } else {
            let TermData::Not(inner) = terms.get(literal) else {
                continue;
            };
            *inner
        };
        let TermData::Ite(cond, then_term, else_term) = *terms.get(parent) else {
            continue;
        };
        if *terms.sort(parent) != Sort::Bool {
            continue;
        }
        let not_parent = complement_of(terms, parent);
        let not_cond = complement_of(terms, cond);
        let not_then = complement_of(terms, then_term);
        let not_else = complement_of(terms, else_term);
        let expected = match rule {
            AletheRule::ItePos1 => [not_parent, cond, else_term],
            AletheRule::ItePos2 => [not_parent, not_cond, then_term],
            AletheRule::IteNeg1 => [parent, cond, not_else],
            AletheRule::IteNeg2 => [parent, not_cond, not_then],
            _ => return false,
        };
        if exact_clause_permutation(clause, expected) {
            candidates.insert(parent);
        }
    }
    let mut candidates = candidates.into_iter();
    let Some(ite_term) = candidates.next() else {
        return false;
    };
    if candidates.next().is_some() {
        return false;
    }
    // SAT clausification records the canonical source as one internal
    // bookkeeping argument. The Alethe printer uses this exact singleton to
    // reconstruct normalized negated children with explicit `not_not`
    // bridges, then suppresses it from the exported tautology step. A native
    // no-args ITE rule is broader: with an already-negated child its normalized
    // clause is not a direct external Alethe tuple, so copied retained-map
    // surgery conservatively requires the production source authority.
    if args != [ite_term] {
        return false;
    }
    let TermData::Ite(_, then_term, else_term) = *terms.get(ite_term) else {
        return false;
    };
    let eq_then = terms.mk_app(Symbol::named("="), [ite_term, then_term], Sort::Bool);
    let eq_else = terms.mk_app(Symbol::named("="), [ite_term, else_term], Sort::Bool);
    audit.protect_ite_intro_role(terms, ite_term, eq_then, eq_else);
    for &literal in clause {
        audit.protect_operand(terms, literal);
    }
    !audit.overflowed
}

#[cfg(test)]
mod tests {
    use ay_core::kani_compat::{DetHashMap as HashMap, DetHashSet as HashSet};
    use ay_core::{AletheRule, Proof, Sort, TermStore};

    use super::super::{copied_structural_roles_are_static, ProvenanceSurfaceAudit};

    #[test]
    fn copied_ite_axiom_accepts_consistent_condition_surface() {
        let mut terms = TermStore::new();
        let condition = terms.mk_var("copied_axiom_condition", Sort::Bool);
        let then_term = terms.mk_var("copied_axiom_then", Sort::Bool);
        let else_term = terms.mk_var("copied_axiom_else", Sort::Bool);
        let ite = terms.mk_ite(condition, then_term, else_term);
        let not_ite = terms.mk_not_raw(ite);
        let not_condition = terms.mk_not_raw(condition);
        let mut proof = Proof::new();
        proof.add_rule_step(
            AletheRule::ItePos2,
            vec![not_ite, not_condition, then_term],
            Vec::new(),
            vec![ite],
        );

        let mut audit = ProvenanceSurfaceAudit::default();
        let surface = "(= copied_axiom_condition true)";
        assert!(audit.require_spelling(&mut terms, condition, surface));
        assert!(audit.protect_copied_resolution_and_farkas_roles(
            &proof,
            &[true],
            &HashSet::default(),
            &mut terms,
        ));
        let mut effective = HashMap::default();
        effective.insert(condition, surface.to_string());
        assert!(audit.validate_effective(&terms, &effective));
        assert!(copied_structural_roles_are_static(
            &proof,
            &[true],
            &HashSet::default(),
            &terms,
            &effective,
        ));
    }

    #[test]
    fn copied_ite_axioms_accept_normalized_negated_children() {
        let mut terms = TermStore::new();
        let condition_atom = terms.mk_var("copied_negated_condition", Sort::Bool);
        let then_atom = terms.mk_var("copied_negated_then", Sort::Bool);
        let else_atom = terms.mk_var("copied_negated_else", Sort::Bool);
        let condition = terms.mk_not_raw(condition_atom);
        let then_term = terms.mk_not_raw(then_atom);
        let else_term = terms.mk_not_raw(else_atom);
        let ite = terms.mk_ite_raw(condition, then_term, else_term);
        let not_ite = terms.mk_not_raw(ite);
        let mut proof = Proof::new();
        for (rule, clause) in [
            (AletheRule::ItePos1, vec![not_ite, condition, else_term]),
            (
                AletheRule::ItePos2,
                vec![not_ite, condition_atom, then_term],
            ),
            (AletheRule::IteNeg1, vec![ite, condition, else_atom]),
            (AletheRule::IteNeg2, vec![ite, condition_atom, then_atom]),
        ] {
            proof.add_rule_step(rule, clause, Vec::new(), vec![ite]);
        }

        let surface = "(= copied_negated_condition true)";
        let mut audit = ProvenanceSurfaceAudit::default();
        assert!(audit.require_spelling(&mut terms, condition_atom, surface));
        assert!(audit.protect_copied_resolution_and_farkas_roles(
            &proof,
            &[true; 4],
            &HashSet::default(),
            &mut terms,
        ));
        let mut effective = HashMap::default();
        effective.insert(condition_atom, surface.to_string());
        assert!(audit.validate_effective(&terms, &effective));
        assert!(copied_structural_roles_are_static(
            &proof,
            &[true; 4],
            &HashSet::default(),
            &terms,
            &effective,
        ));
    }

    #[test]
    fn copied_ite_axiom_rejects_unrelated_internal_source_arg() {
        let mut terms = TermStore::new();
        let condition = terms.mk_var("copied_axiom_arg_condition", Sort::Bool);
        let then_term = terms.mk_var("copied_axiom_arg_then", Sort::Bool);
        let else_term = terms.mk_var("copied_axiom_arg_else", Sort::Bool);
        let ite = terms.mk_ite(condition, then_term, else_term);
        let not_ite = terms.mk_not_raw(ite);
        let not_condition = terms.mk_not_raw(condition);
        let mut proof = Proof::new();
        proof.add_rule_step(
            AletheRule::ItePos2,
            vec![not_ite, not_condition, then_term],
            Vec::new(),
            vec![condition],
        );
        let mut audit = ProvenanceSurfaceAudit::default();
        assert!(!audit.protect_copied_resolution_and_farkas_roles(
            &proof,
            &[true],
            &HashSet::default(),
            &mut terms,
        ));
    }

    #[test]
    fn copied_ite_axiom_rejects_missing_internal_source_arg() {
        let mut terms = TermStore::new();
        let condition = terms.mk_var("copied_axiom_empty_condition", Sort::Bool);
        let then_term = terms.mk_var("copied_axiom_empty_then", Sort::Bool);
        let else_term = terms.mk_var("copied_axiom_empty_else", Sort::Bool);
        let ite = terms.mk_ite(condition, then_term, else_term);
        let not_ite = terms.mk_not_raw(ite);
        let not_condition = terms.mk_not_raw(condition);
        let mut proof = Proof::new();
        proof.add_rule_step(
            AletheRule::ItePos2,
            vec![not_ite, not_condition, then_term],
            Vec::new(),
            Vec::new(),
        );
        let mut audit = ProvenanceSurfaceAudit::default();
        assert!(!audit.protect_copied_resolution_and_farkas_roles(
            &proof,
            &[true],
            &HashSet::default(),
            &mut terms,
        ));
    }

    #[test]
    fn copied_ite_axiom_rejects_swapped_negated_parent_surface() {
        let mut terms = TermStore::new();
        let condition = terms.mk_var("copied_axiom_bad_condition", Sort::Bool);
        let then_term = terms.mk_var("copied_axiom_bad_then", Sort::Bool);
        let else_term = terms.mk_var("copied_axiom_bad_else", Sort::Bool);
        let ite = terms.mk_ite(condition, then_term, else_term);
        let not_ite = terms.mk_not_raw(ite);
        let not_condition = terms.mk_not_raw(condition);
        let mut proof = Proof::new();
        proof.add_rule_step(
            AletheRule::ItePos2,
            vec![not_ite, not_condition, then_term],
            Vec::new(),
            vec![ite],
        );

        let surface =
            "(ite (not copied_axiom_bad_condition) copied_axiom_bad_else copied_axiom_bad_then)";
        let mut audit = ProvenanceSurfaceAudit::default();
        assert!(audit.require_spelling(&mut terms, ite, surface));
        assert!(audit.protect_copied_resolution_and_farkas_roles(
            &proof,
            &[true],
            &HashSet::default(),
            &mut terms,
        ));
        let mut effective = HashMap::default();
        effective.insert(ite, surface.to_string());
        assert!(copied_structural_roles_are_static(
            &proof,
            &[true],
            &HashSet::default(),
            &terms,
            &effective,
        ));
        assert!(!audit.validate_effective(&terms, &effective));
    }
}
