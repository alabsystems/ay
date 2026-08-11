// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Rendered-role authentication for copied Boolean OR CNF axioms.

use ay_core::term::TermData;
use ay_core::{AletheRule, Sort, Symbol, TermId, TermStore};

use super::ProvenanceSurfaceAudit;

const MAX_OR_ARITY: usize =
    crate::executor::proof_trust_surgery_provenance::MAX_PROVENANCE_REPAIR_TERMS;

fn exact_clause_permutation(clause: &[TermId], expected: &[TermId]) -> bool {
    if clause.len() != expected.len() {
        return false;
    }
    let mut actual = clause.to_vec();
    actual.sort_unstable();
    let mut expected = expected.to_vec();
    expected.sort_unstable();
    actual == expected
}

pub(super) fn protect_or_composition_role(
    audit: &mut ProvenanceSurfaceAudit,
    terms: &mut TermStore,
    root: TermId,
    disjuncts: &[TermId],
) -> bool {
    let role = (root, disjuncts.to_vec());
    if audit.or_decomposition_roles.len() >= super::super::MAX_AUDITED_FARKAS_LEMMAS
        && !audit.or_decomposition_roles.contains(&role)
    {
        return false;
    }
    audit.protect_operand(terms, root);
    for &disjunct in disjuncts {
        audit.protect_operand(terms, disjunct);
    }
    audit.or_decomposition_roles.insert(role);
    !audit.overflowed
}

/// Authenticate the exact SAT-produced `or_pos` tautology named by its
/// singleton source argument. The rendered OR-composition role lets this
/// copied step bypass the blanket descendant-intersection veto while still
/// rejecting operator, arity, nesting, duplicate, or operand drift.
pub(super) fn protect_copied_or_pos_role(
    audit: &mut ProvenanceSurfaceAudit,
    terms: &mut TermStore,
    rule: &AletheRule,
    clause: &[TermId],
    args: &[TermId],
) -> bool {
    if !matches!(rule, AletheRule::OrPos(0)) {
        return false;
    }
    let [root] = args else {
        return false;
    };
    let root = *root;
    let disjuncts = {
        let TermData::App(Symbol::Named(op), disjuncts) = terms.get(root) else {
            return false;
        };
        if op != "or"
            || *terms.sort(root) != Sort::Bool
            || !(2..=MAX_OR_ARITY).contains(&disjuncts.len())
            || disjuncts
                .iter()
                .any(|&disjunct| *terms.sort(disjunct) != Sort::Bool)
        {
            return false;
        }
        disjuncts.clone()
    };
    let mut expected = Vec::with_capacity(disjuncts.len() + 1);
    expected.push(terms.mk_not_raw(root));
    expected.extend(disjuncts.iter().copied());
    if !exact_clause_permutation(clause, &expected) {
        return false;
    }
    for &literal in clause {
        audit.protect_operand(terms, literal);
    }
    protect_or_composition_role(audit, terms, root, &disjuncts)
}

#[cfg(test)]
mod tests {
    use ay_core::kani_compat::{DetHashMap as HashMap, DetHashSet as HashSet};
    use ay_core::{AletheRule, Proof, ProofId, Sort, Symbol, TermStore};

    use super::super::{copied_structural_roles_are_static, ProvenanceSurfaceAudit};

    fn audit_copied_roles(proof: &Proof, terms: &mut TermStore) -> ProvenanceSurfaceAudit {
        let mut audit = ProvenanceSurfaceAudit::default();
        assert!(audit.protect_copied_resolution_and_farkas_roles(
            proof,
            &vec![true; proof.steps.len()],
            &HashSet::default(),
            terms,
        ));
        audit
    }

    #[test]
    fn copied_or_pos_accepts_identity_descendant_and_top_level_reordering() {
        let mut terms = TermStore::new();
        let a = terms.mk_var("copied_or_pos_a", Sort::Bool);
        let j = terms.mk_var("copied_or_pos_j", Sort::Int);
        let one = terms.mk_int(1.into());
        let condition = terms.mk_app(Symbol::named("="), [j, one], Sort::Bool);
        let c = terms.mk_var("copied_or_pos_c", Sort::Bool);
        let root = terms.mk_or(vec![a, condition, c]);
        let not_root = terms.mk_not_raw(root);
        let disjuncts = match terms.get(root) {
            ay_core::TermData::App(_, disjuncts) => disjuncts.clone(),
            other => panic!("expected OR, got {other:?}"),
        };
        let mut clause = vec![not_root];
        clause.extend(disjuncts.iter().copied());
        let mut proof = Proof::new();
        proof.add_rule_step(AletheRule::OrPos(0), clause, Vec::new(), vec![root]);

        let mut audit = audit_copied_roles(&proof, &mut terms);
        let mut effective = HashMap::default();
        let condition_surface = "(= copied_or_pos_j 1)";
        assert!(audit.require_spelling(&mut terms, condition, condition_surface));
        effective.insert(condition, condition_surface.to_string());
        assert!(audit.validate_effective(&terms, &effective));
        assert!(copied_structural_roles_are_static(
            &proof,
            &[true],
            &HashSet::default(),
            &terms,
            &effective,
        ));

        let reordered = format!(
            "(or {} {} {})",
            ay_proof::format_term_alethe(&terms, disjuncts[2]),
            ay_proof::format_term_alethe(&terms, disjuncts[0]),
            ay_proof::format_term_alethe(&terms, disjuncts[1]),
        );
        assert!(audit.require_spelling(&mut terms, root, &reordered));
        effective.insert(root, reordered);
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
    fn copied_or_pos_rejects_rendered_shape_drift() {
        let mut terms = TermStore::new();
        let a = terms.mk_var("copied_or_shape_a", Sort::Bool);
        let b = terms.mk_var("copied_or_shape_b", Sort::Bool);
        let c = terms.mk_var("copied_or_shape_c", Sort::Bool);
        let d = terms.mk_var("copied_or_shape_d", Sort::Bool);
        let root = terms.mk_or(vec![a, b, c]);
        let not_root = terms.mk_not_raw(root);
        let disjuncts = match terms.get(root) {
            ay_core::TermData::App(_, disjuncts) => disjuncts.clone(),
            other => panic!("expected OR, got {other:?}"),
        };
        let mut clause = vec![not_root];
        clause.extend(disjuncts.iter().copied());
        let mut proof = Proof::new();
        proof.add_rule_step(AletheRule::OrPos(0), clause, Vec::new(), vec![root]);

        let whitespace = format!(
            "(or\t{}\n{} {})",
            ay_proof::format_term_alethe(&terms, disjuncts[0]),
            ay_proof::format_term_alethe(&terms, disjuncts[1]),
            ay_proof::format_term_alethe(&terms, disjuncts[2]),
        );
        let mut whitespace_audit = audit_copied_roles(&proof, &mut terms);
        assert!(whitespace_audit.require_spelling(&mut terms, root, &whitespace));
        let mut whitespace_effective = HashMap::default();
        whitespace_effective.insert(root, whitespace);
        assert!(whitespace_audit.validate_effective(&terms, &whitespace_effective));

        for surface in [
            "(or copied_or_shape_a (or copied_or_shape_b copied_or_shape_c))".to_string(),
            "(=> copied_or_shape_a copied_or_shape_b)".to_string(),
            "(orcopied_or_shape_a copied_or_shape_b copied_or_shape_c)".to_string(),
            format!(
                "(or {} {} {})",
                ay_proof::format_term_alethe(&terms, disjuncts[0]),
                ay_proof::format_term_alethe(&terms, disjuncts[1]),
                ay_proof::format_term_alethe(&terms, d),
            ),
        ] {
            let mut audit = audit_copied_roles(&proof, &mut terms);
            assert!(audit.require_spelling(&mut terms, root, &surface));
            let mut effective = HashMap::default();
            effective.insert(root, surface);
            assert!(!audit.validate_effective(&terms, &effective));
        }
    }

    #[test]
    fn copied_or_pos_rejects_malformed_source_contracts() {
        let mut terms = TermStore::new();
        let a = terms.mk_var("copied_or_contract_a", Sort::Bool);
        let b = terms.mk_var("copied_or_contract_b", Sort::Bool);
        let root = terms.mk_or(vec![a, b]);
        let not_root = terms.mk_not_raw(root);
        let valid = vec![not_root, a, b];
        let premise = ProofId(0);
        let cases = [
            (AletheRule::OrPos(0), valid.clone(), Vec::new(), Vec::new()),
            (AletheRule::OrPos(0), valid.clone(), Vec::new(), vec![a]),
            (
                AletheRule::OrPos(0),
                valid.clone(),
                Vec::new(),
                vec![root, root],
            ),
            (
                AletheRule::OrPos(0),
                valid.clone(),
                vec![premise],
                vec![root],
            ),
            (
                AletheRule::OrPos(0),
                vec![not_root, a, a],
                Vec::new(),
                vec![root],
            ),
            (AletheRule::OrPos(1), valid, Vec::new(), vec![root]),
        ];
        for (rule, clause, premises, args) in cases {
            let mut proof = Proof::new();
            if !premises.is_empty() {
                proof.add_assume(a, None);
            }
            proof.add_rule_step(rule, clause, premises, args);
            let mut audit = ProvenanceSurfaceAudit::default();
            assert!(!audit.protect_copied_resolution_and_farkas_roles(
                &proof,
                &vec![true; proof.steps.len()],
                &HashSet::default(),
                &mut terms,
            ));
        }

        let int_child = terms.mk_var("copied_or_contract_int", Sort::Int);
        let malformed_root = terms.mk_app(Symbol::named("or"), [a, int_child], Sort::Bool);
        let malformed_not_root = terms.mk_not_raw(malformed_root);
        let mut malformed = Proof::new();
        malformed.add_rule_step(
            AletheRule::OrPos(0),
            vec![malformed_not_root, a, int_child],
            Vec::new(),
            vec![malformed_root],
        );
        let mut audit = ProvenanceSurfaceAudit::default();
        assert!(!audit.protect_copied_resolution_and_farkas_roles(
            &malformed,
            &[true],
            &HashSet::default(),
            &mut terms,
        ));
    }
}
