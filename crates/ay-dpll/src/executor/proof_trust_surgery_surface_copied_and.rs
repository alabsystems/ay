// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Rendered-role authentication for copied Boolean AND projections.

use ay_core::term::TermData;
use ay_core::{AletheRule, Sort, Symbol, TermId, TermStore};

use super::{spend_scan_work, ProvenanceSurfaceAudit};

const MAX_AND_ARITY: usize =
    crate::executor::proof_trust_surgery_provenance::MAX_PROVENANCE_REPAIR_TERMS;

fn exact_clause_permutation(clause: &[TermId], expected: [TermId; 2]) -> bool {
    if clause.len() != expected.len() {
        return false;
    }
    let mut actual = [clause[0], clause[1]];
    actual.sort_unstable();
    let mut expected = expected;
    expected.sort_unstable();
    actual == expected
}

/// Authenticate the exact SAT-produced `and_pos(i)` tautology named by its
/// singleton source argument. The separate copied role permits duplicate
/// selected operands while still requiring the final rendered AND to preserve
/// the complete immediate operand multiset and multiplicities.
pub(super) fn protect_copied_and_pos_role(
    audit: &mut ProvenanceSurfaceAudit,
    terms: &mut TermStore,
    rule: &AletheRule,
    clause: &[TermId],
    args: &[TermId],
    work: &mut usize,
) -> bool {
    let AletheRule::AndPos(index) = rule else {
        return false;
    };
    let [root] = args else {
        return false;
    };
    let root = *root;
    let selected = {
        let TermData::App(Symbol::Named(head), conjuncts) = terms.get(root) else {
            return false;
        };
        if head != "and"
            || *terms.sort(root) != Sort::Bool
            || !(2..=MAX_AND_ARITY).contains(&conjuncts.len())
            || !spend_scan_work(work, conjuncts.len())
            || conjuncts
                .iter()
                .any(|&conjunct| *terms.sort(conjunct) != Sort::Bool)
        {
            return false;
        }
        let Some(&selected) = conjuncts.get(*index as usize) else {
            return false;
        };
        selected
    };
    let not_root = terms.mk_not_raw(root);
    if !exact_clause_permutation(clause, [not_root, selected]) {
        return false;
    }
    let role = (root, *index, selected);
    if audit.copied_and_projection_roles.len() >= super::super::MAX_AUDITED_FARKAS_LEMMAS
        && !audit.copied_and_projection_roles.contains(&role)
    {
        return false;
    }
    // Protect the source, raw gate, selected conjunct, and both Boolean
    // polarities. `protect_operand` recursively covers all source children.
    audit.protect_operand(terms, root);
    audit.protect_operand(terms, not_root);
    audit.protect_operand(terms, selected);
    audit.copied_and_projection_roles.insert(role);
    !audit.overflowed
}

#[cfg(test)]
mod tests {
    use ay_core::kani_compat::{DetHashMap as HashMap, DetHashSet as HashSet};
    use ay_core::{AletheRule, Proof, ProofId, Sort, Symbol, TermId, TermStore};

    use super::super::{copied_structural_roles_are_static, ProvenanceSurfaceAudit};

    fn add_projection(
        proof: &mut Proof,
        rule: AletheRule,
        clause: Vec<TermId>,
        premises: Vec<ProofId>,
        args: Vec<TermId>,
    ) {
        proof.add_rule_step(rule, clause, premises, args);
    }

    fn collect_roles(proof: &Proof, terms: &mut TermStore) -> Option<ProvenanceSurfaceAudit> {
        let mut audit = ProvenanceSurfaceAudit::default();
        audit
            .protect_copied_resolution_and_farkas_roles(
                proof,
                &vec![true; proof.steps.len()],
                &HashSet::default(),
                terms,
            )
            .then_some(audit)
    }

    #[test]
    fn copied_and_pos_accepts_t7_shape_reordering_and_identity_descendant() {
        let mut terms = TermStore::new();
        let t = terms.mk_bool(true);
        let f = terms.mk_bool(false);
        let a = terms.mk_var("copied_and_t7_a", Sort::Bool);
        let b = terms.mk_var("copied_and_t7_b", Sort::Bool);
        let root = terms.mk_app(Symbol::named("and"), [t, t, a, f, b], Sort::Bool);
        let not_root = terms.mk_not_raw(root);
        let mut proof = Proof::new();
        add_projection(
            &mut proof,
            AletheRule::AndPos(3),
            vec![not_root, f],
            Vec::new(),
            vec![root],
        );

        let mut audit = collect_roles(&proof, &mut terms).expect("exact copied role");
        let root_surface = "(and false true copied_and_t7_b true copied_and_t7_a)";
        assert!(audit.require_spelling(&mut terms, root, root_surface));
        assert!(audit.require_spelling(&mut terms, a, "copied_and_t7_a"));
        let mut effective = HashMap::default();
        effective.insert(root, root_surface.to_string());
        effective.insert(a, "copied_and_t7_a".to_string());
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
    fn copied_and_pos_accepts_duplicate_selected_operand_with_exact_multiplicity() {
        let mut terms = TermStore::new();
        let f = terms.mk_bool(false);
        let a = terms.mk_var("copied_and_duplicate_a", Sort::Bool);
        let root = terms.mk_app(Symbol::named("and"), [f, a, f], Sort::Bool);
        let not_root = terms.mk_not_raw(root);
        let mut proof = Proof::new();
        add_projection(
            &mut proof,
            AletheRule::AndPos(0),
            vec![not_root, f],
            Vec::new(),
            vec![root],
        );
        let mut audit = collect_roles(&proof, &mut terms).expect("duplicate copied role");
        let surface = "(and false false copied_and_duplicate_a)";
        assert!(audit.require_spelling(&mut terms, root, surface));
        let mut effective = HashMap::default();
        effective.insert(root, surface.to_string());
        assert!(audit.validate_effective(&terms, &effective));
        assert!(copied_structural_roles_are_static(
            &proof,
            &[true],
            &HashSet::default(),
            &terms,
            &effective,
        ));

        for wrong in [
            "(and false copied_and_duplicate_a)",
            "(and false (and false copied_and_duplicate_a))",
            "(or false false copied_and_duplicate_a)",
        ] {
            let mut wrong_audit = collect_roles(&proof, &mut terms).expect("canonical role");
            assert!(wrong_audit.require_spelling(&mut terms, root, wrong));
            let mut wrong_effective = HashMap::default();
            wrong_effective.insert(root, wrong.to_string());
            assert!(!wrong_audit.validate_effective(&terms, &wrong_effective));
        }
    }

    #[test]
    fn copied_and_pos_audit_shares_exotic_surface_tokenization_with_printer() {
        let mut terms = TermStore::new();
        let string_var = terms.mk_var("copied_and_string_s", Sort::String);
        let string = terms.mk_string("a)\"b".to_string());
        let equality = terms.mk_app(Symbol::named("="), [string_var, string], Sort::Bool);
        let exotic = terms.mk_var("copied_and_a|b\\c", Sort::Bool);
        let root = terms.mk_app(Symbol::named("and"), [exotic, equality], Sort::Bool);
        let not_root = terms.mk_not_raw(root);
        let mut proof = Proof::new();
        add_projection(
            &mut proof,
            AletheRule::AndPos(0),
            vec![not_root, exotic],
            Vec::new(),
            vec![root],
        );

        let mut audit = collect_roles(&proof, &mut terms).expect("exact exotic role");
        let surface = r#"(and (= copied_and_string_s "a)""b") |copied_and_a\|b\\c|)"#;
        assert!(audit.require_spelling(&mut terms, root, surface));
        let mut effective = HashMap::default();
        effective.insert(root, surface.to_string());
        assert!(audit.validate_effective(&terms, &effective));
    }

    #[test]
    fn copied_and_pos_rejects_malformed_native_contracts() {
        let mut terms = TermStore::new();
        let a = terms.mk_var("copied_and_bad_a", Sort::Bool);
        let b = terms.mk_var("copied_and_bad_b", Sort::Bool);
        let root = terms.mk_app(Symbol::named("and"), [a, b], Sort::Bool);
        let not_root = terms.mk_not_raw(root);
        let wrong_gate = terms.mk_not_raw(a);
        let premise = ProofId(0);
        let cases = [
            (
                AletheRule::AndPos(2),
                vec![not_root, b],
                Vec::new(),
                vec![root],
            ),
            (
                AletheRule::AndPos(0),
                vec![not_root, b],
                Vec::new(),
                vec![root],
            ),
            (
                AletheRule::AndPos(0),
                vec![wrong_gate, a],
                Vec::new(),
                vec![root],
            ),
            (
                AletheRule::AndPos(0),
                vec![not_root, a],
                Vec::new(),
                Vec::new(),
            ),
            (
                AletheRule::AndPos(0),
                vec![not_root, a],
                Vec::new(),
                vec![a],
            ),
            (
                AletheRule::AndPos(0),
                vec![not_root, a],
                Vec::new(),
                vec![root, a],
            ),
            (
                AletheRule::AndPos(0),
                vec![not_root, a],
                vec![premise],
                vec![root],
            ),
        ];
        for (rule, clause, premises, args) in cases {
            let mut proof = Proof::new();
            if !premises.is_empty() {
                proof.add_assume(a, None);
            }
            add_projection(&mut proof, rule, clause, premises, args);
            assert!(collect_roles(&proof, &mut terms).is_none());
        }

        let int = terms.mk_var("copied_and_bad_int", Sort::Int);
        let ill_sorted = terms.mk_app(Symbol::named("and"), [a, int], Sort::Bool);
        let mut proof = Proof::new();
        add_projection(
            &mut proof,
            AletheRule::AndPos(0),
            vec![terms.mk_not_raw(ill_sorted), a],
            Vec::new(),
            vec![ill_sorted],
        );
        assert!(collect_roles(&proof, &mut terms).is_none());
    }

    #[test]
    fn copied_and_pos_rejects_overwide_source_before_role_registration() {
        let mut terms = TermStore::new();
        let children: Vec<TermId> = (0..65)
            .map(|index| terms.mk_var(format!("copied_and_wide_{index}"), Sort::Bool))
            .collect();
        let root = terms.mk_app(Symbol::named("and"), children.clone(), Sort::Bool);
        let not_root = terms.mk_not_raw(root);
        let mut proof = Proof::new();
        add_projection(
            &mut proof,
            AletheRule::AndPos(0),
            vec![not_root, children[0]],
            Vec::new(),
            vec![root],
        );
        assert!(collect_roles(&proof, &mut terms).is_none());
    }
}
