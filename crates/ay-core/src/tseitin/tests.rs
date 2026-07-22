// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;
use crate::Sort;

#[test]
fn test_tseitin_state_default_is_dimacs_1_indexed() {
    let state = TseitinState::default();
    assert_eq!(state.next_var, 1);
}

#[test]
fn test_tseitin_simple_and() {
    let mut store = TermStore::new();

    let a = store.mk_var("a", Sort::Bool);
    let b = store.mk_var("b", Sort::Bool);
    let and_ab = store.mk_and(vec![a, b]);

    let tseitin = Tseitin::new(&store);
    let result = tseitin.transform(and_ab);

    // Should have clauses for:
    // - v_and ↔ (a ∧ b)
    // - v_and (root assertion)
    assert!(result.num_vars >= 3); // a, b, and_ab
    assert!(!result.clauses.is_empty());
}

#[test]
fn test_tseitin_simple_or() {
    let mut store = TermStore::new();

    let a = store.mk_var("a", Sort::Bool);
    let b = store.mk_var("b", Sort::Bool);
    let or_ab = store.mk_or(vec![a, b]);

    let tseitin = Tseitin::new(&store);
    let result = tseitin.transform(or_ab);

    assert!(result.num_vars >= 3);
    assert!(!result.clauses.is_empty());
}

#[test]
fn test_tseitin_negation() {
    let mut store = TermStore::new();

    let a = store.mk_var("a", Sort::Bool);
    let not_a = store.mk_not(a);

    let tseitin = Tseitin::new(&store);
    let result = tseitin.transform(not_a);

    // not(a) should just flip polarity
    // The root assertion should be ¬a
    assert!(!result.clauses.is_empty());
    // Should have a unit clause with negative literal
    let has_negative_unit = result.clauses.iter().any(|c| c.0.len() == 1 && c.0[0] < 0);
    assert!(has_negative_unit);
}

#[test]
fn test_tseitin_ite() {
    let mut store = TermStore::new();

    let c = store.mk_var("c", Sort::Bool);
    let a = store.mk_var("a", Sort::Bool);
    let b = store.mk_var("b", Sort::Bool);
    let ite = store.mk_ite(c, a, b);

    let tseitin = Tseitin::new(&store);
    let result = tseitin.transform(ite);

    // Full ITE encoding: 4 ternary clauses + root assertion.
    assert!(result.clauses.len() >= 5);
    let ternary_count = result.clauses.iter().filter(|c| c.0.len() == 3).count();
    assert_eq!(ternary_count, 4);
}

#[test]
fn test_tseitin_ite_both_polarities_emits_full_encoding() {
    let mut store = TermStore::new();

    let c = store.mk_var("c", Sort::Bool);
    let a = store.mk_var("a", Sort::Bool);
    let b = store.mk_var("b", Sort::Bool);
    let ite = store.mk_ite(c, a, b);

    // Force encoding at both polarities for the SAME ITE term.
    let mut tseitin = Tseitin::new(&store);
    let pos = tseitin.encode(ite, true);
    let neg = tseitin.encode(ite, false);
    tseitin.add_clause(CnfClause::unit(pos));
    tseitin.add_clause(CnfClause::unit(neg));

    // Full encoding is 4 ternary clauses total; the second encode should not duplicate.
    let ternary_count = tseitin
        .all_clauses()
        .iter()
        .filter(|cl| cl.0.len() == 3)
        .count();
    assert_eq!(ternary_count, 4);
}

#[test]
fn test_tseitin_boolean_eq() {
    let mut store = TermStore::new();

    let a = store.mk_var("a", Sort::Bool);
    let b = store.mk_var("b", Sort::Bool);
    let eq_ab = store.mk_eq(a, b);

    let tseitin = Tseitin::new(&store);
    let result = tseitin.transform(eq_ab);

    // Boolean equality generates 4 clauses + root assertion
    assert!(result.clauses.len() >= 4);
}

#[test]
fn test_tseitin_nested() {
    let mut store = TermStore::new();

    // (a ∧ b) ∨ (c ∧ d)
    let a = store.mk_var("a", Sort::Bool);
    let b = store.mk_var("b", Sort::Bool);
    let c = store.mk_var("c", Sort::Bool);
    let d = store.mk_var("d", Sort::Bool);

    let and_ab = store.mk_and(vec![a, b]);
    let and_cd = store.mk_and(vec![c, d]);
    let or_both = store.mk_or(vec![and_ab, and_cd]);

    let tseitin = Tseitin::new(&store);
    let result = tseitin.transform(or_both);

    // Should have variables for a, b, c, d, and_ab, and_cd, or_both
    assert!(result.num_vars >= 7);
}

#[test]
fn test_tseitin_multiple_terms() {
    let mut store = TermStore::new();

    let a = store.mk_var("a", Sort::Bool);
    let b = store.mk_var("b", Sort::Bool);
    let c = store.mk_var("c", Sort::Bool);

    let terms = vec![a, b, c];

    let tseitin = Tseitin::new(&store);
    let result = tseitin.transform_all(&terms);

    // Should have unit clauses for a, b, c
    assert_eq!(result.clauses.iter().filter(|c| c.0.len() == 1).count(), 3);
}

#[test]
fn test_variable_mapping() {
    let mut store = TermStore::new();

    let a = store.mk_var("a", Sort::Bool);
    let b = store.mk_var("b", Sort::Bool);
    let and_ab = store.mk_and(vec![a, b]);

    let tseitin = Tseitin::new(&store);
    let result = tseitin.transform(and_ab);

    // Check that we can map back from variables to terms
    assert!(result.var_for_term(a).is_some());
    assert!(result.var_for_term(b).is_some());

    let var_a = result.var_for_term(a).unwrap();
    let var_b = result.var_for_term(b).unwrap();

    assert_eq!(result.term_for_var(var_a), Some(a));
    assert_eq!(result.term_for_var(var_b), Some(b));
}

#[test]
fn test_incremental_api() {
    let mut store = TermStore::new();

    let a = store.mk_var("a", Sort::Bool);
    let b = store.mk_var("b", Sort::Bool);
    let or_ab = store.mk_or(vec![a, b]);

    let mut tseitin = Tseitin::new(&store);

    // First batch: encode (a ∨ b)
    let _lit1 = tseitin.encode_and_assert(or_ab);
    let clauses1 = tseitin.take_new_clauses();
    assert!(!clauses1.is_empty());

    // Record variable assignment for 'a'
    let var_a = tseitin.get_var_for_term(a).unwrap();

    // Second batch: encode 'a' again - should reuse same variable
    let _lit2 = tseitin.encode_and_assert(a);
    let clauses2 = tseitin.take_new_clauses();

    // 'a' was already encoded, so we should just get a unit clause
    // with the same variable
    assert_eq!(clauses2.len(), 1);
    let unit_clause = &clauses2[0];
    assert_eq!(unit_clause.0.len(), 1);
    assert_eq!(unit_clause.0[0].unsigned_abs(), var_a);
}

#[test]
fn test_incremental_shared_variables() {
    let mut store = TermStore::new();

    // Create terms that share subterms
    let a = store.mk_var("a", Sort::Bool);
    let b = store.mk_var("b", Sort::Bool);
    let c = store.mk_var("c", Sort::Bool);
    let and_ab = store.mk_and(vec![a, b]);
    let or_ab_c = store.mk_or(vec![and_ab, c]);

    let mut tseitin = Tseitin::new(&store);

    // First: encode (a ∧ b) ∨ c
    let _ = tseitin.encode_and_assert(or_ab_c);
    let _ = tseitin.take_new_clauses();

    // Get variable for 'a'
    let var_a_first = tseitin.get_var_for_term(a).unwrap();

    // Second: encode just 'a' - should get same variable
    let _ = tseitin.encode_and_assert(a);

    let var_a_second = tseitin.get_var_for_term(a).unwrap();

    // Critical: variable for 'a' should be the same in both encodings
    assert_eq!(var_a_first, var_a_second);
}

#[test]
fn test_encode_assertion_api() {
    let mut store = TermStore::new();

    let a = store.mk_var("a", Sort::Bool);
    let b = store.mk_var("b", Sort::Bool);
    let and_ab = store.mk_and(vec![a, b]);

    let mut tseitin = Tseitin::new(&store);

    // Use the new encode_assertion API
    let enc = tseitin.encode_assertion(and_ab);

    // Should get a valid root literal
    assert_ne!(enc.root_lit, 0);

    // Should get definitional clauses for the AND encoding
    // AND(a,b) creates: (¬v ∨ a), (¬v ∨ b), (¬a ∨ ¬b ∨ v)
    assert!(!enc.def_clauses.is_empty());

    // The root literal should be the variable for and_ab
    let var_and = tseitin.get_var_for_term(and_ab).unwrap();
    assert_eq!(enc.root_lit.unsigned_abs(), var_and);

    // Encoding the same term again should return empty def_clauses
    // (term already encoded, no new definitions needed)
    let enc2 = tseitin.encode_assertion(and_ab);
    assert_eq!(enc2.root_lit, enc.root_lit);
    assert!(enc2.def_clauses.is_empty());
}

#[test]
fn test_encode_assertion_with_proofs_tracks_def_annotations() {
    use crate::proof::AletheRule;

    let mut store = TermStore::new();

    let a = store.mk_var("a", Sort::Bool);
    let b = store.mk_var("b", Sort::Bool);
    let and_ab = store.mk_and(vec![a, b]);

    let mut tseitin = Tseitin::new_with_proofs(&store);

    let enc = tseitin.encode_assertion(and_ab);
    let proofs = enc
        .def_proof_annotations
        .as_ref()
        .expect("proof tracking should annotate incremental clauses");
    assert_eq!(proofs.len(), enc.def_clauses.len());

    let annotated: Vec<_> = proofs.iter().filter_map(|proof| proof.as_ref()).collect();
    let rules: Vec<_> = annotated.iter().map(|proof| &proof.rule).collect();
    assert!(rules.contains(&&AletheRule::AndPos(0)));
    assert!(rules.contains(&&AletheRule::AndPos(1)));
    assert!(rules.contains(&&AletheRule::AndNeg));

    let enc2 = tseitin.encode_assertion(and_ab);
    assert_eq!(enc2.root_lit, enc.root_lit);
    assert!(enc2.def_clauses.is_empty());
    assert!(
        enc2.def_proof_annotations
            .as_ref()
            .is_some_and(Vec::is_empty),
        "re-encoding an existing term should not emit fresh proof annotations"
    );
}

#[test]
fn test_encode_assertion_separates_defs_from_root() {
    let mut store = TermStore::new();

    let a = store.mk_var("a", Sort::Bool);
    let b = store.mk_var("b", Sort::Bool);
    let and_ab = store.mk_and(vec![a, b]);

    let mut tseitin = Tseitin::new(&store);

    let enc = tseitin.encode_assertion(and_ab);

    // The def_clauses should NOT contain a unit clause for root_lit
    // (that's the activation, which the caller adds separately)
    let root_as_unit = CnfClause::unit(enc.root_lit);
    let has_root_unit = enc.def_clauses.contains(&root_as_unit);
    assert!(
        !has_root_unit,
        "encode_assertion should NOT include root activation in def_clauses"
    );

    // Compare with encode_and_assert which DOES include the root unit clause
    let mut tseitin2 = Tseitin::new(&store);
    let _ = tseitin2.encode_and_assert(and_ab);
    let all_clauses = tseitin2.take_new_clauses();
    let has_root_unit2 = all_clauses.iter().any(|c| c.0.len() == 1);
    assert!(
        has_root_unit2,
        "encode_and_assert SHOULD include root activation"
    );
}

/// Regression test for #2889: Let binding in Tseitin should produce an
/// opaque literal instead of panicking.
#[test]
fn test_let_binding_does_not_panic() {
    let mut store = TermStore::new();

    let x = store.mk_var("x", Sort::Bool);
    let let_term = store.mk_let(vec![("y".to_string(), x)], x);

    let tseitin = Tseitin::new(&store);
    // In release mode this must not panic; it returns an opaque literal.
    let result = tseitin.transform(let_term);
    assert!(!result.clauses.is_empty());
}

// ======================================================================
// Clausification proof annotation tests (#6031)
// ======================================================================

#[test]
fn test_proof_tracking_disabled_by_default() {
    let mut store = TermStore::new();
    let a = store.mk_var("a", Sort::Bool);
    let b = store.mk_var("b", Sort::Bool);
    let and_ab = store.mk_and(vec![a, b]);

    let tseitin = Tseitin::new(&store);
    let result = tseitin.transform(and_ab);
    assert!(result.proof_annotations.is_none());
}

#[test]
fn test_proof_and_annotations() {
    use crate::proof::AletheRule;

    let mut store = TermStore::new();
    let a = store.mk_var("a", Sort::Bool);
    let b = store.mk_var("b", Sort::Bool);
    let and_ab = store.mk_and(vec![a, b]);

    let tseitin = Tseitin::new_with_proofs(&store);
    let result = tseitin.transform(and_ab);

    let proofs = result.proof_annotations.as_ref().expect("proofs enabled");
    assert_eq!(proofs.len(), result.clauses.len());

    // AND generates: and_pos(0), and_pos(1), and_neg, then root unit
    let annotated: Vec<_> = proofs.iter().filter_map(|p| p.as_ref()).collect();
    assert!(
        annotated.len() >= 3,
        "AND should produce at least 3 annotated clauses"
    );

    let rules: Vec<_> = annotated.iter().map(|p| &p.rule).collect();
    assert!(rules.contains(&&AletheRule::AndPos(0)));
    assert!(rules.contains(&&AletheRule::AndPos(1)));
    assert!(rules.contains(&&AletheRule::AndNeg));

    // All annotated clauses should reference the AND term
    for proof in &annotated {
        assert_eq!(proof.source_term, and_ab);
    }
}

#[test]
fn test_proof_or_annotations() {
    use crate::proof::AletheRule;

    let mut store = TermStore::new();
    let a = store.mk_var("a", Sort::Bool);
    let b = store.mk_var("b", Sort::Bool);
    let or_ab = store.mk_or(vec![a, b]);

    let tseitin = Tseitin::new_with_proofs(&store);
    let result = tseitin.transform(or_ab);

    let proofs = result.proof_annotations.as_ref().expect("proofs enabled");
    assert_eq!(proofs.len(), result.clauses.len());

    let annotated: Vec<_> = proofs.iter().filter_map(|p| p.as_ref()).collect();
    assert!(
        annotated.len() >= 3,
        "OR should produce at least 3 annotated clauses"
    );

    let rules: Vec<_> = annotated.iter().map(|p| &p.rule).collect();
    assert!(rules.contains(&&AletheRule::OrPos(0)));
    assert!(rules.iter().any(|r| matches!(r, AletheRule::OrNeg)));
}

#[test]
fn test_proof_ite_annotations() {
    use crate::proof::AletheRule;

    let mut store = TermStore::new();
    let c = store.mk_var("c", Sort::Bool);
    let t = store.mk_var("t", Sort::Bool);
    let e = store.mk_var("e", Sort::Bool);
    let ite = store.mk_ite(c, t, e);

    let tseitin = Tseitin::new_with_proofs(&store);
    let result = tseitin.transform(ite);

    let proofs = result.proof_annotations.as_ref().expect("proofs enabled");
    assert_eq!(proofs.len(), result.clauses.len());

    let annotated: Vec<_> = proofs.iter().filter_map(|p| p.as_ref()).collect();
    assert_eq!(
        annotated.len(),
        4,
        "ITE full encoding should produce 4 annotated clauses"
    );

    let rules: Vec<_> = annotated.iter().map(|p| &p.rule).collect();
    assert!(rules.contains(&&AletheRule::ItePos1));
    assert!(rules.contains(&&AletheRule::ItePos2));
    assert!(rules.contains(&&AletheRule::IteNeg1));
    assert!(rules.contains(&&AletheRule::IteNeg2));
}

#[test]
fn test_proof_equiv_annotations() {
    use crate::proof::AletheRule;
    use crate::term::Symbol;

    let mut store = TermStore::new();
    let a = store.mk_var("a", Sort::Bool);
    let b = store.mk_var("b", Sort::Bool);
    // mk_eq on Bool rewrites to ITE internally (#3421).
    // Use mk_app to create a raw (= a b) App that hits encode_eq.
    let eq_ab = store.mk_app(Symbol::named("="), vec![a, b], Sort::Bool);

    let tseitin = Tseitin::new_with_proofs(&store);
    let result = tseitin.transform(eq_ab);

    let proofs = result.proof_annotations.as_ref().expect("proofs enabled");
    assert_eq!(proofs.len(), result.clauses.len());

    let annotated: Vec<_> = proofs.iter().filter_map(|p| p.as_ref()).collect();
    assert_eq!(
        annotated.len(),
        4,
        "EQUIV should produce 4 annotated clauses"
    );

    let rules: Vec<_> = annotated.iter().map(|p| &p.rule).collect();
    assert!(rules.contains(&&AletheRule::EquivPos1));
    assert!(rules.contains(&&AletheRule::EquivPos2));
    assert!(rules.contains(&&AletheRule::EquivNeg1));
    assert!(rules.contains(&&AletheRule::EquivNeg2));
}

#[test]
fn test_proof_xor_annotations() {
    use crate::proof::AletheRule;

    let mut store = TermStore::new();
    let a = store.mk_var("a", Sort::Bool);
    let b = store.mk_var("b", Sort::Bool);
    let xor_ab = store.mk_xor(a, b);

    let tseitin = Tseitin::new_with_proofs(&store);
    let result = tseitin.transform(xor_ab);

    let proofs = result.proof_annotations.as_ref().expect("proofs enabled");
    assert_eq!(proofs.len(), result.clauses.len());

    let annotated: Vec<_> = proofs.iter().filter_map(|p| p.as_ref()).collect();
    assert_eq!(annotated.len(), 4, "XOR should produce 4 annotated clauses");

    let rules: Vec<_> = annotated.iter().map(|p| &p.rule).collect();
    assert!(rules.contains(&&AletheRule::XorPos1));
    assert!(rules.contains(&&AletheRule::XorPos2));
    assert!(rules.contains(&&AletheRule::XorNeg1));
    assert!(rules.contains(&&AletheRule::XorNeg2));
}

#[test]
fn test_proof_annotations_parallel_to_clauses() {
    let mut store = TermStore::new();
    let a = store.mk_var("a", Sort::Bool);
    let b = store.mk_var("b", Sort::Bool);
    let c = store.mk_var("c", Sort::Bool);
    // (a AND b) OR c — nested, multiple connectives
    let and_ab = store.mk_and(vec![a, b]);
    let or_abc = store.mk_or(vec![and_ab, c]);

    let tseitin = Tseitin::new_with_proofs(&store);
    let result = tseitin.transform(or_abc);

    let proofs = result.proof_annotations.as_ref().expect("proofs enabled");
    assert_eq!(
        proofs.len(),
        result.clauses.len(),
        "proof_annotations must be parallel to clauses"
    );
}
