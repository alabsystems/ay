const QF_LIA_LET_BRIDGE_RESOLUTION: &str = r#"
(set-logic QF_LIA)
(declare-const x Int)
(assert (let ((?v_0 x)) (= ?v_0 ?v_0)))
(check-sat)
"#;

#[test]
fn let_bridged_derived_complement_is_accepted_by_carcara() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Int);
    let equality = terms.mk_app(ay_core::Symbol::named("="), vec![x, x], Sort::Bool);
    let disequality = terms.mk_not_raw(equality);

    let let_surface = "(let ((?v_0 x)) (= ?v_0 ?v_0))";
    let mut overrides: DetHashMap<TermId, String> = det_hash_map_new();
    overrides.insert(equality, let_surface.to_string());
    overrides.insert(disequality, format!("(not {let_surface})"));

    let mut proof = Proof::new();
    let positive = proof.add_assume(equality, None);
    let negative = proof.add_theory_lemma("test", vec![disequality]);
    proof.add_resolution(Vec::new(), equality, positive, negative);

    let alethe = export_alethe_with_problem_scope_and_overrides(
        &proof,
        &terms,
        &[equality],
        Some(&overrides),
    );
    assert_carcara_verdict(
        "let_bridged_derived_complement",
        QF_LIA_LET_BRIDGE_RESOLUTION,
        &alethe,
        "holey",
    );

    // Reconstruct the pre-fix document: the derived complement retained its
    // independent authored spelling instead of negating the certified
    // canonical bridge. Carcara must reject that resolution step.
    let canonical = "(step t1 (cl (not (= x x))) :rule hole)";
    let authored = format!("(step t1 (cl (not {let_surface})) :rule hole)");
    assert!(alethe.contains(canonical), "{alethe}");
    let unbridged = alethe.replacen(canonical, &authored, 1);
    assert_ne!(unbridged, alethe);

    // Through the shared runner, so this rejection differential cannot pass
    // on a document whose verdict is not evidence at all.
    assert_carcara_verdict(
        "let_bridged_derived_complement_unpatched",
        QF_LIA_LET_BRIDGE_RESOLUTION,
        &unbridged,
        "invalid",
    );
}
