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

    let Some(carcara) = find_carcara() else {
        eprintln!("carcara not found, skipping external rejection differential");
        return;
    };
    let (problem_path, proof_path) = write_problem_and_proof(
        "let_bridged_derived_complement_unpatched",
        QF_LIA_LET_BRIDGE_RESOLUTION,
        &unbridged,
    );
    let output = Command::new(carcara)
        .arg("check")
        .arg("--")
        .arg(&proof_path)
        .arg(&problem_path)
        .output()
        .expect("run carcara check on the unpatched document");
    let _ = std::fs::remove_file(&problem_path);
    let _ = std::fs::remove_file(&proof_path);

    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert_eq!(
        stdout.trim(),
        "invalid",
        "the pre-fix document unexpectedly survived Carcara\nstdout: {stdout}\n\
         stderr: {stderr}\nproof:\n{unbridged}"
    );
}
