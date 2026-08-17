// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

#[test]
#[cfg(debug_assertions)]
fn test_fixed_point_integrity_audit_covers_many_direct_and_congruence_merges() {
    const CLASS_MEMBERS: usize = 512;

    let mut store = TermStore::new();
    let u = Sort::Uninterpreted("IntegrityBatchU".to_string());
    let members: Vec<_> = (0..CLASS_MEMBERS)
        .map(|index| store.mk_var(format!("integrity_batch_{index}"), u.clone()))
        .collect();
    let applications: Vec<_> = members
        .iter()
        .map(|&member| store.mk_app(Symbol::named("integrity_f"), vec![member], u.clone()))
        .collect();
    let equalities: Vec<_> = members
        .windows(2)
        .map(|pair| store.mk_eq(pair[0], pair[1]))
        .collect();

    let mut euf = EufSolver::new(&store);
    for equality in equalities {
        euf.assert_literal(equality, true);
    }
    assert!(matches!(euf.check(), TheoryResult::Sat));

    let member_root = euf.enode_find_const(members[0].0);
    let application_root = euf.enode_find_const(applications[0].0);
    assert_eq!(
        euf.enodes[member_root as usize].class_size as usize,
        CLASS_MEMBERS
    );
    assert_eq!(
        euf.enodes[application_root as usize].class_size as usize,
        CLASS_MEMBERS
    );
    euf.debug_assert_enode_class_integrity(member_root, "direct-merge batch test");
    euf.debug_assert_enode_class_integrity(application_root, "congruence-merge batch test");
}
