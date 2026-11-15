//! Actual SAT/installer boundary controls; no scripted solver verdicts.
use super::*;
use ay_core::{Sort, TermStore, TheoryLit};
use ay_sat::{Literal, Variable};

fn pos(index: u32) -> Literal {
    Literal::positive(Variable::new(index))
}

#[test]
fn tautological_conflict_never_inserts_a_remainder_or_claims_root_unsat() {
    let mut terms = TermStore::new();
    let atoms: Vec<_> = (0..5)
        .map(|i| terms.mk_var(format!("p{i}"), Sort::Bool))
        .collect();
    let map: HashMap<_, _> = atoms.iter().copied().zip(0u32..).collect();
    let mut conflict = vec![
        TheoryLit::new(atoms[0], true),
        TheoryLit::new(atoms[0], false),
    ];
    conflict.extend(atoms[1..].iter().map(|&term| TheoryLit::new(term, false)));
    for proof_enabled in [false, true] {
        let mut sat = ay_sat::Solver::new(5);
        sat.set_preprocess_enabled(false);
        for index in 1..5 {
            sat.add_clause(vec![pos(index)]);
        }
        assert!(sat.solve().into_inner().is_sat());
        let before = sat.issued_original_clause_id_max();
        let mut last = None;
        let mut reason = None;
        let outcome = add_incremental_conflict_clause(
            &mut last,
            &mut reason,
            &mut sat,
            &map,
            &conflict,
            "tautology-control",
            true,
            "unmapped control",
            proof_enabled,
        );
        assert!(matches!(
            outcome,
            AddConflictClauseOutcome::Break(SolveResult::Unknown)
        ));
        assert!(matches!(last, Some(SolveResult::Unknown)));
        assert_eq!(sat.issued_original_clause_id_max(), before);
        assert!(
            sat.solve().into_inner().is_sat(),
            "no strengthened remainder may exclude this witness"
        );
    }
}

#[test]
fn satisfied_root_literal_is_not_deleted_from_a_valid_clause() {
    let mut terms = TermStore::new();
    let a = terms.mk_var("a", Sort::Int);
    let b = terms.mk_var("b", Sort::Int);
    let c = terms.mk_var("c", Sort::Int);
    let ab = terms.mk_eq(a, b);
    let bc = terms.mk_eq(b, c);
    let ac = terms.mk_eq(a, c);
    let mut atoms = vec![ab, bc, ac];
    atoms.extend((0..3).map(|i| terms.mk_var(format!("padding{i}"), Sort::Bool)));
    let map: HashMap<_, _> = atoms.iter().copied().zip(0u32..).collect();
    let mut conflict = vec![
        TheoryLit::new(ab, true),
        TheoryLit::new(bc, true),
        TheoryLit::new(ac, false),
    ];
    conflict.extend(atoms[3..].iter().map(|&term| TheoryLit::new(term, false)));
    // Valid theory clause: not ab or not bc or ac or padding0..2.
    // Real model a=0,b=c=1 satisfies only its root literal not ab.
    let mut sat = ay_sat::Solver::new(6);
    sat.set_preprocess_enabled(false);
    sat.add_clause(vec![pos(0).negated()]);
    sat.add_clause(vec![pos(1)]);
    for index in 2..6 {
        sat.add_clause(vec![pos(index).negated()]);
    }
    assert!(sat.solve().into_inner().is_sat());
    assert_eq!(sat.var_level(pos(0).variable()), Some(0));
    assert_eq!(sat.value(pos(0).variable()), Some(false));
    let mut last = None;
    let mut reason = None;
    let outcome = add_incremental_conflict_clause(
        &mut last,
        &mut reason,
        &mut sat,
        &map,
        &conflict,
        "root-control",
        true,
        "unmapped control",
        false,
    );
    assert!(matches!(outcome, AddConflictClauseOutcome::Added { .. }));
    assert!(last.is_none());
    assert!(sat.solve().into_inner().is_sat());
}

#[test]
fn nonempty_partial_transitivity_mapping_refuses_without_installing_a_clause() {
    let mut terms = TermStore::new();
    let a = terms.mk_var("a", Sort::Int);
    let b = terms.mk_var("b", Sort::Int);
    let c = terms.mk_var("c", Sort::Int);
    let ab = terms.mk_eq(a, b);
    let bc = terms.mk_eq(b, c);
    let ac = terms.mk_eq(a, c);
    let conflict = vec![
        TheoryLit::new(ab, true),
        TheoryLit::new(bc, true),
        TheoryLit::new(ac, false),
    ];
    // Complete theorem: not ab or not bc or ac. Omitting bc would exclude
    // the genuine model a=b=0,c=1, whose SAT abstraction is ab=true,ac=false.
    let map: HashMap<_, _> = [(ab, 0), (ac, 1)].into_iter().collect();
    for proof_enabled in [false, true] {
        let mut sat = ay_sat::Solver::new(2);
        sat.set_preprocess_enabled(false);
        sat.add_clause(vec![pos(0)]);
        sat.add_clause(vec![pos(1).negated()]);
        assert!(sat.solve().into_inner().is_sat());
        let before = sat.issued_original_clause_id_max();
        let mut last = None;
        let mut reason = None;
        let outcome = add_incremental_conflict_clause(
            &mut last,
            &mut reason,
            &mut sat,
            &map,
            &conflict,
            "partial-control",
            true,
            "unmapped control",
            proof_enabled,
        );
        assert!(matches!(
            outcome,
            AddConflictClauseOutcome::Break(SolveResult::Unknown)
        ));
        assert_eq!(sat.issued_original_clause_id_max(), before);
        assert!(sat.solve().into_inner().is_sat());
    }
}
