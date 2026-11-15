//! Final-check assignment and coefficient-projection boundaries.
use super::*;

fn transitivity(eqs: [TermId; 3]) -> Vec<TheoryLit> {
    vec![
        TheoryLit::new(eqs[0], true),
        TheoryLit::new(eqs[1], true),
        TheoryLit::new(eqs[2], false),
    ]
}

fn falsifying_trail() -> Vec<Literal> {
    vec![
        Literal::positive(Variable::new(1)),
        Literal::positive(Variable::new(2)),
        Literal::negative(Variable::new(3)),
    ]
}

#[test]
fn final_plain_check_delivers_unassigned_valid_clause_as_lemma() {
    let (terms, vtt, ttv, atoms, atom_set, _, eqs) = create_euf_test_setup();
    for assigned in [false, true] {
        let mut theory =
            EufMockTheory::new().with_check_result(TheoryResult::Unsat(transitivity(eqs)));
        let mut ext = TheoryExtension::new(
            &mut theory,
            &vtt,
            &ttv,
            &atoms,
            &atom_set,
            Some(&terms),
            None,
        );
        let ctx = if assigned {
            MockContext::new().with_trail(falsifying_trail())
        } else {
            MockContext::new()
        };
        let result = ext.check(&ctx);
        let mut expected = vec![
            Literal::negative(Variable::new(1)),
            Literal::negative(Variable::new(2)),
            Literal::positive(Variable::new(3)),
        ];
        expected.sort_unstable();
        let mut actual = match result {
            ExtCheckResult::Conflict(clause) if assigned => clause,
            ExtCheckResult::AddClauses(mut clauses) if !assigned => {
                assert_eq!(clauses.len(), 1);
                clauses.remove(0)
            }
            _ => panic!("validity and current falsity must be distinguished"),
        };
        actual.sort_unstable();
        assert_eq!(actual, expected);
        assert!(ext.take_pending_split().is_none());
    }
}

#[test]
fn final_farkas_conflict_without_current_false_values_refuses() {
    let (terms, vtt, ttv, atoms, atom_set, _, eqs) = create_euf_test_setup();
    for assigned in [false, true] {
        let conflict = ay_core::TheoryConflict::new(transitivity(eqs));
        let mut theory =
            EufMockTheory::new().with_check_result(TheoryResult::UnsatWithFarkas(conflict));
        let mut ext = TheoryExtension::new(
            &mut theory,
            &vtt,
            &ttv,
            &atoms,
            &atom_set,
            Some(&terms),
            None,
        );
        let ctx = if assigned {
            MockContext::new().with_trail(falsifying_trail())
        } else {
            MockContext::new()
        };
        match ext.check(&ctx) {
            ExtCheckResult::Conflict(clause) if assigned => assert_eq!(clause.len(), 3),
            ExtCheckResult::Unknown if !assigned => {}
            _ => panic!("the coefficient-aligned conflict path requires actual current falsity"),
        }
    }
}

#[test]
fn downgraded_farkas_zero_weights_cannot_project_the_valid_explanation() {
    let (mut terms, mut vtt, mut ttv, mut atoms, mut atom_set, _, eqs) = create_euf_test_setup();
    let mut conflict = transitivity(eqs);
    let mut trail = falsifying_trail();
    for index in 4..8 {
        let term = terms.mk_var(format!("padding{index}"), Sort::Bool);
        vtt.insert(index, term);
        ttv.insert(term, index);
        atoms.push(term);
        atom_set.insert(term);
        conflict.push(TheoryLit::new(term, true));
        trail.push(Literal::positive(Variable::new(index)));
    }
    // A genuine semantic contradiction remains, but this certificate is
    // invalid: a negative coefficient must be downgraded by the real gate.
    // Its zero weights may not remove the three necessary EUF premises.
    let mut weights = vec![num_rational::Rational64::from(0); conflict.len()];
    *weights.last_mut().unwrap() = num_rational::Rational64::from(-1);
    let conflict =
        ay_core::TheoryConflict::with_farkas(conflict, ay_core::FarkasAnnotation::new(weights));
    let mut theory =
        EufMockTheory::new().with_check_result(TheoryResult::UnsatWithFarkas(conflict));
    let mut ext = TheoryExtension::new(
        &mut theory,
        &vtt,
        &ttv,
        &atoms,
        &atom_set,
        Some(&terms),
        None,
    );
    let ctx = MockContext::new().with_trail(trail);
    match ext.check(&ctx) {
        ExtCheckResult::Conflict(clause) => assert_eq!(clause.len(), 7),
        _ => panic!("the independently verified full contradiction must retain all seven literals"),
    }
}
