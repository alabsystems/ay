// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

fn mixed(fixture: &mut Fixture, unknown: usize) -> TermId {
    let mut children = fixture.apps[..64 - unknown].to_vec();
    children.push(fixture.terms.mk_not(fixture.apps[64]));
    // Keep the unforced applications reachable without forcing their values.
    let condition = fixture.terms.mk_var("condition", Sort::Bool);
    for &app in &fixture.apps[64 - unknown..64] {
        children.push(
            fixture
                .terms
                .mk_app(Symbol::named("or"), [condition, app], Sort::Bool),
        );
    }
    fixture
        .terms
        .mk_app(Symbol::named("and"), children, Sort::Bool)
}

#[test]
fn mixed_65_real_encoding_materializes_all_arguments_and_preserves_pair_order() {
    for kind in [Argument::Bv, Argument::FpBits] {
        for unknown in [0, 1, 2] {
            let mut fixture = Fixture::new(kind, 65);
            let root = mixed(&mut fixture, unknown);
            let cnf = encode(&fixture.terms, root);
            let scan = scan_foreign(&fixture.terms, &[root]);
            assert!(!scan.unencodable);
            assert_eq!(scan.groups.len(), 1);
            let values = unit_closure(&cnf, &mut Work(MAX_FORCING_WORK), &mut || Ok::<_, ()>(()))
                .unwrap()
                .unwrap();
            let group = &scan.groups[0];
            let signs: Vec<_> = group
                .iter()
                .map(|(term, _)| values[cnf.var_for_term(*term).unwrap() as usize])
                .collect();
            assert_eq!(signs.iter().filter(|&&v| v == 0).count(), unknown);
            let expected: Vec<_> = (0..65)
                .flat_map(|i| {
                    let signs = &signs;
                    ((i + 1)..65).filter_map(move |j| {
                        (!(signs[i] != 0 && signs[i] == signs[j])).then_some((i, j))
                    })
                })
                .collect();
            let mut allow = |_| false;
            let mut owner = FpConstruction::new(FpSolver::new(&fixture.terms), &mut allow).unwrap();
            let mut forcing = ForcedOutputs::new();
            let pairs = forcing
                .residual_pairs(&fixture.terms, &mut owner, &cnf, group, &mut || Ok(()))
                .unwrap()
                .unwrap();
            assert_eq!(pairs, expected);
            assert!(
                forcing.work.0 > 0,
                "actual 65-app CNF plus pairs must fit shared4096"
            );
            let built = owner.finish().unwrap();
            assert!(!built.has_encoding_gap);
            for &word in &fixture.words {
                assert_eq!(built.cache.bv_term_bits.get(&word).map(Vec::len), Some(64));
            }
            for &arg in &fixture.args {
                if matches!(fixture.terms.sort(arg), Sort::FloatingPoint(..)) {
                    assert!(built.cache.term_to_fp.contains_key(&arg));
                }
            }
            let mut fp = FpSolver::new(&fixture.terms);
            let plan = plan_congruence(&fixture.terms, &mut fp, &cnf, &scan);
            assert!(!plan.incomplete);
            assert_eq!(plan.clauses.len(), expected.len() * 2);
            for (clauses, &(i, j)) in plan.clauses.chunks_exact(2).zip(&expected) {
                let a = cnf.var_for_term(group[i].0).unwrap() as i32;
                let b = cnf.var_for_term(group[j].0).unwrap() as i32;
                let outputs = |clause: &[crate::executor::theories::fp::congruence::PlanLit]| {
                    clause
                        .iter()
                        .filter_map(|lit| match lit {
                            crate::executor::theories::fp::congruence::PlanLit::Tseitin(value) => {
                                Some(*value)
                            }
                            _ => None,
                        })
                        .collect::<Vec<_>>()
                };
                assert_eq!(outputs(&clauses[0]), [-a, b]);
                assert_eq!(outputs(&clauses[1]), [a, -b]);
            }
        }
    }
}

#[test]
fn residual_admission_refuses_unforced_bad_mappings_and_unsupported_arguments() {
    let mut fixture = Fixture::new(Argument::FpBits, 65);
    let root = mixed(&mut fixture, 1);
    let scan = scan_foreign(&fixture.terms, &[root]);
    for remove in [false, true] {
        let mut cnf = encode(&fixture.terms, root);
        let unknown = fixture.apps[63];
        let var = cnf.var_for_term(unknown).unwrap();
        if remove {
            cnf.term_to_var.remove(&unknown);
        } else {
            cnf.var_to_term.insert(var, fixture.apps[0]);
        }
        let mut fp = FpSolver::new(&fixture.terms);
        let plan = plan_congruence(&fixture.terms, &mut fp, &cnf, &scan);
        assert!(plan.incomplete && plan.clauses.is_empty());
        assert!(
            fp.term_to_fp().is_empty(),
            "admission precedes materialization"
        );
    }

    // Residual pairs must not turn an unsupported BV term into free bits.
    let mut fixture = Fixture::new(Argument::Bv, 65);
    let arg = fixture.terms.mk_app(
        Symbol::named("opaque_bv"),
        [fixture.words[0]],
        Sort::bitvec(64),
    );
    fixture.apps[0] = fixture.terms.mk_app(Symbol::named("g"), [arg], Sort::Bool);
    let root = mixed(&mut fixture, 0);
    let cnf = encode(&fixture.terms, root);
    let scan = scan_foreign(&fixture.terms, &[root]);
    let mut fp = FpSolver::new(&fixture.terms);
    assert!(plan_congruence(&fixture.terms, &mut fp, &cnf, &scan).incomplete);
}

#[test]
fn residual_whole_admission_work_is_shared_and_materialization_stop_is_sticky() {
    let mut fixture = Fixture::new(Argument::FpBits, 65);
    let root = mixed(&mut fixture, 0);
    let cnf = encode(&fixture.terms, root);
    let scan = scan_foreign(&fixture.terms, &[root]);
    let group = &scan.groups[0];
    let mut fp = FpSolver::new(&fixture.terms);
    let mut forcing = ForcedOutputs::new();
    assert!(forcing
        .residual_pairs(&fixture.terms, &mut fp, &cnf, group, &mut || Ok(()))
        .unwrap()
        .is_some());
    let cost = MAX_FORCING_WORK - forcing.work.0;
    assert!(cost > 2208 && cost <= MAX_FORCING_WORK);
    for budget in [cost - 1, cost] {
        let mut fp = FpSolver::new(&fixture.terms);
        let mut attempt = ForcedOutputs {
            work: Work(budget),
            closure: Closure::Uncomputed,
        };
        let result = attempt
            .residual_pairs(&fixture.terms, &mut fp, &cnf, group, &mut || Ok(()))
            .unwrap();
        assert_eq!(result.is_some(), budget == cost);
        if budget < cost {
            assert!(fp.term_to_fp().is_empty());
        }
    }
    assert!(forcing
        .residual_pairs(&fixture.terms, &mut fp, &cnf, group, &mut || Ok(()))
        .unwrap()
        .is_none());

    let stopped = Cell::new(false);
    let mut stop = |progress: FpBuildProgress| {
        if progress.clauses > 0 {
            stopped.set(true);
        }
        stopped.get()
    };
    let mut owner = FpConstruction::new(FpSolver::new(&fixture.terms), &mut stop).unwrap();
    assert!(matches!(
        plan_congruence_controlled(&fixture.terms, &mut owner, &cnf, &scan, &mut || Ok(())),
        Err(FpBuildError::Interrupted)
    ));
    assert!(stopped.get());
    stopped.set(false);
    assert!(matches!(owner.finish(), Err(FpBuildError::Interrupted)));
}

#[test]
fn failed_residual_admission_still_reaches_the_planners_final_stop_check() {
    let mut fixture = Fixture::new(Argument::Bv, 65);
    let root = fixture.conditional_root();
    let cnf = encode(&fixture.terms, root);
    let scan = scan_foreign(&fixture.terms, &[root]);
    let mut total = 0;
    let mut fp = FpSolver::new(&fixture.terms);
    let result =
        super::super::super::controlled::plan(&fixture.terms, &mut fp, &cnf, &scan, &mut || {
            total += 1;
            Ok(())
        })
        .unwrap();
    assert!(result.incomplete && result.clauses.is_empty());
    // FpSolver's infallible encoder cannot carry a stop error; the real
    // controlled owner can, and must not mask it with ordinary Incomplete.
    let mut allow = |_| false;
    let mut owner = FpConstruction::new(FpSolver::new(&fixture.terms), &mut allow).unwrap();
    let mut polls = 0;
    let result = plan_congruence_controlled(&fixture.terms, &mut owner, &cnf, &scan, &mut || {
        polls += 1;
        if polls == total {
            Err(FpBuildError::Interrupted)
        } else {
            Ok(())
        }
    });
    assert!(matches!(result, Err(FpBuildError::Interrupted)));
    assert_eq!(polls, total);
}
