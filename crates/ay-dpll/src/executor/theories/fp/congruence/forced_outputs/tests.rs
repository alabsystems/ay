// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use std::cell::Cell;
use std::collections::BTreeMap;

use ay_core::{CnfClause, Symbol, TermId, Tseitin};
use ay_fp::{FpBuildError, FpBuildProgress, FpConstruction, FpSolver};

use super::*;
use crate::executor::theories::fp::congruence::{
    plan_congruence, plan_congruence_controlled, scan_foreign,
};

#[path = "tests/residual.rs"]
mod residual;
#[path = "tests/stateless.rs"]
mod stateless;

// Retain the original uniform-only assertions as compatibility controls.
impl ForcedOutputs {
    fn elides<E: Encoder>(
        &mut self,
        terms: &TermStore,
        fp: &mut E,
        tseitin: &TseitinResult,
        group: &[Application],
        check: &mut dyn FnMut() -> Result<(), E::Error>,
    ) -> Result<bool, E::Error> {
        Ok(self
            .residual_pairs(terms, fp, tseitin, group, check)?
            .is_some_and(|pairs| pairs.is_empty()))
    }
}

#[derive(Clone, Copy)]
enum Argument {
    Bv,
    FpBits,
}

struct Fixture {
    terms: TermStore,
    apps: Vec<TermId>,
    args: Vec<TermId>,
    words: Vec<TermId>,
}

impl Fixture {
    fn new(kind: Argument, count: usize) -> Self {
        let mut terms = TermStore::new();
        let mut apps = Vec::new();
        let mut args = Vec::new();
        let mut words = Vec::new();
        for i in 0..count {
            let word = terms.mk_var(&format!("word{i}"), Sort::bitvec(64));
            let arg = match kind {
                Argument::Bv => word,
                Argument::FpBits => {
                    let sign = terms.mk_bvextract(63, 63, word);
                    let exponent = terms.mk_bvextract(62, 52, word);
                    let fraction = terms.mk_bvextract(51, 0, word);
                    terms.mk_app(
                        Symbol::named("fp"),
                        [sign, exponent, fraction],
                        Sort::FloatingPoint(11, 53),
                    )
                }
            };
            words.push(word);
            args.push(arg);
            apps.push(terms.mk_app(Symbol::named("g"), [arg], Sort::Bool));
        }
        Self {
            terms,
            apps,
            args,
            words,
        }
    }

    fn root(&mut self, polarity: bool) -> TermId {
        let children: Vec<_> = self
            .apps
            .iter()
            .map(|&app| {
                if polarity {
                    app
                } else {
                    self.terms.mk_not(app)
                }
            })
            .collect();
        self.terms
            .mk_app(Symbol::named("and"), children, Sort::Bool)
    }

    fn conditional_root(&mut self) -> TermId {
        let condition = self.terms.mk_var("condition", Sort::Bool);
        let children: Vec<_> = self
            .apps
            .iter()
            .map(|&app| {
                self.terms
                    .mk_app(Symbol::named("or"), [condition, app], Sort::Bool)
            })
            .collect();
        self.terms
            .mk_app(Symbol::named("and"), children, Sort::Bool)
    }
}

fn encode(terms: &TermStore, root: TermId) -> TseitinResult {
    // The real stateless prepare path appends the activation AFTER definition
    // clauses and deliberately supplies root=0. Preserve that exact shape.
    let mut encoder = Tseitin::new(terms);
    let encoded = encoder.encode_assertion(root);
    let mut clauses = encoded.def_clauses;
    clauses.push(CnfClause::unit(encoded.root_lit));
    TseitinResult::new(
        clauses,
        encoder.term_to_var().clone(),
        encoder.var_to_term().clone(),
        0,
        encoder.num_vars(),
    )
}

fn raw_cnf(vars: u32, clauses: &[&[i32]]) -> TseitinResult {
    TseitinResult::new(
        clauses
            .iter()
            .map(|lits| CnfClause::new(lits.to_vec()))
            .collect(),
        BTreeMap::new(),
        BTreeMap::new(),
        0,
        vars,
    )
}

#[test]
fn asserted_and_256_uniform_outputs_materialize_every_fp_and_bv_argument() {
    for kind in [Argument::Bv, Argument::FpBits] {
        for polarity in [true, false] {
            let mut fixture = Fixture::new(kind, 256);
            let root = fixture.root(polarity);
            let tseitin = encode(&fixture.terms, root);
            let scan = scan_foreign(&fixture.terms, &[root]);
            assert!(!scan.unencodable);
            assert_eq!(scan.groups.len(), 1);
            assert_eq!(scan.groups[0].len(), 256);
            let mut allow = |_| false;
            let mut owner = FpConstruction::new(FpSolver::new(&fixture.terms), &mut allow).unwrap();
            let mut forcing = ForcedOutputs::new();
            assert!(
                forcing
                    .elides(
                        &fixture.terms,
                        &mut owner,
                        &tseitin,
                        &scan.groups[0],
                        &mut || Ok(())
                    )
                    .unwrap(),
                "256-app fixture must fit the unchanged {MAX_FORCING_WORK} allowance"
            );
            assert!(forcing.work.0 > 0);
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
            // The actual planner must take this branch as well, with no
            // residual congruence clauses and unchanged controlled parity.
            let mut legacy = FpSolver::new(&fixture.terms);
            let plan = plan_congruence(&fixture.terms, &mut legacy, &tseitin, &scan);
            assert!(!plan.incomplete && plan.clauses.is_empty());
        }
    }
}

#[test]
fn units_handle_duplicates_tautologies_and_atomic_conflict_refusal() {
    let cnf = raw_cnf(4, &[&[1, 1], &[-1, 2, 2], &[3, -3], &[-2, 4]]);
    let values = unit_closure(&cnf, &mut Work(MAX_FORCING_WORK), &mut || Ok::<_, ()>(()))
        .unwrap()
        .unwrap();
    assert_eq!(values, [0, 1, 1, 0, 1]);
    for clauses in [
        vec![vec![1], vec![-1]],
        vec![vec![1], vec![-1, 2], vec![-2]],
    ] {
        let refs: Vec<_> = clauses.iter().map(Vec::as_slice).collect();
        assert!(unit_closure(
            &raw_cnf(2, &refs),
            &mut Work(MAX_FORCING_WORK),
            &mut || Ok::<_, ()>(())
        )
        .unwrap()
        .is_none());
    }
}

#[test]
fn every_small_cnf_forced_literal_is_a_truth_table_consequence() {
    // Exhaust all triples from the four units and sixteen ordered binary
    // clauses over two variables, including duplicates and tautologies.
    // This oracle evaluates CNF directly; it does not reuse unit propagation.
    let literals = [-2i32, -1, 1, 2];
    let mut clauses: Vec<Vec<i32>> = literals.iter().map(|&lit| vec![lit]).collect();
    for a in literals {
        for b in literals {
            clauses.push(vec![a, b]);
        }
    }
    let mut checked = 0;
    for a in &clauses {
        for b in &clauses {
            for c in &clauses {
                let input = [a.as_slice(), b.as_slice(), c.as_slice()];
                let cnf = raw_cnf(2, &input);
                let Some(forced) =
                    unit_closure(&cnf, &mut Work(MAX_FORCING_WORK), &mut || Ok::<_, ()>(()))
                        .unwrap()
                else {
                    continue;
                };
                for mask in 0u8..4 {
                    let holds = |lit: i32| {
                        let value = mask & (1 << (lit.unsigned_abs() - 1)) != 0;
                        value == (lit > 0)
                    };
                    if !input
                        .iter()
                        .all(|clause| clause.iter().any(|&lit| holds(lit)))
                    {
                        continue;
                    }
                    for (variable, &value) in forced.iter().enumerate().skip(1) {
                        if value != 0 {
                            assert_eq!(
                                mask & (1 << (variable - 1)) != 0,
                                value > 0,
                                "unsound forced literal: {input:?}, {forced:?}, mask={mask}"
                            );
                            checked += 1;
                        }
                    }
                }
            }
        }
    }
    assert!(checked > 0);
}

#[test]
fn malformed_namespaces_and_partial_closures_never_authorize_elision() {
    for cnf in [
        raw_cnf(1, &[&[0]]),
        raw_cnf(1, &[&[i32::MIN]]),
        raw_cnf(1, &[&[2]]),
        raw_cnf(1, &[&[]]),
        raw_cnf(u32::MAX, &[&[1]]),
        raw_cnf(MAX_FORCING_WORK as u32, &[&[1]]),
    ] {
        assert!(
            unit_closure(&cnf, &mut Work(MAX_FORCING_WORK), &mut || Ok::<_, ()>(()))
                .unwrap()
                .is_none()
        );
    }
    let cnf = raw_cnf(3, &[&[1], &[-1, 2], &[-2, 3]]);
    let mut complete_work = Work(MAX_FORCING_WORK);
    assert!(
        unit_closure(&cnf, &mut complete_work, &mut || Ok::<_, ()>(()))
            .unwrap()
            .is_some()
    );
    let cost = MAX_FORCING_WORK - complete_work.0;
    for budget in 0..cost {
        assert!(
            unit_closure(&cnf, &mut Work(budget), &mut || Ok::<_, ()>(()))
                .unwrap()
                .is_none()
        );
    }
}

#[test]
fn conditional_and_missing_output_mappings_keep_the_group_incomplete() {
    let mut fixture = Fixture::new(Argument::FpBits, 65);
    let conditional = fixture.conditional_root();
    let conditional_cnf = encode(&fixture.terms, conditional);
    let values = unit_closure(&conditional_cnf, &mut Work(MAX_FORCING_WORK), &mut || {
        Ok::<_, ()>(())
    })
    .unwrap()
    .unwrap();
    for &app in &fixture.apps {
        assert_eq!(
            values[conditional_cnf.var_for_term(app).unwrap() as usize],
            0
        );
    }
    let all_true = fixture.root(true);
    for root in [conditional, all_true] {
        let mut cnf = encode(&fixture.terms, root);
        if root == all_true {
            let variable = cnf.term_to_var.remove(&fixture.apps[0]).unwrap();
            cnf.term_to_var.insert(fixture.apps[0], variable + 1);
        }
        let scan = scan_foreign(&fixture.terms, &[root]);
        let mut fp = FpSolver::new(&fixture.terms);
        let plan = plan_congruence(&fixture.terms, &mut fp, &cnf, &scan);
        assert!(plan.incomplete && plan.clauses.is_empty());
        assert!(fp.term_to_fp().is_empty());
    }
}

#[test]
fn unsupported_bv_composites_cannot_be_materialized_as_free_bits() {
    let mut fixture = Fixture::new(Argument::Bv, 65);
    for (app, &word) in fixture.apps.iter_mut().zip(&fixture.words) {
        let unsupported =
            fixture
                .terms
                .mk_app(Symbol::named("opaque_bv"), [word], Sort::bitvec(64));
        *app = fixture
            .terms
            .mk_app(Symbol::named("g"), [unsupported], Sort::Bool);
    }
    let root = fixture.root(true);
    let cnf = encode(&fixture.terms, root);
    let scan = scan_foreign(&fixture.terms, &[root]);
    assert_eq!(scan.groups.len(), 2);
    assert!(!scan.unencodable);
    let mut allow = |_| false;
    let mut owner = FpConstruction::new(FpSolver::new(&fixture.terms), &mut allow).unwrap();
    let plan = plan_congruence_controlled(&fixture.terms, &mut owner, &cnf, &scan, &mut || Ok(()))
        .unwrap();
    assert!(plan.incomplete && plan.clauses.is_empty());
    let built = owner.finish().unwrap();
    for &(term, _) in &scan.groups[1] {
        assert!(!built.cache.bv_term_bits.contains_key(&term));
    }
}

#[test]
fn forcing_is_query_local_and_budget_is_shared_across_groups() {
    let mut fixture = Fixture::new(Argument::Bv, 65);
    let asserted = fixture.root(true);
    let conditional = fixture.conditional_root();
    for (root, incomplete) in [(asserted, false), (conditional, true), (asserted, false)] {
        let scan = scan_foreign(&fixture.terms, &[root]);
        let cnf = encode(&fixture.terms, root);
        let mut fp = FpSolver::new(&fixture.terms);
        assert_eq!(
            plan_congruence(&fixture.terms, &mut fp, &cnf, &scan).incomplete,
            incomplete
        );
    }
    let scan = scan_foreign(&fixture.terms, &[asserted]);
    let cnf = encode(&fixture.terms, asserted);
    let mut forcing = ForcedOutputs::new();
    let mut fp = FpSolver::new(&fixture.terms);
    assert!(forcing
        .elides(&fixture.terms, &mut fp, &cnf, &scan.groups[0], &mut || Ok(
            ()
        ))
        .unwrap());
    let after_first = forcing.work.0;
    let mut declined = false;
    for _ in 0..MAX_GROUP_APPLICATIONS {
        if !forcing
            .elides(&fixture.terms, &mut fp, &cnf, &scan.groups[0], &mut || {
                Ok(())
            })
            .unwrap()
        {
            declined = true;
            break;
        }
    }
    assert!(declined && forcing.work.0 == 0 && after_first < MAX_FORCING_WORK);
    assert!(!forcing
        .elides(&fixture.terms, &mut fp, &cnf, &scan.groups[0], &mut || Ok(
            ()
        ))
        .unwrap());
}

#[test]
fn cancellation_in_closure_and_real_materialization_returns_no_partial_plan() {
    let cnf = raw_cnf(3, &[&[1], &[-1, 2], &[-2, 3]]);
    for cutoff in [1, 5, 12] {
        let calls = Cell::new(0);
        let result = unit_closure(&cnf, &mut Work(MAX_FORCING_WORK), &mut || {
            calls.set(calls.get() + 1);
            if calls.get() == cutoff {
                Err(FpBuildError::Interrupted)
            } else {
                Ok(())
            }
        });
        assert!(matches!(result, Err(FpBuildError::Interrupted)));
        assert_eq!(calls.get(), cutoff);
    }
    let mut fixture = Fixture::new(Argument::FpBits, 65);
    let root = fixture.root(true);
    let scan = scan_foreign(&fixture.terms, &[root]);
    let cnf = encode(&fixture.terms, root);
    let interrupted = Cell::new(false);
    let clauses = Cell::new(0);
    let mut stop = |progress: FpBuildProgress| {
        clauses.set(progress.clauses);
        if progress.clauses > 0 {
            interrupted.set(true);
        }
        interrupted.get()
    };
    let mut owner = FpConstruction::new(FpSolver::new(&fixture.terms), &mut stop).unwrap();
    assert!(matches!(
        plan_congruence_controlled(&fixture.terms, &mut owner, &cnf, &scan, &mut || Ok(())),
        Err(FpBuildError::Interrupted)
    ));
    assert!(clauses.get() > 0);
    interrupted.set(false);
    assert!(matches!(owner.finish(), Err(FpBuildError::Interrupted)));
}
