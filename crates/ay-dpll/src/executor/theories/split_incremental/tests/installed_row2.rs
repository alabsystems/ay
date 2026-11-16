// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Caller-protocol controls: real scoped SAT installation, then array callbacks.
//!
//! Register as a child of executor::theories::split_incremental::tests. These
//! controls deliberately leave array theory assignments sparse. They establish
//! exact installed-clause ownership and same-instance progress, not a public SMT
//! query verdict or automatic coverage of every split-loop macro call site.

use super::super::recheck_installed_theory_lemmas;
use super::*;
use ay_arrays::ArraySolver;
use ay_core::{TermId, TheoryResult, TheorySolver};

const APPLIED_MEMO_BOUND: usize = 8_192;
const LAZY_BATCH: usize = 64;

struct RowFixture {
    terms: TermStore,
    clauses: Vec<Vec<TheoryLit>>,
}

fn rows(count: usize) -> RowFixture {
    let mut terms = TermStore::new();
    let sort = Sort::array(Sort::Int, Sort::Int);
    let base = terms.mk_var("installed_base", sort.clone());
    let index = terms.mk_var("installed_write_index", Sort::Int);
    let value = terms.mk_var("installed_value", Sort::Int);
    let stored = terms.mk_store(base, index, value);
    let alias = terms.mk_var("installed_alias", sort);
    let alias_eq = terms.mk_eq(alias, stored);
    let mut clauses = Vec::with_capacity(count);
    for n in 0..count {
        let read_index = terms.mk_var(format!("installed_read_index_{n}"), Sort::Int);
        let read = terms.mk_select(alias, read_index);
        let base_read = terms.mk_select(base, read_index);
        let index_eq = terms.mk_eq(index, read_index);
        let value_eq = terms.mk_eq(read, base_read);
        clauses.push(canonical(&[
            TheoryLit::new(alias_eq, false),
            TheoryLit::new(index_eq, true),
            TheoryLit::new(value_eq, true),
        ]));
    }
    RowFixture { terms, clauses }
}

fn canonical(clause: &[TheoryLit]) -> Vec<TheoryLit> {
    let mut key = clause.to_vec();
    key.sort_by_key(|lit| (lit.term.0, lit.value));
    key.dedup();
    key
}

/// This local ledger is populated only AFTER the actual scoped SAT add returns.
/// Its lifetime is one unpopped SAT scope. Issued IDs corroborate the add; they
/// are not themselves proof that a popped clause remains installed.
struct Installed<'a> {
    terms: &'a TermStore,
    sat: SatSolver,
    term_to_var: super::super::HashMap<TermId, u32>,
    var_to_term: super::super::HashMap<u32, TermId>,
    next_var: u32,
    negations: IncrementalNegationCache,
    ledger: super::super::HashMap<Vec<TheoryLit>, u64>,
}

impl<'a> Installed<'a> {
    fn new(terms: &'a TermStore, negations: IncrementalNegationCache) -> Self {
        Self {
            terms,
            sat: SatSolver::new(0),
            term_to_var: super::super::HashMap::default(),
            var_to_term: super::super::HashMap::default(),
            next_var: 0,
            negations,
            ledger: super::super::HashMap::default(),
        }
    }

    fn install(&mut self, clause: &[TheoryLit]) {
        let key = canonical(clause);
        assert!(
            !self.ledger.contains_key(&key),
            "test installs each clause once per scope"
        );
        let original = apply_theory_lemma_incremental(
            self.terms,
            &mut self.sat,
            &mut self.term_to_var,
            &mut self.var_to_term,
            &mut self.next_var,
            &mut self.negations,
            clause,
        )
        .expect("a nontrivial ROW2 clause gets an actual original-clause ID");
        assert!(self.sat.is_issued_original_clause_id(original));
        assert!(self.ledger.insert(key, original).is_none());
    }

    fn owns(&self, clause: &[TheoryLit]) -> bool {
        self.ledger
            .get(&canonical(clause))
            .is_some_and(|id| self.sat.is_issued_original_clause_id(*id))
    }

    fn pop_scope(&mut self) {
        assert!(self.sat.pop());
        self.ledger.clear();
    }

    fn encode_clause_atoms(&mut self, clause: &[TheoryLit]) {
        for lit in clause {
            let _ = ensure_incremental_atom_encoded(
                self.terms,
                &mut self.sat,
                &mut self.term_to_var,
                &mut self.var_to_term,
                &mut self.next_var,
                &mut self.negations,
                lit.term,
            );
        }
    }

    fn forbid_clause(&mut self, clause: &[TheoryLit]) {
        for lit in clause {
            let var = *self
                .term_to_var
                .get(&lit.term)
                .expect("atom was actually encoded");
            let var = SatVariable::new(var);
            self.sat.add_clause(vec![if lit.value {
                SatLiteral::negative(var)
            } else {
                SatLiteral::positive(var)
            }]);
        }
    }
}

fn need_rows(result: TheoryResult) -> Vec<TheoryLemma> {
    match result {
        TheoryResult::NeedLemmas(lemmas) => {
            assert!(!lemmas.is_empty(), "empty NeedLemmas is not progress");
            lemmas
        }
        other => panic!("expected a guarded ROW2 request, got {other:?}"),
    }
}

#[test]
fn installed_row2_replay_before_discovery_rechecks_same_live_theory_past_8192() {
    let mut fixture = rows(APPLIED_MEMO_BOUND + 1);
    let negations = IncrementalNegationCache::seed(&mut fixture.terms, [], false);
    let mut installed = Installed::new(&fixture.terms, negations);
    installed.sat.push();
    for clause in &fixture.clauses {
        installed.install(clause);
    }
    assert_eq!(installed.ledger.len(), APPLIED_MEMO_BOUND + 1);
    let original_max = installed.sat.issued_original_clause_id_max();
    let clause_count = installed.sat.num_clauses();

    // Actual lazy/assuming callers replay installed clauses BEFORE the fresh
    // theory's first discovery. Sparse delivery means no clause literal is
    // asserted true in this array component; installed ownership is separate.
    let mut theory = ArraySolver::new(&fixture.terms);
    theory.set_defer_expensive_checks(true);
    for clause in &fixture.clauses {
        theory.note_applied_theory_lemma(clause);
    }
    let installed_lemmas: Vec<_> = fixture
        .clauses
        .iter()
        .map(|clause| {
            assert!(installed.owns(clause));
            TheoryLemma::new(clause.clone())
        })
        .collect();
    let initial = theory.check();
    assert!(
        matches!(&initial, TheoryResult::NeedLemmas(lemmas) if !lemmas.is_empty()),
        "the control must exercise a real replay-before-discovery duplicate request"
    );
    let result =
        recheck_installed_theory_lemmas(&mut theory, initial, &installed_lemmas, &|| false);
    assert!(
        matches!(result, TheoryResult::Sat),
        "actual installed duplicates must settle through the same live theory"
    );
    let round_limit = fixture.clauses.len().div_ceil(LAZY_BATCH) + 2;
    let checks = theory
        .collect_statistics()
        .into_iter()
        .find_map(|(name, value)| (name == "arrays_checks").then_some(value))
        .expect("actual array check counter is exposed");
    assert!(
        checks <= round_limit as u64,
        "the real helper must progress within the unchanged lazy64 discovery bound"
    );
    assert_eq!(installed.sat.issued_original_clause_id_max(), original_max);
    assert_eq!(
        installed.sat.num_clauses(),
        clause_count,
        "same-live re-ack adds no SAT clauses"
    );
    // TheoryResult::Sat here is a component result, not an SMT acceptance claim.
}

#[test]
fn planned_seen_row2_without_sat_installation_does_not_acknowledge_live_work() {
    let mut fixture = rows(1);
    let negations = IncrementalNegationCache::seed(&mut fixture.terms, [], false);
    let mut installed = Installed::new(&fixture.terms, negations);
    installed.sat.push();
    let mut theory = ArraySolver::new(&fixture.terms);
    theory.set_defer_expensive_checks(true);
    let first = need_rows(theory.check());
    assert_eq!(first.len(), 1);
    assert_eq!(canonical(&first[0].clause), fixture.clauses[0]);
    let mut seen = TheoryLemmaSeenSet::default();
    let (planned, skipped) = take_new_theory_lemmas(first, &mut seen);
    assert_eq!((planned.len(), skipped), (1, 0));
    assert_eq!(installed.sat.issued_original_clause_id_max(), 0);
    assert!(installed.ledger.is_empty());

    let repeated_result = theory.check();
    let without_install =
        recheck_installed_theory_lemmas(&mut theory, repeated_result, &[], &|| false);
    let repeated = need_rows(without_install);
    let (new, skipped) = take_new_theory_lemmas(repeated, &mut seen);
    assert_eq!(new, [] as [TheoryLemma; 0]);
    assert_eq!(
        skipped, 1,
        "a planned duplicate is still not an installed clause"
    );
    assert!(!installed.owns(&planned[0].clause));
    let still_requested = need_rows(theory.check());
    assert_eq!(canonical(&still_requested[0].clause), fixture.clauses[0]);

    installed.install(&planned[0].clause);
    assert!(installed.owns(&planned[0].clause));
    let result = recheck_installed_theory_lemmas(
        &mut theory,
        TheoryResult::NeedLemmas(still_requested),
        &planned,
        &|| false,
    );
    assert!(
        matches!(result, TheoryResult::Sat),
        "only actual installation licenses the callback"
    );
}

#[test]
fn popped_sat_scope_does_not_replay_an_old_row2_installation_into_a_new_scope() {
    let mut fixture = rows(1);
    let negations = IncrementalNegationCache::seed(&mut fixture.terms, [], false);
    let mut installed = Installed::new(&fixture.terms, negations);
    installed.sat.push();
    installed.install(&fixture.clauses[0]);
    installed.pop_scope();
    // An issued ID is not an active-scope ownership oracle. The SAT witness
    // below independently checks absence after the owner ledger is retired.
    assert!(!installed.owns(&fixture.clauses[0]));
    installed.sat.push();
    installed.forbid_clause(&fixture.clauses[0]);
    assert!(
        matches!(installed.sat.solve().into_inner(), SatResult::Sat(_)),
        "the old scoped clause must really be absent, not merely absent from a test set"
    );

    let mut current_theory = ArraySolver::new(&fixture.terms);
    current_theory.set_defer_expensive_checks(true);
    let requested = need_rows(current_theory.check());
    assert_eq!(requested.len(), 1);
    assert_eq!(canonical(&requested[0].clause), fixture.clauses[0]);
    assert!(!installed.owns(&requested[0].clause));
    installed.install(&requested[0].clause);
    current_theory.note_applied_theory_lemma(&requested[0].clause);
    assert!(
        installed.sat.solve().into_inner().is_unsat(),
        "only the real new-scope installation excludes this Boolean assignment"
    );
}

#[test]
fn partial_installed_ledger_returns_uninstalled_rows_instead_of_accepting_some_duplicates() {
    let mut fixture = rows(2);
    let negations = IncrementalNegationCache::seed(&mut fixture.terms, [], false);
    let mut installed = Installed::new(&fixture.terms, negations);
    installed.sat.push();
    let mut theory = ArraySolver::new(&fixture.terms);
    theory.set_defer_expensive_checks(true);
    let requested = need_rows(theory.check());
    assert_eq!(requested.len(), 2);
    assert_ne!(
        canonical(&requested[0].clause),
        canonical(&requested[1].clause)
    );

    installed.install(&requested[0].clause);
    installed.encode_clause_atoms(&requested[1].clause);
    installed.forbid_clause(&requested[1].clause);
    assert!(
        matches!(installed.sat.solve().into_inner(), SatResult::Sat(_)),
        "the actual first installed clause does not imply installation of the missing one"
    );
    let missing = canonical(&requested[1].clause);
    assert!(installed.owns(&requested[0].clause));
    assert!(!installed.owns(&requested[1].clause));
    let original_max = installed.sat.issued_original_clause_id_max();
    let clause_count = installed.sat.num_clauses();

    let remaining = need_rows(recheck_installed_theory_lemmas(
        &mut theory,
        TheoryResult::NeedLemmas(requested.clone()),
        &requested[..1],
        &|| false,
    ));
    assert_eq!(
        remaining.len(),
        1,
        "some acknowledged work cannot hide the still-uninstalled request"
    );
    assert_eq!(canonical(&remaining[0].clause), missing);
    assert!(!installed.owns(&remaining[0].clause));
    assert_eq!(installed.sat.issued_original_clause_id_max(), original_max);
    assert_eq!(installed.sat.num_clauses(), clause_count);

    installed.install(&remaining[0].clause);
    assert!(
        installed.sat.solve().into_inner().is_unsat(),
        "only real installation of the remaining clause excludes its complementary witness"
    );
}

#[test]
fn original_stop_after_initial_request_prevents_reack_rechecks_and_sat_mutation() {
    let mut fixture = rows(1);
    let negations = IncrementalNegationCache::seed(&mut fixture.terms, [], false);
    let mut installed = Installed::new(&fixture.terms, negations);
    installed.sat.push();
    let stopped = std::cell::Cell::new(false);
    let should_stop = || stopped.get();
    let mut theory = ArraySolver::new(&fixture.terms);
    theory.set_defer_expensive_checks(true);
    let requested = need_rows(theory.check());
    assert_eq!(requested.len(), 1);
    installed.install(&requested[0].clause);
    let checks_before = theory
        .collect_statistics()
        .into_iter()
        .find_map(|(name, value)| (name == "arrays_checks").then_some(value))
        .unwrap();
    let original_max = installed.sat.issued_original_clause_id_max();
    let clause_count = installed.sat.num_clauses();

    // This is the SAME caller-owned stop closure, created before the initial
    // check. Do not reset it or replace it with a fresh grant during replay.
    stopped.set(true);
    let result = recheck_installed_theory_lemmas(
        &mut theory,
        TheoryResult::NeedLemmas(requested.clone()),
        &requested,
        &should_stop,
    );
    assert!(matches!(result, TheoryResult::Unknown));
    assert!(stopped.get());
    let checks_after = theory
        .collect_statistics()
        .into_iter()
        .find_map(|(name, value)| (name == "arrays_checks").then_some(value))
        .unwrap();
    assert_eq!(
        checks_after, checks_before,
        "a held original stop permits no further live-theory checks"
    );
    assert_eq!(installed.sat.issued_original_clause_id_max(), original_max);
    assert_eq!(installed.sat.num_clauses(), clause_count);
}

#[path = "installed_row2_phase.rs"]
mod installed_row2_phase;
