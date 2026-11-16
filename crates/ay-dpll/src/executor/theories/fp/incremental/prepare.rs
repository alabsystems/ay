// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Prepare only a disposable trial: caches never outlive missing SAT clauses.

use ay_core::kani_compat::DetHashSet as HashSet;
use ay_core::{CnfClause, TermId, TermStore, Tseitin};
use ay_fp::{FpBuiltEncoding, FpConstruction, FpSolver};

use crate::executor_types::UnknownOrigin;
use crate::incremental_state::IncrementalFpState;

use super::super::bitblast::bitblast_fp_predicate_controlled;
use super::super::stop::FpStop;
use super::super::support::FpPredicateResult;
use super::{checkpoint, IncrementalFpPhase};

pub(super) struct PreparedIncrementalFp {
    pub(super) definitions: Vec<CnfClause>,
    pub(super) fp_clauses: Vec<CnfClause>,
    pub(super) predicate_links: Vec<(i32, i32)>,
    pub(super) condition_links: Vec<(u32, u32)>,
    pub(super) bool_links: Vec<(i32, i32)>,
    pub(super) offset: i32,
}

pub(super) enum PreparationError {
    Stopped(UnknownOrigin),
    ConversionDecline,
    Unsupported,
    EncodingGap,
}

impl From<UnknownOrigin> for PreparationError {
    fn from(origin: UnknownOrigin) -> Self {
        Self::Stopped(origin)
    }
}

fn checked<T>(stop: &FpStop, result: Result<T, UnknownOrigin>) -> Result<T, PreparationError> {
    result.map_err(|origin| PreparationError::Stopped(stop.refuse(origin)))
}

pub(super) fn prepare(
    terms: &TermStore,
    assertions: &[TermId],
    trial: &mut IncrementalFpState,
    stop: &FpStop,
    observe: &impl Fn(IncrementalFpPhase),
) -> Result<PreparedIncrementalFp, PreparationError> {
    let (mut definitions, offset) = prepare_tseitin(terms, assertions, trial, stop, observe)?;
    let BuiltPredicates {
        encoding,
        predicate_links,
        newly_linked,
        unsupported,
    } = build_predicates(terms, trial, stop, observe)?;
    checkpoint(stop, observe, IncrementalFpPhase::Namespace)?;

    // Preserve the existing decline priority. In particular a conversion
    // defers to stateless even if a later predicate also proved unsupported.
    if !encoding.cache.to_bv_unspec_sites.is_empty() {
        return Err(PreparationError::ConversionDecline);
    }
    if unsupported {
        return Err(PreparationError::Unsupported);
    }
    if encoding.has_encoding_gap {
        return Err(PreparationError::EncodingGap);
    }

    let FpBuiltEncoding {
        clauses: fp_clauses,
        pending_condition_links: condition_links,
        cache,
        has_encoding_gap: _,
    } = encoding;
    trial.next_fp_var = trial.next_fp_var.max(cache.next_var);
    trial.fp_cache = cache;
    for variable in newly_linked {
        checkpoint(stop, observe, IncrementalFpPhase::Tseitin)?;
        trial.linked_predicate_vars.insert(variable);
    }
    let bool_links = repair_bool_inputs(terms, trial, &mut definitions, stop, observe)?;
    checkpoint(stop, observe, IncrementalFpPhase::Namespace)?;
    Ok(PreparedIncrementalFp {
        definitions,
        fp_clauses,
        predicate_links,
        condition_links,
        bool_links,
        offset,
    })
}

fn prepare_tseitin(
    terms: &TermStore,
    assertions: &[TermId],
    trial: &mut IncrementalFpState,
    stop: &FpStop,
    observe: &impl Fn(IncrementalFpPhase),
) -> Result<(Vec<CnfClause>, i32), PreparationError> {
    checkpoint(stop, observe, IncrementalFpPhase::Tseitin)?;
    // The tight pair's order is load-bearing for the frozen offset.
    checked(stop, trial.sync_tseitin_next_var())?;
    checked(stop, trial.sync_next_fp_var())?;
    let mut new_assertions = Vec::new();
    for &term in assertions {
        checkpoint(stop, observe, IncrementalFpPhase::Tseitin)?;
        if !trial.encoded_assertions.contains_key(&term) {
            new_assertions.push(term);
        }
    }
    let mut tseitin = Tseitin::from_state(terms, std::mem::take(&mut trial.tseitin_state));
    let mut definitions = Vec::new();
    for term in new_assertions {
        checkpoint(stop, observe, IncrementalFpPhase::Tseitin)?;
        let encoded = tseitin.encode_assertion(term);
        for clause in encoded.def_clauses {
            checkpoint(stop, observe, IncrementalFpPhase::Tseitin)?;
            definitions.push(clause);
        }
        trial.encoded_assertions.insert(term, encoded.root_lit);
        checkpoint(stop, observe, IncrementalFpPhase::Tseitin)?;
    }
    super::super::nested_bv_guards::seed(
        terms,
        assertions.iter().copied(),
        &mut tseitin,
        stop,
        &|| observe(IncrementalFpPhase::Tseitin),
    )?;
    for clause in tseitin.take_new_clauses() {
        checkpoint(stop, observe, IncrementalFpPhase::Tseitin)?;
        definitions.push(clause);
    }
    trial.tseitin_state = tseitin.into_state();
    let offset = match trial.fp_var_offset {
        Some(offset) => offset,
        None => {
            let offset = i32::try_from(trial.tseitin_state.next_var)
                .map_err(|_| stop.refuse(UnknownOrigin::DeterministicResourceBudget))?;
            trial.fp_var_offset = Some(offset);
            offset
        }
    };
    checked(stop, trial.sync_tseitin_next_var())?;
    checked(stop, trial.sync_next_fp_var())?;
    checkpoint(stop, observe, IncrementalFpPhase::Tseitin)?;
    Ok((definitions, offset))
}

struct BuiltPredicates {
    encoding: FpBuiltEncoding,
    predicate_links: Vec<(i32, i32)>,
    newly_linked: HashSet<u32>,
    unsupported: bool,
}

fn build_predicates(
    terms: &TermStore,
    trial: &mut IncrementalFpState,
    stop: &FpStop,
    observe: &impl Fn(IncrementalFpPhase),
) -> Result<BuiltPredicates, PreparationError> {
    checkpoint(stop, observe, IncrementalFpPhase::Tseitin)?;
    let mut solver = FpSolver::new_with_seeded_tseitin(terms, &trial.tseitin_state.term_to_var);
    checkpoint(stop, observe, IncrementalFpPhase::Tseitin)?;
    // The old constants and cached bits belong to the same trial's SAT owner.
    // Move the entire cache; neither a clone nor a partial getter is needed.
    solver.import_cache(std::mem::take(&mut trial.fp_cache));
    let build_error = |error| PreparationError::Stopped(stop.refuse_build_error(error));
    let mut should_stop = |progress| {
        observe(IncrementalFpPhase::construction(progress));
        stop.should_stop()
    };
    let mut fp = FpConstruction::new(solver, &mut should_stop).map_err(build_error)?;
    let mut predicate_links = Vec::new();
    let mut newly_linked = HashSet::default();
    let mut unsupported = false;
    for (&variable, &term) in &trial.tseitin_state.var_to_term {
        // Even skipped immutable/previously linked predicates must poll.
        checkpoint(stop, observe, IncrementalFpPhase::Tseitin)?;
        if trial.linked_predicate_vars.contains(&variable) || newly_linked.contains(&variable) {
            continue;
        }
        match bitblast_fp_predicate_controlled(terms, &mut fp, term).map_err(build_error)? {
            FpPredicateResult::Bitblasted(lit) => {
                let variable_lit = i32::try_from(variable)
                    .map_err(|_| stop.refuse(UnknownOrigin::DeterministicResourceBudget))?;
                predicate_links.push((variable_lit, lit));
                newly_linked.insert(variable);
            }
            FpPredicateResult::NotFpPredicate => {
                newly_linked.insert(variable);
            }
            FpPredicateResult::Unsupported => {
                unsupported = true;
                break;
            }
        }
    }
    let encoding = fp.finish().map_err(build_error)?;
    Ok(BuiltPredicates {
        encoding,
        predicate_links,
        newly_linked,
        unsupported,
    })
}

fn repair_bool_inputs(
    terms: &TermStore,
    trial: &mut IncrementalFpState,
    definitions: &mut Vec<CnfClause>,
    stop: &FpStop,
    observe: &impl Fn(IncrementalFpPhase),
) -> Result<Vec<(i32, i32)>, PreparationError> {
    checkpoint(stop, observe, IncrementalFpPhase::BoolRepair)?;
    let mut pending = Vec::new();
    for (&term, &literal) in &trial.fp_cache.bool_input_lits {
        checkpoint(stop, observe, IncrementalFpPhase::BoolRepair)?;
        if !trial.linked_bool_inputs.contains(&term) {
            pending.push((term, literal));
        }
    }
    pending.sort_unstable();
    checkpoint(stop, observe, IncrementalFpPhase::BoolRepair)?;
    let mut links = Vec::new();
    if !pending.is_empty() {
        // FP just grew; name Bool inputs above that range, never inside it.
        checked(stop, trial.sync_tseitin_next_var())?;
        let mut naming = Tseitin::from_state(terms, std::mem::take(&mut trial.tseitin_state));
        for &(term, literal) in &pending {
            checkpoint(stop, observe, IncrementalFpPhase::BoolRepair)?;
            links.push((naming.encode_root(term), literal));
        }
        for clause in naming.take_new_clauses() {
            checkpoint(stop, observe, IncrementalFpPhase::BoolRepair)?;
            definitions.push(clause);
        }
        trial.tseitin_state = naming.into_state();
        for (term, _) in pending {
            checkpoint(stop, observe, IncrementalFpPhase::BoolRepair)?;
            trial.linked_bool_inputs.insert(term);
        }
        checked(stop, trial.sync_next_fp_var())?;
    }
    checkpoint(stop, observe, IncrementalFpPhase::BoolRepair)?;
    Ok(links)
}
