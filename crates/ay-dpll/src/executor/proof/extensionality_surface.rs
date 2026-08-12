// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Honest artifact-only surface for strictly checked array extensionality.
//!
//! AY can strictly certify a diff witness whose reads were operationally folded
//! through stores/ITEs, or whose raw packed clause has a surface spelling that
//! is not byte-identical to Carcara's `arrays_ext` conclusion. The ordinary
//! Alethe surface correctly declines both. Consumer artifacts may still carry
//! an honest diagnostic skeleton: after the original proof passes the
//! datatype-aware strict checker, this module gives a presentation clone a
//! provenance-derived choice definition and replaces only the specifically
//! rejected lemma with `hole`.

use ay_core::{
    kani_compat::DetHashMap, AletheRule, Proof, ProofStep, SkolemChoice, Sort, Symbol, TermData,
    TermId, TermStore, TheoryLemmaKind,
};
use ay_proof::AlethePrintError;

use super::super::Executor;
use super::DEFAULT_ALETHE_EMISSION_WORK_BUDGET;

const DIAGNOSTIC_CLONE_ENVELOPE_BYTES: usize = 64 * 1024 * 1024;
const MAX_DIAGNOSTIC_PROOF_STEPS: usize = 131_072;
const MAX_DIAGNOSTIC_PROOF_CELLS: usize = 1_048_576;
const PROOF_STEP_WORK_BYTES: usize = 512;
const PROOF_CELL_WORK_BYTES: usize = 64;
const TERM_CLONE_PEAK_MULTIPLIER: usize = 8;
const CHOICE_CONSTRUCTION_HEADROOM_BYTES: usize = 1024 * 1024;

#[derive(Clone, Copy)]
struct ExtensionalitySurface {
    step: usize,
    witness: TermId,
    array_a: TermId,
    array_b: TermId,
}

impl Executor {
    #[cfg(test)]
    pub(crate) fn strict_check_counters_for_test(&self) -> (u64, u64) {
        (
            self.strict_check_invocations.get(),
            self.strict_check_steps_validated.get(),
        )
    }

    /// Render an artifact diagnostic for a strict proof whose ordinary surface
    /// declined a specifically identified extensionality presentation step.
    ///
    /// This is deliberately separate from `(get-proof)` and file-backed proof
    /// export. Those paths keep requiring a fully lowerable Alethe document.
    pub(crate) fn try_export_extensionality_artifact_surface(
        &self,
        rejected: ay_core::ProofId,
    ) -> Option<Result<String, AlethePrintError>> {
        if self.last_unsat_proof_reconstruction_suppressed
            || self.last_proof_has_finite_enum_sidecar()
        {
            return None;
        }
        let proof = self.last_proof.as_ref()?;
        diagnostic_clone_within_envelope(proof, &self.ctx.terms)?;
        // The public artifact boundary has already computed and accepted the
        // native strict verdict. Do not repeat that full walk or double-count
        // its published validation metrics here.
        let rejected =
            authenticate_rejected_extensionality(self, proof, &self.ctx.terms, rejected)?;
        let (diagnostic, terms) = make_diagnostic_clone(proof, &self.ctx.terms, &[rejected])?;
        let scope = self.proof_export_scope_assertions_for(proof)?;
        let overrides = self.proof_export_term_overrides();
        let emission_budget = self
            .proof_reconstruction_step_budget
            .map(|_| DEFAULT_ALETHE_EMISSION_WORK_BUDGET);
        Some(
            ay_proof::try_export_alethe_with_problem_scope_overrides_and_budget(
                &diagnostic,
                &terms,
                &scope,
                overrides.as_ref(),
                emission_budget,
            ),
        )
    }
}

fn authenticate_rejected_extensionality(
    executor: &Executor,
    proof: &Proof,
    terms: &TermStore,
    rejected: ay_core::ProofId,
) -> Option<ExtensionalitySurface> {
    let step = usize::try_from(rejected.0).ok()?;
    let ProofStep::TheoryLemma {
        clause,
        kind: TheoryLemmaKind::ArrayExtensionality,
        ..
    } = proof.steps.get(step)?
    else {
        return None;
    };
    let [clause_term] = clause.as_slice() else {
        return None;
    };
    let bindings = executor.recorded_array_extensionality_chain(*clause_term)?;
    let [(witness, array_a, array_b)] = bindings.as_slice() else {
        return None;
    };
    let raw_matches = ay_proof::recognize_array_extensionality(terms, clause).is_some_and(
        |(raw_a, raw_b, raw_witness)| {
            raw_witness == *witness && ordered(raw_a, raw_b) == ordered(*array_a, *array_b)
        },
    );
    let folded_matches = ay_proof::recognize_folded_array_extensionality(
        terms, clause, *array_a, *array_b, *witness,
    );
    if !raw_matches && !folded_matches {
        return None;
    }
    let introductions = proof
        .steps
        .iter()
        .filter(|candidate| exact_introduction(candidate, *witness, *array_a, *array_b))
        .count();
    if introductions != 1 {
        return None;
    }
    Some(ExtensionalitySurface {
        step,
        witness: *witness,
        array_a: *array_a,
        array_b: *array_b,
    })
}

fn exact_introduction(step: &ProofStep, witness: TermId, array_a: TermId, array_b: TermId) -> bool {
    matches!(
        step,
        ProofStep::Step {
            rule: AletheRule::ArrayExtDiffIntro,
            clause,
            premises,
            args,
        } if clause.is_empty()
            && premises.is_empty()
            && matches!(args.as_slice(), [w, a, b]
                if *w == witness && ordered(*a, *b) == ordered(array_a, array_b))
    )
}

fn make_diagnostic_clone(
    proof: &Proof,
    terms: &TermStore,
    extensionality: &[ExtensionalitySurface],
) -> Option<(Proof, TermStore)> {
    // Named assume labels are not consulted by the Alethe printer; rebuilding
    // from the ordered steps preserves every ProofId without cloning that map.
    let mut diagnostic = Proof::from_steps(proof.steps.clone());
    let mut diagnostic_terms = terms.clone();
    let mut registered: DetHashMap<TermId, (TermId, TermId)> = DetHashMap::default();
    for item in extensionality {
        let clause = match proof.steps.get(item.step)? {
            ProofStep::TheoryLemma { clause, .. } => clause.clone(),
            _ => return None,
        };
        diagnostic.steps[item.step] = ProofStep::Step {
            rule: AletheRule::Hole,
            clause,
            premises: Vec::new(),
            args: Vec::new(),
        };

        if let Some(&(seen_a, seen_b)) = registered.get(&item.witness) {
            if ordered(seen_a, seen_b) != ordered(item.array_a, item.array_b) {
                return None;
            }
            continue;
        }
        register_extensionality_choice(&mut diagnostic_terms, *item)?;
        registered.insert(item.witness, (item.array_a, item.array_b));
    }
    Some((diagnostic, diagnostic_terms))
}

#[derive(Clone, Copy, Default)]
struct ProofCloneAccounting {
    steps: usize,
    cells: usize,
    payload_bytes: usize,
}

fn diagnostic_clone_within_envelope(proof: &Proof, terms: &TermStore) -> Option<()> {
    let accounting = proof_clone_accounting(proof)?;
    let term_clone_bytes = terms.diagnostic_clone_memory_bytes(DIAGNOSTIC_CLONE_ENVELOPE_BYTES)?;
    clone_accounting_fits(term_clone_bytes, accounting).then_some(())
}

fn proof_clone_accounting(proof: &Proof) -> Option<ProofCloneAccounting> {
    let mut accounting = ProofCloneAccounting {
        steps: proof.steps.len(),
        cells: 0,
        payload_bytes: 0,
    };
    for step in &proof.steps {
        let (cells, payload) = match step {
            ProofStep::Assume(_) => (0, 0),
            ProofStep::Resolution { clause, .. } => (clause.len(), 0),
            ProofStep::TheoryLemma {
                theory,
                clause,
                farkas,
                lia,
                ..
            } => {
                let coefficients = farkas.as_ref().map_or(0, |f| f.coefficients.len());
                let cutting = match lia {
                    Some(ay_core::LiaAnnotation::CuttingPlane(cut)) => {
                        cut.farkas.coefficients.len()
                    }
                    _ => 0,
                };
                (
                    clause
                        .len()
                        .checked_add(coefficients)?
                        .checked_add(cutting)?,
                    theory.len(),
                )
            }
            ProofStep::Step {
                rule,
                clause,
                premises,
                args,
            } => (
                clause
                    .len()
                    .checked_add(premises.len())?
                    .checked_add(args.len())?,
                match rule {
                    AletheRule::Custom(name) => name.len(),
                    _ => 0,
                },
            ),
            // Folded datatype-array refutations are ground. Decline rather
            // than estimate/cloning arbitrarily nested anchor sort payloads.
            ProofStep::Anchor { .. } => return None,
            _ => return None,
        };
        accounting.cells = accounting.cells.checked_add(cells)?;
        accounting.payload_bytes = accounting.payload_bytes.checked_add(payload)?;
    }
    Some(accounting)
}

fn clone_accounting_fits(term_clone_bytes: usize, accounting: ProofCloneAccounting) -> bool {
    if term_clone_bytes > DIAGNOSTIC_CLONE_ENVELOPE_BYTES
        || accounting.steps > MAX_DIAGNOSTIC_PROOF_STEPS
        || accounting.cells > MAX_DIAGNOSTIC_PROOF_CELLS
    {
        return false;
    }
    // A one-entry append can resize a cloned Vec or hash table. Three copies
    // of the complete clone cover its old allocation plus a doubled new one;
    // four more cover every transient/stored copy of the already-accounted
    // array index/element sorts built by the seven-term choice definition.
    // Round that seven-copy upper bound to eight, then reserve fixed space for
    // the new entries, symbols, buckets, binder, and rollback identity.
    term_clone_bytes
        .checked_mul(TERM_CLONE_PEAK_MULTIPLIER)
        .and_then(|work| work.checked_add(CHOICE_CONSTRUCTION_HEADROOM_BYTES))
        .and_then(|work| {
            accounting
                .steps
                .checked_mul(PROOF_STEP_WORK_BYTES)
                .and_then(|proof_steps| work.checked_add(proof_steps))
        })
        .and_then(|work| {
            accounting
                .cells
                .checked_mul(PROOF_CELL_WORK_BYTES)
                .and_then(|cells| work.checked_add(cells))
        })
        .and_then(|work| work.checked_add(accounting.payload_bytes))
        .is_some_and(|work| work <= DIAGNOSTIC_CLONE_ENVELOPE_BYTES)
}

fn register_extensionality_choice(
    terms: &mut TermStore,
    binding: ExtensionalitySurface,
) -> Option<()> {
    if terms.skolem_choice(binding.witness).is_some() {
        return None;
    }
    let Sort::Array(array_sort) = terms.sort(binding.array_a).clone() else {
        return None;
    };
    if terms.sort(binding.array_b) != &Sort::Array(array_sort.clone())
        || terms.sort(binding.witness) != &array_sort.index_sort
    {
        return None;
    }
    let binder = terms.mk_fresh_var("array_ext_diagnostic_choice", array_sort.index_sort.clone());
    let TermData::Var(binder_name, _) = terms.get(binder) else {
        return None;
    };
    let binder_name = binder_name.clone();
    let selected_a = terms.mk_app(
        Symbol::named("select"),
        [binding.array_a, binder],
        array_sort.element_sort.clone(),
    );
    let selected_b = terms.mk_app(
        Symbol::named("select"),
        [binding.array_b, binder],
        array_sort.element_sort,
    );
    let arrays_equal = terms.mk_app(
        Symbol::named("="),
        [binding.array_a, binding.array_b],
        Sort::Bool,
    );
    let selected_equal = terms.mk_app(Symbol::named("="), [selected_a, selected_b], Sort::Bool);
    let selected_differ = terms.mk_not_raw(selected_equal);
    let body = terms.mk_app(
        Symbol::named("or"),
        [arrays_equal, selected_differ],
        Sort::Bool,
    );
    terms.register_skolem_choice(
        binding.witness,
        SkolemChoice {
            binder: binder_name,
            sort: array_sort.index_sort,
            body,
        },
    );
    Some(())
}

fn ordered(a: TermId, b: TermId) -> (TermId, TermId) {
    if a <= b {
        (a, b)
    } else {
        (b, a)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn diagnostic_clone_accounting_fails_closed_at_every_bound() {
        let one = ProofCloneAccounting {
            steps: 1,
            cells: 1,
            payload_bytes: 1,
        };
        assert!(clone_accounting_fits(1, one));
        assert!(!clone_accounting_fits(
            DIAGNOSTIC_CLONE_ENVELOPE_BYTES + 1,
            ProofCloneAccounting::default()
        ));
        let maximum_term_clone = (DIAGNOSTIC_CLONE_ENVELOPE_BYTES
            - CHOICE_CONSTRUCTION_HEADROOM_BYTES)
            / TERM_CLONE_PEAK_MULTIPLIER;
        assert!(clone_accounting_fits(
            maximum_term_clone,
            ProofCloneAccounting::default()
        ));
        assert!(!clone_accounting_fits(
            maximum_term_clone + 1,
            ProofCloneAccounting::default()
        ));
        assert!(!clone_accounting_fits(
            0,
            ProofCloneAccounting {
                steps: MAX_DIAGNOSTIC_PROOF_STEPS + 1,
                ..ProofCloneAccounting::default()
            }
        ));
        assert!(!clone_accounting_fits(
            0,
            ProofCloneAccounting {
                cells: MAX_DIAGNOSTIC_PROOF_CELLS + 1,
                ..ProofCloneAccounting::default()
            }
        ));
    }

    #[test]
    fn proof_clone_accounting_counts_all_step_vectors() {
        let mut proof = Proof::new();
        proof.add_step(ProofStep::Step {
            rule: AletheRule::Hole,
            clause: vec![TermId(0), TermId(1)],
            premises: vec![ay_core::ProofId(0)],
            args: vec![TermId(2), TermId(3), TermId(4)],
        });
        let accounting = proof_clone_accounting(&proof).expect("bounded accounting");
        assert_eq!(accounting.steps, 1);
        assert_eq!(accounting.cells, 6);
    }
}
