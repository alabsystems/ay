// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use ay_arrays::{ArrayModel, ArraySolver};
use ay_core::{Sort, TermStore};
use ay_euf::{EufModel, EufSolver};
use ay_lia::LiaModel;
use ay_lra::LraModel;

use crate::executor_format::{format_bigint, format_rational};

/// Extract an EUF model and extend it with Int term values from equivalence classes.
pub(super) fn euf_with_int_values(euf: &mut EufSolver<'_>) -> EufModel {
    let mut euf_model = euf.extract_model();
    let base_count = euf_model.term_values.len();
    let (int_term_values, speculative) = euf.extract_int_term_values();
    euf_model.term_values.extend(int_term_values);
    euf_model.speculative_int_terms.extend(speculative);
    // Int value extraction should only add new entries, not replace (#4714)
    debug_assert!(
        euf_model.term_values.len() >= base_count,
        "euf_with_int_values: term_values shrank from {} to {}",
        base_count,
        euf_model.term_values.len()
    );
    // #uf-one-int-lane: `extract_model` fabricates per-class fresh integers
    // into `int_values` (the NUMERIC lane: UF-table argument keys, the
    // cross-theory congruence-restoration repair, class-merge passes) while
    // `extract_int_term_values` runs a SECOND, independent fabrication into
    // `term_values` (the FORMATTED lane: model printing, `evaluate_term`,
    // array extraction). The two sweeps use separate counters and iteration
    // orders, so a speculative class can carry two DIFFERENT values, one per
    // lane. The congruence repair then audits UF tables under the numeric
    // values while the printer resolves the same rows under the formatted
    // values — a table that is congruence-consistent internally prints with
    // contradictory duplicate keys (U4_rand_24: internal c1=11/f(11)=32 vs
    // printed c1=0 colliding with committed c3=0, first-match f(0)=0
    // falsifying the printed model). One interpretation must own both lanes:
    // mirror the numeric lane into the formatted lane for every Int term, the
    // same synchronization `merge_lia_values` performs for LIA-committed
    // values. Repair passes downstream always write both lanes together, so
    // the views stay aligned from here on.
    for (term_id, value) in &euf_model.int_values {
        euf_model.term_values.insert(*term_id, format_bigint(value));
    }
    euf_model
}

/// Merge LIA values into both EUF integer views for complete Int coverage.
///
/// LIA is authoritative for arithmetic terms. EUF's `extract_int_term_values()`
/// assigns speculative fresh integers to equivalence classes without concrete
/// constants, so disagreement with LIA is expected and LIA's values win. Both
/// maps form one committed interpretation: numeric UF-table lookup reads
/// `int_values`, while formatting and array extraction read `term_values`.
pub(super) fn merge_lia_values(euf_model: &mut EufModel, lia_model: Option<&LiaModel>) {
    if let Some(lia_model) = lia_model {
        let size_before = euf_model.term_values.len();
        let int_size_before = euf_model.int_values.len();
        for (&term_id, val) in &lia_model.values {
            // Numeric consumers (notably UF table argument lookup) consult
            // `int_values` before the formatted fallback.  Updating only
            // `term_values` leaves EUF's speculative class integer silently
            // shadowing the authoritative LIA repair.
            euf_model.int_values.insert(term_id, val.clone());
            euf_model.term_values.insert(term_id, format_bigint(val));
            // The LIA value is committed — no longer speculative
            // (#uflia-arith-arg-key).
            euf_model.speculative_int_terms.remove(&term_id);
        }
        // Model merge must not shrink the value map (insert only overwrites, never removes)
        debug_assert!(
            euf_model.term_values.len() >= size_before,
            "BUG: merge_lia_values shrank term_values from {} to {}",
            size_before,
            euf_model.term_values.len()
        );
        debug_assert!(
            euf_model.int_values.len() >= int_size_before,
            "BUG: merge_lia_values shrank int_values from {} to {}",
            int_size_before,
            euf_model.int_values.len()
        );
    }
}

/// Merge LRA values into an EUF model for Real-sorted terms.
///
/// LRA is authoritative for Real-sorted terms, same rationale as `merge_lia_values`.
/// Int-sorted terms are skipped: their values come from LIA, and LRA's unconstrained
/// defaults would overwrite correct LIA values with unparseable Real literals (#6291).
pub(super) fn merge_lra_values(euf_model: &mut EufModel, lra_model: &LraModel, terms: &TermStore) {
    let size_before = euf_model.term_values.len();
    for (&term_id, val) in &lra_model.values {
        // Int-sorted terms belong to LIA. Overwriting with LRA's default
        // produces a Real literal ("0.0") that fails Int parsing (#6291).
        if matches!(*terms.sort(term_id), Sort::Int) {
            continue;
        }
        euf_model.term_values.insert(term_id, format_rational(val));
    }
    // Model merge must not shrink the value map (insert only overwrites, never removes)
    debug_assert!(
        euf_model.term_values.len() >= size_before,
        "BUG: merge_lra_values shrank term_values from {} to {}",
        size_before,
        euf_model.term_values.len()
    );
}

/// Reconcile shared Int terms that appear in both LIA and LRA models.
///
/// In LIRA-family solvers the LRA side can see tighter `to_real(x)` constraints
/// than the LIA side. If LRA found an integral value for a shared Int term, keep
/// it and update LIA so model validation sees one coherent assignment. If LRA's
/// value is non-integral, keep the existing LIA-to-LRA patching behavior used by
/// `to_int` floor repairs.
pub(super) fn reconcile_lia_lra_values(
    lia_model: &mut Option<LiaModel>,
    lra_model: &mut LraModel,
    lia_authoritative: &ay_core::kani_compat::DetHashSet<ay_core::TermId>,
) -> Vec<ay_core::TermId> {
    let Some(lia) = lia_model.as_mut() else {
        return Vec::new();
    };

    let shared_terms = lia
        .values
        .iter()
        .filter_map(|(&term, val)| {
            lra_model
                .values
                .get(&term)
                .cloned()
                .map(|lra_val| (term, val.clone(), lra_val))
        })
        .collect::<Vec<_>>();

    let mut patched_lra_terms = Vec::new();
    for (term, lia_val, lra_val) in shared_terms {
        let lia_rational = num_rational::BigRational::from(lia_val);
        if lra_val == lia_rational {
            continue;
        }
        // #reconcile-lia-authority (2026-07-11): an Int-only equality —
        // `(= (g phase) phase)` forwarded via `assert_shared_equality` — is
        // routed to LIA ALONE. The sibling LRA solver may still carry the
        // same Int term as an UNCONSTRAINED cross-sort phantom (registered
        // through `to_real`), whose relaxation value defaults to 0. Letting
        // that integer-looking default overwrite LIA's constrained value
        // manufactured an invalid model (g(phase)=0 with phase=1) that the
        // independent gate then correctly refuted — degrading a genuine sat
        // to unknown (auflira_cross_sort). For any term LIA constrains via a
        // shared equality, LIA is authoritative: patch LRA instead.
        if lra_val.is_integer() && !lia_authoritative.contains(&term) {
            lia.values.insert(term, lra_val.to_integer());
        } else {
            lra_model.values.insert(term, lia_rational);
            patched_lra_terms.push(term);
        }
    }
    patched_lra_terms
}

/// Build an array model from a merged EUF model term-value map.
///
/// Delegates to `ArraySolver::extract_model` which walks store chains
/// and const-array terms using the merged term-value map from EUF+LIA/LRA.
pub(super) fn extract_array_model(
    arrays: &mut ArraySolver<'_>,
    euf_model: &EufModel,
) -> ArrayModel {
    arrays.extract_model(&euf_model.term_values)
}

#[cfg(test)]
mod tests {
    use super::*;
    use ay_core::TermId;
    use num_bigint::BigInt;

    #[test]
    fn merge_lia_values_overwrites_both_euf_integer_views() {
        let term = TermId(0);
        let mut euf = EufModel::default();
        euf.int_values.insert(term, BigInt::from(0));
        euf.term_values.insert(term, "0".to_string());
        let mut lia = LiaModel {
            values: Default::default(),
        };
        lia.values.insert(term, BigInt::from(7));

        merge_lia_values(&mut euf, Some(&lia));

        assert_eq!(euf.int_values.get(&term), Some(&BigInt::from(7)));
        assert_eq!(euf.term_values.get(&term).map(String::as_str), Some("7"));
    }
}
