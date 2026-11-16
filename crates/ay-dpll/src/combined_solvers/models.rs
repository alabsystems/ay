// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use ay_arrays::{ArrayModel, ArraySolver};
use ay_core::{Sort, TermStore};
use ay_euf::{EufModel, EufSolver};
use ay_lia::LiaModel;
use ay_lra::LraModel;

use crate::executor_format::{format_bigint, format_rational};

/// LIA owns both integer views, including commitment of speculative EUF values.
fn lia_values_are_merged(euf_model: &EufModel, lia_model: &LiaModel) -> bool {
    lia_model.values.iter().all(|(term, value)| {
        euf_model.int_values.get(term) == Some(value)
            && euf_model.term_values.get(term) == Some(&format_bigint(value))
            && !euf_model.speculative_int_terms.contains(term)
    })
}

/// LRA owns only Real-sorted terms. Its registration map may also carry
/// numerical defaults for Int, Bool or Array terms; those are not merge inputs.
/// Check identities and values rather than comparing unrelated map sizes.
pub(super) fn real_values_are_merged(
    euf_model: &EufModel,
    lra_model: &LraModel,
    terms: &TermStore,
) -> bool {
    lra_model.values.iter().all(|(term, value)| {
        !matches!(terms.sort(*term), Sort::Real)
            || euf_model.term_values.get(term) == Some(&format_rational(value))
    })
}

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
        debug_assert!(
            lia_values_are_merged(euf_model, lia_model),
            "BUG: LIA merge did not commit every exact integer key in both EUF views"
        );
    }
}

/// Merge LRA values into an EUF model for Real-sorted terms.
///
/// LRA is authoritative for Real-sorted terms, same rationale as `merge_lia_values`.
/// Every other sort is skipped. Int-sorted terms take their values from LIA, and
/// LRA's unconstrained defaults would overwrite correct LIA values with
/// unparseable Real literals (#6291). A term of a non-arithmetic sort that LRA
/// happens to hold a value for is not a number at all: a RoundingMode constant
/// whose class names `roundTowardZero` printed as `|0.0|` (2026-09-30 FP
/// verify 2, `preexisting_rm_value_0_0.smt2`).
pub(super) fn merge_lra_values(euf_model: &mut EufModel, lra_model: &LraModel, terms: &TermStore) {
    let size_before = euf_model.term_values.len();
    for (&term_id, val) in &lra_model.values {
        if !matches!(*terms.sort(term_id), Sort::Real) {
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
    debug_assert!(
        real_values_are_merged(euf_model, lra_model, terms),
        "BUG: LRA merge did not preserve every exact Real key and value in EUF"
    );
}

/// Reconcile shared Int terms that appear in both LIA and LRA models.
///
/// In LIRA-family solvers the LRA side can see tighter `to_real(x)` constraints
/// than the LIA side. If LRA found an integral value for a shared Int term, keep
/// it and update LIA so model validation sees one coherent assignment. If LRA's
/// value is non-integral, keep the existing LIA-to-LRA patching behavior used by
/// `to_int` floor repairs.
///
/// LRA's integral value is adopted only when it falsifies none of LIA's own
/// asserted literals (`lia_falsified`): an Int term the Real side also carries
/// (e.g. through a forwarded bound) can sit at an integral relaxation value
/// that an Int-only atom excludes. Measured (QF_AUFLIRA, an unused Real
/// declared): `(and (= (select A 1) 7) (< a 4))` published `a = 4` over LIA's
/// `a = 0`, and the model gate refused `a < 4`.
pub(super) fn reconcile_lia_lra_values(
    lia_model: &mut Option<LiaModel>,
    lra_model: &mut LraModel,
    lia_authoritative: &ay_core::kani_compat::DetHashSet<ay_core::TermId>,
    lia_falsified: &dyn Fn(&LiaModel) -> bool,
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
        let adopt_lra = lra_val.is_integer() && !lia_authoritative.contains(&term) && {
            let previous = lia.values.insert(term, lra_val.to_integer());
            let falsified = lia_falsified(lia);
            if falsified {
                if let Some(previous) = previous {
                    lia.values.insert(term, previous);
                }
            }
            !falsified
        };
        if !adopt_lra {
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
    use ay_core::{ArraySort, TermId};
    use num_bigint::BigInt;
    use num_rational::BigRational;

    #[test]
    fn merge_lia_values_overwrites_both_euf_integer_views() {
        let term = TermId(0);
        let mut euf = EufModel::default();
        euf.int_values.insert(term, BigInt::from(0));
        euf.term_values.insert(term, "0".to_string());
        euf.speculative_int_terms.insert(term);
        let mut lia = LiaModel {
            values: Default::default(),
        };
        lia.values.insert(term, BigInt::from(7));

        merge_lia_values(&mut euf, Some(&lia));

        assert_eq!(euf.int_values.get(&term), Some(&BigInt::from(7)));
        assert_eq!(euf.term_values.get(&term).map(String::as_str), Some("7"));
        assert!(!euf.speculative_int_terms.contains(&term));
    }

    #[test]
    fn integer_coverage_rejects_wrong_keys_views_and_speculative_values() {
        let term = TermId(0);
        let other = TermId(1);
        let lia = LiaModel {
            values: [(term, BigInt::from(7))].into_iter().collect(),
        };
        let mut euf = EufModel::default();
        euf.int_values.insert(other, BigInt::from(7));
        euf.term_values.insert(other, "7".into());
        assert!(!lia_values_are_merged(&euf, &lia));

        euf.int_values.insert(term, BigInt::from(7));
        euf.term_values.insert(term, "0".into());
        assert!(!lia_values_are_merged(&euf, &lia));
        euf.int_values.insert(term, BigInt::from(0));
        euf.term_values.insert(term, "7".into());
        assert!(!lia_values_are_merged(&euf, &lia));
        euf.int_values.insert(term, BigInt::from(7));
        euf.speculative_int_terms.insert(term);
        assert!(!lia_values_are_merged(&euf, &lia));
        euf.speculative_int_terms.remove(&term);
        assert!(lia_values_are_merged(&euf, &lia));
    }

    #[test]
    fn real_merge_preserves_integer_bool_and_array_ownership_without_padding() {
        let mut terms = TermStore::new();
        let real = terms.mk_var("r", Sort::Real);
        let integer = terms.mk_var("i", Sort::Int);
        let boolean = terms.mk_var("p", Sort::Bool);
        let array = terms.mk_var(
            "a",
            Sort::Array(Box::new(ArraySort::new(Sort::Int, Sort::Real))),
        );
        let index = terms.mk_int(3.into());
        let store = terms.mk_store(array, index, real);
        let mut euf = EufModel::default();
        let lia = LiaModel {
            values: [(integer, BigInt::from(7))].into_iter().collect(),
        };
        merge_lia_values(&mut euf, Some(&lia));
        euf.term_values.insert(boolean, "true".into());
        euf.term_values.insert(array, "a!0".into());
        euf.term_values.insert(real, "0.0".into());
        let value = BigRational::new(3.into(), 2.into());
        let lra = LraModel {
            values: [
                (real, value.clone()),
                (integer, BigRational::from_integer(0.into())),
                (boolean, BigRational::from_integer(0.into())),
                (array, BigRational::from_integer(0.into())),
                (store, BigRational::from_integer(0.into())),
            ]
            .into_iter()
            .collect(),
        };

        merge_lra_values(&mut euf, &lra, &terms);

        assert_eq!(euf.term_values.get(&real), Some(&format_rational(&value)));
        assert!(lia_values_are_merged(&euf, &lia));
        assert_eq!(
            euf.term_values.get(&boolean).map(String::as_str),
            Some("true")
        );
        assert_eq!(euf.term_values.get(&array).map(String::as_str), Some("a!0"));
        assert!(!euf.term_values.contains_key(&store));
        assert!(!euf.int_values.contains_key(&real));
        assert!(euf.term_values.len() < lra.values.len());
        assert!(real_values_are_merged(&euf, &lra, &terms));
    }

    #[test]
    fn real_coverage_rejects_missing_or_wrong_values_despite_sufficient_map_size() {
        let mut terms = TermStore::new();
        let real = terms.mk_var("r", Sort::Real);
        let other = terms.mk_var("other", Sort::Real);
        let value = BigRational::new(3.into(), 2.into());
        let lra = LraModel {
            values: [(real, value.clone())].into_iter().collect(),
        };
        let mut euf = EufModel::default();
        euf.term_values.insert(other, format_rational(&value));
        assert_eq!(euf.term_values.len(), lra.values.len());
        assert!(!real_values_are_merged(&euf, &lra, &terms));
        euf.term_values.insert(real, "0.0".into());
        assert!(!real_values_are_merged(&euf, &lra, &terms));
        euf.term_values.insert(real, format_rational(&value));
        assert!(real_values_are_merged(&euf, &lra, &terms));
    }

    #[test]
    fn lra_merge_checks_real_values_without_overwriting_other_sorts() {
        let mut terms = TermStore::new();
        let real = terms.mk_var("r", Sort::Real);
        let integer = terms.mk_var("i", Sort::Int);
        let opaque = terms.mk_var("b", Sort::Bool);
        let mut euf = EufModel::default();
        euf.term_values.insert(integer, "7".to_string());
        euf.term_values.insert(opaque, "true".to_string());
        let mut lra = LraModel {
            values: Default::default(),
        };
        for term in [real, integer, opaque] {
            lra.values.insert(term, BigRational::from_integer(3.into()));
        }
        assert!(!real_values_are_merged(&euf, &lra, &terms));
        merge_lra_values(&mut euf, &lra, &terms);
        assert!(real_values_are_merged(&euf, &lra, &terms));
        assert_eq!(euf.term_values[&integer], "7");
        assert_eq!(euf.term_values[&opaque], "true");
        euf.term_values.insert(real, "4.0".to_string());
        assert!(!real_values_are_merged(&euf, &lra, &terms));
        euf.term_values.remove(&real);
        assert!(!real_values_are_merged(&euf, &lra, &terms));
    }
}
