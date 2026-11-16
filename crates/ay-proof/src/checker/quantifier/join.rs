// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Strict, original-caller-metered validation of canonical Alethe `qnt_join`.

use ay_core::kani_compat::DetHashSet as HashSet;
use ay_core::{ProofId, Sort, Symbol, TermData, TermId, TermStore};

use super::progress::QuantifierMeter;
use super::ProofCheckError;

type Quantifier<'a> = (bool, &'a [(String, Sort)], TermId);

fn quantifier<'a>(
    terms: &'a TermStore,
    term: TermId,
    meter: &mut QuantifierMeter<'_, '_>,
) -> Result<Quantifier<'a>, ProofCheckError> {
    let sort = meter.sort(terms, term)?;
    if !meter.sort_equal(sort, &Sort::Bool)? {
        return Err(meter.invalid("quantifier result must have Bool sort")?);
    }
    match meter.term(terms, term)? {
        TermData::Forall(bindings, body, _) => Ok((false, bindings.as_slice(), *body)),
        TermData::Exists(bindings, body, _) => Ok((true, bindings.as_slice(), *body)),
        _ => Err(meter.invalid("join operands must be quantifiers")?),
    }
}

fn equality(
    terms: &TermStore,
    clause: &[TermId],
    meter: &mut QuantifierMeter<'_, '_>,
) -> Result<(TermId, TermId), ProofCheckError> {
    let [equality] = clause else {
        return Err(meter.invalid("conclusion must be one equality literal")?);
    };
    let TermData::App(Symbol::Named(name), args) = meter.term(terms, *equality)? else {
        return Err(meter.invalid("conclusion must use canonical named equality")?);
    };
    meter.name(name)?;
    let sort = meter.sort(terms, *equality)?;
    if name != "=" || args.len() != 2 || !meter.sort_equal(sort, &Sort::Bool)? {
        return Err(meter.invalid("conclusion must be a Boolean binary equality")?);
    }
    Ok((args[0], args[1]))
}

fn binders(
    outer: &[(String, Sort)],
    inner: &[(String, Sort)],
    joined: &[(String, Sort)],
    meter: &mut QuantifierMeter<'_, '_>,
) -> Result<(), ProofCheckError> {
    let length = outer
        .len()
        .checked_add(inner.len())
        .ok_or(ProofCheckError::ResourceLimit)?;
    if outer.is_empty() || inner.is_empty() || joined.len() != length {
        return Err(meter.invalid("join needs two non-empty exactly concatenated binder lists")?);
    }
    for ((left_name, left_sort), (right_name, right_sort)) in outer.iter().chain(inner).zip(joined)
    {
        meter.visit()?;
        meter.name(left_name)?;
        meter.name(right_name)?;
        if left_name != right_name || !meter.sort_equal(left_sort, right_sort)? {
            return Err(meter
                .invalid("right binders must exactly concatenate the outer and inner lists")?);
        }
    }
    let mut names = HashSet::default();
    for (name, _) in joined {
        meter.visit()?;
        meter.name_set_entry(&names, name)?;
        if !names.insert(name.as_str()) {
            return Err(meter.invalid("joined binder names must be distinct")?);
        }
    }
    // Borrowed keys and all table scratch are retired before final admission.
    meter.table_iteration(names.len())?;
    drop(names);
    meter.charge(0, 0)
}

/// Validate the binder-join step `(Q x⃗ (Q y⃗ φ)) = (Q x⃗y⃗ φ)`.
///
/// # Shape
///
/// A premiseless, argument-free unit clause `(cl (= N J))`: `N` is a
/// quantifier `Q x⃗` whose body is a quantifier `Q y⃗` of the SAME kind, `J`
/// is a quantifier `Q z⃗` of that kind, `z⃗` is exactly `x⃗` followed by `y⃗`
/// (names, sorts and order), every name of `z⃗` is distinct, and the bodies
/// of `Q y⃗` and `Q z⃗` are the same interned `φ`. This is Alethe's
/// `qnt_join` conclusion, which the pinned Carcara checks under the same
/// name.
///
/// # Soundness argument
///
/// `∃x⃗.∃y⃗.φ ≡ ∃x⃗y⃗.φ` and `∀x⃗.∀y⃗.φ ≡ ∀x⃗y⃗.φ` hold whenever no name of `y⃗`
/// re-binds a name of `x⃗`: then every occurrence in `φ` of a name of `x⃗`
/// or `y⃗` is bound by the binder of the same name and sort on both sides,
/// and a valuation of the pair `(x⃗, y⃗)` is exactly a valuation of `z⃗`.
/// Nothing is substituted, so there is no capture to consider. Each
/// precondition below is load-bearing and re-derived from the clause alone:
///
/// * **one quantifier kind for all three** — `∃x.∀y.φ` is not `∃xy.φ`;
/// * **`z⃗ = x⃗ ++ y⃗` exactly** — a dropped, reordered-by-sort, renamed or
///   re-sorted binder changes which occurrences are bound and by what domain;
/// * **distinct names in `z⃗`** — with `x` in both lists the inner binder
///   shadows the outer one in `N`, while `J` binds `x` once: the two sides
///   then quantify different variable sets;
/// * **the same interned body** — terms are hash-consed, so this is exact
///   identity, not an approximation;
/// * **non-empty `x⃗` and `y⃗`** and a **Boolean body** — a malformed raw
///   quantifier has no such equivalence.
///
/// A violated precondition REJECTS, so a wrong step costs completeness, never
/// soundness.
#[cfg(test)]
pub(crate) fn validate_qnt_join(
    terms: &TermStore,
    step: ProofId,
    clause: &[TermId],
    premise_count: usize,
    args: &[TermId],
) -> Result<(), ProofCheckError> {
    validate_qnt_join_with_progress(terms, step, clause, premise_count, args, &mut |_, _| true)
}

/// Re-derive the join within the unchanged caller callback. The local visit
/// ceiling only bounds this walk; it never issues a caller work/memory grant.
pub(crate) fn validate_qnt_join_with_progress(
    terms: &TermStore,
    step: ProofId,
    clause: &[TermId],
    premise_count: usize,
    args: &[TermId],
    progress: &mut dyn FnMut(usize, usize) -> bool,
) -> Result<(), ProofCheckError> {
    let mut work = 0usize;
    let mut meter = QuantifierMeter::new(step, "qnt_join", &mut work, progress);
    meter.charge(1, 0)?;
    if premise_count != 0 || !args.is_empty() {
        return Err(meter.invalid("join must not have premises or arguments")?);
    }
    let (nested, joined) = equality(terms, clause, &mut meter)?;
    let (outer_exists, outer, outer_body) = quantifier(terms, nested, &mut meter)?;
    let (inner_exists, inner, body) = quantifier(terms, outer_body, &mut meter)?;
    let (joined_exists, joined_bindings, joined_body) = quantifier(terms, joined, &mut meter)?;
    if outer_exists != inner_exists || outer_exists != joined_exists {
        return Err(meter.invalid("all three quantifiers must be of one kind")?);
    }
    let body_sort = meter.sort(terms, body)?;
    if joined_body != body || !meter.sort_equal(body_sort, &Sort::Bool)? {
        return Err(meter.invalid("both sides must share the same Boolean body")?);
    }
    binders(outer, inner, joined_bindings, &mut meter)?;
    meter.charge(0, 0)
}

#[cfg(test)]
#[path = "join_resource_tests.rs"]
mod resource_tests;
#[cfg(test)]
#[path = "join_tests.rs"]
mod tests;
