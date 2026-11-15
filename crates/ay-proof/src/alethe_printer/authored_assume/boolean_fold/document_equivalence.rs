// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Boolean folds onto the document rendering under its original emission owner.

use super::super::super::quantifier_surface::printed_terms_alpha_equivalent_with_progress;
use super::{fold_reads_opaque_syntax, normalize::fold_surface_with_progress};

/// Uncontrolled compatibility entry for callers without an emission owner.
/// Production admission and rendering use the progress-aware entry below.
#[cfg(test)]
pub(in crate::alethe_printer::authored_assume) fn render_folded_document_equivalence(
    id: impl std::fmt::Display,
    surface: &str,
    rendering: &str,
) -> (Option<String>, usize) {
    render_folded_document_equivalence_with_progress(
        &id.to_string(),
        surface,
        rendering,
        &mut |_| true,
    )
}

/// The [`super::AuthoredAssumeBridge::FoldedDocumentEquivalence`] bridge for the
/// `assume` `id`, with the fold's node count: the authored `surface` folds
/// onto `rendering`, the text the document prints for the assumed term with
/// only its own override set aside (`document_canonical`), byte for byte or
/// up to carcara's `alpha_equiv` (equality operand order, bit-vector literal
/// notation; one `refl`, as in `fold_remainder`). The
/// derivation reads nothing but the two texts, so the emitter re-renders the
/// planned bridge byte for byte.
///
/// ```text
/// (assume t0.a (= (bvult b #x03) false))
/// (step t0.n (cl (= (= (bvult b #x03) false) (not (bvult b #x03)))) :rule equiv_simplify)
/// (step t0.e (cl (not (= (= (bvult b #x03) false) (not (bvult b #x03)))) (not (= (bvult b #x03) false)) (not (bvult b #x03))) :rule equiv_pos2)
/// (step t0 (cl (not (bvult b #x03))) :rule resolution :premises (t0.e t0.n t0.a))
/// ```
///
/// Declines a fold that only re-spelled a connective (`distinct_elim` alone is
/// the dedicated distinct bridge's), a fold through an annotation, a `let` or
/// a binder, and any fold whose result is not the rendering.
pub(in crate::alethe_printer::authored_assume) fn render_folded_document_equivalence_with_progress(
    id: &str,
    surface: &str,
    rendering: &str,
    progress: &mut dyn FnMut(u64) -> bool,
) -> (Option<String>, usize) {
    let mut nodes = 0;
    // Six bounded syntax scans precede the fold, including declining paths.
    let Some(scan_work) = surface
        .len()
        .checked_mul(6)
        .and_then(|n| n.checked_add(id.len()))
        .and_then(|n| n.checked_add(2))
        .and_then(|n| u64::try_from(n).ok())
    else {
        return (None, nodes);
    };
    if !progress(scan_work) {
        return (None, nodes);
    }
    if fold_reads_opaque_syntax(surface) {
        return (None, 1);
    }
    let fold_id = format!("{id}.n");
    let Some((folded, steps, true)) =
        fold_surface_with_progress(surface, &fold_id, 0, &mut nodes, progress)
    else {
        return (None, nodes.max(1));
    };
    let Some(comparison_bytes) = folded
        .len()
        .checked_add(rendering.len())
        .and_then(|n| u64::try_from(n).ok())
    else {
        return (None, nodes);
    };
    if !progress(comparison_bytes) {
        return (None, nodes);
    }
    let exact = folded == rendering;
    if !exact && !printed_terms_alpha_equivalent_with_progress(&folded, rendering, progress) {
        return (None, nodes);
    }
    let Some(output_bound) = bridge_output_bound(id, surface, &folded, rendering, &steps) else {
        return (None, nodes);
    };
    if !progress(output_bound) {
        return (None, nodes);
    }
    let mut output = format!("(assume {id}.a {surface})\n");
    for step in steps {
        output.push_str(&step);
        output.push('\n');
    }
    let equality_id = if exact {
        fold_id
    } else {
        output.push_str(&format!(
            "(step {id}.r (cl (= {folded} {rendering})) :rule refl)\n\
             (step {id}.t (cl (= {surface} {rendering})) :rule trans :premises ({fold_id} {id}.r))\n"
        ));
        format!("{id}.t")
    };
    output.push_str(&format!(
        "(step {id}.e (cl (not (= {surface} {rendering})) (not {surface}) {rendering}) :rule equiv_pos2)\n\
         (step {id} (cl {rendering}) :rule resolution :premises ({id}.e {equality_id} {id}.a))"
    ));
    if !progress(0) {
        return (None, nodes);
    }
    (Some(output), nodes)
}

/// The fixed bridge repeats each input or identifier fewer than sixteen times,
/// even with the optional refl/trans pair. One KiB covers its fixed syntax.
/// Fold steps are copied once with a newline. Admit this checked upper bound
/// before final assembly; overflow must not grant a smaller work allowance.
fn bridge_output_bound(
    id: &str,
    surface: &str,
    folded: &str,
    rendering: &str,
    steps: &[String],
) -> Option<u64> {
    let text_bytes = [id, surface, folded, rendering]
        .into_iter()
        .try_fold(0usize, |sum, text| sum.checked_add(text.len()))?
        .checked_mul(16)?;
    let bytes = steps
        .iter()
        .try_fold(text_bytes.checked_add(1024)?, |sum, step| {
            sum.checked_add(step.len())?.checked_add(1)
        })?;
    u64::try_from(bytes).ok()
}

#[cfg(test)]
#[path = "document_equivalence_tests.rs"]
mod tests;
