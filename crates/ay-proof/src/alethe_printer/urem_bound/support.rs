// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use ay_core::kani_compat::{DetHashMap, DetHashSet};
use ay_core::{ProofId, TermData, TermId, TermStore};

/// Deny-only preflight of the native remainder-bound certificate surface.
///
/// The same borrowed continuation pays the full typed source census and the
/// override scan. A reached override is conservatively refused here; actual
/// export may additionally admit an exactly unchanged spelling. A `true`
/// answer is neither semantic authority nor a promise that the potentially
/// expensive stage certificate fits the original remaining export budget.
pub fn checked_urem_bound_lowering_supported(
    terms: &TermStore,
    clause: &[TermId],
    overrides: Option<&DetHashMap<TermId, String>>,
    progress: &mut dyn FnMut(usize, usize) -> bool,
) -> bool {
    let Ok(shape) = crate::checker::bv_urem_bound::validate(terms, ProofId(0), clause, progress)
    else {
        return false;
    };
    let Some(overrides) = overrides.filter(|map| !map.is_empty()) else {
        return progress(0, 0);
    };
    unoverridden(terms, shape.theorem, overrides, progress).is_some()
}

fn unoverridden(
    terms: &TermStore,
    root: TermId,
    overrides: &DetHashMap<TermId, String>,
    progress: &mut dyn FnMut(usize, usize) -> bool,
) -> Option<()> {
    progress(1, 4).then_some(())?;
    let mut stack = Vec::new();
    stack.try_reserve(1).ok()?;
    stack.push(root);
    let mut seen = DetHashSet::default();
    let accepted = (|| {
        while let Some(id) = stack.pop() {
            progress(1, 64).then_some(())?;
            seen.try_reserve(1).ok()?;
            if !seen.insert(id) {
                continue;
            }
            if overrides.contains_key(&id) {
                return None;
            }
            let inline;
            let children: &[TermId] = match terms.get(id) {
                TermData::App(_, args) => args,
                TermData::Not(arg) => std::slice::from_ref(arg),
                TermData::Ite(c, a, b) => {
                    inline = [*c, *a, *b];
                    &inline
                }
                TermData::Const(_) | TermData::Var(..) => &[],
                _ => return None,
            };
            progress(children.len(), children.len().checked_mul(4)?).then_some(())?;
            stack.try_reserve(children.len()).ok()?;
            stack.extend_from_slice(children);
        }
        Some(())
    })();
    drop(stack);
    drop(seen);
    accepted?;
    progress(0, 0).then_some(())
}
