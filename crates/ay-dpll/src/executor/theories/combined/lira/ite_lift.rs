// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Arithmetic ITE lifting for the AUFLIRA route's assertion window.

use ay_core::kani_compat::DetHashMap as HashMap;
use ay_core::{TermId, TermStore};

/// Lift the arithmetic ITEs out of `assertions` and give each rewritten
/// assertion the proof sources of the assertion it came from.
///
/// The split loop's Tseitin setup lifts every assertion it encodes, but it
/// hands the theory only the atoms reachable from `ctx.assertions`. An
/// assertion that reaches the loop unlifted is therefore encoded through atoms
/// the theory never receives: an instance such as
/// `(= (len s) (Add (len t) (ite c 0 1)))` is lifted to
/// `(ite c (= (len s) (Add (len t) 0)) (= (len s) (Add (len t) 1)))`, whose
/// branch atoms have SAT variables and no theory counterpart. The theory then
/// accepts assignments that violate it, and the model gate turns the result
/// into `unknown`; when the unlifted atom is a top-level fact instead, its
/// conflicts name an atom with no SAT variable and the loop gives up. Lifting
/// here, as the AUFLIA and UFNIA preprocessors do, makes the two sets agree.
/// The lifted assertion is equivalent to the original, so no verdict changes
/// meaning.
pub(super) fn lift_arithmetic_ites_keeping_sources(
    terms: &mut TermStore,
    assertions: Vec<TermId>,
    sources: &mut HashMap<TermId, Vec<Vec<TermId>>>,
) -> Vec<TermId> {
    let lifted = terms.lift_arithmetic_ite_all(&assertions);
    for (before, &after) in assertions.iter().zip(&lifted) {
        if *before == after {
            continue;
        }
        let Some(before_sets) = sources.get(before).cloned() else {
            continue;
        };
        let after_sets = sources.entry(after).or_default();
        for set in before_sets {
            if !after_sets.contains(&set) {
                after_sets.push(set);
            }
        }
    }
    lifted
}
