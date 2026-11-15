// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

/// A stale position must not rewind onto a previously resolved seen variable:
/// that variable is no longer included in the open current-level counter.
/// Keep the ordinary fast path for an exact signed live trail entry. Repair
/// stale metadata only from the actual unique assignment, never by capping
/// an untrusted position to the end of the trail.
pub(super) fn extend<P: Policy>(
    s: &Solver,
    w: &mut Walk,
    var: usize,
    p: &P,
) -> Result<(), P::Error> {
    p.work(3)?;
    let positive = Literal::positive(Variable(var as u32));
    let assigned = match s.lit_val(positive) {
        1 => positive,
        -1 => positive.negated(),
        _ => {
            w.invalid_cursor = true;
            return Ok(());
        }
    };
    let position = s.var_data[var].trail_pos as usize;
    if s.trail.get(position).copied() == Some(assigned) {
        accept(w, position);
        return Ok(());
    }
    let mut actual = None;
    for at in (0..s.trail.len()).rev() {
        p.work(1)?;
        let literal = s.trail[at];
        if literal.variable().index() != var {
            continue;
        }
        if literal != assigned || actual.is_some() {
            w.invalid_cursor = true;
            return Ok(());
        }
        actual = Some(at);
    }
    if let Some(position) = actual {
        accept(w, position);
    } else {
        w.invalid_cursor = true;
    }
    Ok(())
}

fn accept(w: &mut Walk, position: usize) {
    // Even an exact live entry cannot reopen the already-resolved suffix.
    // Normal causal reasons precede their pivot, including after stable chrono
    // compaction. A noncausal/stale reason needs a semantic restart, not a
    // decrement against the residual counter using retained old seen marks.
    if w.pivot.is_some() && position >= w.index {
        w.invalid_cursor = true;
    } else {
        w.index = w.index.max(position + 1);
    }
}
