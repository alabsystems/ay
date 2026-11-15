// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The one explanation for an UNSAT the NRA cannot narrow: the asserted set
//! PLUS every cross-theory fact the inner LRA holds (#nonlinear-shared-reasons).
//!
//! Same rule as the NIA's `full_conflict.rs`: the inner LRA's state is the
//! atoms this solver asserted into it, the EUF shared equalities and
//! disequalities (held as bounds on difference rows and as disequality
//! constraints) and cross-sort bounds the combiner forwarded, and this
//! solver's own lemmas. A decision that names the whole asserted set as its
//! explanation must also name those facts, or the conflict is not a theorem
//! once one of them carried the refutation (QF_UFNIA `euf_div_010` was
//! answered `unsat` that way). Today's NRA full-set sites — the exact
//! pre-phases (interval, SOS, `is_int`, linear substitution, univariate,
//! ICP) and the sign check — decide from asserted atoms alone, so for them
//! the widening only weakens the learned clause; it is applied anyway so that
//! no future full-set site can forget it. The post-refinement recheck returns
//! the LRA's own conflict, which carries its reasons, and is not a full-set
//! site.
//!
//! Every full-set site in this crate goes through [`NraSolver::full_conflict_lits`];
//! none maps `self.asserted` to a conflict by hand.

use crate::NraSolver;
use ay_core::kani_compat::DetHashSet;
use ay_core::TheoryLit;

impl NraSolver<'_> {
    /// The asserted literals, in assertion order, followed by the reason
    /// literals of every cross-theory fact the inner LRA holds that are not
    /// already among them. With no cross-theory facts this is exactly the
    /// asserted set, so pure QF_NRA conflicts are unchanged.
    pub(crate) fn full_conflict_lits(&self) -> Vec<TheoryLit> {
        let mut conflict: Vec<TheoryLit> = self
            .asserted
            .iter()
            .map(|&(term, value)| TheoryLit::new(term, value))
            .collect();
        let shared = self.lra.shared_constraint_reasons();
        if !shared.is_empty() {
            let mut seen: DetHashSet<TheoryLit> = conflict.iter().copied().collect();
            conflict.extend(shared.into_iter().filter(|lit| seen.insert(*lit)));
        }
        conflict
    }

    /// A conflict the sign check derived from asserted atoms: kept as is when
    /// it is a strict subset of the asserted set, widened to
    /// [`Self::full_conflict_lits`] when it is the whole set (the shared
    /// `ay_core::nonlinear::check_sign_consistency` falls back to the full
    /// asserted set when it cannot name the contradicting assertion).
    pub(crate) fn widen_full_set_conflict(&self, conflict: Vec<TheoryLit>) -> Vec<TheoryLit> {
        if conflict.len() >= self.asserted.len() {
            self.full_conflict_lits()
        } else {
            conflict
        }
    }
}
