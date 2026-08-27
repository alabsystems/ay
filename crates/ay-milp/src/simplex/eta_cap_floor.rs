// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::Simplex;

impl Simplex {
    /// REBUILD CAP FLOOR — keep `eta_nnz_cap` above the file a REBUILD lands
    /// on, so the nnz trigger can only fire on UPDATE GROWTH.
    ///
    /// The nnz trigger (`eta_nnz >= eta_nnz_cap && since_refactor >= 5`) exists
    /// to bound the fill that FTRAN updates add to the eta file. Its cap is
    /// derived from the MATRIX (`4*nnz`, `16*m`, `1024`), which says nothing
    /// about how big the file a rebuild PRODUCES is: a heavy or degenerate
    /// basis rebuilds straight past it, and then the trigger is armed the
    /// instant the rebuild finishes and refires every fifth pivot — a rebuild
    /// storm, in which the walk pays for a fresh inverse per five pivots and
    /// makes almost no progress. Raising the cap to the rebuilt file plus its
    /// growth allowance restores the trigger's actual meaning.
    ///
    /// THE GATE IS `floor > eta_nnz_cap` — a question about the REBUILT SIZE,
    /// asked of the rebuilt size. It used to be `cols >= BIG_LP_COLS && m >=
    /// BIG_LP_ROWS`, on the belief that "small LPs never rebuild past their
    /// static cap". But that is itself a claim about the rebuilt size, and the
    /// rebuilt size is measurable right here; the dimension test could only
    /// ever agree with the measurement or suppress it, and it suppressed it.
    /// Hexgrid covering LPs at 4,060 x 4,060 rebuild to ~860k entries against a
    /// 64,960 cap (13.2x over) and storm — 91.7% of all rebuilds fired by the
    /// nnz trigger rather than the pivot cadence — and the 8,170 x 8,170 member
    /// missed the old gate by 22 rows. Asking the measurement needs no constant
    /// of its own and cannot miss a size class.
    ///
    /// BLAST RADIUS, STATED HONESTLY BECAUSE IT IS WIDER THAN THE NNZ TRIGGER.
    /// `eta_nnz_cap` is read at five sites, so raising it also loosens the
    /// ETA-lane reuse skip, three LU-lane skips, and the peel-order fill guard —
    /// and because `reset()` runs on every warm solve entry, the real reach is
    /// "every warm MILP node", not "mid-size LPs". Previously none of those
    /// could move below 8192 x 8192. The empirical bound on that reach, measured
    /// over the 30-instance canonical corpus: 24 of 29 instances are
    /// BIT-IDENTICAL, and the movers are named and ratcheted in the commit that
    /// landed this.
    ///
    /// THE NARROWER GATE `entries >= eta_nnz_cap` (raise only when the trigger
    /// is ALREADY armed at rebuild time) was built and measured, because it is
    /// the more literal reading of "only growth can trigger" — and it is WORSE,
    /// so it is not what ships. Interleaved, quiet box: stein27 3,077 nodes /
    /// 0.117-0.126s baseline, 3,245 / 0.229-0.236s under this gate, 4,534 /
    /// 0.187-0.211s under the narrow one; domset_mw19_18 13.1-13.3s baseline,
    /// 6.5-6.8s here, 7.3-7.6s narrow. It loses on both the regression it was
    /// built to remove and the win it had to keep. A file landing just UNDER the
    /// cap re-arms after a handful of updates and storms just the same, which is
    /// what the growth allowance is for.
    ///
    /// Monotone: the cap only ever rises, and only within a solve (`reset`
    /// re-derives it from the matrix on every entry).
    pub(super) fn raise_eta_cap_floor(&mut self, entries: usize) {
        // Growth allowance: a quarter of the rebuilt file, but never less than
        // the `16*m` the static cap itself is floored at — a nearly empty rebuild
        // must not pin the cap to a value a handful of updates clears.
        let floor = entries + (entries / 4).max(16 * self.m);
        if floor > self.eta_nnz_cap {
            self.eta_nnz_cap = floor;
        }
    }
}
