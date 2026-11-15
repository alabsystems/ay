// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Initial kernel state, shared by every engine using the plug-in kernel.

use super::*;

impl<'t> Kernel<'t> {
    pub(crate) fn new(
        terms: &'t mut TermStore,
        plugins: Vec<Box<dyn TheoryPlugin>>,
        families: Vec<(Family, ThId)>,
        atoms: AtomTable,
        hub: Hub,
        record_proofs: bool,
    ) -> Self {
        Self {
            terms,
            stop: None,
            guard: None,
            sigma: Vec::new(),
            stopped: false,
            plugins,
            families,
            atoms,
            hub,
            hub_var: Vec::new(),
            hub_watch: Vec::new(),
            hub_props: Vec::new(),
            hub_relevancy: false,
            relevancy: None,
            effects: Effects::default(),
            trail_pos: 0,
            cursors: Vec::new(),
            scan_pos: Cell::new(0),
            seeded_epoch: Cell::new(None),
            theory_branching: false,
            decision_calls: Cell::new(0),
            lazy: Vec::new(),
            minted: Vec::new(),
            next_mint: 0,
            last_final: None,
            preferred: Vec::new(),
            repeats: 0,
            schedule: FinalSchedule::default(),
            give_up: None,
            proof: record_proofs.then(Vec::new),
            stats: EngineStats::default(),
            final_sat: false,
        }
    }
}
