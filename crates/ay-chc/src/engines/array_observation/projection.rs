// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! An original borrowed problem, a reduced candidate problem and its typed map.
//! Shared access prevents source mutation while the candidate is in flight.
//! Rewrites/clone/drop are existing opaque operations bracketed by owner polls.

use super::{admission, map};
use crate::problem::ArrayScalarizationMap;
use crate::ChcProblem;

pub(super) struct Projection<'a> {
    pub(super) original: &'a ChcProblem,
    pub(super) reduced: ChcProblem,
    pub(super) map: ArrayScalarizationMap,
}

impl<'a> Projection<'a> {
    pub(super) fn new(original: &'a ChcProblem, poll: &mut dyn FnMut() -> bool) -> Option<Self> {
        let selects = admission::problem(original, poll)?;
        admission::projected_arity(original, selects, poll)?;
        if !poll() {
            return None;
        }
        let mut reduced = original.clone();
        if !poll() {
            return None;
        }
        // The conservative existing form declines symbolic accesses of the
        // same key sort. No extra keys, alias rewrites or user channels are
        // guessed. They may gain independently reviewed candidate lanes later.
        let map = reduced.try_scalarize_const_array_selects_with_map()?;
        if !poll() {
            return None;
        }
        admission::problem(&reduced, poll)?;
        let projected = Self {
            original,
            reduced,
            map,
        };
        map::authenticate(&projected, poll)?;
        let changed = original
            .predicates()
            .iter()
            .zip(projected.reduced.predicates())
            .any(|(old, new)| old.arg_sorts != new.arg_sorts);
        (changed && poll()).then_some(projected)
    }

    pub(super) fn reduced(&self) -> &ChcProblem {
        &self.reduced
    }
}
