// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Where a node's deadline comes from (the development design notes §2.1, and
//! §3 "Why the deadline must be `Live`").
//!
//! The executor's deadline is extended in the middle of a call (the
//! quantifier backstop), and a stop that captured it by value stopped the
//! solve at the stale wall (`ay-dpll/src/executor/solve_deadline.rs`). A
//! check node therefore reads its deadline LIVE, from a cell its owner keeps
//! moving, at every poll.

use std::sync::atomic::{AtomicU64, Ordering};
use std::sync::{Arc, OnceLock};
use std::time::Duration;

use crate::time::Instant;

/// A node's own deadline.
#[derive(Clone, Debug, Default)]
pub enum DeadlineSource {
    /// No deadline of its own (an ancestor's may still apply, GT1).
    #[default]
    None,
    /// A deadline fixed when the node is built.
    Fixed(Instant),
    /// A deadline read from a shared cell at every poll, so a move the cell's
    /// owner makes in the middle of a call is seen by every node built on it.
    Live(LiveDeadline),
}

impl DeadlineSource {
    /// The deadline now (`None`: no deadline of its own).
    #[must_use]
    pub fn get(&self) -> Option<Instant> {
        match self {
            Self::None => None,
            Self::Fixed(at) => Some(*at),
            Self::Live(cell) => cell.get(),
        }
    }
}

impl From<Option<Instant>> for DeadlineSource {
    fn from(deadline: Option<Instant>) -> Self {
        deadline.map_or(Self::None, Self::Fixed)
    }
}

/// A shared, live deadline: `Clone` hands out another handle on the SAME
/// cell, and [`LiveDeadline::set`] is seen by every handle at its next read.
///
/// One atomic load per read, no lock: the deadline is kept as a signed count
/// of nanoseconds from a process epoch, so every instant reads back exactly
/// as it was set, one before the epoch included (the executor's deadline
/// cells save a deadline and restore it, GuardTree step S2). Only an instant
/// more than about 146 years from the epoch reads back as that bound.
#[derive(Clone, Debug, Default)]
pub struct LiveDeadline {
    cell: Arc<Cell>,
}

#[derive(Debug)]
struct Cell {
    /// [`encode`]d: nanoseconds from [`epoch`], or [`NO_DEADLINE`].
    at: AtomicU64,
    /// Bumped by every [`LiveDeadline::set`].
    generation: AtomicU64,
}

impl Default for Cell {
    fn default() -> Self {
        Self {
            at: AtomicU64::new(NO_DEADLINE),
            generation: AtomicU64::new(0),
        }
    }
}

const NO_DEADLINE: u64 = u64::MAX;

/// The instant every encoded deadline counts from; fixed at first use.
fn epoch() -> Instant {
    static EPOCH: OnceLock<Instant> = OnceLock::new();
    *EPOCH.get_or_init(Instant::now)
}

/// The largest distance from the epoch kept exactly, in nanoseconds (2^62 - 1
/// ns, about 146 years); a farther instant is kept as this far.
const MAX_NANOS: u64 = (1 << 62) - 1;

/// The low bit says which side of the epoch the instant is on (1: before),
/// the rest is its distance in nanoseconds. Never [`NO_DEADLINE`].
fn encode(deadline: Option<Instant>) -> u64 {
    deadline.map_or(NO_DEADLINE, |at| {
        let epoch = epoch();
        let (distance, before) = match at.checked_duration_since(epoch) {
            Some(after) => (after, 0),
            None => (epoch.saturating_duration_since(at), 1),
        };
        let nanos = u64::try_from(distance.as_nanos()).map_or(MAX_NANOS, |n| n.min(MAX_NANOS));
        (nanos << 1) | before
    })
}

fn decode(raw: u64) -> Option<Instant> {
    if raw == NO_DEADLINE {
        return None;
    }
    let distance = Duration::from_nanos(raw >> 1);
    if raw & 1 == 0 {
        epoch().checked_add(distance)
    } else {
        // It was an instant once, so it is one again; the epoch, which has
        // passed too, if the platform says otherwise.
        epoch().checked_sub(distance).or_else(|| Some(epoch()))
    }
}

impl LiveDeadline {
    /// A new cell holding `deadline`.
    #[must_use]
    pub fn new(deadline: Option<Instant>) -> Self {
        let live = Self::default();
        live.cell.at.store(encode(deadline), Ordering::Release);
        live
    }

    /// The deadline at this instant.
    #[must_use]
    pub fn get(&self) -> Option<Instant> {
        decode(self.cell.at.load(Ordering::Acquire))
    }

    /// Install, move or clear the deadline, for every handle on this cell.
    pub fn set(&self, deadline: Option<Instant>) {
        self.cell.at.store(encode(deadline), Ordering::Release);
        self.cell.generation.fetch_add(1, Ordering::AcqRel);
        super::hot::stop_source_moved();
    }

    /// Whether `other` is a handle on this same cell.
    #[must_use]
    pub fn is_same(&self, other: &Self) -> bool {
        Arc::ptr_eq(&self.cell, &other.cell)
    }

    /// How many times [`Self::set`] has run: a poll armed at one generation
    /// knows the deadline moved once this does.
    #[must_use]
    pub fn generation(&self) -> u64 {
        self.cell.generation.load(Ordering::Acquire)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn every_instant_reads_back_as_itself_on_either_side_of_the_epoch() {
        let epoch = epoch();
        let around = [
            Duration::from_secs(3600),
            Duration::from_millis(1),
            Duration::from_nanos(1),
        ];
        let mut instants = vec![epoch, Instant::now() + Duration::from_secs(3600)];
        for step in around {
            instants.extend(epoch.checked_sub(step));
            instants.extend(epoch.checked_add(step));
        }
        for at in instants {
            assert_eq!(decode(encode(Some(at))), Some(at), "{at:?}");
            let cell = LiveDeadline::new(Some(at));
            assert_eq!(cell.get(), Some(at));
        }
        assert_eq!(decode(encode(None)), None);
        assert_ne!(encode(Some(epoch)), NO_DEADLINE);
    }
}
