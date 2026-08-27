//! THIS THREAD's share of the crate's process-global diagnostic counters.
//!
//! # The defect this exists to fix
//!
//! The search and the simplex keep a family of process-global `Atomic*`
//! totals — `NODE_CUT_WRITES_TOTAL`, `BB_PAIRS_TOTAL`, `ETA_REUSE_COUNT`,
//! `SYM_ROWS_TOTAL`, and a dozen more. They are diagnostics: `--trace`
//! prints them and nothing in the search reads them.
//!
//! Tests read them for a different purpose: as a NON-VACUITY GUARD. A test
//! that solves a corpus against brute force and then asserts
//! `NODE_CUT_WRITES_TOTAL.load() > before` is saying "and the engine I claim
//! to be testing actually fired — otherwise this corpus proved nothing".
//! That is a real and valuable assertion, and the counter is the wrong
//! instrument for it: libtest runs this crate's other ~1,450 tests on other
//! threads while any one of them runs, and hundreds of them solve models.
//! `load() - before` is therefore "what the whole binary charged in that
//! interval", not "what this test charged".
//!
//! For a FLOOR (`> before`) the error is one-directional and it is the
//! DANGEROUS direction. A foreign bump cannot make a satisfied floor
//! unsatisfied, so these guards do not flake — instead a foreign bump SUPPLIES
//! the floor, and the guard passes whether or not the engine under test fired.
//! The guard exists precisely to catch "the engine silently stopped firing";
//! a sibling's bump makes it pass in exactly that case.
//!
//! MEASURED, in both directions, and the observation is a NEGATIVE worth
//! keeping:
//!
//! * OBSERVED EXPOSURE, ZERO. Three full concurrent lib-suite runs (1,147
//!   tests, 38–63 s each, box load 15–55) with every converted site printing
//!   `local` against `global`: `foreign=0` in all twenty windows, all three
//!   runs. No floor in this suite is currently being supplied by a sibling.
//!   The reason is structural, not luck — every one of these counters is
//!   charged only under an opt-in knob, and the tests that force those knobs
//!   hold `ay_test_support::env::lock_env`, which serialises them against each
//!   other. That is an ACCIDENT of the current suite: it depends on no future
//!   test charging one of these counters without taking that lock.
//! * CONSTRUCTED EXPOSURE, DETERMINISTIC. `tune::activate_caller` is
//!   thread-local, so the eta-reuse feature can be killed on the asserting
//!   thread by its own shipped switch while a thread spawned inside the window
//!   runs it LIVE, through the production path. Then `global=1, local=0`: the
//!   process-global spelling of `cross_solve_eta_reuse_matches_a_fresh_solve`'s
//!   floor PASSES with the feature it guards dead, 3/3 runs, and the
//!   per-thread spelling fails. That is the masking, end to end, on real
//!   production charges.
//!
//! For an EXACT delta (`- before == 2`) the error is two-directional: a
//! sibling bump also breaks an honest run, which is how the class was first
//! noticed (`759cf08c6`).
//!
//! # The instrument
//!
//! libtest gives each test its own thread, so a per-thread mirror of a
//! counter is the same number with the other tests removed. [`add_usize`] /
//! [`add_u64`] write the global exactly as the bare `fetch_add` they replace
//! did, and additionally — `#[cfg(test)]` only, so the shipped build is the
//! same instruction stream — charge this thread's mirror. [`local_usize`] /
//! [`local_u64`] read it back.
//!
//! # Where this is the WRONG instrument
//!
//! A per-thread mirror measures the ASSERTING thread. Two situations break
//! that, and both are recorded at the sites concerned rather than papered
//! over here:
//!
//! * the charge happens on a thread the test spawned (`sepstat`'s
//!   `concurrent_distinct_rows_have_one_winner_and_charge_its_rows`) — the
//!   fix there is for each worker to report its OWN mirror delta;
//! * the charge happens on a worker the SEARCH spawned (`bab.rs`'s
//!   shared-prefix worker pool) — the mirror on the caller's thread reads
//!   zero and the guard becomes unsatisfiable, which is a destroyed test, not
//!   a fixed one. Sites in that class keep the global spelling and say so.
//!
//! The counters keep their process-wide meaning for `--trace`: this module
//! only adds a second, narrower reading of the same charges.

/// Charge `n` to a process-global `usize` census total, and to this thread's
/// mirror of it.
///
/// Byte-for-byte the `fetch_add(n, Relaxed)` it replaces in a non-test build:
/// the mirror is `#[cfg(test)]` and the function is `#[inline]`.
#[inline]
pub(crate) fn add_usize(counter: &'static std::sync::atomic::AtomicUsize, n: usize) {
    counter.fetch_add(n, std::sync::atomic::Ordering::Relaxed);
    #[cfg(test)]
    imp::tally(std::ptr::from_ref(counter) as usize, n as u64);
}

/// [`add_usize`] for a `u64` counter.
#[inline]
pub(crate) fn add_u64(counter: &'static std::sync::atomic::AtomicU64, n: u64) {
    counter.fetch_add(n, std::sync::atomic::Ordering::Relaxed);
    #[cfg(test)]
    imp::tally(std::ptr::from_ref(counter) as usize, n);
}

/// This thread's running total for a `usize` counter. The delta-asserting
/// instrument; the counter itself keeps its process-wide `--trace` meaning.
#[cfg(test)]
pub(crate) fn local_usize(counter: &'static std::sync::atomic::AtomicUsize) -> u64 {
    imp::read(std::ptr::from_ref(counter) as usize)
}

/// This thread's running total for a `u64` counter.
#[cfg(test)]
pub(crate) fn local_u64(counter: &'static std::sync::atomic::AtomicU64) -> u64 {
    imp::read(std::ptr::from_ref(counter) as usize)
}

/// A non-vacuity guard's snapshot of one counter, in BOTH spellings.
///
/// Take one before the window, then assert on [`Floor::local`]. [`Floor::global`]
/// is kept only so the two can be compared: the difference is exactly the
/// foreign charge the old process-global spelling was accepting as if it were
/// this test's own, and [`Floor::report`] prints it under `--nocapture`.
#[cfg(test)]
pub(crate) struct Floor {
    src: Src,
    label: &'static str,
    local: u64,
    global: u64,
}

#[cfg(test)]
enum Src {
    Usize(&'static std::sync::atomic::AtomicUsize),
    U64(&'static std::sync::atomic::AtomicU64),
}

#[cfg(test)]
impl Src {
    fn key(&self) -> usize {
        match self {
            Self::Usize(c) => std::ptr::from_ref(*c) as usize,
            Self::U64(c) => std::ptr::from_ref(*c) as usize,
        }
    }

    fn load(&self) -> u64 {
        match self {
            Self::Usize(c) => c.load(std::sync::atomic::Ordering::Relaxed) as u64,
            Self::U64(c) => c.load(std::sync::atomic::Ordering::Relaxed),
        }
    }
}

#[cfg(test)]
impl Floor {
    /// Snapshot a `usize` counter.
    pub(crate) fn usize_at(
        counter: &'static std::sync::atomic::AtomicUsize,
        label: &'static str,
    ) -> Self {
        Self::new(Src::Usize(counter), label)
    }

    /// Snapshot a `u64` counter.
    pub(crate) fn u64_at(
        counter: &'static std::sync::atomic::AtomicU64,
        label: &'static str,
    ) -> Self {
        Self::new(Src::U64(counter), label)
    }

    fn new(src: Src, label: &'static str) -> Self {
        let local = imp::read(src.key());
        let global = src.load();
        Self {
            src,
            label,
            local,
            global,
        }
    }

    /// THIS THREAD's charges since the snapshot — the number a non-vacuity
    /// guard means. The instrument.
    pub(crate) fn local(&self) -> u64 {
        imp::read(self.src.key()).saturating_sub(self.local)
    }

    /// The whole process's charges since the snapshot — what the old spelling
    /// read. NOT an instrument; reported only, so the gap is visible.
    pub(crate) fn global(&self) -> u64 {
        self.src.load().saturating_sub(self.global)
    }

    /// Print `local` against `global`, so the foreign supply this guard used
    /// to accept as its own is on the record. Captured by libtest unless
    /// `--nocapture`.
    pub(crate) fn report(&self) -> u64 {
        let (local, global) = (self.local(), self.global());
        eprintln!(
            "LOCAL-CENSUS {} local={local} global={global} foreign={}",
            self.label,
            global.saturating_sub(local)
        );
        local
    }
}

#[cfg(test)]
mod imp {
    use std::cell::RefCell;

    /// Distinct counters one thread may charge. Sized for the converted set
    /// with room to spare; overflow degrades to "not mirrored", which a
    /// converted test detects immediately as an unsatisfiable floor rather
    /// than as a silent pass.
    const CAP: usize = 32;

    thread_local! {
        /// `(counter address, this thread's summed charge)`, insertion-ordered.
        /// Keyed by address rather than by a slot enum so a new counter needs
        /// no registration step to be mirrored — the failure mode of a
        /// registration table is a counter that silently is not mirrored.
        static LOCAL: RefCell<[(usize, u64); CAP]> = const { RefCell::new([(0, 0); CAP]) };
    }

    pub(super) fn tally(key: usize, n: u64) {
        LOCAL.with(|cell| {
            let Ok(mut slots) = cell.try_borrow_mut() else {
                // A counter charged from inside a `LOCAL` borrow cannot happen
                // today; refuse rather than panic if it ever does.
                return;
            };
            for slot in slots.iter_mut() {
                if slot.0 == key {
                    slot.1 = slot.1.saturating_add(n);
                    return;
                }
                if slot.0 == 0 {
                    *slot = (key, n);
                    return;
                }
            }
        });
    }

    pub(super) fn read(key: usize) -> u64 {
        LOCAL.with(|cell| {
            let Ok(slots) = cell.try_borrow() else {
                return 0;
            };
            slots
                .iter()
                .find(|slot| slot.0 == key)
                .map_or(0, |slot| slot.1)
        })
    }
}

#[cfg(test)]
mod tests {
    use std::sync::atomic::{AtomicU64, AtomicUsize};

    static PROBE_USIZE: AtomicUsize = AtomicUsize::new(0);
    static PROBE_U64: AtomicU64 = AtomicU64::new(0);

    /// The mirror tracks the global for the charges made on ONE thread, and
    /// tracks NEITHER for another thread's charges. This is the whole
    /// contract, and the second half is the point of the module.
    #[test]
    fn the_mirror_is_per_thread_and_the_global_is_not() {
        let global_before = PROBE_USIZE.load(std::sync::atomic::Ordering::Relaxed);
        let local_before = super::local_usize(&PROBE_USIZE);

        super::add_usize(&PROBE_USIZE, 3);
        super::add_usize(&PROBE_USIZE, 4);

        // A charge from a thread this test does not own — the sibling libtest
        // supplies for free, made deterministic here.
        std::thread::scope(|scope| {
            scope.spawn(|| {
                super::add_usize(&PROBE_USIZE, 100);
                assert_eq!(
                    super::local_usize(&PROBE_USIZE),
                    100,
                    "each thread mirrors only its own charges"
                );
            });
        });

        assert_eq!(
            super::local_usize(&PROBE_USIZE) - local_before,
            7,
            "this thread charged 3 + 4 and nothing else"
        );
        assert_eq!(
            PROBE_USIZE.load(std::sync::atomic::Ordering::Relaxed) - global_before,
            107,
            "the global carries the foreign charge, which is why it is not the instrument"
        );
    }

    #[test]
    fn u64_counters_mirror_independently_of_usize_counters() {
        let before = super::local_u64(&PROBE_U64);
        super::add_u64(&PROBE_U64, 11);
        assert_eq!(super::local_u64(&PROBE_U64) - before, 11);
        // A different counter is a different slot, not the same one.
        let other = super::local_usize(&PROBE_USIZE);
        super::add_u64(&PROBE_U64, 5);
        assert_eq!(super::local_usize(&PROBE_USIZE), other);
    }
}
