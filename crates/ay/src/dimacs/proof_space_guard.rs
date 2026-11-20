// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

/// The free space the proof keeps on its own filesystem (2026-09-20).
///
/// SAT-COMP 2026 states no proof-size limit and nothing about scratch disk, so
/// how large a proof may grow is our policy. The policy is a reserve and not a
/// ceiling: a proof too large for the checker's budget scores what no proof
/// scores, so a fixed ceiling can only lose an UNSAT the disk could have held,
/// while a filled disk costs every later instance on the machine. The writer
/// therefore stops the PROOF — never the search (77d0e04fb) — when a probe
/// finds the filesystem down to this much free space.
const PROOF_FREE_SPACE_RESERVE_BYTES: u64 = 2 * 1024 * 1024 * 1024;

/// The byte cadence of the probe. `statvfs` is cheap but not free, and the
/// proof grows at 6 to 19 MB/s on the instances that write the most
/// (competition/proof-posture-parity/capoff-1500-traces.tsv at 9598c4206), so 256 MiB is a look
/// every 14 to 45 seconds there. The interval is clamped to an eighth of the
/// reserve so a small reserve keeps its meaning: between two probes at most
/// `interval` bytes are written, so the floor actually held is
/// `reserve - interval`.
const PROOF_FREE_SPACE_PROBE_BYTES: u64 = 256 * 1024 * 1024;

/// Free bytes on the filesystem holding `dir`, or `None` when it cannot be
/// asked — an unprobeable filesystem never stops a proof.
#[cfg(unix)]
fn proof_filesystem_free_bytes(dir: &Path) -> Option<u64> {
    let existing = dir.ancestors().find(|candidate| candidate.exists())?;
    let stats = nix::sys::statvfs::statvfs(existing).ok()?;
    // `fragment_size` is the allocation unit `blocks_available` counts; some
    // filesystems report 0 for it. `fsblkcnt_t` is u32 on macOS, u64 on Linux.
    let unit = if stats.fragment_size() == 0 {
        stats.block_size()
    } else {
        stats.fragment_size()
    };
    Some(u64::from(stats.blocks_available()).saturating_mul(u64::from(unit)))
}

#[cfg(not(unix))]
fn proof_filesystem_free_bytes(_dir: &Path) -> Option<u64> {
    None
}

/// What stops a proof before the disk does: the free-space reserve, and the
/// optional explicit ceiling of `--sat-proof-cap-bytes`.
///
/// Both stops are reported as a write error, so they reach the solver through
/// the one latch a real ENOSPC reaches (`BoxedWriter`'s first error, the format
/// writer's `io_failed`, `Solver::proof_write_failure`). Nothing else has to
/// know they exist.
struct ProofSpaceGuard {
    /// The directory the proof and its stage live in; both are on this
    /// filesystem, because the stage is published by rename.
    dir: PathBuf,
    /// Free bytes the proof refuses to eat into. Zero turns the reserve off.
    reserve: u64,
    /// `--sat-proof-cap-bytes`, unset by default.
    cap: Option<u64>,
    interval: u64,
    /// The file length at which the next probe is due.
    next_probe: u64,
    free: fn(&Path) -> Option<u64>,
}

impl ProofSpaceGuard {
    fn for_proof(path: &str) -> Self {
        let switches = ay_core::sat_ab_switches();
        let reserve = switches
            .proof_min_free_bytes
            .unwrap_or(PROOF_FREE_SPACE_RESERVE_BYTES);
        Self {
            dir: Path::new(path).parent().map_or_else(
                || PathBuf::from("."),
                |parent| {
                    if parent.as_os_str().is_empty() {
                        PathBuf::from(".")
                    } else {
                        parent.to_path_buf()
                    }
                },
            ),
            reserve,
            cap: switches.proof_cap_bytes,
            interval: PROOF_FREE_SPACE_PROBE_BYTES.min((reserve / 8).max(1)),
            next_probe: 0,
            free: proof_filesystem_free_bytes,
        }
    }

    /// The stop this write must not cross, if any. `len` is the file's length,
    /// `incoming` the bytes about to be written: the cap is enforced before the
    /// write, so the proof never passes it.
    fn check(&mut self, len: u64, incoming: usize) -> io::Result<()> {
        if let Some(cap) = self.cap {
            if len.saturating_add(incoming as u64) > cap {
                return Err(io::Error::other(format!(
                    "proof reached its {cap}-byte ceiling (--sat-proof-cap-bytes)"
                )));
            }
        }
        if self.reserve == 0 || len < self.next_probe {
            return Ok(());
        }
        self.next_probe = len.saturating_add(self.interval);
        let Some(free) = (self.free)(&self.dir) else {
            return Ok(());
        };
        if free < self.reserve {
            return Err(io::Error::other(format!(
                "{free} bytes free on {}, below the {}-byte proof reserve",
                self.dir.display(),
                self.reserve
            )));
        }
        Ok(())
    }

    /// A look that does not wait for the byte cadence, for the flush the solver
    /// makes at each inprocessing boundary.
    fn probe_now(&mut self, len: u64) -> io::Result<()> {
        self.next_probe = len;
        self.check(len, 0)
    }
}

/// The disk reserve that stops a proof before the filesystem fills
/// (2026-09-20). A stop is a write error, so what these assert is the arithmetic
/// and the cadence; that a write error stops the proof and not the search is
/// the subject of `crates/ay-sat/src/solver/tests/proof_write_failure.rs`.
#[cfg(test)]
mod proof_space_guard_tests {
    use super::*;
    use std::cell::Cell;

    // Per thread, not per process: cargo runs these tests concurrently, and a
    // shared counter would count another test's probes.
    thread_local! {
        static FREE_BYTES: Cell<u64> = const { Cell::new(0) };
        static PROBES: Cell<u64> = const { Cell::new(0) };
    }

    fn set_free(bytes: u64) {
        FREE_BYTES.with(|free| free.set(bytes));
    }

    fn probes() -> u64 {
        PROBES.with(Cell::get)
    }

    fn probed(_dir: &Path) -> Option<u64> {
        PROBES.with(|count| count.set(count.get() + 1));
        Some(FREE_BYTES.with(Cell::get))
    }

    fn unprobeable(_dir: &Path) -> Option<u64> {
        PROBES.with(|count| count.set(count.get() + 1));
        None
    }

    fn guard(reserve: u64, cap: Option<u64>, free: fn(&Path) -> Option<u64>) -> ProofSpaceGuard {
        PROBES.with(|count| count.set(0));
        ProofSpaceGuard {
            dir: PathBuf::from("."),
            reserve,
            cap,
            interval: PROOF_FREE_SPACE_PROBE_BYTES.min((reserve / 8).max(1)),
            next_probe: 0,
            free,
        }
    }

    #[test]
    fn the_reserve_stops_the_proof_while_the_disk_still_has_room() {
        set_free(1_900_000_000);
        let mut guard = guard(2 * 1024 * 1024 * 1024, None, probed);
        let error = guard
            .check(0, 4096)
            .expect_err("a filesystem under the reserve stops the proof");
        let message = error.to_string();
        assert!(
            message.contains("1900000000 bytes free") && message.contains("proof reserve"),
            "the stop says what it measured and what it wanted: {message}"
        );
    }

    #[test]
    fn a_filesystem_above_the_reserve_writes_on() {
        set_free(8 * 1024 * 1024 * 1024);
        let mut guard = guard(2 * 1024 * 1024 * 1024, None, probed);
        guard.check(0, 4096).expect("room to write");
        assert_eq!(probes(), 1, "the first write probes");
    }

    #[test]
    fn the_probe_keeps_the_byte_cadence() {
        set_free(8 * 1024 * 1024 * 1024);
        // An 8 MiB reserve clamps the interval to 1 MiB, so four megabytes of
        // proof are four probes, not four thousand.
        let mut guard = guard(8 * 1024 * 1024, None, probed);
        assert_eq!(guard.interval, 1024 * 1024);
        let mut len = 0u64;
        for _ in 0..4096 {
            guard.check(len, 1024).expect("room to write");
            len += 1024;
        }
        assert_eq!(probes(), 4, "one probe per interval of bytes written");
    }

    #[test]
    fn a_flush_probes_without_waiting_for_the_cadence() {
        set_free(8 * 1024 * 1024 * 1024);
        let mut guard = guard(8 * 1024 * 1024, None, probed);
        guard.check(0, 1024).expect("room to write");
        guard.check(1024, 1024).expect("inside the interval");
        assert_eq!(probes(), 1, "the cadence held");
        guard.probe_now(1024).expect("room to write");
        assert_eq!(probes(), 2, "the inprocessing boundary looks anyway");
    }

    #[test]
    fn an_unprobeable_filesystem_never_stops_the_proof() {
        let mut guard = guard(2 * 1024 * 1024 * 1024, None, unprobeable);
        guard
            .check(0, 4096)
            .expect("an unanswerable statvfs is not a stop");
        assert_eq!(probes(), 1, "it did ask");
    }

    #[test]
    fn a_reserve_of_zero_never_probes() {
        let mut guard = guard(0, None, probed);
        for len in 0..16 {
            guard.check(len * 4096, 4096).expect("no reserve, no stop");
        }
        assert_eq!(probes(), 0, "nothing to ask about");
    }

    #[test]
    fn the_optional_ceiling_stops_the_proof_at_its_size() {
        set_free(8 * 1024 * 1024 * 1024);
        let mut guard = guard(2 * 1024 * 1024 * 1024, Some(4096), probed);
        guard
            .check(0, 4096)
            .expect("the ceiling is not yet reached");
        let error = guard
            .check(4096, 1)
            .expect_err("one byte past the ceiling stops the proof");
        assert!(
            error.to_string().contains("4096-byte ceiling"),
            "the stop names the ceiling: {error}"
        );
    }

    #[test]
    fn the_default_guard_reads_the_proof_directory_and_the_default_reserve() {
        let guard = ProofSpaceGuard::for_proof("/tmp/some-run/proof.out");
        assert_eq!(guard.dir, PathBuf::from("/tmp/some-run"));
        assert_eq!(guard.reserve, PROOF_FREE_SPACE_RESERVE_BYTES);
        assert_eq!(guard.cap, None, "no size ceiling by default");
        assert_eq!(guard.interval, PROOF_FREE_SPACE_PROBE_BYTES);
        let bare = ProofSpaceGuard::for_proof("proof.out");
        assert_eq!(
            bare.dir,
            PathBuf::from("."),
            "a bare name is this directory"
        );
    }
}
