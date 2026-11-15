// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Private test data and heuristic-state preservation; no solver authority,
//! resource grant, work refund, or proof permission is created here.

/// A finite Frobenius family: shifted reads lie in {0, k+1, k+2}, but
/// their target k*k+k-1 is not a nonnegative combination of k+1 and k+2.
/// Modulo k+1, the number of k+2 summands would be at least k, already
/// exceeding the target. These are logically UNSAT independent of search.
pub(crate) fn frobenius_script(k: i64) -> String {
    frobenius_script_for_reads(k, k + 2)
}

/// The two large-family inputs with completed pinned-reference UNSAT evidence.
/// This is a bounded test-data search, not an accepting solver permission.
pub(crate) const OUTER_COUNT_MEMBERS: [i64; 2] = [8, 10];

/// A separate, fixed two-member cost premise for the large outer counts.
/// Keep the same impossible shifted target while adding reads, rather than
/// holding the original sum fixed (which can make the formula satisfiable).
/// Whether a member exhausts a count is still established by the raw probe.
pub(crate) fn outer_count_frobenius_script(k: i64) -> String {
    assert!(OUTER_COUNT_MEMBERS.contains(&k));
    frobenius_script_for_reads(k, 2 * k + 2)
}

fn frobenius_script_for_reads(k: i64, read_count: i64) -> String {
    assert!((2..=12).contains(&k));
    assert!((k + 2..=2 * k + 2).contains(&read_count));
    let mut script = String::from("(set-logic QF_AUFLIA)\n(declare-fun a () (Array Int Int))\n");
    let reads: Vec<String> = (0..read_count)
        .map(|i| format!("(select a i{i})"))
        .collect();
    for (i, read) in reads.iter().enumerate() {
        script += &format!(
            "(declare-const i{i} Int)\n\
             (assert (or (< {read} 0) (> {read} {})))\n\
             (assert (and (<= (- 1) {read}) (<= {read} {})))\n",
            k - 1,
            k + 1,
        );
    }
    let shifted_target = k * k + k - 1;
    script += &format!(
        "(assert (= (+ {}) {}))\n",
        reads.join(" "),
        shifted_target - read_count,
    );
    script
}

pub(crate) struct PreservedProbeState(Option<ay_lia::ProbeStateSnapshot>);

pub(crate) fn preserve_lia_probe_state() -> PreservedProbeState {
    PreservedProbeState(Some(ay_lia::save_probe_state()))
}

impl Drop for PreservedProbeState {
    fn drop(&mut self) {
        if let Some(saved) = self.0.take() {
            ay_lia::restore_probe_state(saved);
        }
    }
}
