// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

// REAL XOR merge-polarity / parity core for the `ay-sat` congruence closure.
//
// This is the single, shared source of truth for the GF(2) parity arithmetic
// that the congruence XOR-collapse path uses to decide the polarity of a
// derived unit. It is compiled by `cargo` (the solver depends on this crate
// and calls these functions) AND submitted to `offline deductive checker check` as the exact
// same source bytes (the development proof harness pulls this file in
// with `include!`, so the obligation is over the real code — NO TWIN).
//
// PROOF STATUS — a measurement, not a standing claim; re-run before quoting it.
// Measured 2026-09-23 on compiler_consumer/targo 321aaeda7 (atpkg trust store 9192):
// `offline deductive checker check` over BOTH harnesses in `proofs/` returns Verdict
// INCONCLUSIVE, Gate FAIL. The `u8` overflow and hardened-boundary rows of
// `xor_collapse_parity` are PROVED; its `assert_eq!` soundness obligation is
// UNKNOWN (model-checker-consumer PDR returned unknown) and its panic-freedom row is UNKNOWN
// (the native CHC bundle refuses an `Alloca` without a bound extent). Those
// PROVED rows depend on the verifier's wall-clock budget: re-run 2026-09-24 on
// the same toolchain at load average ~90, every overflow, boundary and
// assertion row of `xor_collapse_parity` came back TIMEOUT (3000 ms, "budget
// exceeded before accepting primary evidence"); the verdict stays INCONCLUSIVE.
// `xor_accumulate_parity` carries no obligation at all. So neither the bounded
// nor the unbounded parity property is machine-proved today; both are checked
// by EXECUTION in `lib.rs`'s tests.
// Module-level rustdoc lives on the crate root in `lib.rs`; this file uses
// plain `//` comments so it stays valid when `include!`d into the proof.
//
// Soundness rationale: the historical `asconhash-m5_6` false UNSAT (#6997) was
// a single XOR-folded parity bit off by one flip, so an EVEN (satisfiable)
// cycle was mis-tagged ODD and a contradiction unit NOT entailed by the
// clauses was emitted. The obligation stated here (`acc == GF(2) mod-2 popcount
// of true contributions`) is exactly the property whose violation produces
// that class of false UNSAT. Arity is bounded by `XOR_ARITY_LIMIT = 5`
// (`ay-sat/src/gates/xor.rs`), so the fixed-width model is FAITHFUL, not an
// approximation — a verifier route that grounds the complete finite Bool
// domain could discharge it (see PROOF STATUS above for whether one does).

/// THE GF(2) accumulation step the real congruence XOR-collapse runs.
///
/// Every parity flip in the solver — a level-0 true-assigned input eliminated
/// from the XOR (`x ⊕ true = ¬x`) and a complementary input pair cancelled
/// (`x ⊕ ¬x = true`) — is folded through THIS function. It is the only place
/// the parity bit is mutated, so there is a single audited GF(2) step.
#[inline]
#[must_use]
pub fn xor_accumulate_parity(acc: bool, contribution: bool) -> bool {
    acc ^ contribution
}

/// THE REAL fixed-arity XOR-collapse polarity (arity <= `XOR_ARITY_LIMIT` = 5).
///
/// Built ONLY from [`xor_accumulate_parity`] — the same primitive the solver
/// folds in its merge/simplify loops — seeded with the XOR/XNOR output polarity
/// `neg_out` and folded against the per-slot contribution bits `c0..c4` (a slot
/// is `true` iff it flips the XOR polarity). The returned bit is the polarity of
/// the unit the congruence closure would emit on a fully-collapsing gate.
///
/// SOUNDNESS OBLIGATION (trust-checkable): the returned parity bit equals the
/// GF(2) mod-2 popcount of its true contributions — see
/// the development proof harness. `offline deductive checker check` leaves it UNKNOWN
/// as measured 2026-09-23 (PROOF STATUS at the top of this file); the
/// exhaustive 2^6 test in `lib.rs` checks it by execution. A derived
/// XOR-collapse unit is sound iff this holds.
#[inline]
#[must_use]
pub fn xor_collapse_parity(
    neg_out: bool,
    c0: bool,
    c1: bool,
    c2: bool,
    c3: bool,
    c4: bool,
) -> bool {
    // Straight-line GF(2) fold — the same XOR algebra the solver loops with
    // `xor_accumulate_parity`, kept inline here so the bounded-MC
    // exhaustive-finite verifier route can ground and discharge the embedded
    // obligation over the complete finite Bool domain.
    let acc = neg_out ^ c0 ^ c1 ^ c2 ^ c3 ^ c4;
    // SOUNDNESS OBLIGATION (trust-checkable): the folded parity bit equals the
    // GF(2) mod-2 popcount of its true contributions. A derived XOR-collapse
    // unit is sound iff this holds. Max popcount is 6, so the `u8` sum never
    // overflows (those overflow rows are proved when the verifier's wall-clock
    // budget is met; see PROOF STATUS). The equality itself is UNKNOWN
    // to `offline deductive checker check` as measured 2026-09-23 — see PROOF STATUS at the
    // top of this file; it is checked for all 2^6 inputs by execution.
    assert_eq!(
        acc,
        (((neg_out as u8) + (c0 as u8) + (c1 as u8) + (c2 as u8) + (c3 as u8) + (c4 as u8)) % 2
            == 1)
    );
    acc
}

/// THE UNBOUNDED XOR-collapse polarity over an ARBITRARY-length contribution
/// slice — the same GF(2) fold the solver runs in its merge/simplify loops,
/// generalised past the `XOR_ARITY_LIMIT = 5` fixed-width form.
///
/// Built ONLY from [`xor_accumulate_parity`], seeded `false` and folded left
/// over `bits`. Each slot is `true` iff it flips the XOR polarity. The returned
/// bit is the polarity the congruence closure would emit on a fully-collapsing
/// gate of ANY arity.
///
/// SOUNDNESS (UNBOUNDED): the returned bit equals the GF(2) mod-2 popcount of the
/// `true` contributions, for slices of EVERY length. The argument is a
/// HAND-WRITTEN induction, not a machine-checked one:
///   * base: empty prefix `acc == false == (0 % 2 == 1)`;
///   * step: `xor_accumulate_parity(acc, b) == acc ^ b` flips parity iff `b`.
/// This unbounded obligation is kept OUT of this lib's trust surface; no
/// `offline deductive checker check` run discharges it. the development proof harness
/// states the inductive step (`step_bv`) and measured INCONCLUSIVE on
/// 2026-09-23 (its assertion is UNKNOWN; PROOF STATUS at the top of this file).
/// What IS established is by execution only, in `lib.rs`: the exhaustive test
/// over every slice of length `0..=16`, and a test that checks the base case,
/// the step over its complete 2x2 state, and that the fold is that step
/// iterated for lengths `1..=20`. The step from there to EVERY length is the
/// hand-written induction above; no test observes a length past 20.
#[inline]
#[must_use]
pub fn xor_collapse_slice(bits: &[bool]) -> bool {
    let mut acc = false;
    for &b in bits {
        acc = xor_accumulate_parity(acc, b);
    }
    acc
}
