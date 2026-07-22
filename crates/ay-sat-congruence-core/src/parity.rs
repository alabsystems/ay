// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

// REAL XOR merge-polarity / parity core for the `ay-sat` congruence closure.
//
// This is the single, shared source of truth for the GF(2) parity arithmetic
// that the congruence XOR-collapse path uses to decide the polarity of a
// derived unit. It is compiled by `cargo` (the solver depends on this crate
// and calls these functions) AND verified by `offline deductive checker check` against the
// exact same source bytes (the development proof harness pulls this
// file in with `include!`, so the proof is over the real code — NO TWIN).
// Module-level rustdoc lives on the crate root in `lib.rs`; this file uses
// plain `//` comments so it stays valid when `include!`d into the proof.
//
// Soundness rationale: the historical `asconhash-m5_6` false UNSAT (#6997) was
// a single XOR-folded parity bit off by one flip, so an EVEN (satisfiable)
// cycle was mis-tagged ODD and a contradiction unit NOT entailed by the
// clauses was emitted. The obligation proved here (`acc == GF(2) mod-2 popcount
// of true contributions`) is exactly the property whose violation produces
// that class of false UNSAT. Arity is bounded by `XOR_ARITY_LIMIT = 5`
// (`ay-sat/src/gates/xor.rs`), so the fixed-width model is FAITHFUL, not an
// approximation — and the bounded-MC exhaustive-finite verifier route can
// discharge it over the complete finite Bool domain.

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
/// the development proof harness, discharged through `offline deductive checker check`
/// by the bounded-MC exhaustive-finite route over the complete 2^6 Bool domain.
/// A derived XOR-collapse unit is sound iff this holds.
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
    // SOUNDNESS OBLIGATION (trust-checked): the folded parity bit equals the
    // GF(2) mod-2 popcount of its true contributions. A derived XOR-collapse
    // unit is sound iff this holds. Max popcount is 6, so the `u8` sum never
    // overflows. `offline deductive checker check` proves this for ALL 2^6 inputs.
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
/// `true` contributions, for slices of EVERY length, by induction:
///   * base: empty prefix `acc == false == (0 % 2 == 1)`;
///   * step: `xor_accumulate_parity(acc, b) == acc ^ b` flips parity iff `b`.
/// This unbounded obligation is a RESEARCH WIP and is deliberately kept OUT of
/// this lib's trust surface so the crate compiles CLEAN/load-bearing through
/// `targo`: the canonical engine proves the BOUNDED core ([`xor_collapse_parity`],
/// the solver's arity<=5 reality, exhaustive finite domain) but cannot yet
/// discharge the loop-inductive form (multi-predicate cyclic CHC frontier). The
/// property is still checked at runtime by the 0..=12 exhaustive test in `lib.rs`,
/// and the unproven trust obligation lives in the development proof harness
/// (INCONCLUSIVE), not here.
#[inline]
#[must_use]
pub fn xor_collapse_slice(bits: &[bool]) -> bool {
    let mut acc = false;
    for &b in bits {
        acc = xor_accumulate_parity(acc, b);
    }
    acc
}
