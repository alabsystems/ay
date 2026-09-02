// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The independent SAT gate's pure decision core, alone in a file.
//!
//! It is alone because of its `ensures` clause. Native Trust contract clauses are
//! RAW GRAMMAR: cfg-stripping runs after parsing, so no `cfg` can hide one, and a
//! compiler without the extension rejects the WHOLE FILE it appears in. Keeping
//! this three-line function inside the 11k-line `independent_gate.rs` therefore
//! made that file unreadable to stock rustc — and `model-checker-consumer`'s Kani lane, a
//! `rustc_private` driver frozen on `nightly-2025-12-03`, links this crate.
//!
//! `gate_decision_stock.rs` is the same decision without the clause, and
//! `mod.rs` selects between the two on `cfg(deductive_verify)`. The two are pinned to
//! each other, and to the proof fixture, by `tests/smt_model_gate_conformance.rs`.

/// Pure, contract-carrying decision core of the independent SAT gate — the SMT
/// twin of the SAT-side Verified-SAT-Gate (`decision_sat_self_checked` in
/// `crates/ay/src/cmd_pb.rs`, proven in `decision_sat_vig_realbody.rs`).
///
/// DIRECTIONAL SOUNDNESS: the gate keeps a `Sat` verdict (`true`) EXACTLY when the
/// incoming verdict was `Sat` AND the model was independently `confirmed`, OR
/// the generic proof model supplies `enforce = false`. Every live unconfirmed
/// publication call site supplies `enforce = true`; `CannotConfirm` bypasses
/// this helper only to downgrade directly (see
/// `Executor::apply_independent_model_gate`). Consequences, both
/// machine-checkable: it can NEVER manufacture `Sat` from a non-`Sat` verdict
/// (`result ==> was_sat`), and once enforcement is on it NEVER keeps an
/// unconfirmed model (`result && enforce ==> confirmed`). The gate only ever maps
/// `Sat -> {Sat, Unknown}`, never toward unsoundness.
///
/// The postcondition is a native `ensures` clause, which the default
/// (Trust) toolchain parses unconditionally: no `cfg` gate, no
/// `trust` dependency, and no `--extern trust` overlay. It replaced a
/// `` attribute that was inert
/// outside the ratchet lane and, once verification became the default, a hard
/// E0433 inside it. Same predicate, same codegen (a contract clause is not a
/// runtime check here); the P1 soundness proof and its refuted `no_check`
/// control still live in the development proof harness.
pub(super) fn gate_keeps_sat(was_sat: bool, confirmed: bool, enforce: bool) -> bool
    ensures result == (was_sat && (confirmed || !enforce))
{
    was_sat && (confirmed || !enforce)
}
