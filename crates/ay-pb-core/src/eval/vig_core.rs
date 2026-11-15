// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

// Contract-carrying fragment of `eval.rs`, `include!`d into module `eval` — so
// `verify_all_constraints` keeps its module, its `crate::` re-export and its doc
// links, and only the ONE file a stock compiler cannot read is swapped.
//
// It is a separate file because a native Trust clause is RAW GRAMMAR: cfg-stripping
// runs after parsing, so no `cfg` can hide one and a compiler without the extension
// rejects the WHOLE FILE it appears in. `vig_core_stock.rs` is this fragment minus
// the clause; `eval.rs` selects between them on `cfg(deductive_verify)`.

/// Verify that all constraints in an instance are satisfied.
///
/// This is the incumbent gate used to re-check candidate models against the
/// original constraints. [`eval_constraint`] uses an exact big-integer fallback
/// for sums outside `i128`, so extreme coefficients cannot wrap or panic here.
///
/// # The postcondition, and what the verifier does with it
///
/// The postcondition is spelled in the native clause grammar, which the default
/// (`channel = "trust"`) toolchain parses without any `--extern trust` overlay.
/// MEASURED 2026-08-30 on the sealed toolchain (rustc 1.99.0-dev, 1979a7b85): it
/// PARSES but does not LOWER — the verifier answers `unsupported contract
/// predicate expression`, twice, and the clause lands in UNKNOWN. That is the
/// same verdict the attribute form earned; the bounded quantifier is outside the
/// lowerable fragment either way. It is kept, rather than deleted, because an
/// UNKNOWN row naming a real obligation is the honest census entry, and because
/// `unsupported` is a frontend gap that will close — a deleted clause would not
/// come back when it does. It is not ASSUMED, so nothing downstream relies on it.
pub fn verify_all_constraints(constraints: &[PbConstraint], assignment: &[bool]) -> bool
    ensures result == forall|i: usize| (i < constraints.len()) ==> eval_constraint(&constraints[i], assignment)
{
    constraints.iter().all(|c| eval_constraint(c, assignment))
}
