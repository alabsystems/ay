// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Checked source retention for native assertions.

use ay_frontend::Command;

use crate::api::{Solver, SolverError, Term};

impl Solver {
    /// Assert a native term while retaining its submitted SMT-LIB assertion.
    ///
    /// The input must contain exactly one `(assert ...)` command. Its expression
    /// must elaborate in this solver to the exact same canonical term. Source
    /// text is never trusted as a replacement for the native assertion. A
    /// mismatch, parse failure, foreign term, or source over 8 MiB is rejected
    /// before changing the assertion stack. Term interning may still occur.
    ///
    /// WHAT THE COMPARISON IS. The guard compares the BUILT assertion — one
    /// canonical `TermId` — against the `TermId` the source elaborates to. It
    /// is an identity check on the elaborated term, NOT a syntactic check on
    /// the text and NOT a check of the text's provenance.
    ///
    /// Elaboration folds. `(pred (succ l))` is `l`, `((_ is succ) (succ l))`
    /// is `true`, `((_ is C) x)` for a sole-constructor datatype is `true`,
    /// `(= (succ a) (succ b))` is `(= a b)`. Where a spelling folds all the
    /// way to a CONSTANT, every other spelling that folds to the same constant
    /// is by construction the same `TermId`, so this guard accepts it: a
    /// natively built `((_ is succ) (succ l))` is retained just as willingly
    /// with the source `(assert true)` as with its own spelling. This is
    /// deliberate and is not a hole in the guard — folding is what makes the
    /// native builders and the surface elaborator agree in the first place —
    /// but it bounds what retention certifies:
    ///
    /// * CERTIFIED: the retained text, re-parsed and re-elaborated in THIS
    ///   solver against THIS declaration context, denotes exactly the formula
    ///   that entered the assertion stack. Nothing weaker than the assertion
    ///   can be smuggled in under a stronger-looking spelling, or the reverse:
    ///   a source denoting any other formula is refused outright.
    /// * NOT CERTIFIED: that the text is the one the caller originally
    ///   authored, that it is the most informative spelling of the term, or
    ///   that it shares any subterm structure with how the term was built.
    ///   For a term that folds to a constant it carries no structure at all.
    ///
    /// Consumers that need authored provenance — a proof document that must
    /// read the way the query wrote it — get it from the retained source being
    /// the caller's own text, not from this check. Downstream soundness never
    /// rests on the spelling: the strict proof checker validates the CANONICAL
    /// term, and an unprintable spelling is withheld rather than trusted (see
    /// `Solver::export_last_unsat_artifact`).
    pub fn try_assert_term_with_source(
        &mut self,
        term: Term,
        assertion: &str,
    ) -> Result<(), SolverError> {
        let invalid = |message: &str| SolverError::InvalidArgument {
            operation: "assert_term_with_source",
            message: message.to_string(),
        };
        let term_id = self.resolve_term("assert_term_with_source", term)?;
        if assertion.len() > 8 * 1024 * 1024 {
            return Err(invalid("assertion source exceeds 8 MiB"));
        }
        let mut commands = ay_frontend::parse(assertion)
            .map_err(|error| invalid(&format!("invalid assertion source: {error}")))?;
        if commands.len() != 1 {
            return Err(invalid("source must contain exactly one assertion"));
        }
        let Some(Command::Assert(source)) = commands.pop() else {
            return Err(invalid("source must contain exactly one assertion"));
        };
        // Identity of the ELABORATED terms, not of the text: see the
        // provenance bounds on this method's contract. A source that folds to
        // the same canonical term IS the same assertion, whatever it looks
        // like; anything else is refused before the stack moves.
        let reconstructed = self
            .executor
            .context_mut_internal()
            .elaborate_surface_subterm(&source);
        if reconstructed != Some(term_id) {
            return Err(invalid("source does not reconstruct the native assertion"));
        }
        self.assert_native_term(term, source)
    }
}
