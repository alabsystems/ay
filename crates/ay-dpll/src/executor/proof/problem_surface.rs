// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The external-recheck surface of a whole certificate: problem AND proof.

use ay_core::kani_compat::DetHashMap;
use ay_core::{Proof, TermId};
use ay_frontend::Context;

use super::super::Executor;

mod authored_source;
pub(crate) use authored_source::AuthoredProblemSurface;

impl Executor {
    /// The proof's surface ([`ay_proof::carcara_proof_surface`]) joined with
    /// the problem's own declarations and its authored spelling.
    ///
    /// The certificate an external checker receives is the problem together
    /// with the proof, and the checker parses every declaration of the problem
    /// whether or not the proof mentions it. A proof whose document is
    /// supported therefore still has an unsupported certificate when the
    /// problem declares a symbol the pinned checker cannot read — see
    /// [`ay_proof::carcara_declaration_gap`]. The proof's own gap, when it has
    /// one, is kept: it is the one a reader of the document can act on. The
    /// declarations read AY's elaborated signature, so a construct the author
    /// wrote and AY elaborated away (`(as mkVec Vec)`, `is-C`, an implicit
    /// Int/Real coercion) is judged on the authored commands themselves
    /// ([`AuthoredProblemSurface`]).
    ///
    /// Every surface reader goes through here: the strict gates' parse
    /// verdict (`strict_gate_carcara_surface`, which the CLI's streamed
    /// export `try_export_last_proof_alethe_for_problem_scope_to_with_carcara_surface`
    /// folds its render's report into), the artifact disclosure
    /// (`carcara_surface_for_last_export`) and the paired problem-scoped
    /// export (`try_export_last_proof_alethe_for_problem_scope_with_carcara_surface`,
    /// which `last_unsat_proof_carcara_surface` reads).
    pub(crate) fn problem_and_proof_surface(
        &self,
        proof: &Proof,
        overrides: Option<&DetHashMap<TermId, String>>,
    ) -> ay_proof::CarcaraSurface {
        let surface = ay_proof::carcara_proof_surface(proof, &self.ctx.terms, overrides);
        if !surface.is_supported() {
            return surface;
        }
        // The smallest gap, so the disclosed reason does not depend on the
        // symbol table's iteration order.
        let gap = self
            .ctx
            .symbol_iter()
            .filter(|(name, _)| !self.ctx.is_internal_symbol(name))
            .filter_map(|(name, info)| {
                ay_proof::carcara_declaration_gap(name, &info.arg_sorts, &info.sort)
            })
            .min();
        match gap.or_else(|| self.authored_problem_surface.gap().map(str::to_string)) {
            Some(reason) => ay_proof::CarcaraSurface::Unsupported { reason },
            None => surface,
        }
    }

    /// Whether pinned Carcara reads the authored problem's numerals as
    /// `Real`s (a logic with reals and no integers, such as `QF_LRA`), while
    /// its proof parser reads a numeral in the certificate as an `Int`. See
    /// [`crate::executor::premise_int_let_binding`].
    #[must_use]
    pub fn authored_numerals_read_as_reals(&self) -> bool {
        self.authored_problem_surface.reads_numerals_as_reals()
    }

    /// Judge the exact source text of one authored command, which the CLI
    /// hands over just before it executes the parsed command. Pinned
    /// Carcara's lexer reads every command, and AY's command parser reads
    /// `assert-not`, the legacy `(declare-datatypes () ...)` and a bare-symbol
    /// constructor like standard spellings, which pinned Carcara does not
    /// parse, and `define-const`, which it skips. See [`AuthoredProblemSurface`].
    pub fn observe_authored_command_source(&mut self, source: &str) {
        self.authored_problem_surface.observe_source_text(source);
    }

    /// Judge the text of an authored command AY could not parse and dropped:
    /// pinned Carcara still tokenizes it with the rest of the file.
    pub fn observe_authored_dropped_source(&mut self, source: &str) {
        self.authored_problem_surface.observe_dropped_text(source);
    }

    /// Judge the rest of the authored file, `remainder` (from a query command
    /// on), before that query runs. Carcara parses the whole file, so a
    /// construct after the query that decides a verdict still stops the parse
    /// of that verdict's certificate; only a caller holding the whole file (the
    /// CLI's file mode) can read ahead. Reads it once, and only when this
    /// session can read a certificate surface at all (proofs retained, or a
    /// claiming `--self-check` / `:check-proofs-strict` consumer): the caller
    /// passes each query's remainder, and the first that qualifies is read.
    pub fn observe_authored_commands_ahead(&mut self, remainder: &str) {
        if self.is_producing_proofs() || self.self_check() || self.strict_proofs_enabled() {
            self.authored_problem_surface.look_ahead(remainder);
        }
    }

    /// `(reset)` rebuilds the whole executor, but Carcara reads the whole
    /// authored file, a `(reset)` included, so an authored reset keeps the
    /// authored surface. A library caller's `(reset)` starts a fresh problem.
    pub(in crate::executor) fn reset_keeping_authored_surface(
        &mut self,
        ctx: Context,
        authored: bool,
    ) {
        let surface = std::mem::take(&mut self.authored_problem_surface);
        self.reset_to_fresh_session(ctx);
        if authored {
            self.authored_problem_surface = surface;
        }
    }
}
