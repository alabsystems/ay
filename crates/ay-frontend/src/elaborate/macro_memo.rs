// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Use-site memo for `define-fun` macro expansion.
//!
//! A `define-fun` is a macro with call-by-value substitution of its formals, and
//! AY inlines it by elaborating the callee's PARSE TREE at every call site
//! (`elaborate/app/mod.rs` for an applied definition, `elaborate/term.rs` for a
//! nullary one). Nothing shared the result, so a chain of definitions each
//! naming the previous one cost exponentially in the chain length even though
//! the hash-consed term it builds stays linear: a 30-line Fibonacci-shaped chain
//! of unary `define-fun`s with no datatypes and no arithmetic already burned a
//! 20 s deadline. This module elaborates each `(callee, argument terms)` pair
//! once and shares the interned result.
//!
//! # Why a use-site memo is sound here
//!
//! The expansion sites already elaborate a body in a FRESH environment binding
//! exactly the formals to exactly the elaborated arguments — never the use-site
//! environment, which would capture. So the body's elaboration is a function of
//! `(callee, argument terms)` alone, which is precisely the memo key; a caller's
//! `let`, quantifier or `match` binder cannot reach the body and therefore
//! cannot reach the key. Four further conditions make a replay indistinguishable
//! from a fresh walk:
//!
//! 1. **Environment freshness.** Every entry is dropped by
//!    [`Context::advance_source_revision`], the funnel that every declaration,
//!    definition, macro adoption, `push`/`pop`, `set-logic` and reset passes
//!    through, and an expansion that STRADDLED such a change is not recorded at
//!    all. No entry can outlive a change to what its body's free symbols
//!    resolve to. The single exception is
//!    [`Context::advance_source_revision_introducing`], which keeps the memo
//!    across a `define-fun` binding a name that no memoized expansion has ever
//!    resolved — see its own contract.
//! 2. **Errors are never cached.** Only a successful expansion is recorded, so a
//!    malformed body keeps raising its diagnostic at every call site.
//! 3. **Purity.** An expansion that minted a fresh variable is not recorded. A
//!    quantifier or lambda binder, `pow_neg_at_zero`, and `map.empty`'s default
//!    are all minted per occurrence; sharing one across call sites would equate
//!    values the un-memoized elaboration leaves independent.
//! 4. **Depth.** An entry records how deep BELOW itself its expansion reached,
//!    and is served only where every skipped nested expansion would still have
//!    cleared [`MAX_FUN_EXPANSION_DEPTH`] — so a replay can never stand in for a
//!    `RecursionDepthExceeded`. That reach is measured from the expanding
//!    site's own depth base, which differs between the two sites, so the key
//!    carries a [`super::MacroCallSite`] and entries never cross.
//!
//! Measured: over a linear chain of `n` definitions the first refusal lands at
//! exactly the same `n`, with the same refusal count and the same canonical
//! elaborated dump, memoized or not.

use ay_core::TermId;

use super::term::collect_term_names;
use super::{Context, MacroExpansion, MacroExpansionKey, ParsedTerm, MAX_FUN_EXPANSION_DEPTH};

/// Scope around one macro-body elaboration.
///
/// Open it after the memo misses and before the body is walked; closing it
/// records the entry (when it is replayable) and restores the enclosing
/// expansion's depth watermark.
pub(super) struct MacroExpansionWatermark {
    /// `Context::fun_expansion_depth` as the memoized call was entered.
    entry_depth: usize,
    /// The watermark of the enclosing expansion, parked for the duration.
    outer_watermark: usize,
    /// Variable counter before the body was walked, for the purity test.
    vars_before: u32,
    /// Source revision before the body was walked, for the freshness test.
    revision_before: u64,
}

impl MacroExpansionWatermark {
    pub(super) fn open(context: &mut Context, entry_depth: usize, body: &ParsedTerm) -> Self {
        // Over-approximate the names this expansion can resolve, so a later
        // `define-fun` that takes one of those spellings away from a builtin is
        // seen. Recorded for EVERY body walked under a live memo, not only the
        // ones that end up recorded, so the set covers nested expansions too.
        //
        // `collect_term_names` does not report the HEAD of an indexed
        // application (`extract` in `(_ extract 3 0)`), and does not need to:
        // `elaborate/indexed.rs` dispatches those spellings structurally and
        // never consults `fun_defs` for them, so a later definition of one
        // cannot change an expansion. The function symbol an index NAMES
        // (`(_ map f)`, `(_ as-array f)`) is consulted, but that site mints a
        // fresh array index — condition 3 already refuses to record it.
        collect_term_names(body, &mut context.macro_expansion_memo_names);
        let outer_watermark =
            std::mem::replace(&mut context.fun_expansion_depth_watermark, entry_depth);
        Self {
            entry_depth,
            outer_watermark,
            vars_before: context.terms.var_counter(),
            revision_before: context.source_revision,
        }
    }

    /// Close the scope. `term` is the expansion's result, or `None` when it
    /// failed — a failure is deliberately not recorded.
    pub(super) fn close(self, context: &mut Context, key: MacroExpansionKey, term: Option<TermId>) {
        let reached = context.fun_expansion_depth_watermark;
        // The enclosing expansion reached at least as deep as this one did.
        context.fun_expansion_depth_watermark = self.outer_watermark.max(reached);
        let Some(term) = term else {
            return;
        };
        if context.terms.var_counter() != self.vars_before {
            // Condition 3: this body mints a fresh variable per occurrence.
            return;
        }
        if context.source_revision != self.revision_before {
            // Condition 1: something registered a symbol mid-walk (a lazy
            // parametric-datatype instance, a `map.dom` carrier), so part of
            // this result was resolved against an environment that no longer
            // exists. Re-derive it next time.
            return;
        }
        context.macro_expansion_memo.insert(
            key,
            MacroExpansion {
                term,
                relative_depth: reached.saturating_sub(self.entry_depth),
            },
        );
    }
}

impl Context {
    /// The memoized expansion of `key`, when replaying it here is
    /// indistinguishable from walking the body again.
    pub(super) fn memoized_macro_expansion(
        &mut self,
        key: &MacroExpansionKey,
        entry_depth: usize,
    ) -> Option<TermId> {
        let hit = *self.macro_expansion_memo.get(key)?;
        // Condition 4: the deepest nested expansion this replay skips would sit
        // here. Serving the entry past the guard would turn the
        // `RecursionDepthExceeded` the un-memoized walk raises into a success.
        let deepest = entry_depth.checked_add(hit.relative_depth)?;
        if deepest >= MAX_FUN_EXPANSION_DEPTH {
            return None;
        }
        self.fun_expansion_depth_watermark = self.fun_expansion_depth_watermark.max(deepest);
        Some(hit.term)
    }
}
