// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

#[cfg(test)]
mod tests;

impl AlethePrinter<'_> {
    /// Format a term as an SMT-LIB expression
    pub(crate) fn format_term(&self, term_id: TermId) -> String {
        let mut out = String::new();
        self.write_term_into(&mut out, term_id);
        out
    }

    /// Append the rendering of `term_id` to `out`.
    ///
    /// Same semantics (including #A2b work-budget charging) as
    /// [`Self::format_term`], but a cache hit copies the cached bytes
    /// straight into the caller's buffer instead of allocating an owned
    /// clone first (#proof-tax).
    pub(super) fn write_term_into(&self, out: &mut String, term_id: TermId) {
        // #A2b: once the emission work budget is exhausted the whole
        // document is guaranteed to be DISCARDED (the export loop returns
        // `EmissionBudgetExhausted` at the next step boundary — `work` never
        // decreases), so cut the recursion short instead of grinding through
        // gigabytes of string building for output nobody will see. The
        // placeholder never reaches disk.
        if self.work_budget_exhausted() {
            out.push_str("@a2b_emission_budget_exhausted");
            return;
        }
        if let Some(term_str) = self.skolem_overrides.borrow().get(&term_id).cloned() {
            self.charge(term_str.len() as u64);
            out.push_str(&term_str);
            return;
        }
        // A `let`-bridged assertion prints as its eliminated form from the
        // bridge step onwards; the surface `(let ...)` spelling survives only
        // inside the bridge itself (the `assume` and the equivalence it
        // discharges), which embeds it literally.
        if let Some(term_str) = self.let_bridge_renderings.borrow().get(&term_id).cloned() {
            self.charge(term_str.len() as u64);
            out.push_str(&term_str);
            return;
        }
        // An authored override whose `Assume` rows are all unused belongs only
        // at those leaves. Every other occurrence must expose the canonical
        // term, including steps printed before the unused assume itself.
        if !self.assume_only_override_terms.borrow().contains(&term_id) {
            if let Some(term_str) = self
                .term_overrides
                .and_then(|overrides| overrides.get(&term_id))
            {
                self.charge(term_str.len() as u64);
                out.push_str(term_str);
                return;
            }
        }
        if let Some(cached) = self.format_cache.borrow().get(&term_id) {
            // A cache hit still copies the rendered bytes; on proofs whose
            // steps repeat megabyte literals that copy IS the dominant cost,
            // so it is charged against the emission work budget (#A2b).
            self.charge(cached.len() as u64);
            out.push_str(cached);
            return;
        }
        let term = self.terms.get(term_id);
        let formatted = if let Some(formatted) = self.format_const_array(term_id, term) {
            formatted
        } else if let TermData::App(symbol, args) = term {
            // Stream applications into the final buffer. Materializing and
            // caching every store prefix copies a depth-n array n times, even
            // when its final spelling fits the unchanged emission budget.
            // Overrides and existing cache entries still take precedence.
            self.write_application_into(out, symbol, args);
            return;
        } else {
            self.format_term_data(term)
        };
        self.charge(formatted.len() as u64);
        out.push_str(&formatted);
        self.format_cache.borrow_mut().insert(term_id, formatted);
    }

    /// The single structural application spelling, shared by direct append
    /// and structural-only rendering. Charge the bytes this application adds;
    /// each child charges its own writes, without copying ancestor buffers.
    pub(super) fn write_application_into(
        &self,
        out: &mut String,
        symbol: &Symbol,
        args: &[TermId],
    ) {
        if self.work_budget_exhausted() {
            return;
        }
        let name = Self::application_spelling_head(symbol, args.len());
        let own_bytes = if args.is_empty() {
            name.len()
        } else {
            name.len().saturating_add(args.len()).saturating_add(2)
        };
        if !self.admit_emission_work(own_bytes as u64) {
            return;
        }
        if args.is_empty() {
            out.push_str(&name);
            return;
        }
        out.push('(');
        out.push_str(&name);
        for arg in args {
            out.push(' ');
            self.write_term_into(out, *arg);
            if self.work_budget_exhausted() {
                return;
            }
        }
        out.push(')');
    }

    /// The one application-head spelling shared by ordinary rendering and
    /// the bounded canonical projection used by authored definition bridges.
    pub(super) fn application_spelling_head(symbol: &Symbol, arity: usize) -> String {
        match symbol {
            Symbol::Named(name) if arity == 1 && name.starts_with("is-") => {
                format!("(_ is {})", quote_symbol(&name[3..]))
            }
            Symbol::Named(name) if arity == 0 && name == "cl" => {
                ALETHE_CLAUSE_CONSTRUCTOR_TERM.to_string()
            }
            _ => Self::format_symbol(symbol),
        }
    }

    /// The document's rendering of `term_id` with only its OWN producer
    /// override set aside: every descendant keeps its channel. `None` when a
    /// printer channel (a Skolem `choice`, a confined bridge rendering) already
    /// owns the term, because then there is no second spelling to derive.
    pub(super) fn format_term_without_own_override(&self, term_id: TermId) -> Option<String> {
        if self.skolem_overrides.borrow().contains_key(&term_id)
            || self.let_bridge_renderings.borrow().contains_key(&term_id)
        {
            return None;
        }
        Some(self.format_term_structurally(term_id))
    }

    /// The structural rendering of `term_id` with EVERY channel for the term
    /// itself set aside and every descendant keeping its channel. Uncached.
    pub(super) fn format_term_structurally(&self, term_id: TermId) -> String {
        let term = self.terms.get(term_id);
        let formatted = self
            .format_const_array(term_id, term)
            .unwrap_or_else(|| self.format_term_data(term));
        self.charge(formatted.len() as u64);
        formatted
    }

    /// Render AY's internal constant-array spelling as SMT-LIB's.
    ///
    /// `TermStore::mk_const_array` stores `((as const (Array I E)) v)` as the
    /// plain application `(const-array v)` (see `term/array.rs`). SMT-LIB has
    /// no such function, so printing it verbatim makes every external consumer
    /// reject the whole file with "identifier 'const-array' is not defined" —
    /// `invalid`, which is strictly worse than a `hole`, since no rule can even
    /// run on an unparseable document. This is the same defect class the
    /// datatype-tester rewrite below fixes (`is-C` → `(_ is C)`).
    ///
    /// The sort annotation is mandatory in the surface syntax and is recovered
    /// from the term's own sort, so nothing is inferred. Deliberately keyed on
    /// BOTH the name and an `Array` sort whose element sort is the argument's,
    /// so a user-declared function that happens to be spelled `const-array`
    /// keeps its ordinary rendering.
    fn format_const_array(&self, term_id: TermId, term: &TermData) -> Option<String> {
        let TermData::App(Symbol::Named(name), args) = term else {
            return None;
        };
        if name != "const-array" {
            return None;
        }
        let [value] = args.as_slice() else {
            return None;
        };
        let sort = self.terms.sort(term_id);
        let Sort::Array(array_sort) = sort else {
            return None;
        };
        if self.terms.sort(*value) != &array_sort.element_sort {
            return None;
        }
        Some(format!(
            "((as const {}) {})",
            format_sort_alethe(sort),
            self.format_term(*value)
        ))
    }
}
