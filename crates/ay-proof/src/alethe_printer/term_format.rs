// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

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
        if let Some(term_str) = self
            .term_overrides
            .and_then(|overrides| overrides.get(&term_id))
        {
            self.charge(term_str.len() as u64);
            out.push_str(term_str);
            return;
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
        let formatted = self
            .format_const_array(term_id, term)
            .unwrap_or_else(|| self.format_term_data(term));
        self.charge(formatted.len() as u64);
        out.push_str(&formatted);
        self.format_cache.borrow_mut().insert(term_id, formatted);
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
        Some(format!("((as const {sort}) {})", self.format_term(*value)))
    }
}
