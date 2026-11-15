// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Function-table rows of applications the current query does not contain.
//!
//! EUF model extraction sweeps every application in the TERM STORE into the
//! function tables when no model scope is set. The store holds more than the
//! query: the Z3 C API builds terms it never asserts (`h(a)` of a Real-ranged
//! `h`), its model evaluator substitutes values into terms (`pr(c)` under
//! `c = 0` interns `pr(0)`), and earlier queries leave their terms behind. Such
//! an application constrains nothing, yet its row entered the published table:
//! measured through the Z3 C API (2026-10-01), a Real-ranged one had no value
//! and failed the whole `(get-model)` ("no model value for function-table
//! entry of sort Real"), and `pr(0)`'s default `false` collided with the
//! query's `pr(c) = true` at `c = 0` ("inconsistent function table"). Either
//! way the API published `sat` with an EMPTY model.
//!
//! A quantifier-free query is decided entirely by the applications reachable
//! from its AUTHORED assertions and assumptions, including forms restored after
//! preprocessing, plus the current working/kernel window. Rows of unrelated
//! applications are not model points and are dropped before validation.
//! A quantified query keeps
//! every row: quantifier instantiation adds ground applications (`f(0)` from
//! `forall x. f(x) > 100`) that the restored authored assertions no longer
//! contain but the published function must still honour.

use ay_core::kani_compat::DetHashSet as HashSet;
use ay_core::term::TermData;
use ay_core::TermId;
use ay_euf::EufModel;

use crate::executor::Executor;

impl Executor {
    /// Drop every function-table row of `euf` whose source application is not
    /// reachable from the canonical same-query authored roots/assumptions,
    /// current working assertions or the checked kernel window
    /// (`function_row_roots`),
    /// unless the query contains a quantifier (see the module docs).
    pub(in crate::executor) fn retain_query_function_table_rows(
        &self,
        euf: &mut EufModel,
    ) -> Result<(), crate::executor_types::UnknownOrigin> {
        if euf.function_tables.is_empty() {
            return Ok(());
        }
        let mut reachable: HashSet<TermId> = HashSet::default();
        // Store runs inside the authored-root snapshot installed by plain or
        // assumption checks. The same constructor used by the public gate
        // includes the actual temporary assumptions; current rewritten roots
        // alone can omit the original row representative chosen by recovery.
        let mut stack = self.independent_gate_query_roots()?;
        // Preserve the pre-existing authorized working/kernel window too.
        // This is not a scan of unasserted or previous-query TermStore terms.
        stack.extend(self.ctx.assertions.iter().copied());
        stack.extend(self.function_row_roots.iter().copied());
        let root_entries = stack.len();
        while let Some(term) = stack.pop() {
            if !reachable.insert(term) {
                continue;
            }
            match self.ctx.terms.get(term) {
                TermData::Forall(..) | TermData::Exists(..) => return Ok(()),
                TermData::App(_, args) => stack.extend(args.iter().copied()),
                TermData::Not(inner) => stack.push(*inner),
                TermData::Ite(c, a, b) => stack.extend([*c, *a, *b]),
                TermData::Let(bindings, body) => {
                    stack.extend(bindings.iter().map(|(_, value)| *value));
                    stack.push(*body);
                }
                _ => {}
            }
        }
        let names: Vec<String> = euf.function_tables.keys().cloned().collect();
        for name in names {
            let Some(sources) = euf.function_table_terms.get(&name) else {
                continue;
            };
            let Some(rows) = euf.function_tables.get(&name) else {
                continue;
            };
            if sources.len() != rows.len() || sources.iter().all(|t| reachable.contains(t)) {
                continue;
            }
            let observing = ay_core::misc_cli_flags().model_reject_dump;
            let before = rows.len();
            let mut first_removed = None;
            let mut first_kept = None;
            let (kept_rows, kept_sources): (Vec<_>, Vec<_>) = rows
                .iter()
                .cloned()
                .zip(sources.iter().copied())
                .filter(|(_, source)| {
                    let keep = reachable.contains(source);
                    if observing {
                        if keep && first_kept.is_none() {
                            first_kept = Some(*source);
                        }
                        if !keep && first_removed.is_none() {
                            first_removed = Some(*source);
                        }
                    }
                    keep
                })
                .unzip();
            if observing {
                self.observe_removed_uf_rows(
                    &name,
                    before,
                    kept_rows.len(),
                    first_removed,
                    first_kept,
                    reachable.len(),
                    root_entries,
                );
            }
            if kept_rows.is_empty() {
                euf.function_tables.remove(&name);
                euf.function_table_terms.remove(&name);
            } else {
                euf.function_tables.insert(name.clone(), kept_rows);
                euf.function_table_terms.insert(name, kept_sources);
            }
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests;
