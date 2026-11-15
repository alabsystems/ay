// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Functions only a quantified assertion applies (2026-09-25 fix-up, B3 for
//! function symbols).
//!
//! The affine elimination can remove every application of an uninterpreted
//! function: `(forall v. (or (= (* v w) 0) (= (+ (* 2 v) (h s)) 1)))` becomes
//! `(= w 0)`, the solver's model gives `h` no table, and the quantified gate
//! confirms the universal without one (it holds whatever `h` is). The printer
//! omits a function that occurs under a quantifier with no interpretation, so
//! `(get-model)` printed a partial model and `(get-value ((h s)))` failed —
//! 20 `--z3-mode` `sat` answers of the fix-up's fresh-seed sets, one where main
//! printed the function. Output completion now gives such a function the
//! canonical formula-neutral default, which the printer prints, the evaluator
//! reads and the quantified gate re-checks. A result sort with no canonical
//! default (datatypes, arrays) stays as main leaves it: main prints the same
//! partial model there (a certificate lane), so refusing the `sat` would lose
//! main's verdict.

use ay_core::kani_compat::DetHashSet as HashSet;
use ay_core::term::{Symbol, TermData};
use ay_core::{Sort, TermId};

use super::super::Model;
use crate::executor::Executor;

impl Executor {
    /// Give the canonical default to every ordinary free function that the
    /// assertions and `extra_roots` apply only under a quantifier and that
    /// `model` does not interpret
    /// ([`Self::quantified_only_functions_without_interpretation`]). Returns
    /// how many were defaulted — 0 when none could be (the install is atomic).
    pub(super) fn complete_quantified_only_functions(
        &self,
        model: &mut Model,
        extra_roots: &[TermId],
    ) -> usize {
        let mut additions = Vec::new();
        for (symbol, parameter_sorts, result_sort) in
            self.quantified_only_functions_without_interpretation(model, extra_roots)
        {
            let Some(default) = self.unconstrained_default_value(&result_sort) else {
                continue;
            };
            let request = ay_frontend::ProjectionBindingRequest {
                symbol,
                parameter_sorts,
                result_sort,
            };
            let Ok(binding) = self.ctx.check_projection_declaration(&request) else {
                continue;
            };
            additions.push((binding, default));
        }
        if additions.is_empty() {
            return 0;
        }
        let added = additions.len();
        // The install replaces the whole set: carry the defaults already there
        // (a binding is not `Clone`; re-check each one).
        let mut entries = Vec::new();
        for entry in model.formula_neutral_function_default_entries() {
            let request = ay_frontend::ProjectionBindingRequest {
                symbol: entry.symbol().clone(),
                parameter_sorts: entry.parameter_sorts().to_vec(),
                result_sort: entry.result_sort().clone(),
            };
            let Ok(binding) = self.ctx.check_projection_declaration(&request) else {
                return 0;
            };
            entries.push((binding, entry.value().clone()));
        }
        entries.extend(additions);
        match model.install_formula_neutral_function_defaults(&self.ctx, entries) {
            Some(()) => added,
            None => 0,
        }
    }

    /// Every ordinary free function (identity symbol and signature) that the
    /// assertions and `extra_roots` apply only under a quantifier — no ground
    /// application, so a default cannot change a ground value — and that
    /// `model` interprets nowhere the printer reads: no EUF table, certified
    /// total or constant interpretation, symbolic projection or formula-neutral
    /// default. The printer omits exactly such a function.
    fn quantified_only_functions_without_interpretation(
        &self,
        model: &Model,
        extra_roots: &[TermId],
    ) -> Vec<(Symbol, Vec<Sort>, Sort)> {
        let mut roots = self.ctx.assertions.clone();
        roots.extend_from_slice(extra_roots);
        let (ground, quantified) = self.function_heads_by_scope(&roots);
        let mut missing = Vec::new();
        if quantified.is_empty() {
            return missing;
        }
        for (surface_name, info) in self.ctx.symbol_iter() {
            if info.arg_sorts.is_empty()
                || !self.is_ordinary_free_primary_declaration(surface_name, info)
            {
                continue;
            }
            let identity = self.ctx.symbol_identity_name(surface_name, info);
            let symbol = Symbol::named(identity);
            if !quantified.contains(&symbol) || ground.contains(&symbol) {
                continue;
            }
            let interpreted = model.euf_model.as_ref().is_some_and(|euf| {
                euf.function_tables.contains_key(identity)
                    || euf.function_table_terms.contains_key(identity)
                    || euf.function_table_conflicts.contains(identity)
            }) || model.has_certified_total_uf(identity)
                || model.has_certified_const_interp_symbol(&symbol)
                || model.has_formula_neutral_function_default_symbol(&symbol)
                || self
                    .const_interp_cert_witness_entries(model)
                    .iter()
                    .any(|entry| entry.name() == Some(surface_name))
                || !matches!(
                    model.projection_ufs.projected_argument_for_signature(
                        &symbol,
                        &info.arg_sorts,
                        &info.sort,
                    ),
                    Ok(None)
                );
            if !interpreted {
                missing.push((symbol, info.arg_sorts.clone(), info.sort.clone()));
            }
        }
        missing.sort_by(|left, right| left.0.name().cmp(right.0.name()));
        missing
    }

    /// The heads of the applications (arity > 0) reachable from `roots`
    /// outside every quantifier, and those reachable inside one (bodies and
    /// triggers).
    fn function_heads_by_scope(&self, roots: &[TermId]) -> (HashSet<Symbol>, HashSet<Symbol>) {
        let mut ground: HashSet<Symbol> = HashSet::default();
        let mut quantified: HashSet<Symbol> = HashSet::default();
        let mut seen: HashSet<(TermId, bool)> = HashSet::default();
        let mut stack: Vec<(TermId, bool)> = roots.iter().map(|&root| (root, false)).collect();
        while let Some((t, under)) = stack.pop() {
            if !seen.insert((t, under)) {
                continue;
            }
            match self.ctx.terms.get(t) {
                TermData::App(symbol, args) => {
                    if !args.is_empty() {
                        if under {
                            quantified.insert(symbol.clone());
                        } else {
                            ground.insert(symbol.clone());
                        }
                    }
                    stack.extend(args.iter().map(|&arg| (arg, under)));
                }
                TermData::Not(inner) => stack.push((*inner, under)),
                TermData::Ite(c, a, b) => stack.extend([(*c, under), (*a, under), (*b, under)]),
                TermData::Let(bindings, body) => {
                    stack.extend(bindings.iter().map(|(_, value)| (*value, under)));
                    stack.push((*body, under));
                }
                TermData::Forall(_, body, triggers) | TermData::Exists(_, body, triggers) => {
                    stack.push((*body, true));
                    stack.extend(triggers.iter().flatten().map(|&trigger| (trigger, true)));
                }
                _ => {}
            }
        }
        (ground, quantified)
    }
}
