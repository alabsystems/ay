// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Model extraction: one value per equivalence class that holds a store chain
//! (2026-09-24 arrays fix-up).
//!
//! An asserted `(= X (store (store b i v) j w))` fixes every cell of `X`: the
//! written cells read `v`/`w`, every other cell reads `b` there. The per-term
//! extraction builds each array from its own observed reads, so `X` and `b`
//! can each miss what the other one observed, and two store chains asserted
//! equal over DIFFERENT free bases `b` and `c` get independent `else` values
//! from the renderer (it folds each array's observed cell into its default).
//! The printed witness then falsifies the asserted equality and the gate
//! refutes it (hunt D4-b free-bases witness; the D4-a repair's lost
//! incremental `sat` answers), although the solver's assignment is consistent.
//!
//! [`ArraySolver::reconcile_store_chain_classes`] gives such a class a single
//! value, as the equality demands: every cell a member or a chain base
//! observed OUTSIDE the chains' written indices is a cell of every base (the
//! chains agree with their bases there), every written cell is a cell of
//! every non-store member (outermost write first), and one `else` value is
//! shared by the members and the bases. Only cells the model has no value
//! for are filled; a cell the model already fixes differently is left alone
//! (the assignment is then inconsistent, and the gate says so). The result is
//! a candidate model: validation and the independent gate still check every
//! assertion against it.

use super::*;

/// A store member of a class: the store term, its chain's base, and the
/// chain's written cells outermost first.
struct ClassChain {
    store: TermId,
    base: TermId,
    writes: Vec<(String, String)>,
}

impl ArraySolver<'_> {
    pub(crate) fn reconcile_store_chain_classes(
        &self,
        model: &mut ArrayModel,
        term_values: &HashMap<TermId, String>,
    ) {
        for class in &self.equiv_classes {
            // Nested arrays name their element values by congruence class
            // (`@Arr!n`), which is not a value an `else` can take.
            if class.first().is_some_and(|&member| {
                matches!(self.terms.sort(member), Sort::Array(array_sort)
                    if matches!(array_sort.element_sort, Sort::Array(_)))
            }) {
                continue;
            }
            let chains: Vec<ClassChain> = class
                .iter()
                .filter_map(|&member| self.class_chain(member, term_values))
                .filter(|chain| !class.contains(&chain.base))
                .collect();
            if chains.is_empty() {
                continue;
            }
            let written: HashSet<&str> = chains
                .iter()
                .flat_map(|chain| chain.writes.iter().map(|(index, _)| index.as_str()))
                .collect();
            let bases: Vec<TermId> = {
                let mut bases: Vec<TermId> = chains.iter().map(|chain| chain.base).collect();
                bases.sort_unstable_by_key(|t| t.0);
                bases.dedup();
                bases
            };
            let members: Vec<TermId> = class
                .iter()
                .copied()
                .filter(|member| {
                    !self.store_cache.contains_key(member) && self.array_vars.contains_key(member)
                })
                .collect();

            // Cells outside the written indices, observed on a plain member
            // or on any base: every base reads them too.
            let mut unwritten_cells: Vec<(String, String)> = Vec::new();
            for &term in members.iter().chain(bases.iter()) {
                if let Some(interp) = model.array_values.get(&term) {
                    unwritten_cells.extend(
                        interp
                            .stores
                            .iter()
                            .filter(|(index, _)| !written.contains(index.as_str()))
                            .cloned(),
                    );
                }
            }
            let mut shared_default: Option<String> = None;
            let mut default_conflict = false;
            for &term in members.iter().chain(bases.iter()) {
                // A const-array base FIXES the class's else value: every chain
                // over it reads the const value off its written indices. The
                // extraction gives a const-array term an interpretation only
                // when its value term has a model value, so read the value
                // directly (a literal needs none); inventing one instead
                // printed `a0` with a different else value than the chain
                // over `(as const 1)` it is asserted equal to (fresh
                // storeeq_2609_0475 --z3-mode).
                let default = self
                    .const_array_cache
                    .get(&term)
                    .and_then(|&value| {
                        term_values
                            .get(&value)
                            .filter(|value| !value.is_empty())
                            .cloned()
                            .or_else(|| self.constant_model_value(value))
                    })
                    .or_else(|| {
                        model
                            .array_values
                            .get(&term)
                            .and_then(|interp| interp.default.clone())
                    });
                if let Some(default) = default {
                    match &shared_default {
                        Some(existing) if *existing != default => default_conflict = true,
                        Some(_) => {}
                        None => shared_default = Some(default),
                    }
                }
            }
            if shared_default.is_none() && !default_conflict {
                shared_default =
                    self.invented_class_else_value(class, &bases, &unwritten_cells, &chains);
            }

            for &base in &bases {
                // A const-array base is its default everywhere; its value is
                // not the extraction's to fill.
                if self.const_array_cache.contains_key(&base) {
                    continue;
                }
                // Bases take only the cells observed OUTSIDE every written
                // index. Filling a base also at indices only OTHER chains of
                // the class write (`bcaf205a27`, reverted 2026-09-25) cost
                // decided verdicts and won none measured: on fresh
                // incr2_2410_0011's fourth query it gave `a` the cells
                // `1 -> 5`, `2 -> 5` of a chain over `c`, falsifying p0's
                // `(= K2 (store a i (select b 2)))`.
                let interp = self.interpretation_entry(model, base);
                for (index, value) in &unwritten_cells {
                    if !interp.stores.iter().any(|(k, _)| k == index) {
                        interp.stores.push((index.clone(), value.clone()));
                    }
                }
                if interp.default.is_none() && !default_conflict {
                    interp.default = shared_default.clone();
                }
            }
            for chain in &chains {
                let interp = self.interpretation_entry(model, chain.store);
                for (index, value) in &unwritten_cells {
                    if !interp.stores.iter().any(|(k, _)| k == index) {
                        interp.stores.push((index.clone(), value.clone()));
                    }
                }
                if interp.default.is_none() && !default_conflict {
                    interp.default = shared_default.clone();
                }
            }
            for &member in &members {
                let interp = self.interpretation_entry(model, member);
                for chain in &chains {
                    for (index, value) in &chain.writes {
                        if !interp.stores.iter().any(|(k, _)| k == index) {
                            interp.stores.push((index.clone(), value.clone()));
                        }
                    }
                }
                for (index, value) in &unwritten_cells {
                    if !interp.stores.iter().any(|(k, _)| k == index) {
                        interp.stores.push((index.clone(), value.clone()));
                    }
                }
                if interp.default.is_none() && !default_conflict {
                    interp.default = shared_default.clone();
                }
            }
        }
    }

    /// `member`'s store chain with every written index and value valued in
    /// `term_values`, or `None` (not a store, or a cell without a value).
    fn class_chain(
        &self,
        member: TermId,
        term_values: &HashMap<TermId, String>,
    ) -> Option<ClassChain> {
        if !self.store_cache.contains_key(&member) {
            return None;
        }
        let mut writes = Vec::new();
        let mut current = member;
        for _ in 0..=self.store_cache.len() {
            let Some(&(base, index, value)) = self.store_cache.get(&current) else {
                break;
            };
            let index = term_values.get(&index).filter(|s| !s.is_empty())?;
            let value = term_values.get(&value).filter(|s| !s.is_empty())?;
            writes.push((index.clone(), value.clone()));
            current = base;
        }
        Some(ClassChain {
            store: member,
            base: current,
            writes,
        })
    }

    /// The else value a class takes when no member fixes one, or `None` to
    /// leave it to model completion.
    ///
    /// A class with an OPAQUE member or base -- a read out of an array of
    /// arrays, or an application of an array-valued uninterpreted function --
    /// always takes an observed cell value: completion derives no such term
    /// from a base, the outer array names an inner array by its congruence
    /// class (`@Arr!n`, which the gate could not resolve under a fresh else
    /// value: fresh nested_2609_0011 --z3-mode), and the search does not
    /// merge congruent array-valued applications (variants5 m2v_23/m2v_55:
    /// left open or made fresh, their classes printed apart).
    ///
    /// Otherwise only a class with two or more FREE bases needs one: each free
    /// base would otherwise get its own else value from completion, and
    /// `(= (store b ..) (store c ..))` over different bases prints false (the
    /// hunt's d4b_free_bases witness). With a single free base completion
    /// derives every member from that base's own reads and definitions, and an
    /// invented value only fought them: fresh finstore_2410_0012, corpus
    /// swap_invalid_t3_pp_sf_ai_00002_009 --z3-mode and the differential-fuzz
    /// arrays seed 179 (`arrays_seed_179_emits_a_valid_model`, a read at a
    /// store-missed index needs the base's else value to be -5) all went
    /// `sat` -> `unknown`.
    ///
    /// The value is an observed cell value, shared by the class. A FRESH
    /// value per class (distinct across classes; 6bda610eb8) was tried and
    /// reverted: with the invention already limited as above it only cost
    /// verdicts -- the corpus storecomm_invalid_t{1,3}_pp_sf_ni family (14
    /// files, both postures) went `sat` -> `unknown` under it.
    fn invented_class_else_value(
        &self,
        class: &[TermId],
        bases: &[TermId],
        unwritten_cells: &[(String, String)],
        chains: &[ClassChain],
    ) -> Option<String> {
        let opaque = class.iter().chain(bases.iter()).any(|&member| {
            self.select_cache.get(&member).is_some_and(|&(outer, _)| {
                matches!(self.terms.sort(outer), Sort::Array(array_sort)
                    if matches!(array_sort.element_sort, Sort::Array(_)))
            }) || self.is_array_valued_uf_application(member)
        });
        let free_bases = bases
            .iter()
            .filter(|&base| !self.const_array_cache.contains_key(base))
            .count();
        if !opaque && free_bases < 2 {
            return None;
        }
        unwritten_cells
            .first()
            .map(|(_, value)| value.clone())
            .or_else(|| {
                chains
                    .first()
                    .and_then(|chain| chain.writes.first())
                    .map(|(_, value)| value.clone())
            })
    }

    /// Whether `term` applies an uninterpreted function to arguments and
    /// returns an array (not an array-theory operation).
    fn is_array_valued_uf_application(&self, term: TermId) -> bool {
        if !matches!(self.terms.sort(term), Sort::Array(_)) {
            return false;
        }
        match self.terms.get(term) {
            TermData::App(Symbol::Named(name), args) => {
                !args.is_empty()
                    && !matches!(
                        name.as_str(),
                        "select" | "store" | "ite" | "const-array" | "as-array" | "_as-array"
                    )
            }
            _ => false,
        }
    }

    /// The model spelling of an Int or Bool literal term, or `None`.
    fn constant_model_value(&self, term: TermId) -> Option<String> {
        match self.terms.get(term) {
            TermData::Const(Constant::Int(n)) => Some(format_int_model_value(n)),
            TermData::Const(Constant::Bool(b)) => Some(b.to_string()),
            _ => None,
        }
    }

    fn interpretation_entry<'m>(
        &self,
        model: &'m mut ArrayModel,
        term: TermId,
    ) -> &'m mut ArrayInterpretation {
        let interp = model.array_values.entry(term).or_default();
        if interp.index_sort.is_none() {
            if let Sort::Array(array_sort) = self.terms.sort(term) {
                interp.index_sort = Some(array_sort.index_sort.clone());
                interp.element_sort = Some(array_sort.element_sort.clone());
            }
        }
        interp
    }
}

/// The model's spelling of an Int value.
fn format_int_model_value(n: &BigInt) -> String {
    if n.sign() == num_bigint::Sign::Minus {
        format!("(- {})", -n)
    } else {
        n.to_string()
    }
}
