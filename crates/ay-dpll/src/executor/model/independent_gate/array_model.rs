// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Independent extraction of complete array model values.

use ay_core::kani_compat::DetHashSet;
use ay_core::{Sort, TermId};
use ay_model_check::{ArrayValue, EvalOutcome, Evaluator, ModelValue};

use super::super::datatype_cell_authority::exact_datatype_carrier_token;
use super::super::rendered_dt_limits::model_value_work;
use super::IndependentModelView;

impl IndependentModelView<'_> {
    pub(super) fn array_leaf(
        &self,
        t: TermId,
        index_sort: &Sort,
        element_sort: &Sort,
    ) -> Option<ModelValue> {
        if let Some(cached) = self.resolved.borrow().get(&t) {
            return Some(cached.clone());
        }
        if self.resolved_none.borrow().contains(&t) {
            return None; // cached stack-independent failure (#gate-none-cache)
        }
        if !self.resolving.borrow_mut().insert(t) {
            self.cycle_hits.set(self.cycle_hits.get() + 1);
            return None; // cycle
        }
        let hits_before = self.cycle_hits.get();
        let result = self.array_leaf_inner(t, index_sort, element_sort);
        self.resolving.borrow_mut().remove(&t);
        match &result {
            Some(v) => {
                self.resolved.borrow_mut().insert(t, v.clone());
            }
            // A failure whose frame observed NO cycle re-entry never consulted
            // the in-flight stack, so it is a pure function of the fixed model
            // — cacheable (#gate-none-cache). A post-cycle failure is not.
            None if self.cycle_hits.get() == hits_before => {
                self.resolved_none.borrow_mut().insert(t);
            }
            None => {}
        }
        result
    }

    fn array_leaf_inner(
        &self,
        t: TermId,
        index_sort: &Sort,
        element_sort: &Sort,
    ) -> Option<ModelValue> {
        // 1. Definitional equality `(= t <array-expr>)`: evaluate the defining
        //    expression compositionally with the gate's own evaluator. A leaf can
        //    carry SEVERAL asserted definitions (e.g. a fresh `(= d (const-array
        //    x))` plus alias equalities `(= d other!fld_data)`); they are all
        //    asserted EQUAL, so ANY that the gate can fully evaluate yields the
        //    array's value — try them in order and take the first that resolves to
        //    a concrete array. Consistency between the alternatives is still
        //    enforced: each OTHER definition is itself a top-level assertion the
        //    gate ground-checks, so two definitions that disagree under the model
        //    produce a `ModelViolates` there (never suppressed here).
        for def in self.array_definitions(t) {
            let ev = Evaluator::new(&self.exec.ctx.terms, self);
            if let EvalOutcome::Value(v @ ModelValue::Array(_)) = ev.evaluate(def) {
                return Some(v);
            }
            // else: try the next definition / fall through to the reconstructed
            // model (branch 2 below).
        }

        // 1b. A preprocessing-recorded variable substitution is also an exact
        // definition, even though the defining equality has been consumed and
        // therefore cannot appear in `array_definitions`. Resolve only the
        // recorded forward edge, require the replacement to have the identical
        // array sort, and evaluate it compositionally through this independent
        // view. This is stronger evidence than the poisoned theory model below:
        // the preprocessor may replace `a24 -> a9`, while `a9` itself resolves
        // through an authored equality to a concrete store chain.
        //
        // The outer `array_leaf` cycle guard is already active for `t`, so a
        // malformed/cyclic substitution chain (`a -> b -> a`) fails closed.
        if let Some(&replacement) = self.exec.recorded_var_substitutions.get(&t) {
            if self.exec.ctx.terms.sort(replacement) == self.exec.ctx.terms.sort(t) {
                let ev = Evaluator::new(&self.exec.ctx.terms, self);
                if let EvalOutcome::Value(v @ ModelValue::Array(_)) = ev.evaluate(replacement) {
                    return Some(v);
                }
            }
        }

        // A read-conflicted theory interpretation is not evidence for the
        // array value, but an independently evaluated authored definition
        // above is. Keep the conflict fail-closed for every fallback below;
        // this ordering permits only the stronger, assertion-derived value.
        if self
            .model
            .array_model
            .as_ref()
            .is_some_and(|arrays| arrays.read_conflicted.contains(&t))
        {
            return None;
        }

        // 2. Fallback: the array theory's reconstructed model entry.
        if let Some(v) = self.array_from_model(t, index_sort, element_sort) {
            return Some(v);
        }

        // 3. EXTENSIONALITY-COVERING MERGE. An array leaf the theory model does
        //    not reconstruct, but which is asserted EQUAL to other array leaves
        //    (a mutual SSA-copy class `(= a b)`, `(= b c)`), is resolved by
        //    giving the WHOLE class ONE shared canonical array value: the fixed
        //    canonical default of the element sort (a deterministic function of
        //    the sort, identical for every member) plus the merged committed
        //    direct-select reads of the class. Because every member then denotes
        //    the IDENTICAL array, `select(a,i)` and `select(b,i)` read the same
        //    value at every index, so the asserted equalities confirm.
        //
        //    SOUND: the members are asserted mutually equal, so a model in which
        //    they are the identical array satisfies those equalities; the shared
        //    default only sets indices in NO committed read (hence in no other
        //    constraint besides the extensionality), and the gate still
        //    re-checks every assertion, so any real conflict ⇒ `ModelViolates`.
        //    Guards: only array-`Var == Var` equalities that are top-level or
        //    top-level-`and` conjuncts join the class (never `or`/`ite`/`not`);
        //    a committed-read VALUE conflict between members fails the whole
        //    class closed; the default is a fixed function of the element sort.
        //
        //    NOTE (#seed-1213-case-187): a printed-witness fallback was tried
        //    here and REVERTED — parsing back the printer's total array and
        //    refuting against it is UNSOUND, because the printer fabricates a
        //    single canonical default for the array's unread indices, so a
        //    satisfiable `(distinct -3 (select a z) (select a x))` with z != x
        //    and `a` genuinely unpinned would be falsely refuted (both reads
        //    collapse to the fabricated default). A refutation is only sound
        //    when it holds in EVERY completion of the unpinned leaf; that
        //    "for-all-completions" reasoning is the job of the authoritative
        //    congruent-read fail-closed gate, not this per-leaf resolver. Case
        //    187 is fixed by CONSTRUCTION (same-array read-congruence
        //    propagation in ay-arrays), so no wrong model reaches here for that
        //    class; an unpinned leaf stays a coverage gap (keeps `sat`).
        self.array_extensionality_value(t, index_sort, element_sort)
    }

    /// Branch 2 of [`Self::array_leaf_inner`]: the array theory's reconstructed
    /// model entry for `t`, or `None` if partial/absent.
    pub(super) fn array_from_model(
        &self,
        t: TermId,
        index_sort: &Sort,
        element_sort: &Sort,
    ) -> Option<ModelValue> {
        let array_model = self.model.array_model.as_ref()?;
        // Extraction dropped at least one disputed cell. Neither an existing
        // default nor a later completion may turn that deliberately-partial
        // interpretation into independent evidence for a total array.
        if array_model.read_conflicted.contains(&t) {
            return None;
        }
        let interp = array_model.array_values.get(&t)?;
        // A partial array fails closed.
        let default_str = interp.default.as_ref()?;
        // A whole-array field can survive sole-constructor lowering as a bare
        // `Array<_, D>` leaf even though no datatype owner or cell read remains
        // in the authored query. For a hazardous `D`, W6 correctly has no cell
        // class to certify. Authenticate that exact absence for this outer
        // sort, then collapse every remaining abstract extractor carrier to
        // ONE canonical structured inhabitant. Distinct opaque spellings are
        // never preserved as datatype identities (which could invent a bogus
        // disequality for a singleton carrier). `None` or a nonempty cell
        // capability retains the ordinary W6 quarantine.
        let unobserved_hazardous_slack =
            if self.exec.datatype_sort_carries_array_field(element_sort) {
                self.exec.ctx.terms.entry_stamp(t)?;
                let Sort::Array(outer_sort) = self.exec.ctx.terms.sort(t) else {
                    return None;
                };
                if &outer_sort.index_sort != index_sort || &outer_sort.element_sort != element_sort
                {
                    return None;
                }
                let members = self
                    .exec
                    .authenticated_datatype_array_completion_members(self.model, outer_sort)?;
                if members.is_empty() {
                    let constructor_tokens = self
                        .exec
                        .ctx
                        .datatype_iter()
                        .flat_map(|(_, constructors)| constructors)
                        .flat_map(|constructor| {
                            [
                                constructor.clone(),
                                self.exec.dt_surface(constructor).to_string(),
                            ]
                        })
                        .collect();
                    Some(constructor_tokens)
                } else {
                    None
                }
            } else {
                None
            };
        let default = self.array_interpretation_element_value(
            default_str,
            element_sort,
            unobserved_hazardous_slack.as_ref(),
        )?;
        let mut store = Vec::with_capacity(interp.stores.len());
        // ArrayInterpretation is authoritative/newest first, whereas the
        // independent evaluator's ArrayValue is oldest first (and selects by
        // scanning in reverse). Reverse at this representation boundary so a
        // repeated store index keeps the same winner the solver/emitter use.
        for (k_s, v_s) in interp.stores.iter().rev() {
            let key = self.parse_leaf(k_s, index_sort)?;
            let val = self.array_interpretation_element_value(
                v_s,
                element_sort,
                unobserved_hazardous_slack.as_ref(),
            )?;
            store.push((key, val));
        }
        Some(ModelValue::Array(Box::new(ArrayValue { default, store })))
    }

    fn array_interpretation_element_value(
        &self,
        spelling: &str,
        sort: &Sort,
        unobserved_hazardous_slack: Option<&DetHashSet<String>>,
    ) -> Option<ModelValue> {
        if let Some(value) = self.parse_leaf(spelling, sort) {
            return Some(value);
        }
        let constructor_tokens = unobserved_hazardous_slack?;
        let guard = self.datatype_guard();
        if guard.datatype_name(sort).is_some() {
            if let Some(value) = self
                .exec
                .parse_rendered_dt_value_cached(spelling, sort, guard)
            {
                return Some(value);
            }
        }
        if guard.is_exact_array_cell(sort)
            && exact_datatype_carrier_token(guard, constructor_tokens, sort, spelling)
        {
            let canonical = self.canonical_model_value(sort)?;
            model_value_work(&canonical)?;
            return Some(canonical);
        }
        None
    }
}
