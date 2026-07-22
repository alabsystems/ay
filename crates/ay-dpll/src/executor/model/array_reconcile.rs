// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Final-assignment reconciliation of Int-indexed array select cells
//! (#qf-auflia-final-index-reconcile).
//!
//! The AUFLIA combined lane extracts its `ArrayModel` from theory-side term
//! values (`ArraySolver::extract_model` keys interpretation entries by the
//! EUF/LIA value STRINGS of each select's index term). For a select whose
//! index is an arithmetic composite over Bool-conditioned ITEs — e.g. the
//! bit-recombination sums `(+ (ite b0 1 0) (* (ite b1 1 0) 2) ... 16)` that
//! the ay-chc BMC executor lane emits when a wide-BV table index is lowered to
//! per-bit Bools over an `(Array Int Int)` — the LIA solver never sees the
//! SAT-level Bool assignment, so `recompute_composite_int_values` cannot
//! evaluate the ITE conditions and the interpretation entry stays keyed by a
//! SPECULATIVE index value (observed: keys 19/32 while the final Bool
//! assignment makes the asserted reads hit 144/160).
//!
//! Under the final assignment the asserted reads then hit ABSENT cells, model
//! completion collapses them to a common default, an asserted distinctness
//! between the two reads evaluates false, and the independent soundness gate
//! (correctly) refuses the model — degrading a genuine `Sat` to `unknown` and,
//! in the CHC portfolio, re-manufacturing the same invalid model until the
//! guard budget burns (model-checker-consumer parity wishlist item 1, second trigger).
//!
//! This pass runs right after the full model is stored (so the SAT Bool
//! assignment, the LIA/EUF values and the array interpretations are all
//! available) and BEFORE validation:
//!
//! 0. ITE conditions inside select indices that the final model leaves
//!    UNVALUED (#w11-ite-sum: the SAT layer never saw the Bool var — the
//!    AUFLIA arithmetic lane keeps `(ite b 8 0)` opaque, so `b` can end the
//!    search entirely unassigned while the LIA model commits a value to the
//!    ITE term) are PINNED into `Model::bool_overrides`: when the ITE term's
//!    committed value matches exactly one literal branch, the condition is
//!    forced to that branch; conditions whose committed value matches
//!    neither branch (an incoherent speculative value — observed: committed
//!    `2` for `(ite b2 8 0)`) are searched over both polarities, keeping the
//!    first completion whose committed reads form a CONSISTENT cell map. If
//!    no completion is consistent the pins are removed and the pass behaves
//!    exactly as before (degrade to Unknown). Pinning only fills don't-care
//!    Bools in a CANDIDATE model — every validator re-checks all assertions
//!    against the completed model afterwards, so a wrong pin can only keep
//!    the degrade-to-Unknown outcome, never manufacture an invalid `Sat`
//!    and never flip sat/unsat.
//! 1. every `select` reachable from the assertions whose index sort is `Int`
//!    has its index EVALUATED under the final model (structural evaluation:
//!    ITE conditions read the SAT assignment / the step-0 pins, leaves read
//!    the LIA model);
//! 2. the read's COMMITTED value (the LIA/EUF per-term value of the select
//!    term — the value the solver actually reasoned with, never a completion
//!    default) is instantiated into the base array's interpretation at the
//!    evaluated index, with congruence enforced: two committed reads of one
//!    `(base, index-value)` cell that DISAGREE mean the candidate model is
//!    internally inconsistent, so the pass FAILS CLOSED — the caller must
//!    degrade the proposed `Sat` to `Unknown` instead of emitting the model;
//! 3. cells the pass cannot resolve (unevaluable index, no committed value,
//!    store-chain hit, unevaluable store key) are left exactly as today —
//!    validation and the independent gate still run unchanged either way.
//!
//! Soundness: the pass only adds cells that are FORCED by the model's own
//! committed values (so it can never make an invalid model pass validation —
//! the validators re-check every assertion against the same interpretation),
//! and its only other effect is degrading a proposed `Sat` to `Unknown`. It
//! can never flip sat/unsat.

use ay_core::kani_compat::{DetHashMap as HashMap, DetHashSet as HashSet};
use ay_core::term::{Constant, TermData};
use ay_core::{Sort, TermId};
use num_bigint::BigInt;

use super::{EvalValue, Executor, Model};

/// Cap on the number of UNFORCED ITE-condition pins searched by step 0
/// (#w11-ite-sum). `2^4 = 16` candidate completions at most; beyond the cap
/// the pass keeps today's behavior (no pins, degrade to Unknown).
const MAX_FREE_ITE_COND_PINS: usize = 4;

/// Parse an interpretation-entry Int string (`"7"` or `"(- 7)"`).
fn parse_int_entry(s: &str) -> Option<BigInt> {
    let t = s.trim();
    if let Some(inner) = t.strip_prefix("(-").and_then(|r| r.strip_suffix(')')) {
        return inner.trim().parse::<BigInt>().ok().map(|n| -n);
    }
    t.parse::<BigInt>().ok()
}

/// The model's committed value string for a term the theory search reasoned
/// about: an Int constant folds directly, otherwise the LIA per-term value
/// wins (it is what the arithmetic constraints were solved against), then the
/// EUF term-value string. Returns `None` when the model committed nothing —
/// the caller must then leave the cell alone (never fabricate).
fn committed_value_string(terms: &ay_core::TermStore, model: &Model, t: TermId) -> Option<String> {
    if let TermData::Const(Constant::Int(n)) = terms.get(t) {
        return Some(crate::executor_format::format_bigint(n));
    }
    if let Some(lia) = model.lia_model.as_ref() {
        if let Some(v) = lia.values.get(&t) {
            return Some(crate::executor_format::format_bigint(v));
        }
    }
    if let Some(euf) = model.euf_model.as_ref() {
        if let Some(s) = euf.term_values.get(&t) {
            if !s.is_empty() {
                return Some(s.clone());
            }
        }
    }
    None
}

/// Two committed value strings denote the same value: exact string match, or
/// both parse as the same integer (extraction and this pass may spell a
/// negative differently: `-3` vs `(- 3)`).
fn value_strings_agree(a: &str, b: &str) -> bool {
    if a == b {
        return true;
    }
    match (parse_int_entry(a), parse_int_entry(b)) {
        (Some(x), Some(y)) => x == y,
        _ => false,
    }
}

impl Executor {
    /// Reconcile Int-indexed array interpretation cells with the final
    /// assignment (see module docs). Returns `false` when the committed reads
    /// are internally inconsistent — the caller must NOT emit the model
    /// (degrade the proposed `Sat` to `Unknown`, fail-closed).
    pub(in crate::executor) fn reconcile_array_select_entries_with_final_assignment(
        &mut self,
    ) -> bool {
        let Some(model) = self.last_model.as_ref() else {
            return true;
        };
        if model.array_model.is_none() {
            return true;
        }

        // Collect `(select a i)` applications with Int-sorted index reachable
        // from the assertion window.
        let mut selects: Vec<(TermId, TermId, TermId)> = Vec::new();
        let mut seen: HashSet<TermId> = HashSet::default();
        let mut stack: Vec<TermId> = self.ctx.assertions.clone();
        while let Some(t) = stack.pop() {
            if !seen.insert(t) {
                continue;
            }
            match self.ctx.terms.get(t) {
                TermData::App(sym, args) => {
                    if sym.name() == "select"
                        && args.len() == 2
                        && matches!(self.ctx.terms.sort(args[1]), Sort::Int)
                    {
                        selects.push((t, args[0], args[1]));
                    }
                    stack.extend(args.iter().copied());
                }
                TermData::Not(inner) => stack.push(*inner),
                TermData::Ite(c, a, b) => {
                    stack.push(*c);
                    stack.push(*a);
                    stack.push(*b);
                }
                _ => {}
            }
        }
        if selects.is_empty() {
            return true;
        }

        // Deterministic processing order regardless of the DFS above.
        selects.sort_unstable();
        selects.dedup();

        // Snapshot the pre-pass model (#w1b-mutation-guard, see the post-check
        // below): every mutation this pass makes (step-0 Bool pins, committed
        // cells) must be revertible to the exact prior state.
        let before_model = model.clone();

        // Step 0 (#w11-ite-sum): pin unvalued Bool ITE conditions inside the
        // select indices so composite ite-sum indices evaluate under the
        // final assignment. No-op when every index already evaluates.
        let mut mutated = self.pin_unvalued_select_index_ite_conds(&selects);

        let Some(model) = self.last_model.as_ref() else {
            return true;
        };
        let Some(fresh) = self.collect_committed_read_cells(model, &selects) else {
            // Two committed reads of one cell disagree, or a committed read
            // contradicts an already-extracted cell/default: the candidate
            // model violates read congruence. Fail closed — do not emit.
            return false;
        };

        if !fresh.is_empty() {
            // Element sorts for interpretation bookkeeping (index sort is Int
            // by construction). Look one up per base from any select on it.
            let mut element_sorts: HashMap<TermId, Sort> = HashMap::default();
            for &(sel, arr, _) in &selects {
                let mut base = arr;
                while let TermData::App(sym, args) = self.ctx.terms.get(base) {
                    if sym.name() == "store" && args.len() == 3 {
                        base = args[0];
                    } else {
                        break;
                    }
                }
                element_sorts
                    .entry(base)
                    .or_insert_with(|| self.ctx.terms.sort(sel).clone());
            }

            let Some(model) = self.last_model.as_mut() else {
                return true;
            };
            let Some(am) = model.array_model.as_mut() else {
                return true;
            };
            for ((base, idx_int), val) in fresh {
                // Read-only consistency checks FIRST, so a base without any
                // cell to add never gains an empty interpretation entry (a
                // present-but-empty interp would block the definitional-
                // equality chase in `evaluate_select`, changing evaluations
                // without adding any information).
                if let Some(interp) = am.array_values.get(&base) {
                    // Match existing entries by PARSED index
                    // (spelling-insensitive).
                    if let Some(pos) = interp
                        .stores
                        .iter()
                        .position(|(k, _)| parse_int_entry(k).is_some_and(|n| n == idx_int))
                    {
                        if !value_strings_agree(&interp.stores[pos].1, &val) {
                            // The extracted cell disagrees with the committed
                            // read under the final assignment. Emitting either
                            // value would fabricate a winner — fail closed.
                            return false;
                        }
                        continue; // present and agreeing — nothing to add
                    }
                    if let Some(default) = &interp.default {
                        if !value_strings_agree(default, &val) {
                            // A total default already claims this cell with a
                            // different value — inconsistent. Fail closed.
                            return false;
                        }
                        continue; // redundant with the default
                    }
                }
                let interp = am.array_values.entry(base).or_default();
                if interp.index_sort.is_none() {
                    interp.index_sort = Some(Sort::Int);
                }
                if interp.element_sort.is_none() {
                    if let Some(es) = element_sorts.get(&base) {
                        interp.element_sort = Some(es.clone());
                    }
                }
                interp
                    .stores
                    .push((crate::executor_format::format_bigint(&idx_int), val));
                mutated = true;
            }
        }

        // Post-mutation guard (#w1b-mutation-guard): the pass may only KEEP
        // its mutations when they do not NEWLY FALSIFY any assertion. The
        // committed per-term select values this pass bakes into a variable
        // array's interpretation can be stale relative to interpretations the
        // extraction/witness-adoption machinery installed for OTHER arrays the
        // variable is equated to (observed: a store-permutation model where a
        // var-level committed cell contradicted the asserted store-chain
        // equality `(= a2 (store a1 i2 v2))` — the unmutated model validated,
        // the mutated one was strict-oracle rejected, degrading a genuine Sat
        // to Unknown). The per-cell same-key checks above cannot see such
        // CROSS-ARRAY clashes, so re-evaluate every assertion: if one is
        // definitively false under the mutated model but was NOT false under
        // the snapshot, revert to the snapshot wholesale (the exact pre-pass
        // status quo — skip the doubtful mutation rather than commit it).
        // Completeness can only improve: kept mutations validate at least as
        // well as before, reverts restore prior behavior exactly. Soundness is
        // untouched: both outcomes still pass the full strict + independent +
        // authoritative gate battery downstream.
        if mutated {
            let assertions = self.ctx.assertions.clone();
            let newly_false = {
                let Some(model_now) = self.last_model.as_ref() else {
                    return true;
                };
                assertions.iter().any(|&a| {
                    matches!(self.evaluate_term(model_now, a), EvalValue::Bool(false))
                        && !matches!(self.evaluate_term(&before_model, a), EvalValue::Bool(false))
                })
            };
            if newly_false {
                self.last_model = Some(before_model);
            }
        }
        true
    }

    /// Build the `(base array, evaluated index) -> committed value` cell map
    /// for the asserted reads (steps 1-2 of the module docs).
    ///
    /// Returns `None` when the committed reads are provably inconsistent:
    /// two reads of one cell with DISAGREEING committed values, or a
    /// committed read contradicting an already-extracted interpretation
    /// entry / total default. Unresolvable reads (unevaluable index, no
    /// committed value, store-chain hit) are skipped exactly as before.
    fn collect_committed_read_cells(
        &self,
        model: &Model,
        selects: &[(TermId, TermId, TermId)],
    ) -> Option<HashMap<(TermId, BigInt), String>> {
        let mut fresh: HashMap<(TermId, BigInt), String> = HashMap::default();
        'sel: for &(sel, arr, idx) in selects {
            let EvalValue::Rational(idx_val) = self.evaluate_term(model, idx) else {
                continue;
            };
            if !idx_val.is_integer() {
                continue;
            }
            let idx_int = idx_val.to_integer();
            let Some(sel_val) = committed_value_string(&self.ctx.terms, model, sel) else {
                continue;
            };

            // Attribute the read to the BASE array: peel store layers whose
            // keys evaluate to a DIFFERENT index. A store key that matches the
            // read index means the store (not the base) answers this read —
            // structural evaluation already handles it, nothing to instantiate.
            // An unevaluable store key makes the attribution unsafe: skip.
            let mut base = arr;
            loop {
                match self.ctx.terms.get(base) {
                    TermData::App(sym, args) if sym.name() == "store" && args.len() == 3 => {
                        let EvalValue::Rational(k) = self.evaluate_term(model, args[1]) else {
                            continue 'sel;
                        };
                        if !k.is_integer() || k.to_integer() == idx_int {
                            continue 'sel;
                        }
                        base = args[0];
                    }
                    TermData::App(sym, _) if sym.name() == "const-array" => {
                        continue 'sel;
                    }
                    _ => break,
                }
            }

            let key = (base, idx_int);
            if let Some(existing) = fresh.get(&key) {
                if !value_strings_agree(existing, &sel_val) {
                    return None;
                }
            } else {
                // Consistency against the already-extracted interpretation
                // (mirrors the apply step, so the step-0 completion search
                // sees these clashes too).
                if let Some(am) = model.array_model.as_ref() {
                    if let Some(interp) = am.array_values.get(&key.0) {
                        let existing = interp
                            .stores
                            .iter()
                            .find(|(k, _)| parse_int_entry(k).is_some_and(|n| n == key.1));
                        if let Some((_, v)) = existing {
                            if !value_strings_agree(v, &sel_val) {
                                return None;
                            }
                        } else if let Some(default) = &interp.default {
                            if !value_strings_agree(default, &sel_val) {
                                return None;
                            }
                        }
                    }
                }
                fresh.insert(key, sel_val);
            }
        }
        Some(fresh)
    }

    /// Step 0 (#w11-ite-sum): pin Bool ITE-condition variables inside select
    /// indices that the final model leaves UNVALUED (see module docs).
    ///
    /// Forced pins take the branch whose literal value matches the ITE
    /// term's committed LIA/EUF value; conditions with no committed match
    /// are searched over both polarities (capped at
    /// `MAX_FREE_ITE_COND_PINS`), keeping the first completion whose
    /// committed reads form a consistent cell map. On total failure every
    /// pin added here is removed again — behavior is then exactly the
    /// pre-pass status quo.
    ///
    /// Returns `true` iff pins were KEPT in `Model::bool_overrides` (the
    /// caller's post-mutation guard must then cover them).
    fn pin_unvalued_select_index_ite_conds(
        &mut self,
        selects: &[(TermId, TermId, TermId)],
    ) -> bool {
        let Some(model) = self.last_model.as_ref() else {
            return false;
        };

        // Only act when at least one select index fails to evaluate — never
        // touch a model whose indices are already fully valued.
        let mut blocked_indices: Vec<TermId> = Vec::new();
        for &(_, _, idx) in selects {
            if !matches!(self.evaluate_term(model, idx), EvalValue::Rational(_)) {
                blocked_indices.push(idx);
            }
        }
        if blocked_indices.is_empty() {
            return false;
        }

        // Collect unvalued Bool-Var ITE conditions (with literal-distinct
        // branches) beneath the blocked indices.
        let mut forced: Vec<(TermId, bool)> = Vec::new();
        let mut free: Vec<TermId> = Vec::new();
        let mut seen: HashSet<TermId> = HashSet::default();
        let mut cond_seen: HashSet<TermId> = HashSet::default();
        let mut stack: Vec<TermId> = blocked_indices;
        while let Some(t) = stack.pop() {
            if !seen.insert(t) {
                continue;
            }
            match self.ctx.terms.get(t) {
                TermData::App(_, args) => stack.extend(args.iter().copied()),
                TermData::Not(inner) => stack.push(*inner),
                TermData::Ite(c, a, b) => {
                    let (c, a, b) = (*c, *a, *b);
                    stack.push(a);
                    stack.push(b);
                    if matches!(self.ctx.terms.sort(t), Sort::Int)
                        && matches!(self.ctx.terms.get(c), TermData::Var(..))
                        && matches!(self.ctx.terms.sort(c), Sort::Bool)
                        && matches!(self.evaluate_term(model, c), EvalValue::Unknown)
                        && cond_seen.insert(c)
                    {
                        let then_val = match self.evaluate_term(model, a) {
                            EvalValue::Rational(v) if v.is_integer() => Some(v.to_integer()),
                            _ => None,
                        };
                        let else_val = match self.evaluate_term(model, b) {
                            EvalValue::Rational(v) if v.is_integer() => Some(v.to_integer()),
                            _ => None,
                        };
                        let committed = committed_value_string(&self.ctx.terms, model, t)
                            .and_then(|s| parse_int_entry(&s));
                        match (then_val, else_val) {
                            (Some(tv), Some(ev)) if tv != ev => {
                                if committed.as_ref() == Some(&tv) {
                                    forced.push((c, true));
                                } else if committed.as_ref() == Some(&ev) {
                                    forced.push((c, false));
                                } else {
                                    free.push(c);
                                }
                            }
                            // Branches unvalued or equal: polarity is
                            // unconstrained by the committed value — search.
                            _ => free.push(c),
                        }
                    }
                }
                _ => {}
            }
        }
        if forced.is_empty() && free.is_empty() {
            return false;
        }
        if free.len() > MAX_FREE_ITE_COND_PINS {
            return false;
        }
        // Deterministic candidate order.
        forced.sort_unstable_by_key(|&(c, _)| c);
        free.sort_unstable();

        for mask in 0u32..(1u32 << free.len()) {
            {
                let Some(model) = self.last_model.as_mut() else {
                    return false;
                };
                for &(c, v) in &forced {
                    model.bool_overrides.insert(c, v);
                }
                for (i, &c) in free.iter().enumerate() {
                    model.bool_overrides.insert(c, (mask >> i) & 1 == 1);
                }
            }
            let Some(model) = self.last_model.as_ref() else {
                return false;
            };
            if self.collect_committed_read_cells(model, selects).is_some() {
                return true; // keep this completion's pins
            }
        }

        // No completion yields consistent committed reads: remove every pin
        // added here (the conditions were unvalued before, so removal
        // restores the exact prior state) and keep today's behavior.
        let Some(model) = self.last_model.as_mut() else {
            return false;
        };
        for &(c, _) in &forced {
            model.bool_overrides.remove(&c);
        }
        for &c in &free {
            model.bool_overrides.remove(&c);
        }
        false
    }
}
