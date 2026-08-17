// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Model extraction and LIA state preservation for TheoryCombiner.
//!
//! Separated from `combiner.rs` for file-size compliance (#6332 Wave 0).

// Wave 1: TheoryCombiner now used in production dispatch (#6332).

// #8529: Use deterministic hash sets in all builds.
use ay_arrays::ArrayModel;
use ay_core::kani_compat::DetHashSet as HashSet;
use ay_core::TermId;
use ay_core::TheoryConflict;
use ay_euf::EufModel;
use ay_lia::{DiophState, HnfCutKey, LiaModel, LiaSolver, StoredCut};
use ay_lra::LraModel;

use super::combiner::TheoryCombiner;
use super::models::{euf_with_int_values, extract_array_model, merge_lia_values, merge_lra_values};

impl TheoryCombiner<'_> {
    // --- Model extraction ---

    pub(crate) fn scope_euf_model_to_roots(&mut self, roots: &[TermId]) {
        self.euf.scope_model_to_roots(roots);
    }

    pub(crate) fn clear_euf_model_scope(&mut self) {
        self.euf.clear_model_scope();
    }

    pub(crate) fn extract_euf_lra_models(&mut self) -> (EufModel, LraModel) {
        let euf_model = euf_with_int_values(&mut self.euf);
        let lra_model = self
            .lra
            .as_mut()
            .expect("extract_euf_lra_models requires LRA")
            .extract_model();
        (euf_model, lra_model)
    }

    pub(crate) fn extract_euf_lia_models_with_lia_value_filter_and_fixup(
        &mut self,
        assertions: &[TermId],
        keep_lia_value: impl Fn(TermId) -> bool,
        fixup: impl FnOnce(&ay_core::TermStore, &mut EufModel, &mut Option<LiaModel>),
    ) -> (EufModel, Option<LiaModel>) {
        let mut euf_model = euf_with_int_values(&mut self.euf);
        let mut lia_model = self
            .lia
            .as_mut()
            .expect("extract_euf_lia_models requires LIA")
            .extract_model();
        if let Some(model) = lia_model.as_mut() {
            model.values.retain(|term, _| keep_lia_value(*term));
        }
        // Recovery must precede the one authoritative merge.  A caller may
        // restore variables eliminated by preprocessing, repair opaque
        // applications, or recompute arithmetic composites; merging before
        // that fixup leaves both EUF value views stale for every restored key.
        fixup(self.terms, &mut euf_model, &mut lia_model);
        merge_lia_values(&mut euf_model, lia_model.as_ref());
        let reunify_protected =
            crate::pipeline_fns::collect_top_level_arith_diseq_vars(self.terms, assertions);
        self.reunify_lia_values_across_euf_classes(
            &mut euf_model,
            lia_model.as_mut(),
            &reunify_protected,
            assertions,
        );
        #[cfg(debug_assertions)]
        let lia_value_count = lia_model.as_ref().map_or(0, |m| m.values.len());
        #[cfg(debug_assertions)]
        debug_assert!(
            euf_model.term_values.len() >= lia_value_count,
            "BUG: UFLIA combiner EUF model has {} values, fewer than LIA model's {} values",
            euf_model.term_values.len(),
            lia_value_count
        );
        (euf_model, lia_model)
    }

    /// AUFLIA model extraction with a caller-supplied LIA model fixup that
    /// runs BEFORE LIA values are merged into the EUF term-value map and
    /// before the array model is extracted from that map (#A1 / #8373).
    ///
    /// The executor uses the fixup to (1) recover variable values eliminated
    /// by `VariableSubstitution`, (2) recompute Int composites the EUF model
    /// covered with speculative values, and (3) restore opaque-select read
    /// congruence — so the array interpretation strings produced by
    /// `extract_array_model` reflect the FINAL variable assignment instead of
    /// a pre-recovery snapshot.
    pub(crate) fn extract_all_models_auflia_with_lia_fixup(
        &mut self,
        assertions: &[TermId],
        mut fixup: impl FnMut(&ay_core::TermStore, &mut EufModel, &mut Option<LiaModel>),
    ) -> (EufModel, ArrayModel, Option<LiaModel>) {
        let mut euf_model = euf_with_int_values(&mut self.euf);
        let mut lia_model = self.lia.as_mut().and_then(|l| l.extract_model());
        fixup(self.terms, &mut euf_model, &mut lia_model);
        merge_lia_values(&mut euf_model, lia_model.as_ref());
        let reunify_protected =
            crate::pipeline_fns::collect_top_level_arith_diseq_vars(self.terms, assertions);
        if ay_core::misc_cli_flags().debug_class_merge {
            eprintln!(
                "[class-merge-dbg] protected={:?}",
                reunify_protected.iter().map(|t| t.0).collect::<Vec<_>>()
            );
        }
        self.reunify_lia_values_across_euf_classes(
            &mut euf_model,
            lia_model.as_mut(),
            &reunify_protected,
            assertions,
        );
        // #A1 chain member: the class-merge repairs above can MOVE an opaque
        // select's value again (pass-1 winner adoption / pass-2 fresh-shift
        // over a stale diseq edge), re-breaking the read congruence the fixup
        // closure just reconciled (observed: `(select Q (+ B1 (* 4 R)))`
        // reconciled to -1, shifted to -3, while `(select Q G)` stayed 0 —
        // the committed reads then disagree on one cell, the materialization
        // pass fails closed and a genuine `sat` degrades to unknown, which
        // escalates into the diverging axiom-expanded re-solve). Re-run the
        // recovery/reconciliation fixpoint on the POST-class-merge values and
        // re-merge, so array extraction sees a read-congruent valuation.
        // Candidate-model repair only: the strict + independent gates still
        // decide acceptance downstream.
        fixup(self.terms, &mut euf_model, &mut lia_model);
        merge_lia_values(&mut euf_model, lia_model.as_ref());
        #[cfg(debug_assertions)]
        let lia_value_count = lia_model.as_ref().map_or(0, |m| m.values.len());
        #[cfg(debug_assertions)]
        debug_assert!(
            euf_model.term_values.len() >= lia_value_count,
            "BUG: AUFLIA combiner EUF model has {} values, fewer than LIA model's {} values",
            euf_model.term_values.len(),
            lia_value_count
        );
        let arrays = self
            .arrays
            .as_mut()
            .expect("extract_all_models_auflia requires arrays");
        let array_model = extract_array_model(arrays, &euf_model);
        (euf_model, array_model, lia_model)
    }

    /// Re-unify LIA-merged values across EUF equivalence classes
    /// (#qf-auflia-class-merge).
    ///
    /// `euf_with_int_values` assigns one value per e-class, but
    /// `merge_lia_values` then overwrites PER TERM from `lia.values` — and the
    /// LIA model can value two EUF-EQUAL terms differently when their equality
    /// is EUF-owned and never became a LIA constraint (the skolemized-
    /// extensionality `_pp_` shape: `(= e_0 (select a2 i1))` leaves the opaque
    /// select registered in LIA as a FREE variable defaulted to 0 while e_0 is
    /// constrained to -1). The materialized model then contradicts the asserted
    /// equality, array extraction bakes the wrong select value into the interp,
    /// and the strict validation gate (correctly) rejects the model — degrading
    /// a genuine `sat` to `unknown`.
    ///
    /// Repair: group the merged Int values by EUF class representative; when a
    /// class carries more than one distinct value, adopt a single winner for
    /// the whole class — preferring a non-application term's value (a Var like
    /// `e_0` carries real LIA constraints; an opaque `select`/UF application's
    /// LIA entry is a registration shadow). Every scoped Int peer in the class
    /// is written back to `lia.values` and BOTH EUF value maps so array
    /// extraction, evaluators, and UF-table lookup see one valuation.
    /// Terms asserted EUF-equal MUST agree in any satisfying model, so
    /// unification never makes a correct model wrong; it repairs exactly the
    /// materializations that were internally contradictory.
    fn reunify_lia_values_across_euf_classes(
        &mut self,
        euf_model: &mut EufModel,
        lia_model: Option<&mut LiaModel>,
        protected: &ay_core::kani_compat::DetHashSet<TermId>,
        assertions: &[TermId],
    ) {
        use ay_core::kani_compat::{DetHashMap, DetHashSet};
        use ay_core::term::TermData;
        use ay_core::{Constant, Sort};
        let Some(lia) = lia_model else {
            return;
        };

        fn current_int_value(
            lia: &LiaModel,
            euf: &EufModel,
            term: TermId,
        ) -> Option<num_bigint::BigInt> {
            lia.values
                .get(&term)
                .or_else(|| euf.int_values.get(&term))
                .cloned()
        }

        // LIA keys identify classes that actually need cross-theory repair;
        // the union with scoped EUF numeric keys supplies every peer that must
        // receive the chosen class value.  EUF-only speculative values never
        // become winner authority merely by being present in the model.
        let lia_sources: DetHashSet<TermId> = lia.values.keys().copied().collect();
        let mut candidates = lia_sources.clone();
        candidates.extend(euf_model.int_values.keys().copied());
        let mut by_rep: DetHashMap<u32, Vec<TermId>> = DetHashMap::default();
        for term in candidates {
            if (term.0 as usize) >= self.euf.num_terms()
                || !matches!(self.terms.sort(term), Sort::Int)
            {
                continue;
            }
            by_rep
                .entry(self.euf.enode_find_const(term.0))
                .or_default()
                .push(term);
        }
        for members in by_rep.values_mut() {
            members.sort_unstable_by_key(|term| term.0);
            members.dedup();
        }

        for members in by_rep.values() {
            if !members.iter().any(|term| lia_sources.contains(term)) {
                continue;
            }
            // A complete known-disequality audit is quadratic.  Large classes
            // must fail closed instead of bypassing the audit and being
            // unified optimistically.
            if members.len() > 128 {
                continue;
            }
            // A sound e-class can never contain BOTH endpoints of an asserted
            // disequality; seeing >= 2 protected members means the extraction-
            // time find() state merged by SPECULATIVE VALUE, not by congruence
            // (observed: one 60-member blob holding every element var). Any
            // unification over such a blob manufactures collisions — skip.
            let protected_count = members
                .iter()
                .filter(|&&term| protected.contains(&term))
                .count();
            let has_known_disequal_pair = members.iter().enumerate().any(|(index, &lhs)| {
                members[index + 1..].iter().copied().any(|rhs| {
                    self.euf.are_known_disequal(lhs, rhs) || self.euf.are_known_disequal(rhs, lhs)
                })
            });
            if protected_count >= 2 || has_known_disequal_pair {
                continue;
            }

            // An e-class containing an Int constant is pinned to that immutable
            // value.  Conflicting constants indicate an inconsistent candidate
            // state; skip repair and let validation fail closed.
            let mut constant_value: Option<num_bigint::BigInt> = None;
            let mut conflicting_constants = false;
            for &member in members {
                if let TermData::Const(Constant::Int(value)) = self.terms.get(member) {
                    if constant_value.as_ref().is_some_and(|old| old != value) {
                        conflicting_constants = true;
                        break;
                    }
                    constant_value = Some(value.clone());
                }
            }
            if conflicting_constants {
                continue;
            }

            // Otherwise prefer a protected LIA value, then a non-application
            // LIA value, then any LIA value.  Never let an EUF-only speculative
            // completion override a repaired LIA class member.
            let winner_term = members
                .iter()
                .copied()
                .find(|m| lia_sources.contains(m) && protected.contains(m))
                .or_else(|| {
                    members.iter().copied().find(|m| {
                        lia_sources.contains(m)
                            && !matches!(self.terms.get(*m), TermData::App(_, _))
                    })
                })
                .or_else(|| members.iter().copied().find(|m| lia_sources.contains(m)));
            let winner_val = if let Some(value) = constant_value {
                value
            } else if let Some(winner_term) = winner_term {
                let Some(value) = current_int_value(lia, euf_model, winner_term) else {
                    continue;
                };
                value
            } else {
                continue;
            };
            if ay_core::misc_cli_flags().debug_class_merge
                && members.iter().any(|m| protected.contains(m))
            {
                eprintln!(
                    "[class-merge-dbg] class members={:?} val={winner_val}",
                    members.iter().map(|t| t.0).collect::<Vec<_>>(),
                );
            }
            let winner_str = crate::executor_format::format_bigint(&winner_val);
            for &m in members {
                lia.values.insert(m, winner_val.clone());
                euf_model.int_values.insert(m, winner_val.clone());
                euf_model.term_values.insert(m, winner_str.clone());
            }
        }

        // Pass 2 (#qf-auflia-class-merge): separate SAME-VALUED terms that EUF
        // knows are disequal. Free Int element variables (different classes,
        // pairwise-distinct via EUF-owned diseqs that never became LIA
        // constraints) all default to the same LIA value (0), overwriting the
        // per-class DISTINCT speculative integers `euf_with_int_values` chose —
        // so the arithmetic oracle rejects '(not (= e_17 e_18))' and degrades
        // a genuine sat. Shift the later member of each known-disequal
        // same-value pair to a fresh integer beyond every value in use. Move a
        // whole equivalence class at once: shifting only one peer would undo
        // pass 1's equality repair.
        // Fail-closed either way: validation re-checks every assertion under
        // the adjusted values, so a shift that breaks a REAL constraint leaves
        // the verdict degraded exactly as before, while a shift that repairs a
        // shadow-default collision lets a correct sat validate.
        struct ClassValue {
            members: Vec<TermId>,
            constant_pinned: bool,
            protected: bool,
            has_lia_source: bool,
        }

        let mut classes: DetHashMap<u32, ClassValue> = DetHashMap::default();
        let mut by_value: DetHashMap<num_bigint::BigInt, Vec<u32>> = DetHashMap::default();
        for (&rep, members) in &by_rep {
            let mut class_value = None;
            let mut inconsistent = false;
            for &member in members {
                let Some(value) = current_int_value(lia, euf_model, member) else {
                    continue;
                };
                if class_value.as_ref().is_some_and(|old| old != &value) {
                    inconsistent = true;
                    break;
                }
                class_value = Some(value);
            }
            let Some(value) = class_value else { continue };
            if inconsistent {
                continue;
            }
            let class = ClassValue {
                members: members.clone(),
                constant_pinned: members.iter().any(|&member| {
                    matches!(self.terms.get(member), TermData::Const(Constant::Int(_)))
                }),
                protected: members.iter().any(|member| protected.contains(member)),
                has_lia_source: members.iter().any(|member| lia_sources.contains(member)),
            };
            classes.insert(rep, class);
            by_value.entry(value).or_default().push(rep);
        }

        // #A1 stale-diseq move guard (#qf-auflia-class-merge, follow-up): an
        // EUF "known disequal" edge can be CANDIDATE-STATE GARBAGE — e.g. an
        // array index-disequality lemma derived from a stale read pair that
        // the LIA-side recovery has since reconciled (gate-over-select shape:
        // `x = base + 8*i` with `i = 0` forces `x = base`, yet the e-graph
        // still carries `x != base` from an intermediate round). Trusting such
        // an edge and fresh-shifting the class breaks an ORIGINAL equality
        // that currently HOLDS under the final values, manufacturing exactly
        // the definitive-false the strict gate then rejects (a genuine sat
        // degrades to unknown). A class whose member occurs in an original
        // Int equality that HOLDS under the current values is therefore
        // move-pinned: shifting it can only break that equality. The genuine
        // shadow-default repairs this pass exists for (free element vars /
        // UF results pairwise-distinct via EUF-owned diseqs) involve terms
        // that are NOT pinned by any holding original equality, so they keep
        // moving exactly as before. Fail-closed either way: validation still
        // re-checks every assertion under whatever values ship.
        let holding_eq_pinned: DetHashSet<TermId> = {
            fn eval_int(
                terms: &ay_core::TermStore,
                lia: &LiaModel,
                euf: &EufModel,
                term: TermId,
                depth: usize,
            ) -> Option<num_bigint::BigInt> {
                if let TermData::Const(Constant::Int(value)) = terms.get(term) {
                    return Some(value.clone());
                }
                if let Some(value) = lia.values.get(&term) {
                    return Some(value.clone());
                }
                if let Some(value) = euf.int_values.get(&term) {
                    return Some(value.clone());
                }
                if depth == 0 {
                    return None;
                }
                match terms.get(term) {
                    TermData::App(symbol, args) => {
                        let vals: Option<Vec<num_bigint::BigInt>> = args
                            .iter()
                            .map(|&arg| eval_int(terms, lia, euf, arg, depth - 1))
                            .collect();
                        let vals = vals?;
                        match symbol.name() {
                            "+" => Some(vals.into_iter().sum()),
                            "*" => Some(vals.into_iter().product()),
                            "-" => match vals.len() {
                                1 => Some(-vals[0].clone()),
                                2 => Some(vals[0].clone() - vals[1].clone()),
                                _ => None,
                            },
                            _ => None,
                        }
                    }
                    _ => None,
                }
            }
            fn collect_int_vars(
                terms: &ay_core::TermStore,
                term: TermId,
                out: &mut DetHashSet<TermId>,
            ) {
                match terms.get(term) {
                    TermData::Var(_, _) => {
                        if matches!(terms.sort(term), Sort::Int) {
                            out.insert(term);
                        }
                    }
                    TermData::App(_, args) => {
                        for &arg in args.to_vec().iter() {
                            collect_int_vars(terms, arg, out);
                        }
                    }
                    _ => {}
                }
            }
            let mut pinned = DetHashSet::default();
            for &assertion in assertions {
                let TermData::App(symbol, args) = self.terms.get(assertion) else {
                    continue;
                };
                if symbol.name() != "=" || args.len() != 2 {
                    continue;
                }
                let (lhs, rhs) = (args[0], args[1]);
                if !matches!(self.terms.sort(lhs), Sort::Int) {
                    continue;
                }
                let (Some(lv), Some(rv)) = (
                    eval_int(self.terms, lia, euf_model, lhs, 8),
                    eval_int(self.terms, lia, euf_model, rhs, 8),
                ) else {
                    continue;
                };
                if lv == rv {
                    collect_int_vars(self.terms, lhs, &mut pinned);
                    collect_int_vars(self.terms, rhs, &mut pinned);
                }
            }
            pinned
        };

        let mut used_values: DetHashSet<num_bigint::BigInt> =
            lia.values.values().cloned().collect();
        used_values.extend(euf_model.int_values.values().cloned());
        let mut next_fresh = used_values
            .iter()
            .map(|v| v.magnitude().clone())
            .max()
            .map(|m| num_bigint::BigInt::from(m) + 1)
            .unwrap_or_else(|| num_bigint::BigInt::from(1));
        for (_val, mut group) in by_value {
            if group.len() < 2 || group.len() > 128 {
                continue; // huge same-value groups: not the shadow-default shape
            }
            group.sort_unstable_by_key(|rep| {
                let class = &classes[rep];
                (
                    !class.constant_pinned,
                    !class.protected,
                    !class.has_lia_source,
                    *rep,
                )
            });
            if ay_core::misc_cli_flags().debug_class_merge {
                let mut pairs: Vec<String> = Vec::new();
                for i in 0..group.len() {
                    for j in (i + 1)..group.len() {
                        let (a, b) = (group[i], group[j]);
                        pairs.push(format!(
                            "({},{})={}",
                            a,
                            b,
                            self.euf.are_known_disequal(TermId(a), TermId(b))
                        ));
                    }
                }
                eprintln!("[class-merge-dbg] value={_val} group={group:?} diseq={pairs:?}");
            }
            // Keep the highest-authority class at this value; move any
            // lower-authority known-disequal class as a unit.
            let mut kept: Vec<u32> = Vec::new();
            for rep in group {
                let clashes = kept.iter().any(|&kept_rep| {
                    self.euf.are_known_disequal(TermId(kept_rep), TermId(rep))
                        || self.euf.are_known_disequal(TermId(rep), TermId(kept_rep))
                });
                if clashes {
                    let class = &classes[&rep];
                    if class.constant_pinned {
                        // Constants are immutable. Leave the inconsistent
                        // candidate visible for fail-closed validation.
                        kept.push(rep);
                        continue;
                    }
                    if class
                        .members
                        .iter()
                        .any(|member| holding_eq_pinned.contains(member))
                    {
                        // Move-pinned (#A1 stale-diseq guard above): shifting
                        // this class would break an original Int equality that
                        // HOLDS under the current values — the "disequality"
                        // driving the shift is stale candidate state, not a
                        // constraint of the formula. Keep the values; the
                        // validation gates decide acceptance.
                        kept.push(rep);
                        continue;
                    }
                    while used_values.contains(&next_fresh) {
                        next_fresh += 1;
                    }
                    let fresh = next_fresh.clone();
                    used_values.insert(fresh.clone());
                    next_fresh += 1;
                    let fresh_str = crate::executor_format::format_bigint(&fresh);
                    for &member in &class.members {
                        lia.values.insert(member, fresh.clone());
                        euf_model.int_values.insert(member, fresh.clone());
                        euf_model.term_values.insert(member, fresh_str.clone());
                    }
                } else {
                    kept.push(rep);
                }
            }
        }

        // Pass 3: restore UF congruence under the FINAL arithmetic values.
        // A table key may be mixed-sort; changing just one Int position can
        // make two formerly-distinct rows denote the same mathematical point.
        #[derive(Clone, PartialEq, Eq, Hash)]
        enum KeyAtom {
            Int(num_bigint::BigInt),
            Stable(String),
        }
        struct TableRow {
            table_name: String,
            row_index: usize,
            source: TermId,
            result_sort: Sort,
            value: String,
            hard_constant: Option<(String, TermId)>,
            hard_bool: Option<bool>,
            literal_arg_count: usize,
        }

        fn constant_atom(terms: &ay_core::TermStore, term: TermId) -> Option<String> {
            match terms.get(term) {
                TermData::Const(Constant::Bool(value)) => Some(value.to_string()),
                TermData::Const(Constant::Int(value)) => {
                    Some(crate::executor_format::format_bigint(value))
                }
                TermData::Const(Constant::Rational(value)) => {
                    Some(crate::executor_format::format_rational(&value.0))
                }
                TermData::Const(Constant::BitVec { value, width }) => {
                    Some(crate::executor_format::format_bitvec(value, *width))
                }
                TermData::Const(Constant::String(value)) => Some(ay_core::string_literal(value)),
                _ => None,
            }
        }

        let mut hard_bool_pins: DetHashMap<TermId, bool> = DetHashMap::default();
        let mut hard_stack = assertions.to_vec();
        while let Some(term) = hard_stack.pop() {
            match self.terms.get(term) {
                TermData::App(symbol, args) if symbol.name() == "and" => {
                    hard_stack.extend(args.iter().copied());
                }
                TermData::Not(inner) if matches!(self.terms.sort(*inner), Sort::Bool) => {
                    hard_bool_pins.insert(*inner, false);
                }
                _ if matches!(self.terms.sort(term), Sort::Bool) => {
                    hard_bool_pins.insert(term, true);
                }
                _ => {}
            }
        }

        let placeholder_term = |raw: &str| {
            raw.strip_prefix("@?")
                .and_then(|text| text.parse::<u32>().ok())
                .map(TermId)
                .filter(|term| (term.0 as usize) < self.terms.len())
        };
        let final_int_value = |term: TermId, lia: &LiaModel, euf: &EufModel| {
            if let TermData::Const(Constant::Int(value)) = self.terms.get(term) {
                Some(value.clone())
            } else {
                lia.values
                    .get(&term)
                    .or_else(|| euf.int_values.get(&term))
                    .cloned()
            }
        };

        let mut collisions: DetHashMap<(String, Vec<KeyAtom>), Vec<TableRow>> =
            DetHashMap::default();
        for (table_name, table) in &euf_model.function_tables {
            let Some(source_terms) = euf_model.function_table_terms.get(table_name) else {
                continue;
            };
            if source_terms.len() != table.len() {
                euf_model
                    .function_table_conflicts
                    .insert(table_name.clone());
                continue;
            }
            for (row_index, ((raw_args, raw_result), &source)) in
                table.iter().zip(source_terms).enumerate()
            {
                let TermData::App(_, source_args) = self.terms.get(source) else {
                    continue;
                };
                if source_args.len() != raw_args.len() {
                    euf_model
                        .function_table_conflicts
                        .insert(table_name.clone());
                    continue;
                }
                let mut key = Vec::with_capacity(raw_args.len());
                let mut has_int = false;
                let mut literal_arg_count = 0usize;
                let mut complete = true;
                for (&arg, raw_arg) in source_args.iter().zip(raw_args) {
                    if matches!(self.terms.sort(arg), Sort::Int) {
                        let Some(value) = final_int_value(arg, lia, euf_model) else {
                            complete = false;
                            break;
                        };
                        has_int = true;
                        literal_arg_count += usize::from(matches!(
                            self.terms.get(arg),
                            TermData::Const(Constant::Int(_))
                        ));
                        key.push(KeyAtom::Int(value));
                    } else {
                        let atom = placeholder_term(raw_arg)
                            .and_then(|term| euf_model.term_values.get(&term).cloned())
                            .unwrap_or_else(|| raw_arg.clone());
                        key.push(KeyAtom::Stable(atom));
                    }
                }
                if !complete || !has_int {
                    continue;
                }
                let result_sort = self.terms.sort(source).clone();
                let int_value = matches!(result_sort, Sort::Int)
                    .then(|| final_int_value(source, lia, euf_model))
                    .flatten();
                let value = match &result_sort {
                    Sort::Int => int_value
                        .as_ref()
                        .map(crate::executor_format::format_bigint)
                        .unwrap_or_else(|| raw_result.clone()),
                    Sort::Uninterpreted(_) => euf_model
                        .term_values
                        .get(&source)
                        .cloned()
                        .unwrap_or_else(|| raw_result.clone()),
                    _ => raw_result.clone(),
                };
                let class_int_constant = matches!(result_sort, Sort::Int)
                    .then(|| self.euf.find_int_const_in_class(source))
                    .flatten()
                    .map(|(value, term)| (crate::executor_format::format_bigint(&value), term));
                let mapped_constant = euf_model
                    .func_app_const_terms
                    .get(&source)
                    .copied()
                    .and_then(|term| constant_atom(self.terms, term).map(|value| (value, term)));
                collisions
                    .entry((table_name.clone(), key))
                    .or_default()
                    .push(TableRow {
                        table_name: table_name.clone(),
                        row_index,
                        source,
                        result_sort,
                        value,
                        hard_constant: class_int_constant.or(mapped_constant),
                        hard_bool: hard_bool_pins.get(&source).copied(),
                        literal_arg_count,
                    });
            }
        }

        for rows in collisions.values_mut() {
            if rows.len() < 2 || rows.iter().all(|row| row.value == rows[0].value) {
                continue;
            }
            let table_name = rows[0].table_name.clone();
            let result_sort = rows[0].result_sort.clone();
            let mut hard_values: DetHashSet<String> = rows
                .iter()
                .filter_map(|row| row.hard_constant.as_ref().map(|(value, _)| value.clone()))
                .collect();
            hard_values.extend(
                rows.iter()
                    .filter_map(|row| row.hard_bool.map(|value| value.to_string())),
            );
            let known_disequal_results = matches!(
                result_sort,
                Sort::Uninterpreted(_) | Sort::Array(_) | Sort::Seq(_)
            ) && rows.iter().enumerate().any(|(index, lhs)| {
                rows[index + 1..].iter().any(|rhs| {
                    self.euf.are_known_disequal(lhs.source, rhs.source)
                        || self.euf.are_known_disequal(rhs.source, lhs.source)
                })
            });
            // #A1 (#8373 gate-over-select class): two rows of one table whose
            // keys coincide under the FINAL arithmetic values are congruent
            // applications, so their results MUST be equal in any consistent
            // model. For Array-sorted results — `store` rows duplicated by
            // AUFLIA preprocessing in pre-/post-substitution form — the row
            // "values" are opaque e-class tokens; unifying them onto one
            // representative is the same congruence restoration this pass
            // performs for scalars. Seq-returning UF rows use the same opaque
            // e-class-token representation and are repairable for the same
            // reason. This is NOT a choice between conflicting evidence
            // (contradictory hard pins and known-disequal results are excluded
            // by the guards above and keep the fail-closed conflict marker).
            // Downstream array extraction then builds ONE interpretation for
            // the unified class, and the strict + independent validation gates
            // still decide acceptance fail-closed. Before this arm, such rows
            // were conflict-marked and the outer witness sweep discarded the
            // whole model, degrading a genuine `sat` to `unknown` with
            // "No model available".
            let directly_repairable = matches!(
                result_sort,
                Sort::Bool
                    | Sort::Int
                    | Sort::Real
                    | Sort::BitVec(_)
                    | Sort::String
                    | Sort::Uninterpreted(_)
            ) || (matches!(result_sort, Sort::Array(_) | Sort::Seq(_))
                && hard_values.is_empty());
            if hard_values.len() > 1 || known_disequal_results || !directly_repairable {
                // A contradictory hard pin cannot be repaired by choosing one
                // side: doing so would erase evidence owned by the other row.
                // Compound/non-atomic results likewise cannot be represented
                // faithfully in the scalar EUF table.  Record the conflict;
                // outer witness completion consumes this marker by discarding
                // the candidate model, so the public SAT funnel fails closed.
                if ay_core::misc_cli_flags().f1_diag {
                    fn fmt_term(terms: &ay_core::TermStore, t: TermId, depth: usize) -> String {
                        if depth == 0 {
                            return format!("#{}", t.0);
                        }
                        match terms.get(t) {
                            TermData::App(sym, args) => format!(
                                "({} {})",
                                sym.name(),
                                args.iter()
                                    .map(|&a| fmt_term(terms, a, depth - 1))
                                    .collect::<Vec<_>>()
                                    .join(" ")
                            ),
                            TermData::Const(c) => format!("{c:?}"),
                            TermData::Var(name, _) => name.clone(),
                            other => format!("{other:?}"),
                        }
                    }
                    eprintln!(
                        "--f1-diag: table {table_name:?} conflict-marked: hard_values={hard_values:?} \
                         known_disequal={known_disequal_results} repairable={directly_repairable}"
                    );
                    for row in rows.iter() {
                        eprintln!(
                            "--f1-diag:   deep src={}",
                            fmt_term(self.terms, row.source, 6)
                        );
                    }
                    for row in rows.iter() {
                        eprintln!(
                            "--f1-diag:   row src={:?} ({:?}) value={:?} hard_const={:?} hard_bool={:?}",
                            row.source,
                            self.terms.get(row.source),
                            row.value,
                            row.hard_constant,
                            row.hard_bool,
                        );
                    }
                }
                euf_model.function_table_conflicts.insert(table_name);
                continue;
            }

            rows.sort_unstable_by_key(|row| {
                (
                    row.hard_constant.is_none() && row.hard_bool.is_none(),
                    std::cmp::Reverse(row.literal_arg_count),
                    row.source.0,
                    row.row_index,
                )
            });
            let winner_value = rows[0]
                .hard_constant
                .as_ref()
                .map(|(value, _)| value.clone())
                .or_else(|| rows[0].hard_bool.map(|value| value.to_string()))
                .unwrap_or_else(|| rows[0].value.clone());
            let winner_constant = rows[0].hard_constant.as_ref().map(|(_, term)| *term);
            let winner_int = matches!(result_sort, Sort::Int)
                .then(|| {
                    rows.iter().find_map(|row| {
                        if row.value == winner_value {
                            final_int_value(row.source, lia, euf_model)
                        } else {
                            None
                        }
                    })
                })
                .flatten();

            for row in rows {
                let rep = self.euf.enode_find_const(row.source.0);
                let mut peers: Vec<TermId> = euf_model
                    .term_values
                    .keys()
                    .copied()
                    .filter(|term| {
                        (term.0 as usize) < self.euf.num_terms()
                            && self.euf.enode_find_const(term.0) == rep
                    })
                    .collect();
                peers.push(row.source);
                peers.sort_unstable_by_key(|term| term.0);
                peers.dedup();
                for peer in peers {
                    euf_model.term_values.insert(peer, winner_value.clone());
                    if let Some(value) = winner_int.as_ref() {
                        lia.values.insert(peer, value.clone());
                        euf_model.int_values.insert(peer, value.clone());
                    }
                    if matches!(self.terms.get(peer), TermData::App(_, _)) {
                        if let Some(constant) = winner_constant {
                            euf_model.func_app_const_terms.insert(peer, constant);
                        } else {
                            euf_model.func_app_const_terms.remove(&peer);
                        }
                    }
                }
                if let Some(table) = euf_model.function_tables.get_mut(&row.table_name) {
                    table[row.row_index].1 = winner_value.clone();
                }
            }
        }
    }

    pub(crate) fn extract_all_models_auflra(&mut self) -> (EufModel, ArrayModel, LraModel) {
        let mut euf_model = euf_with_int_values(&mut self.euf);
        let lra = self
            .lra
            .as_mut()
            .expect("extract_all_models_auflra requires LRA");
        let lra_model = lra.extract_model();
        merge_lra_values(&mut euf_model, &lra_model, self.terms);
        #[cfg(debug_assertions)]
        let lra_value_count = lra_model.values.len();
        #[cfg(debug_assertions)]
        debug_assert!(
            euf_model.term_values.len() >= lra_value_count,
            "BUG: AUFLRA combiner EUF model has {} values, fewer than LRA model's {} values",
            euf_model.term_values.len(),
            lra_value_count
        );
        let arrays = self
            .arrays
            .as_mut()
            .expect("extract_all_models_auflra requires arrays");
        let array_model = extract_array_model(arrays, &euf_model);
        (euf_model, array_model, lra_model)
    }

    pub(crate) fn extract_euf_array_models(&mut self) -> (EufModel, ArrayModel) {
        let euf_model = euf_with_int_values(&mut self.euf);
        let arrays = self
            .arrays
            .as_mut()
            .expect("extract_euf_array_models requires arrays");
        let array_model = extract_array_model(arrays, &euf_model);
        (euf_model, array_model)
    }

    // --- LIA state preservation ---

    pub(crate) fn take_learned_state(&mut self) -> Option<(Vec<StoredCut>, HashSet<HnfCutKey>)> {
        self.lia.as_mut().map(LiaSolver::take_learned_state)
    }

    pub(crate) fn import_learned_state(&mut self, cuts: Vec<StoredCut>, seen: HashSet<HnfCutKey>) {
        if let Some(lia) = &mut self.lia {
            lia.import_learned_state(cuts, seen);
        }
    }

    pub(crate) fn take_dioph_state(&mut self) -> Option<DiophState> {
        self.lia.as_mut().map(LiaSolver::take_dioph_state)
    }

    pub(crate) fn import_dioph_state(&mut self, state: DiophState) {
        if let Some(lia) = &mut self.lia {
            lia.import_dioph_state(state);
        }
    }

    pub(crate) fn replay_learned_cuts(&mut self) {
        if let Some(lia) = &mut self.lia {
            lia.replay_learned_cuts();
        }
        if let Some(lra) = &mut self.lra {
            lra.replay_learned_cuts();
        }
    }

    pub(crate) fn lra_solver(&self) -> &Self {
        self
    }

    pub(crate) fn collect_all_bound_conflicts(&self, skip_first: bool) -> Vec<TheoryConflict> {
        let mut conflicts = if let Some(lia) = &self.lia {
            lia.collect_all_bound_conflicts(skip_first)
        } else {
            Vec::new()
        };

        let lra_skip_first = skip_first && conflicts.is_empty();
        if let Some(lra) = &self.lra {
            conflicts.extend(lra.collect_all_bound_conflicts(lra_skip_first));
        }

        conflicts
    }
}
