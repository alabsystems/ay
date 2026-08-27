// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Pass 3 of cross-theory model reunification: UF-table congruence under the
//! FINAL arithmetic values, and the fail-closed verdict for what cannot be
//! repaired.
//!
//! Split out of `combiner_models.rs` because `function_table_conflicts` is a
//! VERDICT ABOUT A VALUATION and the AUFLIA extraction path changes the
//! valuation again after the pass that reaches it returns. Its own file so it
//! can be re-run on the final values without dragging the class-merge passes
//! along — those may only run once (re-running them re-breaks the read
//! congruence the fixup closure restores).

use ay_core::TermId;
use ay_euf::EufModel;
use ay_lia::LiaModel;

use super::combiner::TheoryCombiner;

impl TheoryCombiner<'_> {
    /// Restore UF congruence under the FINAL arithmetic values, and
    /// conflict-mark the collisions that cannot be repaired.
    ///
    /// A table key may be mixed-sort; changing just one Int position can make
    /// two formerly-distinct rows denote the same mathematical point.
    ///
    /// THE SOLE PRODUCER of `EufModel::function_table_conflicts` — no other
    /// site in the workspace inserts into it, which is what makes clearing the
    /// set before a re-run an exact retraction of this pass's own provisional
    /// verdict rather than a loss of evidence.
    pub(super) fn restore_uf_congruence_under_final_values(
        &self,
        euf_model: &mut EufModel,
        lia: &mut LiaModel,
        assertions: &[TermId],
    ) {
        use ay_core::kani_compat::{DetHashMap, DetHashSet};
        use ay_core::term::TermData;
        use ay_core::{Constant, Sort};
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
                // #A1 stale-pin guard (sibling of the stale-diseq move guard):
                // a class constant CONTRADICTED by the row's own FINAL
                // arithmetic value is stale candidate state — an internal
                // solve-time pin atom (`(= (select ..) c)`) the reconciliation
                // fixpoints have already overridden — not semantic evidence
                // about the model being extracted. Counting it as a hard pin
                // conflict-marks the table and discards the whole model,
                // degrading genuine `sat` to unknown. Dropping it here only
                // widens what the congruence repair may ATTEMPT; the strict +
                // independent validation gates still decide acceptance
                // fail-closed, so an authored pin the final valuation really
                // violates still ends in rejection, never a false SAT.
                let final_value_str = matches!(result_sort, Sort::Int)
                    .then(|| {
                        int_value
                            .as_ref()
                            .map(crate::executor_format::format_bigint)
                    })
                    .flatten();
                let stale_pin_filter = |pin: &(String, TermId)| match &final_value_str {
                    Some(final_value) => pin.0 == *final_value,
                    None => true,
                };
                collisions
                    .entry((table_name.clone(), key))
                    .or_default()
                    .push(TableRow {
                        table_name: table_name.clone(),
                        row_index,
                        source,
                        result_sort,
                        value,
                        hard_constant: class_int_constant
                            .or(mapped_constant)
                            .filter(stale_pin_filter),
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
}
