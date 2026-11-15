// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The order in which the model-true ground array definitions are built, and
//! which built definitions may be published.
//!
//! A definition reads other arrays: its store base, an array an operand
//! selects from, an array stored as a nested value. Built in source order, a
//! definition listed before the definition of an array it reads sees that
//! array still withheld (a nested-only definition) or still holding its
//! select-derived entry, which the later definition then replaces. The first
//! case withholds a definition whose every cell is known; the second builds an
//! interpretation that disagrees with the array it was built from. So a
//! definition waits until every definition of each array it reads has been
//! attempted. A cycle falls back to source order, which is the old behaviour.
//!
//! Every interpretation built here is published only while it agrees with
//! what the model publishes for what it read:
//!
//! * two definitions of one variable that build different arrays cannot both
//!   hold in the published model; at least one was built over a guessed cell
//!   (a free base's default, a partial select-derived entry). The variable is
//!   withheld, exactly as two disagreeing committed reads withhold it, instead
//!   of letting the later one silently win. Agreeing definitions publish the
//!   latest, as before. Two defaults that differ agree only over a fully
//!   stored domain;
//! * a definition that reads its own variable, `(= w (store u i (select w
//!   j)))`, read the interpretation it then replaces. It is published only as
//!   a fixpoint: every cell of `w` it read must be unchanged in the new
//!   interpretation;
//! * a definition asserted unconditionally (at the top level or as a conjunct
//!   of a top-level `and`) must build the model's value of `(default w)` as
//!   its default when there is one: model completion re-derives every
//!   unconditional definition against that value and taints `w`, its base
//!   and its stores on disagreement (`model/completion.rs`, the directed
//!   definition fixpoint). A built default is its base's else-value, which is
//!   the model's own value, or the one this definition passes down to a base
//!   without one (`model_defaults.rs`); so this withholds only a definition
//!   over a base whose own `(default u)` disagrees with `(default w)`. Before
//!   the base took that value every free base built `#x00` and this rule had
//!   to be confined to self-reading definitions, the one class that resolved
//!   no earlier;
//! * a definition whose read array was published again later (only possible
//!   in a dependency cycle) was built from a value the model no longer
//!   publishes.
//!
//! Each case withholds the variable. Withholding is the fail-closed direction:
//! the gate then treats the variable as opaque instead of judging cells built
//! over a guess. (A definition that read an array withheld for another reason
//! stays as before: that array keeps the read-conflict oracle armed.)

use super::*;

/// One pass over the collected definitions.
#[derive(Default)]
struct DefinitionPass {
    fully_resolved: Vec<(TermId, TermId)>,
    failed: HashSet<TermId>,
    /// The interpretation each variable's latest agreeing definition built.
    built: HashMap<TermId, ArrayInterpretation>,
    /// The `(var, definition)` equalities asserted unconditionally.
    unconditional: HashSet<(TermId, TermId)>,
    /// Sequence number of each variable's first publication (a later,
    /// agreeing definition publishes the same array).
    published_at: HashMap<TermId, usize>,
    /// Every successful definition: its variable, its sequence number, the
    /// other arrays it read, and the `(index, value)` cells of its own
    /// variable it read.
    reads: Vec<DefinitionReads>,
    sequence: usize,
}

struct DefinitionReads {
    var: TermId,
    sequence: usize,
    arrays: Vec<TermId>,
    own_cells: Vec<(String, String)>,
}

impl Executor {
    /// Build every collected `(var, definition, base)` in dependency order.
    ///
    /// Returns the definitions that resolved completely, as
    /// `(var, store_chain_base)` pairs, and the variables with at least one
    /// definition that did not resolve, or that disagrees with what the model
    /// publishes. Each definition is attempted exactly once; only the order
    /// changes.
    pub(super) fn resolve_ground_definitions(
        terms: &TermStore,
        bv_model: &BvModel,
        assertions: &[TermId],
        store_defs: &[(TermId, TermId, TermId)],
        array_model: &mut ArrayModel,
    ) -> (Vec<(TermId, TermId)>, HashSet<TermId>) {
        let mut unattempted: HashMap<TermId, usize> = HashMap::default();
        for &(var_id, _, _) in store_defs {
            *unattempted.entry(var_id).or_default() += 1;
        }
        let reads: Vec<Vec<TermId>> = store_defs
            .iter()
            .map(|&(var_id, definition, base)| {
                let mut reads = Self::ground_definition_array_reads(terms, definition);
                reads.push(base);
                reads.retain(|read| *read != var_id && unattempted.contains_key(read));
                reads
            })
            .collect();

        let mut pass = DefinitionPass {
            unconditional: Self::unconditional_ground_definitions(terms, assertions),
            ..DefinitionPass::default()
        };
        let mut queue: Vec<usize> = (0..store_defs.len()).collect();
        while !queue.is_empty() {
            let waiting = queue.len();
            let mut deferred = Vec::new();
            for index in queue {
                if reads[index]
                    .iter()
                    .any(|read| unattempted.get(read).is_some_and(|&left| left > 0))
                {
                    deferred.push(index);
                    continue;
                }
                Self::attempt_ground_definition(
                    terms,
                    bv_model,
                    store_defs[index],
                    array_model,
                    &mut pass,
                );
                if let Some(left) = unattempted.get_mut(&store_defs[index].0) {
                    *left -= 1;
                }
            }
            if deferred.len() == waiting {
                // A dependency cycle: nothing became ready. Attempt the rest
                // in source order, exactly as the single ordered pass did.
                for index in deferred {
                    Self::attempt_ground_definition(
                        terms,
                        bv_model,
                        store_defs[index],
                        array_model,
                        &mut pass,
                    );
                }
                break;
            }
            queue = deferred;
        }
        Self::withhold_stale_definitions(array_model, &mut pass);
        (pass.fully_resolved, pass.failed)
    }

    /// Build one definition and record its outcome.
    fn attempt_ground_definition(
        terms: &TermStore,
        bv_model: &BvModel,
        (var_id, store_term, base_array): (TermId, TermId, TermId),
        array_model: &mut ArrayModel,
        pass: &mut DefinitionPass,
    ) {
        pass.sequence += 1;
        let interp = (terms.sort(var_id) == terms.sort(store_term))
            .then(|| Self::ground_definition_interp(terms, bv_model, store_term, array_model))
            .flatten();
        let Some(interp) = interp else {
            // An unresolved `const-array` default leaves the variable as it
            // was before this walk recognised const arrays: it neither lifts
            // nor poisons: the variable keeps its entry for the gate to judge,
            // or the withholding of a sort the select scans skip.
            // An unresolved store chain still withholds.
            if !matches!(terms.get(store_term), TermData::App(sym, _) if sym.name() == "const-array")
            {
                pass.failed.insert(var_id);
                array_model.read_conflicted.insert(var_id);
            }
            return;
        };
        // Read back before publishing: the cells of `var_id` this definition
        // read are those of the interpretation it is about to replace.
        let own_cells =
            Self::definition_own_cells(terms, bv_model, var_id, store_term, array_model);
        pass.reads.push(DefinitionReads {
            var: var_id,
            sequence: pass.sequence,
            arrays: Self::ground_definition_array_reads(terms, store_term)
                .into_iter()
                .chain(matches!(terms.get(base_array), TermData::Var(_, _)).then_some(base_array))
                .filter(|&array| array != var_id)
                .collect(),
            own_cells,
        });
        pass.fully_resolved.push((var_id, base_array));
        let disputed_default = pass.unconditional.contains(&(var_id, store_term))
            && !Self::default_matches_model(terms, bv_model, var_id, &interp);
        if disputed_default
            || pass
                .built
                .get(&var_id)
                .is_some_and(|previous| !Self::same_definition_interp(previous, &interp))
        {
            pass.failed.insert(var_id);
            array_model.read_conflicted.insert(var_id);
            return;
        }
        // Of agreeing definitions the latest is published, as before this
        // check; a reader of an earlier one read the same array.
        pass.published_at.entry(var_id).or_insert(pass.sequence);
        pass.built.insert(var_id, interp.clone());
        array_model.array_values.insert(var_id, interp);
        array_model.read_conflicted.remove(&var_id);
    }

    /// Withhold every published definition built from a value the model no
    /// longer publishes: a read array published after it, or one of its own
    /// cells that the new interpretation changed. Withholding publishes
    /// nothing, so one pass reaches every such definition.
    fn withhold_stale_definitions(array_model: &mut ArrayModel, pass: &mut DefinitionPass) {
        for reads in &pass.reads {
            let stale_array = reads.arrays.iter().any(|array| {
                pass.published_at
                    .get(array)
                    .is_some_and(|&published| published > reads.sequence)
            });
            let stale_cell = reads.own_cells.iter().any(|(index, value)| {
                Self::interpretation_cell(array_model.array_values.get(&reads.var), index)
                    != Some(value.as_str())
            });
            if stale_array || stale_cell {
                pass.failed.insert(reads.var);
                array_model.read_conflicted.insert(reads.var);
            }
        }
    }

    /// The `(var, definition)` ground array definitions asserted at the top
    /// level or as a conjunct of a top-level `and`, in either orientation.
    fn unconditional_ground_definitions(
        terms: &TermStore,
        assertions: &[TermId],
    ) -> HashSet<(TermId, TermId)> {
        let mut unconditional = HashSet::default();
        let mut seen: HashSet<TermId> = HashSet::default();
        let mut top: Vec<TermId> = assertions.to_vec();
        while let Some(term) = top.pop() {
            if !seen.insert(term) {
                continue;
            }
            match terms.get(term) {
                TermData::App(sym, args) if sym.name() == "and" => top.extend(args.iter().copied()),
                TermData::App(sym, args) if sym.name() == "=" && args.len() == 2 => {
                    for (var, definition) in [(args[0], args[1]), (args[1], args[0])] {
                        if matches!(terms.get(var), TermData::Var(_, _))
                            && matches!(terms.sort(var), Sort::Array(_))
                            && Self::is_array_ground_definition(terms, definition)
                        {
                            unconditional.insert((var, definition));
                        }
                    }
                }
                _ => {}
            }
        }
        unconditional
    }

    /// The `(index, value)` cells of `var` that `(select var i)` reads inside
    /// `definition` see under the current model. A read whose index or cell
    /// does not resolve contributed no value to a definition that built, so it
    /// is skipped.
    fn definition_own_cells(
        terms: &TermStore,
        bv_model: &BvModel,
        var: TermId,
        definition: TermId,
        array_model: &mut ArrayModel,
    ) -> Vec<(String, String)> {
        let Sort::Array(sort) = terms.sort(var) else {
            return Vec::new();
        };
        let Sort::BitVec(index_sort) = &sort.index_sort else {
            return Vec::new();
        };
        let width = index_sort.width;
        let mut cells = Vec::new();
        let mut memo = BvEvalMemo::default();
        for (array, index) in Self::definition_array_selects(terms, definition) {
            if array != var {
                continue;
            }
            Self::seed_definition_operand_leaves(terms, bv_model, index, array_model, &mut memo);
            let Some(key) = Self::store_chain_operand_value(terms, bv_model, index, &mut memo)
            else {
                continue;
            };
            let Some(value) = Self::definition_operand_read_value(
                terms,
                bv_model,
                var,
                index,
                array_model,
                &mut memo,
            ) else {
                continue;
            };
            cells.push((format_bitvec(&key, width), value));
        }
        cells
    }

    /// `interp`'s cell at `index`: its store there, else its default.
    pub(super) fn interpretation_cell<'a>(
        interp: Option<&'a ArrayInterpretation>,
        index: &str,
    ) -> Option<&'a str> {
        let interp = interp?;
        interp
            .stores
            .iter()
            .find(|(key, _)| key == index)
            .map(|(_, value)| value.as_str())
            .or(interp.default.as_deref())
    }

    /// Whether `interp`'s default is the model's value of `(default var)`,
    /// when that term exists and has one.
    fn default_matches_model(
        terms: &TermStore,
        bv_model: &BvModel,
        var: TermId,
        interp: &ArrayInterpretation,
    ) -> bool {
        // A value no cell can render matches no built default.
        Self::model_array_default_value(terms, bv_model, var).is_none_or(|value| {
            value.is_some_and(|value| interp.default.as_deref() == Some(value.as_str()))
        })
    }

    /// Whether two built interpretations denote the same array: the same
    /// sorts and the same cell at every index. Outside their stores both read
    /// their defaults, so differing defaults agree only when the stores cover
    /// the whole (BV) index domain.
    fn same_definition_interp(lhs: &ArrayInterpretation, rhs: &ArrayInterpretation) -> bool {
        if lhs.index_sort != rhs.index_sort || lhs.element_sort != rhs.element_sort {
            return false;
        }
        let keys: HashSet<&str> = lhs
            .stores
            .iter()
            .chain(&rhs.stores)
            .map(|(key, _)| key.as_str())
            .collect();
        if keys.iter().any(|key| {
            Self::interpretation_cell(Some(lhs), key) != Self::interpretation_cell(Some(rhs), key)
        }) {
            return false;
        }
        lhs.default == rhs.default
            || matches!(&lhs.index_sort, Some(Sort::BitVec(bv))
                if bv.width < 64 && keys.len() as u64 == 1u64 << bv.width)
    }

    /// The `(array, index)` of every `(select array index)` over an array
    /// variable inside `definition`, at most 4096 nodes deep into it.
    fn definition_array_selects(terms: &TermStore, definition: TermId) -> Vec<(TermId, TermId)> {
        Self::bounded_definition_subterms(terms, definition)
            .into_iter()
            .filter_map(|term| match terms.get(term) {
                TermData::App(sym, args)
                    if sym.name() == "select"
                        && args.len() == 2
                        && matches!(terms.get(args[0]), TermData::Var(_, _)) =>
                {
                    Some((args[0], args[1]))
                }
                _ => None,
            })
            .collect()
    }

    /// The array variables a definition term mentions: an ordering hint, and
    /// the reads a published definition depends on. A truncated walk can only
    /// fall back towards source order, and can only miss a read in a cycle,
    /// the one case where a read array is published after its reader.
    fn ground_definition_array_reads(terms: &TermStore, definition: TermId) -> Vec<TermId> {
        Self::bounded_definition_subterms(terms, definition)
            .into_iter()
            .filter(|&term| {
                matches!(terms.get(term), TermData::Var(_, _))
                    && matches!(terms.sort(term), Sort::Array(_))
            })
            .collect()
    }

    /// The distinct subterms of `definition`, at most 4096 of them.
    fn bounded_definition_subterms(terms: &TermStore, definition: TermId) -> Vec<TermId> {
        const MAX_NODES: usize = 4096;
        let mut seen: HashSet<TermId> = HashSet::default();
        let mut order = Vec::new();
        let mut stack = vec![definition];
        while let Some(term) = stack.pop() {
            if seen.len() >= MAX_NODES || !seen.insert(term) {
                continue;
            }
            order.push(term);
            match terms.get(term) {
                TermData::App(_, args) => stack.extend(args.iter().copied()),
                TermData::Not(inner) => stack.push(*inner),
                TermData::Ite(cond, then_term, else_term) => {
                    stack.extend([*cond, *then_term, *else_term]);
                }
                _ => {}
            }
        }
        order
    }
}

#[cfg(test)]
#[path = "definition_completeness_tests.rs"]
mod tests;

#[cfg(test)]
#[path = "definition_agreement_tests.rs"]
mod agreement_tests;

#[cfg(test)]
#[path = "model_defaults_tests.rs"]
mod default_tests;

#[cfg(test)]
#[path = "nested_reads_tests.rs"]
mod nested_read_tests;
