// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Array reads, index identification and cell pins of the `_BV_LIA_INDEP`
//! final-assignment reconciliation — the value-level half of
//! `bv_lia_indep_reconcile` (whose module docs carry the ownership rule, the
//! pinning discipline and the soundness argument).

use ay_core::kani_compat::{DetHashMap as HashMap, DetHashSet as HashSet};
use ay_core::term::TermData;
use ay_core::{Sort, TermId};
use num_bigint::BigInt;

use super::super::{EvalValue, Executor, Model};

/// One collected read over a BitVec-indexed array: the `select` term, its
/// array argument, its index.
pub(super) type ArrayRead = (TermId, TermId, TermId);

/// The final value of one array cell.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(super) enum CellValue {
    Bool(bool),
    BitVec { value: BigInt, width: u32 },
}

impl CellValue {
    /// The interpretation-entry spelling (`true`/`false`, `#x..`/`#b..`).
    fn entry_string(&self) -> String {
        match self {
            Self::Bool(b) => if *b { "true" } else { "false" }.to_string(),
            Self::BitVec { value, width } => crate::executor_format::format_bitvec(value, *width),
        }
    }
}

/// One pinned cell: `(base array var, index value)` with its final value.
pub(super) type CellPin = ((TermId, BigInt), CellValue);

impl Executor {
    /// `select` applications over BitVec-indexed arrays with Bool or BitVec
    /// elements reachable from `roots`, in deterministic order.
    pub(super) fn collect_bv_array_reads(&self, roots: &[TermId]) -> Vec<ArrayRead> {
        let mut reads: Vec<ArrayRead> = Vec::new();
        let mut seen: HashSet<TermId> = HashSet::default();
        let mut stack: Vec<TermId> = roots.to_vec();
        while let Some(t) = stack.pop() {
            if !seen.insert(t) {
                continue;
            }
            match self.ctx.terms.get(t) {
                TermData::App(sym, args) => {
                    if sym.name() == "select"
                        && args.len() == 2
                        && matches!(self.ctx.terms.sort(t), Sort::Bool | Sort::BitVec(_))
                        && matches!(self.ctx.terms.sort(args[1]), Sort::BitVec(_))
                    {
                        reads.push((t, args[0], args[1]));
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
        reads.sort_unstable();
        reads.dedup();
        reads
    }

    /// Walk `array` through its `store` chain under the merged model to the
    /// base array VARIABLE that a read at `index_val` reaches. `None` when the
    /// read hits a store key (ROW-forced; left to the validators), when a
    /// store key cannot be evaluated, or when the chain ends in anything but
    /// a variable (const arrays, ITEs, ...).
    fn resolve_bv_store_chain_base(
        &self,
        merged: &Model,
        array: TermId,
        index_val: &BigInt,
    ) -> Option<TermId> {
        let mut current = array;
        let mut visited: HashSet<TermId> = HashSet::default();
        loop {
            if !visited.insert(current) {
                return None;
            }
            match self.ctx.terms.get(current) {
                TermData::Var(_, _) => {
                    return matches!(
                        self.ctx.terms.sort(current),
                        Sort::Array(arr) if matches!(arr.index_sort, Sort::BitVec(_))
                            && matches!(arr.element_sort, Sort::Bool | Sort::BitVec(_))
                    )
                    .then_some(current);
                }
                TermData::App(sym, args) if sym.name() == "store" && args.len() == 3 => {
                    let EvalValue::BitVec { value, .. } = self.evaluate_term(merged, args[1])
                    else {
                        return None;
                    };
                    if &value == index_val {
                        return None;
                    }
                    current = args[0];
                }
                _ => return None,
            }
        }
    }

    /// BitVec-sorted index variables the BV lane never related to other bits
    /// that the final assignment's EUF model committed to a BitVec literal,
    /// with that literal, where the BV lane's value differs.
    pub(super) fn final_index_literal_updates(
        &self,
        merged: &Model,
        final_assignment: &Model,
        roots: &[TermId],
    ) -> Vec<(TermId, BigInt)> {
        let Some(bv_model) = merged.bv_model.as_ref() else {
            return Vec::new();
        };
        let (index_vars, bv_constrained) = self.index_vars_and_bv_constrained_vars(merged, roots);
        index_vars
            .into_iter()
            .filter(|var| !bv_constrained.contains(var))
            .filter_map(|var| {
                let value = self.final_bv_literal(final_assignment, var)?;
                (bv_model.values.get(&var) != Some(&value)).then_some((var, value))
            })
            .collect()
    }

    /// Partition the BitVec variables: those occurring as the index of a
    /// `select` or the key of a `store` over a BitVec-indexed array anywhere
    /// in the roots (`index_vars`, sorted), and those the BV LANE actually
    /// bit-blasted in relation to other bits (`bv_constrained`): variables
    /// occurring outside such an index/key position inside a BV predicate
    /// atom of the BV lane's SAT layer or inside a BV term the BV lane
    /// valued. The roots are consulted only for index positions — after the
    /// AUFLIA cross-check they are that lane's rewritten window and may carry
    /// atoms (ROW splits, extensionality Skolems) the BV lane never saw, so
    /// they cannot say what the BV lane constrained.
    fn index_vars_and_bv_constrained_vars(
        &self,
        merged: &Model,
        roots: &[TermId],
    ) -> (Vec<TermId>, HashSet<TermId>) {
        let mut index_vars: HashSet<TermId> = HashSet::default();
        let mut seen: HashSet<TermId> = HashSet::default();
        let mut stack: Vec<TermId> = roots.to_vec();
        while let Some(t) = stack.pop() {
            if !seen.insert(t) {
                continue;
            }
            match self.ctx.terms.get(t) {
                TermData::App(sym, args) => {
                    let index_position = match sym.name() {
                        "select" if args.len() == 2 => Some(args[1]),
                        "store" if args.len() == 3 => Some(args[1]),
                        _ => None,
                    };
                    if let Some(index) = index_position {
                        if matches!(self.ctx.terms.get(index), TermData::Var(_, _))
                            && matches!(self.ctx.terms.sort(index), Sort::BitVec(_))
                        {
                            index_vars.insert(index);
                        }
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
        let mut bv_constrained: HashSet<TermId> = HashSet::default();
        let mut bv_lane_terms: Vec<TermId> = merged
            .term_to_var
            .keys()
            .copied()
            .filter(|&atom| {
                let TermData::App(sym, args) = self.ctx.terms.get(atom) else {
                    return false;
                };
                matches!(self.ctx.terms.sort(atom), Sort::Bool)
                    && args
                        .first()
                        .is_some_and(|&a| matches!(self.ctx.terms.sort(a), Sort::BitVec(_)))
                    && Self::is_known_theory_symbol(sym.name())
            })
            .collect();
        if let Some(bv_model) = merged.bv_model.as_ref() {
            bv_lane_terms.extend(
                bv_model
                    .values
                    .keys()
                    .copied()
                    .filter(|&t| !matches!(self.ctx.terms.get(t), TermData::Var(_, _))),
            );
        }
        bv_lane_terms.sort_unstable();
        bv_lane_terms.dedup();
        for t in bv_lane_terms {
            self.collect_bv_vars_outside_index_positions(t, &mut bv_constrained);
        }
        let mut index_vars: Vec<TermId> = index_vars.into_iter().collect();
        index_vars.sort_unstable();
        (index_vars, bv_constrained)
    }

    /// BitVec variables reachable from `term` through any position except a
    /// `select` index / `store` key (the operands the BV lane's bit-blaster
    /// actually relates to other bits).
    fn collect_bv_vars_outside_index_positions(&self, term: TermId, out: &mut HashSet<TermId>) {
        let mut seen: HashSet<TermId> = HashSet::default();
        let mut stack: Vec<TermId> = vec![term];
        while let Some(t) = stack.pop() {
            if !seen.insert(t) {
                continue;
            }
            match self.ctx.terms.get(t) {
                TermData::Var(_, _) => {
                    if matches!(self.ctx.terms.sort(t), Sort::BitVec(_)) {
                        out.insert(t);
                    }
                }
                TermData::App(sym, args) => {
                    let skip = match sym.name() {
                        "select" if args.len() == 2 => Some(1),
                        "store" if args.len() == 3 => Some(1),
                        _ => None,
                    };
                    stack.extend(
                        args.iter()
                            .enumerate()
                            .filter(|(i, _)| Some(*i) != skip)
                            .map(|(_, &a)| a),
                    );
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
    }

    /// The final assignment's value for one read: the atom value for a
    /// Bool-element read, the EUF literal for a BitVec-element read.
    fn final_read_value(&self, final_assignment: &Model, sel: TermId) -> Option<CellValue> {
        match self.ctx.terms.sort(sel) {
            Sort::Bool => self
                .final_bool_value(final_assignment, sel)
                .map(CellValue::Bool),
            Sort::BitVec(bv) => {
                self.final_bv_literal(final_assignment, sel)
                    .map(|value| CellValue::BitVec {
                        value,
                        width: bv.width,
                    })
            }
            _ => None,
        }
    }

    /// The value the merged witness already carries for each root read this
    /// pass cannot LOCATE — its index does not evaluate to a BitVec literal,
    /// so the pass cannot say which cell the read answers from — paired with
    /// every base array variable the read reaches.
    ///
    /// No cell of such a base may be pinned to a DIFFERENT value. Model
    /// COMPLETION closes the open index downstream and can land the read on
    /// ANY cell of the arrays it reads through; a cell this pass pinned to
    /// the other lane's value then decides the read against the value the
    /// witness carries for it, and the strict oracle refuses a witness the
    /// ladder had already accepted. Measured on `isweep/min/m_04_0124.smt2`
    /// (reduced from `gq2/iabvx/iabvx_0104_named.smt2`): the BV lane values no
    /// `k0`, so `(select S0 (bvadd k0 #x00000002))` is unlocatable and keeps
    /// that lane's `true`, while `(select S0 #x00000005)` pinned cell 5 to
    /// `false`; completion closes `k0 := 0` and the assertion tying the two
    /// reads together is then read off two cells the pass itself put out of
    /// agreement. Base and z3 answer `sat`; the pass degraded it to
    /// `unknown (incomplete)`.
    ///
    /// Pins that AGREE with the carried value stay: wherever completion lands
    /// the read, the cell then says exactly what the witness already said, so
    /// the pass introduces no disagreement it did not find. A cell it leaves
    /// alone keeps the BV lane's own value, exactly as before this pass ran.
    /// Reads whose index IS a literal are unaffected — a ROW-forced chain is
    /// decided by the store's own value term, and a located read is decided
    /// by the cell it pins.
    ///
    /// Every array variable reachable from the read's array term is paired,
    /// so an `ite` over two bases constrains both; a read over a const array
    /// reaches none and constrains nothing. A read the witness carries NO
    /// value for constrains nothing either: completion reads it out of
    /// whichever cell it lands on, and no second value exists to disagree.
    pub(super) fn unlocatable_read_values(
        &self,
        merged: &Model,
        reads: &[ArrayRead],
    ) -> Vec<(TermId, CellValue)> {
        let mut out: Vec<(TermId, CellValue)> = Vec::new();
        for &(sel, array, index) in reads {
            if matches!(self.evaluate_term(merged, index), EvalValue::BitVec { .. }) {
                continue;
            }
            let Some(carried) = self.merged_read_cell_value(merged, sel) else {
                continue;
            };
            let mut seen: HashSet<TermId> = HashSet::default();
            let mut stack: Vec<TermId> = vec![array];
            while let Some(t) = stack.pop() {
                if !seen.insert(t) {
                    continue;
                }
                if matches!(self.ctx.terms.get(t), TermData::Var(_, _))
                    && matches!(self.ctx.terms.sort(t), Sort::Array(_))
                {
                    out.push((t, carried.clone()));
                }
                stack.extend(self.ctx.terms.children(t));
            }
        }
        out.sort_unstable_by(|a, b| a.0.cmp(&b.0));
        out.dedup();
        out
    }

    /// The value the merged witness carries for the read `sel`, read out of
    /// the layers the BV lane itself writes: the SAT assignment, the BV
    /// model's Bool overrides / term values, and the model-level Bool
    /// overrides. `None` when nothing in the witness values it.
    fn merged_read_cell_value(&self, merged: &Model, sel: TermId) -> Option<CellValue> {
        match self.ctx.terms.sort(sel) {
            Sort::Bool => {
                let bv_override = merged
                    .bv_model
                    .as_ref()
                    .and_then(|bv| bv.bool_overrides.get(&sel).copied());
                self.term_value(&merged.sat_model, &merged.term_to_var, sel)
                    .or(bv_override)
                    .or_else(|| merged.bool_overrides.get(&sel).copied())
                    .map(CellValue::Bool)
            }
            Sort::BitVec(bv) => merged
                .bv_model
                .as_ref()
                .and_then(|m| m.values.get(&sel))
                .map(|value| CellValue::BitVec {
                    value: value.clone(),
                    width: bv.width,
                }),
            _ => None,
        }
    }

    /// Cells pinned by the final assignment, keyed by `(base, index value)`,
    /// in first-seen order, skipping every cell whose base carries an
    /// unlocatable read valued otherwise (see
    /// [`Self::unlocatable_read_values`]). `None` when two final reads of one
    /// cell disagree (fail closed: the caller mutates nothing).
    pub(super) fn pin_cells_from_final_assignment(
        &self,
        merged: &Model,
        final_assignment: &Model,
        reads: &[ArrayRead],
        unlocatable: &[(TermId, CellValue)],
    ) -> Option<Vec<CellPin>> {
        let mut pins: HashMap<(TermId, BigInt), CellValue> = HashMap::default();
        let mut order: Vec<(TermId, BigInt)> = Vec::new();
        for &(sel, array, index) in reads {
            let Some(val) = self.final_read_value(final_assignment, sel) else {
                continue;
            };
            let EvalValue::BitVec { value: idx_val, .. } = self.evaluate_term(merged, index) else {
                continue;
            };
            let Some(base) = self.resolve_bv_store_chain_base(merged, array, &idx_val) else {
                continue;
            };
            if unlocatable
                .iter()
                .any(|(open, carried)| *open == base && *carried != val)
            {
                continue;
            }
            let key = (base, idx_val);
            match pins.get(&key) {
                Some(existing) if *existing != val => return None,
                Some(_) => {}
                None => {
                    pins.insert(key.clone(), val);
                    order.push(key);
                }
            }
        }
        Some(
            order
                .into_iter()
                .map(|key| {
                    let val = pins[&key].clone();
                    (key, val)
                })
                .collect(),
        )
    }

    /// Overwrite the BV lane's value of every pinned cell in the merged model
    /// (BV `bool_overrides`/`values`, SAT assignment, array interpretation).
    /// `reads` are the root reads the pins were derived from. Returns whether
    /// anything changed.
    pub(super) fn apply_cell_pins(
        &self,
        merged: &mut Model,
        pins: &[CellPin],
        reads: &[ArrayRead],
    ) -> bool {
        let (bool_updates, bv_updates) = self.pinned_read_updates(merged, pins, reads);
        let mut changed = false;
        if let Some(bv_model) = merged.bv_model.as_mut() {
            for &(sel, val) in &bool_updates {
                if bv_model.bool_overrides.insert(sel, val) != Some(val) {
                    changed = true;
                }
            }
        }
        changed |= Self::apply_atom_updates(merged, &bool_updates);
        changed |= self.apply_bv_value_updates(merged, &bv_updates);
        let contradicted =
            self.bases_whose_default_would_contradict_an_unresolved_read(merged, pins, reads);
        changed |= self.pin_cells_into_interpretations(merged, pins, &contradicted);
        changed
    }

    /// Base arrays for which CREATING an interpretation would answer a read
    /// this pass could not resolve — its index does not evaluate to a
    /// literal under the merged model, or its store chain is ROW-forced —
    /// with a value the witness already contradicts.
    ///
    /// An interpretation carries a TOTAL default (`false` / zero), so
    /// creating one for a base the BV lane extracted none for does not only
    /// pin the pinned cells: it also answers every unresolved read over that
    /// base, from a component the BV lane never had, overriding the value
    /// the witness already carries for it in the SAT assignment or the BV
    /// model. The read is unresolved here only because its index is still
    /// open; model COMPLETION closes that index downstream, and the
    /// fabricated default then decides the read against the value the
    /// candidate was accepted on. Measured on `sfz/q/abv2/abv_0475_named.smt2`
    /// (`(select S0 (bvadd k0 #x1))` valued `true`, with the BV lane valuing
    /// no `k0`): base and z3 answer `sat`, the created `default: false`
    /// interpretation makes the completed witness falsify the assertion, and
    /// the gate fail-closes a genuine `sat` to `unknown (incomplete)`.
    ///
    /// Only a CONTRADICTED read disqualifies the base, not merely an
    /// unresolved one: where the default agrees with the value the witness
    /// carries — or nothing carries one — the interpretation answers exactly
    /// what the model already said, and withholding it would cost verdicts
    /// (`sfz/q/abv/abv_0112_named.smt2`, `abv_0220_named.smt2`, both `sat`
    /// at base and under this pass, `unknown` under a blanket decline).
    ///
    /// For a disqualified base the pins stay in the layers the BV lane
    /// itself uses — the SAT assignment and the BV model's
    /// overrides/values, all written by the caller — which answer exactly
    /// the reads they pin and leave every other read to the BV lane. A base
    /// whose interpretation the BV lane already extracted is never listed:
    /// its default already governed those reads before this pass, so writing
    /// a pin into it fabricates nothing.
    fn bases_whose_default_would_contradict_an_unresolved_read(
        &self,
        merged: &Model,
        pins: &[CellPin],
        reads: &[ArrayRead],
    ) -> HashSet<TermId> {
        let mut out: HashSet<TermId> = HashSet::default();
        for &(sel, array, index) in reads {
            let Some(base) = self.syntactic_store_chain_base(array) else {
                continue;
            };
            if out.contains(&base)
                || merged
                    .array_model
                    .as_ref()
                    .is_some_and(|am| am.array_values.contains_key(&base))
            {
                continue;
            }
            let pinned = match self.evaluate_term(merged, index) {
                EvalValue::BitVec { value: idx_val, .. } => self
                    .resolve_bv_store_chain_base(merged, array, &idx_val)
                    .is_some_and(|resolved| {
                        pins.iter()
                            .any(|((b, i), _)| *b == resolved && *i == idx_val)
                    }),
                _ => false,
            };
            if !pinned && self.merged_read_value_contradicts_default(merged, sel) {
                out.insert(base);
            }
        }
        out
    }

    /// Whether the merged witness already carries a value for the read `sel`
    /// that a created interpretation's default (`false` for a Bool element,
    /// zero for a BitVec element) would contradict.
    fn merged_read_value_contradicts_default(&self, merged: &Model, sel: TermId) -> bool {
        match self.merged_read_cell_value(merged, sel) {
            Some(CellValue::Bool(b)) => b,
            Some(CellValue::BitVec { value, .. }) => value != BigInt::from(0u8),
            None => false,
        }
    }

    /// The base array VARIABLE `array` reaches through its `store` chain,
    /// read structurally (no model values, so an unevaluable store key does
    /// not hide the base). `None` when the chain ends in anything else.
    fn syntactic_store_chain_base(&self, array: TermId) -> Option<TermId> {
        let mut current = array;
        let mut visited: HashSet<TermId> = HashSet::default();
        loop {
            if !visited.insert(current) {
                return None;
            }
            match self.ctx.terms.get(current) {
                TermData::Var(_, _) => return Some(current),
                TermData::App(sym, args) if sym.name() == "store" && args.len() == 3 => {
                    current = args[0];
                }
                _ => return None,
            }
        }
    }

    /// Every `select` term the BV lane valued, plus every root read, whose
    /// index evaluates to a pinned cell, with the pinned value — including
    /// reads the roots do not mention — so no reader of the model sees the
    /// stale seed. Evaluates only (the evaluator borrows the model); the
    /// caller mutates.
    fn pinned_read_updates(
        &self,
        merged: &Model,
        pins: &[CellPin],
        reads: &[ArrayRead],
    ) -> (Vec<(TermId, bool)>, Vec<(TermId, BigInt)>) {
        let mut candidates: Vec<TermId> = reads.iter().map(|&(sel, _, _)| sel).collect();
        if let Some(bv_model) = merged.bv_model.as_ref() {
            candidates.extend(bv_model.bool_overrides.keys().copied());
            candidates.extend(bv_model.values.keys().copied());
        }
        candidates.sort_unstable();
        candidates.dedup();
        let mut bool_updates: Vec<(TermId, bool)> = Vec::new();
        let mut bv_updates: Vec<(TermId, BigInt)> = Vec::new();
        for sel in candidates {
            let TermData::App(sym, args) = self.ctx.terms.get(sel) else {
                continue;
            };
            if sym.name() != "select" || args.len() != 2 {
                continue;
            }
            let EvalValue::BitVec { value: idx_val, .. } = self.evaluate_term(merged, args[1])
            else {
                continue;
            };
            let Some(base) = self.resolve_bv_store_chain_base(merged, args[0], &idx_val) else {
                continue;
            };
            let Some((_, val)) = pins.iter().find(|((b, i), _)| *b == base && *i == idx_val) else {
                continue;
            };
            match (val, self.ctx.terms.sort(sel)) {
                (CellValue::Bool(b), Sort::Bool) => bool_updates.push((sel, *b)),
                (CellValue::BitVec { value, .. }, Sort::BitVec(_)) => {
                    bv_updates.push((sel, value.clone()));
                }
                _ => {}
            }
        }
        (bool_updates, bv_updates)
    }

    /// Write every pinned cell into its base array's interpretation. A base
    /// the BV lane extracted no interpretation for gets one of the
    /// extraction's own shape — unless it is listed in `skip_creation_for`
    /// (see [`Self::bases_whose_default_would_contradict_an_unresolved_read`]),
    /// whose pins stay
    /// in the BV lane's own layers so no fabricated default can decide a
    /// read this pass could not resolve (`extract_array_model_from_bv_model`: Bool
    /// elements default to `false`, BitVec elements to zero), so the pinned
    /// reads are readable by the array lookup and the gate; the validators
    /// still re-check every assertion against it. Returns whether anything
    /// changed.
    fn pin_cells_into_interpretations(
        &self,
        merged: &mut Model,
        pins: &[CellPin],
        skip_creation_for: &HashSet<TermId>,
    ) -> bool {
        let mut changed = false;
        let array_model = merged.array_model.get_or_insert_with(Default::default);
        for ((base, idx_val), val) in pins {
            if skip_creation_for.contains(base) && !array_model.array_values.contains_key(base) {
                continue;
            }
            let Sort::Array(arr_sort) = self.ctx.terms.sort(*base) else {
                continue;
            };
            let Sort::BitVec(idx_bv) = &arr_sort.index_sort else {
                continue;
            };
            let default = match &arr_sort.element_sort {
                Sort::Bool => "false".to_string(),
                Sort::BitVec(elem) => {
                    crate::executor_format::format_bitvec(&BigInt::from(0u8), elem.width)
                }
                _ => continue,
            };
            let interp = array_model.array_values.entry(*base).or_insert_with(|| {
                ay_arrays::ArrayInterpretation {
                    index_sort: Some(arr_sort.index_sort.clone()),
                    element_sort: Some(arr_sort.element_sort.clone()),
                    default: Some(default),
                    ..Default::default()
                }
            });
            let idx_str = crate::executor_format::format_bitvec(idx_val, idx_bv.width);
            let val_str = val.entry_string();
            let entries_at_index = interp.stores.iter().filter(|(i, _)| *i == idx_str).count();
            let already_pinned = entries_at_index == 1
                && interp
                    .stores
                    .iter()
                    .any(|(i, v)| *i == idx_str && *v == val_str);
            if already_pinned {
                continue;
            }
            interp.stores.retain(|(i, _)| *i != idx_str);
            interp.stores.insert(0, (idx_str, val_str));
            changed = true;
        }
        if array_model.array_values.is_empty() {
            merged.array_model = None;
        }
        changed
    }
}
