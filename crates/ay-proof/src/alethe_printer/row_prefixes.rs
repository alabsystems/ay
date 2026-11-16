// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Proof-local names for long, closed BV-array ROW paths. The original clause
//! and every assumption keep their existing rendering. Names occur only in
//! intermediate ROW steps and are bridged back to the raw read explicitly.

use super::*;
use crate::checker::RowChainEnd;

// These are refusal bounds for this optional printer, not larger grants to a
// solver/checker or the existing inline fallback. Small paths keep their text.
const MIN_SKIPS: usize = 16;
const MAX_NODES: usize = 4096;
const MAX_DEPTH: usize = 128;
const MAX_RAW_BYTES: usize = 1024 * 1024;
const MAX_TEXT: usize = 2 * 1024 * 1024;
const NONCES: usize = 32;
const MAX_NAME_ENTRIES: usize = 1 << 20;
const MAX_NAME_BYTES: usize = 8 * 1024 * 1024;

struct Prefixes {
    names: HashMap<TermId, String>,
    raw: HashMap<TermId, String>,
    definitions: Vec<String>,
}

struct Text<'p, 'a> {
    printer: &'p AlethePrinter<'a>,
    lines: Vec<String>,
    bytes: usize,
}

impl Text<'_, '_> {
    // Callers admit their construction bound before formatting. Appending is
    // a separate real copy, including the final copy into the parent's vector.
    fn admit(&self, bytes: usize) -> Option<()> {
        (self.bytes.checked_add(bytes)? <= MAX_TEXT).then_some(())?;
        self.printer.admit_emission_work(bytes as u64).then_some(())
    }

    fn push(&mut self, line: String) -> Option<()> {
        self.admit(line.len().checked_add(1)?)?;
        self.bytes = self.bytes.checked_add(line.len().checked_add(1)?)?;
        self.lines.push(line);
        Some(())
    }
}

impl AlethePrinter<'_> {
    pub(super) fn emit_shared_row_chain_path(
        &self,
        guards: &RowChainGuards,
        emission: &RowChainPathEmission<'_>,
        destination: &mut Vec<String>,
    ) -> Option<RowChainPathProof> {
        let RowChainPathEmission {
            prefix,
            read_index,
            index_str,
            path,
            tail,
        } = emission;
        if path.skips.len() < MIN_SKIPS || !self.anchor_binder_names.borrow().is_empty() {
            return None;
        }
        let mut text = Text {
            printer: self,
            lines: Vec::new(),
            bytes: 0,
        };
        let plan = self.row_prefix_plan(prefix, path.root, &mut text)?;
        let root = plan.raw.get(&path.root)?;
        let root_name = plan.names.get(&path.root)?;
        let mut current = path.root;
        let mut steps = Vec::new();
        for (position, skip) in path.skips.iter().enumerate() {
            let [inner, key, _] = self.row_store_parts(skip.outer)?;
            if current != skip.outer || inner != skip.inner || key != skip.store_index {
                return None;
            }
            let outer = plan.names.get(&skip.outer)?;
            let inner = plan
                .names
                .get(&skip.inner)
                .or_else(|| plan.raw.get(&skip.inner))?;
            text.admit(guards.order.len().checked_mul(8)?)?;
            let guard_position = guards.order.iter().position(|&g| g == skip.guard)?;
            let unit = guards.row_ids.get(guard_position)?;
            let step = format!("{prefix}{position}");
            text.admit(
                outer.len() + inner.len() + index_str.len() * 2 + unit.len() + step.len() + 128,
            )?;
            text.push(format!("(step {step} (cl (= (select {outer} {index_str}) (select {inner} {index_str}))) :rule arrays_row :premises ({unit}))"))?;
            steps.push(step);
            current = skip.inner;
        }
        match path.end {
            RowChainEnd::Value { outer, value } => {
                let [_, key, stored] = self.row_store_parts(outer)?;
                if current != outer
                    || key != *read_index
                    || value != stored
                    || self.format_term(key) != *index_str
                    || self.format_term(value) != *tail
                {
                    return None;
                }
                let outer = plan.names.get(&outer)?;
                let step = format!("{prefix}idx");
                text.admit(outer.len() + index_str.len() + tail.len() + step.len() + 96)?;
                text.push(format!(
                    "(step {step} (cl (= (select {outer} {index_str}) {tail})) :rule arrays_idx)"
                ))?;
                steps.push(step);
            }
            RowChainEnd::Base { base } => {
                if current != base || self.format_term(base) != *plan.raw.get(&base)? {
                    return None;
                }
                let base = plan.raw.get(&base)?;
                text.admit(base.len() + index_str.len() + 16)?;
                if *tail != format!("(select {base} {index_str})") {
                    return None;
                }
            }
            RowChainEnd::Const { .. } => return None,
        }
        text.admit(root.len() + root_name.len() + index_str.len() * 2 + 32)?;
        let head = format!("(select {root} {index_str})");
        let shared = format!("(select {root_name} {index_str})");
        let chain = format!("{prefix}shared");
        text.admit(
            steps
                .iter()
                .try_fold(0usize, |bytes, step| bytes.checked_add(step.len() + 1))?,
        )?;
        let premises = steps.join(" ");
        text.admit(shared.len() + tail.len() + premises.len() + chain.len() + 96)?;
        text.push(format!(
            "(step {chain} (cl (= {shared} {tail})) :rule trans :premises ({premises}))"
        ))?;
        // Every name is a definition of the exact effective raw store, so refl
        // is checked after macro expansion by the independent parser. Keep this
        // bridge explicit; the rest of the document never learns an alias.
        text.admit(root.len() + root_name.len() + prefix.len() + 96)?;
        text.push(format!(
            "(step {prefix}array (cl (= {root} {root_name})) :rule refl)"
        ))?;
        text.admit(head.len() + shared.len() + prefix.len() * 2 + 128)?;
        text.push(format!(
            "(step {prefix}read (cl (= {head} {shared})) :rule cong :premises ({prefix}array))"
        ))?;
        text.admit(head.len() + tail.len() + prefix.len() * 3 + chain.len() + 128)?;
        text.push(format!(
            "(step {prefix}tr (cl (= {head} {tail})) :rule trans :premises ({prefix}read {chain}))"
        ))?;
        text.admit(text.bytes)?;
        let mut definitions = plan.definitions;
        definitions.append(&mut text.lines);
        destination.extend(definitions);
        Some(RowChainPathProof::Step(format!("{prefix}tr")))
    }

    fn row_store_parts(&self, outer: TermId) -> Option<[TermId; 3]> {
        self.terms.entry_stamp(outer)?;
        let TermData::App(Symbol::Named(op), args) = self.terms.get(outer) else {
            return None;
        };
        let [inner, key, value] = args.as_slice() else {
            return None;
        };
        if op != "store" {
            return None;
        }
        for term in [*inner, *key, *value] {
            self.terms.entry_stamp(term)?;
        }
        let Sort::Array(sort) = self.terms.sort(outer) else {
            return None;
        };
        (self.terms.sort(*inner) == self.terms.sort(outer)
            && self.terms.sort(*key) == &sort.index_sort
            && self.terms.sort(*value) == &sort.element_sort)
            .then_some([*inner, *key, *value])
    }

    fn row_prefix_plan(
        &self,
        tag: &str,
        root: TermId,
        text: &mut Text<'_, '_>,
    ) -> Option<Prefixes> {
        let bounds = self.row_prefix_bounds(root)?;
        let mut stores = Vec::new();
        let mut current = root;
        let mut raw = HashMap::default();
        while let Some(parts) = self.row_store_parts(current) {
            text.admit(64)?;
            if stores.len() >= MAX_NODES {
                return None;
            }
            stores.push((current, parts));
            current = parts[0];
        }
        if stores.is_empty() {
            return None;
        }
        let mut raw_bytes = 0usize;
        for term in stores.iter().map(|(outer, _)| *outer).chain([current]) {
            let bound = *bounds.get(&term)?;
            raw_bytes = raw_bytes.checked_add(bound.checked_add(64)?)?;
            if raw_bytes > MAX_TEXT {
                return None;
            }
            text.admit(bound)?;
            let rendered = self.format_term(term);
            if rendered.len() > *bounds.get(&term)? {
                return None;
            }
            raw.insert(term, rendered);
        }
        // Authenticate every actual rendered store BEFORE abbreviating it.
        // In particular, an own override or collapsed prefix is never a name
        // for a different constructor or a differently sorted store.
        for (outer, [inner, key, value]) in &stores {
            let actual = raw.get(outer)?;
            text.admit(actual.len())?;
            let parts = split_alethe_application_bounded(actual, "store", 3, MAX_RAW_BYTES).ok()?;
            let [base, index, element] = parts.as_slice() else {
                return None;
            };
            if *base != raw.get(inner)?
                || *index != self.format_term(*key)
                || *element != self.format_term(*value)
            {
                return None;
            }
        }
        let prefix = (0..NONCES).find_map(|nonce| {
            let prefix = format!("@ay_row_{tag}_{nonce}_");
            self.row_prefix_is_fresh(&prefix).then_some(prefix)
        })?;
        let mut names = HashMap::default();
        let mut definitions = Vec::new();
        for (outer, [inner, key, value]) in stores.iter().rev() {
            let base = names.get(inner).or_else(|| raw.get(inner))?;
            let key = self.format_term(*key);
            let value = self.format_term(*value);
            let sort = format_sort_alethe(self.terms.sort(*outer));
            text.admit(prefix.len() + base.len() + key.len() + value.len() + sort.len() + 96)?;
            let name = format!("{prefix}{}", names.len());
            let line = format!("(define-fun {name} () {sort} (store {base} {key} {value}))");
            text.push(line)?;
            names.insert(*outer, name);
        }
        definitions.append(&mut text.lines);
        Some(Prefixes {
            names,
            raw,
            definitions,
        })
    }

    fn row_prefix_is_fresh(&self, prefix: &str) -> bool {
        if self.terms.len() > MAX_NAME_ENTRIES {
            return false;
        }
        let mut entries = self.terms.len();
        for index in 0..self.terms.len() {
            if !self.admit_emission_work(prefix.len() as u64 + 32) {
                return false;
            }
            let collision = match self.terms.get(TermId(index as u32)) {
                TermData::Var(name, _) => name.starts_with(prefix),
                TermData::App(symbol, _) => symbol.name().starts_with(prefix),
                TermData::Let(bindings, _) => bindings.iter().any(|(name, _)| {
                    entries += 1;
                    entries > MAX_NAME_ENTRIES
                        || !self.admit_emission_work(prefix.len() as u64 + 8)
                        || name.starts_with(prefix)
                }),
                TermData::Forall(bindings, ..) | TermData::Exists(bindings, ..) => {
                    bindings.iter().any(|(name, _)| {
                        entries += 1;
                        entries > MAX_NAME_ENTRIES
                            || !self.admit_emission_work(prefix.len() as u64 + 8)
                            || name.starts_with(prefix)
                    })
                }
                _ => false,
            };
            if collision {
                return false;
            }
        }
        let mut bytes = 0usize;
        for text in self
            .term_overrides
            .into_iter()
            .flat_map(|m| m.values())
            .chain(self.skolem_overrides.borrow().values())
            .chain(self.let_bridge_renderings.borrow().values())
        {
            entries += 1;
            let Some(total) = bytes.checked_add(text.len()) else {
                return false;
            };
            bytes = total;
            if entries > MAX_NAME_ENTRIES
                || bytes > MAX_NAME_BYTES
                || !self.admit_emission_work(text.len() as u64 + 8)
                || text.contains(prefix)
            {
                return false;
            }
        }
        true
    }

    // Bound expanded text and all visited payload before format_term can copy
    // it. Closed Bool/BV/array nodes only; no binder-dependent global macro and
    // no unexamined alternate printer channel is introduced by this fast path.
    fn row_prefix_bounds(&self, root: TermId) -> Option<HashMap<TermId, usize>> {
        let mut bounds = HashMap::default();
        let mut heights: HashMap<TermId, usize> = HashMap::default();
        let mut active = HashSet::default();
        let mut pending = vec![(root, false, 0usize)];
        while let Some((term, done, depth)) = pending.pop() {
            if !self.admit_emission_work(64) || depth > MAX_DEPTH {
                return None;
            }
            if bounds.contains_key(&term) {
                continue;
            }
            self.terms.entry_stamp(term)?;
            if matches!(self.terms.get(term), TermData::App(Symbol::Named(op), _) if op == "store")
            {
                let _ = self.row_store_parts(term)?;
            }
            if !row_sort(self.terms.sort(term))
                || self.term_overrides.is_some_and(|m| m.contains_key(&term))
                || self.skolem_overrides.borrow().contains_key(&term)
                || self.let_bridge_renderings.borrow().contains_key(&term)
            {
                return None;
            }
            let (own, children): (usize, &[TermId]) = match self.terms.get(term) {
                TermData::Const(Constant::Bool(_)) => (5, &[]),
                TermData::Const(Constant::BitVec { width, value }) => {
                    if value.sign() == Sign::Minus || value.bits() > u64::from(*width) {
                        return None;
                    }
                    (*width as usize + 32, &[])
                }
                TermData::Var(name, _) if name.len() <= 4096 => (name.len() * 2 + 4, &[]),
                TermData::App(symbol, args)
                    if args.len() <= 128
                        && symbol.name().len() <= 4096
                        && symbol.name() != "const-array" =>
                {
                    let indices = match symbol {
                        Symbol::Named(_) => 0,
                        Symbol::Indexed(_, indices) if indices.len() <= 2 => indices.len() * 12,
                        _ => return None,
                    };
                    (symbol.name().len() * 2 + indices + args.len() + 32, args)
                }
                // No new definition captures a binder, even through a Bool
                // condition. The ordinary inline printer retains its domain.
                _ => return None,
            };
            if !self.admit_emission_work((children.len() as u64).checked_mul(64)?) {
                return None;
            }
            if !done {
                if !active.insert(term) || active.len() + bounds.len() > MAX_NODES {
                    return None;
                }
                pending.push((term, true, depth));
                pending.extend(children.iter().map(|&child| (child, false, depth + 1)));
            } else {
                let bytes = children
                    .iter()
                    .try_fold(own, |sum, child| sum.checked_add(*bounds.get(child)?))?;
                let height = children.iter().try_fold(0usize, |height, child| {
                    Some(height.max(heights.get(child)?.checked_add(1)?))
                })?;
                if bytes > MAX_RAW_BYTES
                    || height > MAX_DEPTH
                    || self
                        .format_cache
                        .borrow()
                        .get(&term)
                        .is_some_and(|text| text.len() > bytes)
                {
                    return None;
                }
                active.remove(&term);
                bounds.insert(term, bytes);
                heights.insert(term, height);
            }
        }
        Some(bounds)
    }
}

fn row_sort(sort: &Sort) -> bool {
    match sort {
        Sort::Bool => true,
        Sort::BitVec(width) => (1..=128).contains(&width.width),
        Sort::Array(shape) => matches!((&shape.index_sort, &shape.element_sort),
            (Sort::BitVec(i),Sort::BitVec(e)) if (1..=128).contains(&i.width) && (1..=128).contains(&e.width)),
        _ => false,
    }
}

#[cfg(test)]
mod tests;
