// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Replay shadowed writes using array extensionality and read-over-write.
//! Every surviving index has a discharged hit case. Its miss then licenses
//! later skipped writes at that exact index. The final case reads the same
//! base. No array rewrite or disequality is an unchecked exported axiom.

use super::*;
use crate::checker::shadowed_stores::{shadowed_stores, ShadowedStores, Write};

const MAX_SHADOW_TEXT: usize = 64 * 1024 * 1024;

struct Derivation<'a, 'terms> {
    printer: &'a AlethePrinter<'terms>,
    prefix: String,
    next: usize,
    output: String,
    witness: String,
    selected: String,
    ext: String,
    not_false: String,
}

struct Walk<'a> {
    writes: &'a [Write],
    position: usize,
    current: TermId,
    head: String,
    prefix: String,
}

impl AlethePrinter<'_> {
    pub(super) fn format_shadowed_stores(&self, id: ProofId, clause: &[TermId]) -> Option<String> {
        let shape = shadowed_stores(self.terms, clause)?;
        if term_mentions_symbol(self.terms, shape.left, EXT_CHOICE_BINDER)
            || term_mentions_symbol(self.terms, shape.right, EXT_CHOICE_BINDER)
        {
            return None;
        }
        let raw =
            AlethePrinter::new_with_overrides_and_budget(self.terms, None, Some(4 * 1024 * 1024));
        let left = raw.format_term(shape.left);
        let right = raw.format_term(shape.right);
        let equality = format!("(= {left} {right})");
        self.charge(raw.work_used());
        if raw.work_budget_exhausted() || self.format_term(clause[0]) != equality {
            return None;
        }
        // Require each used subterm to retain its certified spelling too.
        for term in shape
            .left_writes
            .iter()
            .chain(&shape.right_writes)
            .flat_map(|w| [w.outer, w.inner, w.index, w.value])
            .chain([shape.base])
        {
            let used = raw.work_used();
            let raw_text = raw.format_term(term);
            self.charge(raw.work_used().saturating_sub(used));
            if self.format_term(term) != raw_text
                || raw.work_budget_exhausted()
                || self.work_budget_exhausted()
            {
                return None;
            }
        }
        let Sort::Array(sort) = self.terms.sort(shape.left) else {
            return None;
        };
        let binder = EXT_CHOICE_BINDER;
        let witness = format!("(choice (({binder} {})) (or {equality} (not (= (select {left} {binder}) (select {right} {binder})))))", format_sort_alethe(&sort.index_sort));
        let selected = format!("(= (select {left} {witness}) (select {right} {witness}))");
        let mut d = Derivation {
            printer: self,
            prefix: format!("{id}.shadow"),
            next: 0,
            output: String::new(),
            witness,
            selected,
            ext: String::new(),
            not_false: String::new(),
        };
        d.not_false = d.step("(not false)", "false", &[])?;
        let end = d.fresh();
        let assumption = d.fresh();
        d.append(&format!(
            "(anchor :step {end})\n(assume {assumption} (not {equality}))\n"
        ))?;
        d.ext = d.step(
            &format!("(not {})", d.selected),
            "arrays_ext",
            &[&assumption],
        )?;
        d.reads(&shape)?;
        d.append(&format!("(step {end} (cl (not (not {equality})) false) :rule subproof :discharge ({assumption}))\n"))?;
        let unit = d.step(
            &format!("(not (not {equality}))"),
            "resolution",
            &[&end, &d.not_false.clone()],
        )?;
        let nn = d.step(
            &format!("(not (not (not {equality}))) {equality}"),
            "not_not",
            &[],
        )?;
        d.append(&format!(
            "(step {id} (cl {equality}) :rule resolution :premises ({unit} {nn}))"
        ))?;
        Some(d.output)
    }
}

impl Derivation<'_, '_> {
    fn fresh(&mut self) -> String {
        let name = format!("{}.{}", self.prefix, self.next);
        self.next += 1;
        name
    }

    fn append(&mut self, text: &str) -> Option<()> {
        self.printer.charge(text.len() as u64);
        if self.output.len().checked_add(text.len())? > MAX_SHADOW_TEXT
            || self.printer.work_budget_exhausted()
        {
            return None;
        }
        self.output.push_str(text);
        Some(())
    }

    fn step(&mut self, clause: &str, rule: &str, premises: &[&str]) -> Option<String> {
        // WIRE-RULE BOUND: every step of this derivation is printed here, so
        // no name outside the pinned checker's implemented set can reach the
        // wire. See `PackedProof::named_step` for the full rationale and
        // `tests/wire_rule_coverage.rs` for the probe that re-proves the set.
        if !ay_core::is_checkable_alethe_rule(rule) {
            return None;
        }
        let id = self.fresh();
        let suffix = if premises.is_empty() {
            String::new()
        } else {
            format!(" :premises ({})", premises.join(" "))
        };
        self.append(&format!("(step {id} (cl {clause}) :rule {rule}{suffix})\n"))?;
        Some(id)
    }

    fn eq(&mut self, left: &str, right: &str, rule: &str, premises: &[&str]) -> Option<String> {
        self.step(&format!("(= {left} {right})"), rule, premises)
    }

    fn select(&self, array: TermId) -> String {
        format!(
            "(select {} {})",
            self.printer.format_term(array),
            self.witness
        )
    }

    fn walk<'a>(&mut self, root: TermId, writes: &'a [Write]) -> Option<Walk<'a>> {
        let head = self.select(root);
        let prefix = self.eq(&head, &head, "refl", &[])?;
        Some(Walk {
            writes,
            position: 0,
            current: root,
            head,
            prefix,
        })
    }

    fn miss(&mut self, walk: &mut Walk<'_>, assumption: &str) -> Option<()> {
        let write = walk.writes.get(walk.position)?;
        if write.outer != walk.current {
            return None;
        }
        let current = self.select(write.outer);
        let next = self.select(write.inner);
        let row = self.eq(&current, &next, "arrays_row", &[assumption])?;
        walk.prefix = self.eq(&walk.head, &next, "trans", &[&walk.prefix, &row])?;
        walk.position += 1;
        walk.current = write.inner;
        Some(())
    }

    fn skip(&mut self, walk: &mut Walk<'_>, misses: &HashMap<TermId, String>) -> Option<()> {
        while let Some(write) = walk.writes.get(walk.position) {
            let Some(assumption) = misses.get(&write.index) else {
                break;
            };
            self.miss(walk, assumption)?;
        }
        Some(())
    }

    fn hit(&mut self, walk: &Walk<'_>, assumption: &str) -> Option<String> {
        let write = walk.writes.get(walk.position)?;
        let array = self.printer.format_term(write.outer);
        let index = self.printer.format_term(write.index);
        let value = self.printer.format_term(write.value);
        let current = self.select(write.outer);
        let at_index = format!("(select {array} {index})");
        let moved = self.eq(&at_index, &current, "cong", &[assumption])?;
        let reverse = self.eq(&current, &at_index, "symm", &[&moved])?;
        let row = self.eq(&at_index, &value, "arrays_idx", &[])?;
        self.eq(&walk.head, &value, "trans", &[&walk.prefix, &reverse, &row])
    }

    fn reject_hit(
        &mut self,
        left: &Walk<'_>,
        right: &Walk<'_>,
        index: TermId,
        value: TermId,
    ) -> Option<String> {
        let condition = format!("(= {} {})", self.printer.format_term(index), self.witness);
        let end = self.fresh();
        let assumption = self.fresh();
        self.append(&format!(
            "(anchor :step {end})\n(assume {assumption} {condition})\n"
        ))?;
        let l = self.hit(left, &assumption)?;
        let r = self.hit(right, &assumption)?;
        let reverse = self.eq(&self.printer.format_term(value), &right.head, "symm", &[&r])?;
        let equality = self.step(&self.selected.clone(), "trans", &[&l, &reverse])?;
        self.step("", "resolution", &[&self.ext.clone(), &equality])?;
        self.append(&format!(
            "(step {end} (cl (not {condition}) false) :rule subproof :discharge ({assumption}))\n"
        ))?;
        self.step(
            &format!("(not {condition})"),
            "resolution",
            &[&end, &self.not_false.clone()],
        )
    }

    fn reads(&mut self, shape: &ShadowedStores) -> Option<()> {
        let mut left = self.walk(shape.left, &shape.left_writes)?;
        let mut right = self.walk(shape.right, &shape.right_writes)?;
        let mut misses = HashMap::default();
        for &(index, value) in &shape.retained {
            self.skip(&mut left, &misses)?;
            self.skip(&mut right, &misses)?;
            for walk in [&left, &right] {
                let write = walk.writes.get(walk.position)?;
                if (write.index, write.value) != (index, value) {
                    return None;
                }
            }
            let miss = self.reject_hit(&left, &right, index, value)?;
            self.miss(&mut left, &miss)?;
            self.miss(&mut right, &miss)?;
            misses.insert(index, miss);
        }
        self.skip(&mut left, &misses)?;
        self.skip(&mut right, &misses)?;
        if left.current != shape.base
            || right.current != shape.base
            || left.position != left.writes.len()
            || right.position != right.writes.len()
        {
            return None;
        }
        let reverse = self.eq(
            &self.select(shape.base),
            &right.head,
            "symm",
            &[&right.prefix],
        )?;
        let equality = self.step(&self.selected.clone(), "trans", &[&left.prefix, &reverse])?;
        self.step("", "resolution", &[&self.ext.clone(), &equality])?;
        Some(())
    }
}

#[cfg(test)]
#[path = "shadowed_stores_tests.rs"]
mod tests;

/// Test the exact exporter under a caller-owned aggregate work allowance.
/// A native array identity alone does not promise a replayable wire format.
#[must_use]
pub fn checked_shadowed_stores_lowering_supported(
    terms: &TermStore,
    clause: &[TermId],
    term_overrides: Option<&HashMap<TermId, String>>,
    remaining_work: &mut u64,
) -> bool {
    if *remaining_work == 0 {
        return false;
    }
    let printer = AlethePrinter::new_with_overrides_and_budget(
        terms,
        term_overrides,
        Some((*remaining_work).min(MAX_SHADOW_TEXT as u64)),
    );
    let supported = printer.format_shadowed_stores(ProofId(0), clause).is_some();
    *remaining_work = remaining_work.saturating_sub(printer.work_used());
    supported && !printer.work_budget_exhausted()
}
