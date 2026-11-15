// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Text declarations are admitted before allocating their owned metadata. The
//! source registry remains the authority for canonical record signatures.

use super::*;
use crate::quantified::records::{
    sort_bytes, Registry, MAX_FIELDS, MAX_RECORDS, MAX_REGISTRY_COPY_BYTES, MAX_REGISTRY_NAME_BYTES,
};

mod applications;
mod group;

#[derive(Default)]
pub(super) struct RecordState {
    registry: Option<Registry>,
    count: usize,
    names: usize,
    copies: usize,
    max_sort_bytes: usize,
}

impl RecordState {
    pub(super) fn contains(&self, name: &str) -> bool {
        self.registry.as_ref().is_some_and(|registry| {
            registry.lookup(name).is_some() || registry.contains_term_symbol(name)
        })
    }

    fn charge_metadata(&mut self, name_bytes: usize, copy_bytes: usize) -> ChcResult<()> {
        self.names = self
            .names
            .checked_add(name_bytes)
            .ok_or_else(|| invalid("record name limit"))?;
        self.copies = self
            .copies
            .checked_add(copy_bytes)
            .ok_or_else(|| invalid("record copy limit"))?;
        if self.names > MAX_REGISTRY_NAME_BYTES || self.copies > MAX_REGISTRY_COPY_BYTES {
            return Err(invalid("record metadata limit"));
        }
        Ok(())
    }
}

impl Budget {
    pub(super) fn sort_copy(&mut self, sort: &ChcSort) -> ChcResult<()> {
        // Structural admission precedes any general equality or clone. Nested
        // metadata is occurrence/depth bounded, not recursive AST authority.
        let bytes = sort_bytes(sort).ok_or_else(|| invalid("unsupported sort metadata"))?;
        if !crate::quantified::records::small_copy_sort(sort) {
            self.charge(1 + bytes / 64, bytes)?;
        }
        // Narrow scalar/array copies were already covered by the parser's
        // node/edge charges. Wide payloads retain their explicit limb charge.
        Ok(())
    }
}

impl Parser<'_> {
    pub(super) fn source_sort(&mut self, expr: &SExpr) -> ChcResult<ChcSort> {
        if matches!(expr.as_list(), Some([name, _, _]) if name.is_symbol("Array")) {
            if let Ok(sort) = value::sort(expr) {
                return Ok(sort);
            }
            let (indices, leaf) = self.array_indices(expr)?;
            let mut sort = self.source_sort(leaf)?;
            self.budget.sort_copy(&sort)?;
            for width in indices.into_iter().rev() {
                sort = ChcSort::Array(Box::new(ChcSort::BitVec(width)), Box::new(sort));
            }
            self.budget.sort_copy(&sort)?;
            return Ok(sort);
        }
        if let Some(name) = expr.as_symbol() {
            if let Some(sort) = self.records.registry.as_ref().and_then(|r| r.lookup(name)) {
                self.budget.sort_copy(sort)?;
                return Ok(sort.clone());
            }
        }
        value::sort(expr)
    }

    /// Peel at most two BV-key wrappers before resolving a possibly forward
    /// record reference. No uninterpreted placeholder enters typed source.
    fn array_indices<'a>(&mut self, mut expr: &'a SExpr) -> ChcResult<(Vec<u32>, &'a SExpr)> {
        let mut indices = Vec::new();
        while let Some([name, key, value]) = expr.as_list() {
            if !name.is_symbol("Array") {
                break;
            }
            if indices.len() >= crate::quantified::records::MAX_ARRAY_RANK {
                return Err(invalid("array rank limit"));
            }
            let ChcSort::BitVec(width) = value::sort(key)? else {
                return Err(invalid("array index must be a bounded bitvector"));
            };
            self.budget.charge(1, 128)?;
            indices.push(width);
            expr = value;
        }
        Ok((indices, expr))
    }

    pub(super) fn record_declaration(&mut self, name: &SExpr, definition: &SExpr) -> ChcResult<()> {
        self.record_group(&[(name, definition)])?;
        self.refresh_records()
    }

    pub(super) fn record_declarations(
        &mut self,
        names: &SExpr,
        definitions: &SExpr,
    ) -> ChcResult<()> {
        let names = list(names)?;
        let definitions = list(definitions)?;
        if names.is_empty()
            || names.len() != definitions.len()
            || names.len() > MAX_RECORDS.saturating_sub(self.records.count)
        {
            return Err(invalid("record declaration group size"));
        }
        self.budget
            .charge(names.len(), names.len().saturating_mul(128))?;
        let mut group = Vec::new();
        for (header, definition) in names.iter().zip(definitions) {
            let [name, arity] = list(header)? else {
                return Err(invalid("record declaration requires name and zero arity"));
            };
            if arity.as_numeral() != Some("0") {
                return Err(invalid("only zero-arity records are supported"));
            }
            group.push((name, definition));
        }
        self.record_group(&group)?;
        // No public state escapes on a failure anywhere in this group. A
        // single refresh also avoids repeatedly copying all earlier members.
        self.refresh_records()
    }

    fn record_name(&mut self, name: &str) -> ChcResult<()> {
        self.budget.name(name)?;
        if self.bindings.contains_key(name)
            || self.declarations.lookup_predicate(name).is_some()
            || self.functions.contains(name)
        {
            return Err(invalid("record symbol conflicts with a term declaration"));
        }
        // Cross-record selector overloads are intentional. The registry checks
        // complete argument signatures; never resolve one by name alone.
        let bytes = name
            .len()
            .checked_mul(4)
            .and_then(|n| n.checked_add(256))
            .ok_or_else(|| invalid("record metadata limit"))?;
        self.records.charge_metadata(name.len(), bytes)?;
        self.budget.charge(1, 256)
    }

    fn refresh_records(&mut self) -> ChcResult<()> {
        self.budget
            .charge(self.records.copies / 64 + 1, self.records.copies)?;
        self.records.registry = Some(Registry::new(&self.declarations)?);
        Ok(())
    }
}
