// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;
use std::collections::BTreeMap;

const MAX_ALIAS_EQUALITIES: usize = 64;
const MAX_INDEXED_AUTHORED_ROOTS: usize = 100_000;

pub(super) type AliasBinding = (TermId, TermId);
type EndpointKey = (TermId, TermId);

enum BindingEntry {
    Bindings(Vec<AliasBinding>),
    TooMany,
}

pub(super) struct AuthoredIndex {
    pairs: BTreeMap<EndpointKey, (TermId, TermId)>,
    array_aliases: BTreeMap<TermId, BindingEntry>,
    scalar_aliases: BTreeMap<TermId, BindingEntry>,
}

impl AuthoredIndex {
    /// Index exact authored roots once in source order. The proof lifecycle
    /// uses the same 100,000-root envelope, which bounds both maps globally.
    pub(super) fn build(terms: &TermStore, authored: &[TermId]) -> Option<Self> {
        if authored.len() > MAX_INDEXED_AUTHORED_ROOTS {
            return None;
        }
        let mut index = Self {
            pairs: BTreeMap::new(),
            array_aliases: BTreeMap::new(),
            scalar_aliases: BTreeMap::new(),
        };
        for &root in authored {
            index.index_pair(terms, root);
            index.index_aliases(terms, root);
        }
        Some(index)
    }

    pub(super) fn pair(&self, left: TermId, right: TermId) -> Option<(TermId, TermId)> {
        self.pairs.get(&endpoint_key(left, right)).copied()
    }

    pub(super) fn array_bindings(&self, alias: TermId) -> Option<&[AliasBinding]> {
        bounded_bindings(&self.array_aliases, alias)
    }

    pub(super) fn scalar_bindings(&self, alias: TermId) -> Option<&[AliasBinding]> {
        bounded_bindings(&self.scalar_aliases, alias)
    }

    fn bindings_for_sort(&mut self, sort: &Sort) -> &mut BTreeMap<TermId, BindingEntry> {
        if matches!(sort, Sort::Array(_)) {
            &mut self.array_aliases
        } else {
            &mut self.scalar_aliases
        }
    }

    fn index_pair(&mut self, terms: &TermStore, root: TermId) {
        let TermData::Not(inner) = terms.get(root) else {
            return;
        };
        let equality = *inner;
        let Some((left, right)) = decode_eq_local(terms, equality) else {
            return;
        };
        self.pairs
            .entry(endpoint_key(left, right))
            .or_insert((root, equality));
    }

    fn index_aliases(&mut self, terms: &TermStore, root: TermId) {
        let Some((left, right)) = decode_eq_local(terms, root) else {
            return;
        };
        if terms.sort(left) != terms.sort(right) {
            return;
        }
        let aliases = self.bindings_for_sort(terms.sort(left));
        push_binding(aliases, left, (root, right));
        push_binding(aliases, right, (root, left));
    }
}

fn bounded_bindings(
    aliases: &BTreeMap<TermId, BindingEntry>,
    alias: TermId,
) -> Option<&[AliasBinding]> {
    match aliases.get(&alias) {
        Some(BindingEntry::Bindings(bindings)) => Some(bindings),
        Some(BindingEntry::TooMany) => None,
        None => Some(&[]),
    }
}

fn endpoint_key(left: TermId, right: TermId) -> EndpointKey {
    if left <= right {
        (left, right)
    } else {
        (right, left)
    }
}

fn push_binding(
    aliases: &mut BTreeMap<TermId, BindingEntry>,
    alias: TermId,
    binding: AliasBinding,
) {
    let entry = aliases
        .entry(alias)
        .or_insert_with(|| BindingEntry::Bindings(Vec::new()));
    match entry {
        BindingEntry::Bindings(bindings) if bindings.len() < MAX_ALIAS_EQUALITIES => {
            bindings.push(binding);
        }
        BindingEntry::Bindings(_) => *entry = BindingEntry::TooMany,
        BindingEntry::TooMany => {}
    }
}
