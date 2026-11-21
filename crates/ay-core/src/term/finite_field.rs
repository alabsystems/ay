// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
//! Dispatch metadata, never model/proof authority. Normal arena construction
//! computes reachability once; incomplete snapshot/sort metadata stays `None`.
use super::*;

#[derive(Clone, Copy)]
enum BinderSortPresence {
    Inspect,
    // Only the controlled validated grammar may supply this receipt. Its
    // borrowed owned-sort admission has visited every physical binder sort
    // before commit, and rejects FiniteField even beneath Array/Seq.
    KnownFieldFree,
}

fn union(a: Option<bool>, b: Option<bool>) -> Option<bool> {
    match (a, b) {
        (Some(true), _) | (_, Some(true)) => Some(true),
        (Some(false), Some(false)) => Some(false),
        _ => None,
    }
}
fn sort_presence(root: &Sort) -> Option<bool> {
    match root {
        Sort::FiniteField(_) => return Some(true),
        Sort::Array(_) | Sort::Seq(_) | Sort::Datatype(_) => {}
        _ => return Some(false),
    }
    let mut pending = vec![root];
    let mut seen = KaniHashSet::default();
    let mut work = 1024usize;
    while let Some(sort) = pending.pop() {
        work = work.checked_sub(1)?;
        if !seen.insert(std::ptr::from_ref(sort)) {
            continue;
        }
        match sort {
            Sort::FiniteField(_) => return Some(true),
            Sort::Array(a) => {
                if pending.len() > 1022 {
                    return None;
                }
                pending.push(&a.index_sort);
                pending.push(&a.element_sort);
            }
            Sort::Seq(s) => {
                if pending.len() >= 1024 {
                    return None;
                }
                pending.push(s);
            }
            Sort::Datatype(d) => {
                if d.constructors.len() > 1024 {
                    return None;
                }
                for c in &d.constructors {
                    if pending.len().checked_add(c.fields.len())? > 1024 {
                        return None;
                    }
                    pending.extend(c.fields.iter().map(|f| &f.sort));
                }
            }
            _ => {}
        }
    }
    Some(false)
}
impl TermStore {
    /// Cached field-bearing syntax. `None` means unchecked/incomplete metadata,
    /// including positional checker snapshots and over-budget sort descriptors.
    /// Consumers must decline or perform bounded admission in that case.
    #[must_use]
    pub fn finite_field_presence(&self, id: TermId) -> Option<bool> {
        self.terms.get(id.index())?.field_presence
    }

    pub(super) fn entry_field_presence(&self, term: &TermData, sort: &Sort) -> Option<bool> {
        self.entry_field_presence_from_sort(term, sort_presence(sort))
    }
    // Counted builders already prove their complete owned sort belongs to the
    // closed Bool/BV/Array grammar. They supply Some(false) and debit child visits.
    pub(super) fn entry_field_presence_from_sort(
        &self,
        term: &TermData,
        own: Option<bool>,
    ) -> Option<bool> {
        entry_from_sort(&self.terms, term, own)
    }

    /// Dispatch metadata for a controlled-validated producer node. The
    /// controlled grammar proves BOTH output and binder sorts field-free.
    /// Child syntax can still carry true/unknown field presence and is always
    /// unioned. This path performs no sort walk or scratch allocation during
    /// the already-reserved commit; it grants no typing/source/proof authority.
    pub(super) fn entry_field_presence_for_controlled(&self, term: &TermData) -> Option<bool> {
        entry_with_binder_presence(
            &self.terms,
            term,
            Some(false),
            BinderSortPresence::KnownFieldFree,
        )
    }
}

pub(super) fn entry(entries: &[TermEntry], term: &TermData, sort: &Sort) -> Option<bool> {
    entry_from_sort(entries, term, sort_presence(sort))
}
pub(super) fn entry_from_sort(
    entries: &[TermEntry],
    term: &TermData,
    own: Option<bool>,
) -> Option<bool> {
    entry_with_binder_presence(entries, term, own, BinderSortPresence::Inspect)
}

fn entry_with_binder_presence(
    entries: &[TermEntry],
    term: &TermData,
    own: Option<bool>,
    binders: BinderSortPresence,
) -> Option<bool> {
    if own == Some(true) {
        return own;
    }
    let mut presence = own;
    let child = |id: TermId| {
        entries
            .get(id.index())
            .and_then(|entry| entry.field_presence)
    };
    match term {
        TermData::Const(Constant::FiniteField { .. }) => return Some(true),
        TermData::App(Symbol::Named(name), _)
            if matches!(name.as_str(), "ff.add" | "ff.mul" | "ff.neg" | "ff.bitsum") =>
        {
            return Some(true)
        }
        TermData::App(_, args) => {
            for &id in args {
                presence = union(presence, child(id));
            }
        }
        TermData::Not(id) => presence = union(presence, child(*id)),
        TermData::Ite(c, t, e) => {
            for &id in [c, t, e] {
                presence = union(presence, child(id));
            }
        }
        TermData::Let(bindings, body) => {
            for (_, id) in bindings {
                presence = union(presence, child(*id));
            }
            presence = union(presence, child(*body));
        }
        TermData::Forall(bindings, body, triggers) | TermData::Exists(bindings, body, triggers) => {
            if matches!(binders, BinderSortPresence::Inspect) {
                for (_, sort) in bindings {
                    presence = union(presence, sort_presence(sort));
                }
            }
            presence = union(presence, child(*body));
            for trigger in triggers {
                for &id in trigger {
                    presence = union(presence, child(id));
                }
            }
        }
        TermData::Const(_) | TermData::Var(..) => {}
    }
    presence
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn field_presence_tracks_structure_and_rollback() {
        let mut store = TermStore::new();
        let t = store.mk_bool(true);
        let mut wide = t;
        for _ in 0..4096 {
            wide = store.mk_app(Symbol::named("and"), [wide, t], Sort::Bool);
        }
        assert_eq!(store.finite_field_presence(wide), Some(false));
        let field = crate::FiniteFieldSort::new(7).unwrap();
        let x = store.mk_var("x", Sort::FiniteField(field));
        let one = store.mk_finite_field(1, field);
        let equality = store.mk_app(Symbol::named("="), [x, one], Sort::Bool);
        assert_eq!(store.finite_field_presence(equality), Some(true));
        let cloned = store.clone();
        assert_eq!(cloned.finite_field_presence(equality), Some(true));
        let array = store.mk_var("a", Sort::array(Sort::Bool, Sort::FiniteField(field)));
        assert_eq!(store.finite_field_presence(array), Some(true));
        let checkpoint = store.rollback_checkpoint();
        let discarded = store.mk_var("discarded", Sort::FiniteField(field));
        assert_eq!(store.finite_field_presence(discarded), Some(true));
        store.rollback_to(checkpoint);
        let replacement = store.mk_var("replacement", Sort::Bool);
        assert_eq!(replacement, discarded);
        assert_eq!(store.finite_field_presence(replacement), Some(false));
    }
}
