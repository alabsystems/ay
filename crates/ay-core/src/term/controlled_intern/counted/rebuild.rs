// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Source-shape-preserving reconstruction under the existing caller's owner.
use super::*;

#[cfg(test)]
mod tests;

fn children(term: &TermData, visit: &mut dyn FnMut(TermId) -> Result<()>) -> Result<()> {
    match term {
        TermData::Const(_) | TermData::Var(..) => {}
        TermData::App(_, args) => {
            for &arg in args {
                visit(arg)?;
            }
        }
        TermData::Not(arg) => visit(*arg)?,
        TermData::Ite(c, t, e) => {
            for arg in [*c, *t, *e] {
                visit(arg)?;
            }
        }
        TermData::Let(bindings, body) => {
            for (_, value) in bindings {
                visit(*value)?;
            }
            visit(*body)?;
        }
        TermData::Forall(_, body, triggers) | TermData::Exists(_, body, triggers) => {
            visit(*body)?;
            for trigger in triggers {
                for &term in trigger {
                    visit(term)?;
                }
            }
        }
    }
    Ok(())
}

fn copy_price(term: &TermData, sort: &Sort, owner: &dyn TermConstructionAdmission) -> Result<()> {
    let result = crate::term::snapshot::meter_entry(term, sort, &mut |work, bytes| {
        owner.admit(work, bytes).is_ok()
    });
    owner.check()?;
    result.map_err(|_| CountedTermError::Unsupported)
}

impl<O: TermConstructionAdmission> CountedTermBuilder<'_, '_, O> {
    /// Rebuild an existing node, preserving its operator, payload and result
    /// sort. Replacement children must have the original children's sorts.
    /// Order: App arguments; Not operand; Ite condition/then/else; Let values
    /// then body; quantifier body then each trigger's terms in source order.
    ///
    /// This does not authenticate the original node or establish substitution
    /// equivalence. The caller owns declaration/binder semantics and original
    /// source validation. No new operator or variable identity is accepted.
    /// Arbitrary existing sorts reuse the established metered snapshot-copy
    /// walk; the closed constructor vocabulary is unchanged.
    pub fn rebuild_existing(&mut self, source: TermId, replacement: &[TermId]) -> Result<TermId> {
        self.owner.admit(1, 0)?;
        let entry = self
            .store
            .terms
            .get(source.index())
            .ok_or(CountedTermError::InvalidInput)?;
        let mut position = 0usize;
        let mut unchanged = true;
        children(&entry.term, &mut |old| {
            self.owner.admit(1, 0)?;
            let new = *replacement
                .get(position)
                .ok_or(CountedTermError::InvalidInput)?;
            let old_entry = self
                .store
                .terms
                .get(old.index())
                .ok_or(CountedTermError::InvalidInput)?;
            let new_entry = self
                .store
                .terms
                .get(new.index())
                .ok_or(CountedTermError::InvalidInput)?;
            if !inspection::sort_equal(&old_entry.sort, &new_entry.sort, self.owner)? {
                return Err(CountedTermError::InvalidInput);
            }
            unchanged &= old == new;
            position = position
                .checked_add(1)
                .ok_or_else(|| storage::work(self.owner))?;
            Ok(())
        })?;
        if position != replacement.len() {
            return Err(CountedTermError::InvalidInput);
        }
        if unchanged {
            self.owner.check()?;
            return Ok(source);
        }
        // Only a known negative field-presence fact implies that the unchanged
        // result sort is field-free. A positive fact may come from children;
        // do not misrepresent it as a fact about the result sort.
        let sort_presence = if matches!(entry.sort, Sort::FiniteField(_)) {
            Some(true)
        } else if entry.field_presence == Some(false) {
            Some(false)
        } else {
            None
        };
        copy_price(&entry.term, &entry.sort, self.owner)?;
        let mut term = entry.term.clone();
        let sort = entry.sort.clone();
        self.owner.admit(replacement.len(), 0)?;
        let mut incoming = replacement.iter().copied();
        // Length and shape were validated before the first copy. These writes
        // preserve payloads and cannot allocate or call the original owner.
        match &mut term {
            TermData::App(_, args) => args.copy_from_slice(replacement),
            TermData::Not(arg) => *arg = replacement[0],
            TermData::Ite(c, t, e) => {
                *c = replacement[0];
                *t = replacement[1];
                *e = replacement[2];
            }
            TermData::Let(bindings, body) => {
                for (_, value) in bindings {
                    if let Some(next) = incoming.next() {
                        *value = next;
                    }
                }
                if let Some(next) = incoming.next() {
                    *body = next;
                }
            }
            TermData::Forall(_, body, triggers) | TermData::Exists(_, body, triggers) => {
                if let Some(next) = incoming.next() {
                    *body = next;
                }
                for trigger in triggers {
                    for value in trigger {
                        if let Some(next) = incoming.next() {
                            *value = next;
                        }
                    }
                }
            }
            TermData::Const(_) | TermData::Var(..) => return Err(CountedTermError::InvalidInput),
        }
        let result = self.intern_typed_data(term, sort, sort_presence);
        self.owner.check()?;
        result
    }

    pub(super) fn intern_typed_data(
        &mut self,
        term: TermData,
        sort: Sort,
        sort_presence: Option<bool>,
    ) -> Result<TermId> {
        inspection::entry(&term, &sort, self.owner)?;
        let hash = TermStore::compute_hash(&term);
        if let Some(ids) = self.terms.get(hash, self.owner)? {
            for id in ids {
                self.owner.admit(1, 0)?;
                let entry = self
                    .store
                    .terms
                    .get(id.index())
                    .ok_or(CountedTermError::InvalidInput)?;
                inspection::entry(&entry.term, &entry.sort, self.owner)?;
                inspection::entry(&term, &sort, self.owner)?;
                if entry.term == term && entry.sort == sort {
                    return Ok(*id);
                }
            }
        }
        let id = checked_term_id(self.store.terms.len()).map_err(|_| storage::work(self.owner))?;
        let plan = self.store.counted_bucket_plan(hash, self.owner)?;
        let prepared = self.store.counted_reserve(hash, &plan, self.owner)?;
        let heap = TermStore::heap_size(&term);
        let credit = self
            .store
            .counted_credit(heap, plan.bucket_bytes, self.owner)?;
        self.store
            .controlled_settle(credit, heap, prepared.growth)
            .map_err(|_| storage::storage(self.owner))?;
        let stamp =
            next_entry_stamp(&NEXT_TERM_ENTRY_STAMP).map_err(|_| storage::work(self.owner))?;
        self.terms.insert(hash, id, self.owner)?;
        let mut count = 1usize;
        children(&term, &mut |_| {
            count = count
                .checked_add(1)
                .ok_or_else(|| storage::work(self.owner))?;
            self.owner.admit(1, 0)?;
            Ok(())
        })?;
        self.owner.admit(count, 0)?;
        let field_presence = self
            .store
            .entry_field_presence_from_sort(&term, sort_presence);
        self.store
            .controlled_commit_bucket(
                hash,
                id,
                TermEntry {
                    field_presence,
                    term,
                    sort,
                    stamp,
                },
                prepared,
            )
            .map_err(|_| storage::storage(self.owner))?;
        Ok(id)
    }
}
