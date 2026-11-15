// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Shared caller envelope for exact quantifier checks, including queue fan-out.

use std::mem::size_of;

use super::*;

mod sorts;

pub(super) struct QuantifierMeter<'w, 'p> {
    work: &'w mut usize,
    progress: &'p mut dyn FnMut(usize, usize) -> bool,
    step: ProofId,
    rule: &'static str,
}

impl<'w, 'p> QuantifierMeter<'w, 'p> {
    pub(super) fn new(
        step: ProofId,
        rule: &'static str,
        work: &'w mut usize,
        progress: &'p mut dyn FnMut(usize, usize) -> bool,
    ) -> Self {
        Self {
            work,
            progress,
            step,
            rule,
        }
    }

    pub(super) fn charge(&mut self, work: usize, bytes: usize) -> Result<(), ProofCheckError> {
        if (self.progress)(work, bytes) {
            Ok(())
        } else {
            Err(ProofCheckError::ResourceLimit)
        }
    }

    pub(super) fn visit(&mut self) -> Result<(), ProofCheckError> {
        self.charge(1, 0)?;
        if *self.work >= SKOLEM_TERM_WORK_LIMIT {
            return Err(ProofCheckError::ResourceLimit);
        }
        *self.work += 1;
        Ok(())
    }

    pub(super) fn term<'a>(
        &mut self,
        terms: &'a TermStore,
        id: TermId,
    ) -> Result<&'a TermData, ProofCheckError> {
        self.charge(1, 0)?;
        if id.index() >= terms.len() {
            // A u32 TermId needs at most ten decimal digits. Reserve the
            // bounded diagnostic and its rule String before formatting either.
            let bytes = add(64, self.rule.len())?;
            self.charge(bytes, bytes)?;
            return Err(invalid_rule(
                self.step,
                self.rule,
                format!("missing term {id}"),
            ));
        }
        Ok(terms.get(id))
    }

    pub(super) fn invalid(&mut self, reason: &str) -> Result<ProofCheckError, ProofCheckError> {
        let bytes = add(reason.len(), self.rule.len())?;
        self.charge(add(bytes, 1)?, bytes)?;
        Ok(invalid_rule(self.step, self.rule, reason))
    }

    pub(super) fn sort<'a>(
        &mut self,
        terms: &'a TermStore,
        id: TermId,
    ) -> Result<&'a Sort, ProofCheckError> {
        self.term(terms, id)?;
        Ok(terms.sort(id))
    }

    pub(super) fn name(&mut self, name: &str) -> Result<(), ProofCheckError> {
        self.charge(add(name.len(), 1)?, 0)
    }

    pub(super) fn owned_name(&mut self, name: &str) -> Result<(), ProofCheckError> {
        self.charge(add(name.len(), 1)?, name.len())
    }

    pub(super) fn lookup(&mut self, name: &str, entries: usize) -> Result<(), ProofCheckError> {
        // Native hashing is deterministic, not collision-proof. Include every
        // possible occupied-key comparison plus the hash/control-byte walk.
        self.charge(mul(lookup_comparisons(entries)?, add(name.len(), 2)?)?, 0)
    }

    pub(super) fn table_iteration(&mut self, entries: usize) -> Result<(), ProofCheckError> {
        // Private tables are grow-only: native capacity is at most 2*n+1,
        // and an ordered walk visits each tree edge at most twice.
        self.charge(add(mul(entries, 2)?, 1)?, 0)
    }

    fn table_entry<T>(&mut self) -> Result<(), ProofCheckError> {
        // Reserve controls and geometric allocation slack per insertion.
        self.charge(1, add(mul(size_of::<T>(), 4)?, 128)?)
    }

    pub(super) fn name_set_entry<T: AsRef<str> + Ord + std::hash::Hash>(
        &mut self,
        names: &HashSet<T>,
        new_name: &str,
    ) -> Result<(), ProofCheckError> {
        self.lookup(new_name, names.len())?;
        let growing = names.len() == names.capacity();
        if growing {
            // Migration probes can collide too: each old key may traverse a
            // full occupied cluster before its new slot is found.
            self.charge(mul(names.len(), add(names.len(), 1)?)?, 0)?;
            for name in names {
                self.name(name.as_ref())?;
            }
        }
        self.table_entry::<T>()
    }

    pub(super) fn name_map_entry<K: AsRef<str> + Ord + std::hash::Hash, V>(
        &mut self,
        names: &HashMap<K, V>,
        new_name: &str,
    ) -> Result<(), ProofCheckError> {
        self.lookup(new_name, names.len())?;
        let growing = names.len() == names.capacity();
        if growing {
            self.charge(mul(names.len(), add(names.len(), 1)?)?, 0)?;
            for name in names.keys() {
                self.name(name.as_ref())?;
            }
        }
        self.table_entry::<(K, V)>()
    }

    pub(super) fn push<T>(&mut self, stack: &mut Vec<T>, value: T) -> Result<(), ProofCheckError> {
        self.queue_room(stack)?;
        if stack.len() == stack.capacity() {
            let capacity = mul(stack.capacity().max(2), 2)?.min(SKOLEM_TERM_WORK_LIMIT);
            self.charge(capacity, mul(capacity, size_of::<T>())?)?;
            stack
                .try_reserve_exact(capacity - stack.len())
                .map_err(|_| ProofCheckError::ResourceLimit)?;
        }
        stack.push(value);
        Ok(())
    }

    pub(super) fn queue_room<T>(&mut self, stack: &[T]) -> Result<(), ProofCheckError> {
        self.charge(1, 0)?;
        if stack.len() >= SKOLEM_TERM_WORK_LIMIT {
            return Err(ProofCheckError::ResourceLimit);
        }
        Ok(())
    }

    pub(super) fn seen(
        &mut self,
        seen: &mut HashSet<TermId>,
        term: TermId,
    ) -> Result<bool, ProofCheckError> {
        self.charge(lookup_comparisons(seen.len())?, 0)?;
        if seen.contains(&term) {
            return Ok(true);
        }
        if *self.work >= SKOLEM_TERM_WORK_LIMIT {
            return Err(ProofCheckError::ResourceLimit);
        }
        let growing = seen.len() == seen.capacity();
        if growing {
            self.charge(mul(seen.len(), add(seen.len(), 1)?)?, 0)?;
        }
        // insert probes again even after the separate contains lookup.
        self.charge(lookup_comparisons(seen.len())?, 0)?;
        self.table_entry::<TermId>()?;
        seen.insert(term);
        Ok(false)
    }

    pub(super) fn insert_name(
        &mut self,
        names: &mut HashSet<String>,
        name: &str,
    ) -> Result<(), ProofCheckError> {
        self.lookup(name, names.len())?;
        if !names.contains(name) {
            self.name_set_entry(names, name)?;
            self.owned_name(name)?;
            names.insert(name.to_string());
        }
        Ok(())
    }

    pub(super) fn clone_names(
        &mut self,
        names: &HashSet<String>,
    ) -> Result<HashSet<String>, ProofCheckError> {
        // These sets are private and grow-only, but price the actual native
        // table capacity anyway: cloning retains spare buckets and scans them.
        let capacity = names.capacity();
        let bucket_bytes = add(mul(size_of::<String>(), 4)?, 128)?;
        self.charge(
            add(capacity, 1)?,
            add(size_of::<HashSet<String>>(), mul(capacity, bucket_bytes)?)?,
        )?;
        for name in names {
            self.owned_name(name)?;
        }
        self.charge(0, 0)?;
        Ok(names.clone())
    }

    pub(super) fn symbol_equal(
        &mut self,
        left: &Symbol,
        right: &Symbol,
    ) -> Result<bool, ProofCheckError> {
        self.name(left.name())?;
        self.name(right.name())?;
        for symbol in [left, right] {
            match symbol {
                Symbol::Named(_) => {}
                Symbol::Indexed(_, indices) => self.charge(indices.len(), 0)?,
                _ => return Err(ProofCheckError::ResourceLimit),
            }
        }
        Ok(left == right)
    }

    pub(super) fn sort_equal(
        &mut self,
        left: &Sort,
        right: &Sort,
    ) -> Result<bool, ProofCheckError> {
        sorts::meter_sort(left, 0, self)?;
        sorts::meter_sort(right, 0, self)?;
        self.charge(0, 0)?;
        Ok(left == right)
    }
}

fn add(left: usize, right: usize) -> Result<usize, ProofCheckError> {
    left.checked_add(right)
        .ok_or(ProofCheckError::ResourceLimit)
}

fn mul(left: usize, right: usize) -> Result<usize, ProofCheckError> {
    left.checked_mul(right)
        .ok_or(ProofCheckError::ResourceLimit)
}

fn lookup_comparisons(entries: usize) -> Result<usize, ProofCheckError> {
    add(entries, 1)
}
