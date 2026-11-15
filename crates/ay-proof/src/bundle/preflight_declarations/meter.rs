// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Prices the declaration pass's own grow-only tables and owned strings.

use std::mem::size_of;

use super::*;

pub(super) struct DeclarationMeter<'a> {
    progress: Progress<'a>,
}

impl<'a> DeclarationMeter<'a> {
    pub(super) fn new(progress: Progress<'a>) -> Self {
        Self { progress }
    }

    pub(super) fn charge(&mut self, work: usize, bytes: usize) -> Result<(), ProofCheckError> {
        if (self.progress)(work, bytes) {
            Ok(())
        } else {
            Err(ProofCheckError::ResourceLimit)
        }
    }

    pub(super) fn names_equal(&mut self, left: &str, right: &str) -> Result<bool, ProofCheckError> {
        self.charge(add(left.len().min(right.len()), 1)?, 0)?;
        Ok(left == right)
    }

    pub(super) fn prefixed_name(
        &mut self,
        prefix: &str,
        name: &str,
    ) -> Result<String, ProofCheckError> {
        let bytes = add(prefix.len(), name.len())?;
        self.charge(add(bytes, 1)?, bytes)?;
        let mut output = String::new();
        output
            .try_reserve_exact(bytes)
            .map_err(|_| ProofCheckError::ResourceLimit)?;
        output.push_str(prefix);
        output.push_str(name);
        Ok(output)
    }

    pub(super) fn diagnostic(&mut self, names: &[&str]) -> Result<(), ProofCheckError> {
        // Ten bytes per source byte covers Debug escaping, including Unicode
        // escapes. Fixed text, quote marks, and three usize values fit in 256.
        let mut bytes = 256;
        for name in names {
            self.charge(1, 0)?;
            bytes = add(bytes, mul(name.len(), 10)?)?;
        }
        // Formatting may grow its scratch buffer geometrically before moving
        // that String into the error; precharge allocation slack as well.
        self.charge(bytes, mul(bytes, 2)?)
    }

    pub(super) fn lookup(&mut self, name: &str, entries: usize) -> Result<(), ProofCheckError> {
        // Fixed hashing is deterministic, not collision-proof. Account for
        // every possible key comparison and the hash/control-byte walk.
        self.charge(mul(lookup_comparisons(entries)?, add(name.len(), 2)?)?, 0)
    }

    fn table_entry<T>(&mut self) -> Result<(), ProofCheckError> {
        // Own grow-only tables: amortized geometric slack is paid on each
        // insertion before any reserve, never inferred from term count.
        self.charge(1, add(mul(size_of::<T>(), 4)?, 128)?)
    }

    fn name_set_entry(
        &mut self,
        names: &HashSet<String>,
        name: &str,
    ) -> Result<(), ProofCheckError> {
        self.lookup(name, names.len())?;
        let growing = names.len() == names.capacity();
        if growing {
            self.charge(mul(names.len(), add(names.len(), 1)?)?, 0)?;
            for old in names {
                self.charge(add(old.len(), 1)?, 0)?;
            }
        }
        self.table_entry::<String>()
    }

    pub(super) fn insert_name(
        &mut self,
        names: &mut HashSet<String>,
        name: &str,
    ) -> Result<bool, ProofCheckError> {
        self.name_set_entry(names, name)?;
        let owned = self.prefixed_name("", name)?;
        names
            .try_reserve(1)
            .map_err(|_| ProofCheckError::ResourceLimit)?;
        Ok(names.insert(owned))
    }

    pub(super) fn name_map_entry<V>(
        &mut self,
        names: &HashMap<String, V>,
        name: &str,
    ) -> Result<(), ProofCheckError> {
        self.lookup(name, names.len())?;
        let growing = names.len() == names.capacity();
        if growing {
            self.charge(mul(names.len(), add(names.len(), 1)?)?, 0)?;
            for old in names.keys() {
                self.charge(add(old.len(), 1)?, 0)?;
            }
        }
        self.table_entry::<(String, V)>()
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
