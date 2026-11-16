// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Conservative per-operation accounting, without hashing or cloning sorts.

use std::mem::size_of;

use super::{ProofCheckError, Sort};

pub(super) struct ContextMeter<'a> {
    progress: &'a mut dyn FnMut(usize, usize) -> bool,
}

fn add(left: usize, right: usize) -> Result<usize, ProofCheckError> {
    left.checked_add(right)
        .ok_or(ProofCheckError::ResourceLimit)
}

fn mul(left: usize, right: usize) -> Result<usize, ProofCheckError> {
    left.checked_mul(right)
        .ok_or(ProofCheckError::ResourceLimit)
}

impl<'a> ContextMeter<'a> {
    pub(super) fn new(progress: &'a mut dyn FnMut(usize, usize) -> bool) -> Self {
        Self { progress }
    }

    pub(super) fn charge(&mut self, work: usize, bytes: usize) -> Result<(), ProofCheckError> {
        if (self.progress)(work, bytes) {
            Ok(())
        } else {
            Err(ProofCheckError::ResourceLimit)
        }
    }

    pub(super) fn lookup(&mut self, name: &str, entries: usize) -> Result<(), ProofCheckError> {
        // alloc's btree/node.rs has B=6, at most 11 keys and 12 edges per
        // node. Internal branching is >=2, so bit_length(entries)+1 bounds
        // the visited levels. Also retain the full-key-scan upper bound.
        let levels = add(entries.bit_width() as usize, 1)?;
        let comparisons = add(entries, 1)?.min(mul(levels, 12)?);
        self.charge(add(mul(comparisons, add(name.len(), 1)?)?, levels)?, 0)
    }

    pub(super) fn iterate(&mut self, entries: usize) -> Result<(), ProofCheckError> {
        // Each edge of an ordered full-tree walk is traversed at most twice.
        self.charge(add(mul(entries, 2)?, 1)?, 0)
    }

    pub(super) fn insert<K, V>(
        &mut self,
        name: &str,
        entries: usize,
    ) -> Result<(), ProofCheckError> {
        self.lookup(name, entries)?;
        // One split can allocate at most one sibling per visited level, plus
        // a new root. alloc's B=6 node stores 11 (K,V) slots, 12 edges and a
        // parent/length header. 32 slots conservatively cover that layout,
        // padding and key/edge movement without charging the entire tree.
        let nodes = add(entries.bit_width() as usize, 2)?;
        let slot = add(size_of::<(K, V)>(), size_of::<usize>())?;
        self.charge(mul(nodes, 32)?, mul(mul(nodes, 32)?, slot)?)
    }

    pub(super) fn copy_name(&mut self, name: &str) -> Result<String, ProofCheckError> {
        self.charge(add(name.len(), 1)?, name.len())?;
        Ok(name.to_owned())
    }

    pub(super) fn tester(&mut self, constructor: &str) -> Result<String, ProofCheckError> {
        let len = add(constructor.len(), 3)?;
        self.charge(add(len, 1)?, mul(len, 2)?)?;
        Ok(format!("is-{constructor}"))
    }

    pub(super) fn invalid<T>(
        &mut self,
        message: &'static str,
        names: &[&str],
    ) -> Result<T, ProofCheckError> {
        let mut bound = add(message.len(), 16)?;
        for name in names {
            // Debug escaping is bounded by ten bytes per input byte.
            bound = add(bound, add(mul(name.len(), 10)?, 4)?)?;
        }
        // Include geometric String growth and copying in the diagnostic debit.
        let bound = mul(bound, 4)?;
        self.charge(bound, bound)?;
        Err(ProofCheckError::InvalidDatatypeSignatureContext {
            reason: format!("{message}: {names:?}"),
        })
    }

    pub(super) fn equal_names(&mut self, left: &str, right: &str) -> Result<bool, ProofCheckError> {
        self.charge(add(add(left.len(), right.len())?, 1)?, 0)?;
        Ok(left == right)
    }

    pub(super) fn equal_sorts(
        &mut self,
        left: &Sort,
        right: &Sort,
    ) -> Result<bool, ProofCheckError> {
        // Validate BOTH complete trees before derived recursive Eq can run.
        // Every node/name is debited for the walk and subsequent comparison.
        self.sort(left, 0)?;
        self.sort(right, 0)?;
        self.charge(0, 0)?;
        Ok(left == right)
    }

    pub(super) fn sort(&mut self, sort: &Sort, depth: usize) -> Result<(), ProofCheckError> {
        self.charge(2, 0)?;
        if depth > 256 {
            return Err(ProofCheckError::ResourceLimit);
        }
        match sort {
            Sort::Array(array) => {
                self.sort(&array.index_sort, depth + 1)?;
                self.sort(&array.element_sort, depth + 1)
            }
            Sort::Seq(element) => self.sort(element, depth + 1),
            Sort::Uninterpreted(name) | Sort::TypeVar(name) | Sort::FiniteDomain(name, _) => {
                self.charge(mul(add(name.len(), 1)?, 2)?, 0)
            }
            Sort::Datatype(datatype) => {
                self.charge(mul(add(datatype.name.len(), 1)?, 2)?, 0)?;
                for constructor in &datatype.constructors {
                    self.charge(mul(add(constructor.name.len(), 1)?, 2)?, 0)?;
                    for field in &constructor.fields {
                        self.charge(mul(add(field.name.len(), 1)?, 2)?, 0)?;
                        self.sort(&field.sort, depth + 1)?;
                    }
                }
                Ok(())
            }
            Sort::Bool
            | Sort::Int
            | Sort::Real
            | Sort::BitVec(_)
            | Sort::String
            | Sort::RegLan
            | Sort::FloatingPoint(..)
            | Sort::Char => Ok(()),
            _ => Err(ProofCheckError::ResourceLimit),
        }
    }
}
