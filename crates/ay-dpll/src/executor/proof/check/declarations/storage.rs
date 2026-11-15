// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Pre-copy storage prices match the bundle construction payload vocabulary.
//! Hash-table lookups, allocator bookkeeping and destruction are opaque; this
//! is cumulative logical work/owned payload accounting, not an RSS ceiling.

use std::mem::size_of;

use ay_core::{ArraySort, DatatypeConstructor, DatatypeField, Sort};
use ay_proof::ProofCheckError;

use super::Collected;

pub(in crate::executor::proof) struct Control<'a> {
    progress: &'a mut dyn FnMut(usize, usize) -> bool,
    refused: bool,
}

impl<'a> Control<'a> {
    pub(in crate::executor::proof) fn new(
        progress: &'a mut dyn FnMut(usize, usize) -> bool,
    ) -> Self {
        Self {
            progress,
            refused: false,
        }
    }

    pub(in crate::executor::proof) fn charge(
        &mut self,
        work: usize,
        bytes: usize,
    ) -> Collected<()> {
        if self.refused {
            return Err(ProofCheckError::ResourceLimit);
        }
        self.refused = true;
        if !(self.progress)(work, bytes) {
            return Err(ProofCheckError::ResourceLimit);
        }
        self.refused = false;
        Ok(())
    }

    pub(in crate::executor::proof) fn run<T>(
        &mut self,
        operation: impl FnOnce(&mut Self) -> Collected<T>,
    ) -> Collected<T> {
        self.charge(0, 0)?;
        let result = operation(self);
        if matches!(&result, Err(ProofCheckError::ResourceLimit)) {
            self.refused = true;
        }
        // Temporary inventories from a failed operation have been dropped.
        // Refusal is terminal even if an inner callback panic was caught.
        self.charge(0, 0)?;
        result
    }

    pub(in crate::executor::proof) fn vector<T>(&mut self, count: usize) -> Collected<Vec<T>> {
        let bytes = count
            .checked_mul(size_of::<T>())
            .ok_or(ProofCheckError::ResourceLimit)?;
        self.charge(count, bytes)?;
        let mut result = Vec::new();
        result
            .try_reserve_exact(count)
            .map_err(|_| ProofCheckError::ResourceLimit)?;
        Ok(result)
    }

    pub(super) fn string(&mut self, value: &str) -> Collected<String> {
        self.charge(value.len(), value.len())?;
        let mut result = String::new();
        result
            .try_reserve_exact(value.len())
            .map_err(|_| ProofCheckError::ResourceLimit)?;
        result.push_str(value);
        Ok(result)
    }

    pub(super) fn sort(&mut self, sort: &Sort, depth: usize) -> Collected<()> {
        self.charge(1, 0)?;
        if depth > 256 {
            return Err(ProofCheckError::ResourceLimit);
        }
        match sort {
            Sort::Array(array) => {
                self.charge(1, size_of::<ArraySort>())?;
                self.sort(&array.index_sort, depth + 1)?;
                self.sort(&array.element_sort, depth + 1)
            }
            Sort::Seq(element) => {
                self.charge(1, size_of::<Sort>())?;
                self.sort(element, depth + 1)
            }
            Sort::Uninterpreted(name) | Sort::TypeVar(name) | Sort::FiniteDomain(name, _) => {
                self.charge(name.len(), name.len())
            }
            Sort::Datatype(datatype) => {
                self.charge(datatype.name.len(), datatype.name.len())?;
                self.slice::<DatatypeConstructor>(datatype.constructors.len())?;
                for constructor in &datatype.constructors {
                    self.charge(constructor.name.len(), constructor.name.len())?;
                    self.slice::<DatatypeField>(constructor.fields.len())?;
                    for field in &constructor.fields {
                        self.charge(field.name.len(), field.name.len())?;
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

    fn slice<T>(&mut self, count: usize) -> Collected<()> {
        let bytes = count
            .checked_mul(size_of::<T>())
            .ok_or(ProofCheckError::ResourceLimit)?;
        self.charge(count, bytes)
    }
}
