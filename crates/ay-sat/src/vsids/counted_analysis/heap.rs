// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Admission inside the real sparse heap engine. Buffer capacity grows at the
//! original pushes/resizes; no ancestor-union estimate changes its schedule.

use super::*;
use std::convert::Infallible;

pub(in crate::vsids) trait HeapPolicy {
    type Error;
    fn work(&self, units: usize) -> std::result::Result<(), Self::Error>;
    fn reserve<T>(
        &self,
        values: &mut Vec<T>,
        additional: usize,
    ) -> std::result::Result<(), Self::Error>;
    fn sift(&self, s: &VSIDS) -> std::result::Result<(), Self::Error>;
    fn rebuild(&self, s: &VSIDS) -> std::result::Result<(), Self::Error>;
    fn debug_heap(&self, s: &VSIDS) -> std::result::Result<(), Self::Error>;
    fn sparse_entry(&self, s: &VSIDS) -> std::result::Result<(), Self::Error>;
}
pub(in crate::vsids) struct HeapOrdinary;
pub(super) struct HeapCounted<'a>(pub(super) &'a CountedAdmission);

impl HeapPolicy for HeapOrdinary {
    type Error = Infallible;
    fn work(&self, _: usize) -> std::result::Result<(), Infallible> {
        Ok(())
    }
    fn reserve<T>(&self, _: &mut Vec<T>, _: usize) -> std::result::Result<(), Infallible> {
        Ok(())
    }
    fn sift(&self, _: &VSIDS) -> std::result::Result<(), Infallible> {
        Ok(())
    }
    fn rebuild(&self, _: &VSIDS) -> std::result::Result<(), Infallible> {
        Ok(())
    }
    fn debug_heap(&self, _: &VSIDS) -> std::result::Result<(), Infallible> {
        Ok(())
    }
    fn sparse_entry(&self, _: &VSIDS) -> std::result::Result<(), Infallible> {
        Ok(())
    }
}
impl HeapPolicy for HeapCounted<'_> {
    type Error = CountedAdmissionError;
    fn work(&self, units: usize) -> Result<()> {
        self.0.admit(units, 0)
    }
    fn reserve<T>(&self, values: &mut Vec<T>, additional: usize) -> Result<()> {
        try_reserve(self.0, values, additional)
    }
    fn sift(&self, s: &VSIDS) -> Result<()> {
        self.0.admit(s.heap.len().bit_width() as usize + 1, 0)
    }
    fn rebuild(&self, s: &VSIDS) -> Result<()> {
        s.prepare_analysis_rebuild(self.0)
    }
    fn debug_heap(&self, s: &VSIDS) -> Result<()> {
        s.prepare_analysis_heap_debug(self.0)
    }
    fn sparse_entry(&self, s: &VSIDS) -> Result<()> {
        self.0.admit(80, size_of::<([u32; 32], [u32; 32])>())?;
        if !s.heap_repair_scratch.is_empty() || !s.heap_repair_order.is_empty() {
            return Err(invalid(
                self.0,
                "activity heap repair scratch is not retired",
            ));
        }
        Ok(())
    }
}

impl VSIDS {
    pub(super) fn prepare_analysis_heap(
        &self,
        in_heap: usize,
        owner: &CountedAdmission,
    ) -> Result<()> {
        owner.admit(1, 0)?;
        if in_heap == 0 {
            return Ok(());
        }
        if in_heap == 1 {
            let depth = self.heap.len().bit_width() as usize + 1;
            pay_product(owner, depth, 2)?;
        } else {
            self.prepare_analysis_rebuild(owner)?;
        }
        self.prepare_analysis_heap_debug(owner)
    }
    fn prepare_analysis_rebuild(&self, owner: &CountedAdmission) -> Result<()> {
        let depth = self.heap.len().bit_width() as usize + 1;
        pay_product(owner, self.heap.len() / 2, depth)?;
        self.prepare_analysis_heap_debug(owner)
    }
    pub(super) fn prepare_analysis_rescale(&self, owner: &CountedAdmission) -> Result<()> {
        owner.admit(self.activities.len(), 0)?;
        self.prepare_analysis_rebuild(owner)?;
        #[cfg(debug_assertions)]
        owner.admit(self.activities.len(), 0)?;
        Ok(())
    }
    fn prepare_analysis_heap_debug(&self, owner: &CountedAdmission) -> Result<()> {
        #[cfg(debug_assertions)]
        {
            pay_product(owner, self.heap.len(), 2)?;
            owner.admit(self.heap_pos.len(), 0)?;
        }
        #[cfg(not(debug_assertions))]
        let _ = owner;
        Ok(())
    }
}
