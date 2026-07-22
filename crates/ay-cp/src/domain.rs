// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Finite integer domains with efficient bounds tracking.
//!
//! Domains represent the set of values an integer variable can take.
//! Two representations are used depending on domain density:
//! - **Bounds-only** for large/continuous domains: just [lb, ub]
//! - **Sparse bitset** for small domains: explicit set of allowed values
//!
//! Following Chuffed's design: domains <= 1000 values use bitset,
//! larger domains use bounds-only with holes tracked lazily.

use smallvec::SmallVec;

/// A finite integer domain.
///
/// Represents the set of possible values for an integer variable.
/// Supports efficient bounds queries and domain narrowing.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Domain {
    /// Lower bound (inclusive)
    lb: i64,
    /// Upper bound (inclusive)
    ub: i64,
    /// Explicit holes in the domain, if tracked.
    /// None = dense domain (every value in [lb..ub] is present).
    /// Some(bits) = sparse domain with bitset relative to original lb.
    holes: Option<DomainBits>,
}

/// Bitset for tracking domain membership for small domains.
#[derive(Debug, Clone, PartialEq, Eq)]
struct DomainBits {
    /// Base offset for the bitset (original lower bound)
    base: i64,
    /// Bitset: bit i is set if value (base + i) is in the domain
    bits: SmallVec<[u64; 4]>,
}

impl Domain {
    /// Create a dense domain [lb..=ub].
    pub fn new(lb: i64, ub: i64) -> Self {
        assert!(lb <= ub, "empty domain: lb={lb} > ub={ub}");
        Self {
            lb,
            ub,
            holes: None,
        }
    }

    /// Create a singleton domain containing only one value.
    pub fn singleton(val: i64) -> Self {
        Self::new(val, val)
    }

    /// Create a domain from an explicit set of values.
    pub fn from_values(values: &[i64]) -> Self {
        assert!(!values.is_empty(), "empty domain");
        let mut sorted = values.to_vec();
        sorted.sort_unstable();
        sorted.dedup();

        let lb = sorted[0];
        let ub = sorted[sorted.len() - 1];
        let span = (ub - lb + 1) as usize;

        // If all values present, use dense representation
        if span == sorted.len() {
            return Self::new(lb, ub);
        }

        // Sparse: build bitset
        let num_words = span.div_ceil(64);
        let mut bits = SmallVec::from_elem(0u64, num_words);
        for &v in &sorted {
            let offset = (v - lb) as usize;
            bits[offset / 64] |= 1u64 << (offset % 64);
        }

        Self {
            lb,
            ub,
            holes: Some(DomainBits { base: lb, bits }),
        }
    }

    /// Lower bound.
    #[inline]
    pub fn lb(&self) -> i64 {
        self.lb
    }

    /// Upper bound.
    #[inline]
    pub fn ub(&self) -> i64 {
        self.ub
    }

    #[inline]
    fn value_present(&self, v: i64) -> bool {
        match &self.holes {
            None => true,
            Some(bits) => {
                let offset = v - bits.base;
                if offset < 0 {
                    return false;
                }
                let offset = offset as usize;
                let word = offset / 64;
                let bit = offset % 64;
                word < bits.bits.len() && (bits.bits[word] & (1u64 << bit)) != 0
            }
        }
    }

    fn materialize_sparse(&mut self) -> &mut DomainBits {
        self.holes.get_or_insert_with(|| {
            let span = (self.ub - self.lb + 1) as usize;
            let num_words = span.div_ceil(64);
            let mut bits = SmallVec::from_elem(!0u64, num_words);
            let excess_bits = num_words * 64 - span;
            if excess_bits > 0 {
                let keep_bits = 64 - excess_bits;
                let mask = (1u64 << keep_bits) - 1;
                let last = bits
                    .last_mut()
                    .expect("invariant: dense domain span allocates at least one word");
                *last &= mask;
            }
            DomainBits {
                base: self.lb,
                bits,
            }
        })
    }

    pub(crate) fn missing_values(&self) -> Vec<i64> {
        if self.holes.is_none() {
            return Vec::new();
        }
        (self.lb..=self.ub).filter(|&v| !self.contains(v)).collect()
    }

    pub(crate) fn restore_lb(&mut self, prev_lb: i64) {
        self.lb = prev_lb;
    }

    pub(crate) fn restore_ub(&mut self, prev_ub: i64) {
        self.ub = prev_ub;
    }

    /// Domain size (number of values). Exact for sparse, span for dense.
    #[inline]
    pub fn size(&self) -> u64 {
        match &self.holes {
            None => (self.ub - self.lb + 1) as u64,
            Some(bits) => self.count_sparse_values(bits),
        }
    }

    /// Enumerate all currently allowed values.
    pub fn values(&self) -> Vec<i64> {
        match &self.holes {
            None => (self.lb..=self.ub).collect(),
            Some(bits) => self.collect_sparse_values(bits),
        }
    }

    /// Is this a singleton (fixed variable)?
    #[inline]
    pub fn is_fixed(&self) -> bool {
        self.lb == self.ub
    }

    /// Is value `v` in this domain?
    #[inline]
    pub fn contains(&self, v: i64) -> bool {
        if v < self.lb || v > self.ub {
            return false;
        }
        self.value_present(v)
    }

    /// Tighten the lower bound. Returns true if domain changed.
    /// Returns Err if domain becomes empty.
    pub fn set_lb(&mut self, new_lb: i64) -> Result<bool, DomainWipeout> {
        if new_lb <= self.lb {
            return Ok(false);
        }
        if new_lb > self.ub {
            return Err(DomainWipeout);
        }
        let next_lb = match &self.holes {
            None => new_lb,
            Some(_) => {
                let mut candidate = new_lb;
                while candidate <= self.ub && !self.value_present(candidate) {
                    candidate += 1;
                }
                if candidate > self.ub {
                    return Err(DomainWipeout);
                }
                candidate
            }
        };
        self.lb = next_lb;
        Ok(true)
    }

    /// Tighten the upper bound. Returns true if domain changed.
    /// Returns Err if domain becomes empty.
    pub fn set_ub(&mut self, new_ub: i64) -> Result<bool, DomainWipeout> {
        if new_ub >= self.ub {
            return Ok(false);
        }
        if new_ub < self.lb {
            return Err(DomainWipeout);
        }
        let next_ub = match &self.holes {
            None => new_ub,
            Some(_) => {
                let mut candidate = new_ub;
                while candidate >= self.lb && !self.value_present(candidate) {
                    candidate -= 1;
                }
                if candidate < self.lb {
                    return Err(DomainWipeout);
                }
                candidate
            }
        };
        self.ub = next_ub;
        Ok(true)
    }

    /// Remove a single value. Returns true if domain changed.
    /// Returns Err if domain becomes empty.
    pub fn remove(&mut self, val: i64) -> Result<bool, DomainWipeout> {
        if !self.contains(val) {
            return Ok(false);
        }
        if self.is_fixed() {
            return Err(DomainWipeout);
        }

        // Update bounds if removing an endpoint
        if val == self.lb {
            self.lb += 1;
            // Skip holes at the new lower bound
            while self.lb <= self.ub && !self.contains(self.lb) {
                self.lb += 1;
            }
        } else if val == self.ub {
            self.ub -= 1;
            while self.ub >= self.lb && !self.contains(self.ub) {
                self.ub -= 1;
            }
        } else {
            let bits = self.materialize_sparse();
            let offset = (val - bits.base) as usize;
            bits.bits[offset / 64] &= !(1u64 << (offset % 64));
        }

        if self.lb > self.ub {
            return Err(DomainWipeout);
        }
        Ok(true)
    }

    /// Fix this variable to a single value.
    /// Returns Err if value not in domain.
    pub fn fix(&mut self, val: i64) -> Result<bool, DomainWipeout> {
        if !self.contains(val) {
            return Err(DomainWipeout);
        }
        if self.is_fixed() {
            return Ok(false);
        }
        self.lb = val;
        self.ub = val;
        self.holes = None;
        Ok(true)
    }

    fn collect_sparse_values(&self, bits: &DomainBits) -> Vec<i64> {
        let (start_offset, end_offset) = self.sparse_offsets(bits);
        let start_word = start_offset / 64;
        let end_word = end_offset / 64;
        let mut values = Vec::with_capacity(self.count_sparse_values(bits) as usize);

        for word_idx in start_word..=end_word {
            let mut word = bits.bits[word_idx];
            if word_idx == start_word {
                let first_bit = start_offset % 64;
                word &= !0u64 << first_bit;
            }
            if word_idx == end_word {
                let last_bit = end_offset % 64;
                let mask = if last_bit == 63 {
                    !0u64
                } else {
                    (1u64 << (last_bit + 1)) - 1
                };
                word &= mask;
            }

            while word != 0 {
                let bit = word.trailing_zeros() as usize;
                let offset = word_idx * 64 + bit;
                values.push(bits.base + offset as i64);
                word &= word - 1;
            }
        }

        values
    }

    fn count_sparse_values(&self, bits: &DomainBits) -> u64 {
        let (start_offset, end_offset) = self.sparse_offsets(bits);
        let start_word = start_offset / 64;
        let end_word = end_offset / 64;
        let mut count = 0u64;

        for word_idx in start_word..=end_word {
            let mut word = bits.bits[word_idx];
            if word_idx == start_word {
                let first_bit = start_offset % 64;
                word &= !0u64 << first_bit;
            }
            if word_idx == end_word {
                let last_bit = end_offset % 64;
                let mask = if last_bit == 63 {
                    !0u64
                } else {
                    (1u64 << (last_bit + 1)) - 1
                };
                word &= mask;
            }
            count += u64::from(word.count_ones());
        }

        count
    }

    fn sparse_offsets(&self, bits: &DomainBits) -> (usize, usize) {
        let start_offset = (self.lb - bits.base) as usize;
        let end_offset = (self.ub - bits.base) as usize;
        (start_offset, end_offset)
    }
}

/// Sentinel error: a propagator narrowed a domain to empty.
#[derive(Debug, Clone, Copy, PartialEq, Eq, thiserror::Error)]
#[error("domain wipeout (empty domain)")]
pub struct DomainWipeout;

#[cfg(test)]
#[path = "domain_tests.rs"]
mod tests;
