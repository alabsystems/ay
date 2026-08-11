// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Finite integer domains with efficient bounds tracking.
//!
//! Domains represent the set of values an integer variable can take.
//! Dense intervals use a bounds-only representation regardless of width.
//! Explicit non-contiguous domains use an allowed-value bitset only when their
//! span is at most [`MAX_SPARSE_DOMAIN_SPAN`]. Removing values from a wider
//! dense interval records a bounded sorted exclusion list, so a single hole
//! never materializes the full interval.

use smallvec::SmallVec;

/// Largest inclusive span materialized for an explicit sparse domain.
///
/// Dense domains remain lazy; this bound applies only when a bitset is needed
/// to preserve holes from an explicit value list.
pub const MAX_SPARSE_DOMAIN_SPAN: u128 = 1 << 20;

/// Largest number of values returned by the eager enumeration API.
///
/// Domains themselves may be much larger because dense intervals are stored
/// lazily. This limit prevents a public `values()` call from turning such a
/// domain into an unbounded allocation.
pub const MAX_MATERIALIZED_DOMAIN_VALUES: u64 = 1 << 20;

/// A finite integer domain could not be constructed safely.
#[derive(Debug, Clone, Copy, PartialEq, Eq, thiserror::Error)]
#[non_exhaustive]
pub enum DomainCreationError {
    /// Dense bounds describe an empty interval.
    #[error("empty domain: lower bound {lb} exceeds upper bound {ub}")]
    EmptyBounds {
        /// Inclusive lower bound.
        lb: i64,
        /// Inclusive upper bound.
        ub: i64,
    },
    /// An explicit value list was empty.
    #[error("explicit domain contains no values")]
    EmptyValues,
    /// The inclusive span is wider than CP's signed-size arithmetic supports.
    #[error("domain span {span} exceeds the maximum supported {max}")]
    SpanTooLarge {
        /// Requested inclusive span.
        span: u128,
        /// Largest supported inclusive span.
        max: u128,
    },
    /// A sparse value list would require an excessively large hole bitset.
    #[error("sparse domain span {span} exceeds the materialization limit {max}")]
    SparseSpanTooLarge {
        /// Requested inclusive span.
        span: u128,
        /// Largest materialized sparse span.
        max: u128,
    },
}

/// A domain was too large for eager value enumeration.
#[derive(Debug, Clone, Copy, PartialEq, Eq, thiserror::Error)]
pub enum DomainEnumerationError {
    /// Materializing every allowed value would exceed the allocation limit.
    #[error("domain has {size} values, exceeding the enumeration limit {max}")]
    TooManyValues {
        /// Exact number of currently allowed values.
        size: u64,
        /// Largest number the eager API will materialize.
        max: u64,
    },
}

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
    /// Explicit membership information, if tracked.
    /// None = dense domain (every value in [lb..ub] is present).
    holes: Option<DomainHoles>,
}

/// Bounded representations for non-dense membership.
#[derive(Debug, Clone, PartialEq, Eq)]
enum DomainHoles {
    /// Allowed-value bitset for an explicit sparse domain with a bounded span.
    AllowedBits(DomainBits),
    /// Sorted values removed from an otherwise dense, potentially huge range.
    /// This avoids materializing the full span for one interior removal.
    ExcludedValues(SmallVec<[i64; 4]>),
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
    ///
    /// # Panics
    ///
    /// Panics if the interval is empty or its inclusive span exceeds
    /// `i64::MAX`. Use [`try_new`](Self::try_new) for untrusted bounds.
    pub fn new(lb: i64, ub: i64) -> Self {
        Self::try_new(lb, ub).expect("invalid finite integer domain")
    }

    /// Try to create a dense domain `[lb..=ub]`.
    pub fn try_new(lb: i64, ub: i64) -> Result<Self, DomainCreationError> {
        if lb > ub {
            return Err(DomainCreationError::EmptyBounds { lb, ub });
        }
        let span = inclusive_span(lb, ub);
        let max = i64::MAX as u128;
        if span > max {
            return Err(DomainCreationError::SpanTooLarge { span, max });
        }
        Ok(Self {
            lb,
            ub,
            holes: None,
        })
    }

    /// Create a singleton domain containing only one value.
    pub fn singleton(val: i64) -> Self {
        Self::new(val, val)
    }

    /// Create a domain from an explicit set of values.
    ///
    /// # Panics
    ///
    /// Panics when the value list is empty or its sparse span cannot be
    /// materialized. Use [`try_from_values`](Self::try_from_values) for
    /// untrusted values.
    pub fn from_values(values: &[i64]) -> Self {
        Self::try_from_values(values).expect("invalid explicit integer domain")
    }

    /// Try to create a domain from an explicit set of values.
    pub fn try_from_values(values: &[i64]) -> Result<Self, DomainCreationError> {
        if values.is_empty() {
            return Err(DomainCreationError::EmptyValues);
        }
        let mut sorted = values.to_vec();
        sorted.sort_unstable();
        sorted.dedup();

        let lb = sorted[0];
        let ub = sorted[sorted.len() - 1];
        let span = inclusive_span(lb, ub);
        let max = i64::MAX as u128;
        if span > max {
            return Err(DomainCreationError::SpanTooLarge { span, max });
        }

        // If all values present, use dense representation
        if span == sorted.len() as u128 {
            return Self::try_new(lb, ub);
        }
        if span > MAX_SPARSE_DOMAIN_SPAN {
            return Err(DomainCreationError::SparseSpanTooLarge {
                span,
                max: MAX_SPARSE_DOMAIN_SPAN,
            });
        }
        let span = usize::try_from(span).map_err(|_| DomainCreationError::SparseSpanTooLarge {
            span,
            max: MAX_SPARSE_DOMAIN_SPAN,
        })?;

        // Sparse: build bitset
        let num_words = span.div_ceil(64);
        let mut bits = SmallVec::from_elem(0u64, num_words);
        for &v in &sorted {
            let offset = usize::try_from(i128::from(v) - i128::from(lb))
                .expect("checked sparse span keeps every offset representable");
            bits[offset / 64] |= 1u64 << (offset % 64);
        }

        Ok(Self {
            lb,
            ub,
            holes: Some(DomainHoles::AllowedBits(DomainBits { base: lb, bits })),
        })
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
            Some(DomainHoles::AllowedBits(bits)) => {
                let offset = v - bits.base;
                if offset < 0 {
                    return false;
                }
                let offset = offset as usize;
                let word = offset / 64;
                let bit = offset % 64;
                word < bits.bits.len() && (bits.bits[word] & (1u64 << bit)) != 0
            }
            Some(DomainHoles::ExcludedValues(values)) => values.binary_search(&v).is_err(),
        }
    }

    fn exclude_interior(&mut self, value: i64) {
        match &mut self.holes {
            None if inclusive_span(self.lb, self.ub) <= MAX_SPARSE_DOMAIN_SPAN => {
                let span = usize::try_from(inclusive_span(self.lb, self.ub))
                    .expect("bounded bitset span is representable");
                let num_words = span.div_ceil(64);
                let mut bits = SmallVec::from_elem(!0u64, num_words);
                let excess_bits = num_words * 64 - span;
                if excess_bits > 0 {
                    let keep_bits = 64 - excess_bits;
                    let mask = (1u64 << keep_bits) - 1;
                    let last = bits
                        .last_mut()
                        .expect("non-empty domain allocates at least one word");
                    *last &= mask;
                }
                let offset = usize::try_from(i128::from(value) - i128::from(self.lb))
                    .expect("interior value has a representable bitset offset");
                bits[offset / 64] &= !(1u64 << (offset % 64));
                self.holes = Some(DomainHoles::AllowedBits(DomainBits {
                    base: self.lb,
                    bits,
                }));
            }
            None => {
                self.holes = Some(DomainHoles::ExcludedValues(SmallVec::from_slice(&[value])));
            }
            Some(DomainHoles::AllowedBits(bits)) => {
                let offset = usize::try_from(i128::from(value) - i128::from(bits.base))
                    .expect("allowed-bit value offset is representable");
                bits.bits[offset / 64] &= !(1u64 << (offset % 64));
            }
            Some(DomainHoles::ExcludedValues(values)) => {
                if let Err(index) = values.binary_search(&value) {
                    values.insert(index, value);
                }
            }
        }
    }

    pub(crate) fn missing_values(&self) -> Vec<i64> {
        match &self.holes {
            None => Vec::new(),
            Some(DomainHoles::AllowedBits(_)) => {
                (self.lb..=self.ub).filter(|&v| !self.contains(v)).collect()
            }
            Some(DomainHoles::ExcludedValues(values)) => values
                .iter()
                .copied()
                .filter(|&value| value >= self.lb && value <= self.ub)
                .collect(),
        }
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
            None => u64::try_from(inclusive_span(self.lb, self.ub))
                .expect("domain construction bounds dense size to i64::MAX"),
            Some(DomainHoles::AllowedBits(bits)) => self.count_sparse_values(bits),
            Some(DomainHoles::ExcludedValues(values)) => {
                let excluded = values
                    .iter()
                    .filter(|&&value| value >= self.lb && value <= self.ub)
                    .count() as u64;
                u64::try_from(inclusive_span(self.lb, self.ub))
                    .expect("domain construction bounds dense size to i64::MAX")
                    - excluded
            }
        }
    }

    /// Enumerate all currently allowed values.
    ///
    /// # Panics
    ///
    /// Panics deterministically, before allocating, when the domain contains
    /// more than [`MAX_MATERIALIZED_DOMAIN_VALUES`] values. Use
    /// [`try_values`](Self::try_values) when the domain size is untrusted.
    pub fn values(&self) -> Vec<i64> {
        self.try_values()
            .expect("domain is too large for eager value enumeration")
    }

    /// Fallible eager enumeration of all currently allowed values.
    pub fn try_values(&self) -> Result<Vec<i64>, DomainEnumerationError> {
        let size = self.size();
        if size > MAX_MATERIALIZED_DOMAIN_VALUES {
            return Err(DomainEnumerationError::TooManyValues {
                size,
                max: MAX_MATERIALIZED_DOMAIN_VALUES,
            });
        }
        match &self.holes {
            None => Ok((self.lb..=self.ub).collect()),
            Some(DomainHoles::AllowedBits(bits)) => Ok(self.collect_sparse_values(bits)),
            Some(DomainHoles::ExcludedValues(_)) => Ok((self.lb..=self.ub)
                .filter(|&value| self.value_present(value))
                .collect()),
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
            self.exclude_interior(val);
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
        let start_offset = usize::try_from(i128::from(self.lb) - i128::from(bits.base))
            .expect("sparse lower-bound offset is representable");
        let end_offset = usize::try_from(i128::from(self.ub) - i128::from(bits.base))
            .expect("sparse upper-bound offset is representable");
        (start_offset, end_offset)
    }
}

#[inline]
fn inclusive_span(lb: i64, ub: i64) -> u128 {
    (i128::from(ub) - i128::from(lb) + 1) as u128
}

/// Sentinel error: a propagator narrowed a domain to empty.
#[derive(Debug, Clone, Copy, PartialEq, Eq, thiserror::Error)]
#[error("domain wipeout (empty domain)")]
pub struct DomainWipeout;

#[cfg(test)]
#[path = "domain_tests.rs"]
mod tests;
