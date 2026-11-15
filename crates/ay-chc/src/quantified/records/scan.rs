// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

#[derive(Default)]
pub(super) struct Meter {
    occurrences: usize,
    names: usize,
    bytes: usize,
}

impl Meter {
    pub(super) fn bytes(&self) -> usize {
        self.bytes
    }

    fn scalar_payload(&mut self, sort: &ChcSort) -> ChcResult<()> {
        if let ChcSort::BitVec(width) = sort {
            if !(1..=crate::MAX_BITVECTOR_WIDTH).contains(width) {
                return Err(invalid("bitvector width limit"));
            }
            // Keep the original small-scalar allowance unchanged. Wide values
            // require explicit limb-sized work/copy admission per occurrence.
            if *width > 64 {
                let bytes = usize::try_from(width.div_ceil(8))
                    .map_err(|_| invalid("bitvector payload limit"))?;
                self.charge(bytes.div_ceil(64), bytes)?;
            }
        }
        Ok(())
    }

    fn charge(&mut self, occurrences: usize, bytes: usize) -> ChcResult<()> {
        self.occurrences = self
            .occurrences
            .checked_add(occurrences)
            .ok_or_else(|| invalid("sort work limit"))?;
        self.bytes = self
            .bytes
            .checked_add(bytes)
            .ok_or_else(|| invalid("record copy limit"))?;
        if self.occurrences > MAX_SORT_OCCURRENCES || self.bytes > MAX_REGISTRY_COPY_BYTES {
            return Err(invalid("record work/copy limit"));
        }
        Ok(())
    }

    pub(super) fn name(&mut self, name: &str) -> ChcResult<()> {
        if !shape::valid_name(name) {
            return Err(invalid("invalid or oversized record symbol"));
        }
        self.names = self
            .names
            .checked_add(name.len())
            .ok_or_else(|| invalid("record name limit"))?;
        if self.names > MAX_REGISTRY_NAME_BYTES {
            return Err(invalid("record name limit"));
        }
        self.charge(
            1,
            name.len()
                .checked_mul(4)
                .and_then(|n| n.checked_add(256))
                .ok_or_else(|| invalid("record copy limit"))?,
        )
    }

    /// Count leaves per root and charge every edge occurrence before queuing.
    /// Iterative traversal never recursively compares or clones hostile sorts.
    pub(super) fn sort(&mut self, root: &ChcSort, depth: usize) -> ChcResult<usize> {
        let mut pending = vec![(root, depth, 0usize)];
        let mut leaves = 0usize;
        while let Some((sort, depth, rank)) = pending.pop() {
            if depth > MAX_RECORD_DEPTH {
                return Err(invalid("record depth limit"));
            }
            self.charge(1, 0)?;
            if shape::field_sort(sort) {
                if matches!(sort, ChcSort::Array(..)) && rank >= MAX_ARRAY_RANK {
                    return Err(invalid("array rank limit"));
                }
                self.charge(
                    0,
                    if matches!(sort, ChcSort::Array(..)) {
                        192
                    } else {
                        64
                    },
                )?;
                if let ChcSort::Array(key, value) = sort {
                    self.scalar_payload(key)?;
                    self.scalar_payload(value)?;
                } else {
                    self.scalar_payload(sort)?;
                }
                leaves = leaves
                    .checked_add(1)
                    .ok_or_else(|| invalid("record leaf limit"))?;
                if leaves > MAX_FLATTENED_LEAVES {
                    return Err(invalid("record leaf limit"));
                }
                continue;
            }
            if let ChcSort::Array(key, value) = sort {
                if rank >= MAX_ARRAY_RANK
                    || !matches!(
                        key.as_ref(),
                        ChcSort::BitVec(1..=crate::MAX_BITVECTOR_WIDTH)
                    )
                {
                    return Err(invalid("array rank or index sort limit"));
                }
                // The key is a bounded scalar; the cell may carry a complete
                // record DAG. Rank must not reset while crossing that record.
                self.charge(2, 128)?;
                self.scalar_payload(key)?;
                pending.push((value.as_ref(), depth + 1, rank + 1));
                continue;
            }
            let ChcSort::Datatype { name, constructors } = sort else {
                return Err(invalid("unsupported record field sort"));
            };
            self.name(name)?;
            let [constructor] = constructors.as_slice() else {
                return Err(invalid("expected one constructor"));
            };
            self.name(&constructor.name)?;
            if constructor.selectors.is_empty() || constructor.selectors.len() > MAX_FIELDS {
                return Err(invalid("record field count limit"));
            }
            self.charge(constructor.selectors.len(), 0)?;
            for field in &constructor.selectors {
                self.name(&field.name)?;
            }
            pending
                .try_reserve(constructor.selectors.len())
                .map_err(|_| invalid("sort scan allocation"))?;
            pending.extend(
                constructor
                    .selectors
                    .iter()
                    .rev()
                    .map(|field| (&field.sort, depth + 1, rank)),
            );
        }
        Ok(leaves)
    }
}
