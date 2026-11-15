// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Exact guarded Ackermann/select congruence over the completed free reads.
//! Every pair is considered; exhaustion refuses rather than truncating closure.
//! This is the ordinary kernel's EUF/select congruence schema, also recognized
//! by ay-proof's EufCongruent checker. Emitting it is not proof admission.

use super::*;

impl Expansion<'_, '_, '_> {
    pub(super) fn free_congruence(&mut self) -> Result<()> {
        for left_at in 0..self.out.free.len() {
            self.owner.admit(1, 0)?;
            let Unresolved::FreeRead { read: left_read } = self.out.free[left_at] else {
                return Err(Error::Invalid);
            };
            let left = self.out.reads[left_read];
            for right_at in left_at + 1..self.out.free.len() {
                self.owner.admit(1, 0)?;
                let Unresolved::FreeRead { read: right_read } = self.out.free[right_at] else {
                    return Err(Error::Invalid);
                };
                let right = self.out.reads[right_read];
                if left.array != right.array {
                    continue;
                }
                // request() memoizes (array,index), so no identical pair exists.
                if left.index == right.index
                    || left.index_sort != right.index_sort
                    || left.element_sort != right.element_sort
                {
                    return Err(Error::Invalid);
                }
                let guard = self
                    .builder
                    .apply(CountedBuiltin::Eq, &[left.index, right.index])?;
                let not_guard = self.builder.apply(CountedBuiltin::Not, &[guard])?;
                let conclusion = self
                    .builder
                    .apply(CountedBuiltin::Eq, &[left.select, right.select])?;
                self.emit(
                    Derivation::FreeReadCongruence {
                        array: left.array,
                        left_read,
                        right_read,
                    },
                    Some(not_guard),
                    conclusion,
                )?;
            }
        }
        self.owner.check()?;
        Ok(())
    }
}
