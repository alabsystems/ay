// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! In-place heapsort (Williams, CACM 7(6), 1964, Algorithm 232).
//! Each comparison/swap is admitted explicitly; no opaque sorting call needs
//! an assumed implementation-specific work bound or unpriced scratch buffer.

use super::{storage, CountedAdmission, Literal, Result};

pub(super) struct Scratch {
    literals: Vec<Literal>,
}

impl Scratch {
    pub(super) fn new() -> Self {
        Self {
            literals: Vec::new(),
        }
    }

    pub(super) fn literals(&self) -> &[Literal] {
        &self.literals
    }

    pub(super) fn normalize(
        &mut self,
        clause: &[Literal],
        owner: &CountedAdmission,
    ) -> Result<bool> {
        owner.admit(1, 0)?;
        self.literals.clear();
        storage::append_literals(&mut self.literals, clause, owner)?;
        heapsort(&mut self.literals, owner)?;
        let mut previous: Option<Literal> = None;
        let mut written = 0;
        let mut tautology = false;
        for index in 0..self.literals.len() {
            owner.admit(1, 0)?;
            let literal = self.literals[index];
            if let Some(last) = previous {
                if last == literal {
                    continue;
                }
                tautology |= last.variable() == literal.variable();
            }
            owner.admit(1, size_of::<Literal>())?;
            self.literals[written] = literal;
            written += 1;
            previous = Some(literal);
        }
        owner.admit(1, 0)?;
        self.literals.truncate(written);
        Ok(tautology)
    }
}

fn heapsort(literals: &mut [Literal], owner: &CountedAdmission) -> Result<()> {
    owner.admit(1, 0)?;
    let end = literals.len();
    for root in (0..end / 2).rev() {
        sift_down(literals, root, end, owner)?;
    }
    for end in (1..end).rev() {
        swap(literals, 0, end, owner)?;
        sift_down(literals, 0, end, owner)?;
    }
    Ok(())
}

fn sift_down(
    literals: &mut [Literal],
    mut root: usize,
    end: usize,
    owner: &CountedAdmission,
) -> Result<()> {
    loop {
        owner.admit(1, 0)?;
        let Some(left) = root.checked_mul(2).and_then(|index| index.checked_add(1)) else {
            return Ok(()); // An unrepresentable child is beyond this slice.
        };
        if left >= end {
            return Ok(());
        }
        let mut child = left;
        if left + 1 < end {
            owner.admit(1, 0)?;
            if literals[left] < literals[left + 1] {
                child = left + 1;
            }
        }
        owner.admit(1, 0)?;
        if literals[root] >= literals[child] {
            return Ok(());
        }
        swap(literals, root, child, owner)?;
        root = child;
    }
}

fn swap(
    literals: &mut [Literal],
    left: usize,
    right: usize,
    owner: &CountedAdmission,
) -> Result<()> {
    owner.admit(2, 2 * size_of::<Literal>())?;
    literals.swap(left, right);
    Ok(())
}

// Exercise a stop caused by actual scratch disposal before the public fence.
// The production buffer contains only Copy literals and needs no Drop impl.
#[cfg(test)]
std::thread_local! {
    pub(super) static AFTER_SCRATCH_DROP: std::cell::RefCell<Option<Box<dyn FnOnce()>>> =
        std::cell::RefCell::new(None);
}

#[cfg(test)]
impl Drop for Scratch {
    fn drop(&mut self) {
        drop(std::mem::take(&mut self.literals));
        AFTER_SCRATCH_DROP.with(|hook| {
            if let Some(hook) = hook.borrow_mut().take() {
                hook();
            }
        });
    }
}
