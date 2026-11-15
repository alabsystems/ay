// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

const MAX_WORK: usize = 1_048_576;
const MAX_COPY: usize = 16 * 1024 * 1024;
const MAX_OUTPUT: usize = 8 * 1024 * 1024;

pub(super) struct Budget {
    pub(super) work: usize,
    pub(super) bytes: usize,
    pub(super) output: usize,
    pub(super) stopped: bool,
    // Literal payload/conversion/output scratch is precharged to THIS byte
    // ledger before calling Decoder. Its remaining counters are an additional
    // tighter guard, not a second independent 16 MiB retention allowance.
    pub(super) literals: Decoder<'static>,
}

impl Budget {
    pub(super) fn new() -> Self {
        Self {
            work: MAX_WORK,
            bytes: MAX_COPY,
            output: MAX_OUTPUT,
            stopped: false,
            literals: Decoder::new(),
        }
    }

    pub(super) fn charge(&mut self, work: usize, bytes: usize) -> Option<()> {
        if self.stopped {
            return None;
        }
        let left = self
            .work
            .checked_sub(work)
            .zip(self.bytes.checked_sub(bytes));
        let Some((work, bytes)) = left else {
            self.stopped = true;
            return None;
        };
        self.work = work;
        self.bytes = bytes;
        Some(())
    }

    pub(super) fn name(&mut self, name: &str) -> Option<()> {
        self.charge(
            name.len().checked_add(1)?,
            name.len().checked_mul(4)?.checked_add(64)?,
        )?;
        valid_name(name).then_some(())
    }

    pub(super) fn scalar(&mut self, sort: Scalar) -> Option<()> {
        let bytes = match sort {
            Scalar::Bool => 64,
            Scalar::Bv(width) => usize::try_from(width).ok()?.div_ceil(8).checked_add(64)?,
        };
        self.charge(1, bytes)
    }

    pub(super) fn push(&mut self, output: &mut String, piece: &str) -> Option<()> {
        self.charge(1, piece.len().checked_mul(2)?)?;
        self.output = match self.output.checked_sub(piece.len()) {
            Some(left) => left,
            None => {
                self.stopped = true;
                return None;
            }
        };
        output.try_reserve(piece.len()).ok()?;
        output.push_str(piece);
        Some(())
    }

    pub(super) fn symbol(&mut self, output: &mut String, name: &str) -> Option<()> {
        self.name(name)?;
        self.push(output, &ay_core::quote_symbol(name))
    }

    pub(super) fn sort_text(&mut self, output: &mut String, sort: Scalar) -> Option<()> {
        self.charge(1, 32)?;
        match sort {
            Scalar::Bool => self.push(output, "Bool"),
            Scalar::Bv(width) => self.push(output, &format!("(_ BitVec {width})")),
        }
    }

    pub(super) fn local(&mut self, output: &mut String, index: usize) -> Option<()> {
        self.charge(1, 64)?;
        self.push(output, &format!("ay_uf_v{index}"))
    }
}
