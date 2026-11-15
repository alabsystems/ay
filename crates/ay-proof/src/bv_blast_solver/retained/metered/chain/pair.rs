// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use wire::pair::FrameSet;

impl Chain<'_, '_> {
    /// Join two already captured frames. Their owners remain reserved while
    /// the new output is allocated/copied; no earlier debit is refunded.
    pub(crate) fn pack_pair(&mut self, frames: [&[u8]; 2]) -> Result<Vec<u8>, MeteredError> {
        self.pack_frames(FrameSet::Outside, &frames)
    }

    pub(crate) fn pack_frames(
        &mut self,
        plan: FrameSet,
        frames: &[&[u8]],
    ) -> Result<Vec<u8>, MeteredError> {
        let proof = self.proof;
        let gates = self.gates;
        self.child(proof, gates, |chain, proof, gates, wire| {
            let (bytes, usage) = chain.ledger.phase(Phase::Wire, wire.max_work, |grant| {
                let mut wire = *wire;
                wire.max_work = grant;
                let outcome =
                    wire::pair::encode_frames(plan, frames, &wire, proof, gates, chain.poll);
                Ok(((outcome.result?, outcome.usage), outcome.usage.charged_work))
            })?;
            chain.budget.commit(
                Shape {
                    rows: 0,
                    literals: 0,
                    hints: 0,
                },
                plan.overhead(),
                usage.returned_owned_bytes,
                usage.charged_work,
            )?;
            Ok(bytes)
        })
    }

    /// Admit a whole borrowed pair before decoding either child. Conservatively
    /// reserve the full input across both replays, in addition to each child's
    /// existing slice reservation. These are logical nonrefundable reservations,
    /// not distinct live allocations or unseen backing-buffer capacity.
    pub(crate) fn split_pair<'d>(
        &mut self,
        bytes: &'d [u8],
    ) -> Result<[&'d [u8]; 2], MeteredError> {
        self.split_frames(FrameSet::Outside, bytes)
            .map(|frames| [frames[0], frames[1]])
    }

    pub(crate) fn split_frames<'d>(
        &mut self,
        plan: FrameSet,
        bytes: &'d [u8],
    ) -> Result<[&'d [u8]; 3], MeteredError> {
        let proof = self.proof;
        let gates = self.gates;
        self.child(proof, gates, |chain, proof, gates, wire| {
            let (frames, usage) = chain.ledger.phase(Phase::Wire, wire.max_work, |grant| {
                let mut wire = *wire;
                wire.max_work = grant;
                let outcome =
                    wire::pair::decode_frames(plan, bytes, &wire, proof, gates, chain.poll);
                Ok(((outcome.result?, outcome.usage), outcome.usage.charged_work))
            })?;
            let framing = frames.iter().try_fold(bytes.len(), |remaining, frame| {
                remaining
                    .checked_sub(frame.len())
                    .ok_or(wire::WireError::Overflow)
            })?;
            chain.budget.commit(
                Shape {
                    rows: 0,
                    literals: 0,
                    hints: 0,
                },
                framing,
                bytes.len(),
                usage.charged_work,
            )?;
            Ok(frames)
        })
    }
}
