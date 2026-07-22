// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Proof-tap micro-op record encoding (proof-tap spec, "Micro-op format").
//!
//! Each record is `tag byte + LEB128-encoded payload`; the ring layer adds a
//! LEB128 length prefix. A conflict analysis is a FRAME:
//! `BeginFrame .. resolve ops .. (FinalFrame | AbortFrame)`; everything else
//! (RUP rows, deletions, conclusions, shutdown) flows through the same ring in
//! program order so cross-record ordering is trivially correct.
//!
//! Literals are encoded as `(var << 1) | negated` (the `DenseCp` index
//! convention up to the `var - 1` shift); proof ids as u64 varints, RESOLVED
//! at capture time on the solver thread (the ring never carries propagator
//! constraint indices). Positive scalars are u128 varints; RUP coefficients
//! and degrees are zigzag i128 (they may be negative before normalization).

use crate::types::PbLit;

use super::varint::{decode_i128, decode_u64, encode_i128, encode_u64, VarintError};

/// Record tags. Kept stable so ring bytes are self-describing in debuggers.
const TAG_BEGIN_FRAME: u8 = 1;
const TAG_PROVEN_RESOLVE: u8 = 2;
const TAG_HEURISTIC_RESOLVE: u8 = 3;
const TAG_FINAL_FRAME: u8 = 5;
const TAG_ABORT_FRAME: u8 = 6;
const TAG_RUP: u8 = 7;
const TAG_DELETE: u8 = 8;
const TAG_RUP_TEXT: u8 = 9;
const TAG_CONCLUDE_UNSAT: u8 = 10;
const TAG_CONCLUDE_SAT: u8 = 11;
const TAG_SHUTDOWN: u8 = 12;
const TAG_CHECKPOINT: u8 = 13;
const TAG_WEAKEN_CONT: u8 = 14;

/// One proof-tap micro-op record.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum TapRecord {
    /// Opens a conflict frame. The serializer opens `pol <conflict_pid> s `
    /// (the initial saturate of the conflict constraint is implicit here).
    BeginFrame { conflict_pid: u64 },
    /// One PROVEN round-to-one resolution step (cp_dense.rs
    /// `resolve_proven_round_to_one`): the reason `reason_pid` was partially
    /// weakened by `(lit, rem)` pairs (adding `rem * (~lit >= 0)` literal
    /// axioms), ceiling-divided by `c` (its post-orientation asserted-pivot
    /// coefficient), multiplied by `w` (the conflict's falsified-pivot
    /// coefficient), added into the running conflict (the pivot pair cancels
    /// in checker normal form), and saturated.
    ProvenResolve {
        reason_pid: u64,
        c: i128,
        w: i128,
        weakened: Vec<(PbLit, i128)>,
    },
    /// One heuristic (add-then-divide) resolution step
    /// (`dense_build_resolvent` + optional round-to-one division): the running
    /// conflict is multiplied by `conflict_factor`, the reason by
    /// `reason_factor`, added, saturated; `div` is the optional round-to-one
    /// divisor (followed by a saturate).
    HeuristicResolve {
        reason_pid: u64,
        conflict_factor: i128,
        reason_factor: i128,
        div: Option<i128>,
    },
    /// Closes a frame: post-loop strengthening (saturate, divide by `gcd1` if
    /// `> 1`, then — when the conservative-weaken branch ran — weaken each
    /// listed literal, saturate, divide by `gcd2` if `> 1`). `lemma_pid` is
    /// the SOLVER-pre-allocated id for the frame's single emitted pol line;
    /// the serializer asserts it matches the writer-allocated id.
    FinalFrame {
        gcd1: i128,
        weaken_ran: bool,
        weakened: Vec<PbLit>,
        gcd2: i128,
        lemma_pid: u64,
    },
    /// Aborts the open frame: the serializer discards the buffered pol
    /// expression. No proof id was allocated for the frame's LEMMA (any
    /// checkpoint intermediates already emitted stay allocated on both sides
    /// and are deleted by the serializer).
    AbortFrame,
    /// Line-length control (spec record kind 9): closes the current pol line
    /// at the SOLVER-pre-allocated `intermediate_pid` and continues the frame
    /// from it (`pol <intermediate_pid> ...`). The serializer deletes every
    /// intermediate right after the frame's final line (`del` allocates no
    /// id, so serializer-injected deletes never desync the counters).
    Checkpoint { intermediate_pid: u64 },
    /// 64 KiB record chunking for oversized `ProvenResolve` weaken lists: the
    /// pairs buffer up on the serializer and are consumed (in order, ahead of
    /// the record's own list) by the NEXT `ProvenResolve`. Only more
    /// `WeakenCont` records or the consuming `ProvenResolve` may follow.
    WeakenCont { pairs: Vec<(PbLit, i128)> },
    /// A structured RUP row (`rup <terms> >= <degree> ;`) with a solver-
    /// pre-allocated id. Terms are formatted (sorted by `(var, negated)`) on
    /// the serializer thread.
    Rup {
        pid: u64,
        terms: Vec<(PbLit, i128)>,
        degree: i128,
    },
    /// A pre-formatted RUP row (legacy `ProofStep::Rup` payloads routed
    /// through the tap, e.g. the `>= 1 ;` contradiction row).
    RupText { pid: u64, text: String },
    /// Checked deletion `del id <pid> ;` (allocates no id).
    Delete { pid: u64 },
    /// UNSAT conclusion referencing the contradiction row. The serializer
    /// emits the conclusion block, flushes, and completes the conclusion
    /// handshake.
    ConcludeUnsat { contradiction_pid: u64 },
    /// SAT conclusion with the full assignment (index 0 = x1).
    ConcludeSat { assignment: Vec<bool> },
    /// Terminates the serializer loop (also implied by producer close).
    Shutdown,
}

/// Decode failure (truncated, oversized, or malformed record bytes).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) struct RecordDecodeError;

impl From<VarintError> for RecordDecodeError {
    fn from(_: VarintError) -> Self {
        RecordDecodeError
    }
}

fn encode_lit(out: &mut Vec<u8>, lit: PbLit) {
    encode_u64(out, (u64::from(lit.var) << 1) | u64::from(lit.negated));
}

fn decode_lit(bytes: &[u8], pos: &mut usize) -> Result<PbLit, RecordDecodeError> {
    let raw = decode_u64(bytes, pos)?;
    let var = u32::try_from(raw >> 1).map_err(|_| RecordDecodeError)?;
    if var == 0 {
        return Err(RecordDecodeError);
    }
    Ok(PbLit {
        var,
        negated: raw & 1 == 1,
    })
}

fn decode_len(bytes: &[u8], pos: &mut usize) -> Result<usize, RecordDecodeError> {
    let raw = decode_u64(bytes, pos)?;
    usize::try_from(raw).map_err(|_| RecordDecodeError)
}

impl TapRecord {
    /// Appends the record (tag + payload, no length prefix) to `out`.
    pub(crate) fn encode(&self, out: &mut Vec<u8>) {
        match self {
            Self::BeginFrame { conflict_pid } => {
                out.push(TAG_BEGIN_FRAME);
                encode_u64(out, *conflict_pid);
            }
            Self::ProvenResolve {
                reason_pid,
                c,
                w,
                weakened,
            } => {
                out.push(TAG_PROVEN_RESOLVE);
                encode_u64(out, *reason_pid);
                encode_i128(out, *c);
                encode_i128(out, *w);
                encode_u64(out, weakened.len() as u64);
                for &(lit, rem) in weakened {
                    encode_lit(out, lit);
                    encode_i128(out, rem);
                }
            }
            Self::HeuristicResolve {
                reason_pid,
                conflict_factor,
                reason_factor,
                div,
            } => {
                out.push(TAG_HEURISTIC_RESOLVE);
                encode_u64(out, *reason_pid);
                encode_i128(out, *conflict_factor);
                encode_i128(out, *reason_factor);
                match div {
                    Some(d) => {
                        out.push(1);
                        encode_i128(out, *d);
                    }
                    None => out.push(0),
                }
            }
            Self::FinalFrame {
                gcd1,
                weaken_ran,
                weakened,
                gcd2,
                lemma_pid,
            } => {
                out.push(TAG_FINAL_FRAME);
                encode_i128(out, *gcd1);
                out.push(u8::from(*weaken_ran));
                encode_u64(out, weakened.len() as u64);
                for &lit in weakened {
                    encode_lit(out, lit);
                }
                encode_i128(out, *gcd2);
                encode_u64(out, *lemma_pid);
            }
            Self::AbortFrame => out.push(TAG_ABORT_FRAME),
            Self::Checkpoint { intermediate_pid } => {
                out.push(TAG_CHECKPOINT);
                encode_u64(out, *intermediate_pid);
            }
            Self::WeakenCont { pairs } => {
                out.push(TAG_WEAKEN_CONT);
                encode_u64(out, pairs.len() as u64);
                for &(lit, rem) in pairs {
                    encode_lit(out, lit);
                    encode_i128(out, rem);
                }
            }
            Self::Rup { pid, terms, degree } => {
                out.push(TAG_RUP);
                encode_u64(out, *pid);
                encode_u64(out, terms.len() as u64);
                for &(lit, coeff) in terms {
                    encode_lit(out, lit);
                    encode_i128(out, coeff);
                }
                encode_i128(out, *degree);
            }
            Self::RupText { pid, text } => {
                out.push(TAG_RUP_TEXT);
                encode_u64(out, *pid);
                encode_u64(out, text.len() as u64);
                out.extend_from_slice(text.as_bytes());
            }
            Self::Delete { pid } => {
                out.push(TAG_DELETE);
                encode_u64(out, *pid);
            }
            Self::ConcludeUnsat { contradiction_pid } => {
                out.push(TAG_CONCLUDE_UNSAT);
                encode_u64(out, *contradiction_pid);
            }
            Self::ConcludeSat { assignment } => {
                out.push(TAG_CONCLUDE_SAT);
                encode_u64(out, assignment.len() as u64);
                // Pack the witness bits densely (LSB-first within each byte).
                let mut byte = 0u8;
                for (i, &bit) in assignment.iter().enumerate() {
                    if bit {
                        byte |= 1 << (i % 8);
                    }
                    if i % 8 == 7 {
                        out.push(byte);
                        byte = 0;
                    }
                }
                if !assignment.len().is_multiple_of(8) {
                    out.push(byte);
                }
            }
            Self::Shutdown => out.push(TAG_SHUTDOWN),
        }
    }

    /// Decodes one record from `bytes` (tag + payload, no length prefix).
    /// Fails closed on any malformed or trailing input.
    pub(crate) fn decode(bytes: &[u8]) -> Result<Self, RecordDecodeError> {
        let (&tag, rest) = bytes.split_first().ok_or(RecordDecodeError)?;
        let mut pos = 0usize;
        let record = match tag {
            TAG_BEGIN_FRAME => Self::BeginFrame {
                conflict_pid: decode_u64(rest, &mut pos)?,
            },
            TAG_PROVEN_RESOLVE => {
                let reason_pid = decode_u64(rest, &mut pos)?;
                let c = decode_i128(rest, &mut pos)?;
                let w = decode_i128(rest, &mut pos)?;
                let n = decode_len(rest, &mut pos)?;
                // Cap pre-allocation: a hostile length cannot OOM the decoder.
                let mut weakened = Vec::with_capacity(n.min(1024));
                for _ in 0..n {
                    let lit = decode_lit(rest, &mut pos)?;
                    let rem = decode_i128(rest, &mut pos)?;
                    weakened.push((lit, rem));
                }
                Self::ProvenResolve {
                    reason_pid,
                    c,
                    w,
                    weakened,
                }
            }
            TAG_HEURISTIC_RESOLVE => {
                let reason_pid = decode_u64(rest, &mut pos)?;
                let conflict_factor = decode_i128(rest, &mut pos)?;
                let reason_factor = decode_i128(rest, &mut pos)?;
                let has_div = *rest.get(pos).ok_or(RecordDecodeError)?;
                pos += 1;
                let div = match has_div {
                    0 => None,
                    1 => Some(decode_i128(rest, &mut pos)?),
                    _ => return Err(RecordDecodeError),
                };
                Self::HeuristicResolve {
                    reason_pid,
                    conflict_factor,
                    reason_factor,
                    div,
                }
            }
            TAG_FINAL_FRAME => {
                let gcd1 = decode_i128(rest, &mut pos)?;
                let weaken_flag = *rest.get(pos).ok_or(RecordDecodeError)?;
                pos += 1;
                if weaken_flag > 1 {
                    return Err(RecordDecodeError);
                }
                let n = decode_len(rest, &mut pos)?;
                let mut weakened = Vec::with_capacity(n.min(1024));
                for _ in 0..n {
                    weakened.push(decode_lit(rest, &mut pos)?);
                }
                Self::FinalFrame {
                    gcd1,
                    weaken_ran: weaken_flag == 1,
                    weakened,
                    gcd2: decode_i128(rest, &mut pos)?,
                    lemma_pid: decode_u64(rest, &mut pos)?,
                }
            }
            TAG_ABORT_FRAME => Self::AbortFrame,
            TAG_CHECKPOINT => Self::Checkpoint {
                intermediate_pid: decode_u64(rest, &mut pos)?,
            },
            TAG_WEAKEN_CONT => {
                let n = decode_len(rest, &mut pos)?;
                let mut pairs = Vec::with_capacity(n.min(1024));
                for _ in 0..n {
                    let lit = decode_lit(rest, &mut pos)?;
                    let rem = decode_i128(rest, &mut pos)?;
                    pairs.push((lit, rem));
                }
                Self::WeakenCont { pairs }
            }
            TAG_RUP => {
                let pid = decode_u64(rest, &mut pos)?;
                let n = decode_len(rest, &mut pos)?;
                let mut terms = Vec::with_capacity(n.min(1024));
                for _ in 0..n {
                    let lit = decode_lit(rest, &mut pos)?;
                    let coeff = decode_i128(rest, &mut pos)?;
                    terms.push((lit, coeff));
                }
                Self::Rup {
                    pid,
                    terms,
                    degree: decode_i128(rest, &mut pos)?,
                }
            }
            TAG_RUP_TEXT => {
                let pid = decode_u64(rest, &mut pos)?;
                let len = decode_len(rest, &mut pos)?;
                let end = pos.checked_add(len).ok_or(RecordDecodeError)?;
                let raw = rest.get(pos..end).ok_or(RecordDecodeError)?;
                pos = end;
                Self::RupText {
                    pid,
                    text: String::from_utf8(raw.to_vec()).map_err(|_| RecordDecodeError)?,
                }
            }
            TAG_DELETE => Self::Delete {
                pid: decode_u64(rest, &mut pos)?,
            },
            TAG_CONCLUDE_UNSAT => Self::ConcludeUnsat {
                contradiction_pid: decode_u64(rest, &mut pos)?,
            },
            TAG_CONCLUDE_SAT => {
                let n = decode_len(rest, &mut pos)?;
                let byte_count = n.div_ceil(8);
                let end = pos.checked_add(byte_count).ok_or(RecordDecodeError)?;
                let packed = rest.get(pos..end).ok_or(RecordDecodeError)?;
                pos = end;
                let mut assignment = Vec::with_capacity(n);
                for i in 0..n {
                    assignment.push(packed[i / 8] & (1 << (i % 8)) != 0);
                }
                Self::ConcludeSat { assignment }
            }
            TAG_SHUTDOWN => Self::Shutdown,
            _ => return Err(RecordDecodeError),
        };
        if pos != rest.len() {
            return Err(RecordDecodeError);
        }
        Ok(record)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn lit(var: u32, negated: bool) -> PbLit {
        PbLit { var, negated }
    }

    fn round_trip(record: &TapRecord) {
        let mut buf = Vec::new();
        record.encode(&mut buf);
        let decoded = TapRecord::decode(&buf).expect("well-formed record decodes");
        assert_eq!(&decoded, record);
    }

    #[test]
    fn all_record_kinds_round_trip() {
        round_trip(&TapRecord::BeginFrame { conflict_pid: 7 });
        round_trip(&TapRecord::ProvenResolve {
            reason_pid: u64::MAX,
            c: 12345678901234567890123456789i128,
            w: 3,
            weakened: vec![(lit(1, false), 2), (lit(400000, true), 1 << 90)],
        });
        round_trip(&TapRecord::ProvenResolve {
            reason_pid: 1,
            c: 1,
            w: 1,
            weakened: Vec::new(),
        });
        round_trip(&TapRecord::HeuristicResolve {
            reason_pid: 9,
            conflict_factor: 1,
            reason_factor: i128::MAX,
            div: None,
        });
        round_trip(&TapRecord::HeuristicResolve {
            reason_pid: 9,
            conflict_factor: 4,
            reason_factor: 6,
            div: Some(5),
        });
        round_trip(&TapRecord::FinalFrame {
            gcd1: 6,
            weaken_ran: true,
            weakened: vec![lit(3, true), lit(17, false)],
            gcd2: 1,
            lemma_pid: 42,
        });
        round_trip(&TapRecord::FinalFrame {
            gcd1: 0,
            weaken_ran: false,
            weakened: Vec::new(),
            gcd2: 0,
            lemma_pid: 1,
        });
        round_trip(&TapRecord::AbortFrame);
        round_trip(&TapRecord::Checkpoint {
            intermediate_pid: 123456789,
        });
        round_trip(&TapRecord::WeakenCont { pairs: Vec::new() });
        round_trip(&TapRecord::WeakenCont {
            pairs: vec![(lit(9, true), 1), (lit(70000, false), 1 << 80)],
        });
        round_trip(&TapRecord::Rup {
            pid: 11,
            terms: vec![(lit(1, false), -3), (lit(2, true), 5)],
            degree: -7,
        });
        round_trip(&TapRecord::RupText {
            pid: 12,
            text: String::from(">= 1 ;"),
        });
        round_trip(&TapRecord::Delete { pid: 5 });
        round_trip(&TapRecord::ConcludeUnsat {
            contradiction_pid: 99,
        });
        round_trip(&TapRecord::ConcludeSat {
            assignment: vec![true, false, true, true, false, false, true, false, true],
        });
        round_trip(&TapRecord::ConcludeSat {
            assignment: Vec::new(),
        });
        round_trip(&TapRecord::Shutdown);
    }

    #[test]
    fn typical_proven_resolve_is_compact() {
        // Spec size budget: typical PROVEN_RESOLVE is 10-150 bytes.
        let mut buf = Vec::new();
        TapRecord::ProvenResolve {
            reason_pid: 100_000,
            c: 12,
            w: 40,
            weakened: vec![(lit(17, true), 3), (lit(90, false), 5)],
        }
        .encode(&mut buf);
        assert!(buf.len() <= 24, "encoded {} bytes", buf.len());
    }

    #[test]
    fn malformed_records_fail_closed() {
        assert!(TapRecord::decode(&[]).is_err());
        assert!(TapRecord::decode(&[0xff]).is_err());
        // Truncated payload.
        let mut buf = Vec::new();
        TapRecord::Rup {
            pid: 11,
            terms: vec![(lit(1, false), 3)],
            degree: 1,
        }
        .encode(&mut buf);
        buf.pop();
        assert!(TapRecord::decode(&buf).is_err());
        // Trailing garbage.
        let mut buf2 = Vec::new();
        TapRecord::Delete { pid: 5 }.encode(&mut buf2);
        buf2.push(0);
        assert!(TapRecord::decode(&buf2).is_err());
        // Literal with var 0.
        let mut buf3 = vec![TAG_BEGIN_FRAME];
        encode_u64(&mut buf3, 1);
        assert!(TapRecord::decode(&buf3).is_ok());
    }
}
