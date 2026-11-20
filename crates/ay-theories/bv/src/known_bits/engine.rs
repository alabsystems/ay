// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The interpreted region: the transfer rules of [`super::rules`] applied
//! over a [`KbRegion`] by an ordinary loop. Its schedule and trail are the
//! contract the compiled region is tested against, entry for entry.

use ay_jit::known_bits_region::{
    KbOp, KbRegion, KB_STATUS_CONFLICT, KB_STATUS_FIXPOINT, KB_STATUS_ROUND_LIMIT,
    KB_STATUS_TRAIL_FULL,
};

use super::rules::{self, mask, CarryChain, KnownBits};

/// How a run ended.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum RegionStatus {
    /// A round changed nothing.
    Fixpoint,
    /// Some node's knowledge contradicts itself: the asserted cone has no
    /// model. The last trail entry, if any, is the contradiction.
    Conflict,
    /// The round limit stopped the run.
    RoundLimit,
    /// The trail filled up (never expected; see `KbRegion::trail_capacity`).
    TrailFull,
}

impl RegionStatus {
    /// The status code the compiled region returns for this status.
    #[must_use]
    pub fn code(self) -> i64 {
        match self {
            Self::Fixpoint => KB_STATUS_FIXPOINT,
            Self::Conflict => KB_STATUS_CONFLICT,
            Self::RoundLimit => KB_STATUS_ROUND_LIMIT,
            Self::TrailFull => KB_STATUS_TRAIL_FULL,
        }
    }

    /// The status for a compiled region's status code.
    #[must_use]
    pub fn from_code(code: i64) -> Option<Self> {
        match code {
            KB_STATUS_FIXPOINT => Some(Self::Fixpoint),
            KB_STATUS_CONFLICT => Some(Self::Conflict),
            KB_STATUS_ROUND_LIMIT => Some(Self::RoundLimit),
            KB_STATUS_TRAIL_FULL => Some(Self::TrailFull),
            _ => None,
        }
    }
}

/// One trail entry: a node's knowledge after a change.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct TrailEntry {
    /// The node.
    pub node: u32,
    /// Its new knowledge.
    pub bits: KnownBits,
}

/// Default round limit for a region run.
pub const DEFAULT_MAX_ROUNDS: u32 = 256;

/// Run `region` from `state` (one entry per node), appending every change to
/// `trail`, until a fixpoint, a contradiction or `max_rounds` rounds.
///
/// `state` must have one entry per node and `region` must validate.
#[must_use]
pub fn run_interpreted(
    region: &KbRegion,
    state: &mut [KnownBits],
    trail: &mut Vec<TrailEntry>,
    max_rounds: u32,
) -> RegionStatus {
    let mut run = Run {
        region,
        state,
        trail,
        capacity: region.trail_capacity(),
        changed: false,
    };
    for _ in 0..max_rounds {
        run.changed = false;
        for index in 0..region.nodes.len() {
            if let Err(status) = run.forward(index) {
                return status;
            }
        }
        for index in (0..region.nodes.len()).rev() {
            if let Err(status) = run.backward(index) {
                return status;
            }
        }
        if !run.changed {
            return RegionStatus::Fixpoint;
        }
    }
    RegionStatus::RoundLimit
}

struct Run<'a> {
    region: &'a KbRegion,
    state: &'a mut [KnownBits],
    trail: &'a mut Vec<TrailEntry>,
    capacity: usize,
    changed: bool,
}

impl Run<'_> {
    fn get(&self, node: u32) -> KnownBits {
        self.state[node as usize]
    }

    fn width(&self, node: u32) -> u32 {
        self.region.nodes[node as usize].width
    }

    /// Merge `bits` into `node`. A change is recorded on the trail; a
    /// contradiction ends the run.
    fn merge(&mut self, node: u32, bits: KnownBits) -> Result<(), RegionStatus> {
        let old = self.state[node as usize];
        let new = old.union(bits.restrict(mask(self.width(node))));
        if new == old {
            return Ok(());
        }
        if self.trail.len() >= self.capacity {
            return Err(RegionStatus::TrailFull);
        }
        self.state[node as usize] = new;
        self.trail.push(TrailEntry { node, bits: new });
        self.changed = true;
        if new.is_conflict() {
            return Err(RegionStatus::Conflict);
        }
        Ok(())
    }

    fn forward(&mut self, index: usize) -> Result<(), RegionStatus> {
        let node = self.region.nodes[index];
        let z = index as u32;
        let w = node.width;
        let bits = match node.op {
            KbOp::Leaf | KbOp::Const => return Ok(()),
            KbOp::Not { a } => rules::not_fwd(self.get(a)),
            KbOp::And { a, b } => rules::and_fwd(self.get(a), self.get(b)),
            KbOp::Or { a, b } => rules::or_fwd(self.get(a), self.get(b)),
            KbOp::Xor { a, b } => rules::xor_fwd(self.get(a), self.get(b), w),
            KbOp::Ite { c, t, e } => rules::ite_fwd(self.get(c), self.get(t), self.get(e)),
            KbOp::Eq { a, b } => rules::eq_fwd(self.get(a), self.get(b), self.width(a)),
            KbOp::Cmp {
                a,
                b,
                signed,
                or_equal,
            } => {
                let wa = self.width(a);
                let (x, y) = rules::compare_operands(self.get(a), self.get(b), signed, wa);
                let chain = CarryChain {
                    x,
                    y,
                    sum: None,
                    carry_out: self.get(z),
                };
                match rules::carry_chain_closure(chain, or_equal, wa) {
                    Some(closed) => closed.carry_out,
                    None => return self.contradiction(z),
                }
            }
            KbOp::Add { .. } | KbOp::Sub { .. } | KbOp::Neg { .. } => match self.adder(index) {
                Some((_, _, sum)) => sum,
                None => return self.contradiction(z),
            },
            KbOp::Shl { a, s } => match self.amount(s) {
                Some(k) => rules::shl_fwd(self.get(a), k, w),
                None => return Ok(()),
            },
            KbOp::Lshr { a, s } => match self.amount(s) {
                Some(k) => rules::lshr_fwd(self.get(a), k, w),
                None => return Ok(()),
            },
            KbOp::Ashr { a, s } => match self.amount(s) {
                Some(k) => rules::ashr_fwd(self.get(a), k, w),
                None => return Ok(()),
            },
            KbOp::Extract { a, lo } => rules::extract_fwd(self.get(a), lo, w),
            KbOp::Concat { a, b } => rules::concat_fwd(self.get(a), self.get(b), self.width(b)),
            KbOp::Zext { a } => rules::zext_fwd(self.get(a), self.width(a), w),
            KbOp::Sext { a } => rules::sext_fwd(self.get(a), self.width(a), w),
        };
        self.merge(z, bits)
    }

    fn backward(&mut self, index: usize) -> Result<(), RegionStatus> {
        let node = self.region.nodes[index];
        let z = index as u32;
        let w = node.width;
        let zb = self.get(z);
        match node.op {
            KbOp::Leaf | KbOp::Const => Ok(()),
            KbOp::Not { a } => self.merge(a, rules::not_bwd(zb)),
            KbOp::And { a, b } => {
                let (ka, kb) = (self.get(a), self.get(b));
                self.merge(a, rules::and_bwd(zb, kb))?;
                self.merge(b, rules::and_bwd(zb, ka))
            }
            KbOp::Or { a, b } => {
                let (ka, kb) = (self.get(a), self.get(b));
                self.merge(a, rules::or_bwd(zb, kb))?;
                self.merge(b, rules::or_bwd(zb, ka))
            }
            KbOp::Xor { a, b } => {
                let (ka, kb) = (self.get(a), self.get(b));
                self.merge(a, rules::xor_fwd(zb, kb, w))?;
                self.merge(b, rules::xor_fwd(zb, ka, w))
            }
            KbOp::Ite { c, t, e } => {
                let (kc, kt, ke) = (self.get(c), self.get(t), self.get(e));
                self.merge(c, rules::ite_bwd_cond(zb, kt, ke))?;
                self.merge(t, rules::ite_bwd_branch(zb, kc, 1))?;
                self.merge(e, rules::ite_bwd_branch(zb, kc, 0))
            }
            KbOp::Eq { a, b } => {
                let (ka, kb) = (self.get(a), self.get(b));
                let wa = self.width(a);
                self.merge(a, rules::eq_bwd(zb, ka, kb, wa))?;
                self.merge(b, rules::eq_bwd(zb, kb, ka, wa))
            }
            KbOp::Cmp {
                a,
                b,
                signed,
                or_equal,
            } => {
                let wa = self.width(a);
                let (x, y) = rules::compare_operands(self.get(a), self.get(b), signed, wa);
                let chain = CarryChain {
                    x,
                    y,
                    sum: None,
                    carry_out: zb,
                };
                let Some(closed) = rules::carry_chain_closure(chain, or_equal, wa) else {
                    return self.contradiction(a);
                };
                let (na, nb) = rules::compare_results(closed.x, closed.y, signed, wa);
                self.merge(a, na)?;
                self.merge(b, nb)
            }
            KbOp::Add { a, b } | KbOp::Sub { a, b } => {
                let Some((na, nb, _)) = self.adder(index) else {
                    return self.contradiction(a);
                };
                self.merge(a, na)?;
                self.merge(b, nb)
            }
            KbOp::Neg { a } => {
                let Some((na, _, _)) = self.adder(index) else {
                    return self.contradiction(a);
                };
                self.merge(a, na)
            }
            KbOp::Shl { a, s } => match self.amount(s) {
                Some(k) => self.merge(a, rules::shl_bwd(zb, k, w)),
                None => Ok(()),
            },
            KbOp::Lshr { a, s } => match self.amount(s) {
                Some(k) => self.merge(a, rules::lshr_bwd(zb, k, w)),
                None => Ok(()),
            },
            KbOp::Ashr { a, s } => match self.amount(s) {
                Some(k) => self.merge(a, rules::ashr_bwd(zb, k, w)),
                None => Ok(()),
            },
            KbOp::Extract { a, lo } => self.merge(a, rules::extract_bwd(zb, lo)),
            KbOp::Concat { a, b } => {
                let wb = self.width(b);
                self.merge(a, rules::concat_bwd_high(zb, wb))?;
                self.merge(b, rules::concat_bwd_low(zb, wb))
            }
            KbOp::Zext { a } => self.merge(a, zb),
            KbOp::Sext { a } => {
                let wa = self.width(a);
                self.merge(a, rules::sext_bwd(zb, wa, w))
            }
        }
    }

    /// A rule found no consistent operands: record the contradiction on the
    /// node it was applied for and stop.
    fn contradiction(&mut self, node: u32) -> Result<(), RegionStatus> {
        let all = mask(self.width(node));
        self.merge(
            node,
            KnownBits {
                zero: all,
                one: all,
            },
        )?;
        Err(RegionStatus::Conflict)
    }

    /// A fully known shift amount.
    fn amount(&self, s: u32) -> Option<u64> {
        let k = self.get(s);
        k.is_fully_known(self.width(s)).then_some(k.one)
    }

    /// The adder chain of an `Add`, `Sub` or `Neg` node closed under unit
    /// propagation, mapped back to (operand a, operand b, result).
    fn adder(&self, index: usize) -> Option<(KnownBits, KnownBits, KnownBits)> {
        let node = self.region.nodes[index];
        let w = node.width;
        let m = mask(w);
        let z = self.get(index as u32);
        let (x, y, carry_in) = match node.op {
            KbOp::Add { a, b } => (self.get(a), self.get(b), false),
            KbOp::Sub { a, b } => (self.get(a), self.get(b).complement(), true),
            KbOp::Neg { a } => (
                self.get(a).complement(),
                KnownBits { zero: m, one: 0 },
                true,
            ),
            _ => unreachable!("adder() is called for Add, Sub and Neg only"),
        };
        let chain = CarryChain {
            x,
            y,
            sum: Some(z),
            carry_out: KnownBits::UNKNOWN,
        };
        let closed = rules::carry_chain_closure(chain, carry_in, w)?;
        let sum = closed.sum.unwrap_or(z);
        Some(match node.op {
            KbOp::Add { .. } => (closed.x, closed.y, sum),
            KbOp::Sub { .. } => (closed.x, closed.y.complement(), sum),
            _ => (closed.x.complement(), KnownBits::UNKNOWN, sum),
        })
    }
}
