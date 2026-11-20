// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The known-bits region program: the vocabulary shared by the interpreted
//! region in `ay-bv` and the compiled one emitted by
//! `external_codegen_ir_emit::emit_known_bits_region_external_codegen_ir`.
//!
//! A region is a cone of bit-vector and Boolean terms in topological order
//! (every operand index is below its node's index). Its state is two words
//! per node, the bits known to be 0 and the bits known to be 1, each value at
//! most 64 bits wide (a Boolean is one bit). Running the region applies every
//! node's forward rule in index order and every node's backward rules in
//! reverse index order, round after round, until a round changes nothing, a
//! node's knowledge contradicts itself, or the round limit is reached. Each
//! change appends one trail entry (node index, new zero mask, new one mask);
//! the caller commits the trail as one transaction.
//!
//! The semantics of each rule are stated once, in `ay_bv::known_bits::rules`;
//! the compiled region restates them in external-codegen-ir and is held to them by
//! differential tests that compare whole trails.

/// One node's operation. Operand fields are node indices below the node's own.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum KbOp {
    /// A variable or a term outside the region's vocabulary: no rule.
    Leaf,
    /// A constant: its value is in the initial state.
    Const,
    /// Bitwise (or Boolean) complement.
    Not {
        /// Operand.
        a: u32,
    },
    /// Bitwise (or Boolean) and.
    And {
        /// Left operand.
        a: u32,
        /// Right operand.
        b: u32,
    },
    /// Bitwise (or Boolean) or.
    Or {
        /// Left operand.
        a: u32,
        /// Right operand.
        b: u32,
    },
    /// Bitwise (or Boolean) exclusive or.
    Xor {
        /// Left operand.
        a: u32,
        /// Right operand.
        b: u32,
    },
    /// If-then-else on a one-bit condition.
    Ite {
        /// Condition.
        c: u32,
        /// Then-branch.
        t: u32,
        /// Else-branch.
        e: u32,
    },
    /// Equality of two equal-width operands, a one-bit result.
    Eq {
        /// Left operand.
        a: u32,
        /// Right operand.
        b: u32,
    },
    /// Comparison of two equal-width operands, a one-bit result:
    /// `a < b`, or `a <= b` when `or_equal`; two's-complement when `signed`.
    Cmp {
        /// Left operand.
        a: u32,
        /// Right operand.
        b: u32,
        /// Two's-complement order.
        signed: bool,
        /// Non-strict order.
        or_equal: bool,
    },
    /// Modular addition.
    Add {
        /// Left operand.
        a: u32,
        /// Right operand.
        b: u32,
    },
    /// Modular subtraction `a - b`.
    Sub {
        /// Left operand.
        a: u32,
        /// Right operand.
        b: u32,
    },
    /// Modular negation.
    Neg {
        /// Operand.
        a: u32,
    },
    /// Shift left; an amount at or past the width gives 0.
    Shl {
        /// Shifted value.
        a: u32,
        /// Amount.
        s: u32,
    },
    /// Logical shift right; an amount at or past the width gives 0.
    Lshr {
        /// Shifted value.
        a: u32,
        /// Amount.
        s: u32,
    },
    /// Arithmetic shift right; an amount at or past the width gives the sign.
    Ashr {
        /// Shifted value.
        a: u32,
        /// Amount.
        s: u32,
    },
    /// The node's width of bits of `a` starting at bit `lo`.
    Extract {
        /// Operand.
        a: u32,
        /// Lowest extracted bit.
        lo: u32,
    },
    /// `a` above `b`.
    Concat {
        /// High operand.
        a: u32,
        /// Low operand.
        b: u32,
    },
    /// Zero extension to the node's width.
    Zext {
        /// Operand.
        a: u32,
    },
    /// Sign extension to the node's width.
    Sext {
        /// Operand.
        a: u32,
    },
}

impl KbOp {
    /// The operand node indices, in rule order.
    #[must_use]
    pub fn operands(&self) -> Vec<u32> {
        match *self {
            Self::Leaf | Self::Const => Vec::new(),
            Self::Not { a } | Self::Neg { a } | Self::Zext { a } | Self::Sext { a } => vec![a],
            Self::Extract { a, .. } => vec![a],
            Self::And { a, b }
            | Self::Or { a, b }
            | Self::Xor { a, b }
            | Self::Eq { a, b }
            | Self::Cmp { a, b, .. }
            | Self::Add { a, b }
            | Self::Sub { a, b }
            | Self::Concat { a, b } => vec![a, b],
            Self::Shl { a, s } | Self::Lshr { a, s } | Self::Ashr { a, s } => vec![a, s],
            Self::Ite { c, t, e } => vec![c, t, e],
        }
    }
}

/// One node: its operation and its width in bits (`1..=64`).
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct KbNode {
    /// The operation.
    pub op: KbOp,
    /// Width in bits; 1 for a Boolean.
    pub width: u32,
}

/// A region program: nodes in topological order.
#[derive(Clone, Debug, Default, PartialEq, Eq, Hash)]
pub struct KbRegion {
    /// Nodes; every operand index is below the index of its node.
    pub nodes: Vec<KbNode>,
}

impl KbRegion {
    /// Check the shape every runner relies on: widths in `1..=64`, operands
    /// before their node, operand widths as the operation requires.
    ///
    /// # Errors
    ///
    /// A description of the first malformed node.
    pub fn validate(&self) -> Result<(), String> {
        for (index, node) in self.nodes.iter().enumerate() {
            if node.width == 0 || node.width > MAX_REGION_WIDTH {
                return Err(format!("node {index}: width {} outside 1..=64", node.width));
            }
            for operand in node.op.operands() {
                if operand as usize >= index {
                    return Err(format!("node {index}: operand {operand} is not below it"));
                }
            }
            let w = |i: u32| self.nodes[i as usize].width;
            let ok = match node.op {
                KbOp::Leaf | KbOp::Const => true,
                KbOp::Not { a } | KbOp::Neg { a } => w(a) == node.width,
                KbOp::And { a, b }
                | KbOp::Or { a, b }
                | KbOp::Xor { a, b }
                | KbOp::Add { a, b }
                | KbOp::Sub { a, b } => w(a) == node.width && w(b) == node.width,
                KbOp::Shl { a, s } | KbOp::Lshr { a, s } | KbOp::Ashr { a, s } => {
                    w(a) == node.width && w(s) == node.width
                }
                KbOp::Ite { c, t, e } => w(c) == 1 && w(t) == node.width && w(e) == node.width,
                KbOp::Eq { a, b } | KbOp::Cmp { a, b, .. } => node.width == 1 && w(a) == w(b),
                KbOp::Extract { a, lo } => lo + node.width <= w(a),
                KbOp::Concat { a, b } => w(a) + w(b) == node.width,
                KbOp::Zext { a } | KbOp::Sext { a } => w(a) <= node.width,
            };
            if !ok {
                return Err(format!(
                    "node {index}: operand widths do not fit {:?}",
                    node.op
                ));
            }
        }
        Ok(())
    }

    /// Trail capacity that no run can exceed: every entry but the last adds
    /// at least one known bit to its node, and the last may conflict.
    #[must_use]
    pub fn trail_capacity(&self) -> usize {
        self.nodes.iter().map(|n| n.width as usize).sum::<usize>() + 1
    }
}

/// Widest value a region holds.
pub const MAX_REGION_WIDTH: u32 = 64;

/// Words per trail entry: node index, zero mask, one mask.
pub const TRAIL_ENTRY_WORDS: usize = 3;

/// Run status: a round changed nothing.
pub const KB_STATUS_FIXPOINT: i64 = 0;
/// Run status: a node's knowledge contradicts itself; the last trail entry,
/// if any, is the contradiction.
pub const KB_STATUS_CONFLICT: i64 = 1;
/// Run status: the round limit stopped the run before a fixpoint.
pub const KB_STATUS_ROUND_LIMIT: i64 = 2;
/// Run status: the trail would have overflowed its buffer (never expected:
/// see [`KbRegion::trail_capacity`]).
pub const KB_STATUS_TRAIL_FULL: i64 = 3;
