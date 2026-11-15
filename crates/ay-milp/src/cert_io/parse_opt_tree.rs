// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Parser for the `opttree` block: a whole-tree MILP OPTIMALITY certificate.
//!
//! # Why this is a separate parser from `parse_tree`
//!
//! The two blocks have nearly the same grammar and OPPOSITE meanings. A
//! [`crate::MilpInfeasibilityCertificate`]'s `Ok(())` means "the model has no
//! feasible point"; an [`OptTreeNode`]'s means "nothing here beats `z*`". The
//! design review that preceded this named the conflation as its own hazard:
//!
//! > Distinct block token and distinct parsed field from `cert.tree` — a Farkas
//! > tree backing `dual` is merely vacuous, but a bound tree backing
//! > `infeasible` is FATAL.
//!
//! So the token is `opttree` (not `tree`), the parsed field is
//! `Certificate::opt_tree_body` (not `Certificate::tree`), the two lanes share
//! no code, and a `boundleaf` record is a PARSE ERROR inside a `tree` block —
//! `parse_tree` has no arm for it. There is no code path on which a bound leaf
//! can be read as a proof of emptiness.
//!
//! # Why this module PARSES NOTHING into a tree
//!
//! It used to build an `OptTreeNode`, and that was a hard ceiling on what could
//! be CHECKED — measured at ~110 bytes per multiplier, i.e. ~2.5 GB for
//! `khb05250`'s completed 17,124-leaf proof, against 655 MB for the file that
//! prints it. The block is now CAPTURED verbatim and VERIFIED as a record
//! stream, one leaf resident at a time.

use super::*;

/// Capture an `opttree` body starting at `start` (the line AFTER the `opttree`
/// opener), through its `end` terminator.
///
/// Returns the body's records — everything strictly between the opener and the
/// terminator — plus the line index just past the terminator.
///
/// # This deliberately validates nothing but the extent
///
/// A `tree`-shaped grammar check here would be a SECOND implementation of the
/// obligations [`verify_opt_tree_body`] already discharges, and two
/// implementations of the same check is how a checker acquires a hole. The
/// only property this needs is where the block ENDS, and that is unambiguous:
/// the block's records are `split`, `leaf`, `boundleaf`, `mult` and `endleaf`,
/// none of which is `end`. A body whose terminator is missing therefore
/// swallows whatever follows it and is REJECTED by the verifier as malformed —
/// failing closed, which is the only direction that is safe.
pub(super) fn capture_opt_tree_body(
    lines: &[&str],
    start: usize,
) -> Result<(String, usize), CertIoError> {
    let mut i = start;
    while i < lines.len() {
        if lines[i].trim() == "end" {
            // `join` rather than a running push: one allocation of the exact
            // size, which on a body measured at 655 MB is the difference
            // between one copy and a reallocation ladder.
            let mut body = lines[start..i].join("\n");
            if !body.is_empty() {
                body.push('\n');
            }
            return Ok((body, i + 1));
        }
        i += 1;
    }
    Err(CertIoError::Malformed {
        line: start,
        msg: "opttree block is not terminated by `end`".into(),
    })
}

// ---------------------------------------------------------------------------
// STREAMING verification: the same grammar and the same obligations, in
// O(depth) memory instead of O(leaves).
// ---------------------------------------------------------------------------

/// Verify an `opttree` BODY against `model` and `value` WITHOUT materialising
/// the tree.
///
/// # Why a second entry point and not a second grammar
///
/// The object form this replaces built an `OptTreeNode`, which costs
/// `O(leaves x multipliers)` live heap — one `FactRef` plus one heap-allocated
/// `BigRational` for every multiplier of every leaf. On the trees this feature
/// most wants to certify that is gigabytes: `khb05250`'s completed proof is
/// 17,124 leaves over 1,350 columns, ~2.5 GB as objects against 655 MB as the
/// file that prints them. Reading a leaf, PRICING it, and dropping it holds one
/// leaf at a time and a bound-restore stack whose depth is the tree's, so the
/// ceiling becomes the file rather than the object graph behind it.
///
/// It is the same grammar because it uses the same record parsers
/// ([`parse_proof_rat`] for the cut, [`parse_mults`] for the leaves). It is the
/// same set of obligations because the checks below are
/// [`crate::verify_optimality_tree_bound`]'s, transcribed with the identical
/// tighten/restore discipline:
///
/// * the box is RECONSTRUCTED from `model.col_bounds` intersected with the
///   path's splits, never read from the block;
/// * every leaf is priced against the caller's single `value`;
/// * a split is licensed only on an INTEGRAL column at an INTEGER cut, so the
///   two branches tile the parent.
///
/// The one obligation that has no analogue in the object form is completeness:
/// a truncated body must not verify. `Incomplete` covers it — the walk must end
/// with exactly one finished root and no open split.
pub(crate) fn verify_opt_tree_body(
    model: &Model,
    value: &BigRational,
    body: &str,
) -> Result<OptTreeStreamStats, OptTreeStreamError> {
    let lines: Vec<&str> = body.lines().collect();
    let n = model.num_cols();
    let mut lb: Vec<Option<BigRational>> = (0..n)
        .map(|j| exact(model.col_bounds(Col(j as u32)).0))
        .collect();
    let mut ub: Vec<Option<BigRational>> = (0..n)
        .map(|j| exact(model.col_bounds(Col(j as u32)).1))
        .collect();

    let mut frames: Vec<OptTreeFrame> = Vec::new();
    let mut stats = OptTreeStreamStats::default();
    let mut root_done = false;
    let mut i = 0usize;

    while i < lines.len() {
        let record = lines[i].trim();
        if record.is_empty() {
            i += 1;
            continue;
        }
        let fields: Vec<&str> = record.split_whitespace().collect();
        match fields.first().copied() {
            Some("split") if fields.len() == 3 => {
                let index = stats.splits;
                stats.splits += 1;
                let split = SplitRecord {
                    column: fields[1],
                    cut: fields[2],
                    line: i + 1,
                    index,
                };
                frames.push(open_split(model, &split, &mut ub)?);
                i += 1;
            }
            Some(kind @ ("leaf" | "boundleaf")) if fields.len() == 1 => {
                let index = stats.leaves;
                stats.leaves += 1;
                // ONE LEAF LIVE AT A TIME. `mults` is dropped at the end of
                // this arm; that is the whole memory argument.
                let (mults, next) = parse_mults(&lines, i + 1, "endleaf").map_err(|e| {
                    OptTreeStreamError::Malformed {
                        line: i + 1,
                        msg: format!("{e}"),
                    }
                })?;
                let checked = if kind == "boundleaf" {
                    stats.dominated += 1;
                    OptimalityCertificate::verify_bound_leaf(&mults, model, &lb, &ub, value)
                } else {
                    FarkasCertificate { multipliers: mults }.verify_with_col_bounds(model, &lb, &ub)
                };
                checked.map_err(|error| OptTreeStreamError::LeafRejected {
                    index,
                    error: Box::new(error),
                })?;
                i = next;
                if complete_child(&mut frames, &mut lb, &mut ub) {
                    if root_done {
                        return Err(OptTreeStreamError::Malformed {
                            line: i,
                            msg: "opttree body contains more than one root".into(),
                        });
                    }
                    root_done = true;
                }
            }
            _ => {
                return Err(OptTreeStreamError::Malformed {
                    line: i + 1,
                    msg: format!("malformed opttree record `{record}`"),
                })
            }
        }
    }
    if !root_done || !frames.is_empty() {
        return Err(OptTreeStreamError::Incomplete);
    }
    Ok(stats)
}

/// The fields of one `split <column> <cut>` record, and where it sits.
struct SplitRecord<'a> {
    column: &'a str,
    cut: &'a str,
    /// One-based line of the record, for `Malformed`.
    line: usize,
    /// How many splits came before this one, for `InvalidSplit`.
    index: usize,
}

/// Open one split: parse its column and cut, check its coverage licence, and
/// apply its `lo` tightening `x_col <= cut` to `ub`. Returns the frame that
/// holds the bound the tightening displaced.
///
/// A refused split leaves `ub` untouched.
fn open_split(
    model: &Model,
    split: &SplitRecord<'_>,
    ub: &mut [Option<BigRational>],
) -> Result<OptTreeFrame, OptTreeStreamError> {
    let column: u32 = split
        .column
        .parse()
        .map_err(|_| OptTreeStreamError::Malformed {
            line: split.line,
            msg: "malformed split column".into(),
        })?;
    let cut = parse_proof_rat(split.cut, ProofParseMode::General).ok_or(
        OptTreeStreamError::Malformed {
            line: split.line,
            msg: "malformed split cut".into(),
        },
    )?;
    let c = column as usize;
    // THE COVERAGE LICENCE, whitelisted exactly as the object-form verifier
    // whitelists it: only an INTEGRAL column split at an INTEGER leaves no
    // point between the branches.
    let integral = c < model.num_cols()
        && matches!(
            model.col_kind(Col(column)),
            ColKind::Binary | ColKind::Integer
        );
    if !integral || !cut.is_integer() {
        return Err(OptTreeStreamError::InvalidSplit {
            index: split.index,
            col: c,
        });
    }
    let slot = &mut ub[c];
    let prev = slot.clone();
    *slot = Some(match slot.take() {
        Some(p) => p.min(cut.clone()),
        None => cut.clone(),
    });
    Ok(OptTreeFrame {
        col: c,
        cut,
        prev,
        child: 0,
    })
}

/// One split whose children are still arriving, in the STREAMING verifier's
/// bound stack.
///
/// It carries what it displaced rather than parking that on a side stack, for
/// the same reason [`crate::verify_optimality_tree_bound`]'s `Restore` frame
/// does: a
/// certificate is untrusted input and restoring must not depend on a second
/// stack being balanced.
struct OptTreeFrame {
    col: usize,
    cut: BigRational,
    /// The bound this frame's CURRENT tightening displaced.
    prev: Option<BigRational>,
    /// 0 = the `lo` child is running, 1 = the `hi` child is running.
    child: u8,
}

/// One child of the innermost open split has finished. Unwind as far as the
/// completions carry, moving each frame from its `lo` tightening to its `hi`
/// tightening and restoring what it displaced.
///
/// Returns `true` when the unwind reached the top, i.e. the ROOT is finished.
/// Total by construction — every path pops or pushes, and there is no `unwrap`
/// — because this runs on untrusted input.
fn complete_child(
    frames: &mut Vec<OptTreeFrame>,
    lb: &mut [Option<BigRational>],
    ub: &mut [Option<BigRational>],
) -> bool {
    loop {
        let Some(mut frame) = frames.pop() else {
            return true;
        };
        if frame.child == 0 {
            // `lo` is done: undo its `x_col <= cut` and apply `x_col >= cut + 1`.
            ub[frame.col] = frame.prev.take();
            frame.child = 1;
            let to = &frame.cut + BigRational::one();
            let slot = &mut lb[frame.col];
            frame.prev = slot.clone();
            *slot = Some(match slot.take() {
                Some(prev) => prev.max(to),
                None => to,
            });
            frames.push(frame);
            return false;
        }
        // Both children done: restore, and let the completion carry upward.
        lb[frame.col] = frame.prev;
    }
}

/// What a streaming verification saw. Diagnostics only — the verdict is the
/// `Result` itself.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub(crate) struct OptTreeStreamStats {
    pub(crate) splits: usize,
    pub(crate) leaves: usize,
    pub(crate) dominated: usize,
}

/// Why a streaming verification refused.
#[derive(Debug)]
pub(crate) enum OptTreeStreamError {
    /// The body is not a well-formed record stream.
    Malformed { line: usize, msg: String },
    /// A split is not licensed: a non-integral column, or a non-integer cut.
    InvalidSplit { index: usize, col: usize },
    /// A leaf did not verify at the box its position implies.
    LeafRejected {
        index: usize,
        error: Box<CertificateError>,
    },
    /// The body ended with a split still open, or with no root at all. A
    /// truncated proof must not pass, and this is the check that stops it.
    Incomplete,
}

impl fmt::Display for OptTreeStreamError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Malformed { line, msg } => write!(f, "malformed opttree at line {line}: {msg}"),
            Self::InvalidSplit { index, col } => {
                write!(f, "split {index} on column {col} is not a licensed cut")
            }
            Self::LeafRejected { index, error } => write!(f, "leaf {index} rejected: {error}"),
            Self::Incomplete => write!(
                f,
                "the opttree body is incomplete: it does not close every split it opens"
            ),
        }
    }
}
