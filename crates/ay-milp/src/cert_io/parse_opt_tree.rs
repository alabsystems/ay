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
//! `Certificate::opt_tree` (not `Certificate::tree`), the two Rust types are
//! unrelated, and a `boundleaf` record is a PARSE ERROR inside a `tree` block —
//! `parse_tree` has no arm for it. There is no code path on which a bound leaf
//! can be read as a proof of emptiness.

use super::*;

type PendingSplit = (Col, BigRational, Vec<OptTreeNode>);

struct OptTreeParser {
    frames: Vec<PendingSplit>,
    root: Option<OptTreeNode>,
    line: usize,
}

/// Parse an `opttree` body starting at `start` (the line AFTER the `opttree`
/// opener), through its `end` terminator.
pub(super) fn parse_opt_tree(
    lines: &[&str],
    start: usize,
) -> Result<(OptTreeNode, usize), CertIoError> {
    let mut parser = OptTreeParser {
        frames: Vec::new(),
        root: None,
        line: start,
    };
    while parser.line < lines.len() {
        let Some(node) = parse_opt_tree_record(lines, &mut parser)? else {
            if lines
                .get(parser.line.saturating_sub(1))
                .is_some_and(|line| line.trim() == "end")
            {
                break;
            }
            continue;
        };
        attach(&mut parser, node)?;
    }
    match (parser.root, parser.frames.is_empty()) {
        (Some(root), true) => Ok((root, parser.line)),
        _ => Err(CertIoError::Malformed {
            line: start,
            msg: "opttree block is not a complete binary pre-order terminated by `end`".into(),
        }),
    }
}

fn parse_opt_tree_record(
    lines: &[&str],
    parser: &mut OptTreeParser,
) -> Result<Option<OptTreeNode>, CertIoError> {
    let line = parser.line;
    let record = lines[line].trim();
    let fields: Vec<&str> = record.split_whitespace().collect();
    match fields.first().copied() {
        Some("split") => {
            parse_split(&fields, parser)?;
            parser.line += 1;
            Ok(None)
        }
        // An EMPTINESS leaf. Same `leaf`/`endleaf` shape as the infeasibility
        // tree, and it means the same thing there and here.
        Some("leaf") if fields.len() == 1 => {
            let (multipliers, next) = parse_mults(lines, line + 1, "endleaf")?;
            parser.line = next;
            Ok(Some(OptTreeNode::Empty {
                farkas: FarkasCertificate { multipliers },
            }))
        }
        // A DOMINATION leaf. Deliberately carries NO bound of its own: the
        // bound is recomputed from the multipliers and compared against the
        // value on the VERDICT line, so there is no second number for a forger
        // to disagree with. See `opt_cert`'s module docs.
        Some("boundleaf") if fields.len() == 1 => {
            let (multipliers, next) = parse_mults(lines, line + 1, "endleaf")?;
            parser.line = next;
            Ok(Some(OptTreeNode::Dominated { multipliers }))
        }
        Some("end") if fields.len() == 1 => {
            parser.line += 1;
            Ok(None)
        }
        _ => Err(opt_tree_error(
            line,
            &format!("malformed opttree record `{record}`"),
        )),
    }
}

fn parse_split(fields: &[&str], parser: &mut OptTreeParser) -> Result<(), CertIoError> {
    if fields.len() != 3 {
        return Err(opt_tree_error(parser.line, "malformed split record"));
    }
    let column = fields[1]
        .parse::<u32>()
        .map_err(|_| opt_tree_error(parser.line, "malformed split column"))?;
    let cut = parse_proof_rat(fields[2], ProofParseMode::General)
        .ok_or_else(|| opt_tree_error(parser.line, "malformed split cut"))?;
    parser.frames.push((Col(column), cut, Vec::new()));
    Ok(())
}

fn attach(parser: &mut OptTreeParser, node: OptTreeNode) -> Result<(), CertIoError> {
    let mut completed = node;
    loop {
        let Some((_, _, children)) = parser.frames.last_mut() else {
            if parser.root.is_some() {
                return Err(CertIoError::Malformed {
                    line: parser.line,
                    msg: "opttree block contains more than one root".into(),
                });
            }
            parser.root = Some(completed);
            return Ok(());
        };
        children.push(completed);
        if children.len() < 2 {
            return Ok(());
        }
        let Some((column, cut, children)) = parser.frames.pop() else {
            return Err(opt_tree_error(
                parser.line,
                "opttree parser lost a pending split",
            ));
        };
        let mut children = children.into_iter();
        let (Some(lo), Some(hi), None) = (children.next(), children.next(), children.next()) else {
            return Err(opt_tree_error(
                parser.line,
                "opttree split has the wrong arity",
            ));
        };
        completed = OptTreeNode::Split {
            col: column,
            cut,
            lo: Box::new(lo),
            hi: Box::new(hi),
        };
    }
}

fn opt_tree_error(line: usize, message: &str) -> CertIoError {
    CertIoError::Malformed {
        line: line + 1,
        msg: message.to_owned(),
    }
}
