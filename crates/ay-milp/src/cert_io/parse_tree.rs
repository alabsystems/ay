// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

type PendingSplit = (Col, BigRational, Vec<TreeNode>);

struct TreeParser {
    frames: Vec<PendingSplit>,
    root: Option<TreeNode>,
    line: usize,
    nodes: usize,
    multipliers: usize,
}

pub(super) fn parse_tree(lines: &[&str], start: usize) -> Result<(TreeNode, usize), CertIoError> {
    parse_tree_until(lines, start, "end", ProofParseMode::General)
}

pub(super) fn parse_tree_until(
    lines: &[&str],
    start: usize,
    terminator: &str,
    mode: ProofParseMode,
) -> Result<(TreeNode, usize), CertIoError> {
    let mut parser = TreeParser {
        frames: Vec::new(),
        root: None,
        line: start,
        nodes: 0,
        multipliers: 0,
    };
    while parser.line < lines.len() {
        let Some(node) = parse_tree_record(lines, terminator, mode, &mut parser)? else {
            if lines
                .get(parser.line.saturating_sub(1))
                .is_some_and(|line| line.trim() == terminator)
            {
                break;
            }
            continue;
        };
        attach_tree_node(&mut parser, node)?;
    }
    match (parser.root, parser.frames.is_empty()) {
        (Some(root), true) => Ok((root, parser.line)),
        _ => Err(CertIoError::Malformed {
            line: start,
            msg: format!(
                "tree block is not a complete binary pre-order terminated by `{terminator}`"
            ),
        }),
    }
}

fn parse_tree_record(
    lines: &[&str],
    terminator: &str,
    mode: ProofParseMode,
    parser: &mut TreeParser,
) -> Result<Option<TreeNode>, CertIoError> {
    let line = parser.line;
    let record = lines[line].trim();
    let fields: Vec<&str> = record.split_whitespace().collect();
    match fields.first().copied() {
        Some("split") => {
            parse_split(&fields, mode, parser)?;
            parser.line += 1;
            Ok(None)
        }
        Some("leaf") => {
            let node = parse_leaf(lines, mode, parser)?;
            Ok(Some(node))
        }
        Some(token) if token == terminator && fields.len() == 1 => {
            parser.line += 1;
            Ok(None)
        }
        _ => Err(tree_error(
            line,
            &format!("malformed tree record `{record}`"),
        )),
    }
}

fn parse_split(
    fields: &[&str],
    mode: ProofParseMode,
    parser: &mut TreeParser,
) -> Result<(), CertIoError> {
    if fields.len() != 3 {
        return Err(tree_error(parser.line, "malformed split record"));
    }
    let column = fields[1]
        .parse::<u32>()
        .map_err(|_| tree_error(parser.line, "malformed split column"))?;
    charge_tree_node(parser, mode)?;
    let cut = parse_proof_rat(fields[2], mode)
        .ok_or_else(|| tree_error(parser.line, "malformed split cut"))?;
    if mode == ProofParseMode::Affine && parser.frames.len() >= MAX_AFFINE_TREE_DEPTH {
        return Err(tree_error(
            parser.line,
            "affine tree depth exceeds hard cap",
        ));
    }
    parser.frames.push((Col(column), cut, Vec::new()));
    Ok(())
}

fn parse_leaf(
    lines: &[&str],
    mode: ProofParseMode,
    parser: &mut TreeParser,
) -> Result<TreeNode, CertIoError> {
    charge_tree_node(parser, mode)?;
    let line = parser.line;
    let (multipliers, next) = parse_mults_mode(lines, line + 1, "endleaf", mode)?;
    parser.multipliers = parser
        .multipliers
        .checked_add(multipliers.len())
        .ok_or_else(|| tree_error(line, "tree multiplier count overflow"))?;
    if mode == ProofParseMode::Affine && parser.multipliers > MAX_AFFINE_PROOF_MULTIPLIERS {
        return Err(tree_error(
            line,
            "affine tree multiplier count exceeds hard cap",
        ));
    }
    parser.line = next;
    Ok(TreeNode::Leaf {
        farkas: FarkasCertificate { multipliers },
    })
}

fn charge_tree_node(parser: &mut TreeParser, mode: ProofParseMode) -> Result<(), CertIoError> {
    parser.nodes = parser
        .nodes
        .checked_add(1)
        .ok_or_else(|| tree_error(parser.line, "tree node count overflow"))?;
    if mode == ProofParseMode::Affine && parser.nodes > MAX_AFFINE_TREE_NODES {
        return Err(tree_error(
            parser.line,
            "affine tree node count exceeds hard cap",
        ));
    }
    Ok(())
}

fn attach_tree_node(parser: &mut TreeParser, node: TreeNode) -> Result<(), CertIoError> {
    let mut completed = node;
    loop {
        let Some((_, _, children)) = parser.frames.last_mut() else {
            if parser.root.is_some() {
                return Err(CertIoError::Malformed {
                    line: parser.line,
                    msg: "tree block contains more than one root".into(),
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
            return Err(tree_error(parser.line, "tree parser lost a pending split"));
        };
        let mut children = children.into_iter();
        let (Some(lo), Some(hi), None) = (children.next(), children.next(), children.next()) else {
            return Err(tree_error(parser.line, "tree split has the wrong arity"));
        };
        completed = TreeNode::Split {
            col: column,
            cut,
            lo: Box::new(lo),
            hi: Box::new(hi),
        };
    }
}

fn tree_error(line: usize, message: &str) -> CertIoError {
    CertIoError::Malformed {
        line: line + 1,
        msg: message.to_owned(),
    }
}
