// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Prenex QCIR reader (QCIR-G14, the QBF Gallery's non-CNF format).
//!
//! ```text
//! #QCIR-G14 [n]
//! free(v1, ...)            optional, outermost existential; first block only
//! exists(v2, ...) | forall(v3, ...)
//! output(lit)
//! g = and(lit, ...) | or(lit, ...) | xor(lit, lit) | ite(lit, lit, lit)
//! ```
//!
//! A literal is a name or `-name`; names are runs of letters, digits and `_`.
//! Lines starting with `#` after the first are comments. Every name a gate
//! uses must be declared in a quantifier block (`free` included) or defined
//! by an earlier gate line, as QCIR-G14 requires; a gate that names itself,
//! a misspelled name or a forward reference is a syntax error, not a free
//! input. Only `output(...)` may name a gate defined after it.
//!
//! The circuit is translated to prenex CNF directly: each gate in the cone of
//! the output gets one variable, existentially quantified in a new innermost
//! block, and the output literal becomes a unit clause. Each gate gets only
//! the Tseitin implications for the polarities the output uses it in
//! (Plaisted & Greenbaum 1986). For every assignment `X` of the quantified
//! inputs, the gate clauses are satisfiable exactly when the circuit outputs
//! true under `X`: setting every gate to its value under `X` satisfies them
//! when it does, and when they hold, every gate used as true is true under
//! `X` and every gate used as false is false (induction from the inputs), so
//! the output is true. The innermost existential block therefore keeps the
//! formula's truth value. The innermost existential player also gets more
//! freedom than with full equivalences, which the abstraction engine uses
//! for smaller `Win` sets. Gates outside the output's cone are not encoded, and a gate
//! shared by several parents is encoded once, so the CNF has one variable per
//! input and per used gate (no further blow-up). Non-prenex QCIR (quantifier
//! gates in the body) is refused.

use std::collections::HashMap;

use ay_sat::{Literal, Variable};

use crate::formula::{QbfFormula, QuantifierBlock, MAX_QBF_VARS};

/// Error type for QCIR parsing.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum QcirError {
    /// The first line is not a `#QCIR-G14` header.
    MissingHeader,
    /// A line could not be parsed (1-based line number, message).
    Syntax(usize, String),
    /// The input uses a QCIR feature this reader does not support.
    Unsupported(usize, String),
    /// The translated formula would exceed the dense solver state.
    TooLarge(usize),
}

impl std::fmt::Display for QcirError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::MissingHeader => write!(f, "missing '#QCIR-G14' header"),
            Self::Syntax(line, msg) => write!(f, "line {line}: {msg}"),
            Self::Unsupported(line, msg) => write!(f, "line {line}: unsupported: {msg}"),
            Self::TooLarge(n) => write!(
                f,
                "{n} variables exceed the maximum supported {MAX_QBF_VARS}; refusing to allocate"
            ),
        }
    }
}

impl std::error::Error for QcirError {}

/// Whether `input` looks like QCIR (its first non-blank text is `#QCIR`).
pub fn is_qcir(input: &str) -> bool {
    input.trim_start().starts_with("#QCIR")
}

#[derive(Clone, Copy)]
enum GateKind {
    And,
    Or,
    Xor,
    Ite,
}

struct Gate {
    kind: GateKind,
    /// Operands as signed node references (node index + 1, negative when
    /// negated).
    operands: Vec<i64>,
}

/// A node is a quantified (or free) input or a gate.
enum Node {
    Input,
    Gate(Gate),
}

struct Reader {
    names: HashMap<String, usize>,
    nodes: Vec<Node>,
    /// Quantifier blocks in order: (exists?, node indices).
    blocks: Vec<(bool, Vec<usize>)>,
}

fn is_name(text: &str) -> bool {
    !text.is_empty() && text.bytes().all(|b| b.is_ascii_alphanumeric() || b == b'_')
}

/// Split `head(args)` into `head` and the argument text.
fn call(line: &str) -> Option<(&str, &str)> {
    let open = line.find('(')?;
    let rest = line.get(open + 1..)?.trim_end();
    let args = rest.strip_suffix(')')?;
    Some((line.get(..open)?.trim(), args))
}

fn split_args(args: &str) -> Vec<&str> {
    if args.trim().is_empty() {
        return Vec::new();
    }
    args.split(',').map(str::trim).collect()
}

impl Reader {
    fn literal(&mut self, line: usize, text: &str) -> Result<i64, QcirError> {
        let (negated, name) = match text.strip_prefix('-') {
            Some(name) => (true, name.trim()),
            None => (false, text),
        };
        if !is_name(name) {
            return Err(QcirError::Syntax(line, format!("bad literal '{text}'")));
        }
        // A name must be declared or defined before it is used: an unknown
        // name is invalid QCIR, not an implicit free input.
        let index = *self.names.get(name).ok_or_else(|| {
            QcirError::Syntax(
                line,
                format!("'{name}' is neither declared nor defined before this use"),
            )
        })?;
        let reference = i64::try_from(index + 1)
            .map_err(|_| QcirError::Syntax(line, "too many nodes".to_string()))?;
        Ok(if negated { -reference } else { reference })
    }

    fn declare(&mut self, line: usize, exists: bool, args: &str) -> Result<(), QcirError> {
        let mut vars = Vec::new();
        for name in split_args(args) {
            if !is_name(name) {
                return Err(QcirError::Syntax(line, format!("bad variable '{name}'")));
            }
            if self.names.contains_key(name) {
                return Err(QcirError::Syntax(
                    line,
                    format!("variable '{name}' is declared twice"),
                ));
            }
            let index = self.nodes.len();
            self.nodes.push(Node::Input);
            self.names.insert(name.to_string(), index);
            vars.push(index);
        }
        self.blocks.push((exists, vars));
        Ok(())
    }

    fn gate(&mut self, line: usize, name: &str, body: &str) -> Result<(), QcirError> {
        if !is_name(name) {
            return Err(QcirError::Syntax(line, format!("bad gate name '{name}'")));
        }
        if self.names.contains_key(name) {
            return Err(QcirError::Syntax(
                line,
                format!("'{name}' is defined twice"),
            ));
        }
        let (head, args) =
            call(body).ok_or_else(|| QcirError::Syntax(line, format!("bad gate '{body}'")))?;
        let kind = match head {
            "and" => GateKind::And,
            "or" => GateKind::Or,
            "xor" => GateKind::Xor,
            "ite" => GateKind::Ite,
            "exists" | "forall" => {
                return Err(QcirError::Unsupported(
                    line,
                    "quantifier gate (non-prenex QCIR)".to_string(),
                ))
            }
            other => {
                return Err(QcirError::Syntax(
                    line,
                    format!("unknown gate type '{other}'"),
                ))
            }
        };
        let mut operands = Vec::new();
        for arg in split_args(args) {
            if arg.strip_prefix('-').map_or(arg, str::trim) == name {
                return Err(QcirError::Syntax(
                    line,
                    format!("gate '{name}' uses itself"),
                ));
            }
            operands.push(self.literal(line, arg)?);
        }
        let arity_ok = match kind {
            GateKind::And | GateKind::Or => true,
            GateKind::Xor => operands.len() == 2,
            GateKind::Ite => operands.len() == 3,
        };
        if !arity_ok {
            return Err(QcirError::Syntax(line, format!("wrong arity in '{body}'")));
        }
        let index = self.nodes.len();
        self.nodes.push(Node::Gate(Gate { kind, operands }));
        self.names.insert(name.to_string(), index);
        Ok(())
    }
}

/// Parse a prenex QCIR string into an equisatisfiable prenex CNF formula
/// (same truth value; see the module comment).
pub fn parse_qcir(input: &str) -> Result<QbfFormula, QcirError> {
    let mut lines = input.lines().enumerate();
    let header = lines
        .by_ref()
        .find(|(_, l)| !l.trim().is_empty())
        .ok_or(QcirError::MissingHeader)?;
    if !header.1.trim().starts_with("#QCIR-G14") {
        return Err(QcirError::MissingHeader);
    }
    let mut reader = Reader {
        names: HashMap::new(),
        nodes: Vec::new(),
        blocks: Vec::new(),
    };
    // The output may name a gate defined after it: resolve it at the end.
    let mut output_text: Option<(usize, String)> = None;
    // Quantifier statements read so far, `free` included.
    let mut blocks_seen = 0usize;
    for (number, raw) in lines {
        let line_no = number + 1;
        let line = raw.trim();
        if line.is_empty() || line.starts_with('#') {
            continue;
        }
        if let Some((name, body)) = line.split_once('=') {
            if output_text.is_none() {
                return Err(QcirError::Syntax(
                    line_no,
                    "gate before output(...)".to_string(),
                ));
            }
            reader.gate(line_no, name.trim(), body.trim())?;
            continue;
        }
        let (head, args) = call(line)
            .ok_or_else(|| QcirError::Syntax(line_no, format!("cannot parse '{line}'")))?;
        match head {
            "free" | "exists" | "forall" => {
                if output_text.is_some() {
                    return Err(QcirError::Syntax(
                        line_no,
                        "quantifier block after output(...)".to_string(),
                    ));
                }
                // QCIR-G14 allows one `free` block, before the prefix. A
                // `free` block anywhere else would be read as an existential
                // block at that position, and the verdict would depend on
                // where an invalid line sits.
                if head == "free" && blocks_seen > 0 {
                    return Err(QcirError::Syntax(
                        line_no,
                        "free(...) must be the first block, and there is only one".to_string(),
                    ));
                }
                blocks_seen += 1;
                reader.declare(line_no, head != "forall", args)?;
            }
            "output" => {
                if output_text.is_some() {
                    return Err(QcirError::Syntax(line_no, "second output(...)".to_string()));
                }
                output_text = Some((line_no, args.trim().to_string()));
            }
            other => {
                return Err(QcirError::Syntax(
                    line_no,
                    format!("unknown statement '{other}'"),
                ))
            }
        }
    }
    let (out_line, out_text) =
        output_text.ok_or_else(|| QcirError::Syntax(0, "missing output(...)".to_string()))?;
    let output = reader.literal(out_line, &out_text)?;
    encode(&reader, output)
}

fn encode(reader: &Reader, output: i64) -> Result<QbfFormula, QcirError> {
    // Polarity in which each node is used by the output (bit 1: as true,
    // bit 2: as false); zero outside the output's cone. Gates refer only to
    // earlier nodes, so one reverse sweep suffices.
    const POS: u8 = 1;
    const NEG: u8 = 2;
    let flip = |p: u8| ((p & POS) << 1) | ((p & NEG) >> 1);
    let signed = |p: u8, reference: i64| if reference > 0 { p } else { flip(p) };
    let node_count = reader.nodes.len();
    let mut polarity = vec![0u8; node_count];
    polarity[output.unsigned_abs() as usize - 1] = signed(POS, output);
    for index in (0..node_count).rev() {
        let p = polarity[index];
        if p == 0 {
            continue;
        }
        if let Node::Gate(gate) = &reader.nodes[index] {
            for (k, &operand) in gate.operands.iter().enumerate() {
                let both = matches!(gate.kind, GateKind::Xor)
                    || (matches!(gate.kind, GateKind::Ite) && k == 0);
                let needed = if both { POS | NEG } else { signed(p, operand) };
                polarity[operand.unsigned_abs() as usize - 1] |= needed;
            }
        }
    }
    let used: Vec<bool> = polarity.iter().map(|&p| p != 0).collect();

    // Number variables: declared inputs in prefix order, then used gates.
    let mut id = vec![0u32; node_count];
    let mut next: usize = 0;
    let mut assign = |index: usize, id: &mut Vec<u32>| -> Result<u32, QcirError> {
        next += 1;
        if next > MAX_QBF_VARS {
            return Err(QcirError::TooLarge(next));
        }
        let value = u32::try_from(next).map_err(|_| QcirError::TooLarge(next))?;
        id[index] = value;
        Ok(value)
    };
    let mut prefix = Vec::new();
    for (exists, vars) in &reader.blocks {
        let mut ids = Vec::with_capacity(vars.len());
        for &index in vars {
            ids.push(assign(index, &mut id)?);
        }
        prefix.push(if *exists {
            QuantifierBlock::exists(ids)
        } else {
            QuantifierBlock::forall(ids)
        });
    }
    let mut gate_vars = Vec::new();
    for index in 0..node_count {
        if used[index] && matches!(reader.nodes[index], Node::Gate(_)) {
            gate_vars.push(assign(index, &mut id)?);
        }
    }
    let num_vars = next;

    let lit = |reference: i64| -> Literal {
        let var = Variable::new(id[reference.unsigned_abs() as usize - 1]);
        if reference > 0 {
            Literal::positive(var)
        } else {
            Literal::negative(var)
        }
    };

    let mut clauses: Vec<Vec<Literal>> = Vec::new();
    for index in 0..node_count {
        if !used[index] {
            continue;
        }
        let Node::Gate(gate) = &reader.nodes[index] else {
            continue;
        };
        let g = Literal::positive(Variable::new(id[index]));
        let ops: Vec<Literal> = gate.operands.iter().map(|&r| lit(r)).collect();
        // Plaisted-Greenbaum: emit only the implication directions the
        // output's cone needs (`g → f` when `g` is used as true, `f → g`
        // when it is used as false).
        let (pos, neg) = (polarity[index] & POS != 0, polarity[index] & NEG != 0);
        match gate.kind {
            GateKind::And => {
                if pos {
                    for &a in &ops {
                        clauses.push(vec![g.negated(), a]);
                    }
                }
                if neg {
                    let mut long: Vec<Literal> = ops.iter().map(|a| a.negated()).collect();
                    long.push(g);
                    clauses.push(long);
                }
            }
            GateKind::Or => {
                if pos {
                    let mut long = ops.clone();
                    long.push(g.negated());
                    clauses.push(long);
                }
                if neg {
                    for &a in &ops {
                        clauses.push(vec![g, a.negated()]);
                    }
                }
            }
            GateKind::Xor => {
                let (a, b) = (ops[0], ops[1]);
                if pos {
                    clauses.push(vec![g.negated(), a, b]);
                    clauses.push(vec![g.negated(), a.negated(), b.negated()]);
                }
                if neg {
                    clauses.push(vec![g, a.negated(), b]);
                    clauses.push(vec![g, a, b.negated()]);
                }
            }
            GateKind::Ite => {
                let (c, t, e) = (ops[0], ops[1], ops[2]);
                if pos {
                    clauses.push(vec![g.negated(), c.negated(), t]);
                    clauses.push(vec![g.negated(), c, e]);
                }
                if neg {
                    clauses.push(vec![g, c.negated(), t.negated()]);
                    clauses.push(vec![g, c, e.negated()]);
                }
            }
        }
    }
    clauses.push(vec![lit(output)]);
    if !gate_vars.is_empty() {
        prefix.push(QuantifierBlock::exists(gate_vars));
    }
    Ok(QbfFormula::new(num_vars, prefix, clauses))
}

#[cfg(test)]
#[path = "qcir_tests.rs"]
mod tests;
