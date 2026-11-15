// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Array-valued model cells compared and merged as arrays, not as text.
//!
//! A cell of an array of arrays is the printer's text of the inner array,
//! `((as const <sort>) <default>)` under a `store` chain. One inner array has
//! many spellings: any store order, a store of the default value or none, a
//! fully stored domain under any default, or a single read folded into the
//! else-value. Two consumers compared such cells as strings:
//!
//! - model completion merges a candidate interpretation into the extracted
//!   one cell by cell (`merge_array_completion_candidate`), so the extractor's
//!   `(store ((as const S) #x00) #x5 #x04)` against the candidate's fold
//!   `((as const S) #x04)` was a conflict that tainted the whole array;
//! - the BV model's release of an array of arrays checks that the published
//!   interpretations falsify a definition the SAT assignment set false
//!   (`theories/bv_model/live_definitions.rs`), which needs a real equality.
//!
//! The BV model also reads a cell back into its else-value and stores
//! ([`array_cell_parts`]) to build a store chain over a read of an array of
//! arrays (`theories/bv_model/nested_cells.rs`).
//!
//! [`merge_array_cells`] merges an inner array by the rule the outer merge
//! applies to a whole interpretation, one level at a time: the existing
//! stores stand, a candidate store at an index the existing array does not
//! store is added, two stores at one index merge recursively, and two
//! different scalar values stored at one index are a conflict. The two
//! else-values follow the outer default policy ([`CellDefaultPolicy`]) at
//! every level: under `Preserve` (completion's reads-derived pass) the
//! existing one stands and the candidate's is dropped as a fallback, even
//! where it disagrees with an existing store; under `Require` they must denote
//! the same value wherever an index is left to read them, or the cells
//! conflict and the strict conflict -> taint path runs; under `Ignore` (a
//! defined target) the candidate's replaces the extractor's.
//! [`array_cells_equal`] decides whether two cells denote the same array. A
//! text this reader does not recognise is a conflict to the first and
//! undecided to the second.

use std::collections::{BTreeMap, BTreeSet};

/// A parsed s-expression of rendered model text.
#[derive(Clone, Debug, PartialEq, Eq)]
enum Expr {
    Atom(String),
    List(Vec<Expr>),
}

/// A rendered cell: an inner array, or any other value compared as text.
#[derive(Clone, Debug, PartialEq, Eq)]
enum Cell {
    Scalar(String),
    Array {
        /// The `(as const <sort>)` head, kept verbatim.
        head: String,
        default: Box<Cell>,
        /// One cell per index; the outermost store of an index wins.
        stores: BTreeMap<String, Cell>,
    },
}

/// Nesting beyond which a cell is not parsed.
const MAX_DEPTH: usize = 64;

/// How [`merge_array_cells`] treats the two else-values of an inner array:
/// as the outer merge treats the two outer ones
/// (`model/completion.rs`, `ExistingArrayDefaultPolicy`).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum CellDefaultPolicy {
    /// The existing else-value stands and the candidate's is dropped.
    Preserve,
    /// The two else-values must denote the same value.
    Require,
    /// The candidate's else-value replaces the existing one, which is an
    /// extractor fallback for a defined target.
    Ignore,
}

/// The merge of two different renderings of one array-valued cell, or `None`
/// when they disagree on a stored scalar, on an else-value `policy` requires
/// to agree, or either is not an array this reader recognises.
pub(crate) fn merge_array_cells(
    existing: &str,
    candidate: &str,
    policy: CellDefaultPolicy,
) -> Option<String> {
    let existing = parse_array(existing)?;
    let candidate = parse_array(candidate)?;
    Some(render(&merge(existing, candidate, policy)?))
}

/// The else-value and the stores of an array-valued cell, each rendered as
/// cell text, one store per index; `None` when `text` is not an array this
/// reader recognises.
pub(crate) fn array_cell_parts(text: &str) -> Option<(String, Vec<(String, String)>)> {
    let Cell::Array {
        default, stores, ..
    } = parse_array(text)?
    else {
        return None;
    };
    let stores = stores
        .iter()
        .map(|(index, cell)| (index.clone(), render(cell)))
        .collect();
    Some((render(&default), stores))
}

/// Whether two array-valued cells denote the same array; `None` when either
/// is not an array this reader recognises.
pub(crate) fn array_cells_equal(lhs: &str, rhs: &str) -> Option<bool> {
    Some(equal(&parse_array(lhs)?, &parse_array(rhs)?))
}

fn parse_array(text: &str) -> Option<Cell> {
    let cell = parse_cell(&parse_expr(text)?, 0)?;
    matches!(cell, Cell::Array { .. }).then_some(cell)
}

fn merge(existing: Cell, candidate: Cell, policy: CellDefaultPolicy) -> Option<Cell> {
    match (existing, candidate) {
        (Cell::Scalar(lhs), Cell::Scalar(rhs)) => (lhs == rhs).then_some(Cell::Scalar(lhs)),
        (
            Cell::Array {
                head,
                default,
                mut stores,
            },
            Cell::Array {
                head: candidate_head,
                default: candidate_default,
                stores: candidate_stores,
            },
        ) if head == candidate_head => {
            if policy == CellDefaultPolicy::Require && !equal(&default, &candidate_default) {
                // Different else-values agree only where no index is left to
                // read them.
                let keys: BTreeSet<&String> =
                    stores.keys().chain(candidate_stores.keys()).collect();
                if !covers_domain(&keys) {
                    return None;
                }
            }
            let default = match policy {
                CellDefaultPolicy::Ignore => candidate_default,
                CellDefaultPolicy::Preserve | CellDefaultPolicy::Require => default,
            };
            for (index, cell) in candidate_stores {
                let merged = match stores.remove(&index) {
                    Some(existing_cell) => merge(existing_cell, cell, policy)?,
                    None => cell,
                };
                stores.insert(index, merged);
            }
            Some(Cell::Array {
                head,
                default,
                stores,
            })
        }
        _ => None,
    }
}

/// Same array: equal at every index either stores, and equal defaults unless
/// those indices cover the whole (bit-vector) index domain.
fn equal(lhs: &Cell, rhs: &Cell) -> bool {
    match (lhs, rhs) {
        (Cell::Scalar(lhs), Cell::Scalar(rhs)) => lhs == rhs,
        (
            Cell::Array {
                head,
                default,
                stores,
            },
            Cell::Array {
                head: rhs_head,
                default: rhs_default,
                stores: rhs_stores,
            },
        ) if head == rhs_head => {
            let keys: BTreeSet<&String> = stores.keys().chain(rhs_stores.keys()).collect();
            keys.iter().all(|key| {
                equal(
                    cell_at(stores, default, key),
                    cell_at(rhs_stores, rhs_default, key),
                )
            }) && (equal(default, rhs_default) || covers_domain(&keys))
        }
        _ => false,
    }
}

/// The cell an array holds at `key`: its store there, else its default.
fn cell_at<'a>(stores: &'a BTreeMap<String, Cell>, default: &'a Cell, key: &str) -> &'a Cell {
    stores.get(key).unwrap_or(default)
}

/// Whether `keys`, bit-vector literals of one width, are every value of it.
fn covers_domain(keys: &BTreeSet<&String>) -> bool {
    let width = |key: &str| {
        if let Some(hex) = key.strip_prefix("#x") {
            Some(hex.len() * 4)
        } else {
            key.strip_prefix("#b").map(str::len)
        }
    };
    let Some(first) = keys.iter().next() else {
        return false;
    };
    match width(first) {
        Some(bits) if bits < 64 && keys.iter().all(|key| width(key) == Some(bits)) => {
            keys.len() as u64 == 1u64 << bits
        }
        _ => false,
    }
}

fn parse_cell(expr: &Expr, depth: usize) -> Option<Cell> {
    if depth > MAX_DEPTH {
        return None;
    }
    let Expr::List(items) = expr else {
        return Some(Cell::Scalar(render_expr(expr)));
    };
    match items.as_slice() {
        [Expr::List(head), default] if matches!(head.as_slice(), [Expr::Atom(a), Expr::Atom(c), _] if a == "as" && c == "const") => {
            Some(Cell::Array {
                head: render_expr(&items[0]),
                default: Box::new(parse_cell(default, depth + 1)?),
                stores: BTreeMap::new(),
            })
        }
        [Expr::Atom(store), base, index, value] if store == "store" => {
            let Cell::Array {
                head,
                default,
                mut stores,
            } = parse_cell(base, depth + 1)?
            else {
                return None;
            };
            stores.insert(render_expr(index), parse_cell(value, depth + 1)?);
            Some(Cell::Array {
                head,
                default,
                stores,
            })
        }
        _ => Some(Cell::Scalar(render_expr(expr))),
    }
}

fn render(cell: &Cell) -> String {
    match cell {
        Cell::Scalar(text) => text.clone(),
        Cell::Array {
            head,
            default,
            stores,
        } => {
            let mut text = format!("({head} {})", render(default));
            for (index, value) in stores {
                text = format!("(store {text} {index} {})", render(value));
            }
            text
        }
    }
}

fn render_expr(expr: &Expr) -> String {
    match expr {
        Expr::Atom(atom) => atom.clone(),
        Expr::List(items) => {
            let inner: Vec<String> = items.iter().map(render_expr).collect();
            format!("({})", inner.join(" "))
        }
    }
}

/// Parse one s-expression; `|..|` symbols and `".."` strings are atoms.
fn parse_expr(text: &str) -> Option<Expr> {
    let mut stack: Vec<Vec<Expr>> = vec![Vec::new()];
    let mut chars = text.char_indices().peekable();
    while let Some((start, ch)) = chars.next() {
        match ch {
            '(' => {
                if stack.len() > MAX_DEPTH * 4 {
                    return None;
                }
                stack.push(Vec::new());
            }
            ')' => {
                let list = stack.pop()?;
                stack.last_mut()?.push(Expr::List(list));
            }
            c if c.is_whitespace() => {}
            _ => {
                let mut end = start + ch.len_utf8();
                let quote = matches!(ch, '|' | '"').then_some(ch);
                while let Some(&(at, next)) = chars.peek() {
                    if let Some(quote) = quote {
                        chars.next();
                        end = at + next.len_utf8();
                        if next == quote {
                            break;
                        }
                    } else if next == '(' || next == ')' || next.is_whitespace() {
                        break;
                    } else {
                        chars.next();
                        end = at + next.len_utf8();
                    }
                }
                stack
                    .last_mut()?
                    .push(Expr::Atom(text[start..end].to_string()));
            }
        }
    }
    let mut top = stack.pop()?;
    (stack.is_empty() && top.len() == 1).then(|| top.remove(0))
}

#[cfg(test)]
#[path = "array_cell_tests.rs"]
mod tests;
