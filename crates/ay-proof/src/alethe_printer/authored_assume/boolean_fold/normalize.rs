// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The bottom-up fold of one printed surface: operands first (one `cong`),
//! then one mirrored rewrite of the node, then the rewritten text again, the
//! equalities chained with `trans`.

use super::super::super::split_alethe_application_bounded;
use super::super::{MAX_EQUIVALENCE_BYTES, MAX_EQUIVALENCE_DEPTH, MAX_EQUIVALENCE_NODES};
use super::mirror::{top_rewrite_with_progress, FoldRule, FOLD_CONNECTIVES};

const MAX_FOLD_WORK: u64 = 4 * 1024 * 1024;
const MAX_FOLD_OUTPUT_BYTES: usize = 32 * 1024 * 1024;

/// Only simple native connective spellings are fold heads. An operand came
/// from the bounded balanced scanner; all other heads remain opaque leaves.
fn fold_head(text: &str) -> Option<&'static str> {
    let inner = text
        .strip_prefix('(')?
        .strip_suffix(')')?
        .trim_start_matches(|character: char| character.is_ascii_whitespace());
    FOLD_CONNECTIVES.into_iter().find(|head| {
        inner.strip_prefix(head).is_some_and(|tail| {
            tail.is_empty()
                || tail.as_bytes().first().is_some_and(|byte| {
                    byte.is_ascii_whitespace() || matches!(byte, b'(' | b'"' | b'|')
                })
        })
    })
}

/// The result of folding one printed node.
pub(super) struct Normalized {
    text: String,
    /// The id of the step concluding `(= input text)`; `None` when unchanged.
    proof: Option<String>,
    /// Whether any rewrite below removed structure ([`FoldRule::folds`]).
    folded: bool,
}

/// Shared bounds for one fold derivation.
struct FoldBudget<'n, 'p> {
    nodes: &'n mut usize,
    output: Vec<String>,
    output_bound: usize,
    work: u64,
    refused: bool,
    progress: &'p mut dyn FnMut(u64) -> bool,
}

impl FoldBudget<'_, '_> {
    fn spend(&mut self, amount: u64) -> bool {
        let Some(next) = self.work.checked_add(amount) else {
            self.refused = true;
            return false;
        };
        if self.refused || next > MAX_FOLD_WORK || !(self.progress)(amount) {
            self.refused = true;
            return false;
        }
        self.work = next;
        true
    }

    fn admit(&mut self, depth: usize, text: &str) -> bool {
        if depth > MAX_EQUIVALENCE_DEPTH
            || *self.nodes >= MAX_EQUIVALENCE_NODES
            || text.len() > MAX_EQUIVALENCE_BYTES
            || !self.spend(text.len() as u64 + 1)
        {
            return false;
        }
        *self.nodes += 1;
        true
    }

    fn admit_output(&mut self, texts: &[&str], id: &str, premises: usize) -> bool {
        let bound = texts
            .iter()
            .try_fold(256usize, |sum, text| sum.checked_add(text.len()))
            .and_then(|bytes| bytes.checked_mul(8))
            .and_then(|bytes| {
                premises
                    .checked_mul(id.len().saturating_add(64))
                    .and_then(|ids| bytes.checked_add(ids))
            });
        let Some(bound) = bound else {
            return false;
        };
        let Some(total) = self.output_bound.checked_add(bound) else {
            return false;
        };
        if total > MAX_FOLD_OUTPUT_BYTES || !self.spend(bound as u64) {
            return false;
        }
        self.output_bound = total;
        true
    }
}

/// Fold `text` bottom-up, emitting every step under ids that extend `id`.
/// The returned proof id is `id` itself whenever the node changed.
fn normalize(
    text: &str,
    id: &str,
    depth: usize,
    budget: &mut FoldBudget<'_, '_>,
) -> Option<Normalized> {
    if !budget.admit(depth, text) {
        return None;
    }
    let unchanged = || Normalized {
        text: text.to_string(),
        proof: None,
        folded: false,
    };
    let Some(head) = fold_head(text) else {
        return Some(unchanged());
    };
    let operands = split_alethe_application_bounded(
        text,
        head,
        MAX_EQUIVALENCE_NODES.saturating_sub(*budget.nodes),
        MAX_EQUIVALENCE_BYTES,
    )
    .ok()?;

    let mut folded = false;
    let mut child_proofs = Vec::new();
    let mut rebuilt = Vec::with_capacity(operands.len());
    for (position, operand) in operands.iter().enumerate() {
        if !budget.spend(id.len() as u64 + 32) {
            return None;
        }
        let child = normalize(operand, &format!("{id}.a{position}"), depth + 1, budget)?;
        folded |= child.folded;
        if let Some(proof) = child.proof {
            child_proofs.push(proof);
        }
        rebuilt.push(child.text);
    }
    let rewrite = top_rewrite_with_progress(head, &rebuilt, &mut |amount| budget.spend(amount));
    if budget.refused {
        return None;
    }
    let rest = match &rewrite {
        Some((rule, rewritten)) => {
            folded |= rule.folds();
            Some(normalize(rewritten, &format!("{id}.n"), depth + 1, budget)?)
        }
        None => None,
    };
    if let Some(rest) = &rest {
        folded |= rest.folded;
    }
    let rebuild_bound = rebuilt
        .iter()
        .try_fold(head.len() + 3, |sum, text| sum.checked_add(text.len() + 1))?;
    if !budget.spend(u64::try_from(rebuild_bound.checked_mul(2)?).ok()?) {
        return None;
    }
    let rebuilt_text = format!("({head} {})", rebuilt.join(" "));
    let rewritten_text = rewrite
        .as_ref()
        .map(|(_, text)| text.as_str())
        .unwrap_or("");
    let rest_text = rest.as_ref().map(|rest| rest.text.as_str()).unwrap_or("");
    if !budget.admit_output(
        &[text, &rebuilt_text, rewritten_text, rest_text],
        id,
        child_proofs.len(),
    ) {
        return None;
    }
    let links = NodeLinks {
        text,
        rebuilt: rebuilt_text,
        child_proofs,
        rewrite,
        rest,
    };
    let Some(final_text) = links.emit(id, &mut budget.output) else {
        return Some(unchanged());
    };
    Some(Normalized {
        text: final_text,
        proof: Some(id.to_string()),
        folded,
    })
}

/// One node's own equalities: the `cong` over its changed operands, its one
/// rewrite, and the fold of the rewritten text.
struct NodeLinks<'t> {
    text: &'t str,
    /// The node over its folded operands.
    rebuilt: String,
    child_proofs: Vec<String>,
    rewrite: Option<(FoldRule, String)>,
    rest: Option<Normalized>,
}

impl NodeLinks<'_> {
    /// Emit the links under `id`: one step when there is one, otherwise each
    /// link under its own id and a `trans` under `id`. Returns the node's
    /// folded text, or `None` when nothing changed.
    fn emit(self, id: &str, output: &mut Vec<String>) -> Option<String> {
        let NodeLinks {
            text,
            rebuilt,
            child_proofs,
            rewrite,
            rest,
        } = self;
        let rest_proof = rest.as_ref().and_then(|rest| rest.proof.clone());
        let cong = |step_id: &str| {
            format!(
                "(step {step_id} (cl (= {text} {rebuilt})) :rule cong :premises ({}))",
                child_proofs.join(" ")
            )
        };
        let links = usize::from(!child_proofs.is_empty())
            + usize::from(rewrite.is_some())
            + usize::from(rest_proof.is_some());
        let final_text = match (&rest, &rewrite) {
            (Some(rest), _) => rest.text.clone(),
            (None, Some((_, rewritten))) => rewritten.clone(),
            // Only the operands changed.
            (None, None) => rebuilt.clone(),
        };
        match links {
            0 => return None,
            1 => match &rewrite {
                Some((rule, rewritten)) if child_proofs.is_empty() => {
                    output.push(rule.step(id, text, rewritten));
                }
                _ => output.push(cong(id)),
            },
            _ => {
                let mut premises = Vec::new();
                if !child_proofs.is_empty() {
                    let cong_id = format!("{id}.g");
                    output.push(cong(&cong_id));
                    premises.push(cong_id);
                }
                if let Some((rule, rewritten)) = &rewrite {
                    let from = if premises.is_empty() {
                        text
                    } else {
                        rebuilt.as_str()
                    };
                    let rewrite_id = format!("{id}.s");
                    output.push(rule.step(&rewrite_id, from, rewritten));
                    premises.push(rewrite_id);
                }
                premises.extend(rest_proof);
                output.push(format!(
                    "(step {id} (cl (= {text} {final_text})) :rule trans :premises ({}))",
                    premises.join(" ")
                ));
            }
        }
        Some(final_text)
    }
}

/// Fold `surface` under ids extending `id`: the folded text, the steps, and
/// whether a structural rewrite fired. `None` when the fold is over a bound or
/// changes nothing.
pub(super) fn fold_surface(
    surface: &str,
    id: &str,
    depth: usize,
    nodes: &mut usize,
) -> Option<(String, Vec<String>, bool)> {
    fold_surface_with_progress(surface, id, depth, nodes, &mut |_| true)
}

pub(super) fn fold_surface_with_progress(
    surface: &str,
    id: &str,
    depth: usize,
    nodes: &mut usize,
    progress: &mut dyn FnMut(u64) -> bool,
) -> Option<(String, Vec<String>, bool)> {
    let mut budget = FoldBudget {
        nodes,
        output: Vec::new(),
        output_bound: 0,
        work: 0,
        refused: false,
        progress,
    };
    let normalized = normalize(surface, id, depth, &mut budget)?;
    normalized.proof.as_ref()?;
    Some((normalized.text, budget.output, normalized.folded))
}

#[cfg(test)]
#[path = "normalize_resource_tests.rs"]
mod resource_tests;
