// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Closed scalar captures under the SAME independent model and original work.

use super::*;
use crate::{recognize_fill_lambda, ArrayValue};

mod grammar;
mod prefix;

impl Evaluator<'_> {
    pub(super) fn fill_lambda_snapshot(
        &self,
        term: TermId,
        depth: usize,
    ) -> EvalResult<Option<Arc<ArraySnapshot>>> {
        self.charge_functional_work(32)?;
        let Some(recipe) = prefix::recognize(self.terms, term)
            .or_else(|| recognize_fill_lambda(self.terms, term).map(prefix::Recipe::from))
        else {
            return Ok(None);
        };
        let nodes = self.fill_grammar(term, recipe.bound)?;
        self.fill_capture_independence(&recipe)?;
        // Authenticate every scalar/array capture, even an unchosen branch,
        // overwritten datum or empty interval. This is one immutable model,
        // not per-value fallbacks or default fabrication.
        for (node, node_depth) in nodes {
            if node == term || node == recipe.bound {
                continue;
            }
            self.charge_functional_work(32)?;
            if self.term_contains(node, recipe.bound)? {
                continue;
            }
            if matches!(self.terms.sort(node), Sort::Array(_)) {
                self.functional_snapshot(node, depth + node_depth + 1)?;
            } else {
                let value = self.eval_operand(node, depth + node_depth + 1)?;
                grammar::scalar_value(&value, self.terms.sort(node))?;
            }
        }
        let value = self.eval_operand(recipe.value, depth + 1)?;
        let source = self.fill_default_snapshot(term, value)?;
        let Some(interval) = recipe.interval else {
            return Ok(Some(source));
        };
        let lo = match interval.lo {
            Some(term) => self.eval_operand(term, depth + 1)?,
            None => ModelValue::bitvec(BigInt::from(0), 64),
        };
        let mut hi = self.eval_operand(interval.hi, depth + 1)?;
        let destination = match interval.destination {
            Some(array) => self.functional_snapshot(array, depth + 1)?,
            None => {
                self.fill_default_snapshot(term, self.eval_operand(interval.frame, depth + 1)?)?
            }
        };
        if interval.inclusive {
            self.charge_functional_work(32)?;
            let ModelValue::BitVec { value, width: 64 } = &hi else {
                return Err("prefix upper bound differs from BV64".into());
            };
            if value == &BigInt::from(u64::MAX) {
                return Ok(Some(source)); // every unsigned BV64 index is <= MAX
            }
            hi = ModelValue::bitvec(value + BigInt::from(1), 64);
        }
        let zero = ModelValue::bitvec(BigInt::from(0), 64);
        self.snapshot_work(|work| {
            ArraySnapshot::range_copy(destination, source, &lo, &hi, &zero, work)
        })
        .map(Some)
    }

    fn fill_capture_independence(&self, recipe: &prefix::Recipe) -> EvalResult<()> {
        let mut captures = [Some(recipe.value), None, None, None];
        if let Some(interval) = recipe.interval {
            captures[1] = interval.lo;
            captures[2] = Some(interval.hi);
            captures[3] = Some(interval.destination.unwrap_or(interval.frame));
        }
        for capture in captures.into_iter().flatten() {
            self.charge_functional_work(32)?;
            if self.term_contains(capture, recipe.bound)? {
                return Err("scalar fill captures its lexical binder".into());
            }
        }
        Ok(())
    }

    fn fill_default_snapshot(
        &self,
        term: TermId,
        default: ModelValue,
    ) -> EvalResult<Arc<ArraySnapshot>> {
        self.snapshot_work(|work| {
            ArraySnapshot::finite(
                ArrayValue {
                    default,
                    store: Vec::new(),
                },
                self.terms.sort(term),
                work,
            )
        })
    }

    fn fill_grammar(&self, root: TermId, bound: TermId) -> EvalResult<Vec<(TermId, usize)>> {
        self.charge_functional_work(32)?;
        let mut pending = Vec::new();
        pending
            .try_reserve_exact(1)
            .map_err(|_| "fill grammar allocation refused")?;
        pending.push((root, 0usize, false));
        let mut active = std::collections::BTreeSet::new();
        let mut seen = std::collections::BTreeMap::new();
        let mut ordered = Vec::new();
        while let Some((term, depth, exit)) = pending.pop() {
            self.charge_functional_work(64)?;
            if depth > 64 || (term.0 as usize) >= self.terms.len() {
                return Err("fill grammar depth or term refused".into());
            }
            if exit {
                active.remove(&term);
                let mut small = [term; 3];
                let children = grammar::children(self.terms, term, &mut small);
                self.charge_functional_work(children.len())?;
                let height = children.iter().try_fold(0usize, |height, child| {
                    seen.get(child)
                        .map(|child_height| height.max(*child_height + 1))
                        .ok_or("fill grammar postorder refused")
                })?;
                if depth + height > 64 {
                    return Err("fill grammar shared depth refused".into());
                }
                seen.insert(term, height);
                self.charge_functional_work(ordered.len() + 1)?;
                ordered
                    .try_reserve(1)
                    .map_err(|_| "fill grammar output allocation refused")?;
                ordered.push((term, depth));
                continue;
            }
            if let Some(height) = seen.get(&term) {
                if depth + *height > 64 {
                    return Err("fill grammar shared depth refused".into());
                }
                continue;
            }
            if !active.insert(term) {
                return Err("cyclic fill grammar refused".into());
            }
            if active.len() + seen.len() > 4096 {
                return Err("fill grammar node limit".into());
            }
            if self.default_projection_target(term)?.is_some() {
                return Err("projected fill grammar requires another interpreter".into());
            }
            let mut small = [term; 3];
            let children = grammar::children(self.terms, term, &mut small);
            if children.len() > 4096 {
                return Err("fill grammar edge limit".into());
            }
            self.charge_functional_work(pending.len() + children.len() + 1)?;
            grammar::node(self.terms, term, root, bound)?;
            pending
                .try_reserve(children.len() + 1)
                .map_err(|_| "fill grammar stack allocation refused")?;
            pending.push((term, depth, true));
            pending.extend(
                children
                    .iter()
                    .rev()
                    .map(|child| (*child, depth + 1, false)),
            );
        }
        Ok(ordered)
    }
}
