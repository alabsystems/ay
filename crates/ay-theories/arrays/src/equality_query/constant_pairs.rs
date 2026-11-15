// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Join constant-valued select classes through their existing index blocks.
//!
//! This moves candidate discovery, not proof or equality reasoning. The caller
//! keeps the same index partition, disequality pairs, grouped select emission,
//! final ordering and downstream explanation checks.

use super::*;

pub(super) type ClassBlockGroups = HashMap<TermId, HashMap<TermId, Vec<TermId>>>;

/// Add exactly the constant-distinct class pairs capable of producing a pair
/// in the caller's existing block-restricted emission. A discarded class pair
/// had no shared block, hence its old emission was empty. Every retained pair
/// has the same chosen constants and reaches the same final select product.
///
/// The inverse join avoids the global O(C²) comparison/storage population for
/// C classes at distinct indices. Comparisons are Σ choose(C_block, 2); dense
/// blocks still require quadratic work. This is not a whole-solver complexity,
/// allocation-failure recovery or cancellation-latency bound.
pub(super) fn add_pairs(
    constants: &[(TermId, Constant)],
    groups: &ClassBlockGroups,
    class_pairs: &mut HashSet<(TermId, TermId)>,
) {
    let mut classes_by_block: HashMap<TermId, Vec<usize>> = HashMap::default();
    for (index, (class, _)) in constants.iter().enumerate() {
        let Some(blocks) = groups.get(class) else {
            continue;
        };
        // One entry per CLASS/block, not per select. Constants remain owned
        // once by the caller; index vectors neither clone nor hash their values.
        for &block in blocks.keys() {
            classes_by_block.entry(block).or_default().push(index);
        }
    }
    for classes in classes_by_block.values() {
        for (position, &left) in classes.iter().enumerate() {
            for &right in &classes[position + 1..] {
                #[cfg(test)]
                COMPARISONS.with(|count| count.set(count.get().saturating_add(1)));
                let (left_class, left_value) = &constants[left];
                let (right_class, right_value) = &constants[right];
                if left_value != right_value {
                    // Also deduplicate pairs sharing several index blocks or
                    // already present through explicit disequality evidence.
                    class_pairs.insert(ArraySolver::ordered_pair(*left_class, *right_class));
                }
            }
        }
    }
}

#[cfg(test)]
thread_local! {
    static COMPARISONS: Cell<usize> = const { Cell::new(0) };
}

#[cfg(test)]
fn comparisons() -> usize {
    COMPARISONS.with(Cell::get)
}

#[cfg(test)]
mod tests;
