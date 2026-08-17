// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Deterministic near-linear cover construction.

use std::collections::VecDeque;

use ay_core::term::TermId;

/// Candidate pin sets, ordered as both bipartite sides followed by a general
/// greedy cover.  Every returned cover leaves at most one unpinned factor in
/// every monomial, counting multiplicity.
pub(super) fn grounding_covers(monomials: &[Vec<TermId>]) -> Vec<Vec<TermId>> {
    let mut candidates = Vec::with_capacity(3);
    if let Some((left, right)) = bipartite_sides(monomials) {
        candidates.push(left);
        candidates.push(right);
    }
    candidates.push(greedy_cover(monomials));
    candidates.retain(|cover| !cover.is_empty());

    let mut unique = Vec::with_capacity(candidates.len());
    for cover in candidates {
        if !unique.contains(&cover) {
            unique.push(cover);
        }
    }
    unique
}

/// Two-color a graph of distinct bilinear products.  Either color class is a
/// cover, which lets template systems try "pin multipliers" and "pin template
/// coefficients" independently.
pub(super) fn bipartite_sides(monomials: &[Vec<TermId>]) -> Option<(Vec<TermId>, Vec<TermId>)> {
    if monomials.is_empty()
        || monomials
            .iter()
            .any(|monomial| monomial.len() != 2 || monomial[0] == monomial[1])
    {
        return None;
    }

    let (variables, index) = index_variables(monomials);
    let mut adjacency = vec![Vec::new(); variables.len()];
    for monomial in monomials {
        let left = index[&monomial[0]];
        let right = index[&monomial[1]];
        adjacency[left].push(right);
        adjacency[right].push(left);
    }

    let mut colors = vec![None; variables.len()];
    let mut queue = VecDeque::new();
    for seed in 0..variables.len() {
        if colors[seed].is_some() {
            continue;
        }
        colors[seed] = Some(false);
        queue.push_back(seed);
        while let Some(vertex) = queue.pop_front() {
            let color = colors[vertex]?;
            for &neighbor in &adjacency[vertex] {
                match colors[neighbor] {
                    None => {
                        colors[neighbor] = Some(!color);
                        queue.push_back(neighbor);
                    }
                    Some(other) if other == color => return None,
                    Some(_) => {}
                }
            }
        }
    }

    let mut left = Vec::new();
    let mut right = Vec::new();
    for (variable, color) in variables.into_iter().zip(colors) {
        match color {
            Some(false) => left.push(variable),
            Some(true) => right.push(variable),
            None => return None,
        }
    }
    (!left.is_empty() && !right.is_empty()).then_some((left, right))
}

/// General deterministic cover.  Repeated factors are mandatory; remaining
/// factors are pinned by descending global frequency so one factor per
/// monomial stays free.  Dense scratch vectors keep this linear in the total
/// factor count instead of repeatedly scanning partial covers.
pub(super) fn greedy_cover(monomials: &[Vec<TermId>]) -> Vec<TermId> {
    let (variables, index) = index_variables(monomials);
    let mut in_cover = vec![false; variables.len()];
    let mut frequency = vec![0usize; variables.len()];
    for monomial in monomials {
        for variable in monomial {
            frequency[index[variable]] += 1;
        }
    }

    let mut seen = vec![false; variables.len()];
    let mut touched = Vec::new();
    for monomial in monomials {
        touched.clear();
        for variable in monomial {
            let slot = index[variable];
            if seen[slot] {
                in_cover[slot] = true;
            } else {
                seen[slot] = true;
                touched.push(slot);
            }
        }
        for &slot in &touched {
            seen[slot] = false;
        }
    }

    for monomial in monomials {
        let mut free = Vec::new();
        for variable in monomial {
            let slot = index[variable];
            if !in_cover[slot] && !seen[slot] {
                seen[slot] = true;
                free.push(slot);
            }
        }
        for &slot in &free {
            seen[slot] = false;
        }
        if free.len() <= 1 {
            continue;
        }
        free.sort_by_key(|&slot| (std::cmp::Reverse(frequency[slot]), variables[slot]));
        for &slot in &free[..free.len() - 1] {
            in_cover[slot] = true;
        }
    }

    variables
        .into_iter()
        .enumerate()
        .filter_map(|(slot, variable)| in_cover[slot].then_some(variable))
        .collect()
}

fn index_variables(monomials: &[Vec<TermId>]) -> (Vec<TermId>, crate::HashMap<TermId, usize>) {
    let mut variables = Vec::new();
    for monomial in monomials {
        variables.extend_from_slice(monomial);
    }
    variables.sort_unstable();
    variables.dedup();

    let mut index = crate::HashMap::default();
    for (slot, variable) in variables.iter().copied().enumerate() {
        index.insert(variable, slot);
    }
    (variables, index)
}

#[cfg(test)]
pub(super) fn free_factor_count(monomial: &[TermId], cover: &[TermId]) -> usize {
    monomial
        .iter()
        .filter(|variable| !cover.contains(variable))
        .count()
}
