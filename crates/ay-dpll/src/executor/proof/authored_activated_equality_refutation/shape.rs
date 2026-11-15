// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Source-owned recipes and a bounded, nonredundant equality-path search.

use super::*;

#[derive(Clone, Copy)]
pub(super) struct Source {
    pub(super) root: TermId,
    pub(super) body: TermId,
    pub(super) activation: Option<TermId>,
}

#[derive(Clone, Copy)]
pub(super) struct Node {
    pub(super) term: TermId,
    pub(super) source: usize,
    pub(super) parent: Option<(usize, u32)>,
    depth: usize,
}

#[derive(Clone, Copy)]
pub(super) struct Edge {
    pub(super) node: usize,
    pub(super) equality: TermId,
    pub(super) left: TermId,
    pub(super) right: TermId,
}

#[derive(Clone, Copy)]
pub(super) struct Goal {
    pub(super) node: usize,
    pub(super) equality: TermId,
    pub(super) left: TermId,
    pub(super) right: TermId,
}

pub(super) struct Plan {
    pub(super) sources: Vec<Source>,
    pub(super) nodes: Vec<Node>,
    pub(super) edges: Vec<Edge>,
    pub(super) goals: Vec<Goal>,
}

pub(super) fn scan(
    terms: &TermStore,
    originals: &[TermId],
    budget: &mut Budget<'_>,
) -> Option<Plan> {
    let mut plan = Plan {
        sources: Vec::new(),
        nodes: Vec::new(),
        edges: Vec::new(),
        goals: Vec::new(),
    };
    for &root in originals {
        let source = source(terms, originals, root, budget)?;
        let index = plan.sources.len();
        budget.push(&mut plan.sources, source)?;
        budget.push(
            &mut plan.nodes,
            Node {
                term: source.body,
                source: index,
                parent: None,
                depth: 0,
            },
        )?;
    }
    let mut cursor = 0usize;
    while cursor < plan.nodes.len() {
        budget.charge(1, 0)?;
        let node = plan.nodes[cursor];
        if node.depth > MAX_DEPTH || terms.sort(node.term) != &Sort::Bool {
            return None;
        }
        if let TermData::App(Symbol::Named(name), children) = terms.get(node.term) {
            if name == "and" {
                if children.len() < 2
                    || plan.nodes.len().checked_add(children.len())? > MAX_PLAN_NODES
                {
                    return None;
                }
                for (position, &child) in children.iter().enumerate() {
                    if terms.sort(child) != &Sort::Bool {
                        return None;
                    }
                    budget.push(
                        &mut plan.nodes,
                        Node {
                            term: child,
                            source: node.source,
                            parent: Some((cursor, u32::try_from(position).ok()?)),
                            depth: node.depth.checked_add(1)?,
                        },
                    )?;
                }
                cursor += 1;
                continue;
            }
        }
        if let Some((left, right)) = equality(terms, node.term, budget)? {
            if left != right {
                if plan.edges.len() == MAX_EQUALITIES {
                    return None;
                }
                budget.push(
                    &mut plan.edges,
                    Edge {
                        node: cursor,
                        equality: node.term,
                        left,
                        right,
                    },
                )?;
            }
        } else if let TermData::Not(inner) = terms.get(node.term) {
            if let Some((left, right)) = equality(terms, *inner, budget)? {
                if left != right {
                    if plan.goals.len() == MAX_GOALS {
                        return None;
                    }
                    budget.push(
                        &mut plan.goals,
                        Goal {
                            node: cursor,
                            equality: *inner,
                            left,
                            right,
                        },
                    )?;
                }
            }
        }
        cursor += 1;
    }
    Some(plan)
}

/// Only an exact original positive Boolean variable can activate this source.
/// No truth assignment, derived guard or merely mentioned variable qualifies.
fn source(
    terms: &TermStore,
    originals: &[TermId],
    root: TermId,
    budget: &mut Budget<'_>,
) -> Option<Source> {
    let direct = Source {
        root,
        body: root,
        activation: None,
    };
    let TermData::App(Symbol::Named(name), args) = terms.get(root) else {
        return Some(direct);
    };
    if name != "or" || args.len() != 2 {
        return Some(direct);
    }
    for position in 0..2 {
        budget.charge(1, 0)?;
        let TermData::Not(guard) = terms.get(args[position]) else {
            continue;
        };
        if terms.sort(args[position]) != &Sort::Bool
            || terms.sort(args[1 - position]) != &Sort::Bool
            || terms.sort(*guard) != &Sort::Bool
            || !matches!(terms.get(*guard), TermData::Var(_, _))
        {
            continue;
        }
        for &original in originals {
            budget.charge(1, 0)?;
            if original == *guard {
                return Some(Source {
                    root,
                    body: args[1 - position],
                    activation: Some(*guard),
                });
            }
        }
    }
    Some(direct)
}

/// `None` is malformed metadata; `Some(None)` is an unsupported leaf. Arrays,
/// Boolean equality and arithmetic theories do not enter this BV-only graph.
fn equality(
    terms: &TermStore,
    term: TermId,
    budget: &mut Budget<'_>,
) -> Option<Option<(TermId, TermId)>> {
    let TermData::App(Symbol::Named(name), args) = terms.get(term) else {
        return Some(None);
    };
    if name != "=" || args.len() != 2 {
        return Some(None);
    }
    // Prepay this fresh structural comparison too, including rejected array
    // leaves. Source admission is not a reusable allowance for later scans.
    admit_sort(terms.sort(args[0]), 0, budget)?;
    admit_sort(terms.sort(args[1]), 0, budget)?;
    if terms.sort(term) != &Sort::Bool || terms.sort(args[0]) != terms.sort(args[1]) {
        return None;
    }
    let Some(width) = terms.sort(args[0]).bitvec_width() else {
        return Some(None);
    };
    if width == 0 || width > crate::api::MAX_API_BITVECTOR_WIDTH {
        return None;
    }
    Some(Some((args[0], args[1])))
}

#[derive(Clone, Copy)]
struct Vertex {
    term: TermId,
    parent: Option<(usize, usize)>,
}

/// `Some(None)` means no path; outer `None` preserves resource refusal rather
/// than retrying another goal with a fresh allowance. Visited vertices make
/// the selected path simple, including with reversed/duplicate source edges.
pub(super) fn equality_path(
    edges: &[Edge],
    goal: &Goal,
    budget: &mut Budget<'_>,
) -> Option<Option<Vec<usize>>> {
    let mut vertices = Vec::new();
    budget.push(
        &mut vertices,
        Vertex {
            term: goal.left,
            parent: None,
        },
    )?;
    let mut cursor = 0usize;
    let mut found = None;
    while cursor < vertices.len() && found.is_none() {
        let current = vertices[cursor].term;
        for (edge_index, edge) in edges.iter().enumerate() {
            budget.charge(1, 0)?;
            let next = if edge.left == current {
                edge.right
            } else if edge.right == current {
                edge.left
            } else {
                continue;
            };
            let mut visited = false;
            for vertex in &vertices {
                budget.charge(1, 0)?;
                if vertex.term == next {
                    visited = true;
                    break;
                }
            }
            if visited {
                continue;
            }
            let index = vertices.len();
            budget.push(
                &mut vertices,
                Vertex {
                    term: next,
                    parent: Some((cursor, edge_index)),
                },
            )?;
            if next == goal.right {
                found = Some(index);
                break;
            }
        }
        cursor += 1;
    }
    let Some(mut current) = found else {
        return Some(None);
    };
    let mut path = Vec::new();
    while let Some((parent, edge)) = vertices.get(current)?.parent {
        budget.push(&mut path, edge)?;
        current = parent;
    }
    budget.charge(path.len(), 0)?;
    path.reverse();
    Some(Some(path))
}
