// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The implication graph of a leaf's binary clauses and its strongly
//! connected components: the classes of literals the leaf's values make
//! equal (`leaf.rs`).

use super::super::*;

/// The binary clauses' implications between open literals.
#[derive(Default)]
pub(super) struct Implications {
    pub(super) node: DetHashMap<Literal, u32>,
    pub(super) lits: Vec<Literal>,
    /// Edges out of each node: (target, pool clause).
    out: Vec<Vec<(u32, usize)>>,
    /// Edges into each node: (source, pool clause).
    pub(super) into: Vec<Vec<(u32, usize)>>,
}

/// Each node's strongly connected component.
pub(super) struct Components {
    pub(super) of: Vec<usize>,
    pub(super) count: usize,
}

impl Implications {
    fn node(&mut self, lit: Literal) -> u32 {
        if let Some(&node) = self.node.get(&lit) {
            return node;
        }
        let node = self.lits.len() as u32;
        self.node.insert(lit, node);
        self.lits.push(lit);
        self.out.push(Vec::new());
        self.into.push(Vec::new());
        // The complement is a node too, so every class has one.
        let complement = lit.negated();
        if !self.node.contains_key(&complement) {
            let other = self.lits.len() as u32;
            self.node.insert(complement, other);
            self.lits.push(complement);
            self.out.push(Vec::new());
            self.into.push(Vec::new());
        }
        node
    }

    pub(super) fn edge(&mut self, from: Literal, to: Literal, clause: usize) {
        let from = self.node(from);
        let to = self.node(to);
        self.out[from as usize].push((to, clause));
        self.into[to as usize].push((from, clause));
    }

    /// Tarjan's strongly connected components, iteratively.
    pub(super) fn components(&self) -> Components {
        let count = self.lits.len();
        let unvisited = u32::MAX;
        let mut index = vec![unvisited; count];
        let mut low = vec![0u32; count];
        let mut on_stack = vec![false; count];
        let mut stack: Vec<u32> = Vec::new();
        let mut of = vec![usize::MAX; count];
        let mut components = 0usize;
        let mut next = 0u32;
        for start in 0..count as u32 {
            if index[start as usize] != unvisited {
                continue;
            }
            // (node, next edge to look at)
            let mut frames: Vec<(u32, usize)> = vec![(start, 0)];
            index[start as usize] = next;
            low[start as usize] = next;
            next += 1;
            stack.push(start);
            on_stack[start as usize] = true;
            while let Some(&mut (node, ref mut edge)) = frames.last_mut() {
                if let Some(&(to, _)) = self.out[node as usize].get(*edge) {
                    *edge += 1;
                    if index[to as usize] == unvisited {
                        index[to as usize] = next;
                        low[to as usize] = next;
                        next += 1;
                        stack.push(to);
                        on_stack[to as usize] = true;
                        frames.push((to, 0));
                    } else if on_stack[to as usize] {
                        low[node as usize] = low[node as usize].min(index[to as usize]);
                    }
                    continue;
                }
                frames.pop();
                if let Some(&(parent, _)) = frames.last() {
                    low[parent as usize] = low[parent as usize].min(low[node as usize]);
                }
                if low[node as usize] == index[node as usize] {
                    while let Some(member) = stack.pop() {
                        on_stack[member as usize] = false;
                        of[member as usize] = components;
                        if member == node {
                            break;
                        }
                    }
                    components += 1;
                }
            }
        }
        Components {
            of,
            count: components,
        }
    }
}
