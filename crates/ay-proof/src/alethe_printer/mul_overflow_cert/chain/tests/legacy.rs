// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

#![cfg(test)]

//! The previous linear-membership algorithm, retained only as a test oracle.

use super::*;

pub(super) fn covered_state(
    p: &Proof<'_>,
    reach: &[&Vec<bool>],
    chosen: &[Vec<(usize, bool)>],
    s: &[bool],
) -> Option<bool> {
    for r in reach {
        p.observe()?;
        if r.as_slice() == s {
            return Some(true);
        }
    }
    for c in chosen {
        p.observe()?;
        if c.iter().all(|&(j, v)| s[j] != v) {
            return Some(true);
        }
    }
    Some(false)
}

pub(super) fn invariant(
    p: &mut Proof<'_>,
    atoms: &[T],
    reach: &HashSet<Vec<bool>>,
    prem: &[Prem],
    decide: &[T],
) -> Option<Vec<S>> {
    p.observe()?;
    let k = atoms.len();
    if k > MAX_STATE {
        return None;
    }
    let reach: Vec<&Vec<bool>> = reach.iter().collect();
    let mut chosen: Vec<Vec<(usize, bool)>> = Vec::new();
    for size in 1..=2usize {
        for c in small_clauses(k, size) {
            p.observe()?;
            if chosen.iter().any(|x| x.iter().all(|l| c.contains(l))) {
                continue;
            }
            if valid_clause(p, &reach, &c)? {
                chosen.push(c);
            }
        }
    }
    for st in 0u64..(1u64 << k) {
        let s: Vec<bool> = (0..k).map(|j| (st >> j) & 1 == 1).collect();
        p.observe()?;
        if covered_state(p, &reach, &chosen, &s)? {
            continue;
        }
        let mut c: Vec<(usize, bool)> = (0..k).map(|j| (j, !s[j])).collect();
        let mut shrunk = true;
        while shrunk {
            p.observe()?;
            shrunk = false;
            for x in 0..c.len() {
                p.observe()?;
                let mut c2 = c.clone();
                c2.remove(x);
                if !c2.is_empty() && valid_clause(p, &reach, &c2)? {
                    c = c2;
                    shrunk = true;
                    break;
                }
            }
        }
        chosen.push(c);
    }
    let mut out = Vec::new();
    for c in chosen {
        p.observe()?;
        let lits: Vec<T> = c
            .iter()
            .map(|&(j, v)| if v { atoms[j] } else { p.t.not(atoms[j]) })
            .collect();
        out.push(p.derive(&lits, prem, decide)?);
    }
    Some(out)
}
