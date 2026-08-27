// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

/// Build the aux-free SR refutation steps from a recognised pigeonhole matrix
/// `M[row][col]` (`P = M.len()` pigeons, `H = M[0].len()` holes, `P = H + 1`).
/// Mirrors the loop structure and witness layout of php-sr.c verbatim. The empty
/// clause is intentionally NOT emitted here — it follows by root unit propagation
/// once the caller has added these units, and the solver emits it.
fn build_php_aux_free_sr(matrix: &[Vec<Variable>]) -> Vec<LexClause> {
    let p = matrix.len(); // P = H + 1 pigeons (rows 0..=H)
    let h = matrix.first().map_or(0, Vec::len); // H holes (cols 0..H-1)
    let mut out: Vec<LexClause> = Vec::new();
    if p < 3 || h < 2 || p < h + 1 {
        return out; // see detect_php_matrix: P >= H + 1, untruncated
    }

    for hole in 0..h - 1 {
        // SR units (¬x_{p,h}) for p = P-1 down to hole+1, each witnessed by the
        // pigeon-swap (pigeon p-1 ↔ pigeon p) over holes j > hole.
        for pig in ((hole + 1)..=(p - 1)).rev() {
            let v1 = matrix[pig][hole];
            let v2 = matrix[pig - 1][hole];
            let clause = vec![Literal::negative(v1)];
            // Witness token stream: [pivot, PR-assignment…, pivot(separator),
            // substitution pairs…]. The PR part puts pigeon p-1 into hole h; the
            // substitution swaps pigeons p-1 and p in every later hole.
            let mut witness = vec![
                Literal::negative(v1), // 2nd pivot occurrence: opens the PR part
                Literal::positive(v2), // PR assignment x_{p-1,h} = 1
                Literal::negative(v1), // 3rd pivot occurrence: separator
            ];
            for (&v3, &v4) in matrix[pig - 1][(hole + 1)..h]
                .iter()
                .zip(&matrix[pig][(hole + 1)..h])
            {
                // σ(v3) = v4, σ(v4) = v3 (swap the two pigeons in hole j).
                witness.push(Literal::positive(v3));
                witness.push(Literal::positive(v4));
                witness.push(Literal::positive(v4));
                witness.push(Literal::positive(v3));
            }
            out.push(LexClause::Sr { clause, witness });
        }

        // RAT unit (x_{h,h}): pigeon `hole` occupies hole `hole`.
        let diag = matrix[hole][hole];
        out.push(LexClause::Sr {
            clause: vec![Literal::positive(diag)],
            witness: vec![Literal::positive(diag)],
        });

        // RAT units (¬x_{h,j}) for j > hole: pigeon `hole` is in no later hole.
        for &v in &matrix[hole][(hole + 1)..h] {
            out.push(LexClause::Sr {
                clause: vec![Literal::negative(v)],
                witness: vec![Literal::negative(v)],
            });
        }
    }
    out
}

/// Aux-free SR refutation for the r-uniform K_n perfect-matching family
/// (`count_p2` = edges, `count_p3` = triples, …; task #17/#4). Same contract
/// as [`detect_php_aux_free_sr`]: `None` when the formula is not a pure
/// r-uniform matching incidence with `n % r != 0`. The exact structural gate
/// is part of the soundness boundary because this route also runs without a
/// proof surface; when it returns `Some`, every step is SR-redundant by
/// construction.
///
/// The structure: `n` all-positive "exactly-one" group clauses (one group per
/// point of the complete r-uniform hypergraph K_n^(r), one variable per
/// incident r-set) of uniform width `C(n-1, r-1)`, every variable in exactly
/// `r` groups (its r-set — distinct across variables, `C(n,r)` in total), and
/// the within-group AMO binaries as an exact MULTISET: one copy per shared
/// group, i.e. a pair of r-sets sharing `s` points appears `s` times
/// (`count_p3` emits exactly that; at `r = 2` this degenerates to the old
/// no-duplicate rule). Then every point permutation is a formula
/// automorphism, and for `n` not divisible by `r` the formula (a perfect
/// r-matching on K_n^(r)) is UNSAT by counting; `n % r == 0` is SAT-shaped
/// and skipped.
///
/// The derivation generalizes the validated `r = 2` chain (php-sr.c shape,
/// NOT the lex-leader tower whose per-generator σ-witness cannot preserve
/// earlier generators' towers — measured): with `alive` the unmatched points
/// ascending and `P` the `r` lowest, derive for every other (r-1)-subset `A`
/// of `alive ∖ {v}` (descending) the SR unit `¬x_{{v}∪A}` (witness:
/// `x_{{v}∪A}=0`, `x_P=1`, substitution = the involution pairing
/// `sorted(P∖({v}∪A))` with `sorted(A∖P)` acting on the alive r-sets not
/// containing `v`, each 2-cycle listed once), then the RAT unit `x_P`;
/// recurse on `alive ∖ P`. The last point's group clause is falsified by
/// root unit propagation, which closes the proof. Validated externally
/// before this port: the r-parametric generator reproduces the r=2 K_9 chain
/// and gives `dsr-trim` `s VERIFIED UNSAT` on `count_p3_M19` and the whole
/// `count_p2` corpus family (K_21..K_45).
pub(crate) fn detect_matching_aux_free_sr(clauses: &[Vec<Literal>]) -> Option<Vec<LexClause>> {
    let (n, r, svar) = detect_rmatching_incidence(clauses)?;
    build_rmatching_aux_free_sr(n, r, &svar)
}

/// `C(n, k)` while it stays far below any plausible variable count; `None`
/// on overflow so a spoofed shape cannot wrap the arithmetic.
fn binom(n: usize, k: usize) -> Option<usize> {
    if k > n {
        return None;
    }
    let k = k.min(n - k);
    let mut acc: u128 = 1;
    for i in 0..k {
        acc = acc.checked_mul((n - i) as u128)? / (i as u128 + 1);
        if acc > u128::from(u32::MAX) {
            return None;
        }
    }
    usize::try_from(acc).ok()
}

/// Visit the `k`-combinations of `pool` (kept in `pool`'s order) in
/// lexicographic position order.
fn for_each_combination(pool: &[usize], k: usize, f: &mut impl FnMut(&[usize])) {
    if k == 0 || k > pool.len() {
        return;
    }
    let mut idx: Vec<usize> = (0..k).collect();
    let mut buf: Vec<usize> = vec![0; k];
    loop {
        for (slot, &i) in buf.iter_mut().zip(idx.iter()) {
            *slot = pool[i];
        }
        f(&buf);
        let mut i = k;
        loop {
            if i == 0 {
                return;
            }
            i -= 1;
            if idx[i] != pool.len() - k + i {
                break;
            }
            if i == 0 {
                return;
            }
        }
        idx[i] += 1;
        for j in (i + 1)..k {
            idx[j] = idx[j - 1] + 1;
        }
    }
}

/// Recognise the r-uniform matching incidence (see
/// [`detect_matching_aux_free_sr`]) and return `(n, r, svar)` with `svar`
/// mapping each ascending r-set of group indices to its variable.
fn detect_rmatching_incidence(
    clauses: &[Vec<Literal>],
) -> Option<(usize, usize, BTreeMap<Vec<usize>, Variable>)> {
    // Cheap shape pre-filter, same reasoning as `detect_php_aux_free_sr`'s.
    if !clauses.iter().all(|c| {
        (c.len() >= 4 && c.iter().all(|l| l.is_positive()))
            || (c.len() == 2 && c.iter().all(|l| !l.is_positive()))
    }) {
        return None;
    }
    let groups: Vec<&Vec<Literal>> = clauses.iter().filter(|c| c.len() >= 4).collect();
    let n = groups.len();
    if n < 3 {
        return None;
    }
    // Occurrence signatures: every variable in exactly r distinct groups.
    let mut owner: BTreeMap<Variable, Vec<usize>> = BTreeMap::new();
    for (i, g) in groups.iter().enumerate() {
        for l in g.iter() {
            let sig = owner.entry(l.variable()).or_default();
            if sig.last() == Some(&i) {
                return None; // twice in one group
            }
            sig.push(i);
        }
    }
    let r = owner.values().next()?.len();
    if r < 2 || r >= n || owner.values().any(|sig| sig.len() != r) {
        return None;
    }
    // n divisible by r admits a perfect matching: SAT-shaped, skip (the WLOG
    // units would still be SR — the old odd-n rule is this test at r = 2).
    if n.is_multiple_of(r) {
        return None;
    }
    if binom(n, r)? != owner.len() {
        return None;
    }
    let width = binom(n - 1, r - 1)?;
    if groups.iter().any(|g| g.len() != width) {
        return None;
    }
    // Distinct signatures: with C(n,r) variables this makes `svar` total over
    // the r-subsets, which the chain construction relies on.
    let mut svar: BTreeMap<Vec<usize>, Variable> = BTreeMap::new();
    for (&var, sig) in &owner {
        if svar.insert(sig.clone(), var).is_some() {
            return None;
        }
    }
    // The binaries must be the within-group AMOs as an exact MULTISET: one
    // copy per shared group. A count-only or set-only test is insufficient —
    // copies of one valid AMO could stand in for missing ones (the r = 2
    // lesson), and at r >= 3 legitimate pairs genuinely repeat.
    let binaries: Vec<&Vec<Literal>> = clauses.iter().filter(|c| c.len() == 2).collect();
    if binaries.len() != n * (width * (width - 1) / 2) {
        return None;
    }
    let ordered_pair = |x: Variable, y: Variable| if x < y { (x, y) } else { (y, x) };
    let mut balance: BTreeMap<(Variable, Variable), u32> = BTreeMap::new();
    for group in &groups {
        for a in 0..group.len() {
            for b in (a + 1)..group.len() {
                *balance
                    .entry(ordered_pair(group[a].variable(), group[b].variable()))
                    .or_insert(0) += 1;
            }
        }
    }
    for binary in &binaries {
        let (x, y) = (binary[0].variable(), binary[1].variable());
        if x == y {
            return None;
        }
        let slot = balance.get_mut(&ordered_pair(x, y))?;
        *slot = slot.checked_sub(1)?;
    }
    // Total decrements equal total increments and none went negative, so
    // every multiplicity balanced to exactly zero.
    Some((n, r, svar))
}

/// Build the r-uniform WLOG chain (see [`detect_matching_aux_free_sr`]).
/// `svar` is total over the ascending r-subsets of `0..n` by the detection
/// counting argument; lookups still fail closed rather than panic.
fn build_rmatching_aux_free_sr(
    n: usize,
    r: usize,
    svar: &BTreeMap<Vec<usize>, Variable>,
) -> Option<Vec<LexClause>> {
    use std::collections::BTreeSet;

    let mut out: Vec<LexClause> = Vec::new();
    let mut alive: Vec<usize> = (0..n).collect();
    while alive.len() >= r {
        // Fix the r lowest alive points as one part: P = {v} ∪ pref.
        let pref: Vec<usize> = alive[1..r].to_vec();
        let x_p = Literal::positive(*svar.get(&alive[..r])?);
        let rest: Vec<usize> = alive[1..].to_vec();
        let mut cands: Vec<Vec<usize>> = Vec::new();
        for_each_combination(&rest, r - 1, &mut |a| {
            if a != pref.as_slice() {
                cands.push(a.to_vec());
            }
        });
        for a in cands.iter().rev() {
            // Unit ¬x_{{v}∪A}; v = alive[0] is the smallest alive point.
            let mut t = Vec::with_capacity(r);
            t.push(alive[0]);
            t.extend_from_slice(a);
            let piv = Literal::negative(*svar.get(&t)?);
            let mut witness = vec![
                piv, // 2nd pivot: opens the PR part
                x_p, // PR assignment x_P = 1
                piv, // 3rd pivot: separator
            ];
            // Involution π pairing sorted(pref ∖ A) with sorted(A ∖ pref).
            let pi: BTreeMap<usize, usize> = pref
                .iter()
                .filter(|p| !a.contains(p))
                .zip(a.iter().filter(|q| !pref.contains(q)))
                .flat_map(|(&c1, &c2)| [(c1, c2), (c2, c1)])
                .collect();
            // Induced action on the alive r-sets not containing v; each
            // 2-cycle listed once, at its lexicographically first member.
            let mut seen: BTreeSet<Vec<usize>> = BTreeSet::new();
            let mut broken = false;
            for_each_combination(&rest, r, &mut |s| {
                if broken || seen.contains(s) {
                    return;
                }
                let mut img: Vec<usize> = s.iter().map(|m| *pi.get(m).unwrap_or(m)).collect();
                img.sort_unstable();
                if img.as_slice() == s {
                    return;
                }
                match (svar.get(s), svar.get(&img)) {
                    (Some(&va), Some(&vb)) => {
                        witness.push(Literal::positive(va));
                        witness.push(Literal::positive(vb));
                        witness.push(Literal::positive(vb));
                        witness.push(Literal::positive(va));
                        seen.insert(s.to_vec());
                        seen.insert(img);
                    }
                    _ => broken = true,
                }
            });
            if broken {
                return None;
            }
            out.push(LexClause::Sr {
                clause: vec![piv],
                witness,
            });
        }
        // RAT unit x_P: v matches its preferred part (RUP from v's group
        // clause plus the units just derived).
        out.push(LexClause::Sr {
            clause: vec![x_p],
            witness: vec![x_p],
        });
        alive.drain(..r);
    }
    Some(out)
}
