// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

/// Aux-free SR refutation for the relativized pigeonhole family
/// (`rphp_pN_rN`, task #17). Same contract as [`detect_php_aux_free_sr`]:
/// `None` unless the formula is EXACTLY this shape; the strict recognizer
/// (exact family counts, membership and guard checks) is the soundness
/// boundary when no proof is requested, and a mis-detection can only produce
/// a certificate the external checker rejects, never a false VERIFIED.
///
/// The variables, recovered permutation-robustly:
///   * `u[i][j]`: pigeon `i` (row of the `N` all-positive width-`N` ALOs)
///     sits in resource `j` — resource identity is the guard variable `y_j`
///     reached through the `N²` activation binaries `¬u ∨ y`;
///   * `y_j`: resource `j` is active — the `N` distinct negative literals of
///     the mixed width-`N` rows;
///   * `v[j][l]`: resource `j` maps to hole `l` — the positive literals of
///     the guarded rows `¬y_j ∨ v_{j,1..N-1}`; the `N-1` hole classes are the
///     components of the quaternary co-occurrence graph, and every quaternary
///     `¬y ∨ ¬y' ∨ ¬v ∨ ¬v'` must carry EXACTLY the guards of its two v
///     variables' resources.
///
/// Every all-negative binary must pair two `u` of the same resource on
/// different pigeon rows (count `N·C(N,2)`, no duplicates); quaternaries
/// number `C(N,2)·(N-1)`; nothing else may appear.
///
/// The chain (externally validated before this port: 650 steps for
/// `rphp_p25_r25`, `dsr-trim` `s VERIFIED UNSAT`): Phase 1 matches pigeon `i`
/// to resource `i`, each WLOG unit witnessed by the resource transposition
/// `(i s)` applied to the `u` columns AND the `y` pair AND the hole-aligned
/// `v` rows (forgetting the y/v part makes the guarded rows fail), then the
/// RUP diagonal `u[i][i]`; the `N` guard units `y_j` follow by RUP; Phase 2
/// is guarded PHP(N, N-1) on `v` — resource `t` takes hole `t`, with hole
/// transpositions over all other resources' `v` variables. The last
/// resource's guarded ALO then dies by root unit propagation, which closes
/// the proof (the solver emits the empty clause; it is not a returned step).
pub(crate) fn detect_relativized_php_aux_free_sr(
    clauses: &[Vec<Literal>],
) -> Option<Vec<LexClause>> {
    let shape = detect_relativized_php_shape(clauses)?;
    Some(build_relativized_php_chain(&shape))
}

/// The recognised relativized-pigeonhole structure (see
/// [`detect_relativized_php_aux_free_sr`]). Resource `j`'s identity is
/// `y[j]`, the `j`-th guard variable in ascending order.
struct RelativizedPhpShape {
    n: usize,
    u: Vec<Vec<Variable>>, // n x n: [pigeon][resource]
    y: Vec<Variable>,      // n guards, ascending
    v: Vec<Vec<Variable>>, // n x (n-1): [resource][hole]
}

/// Recognise the relativized-pigeonhole shape or return `None`.
fn detect_relativized_php_shape(clauses: &[Vec<Literal>]) -> Option<RelativizedPhpShape> {
    use std::collections::{BTreeMap, BTreeSet};

    // Partition; anything outside the five clause families disqualifies.
    let mut posw: Vec<&Vec<Literal>> = Vec::new();
    let mut mixw: Vec<&Vec<Literal>> = Vec::new();
    let mut mixb: Vec<(Variable, Variable)> = Vec::new(); // (u, y)
    let mut negb: Vec<(Variable, Variable)> = Vec::new();
    let mut neg4: Vec<&Vec<Literal>> = Vec::new();
    for cl in clauses {
        let npos = cl.iter().filter(|l| l.is_positive()).count();
        match (cl.len(), npos) {
            (0 | 1, _) => return None,
            (2, 0) => negb.push((cl[0].variable(), cl[1].variable())),
            (2, 1) => {
                let neg = cl.iter().find(|l| !l.is_positive())?;
                let pos = cl.iter().find(|l| l.is_positive())?;
                mixb.push((neg.variable(), pos.variable()));
            }
            (4, 0) => neg4.push(cl),
            (len, np) if len > 2 && np == len => posw.push(cl),
            (len, np) if len > 2 && np == len - 1 => mixw.push(cl),
            _ => return None,
        }
    }
    let n = posw.first()?.len();
    if posw.len() != n || posw.iter().any(|r| r.len() != n) {
        return None;
    }
    if mixw.len() != n || mixw.iter().any(|r| r.len() != n) {
        return None;
    }
    // Pigeon rows: every u variable in exactly one.
    let mut pigeon_of: BTreeMap<Variable, usize> = BTreeMap::new();
    for (i, r) in posw.iter().enumerate() {
        for l in r.iter() {
            if pigeon_of.insert(l.variable(), i).is_some() {
                return None;
            }
        }
    }
    // Guards: the N distinct negative literals of the guarded rows.
    let mut yset: BTreeSet<Variable> = BTreeSet::new();
    for r in &mixw {
        let guard = r.iter().find(|l| !l.is_positive())?.variable();
        if pigeon_of.contains_key(&guard) || !yset.insert(guard) {
            return None;
        }
    }
    let y: Vec<Variable> = yset.iter().copied().collect();
    let res_idx: BTreeMap<Variable, usize> =
        y.iter().enumerate().map(|(t, &g)| (g, t)).collect();
    // Hole variables: resource = the row's guard; fresh everywhere else.
    let mut v2res: BTreeMap<Variable, usize> = BTreeMap::new();
    for r in &mixw {
        let guard = r.iter().find(|l| !l.is_positive())?.variable();
        let res = *res_idx.get(&guard)?;
        for l in r.iter().filter(|l| l.is_positive()) {
            let var = l.variable();
            if pigeon_of.contains_key(&var)
                || yset.contains(&var)
                || v2res.insert(var, res).is_some()
            {
                return None;
            }
        }
    }
    let ures = rphp_resource_map(&mixb, &pigeon_of, &res_idx, n)?;
    rphp_check_resource_amo(&negb, &pigeon_of, &ures, n)?;
    let mut u: Vec<Vec<Option<Variable>>> = vec![vec![None; n]; n];
    for (&uv, &res) in &ures {
        if u[*pigeon_of.get(&uv)?][res].replace(uv).is_some() {
            return None;
        }
    }
    let u = u
        .into_iter()
        .map(|row| row.into_iter().collect::<Option<Vec<_>>>())
        .collect::<Option<Vec<_>>>()?;
    let v = rphp_hole_matrix(&neg4, &v2res, &y, n)?;
    Some(RelativizedPhpShape { n, u, y, v })
}

/// Activation binaries `¬u ∨ y`: exactly `N²`, each `u` variable exactly
/// once. Returns the u-variable → resource-index map.
fn rphp_resource_map(
    mixb: &[(Variable, Variable)],
    pigeon_of: &BTreeMap<Variable, usize>,
    res_idx: &BTreeMap<Variable, usize>,
    n: usize,
) -> Option<BTreeMap<Variable, usize>> {
    if mixb.len() != n * n {
        return None;
    }
    let mut ures: BTreeMap<Variable, usize> = BTreeMap::new();
    for &(uv, yv) in mixb {
        if !pigeon_of.contains_key(&uv) {
            return None;
        }
        let res = *res_idx.get(&yv)?;
        if ures.insert(uv, res).is_some() {
            return None;
        }
    }
    if ures.len() != n * n {
        return None;
    }
    Some(ures)
}

/// Every all-negative binary pairs two `u` of the SAME resource on DIFFERENT
/// pigeon rows: exactly `N·C(N,2)` distinct pairs (the complete per-resource
/// AMO set, since each resource column has one variable per pigeon).
fn rphp_check_resource_amo(
    negb: &[(Variable, Variable)],
    pigeon_of: &BTreeMap<Variable, usize>,
    ures: &BTreeMap<Variable, usize>,
    n: usize,
) -> Option<()> {
    use std::collections::BTreeSet;

    let mut seen: BTreeSet<(Variable, Variable)> = BTreeSet::new();
    for &(a, b) in negb {
        if a == b
            || ures.get(&a)? != ures.get(&b)?
            || pigeon_of.get(&a)? == pigeon_of.get(&b)?
            || !seen.insert(if a < b { (a, b) } else { (b, a) })
        {
            return None;
        }
    }
    (seen.len() == n * (n * (n - 1) / 2)).then_some(())
}

/// Guarded hole-AMO quaternaries `¬y ∨ ¬y' ∨ ¬v ∨ ¬v'`: exact count
/// `C(N,2)·(N-1)`, no duplicates, guards EXACTLY the two v variables'
/// resources; hole classes are the components of the v co-occurrence graph
/// (`N-1` of them, one variable per resource — enforced by the matrix fill).
fn rphp_hole_matrix(
    neg4: &[&Vec<Literal>],
    v2res: &BTreeMap<Variable, usize>,
    y: &[Variable],
    n: usize,
) -> Option<Vec<Vec<Variable>>> {
    use std::collections::{BTreeMap, BTreeSet};

    if v2res.len() != n * (n - 1) || neg4.len() != (n * (n - 1) / 2) * (n - 1) {
        return None;
    }
    let mut seen: BTreeSet<[Variable; 4]> = BTreeSet::new();
    let mut hadj: BTreeMap<Variable, BTreeSet<Variable>> = BTreeMap::new();
    for cl in neg4 {
        let mut guards: BTreeSet<Variable> = BTreeSet::new();
        let mut vs: Vec<Variable> = Vec::new();
        for l in cl.iter() {
            let var = l.variable();
            if v2res.contains_key(&var) {
                vs.push(var);
            } else {
                guards.insert(var);
            }
        }
        if vs.len() != 2 || guards.len() != 2 {
            return None;
        }
        let (ra, rb) = (*v2res.get(&vs[0])?, *v2res.get(&vs[1])?);
        // The guards must be exactly the two v variables' resources.
        let expected: BTreeSet<Variable> = [*y.get(ra)?, *y.get(rb)?].into_iter().collect();
        if ra == rb || guards != expected {
            return None;
        }
        let mut key = [
            cl[0].variable(),
            cl[1].variable(),
            cl[2].variable(),
            cl[3].variable(),
        ];
        key.sort_unstable();
        if !seen.insert(key) {
            return None;
        }
        hadj.entry(vs[0]).or_default().insert(vs[1]);
        hadj.entry(vs[1]).or_default().insert(vs[0]);
    }
    let mut hole_of: BTreeMap<Variable, usize> = BTreeMap::new();
    let mut nholes = 0usize;
    for &start in v2res.keys() {
        if hole_of.contains_key(&start) {
            continue;
        }
        let mut stack = vec![start];
        hole_of.insert(start, nholes);
        while let Some(a) = stack.pop() {
            for &b in hadj.get(&a).into_iter().flatten() {
                if let std::collections::btree_map::Entry::Vacant(e) = hole_of.entry(b) {
                    e.insert(nholes);
                    stack.push(b);
                }
            }
        }
        nholes += 1;
    }
    if nholes != n - 1 {
        return None;
    }
    let mut v: Vec<Vec<Option<Variable>>> = vec![vec![None; n - 1]; n];
    for (&vv, &res) in v2res {
        if v[res][*hole_of.get(&vv)?].replace(vv).is_some() {
            return None;
        }
    }
    v.into_iter()
        .map(|row| row.into_iter().collect::<Option<Vec<_>>>())
        .collect::<Option<Vec<_>>>()
}

/// Emit the validated Phase 1 / guard units / Phase 2 chain.
fn build_relativized_php_chain(shape: &RelativizedPhpShape) -> Vec<LexClause> {
    let RelativizedPhpShape { n, u, y, v } = shape;
    let n = *n;
    let unit = |lit: Literal| LexClause::Sr {
        clause: vec![lit],
        witness: vec![lit],
    };
    let mut out: Vec<LexClause> = Vec::new();
    // Phase 1: pigeon i takes resource i; σ = resource transposition (i s)
    // on the u columns, the y pair and the hole-aligned v rows.
    for i in 0..n {
        for s in (i + 1)..n {
            let piv = Literal::negative(u[i][s]);
            let mut witness = vec![piv, Literal::positive(u[i][i]), piv];
            for row in u.iter().enumerate().filter(|&(m, _)| m != i) {
                push_var_swap(&mut witness, row.1[i], row.1[s]);
            }
            push_var_swap(&mut witness, y[i], y[s]);
            for (&a, &b) in v[i].iter().zip(v[s].iter()) {
                push_var_swap(&mut witness, a, b);
            }
            out.push(LexClause::Sr {
                clause: vec![piv],
                witness,
            });
        }
        out.push(unit(Literal::positive(u[i][i])));
    }
    // Every resource now hosts a pigeon: the guards are forced by RUP.
    for &guard in y.iter() {
        out.push(unit(Literal::positive(guard)));
    }
    // Phase 2: guarded PHP(N, N-1) — resource t takes hole t; σ = hole
    // transposition (t h) on every other resource's v variables.
    for t in 0..(n - 1) {
        for h in (t + 1)..(n - 1) {
            let piv = Literal::negative(v[t][h]);
            let mut witness = vec![piv, Literal::positive(v[t][t]), piv];
            for row in v.iter().enumerate().filter(|&(r, _)| r != t) {
                push_var_swap(&mut witness, row.1[t], row.1[h]);
            }
            out.push(LexClause::Sr {
                clause: vec![piv],
                witness,
            });
        }
        out.push(unit(Literal::positive(v[t][t])));
    }
    out
}
