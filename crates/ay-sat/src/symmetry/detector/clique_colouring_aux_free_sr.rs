// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

/// Aux-free SR refutation for the clique-plus-colouring family
/// (`clqcl_n_k_c`, `c = k - 1`, task #17). Same contract as
/// [`detect_php_aux_free_sr`]: `None` unless the formula is EXACTLY this
/// shape; the strict recognizer (exact family counts, membership and
/// consistency checks throughout) is the soundness boundary when no proof is
/// requested, and a mis-detection can only produce a certificate the external
/// checker rejects, never a false VERIFIED.
///
/// The variables, recovered permutation-robustly:
///   * `q[i][v]`: clique position `i` (of `k` all-positive width-`n` rows)
///     hosts vertex `v` — the `n` vertex classes are the components of the
///     cross-row all-negative qq binaries (complete `k`-cliques, one variable
///     per position row);
///   * `x[r][j]`: the vertex of x-row `r` (of `n` all-positive width-`c`
///     rows) has colour `j` — the `c` colour classes are the components of
///     the negative-ternary co-occurrence graph;
///   * `e_{u,v}`: one edge variable per unordered vertex pair, tied to its
///     vertex pair by the mixed ternaries `¬q ∨ ¬q ∨ e` and to its x-row pair
///     by the negative ternaries `¬e ∨ ¬x ∨ ¬x`; intersecting the incident
///     edges' x-row pairs gives the vertex ↔ x-row bijection.
///
/// The chain (externally validated before this port: 196 steps for
/// `clqcl_25_7_6`, 228 for `clqcl_25_8_7`, both `dsr-trim` `s VERIFIED
/// UNSAT`): Phase Q fixes position `i` := vertex `i` with vertex-transposition
/// witnesses applied to ALL THREE variable groups (q rows, colour-aligned x
/// rows, e edges), then RUPs the diagonal; the clique edge units `e_{i,j}`
/// follow by RUP; Phase X fixes clique vertex `t` := colour `t` with colour
/// transpositions on every vertex's x variables. The last clique vertex's
/// colour ALO then dies by root unit propagation, which closes the proof (the
/// solver emits the empty clause; it is not a returned step).
pub(crate) fn detect_clique_colouring_aux_free_sr(
    clauses: &[Vec<Literal>],
) -> Option<Vec<LexClause>> {
    let shape = detect_clique_colouring_shape(clauses)?;
    Some(build_clique_colouring_chain(&shape))
}

/// The recognised clique-colouring structure (see
/// [`detect_clique_colouring_aux_free_sr`]). Vertex, colour and x-row indices
/// are 0-based recognition labels; `edge`'s diagonal is an unused placeholder.
struct CliqueColouringShape {
    k: usize,
    c: usize,
    n: usize,
    q: Vec<Vec<Variable>>,      // k x n: [position][vertex]
    x: Vec<Vec<Variable>>,      // n x c: [x-row][colour]
    xrow_of_vert: Vec<usize>,   // vertex -> x-row (a bijection)
    edge: Vec<Vec<Variable>>,   // n x n: [vertex][vertex]
}

/// Recognise the clique-colouring shape or return `None`.
fn detect_clique_colouring_shape(clauses: &[Vec<Literal>]) -> Option<CliqueColouringShape> {
    use std::collections::{BTreeMap, BTreeSet};

    // Partition; anything outside the four clause families disqualifies.
    let mut pos: Vec<&Vec<Literal>> = Vec::new();
    let mut negb: Vec<(Variable, Variable)> = Vec::new();
    let mut mixed3: Vec<&Vec<Literal>> = Vec::new();
    let mut neg3: Vec<&Vec<Literal>> = Vec::new();
    for cl in clauses {
        let npos = cl.iter().filter(|l| l.is_positive()).count();
        match (cl.len(), npos) {
            (0 | 1, _) => return None,
            (2, 0) => negb.push((cl[0].variable(), cl[1].variable())),
            (3, 1) => mixed3.push(cl),
            (3, 0) => neg3.push(cl),
            (len, np) if np == len => pos.push(cl),
            _ => return None,
        }
    }
    // Exactly two all-positive widths: c (colour rows) < n (position rows).
    let widths: BTreeSet<usize> = pos.iter().map(|cl| cl.len()).collect();
    if widths.len() != 2 {
        return None;
    }
    let mut width_it = widths.into_iter();
    let (c, n) = (width_it.next()?, width_it.next()?);
    let qrows: Vec<&Vec<Literal>> = pos.iter().filter(|r| r.len() == n).copied().collect();
    let xrows: Vec<&Vec<Literal>> = pos.iter().filter(|r| r.len() == c).copied().collect();
    let k = qrows.len();
    if k != c + 1 || xrows.len() != n || n < k {
        return None;
    }
    // Each variable in at most one row, and never in both row kinds.
    let mut qrow_of: BTreeMap<Variable, usize> = BTreeMap::new();
    for (i, r) in qrows.iter().enumerate() {
        for l in r.iter() {
            if qrow_of.insert(l.variable(), i).is_some() {
                return None;
            }
        }
    }
    let mut xrow_of: BTreeMap<Variable, usize> = BTreeMap::new();
    for (i, r) in xrows.iter().enumerate() {
        for l in r.iter() {
            if qrow_of.contains_key(&l.variable()) || xrow_of.insert(l.variable(), i).is_some() {
                return None;
            }
        }
    }
    // Everything else is an edge variable: exactly C(n,2) of them.
    let mut evars: BTreeSet<Variable> = BTreeSet::new();
    for cl in clauses {
        for l in cl.iter() {
            let v = l.variable();
            if !qrow_of.contains_key(&v) && !xrow_of.contains_key(&v) {
                evars.insert(v);
            }
        }
    }
    if evars.len() != n * (n - 1) / 2 {
        return None;
    }
    let (vert_of, q) = cc_vertex_classes(&negb, &qrow_of, &xrow_of, n, k, c)?;
    let (evc, edge) = cc_edge_map(&mixed3, &vert_of, &evars, n, k)?;
    let (exr, x) = cc_colour_map(&neg3, &xrow_of, &evars, n, c)?;
    let xrow_of_vert = cc_vertex_xrows(&evc, &exr, n)?;
    Some(CliqueColouringShape {
        k,
        c,
        n,
        q,
        x,
        xrow_of_vert,
        edge,
    })
}

/// Sort the all-negative binaries into their three AMO families with exact
/// counts and no duplicates, then recover the vertex classes (components of
/// the cross-row qq graph: complete `k`-cliques, one variable per position
/// row) and the `q` matrix.
fn cc_vertex_classes(
    negb: &[(Variable, Variable)],
    qrow_of: &BTreeMap<Variable, usize>,
    xrow_of: &BTreeMap<Variable, usize>,
    n: usize,
    k: usize,
    c: usize,
) -> Option<(BTreeMap<Variable, usize>, Vec<Vec<Variable>>)> {
    use std::collections::{BTreeMap, BTreeSet};

    let mut q_in: BTreeSet<(Variable, Variable)> = BTreeSet::new();
    let mut q_cross: BTreeSet<(Variable, Variable)> = BTreeSet::new();
    let mut x_in: BTreeSet<(Variable, Variable)> = BTreeSet::new();
    let mut adj: BTreeMap<Variable, BTreeSet<Variable>> = BTreeMap::new();
    for &(a, b) in negb {
        if a == b {
            return None;
        }
        let key = if a < b { (a, b) } else { (b, a) };
        let fresh = match (qrow_of.get(&a), qrow_of.get(&b)) {
            (Some(ra), Some(rb)) if ra == rb => q_in.insert(key),
            (Some(_), Some(_)) => {
                adj.entry(a).or_default().insert(b);
                adj.entry(b).or_default().insert(a);
                q_cross.insert(key)
            }
            (None, None) => {
                if xrow_of.get(&a)? != xrow_of.get(&b)? {
                    return None; // xx binaries are within-row colour AMOs only
                }
                x_in.insert(key)
            }
            _ => return None,
        };
        if !fresh {
            return None; // duplicated AMO binary
        }
    }
    if q_in.len() != k * (n * (n - 1) / 2)
        || q_cross.len() != n * (k * (k - 1) / 2)
        || x_in.len() != n * (c * (c - 1) / 2)
    {
        return None;
    }
    let mut vert_of: BTreeMap<Variable, usize> = BTreeMap::new();
    let mut classes: Vec<Vec<Variable>> = Vec::new();
    for &start in qrow_of.keys() {
        if vert_of.contains_key(&start) {
            continue;
        }
        let id = classes.len();
        let mut members: Vec<Variable> = Vec::new();
        let mut stack = vec![start];
        vert_of.insert(start, id);
        while let Some(u) = stack.pop() {
            members.push(u);
            for &w in adj.get(&u).into_iter().flatten() {
                if let std::collections::btree_map::Entry::Vacant(e) = vert_of.entry(w) {
                    e.insert(id);
                    stack.push(w);
                }
            }
        }
        classes.push(members);
    }
    if classes.len() != n {
        return None;
    }
    let mut q: Vec<Vec<Option<Variable>>> = vec![vec![None; n]; k];
    for (cid, members) in classes.iter().enumerate() {
        if members.len() != k {
            return None;
        }
        for &v in members {
            // Degree k-1 makes each class a complete clique (neighbours never
            // leave a component and `adj` deduplicates); the matrix cell
            // rejects two class members on one position row.
            if adj.get(&v).map_or(0, BTreeSet::len) != k - 1
                || q[*qrow_of.get(&v)?][cid].replace(v).is_some()
            {
                return None;
            }
        }
    }
    let q = q
        .into_iter()
        .map(|row| row.into_iter().collect::<Option<Vec<_>>>())
        .collect::<Option<Vec<_>>>()?;
    Some((vert_of, q))
}

/// Recover the edge ↔ vertex-pair bijection from the mixed ternaries
/// `¬q_{i,u} ∨ ¬q_{j,v} ∨ e_{u,v}` (exact count, no duplicates, one
/// consistent vertex pair per edge variable).
fn cc_edge_map(
    mixed3: &[&Vec<Literal>],
    vert_of: &BTreeMap<Variable, usize>,
    evars: &std::collections::BTreeSet<Variable>,
    n: usize,
    k: usize,
) -> Option<(
    BTreeMap<Variable, (usize, usize)>,
    Vec<Vec<Variable>>,
)> {
    use std::collections::{BTreeMap, BTreeSet};

    if mixed3.len() != (k * (k - 1) / 2) * n * (n - 1) {
        return None;
    }
    let mut seen: BTreeSet<[Variable; 3]> = BTreeSet::new();
    let mut evc: BTreeMap<Variable, (usize, usize)> = BTreeMap::new();
    for cl in mixed3 {
        let e = cl.iter().find(|l| l.is_positive())?.variable();
        if !evars.contains(&e) {
            return None;
        }
        let verts: Vec<usize> = cl
            .iter()
            .filter(|l| !l.is_positive())
            .map(|l| vert_of.get(&l.variable()).copied())
            .collect::<Option<Vec<_>>>()?;
        let pair = (verts[0].min(verts[1]), verts[0].max(verts[1]));
        if pair.0 == pair.1 {
            return None;
        }
        let mut key = [cl[0].variable(), cl[1].variable(), cl[2].variable()];
        key.sort_unstable();
        if !seen.insert(key) {
            return None;
        }
        if *evc.entry(e).or_insert(pair) != pair {
            return None;
        }
    }
    if evc.len() != n * (n - 1) / 2 {
        return None;
    }
    // Distinct pairs (two edges sharing a pair collide in the matrix), and
    // C(n,2) distinct pairs fill every off-diagonal cell.
    let mut cells: Vec<Vec<Option<Variable>>> = vec![vec![None; n]; n];
    for (&e, &(a, b)) in &evc {
        if cells[a][b].replace(e).is_some() {
            return None;
        }
        cells[b][a] = Some(e);
    }
    let mut edge: Vec<Vec<Variable>> = vec![vec![Variable(0); n]; n];
    for a in 0..n {
        for b in 0..n {
            if a != b {
                edge[a][b] = cells[a][b]?;
            }
        }
    }
    Some((evc, edge))
}

/// Recover each edge's x-row pair and the colour classes from the negative
/// ternaries `¬e ∨ ¬x_{u,j} ∨ ¬x_{v,j}`, and build the `x` matrix
/// (`[x-row][colour]`, every cell exactly once).
fn cc_colour_map(
    neg3: &[&Vec<Literal>],
    xrow_of: &BTreeMap<Variable, usize>,
    evars: &std::collections::BTreeSet<Variable>,
    n: usize,
    c: usize,
) -> Option<(
    BTreeMap<Variable, (usize, usize)>,
    Vec<Vec<Variable>>,
)> {
    use std::collections::{BTreeMap, BTreeSet};

    if neg3.len() != (n * (n - 1) / 2) * c {
        return None;
    }
    let mut seen: BTreeSet<[Variable; 3]> = BTreeSet::new();
    let mut exr: BTreeMap<Variable, (usize, usize)> = BTreeMap::new();
    let mut col_adj: BTreeMap<Variable, BTreeSet<Variable>> = BTreeMap::new();
    for cl in neg3 {
        let mut e: Option<Variable> = None;
        let mut xs: Vec<Variable> = Vec::new();
        for l in cl.iter() {
            let v = l.variable();
            if evars.contains(&v) {
                if e.replace(v).is_some() {
                    return None;
                }
            } else if xrow_of.contains_key(&v) {
                xs.push(v);
            } else {
                return None;
            }
        }
        let e = e?;
        if xs.len() != 2 {
            return None;
        }
        let (ra, rb) = (*xrow_of.get(&xs[0])?, *xrow_of.get(&xs[1])?);
        if ra == rb {
            return None;
        }
        let pair = (ra.min(rb), ra.max(rb));
        let mut key = [cl[0].variable(), cl[1].variable(), cl[2].variable()];
        key.sort_unstable();
        if !seen.insert(key) {
            return None;
        }
        if *exr.entry(e).or_insert(pair) != pair {
            return None;
        }
        col_adj.entry(xs[0]).or_default().insert(xs[1]);
        col_adj.entry(xs[1]).or_default().insert(xs[0]);
    }
    if exr.len() != n * (n - 1) / 2 {
        return None;
    }
    // Colour classes = components of the co-occurrence graph on x variables.
    let mut col_of: BTreeMap<Variable, usize> = BTreeMap::new();
    let mut ncols = 0usize;
    for &start in xrow_of.keys() {
        if col_of.contains_key(&start) {
            continue;
        }
        let mut stack = vec![start];
        col_of.insert(start, ncols);
        while let Some(u) = stack.pop() {
            for &w in col_adj.get(&u).into_iter().flatten() {
                if let std::collections::btree_map::Entry::Vacant(entry) = col_of.entry(w) {
                    entry.insert(ncols);
                    stack.push(w);
                }
            }
        }
        ncols += 1;
    }
    if ncols != c {
        return None;
    }
    let mut x: Vec<Vec<Option<Variable>>> = vec![vec![None; c]; n];
    for (&v, &row) in xrow_of {
        if x[row][*col_of.get(&v)?].replace(v).is_some() {
            return None;
        }
    }
    let x = x
        .into_iter()
        .map(|row| row.into_iter().collect::<Option<Vec<_>>>())
        .collect::<Option<Vec<_>>>()?;
    Some((exr, x))
}

/// Vertex ↔ x-row correspondence: intersect the incident edges' x-row pairs
/// down to a single row per vertex class, demand a bijection, and re-check
/// every edge's x-row pair against its endpoints.
fn cc_vertex_xrows(
    evc: &BTreeMap<Variable, (usize, usize)>,
    exr: &BTreeMap<Variable, (usize, usize)>,
    n: usize,
) -> Option<Vec<usize>> {
    use std::collections::BTreeSet;

    let mut inc: Vec<Vec<Variable>> = vec![Vec::new(); n];
    for (&e, &(a, b)) in evc {
        inc[a].push(e);
        inc[b].push(e);
    }
    let mut xrow_of_vert: Vec<usize> = Vec::with_capacity(n);
    let mut used: BTreeSet<usize> = BTreeSet::new();
    for members in &inc {
        let mut cands: Option<BTreeSet<usize>> = None;
        for e in members {
            let &(ra, rb) = exr.get(e)?;
            let pair: BTreeSet<usize> = [ra, rb].into_iter().collect();
            cands = Some(match cands {
                None => pair,
                Some(prev) => prev.intersection(&pair).copied().collect(),
            });
        }
        let cands = cands?;
        if cands.len() != 1 {
            return None;
        }
        let row = *cands.first()?;
        if !used.insert(row) {
            return None;
        }
        xrow_of_vert.push(row);
    }
    for (e, &(a, b)) in evc {
        let (ra, rb) = (xrow_of_vert[a], xrow_of_vert[b]);
        if *exr.get(e)? != (ra.min(rb), ra.max(rb)) {
            return None;
        }
    }
    Some(xrow_of_vert)
}

/// Append the 2-cycle `a ↔ b` to a DSR substitution token stream.
fn push_var_swap(witness: &mut Vec<Literal>, a: Variable, b: Variable) {
    witness.push(Literal::positive(a));
    witness.push(Literal::positive(b));
    witness.push(Literal::positive(b));
    witness.push(Literal::positive(a));
}

/// Emit the validated Phase Q / edge units / Phase X chain.
fn build_clique_colouring_chain(shape: &CliqueColouringShape) -> Vec<LexClause> {
    let CliqueColouringShape {
        k,
        c,
        n,
        q,
        x,
        xrow_of_vert,
        edge,
    } = shape;
    let (k, c, n) = (*k, *c, *n);
    let unit = |lit: Literal| LexClause::Sr {
        clause: vec![lit],
        witness: vec![lit],
    };
    let mut out: Vec<LexClause> = Vec::new();
    // Phase Q: position i hosts vertex i; σ = vertex transposition (i v) on
    // the q rows, the colour-aligned x rows AND the incident edges.
    for i in 0..k {
        for v in (i + 1)..n {
            let piv = Literal::negative(q[i][v]);
            let mut witness = vec![piv, Literal::positive(q[i][i]), piv];
            for j in (0..k).filter(|&j| j != i) {
                push_var_swap(&mut witness, q[j][i], q[j][v]);
            }
            let (xi, xv) = (&x[xrow_of_vert[i]], &x[xrow_of_vert[v]]);
            for (&a, &b) in xi.iter().zip(xv.iter()) {
                push_var_swap(&mut witness, a, b);
            }
            for w in (0..n).filter(|&w| w != i && w != v) {
                push_var_swap(&mut witness, edge[i][w], edge[v][w]);
            }
            out.push(LexClause::Sr {
                clause: vec![piv],
                witness,
            });
        }
        out.push(unit(Literal::positive(q[i][i])));
    }
    // The clique's edges are now all forced: plain RUP units.
    for (i, row) in edge.iter().enumerate().take(k) {
        for &e in row.iter().take(k).skip(i + 1) {
            out.push(unit(Literal::positive(e)));
        }
    }
    // Phase X: clique vertex t gets colour t; σ = colour transposition (t j)
    // on every other vertex's x variables.
    for t in 0..c {
        let rt = xrow_of_vert[t];
        for j in (t + 1)..c {
            let piv = Literal::negative(x[rt][j]);
            let mut witness = vec![piv, Literal::positive(x[rt][t]), piv];
            for w in (0..n).filter(|&w| xrow_of_vert[w] != rt) {
                push_var_swap(&mut witness, x[xrow_of_vert[w]][t], x[xrow_of_vert[w]][j]);
            }
            out.push(LexClause::Sr {
                clause: vec![piv],
                witness,
            });
        }
        out.push(unit(Literal::positive(x[rt][t])));
    }
    out
}
