// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! OPT-LIN optimality certificates for the `ihalainen/PBO-clique-coloring`
//! family — the family that was pinned as PERMANENTLY UNCERTIFIABLE because its
//! LP relaxation optimum is exactly `0` against optima of `n - t`.
//!
//! # Why an LP-dual floor can never certify this family, and why that is not the end
//!
//! `040f9f41d` established, in exact rational arithmetic, that these instances
//! have `LP* = 0`. That is correct and this module does not touch it. It is also
//! true — and measured, on 209,314 rows at `n=7,t=3` and 447,828 at `n=8,t=3`,
//! with an exact orbit-averaged rational witness — that the FULL canonical
//! level-1 RLT lift is *still* exactly `0`. So the obvious repair (lift into
//! product space, take the dual there) is dead too. Do not build a general RLT
//! loop; it has been measured and it lifts nothing.
//!
//! What was over-read is the sentence after the negative. "No LP-dual floor can
//! fire" does not imply "this cannot be certified", because a dual floor is not
//! the only certificate VeriPB accepts. Cutting planes has SATURATION and
//! DIVISION, and neither has an LP dual. The bound that works needs the product
//! atoms `p[i][j][k] = M[i][j] * C[i][k]` plus a per-colour at-most-one over
//! them; in the LP that at-most-one is only valid after an optimum-preserving
//! symmetry break (an explicit feasible point, `two_in_a_slot` in the tests,
//! violates zero of the instance's rows but would be cut by it), whereas in the
//! PROOF SYSTEM no symmetry break is needed at all. Every place the LP would
//! need the products' 0/1-ness, the proof spends one `s` or one `2 d`. The proof
//! needs strictly LESS than the LP does.
//!
//! # The mathematics, in one paragraph
//!
//! Each occupied slot holds a vertex; vertices in DISTINCT slots are forced
//! adjacent by the edge rows, hence differently coloured by the proper-colouring
//! rows. So occupied slots inject into colours, at most `t` slots are occupied,
//! and at least `n - t` are paid for. The proof makes that injection explicit:
//! `z[j][k]` reifies "slot `j` holds a colour-`k` vertex", `o[j] + Σ_k z[j][k] >= 1`
//! says an unpaid slot holds something, and a prefix-OR ladder over the pairwise
//! conflicts turns them into `Σ_j z[j][k] <= 1`. Adding the `n` slot rows to the
//! `t` at-most-one rows gives `Σ_j o[j] >= n - t` with UNIT multipliers.
//!
//! Pairwise conflicts alone are worth exactly nothing (`z = 1/2` everywhere);
//! the LADDER, which needs saturation, is the whole content.
//!
//! # Fail-closed, in four independent layers
//!
//! A certificate the checker accepts that does NOT establish the bound is the
//! worst defect this repository can ship — a wrong answer wearing a proof — so
//! nothing is emitted until all four layers pass:
//!
//! 1. **O(1) pre-gate** ([`header_candidate`]). Two header integers decide
//!    membership before any constraint is touched. Off-family instances pay a
//!    handful of integer operations and nothing else.
//! 2. **Exact structural match** ([`super::super::super::optimize::clique_coloring::detect_shape`]).
//!    The instance's constraint multiset must equal the canonical family for the
//!    recovered `(n, t)` EXACTLY — none missing, none extra. This is the same
//!    recognizer the solver's optimum shortcut uses, deliberately shared so the
//!    certifier and the answer can never disagree about what the instance is.
//! 3. **Independent incumbent re-verification.** The passed incumbent must be
//!    feasible against the ORIGINAL rows and evaluate to exactly `n - t`, and the
//!    solver's reported optimum must agree with the structural prediction.
//! 4. **Self-check of the emitted BYTES** ([`self_check`]). The finished proof
//!    text is PARSED BACK and replayed through an independent cutting-planes
//!    interpreter with VeriPB's normalized-literal semantics for `s`, `d` and
//!    `w`. The replay re-derives every row from scratch, so an id desync, a
//!    mis-ordered operand or a wrong multiplier cannot survive. It then requires
//!    (a) every `red` to be a definitional clause of a well-founded extension
//!    that this checker extracts from the proof itself, (b) the penultimate row
//!    to be EXACTLY `Σ_j o[j] >= n - t` over exactly the objective variables, and
//!    (c) the final row to be the empty contradiction.
//!
//! Layers 2 and 4(a,b) together are a complete soundness argument that does not
//! trust the emitter: the `red` steps only ever introduce fresh variables as
//! explicit Boolean functions of already-known ones, so they are conservative
//! over the original variables; every other step is a checked cutting-planes
//! inference; and the row they reach mentions no fresh variable. Hence
//! `Σ_j o[j] >= n - t` is entailed by the instance alone.
//!
//! SOUNDNESS: this module returns proof *text* only, and it is not trusted until
//! the external PINNED VeriPB re-checks it (verify-before-claim). A `None` is a
//! withheld certificate and never changes the reported status.

use std::collections::BTreeMap;
use std::fmt::Write as _;

use crate::optimize::clique_coloring::{detect_shape, CliqueColoringShape};
use crate::types::{PbInstance, PbRel};

use super::super::steps::{ConstraintId, ProofStep};
use super::super::veripb::{veripb_input_constraint_count, VeriPbWriter};
use super::cp_replay::{eval_pol, parse_lit, parse_terms, CpRow};
use super::{evaluate_linear_objective, format_assignment};

// ---------------------------------------------------------------------------
// Layer 1: the O(1) pre-gate.
// ---------------------------------------------------------------------------

/// The `(n, t)` consistent with a header's two counts, or `None`.
///
/// The family's shape fixes both counts exactly:
///
/// ```text
/// #variable   = n^2 + n + n*t + C(n,2)
/// #constraint = 3n + C(n,2)*n*(n-1) + C(n,2)*t
/// ```
///
/// The search over `n` is bounded TWICE: by `n^2 + n <= nvar` and, much more
/// tightly, by `C(n,2)*n*(n-1) <= ncon`, which is `~n^4/2`. The second bound is
/// what makes this O(1) in practice — a 1,000,000-row instance admits `n <= 38`,
/// so the loop is a few dozen integer operations regardless of instance size.
/// Dropping a candidate by the second bound loses nothing: the count identity
/// needs `t >= 1`, so any real member satisfies `C(n,2)*n*(n-1) < ncon` strictly.
///
/// Measured over the 1,124-file / 11 GiB PB25 selected corpus: 10 accepted,
/// 1,114 rejected, zero false accepts.
fn header_candidate(nvar: u64, ncon: u64) -> Option<(usize, usize)> {
    let mut n: u64 = 2;
    loop {
        let square = n.checked_mul(n)?.checked_add(n)?;
        if square > nvar {
            return None;
        }
        let c2 = n.checked_mul(n - 1)? / 2;
        // `~n^4/2` bound: a genuine member has t >= 1, hence strict inequality.
        let forcing = c2.checked_mul(n.checked_mul(n - 1)?)?;
        if forcing > ncon {
            return None;
        }
        let fixed = square.checked_add(c2)?;
        if let Some(rest) = nvar.checked_sub(fixed) {
            if rest % n == 0 {
                let t = rest / n;
                if t >= 1 {
                    let expect = 3u64
                        .checked_mul(n)?
                        .checked_add(forcing)?
                        .checked_add(c2.checked_mul(t)?)?;
                    if expect == ncon {
                        return Some((usize::try_from(n).ok()?, usize::try_from(t).ok()?));
                    }
                }
            }
        }
        n += 1;
    }
}

/// How a fresh variable is defined in terms of already-known ones. Extracted
/// from the proof's own `red` steps, never from the emitter.
#[derive(Clone, Debug, PartialEq, Eq)]
enum Def {
    /// `f = Λ operands` (introduced by `+1 f +1 ~a +1 ~b ... >= 1`).
    And(Vec<u32>),
    /// `f = V operands` (introduced by `+1 ~f +1 a +1 b ... >= 1`).
    Or(Vec<u32>),
}

// ---------------------------------------------------------------------------
// Proof emission.
// ---------------------------------------------------------------------------

/// Thin id-tracking wrapper so the emitter reads like the derivation it encodes.
struct Emitter<'w> {
    writer: &'w mut VeriPbWriter<Vec<u8>>,
}

impl Emitter<'_> {
    fn red(&mut self, body: &str, degree: i128, witness: &str) -> Option<ConstraintId> {
        self.writer
            .log_step(ProofStep::Red(
                format!("{body} >= {degree} "),
                format!("{witness} ;"),
            ))
            .ok()
    }

    fn pol(&mut self, expr: &str) -> Option<ConstraintId> {
        self.writer
            .log_step(ProofStep::Polynomial(format!("{expr} ;")))
            .ok()
    }
}

/// The positional layout, resolved to OPB variable ids and INPUT ROW IDS.
///
/// Row ids are 1-based indices into `instance.constraints`, which is exactly
/// VeriPB's numbering for the `f` block when every row is a `>=` (this family
/// has no equalities; the emitter asserts it).
struct Layout {
    n: usize,
    t: usize,
    /// `m[i][j]`: vertex `i` occupies slot `j`.
    m: Vec<Vec<u32>>,
    /// `c[i][k]`: vertex `i` takes colour `k`.
    c: Vec<Vec<u32>>,
    /// `o[j]`: slot `j` is paid for (the objective literals).
    o: Vec<u32>,
    /// Row id of the slot-cover row for slot `j`.
    slot_id: Vec<u64>,
    /// Row id of the at-most-one-slot row for vertex `i`.
    vertex_id: Vec<u64>,
    /// Row id of the at-least-one-colour row for vertex `i`.
    colour_id: Vec<u64>,
    /// Row id of the difference-forcing row for vertices `i1<i2` in slots
    /// `(s1, s2)`, indexed `[i1][i2][s1][s2]`.
    edge_id: Vec<Vec<Vec<Vec<u64>>>>,
    /// Row id of the proper-colouring row for vertices `i1<i2`, colour `k`.
    proper_id: Vec<Vec<Vec<u64>>>,
}

impl Layout {
    /// The difference-forcing row for "vertex `v1` in slot `s1`, vertex `v2` in
    /// slot `s2`", in either vertex order.
    fn edge(&self, v1: usize, s1: usize, v2: usize, s2: usize) -> Option<u64> {
        let (lo, lo_s, hi, hi_s) = if v1 < v2 {
            (v1, s1, v2, s2)
        } else {
            (v2, s2, v1, s1)
        };
        self.edge_id
            .get(lo)?
            .get(hi)?
            .get(lo_s)?
            .get(hi_s)
            .copied()
            .filter(|&id| id != 0)
    }

    fn proper(&self, v1: usize, v2: usize, k: usize) -> Option<u64> {
        let (lo, hi) = if v1 < v2 { (v1, v2) } else { (v2, v1) };
        self.proper_id
            .get(lo)?
            .get(hi)?
            .get(k)
            .copied()
            .filter(|&id| id != 0)
    }
}

/// Resolves the shape into variable ids and input row ids.
///
/// `detect_shape` has already proved the constraint multiset equals the
/// canonical family exactly, and every canonical signature is distinct (the A/D
/// rows are separated by their variable blocks, the B/C/E rows by degree and
/// sign pattern), so a signature-to-position map is well defined. Building it is
/// one pass; any duplicate signature — impossible after an exact match, but
/// checked anyway — declines.
fn resolve_layout(instance: &PbInstance, shape: &CliqueColoringShape) -> Option<Layout> {
    let n = shape.n();
    let t = shape.t();
    let mut positions: BTreeMap<Vec<(i128, u32)>, u64> = BTreeMap::new();
    for (index, constraint) in instance.constraints.iter().enumerate() {
        if constraint.rel != PbRel::Ge {
            return None; // an `=` row would make VeriPB's `f` numbering shift
        }
        let mut key: Vec<(i128, u32)> = Vec::with_capacity(constraint.terms.len() + 1);
        // The degree rides in the key so rows differing only by rhs stay distinct.
        key.push((constraint.rhs, 0));
        for term in &constraint.terms {
            let [lit] = term.lits.as_slice() else {
                return None;
            };
            if lit.negated || lit.var == 0 {
                return None;
            }
            key.push((term.coeff, lit.var));
        }
        key[1..].sort_unstable();
        if positions.insert(key, (index as u64) + 1).is_some() {
            return None; // duplicate signature: layout would be ambiguous
        }
    }
    let lookup = |rhs: i128, mut pairs: Vec<(i128, u32)>| -> Option<u64> {
        pairs.sort_unstable();
        let mut key = Vec::with_capacity(pairs.len() + 1);
        key.push((rhs, 0u32));
        key.extend(pairs);
        positions.get(&key).copied()
    };

    let m: Vec<Vec<u32>> = (0..n)
        .map(|i| (0..n).map(|j| shape.g1(i + 1, j + 1) as u32).collect())
        .collect();
    let c: Vec<Vec<u32>> = (0..n)
        .map(|i| (0..t).map(|k| shape.g2(i + 1, k + 1) as u32).collect())
        .collect();
    let o: Vec<u32> = (0..n).map(|j| shape.obj(j + 1) as u32).collect();

    // A (slot cover): o[j] + Σ_i m[i][j] >= 1.
    let mut slot_id = Vec::with_capacity(n);
    for j in 0..n {
        let mut pairs = vec![(1i128, o[j])];
        for row in m.iter().take(n) {
            pairs.push((1i128, row[j]));
        }
        slot_id.push(lookup(1, pairs)?);
    }
    // B (at most one slot per vertex): -Σ_j m[i][j] >= -1.
    let mut vertex_id = Vec::with_capacity(n);
    for row in m.iter().take(n) {
        let pairs: Vec<(i128, u32)> = row.iter().map(|&v| (-1i128, v)).collect();
        vertex_id.push(lookup(-1, pairs)?);
    }
    // D (at least one colour per vertex): Σ_k c[i][k] >= 1.
    let mut colour_id = Vec::with_capacity(n);
    for row in c.iter().take(n) {
        let pairs: Vec<(i128, u32)> = row.iter().map(|&v| (1i128, v)).collect();
        colour_id.push(lookup(1, pairs)?);
    }
    // C (difference forcing): e(i1,i2) - m[i1][s1] - m[i2][s2] >= -1, s1 != s2.
    // E (proper colouring): -e(i1,i2) - c[i1][k] - c[i2][k] >= -2.
    let mut edge_id = vec![vec![vec![vec![0u64; n]; n]; n]; n];
    let mut proper_id = vec![vec![vec![0u64; t]; n]; n];
    for i1 in 0..n {
        for i2 in (i1 + 1)..n {
            let e = shape.edge(i1 + 1, i2 + 1) as u32;
            for s1 in 0..n {
                for s2 in 0..n {
                    if s1 == s2 {
                        continue;
                    }
                    let pairs = vec![(1i128, e), (-1i128, m[i1][s1]), (-1i128, m[i2][s2])];
                    edge_id[i1][i2][s1][s2] = lookup(-1, pairs)?;
                }
            }
            for k in 0..t {
                let pairs = vec![(-1i128, e), (-1i128, c[i1][k]), (-1i128, c[i2][k])];
                proper_id[i1][i2][k] = lookup(-2, pairs)?;
            }
        }
    }

    Some(Layout {
        n,
        t,
        m,
        c,
        o,
        slot_id,
        vertex_id,
        colour_id,
        edge_id,
        proper_id,
    })
}

/// Writes the VeriPB v3 proof. Returns the text and the id of the row that must
/// be exactly `Σ_j o[j] >= n - t` (the self-check verifies that it is).
fn emit(instance: &PbInstance, lay: &Layout, incumbent: &[bool]) -> Option<(String, u64)> {
    let (n, t) = (lay.n, lay.t);
    let nvar = instance.num_vars as u64;
    let big = |x: usize| -> u64 { x as u64 };

    // Fresh variable blocks, laid out above every OPB variable.
    let pvar = |i: usize, j: usize, k: usize| -> u64 {
        nvar + 1 + ((big(i) * big(n) + big(j)) * big(t) + big(k))
    };
    let zvar = |j: usize, k: usize| -> u64 {
        nvar + big(n) * big(n) * big(t) + 1 + (big(j) * big(t) + big(k))
    };
    let svar = |j: usize, k: usize| -> u64 {
        nvar + big(n) * big(n) * big(t) + big(n) * big(t) + 1 + (big(j) * big(t) + big(k))
    };

    let f_count = veripb_input_constraint_count(instance).ok()?;
    if f_count != instance.constraints.len() as u64 {
        return None; // an equality row would desync every id below
    }
    let mut writer = VeriPbWriter::new(Vec::<u8>::new(), f_count).ok()?;
    let mut em = Emitter {
        writer: &mut writer,
    };

    let assignment = format_assignment(incumbent);
    let soli_id = em
        .writer
        .log_step(ProofStep::SolutionImproving(assignment.clone()))
        .ok()?;

    // p[i][j][k] <-> m[i][j] AND c[i][k]. The INTRODUCTION ORDER is load bearing:
    // the `p -> 1` line must come first, or the `p -> 0` witnesses have a
    // proofgoal they cannot discharge.
    let mut pge = vec![vec![vec![0u64; t]; n]; n];
    let mut ple_m = vec![vec![vec![0u64; t]; n]; n];
    let mut ple_c = vec![vec![vec![0u64; t]; n]; n];
    for i in 0..n {
        for j in 0..n {
            for k in 0..t {
                let p = pvar(i, j, k);
                let (mv, cv) = (lay.m[i][j], lay.c[i][k]);
                pge[i][j][k] = em
                    .red(
                        &format!("+1 x{p} +1 ~x{mv} +1 ~x{cv}"),
                        1,
                        &format!("x{p} -> 1"),
                    )?
                    .get();
                ple_m[i][j][k] = em
                    .red(&format!("+1 x{mv} +1 ~x{p}"), 1, &format!("x{p} -> 0"))?
                    .get();
                ple_c[i][j][k] = em
                    .red(&format!("+1 x{cv} +1 ~x{p}"), 1, &format!("x{p} -> 0"))?
                    .get();
            }
        }
    }

    // Σ_k p[i][j][k] >= m[i][j]: the colour row TIMES m[i][j], then `s`. This
    // single saturation is the step LP duality cannot reproduce.
    let mut sum_p = vec![vec![0u64; n]; n];
    for i in 0..n {
        for j in 0..n {
            let mut expr = lay.colour_id[i].to_string();
            for k in 0..t {
                let _ = write!(expr, " {} +", pge[i][j][k]);
            }
            expr.push_str(" s");
            sum_p[i][j] = em.pol(&expr)?.get();
        }
    }

    // z[j][k] <-> "slot j holds a colour-k vertex".
    let mut zor = vec![vec![0u64; t]; n];
    let mut zge = vec![vec![vec![0u64; n]; t]; n];
    for j in 0..n {
        for k in 0..t {
            let z = zvar(j, k);
            let mut body = format!("+1 ~x{z}");
            for i in 0..n {
                let _ = write!(body, " +1 x{}", pvar(i, j, k));
            }
            zor[j][k] = em.red(&body, 1, &format!("x{z} -> 0"))?.get();
            for i in 0..n {
                let p = pvar(i, j, k);
                zge[j][k][i] = em
                    .red(&format!("+1 x{z} +1 ~x{p}"), 1, &format!("x{z} -> 1"))?
                    .get();
            }
        }
    }

    // o[j] + Σ_k z[j][k] >= 1: an unpaid slot holds something.
    let mut unpaid = Vec::with_capacity(n);
    for j in 0..n {
        let mut per_vertex = Vec::with_capacity(n);
        for i in 0..n {
            let mut expr = sum_p[i][j].to_string();
            for k in 0..t {
                let _ = write!(expr, " {} +", zge[j][k][i]);
            }
            per_vertex.push(em.pol(&expr)?.get());
        }
        let mut expr = lay.slot_id[j].to_string();
        for id in &per_vertex {
            let _ = write!(expr, " {id} +");
        }
        expr.push_str(" s");
        unpaid.push(em.pol(&expr)?.get());
    }

    // ~p[i][a][k] + ~p[i2][b][k] >= 1 for slots a < b: two vertices cannot hold
    // colour k in two distinct slots. Same vertex: it has at most one slot.
    // Distinct vertices: distinct slots force the edge, the edge forbids the
    // shared colour, and `2 d` recovers the clause from the doubled sum.
    let mut base = vec![vec![vec![vec![vec![0u64; n]; n]; n]; n]; t];
    for k in 0..t {
        for a in 0..n {
            for b in (a + 1)..n {
                for i in 0..n {
                    for i2 in 0..n {
                        let expr = if i == i2 {
                            let mut expr = lay.vertex_id[i].to_string();
                            for (j, &mv) in lay.m[i].iter().enumerate().take(n) {
                                if j != a && j != b {
                                    let _ = write!(expr, " x{mv} +");
                                }
                            }
                            let _ = write!(expr, " {} + {} +", ple_m[i][a][k], ple_m[i][b][k]);
                            expr
                        } else {
                            let er = lay.edge(i, a, i2, b)?;
                            let pr = lay.proper(i, i2, k)?;
                            format!(
                                "{er} {pr} + {} + {} + {} + {} + 2 d",
                                ple_m[i][a][k], ple_c[i][a][k], ple_m[i2][b][k], ple_c[i2][b][k]
                            )
                        };
                        base[k][a][b][i][i2] = em.pol(&expr)?.get();
                    }
                }
            }
        }
    }

    // ~z[a][k] + ~z[b][k] >= 1, by two rounds of "sum the family, add the
    // reified OR, saturate". Each round replaces one disjunction by its head.
    let mut zconf = vec![vec![vec![0u64; n]; n]; t];
    for k in 0..t {
        for a in 0..n {
            for b in (a + 1)..n {
                let mut lifted = Vec::with_capacity(n);
                for i in 0..n {
                    let mut expr = base[k][a][b][i][0].to_string();
                    for i2 in 1..n {
                        let _ = write!(expr, " {} +", base[k][a][b][i][i2]);
                    }
                    let _ = write!(expr, " {} + s", zor[b][k]);
                    lifted.push(em.pol(&expr)?.get());
                }
                let mut expr = lifted[0].to_string();
                for id in &lifted[1..] {
                    let _ = write!(expr, " {id} +");
                }
                let _ = write!(expr, " {} + s", zor[a][k]);
                zconf[k][a][b] = em.pol(&expr)?.get();
            }
        }
    }

    // Σ_j ~z[j][k] >= n-1 (the at-most-one), via a prefix-OR ladder. Pairwise
    // conflicts alone give only `Σ <= n/2`; the ladder is what makes it 1.
    let mut amo = Vec::with_capacity(t);
    for k in 0..t {
        let mut sor = vec![0u64; n];
        let mut sge = vec![vec![0u64; n]; n];
        for j in 0..n {
            let s = svar(j, k);
            let mut body = format!("+1 ~x{s}");
            for jj in 0..=j {
                let _ = write!(body, " +1 x{}", zvar(jj, k));
            }
            sor[j] = em.red(&body, 1, &format!("x{s} -> 0"))?.get();
            for jj in 0..=j {
                let z = zvar(jj, k);
                sge[j][jj] = em
                    .red(&format!("+1 x{s} +1 ~x{z}"), 1, &format!("x{s} -> 1"))?
                    .get();
            }
        }
        let mut step = vec![0u64; n];
        for j in 1..n {
            let mut expr = zconf[k][0][j].to_string();
            for jj in 1..j {
                let _ = write!(expr, " {} +", zconf[k][jj][j]);
            }
            let _ = write!(expr, " {} + s", sor[j - 1]);
            let conflict = em.pol(&expr)?.get();

            let mut expr = sge[j][0].to_string();
            for jj in 1..j {
                let _ = write!(expr, " {} +", sge[j][jj]);
            }
            let _ = write!(expr, " {} + s", sor[j - 1]);
            let monotone = em.pol(&expr)?.get();

            step[j] = em
                .pol(&format!("{conflict} {} + {monotone} + 2 d", sge[j][j]))?
                .get();
        }
        let mut expr = step[1].to_string();
        for &id in step.iter().take(n).skip(2) {
            let _ = write!(expr, " {id} +");
        }
        let _ = write!(expr, " {} +", sge[0][0]);
        let telescope = em.pol(&expr)?.get();
        amo.push(em.pol(&format!("{telescope} x{} w", svar(n - 1, k)))?.get());
    }

    // Σ_j o[j] >= n - t, with UNIT multipliers on the n slot rows and t AMOs.
    let mut expr = unpaid[0].to_string();
    for &id in &unpaid[1..] {
        let _ = write!(expr, " {id} +");
    }
    for &id in &amo {
        let _ = write!(expr, " {id} +");
    }
    let floor = em.pol(&expr)?;
    let contradiction = writer.log_step(ProofStep::Addition(floor, soli_id)).ok()?;

    let optimum = i128::try_from(n)
        .ok()?
        .checked_sub(i128::try_from(t).ok()?)?;
    writer.set_opt_bounds(optimum, optimum).ok()?;
    writer
        .conclude_opt_hinted(Some(contradiction), Some(&assignment))
        .ok()?;
    let text = String::from_utf8(writer.into_inner()).ok()?;
    Some((text, floor.get()))
}

// ---------------------------------------------------------------------------
// Layer 4: parse the emitted bytes back and replay them.
// ---------------------------------------------------------------------------

/// Result of extracting a `red` step's definitional content.
struct RedInfo {
    row: CpRow,
    /// The fresh variable this step DEFINES, if it is a defining step.
    defines: Option<(u32, Def)>,
}

/// Classifies one `red` clause against the definitions already extracted.
///
/// Returns `None` — declining the whole certificate — unless the clause is
/// either (a) the introduction of exactly one not-yet-defined fresh variable as
/// an AND/OR of already-known variables, or (b) a consequence clause of a
/// definition already extracted. This is what makes the `red` block
/// CONSERVATIVE over the original variables: no `red` can assert anything about
/// the instance, only about how a fresh variable tracks known ones.
fn classify_red(row: &CpRow, nvar: u64, defs: &BTreeMap<u32, Def>) -> Option<RedInfo> {
    // Must be a clause: every normalized coefficient 1, normalized degree 1.
    if row.norm_degree()? != 1 {
        return None;
    }
    for &c in row.coeff.values() {
        if c.abs() != 1 {
            return None;
        }
    }
    let positives: Vec<u32> = row
        .coeff
        .iter()
        .filter(|&(_, &c)| c > 0)
        .map(|(&v, _)| v)
        .collect();
    let negatives: Vec<u32> = row
        .coeff
        .iter()
        .filter(|&(_, &c)| c < 0)
        .map(|(&v, _)| v)
        .collect();

    let undefined_fresh: Vec<u32> = row
        .coeff
        .keys()
        .copied()
        .filter(|&v| u64::from(v) > nvar && !defs.contains_key(&v))
        .collect();

    match undefined_fresh.len() {
        1 => {
            let f = undefined_fresh[0];
            // Every other variable must already be known (original or defined).
            let known = |v: u32| v == f || u64::from(v) <= nvar || defs.contains_key(&v);
            if !row.coeff.keys().all(|&v| known(v)) {
                return None;
            }
            if positives == vec![f] && !negatives.is_empty() {
                Some(RedInfo {
                    row: row.clone(),
                    defines: Some((f, Def::And(negatives))),
                })
            } else if negatives == vec![f] && !positives.is_empty() {
                Some(RedInfo {
                    row: row.clone(),
                    defines: Some((f, Def::Or(positives))),
                })
            } else {
                None
            }
        }
        0 => {
            // A consequence clause of some already-extracted definition. Any
            // reading that validates is enough: each is genuinely entailed.
            let ok = defs.iter().any(|(&f, def)| match def {
                // f = Λ a_i entails `a_i + ~f >= 1`.
                Def::And(ops) => {
                    negatives == vec![f] && positives.len() == 1 && ops.contains(&positives[0])
                }
                // f = V o_i entails `f + ~o_i >= 1`.
                Def::Or(ops) => {
                    positives == vec![f] && negatives.len() == 1 && ops.contains(&negatives[0])
                }
            });
            if ok {
                Some(RedInfo {
                    row: row.clone(),
                    defines: None,
                })
            } else {
                None
            }
        }
        _ => None,
    }
}

/// Extends an assignment over the original variables through the extracted
/// definitions, in definition order.
fn extend(values: &mut Vec<bool>, order: &[(u32, Def)]) -> Option<()> {
    for (var, def) in order {
        let index = (*var as usize).checked_sub(1)?;
        let value = match def {
            Def::And(ops) => ops.iter().all(|&v| values[(v as usize) - 1]),
            Def::Or(ops) => ops.iter().any(|&v| values[(v as usize) - 1]),
        };
        if values.len() <= index {
            values.resize(index + 1, false);
        }
        values[index] = value;
    }
    Some(())
}

/// Parses the emitted proof back and replays it. Returns `true` only if the
/// bytes establish `Σ_j o[j] >= n - t` for THIS instance.
///
/// `probes` are assignments over the original variables that are FEASIBLE for
/// the instance; every replayed row is evaluated against each (extended through
/// the definitions) and any violation declines. A feasible point that falsifies
/// a derived row would mean the derivation is unsound, so this is a real test of
/// the emitted arithmetic and not a restatement of it.
fn self_check(
    text: &str,
    instance: &PbInstance,
    lay: &Layout,
    floor_id: u64,
    probes: &[Vec<bool>],
) -> bool {
    self_check_inner(text, instance, lay, floor_id, probes).is_some()
}

// `DECLINE` records the first refusal site under test so a failure is
// diagnosable instead of a bare `false`; production reads only success/failure.
#[cfg(test)]
thread_local! {
    static DECLINE: std::cell::RefCell<Option<&'static str>> =
        const { std::cell::RefCell::new(None) };
}

/// Records the site of a refusal (test builds only) and returns `None`.
fn decline<T>(_site: &'static str) -> Option<T> {
    #[cfg(test)]
    DECLINE.with(|slot| {
        let mut slot = slot.borrow_mut();
        if slot.is_none() {
            *slot = Some(_site);
        }
    });
    None
}

#[allow(clippy::too_many_lines)]
fn self_check_inner(
    text: &str,
    instance: &PbInstance,
    lay: &Layout,
    floor_id: u64,
    probes: &[Vec<bool>],
) -> Option<()> {
    let nvar = instance.num_vars as u64;
    let optimum = i128::try_from(lay.n)
        .ok()?
        .checked_sub(i128::try_from(lay.t).ok()?)?;

    let mut lines = text.lines();
    if lines.next()? != "pseudo-Boolean proof version 3.0" {
        return decline("header");
    }
    let f_line: Vec<&str> = lines.next()?.split_whitespace().collect();
    if f_line.first()? != &"f" {
        return decline("f-line");
    }
    let f_count: u64 = f_line.get(1)?.parse().ok()?;
    if f_count != instance.constraints.len() as u64 {
        return decline("f-count");
    }

    // The `f` block: VeriPB numbers the input rows 1..=f_count in file order.
    let mut db: BTreeMap<u64, CpRow> = BTreeMap::new();
    for (index, constraint) in instance.constraints.iter().enumerate() {
        if constraint.rel != PbRel::Ge {
            return None;
        }
        let mut row = CpRow {
            coeff: BTreeMap::new(),
            rhs: constraint.rhs,
        };
        for term in &constraint.terms {
            let [lit] = term.lits.as_slice() else {
                return None;
            };
            if lit.negated {
                row.add_coeff(lit.var, term.coeff.checked_neg()?)?;
                row.rhs = row.rhs.checked_sub(term.coeff)?;
            } else {
                row.add_coeff(lit.var, term.coeff)?;
            }
        }
        db.insert((index as u64) + 1, row);
    }

    let mut next_id = f_count + 1;
    // Ids that depend on the `soli` row. The objective-IMPROVING constraint
    // `Σ o < optimum` is an ASSUMPTION for the refutation, not a consequence of
    // the instance — the optimal incumbent falsifies it by construction — so
    // probes must not be applied to it or to anything derived from it. Tracking
    // that dependency also buys the check that matters most: the FLOOR row must
    // NOT be tainted, or the bound would rest on the incumbent it is supposed to
    // be independent of, which is circular.
    let mut tainted: std::collections::BTreeSet<u64> = std::collections::BTreeSet::new();
    let mut defs: BTreeMap<u32, Def> = BTreeMap::new();
    let mut def_order: Vec<(u32, Def)> = Vec::new();
    let mut soli_seen = false;
    let mut last_id: Option<u64> = None;
    // Probe assignments, extended lazily as definitions appear. Each is kept in
    // lockstep with `def_order`, so a row can always be evaluated when produced.
    let mut probe_values: Vec<Vec<bool>> = probes.to_vec();
    let mut probes_extended_to = 0usize;

    let mut conclusion: Option<String> = None;
    let mut row_tainted;
    for line in lines {
        let line = line.trim_end();
        if line == "output NONE;" {
            continue;
        }
        if line == "end pseudo-Boolean proof;" {
            break;
        }
        if let Some(rest) = line.strip_prefix("conclusion ") {
            conclusion = Some(rest.to_string());
            continue;
        }
        let row = if let Some(rest) = line.strip_prefix("soli ") {
            if soli_seen {
                return decline("second-soli"); // exactly one is expected
            }
            soli_seen = true;
            // VeriPB installs `obj <= best - 1` for the logged solution. Rebuild
            // it from the LOGGED literals, not from a remembered value, so a
            // mismatched witness cannot slip through.
            let lits = rest.trim_end_matches(';').trim();
            let mut values = vec![false; nvar as usize];
            for token in lits.split_whitespace() {
                let (var, negated) = parse_lit(token)?;
                let index = (var as usize).checked_sub(1)?;
                if index >= values.len() {
                    return None;
                }
                values[index] = !negated;
            }
            let objective = instance.objective.as_ref()?;
            let value = evaluate_linear_objective(objective, &values)?;
            if value != optimum {
                return decline("soli-objective");
            }
            if !crate::eval::verify_all_constraints(&instance.constraints, &values) {
                return decline("soli-infeasible");
            }
            // `Σ_j o[j] <= optimum - 1`, i.e. `-Σ_j o[j] >= -(optimum - 1)`.
            let mut row = CpRow {
                coeff: BTreeMap::new(),
                rhs: optimum.checked_sub(1)?.checked_neg()?,
            };
            for &v in &lay.o {
                row.add_coeff(v, -1)?;
            }
            row_tainted = true;
            row
        } else if let Some(rest) = line.strip_prefix("red ") {
            let (body, witness) = rest.split_once(':')?;
            let tokens: Vec<&str> = body.split_whitespace().collect();
            let ge = tokens.iter().position(|&tok| tok == ">=")?;
            let mut row = parse_terms(&tokens[..ge])?;
            let degree: i128 = tokens.get(ge + 1)?.parse().ok()?;
            row.rhs = row.rhs.checked_add(degree)?;
            let Some(info) = classify_red(&row, nvar, &defs) else {
                return decline("red-not-definitional");
            };
            if let Some((f, def)) = info.defines {
                // The witness must flip exactly the variable being defined.
                let witness_var = parse_lit(witness.split_whitespace().next()?)?.0;
                if witness_var != f {
                    return decline("red-witness-mismatch");
                }
                defs.insert(f, def.clone());
                def_order.push((f, def));
            }
            row_tainted = false;
            info.row
        } else if let Some(rest) = line.strip_prefix("pol ") {
            match eval_pol(rest.trim_end_matches(';').trim(), &db) {
                Some((row, used)) => {
                    row_tainted = used.iter().any(|id| tainted.contains(id));
                    row
                }
                None => return decline("pol-replay"),
            }
        } else {
            return decline("unmodelled-rule");
        };

        // Keep every probe extended through the definitions seen so far, then
        // require the new row to hold on all of them.
        if probes_extended_to < def_order.len() {
            for values in &mut probe_values {
                extend(values, &def_order[probes_extended_to..])?;
            }
            probes_extended_to = def_order.len();
        }
        if !row_tainted {
            for values in &probe_values {
                if !row.holds(values) {
                    return decline("probe-falsifies-row");
                }
            }
        } else {
            tainted.insert(next_id);
        }

        db.insert(next_id, row);
        last_id = Some(next_id);
        next_id += 1;
    }

    // (b) The floor row must be EXACTLY `Σ_j o[j] >= n - t` — the objective
    // vector, over exactly the objective variables, at exactly the bound. This
    // is the load-bearing check: it is what makes the conclusion the OPTIMUM and
    // not some weaker consequence over a different variable set.
    if tainted.contains(&floor_id) {
        // The floor may not depend on the objective-improving assumption.
        return decline("floor-depends-on-soli");
    }
    let Some(floor) = db.get(&floor_id) else {
        return decline("floor-missing");
    };
    if floor.rhs != optimum || floor.coeff.len() != lay.o.len() {
        return decline("floor-shape");
    }
    for &v in &lay.o {
        if floor.coeff.get(&v) != Some(&1) {
            return decline("floor-coefficient");
        }
    }
    // No fresh variable may survive into the floor (checked by the length and
    // membership test above, since `lay.o` are all original).

    // (c) The last row must be the empty contradiction.
    let last = db.get(&last_id?)?;
    if !last.is_contradiction() {
        return decline("not-contradiction");
    }
    // The contradiction MUST come from the improving assumption: a refutation
    // reached without it would say the instance is infeasible, which the
    // re-verified incumbent disproves.
    if !tainted.contains(&last_id?) {
        return decline("contradiction-without-soli");
    }

    // The conclusion must claim exactly `optimum <= obj <= optimum`, hinted at
    // the contradiction we just replayed.
    let conclusion = conclusion?;
    let expect = format!("BOUNDS {optimum} : {} {optimum} :", last_id?);
    if !conclusion.starts_with(&expect) {
        return decline("conclusion-mismatch");
    }
    if !soli_seen {
        return decline("no-soli");
    }
    Some(())
}

// ---------------------------------------------------------------------------
// Entry point.
// ---------------------------------------------------------------------------

/// CLIQUE-COLORING optimality certificate for the `ihalainen/PBO-clique-coloring`
/// family, whose LP relaxation — and whose full level-1 RLT lift — is exactly 0
/// against an optimum of `n - t`, so no LP-dual floor can ever certify it.
///
/// Returns proof *text* only; `None` withholds the certificate and never changes
/// the reported status. Every returned proof has already been parsed back and
/// replayed by [`self_check`], and is still untrusted until the PINNED external
/// VeriPB accepts it (verify-before-claim).
pub fn certify_opt_lin_clique_coloring(
    instance: &PbInstance,
    incumbent: &[bool],
    optimum: i128,
) -> Option<String> {
    // Layer 1: the O(1) pre-gate. Off-family instances stop here.
    let (n, t) = header_candidate(
        u64::from(instance.num_vars),
        instance.constraints.len() as u64,
    )?;
    let objective = instance.objective.as_ref()?;
    if objective.terms.len() != n {
        return None;
    }
    // The structural prediction must agree with the solver's own optimum.
    let predicted = i128::try_from(n)
        .ok()?
        .checked_sub(i128::try_from(t).ok()?)?;
    if optimum != predicted || predicted < 1 {
        return None;
    }
    if incumbent.len() != instance.num_vars as usize {
        return None;
    }

    // Layer 2: the exact structural match, shared with the solver shortcut.
    let shape = detect_shape(instance, objective)?;
    if shape.n() != n || shape.t() != t {
        return None;
    }
    // The derivation is Θ(t·n⁴) steps — the same order as the instance's own
    // Θ(n⁴/2) rows, so this is proportional rather than explosive. It is still
    // capped: the round that named this work was REFUSED for running two
    // instances into a 3,072 MiB jetsam kill that emitted NOTHING, and declining
    // cleanly beats being SIGKILLed mid-write. At the cap the working set is a
    // few hundred MiB; the whole PB25 corpus sits three orders below it
    // (n=20,t=2 is the largest at 3.2e5).
    let steps = t.checked_mul(n.checked_pow(4)?)?;
    if steps > 40_000_000 {
        return None;
    }
    let lay = resolve_layout(instance, &shape)?;

    // Layer 3: independent re-verification of the incumbent.
    if evaluate_linear_objective(objective, incumbent)? != optimum {
        return None;
    }
    if !crate::eval::verify_all_constraints(&instance.constraints, incumbent) {
        return None;
    }

    let (text, floor_id) = emit(instance, &lay, incumbent)?;

    // Layer 4: replay the emitted bytes. `two_in_a_slot` is a genuinely
    // different feasible point (two vertices sharing one slot, every vertex on
    // colour 0) — it is exactly the point that shows the at-most-one is NOT an
    // LP cut, so it exercises the derivation where the LP argument fails.
    let mut probes = vec![incumbent.to_vec()];
    if let Some(point) = two_in_a_slot(instance, &lay) {
        probes.push(point);
    }
    if !self_check(&text, instance, &lay, floor_id, &probes) {
        return None;
    }
    Some(text)
}

/// A feasible point with two vertices in one slot: `m[0][0] = m[1][0] = 1`,
/// every slot but 0 paid for, every vertex on colour 0, every edge off. No pair
/// of vertices is in DISTINCT slots, so no edge is forced and the proper-colouring
/// rows stay slack. Returns `None` unless it re-verifies as feasible.
fn two_in_a_slot(instance: &PbInstance, lay: &Layout) -> Option<Vec<bool>> {
    let mut values = vec![false; instance.num_vars as usize];
    let mut set = |var: u32| -> Option<()> {
        *values.get_mut((var as usize).checked_sub(1)?)? = true;
        Some(())
    };
    set(lay.m[0][0])?;
    set(lay.m[1][0])?;
    for j in 1..lay.n {
        set(lay.o[j])?;
    }
    for i in 0..lay.n {
        set(lay.c[i][0])?;
    }
    if !crate::eval::verify_all_constraints(&instance.constraints, &values) {
        return None;
    }
    Some(values)
}

#[cfg(test)]
mod tests;
