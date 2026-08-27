// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

// Included by the parent module to preserve the oracle API paths.

/// `mroot::eval_sign_at` vs `Z3_algebraic_eval`.
///
/// Every coordinate INCLUDING the last is assigned here, which is what
/// `Z3_algebraic_eval` requires: it refuses a polynomial whose maximal
/// variable is at or past the number of values supplied.
pub(crate) fn check_mv_sign_at(z3: &Z3, g: &GenMv, sab: Sabotage) -> Outcome {
    let n = g.nvars + 1;
    if g.elimination_degree(n) > MAX_ELIM_DEGREE {
        return Outcome::Skipped("elimination degree over budget");
    }
    let coords = match build_coords(z3, g, n) {
        Ok(c) => c,
        Err(o) => return o,
    };
    let Some((ap, zp)) = build_poly(z3, g) else {
        return Outcome::Skipped("degenerate polynomial");
    };
    let mut x2v = OVar2Anum::new();
    for (i, c) in coords.iter().enumerate() {
        x2v.set(u32::try_from(i).unwrap_or(0), &c.ay);
    }
    let Some(ay_sign) = ap.eval_sign_at(&x2v) else {
        return Outcome::Declined("eval_sign_at");
    };
    let values: Vec<Ast> = coords.iter().map(|c| c.z3).collect();
    let Some(z3_sign) = z3.eval_sign_at(zp, &values) else {
        return Outcome::Skipped("z3 declined eval_sign");
    };
    // Sabotage: turn a zero into a positive, and flip everything else. The
    // zero case is the one that matters — it is the sieve's decision.
    let ay_sign = if sab.on() {
        if ay_sign == 0 {
            1
        } else {
            -ay_sign
        }
    } else {
        ay_sign
    };
    if ay_sign != z3_sign {
        return Divergence::outcome(
            "mv-sign-at",
            "z3",
            format!("AY's sign is {ay_sign}, z3's is {z3_sign}"),
            inputs(g),
        );
    }
    Outcome::Match(1)
}

/// `mroot::isolate_roots_closest_at` vs the same selection made from z3's FULL
/// root list using z3's own exact comparisons.
///
/// The selection rule is the one z3's header states for
/// `isolate_roots_closest`: the last root `<= s`, the first root `> s`, or the
/// single root `s` when `s` is itself a root.
fn closest_indices(z3: &Z3, roots: &[Ast], s: &BigRational) -> Result<Vec<usize>, Outcome> {
    let Some(s_ast) = z3.rational(s) else {
        return Err(Outcome::Skipped("z3 rejected rational comparison point"));
    };
    let mut below = None;
    let mut above = None;
    for (i, value) in roots.iter().enumerate() {
        let Some(is_equal) = z3.eq(*value, s_ast) else {
            return Err(Outcome::Skipped("z3 errored while ordering roots"));
        };
        if is_equal {
            return Ok(vec![i]);
        }
        let Some(is_below) = z3.lt(*value, s_ast) else {
            return Err(Outcome::Skipped("z3 errored while ordering roots"));
        };
        if is_below {
            below = Some(i);
        } else if above.is_none() {
            above = Some(i);
        }
    }
    Ok(below.into_iter().chain(above).collect())
}

pub(crate) fn check_mv_closest(z3: &Z3, g: &GenMv, s: &BigRational, sab: Sabotage) -> Outcome {
    if g.elimination_degree(g.nvars) > MAX_ELIM_DEGREE {
        return Outcome::Skipped("elimination degree over budget");
    }
    let coords = match build_coords(z3, g, g.nvars) {
        Ok(c) => c,
        Err(o) => return o,
    };
    let Some((ap, zp)) = build_poly(z3, g) else {
        return Outcome::Skipped("degenerate polynomial");
    };
    let x = u32::try_from(g.nvars).unwrap_or(0);
    if ap.degree_in(x) == 0 {
        return Outcome::Skipped("unknown does not occur");
    }
    let mut x2v = OVar2Anum::new();
    for (i, c) in coords.iter().enumerate() {
        x2v.set(u32::try_from(i).unwrap_or(0), &c.ay);
    }
    let values: Vec<Ast> = coords.iter().map(|c| c.z3).collect();
    let Some(z3_roots) = z3.roots_at(zp, &values) else {
        return Outcome::Skipped("z3 declined isolate_roots");
    };

    // z3's side of the selection, decided entirely by z3's comparisons.
    let expect = match closest_indices(z3, &z3_roots, s) {
        Ok(indices) => indices,
        Err(outcome) => return outcome,
    };

    let Some((mut ay_roots, mut ay_idx)) = ap.isolate_roots_closest_at(x, &x2v, s) else {
        return Outcome::Declined("isolate_roots_closest_at");
    };
    if sab.on() {
        if ay_roots.is_empty() {
            ay_roots.push(OAnum::rational(s.clone()));
            ay_idx.push(1);
        } else {
            ay_roots.pop();
            ay_idx.pop();
        }
    }

    if ay_idx.len() != expect.len() {
        return Divergence::outcome(
            "mv-closest-roots",
            "z3",
            format!(
                "around s = {s}, AY returned {} root(s), z3's list selects {}",
                ay_idx.len(),
                expect.len()
            ),
            inputs(g),
        );
    }
    let mut comparisons = 1u64;
    for (k, &i) in expect.iter().enumerate() {
        // 1-based index into the full ascending list.
        if ay_idx[k] != i + 1 {
            return Divergence::outcome(
                "mv-closest-roots",
                "z3",
                format!(
                    "around s = {s}, AY's selected root #{} has index {}, z3's has {}",
                    k + 1,
                    ay_idx[k],
                    i + 1
                ),
                inputs(g),
            );
        }
        comparisons += 1;
        let Some(ok) = agrees(z3, z3_roots[i], &ay_roots[k]) else {
            return Outcome::Declined("root comparison");
        };
        comparisons += 1;
        if !ok {
            return Divergence::outcome(
                "mv-closest-roots",
                "z3",
                format!(
                    "around s = {s}, AY's selected root #{} is not z3's {}",
                    k + 1,
                    z3.ast_string(z3_roots[i])
                        .unwrap_or_else(|| "<invalid-z3-ast>".into())
                ),
                inputs(g),
            );
        }
    }
    Outcome::Match(comparisons)
}
