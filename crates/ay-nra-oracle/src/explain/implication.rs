// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

// Included by the parent module so the differential checks share one namespace.

// ===========================================================================
// The INDEPENDENT reference: z3 decides satisfiability by itself
// ===========================================================================

/// Does sign `s` satisfy `c`?
///
/// Deliberately RE-IMPLEMENTED here rather than calling AY's
/// `OISignCond::accepts`. It is six lines, and if the reference side called AY's
/// version then a defect in that predicate would be invisible to every leg
/// below — the `same_set_as` failure exactly. AY's version is cross-checked
/// against this one in [`check_clause_implied`], so it is under test rather than
/// trusted.
fn oracle_accepts(c: OISignCond, s: i32) -> bool {
    match c {
        OISignCond::Lt => s < 0,
        OISignCond::Le => s <= 0,
        OISignCond::Eq => s == 0,
        OISignCond::Ne => s != 0,
        OISignCond::Ge => s >= 0,
        OISignCond::Gt => s > 0,
    }
}

/// Is `/\_j (p_j cond_j 0)` satisfiable over the reals? Decided by z3 alone.
///
/// The real roots of every cited polynomial cut `R` into finitely many cells on
/// which all of them have constant sign, so testing one point per cell plus each
/// root is EXHAUSTIVE. Sample points for the open cells are the exact midpoints
/// of adjacent roots, built with `Z3_algebraic_add` and `Z3_algebraic_mul`, so
/// no rounding or bracketing enters anywhere.
///
/// `None` is a z3 error or refusal, never a verdict: the oracle is not entitled
/// to call a bug on the reference implementation's behalf.
///
/// # Liveness
///
/// The insertion sort is `O(n^2)` over `n = sum of degrees`, which the generator
/// keeps at or below 6; the sample scan is one pass over `2n + 1` points. No
/// condition-driven loop.
fn z3_satisfiable(z3: &Z3, polys: &[Vec<BigInt>], conds: &[OISignCond]) -> Option<bool> {
    if polys.len() != conds.len() {
        return None;
    }
    if polys.is_empty() {
        // The empty conjunction is vacuously true.
        return Some(true);
    }

    // Every root, from z3.
    let mut sorted: Vec<Ast> = Vec::new();
    for p in polys {
        let rs = z3.roots(&rationals(p))?;
        for r in rs {
            let mut pos = sorted.len();
            let mut dup = false;
            for (i, s) in sorted.iter().enumerate() {
                if z3.eq(r, *s)? {
                    dup = true;
                    break;
                }
                if z3.lt(r, *s)? {
                    pos = i;
                    break;
                }
            }
            if !dup {
                sorted.insert(pos, r);
            }
        }
    }
    // One sample point per cell, all exact, all z3's.
    let mut samples: Vec<Ast> = Vec::new();
    if sorted.is_empty() {
        samples.push(z3.rational(&BigRational::zero())?);
    } else {
        let one = z3.rational(&BigRational::one())?;
        let minus_one = z3.rational(&-BigRational::one())?;
        let half = z3.rational(&BigRational::new(BigInt::one(), BigInt::from(2)))?;
        samples.push(z3.add(sorted[0], minus_one)?);
        for (i, r) in sorted.iter().enumerate() {
            samples.push(*r);
            if let Some(next) = sorted.get(i + 1) {
                let sum = z3.add(*r, *next)?;
                samples.push(z3.mul(sum, half)?);
            }
        }
        samples.push(z3.add(sorted[sorted.len() - 1], one)?);
    }
    for s in &samples {
        let mut all = true;
        for (p, c) in polys.iter().zip(conds) {
            let sg = z3.eval_sign(&rationals(p), *s)?;
            if !oracle_accepts(*c, sg) {
                all = false;
                break;
            }
        }
        if z3.errored() {
            return None;
        }
        if all {
            return Some(true);
        }
    }
    Some(false)
}

/// Build AY's literal list, taking every root from z3.
///
/// Driving AY's pure functions on z3's OWN root list is what keeps them pure
/// functions under test rather than a consumer's private state.
fn ay_lits(z3: &Z3, g: &GenEx) -> Option<Vec<OExplainLit>> {
    let mut out = Vec::with_capacity(g.polys.len());
    for (i, (p, c)) in g.polys.iter().zip(&g.conds).enumerate() {
        let rs = z3.roots(&rationals(p))?;
        let mut roots = Vec::with_capacity(rs.len());
        for v in rs {
            let iv = dyadic_iv(z3, v)?;
            roots.push(ODyadicAnum::from_poly_interval(p, &iv)?);
        }
        if z3.errored() {
            return None;
        }
        out.push(OExplainLit {
            lit: i32::try_from(i + 1).ok()?,
            p: p.clone(),
            cond: *c,
            roots,
        });
    }
    Some(out)
}

/// Are all the generated polynomials usable (non-zero, degree >= 1)?
fn usable(g: &GenEx) -> bool {
    !g.polys.is_empty()
        && g.polys.len() == g.conds.len()
        && g.polys.iter().all(|p| {
            p.iter()
                .rev()
                .position(|c| !c.is_zero())
                .map_or(false, |z| p.len().saturating_sub(z).saturating_sub(1) >= 1)
        })
}

// ===========================================================================
// Check 1 — `explain-clause-implied`
// ===========================================================================

/// **The defining property.** AY's implication verdict against z3's own
/// decision procedure.
///
/// z3 legs: `oexplain_clause_is_valid` must be `true` exactly when
/// [`z3_satisfiable`] says the cited conjunction is UNSAT. A disagreement in the
/// direction "AY says implied, z3 says satisfiable" is a WRONG `unsat` in
/// waiting and is reported as such.
/// Identity legs: AY's `accepts` predicate must agree with [`oracle_accepts`] on
/// all three signs and all six conditions; the two ceiling accessors must report
/// the values the guards actually enforce.
/// Guards, fired on purpose: a conflict one literal OVER `MAX_CONFLICT_LITS`
/// must be refused while the same conflict one literal UNDER it is answered —
/// a module that refused everything would fail the pair.
/// Precondition legs, fired on purpose: a root list with one root DROPPED, one
/// SPURIOUS root added, and one root replaced by a non-root at the same count
/// must each be refused. The dropped-root case is the one that turns a
/// satisfiable conjunction into an apparent conflict.
fn check_literal_ceiling(lits: &[OExplainLit], g: &GenEx) -> Result<u64, Outcome> {
    let smallest = lits
        .iter()
        .min_by_key(|literal| literal.roots.len())
        .expect("a case always has at least one literal");
    let over: Vec<OExplainLit> = (0..=oexplain_max_conflict_lits())
        .map(|i| OExplainLit {
            lit: i32::try_from(i + 1).unwrap_or(1),
            p: smallest.p.clone(),
            cond: smallest.cond,
            roots: smallest.roots.clone(),
        })
        .collect();
    if oexplain_clause_is_valid(&over).is_some() {
        return Err(Divergence::outcome(
            "explain-clause-implied",
            "identity",
            format!(
                "{} literals is over the declared ceiling of {} and was ANSWERED",
                over.len(),
                oexplain_max_conflict_lits()
            ),
            inputs(g),
        ));
    }
    if oexplain_clause_is_valid(&over[..oexplain_max_conflict_lits()]).is_none() {
        return Err(Divergence::outcome(
            "explain-clause-implied",
            "identity",
            format!(
                "exactly {} literals is AT the ceiling and was refused -- the guard fires too \
                 early, so the positive control fails",
                oexplain_max_conflict_lits()
            ),
            inputs(g),
        ));
    }
    Ok(2)
}

fn check_root_list_guards(lits: &[OExplainLit], g: &GenEx) -> Result<u64, Outcome> {
    let Some(idx) = lits.iter().position(|literal| !literal.roots.is_empty()) else {
        return Ok(0);
    };
    let mut dropped = lits.to_vec();
    dropped[idx].roots.pop();
    if oexplain_clause_is_valid(&dropped).is_some() {
        return Err(Divergence::outcome(
            "explain-clause-implied",
            "identity",
            "a root list with one root DROPPED was accepted -- an incomplete decomposition \
             makes a satisfiable conjunction look unsatisfiable"
                .to_string(),
            inputs(g),
        ));
    }
    let non_root = || ODyadicAnum::rational(BigRational::from_integer(BigInt::from(1_000_003)));
    let mut extra = lits.to_vec();
    extra[idx].roots.push(non_root());
    if oexplain_clause_is_valid(&extra).is_some() {
        return Err(Divergence::outcome(
            "explain-clause-implied",
            "identity",
            "a root list with a SPURIOUS root was accepted".to_string(),
            inputs(g),
        ));
    }
    let mut swapped = lits.to_vec();
    let n = swapped[idx].roots.len();
    swapped[idx].roots[n - 1] = non_root();
    if oexplain_clause_is_valid(&swapped).is_some() {
        return Err(Divergence::outcome(
            "explain-clause-implied",
            "identity",
            "a root list with the RIGHT COUNT but a non-root value was accepted -- the \
             precondition is verified in the weak direction only"
                .to_string(),
            inputs(g),
        ));
    }
    Ok(3)
}

pub(crate) fn check_clause_implied(z3: &Z3, g: &GenEx, sab: Sabotage) -> Outcome {
    if !usable(g) {
        return Outcome::Skipped("degenerate polynomial");
    }
    if g.polys.len() > oexplain_max_conflict_lits() {
        return Outcome::Skipped("over the declared ceiling");
    }
    let Some(lits) = ay_lits(z3, g) else {
        return Outcome::Skipped("z3 declined the root isolation");
    };
    let Some(z3_sat) = z3_satisfiable(z3, &g.polys, &g.conds) else {
        return Outcome::Skipped("z3 declined");
    };

    // The roster: every facade entry is called by name somewhere in this module,
    // and the two ceiling accessors are called here.
    if oexplain_max_conflict_lits() == 0 || oexplain_max_conflict_roots() == 0 {
        return Divergence::outcome(
            "explain-clause-implied",
            "identity",
            "a declared ceiling is zero, which would refuse every input".to_string(),
            inputs(g),
        );
    }

    // Identity leg: AY's `accepts` vs the oracle's own.
    for c in [
        OISignCond::Lt,
        OISignCond::Le,
        OISignCond::Eq,
        OISignCond::Ne,
        OISignCond::Ge,
        OISignCond::Gt,
    ] {
        for s in [-1, 0, 1] {
            if c.accepts(s) != oracle_accepts(c, s) {
                return Divergence::outcome(
                    "explain-clause-implied",
                    "identity",
                    format!(
                        "AY's accepts({}, {s}) = {}, the oracle's = {}",
                        cond_name(c),
                        c.accepts(s),
                        oracle_accepts(c, s)
                    ),
                    inputs(g),
                );
            }
        }
    }

    // The main leg. Every input is under the declared ceilings and z3 answered,
    // so `None` here is a REFUSAL WHERE THE VALUE IS DOCUMENTED TOTAL, and that
    // is a divergence, not a decline.
    let Some(mut ay_valid) = oexplain_clause_is_valid(&lits) else {
        return Divergence::outcome(
            "explain-clause-implied",
            "z3",
            format!(
                "AY declined a conflict of {} literals with {} total roots, both under the \
                 declared ceilings ({} lits, {} roots); z3 decided it (satisfiable = {z3_sat})",
                lits.len(),
                lits.iter().map(|l| l.roots.len()).sum::<usize>(),
                oexplain_max_conflict_lits(),
                oexplain_max_conflict_roots(),
            ),
            inputs(g),
        );
    };
    if sab.on() {
        ay_valid = !ay_valid;
    }

    if ay_valid == z3_sat {
        let detail = if ay_valid {
            "AY says the clause is IMPLIED, but z3 found a real point satisfying every cited \
             literal -- this clause would prune a satisfiable region and produce a WRONG unsat"
                .to_string()
        } else {
            "AY says the clause is NOT implied, but z3 found no satisfying cell -- AY is \
             refusing a sound explanation (completeness loss, not unsoundness)"
                .to_string()
        };
        return Divergence::outcome("explain-clause-implied", "z3", detail, inputs(g));
    }

    let mut comparisons = 1 + 18;

    match check_literal_ceiling(&lits, g) {
        Ok(count) => comparisons += count,
        Err(outcome) => return outcome,
    }
    match check_root_list_guards(&lits, g) {
        Ok(count) => comparisons += count,
        Err(outcome) => return outcome,
    }

    Outcome::Match(comparisons)
}
