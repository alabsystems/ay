// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

// Included by the parent module so the differential checks share one namespace.

// ===========================================================================
// Check 2 — `explain-produce`
// ===========================================================================

/// The producer end to end: **a clause is emitted only for a real conflict, and
/// only when it is genuinely implied.**
///
/// z3 legs: when AY returns a clause, z3 must independently find the cited
/// conjunction UNSATISFIABLE. When z3 finds the full conjunction SATISFIABLE,
/// AY must return nothing at all — emitting a clause there is the wrong-`unsat`
/// defect in its purest form.
/// Identity legs: every cited literal is one of the inputs; the clause literals
/// are exactly the negations of the cited ones; the clause is FALSE under the
/// trail (`oexplain_clause_is_falsified`), which is property (a) of the defining
/// pair; no literal is cited twice.
///
/// A `None` from AY on a genuinely conflicting input is a DECLINE, not a
/// divergence — completeness is allowed to suffer, correctness is not.
fn validate_produced_clause(
    g: &GenEx,
    explanation: &OExplanation,
    trail: &[i32],
    full_is_sat: bool,
    cited_is_sat: bool,
) -> Option<Outcome> {
    if !oexplain_clause_is_falsified(&explanation.lits, trail) {
        return Some(Divergence::outcome(
            "explain-produce",
            "identity",
            format!(
                "clause {:?} is not falsified by the trail {trail:?} -- a clause that is not \
                 false under the current assignment cannot drive a backjump",
                explanation.lits
            ),
            inputs(g),
        ));
    }
    let expected: Vec<i32> = explanation
        .cited
        .iter()
        .map(|&citation| -citation)
        .collect();
    if explanation.lits != expected {
        return Some(Divergence::outcome(
            "explain-produce",
            "identity",
            format!(
                "clause {:?} is not the negation of its citations {:?}",
                explanation.lits, explanation.cited
            ),
            inputs(g),
        ));
    }
    let mut seen = explanation.cited.clone();
    seen.sort_unstable();
    let original_len = seen.len();
    seen.dedup();
    if seen.len() != original_len {
        return Some(Divergence::outcome(
            "explain-produce",
            "identity",
            format!("clause cites a literal twice: {:?}", explanation.cited),
            inputs(g),
        ));
    }
    if full_is_sat && !cited_is_sat {
        return Some(Divergence::outcome(
            "explain-produce",
            "z3",
            "z3 says the full conjunction is satisfiable but a SUBSET of it is not -- \
             impossible, so one of the two z3 queries is being posed wrongly"
                .to_string(),
            inputs(g),
        ));
    }
    None
}

pub(crate) fn check_produce(z3: &Z3, g: &GenEx, sab: Sabotage) -> Outcome {
    if !usable(g) {
        return Outcome::Skipped("degenerate polynomial");
    }
    let Some(lits) = ay_lits(z3, g) else {
        return Outcome::Skipped("z3 declined the root isolation");
    };
    let Some(z3_sat_full) = z3_satisfiable(z3, &g.polys, &g.conds) else {
        return Outcome::Skipped("z3 declined");
    };
    let trail: Vec<i32> = lits.iter().map(|l| l.lit).collect();

    let Some(e) = oexplain_univariate(&lits) else {
        if z3_sat_full {
            // Correct: there is no conflict, so there is nothing to explain.
            return if sab.on() {
                // Nothing was produced, so there is nothing to corrupt. Reporting
                // a Match here would inflate the catch rate's denominator with a
                // case the sabotage never touched.
                Outcome::Skipped("no clause to corrupt")
            } else {
                Outcome::Match(1)
            };
        }
        return Outcome::Declined("no explanation for a genuine conflict");
    };

    // A clause was produced. z3 must agree the cited conjunction is unsat.
    let mut cited = e.cited.clone();
    if sab.on() {
        // Drop one cited literal: the clause AY returns is minimized and
        // irredundant, so any drop leaves a satisfiable conjunction. This is the
        // unsound-minimization defect.
        cited.pop();
    }

    let mut cited_polys = Vec::with_capacity(cited.len());
    let mut cited_conds = Vec::with_capacity(cited.len());
    for c in &cited {
        let Some(l) = lits.iter().find(|l| l.lit == *c) else {
            return Divergence::outcome(
                "explain-produce",
                "identity",
                format!("clause cites literal {c}, which is not on the trail"),
                inputs(g),
            );
        };
        cited_polys.push(l.p.clone());
        cited_conds.push(l.cond);
    }

    let Some(cited_sat) = z3_satisfiable(z3, &cited_polys, &cited_conds) else {
        return Outcome::Skipped("z3 declined the cited conjunction");
    };
    if cited_sat {
        return Divergence::outcome(
            "explain-produce",
            "z3",
            format!(
                "AY learned the clause {:?} from literals {:?}, but z3 found a real point \
                 satisfying every cited literal. The clause is NOT a theory consequence: \
                 learning it prunes a satisfiable region and the search will answer WRONG \
                 UNSAT.",
                e.lits, cited
            ),
            inputs(g),
        );
    }

    if let Some(outcome) = validate_produced_clause(g, &e, &trail, z3_sat_full, cited_sat) {
        return outcome;
    }

    Outcome::Match(5)
}

// ===========================================================================
// Check 3 — `explain-countermodel`
// ===========================================================================

/// The WITNESS, adjudicated rather than the verdict.
///
/// When AY reports a clause is NOT implied it must hand back the real number
/// that refutes it, and z3 must agree that every cited literal holds there. An
/// unwitnessed `false` — a refusal nobody can check — is the campaign's fourth
/// blind-spot pattern, and it is exactly what would let a checker quietly stop
/// finding counterexamples.
///
/// z3 legs: `Z3_algebraic_eval` at AY's witness must satisfy every literal;
/// absence of a witness must coincide with z3 finding the conjunction unsat.
/// Identity leg: a witness is present exactly when `oexplain_clause_is_valid`
/// says `false`, and absent exactly when it says `true`.
fn countermodel_probe(witness: ODyadicAnum, sabotage: Sabotage) -> Result<ODyadicAnum, Outcome> {
    if !sabotage.on() {
        return Ok(witness);
    }
    let Some(rational) = witness.to_rational() else {
        return Err(Outcome::Skipped(
            "irrational witness: cannot displace it exactly",
        ));
    };
    Ok(ODyadicAnum::rational(rational + BigRational::one()))
}

fn absent_countermodel(z3_sat: bool, sabotage: Sabotage, g: &GenEx) -> Outcome {
    if z3_sat {
        return Divergence::outcome(
            "explain-countermodel",
            "z3",
            "AY found no satisfying cell, but z3 did -- AY's decomposition is missing a \
             cell, which makes a satisfiable conjunction look like a conflict"
                .to_string(),
            inputs(g),
        );
    }
    if sabotage.on() {
        Outcome::Skipped("no witness to corrupt")
    } else {
        Outcome::Match(2)
    }
}

pub(crate) fn check_countermodel(z3: &Z3, g: &GenEx, sab: Sabotage) -> Outcome {
    if !usable(g) {
        return Outcome::Skipped("degenerate polynomial");
    }
    let Some(lits) = ay_lits(z3, g) else {
        return Outcome::Skipped("z3 declined the root isolation");
    };
    let Some(z3_sat) = z3_satisfiable(z3, &g.polys, &g.conds) else {
        return Outcome::Skipped("z3 declined");
    };
    let Some(valid) = oexplain_clause_is_valid(&lits) else {
        return Outcome::Declined("validity");
    };
    let Some(cm) = oexplain_countermodel(&lits) else {
        return Outcome::Declined("countermodel");
    };

    // Identity: a witness exists exactly when the clause is not valid.
    if cm.is_some() == valid {
        return Divergence::outcome(
            "explain-countermodel",
            "identity",
            format!(
                "clause_is_valid = {valid} but countermodel present = {} -- the two must be \
                 exact opposites",
                cm.is_some()
            ),
            inputs(g),
        );
    }

    let Some(w) = cm else {
        return absent_countermodel(z3_sat, sab, g);
    };

    // Turn AY's witness into a z3 term and evaluate every literal there.
    // Move a sabotaged witness. Cases where exact displacement is impossible
    // do not inflate the sabotage catch-rate denominator.
    let probe = match countermodel_probe(w, sab) {
        Ok(probe) => probe,
        Err(outcome) => return outcome,
    };
    let Ok(ast) = z3_ast_of(z3, &probe) else {
        return Outcome::Skipped("witness not representable to z3");
    };

    let mut failed: Option<usize> = None;
    for (i, (p, c)) in g.polys.iter().zip(&g.conds).enumerate() {
        let Some(sg) = z3.eval_sign(&rationals(p), ast) else {
            return Outcome::Skipped("z3 declined the sign");
        };
        if !oracle_accepts(*c, sg) {
            failed = Some(i);
            break;
        }
    }
    if z3.errored() {
        return Outcome::Skipped("z3 errored");
    }

    if let Some(i) = failed {
        if sab.on() {
            return Divergence::outcome(
                "explain-countermodel",
                "z3",
                format!("displaced witness fails literal L{}", i + 1),
                inputs(g),
            );
        }
        return Divergence::outcome(
            "explain-countermodel",
            "z3",
            format!(
                "AY's countermodel does NOT satisfy literal L{} -- the witness is fictional, \
                 so the `not implied` verdict rests on nothing",
                i + 1
            ),
            inputs(g),
        );
    }
    if sab.on() {
        // The displacement happened to land somewhere still satisfying. Not
        // evidence either way.
        return Outcome::Skipped("displacement did not leave the satisfying region");
    }
    Outcome::Match(3)
}

/// AY's algebraic number as a z3 term.
fn z3_ast_of(z3: &Z3, a: &ODyadicAnum) -> Result<Ast, ()> {
    if let Some(r) = a.to_rational() {
        return z3.rational(&r).ok_or(());
    }
    let coeffs = rationals(&a.poly_coeffs().ok_or(())?);
    let roots = z3.roots(&coeffs).ok_or(())?;
    let iv = a.interval().ok_or(())?;
    let lo = z3.rational(&iv.lo().to_rational()).ok_or(())?;
    let hi = z3.rational(&iv.hi().to_rational()).ok_or(())?;
    let mut found = None;
    for r in roots {
        if z3.gt(r, lo).ok_or(())? && z3.lt(r, hi).ok_or(())? {
            if found.is_some() {
                return Err(());
            }
            found = Some(r);
        }
    }
    found.ok_or(())
}
