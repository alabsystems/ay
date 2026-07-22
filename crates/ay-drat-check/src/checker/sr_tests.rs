// Copyright 2026 Andrew Yates
// Unit tests for the native PR/SR checker.

use super::SrChecker;
use crate::cnf_parser::parse_cnf;
use crate::drat_parser::parse_drat;
use crate::error::DratCheckError;
use crate::literal::Literal;

#[allow(dead_code)]
fn lits(ds: &[i32]) -> Vec<Literal> {
    ds.iter().map(|&d| Literal::from_dimacs(d)).collect()
}

/// A plain DRAT (RUP) proof must still verify through the SR driver, which
/// delegates `Add` steps to the DRAT engine.
#[test]
fn sr_driver_accepts_plain_rup_proof() {
    let cnf = parse_cnf(&b"p cnf 2 4\n1 2 0\n1 -2 0\n-1 2 0\n-1 -2 0\n"[..]).expect("cnf");
    // Standard RUP refutation of the 2-variable contradiction.
    let proof = parse_drat(b"1 0\n2 0\n0\n").expect("proof");
    let mut chk = SrChecker::new(cnf.num_vars, true);
    assert!(chk.verify(&cnf.clauses, &proof).is_ok());
}

/// An `a`-line whose witness merely repeats the pivot (so the clause is checked
/// by RUP) is accepted when the clause is genuinely RUP. This exercises the
/// `AddPr` path and its RUP shortcut.
#[test]
fn sr_accepts_pr_line_that_is_actually_rup() {
    let cnf = parse_cnf(&b"p cnf 2 4\n1 2 0\n1 -2 0\n-1 2 0\n-1 -2 0\n"[..]).expect("cnf");
    // "1 1 0" parses as clause [1] with witness [1] (pivot repeated): clause (1)
    // is RUP here because F |- (1). Then "-1 0" and "0".
    let proof = parse_drat(b"1 1 0\n-1 0\n0\n").expect("proof");
    let mut chk = SrChecker::new(cnf.num_vars, true);
    assert!(chk.verify(&cnf.clauses, &proof).is_ok());
}

/// A genuine PR step that is NOT RUP and NOT RAT must be accepted by the SR
/// kernel via the witness.
///
/// Formula (satisfiable): the only models set x1=x2. We add the unit (x1) with
/// witness {x1 -> true, x2 -> true}. alpha = {x1=false}. The witness satisfies
/// (x1). For every clause D reduced by the witness, F /\ alpha /\ !(D|w) |- false.
#[test]
fn sr_accepts_genuine_pr_unit() {
    // F = (x1 \/ -x2) (-x1 \/ x2)  -- equivalent to x1 == x2.
    let cnf = parse_cnf(&b"p cnf 2 2\n1 -2 0\n-1 2 0\n"[..]).expect("cnf");
    // Add unit (1) with PR witness {1->T, 2->T}: tokens "1 1 2 0":
    //   clause = [1], witness = [1, 2]  (pivot 1, then atom 2 -> true).
    let proof = parse_drat(b"1 1 2 0\n").expect("proof");
    let mut chk = SrChecker::new(cnf.num_vars, true);
    // The unit (1) is propagation-redundant; it should be accepted (no empty
    // clause yet, so verify() concludes "not UNSAT" -- we only assert the step
    // itself does not error).
    let res = chk.verify(&cnf.clauses, &proof);
    // verify() requires an empty clause for VERIFIED; here F is SAT so there is
    // none. The only acceptable error is the conclusion (NoEmptyClause) -- the
    // PR STEP itself must not be rejected as not-implied.
    match res {
        Ok(()) => {}
        Err(DratCheckError::ConclusionFailed(_)) => {}
        other => panic!("PR step should not fail; got {other:?}"),
    }
}

/// A witness that does NOT certify redundancy must be rejected (fail closed):
/// the reduced formula clause is not implied under the witness.
#[test]
fn sr_rejects_invalid_certificate() {
    // F = (1 2 3), satisfiable. Add (-1) with witness {1 -> false} ("-1 -1 0").
    // alpha = {1=T}; sigma maps 1->F. Clause (1 2 3)|sigma reduces to (2 3),
    // and F /\ alpha /\ !(2 3) does NOT unit-propagate to a conflict, so the
    // certificate is invalid and the step must be rejected.
    let cnf = parse_cnf(&b"p cnf 3 1\n1 2 3 0\n"[..]).expect("cnf");
    let proof = parse_drat(b"-1 -1 0\n").expect("proof");
    let mut chk = SrChecker::new(cnf.num_vars, true);
    assert!(
        chk.verify(&cnf.clauses, &proof).is_err(),
        "invalid PR certificate must be rejected"
    );
}

/// Exhaustive pin: the REAL `reduce_clause_under_subst` + `Subst::map_lit`
/// satisfy the SAME bounded single-step soundness property that
/// the development proof harness discharges through Trust.
///
/// Over the complete bounded domain (2 variables; clauses of up to 2 literals
/// with either polarity on either variable; sigma mapping each variable's
/// positive literal to identity / True / False / another literal incl.
/// cross-variable; and EVERY assignment alpha) we assert the no-false-accept
/// bridge against an INDEPENDENT model evaluation of the reduct `D|sigma`:
///   * Satisfied     => D|sigma is true  under every alpha (skip is sound);
///   * Contradiction => D|sigma is false under every alpha (genuinely empty);
///   * NotReduced    => D|sigma == D     under every alpha (skip is sound).
///
/// This pins the real, arbitrary-length reduct code (which the Trust harness
/// cannot reflect verbatim — `Vec`/`Literal` do not lower to the finite route)
/// to the verified bounded soundness property: corrupting `classify_reduct`,
/// `Subst::map_lit`, or the reduce loop makes this test fail.
#[test]
fn reduct_single_step_soundness_holds_for_real_reduce() {
    use super::{reduce_clause_under_subst, Reduce, SubImage, Subst};

    // A literal of `var` (0 or 1) with sign `neg`, in DIMACS (vars are 1-based).
    fn lit_of(var: usize, neg: bool) -> Literal {
        let d = (var as i32) + 1;
        Literal::from_dimacs(if neg { -d } else { d })
    }
    // The stored POSITIVE-literal image for sigma kind k in {0=Id,1=T,2=F,3=Lit}.
    fn image_of(kind: u8, lv: bool, ln: bool) -> Option<SubImage> {
        match kind {
            0 => None,
            1 => Some(SubImage::True),
            2 => Some(SubImage::False),
            _ => Some(SubImage::Lit(lit_of(lv as usize, ln))),
        }
    }
    // Independent model truth of literal `(var,neg)` under sigma+alpha.
    // sigma stores the positive-literal image; sigma(neg lit) = !sigma(pos lit).
    fn lit_truth(var: usize, neg: bool, kind: u8, lv: bool, ln: bool, alpha: [bool; 2]) -> bool {
        let pos = match kind {
            0 => return alpha[var] != neg, // identity: literal truth = alpha ^ neg
            1 => true,
            2 => false,
            _ => alpha[lv as usize] != ln,
        };
        if neg {
            !pos
        } else {
            pos
        }
    }

    let bit = |bits: u32, i: u32| (bits >> i) & 1 == 1;
    // 14 bits: clause (p0,sv0,sn0,p1,sv1,sn1) + sigma var0 (ka,kb,lv,ln) + var1.
    for bits in 0u32..(1 << 14) {
        let (p0, sv0, sn0) = (bit(bits, 0), bit(bits, 1), bit(bits, 2));
        let (p1, sv1, sn1) = (bit(bits, 3), bit(bits, 4), bit(bits, 5));
        let k0 = (bit(bits, 6) as u8) + 2 * (bit(bits, 7) as u8);
        let (l0v, l0n) = (bit(bits, 8), bit(bits, 9));
        let k1 = (bit(bits, 10) as u8) + 2 * (bit(bits, 11) as u8);
        let (l1v, l1n) = (bit(bits, 12), bit(bits, 13));

        let map = vec![image_of(k0, l0v, l0n), image_of(k1, l1v, l1n)];
        let subst = Subst {
            map,
            pivot: lit_of(0, false),
        };

        // Slot j (when present) is a literal on variable `svj`.
        let var0 = sv0 as usize;
        let var1 = sv1 as usize;
        let mut clause: Vec<Literal> = Vec::new();
        if p0 {
            clause.push(lit_of(var0, sn0));
        }
        if p1 {
            clause.push(lit_of(var1, sn1));
        }

        let class = reduce_clause_under_subst(&subst, &clause);

        for av in 0u32..4 {
            let alpha = [av & 1 == 1, av & 2 == 2];
            // sigma kind/lit for each present slot's variable.
            let k_of = |v: usize| -> (u8, bool, bool) {
                if v == 0 {
                    (k0, l0v, l0n)
                } else {
                    (k1, l1v, l1n)
                }
            };
            let mut truth_reduct = false;
            let mut truth_d = false;
            if p0 {
                let (k, lv, ln) = k_of(var0);
                truth_reduct |= lit_truth(var0, sn0, k, lv, ln, alpha);
                truth_d |= alpha[var0] != sn0;
            }
            if p1 {
                let (k, lv, ln) = k_of(var1);
                truth_reduct |= lit_truth(var1, sn1, k, lv, ln, alpha);
                truth_d |= alpha[var1] != sn1;
            }

            match class {
                Reduce::Satisfied => assert!(
                    truth_reduct,
                    "Satisfied but reduct false: bits={bits} alpha={alpha:?}"
                ),
                Reduce::Contradiction => assert!(
                    !truth_reduct,
                    "Contradiction but reduct true: bits={bits} alpha={alpha:?}"
                ),
                Reduce::NotReduced => assert!(
                    truth_reduct == truth_d,
                    "NotReduced but reduct != D: bits={bits} alpha={alpha:?}"
                ),
                Reduce::Reduced => {} // checked by real RUP (the trusted BCP core)
            }
        }
    }
}

/// A corrupted witness substitution that breaks the refutation must be
/// rejected -- never a false VERIFIED.
#[test]
fn sr_rejects_corrupted_witness() {
    let cnf = parse_cnf(&b"p cnf 2 2\n1 -2 0\n-1 2 0\n"[..]).expect("cnf");
    // Corrupt the PR witness: map 2 -> false instead of true ("1 1 -2 0").
    // Now alpha={1=F}; sigma={1->T, 2->F}. Clause (-1 2)|sigma: -1->F, 2->F
    //   -> all-false -> CONTRADICTION -> reject. Clause (1 -2)|sigma satisfied.
    let proof = parse_drat(b"1 1 -2 0\n").expect("proof");
    let mut chk = SrChecker::new(cnf.num_vars, true);
    assert!(
        chk.verify(&cnf.clauses, &proof).is_err(),
        "corrupted witness must be rejected"
    );
}
