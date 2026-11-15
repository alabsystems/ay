//! Proved normalization: merge like terms, cancel `x` against `~x`, flip
//! negative coefficients, drop zeros — with the degree bookkeeping done in
//! the domain's exact width ([`CoeffDomain::Exact`]) so it cannot wrap.
//!
//! Every item mirrors a definition or theorem in `clean/veripb_kernel.lean`:
//!
//! | Rust | Clean |
//! |---|---|
//! | [`normalize`] | `VeriPbCore.normC` |
//! | the merge loop in [`normalize`] | `VeriPbCore.normIns` / `VeriPbCore.insTerm` |
//! | the flip/drop loop in [`normalize`] | `VeriPbCore.flipDrop` |
//! | soundness (both directions) | `VeriPbCore.holds_normC_of_holds` / `VeriPbCore.holds_of_holds_normC` |
//! | output nonnegativity | `VeriPbCore.normC_nonneg` |
//! | formula-level transfer | `VeriPbCore.unsat_of_normF_unsat` / `VeriPbCore.holdsAll_of_holdsAll_normF` |
//!
//! This is the structural fix for the wrap-prone degree arithmetic in the
//! live normalizer (upstream wrong-verdict defects 3, 6 and 7 all lived in
//! exactly this bookkeeping): here the merged coefficients and the degree
//! shift are computed in the exact width, which is `i128` for the narrow
//! [`Coeff`](crate::Coeff) domain (exact for every input the checker can hold
//! there: at most `u32::MAX` terms with `i64` coefficients) and unbounded for
//! [`Big`](crate::Big), and the final narrowing back into storage is guarded,
//! so an unrepresentable result refuses to normalize instead of wrapping. At
//! the `Big` domain the narrowing cannot fail, so `normalize` there is
//! `normC` with nothing added.
//!
//! The term *order* of the output is pinned to what the Clean definition
//! computes (`normIns` folds from the right, appending fresh variables at the
//! end; `flipDrop` preserves order), so the kernel-evaluated `ctrl_norm_*`
//! theorems and the unit tests below agree literal-for-literal.
//!
//! ## The indexed merge pass computes the identical function
//!
//! Clean `insTerm` is *first-match-by-var merge, else append*. Because an
//! append happens only after a full no-match scan, the accumulator holds at
//! most one entry per variable at every point of the fold; the first match
//! by variable is therefore the *unique* match. On wide inputs the merge
//! pass keeps a `HashMap<u32, usize>` (variable → accumulator slot) beside
//! the accumulator `Vec` and dispatches each term through it: the map lookup
//! finds exactly the slot the proved linear search finds, so — just as
//! `rup.rs` computes `memB` through a set — the map is an *index for the
//! proved search*, not a new algorithm. Fold order (`rev()`), the exact
//! merge arithmetic, the cancellation delta, and the flip/drop pass are
//! shared verbatim between both dispatch strategies, so both compute
//! `normC` literal-for-literal.
//!
//! That is pinned by a randomized equivalence test against an oracle
//! transcribed *from the Clean definitions* — `insTerm` / `insSt` / `normIns`
//! / `flipDrop` / `normC`, one Rust `fn` each — rather than from `normalize`.
//! The distinction is the whole value of the oracle: one written by deleting a
//! branch from `normalize` shares its bugs, and measurably did. See
//! `normalize_oracle` below.

// The repo-wide clippy policy prefers `ahash` over std's hash collections,
// but the proved kernel keeps its dependency list to the one integer type it
// is instantiated at (see the crate docs), so the merge index uses std's
// `HashMap`. The hasher choice cannot affect the slot the lookup finds —
// only its constant factor.
#![allow(clippy::disallowed_types)]

use std::collections::HashMap;

use crate::{CoeffDomain, Constraint, Exact, GuardError, Lit, Term};

/// Below this input width the merge pass uses the plain linear `ins_term`
/// scan: on narrow constraints (the overwhelmingly common case) the linear
/// scan is faster than hashing, and both strategies compute the same
/// function, so the cutoff is purely a performance knob.
const INDEXED_MERGE_THRESHOLD: usize = 32;

/// One accumulator entry during the merge pass, held at the exact width.
#[derive(Clone)]
struct WideTerm<E> {
    coeff: E,
    lit: Lit,
}

/// Mirrors `VeriPbCore.insTerm`: merge one term into the accumulator by
/// variable. Returns the cancellation delta (`t.coeff` when `t` met its
/// opposite literal, else `0`); the caller subtracts the accumulated deltas
/// from the degree at the end.
fn ins_term<E: Exact>(t: WideTerm<E>, acc: &mut Vec<WideTerm<E>>) -> Result<E, GuardError> {
    for u in acc.iter_mut() {
        if u.lit.var == t.lit.var {
            if u.lit.negated == t.lit.negated {
                u.coeff = u
                    .coeff
                    .checked_add(&t.coeff)
                    .ok_or(GuardError::CoeffOverflow)?;
                return Ok(E::zero());
            }
            u.coeff = u
                .coeff
                .checked_sub(&t.coeff)
                .ok_or(GuardError::CoeffOverflow)?;
            return Ok(t.coeff);
        }
    }
    acc.push(t);
    Ok(E::zero())
}

/// `ins_term` with the first-match-by-var search answered by an index map
/// (variable → accumulator slot) instead of a linear scan.
///
/// This computes the identical function: the accumulator holds at most one
/// entry per variable (an entry is appended only after `ins_term`'s scan
/// found no match, and this dispatch preserves that invariant — a variable
/// is inserted into the map exactly when its entry is pushed), so the slot
/// the map returns is the one and only slot the linear scan would find. The
/// merge arithmetic on that slot is `ins_term`'s, verbatim. Entries are
/// never removed: a merged-to-zero coefficient stays in `acc` (and in the
/// map) until the flip/drop pass, exactly as under the linear scan.
///
/// The slot is taken through [`Vec::get_mut`], not `acc[i]`. Both spell the
/// same access — the invariant above says the slot is always in range — but
/// the index raises a bounds obligation that CANNOT be discharged: `i` comes
/// out of an opaque `HashMap::get`, so nothing in this body relates it to
/// `acc.len()`. That is not a gap in the encoding; the fact genuinely does
/// not exist here, because it is a property of the map's contents held across
/// calls. The `None` arm is therefore unreachable, and it falls back to the
/// proved linear [`ins_term`] rather than to anything weaker: in the state
/// that cannot occur, the function still computes `insTerm` from the
/// accumulator alone.
fn ins_term_indexed<E: Exact>(
    t: WideTerm<E>,
    acc: &mut Vec<WideTerm<E>>,
    slot_by_var: &mut HashMap<u32, usize>,
) -> Result<E, GuardError> {
    if let Some(i) = slot_by_var.get(&t.lit.var).copied() {
        // Explicit length test rather than `.get_mut(i)`; see `Db::get`.
        if i < acc.len() {
            let u = &mut acc[i];
            if u.lit.negated == t.lit.negated {
                u.coeff = u
                    .coeff
                    .checked_add(&t.coeff)
                    .ok_or(GuardError::CoeffOverflow)?;
                return Ok(E::zero());
            }
            u.coeff = u
                .coeff
                .checked_sub(&t.coeff)
                .ok_or(GuardError::CoeffOverflow)?;
            return Ok(t.coeff);
        }
        // Unreachable under the map/accumulator invariant above.
        return ins_term(t, acc);
    }
    slot_by_var.insert(t.lit.var, acc.len());
    acc.push(t);
    Ok(E::zero())
}

/// Normalize a constraint. Mirrors `VeriPbCore.normC`.
///
/// The result has at most one term per variable, every coefficient positive,
/// and a degree shifted by the exact cancellation total. It is semantically
/// equivalent to the input under every assignment (`holds_normC_of_holds` /
/// `holds_of_holds_normC`), and its terms are all nonnegative
/// (`normC_nonneg`), which is what SATURATE and the RUP slack machinery
/// require.
///
/// Fails closed with a [`GuardError`] if a merged coefficient or the shifted
/// degree does not fit the domain — which, at [`Big`](crate::Big), is never.
/// The merge arithmetic is CHECKED, and that is a deliberate change of
/// posture rather than a defensive habit.
///
/// It runs at the EXACT width, so at [`Coeff`](crate::Coeff) an accumulated
/// coefficient is bounded by (term count) x `i64::MAX`, which for the at-most
/// `u32::MAX` terms this crate can hold is below `2^95` and cannot overflow
/// `i128`. That reasoning is correct and it is exactly the problem: it lives
/// in this comment, not in the code, so the verifier could only report the
/// additions as unproved -- and it did, as eighteen of the crate's
/// twenty-eight failing obligations. Its own diagnosis said as much, that the
/// counterexample "does not establish the original violation is reachable".
///
/// Checking costs nothing observable. At `Coeff` the `checked_*` calls return
/// `Some` on every input the checker can construct, and at
/// [`Big`](crate::Big) they always do, so behaviour is identical wherever the
/// unchecked form was defined. What changes is the pathological case: it is
/// REFUSED as `CoeffOverflow` instead of wrapping, which is the same posture
/// [`crate::add`] and the guards already take, and the obligation disappears
/// rather than standing as an unproved claim about an invariant nothing
/// states.
pub fn normalize<C: CoeffDomain>(c: &Constraint<C>) -> Result<Constraint<C>, GuardError> {
    // Merge pass: `normIns` folds the list from the right. Narrow inputs use
    // the plain linear `ins_term`; wide inputs answer the same first-match-
    // by-var search through an index map (see the module header — both
    // dispatch strategies compute the identical accumulator and delta).
    let mut acc: Vec<WideTerm<C::Exact>> = Vec::new();
    let mut delta = <C::Exact as Exact>::zero();
    if c.terms.len() < INDEXED_MERGE_THRESHOLD {
        for t in c.terms.iter().rev() {
            let d = ins_term(
                WideTerm {
                    coeff: t.coeff.widen(),
                    lit: t.lit,
                },
                &mut acc,
            )?;
            delta = delta.checked_add(&d).ok_or(GuardError::CoeffOverflow)?;
        }
    } else {
        let mut slot_by_var: HashMap<u32, usize> = HashMap::with_capacity(c.terms.len());
        for t in c.terms.iter().rev() {
            let d = ins_term_indexed(
                WideTerm {
                    coeff: t.coeff.widen(),
                    lit: t.lit,
                },
                &mut acc,
                &mut slot_by_var,
            )?;
            delta = delta.checked_add(&d).ok_or(GuardError::CoeffOverflow)?;
        }
    }

    // Flip/drop pass: `flipDrop`.
    let mut terms: Vec<Term<C>> = Vec::with_capacity(acc.len());
    for u in acc {
        if u.coeff.is_positive() {
            let coeff = C::narrow(&u.coeff).ok_or(GuardError::CoeffOverflow)?;
            terms.push(Term { coeff, lit: u.lit });
        } else if u.coeff.is_negative() {
            let coeff = C::narrow(&u.coeff.neg()).ok_or(GuardError::CoeffOverflow)?;
            terms.push(Term {
                coeff,
                lit: u.lit.negate(),
            });
            delta = delta
                .checked_add(&u.coeff)
                .ok_or(GuardError::CoeffOverflow)?;
        }
        // coeff == 0: dropped, no delta.
    }

    let degree = C::narrow(&c.degree.widen().sub(&delta)).ok_or(GuardError::DegreeOverflow)?;
    Ok(Constraint { terms, degree })
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{Big, Wide};

    fn x() -> Lit {
        Lit::pos(0)
    }

    /// One accumulator entry of the oracle. Its own type, not [`WideTerm`]:
    /// the oracle shares no state, no helper and no loop with `normalize`.
    #[derive(Clone)]
    struct ONormTerm<E> {
        coeff: E,
        lit: Lit,
    }

    /// `VeriPbCore.NormSt`: a term list paired with the delta accumulated
    /// while producing it.
    struct ONormSt<E> {
        ts: Vec<ONormTerm<E>>,
        delta: E,
    }

    /// `VeriPbCore.consSt u s = { ts := u :: s.ts, delta := s.delta }`.
    fn o_cons_st<E: Exact>(u: ONormTerm<E>, s: ONormSt<E>) -> ONormSt<E> {
        let mut ts = vec![u];
        ts.extend(s.ts);
        ONormSt { ts, delta: s.delta }
    }

    /// `VeriPbCore.insTerm` (`clean/veripb_kernel.lean`), clause for clause.
    fn o_ins_term<E: Exact>(t: ONormTerm<E>, ts: &[ONormTerm<E>]) -> ONormSt<E> {
        // | [] => { ts := [t], delta := 0 }
        let Some((u, rest)) = ts.split_first() else {
            return ONormSt {
                ts: vec![t],
                delta: E::zero(),
            };
        };
        // | u :: rest => match Nat.beq u.lit.var t.lit.var with
        if u.lit.var != t.lit.var {
            //   | false => consSt u (insTerm t rest)
            return o_cons_st(u.clone(), o_ins_term(t, rest));
        }
        //   | true => match boolEqB u.lit.negated t.lit.negated with
        let mut ts = Vec::with_capacity(1 + rest.len());
        if u.lit.negated == t.lit.negated {
            //     | true  => { ts := { coeff := u.coeff + t.coeff, lit := u.lit } :: rest,
            //                  delta := 0 }
            ts.push(ONormTerm {
                coeff: u.coeff.add(&t.coeff),
                lit: u.lit,
            });
            ts.extend_from_slice(rest);
            ONormSt {
                ts,
                delta: E::zero(),
            }
        } else {
            //     | false => { ts := { coeff := u.coeff - t.coeff, lit := u.lit } :: rest,
            //                  delta := t.coeff }
            ts.push(ONormTerm {
                coeff: u.coeff.sub(&t.coeff),
                lit: u.lit,
            });
            ts.extend_from_slice(rest);
            ONormSt { ts, delta: t.coeff }
        }
    }

    /// `VeriPbCore.insSt t s =
    /// { ts := (insTerm t s.ts).ts, delta := s.delta + (insTerm t s.ts).delta }`.
    fn o_ins_st<E: Exact>(t: ONormTerm<E>, s: ONormSt<E>) -> ONormSt<E> {
        let r = o_ins_term(t, &s.ts);
        ONormSt {
            ts: r.ts,
            delta: s.delta.add(&r.delta),
        }
    }

    /// `VeriPbCore.normIns`: `[] => { [], 0 }`,
    /// `t :: rest => insSt t (normIns rest)`.
    ///
    /// Structural recursion on the tail, which is what makes this a *right*
    /// fold. `normalize` gets the same order out of a `rev()` loop instead.
    fn o_norm_ins<E: Exact>(ts: &[ONormTerm<E>]) -> ONormSt<E> {
        match ts.split_first() {
            None => ONormSt {
                ts: Vec::new(),
                delta: E::zero(),
            },
            Some((t, rest)) => o_ins_st(t.clone(), o_norm_ins(rest)),
        }
    }

    /// `VeriPbCore.flipDrop`, clause for clause.
    fn o_flip_drop<E: Exact>(ts: &[ONormTerm<E>]) -> ONormSt<E> {
        // | [] => { ts := [], delta := 0 }
        let Some((t, rest)) = ts.split_first() else {
            return ONormSt {
                ts: Vec::new(),
                delta: E::zero(),
            };
        };
        // match Int.ble t.coeff 0 with
        //   | false => consSt t (flipDrop rest)            -- kept, in place
        if t.coeff > E::zero() {
            return o_cons_st(t.clone(), o_flip_drop(rest));
        }
        //   | true  => match Int.ble 0 t.coeff with
        //     | true  => flipDrop rest                     -- coeff = 0, dropped
        if E::zero() <= t.coeff {
            return o_flip_drop(rest);
        }
        //     | false => { ts := { coeff := Int.neg t.coeff, lit := negLit t.lit }
        //                          :: (flipDrop rest).ts,
        //                  delta := t.coeff + (flipDrop rest).delta }
        let r = o_flip_drop(rest);
        let mut ts = Vec::with_capacity(1 + r.ts.len());
        ts.push(ONormTerm {
            coeff: t.coeff.neg(),
            lit: t.lit.negate(),
        });
        ts.extend(r.ts);
        ONormSt {
            ts,
            delta: t.coeff.add(&r.delta),
        }
    }

    /// **An independent transcription of the Clean definitions**, and the
    /// oracle the randomized equivalence test holds [`normalize`] against.
    ///
    /// The oracle this replaced was `normalize` with one branch deleted: it
    /// called the same [`ins_term`], and it carried the flip/drop pass and
    /// the degree arithmetic *verbatim* from the production body. Only the
    /// merge dispatch differed, so the equivalence test could see a
    /// divergence between the two dispatch strategies and nothing else — a
    /// wrong sign in the flip delta, or a reversed output order, sat in both
    /// copies at once and the test stayed green. Both were measured: with the
    /// old oracle, `delta.add(&u.coeff)` changed to `.sub(&u.coeff)` in both
    /// copies left this test passing, and a `terms.reverse()` in both copies
    /// left the *whole crate's* test suite passing, silently changing the
    /// term order `normC` is proved to compute.
    ///
    /// So this one is transcribed from `clean/veripb_kernel.lean` rather than
    /// from the function it checks, and the transcription is deliberately
    /// literal: one Rust `fn` per Clean `def`, structural recursion where
    /// Clean recurses, the Clean clause quoted above the code implementing
    /// it, its own term type, and the degree assembled the way `normC`
    /// spells it — `c.degree - (normIns.delta + flipDrop.delta)` — rather
    /// than the way `normalize` accumulates it, as one running delta across
    /// both passes. Nothing but [`Exact`] / [`CoeffDomain`], the integer
    /// arithmetic itself, is shared with the code under test.
    ///
    /// The guarded narrowing at the end is the one part with no Clean
    /// counterpart: `normC` is over unbounded `Int`. It is applied in output
    /// order and to the degree last, so the two agree on *which*
    /// [`GuardError`] a too-wide input produces and the test can assert full
    /// `Result` equality.
    fn normalize_oracle<C: CoeffDomain>(c: &Constraint<C>) -> Result<Constraint<C>, GuardError> {
        let input: Vec<ONormTerm<C::Exact>> = c
            .terms
            .iter()
            .map(|t| ONormTerm {
                coeff: t.coeff.widen(),
                lit: t.lit,
            })
            .collect();
        // normC c = { terms := (flipDrop (normIns c.terms).ts).ts,
        //             degree := c.degree - ((normIns c.terms).delta
        //                                    + (flipDrop (normIns c.terms).ts).delta) }
        let merged = o_norm_ins(&input);
        let flipped = o_flip_drop(&merged.ts);

        let mut terms: Vec<Term<C>> = Vec::with_capacity(flipped.ts.len());
        for u in &flipped.ts {
            terms.push(Term {
                coeff: C::narrow(&u.coeff).ok_or(GuardError::CoeffOverflow)?,
                lit: u.lit,
            });
        }
        let shift = merged.delta.add(&flipped.delta);
        let degree = C::narrow(&c.degree.widen().sub(&shift)).ok_or(GuardError::DegreeOverflow)?;
        Ok(Constraint { terms, degree })
    }

    /// A tiny deterministic xorshift PRNG so the equivalence test needs no
    /// dependencies and reproduces exactly.
    struct XorShift(u64);
    impl XorShift {
        fn next(&mut self) -> u64 {
            let mut s = self.0;
            s ^= s << 13;
            s ^= s >> 7;
            s ^= s << 17;
            self.0 = s;
            s
        }
        fn below(&mut self, n: u64) -> u64 {
            self.next() % n
        }
    }

    #[test]
    fn normalize_matches_the_clean_transcription_oracle_on_randomized_inputs() {
        let mut rng = XorShift(0x5eed_cafe_f00d_1234);
        let mut accepted = 0usize;
        let mut refused = 0usize;
        for case in 0..2000 {
            // Two regimes, because one was not enough. Drawing an extreme
            // coefficient with probability 3/10 across a width of up to three
            // times the merge threshold means almost every case contains an
            // extreme somewhere, and almost every case therefore overflows:
            // only 218 of 2000 used to reach `Ok`, so 89% of the comparisons
            // below were `Err` against `Err` and said nothing about the
            // computed value. A quarter of cases still stress the guards; the
            // rest stay well inside the width, where the oracle is comparing
            // constraints rather than error codes. The floors at the end of
            // this test are what keep that true.
            let stress = rng.below(4) == 0;
            // Small variable range forces heavy merge/cancel collisions;
            // widths straddle the indexed-merge threshold so both dispatch
            // strategies are exercised.
            let width = if stress {
                rng.below(3 * INDEXED_MERGE_THRESHOLD as u64) as usize
            } else {
                rng.below(2 * INDEXED_MERGE_THRESHOLD as u64) as usize
            };
            let var_range = 1 + rng.below(8) as u32;
            let mut terms = Vec::with_capacity(width);
            for _ in 0..width {
                let var = rng.below(u64::from(var_range)) as u32;
                let lit = if rng.below(2) == 0 {
                    Lit::pos(var)
                } else {
                    Lit::neg(var)
                };
                // Mixed magnitudes, signs and zeros throughout; the extremes
                // that make the overflow guards fire only in the stress
                // regime.
                let coeff: i64 = match (stress, rng.below(10)) {
                    (_, 0) => 0,
                    (true, 1) => i64::MAX - rng.below(3) as i64,
                    (true, 2) => i64::MIN + rng.below(3) as i64,
                    _ => rng.below(2001) as i64 - 1000,
                };
                terms.push(Term { coeff, lit });
            }
            let degree: i64 = match (stress, rng.below(8)) {
                (true, 0) => i64::MAX - rng.below(3) as i64,
                (true, 1) => i64::MIN + rng.below(3) as i64,
                _ => rng.below(2001) as i64 - 1000,
            };
            let c = Constraint::new(terms, degree);
            let expected = normalize_oracle(&c);
            let got = normalize(&c);
            // Full equality: terms in identical order, identical degree, or
            // the identical GuardError.
            assert_eq!(got, expected, "case {case}: input {c:?}");
            if got.is_ok() {
                accepted += 1;
            } else {
                refused += 1;
            }

            // The same input at the complete domain: it must never fail, and
            // wherever the narrow domain *did* succeed it must agree with it
            // value for value. That is the whole relationship between the two
            // instantiations, checked on every generated case.
            let wide = Constraint::new(
                c.terms
                    .iter()
                    .map(|t| Term {
                        coeff: Big::from(t.coeff),
                        lit: t.lit,
                    })
                    .collect(),
                Big::from(c.degree),
            );
            let wide_out = normalize(&wide).expect("the complete domain cannot fail on width");
            if let Ok(narrow_out) = &got {
                assert_eq!(wide_out.degree, Big::from(narrow_out.degree), "case {case}");
                assert_eq!(
                    wide_out.terms,
                    narrow_out
                        .terms
                        .iter()
                        .map(|t| Term {
                            coeff: Big::from(t.coeff),
                            lit: t.lit
                        })
                        .collect::<Vec<_>>(),
                    "case {case}"
                );
            }
        }

        // Floors on both outcomes. An `Err` compared against an `Err` agrees
        // about a *refusal*, not about a normalized constraint, so a generator
        // that drifts back to overflowing almost everything would leave this
        // test green while checking almost nothing — which is what it was
        // doing. The refusal floor is here for the same reason in the other
        // direction: the guards are half of what this oracle is for.
        assert!(
            accepted > 800,
            "only {accepted} of 2000 cases normalized successfully, so most of \
             this test compared one `Err` against another and said nothing \
             about the value computed"
        );
        assert!(
            refused > 200,
            "only {refused} of 2000 cases hit a width guard, so the guard half \
             of the oracle is barely exercised"
        );
    }

    #[test]
    fn wide_input_exercises_the_indexed_merge_deterministically() {
        // 3 * threshold terms over few variables: guaranteed map dispatch,
        // guaranteed merges and cancellations.
        let n = 3 * INDEXED_MERGE_THRESHOLD;
        let terms: Vec<Term> = (0..n)
            .map(|i| Term {
                coeff: (i as i64 % 7) - 3,
                lit: if i % 2 == 0 {
                    Lit::pos((i % 5) as u32)
                } else {
                    Lit::neg((i % 5) as u32)
                },
            })
            .collect();
        let c = Constraint::new(terms, 42);
        assert_eq!(normalize(&c), normalize_oracle(&c));
    }

    #[test]
    fn merge_matches_clean_control() {
        // Mirrors VeriPbCore.ctrl_norm_merge_terms and
        // VeriPbCore.ctrl_norm_merge_degree: 2x + 3x >= 4  =>  5x >= 4.
        let c = Constraint::new(
            vec![Term { coeff: 2, lit: x() }, Term { coeff: 3, lit: x() }],
            4,
        );
        let n = normalize(&c).unwrap();
        assert_eq!(n.terms, vec![Term { coeff: 5, lit: x() }]);
        assert_eq!(n.degree, 4);
    }

    #[test]
    fn cancel_matches_clean_control() {
        // Mirrors VeriPbCore.ctrl_norm_cancel_terms and
        // VeriPbCore.ctrl_norm_cancel_degree: x + ~x >= 1  =>  0 >= 0.
        // (Upstream defect 7 wrapped exactly this bookkeeping near i64::MIN.)
        let c = Constraint::new(
            vec![
                Term { coeff: 1, lit: x() },
                Term {
                    coeff: 1,
                    lit: x().negate(),
                },
            ],
            1,
        );
        let n = normalize(&c).unwrap();
        assert!(n.terms.is_empty());
        assert_eq!(n.degree, 0);
    }

    #[test]
    fn flip_matches_clean_control() {
        // Mirrors VeriPbCore.ctrl_norm_flip_terms and
        // VeriPbCore.ctrl_norm_flip_degree: -2x >= 1  =>  2~x >= 3.
        let c = Constraint::new(
            vec![Term {
                coeff: -2,
                lit: x(),
            }],
            1,
        );
        let n = normalize(&c).unwrap();
        assert_eq!(
            n.terms,
            vec![Term {
                coeff: 2,
                lit: x().negate()
            }]
        );
        assert_eq!(n.degree, 3);
    }

    #[test]
    fn normalized_output_is_normalized() {
        let c = Constraint::new(
            vec![
                Term {
                    coeff: -7,
                    lit: Lit::pos(1),
                },
                Term {
                    coeff: 3,
                    lit: Lit::neg(2),
                },
                Term {
                    coeff: 4,
                    lit: Lit::pos(1),
                },
                Term {
                    coeff: -3,
                    lit: Lit::neg(2),
                },
            ],
            2,
        );
        let n = normalize(&c).unwrap();
        for t in &n.terms {
            assert!(t.coeff > 0);
        }
        // Semantic spot-check under all four assignments of vars 1, 2.
        for v1 in [false, true] {
            for v2 in [false, true] {
                let a = move |v: u32| if v == 1 { v1 } else { v2 };
                assert_eq!(c.holds(&a), n.holds(&a));
            }
        }
    }

    #[test]
    fn wrap_prone_cancellation_fails_closed_instead_of_wrapping() {
        // 1x + 1~x >= i64::MIN: the cancellation shifts the degree to
        // i64::MIN - 1, which does not fit. Upstream (defect 7's shape) this
        // wrapped silently; the guarded kernel refuses to produce anything.
        let c = Constraint::new(
            vec![
                Term { coeff: 1, lit: x() },
                Term {
                    coeff: 1,
                    lit: x().negate(),
                },
            ],
            i64::MIN,
        );
        assert_eq!(normalize(&c), Err(GuardError::DegreeOverflow));
    }

    #[test]
    fn degree_shift_overflow_is_refused() {
        // Flipping -1 * x shifts the degree by +1; at i64::MAX that leaves
        // the representable range and must fail closed.
        let c = Constraint::new(
            vec![Term {
                coeff: -1,
                lit: x(),
            }],
            i64::MAX,
        );
        assert_eq!(normalize(&c), Err(GuardError::DegreeOverflow));
    }

    /// The complete domain *computes* the two cases above instead of
    /// refusing them, and computes the value the wrap would have destroyed.
    /// This is the whole point of the second instantiation: the same
    /// `normC`, one width up, so the bridge can compare against the live
    /// checker rather than stand down.
    #[test]
    fn the_complete_domain_normalizes_where_the_narrow_one_refuses() {
        let c = Constraint::new(
            vec![
                Term {
                    coeff: Big::from(1),
                    lit: x(),
                },
                Term {
                    coeff: Big::from(1),
                    lit: x().negate(),
                },
            ],
            Big::from(i64::MIN),
        );
        let n = normalize(&c).unwrap();
        assert!(n.terms.is_empty());
        assert_eq!(n.degree, Big::from(i64::MIN) - Big::from(1));
        assert_ne!(
            n.degree,
            Big::from(i64::MAX),
            "the wrap the narrow guard prevents"
        );

        let c = Constraint::new(
            vec![Term {
                coeff: Big::from(-1),
                lit: x(),
            }],
            Big::from(i64::MAX),
        );
        let n = normalize(&c).unwrap();
        assert_eq!(
            n.terms,
            vec![Term {
                coeff: Big::from(1),
                lit: x().negate()
            }]
        );
        assert_eq!(n.degree, Big::from(i64::MAX) + Big::from(1));
    }

    /// A merged coefficient far above `i64`: the narrow domain refuses, the
    /// complete one merges exactly.
    #[test]
    fn merges_beyond_i64_are_exact_at_the_complete_domain() {
        let half = Big::from(u64::MAX);
        let c = Constraint::new(
            vec![
                Term {
                    coeff: half.clone(),
                    lit: x(),
                },
                Term {
                    coeff: half.clone(),
                    lit: x(),
                },
            ],
            Big::from(0),
        );
        let n = normalize(&c).unwrap();
        assert_eq!(
            n.terms,
            vec![Term {
                coeff: half.clone() * Big::from(2),
                lit: x()
            }]
        );

        let narrow = Constraint::new(
            vec![
                Term {
                    coeff: Wide::from(i64::MAX) as i64,
                    lit: x(),
                },
                Term {
                    coeff: i64::MAX,
                    lit: x(),
                },
            ],
            0,
        );
        assert_eq!(normalize(&narrow), Err(GuardError::CoeffOverflow));
    }
}
