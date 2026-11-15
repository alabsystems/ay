//! Witness substitution — the Rust image of the kernel's `substC`.
//!
//! This is what redundance-based strengthening (`red`) needs, and the reason
//! it is worth building: `red` is by a wide margin the largest hole in the
//! checker's end-to-end coverage. Over the accepted corpus, 1194 of the 1350
//! steps outside the proved fragment are `red` witnesses.
//!
//! | Rust | Clean |
//! |---|---|
//! | [`WitVal`] | `VeriPbCore.WitVal` |
//! | [`Wit`] | `VeriPbCore.Wit` |
//! | [`subst_lit`] | `VeriPbCore.substLit` |
//! | [`subst_c`] | `VeriPbCore.substC` |
//!
//! The kernel theorem this feeds is `VeriPbCore.dbOkR_red_of_goals`, which is
//! stated over exactly the proofgoals a checker discharges: under
//! `DB /\ ~c`, every substituted database slot holds and the substituted new
//! constraint holds. `VeriPbCore.holds_substC` is what carries each goal from
//! the substituted constraint the checker reasons about to the original
//! constraint under the witness-built assignment.
//!
//! ## Why the degree moves
//!
//! A witness may settle a literal to a CONSTANT. A term settled true always
//! contributes its coefficient, so substitution moves it to the right-hand
//! side; a term settled false contributes nothing and vanishes. That is the
//! `substShift` of the kernel development, and it is the whole reason
//! `subst_c` can fail: the shifted degree is formed in the exact width and
//! narrowed back, exactly as [`crate::add`] forms its sum.
//!
//! ## What this module does NOT do
//!
//! It does not decide whether a `red` step is sound. It computes the
//! substituted constraint that the proofgoals are about. The decision belongs
//! to the caller, which must establish every hypothesis of
//! `dbOkR_red_of_goals` — including, for any database slot the checker did
//! NOT emit a proofgoal for, that the slot is genuinely untouched by the
//! witness. [`subst_c_is_identity`] is that re-check: it is fail-closed, and
//! a caller that skips it would be assuming what the kernel asks it to prove.

use crate::{CoeffDomain, Constraint, Exact, GuardError, Lit, Term};

/// What a witness does to one variable — `VeriPbCore.WitVal`.
///
/// This is VeriPB's witness vocabulary exactly: a variable is left alone,
/// fixed to a truth value, or mapped to another literal.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum WitVal {
    /// Left alone (`WitVal.keep`).
    Keep,
    /// Fixed to true (`WitVal.isTrue`).
    IsTrue,
    /// Fixed to false (`WitVal.isFalse`).
    IsFalse,
    /// Mapped to another literal (`WitVal.toLit`).
    ToLit(Lit),
}

/// A witness substitution — `VeriPbCore.Wit`, which is `Nat -> WitVal`.
///
/// The kernel's witness is TOTAL, and so is this one: [`Wit::get`] answers
/// `Keep` for every variable outside the support. Keeping it total is what
/// makes `applyA` an ordinary assignment in the kernel, and it keeps the
/// correspondence free of partial-map reasoning on this side too.
pub trait Wit {
    /// What this witness does to `var`.
    fn get(&self, var: u32) -> WitVal;
}

/// The image of a literal under a witness — another literal, or a settled
/// constant. `VeriPbCore.LitImage`.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum LitImage {
    /// The literal is settled to this truth value.
    Const(bool),
    /// The literal became this literal.
    Lit(Lit),
}

/// `VeriPbCore.substLit`.
///
/// Splitting on the SIGN first is the kernel's structure, kept here so the two
/// definitions can be read against each other line by line: the image of a
/// negated literal is the negation of the image of the positive one.
pub fn subst_lit<W: Wit + ?Sized>(w: &W, l: Lit) -> LitImage {
    let positive = match w.get(l.var) {
        WitVal::Keep => LitImage::Lit(Lit {
            var: l.var,
            negated: false,
        }),
        WitVal::IsTrue => LitImage::Const(true),
        WitVal::IsFalse => LitImage::Const(false),
        WitVal::ToLit(m) => LitImage::Lit(m),
    };
    if l.negated {
        match positive {
            LitImage::Const(b) => LitImage::Const(!b),
            LitImage::Lit(m) => LitImage::Lit(m.negate()),
        }
    } else {
        positive
    }
}

/// `VeriPbCore.substC` — the substituted constraint.
///
/// `Err(GuardError::DegreeOverflow)` when the shifted degree does not fit the
/// domain. The kernel is stated over unbounded `Int`, so the shift is formed
/// in the exact width and narrowed back, the same shape [`crate::add`] uses
/// for its sum. Refusing is the fail-closed answer: a `red` whose substituted
/// degree cannot be represented is one this checker will not justify.
pub fn subst_c<C: CoeffDomain, W: Wit + ?Sized>(
    w: &W,
    c: &Constraint<C>,
) -> Result<Constraint<C>, GuardError> {
    let mut terms: Vec<Term<C>> = Vec::new();
    // `substShift`: the coefficients of the terms the witness settles TRUE.
    let mut shift = C::Exact::zero();
    for t in &c.terms {
        match subst_lit(w, t.lit) {
            LitImage::Lit(m) => terms.push(Term {
                coeff: t.coeff.clone(),
                lit: m,
            }),
            LitImage::Const(true) => {
                shift = shift
                    .checked_add(&t.coeff.widen())
                    .ok_or(GuardError::DegreeOverflow)?;
            }
            // Settled false: contributes nothing, and leaves no term.
            LitImage::Const(false) => {}
        }
    }
    let shifted = c
        .degree
        .widen()
        .checked_sub(&shift)
        .ok_or(GuardError::DegreeOverflow)?;
    let degree = C::narrow(&shifted).ok_or(GuardError::DegreeOverflow)?;
    Ok(C::pack(terms, degree))
}

/// Does the witness leave this constraint completely alone?
///
/// This is the re-check that lets a caller discharge
/// `dbOkR_red_of_goals`'s `HoldsAllO b (substDB w DB)` for the database slots
/// the checker emitted NO proofgoal for. Real proof formats only emit goals
/// for constraints the witness touches; the kernel theorem asks about EVERY
/// slot. The gap is closed not by trusting the omission but by computing the
/// substitution and comparing — if `substC w D` is `D`, then `Holds b D` from
/// the database already gives `Holds b (substC w D)`, with nothing assumed.
///
/// Fail-closed in both directions that matter: a constraint whose
/// substitution OVERFLOWS is not identity (there is no substituted constraint
/// at all), and any difference in terms, order, or degree is not identity.
pub fn subst_c_is_identity<C: CoeffDomain, W: Wit + ?Sized>(w: &W, c: &Constraint<C>) -> bool {
    match subst_c(w, c) {
        Ok(s) => s.degree == c.degree && s.terms == c.terms,
        Err(_) => false,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::Coeff;
    use std::collections::BTreeMap;

    struct MapWit(BTreeMap<u32, WitVal>);

    impl Wit for MapWit {
        fn get(&self, var: u32) -> WitVal {
            self.0.get(&var).copied().unwrap_or(WitVal::Keep)
        }
    }

    fn wit(pairs: &[(u32, WitVal)]) -> MapWit {
        MapWit(pairs.iter().copied().collect())
    }

    fn cst(terms: &[(Coeff, u32, bool)], degree: Coeff) -> Constraint<Coeff> {
        Constraint {
            terms: terms
                .iter()
                .map(|&(coeff, var, negated)| Term {
                    coeff,
                    lit: Lit { var, negated },
                })
                .collect(),
            degree,
        }
    }

    /// The sign split of `substLit`: the image of `~x` is the negation of the
    /// image of `x`, in every one of the four witness cases.
    #[test]
    fn negation_commutes_with_substitution() {
        let cases = [
            WitVal::Keep,
            WitVal::IsTrue,
            WitVal::IsFalse,
            WitVal::ToLit(Lit {
                var: 9,
                negated: true,
            }),
        ];
        for wv in cases {
            let w = wit(&[(3, wv)]);
            let pos = subst_lit(
                &w,
                Lit {
                    var: 3,
                    negated: false,
                },
            );
            let neg = subst_lit(
                &w,
                Lit {
                    var: 3,
                    negated: true,
                },
            );
            let expected = match pos {
                LitImage::Const(b) => LitImage::Const(!b),
                LitImage::Lit(m) => LitImage::Lit(m.negate()),
            };
            assert_eq!(neg, expected, "sign split disagrees for {wv:?}");
        }
    }

    /// A term settled TRUE moves to the right-hand side; the degree drops by
    /// its coefficient and the term is gone. This is `substShift`.
    #[test]
    fn a_true_literal_moves_into_the_degree() {
        let w = wit(&[(1, WitVal::IsTrue)]);
        let c = cst(&[(3, 1, false), (2, 2, false)], 4);
        let s = subst_c(&w, &c).expect("no overflow");
        assert_eq!(s.degree, 1, "4 - 3");
        assert_eq!(s.terms, cst(&[(2, 2, false)], 0).terms);
    }

    /// A term settled FALSE contributes nothing at all — it leaves, and the
    /// degree does not move.
    #[test]
    fn a_false_literal_just_vanishes() {
        let w = wit(&[(1, WitVal::IsFalse)]);
        let c = cst(&[(3, 1, false), (2, 2, false)], 4);
        let s = subst_c(&w, &c).expect("no overflow");
        assert_eq!(s.degree, 4);
        assert_eq!(s.terms, cst(&[(2, 2, false)], 0).terms);
    }

    /// The identity re-check is what licenses skipping a proofgoal, so it has
    /// to be exactly right in both directions.
    #[test]
    fn identity_holds_only_when_the_witness_is_irrelevant() {
        let c = cst(&[(3, 1, false), (2, 2, true)], 4);

        assert!(subst_c_is_identity(&wit(&[]), &c), "empty witness");
        assert!(
            subst_c_is_identity(&wit(&[(7, WitVal::IsTrue)]), &c),
            "a variable this constraint does not mention"
        );
        assert!(
            !subst_c_is_identity(&wit(&[(1, WitVal::IsTrue)]), &c),
            "settling a mentioned variable is NOT identity"
        );
        assert!(
            !subst_c_is_identity(&wit(&[(2, WitVal::IsFalse)]), &c),
            "settling a mentioned NEGATED variable is NOT identity"
        );
        assert!(
            !subst_c_is_identity(
                &wit(&[(
                    1,
                    WitVal::ToLit(Lit {
                        var: 5,
                        negated: false
                    })
                )]),
                &c
            ),
            "renaming a mentioned variable is NOT identity"
        );
        // Mapping a variable to ITSELF is identity, and must be recognised as
        // such rather than by looking at the support alone.
        assert!(
            subst_c_is_identity(
                &wit(&[(
                    1,
                    WitVal::ToLit(Lit {
                        var: 1,
                        negated: false
                    })
                )]),
                &c
            ),
            "a variable mapped to itself"
        );
    }

    /// A shift that cannot be represented is refused, not wrapped. This is the
    /// class the whole crate exists to prevent.
    #[test]
    fn an_unrepresentable_shift_is_refused() {
        let w = wit(&[(1, WitVal::IsTrue)]);
        let c = cst(&[(1, 1, false)], Coeff::MIN);
        assert_eq!(subst_c(&w, &c), Err(GuardError::DegreeOverflow));
        assert!(!subst_c_is_identity(&w, &c), "overflow is not identity");
    }
}
