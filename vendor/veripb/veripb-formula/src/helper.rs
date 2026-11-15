//! Some general helper functions used inside this crate.

use std::{iter::Peekable, slice::Iter};

use malachite_bigint::BigInt;
use num_traits::One;

use crate::prelude::*;

/// The exact quotient `ceil(A / d)` of a degree `A` by a divisor `d` that does *not* fit into the
/// constraint's own integer type `N`.
///
/// Every division and MIR rule needs this quotient, and every one of them used to approximate it
/// on this branch — either by substituting `i64::MAX` for `d` before dividing, or by clamping the
/// quotient to `A.is_positive()`. Both are faithful only while `|A| < N::MAX`, and the degree of a
/// constraint reaches `N::MIN`: the substitution then yields `-1` where the rule's quotient is `0`
/// (a weaker constraint than the proof wrote down, so a valid proof is rejected), and the clamp
/// yields `0` where the rule's quotient is `-1` (a stronger one).
///
/// Taking the ceiling exactly in [`BigInt`] costs nothing worth measuring: the branch is only
/// reachable for a divisor too large for `N`, which no realistic proof takes twice.
///
/// # Panics
///
/// Never, on the branch it exists for: `d` not fitting `N` means `|d| >= N::MAX + 1 >= |A|`, so the
/// quotient is one of `-1`, `0`, `1` and always narrows back into `N`.
pub fn quotient_by_oversized_divisor<N: Int>(degree: &N, divisor: &BigInt) -> N {
    let quotient = num_integer::Integer::div_ceil(&Into::<BigInt>::into(degree.clone()), divisor);
    N::try_from(quotient).ok().unwrap_or_else(|| {
        panic!("a divisor that does not fit into `N` bounds `ceil(A / d)` by 1 in absolute value")
    })
}

/// Merge [`Vec<Lit>`] literals and [`Vec<PBTerm`>] to literals.
///
/// This function immediately returns if merging the term in the [`Vec<Lit>`] is not possible due to the coefficient being larger than 1.
pub fn merge_in_situ_lits(
    clause_term: &mut Peekable<Iter<'_, Lit>>,
    summand_term: &mut Peekable<Iter<'_, impl PBTerm>>,
    resulting_lits: &mut Vec<Lit>,
    cancel: &mut i64,
) {
    loop {
        match (clause_term.peek(), summand_term.peek()) {
            (None, None) => break,
            (None, Some(term)) => {
                if !term.get_coeff().is_one() {
                    break;
                }
                resulting_lits.push(term.get_lit());
                summand_term.next();
            }
            (Some(&lit), None) => {
                resulting_lits.push(*lit);
                clause_term.next();
            }
            (Some(&lit), Some(term)) => match lit.get_var().cmp(&term.get_lit().get_var()) {
                std::cmp::Ordering::Less => {
                    resulting_lits.push(*lit);
                    clause_term.next();
                }
                std::cmp::Ordering::Greater => {
                    if !term.get_coeff().is_one() {
                        break;
                    }
                    resulting_lits.push(term.get_lit());
                    summand_term.next();
                }
                std::cmp::Ordering::Equal => {
                    match (lit.is_negated(), term.get_lit().is_negated()) {
                        (false, false) | (true, true) => break,
                        _ => {
                            if *term.get_coeff() == From::from(2) {
                                resulting_lits.push(term.get_lit());
                            } else if !term.get_coeff().is_one() {
                                break;
                            }
                            *cancel += 1;
                            clause_term.next();
                            summand_term.next();
                        }
                    }
                }
            },
        }
    }
}

/// Merge [`Vec<Lit>`] literals and [`Vec<PBTerm`>] to [`Vec<GeneralPBTerm<N>>`].
///
/// This function immediately returns if merging the term in the [`Vec<GeneralPBTerm<N>>`] is not possible due to the coefficient being larger than [`N::MAX`].
pub fn merge_from_lits<N: Int>(
    mut clause_term: Peekable<Iter<'_, Lit>>,
    mut summand_term: Peekable<Iter<'_, impl PBTerm>>,
    resulting_terms: &mut Vec<GeneralPBTerm<N>>,
    cancel: &mut N,
) {
    loop {
        match (clause_term.peek(), summand_term.peek()) {
            (None, None) => break,
            (None, Some(&term)) => {
                resulting_terms.push(GeneralPBTerm::new(
                    term.get_coeff().to_owned().into().try_into().ok().unwrap(),
                    term.get_lit(),
                ));
                summand_term.next();
            }
            (Some(&lit), None) => {
                resulting_terms.push(GeneralPBTerm::new(N::one(), *lit));
                clause_term.next();
            }
            (Some(&lit), Some(&term)) => match lit.get_var().cmp(&term.get_lit().get_var()) {
                std::cmp::Ordering::Less => {
                    resulting_terms.push(GeneralPBTerm::new(N::one(), *lit));
                    clause_term.next();
                }
                std::cmp::Ordering::Greater => {
                    resulting_terms.push(GeneralPBTerm::new(
                        term.get_coeff().to_owned().into().try_into().ok().unwrap(),
                        term.get_lit(),
                    ));
                    summand_term.next();
                }
                std::cmp::Ordering::Equal => {
                    let term = GeneralPBTerm::new(
                        Into::<BigInt>::into(term.get_coeff().to_owned())
                            .try_into()
                            .ok()
                            .unwrap(),
                        term.get_lit(),
                    );
                    resulting_terms.push(GeneralPBTerm::new(N::one(), *lit));
                    *cancel += resulting_terms.last_mut().unwrap().add_with(term);
                    if resulting_terms.last().unwrap().coeff.is_zero() {
                        resulting_terms.pop();
                    }

                    clause_term.next();
                    summand_term.next();
                }
            },
        }
    }
}
