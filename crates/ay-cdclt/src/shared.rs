// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The arithmetic plug-ins' side of the hub (design H1, §4.1): terms the hub
//! shares with a plug-in, and what `new_eq` / `new_diseq` become.
//!
//! A shared term is an arithmetic-sorted hub node: an argument or a result
//! of an uninterpreted application. The plug-in gives it a theory variable
//! (`ThVar`, the index here) so the hub can raise `new_eq` when two classes
//! carrying such variables merge, and `new_diseq` when an equality between
//! them becomes false.
//!
//! A plug-in learns either fact through the search: the lemma
//! `¬why ∨ (= a b)` (or `¬why ∨ ¬(= a b)`) over the equality atom, which the
//! kernel mints and hands to the arithmetic owner (the hub watches it too).
//! The lemma is T-valid: `why` is the hub's explanation, so it entails the
//! (dis)equality in EUF (K4), and its hint is the congruence explanation
//! kind (`lra.rs` says why the simplex does not take bounds instead).
//! Nelson–Oppen in the other direction (an equality the arithmetic implies,
//! which the hub needs) is model-based combination at the final check (H3,
//! `kernel/hub_glue.rs`).

use ay_core::{TermId, TheoryLemmaKind, TheoryLit};

use crate::atoms::eq_atom;
use crate::plugin::{Ctx, GiveUp, Lemma, LemmaTier, ProofHint, ThVar};

/// Terms the hub shares with one plug-in, indexed by their `ThVar`.
#[derive(Debug, Default)]
pub(crate) struct SharedTerms {
    terms: Vec<TermId>,
}

impl SharedTerms {
    /// A variable for `term` (a new one per call: the hub calls once per
    /// node).
    pub(crate) fn attach(&mut self, term: TermId) -> Result<ThVar, GiveUp> {
        let var =
            u32::try_from(self.terms.len()).map_err(|_| GiveUp::new("too many shared terms"))?;
        self.terms.push(term);
        Ok(ThVar(var))
    }

    fn pair(&self, a: ThVar, b: ThVar) -> Result<(TermId, TermId), GiveUp> {
        let get = |v: ThVar| {
            self.terms
                .get(v.0 as usize)
                .copied()
                .ok_or_else(|| GiveUp::new("an unknown shared variable"))
        };
        Ok((get(a)?, get(b)?))
    }

    /// `new_eq`: the lemma `¬why ∨ (= a b)`, unless the atom is true already.
    pub(crate) fn new_eq(
        &self,
        ctx: &mut Ctx<'_>,
        a: ThVar,
        b: ThVar,
        why: &[TheoryLit],
    ) -> Result<(), GiveUp> {
        self.consequence(ctx, a, b, why, true)
    }

    /// `new_diseq`: the lemma `¬why ∨ ¬(= a b)`, unless the atom is false
    /// already.
    pub(crate) fn new_diseq(
        &self,
        ctx: &mut Ctx<'_>,
        a: ThVar,
        b: ThVar,
        why: &[TheoryLit],
    ) -> Result<(), GiveUp> {
        self.consequence(ctx, a, b, why, false)
    }

    fn consequence(
        &self,
        ctx: &mut Ctx<'_>,
        a: ThVar,
        b: ThVar,
        why: &[TheoryLit],
        equal: bool,
    ) -> Result<(), GiveUp> {
        let (ta, tb) = self.pair(a, b)?;
        if ta == tb {
            return if equal {
                Ok(())
            } else {
                Err(GiveUp::new("a hub disequality between one term"))
            };
        }
        if why.is_empty() && !equal {
            // A disequality needs the false equality literal as a premise.
            return Err(GiveUp::new("a hub disequality without a reason"));
        }
        let eq = eq_atom(ctx.terms_mut(), ta, tb);
        if ctx.value(eq) == Some(equal) {
            return Ok(());
        }
        ctx.lemma(consequence_lemma(why, TheoryLit::new(eq, equal)));
        Ok(())
    }
}

/// `¬why ∨ lit`: an EUF consequence the hub derived (`why` holds now).
pub(crate) fn consequence_lemma(why: &[TheoryLit], lit: TheoryLit) -> Lemma {
    let mut clause: Vec<TheoryLit> = why
        .iter()
        .map(|r| TheoryLit::new(r.term, !r.value))
        .collect();
    clause.push(lit);
    Lemma {
        clause,
        tier: LemmaTier::Redundant,
        hint: ProofHint::kind(TheoryLemmaKind::EufCongruenceExplanation),
    }
}
