// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The difference-logic plug-in's clauses: proof hints for its theory
//! clauses, and the definition of an equality atom by its two bounds.

use ay_core::{TermId, TheoryLemmaKind, TheoryLit};
use ay_diff_logic::DlWeight;

use super::DlPlugin;
use crate::lra_certify::certify_clause;
use crate::plugin::{Ctx, Lemma, LemmaTier, ProofHint};

impl<W: DlWeight> DlPlugin<W> {
    /// The hint for `clause`, a theory clause the plug-in hands the kernel.
    ///
    /// Over the reals a negative cycle, and a path bounding an atom, is a
    /// linear-arithmetic tautology: with proofs on it gets the private
    /// simplex's Farkas certificate (`lra_certify`, as the LRA plug-in's
    /// propagations do), so the printed step is an `la_generic` instance an
    /// external checker reads; otherwise, or when no certificate comes back,
    /// the kind alone. Tightened integer bounds need integer reasoning.
    pub(super) fn hint(&self, ctx: &mut Ctx<'_>, clause: &[TheoryLit]) -> ProofHint {
        if self.integer {
            return ProofHint::kind(TheoryLemmaKind::LiaGeneric);
        }
        let certified = if ctx.proofs_on() {
            certify_clause(ctx.terms_mut(), clause)
        } else {
            None
        };
        certified.unwrap_or_else(|| ProofHint::kind(TheoryLemmaKind::ArithClauseTautology))
    }

    /// Define `e := (a = b)` by `a ≤ b` and `b ≤ a` (see the module docs).
    /// With proofs on, a real check certifies each `¬e ∨ bound` clause with
    /// its Farkas coefficients (`la_generic`), as [`Self::hint`] does.
    pub(super) fn define_equality(
        ctx: &mut Ctx<'_>,
        integer: bool,
        e: TermId,
        a: TermId,
        b: TermId,
    ) {
        let terms = ctx.terms_mut();
        let le = terms.mk_le(a, b);
        let ge = terms.mk_le(b, a);
        let lit = TheoryLit::new;
        let definitions = [
            (
                vec![lit(e, false), lit(le, true)],
                TheoryLemmaKind::ArithEqImpliesBound,
            ),
            (
                vec![lit(e, false), lit(ge, true)],
                TheoryLemmaKind::ArithEqImpliesBound,
            ),
            (
                vec![lit(le, false), lit(ge, false), lit(e, true)],
                TheoryLemmaKind::ArithEqTriangle,
            ),
        ];
        for (clause, kind) in definitions {
            let certified =
                (!integer && ctx.proofs_on() && kind == TheoryLemmaKind::ArithEqImpliesBound)
                    .then(|| certify_clause(ctx.terms_mut(), &clause))
                    .flatten();
            ctx.lemma(Lemma {
                clause,
                tier: LemmaTier::Definitional,
                hint: certified.unwrap_or_else(|| ProofHint::kind(kind)),
            });
        }
    }
}
