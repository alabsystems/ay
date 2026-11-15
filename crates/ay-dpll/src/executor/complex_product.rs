// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Ground eta expansion for the builtin product Complex = Real × Real.
//! Reconstruction makes component equality available to EUF congruence,
//! including when Complex values occur as function arguments or array values.

use ay_core::kani_compat::DetHashSet as HashSet;
use ay_core::{Sort, Symbol, TermData, TermId};

use super::Executor;

impl Executor {
    pub(super) fn complex_product_axioms(&mut self, roots: &[TermId]) -> Vec<TermId> {
        let mut pending = roots.to_vec();
        let mut seen = HashSet::default();
        let mut values = Vec::new();
        while let Some(term) = pending.pop() {
            if !seen.insert(term) {
                continue;
            }
            // A bound term cannot become a free top-level axiom. Ground
            // instances reach this pass through their own assertion roots.
            if matches!(
                self.ctx.terms.get(term),
                TermData::Forall(..) | TermData::Exists(..) | TermData::Let(..)
            ) {
                continue;
            }
            pending.extend(self.ctx.terms.children(term));
            if self.ctx.terms.sort(term) == &Sort::Complex {
                values.push(term);
            }
        }
        let mut axioms = Vec::new();
        for value in values {
            let Some(real) = self.ctx.terms.mk_complex_real(value) else {
                continue;
            };
            let Some(imaginary) = self.ctx.terms.mk_complex_imaginary(value) else {
                continue;
            };
            let Some(reconstructed) = self.ctx.terms.mk_complex(real, imaginary) else {
                continue;
            };
            if value == reconstructed {
                continue;
            }
            // Deliberately retain the carrier equality: mk_eq lowers Complex
            // equality to its components, which would erase this EUF bridge.
            let axiom =
                self.ctx
                    .terms
                    .mk_app(Symbol::named("="), [value, reconstructed], Sort::Bool);
            axioms.push(axiom);
        }
        axioms
    }
}
