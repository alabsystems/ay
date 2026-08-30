// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The literal-only RoundingMode atoms Pass B pins, and the pins themselves.
//!
//! Split out of `rm_domain.rs` so the pass's scan and its pin language read
//! separately; the module docs there cover the pass as a whole.

use ay_core::kani_compat::DetHashSet as HashSet;
use ay_core::term::Symbol;
use ay_core::{Sort, TermId, TermStore};

use super::{is_rm_sort, rm_literal_mode, RM_COVERAGE_MAX_TERMS};

/// The two operands of a binary `=` application over RoundingMode literals of
/// DIFFERENT modes, if `symbol`/`args` are exactly that.
///
/// This is the ONLY all-literal RM atom Pass B pins, and the shape is not a
/// matter of taste: `not (= m_i m_j)` with `i != j` is precisely what AY's own
/// strict RoundingMode checker re-derives
/// (`ay-proof/src/checker/rounding_mode.rs::recognize_pairwise_unit`, which
/// normalizes the operand pair and so accepts either order). Every other
/// all-literal RM atom is deliberately left alone — see
/// [`RmLiteralAtoms`] for the measurements that license that.
///
/// SORT-GUARDED. [`rm_literal_mode`] recognizes a term by NAME, and the ten
/// mode spellings are frontend-sealed but not unforgeable through a raw
/// `TermStore`. Requiring the RoundingMode sort as well keeps this off any
/// equality that merely borrows a mode's name at another sort. Mirrors
/// `unsat_cert/rm_domain_expansion.rs::rm_literal_equality_value`.
pub(super) fn rm_literal_disequality_operands(
    terms: &TermStore,
    symbol: &Symbol,
    args: &[TermId],
) -> Option<(TermId, TermId)> {
    if symbol.name() != "=" || args.len() != 2 {
        return None;
    }
    if !is_rm_sort(terms.sort(args[0])) || !is_rm_sort(terms.sort(args[1])) {
        return None;
    }
    let left = rm_literal_mode(terms, args[0])?;
    let right = rm_literal_mode(terms, args[1])?;
    (left != right).then_some((args[0], args[1]))
}

/// Every binary `=` atom over two DIFFERENT RoundingMode literals the walk met.
///
/// # Why the distinct-5 axiom is not enough on its own
///
/// `mk_distinct` expands the five-mode axiom through [`TermStore::mk_eq`],
/// which CANONICALIZES its operand order (`lhs < rhs`) and interns the result.
/// It therefore constrains exactly ten specific atoms. An atom in the assertion
/// DAG that denotes the same equality but is a DIFFERENT interned term —
/// `App("=", [RTN, RTP])` as `TermStore::substitute_terms` rebuilds it, with no
/// smart constructor and hence no canonical order — is not one of those ten,
/// and nothing else constrains it either: the FP lane's fail-closed backstop
/// (`theories/fp/support.rs::check_fp_support`) passes an equality whose two
/// operands are both LITERAL modes, so the atom reaches the SAT layer as a free
/// Boolean. MEASURED on `[(= (fp.roundToIntegral RTN 2.5) 2.0), (= RTN RTP)]`
/// with the second root built by substitution: `unknown` (the candidate model
/// is then refuted by model validation, so the cost was completeness, never a
/// published wrong answer — but the atom was genuinely unconstrained). The same
/// roots with the equality built through `mk_eq` decide `unsat`.
///
/// Pinning the atom that is ACTUALLY IN THE DAG closes that gap for every
/// spelling and every operand order at once, because the axiom names the atom
/// itself rather than a term that is merely equal to it.
///
/// # Why ONLY the different-mode equality
///
/// A producer must not emit an axiom its own checker refuses, so the pinned
/// language is bounded by what
/// [`ay_proof::recognize_rounding_mode_domain`] re-derives. The two shapes an
/// earlier revision of this pass also pinned are both outside it, and both
/// turn out not to need a pin at all (MEASURED at 47773e309, each as a fresh
/// top-level `check_sat` over a raw-interned atom, with the positive pin
/// suppressed):
///
/// * a REFLEXIVE `(= RTP RTP)` — the pin would be `eq_reflexive`, not an RM
///   domain fact, and the atom is already decided:
///   `(assert (not (= RTP RTP)))` → `unsat`, `(assert (= RTP RTP))` → `sat`;
/// * a raw `App("distinct", …)` over mode literals — `mk_distinct` never
///   builds one (it returns `false`, `not (= a b)`, or an `and` of pairwise
///   disequalities), and the three polarities measure
///   `(distinct RTP RTP)` → `unsat`, `(distinct RTN RTP)` → `sat`,
///   `(not (distinct RTN RTP))` → `unknown` with the model gate refuting the
///   candidate ("Assertion 0 violated"). The residual is one `unknown` that
///   should be `unsat`: a COMPLETENESS gap, sound, and not worth an axiom no
///   checker accepts.
#[derive(Default)]
pub(super) struct RmLiteralAtoms {
    seen: HashSet<TermId>,
    /// `(atom, left operand, right operand)`.
    atoms: Vec<(TermId, TermId, TermId)>,
}

impl RmLiteralAtoms {
    /// Record `term` if it is a binary `=` over two different RM literals.
    ///
    /// The Bool guard is not decoration: a pin is ASSERTED, and `mk_not` over a
    /// non-Bool term would be ill-sorted. `=` is Bool by construction through
    /// every smart constructor, so this only rejects a term some raw
    /// `TermStore::intern` mis-sorted.
    pub(super) fn record(
        &mut self,
        terms: &TermStore,
        term: TermId,
        symbol: &Symbol,
        args: &[TermId],
    ) {
        if terms.sort(term) != &Sort::Bool {
            return;
        }
        let Some((left, right)) = rm_literal_disequality_operands(terms, symbol, args) else {
            return;
        };
        if !self.seen.insert(term) {
            return;
        }
        self.atoms.push((term, left, right));
    }

    /// The pins for the recorded atoms, or `None` if the caller must fail
    /// closed.
    ///
    /// `lits` is the five canonical mode literal terms, in `RM_MODES` order —
    /// the same vector `mk_distinct` was just given. The skip test is exact and
    /// interns nothing new: `mk_eq(a, b)` over two of those five returns the
    /// very atom `mk_distinct` built, so `canonical == atom` holds precisely
    /// when this atom IS one of that axiom's ten conjuncts.
    ///
    /// Each pin is VALID in every model of the FP theory (the five modes are
    /// five distinct elements), so this removes no model and can never turn a
    /// `sat` into an `unsat`.
    ///
    /// PRODUCER/CHECKER PARITY. The last gate is AY's OWN strict checker,
    /// called here rather than paraphrased, so classifier and validator cannot
    /// drift (the same "recognition IS the validator" discipline as
    /// `ay_proof::recognize_euf_congruent`'s callers). [`rm_literal_mode`]
    /// accepts spellings the checker's `mode_index` does not — a `Var`-form
    /// literal, a long name — and a pin over one of those would be an axiom AY
    /// asserts and then refuses to check. Declining to pin is the right degrade
    /// rather than a fail-close: the atom's operands are literals, already named
    /// by distinct-5, so nothing floats OUT of the five-element domain (which is
    /// what the fail-closed arms exist for); an unpinned atom costs only
    /// completeness, and MEASURED, the independent model gate refutes any
    /// candidate model that violates one.
    ///
    /// `None` (fail closed) only for the budget: the same bound as the coverage
    /// budget, for the same reason — this pass may not inject an unbounded
    /// number of axioms into a solve it did not size. It is a BACKSTOP, not a
    /// live guard, and honestly labelled as one: the checker gate admits a pin
    /// only when both operands are among the five hash-consed canonical mode
    /// terms, so at most the 20 ordered different-mode pairs of those five can
    /// ever be pinned, and `seen` already deduplicates by atom. 20 < 256, so no
    /// input reaches this arm — `the_pinned_language_is_the_twenty_ordered_pairs`
    /// pins that bound. It stays because an unbounded injection would be the
    /// wrong thing to discover later, not because it fires.
    pub(super) fn pins(self, terms: &mut TermStore, lits: &[TermId]) -> Option<Vec<TermId>> {
        let mut pins: Vec<TermId> = Vec::new();
        for (atom, left, right) in self.atoms {
            if lits.contains(&left) && lits.contains(&right) && terms.mk_eq(left, right) == atom {
                continue;
            }
            let pin = terms.mk_not(atom);
            if !ay_proof::recognize_rounding_mode_domain(terms, &[pin]) {
                continue;
            }
            pins.push(pin);
        }
        (pins.len() <= RM_COVERAGE_MAX_TERMS).then_some(pins)
    }
}
