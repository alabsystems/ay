// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Provenance of what a factor-split branch derives (#nia-factor-split-provenance).
//!
//! A branch of the factor split (`factor_split.rs`) pins its chosen factors (the
//! case hypothesis) and then DERIVES further facts from the asserted atoms: pins
//! (a single-unknown equality under the fixed values), orderings (a two-variable
//! difference atom), linearizations over fixed values and monotonicity cuts. It
//! installs them as sentinel-reason cuts, which an LRA conflict that uses them
//! does not name. The branch's explanation must therefore name what they rest
//! on (#nia-factor-split-premises): main omitted it (a wrong `unsat` on 110 of
//! 400 generated satisfiable QF_NIA files, `gen_fs.py` seed 9101), the NIA
//! soundness landing named EVERY asserted literal once anything was derived
//! (sound, but the weakest clause there is: ~40 corpus `sat` verdicts, VeryMax
//! SAT14 and others, were lost to it).
//!
//! Here each derived fact carries exactly the asserted literals it came from —
//! the atom it was derived from plus, transitively, the premises of every
//! fixed value substituted into that atom — so the explanation names exactly
//! those: never fewer (the wrong answers come back), and not all (the search
//! dies).

use ay_lra::rational::Rational;

use super::*;

/// The asserted literals a derived branch fact rests on
/// (#nia-factor-split-provenance): sorted, deduplicated positions in
/// `NiaSolver::asserted`. A branch's case pins are its hypothesis — the
/// split's cover names them — so they rest on nothing here.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub(crate) struct Premises(pub(crate) Vec<usize>);

impl Premises {
    /// `self ∪= other`.
    pub(crate) fn union(&mut self, other: &Premises) {
        if other.0.is_empty() {
            return;
        }
        self.0.extend_from_slice(&other.0);
        self.0.sort_unstable();
        self.0.dedup();
    }
}

/// The empty premise set: what a case pin rests on.
static NO_PREMISES: Premises = Premises(Vec::new());

/// Provenance of what one factor-split branch derived from the asserted
/// atoms (#nia-factor-split-provenance).
#[derive(Default)]
pub(crate) struct BranchPremises {
    /// Each DERIVED pin's premises. A `fixed` value with no entry is a case
    /// pin (in round 0; see `check_factor_split_branch`).
    pub(crate) pins: HashMap<TermId, Premises>,
    /// Each derived ordering `x <= y` and its premises.
    pub(crate) orderings: HashMap<(TermId, TermId), Premises>,
    /// The union of the premises of every sentinel-reason cut the branch
    /// installed: derived pins, linearizations over derived values, and
    /// monotonicity cuts.
    pub(crate) cuts: Premises,
}

impl BranchPremises {
    /// What the `fixed` value of `v` rests on.
    pub(crate) fn of_value(&self, v: TermId) -> &Premises {
        self.pins.get(&v).unwrap_or(&NO_PREMISES)
    }

    /// What a fact derived from the asserted literal at `atom`, with the
    /// `fixed` values of `used` substituted into it, rests on.
    pub(crate) fn derivation(&self, atom: usize, used: &[TermId]) -> Premises {
        let mut out = vec![atom];
        for v in used {
            out.extend_from_slice(&self.of_value(*v).0);
        }
        out.sort_unstable();
        out.dedup();
        Premises(out)
    }
}

impl NiaSolver<'_> {
    /// What makes `var` non-negative in the branch, or `None` when nothing
    /// does: fixed at a non-negative value (that value's premises), or the
    /// subject of an asserted Positive/NonNegative/Zero sign atom (that
    /// atom). The sign atom is read from the asserted literals themselves
    /// (`asserted_nonneg_atoms`), so the cut it licenses can name it
    /// (#nia-factor-split-provenance).
    pub(crate) fn branch_var_nonneg(
        var: TermId,
        fixed: &HashMap<TermId, Rational>,
        premises: &BranchPremises,
        nonneg_atoms: &HashMap<TermId, usize>,
    ) -> Option<Premises> {
        if let Some(val) = fixed.get(&var) {
            return (!val.is_negative()).then(|| premises.of_value(var).clone());
        }
        nonneg_atoms.get(&var).map(|&index| Premises(vec![index]))
    }

    /// Every term an asserted literal says is non-negative (a sign atom
    /// `t > 0`, `t >= 0` or `t = 0` in either orientation and polarity —
    /// `extract_sign_constraint`), mapped to the first such literal's
    /// position in `self.asserted`.
    pub(crate) fn asserted_nonneg_atoms(&self) -> HashMap<TermId, usize> {
        use ay_core::nonlinear::SignConstraint;
        let mut out: HashMap<TermId, usize> = HashMap::default();
        for (index, &(term, value)) in self.asserted.iter().enumerate() {
            if let Some((subject, constraint)) = self.extract_sign_constraint(term, value) {
                if matches!(
                    constraint,
                    SignConstraint::Positive | SignConstraint::NonNegative | SignConstraint::Zero
                ) {
                    out.entry(subject).or_insert(index);
                }
            }
        }
        out
    }
}
