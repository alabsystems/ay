// Copyright 2026 Andrew Yates
// The substitution sigma of an SR/PR witness, and the reduction of a clause
// under it: dsr-trim's `global_data.c` half (`assume_subst`,
// `map_lit_under_subst`, `reduce_clause_under_subst`). The kernel that
// decides redundancy with it, `DratChecker::sr_redundant_step`, is in `sr.rs`.

use crate::checker::sr_reduct_core::classify_reduct;
use crate::checker::try_filled;
use crate::error::DratCheckError;
use crate::literal::Literal;

/// The image of a *variable's positive literal* under the substitution sigma.
///
/// dsr-trim stores `subst_mappings[var] = mapping ^ IS_NEG(lit)`, i.e. the
/// image of the positive literal; the sign is re-applied on lookup. We mirror
/// that: `True`/`False` are the boolean constants `SUBST_TT`/`SUBST_FF`, and
/// `Lit(m)` is a literal image.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub(super) enum SubImage {
    True,
    False,
    Lit(Literal),
}

impl SubImage {
    /// Negate an image (applying the sign of a negative literal on lookup).
    #[inline]
    fn negate(self) -> Self {
        match self {
            SubImage::True => SubImage::False,
            SubImage::False => SubImage::True,
            SubImage::Lit(m) => SubImage::Lit(m.negated()),
        }
    }
}

/// Result of evaluating one literal under sigma. (`map_lit_under_subst`.)
pub(super) enum LitImage {
    True,
    False,
    Lit(Literal),
}

/// Outcome of reducing a clause under sigma. Mirrors dsr-trim's return codes
/// `SATISFIED_OR_MUL` / `NOT_REDUCED` / `REDUCED` / `CONTRADICTION`.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub(super) enum Reduce {
    /// Some literal maps to true: the reduced clause is satisfied -> skip.
    Satisfied,
    /// sigma does not touch the clause (every literal maps to itself).
    NotReduced,
    /// sigma touches the clause and it is neither satisfied nor empty.
    Reduced,
    /// Every literal maps to false: the reduced clause is empty.
    Contradiction,
}

/// The substitution sigma, indexed by variable.
///
/// `map[var] == None` means sigma is the identity on `var`.
pub(super) struct Subst {
    pub(super) map: Vec<Option<SubImage>>,
    /// The clause pivot (= `witness[0]`), retained for diagnostics.
    pub(super) pivot: Literal,
}

impl Subst {
    /// Build sigma from an `AddPr`/`AddSr` witness token stream.
    ///
    /// Layout (see `dsr-trim::parse_sr_clause_and_witness` and AY's
    /// `DratWriter::add_sr`): `pivot [pr-atoms...] [pivot(sep) (l m)...]`.
    /// `witness[0]` is the pivot, which maps to true. Atoms before the second
    /// pivot occurrence each map to true (PR / DPR part). After the separating
    /// second pivot, tokens are read in (l, m) pairs giving `sigma(l) = m`
    /// (the substitution part that makes this SR rather than PR).
    ///
    /// Faithful to `assume_subst`: the pivot variable may be re-set in the
    /// substitution part, but no *other* variable may be assigned twice; a
    /// duplicate (or a malformed dangling pair) makes the witness invalid and
    /// the step is rejected (fail closed).
    pub(super) fn from_witness(
        witness: &[Literal],
        num_vars: usize,
    ) -> Result<Self, DratCheckError> {
        let Some((&pivot, rest)) = witness.split_first() else {
            return Err(DratCheckError::UnsupportedPr {
                clause: "empty SR/PR witness".to_string(),
            });
        };
        let pivot_var = pivot.variable().index();
        // One slot per checker variable, allocated fallibly: a refused
        // allocation rejects the step (fail closed) instead of aborting.
        let mut map: Vec<Option<SubImage>> =
            try_filled(None, num_vars).ok_or_else(|| DratCheckError::UnsupportedPr {
                clause: format!("SR/PR substitution map for {num_vars} variables is unallocatable"),
            })?;

        // pivot |-> true.
        Self::set(&mut map, pivot, SubImage::True)?;

        let mut seen_divider = false;
        let mut tokens = rest.iter().copied();
        while let Some(lit) = tokens.next() {
            let var = lit.variable().index();
            // A variable outside `map` is unassigned; `set` rejects it.
            let assigned = map.get(var).is_some_and(Option::is_some);
            if !seen_divider {
                if lit == pivot {
                    // The second occurrence of the pivot is the separator.
                    seen_divider = true;
                    continue;
                }
                if assigned && var != pivot_var {
                    return Err(Self::invalid("witness assigns a variable twice"));
                }
                Self::set(&mut map, lit, SubImage::True)?;
            } else {
                // Substitution part: (l, m) pairs.
                let mapped = tokens.next().ok_or_else(|| {
                    Self::invalid("witness has a dangling substitution half-pair")
                })?;
                if assigned && var != pivot_var {
                    return Err(Self::invalid("witness assigns a variable twice"));
                }
                Self::set(&mut map, lit, SubImage::Lit(mapped))?;
            }
        }

        Ok(Subst { map, pivot })
    }

    fn invalid(detail: &str) -> DratCheckError {
        DratCheckError::UnsupportedPr {
            clause: format!("invalid SR/PR witness: {detail}"),
        }
    }

    /// Store `sigma(lit) = image`, normalising to the positive-literal image
    /// (dsr-trim's `set_mapping_for_subst`).
    ///
    /// A literal whose variable lies outside `map` is rejected (fail closed):
    /// the substitution map is sized to the checker's variable count.
    #[inline]
    fn set(
        map: &mut [Option<SubImage>],
        lit: Literal,
        image: SubImage,
    ) -> Result<(), DratCheckError> {
        let stored = if lit.is_positive() {
            image
        } else {
            image.negate()
        };
        let slot = map
            .get_mut(lit.variable().index())
            .ok_or_else(|| Self::invalid("witness variable exceeds the variable count"))?;
        *slot = Some(stored);
        Ok(())
    }

    /// Compute `sigma(lit)` (dsr-trim's `map_lit_under_subst`).
    #[inline]
    pub(super) fn map_lit(&self, lit: Literal) -> LitImage {
        match self.map.get(lit.variable().index()).copied().flatten() {
            None => LitImage::Lit(lit), // identity
            Some(image) => {
                let img = if lit.is_positive() {
                    image
                } else {
                    image.negate()
                };
                match img {
                    SubImage::True => LitImage::True,
                    SubImage::False => LitImage::False,
                    SubImage::Lit(m) => LitImage::Lit(m),
                }
            }
        }
    }
}

/// The per-literal tally of a clause's images under sigma: the inputs of the
/// shared, Trust-verified `classify_reduct`.
#[derive(Clone, Copy, PartialEq, Eq, Debug, Default)]
pub(super) struct ReductTally {
    /// Some literal mapped to the constant True.
    pub(super) any_true: bool,
    /// How many literals mapped to the constant False.
    pub(super) falsified: usize,
    /// How many literals are fixed by sigma (map to themselves).
    pub(super) identity: usize,
}

impl ReductTally {
    /// Fold one literal's image into the tally.
    ///
    /// Both counts are bounded by the clause length (a slice has at most
    /// `isize::MAX` elements), so neither addition can overflow on a real
    /// clause. The additions are still checked: an overflowing tally returns
    /// `None`, which every caller turns into a REJECTED step (fail closed),
    /// never a wrapped or panicking count that could feed a wrong class into
    /// the skip/reject decision.
    #[inline]
    pub(super) fn record(mut self, lit: Literal, image: LitImage) -> Option<Self> {
        match image {
            LitImage::True => self.any_true = true,
            LitImage::False => self.falsified = self.falsified.checked_add(1)?,
            LitImage::Lit(m) => {
                if m == lit {
                    self.identity = self.identity.checked_add(1)?;
                }
            }
        }
        Some(self)
    }

    /// Classify a clause of `size` literals from its complete tally.
    ///
    /// The soundness-critical skip/reject decision is the SHARED,
    /// Trust-verified `classify_reduct` (proofs/sr_reduct_soundness_proof.rs
    /// makes it load-bearing). 0=Satisfied, 1=NotReduced, 2=Reduced,
    /// 3=Contradiction. (Counting all literals before classifying -- rather
    /// than short-circuiting on the first True -- yields the identical class
    /// but routes the WHOLE decision through the verified core.)
    #[inline]
    pub(super) fn classify(self, size: usize) -> Reduce {
        match classify_reduct(self.any_true, self.falsified, self.identity, size) {
            0 => Reduce::Satisfied,
            1 => Reduce::NotReduced,
            3 => Reduce::Contradiction,
            _ => Reduce::Reduced,
        }
    }
}

/// Reduce `clause` under sigma (dsr-trim's `reduce_clause_under_subst`).
///
/// Pure function of the clause and the substitution -- no engine state -- so it
/// can be called while a clause is borrowed from the DB.
///
/// Returns `None` when the tally cannot be represented (see
/// [`ReductTally::record`]); the caller must then reject the step.
pub(super) fn reduce_clause_under_subst(subst: &Subst, clause: &[Literal]) -> Option<Reduce> {
    let mut tally = ReductTally::default();
    for &lit in clause {
        tally = tally.record(lit, subst.map_lit(lit))?;
    }
    Some(tally.classify(clause.len()))
}
