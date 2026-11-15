//! Boolean literal.

use std::fmt::Display;

use num_traits::One;

use crate::prelude::*;

/// The internal representation of a literal.
type LitData = usize;

/// Generic literal struct to represent a Boolean literal. Defining the trait literal does not really make sense, as literals only exist in the context of Boolean variables.
///
/// A literal consist of:
/// - the underlying variable
/// - a flag for negation of the literal
///
/// This implementation uses only one `data` field of type `LitData` to reduce the memory footprint. `LitData` is an unsigned number and if `LitData` is even, then [`Lit`] is not negated and if `LitData` is odd, then [`Lit`] is negated. The [`VarIdx`] is represented by the `width(LitData) - 1` first bits. Hence, the [`VarIdx`] can be obtained from [`Lit`] by dividing with 2 or shifting the bits one to the right.
///
/// Implementation details of the functions did not seem to matter, as the compiler is smart enough to figure out optimizations.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Default, Hash)]
pub struct Lit {
    data: LitData,
}

impl Lit {
    /// Construct a new default [`Lit`].
    #[inline]
    pub fn from_raw_data(data: usize) -> Self {
        Lit { data }
    }

    /// Construct a new default [`Lit`].
    #[inline]
    pub fn new_undef() -> Self {
        Lit { data: usize::MAX }
    }

    /// Check if [`Lit`] is undefined [`Lit`].
    #[inline]
    pub fn is_undef(&self) -> bool {
        self.data == usize::MAX
    }

    /// The largest variable index that [`Lit`] can represent.
    ///
    /// [`from_var()`](Lit::from_var) packs `(var_idx << 1) ^ is_negated`. For
    /// `var_idx == LitData::MAX >> 1` the negated form is exactly `LitData::MAX`, the reserved
    /// value returned by [`new_undef()`](Lit::new_undef) (and the bit pattern of
    /// `SubstitutionValue::TRUE`), and the positive form is `LitData::MAX - 1`
    /// (`SubstitutionValue::FALSE`). For larger indices the shift drops the top bits and two
    /// distinct variables alias to the same literal. Anything that builds a [`Lit`] from an
    /// externally supplied index — the DIMACS CNF parser is the only such place, since every other
    /// index comes from `VarNameManager` and is bounded by its table length — must reject indices
    /// above this bound.
    pub const MAX_VAR_IDX: VarIdx = (LitData::MAX >> 1) - 1;

    /// Construct [`Lit`] by name.
    ///
    /// # Panics
    /// In debug builds if `var_idx` exceeds [`MAX_VAR_IDX`](Lit::MAX_VAR_IDX). Use
    /// [`try_from_var()`](Lit::try_from_var) for indices that come from untrusted input.
    #[inline]
    pub fn from_var(var_idx: VarIdx, is_negated: bool) -> Self {
        debug_assert!(
            var_idx <= Self::MAX_VAR_IDX,
            "variable index {var_idx} exceeds the largest representable index {}",
            Self::MAX_VAR_IDX
        );
        Lit {
            data: (var_idx << 1) ^ (is_negated as usize),
        }
    }

    /// Construct [`Lit`] from an index that may be out of range, returning [`None`] if it is.
    #[inline]
    pub fn try_from_var(var_idx: VarIdx, is_negated: bool) -> Option<Self> {
        (var_idx <= Self::MAX_VAR_IDX).then(|| Self::from_var(var_idx, is_negated))
    }

    /// Check if [`Lit`] is negated or not. Returns `true` if [`Lit`] is negated.
    #[inline]
    pub fn is_negated(&self) -> bool {
        self.data % 2 == 1
    }

    /// Negate [`Lit`].
    #[inline]
    pub fn negate(&mut self) {
        self.data ^= 1;
    }

    /// Get the underlying variable of [`Lit`].
    #[inline]
    pub fn get_var(&self) -> VarIdx {
        self.data >> 1
    }

    /// Direct access to the internal [`Lit`] data. This function is mainly used to check that the internal data is correct.
    #[inline]
    pub fn get_lit_data(&self) -> LitData {
        self.data
    }
}

/// A literal also implements [`PBTerm`], which is used for the pseudo-Boolean constraints [`Clause`] and [`Cardinality`].
impl PBTerm for Lit {
    type CoeffType = i64;

    #[inline]
    fn negate(&mut self) {
        self.negate();
    }

    #[inline]
    fn get_lit(&self) -> Lit {
        *self
    }

    #[inline]
    fn get_coeff(&self) -> &i64 {
        &1
    }

    #[inline]
    fn set_coeff(&mut self, coeff: Self::CoeffType) {
        if !coeff.is_one() {
            panic!("Trying to set coefficient for Clause or Cardinality to something else than 1!")
        }
    }

    #[inline]
    fn divide_round_up(&mut self, _divisor: &Self::CoeffType) {}
}

impl Display for Lit {
    #[inline]
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.data)
    }
}

impl std::ops::Neg for Lit {
    type Output = Lit;
    #[inline]
    fn neg(mut self) -> Self::Output {
        self.negate();
        self
    }
}

impl std::ops::Neg for &Lit {
    type Output = Lit;
    #[inline]
    fn neg(self) -> Self::Output {
        let mut lit = *self;
        lit.negate();
        lit
    }
}

impl ToPrettyString for Lit {
    #[inline]
    fn to_pretty_string<V: VarNameLookup>(&self, var_names: &V) -> String {
        if self.is_negated() {
            "~".to_string() + var_names.get_name(self.get_var())
        } else {
            var_names.get_name(self.get_var()).to_string()
        }
    }
}
