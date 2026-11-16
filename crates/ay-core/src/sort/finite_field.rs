// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Prime-field sorts with exact, checked primality for u32 cardinalities.
//!
//! Deterministic Miller–Rabin with bases 2, 7 and 61. Their least simultaneous
//! strong pseudoprime is 4,759,123,141, above the entire u32 domain: Jaeschke,
//! "On strong pseudoprimes to several bases", Math. Comp. 61 (1993), 915–926,
//! https://doi.org/10.1090/S0025-5718-1993-1192971-8.
//! This is exact admission, not a probable-prime claim. No extension fields or
//! implicit integer-sort lowering are provided.

use serde::{Deserialize, Deserializer, Serialize, Serializer};

/// Largest prime modulus admitted by the native finite-field slice.
pub const MAX_FINITE_FIELD_MODULUS: u32 = 4_294_967_291;

/// A genuinely prime modulus in the supported bounded domain.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct FiniteFieldSort(u32);

impl FiniteFieldSort {
    /// Check the size bound and deterministically prove primality.
    #[must_use]
    pub fn new(modulus: u32) -> Option<Self> {
        if !(2..=MAX_FINITE_FIELD_MODULUS).contains(&modulus) {
            return None;
        }
        // Cheap factors also decide the original small-field domain without
        // modular exponentiation. Having excluded every smaller prime factor,
        // a number below the next prime's square is prime.
        for prime in [2u32, 3, 5, 7, 11, 13, 17] {
            if modulus < prime * prime {
                return Some(Self(modulus));
            }
            if modulus.is_multiple_of(prime) {
                return None;
            }
        }
        let powers_of_two = (modulus - 1).trailing_zeros();
        let odd = (modulus - 1) >> powers_of_two;
        let n = u64::from(modulus);
        for base in [2u64, 7, 61] {
            let base = base % n;
            if base == 0 {
                // A prime witness base can itself equal the admitted prime.
                continue;
            }
            let mut residue = modular_power(base, odd, n);
            if residue == 1 || residue == n - 1 {
                continue;
            }
            let mut passed = false;
            for _ in 1..powers_of_two {
                residue = residue * residue % n;
                if residue == n - 1 {
                    passed = true;
                    break;
                }
            }
            if !passed {
                return None;
            }
        }
        Some(Self(modulus))
    }

    /// The prime characteristic and cardinality.
    #[must_use]
    pub fn modulus(self) -> u32 {
        self.0
    }
}

fn modular_power(mut base: u64, mut exponent: u32, modulus: u64) -> u64 {
    let mut value = 1u64;
    while exponent != 0 {
        // Both factors are reduced u32 residues, so their product fits u64.
        if exponent & 1 != 0 {
            value = value * base % modulus;
        }
        base = base * base % modulus;
        exponent >>= 1;
    }
    value
}

impl Serialize for FiniteFieldSort {
    fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        serializer.serialize_u32(self.0)
    }
}

impl<'de> Deserialize<'de> for FiniteFieldSort {
    fn deserialize<D: Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
        let modulus = u32::deserialize(deserializer)?;
        Self::new(modulus).ok_or_else(|| {
            serde::de::Error::custom("unsupported or non-prime finite-field modulus")
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn primality_is_exact_and_wire_values_cannot_bypass_it() {
        for p in [
            2,
            3,
            7,
            17,
            61,
            127,
            251,
            257,
            65_521,
            2_147_483_647,
            4_294_967_291,
        ] {
            assert_eq!(FiniteFieldSort::new(p).unwrap().modulus(), p);
        }
        for p in [
            0,
            1,
            4,
            9,
            121,
            221,
            247,
            2047,
            65_535,
            1_373_653,
            25_326_001,
            3_215_031_751,
            u32::MAX,
        ] {
            assert!(FiniteFieldSort::new(p).is_none());
            assert!(serde_json::from_str::<FiniteFieldSort>(&p.to_string()).is_err());
        }
    }

    #[test]
    fn deterministic_admission_agrees_with_independent_trial_division() {
        fn trial_prime(n: u32) -> bool {
            if n < 2 {
                return false;
            }
            let mut divisor = 2;
            while divisor <= n / divisor {
                if n.is_multiple_of(divisor) {
                    return false;
                }
                divisor += 1;
            }
            true
        }
        let mut sample = 0x9e37_79b9u32;
        let dispersed = (0..1024).map(|_| {
            sample = sample.wrapping_mul(1_664_525).wrapping_add(1_013_904_223);
            sample
        });
        for n in (0..=u32::from(u16::MAX))
            .chain(u32::MAX - 4095..=u32::MAX)
            .chain(dispersed)
        {
            assert_eq!(
                FiniteFieldSort::new(n).is_some(),
                n <= MAX_FINITE_FIELD_MODULUS && trial_prime(n),
                "modulus {n}"
            );
        }
    }
}
