// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Allocation-conscious hash-first proof-lemma deduplication.

use ay_core::kani_compat::DetHashMap as HashMap;
use ay_core::{FarkasAnnotation, ProofId, TermId, TheoryLemmaKind};

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub(super) struct LemmaKey {
    pub(super) kind: TheoryLemmaKind,
    pub(super) clause: Vec<TermId>,
    pub(super) farkas: Option<Vec<(i64, i64)>>,
}

impl LemmaKey {
    pub(super) fn new(
        kind: TheoryLemmaKind,
        clause: &[TermId],
        farkas: Option<&FarkasAnnotation>,
    ) -> Self {
        Self {
            kind,
            clause: clause.to_vec(),
            farkas: farkas.map(|f| f.coefficients.iter().map(normalized_farkas_pair).collect()),
        }
    }
}

/// Sign-normalize one Farkas coefficient exactly as [`LemmaKey::new`] stores
/// it, so streaming comparison/hashing agrees with the owned key.
fn normalized_farkas_pair(coefficient: &num_rational::Rational64) -> (i64, i64) {
    let mut numer = *coefficient.numer();
    let mut denom = *coefficient.denom();
    if denom < 0 {
        numer = -numer;
        denom = -denom;
    }
    (numer, denom)
}

/// Deterministic stream fingerprint of a lemma identity (#A4).
///
/// Hashes `(kind, clause, normalized farkas)` without allocating, using the
/// std `DefaultHasher` (SipHash with fixed keys — stable within a process).
/// Insert and lookup both use THIS function, never the derived `Hash` of
/// [`LemmaKey`], so the two paths cannot disagree.
pub(super) fn lemma_fingerprint(
    kind: TheoryLemmaKind,
    clause: &[TermId],
    farkas: Option<&FarkasAnnotation>,
) -> u64 {
    use std::hash::{Hash, Hasher};
    let mut hasher = std::collections::hash_map::DefaultHasher::new();
    kind.hash(&mut hasher);
    clause.hash(&mut hasher);
    match farkas {
        None => 0u8.hash(&mut hasher),
        Some(annotation) => {
            1u8.hash(&mut hasher);
            annotation.coefficients.len().hash(&mut hasher);
            for coefficient in &annotation.coefficients {
                normalized_farkas_pair(coefficient).hash(&mut hasher);
            }
        }
    }
    hasher.finish()
}

/// Fingerprint of an owned key; MUST agree with [`lemma_fingerprint`] on the
/// equivalent `(kind, clause, farkas)` query.
pub(super) fn lemma_key_fingerprint(key: &LemmaKey) -> u64 {
    use std::hash::{Hash, Hasher};
    let mut hasher = std::collections::hash_map::DefaultHasher::new();
    key.kind.hash(&mut hasher);
    key.clause.hash(&mut hasher);
    match &key.farkas {
        None => 0u8.hash(&mut hasher),
        Some(pairs) => {
            1u8.hash(&mut hasher);
            pairs.len().hash(&mut hasher);
            for pair in pairs {
                pair.hash(&mut hasher);
            }
        }
    }
    hasher.finish()
}

/// Allocation-free equality between a stored key and a lemma-identity query.
/// Exactly mirrors the derived `PartialEq` on [`LemmaKey`] against
/// `LemmaKey::new(kind, clause, farkas)`.
fn lemma_key_matches(
    key: &LemmaKey,
    kind: TheoryLemmaKind,
    clause: &[TermId],
    farkas: Option<&FarkasAnnotation>,
) -> bool {
    if key.kind != kind || key.clause != clause {
        return false;
    }
    match (&key.farkas, farkas) {
        (None, None) => true,
        (Some(pairs), Some(annotation)) => {
            pairs.len() == annotation.coefficients.len()
                && pairs
                    .iter()
                    .zip(&annotation.coefficients)
                    .all(|(pair, coefficient)| *pair == normalized_farkas_pair(coefficient))
        }
        _ => false,
    }
}

/// One inline identity for the common case, or an allocated collision bucket.
#[derive(Debug, Clone)]
pub(super) enum LemmaBucket {
    One((LemmaKey, ProofId)),
    Many(Vec<(LemmaKey, ProofId)>),
}

#[derive(Clone, Copy)]
pub(super) enum ExistingLemma {
    Replace,
    Preserve,
}

impl LemmaBucket {
    pub(super) fn iter(&self) -> impl Iterator<Item = &(LemmaKey, ProofId)> {
        let slice = match self {
            Self::One(entry) => std::slice::from_ref(entry),
            Self::Many(entries) => entries.as_slice(),
        };
        slice.iter()
    }

    pub(super) fn insert(&mut self, key: LemmaKey, id: ProofId, existing: ExistingLemma) -> bool {
        match self {
            Self::One(entry) if entry.0 == key => {
                if matches!(existing, ExistingLemma::Replace) {
                    entry.1 = id;
                }
                false
            }
            Self::One(_) => {
                let old = std::mem::replace(self, Self::Many(Vec::new()));
                let Self::One(first) = old else {
                    *self = old;
                    return false;
                };
                *self = Self::Many(vec![first, (key, id)]);
                true
            }
            Self::Many(entries) => {
                if let Some(slot) = entries.iter_mut().find(|(existing, _)| *existing == key) {
                    if matches!(existing, ExistingLemma::Replace) {
                        slot.1 = id;
                    }
                    false
                } else {
                    entries.push((key, id));
                    true
                }
            }
        }
    }
}

/// Hash-first lemma deduplication map (#A4).
///
/// The common singleton lives inline in the outer map; only a real fingerprint
/// collision promotes it to a `Vec`. Lookup hashes borrowed data and compares
/// exact identity only inside the matching bucket, so hits allocate nothing.
#[derive(Debug, Clone, Default)]
pub(super) struct LemmaDedupMap {
    pub(super) buckets: HashMap<u64, LemmaBucket>,
    pub(super) entries: usize,
}

impl LemmaDedupMap {
    pub(super) fn get(
        &self,
        kind: TheoryLemmaKind,
        clause: &[TermId],
        farkas: Option<&FarkasAnnotation>,
    ) -> Option<ProofId> {
        let fingerprint = lemma_fingerprint(kind, clause, farkas);
        self.buckets
            .get(&fingerprint)?
            .iter()
            .find(|(key, _)| lemma_key_matches(key, kind, clause, farkas))
            .map(|&(_, id)| id)
    }

    /// `HashMap::insert` semantics: replaces the value on an equal key.
    pub(super) fn insert(&mut self, key: LemmaKey, id: ProofId) {
        let fingerprint = lemma_key_fingerprint(&key);
        let added = if let Some(bucket) = self.buckets.get_mut(&fingerprint) {
            bucket.insert(key, id, ExistingLemma::Replace)
        } else {
            self.buckets
                .insert(fingerprint, LemmaBucket::One((key, id)));
            true
        };
        self.entries += usize::from(added);
    }

    /// `entry(key).or_insert(id)` semantics: keeps an existing mapping.
    pub(super) fn or_insert(&mut self, key: LemmaKey, id: ProofId) {
        let fingerprint = lemma_key_fingerprint(&key);
        let added = if let Some(bucket) = self.buckets.get_mut(&fingerprint) {
            bucket.insert(key, id, ExistingLemma::Preserve)
        } else {
            self.buckets
                .insert(fingerprint, LemmaBucket::One((key, id)));
            true
        };
        self.entries += usize::from(added);
    }

    pub(super) fn clear(&mut self) {
        self.buckets.clear();
        self.entries = 0;
    }

    #[cfg(test)]
    pub(super) fn is_empty(&self) -> bool {
        self.entries == 0
    }

    #[cfg(test)]
    pub(super) fn values(&self) -> impl Iterator<Item = &ProofId> {
        self.buckets
            .values()
            .flat_map(|bucket| bucket.iter().map(|(_, id)| id))
    }
}

#[cfg(test)]
mod tests {
    use num_rational::Rational64;

    use super::*;

    #[test]
    fn fingerprint_matches_owned_key_for_every_identity_component() {
        let cases = [
            (TheoryLemmaKind::Generic, vec![TermId(1), TermId(2)], None),
            (
                TheoryLemmaKind::ArraySelectStore { index_eq: false },
                vec![TermId(2), TermId(1), TermId(2)],
                Some(FarkasAnnotation::new(vec![
                    Rational64::new_raw(3, -2),
                    Rational64::new(5, 7),
                ])),
            ),
            (
                TheoryLemmaKind::LraFarkas,
                Vec::new(),
                Some(FarkasAnnotation::new(Vec::new())),
            ),
        ];

        for (kind, clause, annotation) in cases {
            let key = LemmaKey::new(kind, &clause, annotation.as_ref());
            assert_eq!(
                lemma_fingerprint(kind, &clause, annotation.as_ref()),
                lemma_key_fingerprint(&key),
                "borrowed and owned hashes diverged for {key:?}"
            );
            assert!(lemma_key_matches(&key, kind, &clause, annotation.as_ref()));
        }

        let no_annotation = LemmaKey::new(TheoryLemmaKind::Generic, &[], None);
        let empty_annotation = FarkasAnnotation::new(Vec::new());
        assert_ne!(
            lemma_fingerprint(TheoryLemmaKind::Generic, &[], None),
            lemma_fingerprint(TheoryLemmaKind::Generic, &[], Some(&empty_annotation)),
            "None and Some(empty) are distinct LemmaKey identities"
        );
        assert!(!lemma_key_matches(
            &no_annotation,
            TheoryLemmaKind::Generic,
            &[],
            Some(&empty_annotation)
        ));
    }

    #[test]
    fn forced_fingerprint_collision_uses_structural_equality() {
        let kind = TheoryLemmaKind::Generic;
        let target_clause = [TermId(10), TermId(20)];
        let target_key = LemmaKey::new(kind, &target_clause, None);
        let collision_key = LemmaKey::new(kind, &[TermId(99)], None);
        let fingerprint = lemma_fingerprint(kind, &target_clause, None);
        let collision_id = ProofId(7);
        let target_id = ProofId(8);
        let mut map = LemmaDedupMap::default();
        map.buckets.insert(
            fingerprint,
            LemmaBucket::Many(vec![(collision_key, collision_id), (target_key, target_id)]),
        );
        map.entries = 2;

        assert_eq!(map.get(kind, &target_clause, None), Some(target_id));
        assert_ne!(map.get(kind, &target_clause, None), Some(collision_id));
    }
}
