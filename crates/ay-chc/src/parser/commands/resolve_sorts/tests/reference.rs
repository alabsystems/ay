// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! The resolver against the unmemoized algorithm it replaces.
//!
//! `reference_resolve` is the resolution this module performed before it
//! memoized anything, kept verbatim: it walks every path of the tree
//! expansion. On random registries mixing recursive snapshots, mutual
//! placeholders, same-name conflicting definitions, arrays and shared
//! sub-DAGs, the resolver must return the same variant (`Borrowed` exactly
//! when nothing changed) and the same sort: with a fresh memo per root, with
//! one memo shared across roots (as step 5 shares it), and with one memo kept
//! across registry changes (as the parser keeps it across declarations).

use super::*;

fn reference_resolve<'a>(
    registry: &Registry,
    sort: &'a ChcSort,
    seen: &mut FxHashSet<String>,
) -> Cow<'a, ChcSort> {
    match sort {
        ChcSort::Uninterpreted(name) => {
            let Some(datatype) = registry.get(name) else {
                return Cow::Borrowed(sort);
            };
            if !seen.insert(name.clone()) {
                return Cow::Owned(datatype.clone());
            }
            let resolved = reference_resolve(registry, datatype, seen).into_owned();
            seen.remove(name);
            Cow::Owned(resolved)
        }
        ChcSort::Array(key, value) => {
            let key = reference_resolve(registry, key, seen);
            let value = reference_resolve(registry, value, seen);
            if matches!((&key, &value), (Cow::Borrowed(_), Cow::Borrowed(_))) {
                Cow::Borrowed(sort)
            } else {
                Cow::Owned(ChcSort::Array(
                    Box::new(key.into_owned()),
                    Box::new(value.into_owned()),
                ))
            }
        }
        ChcSort::Datatype { name, constructors } => {
            if !seen.insert(name.clone()) {
                return Cow::Borrowed(sort);
            }
            let mut changed: Option<Vec<ChcDtConstructor>> = None;
            for (constructor_index, constructor) in constructors.iter().enumerate() {
                for (selector_index, selector) in constructor.selectors.iter().enumerate() {
                    if let Cow::Owned(sort) = reference_resolve(registry, &selector.sort, seen) {
                        let updated = changed.get_or_insert_with(|| constructors.to_vec());
                        updated[constructor_index].selectors[selector_index].sort = sort;
                    }
                }
            }
            seen.remove(name);
            match changed {
                Some(constructors) => Cow::Owned(ChcSort::Datatype {
                    name: name.clone(),
                    constructors: crate::ChcDtConstructors::new(constructors),
                }),
                None => Cow::Borrowed(sort),
            }
        }
        _ => Cow::Borrowed(sort),
    }
}

/// xorshift64*: deterministic, so a failure reproduces from its seed.
struct Rng(u64);

impl Rng {
    fn new(seed: u64) -> Self {
        Self(seed.wrapping_mul(0x9e37_79b9_7f4a_7c15) | 1)
    }

    fn below(&mut self, bound: u64) -> u64 {
        self.0 ^= self.0 >> 12;
        self.0 ^= self.0 << 25;
        self.0 ^= self.0 >> 27;
        self.0.wrapping_mul(0x2545_f491_4f6c_dd1d) % bound
    }
}

const NAMES: [&str; 4] = ["A", "B", "C", "D"];

/// A random sort: placeholders name declared and undeclared sorts, and
/// datatypes reuse earlier sub-sorts so that values share sub-DAGs.
fn random_sort(rng: &mut Rng, depth: u32, pool: &mut Vec<ChcSort>) -> ChcSort {
    if depth == 0 {
        return match rng.below(4) {
            0 => ChcSort::Int,
            1 => ChcSort::Bool,
            2 => ChcSort::Uninterpreted("Undeclared".into()),
            _ => ChcSort::Uninterpreted(NAMES[rng.below(4) as usize].into()),
        };
    }
    let sort = match rng.below(6) {
        0 if !pool.is_empty() => pool[rng.below(pool.len() as u64) as usize].clone(),
        1 => ChcSort::Array(
            Box::new(random_sort(rng, depth - 1, pool)),
            Box::new(random_sort(rng, depth - 1, pool)),
        ),
        2 => random_sort(rng, 0, pool),
        _ => {
            let name = NAMES[rng.below(4) as usize];
            let constructors = (0..=rng.below(2))
                .map(|constructor| ChcDtConstructor {
                    name: format!("{name}-{constructor}"),
                    selectors: (0..rng.below(3))
                        .map(|selector| crate::expr::ChcDtSelector {
                            name: format!("{name}-{constructor}-{selector}"),
                            sort: random_sort(rng, depth - 1, pool),
                        })
                        .collect(),
                })
                .collect();
            ChcSort::Datatype {
                name: name.into(),
                constructors: crate::ChcDtConstructors::new(constructors),
            }
        }
    };
    pool.push(sort.clone());
    sort
}

/// A registry entry for `name`. A *regular* entry is a datatype of that name,
/// as every parser insertion is; an irregular one may be any sort.
fn random_entry(rng: &mut Rng, name: &str, regular: bool, pool: &mut Vec<ChcSort>) -> ChcSort {
    let depth = if regular { 3 } else { 2 };
    let mut sort = random_sort(rng, depth, pool);
    while regular && !matches!(sort, ChcSort::Datatype { .. }) {
        sort = random_sort(rng, depth, pool);
    }
    match sort {
        ChcSort::Datatype { constructors, .. } => ChcSort::Datatype {
            name: name.into(),
            constructors,
        },
        other => other,
    }
}

#[expect(
    clippy::ptr_arg,
    reason = "the oracle compares Cow ownership as well as sort value"
)]
fn assert_same(label: &str, expected: &Cow<'_, ChcSort>, actual: &Cow<'_, ChcSort>) {
    assert_eq!(
        matches!(expected, Cow::Borrowed(_)),
        matches!(actual, Cow::Borrowed(_)),
        "{label}: changed/unchanged disagrees"
    );
    assert_eq!(
        expected.as_ref(),
        actual.as_ref(),
        "{label}: resolved sorts differ"
    );
}

/// Compare on 400 fixed random registries; returns the memo entries made.
/// The unmemoized oracle expands an irregular placeholder chain into
/// unshared array trees, so irregular registries use shallower sorts.
fn compare_on_random_registries(regular: bool) -> usize {
    let root_depth = if regular { 4 } else { 2 };
    let mut memoized = 0;
    for seed in 1..=400u64 {
        let mut rng = Rng::new(seed);
        let mut pool = Vec::new();
        let mut registry = Registry::default();
        for name in NAMES {
            if rng.below(4) != 0 {
                let entry = random_entry(&mut rng, name, regular, &mut pool);
                registry.insert(name.into(), entry);
            }
        }
        let roots: Vec<ChcSort> = (0..6)
            .map(|_| random_sort(&mut rng, root_depth, &mut pool))
            .chain(registry.values().cloned())
            .collect();
        let mut shared_memo = ResolutionMemo::default();
        let mut shared = Resolver::new(&registry, &mut shared_memo);
        for (index, root) in roots.iter().enumerate() {
            let label = format!("seed {seed}, root {index}");
            let expected = reference_resolve(&registry, root, &mut FxHashSet::default());
            let mut fresh_memo = ResolutionMemo::default();
            let fresh = Resolver::new(&registry, &mut fresh_memo).resolve(root);
            assert_same(&label, &expected, &fresh);
            assert_same(
                &format!("{label} (shared)"),
                &expected,
                &shared.resolve(root),
            );
            assert!(shared.seen.is_empty(), "{label}: path not unwound");
            assert_eq!(shared.snapshot_names_on_path, 0, "{label}");
        }
        drop(shared);
        assert!(!(regular && shared_memo.irregular_registry), "seed {seed}");
        memoized += shared_memo.resolved.len();
    }
    memoized
}

/// One memo kept across random registry changes, each reported through
/// `registry_changed` as the parser reports it; returns the memo entries made.
fn compare_across_registry_changes(regular: bool) -> usize {
    let root_depth = if regular { 4 } else { 2 };
    let mut memoized = 0;
    for seed in 1..=200u64 {
        let mut rng = Rng::new(seed ^ 0x5eed);
        let mut pool = Vec::new();
        let mut registry = Registry::default();
        let mut memo = ResolutionMemo::default();
        for step in 0..24 {
            if rng.below(3) == 0 {
                let name = NAMES[rng.below(4) as usize];
                let entry = random_entry(&mut rng, name, regular, &mut pool);
                memo.registry_changed(name, &entry);
                registry.insert(name.into(), entry);
                continue;
            }
            let root = if rng.below(2) == 0 || registry.is_empty() {
                random_sort(&mut rng, root_depth, &mut pool)
            } else {
                let names: Vec<_> = registry.keys().cloned().collect();
                registry[&names[rng.below(names.len() as u64) as usize]].clone()
            };
            let label = format!("seed {seed}, step {step}");
            let expected = reference_resolve(&registry, &root, &mut FxHashSet::default());
            let actual = Resolver::new(&registry, &mut memo).resolve(&root);
            assert_same(&label, &expected, &actual);
        }
        memoized += memo.resolved.len();
    }
    memoized
}

#[test]
fn resolver_matches_the_unmemoized_algorithm_on_regular_registries() {
    // The comparison must exercise the memo, not only the shortcut.
    assert!(compare_on_random_registries(true) > 0);
}

#[test]
fn resolver_matches_the_unmemoized_algorithm_on_irregular_registries() {
    compare_on_random_registries(false);
}

#[test]
fn a_kept_memo_matches_the_unmemoized_algorithm_across_registry_changes() {
    assert!(compare_across_registry_changes(true) > 0);
    compare_across_registry_changes(false);
}

#[test]
fn registry_resolution_matches_resolving_every_entry() {
    // Simulated `declare-datatypes` commands. Step 4 stores a block of one or
    // two datatypes whose fields name any datatype, declared or not, and
    // reuse earlier registry values as `parse_sort` would. Step 5 is then
    // replayed as the parser ran it before memoizing (every entry resolved
    // against the registry as it stood, every result stored) and compared
    // with `resolve_registry` on one memo kept across commands.
    for seed in 1..=300u64 {
        let mut rng = Rng::new(seed ^ 0xb10c);
        let mut pool = Vec::new();
        let mut naive = Registry::default();
        let mut registry = Registry::default();
        let mut memo = ResolutionMemo::default();
        for command in 0..8 {
            let first = rng.below(4) as usize;
            let mut block = vec![NAMES[first].to_owned()];
            if rng.below(2) == 0 {
                block.push(NAMES[(first + 1 + rng.below(3) as usize) % 4].to_owned());
            }
            for name in &block {
                let entry = random_entry(&mut rng, name, true, &mut pool);
                naive.insert(name.clone(), entry.clone());
                set_entry(&mut registry, &mut memo, name.clone(), entry);
            }
            let before = naive.clone();
            for (name, sort) in &before {
                let resolved = reference_resolve(&before, sort, &mut FxHashSet::default());
                naive.insert(name.clone(), resolved.into_owned());
            }
            resolve_registry(&mut registry, &mut memo, &block);
            assert_eq!(naive, registry, "seed {seed}, command {command}");
            pool.extend(registry.values().cloned());
        }
    }
}
