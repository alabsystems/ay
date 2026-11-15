// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Content keys for the canonical order (KC9).
//!
//! Wherever the search can observe an order (the order atoms reach their
//! plug-ins, which numbers LRA's columns and the difference graph's
//! vertices; the order plug-ins are registered), the kernel iterates in the
//! order of a key computed from the term's content, not of its `TermId`
//! (which is the order terms happened to be interned in). The key is a
//! 128-bit Merkle hash over (operator, sort, payload, children's keys): a
//! variable's name is its payload, its store-local id is not.
//!
//! This is the kernel-local stand-in for the term layer's `TermKey` (L0,
//! KC4). The order it gives is total once ties break by `TermId`; a tie
//! needs a 128-bit collision.

use ay_core::kani_compat::DetHashMap as HashMap;
use ay_core::{TermData, TermId, TermStore};

const FNV_PRIME: u64 = 0x0000_0100_0000_01B3;

/// Two FNV-1a lanes with different offset bases, read as one 128-bit key.
struct Hasher128 {
    lo: u64,
    hi: u64,
}

impl Hasher128 {
    const fn new() -> Self {
        Self {
            lo: 0xCBF2_9CE4_8422_2325,
            hi: 0x6C62_272E_07BB_0142,
        }
    }

    fn bytes(&mut self, bytes: &[u8]) {
        for &b in bytes {
            self.lo = (self.lo ^ u64::from(b)).wrapping_mul(FNV_PRIME);
            self.hi = (self.hi ^ u64::from(b.rotate_left(3))).wrapping_mul(FNV_PRIME);
        }
        // A length marker, so concatenations cannot collide by shifting.
        self.lo = (self.lo ^ 0xFF).wrapping_mul(FNV_PRIME);
        self.hi = (self.hi ^ 0xFE).wrapping_mul(FNV_PRIME);
    }

    fn key(&mut self, key: u128) {
        self.bytes(&key.to_le_bytes());
    }

    fn finish(&self) -> u128 {
        (u128::from(self.hi) << 64) | u128::from(self.lo)
    }
}

/// Memoized content keys over one store.
#[derive(Debug, Default)]
pub(crate) struct TermKeys {
    memo: HashMap<TermId, u128>,
}

impl TermKeys {
    /// The content key of `term`.
    pub(crate) fn key(&mut self, terms: &TermStore, term: TermId) -> u128 {
        // Post-order without recursion: a child's key exists before its
        // parent's is computed.
        let mut stack = vec![(term, false)];
        while let Some((t, expanded)) = stack.pop() {
            if self.memo.contains_key(&t) {
                continue;
            }
            let kids = children(terms.get(t));
            if !expanded && kids.iter().any(|k| !self.memo.contains_key(k)) {
                stack.push((t, true));
                stack.extend(kids.into_iter().map(|k| (k, false)));
                continue;
            }
            let key = self.node_key(terms, t, &kids);
            self.memo.insert(t, key);
        }
        self.memo.get(&term).copied().unwrap_or(0)
    }

    fn node_key(&self, terms: &TermStore, t: TermId, kids: &[TermId]) -> u128 {
        let mut h = Hasher128::new();
        let data = terms.get(t);
        match data {
            TermData::Const(c) => {
                h.bytes(b"const");
                h.bytes(format!("{c:?}").as_bytes());
            }
            TermData::Var(name, _) => {
                h.bytes(b"var");
                h.bytes(name.as_bytes());
            }
            TermData::App(sym, _) => {
                h.bytes(b"app");
                h.bytes(format!("{sym:?}").as_bytes());
            }
            TermData::Not(_) => h.bytes(b"not"),
            TermData::Ite(..) => h.bytes(b"ite"),
            TermData::Let(bindings, _) => {
                h.bytes(b"let");
                for (name, _) in bindings {
                    h.bytes(name.as_bytes());
                }
            }
            TermData::Forall(vars, _, _) | TermData::Exists(vars, _, _) => {
                h.bytes(if matches!(data, TermData::Forall(..)) {
                    b"forall"
                } else {
                    b"exists"
                });
                for (name, sort) in vars {
                    h.bytes(name.as_bytes());
                    h.bytes(format!("{sort:?}").as_bytes());
                }
            }
            // `TermData` is non-exhaustive: a node kind added later still
            // gets a key from its full debug form.
            other => {
                h.bytes(b"other");
                h.bytes(format!("{other:?}").as_bytes());
            }
        }
        h.bytes(format!("{:?}", terms.sort(t)).as_bytes());
        let mut kid_keys: Vec<u128> = kids
            .iter()
            .map(|kid| self.memo.get(kid).copied().unwrap_or(0))
            .collect();
        if symmetric(data) {
            // The store orders the sides of `=` by `TermId` (`mk_eq`): the
            // key must not see that order.
            kid_keys.sort_unstable();
        }
        for key in kid_keys {
            h.key(key);
        }
        h.finish()
    }
}

/// An operator whose meaning does not depend on its arguments' order.
fn symmetric(data: &TermData) -> bool {
    matches!(data, TermData::App(sym, _) if matches!(sym.name(), "=" | "distinct"))
}

/// The children of a node, in their argument order.
fn children(data: &TermData) -> Vec<TermId> {
    match data {
        TermData::Const(_) | TermData::Var(..) => Vec::new(),
        TermData::App(_, args) => args.clone(),
        TermData::Not(t) => vec![*t],
        TermData::Ite(c, t, e) => vec![*c, *t, *e],
        TermData::Let(bindings, body) => bindings
            .iter()
            .map(|(_, t)| *t)
            .chain(std::iter::once(*body))
            .collect(),
        TermData::Forall(_, body, triggers) | TermData::Exists(_, body, triggers) => {
            std::iter::once(*body)
                .chain(triggers.iter().flatten().copied())
                .collect()
        }
        _ => Vec::new(),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use ay_core::Sort;
    use num_bigint::BigInt;

    /// The key depends on content, not on the order terms were interned in.
    #[test]
    fn keys_follow_content_not_intern_order() {
        let build = |first_y: bool| {
            let mut terms = TermStore::new();
            let (x, y) = if first_y {
                let y = terms.mk_var("y", Sort::Int);
                (terms.mk_var("x", Sort::Int), y)
            } else {
                let x = terms.mk_var("x", Sort::Int);
                (x, terms.mk_var("y", Sort::Int))
            };
            let three = terms.mk_int(BigInt::from(3));
            let atom_x = terms.mk_le(x, three);
            let atom_y = terms.mk_le(y, three);
            let mut keys = TermKeys::default();
            (keys.key(&terms, atom_x), keys.key(&terms, atom_y))
        };
        let (kx, ky) = build(false);
        assert_ne!(kx, ky);
        assert_eq!(build(true), (kx, ky));
    }

    /// `(= x y)` has one key whichever side the store put first.
    #[test]
    fn equality_keys_ignore_side_order() {
        let mut terms = TermStore::new();
        let x = terms.mk_var("x", Sort::Int);
        let y = terms.mk_var("y", Sort::Int);
        let xy = terms.mk_app(ay_core::Symbol::named("="), vec![x, y], Sort::Bool);
        let yx = terms.mk_app(ay_core::Symbol::named("="), vec![y, x], Sort::Bool);
        let le = terms.mk_le(x, y);
        let ge = terms.mk_le(y, x);
        let mut keys = TermKeys::default();
        assert_eq!(keys.key(&terms, xy), keys.key(&terms, yx));
        assert_ne!(keys.key(&terms, le), keys.key(&terms, ge));
    }
}
