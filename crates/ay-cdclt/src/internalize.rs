// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Constructs the engine encodes itself before Tseitin (design §3.3): each
//! rewrite is an equivalence or a conservative definition, so the check's
//! verdict is the input's.
//!
//! - `(distinct t1 .. tn)` becomes the pairwise disequalities;
//! - `(= t1 .. tn)` with n > 2 becomes the chain `t1 = t2 ∧ .. ∧ tn-1 = tn`;
//! - when the hub has work (an uninterpreted application or sort), a
//!   term-level `(ite c a b)` of a non-Boolean sort becomes a fresh constant
//!   `v` with `¬c ∨ v = a` and `c ∨ v = b`, so the hub and the arithmetic see
//!   an ordinary term. Without it, an arithmetic ite stays: the arithmetic
//!   plug-in links it itself, and nothing else can hold one.
//!
//! The assumptions of a check are rewritten exactly like its assertions
//! (they are formulas of the same check), and the definitions their names
//! need are asserted for that check only: a definition is conservative, so
//! it holds in some extension of every model, assumed or not.
//!
//! KC9: a name is spelled from the content key of the `ite` it names
//! (`term_key.rs`), never from a `TermId`, so the order the kernel derives
//! from names (hub nodes, atoms) does not follow the order terms were
//! interned in. Two different `ite`s of one check whose keys collide would
//! share a name; that is refused, so a name always means one `ite`.

use ay_core::kani_compat::{DetHashMap as HashMap, DetHashSet as HashSet};
use ay_core::{Sort, Symbol, TermData, TermId, TermStore};

use crate::content::is_uf_app;
use crate::plugin::GiveUp;
use crate::term_key::TermKeys;

/// The prefix of an internalized `ite`'s name; the rest is its content key.
const ITE_NAME_PREFIX: &str = "__ay_cdclt_ite_";

/// What the input needs.
#[derive(Default)]
struct Needs {
    nary: bool,
    ite: bool,
    /// An uninterpreted application or a term of an uninterpreted sort.
    hub: bool,
}

fn needs(terms: &TermStore, roots: &[TermId]) -> Needs {
    let mut found = Needs::default();
    let mut seen: HashSet<TermId> = HashSet::default();
    let mut stack: Vec<TermId> = roots.to_vec();
    while let Some(term) = stack.pop() {
        if !seen.insert(term) {
            continue;
        }
        if is_uf_app(terms, term) || terms.sort(term).is_uninterpreted() {
            found.hub = true;
        }
        match terms.get(term) {
            TermData::App(Symbol::Named(name), args) => {
                let name: &str = name;
                if name == "distinct" || (name == "=" && args.len() > 2) {
                    found.nary = true;
                }
                stack.extend(args.iter().copied());
            }
            TermData::App(_, args) => stack.extend(args.iter().copied()),
            TermData::Ite(c, t, e) => {
                if terms.sort(term) != &Sort::Bool {
                    found.ite = true;
                }
                stack.extend([*c, *t, *e]);
            }
            TermData::Not(inner) => stack.push(*inner),
            _ => {}
        }
    }
    found
}

/// The assertions and the assumptions with the constructs above encoded
/// (the input when there is nothing to do), and whether the hub has work.
pub(crate) fn normalize(
    terms: &mut TermStore,
    assertions: &[TermId],
    assumptions: &[TermId],
) -> Result<Normalized, GiveUp> {
    let roots: Vec<TermId> = assertions.iter().chain(assumptions).copied().collect();
    let found = needs(terms, &roots);
    let mut rewriter = Rewriter {
        name_ites: found.ite && found.hub,
        memo: HashMap::default(),
        keys: TermKeys::default(),
        names: HashMap::default(),
        defs: Vec::new(),
    };
    let out = if found.nary || rewriter.name_ites {
        roots
            .iter()
            .map(|&root| rewriter.rewrite(terms, root))
            .collect::<Result<Vec<_>, _>>()?
    } else {
        roots
    };
    let (asserted, assumed) = out.split_at(assertions.len());
    let mut encoded = asserted.to_vec();
    encoded.extend(rewriter.defs);
    let changed = encoded != assertions || assumed != assumptions;
    Ok(Normalized {
        assertions: encoded,
        assumptions: assumed.to_vec(),
        changed,
        hub: found.hub,
    })
}

/// The result of [`normalize`].
pub(crate) struct Normalized {
    /// The assertions the encoding asserts: the rewritten assertions, then
    /// the definitions of every name (the assumptions' included).
    pub(crate) assertions: Vec<TermId>,
    /// The rewritten assumptions, one per input assumption, in its order.
    pub(crate) assumptions: Vec<TermId>,
    /// Whether anything differs from the input (a recorded refutation would
    /// be about other formulas).
    pub(crate) changed: bool,
    /// An uninterpreted application or sort occurs: the hub has work.
    pub(crate) hub: bool,
}

impl Normalized {
    /// Every formula of the check: the encoded assertions, then the
    /// assumptions.
    pub(crate) fn roots(&self) -> Vec<TermId> {
        [self.assertions.as_slice(), self.assumptions.as_slice()].concat()
    }
}

/// One bottom-up rewrite shared by every root of a check.
struct Rewriter {
    name_ites: bool,
    memo: HashMap<TermId, TermId>,
    keys: TermKeys,
    /// Content key -> (the `ite` named, its name).
    names: HashMap<u128, (TermId, TermId)>,
    defs: Vec<TermId>,
}

impl Rewriter {
    /// Rebuild `root` bottom-up with `distinct` and n-ary `=` expanded and,
    /// when the hub has work, term-level ites named.
    fn rewrite(&mut self, terms: &mut TermStore, root: TermId) -> Result<TermId, GiveUp> {
        let mut stack: Vec<(TermId, bool)> = vec![(root, false)];
        while let Some((term, ready)) = stack.pop() {
            if self.memo.contains_key(&term) {
                continue;
            }
            let data = terms.get(term).clone();
            let children: Vec<TermId> = match &data {
                TermData::App(_, args) => args.clone(),
                TermData::Ite(c, t, e) => vec![*c, *t, *e],
                TermData::Not(inner) => vec![*inner],
                _ => Vec::new(),
            };
            if !ready && children.iter().any(|c| !self.memo.contains_key(c)) {
                stack.push((term, true));
                stack.extend(children.into_iter().map(|c| (c, false)));
                continue;
            }
            let new: Vec<TermId> = children.iter().map(|c| self.memo[c]).collect();
            let rebuilt = rebuild(terms, term, &data, &new);
            let rebuilt = self.name(terms, rebuilt)?;
            self.memo.insert(term, rebuilt);
        }
        Ok(self.memo[&root])
    }

    /// The name of `term` when it is a non-Boolean `ite` to be named (with
    /// its two definitions recorded once), else `term`.
    fn name(&mut self, terms: &mut TermStore, term: TermId) -> Result<TermId, GiveUp> {
        if !self.name_ites || terms.sort(term) == &Sort::Bool {
            return Ok(term);
        }
        let TermData::Ite(c, t, e) = terms.get(term).clone() else {
            return Ok(term);
        };
        let key = self.keys.key(terms, term);
        match self.names.get(&key) {
            Some(&(ite, name)) if ite == term => return Ok(name),
            Some(_) => {
                return Err(GiveUp::new(
                    "two term-level ites share a content key (a 128-bit collision)",
                ))
            }
            None => {}
        }
        let sort = terms.sort(term).clone();
        let name = terms.mk_var(format!("{ITE_NAME_PREFIX}{key:032x}"), sort);
        let eq_t = terms.mk_eq(name, t);
        let eq_e = terms.mk_eq(name, e);
        let not_c = terms.mk_not(c);
        let then_def = terms.mk_or(vec![not_c, eq_t]);
        let else_def = terms.mk_or(vec![c, eq_e]);
        self.defs.push(then_def);
        self.defs.push(else_def);
        self.names.insert(key, (term, name));
        Ok(name)
    }
}

/// `term` over its rewritten children `new`, with `distinct` and n-ary `=`
/// expanded.
fn rebuild(terms: &mut TermStore, term: TermId, data: &TermData, new: &[TermId]) -> TermId {
    match data {
        TermData::App(Symbol::Named(name), _) if name.as_ref() == "distinct" => {
            let mut pairs = Vec::new();
            for i in 0..new.len() {
                for j in i + 1..new.len() {
                    let eq = terms.mk_eq(new[i], new[j]);
                    pairs.push(terms.mk_not(eq));
                }
            }
            terms.mk_and(pairs)
        }
        TermData::App(Symbol::Named(name), _) if name.as_ref() == "=" && new.len() > 2 => {
            let links: Vec<TermId> = new.windows(2).map(|w| terms.mk_eq(w[0], w[1])).collect();
            terms.mk_and(links)
        }
        TermData::App(sym, args) if args.as_slice() != new => {
            terms.rebuild_app(sym, new.to_vec(), term)
        }
        TermData::Ite(c, t, e) if [*c, *t, *e] != new[..] => terms.mk_ite(new[0], new[1], new[2]),
        TermData::Not(inner) if *inner != new[0] => terms.mk_not(new[0]),
        _ => term,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// The names `normalize` gives `(ite c a b)` under `(= (f _) a)` and
    /// `(ite d b a)` under `(= (f _) b)`, with `pad` unrelated terms interned
    /// first and the two ites interned in either order.
    fn ite_names(pad: usize, swapped: bool) -> (String, String) {
        let mut terms = TermStore::new();
        for i in 0..pad {
            let _ = terms.mk_var(format!("pad{i}"), Sort::Int);
        }
        let u = Sort::Uninterpreted("U".to_string());
        let [a, b] = ["a", "b"].map(|n| terms.mk_var(n, u.clone()));
        let [c, d] = ["c", "d"].map(|n| terms.mk_var(n, Sort::Bool));
        let (first, second) = if swapped {
            let second = terms.mk_ite(d, b, a);
            (terms.mk_ite(c, a, b), second)
        } else {
            let first = terms.mk_ite(c, a, b);
            (first, terms.mk_ite(d, b, a))
        };
        let mut root = |ite, side| {
            let app = terms.mk_app(Symbol::named("f"), vec![ite], u.clone());
            terms.mk_eq(app, side)
        };
        let roots = [root(first, a), root(second, b)];
        let normalized = normalize(&mut terms, &roots, &[]).expect("no key collision");
        let name_in = |root: TermId| {
            let mut stack = vec![root];
            while let Some(t) = stack.pop() {
                if let TermData::Var(name, _) = terms.get(t) {
                    if name.starts_with(ITE_NAME_PREFIX) {
                        return name.clone();
                    }
                }
                stack.extend(terms.children(t));
            }
            panic!("the ite under {root:?} was not named");
        };
        (
            name_in(normalized.assertions[0]),
            name_in(normalized.assertions[1]),
        )
    }

    /// KC9: a named ite's name is spelled from its content key, so neither
    /// unrelated terms interned first (every `TermId` shifted) nor another
    /// ite interned first changes it, and the order the kernel derives from
    /// names does not follow interning. (The names used to be
    /// `__ay_ite_def_{TermId}`.)
    #[test]
    fn ite_names_follow_content_not_term_ids() {
        let plain = ite_names(0, false);
        assert_ne!(plain.0, plain.1, "two different ites, two names");
        for (pad, swapped) in [(0, true), (7, false), (7, true)] {
            assert_eq!(
                ite_names(pad, swapped),
                plain,
                "pad {pad}, swapped {swapped}"
            );
        }
    }
}
