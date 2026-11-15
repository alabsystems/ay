// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The atom table and the content registry (design §3.3, §4.2).

use ay_core::kani_compat::DetHashSet as HashSet;
use ay_core::{is_theory_atom, AtomHandle, Sort, TermData, TermId, TermStore};

use crate::content::{is_uf_app, COMPARISONS};
use crate::linear::Linearizer;
use crate::plugin::{GiveUp, ThId};

/// One SAT variable that names a theory atom.
#[derive(Debug, Clone, Copy)]
pub(crate) struct AtomEntry {
    pub(crate) term: TermId,
    pub(crate) owner: ThId,
    /// The owner's handle (KC3), set once the owner internalized the atom.
    pub(crate) handle: Option<AtomHandle>,
}

/// `by_term` slot of a term with no SAT variable.
const NO_VAR: u32 = u32::MAX;

/// `var <-> term`, append-only for the life of one engine check (INV-S6).
///
/// Every term with a SAT variable is in `by_term`: theory atoms, which also
/// have an owner in `by_var`, and the Boolean structure of the encoding, which
/// has none. A lemma may therefore name a Boolean term the encoding already
/// has (an `ite` condition, say) without minting it.
///
/// Both directions are dense vectors (KC3): `by_term` is indexed by the
/// term's id, so mapping a propagated or reason literal to its variable is
/// one array read, never a hash lookup. A store's ids are dense, and the
/// vector only reaches the largest id that has a variable.
#[derive(Debug, Default)]
pub(crate) struct AtomTable {
    by_var: Vec<Option<AtomEntry>>,
    by_term: Vec<u32>,
}

impl AtomTable {
    /// Bind a theory atom to its variable and owner.
    pub(crate) fn insert(&mut self, var: u32, term: TermId, owner: ThId) {
        let idx = var as usize;
        if self.by_var.len() <= idx {
            self.by_var.resize(idx + 1, None);
        }
        if let Some(slot) = self.by_var.get_mut(idx) {
            debug_assert!(slot.is_none(), "atom binding is append-only");
            *slot = Some(AtomEntry {
                term,
                owner,
                handle: None,
            });
        }
        if let Some(slot) = self.term_slot(term) {
            *slot = var;
        }
    }

    /// Record the owner's handle for the atom of `var` (KC3).
    pub(crate) fn set_handle(&mut self, var: u32, handle: AtomHandle) {
        if let Some(Some(entry)) = self.by_var.get_mut(var as usize) {
            entry.handle = Some(handle);
        }
    }

    /// Bind an unowned Boolean term of the encoding to its variable.
    pub(crate) fn insert_structure(&mut self, var: u32, term: TermId) {
        if let Some(slot) = self.term_slot(term) {
            if *slot == NO_VAR {
                *slot = var;
            }
        }
    }

    /// The `by_term` slot of `term`, grown to reach it.
    fn term_slot(&mut self, term: TermId) -> Option<&mut u32> {
        let idx = term.0 as usize;
        if self.by_term.len() <= idx {
            self.by_term.resize(idx + 1, NO_VAR);
        }
        self.by_term.get_mut(idx)
    }

    pub(crate) fn var_of(&self, term: TermId) -> Option<u32> {
        self.by_term
            .get(term.0 as usize)
            .copied()
            .filter(|&var| var != NO_VAR)
    }

    /// Every bound term with its variable, atoms and structure alike, in
    /// term-id order.
    pub(crate) fn bindings(&self) -> impl Iterator<Item = (TermId, u32)> + '_ {
        self.by_term
            .iter()
            .enumerate()
            .filter(|&(_, &var)| var != NO_VAR)
            .filter_map(|(idx, &var)| Some((TermId(u32::try_from(idx).ok()?), var)))
    }

    pub(crate) fn entry(&self, var: usize) -> Option<AtomEntry> {
        self.by_var.get(var).copied().flatten()
    }

    /// The term of every SAT variable the encoding or the search named, by
    /// variable index (the proof assembler's literal-to-term map).
    pub(crate) fn var_terms(&self) -> Vec<Option<TermId>> {
        let len = self
            .bindings()
            .map(|(_, v)| v as usize + 1)
            .max()
            .unwrap_or(0)
            .max(self.by_var.len());
        let mut out = vec![None; len];
        for (term, var) in self.bindings() {
            if let Some(slot) = out.get_mut(var as usize) {
                *slot = Some(term);
            }
        }
        out
    }

    /// Owned atoms with their variable index.
    pub(crate) fn owned(&self) -> impl Iterator<Item = (usize, AtomEntry)> + '_ {
        self.by_var
            .iter()
            .enumerate()
            .filter_map(|(var, slot)| slot.map(|entry| (var, entry)))
    }
}

/// The theory family that owns an atom, decided by the atom's content. The
/// declaration order is the order plug-ins are registered in (KC9).
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub(crate) enum Family {
    /// Linear real arithmetic comparisons and equalities.
    RealArith,
    /// Linear integer arithmetic comparisons and equalities (LRA in integer
    /// mode, with branch and bound in the search).
    IntArith,
    /// Equalities over uninterpreted sorts and uninterpreted predicates: the
    /// EUF plug-in over the hub (design H1).
    Uf,
}

impl Family {
    pub(crate) const fn name(self) -> &'static str {
        match self {
            Self::RealArith => "real arithmetic",
            Self::IntArith => "integer arithmetic",
            Self::Uf => "uninterpreted functions",
        }
    }

    /// The arithmetic family of a sort.
    pub(crate) const fn of_arith_sort(sort: &Sort) -> Option<Self> {
        match sort {
            Sort::Real => Some(Self::RealArith),
            Sort::Int => Some(Self::IntArith),
            _ => None,
        }
    }

    /// Whether the family is one of the arithmetic tableaux.
    pub(crate) const fn is_arith(self) -> bool {
        matches!(self, Self::RealArith | Self::IntArith)
    }
}

/// Whether the kernel treats an encoded Boolean term as a theory atom.
///
/// `is_theory_atom` also answers yes for an `ite` biconditional and for a
/// binary `=` over Booleans; Tseitin encodes both completely (`encode_ite`,
/// `encode_eq`), so for the kernel they are Boolean structure. Anything else
/// it calls an atom must find an owner.
pub(crate) fn is_kernel_atom(terms: &TermStore, term: TermId) -> bool {
    if !is_theory_atom(terms, term) {
        return false;
    }
    match terms.get(term) {
        TermData::Ite(..) => false,
        TermData::App(sym, args) if sym.name() == "=" && args.len() == 2 => {
            terms.sort(args[0]) != &Sort::Bool
        }
        _ => true,
    }
}

/// `(= a b)` as an atom a lemma can name: the store's equality of `a` and
/// `b` when it exists, else one built without `TermStore::mk_eq`'s `ite`
/// rewrites (which turn `(= (ite c a b) a)` into `(or c (= b a))` and
/// `(= (ite c a b) x)` into an `ite` of equalities, formulas no plug-in
/// owns). Constant folding still applies, so the result may be `true` or
/// `false`, which a lemma handles like any Boolean constant.
pub(crate) fn eq_atom(terms: &mut TermStore, a: TermId, b: TermId) -> TermId {
    match terms.find_eq(a, b) {
        Some(eq) => eq,
        None => terms.mk_eq_coerce_no_ite_expand(a, b),
    }
}

/// How an atom is owned.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum Owner {
    /// By the family of its variables' sort.
    Family(Family),
    /// A comparison of constants: any arithmetic plug-in evaluates it, so it
    /// joins the one the check has (or its arguments' sort if there is none).
    Ground(Family),
}

/// Route an atom by content (design H2).
///
/// - An arithmetic comparison or equality belongs to the family of the sort
///   of its non-constant subterms, which must not mix Int and Real (a
///   comparison of constants follows its first argument); uninterpreted
///   applications inside it are opaque leaves the hub decides;
/// - an equality over an uninterpreted sort, or an uninterpreted predicate,
///   belongs to EUF;
/// - every other atom is named in the give-up, before the search starts.
pub(crate) fn owner_of(terms: &TermStore, atom: TermId) -> Result<Owner, GiveUp> {
    if is_uf_app(terms, atom) {
        return Ok(Owner::Family(Family::Uf));
    }
    let TermData::App(sym, args) = terms.get(atom) else {
        return Err(GiveUp::new(format!(
            "no plug-in owns atom {atom:?} (not an application)"
        )));
    };
    let op = sym.name();
    let Some(&first) = args.first() else {
        return Err(GiveUp::new(format!("no plug-in owns operator `{op}`")));
    };
    if !(op == "=" || COMPARISONS.contains(&op)) {
        return Err(GiveUp::new(format!("no plug-in owns operator `{op}`")));
    }
    let family = match terms.sort(first) {
        Sort::Real => Family::RealArith,
        Sort::Int => Family::IntArith,
        Sort::Uninterpreted(_) if op == "=" && args.len() == 2 => {
            return Ok(Owner::Family(Family::Uf))
        }
        other => {
            return Err(GiveUp::new(format!(
                "no plug-in owns `{op}` over {other:?}"
            )))
        }
    };
    let sorts = numeric_sorts(terms, args);
    if let Some(other) = sorts.other {
        return Err(GiveUp::new(format!("no plug-in owns `{op}` over {other}")));
    }
    // Every operator inside the atom must be one arithmetic owns (H2): an
    // unowned one is named here, before the search, not after it.
    let mut lin = Linearizer::default();
    for &arg in args {
        lin.linearize(terms, arg)?;
    }
    match (sorts.real, sorts.int) {
        (true, true) => Err(GiveUp::new(format!(
            "`{op}` mixes Int and Real terms: needs one LIRA tableau (roadmap AL); \
             Int {:.60}, Real {:.60}",
            sorts.int_example, sorts.real_example
        ))),
        (false, false) => Ok(Owner::Ground(family)),
        // The variables decide, never the first argument's sort: a numeral
        // is sort-neutral, so `(< 3 x)` over a Real `x` may carry an
        // Int-sorted `3`, and routing it by that `3` would tighten a Real
        // bound as an integer one.
        (true, false) => Ok(Owner::Family(Family::RealArith)),
        (false, true) => Ok(Owner::Family(Family::IntArith)),
    }
}

/// Which numeric sorts occur below `roots`, stopping at uninterpreted
/// applications (opaque leaves of the arithmetic, whose arguments the hub
/// owns).
struct NumericSorts {
    real: bool,
    int: bool,
    other: Option<String>,
    int_example: String,
    real_example: String,
}

fn numeric_sorts(terms: &TermStore, roots: &[TermId]) -> NumericSorts {
    let mut found = NumericSorts {
        real: false,
        int: false,
        other: None,
        int_example: String::new(),
        real_example: String::new(),
    };
    let mut seen: HashSet<TermId> = HashSet::default();
    let mut stack: Vec<TermId> = roots.to_vec();
    while let Some(term) = stack.pop() {
        if !seen.insert(term) {
            continue;
        }
        // A numeral is sort-neutral: `(= x 1)` over a Real `x` may carry an
        // Int-sorted `1`, and its value is exact in either tableau.
        if matches!(terms.get(term), TermData::Const(_)) {
            continue;
        }
        match terms.sort(term) {
            Sort::Real if !found.real => {
                found.real = true;
                found.real_example = format!("{:?}", terms.get(term));
            }
            Sort::Int if !found.int => {
                found.int = true;
                found.int_example = format!("{:?}", terms.get(term));
            }
            Sort::Real | Sort::Int => {}
            Sort::Bool => {}
            other => {
                found.other.get_or_insert_with(|| format!("{other:?}"));
            }
        }
        if is_uf_app(terms, term) {
            continue;
        }
        match terms.get(term) {
            TermData::App(_, args) => stack.extend(args.iter().copied()),
            TermData::Ite(c, t, e) => stack.extend([*c, *t, *e]),
            TermData::Not(inner) => stack.push(*inner),
            _ => {}
        }
    }
    found
}
