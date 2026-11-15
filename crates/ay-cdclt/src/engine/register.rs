// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Registration by content (design H2) in canonical order (KC9): every
//! theory atom of the encoding gets an owner, the plug-ins are created in
//! the families' fixed order, and the atoms reach their owners in content-key
//! order, never in the order the terms were interned or encoded.

use std::collections::BTreeMap;

use ay_core::{TermId, TermStore};
use ay_diff_logic::{IStar, RStar};
use ay_sat::{Solver, Variable};

use super::EngineConfig;
use crate::atoms::{is_kernel_atom, owner_of, AtomTable, Family, Owner};
use crate::content::{canonical_apps, Scan};
use crate::dl::DlPlugin;
use crate::dl_shape::{diff_shape, fits_fast_lane, shared_fits, DiffShape};
use crate::euf::EufPlugin;
use crate::hub_layout::HubLayout;
use crate::linear::Linearizer;
use crate::lra::LraPlugin;
use crate::plugin::{GiveUp, ThId, TheoryPlugin};
use crate::term_key::TermKeys;

/// The plug-ins, their families and the atom table, ready for a search.
pub(super) struct Registration {
    pub(super) plugins: Vec<Box<dyn TheoryPlugin>>,
    pub(super) families: Vec<(Family, ThId)>,
    pub(super) atoms: AtomTable,
    /// The atoms' variables in canonical (content-key) order: the order the
    /// kernel internalizes them in.
    pub(super) order: Vec<u32>,
    /// The hub's nodes before the search: the plug-ins were chosen for them.
    pub(super) layout: HubLayout,
}

/// Give every theory atom of the encoding an owner, by content (H2), and
/// record the Boolean structure's variables for lemmas that name it. A
/// plug-in exists iff an atom or a hub node needs it: EUF for any
/// uninterpreted application or sort, and the arithmetic of every arithmetic
/// node (a shared term, design H1). Each arithmetic plug-in is chosen for
/// the atoms it owns and the hub nodes it will carry ([`HubLayout`]).
pub(super) fn register(
    terms: &TermStore,
    term_to_var: &BTreeMap<TermId, u32>,
    solver: &mut Solver,
    cfg: &EngineConfig,
    scanned: &Scan,
) -> Result<Registration, GiveUp> {
    let mut atoms = AtomTable::default();
    let mut owned: Vec<(u32, TermId, Family)> = Vec::new();
    let mut ground: Vec<(u32, TermId, Family)> = Vec::new();
    for (&term, &dimacs_var) in term_to_var {
        let var = dimacs_var
            .checked_sub(1)
            .ok_or_else(|| GiveUp::new("Tseitin variable 0"))?;
        if !is_kernel_atom(terms, term) {
            atoms.insert_structure(var, term);
            continue;
        }
        match owner_of(terms, term)? {
            Owner::Family(family) => owned.push((var, term, family)),
            Owner::Ground(family) => ground.push((var, term, family)),
        }
    }
    // KC9: atoms in content order, which is also the order the hub watches
    // equalities in.
    let mut keys = TermKeys::default();
    let mut in_order: Vec<TermId> = owned.iter().chain(&ground).map(|&(_, t, _)| t).collect();
    in_order.sort_by_cached_key(|&term| (keys.key(terms, term), term));
    let layout = HubLayout::new(terms, &canonical_apps(terms, &scanned.uf_apps), &in_order);
    let mut needed = layout.families(terms);
    if scanned.uninterpreted_sort && !needed.contains(&Family::Uf) {
        needed.push(Family::Uf);
    }
    // A ground comparison joins the arithmetic the check already has (the
    // first in the families' fixed order, KC9).
    let joined = owned
        .iter()
        .map(|&(_, _, f)| f)
        .chain(needed.iter().copied())
        .filter(|f| f.is_arith())
        .min();
    owned.extend(
        ground
            .into_iter()
            .map(|(var, term, family)| (var, term, joined.unwrap_or(family))),
    );
    owned.sort_by_cached_key(|&(_, term, _)| (keys.key(terms, term), term));
    // KC9: plug-ins in the families' fixed order, atoms in content order.
    let mut present: Vec<Family> = owned.iter().map(|&(_, _, f)| f).collect();
    present.extend(needed.iter().copied());
    present.sort_unstable();
    present.dedup();
    let opaque = !scanned.uf_apps.is_empty();
    let mut plugins: Vec<Box<dyn TheoryPlugin>> = Vec::new();
    let mut families: Vec<(Family, ThId)> = Vec::new();
    for family in present {
        let id = ThId::try_from(plugins.len()).map_err(|_| GiveUp::new("too many plug-ins"))?;
        let members: Vec<TermId> = owned
            .iter()
            .filter(|&&(_, _, f)| f == family)
            .map(|&(_, term, _)| term)
            .collect();
        let shared: Vec<TermId> = layout.shared(terms, family);
        plugins.push(family_plugin(terms, family, &members, &shared, cfg, opaque));
        families.push((family, id));
    }
    let mut order = Vec::with_capacity(owned.len());
    for (var, term, family) in owned {
        let owner = families
            .iter()
            .find(|(f, _)| *f == family)
            .map(|&(_, id)| id)
            .ok_or_else(|| GiveUp::new("atom family without a plug-in"))?;
        atoms.insert(var, term, owner);
        solver.freeze(Variable::new(var));
        order.push(var);
    }
    if families.iter().filter(|(f, _)| f.is_arith()).count() > 1 {
        // Two arithmetic tableaux would not share variables: `to_real`
        // and mixed comparisons need the one LIRA tableau (roadmap AL).
        return Err(GiveUp::new(
            "Int and Real atoms in one check need one LIRA tableau (roadmap AL)",
        ));
    }
    Ok(Registration {
        plugins,
        families,
        atoms,
        order,
        layout,
    })
}

/// The plug-in for one family. Arithmetic chooses its sub-module by the
/// content of the check (design §2, "Arith (LRA/LIA/DL)"): difference logic
/// when every atom is a difference atom, the simplex otherwise. With
/// uninterpreted applications (`opaque`), the simplex treats them as opaque
/// variables the hub decides.
fn family_plugin(
    terms: &TermStore,
    family: Family,
    atoms: &[TermId],
    shared: &[TermId],
    cfg: &EngineConfig,
    opaque: bool,
) -> Box<dyn TheoryPlugin> {
    if family == Family::Uf {
        return Box::new(EufPlugin::new());
    }
    let integer = family == Family::IntArith;
    if cfg.difference_logic {
        let mut lin = Linearizer::default();
        let shapes: Option<Vec<DiffShape>> = atoms
            .iter()
            .map(|&atom| diff_shape(terms, &mut lin, atom))
            .collect();
        let shared_ok = shared.iter().all(|&t| shared_fits(terms, &mut lin, t));
        if let (Some(shapes), true) = (shapes, shared_ok) {
            return if fits_fast_lane(&shapes, integer) {
                Box::new(DlPlugin::<IStar>::new(integer))
            } else {
                Box::new(DlPlugin::<RStar>::new(integer))
            };
        }
    }
    if integer {
        let mut plugin = LraPlugin::new_integer(terms).with_opaque_applications(opaque);
        plugin.set_bcp_implied_bounds(cfg.integer_bcp_implied_bounds);
        Box::new(plugin)
    } else {
        Box::new(LraPlugin::new(terms).with_opaque_applications(opaque))
    }
}
