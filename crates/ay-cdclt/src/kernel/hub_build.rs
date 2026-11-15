// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Building the hub before the search from the registration's layout
//! (`hub_layout.rs`): the kernel creates exactly the nodes the plug-ins were
//! chosen for, in the layout's canonical order (KC9).

use ay_core::{Sort, TermData, TermId};

use super::Kernel;
use crate::content::arithmetic;
use crate::hub_layout::{unregistered_app, HubLayout, Step};
use crate::plugin::GiveUp;

impl Kernel<'_> {
    /// The hub's registration-time nodes, exactly as the layout lists them
    /// (applications in canonical order with their arguments first, then the
    /// watched equality atoms in the atoms' canonical order, KC9): the
    /// plug-ins registration chose were chosen for these terms.
    pub(crate) fn build_hub(&mut self, layout: &HubLayout) -> Result<(), GiveUp> {
        for &step in &layout.steps {
            if unregistered_app(self.terms, step) {
                return Err(GiveUp::new(
                    "an uninterpreted application reached the hub unregistered",
                ));
            }
            match step {
                Step::Leaf(term) => {
                    self.hub_leaf(term)?;
                }
                Step::Eq(eq) => self.add_eq_node(eq)?,
                Step::Arg(arg) => {
                    let n = self
                        .hub
                        .node_of(arg)
                        .ok_or_else(|| GiveUp::new("an application argument has no hub node"))?;
                    let arith = arithmetic(self.terms.sort(arg));
                    self.hub.mark_shared(n, arith);
                }
                Step::App(app) => self.add_app_node(app)?,
            }
        }
        // Registration-time congruences hold at level 0.
        self.hub.propagate();
        self.stats.hub_nodes = self.hub.len() as u64;
        Ok(())
    }

    /// The node of an application whose arguments are nodes.
    fn add_app_node(&mut self, app: TermId) -> Result<(), GiveUp> {
        if self.hub.node_of(app).is_some() {
            return Ok(());
        }
        let TermData::App(sym, args) = self.terms.get(app).clone() else {
            return Err(GiveUp::new("a hub application is not an application"));
        };
        let mut arg_nodes = Vec::with_capacity(args.len());
        for &arg in &args {
            let n = self
                .hub
                .node_of(arg)
                .ok_or_else(|| GiveUp::new("an application argument has no hub node"))?;
            arg_nodes.push(n);
        }
        let sort = self.terms.sort(app).clone();
        let func = self.hub.func_id(sym.name(), args.len(), &sort);
        let is_bool = sort == Sort::Bool;
        let n = self.hub.add_app(app, func, arg_nodes, is_bool);
        self.attach_vars(n, app)
    }

    /// The node of an equality whose sides are nodes (before the search).
    fn add_eq_node(&mut self, eq: TermId) -> Result<(), GiveUp> {
        if self.hub.node_of(eq).is_some() {
            return Ok(());
        }
        let TermData::App(_, args) = self.terms.get(eq) else {
            return Err(GiveUp::new("a hub equality is not an application"));
        };
        let mut it = args.iter();
        let (Some(&a), Some(&b), None) = (it.next(), it.next(), it.next()) else {
            return Err(GiveUp::new("a hub equality is not binary"));
        };
        let (Some(na), Some(nb)) = (self.hub.node_of(a), self.hub.node_of(b)) else {
            return Err(GiveUp::new("a hub equality's side has no node"));
        };
        let n = self.hub.add_eq(eq, na, nb);
        self.map_hub_var(n, eq)
    }
}
