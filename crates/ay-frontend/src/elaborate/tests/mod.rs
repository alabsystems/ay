// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;
use crate::parser::parse;
use ay_core::{Symbol, TermData};

fn collect_var_names(terms: &TermStore, term: TermId, out: &mut Vec<String>) {
    match terms.get(term) {
        TermData::Const(_) => {}
        TermData::Var(name, _) => out.push(name.clone()),
        TermData::App(_, args) => {
            for &arg in args {
                collect_var_names(terms, arg, out);
            }
        }
        TermData::Let(bindings, body) => {
            for (_, value) in bindings {
                collect_var_names(terms, *value, out);
            }
            collect_var_names(terms, *body, out);
        }
        TermData::Not(inner) => collect_var_names(terms, *inner, out),
        TermData::Ite(c, t, e) => {
            collect_var_names(terms, *c, out);
            collect_var_names(terms, *t, out);
            collect_var_names(terms, *e, out);
        }
        TermData::Forall(_, body, _) | TermData::Exists(_, body, _) => {
            collect_var_names(terms, *body, out);
        }
        _ => unreachable!("unexpected TermData variant"),
    }
}

mod arrays;
mod bitvectors;
mod core;
mod datatypes;
mod finite_sets_z3_500;
mod floating_point;
mod numerics;
mod pseudo_boolean;
mod redefinition;
mod sequences;
mod special_relations;
mod strings;
