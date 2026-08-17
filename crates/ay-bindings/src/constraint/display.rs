// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates
//
//! SMT-LIB2 formatting for [`Constraint`].

use super::Constraint;
use crate::expr::Expr;
use crate::format_symbol;
use crate::sort::{DatatypeSort, Sort};
use std::fmt::{self, Display, Formatter};

/// Write a space-separated list of sorts in parentheses.
fn write_sort_list(f: &mut Formatter<'_>, sorts: &[Sort]) -> fmt::Result {
    write!(f, "(")?;
    for (i, sort) in sorts.iter().enumerate() {
        if i > 0 {
            write!(f, " ")?;
        }
        write!(f, "{sort}")?;
    }
    write!(f, ")")
}

fn write_datatype(f: &mut Formatter<'_>, dt: &DatatypeSort) -> fmt::Result {
    write!(f, "(declare-datatype {} (", format_symbol(&dt.name))?;
    for (i, cons) in dt.constructors.iter().enumerate() {
        if i > 0 {
            write!(f, " ")?;
        }
        write!(f, "({}", format_symbol(&cons.name))?;
        for field in &cons.fields {
            write!(f, " ({} {})", format_symbol(&field.name), field.sort)?;
        }
        write!(f, ")")?;
    }
    write!(f, "))")
}

fn write_check_sat_assuming(f: &mut Formatter<'_>, assumptions: &[Expr]) -> fmt::Result {
    write!(f, "(check-sat-assuming (")?;
    for (i, a) in assumptions.iter().enumerate() {
        if i > 0 {
            write!(f, " ")?;
        }
        write!(f, "{a}")?;
    }
    write!(f, "))")
}

fn write_get_value(f: &mut Formatter<'_>, exprs: &[Expr]) -> fmt::Result {
    write!(f, "(get-value (")?;
    for (i, e) in exprs.iter().enumerate() {
        if i > 0 {
            write!(f, " ")?;
        }
        write!(f, "{}", e.to_smtlib_shared())?;
    }
    write!(f, "))")
}

/// Format core SMT commands (declarations, assertions, control flow).
fn fmt_core(constraint: &Constraint, f: &mut Formatter<'_>) -> fmt::Result {
    match constraint {
        Constraint::DeclareConst { name, sort } => {
            write!(f, "(declare-const {} {})", format_symbol(name), sort)
        }
        Constraint::DeclareFun {
            name,
            arg_sorts,
            return_sort,
        } => {
            write!(f, "(declare-fun {} ", format_symbol(name))?;
            write_sort_list(f, arg_sorts)?;
            write!(f, " {return_sort})")
        }
        Constraint::DefineFun {
            name,
            params,
            return_sort,
            body,
        } => {
            write!(f, "(define-fun {} (", format_symbol(name))?;
            for (i, (param_name, param_sort)) in params.iter().enumerate() {
                if i > 0 {
                    write!(f, " ")?;
                }
                write!(f, "({} {})", format_symbol(param_name), param_sort)?;
            }
            write!(f, ") {return_sort} {})", body.to_smtlib_shared())
        }
        Constraint::DeclareDatatype(dt) => write_datatype(f, dt),
        // `to_smtlib_shared` hoists subterms shared by Arc identity into `let`
        // bindings, so an asserted DAG serializes in size linear in its distinct
        // nodes instead of unfolding to an exponential tree (a state-machine loop
        // proof otherwise produced tens of GB of `(assert ...)` text). Output is
        // logically identical; identical byte-for-byte when nothing is shared.
        Constraint::Assert { expr, label: None } => {
            write!(f, "(assert {})", expr.to_smtlib_shared())
        }
        Constraint::Assert {
            expr,
            label: Some(name),
        } => write!(
            f,
            "(assert (! {} :named {}))",
            expr.to_smtlib_shared(),
            format_symbol(name)
        ),
        Constraint::SoftAssert {
            expr,
            weight,
            group: None,
        } => write!(
            f,
            "(assert-soft {} :weight {weight})",
            expr.to_smtlib_shared()
        ),
        Constraint::SoftAssert {
            expr,
            weight,
            group: Some(g),
        } => write!(
            f,
            "(assert-soft {} :weight {} :id {})",
            expr.to_smtlib_shared(),
            weight,
            format_symbol(g)
        ),
        Constraint::Push => write!(f, "(push)"),
        Constraint::Pop(levels) => write!(f, "(pop {levels})"),
        Constraint::CheckSat => write!(f, "(check-sat)"),
        Constraint::CheckSatAssuming(assumptions) => write_check_sat_assuming(f, assumptions),
        Constraint::GetModel => write!(f, "(get-model)"),
        Constraint::GetValue(exprs) => write_get_value(f, exprs),
        Constraint::GetUnsatCore => write!(f, "(get-unsat-core)"),
        Constraint::SetOption { name, value } => {
            // The direct Solver API documents option keywords with their
            // leading colon (`:timeout`, `:produce-proofs`). Do not prepend a
            // second colon when rendering the same executable program as
            // SMT-LIB; `::timeout` is not a valid keyword and made diagnostic
            // transcripts impossible to replay.
            if name.starts_with(':') {
                write!(f, "(set-option {name} {value})")
            } else {
                write!(f, "(set-option :{name} {value})")
            }
        }
        Constraint::SetLogic(logic) => write!(f, "(set-logic {logic})"),
        Constraint::Exit => write!(f, "(exit)"),
        _ => unreachable!(),
    }
}

/// Format CHC and OMT commands.
fn fmt_chc_omt(constraint: &Constraint, f: &mut Formatter<'_>) -> fmt::Result {
    match constraint {
        Constraint::DeclareRel { name, arg_sorts } => {
            write!(f, "(declare-rel {} ", format_symbol(name))?;
            write_sort_list(f, arg_sorts)?;
            write!(f, ")")
        }
        // Like the `Assert` arms, every Expr embedded in a CHC/OMT command is
        // serialized DAG-aware via `to_smtlib_shared` (a `let` over Arc-shared
        // subterms): a `head`/`body`/objective built by unrolling a state machine
        // is otherwise an exponential tree. `let` is pure sharing, so the output
        // is logically identical (byte-identical when nothing is shared).
        Constraint::Rule {
            head: Some(head),
            body,
        } => write!(
            f,
            "(rule (=> {} {}))",
            body.to_smtlib_shared(),
            head.to_smtlib_shared()
        ),
        Constraint::Rule { head: None, body } => write!(f, "(rule {})", body.to_smtlib_shared()),
        Constraint::Query(rel) => write!(f, "(query {})", rel.to_smtlib_shared()),
        Constraint::DeclareVar { name, sort } => {
            write!(f, "(declare-var {} {})", format_symbol(name), sort)
        }
        Constraint::Maximize(expr) => write!(f, "(maximize {})", expr.to_smtlib_shared()),
        Constraint::Minimize(expr) => write!(f, "(minimize {})", expr.to_smtlib_shared()),
        Constraint::GetObjectives => write!(f, "(get-objectives)"),
        _ => unreachable!(),
    }
}

impl Display for Constraint {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self {
            Self::DeclareRel { .. }
            | Self::Rule { .. }
            | Self::Query(_)
            | Self::DeclareVar { .. }
            | Self::Maximize(_)
            | Self::Minimize(_)
            | Self::GetObjectives => fmt_chc_omt(self, f),
            _ => fmt_core(self, f),
        }
    }
}
