// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Canonically sorted normalized input; declaration payloads stay borrowed.

use super::payload::DatatypeRefs;
use super::*;

pub(super) fn normalized_input<P: Progress>(
    problem: &ChcProblem,
    progress: &mut P,
) -> Result<String, P::Error> {
    progress.poll()?;
    // The sections after the header are spelled first: whether any datatype
    // sort was referenced decides the schema, and the referenced constructor
    // lists are defined once, before every section that references them.
    let mut refs = DatatypeRefs::default();
    let pred_names = predicate_names(problem, progress, &mut refs)?;
    let mut out = String::new();
    out.push_str("datatypes\n");
    append_datatypes(problem, &mut out, progress, &mut refs)?;

    out.push_str("actions\n");
    let mut actions = Vec::new();
    for name in problem.action_names() {
        progress.poll()?;
        actions.push(json_string(name));
    }
    progress.poll()?;
    actions.sort();
    for action in actions {
        progress.poll()?;
        out.push_str(&format!("action {action}\n"));
    }

    out.push_str("predicates\n");
    let mut predicates = Vec::new();
    for predicate in problem.predicates() {
        progress.poll()?;
        let canonical = pred_names
            .get(&predicate.id.index())
            .cloned()
            .unwrap_or_else(|| fallback_predicate_name(predicate.id));
        let mut sorts = Vec::new();
        for sort in &predicate.arg_sorts {
            sorts.push(payload::normalized_sort(sort, progress, &mut refs)?);
        }
        progress.poll()?;
        predicates.push(format!(
            "predicate {canonical} name={} args=[{}]",
            json_string(&predicate.name),
            sorts.join(",")
        ));
    }
    progress.poll()?;
    predicates.sort();
    for predicate in predicates {
        progress.poll()?;
        out.push_str(&predicate);
        out.push('\n');
    }

    out.push_str("clauses\n");
    let mut clauses = Vec::new();
    for clause in problem.clauses() {
        clauses.push(normalized_clause(
            problem,
            clause,
            &pred_names,
            progress,
            &mut refs,
        )?);
    }
    progress.poll()?;
    clauses.sort();
    for clause in clauses {
        progress.poll()?;
        out.push_str(&clause);
        out.push('\n');
    }
    progress.poll()?;
    header(problem, refs, out, progress)
}

/// Prefix the schema, the fixedpoint flag and, when any datatype sort was
/// referenced, the `datatype-constructors` definitions to the spelled
/// sections. Input that references no datatype keeps the v1 bytes exactly.
fn header<P: Progress>(
    problem: &ChcProblem,
    refs: DatatypeRefs,
    mut sections: String,
    progress: &mut P,
) -> Result<String, P::Error> {
    let referenced = !refs.is_empty();
    let mut out = String::new();
    out.push_str(if referenced {
        NORMALIZED_CHC_INPUT_DATATYPE_REFERENCE_SCHEMA
    } else {
        NORMALIZED_CHC_INPUT_SCHEMA
    });
    out.push('\n');
    out.push_str(&format!(
        "fixedpoint={}\n",
        if problem.is_fixedpoint_format() {
            "true"
        } else {
            "false"
        }
    ));
    if referenced {
        out.push_str("datatype-constructors\n");
        for (id, parts) in payload::datatype_definitions(refs, progress)? {
            progress.poll()?;
            out.push_str(&format!("constructors @{id}={parts}\n"));
        }
    }
    progress.poll()?;
    // Prepended to the sections' own buffer (which may grow) rather than
    // copying the sections, most of the text, after a new header buffer.
    sections.insert_str(0, &out);
    Ok(sections)
}

pub(super) fn predicate_names<P: Progress>(
    problem: &ChcProblem,
    progress: &mut P,
    refs: &mut DatatypeRefs,
) -> Result<BTreeMap<usize, String>, P::Error> {
    progress.poll()?;
    let mut signatures = Vec::new();
    for predicate in problem.predicates() {
        progress.poll()?;
        let mut sorts = Vec::new();
        for sort in &predicate.arg_sorts {
            sorts.push(payload::normalized_sort(sort, progress, refs)?);
        }
        progress.poll()?;
        signatures.push((
            json_string(&predicate.name),
            sorts.join(","),
            predicate.id.index(),
        ));
    }
    progress.poll()?;
    signatures.sort();
    let mut names = BTreeMap::new();
    for (index, (_, _, original_index)) in signatures.into_iter().enumerate() {
        progress.poll()?;
        names.insert(original_index, format!("p{index}"));
    }
    progress.poll()?;
    Ok(names)
}

fn append_datatypes<P: Progress>(
    problem: &ChcProblem,
    out: &mut String,
    progress: &mut P,
    refs: &mut DatatypeRefs,
) -> Result<(), P::Error> {
    progress.poll()?;
    let mut datatypes = Vec::new();
    for entry in problem.datatype_defs() {
        progress.poll()?;
        // Unlike the old collector, sorting borrows entire payloads rather
        // than recursively cloning all nested selector sorts before a poll.
        datatypes.push(entry);
    }
    progress.poll()?;
    datatypes.sort_by_key(|(name, _)| *name);
    for (name, constructors) in datatypes {
        progress.poll()?;
        let mut ctor_parts = Vec::new();
        for (ctor, selectors) in constructors {
            progress.poll()?;
            let mut selector_parts = Vec::new();
            for (selector, sort) in selectors {
                progress.poll()?;
                selector_parts.push(format!(
                    "{}:{}",
                    json_string(selector),
                    payload::normalized_sort(sort, progress, refs)?
                ));
            }
            progress.poll()?;
            ctor_parts.push(format!(
                "{}({})",
                json_string(ctor),
                selector_parts.join(",")
            ));
        }
        progress.poll()?;
        out.push_str(&format!(
            "datatype {}={}\n",
            json_string(name),
            ctor_parts.join("|")
        ));
    }
    progress.poll()
}

fn normalized_clause<P: Progress>(
    problem: &ChcProblem,
    clause: &HornClause,
    pred_names: &BTreeMap<usize, String>,
    progress: &mut P,
    refs: &mut DatatypeRefs,
) -> Result<String, P::Error> {
    progress.poll()?;
    let mut body_predicates = Vec::new();
    for (pred, args) in &clause.body.predicates {
        body_predicates.push(payload::predicate_app(
            *pred, args, pred_names, progress, refs,
        )?);
    }
    progress.poll()?;
    body_predicates.sort();
    progress.poll()?;
    let constraint = match &clause.body.constraint {
        Some(expr) => payload::expression(expr, pred_names, progress, refs)?,
        None => "true".to_string(),
    };
    let head = match &clause.head {
        ClauseHead::False => "false".to_string(),
        ClauseHead::Predicate(pred, args) => {
            payload::predicate_app(*pred, args, pred_names, progress, refs)?
        }
    };
    progress.poll()?;
    let action = clause
        .action_id
        .and_then(|action| problem.action_name(action).map(json_string))
        .unwrap_or_else(|| "none".to_string());
    let result = format!(
        "clause action={action} body=[{}] constraint={constraint} head={head}",
        body_predicates.join(",")
    );
    progress.poll()?;
    Ok(result)
}
