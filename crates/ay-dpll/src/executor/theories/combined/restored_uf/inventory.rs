// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::{charge, entries, integer_bytes, same_sort, total, Atom, Checked, Pay, Probe, Refusal};
use ay_core::kani_compat::{DetHashMap as Map, DetHashSet as Set};
use ay_core::{Constant, Sort, Symbol, TermData, TermId};
use ay_euf::{EufModel, EufSolver, ModelRecoveryFact};
use ay_frontend::{Context, DeclarationKind, SymbolInfo};
use ay_lia::LiaModel;

pub(super) struct Node<'a> {
    pub term: TermId,
    pub sort: &'a Sort,
    // None is reserved for a newly derived alias, never an arbitrary value.
    pub value: Option<Atom>,
    pub alias: Option<TermId>,
    pub hard: Option<Atom>,
    pub live_class: Option<TermId>,
    pub leaf: bool,
    // An absent exact Bool UF output has a soft proposal; an absent equation
    // alias has NO value until exact evaluation. Both need atomic materialization.
    // Neither is a SAT assignment or a new hard fact.
    pub pending_completion: bool,
}
pub(super) struct Application<'a> {
    pub symbol: &'a Symbol,
    pub arguments: Vec<TermId>,
    pub output: usize,
}
struct AdmittedApplication<'a> {
    source: TermId,
    symbol: &'a Symbol,
    arguments: Vec<TermId>,
}

pub(super) struct Inventory<'a> {
    pub ctx: &'a Context,
    pub by_term: Map<TermId, usize>,
    pub nodes: Vec<Node<'a>>,
    pub apps: Vec<Application<'a>>,
    pub completed_outputs: usize,
    pub semantic_peers: Vec<(TermId, TermId)>,
    pub equalities: Vec<(TermId, TermId)>,
    pub disequalities: Vec<(TermId, TermId)>,
}

fn supported(ctx: &Context, sort: &Sort, pay: &mut Pay<'_>) -> Checked<bool> {
    Ok(match sort {
        Sort::Int | Sort::Bool => true,
        Sort::Uninterpreted(name) => {
            charge(pay, &[name.len(), name.len(), name.len(), 1], &[])?;
            ctx.is_model_recovery_free_carrier(name)
        }
        _ => false,
    })
}

fn root_of(
    parents: &Map<TermId, TermId>,
    term: TermId,
    pay: &mut Pay<'_>,
) -> Checked<Option<TermId>> {
    pay(1, 0)?;
    if !parents.contains_key(&term) {
        return Ok(None);
    }
    let mut current = term;
    // The finite node count bounds malformed cycles without an unmetered
    // class walk or the old out-of-range singleton fallback.
    for _ in 0..=parents.len() {
        pay(1, 0)?;
        let parent = *parents.get(&current).ok_or(Refusal::Unsupported)?;
        if current == parent {
            return Ok(Some(current));
        }
        current = parent;
    }
    Err(Refusal::Unsupported)
}

fn copy_int(value: &num_bigint::BigInt, pay: &mut Pay<'_>) -> Checked<Atom> {
    let bytes = integer_bytes(value)?;
    charge(pay, &[bytes, 1], &[bytes, 64])?;
    Ok(Atom::Int(value.clone()))
}

fn atom(
    ctx: &Context,
    term: TermId,
    euf: &EufModel,
    lia: Option<&LiaModel>,
    booleans: &Map<TermId, bool>,
    pay: &mut Pay<'_>,
    probe: &Probe,
) -> Checked<Option<(Atom, Option<Atom>)>> {
    let terms = &ctx.terms;
    probe.check("atom-kind", Some(term), None);
    let (value, hard) = match terms.get(term) {
        TermData::Const(Constant::Int(value)) => {
            let value = copy_int(value, pay)?;
            let hard = value.copy(pay)?;
            return Ok(Some((value, Some(hard))));
        }
        TermData::Const(Constant::Bool(value)) => (Atom::Bool(*value), true),
        _ => match terms.sort(term) {
            Sort::Int => {
                if let Some(value) = lia.and_then(|model| model.values.get(&term)) {
                    (copy_int(value, pay)?, true)
                } else if let Some(value) = euf.int_values.get(&term) {
                    (
                        copy_int(value, pay)?,
                        !euf.speculative_int_terms.contains(&term),
                    )
                } else if let Some(constant) = euf.func_app_const_terms.get(&term) {
                    probe.check("atom-direct-pin", Some(term), Some(*constant));
                    if constant.index() >= terms.len() {
                        return Err(Refusal::Unsupported);
                    }
                    let TermData::Const(Constant::Int(value)) = terms.get(*constant) else {
                        return Err(Refusal::Unsupported);
                    };
                    (copy_int(value, pay)?, true)
                } else {
                    return Ok(None);
                }
            }
            Sort::Bool => {
                let raw = match euf.term_values.get(&term).map(String::as_str) {
                    Some("true") => Some(true),
                    Some("false") => Some(false),
                    _ => None,
                };
                let pin = booleans.get(&term).copied();
                // An old default/table spelling is not a conflicting hard
                // Boolean commitment; preserve the actual current assignment.
                let Some(value) = pin.or(raw) else {
                    return Ok(None);
                };
                (Atom::Bool(value), pin.is_some())
            }
            Sort::Uninterpreted(name) => {
                let Some(raw) = euf.term_values.get(&term) else {
                    return Ok(None);
                };
                charge(pay, &[name.len(), 1], &[])?;
                probe.check("atom-carrier-domain", Some(term), None);
                let Some(elements) = euf.sort_elements.get(name) else {
                    return Err(Refusal::Unsupported);
                };
                let mut found = false;
                for element in elements {
                    charge(pay, &[1, raw.len(), element.len()], &[])?;
                    found |= raw == element;
                }
                if !found {
                    return Err(Refusal::Unsupported);
                }
                charge(pay, &[raw.len(), 1], &[raw.len(), 64])?;
                (Atom::Carrier(raw.as_str().to_owned()), false)
            }
            _ => return Ok(None),
        },
    };
    let pin = if hard { Some(value.copy(pay)?) } else { None };
    Ok(Some((value, pin)))
}

pub(super) fn capture<'a>(
    ctx: &'a Context,
    live: &EufSolver<'_>,
    roots: &[TermId],
    euf: &EufModel,
    lia: Option<&LiaModel>,
    pay: &mut Pay<'_>,
    probe: &Probe,
) -> Checked<Inventory<'a>> {
    let terms = &ctx.terms;
    // The borrowed EUF decoder recognizes these fixed canonical operations.
    // A conflicting native declaration cannot lend its spelling that meaning.
    probe.check("canonical-bindings", None, None);
    for name in ["and", "or", "=", "distinct"] {
        charge(
            pay,
            &[1, name.len(), name.len(), name.len(), name.len()],
            &[],
        )?;
        if !ctx.canonical_operator_binding_is_unambiguous(name) {
            return Err(Refusal::Unsupported);
        }
    }
    let mut parents = Map::default();
    let mut booleans = Map::default();
    let mut relations = Vec::new();
    let mut stack = Vec::new();
    entries(pay, roots.len())?;
    stack.extend_from_slice(roots);
    probe.check("live-facts", None, None);
    let available = live.visit_model_recovery_facts(terms, |fact| -> Checked<()> {
        pay(1, 0)?;
        match fact {
            ModelRecoveryFact::ScanSlots(slots) => {
                pay(slots, 0)?;
            }
            ModelRecoveryFact::Parent { term, parent } => {
                entries(pay, 1)?;
                parents.insert(term, parent);
            }
            ModelRecoveryFact::Boolean { term, value } => {
                entries(pay, 2)?;
                booleans.insert(term, value);
                // Active kernel literals are legitimate current roots. Merely
                // being present in the TermStore or a stale table is not.
                stack.push(term);
            }
            ModelRecoveryFact::Equality { left, right, equal } => {
                entries(pay, 1)?;
                relations.push((left, right, equal));
            }
            ModelRecoveryFact::SharedDisequality { left, right } => {
                entries(pay, 3)?;
                relations.push((left, right, false));
                stack.extend([left, right]);
            }
            ModelRecoveryFact::Distinct(arguments) => {
                for (index, &left) in arguments.iter().enumerate() {
                    pay(1, 0)?;
                    for &right in &arguments[index + 1..] {
                        entries(pay, 1)?;
                        relations.push((left, right, false));
                    }
                }
            }
        }
        Ok(())
    })?;
    if !available {
        return Err(Refusal::Unsupported);
    }

    // Preprocessing may discharge an original equality, so it need not occur
    // in the remaining live theory assignments. Its asserted truth still
    // constrains relabelling. Inspect only logically forced root components;
    // never treat a guarded/disjunctive equality as an unconditional premise.
    probe.check("source-truth", None, None);
    source_truth(ctx, roots, &mut booleans, &mut relations, pay, probe)?;

    let mut seen = Set::default();
    let mut scope = Vec::new();
    while let Some(term) = stack.pop() {
        probe.check("scope-term", Some(term), None);
        entries(pay, 1)?;
        if term.index() >= terms.len() {
            return Err(Refusal::Unsupported);
        }
        if !seen.insert(term) {
            continue;
        }
        entries(pay, 1)?;
        scope.push(term);
        match terms.get(term) {
            TermData::App(_, args) => {
                entries(pay, args.len())?;
                stack.extend_from_slice(args);
            }
            TermData::Not(inner) => {
                entries(pay, 1)?;
                stack.push(*inner);
            }
            TermData::Ite(c, t, e) => {
                entries(pay, 3)?;
                stack.extend([*c, *t, *e]);
            }
            TermData::Const(_) | TermData::Var(..) => {}
            // This ground extraction transaction has no binder/environment
            // authority. Quantified/let terms keep the existing refusal path.
            _ => return Err(Refusal::Unsupported),
        }
    }
    pay(
        scope
            .len()
            .checked_mul((usize::BITS - scope.len().leading_zeros()) as usize + 1)
            .ok_or(Refusal::Unsupported)?,
        0,
    )?;
    scope.sort_unstable_by_key(|term| term.index());

    // Borrow exact signatures once, paying all inventory scans. No RefCell
    // borrow survives into recovery, and no whole signature is cloned per app.
    let mut signatures: Vec<(&str, &SymbolInfo)> = Vec::new();
    let mut adopted = Vec::new();
    for slots in ctx.model_recovery_scan_capacities() {
        pay(slots, 0)?;
    }
    for id in ctx.model_recovery_adopted_declarations() {
        entries(pay, 1)?;
        adopted.push(id);
    }
    for (surface, info) in ctx.model_recovery_symbol_iter() {
        probe.check("declaration-signature", None, None);
        charge(pay, &[1, surface.len()], &[])?;
        if info.declaration_kind() != DeclarationKind::Uninterpreted {
            continue;
        }
        let mut is_adopted = false;
        for id in &adopted {
            pay(1, 0)?;
            is_adopted |= *id == info.declaration_id();
        }
        if is_adopted || !supported(ctx, &info.sort, pay)? {
            continue;
        }
        let mut valid = true;
        for sort in &info.arg_sorts {
            pay(1, 0)?;
            valid &= supported(ctx, sort, pay)?;
        }
        if !valid {
            continue;
        }
        let identity = ctx.symbol_identity_name(surface, info);
        charge(pay, &[identity.len(), 1], &[])?;
        if ay_frontend::is_canonical_theory_operator_identity(identity) {
            // A raw native ordinary binding cannot claim the engine's fixed
            // operator identity even if its declared result/arity happen to fit.
            return Err(Refusal::Unsupported);
        }
        entries(pay, 1)?;
        signatures.push((identity, info));
    }

    let mut admitted = Vec::new();
    for &term in &scope {
        let TermData::App(symbol, arguments) = terms.get(term) else {
            continue;
        };
        probe.check("application-signature", Some(term), None);
        let mut selected: Option<&SymbolInfo> = None;
        for &(identity, info) in &signatures {
            charge(pay, &[1, identity.len(), symbol.name().len()], &[])?;
            // Indexed syntax cannot impersonate a named declaration. It needs
            // its own declaration resolver before this fragment may accept it.
            if identity != symbol.name() {
                continue;
            }
            if !matches!(symbol, Symbol::Named(_)) {
                return Err(Refusal::Unsupported);
            }
            if let Some(previous) = selected {
                pay(1, 0)?;
                if previous.declaration_id() != info.declaration_id()
                    || previous.arg_sorts.len() != info.arg_sorts.len()
                    || !same_sort(&previous.sort, &info.sort, pay)?
                {
                    return Err(Refusal::Unsupported);
                }
                for (a, b) in previous.arg_sorts.iter().zip(&info.arg_sorts) {
                    if !same_sort(a, b, pay)? {
                        return Err(Refusal::Unsupported);
                    }
                }
            }
            selected = Some(info);
        }
        let Some(info) = selected else { continue };
        if arguments.len() != info.arg_sorts.len() || !same_sort(terms.sort(term), &info.sort, pay)?
        {
            return Err(Refusal::Unsupported);
        }
        let mut args = Vec::new();
        entries(pay, total(&[arguments.len(), 1])?)?;
        for (&argument, sort) in arguments.iter().zip(&info.arg_sorts) {
            probe.check("application-argument-sort", Some(argument), Some(term));
            if !same_sort(terms.sort(argument), sort, pay)? {
                return Err(Refusal::Unsupported);
            }
            args.push(argument);
        }
        admitted.push(AdmittedApplication {
            source: term,
            symbol,
            arguments: args,
        });
    }
    let aliases = boolean_aliases(ctx, &scope, &relations, euf, lia, &booleans, pay, probe)?;
    let mut completed_outputs = 0usize;
    let mut nodes = Vec::new();
    let mut by_term = Map::default();
    for &term in &scope {
        probe.check("node-value", Some(term), None);
        pay(1, 0)?;
        if !supported(ctx, terms.sort(term), pay)? {
            continue;
        }
        pay(1, 0)?;
        let alias = aliases.get(&term).copied();
        let captured = atom(ctx, term, euf, lia, &booleans, pay, probe)?;
        let (value, hard, pending_completion) = match captured {
            Some((value, hard)) => (Some(value), hard, false),
            None => {
                let mut admitted_bool = false;
                if matches!(terms.sort(term), Sort::Bool) {
                    for app in &admitted {
                        pay(1, 0)?;
                        if app.source == term {
                            admitted_bool = true;
                            break;
                        }
                    }
                }
                if !admitted_bool && alias.is_none() {
                    // A guard may short-circuit before evaluating this Var.
                    // Its absent value is still outside this recovery fragment;
                    // a guarded equation supplies no completion authority.
                    if matches!(terms.sort(term), Sort::Bool)
                        && matches!(terms.get(term), TermData::Var(..))
                    {
                        return Err(Refusal::Unsupported);
                    }
                    continue;
                }
                probe.check("soft-bool-raw-absence", Some(term), None);
                pay(1, 0)?;
                // atom() already gives genuine current Boolean/source pins
                // priority. An invalid PRESENT spelling is not absence.
                if euf.term_values.contains_key(&term) {
                    return Err(Refusal::Unsupported);
                }
                completed_outputs = completed_outputs
                    .checked_add(1)
                    .ok_or(Refusal::Unsupported)?;
                // The existing extractor uses false for an unassigned Bool
                // application. This is the same SOFT finite-domain proposal;
                // later live pins/congruence may replace it, or reject it.
                // Derived aliases receive no fabricated placeholder: the
                // evaluator resolves their current equation inside its stack.
                (
                    if alias.is_some() {
                        None
                    } else {
                        Some(Atom::Bool(false))
                    },
                    None,
                    true,
                )
            }
        };
        entries(pay, 2)?;
        by_term.insert(term, nodes.len());
        nodes.push(Node {
            term,
            sort: terms.sort(term),
            value,
            alias,
            hard,
            live_class: root_of(&parents, term, pay)?,
            leaf: false,
            pending_completion,
        });
    }
    // Preserve every live-class hard pin, including a peer/constant absent from
    // the root DAG. Peers contribute constraints, never new application roots.
    let mut pin = |term: TermId, value: Atom, pay: &mut Pay<'_>| -> Checked<()> {
        probe.check("hard-pin", Some(term), None);
        let class = root_of(&parents, term, pay)?;
        for node in &mut nodes {
            pay(1, 0)?;
            if node.term != term && (class.is_none() || node.live_class != class) {
                continue;
            }
            if !same_sort(node.sort, terms.sort(term), pay)? {
                return Err(Refusal::Conflict);
            }
            if let Some(old) = &node.hard {
                if !old.same(&value, pay)? {
                    return Err(Refusal::Conflict);
                }
            }
            if node.pending_completion {
                // A real live-class/direct pin overrides only the new soft
                // proposal. Existing conflicting hard facts were checked above.
                node.value = Some(value.copy(pay)?);
            }
            node.hard = Some(value.copy(pay)?);
        }
        Ok(())
    };
    for &term in parents.keys() {
        pay(1, 0)?;
        match terms.get(term) {
            TermData::Const(Constant::Int(value)) => pin(term, copy_int(value, pay)?, pay)?,
            TermData::Const(Constant::Bool(value)) => pin(term, Atom::Bool(*value), pay)?,
            _ => {}
        }
    }
    if let Some(lia) = lia {
        pay(lia.values.capacity(), 0)?;
        for (&term, value) in &lia.values {
            pay(1, 0)?;
            pin(term, copy_int(value, pay)?, pay)?;
        }
    }
    pay(euf.int_values.capacity(), 0)?;
    for (&term, value) in &euf.int_values {
        pay(1, 0)?;
        if !euf.speculative_int_terms.contains(&term) {
            pin(term, copy_int(value, pay)?, pay)?;
        }
    }
    pay(euf.func_app_const_terms.capacity(), 0)?;
    for (&term, &constant) in &euf.func_app_const_terms {
        pay(1, 0)?;
        if constant.index() >= terms.len() {
            return Err(Refusal::Unsupported);
        }
        if let TermData::Const(Constant::Int(value)) = terms.get(constant) {
            pin(term, copy_int(value, pay)?, pay)?;
        }
    }
    drop(pin);

    // All semantic admission preceded any completion. Missing non-Bool
    // outputs still refuse; only this exact current occurrence set can bind.
    let mut apps = Vec::new();
    entries(pay, admitted.len())?;
    for app in admitted {
        probe.check("admitted-output-value", Some(app.source), None);
        let output = *by_term.get(&app.source).ok_or(Refusal::Unsupported)?;
        apps.push(Application {
            symbol: app.symbol,
            arguments: app.arguments,
            output,
        });
    }

    // Only actual free applications, ordinary variables and rigid constants
    // are model leaves. Arithmetic, Boolean structure and ITEs are evaluated
    // exactly under current leaves, never keyed by speculative raw mappings.
    for (index, node) in nodes.iter_mut().enumerate() {
        pay(1, 0)?;
        let mut free_output = false;
        for app in &apps {
            pay(1, 0)?;
            free_output |= app.output == index;
        }
        node.leaf = node.alias.is_none()
            && (free_output
                || matches!(terms.get(node.term), TermData::Var(..) | TermData::Const(_)));
    }
    // A current interpreted peer may have no raw model atom at all. Its live
    // equality still constrains captured leaves; retain the actual expression
    // as a semantic check instead of fabricating a cached point value.
    let mut semantic_peers = Vec::new();
    for &term in &scope {
        pay(1, 0)?;
        if by_term.contains_key(&term) || !supported(ctx, terms.sort(term), pay)? {
            continue;
        }
        let Some(class) = root_of(&parents, term, pay)? else {
            continue;
        };
        for node in &nodes {
            pay(1, 0)?;
            if node.live_class == Some(class) {
                if !same_sort(terms.sort(term), node.sort, pay)? {
                    return Err(Refusal::Conflict);
                }
                entries(pay, 1)?;
                semantic_peers.push((term, node.term));
            }
        }
    }
    let mut equalities = Vec::new();
    let mut disequalities = Vec::new();
    for (left, right, equal) in relations {
        probe.check("relation-sort", Some(left), Some(right));
        pay(1, 0)?;
        if left.index() >= terms.len()
            || right.index() >= terms.len()
            || !supported(ctx, terms.sort(left), pay)?
            || !same_sort(terms.sort(left), terms.sort(right), pay)?
        {
            return Err(Refusal::Unsupported);
        }
        entries(pay, 1)?;
        if equal {
            equalities.push((left, right));
        } else {
            disequalities.push((left, right));
        }
    }
    Ok(Inventory {
        ctx,
        by_term,
        nodes,
        apps,
        completed_outputs,
        semantic_peers,
        equalities,
        disequalities,
    })
}

// A retained true Boolean equality is a constraint, not an independent model
// choice. Prefer a real non-variable definition for its variable component;
// otherwise an actually captured Bool atom may anchor variable-only aliases.
// No default is invented for an unanchored component. All original relations
// remain in Inventory and are validated after current-point closure.
fn boolean_aliases(
    ctx: &Context,
    scope: &[TermId],
    relations: &[(TermId, TermId, bool)],
    euf: &EufModel,
    lia: Option<&LiaModel>,
    booleans: &Map<TermId, bool>,
    pay: &mut Pay<'_>,
    probe: &Probe,
) -> Checked<Map<TermId, TermId>> {
    let terms = &ctx.terms;
    let mut variables = Vec::new();
    let mut components = Map::default();
    let mut equations = Vec::new();
    for &(left, right, equal) in relations {
        probe.check("boolean-equation", Some(left), Some(right));
        pay(1, 0)?;
        if !equal {
            continue;
        }
        if left.index() >= terms.len() || right.index() >= terms.len() {
            return Err(Refusal::Unsupported);
        }
        if !matches!(terms.sort(left), Sort::Bool) || !matches!(terms.sort(right), Sort::Bool) {
            continue;
        }
        let a = matches!(terms.get(left), TermData::Var(..));
        let b = matches!(terms.get(right), TermData::Var(..));
        if !a && !b {
            continue;
        }
        if !canonical(ctx, "=", pay)? {
            return Err(Refusal::Unsupported);
        }
        charge(pay, &[scope.len(), scope.len()], &[])?;
        if !scope.contains(&left) || !scope.contains(&right) {
            continue;
        }
        for (term, variable) in [(left, a), (right, b)] {
            if variable {
                pay(variables.len(), 0)?;
                if !variables.contains(&term) {
                    entries(pay, 2)?;
                    variables.push(term);
                    components.insert(term, term);
                }
            }
        }
        if a && b {
            let x = root_of(&components, left, pay)?.ok_or(Refusal::Unsupported)?;
            let y = root_of(&components, right, pay)?.ok_or(Refusal::Unsupported)?;
            if x != y {
                pay(1, 0)?;
                let (keep, retire) = if x.index() < y.index() {
                    (x, y)
                } else {
                    (y, x)
                };
                components.insert(retire, keep);
            }
        }
        entries(pay, 1)?;
        equations.push((left, right));
    }
    let mut anchors = Map::default();
    for &(left, right) in &equations {
        for (variable, rhs) in [(left, right), (right, left)] {
            pay(1, 0)?;
            if !matches!(terms.get(variable), TermData::Var(..))
                || matches!(terms.get(rhs), TermData::Var(..))
            {
                continue;
            }
            let class = root_of(&components, variable, pay)?.ok_or(Refusal::Unsupported)?;
            pay(1, 0)?;
            if !anchors.contains_key(&class) {
                entries(pay, 1)?;
                anchors.insert(class, (variable, Some(rhs)));
            }
        }
    }
    for &variable in &variables {
        let class = root_of(&components, variable, pay)?.ok_or(Refusal::Unsupported)?;
        pay(1, 0)?;
        if !anchors.contains_key(&class)
            && atom(ctx, variable, euf, lia, booleans, pay, probe)?.is_some()
        {
            entries(pay, 1)?;
            anchors.insert(class, (variable, None));
        }
    }
    let mut aliases = Map::default();
    for variable in variables {
        let class = root_of(&components, variable, pay)?.ok_or(Refusal::Unsupported)?;
        pay(1, 0)?;
        let Some(&(anchor, rhs)) = anchors.get(&class) else {
            continue;
        };
        let target = if variable != anchor {
            Some(anchor)
        } else {
            rhs
        };
        if let Some(target) = target {
            entries(pay, 1)?;
            aliases.insert(variable, target);
        }
    }
    Ok(aliases)
}

fn canonical(ctx: &Context, name: &str, pay: &mut Pay<'_>) -> Checked<bool> {
    charge(
        pay,
        &[1, name.len(), name.len(), name.len(), name.len()],
        &[],
    )?;
    Ok(ctx.canonical_operator_binding_is_unambiguous(name))
}

fn source_truth(
    ctx: &Context,
    roots: &[TermId],
    booleans: &mut Map<TermId, bool>,
    relations: &mut Vec<(TermId, TermId, bool)>,
    pay: &mut Pay<'_>,
    probe: &Probe,
) -> Checked<()> {
    let terms = &ctx.terms;
    let mut stack = Vec::new();
    let mut seen = Set::default();
    entries(pay, roots.len())?;
    stack.extend(roots.iter().map(|&term| (term, true)));
    while let Some((term, value)) = stack.pop() {
        probe.check("source-truth-term", Some(term), None);
        entries(pay, 1)?;
        if term.index() >= terms.len() || !matches!(terms.sort(term), Sort::Bool) {
            return Err(Refusal::Unsupported);
        }
        if !seen.insert((term, value)) {
            continue;
        }
        match terms.get(term) {
            TermData::Not(inner) => {
                entries(pay, 1)?;
                stack.push((*inner, !value));
            }
            TermData::App(Symbol::Named(name), args)
                if ((name.as_ref() == "and" && value) || (name.as_ref() == "or" && !value))
                    && canonical(ctx, name, pay)? =>
            {
                entries(pay, args.len())?;
                stack.extend(args.iter().map(|&child| (child, value)));
            }
            TermData::App(Symbol::Named(name), args)
                if name.as_ref() == "=" && canonical(ctx, name, pay)? =>
            {
                if args.len() != 2
                    || args[0].index() >= terms.len()
                    || args[1].index() >= terms.len()
                    || !supported(ctx, terms.sort(args[0]), pay)?
                    || !same_sort(terms.sort(args[0]), terms.sort(args[1]), pay)?
                {
                    return Err(Refusal::Unsupported);
                }
                entries(pay, 1)?;
                relations.push((args[0], args[1], value));
            }
            TermData::App(Symbol::Named(name), args)
                if name.as_ref() == "distinct" && value && canonical(ctx, name, pay)? =>
            {
                for (index, &left) in args.iter().enumerate() {
                    pay(1, 0)?;
                    for &right in &args[index + 1..] {
                        if left.index() >= terms.len()
                            || right.index() >= terms.len()
                            || !supported(ctx, terms.sort(left), pay)?
                            || !same_sort(terms.sort(left), terms.sort(right), pay)?
                        {
                            return Err(Refusal::Unsupported);
                        }
                        entries(pay, 1)?;
                        relations.push((left, right, false));
                    }
                }
            }
            _ => {
                pay(1, 0)?;
                if booleans.get(&term).is_some_and(|old| *old != value) {
                    return Err(Refusal::Conflict);
                }
                entries(pay, 1)?;
                booleans.insert(term, value);
            }
        }
    }
    Ok(())
}
