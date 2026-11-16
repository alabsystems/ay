// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Definitional variable elimination (the substitution rule of first-order
//! equality). Definitions are retained in elimination order for reverse model
//! reconstruction. Every traversal and rebuild uses the original admission.
use super::field_to_bv::Borrowed;
use super::tactics::TacticFailure;
use ay_core::kani_compat::{DetHashMap, DetHashSet};
use ay_core::term::{reserve_counted, CountedTermBuilder, TermConstructionAdmission};
use ay_core::{Sort, Symbol, TermData, TermId, TermStore};

pub(super) struct Eliminated {
    pub roots: Vec<TermId>,
    pub definitions: Vec<(TermId, TermId)>,
}

fn failed() -> TacticFailure {
    TacticFailure::new("solve-eqs original admission stopped or source graph invalid")
}

fn tick(owner: &dyn TermConstructionAdmission, work: usize) -> Result<(), TacticFailure> {
    owner.admit(work, 0).map_err(|_| failed())
}

fn push<T>(
    v: &mut Vec<T>,
    value: T,
    owner: &dyn TermConstructionAdmission,
) -> Result<(), TacticFailure> {
    reserve_counted(v, 1, owner).map_err(|_| failed())?;
    v.push(value);
    Ok(())
}

pub(super) fn children(
    term: &TermData,
    output: &mut Vec<TermId>,
    owner: &dyn TermConstructionAdmission,
) -> Result<(), TacticFailure> {
    match term {
        TermData::Var(..) | TermData::Const(..) => {}
        TermData::App(_, args) => {
            tick(owner, args.len())?;
            reserve_counted(output, args.len(), owner).map_err(|_| failed())?;
            output.extend_from_slice(args);
        }
        TermData::Not(a) => push(output, *a, owner)?,
        TermData::Ite(a, b, c) => {
            for id in [*a, *b, *c] {
                push(output, id, owner)?;
            }
        }
        TermData::Let(bindings, body) => {
            for (_, id) in bindings {
                tick(owner, 1)?;
                push(output, *id, owner)?;
            }
            push(output, *body, owner)?;
        }
        TermData::Forall(_, body, triggers) | TermData::Exists(_, body, triggers) => {
            push(output, *body, owner)?;
            for trigger in triggers {
                tick(owner, 1)?;
                reserve_counted(output, trigger.len(), owner).map_err(|_| failed())?;
                tick(owner, trigger.len())?;
                output.extend_from_slice(trigger);
            }
        }
        _ => return Err(failed()),
    }
    Ok(())
}

pub(super) fn reachable(
    store: &TermStore,
    roots: &[TermId],
    owner: &dyn TermConstructionAdmission,
) -> Result<Vec<bool>, TacticFailure> {
    let mut seen = Vec::new();
    reserve_counted(&mut seen, store.len(), owner).map_err(|_| failed())?;
    tick(owner, store.len())?;
    seen.resize(store.len(), false);
    let mut pending = Vec::new();
    reserve_counted(&mut pending, roots.len(), owner).map_err(|_| failed())?;
    tick(owner, roots.len())?;
    pending.extend_from_slice(roots);
    let mut args = Vec::new();
    while let Some(id) = pending.pop() {
        tick(owner, 1)?;
        if id.index() >= store.len() {
            return Err(failed());
        }
        if seen[id.index()] {
            continue;
        }
        seen[id.index()] = true;
        args.clear();
        children(store.get(id), &mut args, owner)?;
        for &child in &args {
            tick(owner, 1)?;
            // TermStore is append-only: this also rejects cycles before any
            // rewrite and establishes the topological order used below.
            if child.index() >= id.index() {
                return Err(failed());
            }
            push(&mut pending, child, owner)?;
        }
    }
    Ok(seen)
}

fn equal_name(
    a: &str,
    b: &str,
    owner: &dyn TermConstructionAdmission,
) -> Result<bool, TacticFailure> {
    tick(owner, a.len().checked_add(b.len()).ok_or_else(failed)?)?;
    Ok(a == b)
}

fn frozen(
    name: &str,
    binders: &[String],
    owner: &dyn TermConstructionAdmission,
) -> Result<bool, TacticFailure> {
    for binder in binders {
        if equal_name(name, binder, owner)? {
            return Ok(true);
        }
    }
    Ok(false)
}

/// Depth-first occurs/capture probe over the subgraph reachable from
/// `root`, charging admission per visited node. Returns `(occurs,
/// captures)`: whether `variable` (or any of `also_targets`) occurs in
/// `root`, and whether any variable of `root` is frozen by a binder
/// name. Early-exits once `occurs` is known (capture is then
/// irrelevant to the caller). The variables occurring in `root` are
/// collected into `vars` (complete whenever `occurs` is false), so the
/// caller can keep a batched layer symmetric-independent. Same
/// answers as the previous full-store `reachable` scan, at cost
/// proportional to the value's subgraph instead of the whole store,
/// which the old code paid per candidate orientation.
fn occurs_or_captures(
    store: &TermStore,
    root: TermId,
    variable: TermId,
    also_targets: &DetHashSet<TermId>,
    binders: &[String],
    vars: &mut DetHashSet<TermId>,
    owner: &dyn TermConstructionAdmission,
) -> Result<(bool, bool), TacticFailure> {
    vars.clear();
    let mut seen: DetHashSet<TermId> = DetHashSet::default();
    let mut pending = Vec::new();
    push(&mut pending, root, owner)?;
    let mut args = Vec::new();
    let mut captures = false;
    while let Some(id) = pending.pop() {
        tick(owner, 1)?;
        if id.index() >= store.len() {
            return Err(failed());
        }
        if id == variable || also_targets.contains(&id) {
            return Ok((true, captures));
        }
        tick(owner, 1)?;
        if !seen.insert(id) {
            continue;
        }
        if let TermData::Var(name, _) = store.get(id) {
            tick(owner, 1)?;
            vars.insert(id);
            captures |= frozen(name, binders, owner)?;
        }
        args.clear();
        children(store.get(id), &mut args, owner)?;
        for &child in &args {
            tick(owner, 1)?;
            if child.index() >= id.index() {
                return Err(failed());
            }
            push(&mut pending, child, owner)?;
        }
    }
    Ok((false, captures))
}

pub(super) fn eliminate(
    store: &mut TermStore,
    roots: Vec<TermId>,
    owner: &dyn TermConstructionAdmission,
) -> Result<Eliminated, TacticFailure> {
    let marked = reachable(store, &roots, owner)?;
    let mut binders = Vec::new();
    for (index, present) in marked.iter().enumerate() {
        tick(owner, 1)?;
        if !present {
            continue;
        }
        // Freeze every binder spelling across the goal. This conservative
        // choice permits traversal under binders without capturing a free
        // variable or rewriting a locally bound occurrence.
        match store.get(TermId(index as u32)) {
            TermData::Let(bindings, _) => {
                for (name, _) in bindings {
                    owner
                        .admit(name.len().checked_add(1).ok_or_else(failed)?, name.len())
                        .map_err(|_| failed())?;
                    push(&mut binders, name.clone(), owner)?;
                }
            }
            TermData::Forall(bindings, ..) | TermData::Exists(bindings, ..) => {
                for (name, _) in bindings {
                    owner
                        .admit(name.len().checked_add(1).ok_or_else(failed)?, name.len())
                        .map_err(|_| failed())?;
                    push(&mut binders, name.clone(), owner)?;
                }
            }
            _ => {}
        }
    }
    // Most goals have no definitional equality. Do not build an interning
    // index over the source store merely to report no progress.
    let mut candidate = false;
    for &root in &roots {
        tick(owner, 1)?;
        if store.sort(root) != &Sort::Bool {
            return Err(failed());
        }
        if let TermData::App(Symbol::Named(op), args) = store.get(root) {
            tick(owner, op.len())?;
            if op == "=" && args.len() == 2 && !store.is_declared_function(op) {
                candidate |= args[0] == args[1]
                    || matches!(store.get(args[0]), TermData::Var(..))
                    || matches!(store.get(args[1]), TermData::Var(..));
            }
        }
    }
    if !candidate {
        owner.check().map_err(|_| failed())?;
        return Ok(Eliminated {
            roots,
            definitions: Vec::new(),
        });
    }
    let borrowed = Borrowed(owner);
    let mut builder = CountedTermBuilder::with_admission(store, &borrowed).map_err(|_| failed())?;
    let mut roots = roots;
    let mut definitions = Vec::new();
    let mut args = Vec::new();
    // Layered elimination: each pass selects a symmetric-independent set
    // of currently selectable definitions — no selected value references
    // a variable selected in the same pass, in either scan direction —
    // then rewrites the remaining roots once with the whole layer.
    // Mutually independent substitutions commute, and dependent
    // definitions defer to later layers, so the composed substitution
    // (and therefore the final roots) matches eliminating one variable
    // at a time, while the number of whole-goal scans/rewrites is the
    // dependency depth instead of the definition count. Definitions are
    // still recorded in an order whose reversal reconstructs models:
    // a definition's recorded value references only variables from later
    // layers or never-eliminated ones.
    let mut value_vars: DetHashSet<TermId> = DetHashSet::default();
    loop {
        let mut layer: Vec<(usize, Option<(TermId, TermId)>)> = Vec::new();
        let mut layer_vars: DetHashSet<TermId> = DetHashSet::default();
        // Variables referenced by values already selected in this layer:
        // a later candidate defining one of them must defer, or the
        // earlier definition's substitution would leave it free in the
        // residual while also recording it as defined.
        let mut layer_referenced: DetHashSet<TermId> = DetHashSet::default();
        for (position, &root) in roots.iter().enumerate() {
            tick(owner, 1)?;
            if builder.terms().sort(root) != &Sort::Bool {
                return Err(failed());
            }
            let TermData::App(Symbol::Named(op), operands) = builder.terms().get(root) else {
                continue;
            };
            tick(owner, op.len())?;
            if op != "=" || operands.len() != 2 || builder.terms().is_declared_function(op) {
                continue;
            }
            let [a, b] = [operands[0], operands[1]];
            if a == b {
                push(&mut layer, (position, None), owner)?;
                continue;
            }
            // Model reconstruction currently transports these scalar sorts.
            // Other equalities remain in the goal, with no invented witness.
            let compatible = match (builder.terms().sort(a), builder.terms().sort(b)) {
                (Sort::Bool, Sort::Bool) | (Sort::Int, Sort::Int) | (Sort::Real, Sort::Real) => {
                    true
                }
                (Sort::BitVec(a), Sort::BitVec(b)) => a == b,
                (Sort::FiniteField(a), Sort::FiniteField(b)) => a == b,
                _ => false,
            };
            if !compatible {
                continue;
            }
            for (variable, value) in [(a, b), (b, a)] {
                let TermData::Var(name, _) = builder.terms().get(variable) else {
                    continue;
                };
                if frozen(name, &binders, owner)? {
                    continue;
                }
                tick(owner, 1)?;
                if layer_vars.contains(&variable) || layer_referenced.contains(&variable) {
                    continue;
                }
                let (occurs, captures) = occurs_or_captures(
                    builder.terms(),
                    value,
                    variable,
                    &layer_vars,
                    &binders,
                    &mut value_vars,
                    owner,
                )?;
                if occurs || captures {
                    continue;
                }
                push(&mut layer, (position, Some((variable, value))), owner)?;
                tick(owner, 1)?;
                layer_vars.insert(variable);
                for &referenced in &value_vars {
                    tick(owner, 1)?;
                    layer_referenced.insert(referenced);
                }
                break;
            }
        }
        if layer.is_empty() {
            break;
        }
        // Record the layer's definitions in scan order, then drop its
        // roots by one in-place compaction pass: removing them one by
        // one charges the suffix memmove per removal, quadratic on
        // interleaved definition/residual roots. Layer positions are
        // ascending (scan order) and duplicate-free, so a two-pointer
        // merge moves each kept root at most once.
        let mut subst: DetHashMap<TermId, TermId> = DetHashMap::default();
        for &(_, definition) in &layer {
            if let Some((variable, value)) = definition {
                tick(owner, 1)?;
                subst.insert(variable, value);
                push(&mut definitions, (variable, value), owner)?;
            }
        }
        let mut removed = layer.iter().map(|&(position, _)| position).peekable();
        let mut write = 0usize;
        for read in 0..roots.len() {
            tick(owner, 1)?;
            if removed.peek() == Some(&read) {
                removed.next();
                continue;
            }
            if write != read {
                tick(owner, 1)?;
                roots[write] = roots[read];
            }
            write += 1;
        }
        if removed.next().is_some() {
            return Err(failed());
        }
        tick(owner, roots.len() - write)?;
        roots.truncate(write);
        if subst.is_empty() {
            continue;
        }
        // Rewrite only the subgraph reachable from the remaining roots,
        // in ascending id order (the append-only store keeps children
        // before parents), rebuilding just the nodes whose subgraph
        // contains a substituted variable. The rebuild call sequence
        // for affected nodes matches eliminating the layer's variables
        // one at a time composed in any order (they are independent).
        let mut visited: Vec<TermId> = Vec::new();
        let mut seen: DetHashSet<TermId> = DetHashSet::default();
        let mut pending: Vec<TermId> = Vec::new();
        reserve_counted(&mut pending, roots.len(), owner).map_err(|_| failed())?;
        tick(owner, roots.len())?;
        pending.extend_from_slice(&roots);
        while let Some(id) = pending.pop() {
            tick(owner, 1)?;
            if id.index() >= builder.terms().len() {
                return Err(failed());
            }
            tick(owner, 1)?;
            if !seen.insert(id) {
                continue;
            }
            push(&mut visited, id, owner)?;
            args.clear();
            children(builder.terms().get(id), &mut args, owner)?;
            for &child in &args {
                tick(owner, 1)?;
                if child.index() >= id.index() {
                    return Err(failed());
                }
                push(&mut pending, child, owner)?;
            }
        }
        visited.sort_unstable_by_key(|id| id.index());
        let mut mapped: DetHashMap<TermId, TermId> = DetHashMap::default();
        let mut affected: DetHashSet<TermId> = DetHashSet::default();
        for id in visited {
            tick(owner, 1)?;
            if let Some(&value) = subst.get(&id) {
                tick(owner, 1)?;
                affected.insert(id);
                mapped.insert(id, value);
                continue;
            }
            args.clear();
            children(builder.terms().get(id), &mut args, owner)?;
            if !args.iter().any(|child| affected.contains(child)) {
                tick(owner, 1)?;
                mapped.insert(id, id);
                continue;
            }
            tick(owner, 1)?;
            affected.insert(id);
            for child in &mut args {
                tick(owner, 1)?;
                *child = *mapped.get(child).ok_or_else(failed)?;
            }
            let rebuilt = builder.rebuild_existing(id, &args).map_err(|_| failed())?;
            tick(owner, 1)?;
            mapped.insert(id, rebuilt);
        }
        for root in &mut roots {
            tick(owner, 1)?;
            *root = *mapped.get(root).ok_or_else(failed)?;
        }
    }
    builder.finish().map_err(|_| failed())?;
    Ok(Eliminated { roots, definitions })
}

#[cfg(test)]
mod tests {
    use super::*;
    use ay_core::original_query::{CountedAdmission, FiniteAdmissionGrant};
    use std::sync::{
        atomic::{AtomicBool, Ordering},
        Arc,
    };

    fn owner(stop: Arc<AtomicBool>) -> CountedAdmission {
        CountedAdmission::new(
            FiniteAdmissionGrant::new(20_000_000, 64 << 20),
            None,
            Arc::new(move || stop.load(Ordering::Relaxed)),
        )
        .unwrap()
    }

    fn equality(store: &mut TermStore, a: TermId, b: TermId) -> TermId {
        store.mk_app(Symbol::named("="), [a, b], Sort::Bool)
    }

    #[test]
    fn admitted_substitution_preserves_opaque_operators_and_detects_occurs_cycles() {
        let mut store = TermStore::new();
        let x = store.mk_var("x", Sort::Int);
        let y = store.mk_var("y", Sort::Int);
        let one = store.mk_int(1.into());
        store.register_declared_function("opaque");
        let app = store.mk_app(Symbol::named("opaque"), [x], Sort::Int);
        let defining = equality(&mut store, x, one);
        let residual = equality(&mut store, app, y);
        let admitted = owner(Arc::new(AtomicBool::new(false)));
        let result = eliminate(&mut store, vec![defining, residual], &admitted).unwrap();
        assert_eq!(result.definitions.len(), 2);
        let rebuilt = result.definitions[1].1;
        assert_eq!(
            store.get(rebuilt),
            &TermData::App(Symbol::named("opaque"), vec![one])
        );
        assert_eq!(
            store.get(app),
            &TermData::App(Symbol::named("opaque"), vec![x])
        );
        let cyclic = equality(&mut store, x, app);
        let result = eliminate(&mut store, vec![cyclic], &admitted).unwrap();
        assert_eq!(result.roots, [cyclic]);
        assert_eq!(result.definitions.as_slice(), &[] as &[(TermId, TermId)]);
    }

    #[test]
    fn binder_names_cannot_be_captured_or_eliminated_and_declared_equality_is_opaque() {
        let mut store = TermStore::new();
        let x = store.mk_var("x", Sort::Int);
        let y = store.mk_var("bound", Sort::Int);
        let eq = equality(&mut store, x, y);
        let quantifier = store.mk_forall(vec![("bound".into(), Sort::Int)], eq);
        let admitted = owner(Arc::new(AtomicBool::new(false)));
        let result = eliminate(&mut store, vec![eq, quantifier], &admitted).unwrap();
        assert_eq!(result.roots, [eq, quantifier]);
        assert_eq!(result.definitions.as_slice(), &[] as &[(TermId, TermId)]);
        store.register_declared_function("=");
        let result = eliminate(&mut store, vec![eq], &admitted).unwrap();
        assert_eq!(result.roots, [eq]);
        assert_eq!(result.definitions.as_slice(), &[] as &[(TermId, TermId)]);
    }

    /// At the production functional-work budget (1M units), eliminating
    /// many independent definitions must not re-scan the whole store per
    /// candidate / per elimination: that quadratic charging refused
    /// `(apply solve-eqs)` at ~90 variable pairs (and on real benchmark
    /// files) while z3 applies it at any of these scales. Removing the
    /// eliminated roots one by one from the interleaved root vector is
    /// likewise quadratic in charged memmoves, so this scale uses
    /// interleaved definition/residual roots throughout.
    #[test]
    fn eliminate_scales_within_functional_work_budget() {
        let mut store = TermStore::new();
        let mut roots = Vec::new();
        for i in 0..1200 {
            let x = store.mk_var(format!("x{i}"), Sort::Int);
            let y = store.mk_var(format!("y{i}"), Sort::Int);
            let one = store.mk_int(1.into());
            let plus = store.mk_app(Symbol::named("+"), [x, one], Sort::Int);
            roots.push(equality(&mut store, y, plus));
            let c = store.mk_int((i as i64).into());
            roots.push(store.mk_app(Symbol::named(">"), [y, c], Sort::Bool));
        }
        let admitted = CountedAdmission::new(
            FiniteAdmissionGrant::new(1_048_576, 64 << 20),
            None,
            Arc::new(|| false),
        )
        .unwrap();
        let result = eliminate(&mut store, roots, &admitted).unwrap();
        assert_eq!(result.definitions.len(), 1200);
        assert_eq!(result.roots.len(), 1200);
        // Every remaining root is a comparison over the substituted term:
        // no root still mentions an eliminated variable as a bare operand.
        for &root in &result.roots {
            let TermData::App(Symbol::Named(op), args) = store.get(root) else {
                panic!("expected comparison root, got {:?}", store.get(root));
            };
            assert_eq!(op, ">");
            assert!(matches!(
                store.get(args[0]),
                TermData::App(Symbol::Named(name), _) if name == "+"
            ));
        }
    }

    /// Chained definitions (`y = z + 1`, `z = x + 1`) must compose fully:
    /// after elimination no remaining root may mention an eliminated
    /// variable, in either definition order. A layer that batches both
    /// definitions without symmetric independence would leave `z` free
    /// in the residual while also recording it as defined.
    #[test]
    fn chained_definitions_compose_in_either_order() {
        for chained_first in [true, false] {
            let mut store = TermStore::new();
            let x = store.mk_var("x", Sort::Int);
            let y = store.mk_var("y", Sort::Int);
            let z = store.mk_var("z", Sort::Int);
            let one = store.mk_int(1.into());
            let five = store.mk_int(5.into());
            let z_plus = store.mk_app(Symbol::named("+"), [z, one], Sort::Int);
            let x_plus = store.mk_app(Symbol::named("+"), [x, one], Sort::Int);
            let def_y = equality(&mut store, y, z_plus);
            let def_z = equality(&mut store, z, x_plus);
            let residual = store.mk_app(Symbol::named(">"), [y, five], Sort::Bool);
            let roots = if chained_first {
                vec![def_y, def_z, residual]
            } else {
                vec![def_z, def_y, residual]
            };
            let admitted = owner(Arc::new(AtomicBool::new(false)));
            let result = eliminate(&mut store, roots, &admitted).unwrap();
            assert_eq!(result.definitions.len(), 2, "chained_first={chained_first}");
            assert_eq!(result.roots.len(), 1, "chained_first={chained_first}");
            let marked = reachable(&store, &result.roots, &admitted).unwrap();
            assert!(
                !marked[y.index()] && !marked[z.index()],
                "eliminated variable survives in residual (chained_first={chained_first})"
            );
            assert!(marked[x.index()]);
        }
    }

    #[test]
    fn original_refusal_stays_sticky_before_any_term_growth() {
        let mut store = TermStore::new();
        let x = store.mk_var("x", Sort::Int);
        let one = store.mk_int(1.into());
        let eq = equality(&mut store, x, one);
        let stop = Arc::new(AtomicBool::new(false));
        let admitted = owner(Arc::clone(&stop));
        stop.store(true, Ordering::Relaxed);
        let count = store.len();
        assert!(eliminate(&mut store, vec![eq], &admitted).is_err());
        stop.store(false, Ordering::Relaxed);
        assert!(eliminate(&mut store, vec![eq], &admitted).is_err());
        assert_eq!(store.len(), count);
        let fresh = owner(Arc::clone(&stop));
        assert_eq!(
            eliminate(&mut store, vec![eq], &fresh)
                .unwrap()
                .roots
                .as_slice(),
            &[] as &[TermId]
        );
    }
}
