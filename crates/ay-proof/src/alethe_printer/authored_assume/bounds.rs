// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Resource accounting and iterative rendering bounds for authored bridges.

use super::{
    AlethePrintError, AuthoredAssumeAccounting, AuthoredAssumePlan, MAX_AUTHORED_ASSUME_BRIDGES,
    MAX_CANONICAL_RENDER_NODES, MAX_EQUIVALENCE_BYTES, MAX_EQUIVALENCE_DEPTH,
    MAX_EQUIVALENCE_TOTAL_INPUT_BYTES, MAX_EQUIVALENCE_TOTAL_NODES,
    MAX_EQUIVALENCE_TOTAL_OUTPUT_BYTES,
};
use ay_core::{Constant, ProofId, Sort, Symbol, TermData, TermId, TermStore};

pub(super) fn invalid_authored_assume_plan(id: ProofId, reason: &str) -> AlethePrintError {
    AlethePrintError::InvalidSurfaceStep {
        id,
        reason: reason.to_string(),
    }
}

pub(super) fn account_authored_assume_planning_input(
    id: ProofId,
    input_bytes: usize,
    accounting: &mut AuthoredAssumeAccounting,
) -> Result<(), AlethePrintError> {
    let Some(next_input_bytes) = accounting.total_input_bytes.checked_add(input_bytes) else {
        return Err(invalid_authored_assume_plan(
            id,
            "authored assume bridge aggregate input size overflowed",
        ));
    };
    if next_input_bytes > MAX_EQUIVALENCE_TOTAL_INPUT_BYTES {
        return Err(invalid_authored_assume_plan(
            id,
            "authored assume bridges exceed the aggregate input-size bound",
        ));
    }
    accounting.total_input_bytes = next_input_bytes;
    Ok(())
}

fn add_canonical_payload(bytes: &mut usize, amount: usize) -> bool {
    let Some(next) = bytes.checked_add(amount) else {
        return false;
    };
    if next > MAX_EQUIVALENCE_BYTES {
        return false;
    }
    *bytes = next;
    true
}

fn add_canonical_text_payload(bytes: &mut usize, text: &str) -> bool {
    // Quoted SMT symbols and strings add delimiters and can duplicate an
    // escaping character. Four times the UTF-8 payload plus the per-node base
    // charge is a conservative allocation bound.
    text.len()
        .checked_mul(4)
        .is_some_and(|amount| add_canonical_payload(bytes, amount))
}

fn canonical_constant_payload_is_bounded(constant: &Constant, bytes: &mut usize) -> bool {
    let payload = match constant {
        Constant::Bool(_) => 5,
        Constant::Int(value) => match usize::try_from(value.bits()) {
            Ok(bits) => bits.saturating_add(4),
            Err(_) => return false,
        },
        Constant::Rational(value) => {
            let bits = value.0.numer().bits().checked_add(value.0.denom().bits());
            match bits.and_then(|bits| usize::try_from(bits).ok()) {
                Some(bits) => bits.saturating_add(16),
                None => return false,
            }
        }
        Constant::BitVec { value, width } => {
            let rendered_bits = value.bits().max(u64::from(*width));
            match usize::try_from(rendered_bits) {
                Ok(bits) => bits.saturating_add(2),
                Err(_) => return false,
            }
        }
        Constant::String(value) => return add_canonical_text_payload(bytes, value),
        _ => return false,
    };
    add_canonical_payload(bytes, payload)
}

/// Charge the payload a bound variable's or a constant array's SORT renders to.
///
/// `format_quantifier` prints `(name sort)` for every binding and
/// `format_const_array` prints `((as const sort) value)`, so a sort's own
/// rendering is part of the canonical bytes. `Sort` is a separate recursive
/// structure the term walk never reaches, so it gets its own bounded walk here
/// instead of being left unmeasured: without it a term could answer
/// `UnsupportedShape` — the QUIET answer — while still carrying an unbounded
/// rendering. Only `Array` and `Seq` recurse; every other constructor renders
/// to a bare name or a fixed keyword form, so the per-node charge covers it.
fn canonical_sort_payload_is_bounded(root: &Sort, bytes: &mut usize) -> bool {
    /// `(_ FloatingPoint 4294967295 4294967295)` is the widest fixed-shape
    /// rendering any single sort constructor produces.
    const SORT_NODE_PAYLOAD: usize = 64;
    let mut stack = vec![root];
    let mut visited = 0usize;
    while let Some(sort) = stack.pop() {
        let Some(next_visited) = visited.checked_add(1) else {
            return false;
        };
        if next_visited > MAX_CANONICAL_RENDER_NODES
            || !add_canonical_payload(bytes, SORT_NODE_PAYLOAD)
        {
            return false;
        }
        visited = next_visited;
        // The only sorts whose rendering carries a variable-length payload are
        // the ones printed as a bare name; every other constructor is covered
        // by the per-node charge above.
        let named_payload = match sort {
            Sort::Array(array) => {
                if visited
                    .checked_add(stack.len())
                    .and_then(|scheduled| scheduled.checked_add(2))
                    .is_none_or(|scheduled| scheduled > MAX_CANONICAL_RENDER_NODES)
                {
                    return false;
                }
                stack.push(&array.index_sort);
                stack.push(&array.element_sort);
                None
            }
            Sort::Seq(element) => {
                if visited
                    .checked_add(stack.len())
                    .and_then(|scheduled| scheduled.checked_add(1))
                    .is_none_or(|scheduled| scheduled > MAX_CANONICAL_RENDER_NODES)
                {
                    return false;
                }
                stack.push(element.as_ref());
                None
            }
            Sort::Uninterpreted(name) | Sort::FiniteDomain(name, _) | Sort::TypeVar(name) => {
                Some(name.as_str())
            }
            // `Display` prints a datatype sort by NAME; its constructors and
            // field sorts are never rendered.
            Sort::Datatype(datatype) => Some(datatype.name.as_str()),
            _ => None,
        };
        if named_payload.is_some_and(|name| !add_canonical_text_payload(bytes, name)) {
            return false;
        }
    }
    true
}

fn canonical_symbol_payload_bound(symbol: &Symbol, bytes: &mut usize) -> CanonicalRenderBound {
    match symbol {
        // Constant-array rendering recursively formats a sort as well as its
        // child. This narrow arithmetic lane does not admit that unmetered
        // tree. That is a schema this lane cannot render, not an exhausted
        // budget, so it declines the bridge instead of failing the whole
        // document -- but only AFTER the caller has finished measuring the rest
        // of the term, because a term that is ALSO oversized must still fail
        // loudly. The name's own bytes are charged either way.
        Symbol::Named(name) if name == "const-array" => {
            if add_canonical_text_payload(bytes, name) {
                CanonicalRenderBound::UnsupportedShape
            } else {
                CanonicalRenderBound::ExceedsBound
            }
        }
        Symbol::Named(name) => {
            CanonicalRenderBound::from_budget(add_canonical_text_payload(bytes, name))
        }
        Symbol::Indexed(name, indices) => CanonicalRenderBound::from_budget(
            add_canonical_text_payload(bytes, name)
                && indices
                    .len()
                    .checked_mul(12)
                    .is_some_and(|amount| add_canonical_payload(bytes, amount)),
        ),
        _ => CanonicalRenderBound::ExceedsBound,
    }
}

/// Why the canonical pre-render preflight declined, when it declined.
///
/// The three outcomes are not interchangeable, and they are ORDERED:
/// `ExceedsBound` dominates `UnsupportedShape`, which dominates `Bounded`.
/// `ExceedsBound` means the metered walk ran out of depth, nodes or bytes: the
/// term is real work this lane refuses to do, and refusing must be loud.
/// `UnsupportedShape` means the whole term fits inside every rendering bound
/// but uses a schema this narrow bridge does not render — a binder, a `let`, or
/// AY's internal constant array — which is a statement about the schema, not
/// about size, and is the same answer every other unsupported bridge schema
/// already gives by declining into `AuthoredAssumePlanner::unsupported`.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub(super) enum CanonicalRenderBound {
    /// The fully expanded canonical tree fits inside every rendering bound.
    Bounded,
    /// The tree fits inside every rendering bound but contains a schema this
    /// bridge lane cannot render at any size.
    UnsupportedShape,
    /// Depth, node or byte accounting was exhausted (or overflowed).
    ExceedsBound,
}

impl CanonicalRenderBound {
    /// Lift a resource-accounting predicate: a `false` from the meters is
    /// always exhaustion, never an unsupported schema.
    fn from_budget(within_budget: bool) -> Self {
        if within_budget {
            Self::Bounded
        } else {
            Self::ExceedsBound
        }
    }

    pub(super) fn is_bounded(self) -> bool {
        matches!(self, Self::Bounded)
    }
}

/// Bound the fully expanded canonical tree before calling the recursive term
/// renderer. Deliberately visits repeated DAG children repeatedly: formatting
/// copies a child's bytes at every occurrence, so unique-node counting would
/// understate both output and stack work on a highly shared term.
///
/// The walk MEASURES THE WHOLE TERM before it may answer `UnsupportedShape`. An
/// unrenderable schema is recorded and the walk CONTINUES through the rest of
/// the tree, so the SIZE verdict always dominates the SHAPE verdict: a term
/// that is both unrenderable and oversized answers `ExceedsBound` and stays
/// fatal. Answering at the binder instead — the instant the stack popped one —
/// left the remainder unmeasured, let a binder-wrapped 1_000_000-argument
/// application reach the printer through the quiet lane, and made the verdict
/// depend on which child the stack happened to pop first: the same
/// `(and WIDE (= (select (const-array v) k) v))` answered one way with the wide
/// conjunct first and the other way with it second.
pub(super) fn canonical_term_is_bounded_for_authored_assume(
    terms: &TermStore,
    root: TermId,
) -> CanonicalRenderBound {
    let mut stack = vec![(root, 0usize)];
    let mut nodes = 0usize;
    let mut bytes = 0usize;
    // Recorded, never returned on mid-walk. See the doc comment: the quiet
    // answer is only available to a term the WHOLE of which fits inside the
    // rendering bounds.
    let mut unsupported_shape = false;
    while let Some((term, depth)) = stack.pop() {
        if depth > MAX_EQUIVALENCE_DEPTH {
            return CanonicalRenderBound::ExceedsBound;
        }
        let Some(next_nodes) = nodes.checked_add(1) else {
            return CanonicalRenderBound::ExceedsBound;
        };
        if next_nodes > MAX_CANONICAL_RENDER_NODES || !add_canonical_payload(&mut bytes, 32) {
            return CanonicalRenderBound::ExceedsBound;
        }
        nodes = next_nodes;
        let next_depth = match depth.checked_add(1) {
            Some(next) => next,
            None => return CanonicalRenderBound::ExceedsBound,
        };
        let mut push_children = |children: &[TermId]| {
            if nodes
                .checked_add(stack.len())
                .and_then(|scheduled| scheduled.checked_add(children.len()))
                .is_none_or(|scheduled| scheduled > MAX_CANONICAL_RENDER_NODES)
            {
                return false;
            }
            stack.extend(children.iter().rev().map(|&child| (child, next_depth)));
            true
        };
        match terms.get(term) {
            TermData::Var(name, _) => {
                if !add_canonical_text_payload(&mut bytes, name) {
                    return CanonicalRenderBound::ExceedsBound;
                }
            }
            TermData::Const(constant) => {
                if !canonical_constant_payload_is_bounded(constant, &mut bytes) {
                    return CanonicalRenderBound::ExceedsBound;
                }
            }
            TermData::App(symbol, arguments) => {
                match canonical_symbol_payload_bound(symbol, &mut bytes) {
                    CanonicalRenderBound::Bounded => {}
                    // `format_const_array` renders `((as const SORT) value)`,
                    // so the application's own sort is part of the payload.
                    // Charge it and KEEP WALKING.
                    CanonicalRenderBound::UnsupportedShape => {
                        unsupported_shape = true;
                        if !canonical_sort_payload_is_bounded(terms.sort(term), &mut bytes) {
                            return CanonicalRenderBound::ExceedsBound;
                        }
                    }
                    CanonicalRenderBound::ExceedsBound => {
                        return CanonicalRenderBound::ExceedsBound
                    }
                }
                if !push_children(arguments) {
                    return CanonicalRenderBound::ExceedsBound;
                }
            }
            TermData::Not(inner) => {
                if !push_children(std::slice::from_ref(inner)) {
                    return CanonicalRenderBound::ExceedsBound;
                }
            }
            TermData::Ite(condition, then_branch, else_branch) => {
                if !push_children(&[*condition, *then_branch, *else_branch]) {
                    return CanonicalRenderBound::ExceedsBound;
                }
            }
            // The supported bridge schemas are quantifier-free applications, so
            // a `let` or a binder is a schema no size makes renderable here and
            // the caller declines the bridge rather than failing the document.
            // Record that and CONTINUE metering: the bound names, the bindings
            // and the body are all part of what the recursive renderer would
            // format, and an oversized one of them outranks the shape and has
            // to stay fatal.
            TermData::Let(bindings, body) => {
                unsupported_shape = true;
                for (name, value) in bindings {
                    if !add_canonical_text_payload(&mut bytes, name)
                        || !push_children(std::slice::from_ref(value))
                    {
                        return CanonicalRenderBound::ExceedsBound;
                    }
                }
                if !push_children(std::slice::from_ref(body)) {
                    return CanonicalRenderBound::ExceedsBound;
                }
            }
            TermData::Forall(bindings, body, triggers)
            | TermData::Exists(bindings, body, triggers) => {
                unsupported_shape = true;
                for (name, sort) in bindings {
                    if !add_canonical_text_payload(&mut bytes, name)
                        || !canonical_sort_payload_is_bounded(sort, &mut bytes)
                    {
                        return CanonicalRenderBound::ExceedsBound;
                    }
                }
                if !push_children(std::slice::from_ref(body)) {
                    return CanonicalRenderBound::ExceedsBound;
                }
                // `format_quantifier` drops the trigger sets, but they are part
                // of the term and this preflight must not settle the size
                // question on whichever sub-part the renderer happens to visit.
                for group in triggers {
                    if !push_children(group) {
                        return CanonicalRenderBound::ExceedsBound;
                    }
                }
            }
            _ => return CanonicalRenderBound::ExceedsBound,
        }
    }
    if unsupported_shape {
        CanonicalRenderBound::UnsupportedShape
    } else {
        CanonicalRenderBound::Bounded
    }
}

pub(super) fn account_authored_assume_emission(
    id: ProofId,
    plan: &AuthoredAssumePlan,
    nodes: usize,
    output_bytes: usize,
    accounting: &mut AuthoredAssumeAccounting,
) -> Result<(), AlethePrintError> {
    let Some(next_bridge_count) = accounting.bridge_count.checked_add(1) else {
        return Err(invalid_authored_assume_plan(
            id,
            "authored assume bridge count overflowed",
        ));
    };
    if next_bridge_count > MAX_AUTHORED_ASSUME_BRIDGES {
        return Err(invalid_authored_assume_plan(
            id,
            "authored assume bridge count exceeds the planner bound",
        ));
    }
    let Some(next_input_bytes) = accounting.total_input_bytes.checked_add(plan.input_bytes) else {
        return Err(invalid_authored_assume_plan(
            id,
            "authored assume bridge aggregate input size overflowed",
        ));
    };
    if next_input_bytes > MAX_EQUIVALENCE_TOTAL_INPUT_BYTES {
        return Err(invalid_authored_assume_plan(
            id,
            "authored assume bridges exceed the aggregate input-size bound",
        ));
    }
    let Some(next_nodes) = accounting.total_nodes.checked_add(nodes) else {
        return Err(invalid_authored_assume_plan(
            id,
            "authored assume bridge node accounting overflowed",
        ));
    };
    if next_nodes > MAX_EQUIVALENCE_TOTAL_NODES {
        return Err(invalid_authored_assume_plan(
            id,
            "authored assume bridges exceed the aggregate node bound",
        ));
    }
    let Some(next_output_bytes) = accounting.total_output_bytes.checked_add(output_bytes) else {
        return Err(invalid_authored_assume_plan(
            id,
            "authored assume bridge aggregate output size overflowed",
        ));
    };
    if next_output_bytes > MAX_EQUIVALENCE_TOTAL_OUTPUT_BYTES {
        return Err(invalid_authored_assume_plan(
            id,
            "authored assume bridges exceed the aggregate output-size bound",
        ));
    }
    accounting.bridge_count = next_bridge_count;
    accounting.total_input_bytes = next_input_bytes;
    accounting.total_nodes = next_nodes;
    accounting.total_output_bytes = next_output_bytes;
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::{
        canonical_term_is_bounded_for_authored_assume, CanonicalRenderBound,
        MAX_CANONICAL_RENDER_NODES,
    };
    use ay_core::{Sort, Symbol, TermStore};

    /// The preflight's two declines are not interchangeable, and this pins the
    /// split at the source. Budget exhaustion stays LOUD — the caller escalates
    /// it to `InvalidSurfaceStep`, which `export_last_unsat_artifact` turns into
    /// no artifact at all — while a schema this lane cannot render at any size
    /// must be QUIET, so the caller declines just the bridge. Collapsing either
    /// direction re-creates one of the two defects: a document lost to one
    /// quantified assertion, or a bound that no longer fails closed.
    #[test]
    fn canonical_preflight_separates_unrenderable_shapes_from_exhausted_budgets() {
        let mut terms = TermStore::new();
        let x = terms.mk_var("x", Sort::Int);
        let zero = terms.mk_int(0.into());
        let ground = terms.mk_app(Symbol::named("<="), [zero, x], Sort::Bool);
        assert_eq!(
            canonical_term_is_bounded_for_authored_assume(&terms, ground),
            CanonicalRenderBound::Bounded,
            "an ordinary small ground comparison is renderable"
        );

        let quantified = terms.mk_forall(vec![("x".to_string(), Sort::Int)], ground);
        assert_eq!(
            canonical_term_is_bounded_for_authored_assume(&terms, quantified),
            CanonicalRenderBound::UnsupportedShape,
            "a binder is an unrenderable schema, not an exhausted budget"
        );
        let existential = terms.mk_exists(vec![("x".to_string(), Sort::Int)], ground);
        assert_eq!(
            canonical_term_is_bounded_for_authored_assume(&terms, existential),
            CanonicalRenderBound::UnsupportedShape,
            "an existential is an unrenderable schema, not an exhausted budget"
        );

        let byte = Sort::bitvec(8);
        let fill = terms.mk_bitvec(0u32.into(), 8);
        let const_array = terms.mk_app(
            Symbol::named("const-array"),
            [fill],
            Sort::array(byte.clone(), byte.clone()),
        );
        let key = terms.mk_var("k", byte.clone());
        let read = terms.mk_app(Symbol::named("select"), [const_array, key], byte);
        let read_is_fill = terms.mk_app(Symbol::named("="), [read, fill], Sort::Bool);
        assert_eq!(
            canonical_term_is_bounded_for_authored_assume(&terms, read_is_fill),
            CanonicalRenderBound::UnsupportedShape,
            "a constant array nested under a supported application still declines as a schema"
        );

        // Past MAX_EQUIVALENCE_DEPTH: a real budget, and it must stay loud.
        let mut deep = terms.mk_var("deep_x", Sort::Int);
        for _ in 0..80 {
            deep = terms.mk_app(Symbol::named("deep_f"), [deep], Sort::Int);
        }
        let deep_root = terms.mk_app(Symbol::named("<="), [zero, deep], Sort::Bool);
        assert_eq!(
            canonical_term_is_bounded_for_authored_assume(&terms, deep_root),
            CanonicalRenderBound::ExceedsBound,
            "depth exhaustion is a budget failure and must not be softened to a schema decline"
        );
    }

    /// A `forall` (or `let`, or `const-array`) wrapped around a term this lane
    /// could never afford to render is a SIZE failure, and the size verdict
    /// outranks the shape verdict.
    ///
    /// The preflight may only answer `UnsupportedShape` — the QUIET answer,
    /// which the planner turns into "no bridge" instead of "no document" —
    /// about a term the WHOLE of which fits inside the node, byte and depth
    /// bounds. Answering the instant the walk met the binder left everything
    /// under it unmeasured: measured on the rejected revision, a
    /// `(forall ((z Int)) (or p x1_000_000))` was declined quietly and then
    /// RENDERED by the printer in 31_979us, against 0.5us for a loud refusal
    /// of the same term without its binder.
    #[test]
    fn canonical_preflight_finishes_metering_before_it_answers_unsupported_shape() {
        let mut terms = TermStore::new();
        let p = terms.mk_var("p", Sort::Bool);
        let unaffordable = terms.mk_app(
            Symbol::named("or"),
            vec![p; MAX_CANONICAL_RENDER_NODES + 1],
            Sort::Bool,
        );
        let affordable = terms.mk_app(Symbol::named("or"), vec![p; 4], Sort::Bool);

        for (shape, body) in [("affordable", affordable), ("unaffordable", unaffordable)] {
            let expected = if body == affordable {
                CanonicalRenderBound::UnsupportedShape
            } else {
                CanonicalRenderBound::ExceedsBound
            };
            let quantified = terms.mk_forall(vec![("z".to_string(), Sort::Int)], body);
            assert_eq!(
                canonical_term_is_bounded_for_authored_assume(&terms, quantified),
                expected,
                "a forall over an {shape} body must answer on the SIZE of the whole term"
            );
            let existential = terms.mk_exists(vec![("z".to_string(), Sort::Int)], body);
            assert_eq!(
                canonical_term_is_bounded_for_authored_assume(&terms, existential),
                expected,
                "an exists over an {shape} body must answer on the SIZE of the whole term"
            );
            let bound = terms.mk_let(vec![("v".to_string(), p)], body);
            assert_eq!(
                canonical_term_is_bounded_for_authored_assume(&terms, bound),
                expected,
                "a let over an {shape} body must answer on the SIZE of the whole term"
            );
        }

        // Depth is metered THROUGH the binder too, not just node count.
        let mut deep = terms.mk_var("deep_p", Sort::Bool);
        for _ in 0..80 {
            deep = terms.mk_app(Symbol::named("deep_g"), [deep], Sort::Bool);
        }
        let deep_under_binder = terms.mk_forall(vec![("z".to_string(), Sort::Int)], deep);
        assert_eq!(
            canonical_term_is_bounded_for_authored_assume(&terms, deep_under_binder),
            CanonicalRenderBound::ExceedsBound,
            "depth exhaustion under a binder is still a budget failure"
        );

        // The BYTE meter has to outrank the recorded shape as well, and it is
        // the one that trips mid-walk: 4_096 arguments stay inside the node
        // bound but blow the byte budget after the binder has already been
        // seen, so the answer is decided by a charge that runs AFTER the shape
        // was recorded rather than by the node pre-check.
        let byte_heavy = terms.mk_app(Symbol::named("or"), vec![p; 4096], Sort::Bool);
        assert_eq!(
            canonical_term_is_bounded_for_authored_assume(&terms, byte_heavy),
            CanonicalRenderBound::ExceedsBound,
            "4_096 arguments must be inside the node bound and past the byte bound"
        );
        let byte_heavy_under_binder =
            terms.mk_forall(vec![("z".to_string(), Sort::Int)], byte_heavy);
        assert_eq!(
            canonical_term_is_bounded_for_authored_assume(&terms, byte_heavy_under_binder),
            CanonicalRenderBound::ExceedsBound,
            "byte exhaustion under a binder is still a budget failure"
        );

        // ...and the verdict cannot depend on which conjunct the stack pops
        // first. On the rejected revision the same conjunction refused in
        // 0.4us with the wide operand first and returned a 240-byte document
        // in 7_710us with it second.
        let byte = Sort::bitvec(8);
        let fill = terms.mk_bitvec(0u32.into(), 8);
        let const_array = terms.mk_app(
            Symbol::named("const-array"),
            [fill],
            Sort::array(byte.clone(), byte.clone()),
        );
        let key = terms.mk_var("k", byte.clone());
        let read = terms.mk_app(Symbol::named("select"), [const_array, key], byte);
        let read_is_fill = terms.mk_app(Symbol::named("="), [read, fill], Sort::Bool);
        for (shape, other, expected) in [
            (
                "affordable",
                affordable,
                CanonicalRenderBound::UnsupportedShape,
            ),
            (
                "unaffordable",
                unaffordable,
                CanonicalRenderBound::ExceedsBound,
            ),
        ] {
            let read_first = terms.mk_app(Symbol::named("and"), [read_is_fill, other], Sort::Bool);
            let read_second = terms.mk_app(Symbol::named("and"), [other, read_is_fill], Sort::Bool);
            assert_eq!(
                canonical_term_is_bounded_for_authored_assume(&terms, read_first),
                expected,
                "a constant array conjoined with an {shape} operand, read first"
            );
            assert_eq!(
                canonical_term_is_bounded_for_authored_assume(&terms, read_second),
                expected,
                "a constant array conjoined with an {shape} operand, read second"
            );
        }
    }
}
