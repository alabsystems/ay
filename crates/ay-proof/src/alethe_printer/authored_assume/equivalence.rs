// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Recursive checked equivalence rendering for authored assumption spellings.

use super::*;

impl AlethePrinter<'_> {
    fn begin_authored_equivalence<'a>(
        &self,
        id: &str,
        surface: &str,
        canonical_term: TermId,
        depth: usize,
        nodes: &mut usize,
        shared: Option<&shared_canonical::SharedInput<'a>>,
    ) -> Option<std::borrow::Cow<'a, str>> {
        if !self.admit_emission_work(surface.len() as u64 + id.len() as u64) {
            return None;
        }
        if depth == 0 {
            self.open_boolean_fold_scope(canonical_term);
        }
        if depth > MAX_EQUIVALENCE_DEPTH || *nodes >= MAX_EQUIVALENCE_NODES {
            return None;
        }
        *nodes += 1;
        if let Some(input) = shared {
            if !self.admit_emission_work(input.dag.lookup_work() as u64) {
                return None;
            }
            let text = input.dag.text(input.canonical, canonical_term)?;
            return self
                .admit_emission_work(text.len() as u64)
                .then_some(std::borrow::Cow::Borrowed(text));
        }
        let charge =
            super::bounds::canonical_rendering_work_upper_bound(self.terms, canonical_term)?;
        if !self.admit_emission_work(charge) {
            return None;
        }
        Some(std::borrow::Cow::Owned(crate::render_term_canonical(
            self.terms,
            canonical_term,
        )))
    }

    /// Emit a checked equality between `surface` and the identity rendering of
    /// `canonical_term`. Recursion follows the canonical term DAG and admits
    /// only the selected leaf schema below same-head congruence. A depth-0
    /// call is the bridge ROOT: it opens the scope the Boolean-fold leaf reads
    /// (`boolean_fold/document_spelling.rs`).
    pub(super) fn build_authored_surface_equivalence(
        &self,
        id: &str,
        surface: &str,
        canonical_term: TermId,
        schema: EquivalenceLeafSchema,
        direction: EquivalenceDirection,
        depth: usize,
        nodes: &mut usize,
        output: &mut Vec<String>,
        shared: Option<&shared_canonical::SharedInput<'_>>,
    ) -> bool {
        let Some(canonical) =
            self.begin_authored_equivalence(id, surface, canonical_term, depth, nodes, shared)
        else {
            return false;
        };
        if surface == canonical.as_ref() {
            return false;
        }

        if matches!(
            schema,
            EquivalenceLeafSchema::AuthoredAssume | EquivalenceLeafSchema::NullaryDefinition
        ) && matches!(self.terms.sort(canonical_term), Sort::Array(_))
        {
            let mut remaining_nodes = MAX_EQUIVALENCE_NODES.saturating_sub(*nodes);
            let Some(forward_work) = id.len().checked_add(6).and_then(|n| u64::try_from(n).ok())
            else {
                return false;
            };
            if !self.admit_emission_work(forward_work) {
                return false;
            }
            let forward_id = match direction {
                EquivalenceDirection::SurfaceToCanonical => id.to_string(),
                EquivalenceDirection::CanonicalToSurface => format!("{id}.store"),
            };
            let rendered = self.literal_store_permutation_equivalence(
                &forward_id,
                surface,
                canonical_term,
                &canonical,
                &mut remaining_nodes,
                MAX_EQUIVALENCE_DEPTH.saturating_sub(depth),
            );
            // The borrowed allowance is never reset after a failed plan.
            *nodes = MAX_EQUIVALENCE_NODES - remaining_nodes;
            if let Some(rendered) = rendered {
                let slots = match direction {
                    EquivalenceDirection::SurfaceToCanonical => 1,
                    EquivalenceDirection::CanonicalToSurface => 2,
                };
                let reverse_work = surface
                    .len()
                    .checked_add(canonical.len())
                    .and_then(|n| n.checked_add(id.len()))
                    .and_then(|n| n.checked_add(forward_id.len()))
                    .and_then(|n| n.checked_add(128));
                let work = slots * std::mem::size_of::<String>()
                    + if matches!(direction, EquivalenceDirection::CanonicalToSurface) {
                        let Some(work) = reverse_work else {
                            return false;
                        };
                        work
                    } else {
                        0
                    };
                if !self.admit_emission_work(work as u64) {
                    return false;
                }
                output.push(rendered);
                if matches!(direction, EquivalenceDirection::CanonicalToSurface) {
                    output.push(format!("(step {id} (cl (= {canonical} {surface})) :rule symm :premises ({forward_id}))"));
                }
                return true;
            }
        }

        if self.exact_identity_leaf_step(
            id,
            surface,
            &canonical,
            canonical_term,
            schema,
            direction,
            output,
        ) {
            return true;
        }
        if self.nullary_definition_leaf_step(
            id,
            surface,
            &canonical,
            canonical_term,
            schema,
            direction,
            depth,
            nodes,
            output,
            shared,
        ) {
            return true;
        }
        let mark = output.len();
        if self.head_congruence_step(
            id,
            surface,
            &canonical,
            canonical_term,
            schema,
            direction,
            depth,
            nodes,
            output,
            shared,
        ) {
            return true;
        }
        output.truncate(mark);
        if self.equality_symmetry_step(
            id,
            surface,
            &canonical,
            canonical_term,
            schema,
            direction,
            depth,
            nodes,
            output,
            shared,
        ) {
            return true;
        }
        if self.double_negation_step(
            id,
            surface,
            &canonical,
            canonical_term,
            schema,
            direction,
            depth,
            nodes,
            output,
            shared,
        ) {
            return true;
        }
        output.truncate(mark);
        self.boolean_fold_step(
            id,
            surface,
            &canonical,
            canonical_term,
            schema,
            direction,
            depth,
            nodes,
            output,
            shared,
        )
    }

    /// The exact-identity leaves: one rule instance relating `surface` to the
    /// `canonical` rendering of `canonical_term`, with no recursion.
    ///
    /// Comparison reversal is a leaf under every schema: it is an exact
    /// identity pinned Carcara's `comp_simplify` checks (the helper screens
    /// that rule's constant-evaluation quirk), so a use-site congruence may
    /// relate an authored `(>= x2 3)` to the interned `(<= 3 x2)` exactly as an
    /// authored assume does. The additive identity and the lenient negative
    /// literal are USE-SITE leaves only: admitting them at an authored
    /// `assume` re-planned that assume to its canonical spelling while the
    /// steps projecting its operands kept printing their authored overrides,
    /// which turned Carcara-valid documents `holey` (measured on the
    /// OR-substitution fuzz).
    fn exact_identity_leaf_step(
        &self,
        id: &str,
        surface: &str,
        canonical: &str,
        canonical_term: TermId,
        schema: EquivalenceLeafSchema,
        direction: EquivalenceDirection,
        output: &mut Vec<String>,
    ) -> bool {
        if comparison_reversal_step(id, surface, canonical, direction, output) {
            return true;
        }
        if !matches!(self.terms.sort(canonical_term), Sort::Int | Sort::Real) {
            return false;
        }
        multiplication_commutation_step(id, surface, canonical, direction, output)
            || (matches!(schema, EquivalenceLeafSchema::UseSiteIdentities)
                && (additive_identity::additive_identity_step(
                    id, surface, canonical, direction, output,
                ) || additive_identity::negative_literal_respelling_step(
                    id, surface, canonical, direction, output,
                )))
    }

    /// `cong` under the canonical term's own head, one child bridge per
    /// differing operand. A canonical `not` or `ite` is a head only where
    /// [`EquivalenceLeafSchema::congruent_under_not`] or
    /// [`EquivalenceLeafSchema::congruent_under_ite`] says so.
    fn head_congruence_step(
        &self,
        id: &str,
        surface: &str,
        canonical: &str,
        canonical_term: TermId,
        schema: EquivalenceLeafSchema,
        direction: EquivalenceDirection,
        depth: usize,
        nodes: &mut usize,
        output: &mut Vec<String>,
        shared: Option<&shared_canonical::SharedInput<'_>>,
    ) -> bool {
        let ite_children;
        let (operator, canonical_children) = match self.terms.get(canonical_term) {
            TermData::App(symbol, children) => (Self::format_symbol(symbol), children.as_slice()),
            TermData::Not(child) if schema.congruent_under_not() => {
                ("not".to_string(), std::slice::from_ref(child))
            }
            TermData::Ite(condition, then_term, else_term) if schema.congruent_under_ite() => {
                ite_children = [*condition, *then_term, *else_term];
                ("ite".to_string(), &ite_children[..])
            }
            _ => return false,
        };
        if let Some(input) = shared {
            let Some(surface_args) =
                input.arguments(self, surface, &operator, canonical_children.len())
            else {
                return false;
            };
            if surface_args.len() != canonical_children.len() {
                return false;
            }
            if !self.admit_emission_work(input.dag.lookup_work() as u64) {
                return false;
            }
            let Some(printed_children) = input.dag.children(canonical_term) else {
                return false;
            };
            let mut premises = Vec::new();
            for (position, ((&surface_arg, &child), (printed_child, span))) in surface_args
                .iter()
                .zip(canonical_children)
                .zip(printed_children)
                .enumerate()
            {
                if child != printed_child {
                    return false;
                }
                let Some(canonical_arg) = input.canonical.get(span) else {
                    return false;
                };
                if schema.needs_no_premise(surface_arg, canonical_arg) {
                    continue;
                }
                let child_id = format!("{id}.c{position}");
                if !self.build_authored_surface_equivalence(
                    &child_id,
                    surface_arg,
                    child,
                    schema,
                    direction,
                    depth + 1,
                    nodes,
                    output,
                    shared,
                ) {
                    return false;
                }
                premises.push(child_id);
            }
            if premises.is_empty() {
                return false;
            }
            let equality = oriented_equivalence(surface, canonical, direction);
            output.push(format!(
                "(step {id} (cl {equality}) :rule cong :premises ({}))",
                premises.join(" ")
            ));
            return true;
        }
        let (Some(surface_args), Some(canonical_args)) = (
            split_application(surface, &operator),
            split_application(canonical, &operator),
        ) else {
            return false;
        };
        if surface_args.len() != canonical_children.len()
            || canonical_args.len() != canonical_children.len()
        {
            return false;
        }

        let mut premises = Vec::new();
        for (position, ((surface_arg, canonical_arg), &child)) in surface_args
            .iter()
            .zip(canonical_args.iter())
            .zip(canonical_children.iter())
            .enumerate()
        {
            if schema.needs_no_premise(surface_arg, canonical_arg) {
                continue;
            }
            let child_id = format!("{id}.c{position}");
            if !self.build_authored_surface_equivalence(
                &child_id,
                surface_arg,
                child,
                schema,
                direction,
                depth + 1,
                nodes,
                output,
                shared,
            ) {
                return false;
            }
            premises.push(child_id);
        }
        if premises.is_empty() {
            return false;
        }
        let equality = oriented_equivalence(surface, canonical, direction);
        output.push(format!(
            "(step {id} (cl {equality}) :rule cong :premises ({}))",
            premises.join(" ")
        ));
        true
    }

    /// The ordinary authored-assume equivalence bridge, as the planner admits
    /// it and the emitter renders it: the authored-spelling schema, then (for
    /// a document with nullary definitions) the definition-reading attempt of
    /// `nullary_definition.rs`. The folded-conjunction projection
    /// (`folded_assume.rs`) bridges a projected conjunct with it too.
    pub(in crate::alethe_printer) fn authored_equivalence(
        &self,
        id: &str,
        surface: &str,
        term: TermId,
        nodes: &mut usize,
        output: &mut Vec<String>,
    ) -> bool {
        self.authored_equivalence_with_canonical(id, surface, term, None, nodes, output)
    }

    pub(super) fn authored_equivalence_with_canonical(
        &self,
        id: &str,
        surface: &str,
        term: TermId,
        canonical: Option<&str>,
        nodes: &mut usize,
        output: &mut Vec<String>,
    ) -> bool {
        if matches!(
            canonical_term_is_bounded_for_authored_assume(self.terms, term),
            CanonicalRenderBound::ExceedsBound
        ) {
            return self.shared_definition_bridge(id, surface, term, canonical, nodes, output);
        }
        self.build_authored_surface_equivalence(
            id,
            surface,
            term,
            EquivalenceLeafSchema::AuthoredAssume,
            EquivalenceDirection::SurfaceToCanonical,
            0,
            nodes,
            output,
            None,
        ) || self.definition_bridge(id, surface, term, nodes, output)
    }

    /// Prove `surface` equal to the canonical rendering of `canonical_term` by
    /// position-preserving congruence over EXACT identities only: binary
    /// numeric multiplication commutation, comparison reversal, and the
    /// additive identity (`additive_identity.rs`). Addition permutation and
    /// every authored-only leaf (Boolean folds, definitions) stay outside this
    /// use-site schema.
    pub(in crate::alethe_printer) fn format_nested_identity_surface_equivalence(
        &self,
        id: &str,
        surface: &str,
        canonical_term: TermId,
        direction: EquivalenceDirection,
    ) -> Option<Vec<String>> {
        if surface.len() > MAX_EQUIVALENCE_BYTES
            || !canonical_term_is_bounded_for_authored_assume(self.terms, canonical_term)
                .is_bounded()
        {
            return None;
        }
        let mut output = Vec::new();
        let mut nodes = 0;
        self.build_authored_surface_equivalence(
            id,
            surface,
            canonical_term,
            EquivalenceLeafSchema::UseSiteIdentities,
            direction,
            0,
            &mut nodes,
            &mut output,
            None,
        )
        .then_some(output)
    }
}

/// Derive the equality between a printed comparison and its argument-swapped
/// canonical spelling (`>=`/`<=`, `>`/`<`). A non-strict pair is one
/// `comp_simplify`; a strict pair goes through `(not (<= ..))`, because
/// `comp_simplify` rewrites `(> a b)` to `(not (<= a b))`, never to `(< b a)`.
pub(in crate::alethe_printer) fn comparison_reversal_step(
    id: &str,
    surface: &str,
    canonical: &str,
    direction: EquivalenceDirection,
    output: &mut Vec<String>,
) -> bool {
    for (surface_op, canonical_op) in [(">=", "<="), ("<=", ">="), (">", "<"), ("<", ">")] {
        let (Some(surface_args), Some(canonical_args)) = (
            split_application(surface, surface_op),
            split_application(canonical, canonical_op),
        ) else {
            continue;
        };
        if matches!(
            (surface_args.as_slice(), canonical_args.as_slice()),
            ([surface_left, surface_right], [canonical_left, canonical_right])
                if surface_left == canonical_right && surface_right == canonical_left
        ) {
            let equality = oriented_equivalence(surface, canonical, direction);
            if matches!((surface_op, canonical_op), (">", "<") | ("<", ">")) {
                let (greater_left, greater_right) = if surface_op == ">" {
                    (&surface_args[0], &surface_args[1])
                } else {
                    (&canonical_args[0], &canonical_args[1])
                };
                if greater_left == greater_right
                    && comp_simplify_evaluation::comp_simplify_reorders_self_comparison(
                        greater_left,
                    )
                {
                    let first = match direction {
                        EquivalenceDirection::SurfaceToCanonical => surface,
                        EquivalenceDirection::CanonicalToSurface => canonical,
                    };
                    let greater_first = first.starts_with("(>");
                    output.extend(strict_self_comparison_reversal(
                        id,
                        greater_left,
                        greater_first,
                        &equality,
                    ));
                    return true;
                }
                // Pinned carcara's `comp_simplify` EVALUATES `(< c d)` over two
                // numeric constants (and rewrites `(< t t)` to `false`) instead
                // of rewriting it to `(not (<= d c))`, so the `(< ..)` leg below
                // would not check. A `forall_inst` instance such as `(> 3 3)`
                // reaches this helper unsimplified.
                if comp_simplify_evaluation::comp_simplify_evaluates_less_than(
                    greater_right,
                    greater_left,
                ) {
                    return false;
                }
                let intermediate = format!("(not (<= {greater_left} {greater_right}))");
                let (first, second) = match direction {
                    EquivalenceDirection::SurfaceToCanonical => (surface, canonical),
                    EquivalenceDirection::CanonicalToSurface => (canonical, surface),
                };
                output.push(format!(
                    "(step {id}.s0 (cl (= {first} {intermediate})) :rule comp_simplify)"
                ));
                output.push(format!(
                    "(step {id}.s1 (cl (= {intermediate} {second})) :rule comp_simplify)"
                ));
                output.push(format!(
                    "(step {id} (cl {equality}) :rule trans :premises ({id}.s0 {id}.s1))"
                ));
            } else {
                output.push(format!("(step {id} (cl {equality}) :rule comp_simplify)"));
            }
            return true;
        }
    }
    false
}

/// `(> t t)` and `(< t t)` are both `false`, and pinned carcara's
/// `comp_simplify` folds a self comparison before it reorders one: MEASURED
/// on carcara 1.1.0 (git 9a352ee), the reordering chain's
/// `(= (not (<= x x)) (< x x)) :rule comp_simplify` fails ("simplifying
/// '(not (<= x x))' resulted in '(not (<= x x))', expected result to be
/// '(< x x)'"), while AY's own checker accepted it. So the pair meets at
/// `false` instead: `(> t t)` through `(not (<= t t))` and `(not true)`, and
/// `(< t t)` by one `comp_simplify`; the chain below checks `valid` in both
/// orientations. `greater_first` says the equality's first operand is the
/// `>` side.
fn strict_self_comparison_reversal(
    id: &str,
    operand: &str,
    greater_first: bool,
    equality: &str,
) -> Vec<String> {
    let greater = format!("(> {operand} {operand})");
    let less = format!("(< {operand} {operand})");
    let weak = format!("(<= {operand} {operand})");
    let mut steps = vec![
        format!("(step {id}.g0 (cl (= {greater} (not {weak}))) :rule comp_simplify)"),
        format!("(step {id}.g1 (cl (= {weak} true)) :rule comp_simplify)"),
        format!("(step {id}.g2 (cl (= (not {weak}) (not true))) :rule cong :premises ({id}.g1))"),
        format!("(step {id}.g3 (cl (= (not true) false)) :rule not_simplify)"),
        format!(
            "(step {id}.g4 (cl (= {greater} false)) :rule trans :premises ({id}.g0 {id}.g2 {id}.g3))"
        ),
        format!("(step {id}.l0 (cl (= {less} false)) :rule comp_simplify)"),
    ];
    if greater_first {
        steps.push(format!(
            "(step {id}.l1 (cl (= false {less})) :rule symm :premises ({id}.l0))"
        ));
        steps.push(format!(
            "(step {id} (cl {equality}) :rule trans :premises ({id}.g4 {id}.l1))"
        ));
    } else {
        steps.push(format!(
            "(step {id}.g5 (cl (= false {greater})) :rule symm :premises ({id}.g4))"
        ));
        steps.push(format!(
            "(step {id} (cl {equality}) :rule trans :premises ({id}.l0 {id}.g5))"
        ));
    }
    steps
}

fn multiplication_commutation_step(
    id: &str,
    surface: &str,
    canonical: &str,
    direction: EquivalenceDirection,
    output: &mut Vec<String>,
) -> bool {
    let surface_mul = split_application(surface, "*");
    let canonical_mul = split_application(canonical, "*");
    if !matches!(
        (surface_mul.as_deref(), canonical_mul.as_deref()),
        (Some([surface_left, surface_right]), Some([canonical_left, canonical_right]))
            if surface_left == canonical_right && surface_right == canonical_left
    ) {
        return false;
    }
    let (left, right) = match direction {
        EquivalenceDirection::SurfaceToCanonical => (surface, canonical),
        EquivalenceDirection::CanonicalToSurface => (canonical, surface),
    };
    let Some(step) = crate::alethe_printer::aci_simp_step::ac_identity_step(id, left, right) else {
        return false;
    };
    output.push(step);
    true
}

#[path = "additive_identity.rs"]
mod additive_identity;
#[path = "comp_simplify_evaluation.rs"]
mod comp_simplify_evaluation;
#[cfg(test)]
#[path = "comparison_reversal_tests.rs"]
mod comparison_reversal_tests;
