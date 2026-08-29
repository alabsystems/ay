// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Recursive checked equivalence rendering for authored assumption spellings.

use super::*;

impl AlethePrinter<'_> {
    /// Emit a checked equality between `surface` and the identity rendering of
    /// `canonical_term`. Recursion follows the canonical term DAG and admits
    /// only the selected leaf schema below same-head congruence.
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
    ) -> bool {
        if depth > MAX_EQUIVALENCE_DEPTH || *nodes >= MAX_EQUIVALENCE_NODES {
            return false;
        }
        *nodes += 1;
        let canonical = crate::render_term_canonical(self.terms, canonical_term);
        if surface == canonical {
            return false;
        }

        if matches!(schema, EquivalenceLeafSchema::AuthoredAssume)
            && comparison_reversal_step(id, surface, &canonical, direction, output)
        {
            return true;
        }
        if matches!(self.terms.sort(canonical_term), Sort::Int | Sort::Real)
            && multiplication_commutation_step(id, surface, &canonical, direction, output)
        {
            return true;
        }

        let TermData::App(symbol, canonical_children) = self.terms.get(canonical_term) else {
            return false;
        };
        let operator = Self::format_symbol(symbol);
        let (Some(surface_args), Some(canonical_args)) = (
            split_application(surface, &operator),
            split_application(&canonical, &operator),
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
            if surface_arg == canonical_arg {
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
            ) {
                return false;
            }
            premises.push(child_id);
        }
        if premises.is_empty() {
            return false;
        }
        let equality = oriented_equivalence(surface, &canonical, direction);
        output.push(format!(
            "(step {id} (cl {equality}) :rule cong :premises ({}))",
            premises.join(" ")
        ));
        true
    }

    /// Prove only position-preserving congruence over exact binary numeric
    /// multiplication commutations. Comparison reversal and addition
    /// permutation remain outside this use-site schema.
    pub(in crate::alethe_printer) fn format_nested_multiplication_surface_equivalence(
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
            EquivalenceLeafSchema::MultiplicationOnly,
            direction,
            0,
            &mut nodes,
            &mut output,
        )
        .then_some(output)
    }
}

fn comparison_reversal_step(
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
    let equality = oriented_equivalence(surface, canonical, direction);
    output.push(format!("(step {id} (cl {equality}) :rule aci_simp)"));
    true
}
