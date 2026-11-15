// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! A bounded, lossless canonical projection for definition bridges.
//!
//! The ordinary preflight prices a freshly rendered tree at each recursive
//! bridge call. A nullary macro can repeat the same large array many times.
//! Here one canonical buffer and a term/child span DAG replace those repeated
//! renderings and owned argument copies. This is representation only: every
//! equality is still derived by the existing definition/congruence rules.

use super::*;
use std::cell::Cell;
use std::mem::size_of;
use std::ops::{Deref, Range};

struct Node {
    term: TermId,
    span: Range<usize>,
    first_child: u16,
    child_count: u16,
}

#[derive(Clone)]
struct Edge {
    node: usize,
    span: Range<usize>,
}

#[derive(Clone, Copy)]
struct Measure {
    bytes: usize,
    occurrences: usize,
    depth: usize,
}

pub(super) struct CanonicalDag<'t> {
    terms: &'t ay_core::TermStore,
    nodes: Vec<Node>,
    edges: Vec<Edge>,
    root: usize,
    text_bytes: usize,
    temporary_bytes: usize,
}

impl<'t> CanonicalDag<'t> {
    fn allocation_bytes(&self) -> Option<usize> {
        self.nodes
            .capacity()
            .checked_mul(size_of::<Node>())?
            .checked_add(self.edges.capacity().checked_mul(size_of::<Edge>())?)
    }

    fn fits(&self, text_capacity: usize, source_bytes: usize) -> bool {
        self.allocation_bytes()
            .and_then(|n| n.checked_add(text_capacity))
            .and_then(|n| n.checked_add(source_bytes))
            .and_then(|n| n.checked_add(self.temporary_bytes))
            .is_some_and(|n| n <= MAX_EQUIVALENCE_BYTES)
    }

    /// All metadata, including vector capacities and the construction-only
    /// measurements, is bounded. No source term, policy or proof is changed.
    pub(super) fn plan(
        printer: &AlethePrinter<'t>,
        root: TermId,
        source_bytes: usize,
    ) -> Option<Self> {
        let mut dag = Self {
            terms: printer.terms,
            nodes: Vec::new(),
            edges: Vec::new(),
            root: 0,
            text_bytes: 0,
            temporary_bytes: 0,
        };
        let mut measures = Vec::new();
        let index = dag.visit(printer, root, 0, source_bytes, &mut measures)?;
        let measure = measures.get(index)?.as_ref()?;
        dag.root = index;
        dag.text_bytes = measure.bytes;
        drop(measures);
        if !printer.admit_emission_work(dag.allocation_bytes()?.checked_mul(2)? as u64) {
            return None;
        }
        // Freeze the compact DAG before allocating its canonical buffer. The
        // final cap uses actual capacities even if an allocator keeps slack.
        dag.nodes.shrink_to_fit();
        dag.edges.shrink_to_fit();
        dag.fits(dag.text_bytes, source_bytes).then_some(dag)
    }

    fn construction_fits(&self, measures: &Vec<Option<Measure>>, source_bytes: usize) -> bool {
        measures
            .capacity()
            .checked_mul(size_of::<Option<Measure>>())
            .and_then(|n| self.allocation_bytes()?.checked_add(n))
            .and_then(|n| n.checked_add(source_bytes))
            .and_then(|n| n.checked_add(self.temporary_bytes))
            .is_some_and(|n| n <= MAX_EQUIVALENCE_BYTES)
    }

    fn visit(
        &mut self,
        printer: &AlethePrinter<'_>,
        term: TermId,
        depth: usize,
        source_bytes: usize,
        measures: &mut Vec<Option<Measure>>,
    ) -> Option<usize> {
        if depth > MAX_EQUIVALENCE_DEPTH {
            return None;
        }
        for (index, node) in self.nodes.iter().enumerate() {
            if !printer.admit_emission_work(1) {
                return None;
            }
            if node.term == term {
                // A half-built entry is a cycle, never reusable authority.
                measures.get(index)?.as_ref()?;
                return Some(index);
            }
        }
        if self.nodes.len() >= MAX_CANONICAL_RENDER_NODES {
            return None;
        }
        let local;
        let children = match printer.terms.get(term) {
            TermData::App(symbol, children) => {
                let mut payload = 0;
                if !bounds::canonical_symbol_payload_bound(symbol, &mut payload).is_bounded()
                    || !printer.admit_emission_work(payload as u64)
                {
                    return None;
                }
                children.as_slice()
            }
            TermData::Not(child) => std::slice::from_ref(child),
            TermData::Ite(a, b, c) => {
                local = [*a, *b, *c];
                &local
            }
            TermData::Var(name, _) => {
                if name.len().checked_mul(4)? > MAX_EQUIVALENCE_BYTES
                    || !printer.admit_emission_work(name.len() as u64 * 4 + 32)
                {
                    return None;
                }
                &[]
            }
            TermData::Const(constant) => {
                let mut payload = 0;
                if !bounds::canonical_constant_payload_is_bounded(constant, &mut payload)
                    || !printer.admit_emission_work(payload as u64 + 32)
                {
                    return None;
                }
                &[]
            }
            // No binder/let/constant-array quiet lane is added. The ordinary
            // preflight still decides size-before-shape for those schemas.
            _ => return None,
        };
        let first_child = u16::try_from(self.edges.len()).ok()?;
        let child_count = u16::try_from(children.len()).ok()?;
        let edge_end = self.edges.len().checked_add(children.len())?;
        if edge_end > MAX_CANONICAL_RENDER_NODES {
            return None;
        }
        // Initialize each new node/edge once. Allocation/copy work is charged
        // only when a vector actually grows, rather than re-pricing the whole
        // retained DAG at every newly visited term.
        let old_capacities = [
            self.nodes.capacity(),
            self.edges.capacity(),
            measures.capacity(),
        ];
        let sizes = [
            size_of::<Node>(),
            size_of::<Edge>(),
            size_of::<Option<Measure>>(),
        ];
        let initialize = sizes[0]
            .checked_add(sizes[2])?
            .checked_add(children.len().checked_mul(sizes[1])?)?;
        if !printer.admit_emission_work(initialize as u64) {
            return None;
        }
        self.nodes.try_reserve(1).ok()?;
        self.edges.try_reserve(children.len()).ok()?;
        measures.try_reserve(1).ok()?;
        let new_capacities = [
            self.nodes.capacity(),
            self.edges.capacity(),
            measures.capacity(),
        ];
        let mut growth = 0usize;
        for ((old, new), size) in old_capacities.into_iter().zip(new_capacities).zip(sizes) {
            if old != new {
                growth = growth.checked_add(old.checked_add(new)?.checked_mul(size)?)?;
            }
        }
        if !printer.admit_emission_work(growth as u64) {
            return None;
        }
        let index = self.nodes.len();
        self.nodes.push(Node {
            term,
            span: 0..0,
            first_child,
            child_count,
        });
        measures.push(None);
        self.edges.resize(
            edge_end,
            Edge {
                node: 0,
                span: 0..0,
            },
        );
        if !self.construction_fits(measures, source_bytes) {
            return None;
        }

        let own = own_spelling(printer, term)?;
        self.temporary_bytes = self.temporary_bytes.max(own.capacity().checked_mul(2)?);
        if !self.construction_fits(measures, source_bytes) {
            return None;
        }
        let mut measure = Measure {
            bytes: own.len(),
            occurrences: 1,
            depth: 0,
        };
        drop(own);
        for (position, &child) in children.iter().enumerate() {
            let child_index = self.visit(printer, child, depth + 1, source_bytes, measures)?;
            self.edges[usize::from(first_child) + position].node = child_index;
            let child_measure = measures.get(child_index)?.as_ref()?;
            measure.bytes = measure.bytes.checked_add(child_measure.bytes)?;
            measure.occurrences = measure.occurrences.checked_add(child_measure.occurrences)?;
            measure.depth = measure.depth.max(child_measure.depth.checked_add(1)?);
            if measure.bytes > MAX_EQUIVALENCE_BYTES
                || measure.occurrences > MAX_CANONICAL_RENDER_NODES
                || measure.depth > MAX_EQUIVALENCE_DEPTH
            {
                return None;
            }
        }
        measures[index] = Some(measure);
        Some(index)
    }

    pub(super) fn render(
        &mut self,
        printer: &AlethePrinter<'_>,
        source_bytes: usize,
    ) -> Option<String> {
        if !std::ptr::eq(self.terms, printer.terms) {
            return None;
        }
        let mut text = String::new();
        text.try_reserve_exact(self.text_bytes).ok()?;
        if !self.fits(text.capacity(), source_bytes) {
            return None;
        }
        self.write_node(printer, self.root, &mut text)?;
        (text.len() == self.text_bytes && !printer.work_budget_exhausted()).then_some(text)
    }

    fn write_node(
        &mut self,
        printer: &AlethePrinter<'_>,
        index: usize,
        text: &mut String,
    ) -> Option<()> {
        let start = text.len();
        let first = self.nodes.get(index)?.span.end == 0;
        let term = self.nodes[index].term;
        let first_child = usize::from(self.nodes[index].first_child);
        let count = usize::from(self.nodes[index].child_count);
        let own = own_spelling(printer, term)?;
        if !printer.admit_emission_work(own.len() as u64 + 1) {
            return None;
        }
        if count == 0 {
            text.push_str(&own);
        } else {
            let head_end = own.len().checked_sub(count.checked_add(1)?)?;
            text.push('(');
            text.push_str(own.get(1..head_end)?);
            drop(own);
            for position in 0..count {
                text.push(' ');
                let child_start = text.len();
                let edge = first_child + position;
                self.write_node(printer, self.edges[edge].node, text)?;
                if first {
                    self.edges[edge].span = child_start..text.len();
                }
            }
            text.push(')');
        }
        if text.len() > self.text_bytes {
            return None;
        }
        if first {
            self.nodes[index].span = start..text.len();
        }
        Some(())
    }

    /// Bind a borrowed existing canonical buffer by replaying the SAME bounded
    /// rendering into exact byte comparisons. No TermId-only spelling claim.
    pub(super) fn bind(
        &mut self,
        printer: &AlethePrinter<'_>,
        text: &str,
        source_bytes: usize,
    ) -> bool {
        if !std::ptr::eq(self.terms, printer.terms)
            || text.len() != self.text_bytes
            || !self.fits(text.len(), source_bytes)
        {
            return false;
        }
        let mut cursor = 0;
        self.bind_node(printer, self.root, text, &mut cursor)
            .is_some()
            && cursor == text.len()
            && !printer.work_budget_exhausted()
    }

    fn bind_node(
        &mut self,
        printer: &AlethePrinter<'_>,
        index: usize,
        text: &str,
        cursor: &mut usize,
    ) -> Option<()> {
        let start = *cursor;
        let first = self.nodes.get(index)?.span.end == 0;
        let term = self.nodes[index].term;
        let begin = usize::from(self.nodes[index].first_child);
        let count = usize::from(self.nodes[index].child_count);
        let own = own_spelling(printer, term)?;
        if !printer.admit_emission_work(own.len() as u64 + 1) {
            return None;
        }
        let mut consume = |part: &str| {
            let end = cursor.checked_add(part.len())?;
            if text.get(*cursor..end)? != part {
                return None;
            }
            *cursor = end;
            Some(())
        };
        if count == 0 {
            consume(&own)?;
        } else {
            let head_end = own.len().checked_sub(count.checked_add(1)?)?;
            consume("(")?;
            consume(own.get(1..head_end)?)?;
            drop(consume);
            drop(own);
            for position in 0..count {
                if text.as_bytes().get(*cursor) != Some(&b' ') {
                    return None;
                }
                *cursor += 1;
                let child_start = *cursor;
                let edge = begin + position;
                self.bind_node(printer, self.edges[edge].node, text, cursor)?;
                if first {
                    self.edges[edge].span = child_start..*cursor;
                }
            }
            if text.as_bytes().get(*cursor) != Some(&b')') {
                return None;
            }
            *cursor += 1;
        }
        if first {
            self.nodes[index].span = start..*cursor;
        }
        Some(())
    }

    pub(super) fn lookup_work(&self) -> usize {
        self.nodes.len()
    }

    pub(super) fn text<'a>(&self, text: &'a str, term: TermId) -> Option<&'a str> {
        text.get(
            self.nodes
                .iter()
                .find(|node| node.term == term)?
                .span
                .clone(),
        )
    }

    pub(super) fn children<'a>(
        &'a self,
        term: TermId,
    ) -> Option<impl Iterator<Item = (TermId, Range<usize>)> + 'a> {
        let node = self.nodes.iter().find(|node| node.term == term)?;
        let begin = usize::from(node.first_child);
        let end = begin.checked_add(usize::from(node.child_count))?;
        Some(
            self.edges
                .get(begin..end)?
                .iter()
                .map(|edge| (self.nodes[edge.node].term, edge.span.clone())),
        )
    }
}

/// Only the existing canonical spelling helpers define the token text. The
/// string for an application contains its head and empty argument separators,
/// so its length is exactly the bytes that node itself contributes.
fn own_spelling(printer: &AlethePrinter<'_>, term: TermId) -> Option<String> {
    Some(match printer.terms.get(term) {
        TermData::Var(name, _) => super::super::quote_symbol(name),
        TermData::Const(constant) => AlethePrinter::format_constant(constant),
        TermData::App(symbol, children) => {
            let head = AlethePrinter::application_spelling_head(symbol, children.len());
            if children.is_empty() {
                head
            } else {
                let mut own = String::new();
                own.try_reserve_exact(head.len().checked_add(children.len())?.checked_add(2)?)
                    .ok()?;
                own.push('(');
                own.push_str(&head);
                for _ in children {
                    own.push(' ');
                }
                own.push(')');
                own
            }
        }
        TermData::Not(_) => "(not )".to_string(),
        TermData::Ite(..) => "(ite   )".to_string(),
        _ => return None,
    })
}

pub(super) struct SharedInput<'a> {
    pub(super) dag: &'a CanonicalDag<'a>,
    pub(super) canonical: &'a str,
    baseline: usize,
    argument_bytes: Cell<usize>,
}

impl<'a> SharedInput<'a> {
    pub(super) fn new(
        dag: &'a CanonicalDag<'a>,
        canonical: &'a str,
        source_bytes: usize,
    ) -> Option<Self> {
        let baseline = dag
            .allocation_bytes()?
            .checked_add(canonical.len())?
            .checked_add(source_bytes)?
            .checked_add(dag.temporary_bytes)?;
        (baseline <= MAX_EQUIVALENCE_BYTES).then_some(Self {
            dag,
            canonical,
            baseline,
            argument_bytes: Cell::new(0),
        })
    }

    pub(super) fn arguments<'b>(
        &'b self,
        printer: &AlethePrinter<'_>,
        text: &'b str,
        head: &str,
        arity: usize,
    ) -> Option<Arguments<'b>> {
        if !printer.admit_emission_work(text.len() as u64 + head.len() as u64) {
            return None;
        }
        if arity > MAX_CANONICAL_RENDER_NODES {
            return None;
        }
        let values = super::super::split_alethe_application_bounded(
            text,
            head,
            arity,
            MAX_EQUIVALENCE_BYTES,
        )
        .ok()?;
        let bytes = values.capacity().checked_mul(size_of::<&str>())?;
        let next = self.argument_bytes.get().checked_add(bytes)?;
        if self.baseline.checked_add(next)? > MAX_EQUIVALENCE_BYTES {
            if ay_core::misc_cli_flags().probe_cert_reject {
                eprintln!("--probe-cert-reject: shared authored argument capacity refused baseline={} live_arguments={} requested_arguments={} bound={MAX_EQUIVALENCE_BYTES}", self.baseline, self.argument_bytes.get(), bytes);
            }
            return None;
        }
        self.argument_bytes.set(next);
        Some(Arguments {
            values,
            charged: bytes,
            owner: &self.argument_bytes,
        })
    }
}

pub(super) struct Arguments<'a> {
    values: Vec<&'a str>,
    charged: usize,
    owner: &'a Cell<usize>,
}

impl<'a> Deref for Arguments<'a> {
    type Target = [&'a str];
    fn deref(&self) -> &Self::Target {
        &self.values
    }
}

impl Drop for Arguments<'_> {
    fn drop(&mut self) {
        // Only successful, scoped reservations construct this private type.
        self.owner.set(
            self.owner
                .get()
                .checked_sub(self.charged)
                .unwrap_or(MAX_EQUIVALENCE_BYTES),
        );
    }
}

impl AlethePrinter<'_> {
    pub(super) fn shared_definition_canonical(
        &self,
        term: TermId,
        surface: &str,
    ) -> Option<String> {
        if self.nullary_definitions.is_none_or(HashMap::is_empty) {
            return None;
        }
        CanonicalDag::plan(self, term, surface.len())?.render(self, surface.len())
    }

    pub(super) fn shared_definition_bridge(
        &self,
        id: &str,
        surface: &str,
        term: TermId,
        canonical: Option<&str>,
        nodes: &mut usize,
        output: &mut Vec<String>,
    ) -> bool {
        if self.nullary_definitions.is_none_or(HashMap::is_empty) {
            return false;
        }
        let Some(mut dag) = CanonicalDag::plan(self, term, surface.len()) else {
            return false;
        };
        let owned;
        let text = if let Some(text) = canonical {
            if !dag.bind(self, text, surface.len()) {
                return false;
            }
            text
        } else {
            let Some(text) = dag.render(self, surface.len()) else {
                return false;
            };
            owned = text;
            &owned
        };
        let Some(shared) = SharedInput::new(&dag, text, surface.len()) else {
            return false;
        };
        if ay_core::misc_cli_flags().probe_cert_reject {
            eprintln!("--probe-cert-reject: authored shared canonical root={term} canonical_bytes={} source_bytes={} unique_nodes={} child_edges={} retained_metadata_bytes={} input_baseline_bytes={}", text.len(), surface.len(), dag.nodes.len(), dag.edges.len(), dag.allocation_bytes().unwrap_or(usize::MAX), shared.baseline);
        }
        output.clear();
        let mut attempt = 0;
        let bridged = self.build_authored_surface_equivalence(
            id,
            surface,
            term,
            EquivalenceLeafSchema::NullaryDefinition,
            EquivalenceDirection::SurfaceToCanonical,
            0,
            &mut attempt,
            output,
            Some(&shared),
        );
        *nodes = nodes.saturating_add(attempt);
        bridged
            && !self.work_budget_exhausted()
            && output.iter().any(|line| line.starts_with("(assume "))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use ay_core::{Symbol, TermStore};

    #[test]
    fn canonical_projection_replays_exact_spelling_and_child_spans() {
        let mut terms = TermStore::new();
        let x = terms.mk_var("x quoted λ", Sort::bitvec(64));
        let p = terms.mk_var("p", Sort::Bool);
        let byte = terms.mk_app(Symbol::indexed("extract", vec![7, 0]), [x], Sort::bitvec(8));
        let v = terms.mk_bitvec(7.into(), 8);
        let eq = terms.mk_app(Symbol::named("="), [byte, v], Sort::Bool);
        let neg = terms.mk_not_raw(eq);
        let choice = terms.mk_ite(p, eq, neg);
        let tester = terms.mk_app(Symbol::named("is-C quoted"), [x], Sort::Bool);
        let root = terms.mk_app(Symbol::named("and"), [choice, choice, tester], Sort::Bool);
        let printer = AlethePrinter::new(&terms);
        let expected = crate::render_term_canonical(&terms, root);
        let mut dag = CanonicalDag::plan(&printer, root, 0).unwrap();
        let rendered = dag.render(&printer, 0).unwrap();
        assert_eq!(rendered, expected);
        assert!(dag.nodes.len() < 20);
        for node in &dag.nodes {
            assert_eq!(
                dag.text(&rendered, node.term).unwrap(),
                crate::render_term_canonical(&terms, node.term)
            );
            for (child, span) in dag.children(node.term).unwrap() {
                assert_eq!(&rendered[span], crate::render_term_canonical(&terms, child));
            }
        }
        let mut rebound = CanonicalDag::plan(&printer, root, 0).unwrap();
        assert!(rebound.bind(&printer, &expected, 0));
        let wrong = expected.replacen("#b00000111", "#b00000110", 1);
        assert_ne!(wrong, expected);
        assert!(!CanonicalDag::plan(&printer, root, 0)
            .unwrap()
            .bind(&printer, &wrong, 0));
    }

    #[test]
    fn canonical_projection_keeps_expanded_nodes_depth_and_actual_metadata_bounds() {
        let mut terms = TermStore::new();
        let p = terms.mk_var("p", Sort::Bool);
        let wide = terms.mk_app(Symbol::named("or"), vec![p; 4096], Sort::Bool);
        assert!(CanonicalDag::plan(&AlethePrinter::new(&terms), wide, 0).is_none());
        let mut deep = p;
        for _ in 0..64 {
            deep = terms.mk_app(Symbol::named("g"), [deep], Sort::Bool);
        }
        assert!(CanonicalDag::plan(&AlethePrinter::new(&terms), deep, 0).is_some());
        deep = terms.mk_app(Symbol::named("g"), [deep], Sort::Bool);
        assert!(CanonicalDag::plan(&AlethePrinter::new(&terms), deep, 0).is_none());
        let mut repeated = p;
        for _ in 0..12 {
            repeated = terms.mk_app(Symbol::named("f"), [repeated, repeated], Sort::Bool);
        }
        assert!(
            CanonicalDag::plan(&AlethePrinter::new(&terms), repeated, 0).is_some(),
            "8191 expanded occurrences fit"
        );
        repeated = terms.mk_app(Symbol::named("f"), [repeated, repeated], Sort::Bool);
        assert!(
            CanonicalDag::plan(&AlethePrinter::new(&terms), repeated, 0).is_none(),
            "16383 occurrences still refuse although text alone fits"
        );
        let binder = terms.mk_forall(vec![("p".to_string(), Sort::Bool)], p);
        assert!(CanonicalDag::plan(&AlethePrinter::new(&terms), binder, 0).is_none());
    }

    #[test]
    fn canonical_projection_preserves_work_refusal_and_active_argument_capacity() {
        let mut terms = TermStore::new();
        let p = terms.mk_var("p", Sort::Bool);
        let root = terms.mk_app(Symbol::named("f"), [p, p], Sort::Bool);
        let stopped = AlethePrinter::new_with_overrides_and_budget(&terms, None, Some(0));
        assert!(CanonicalDag::plan(&stopped, root, 0).is_none());
        let printer = AlethePrinter::new(&terms);
        let mut dag = CanonicalDag::plan(&printer, root, 0).unwrap();
        let text = dag.render(&printer, 0).unwrap();
        let mut foreign_terms = TermStore::new();
        let foreign_p = foreign_terms.mk_var("p", Sort::Bool);
        let foreign_root =
            foreign_terms.mk_app(Symbol::named("f"), [foreign_p, foreign_p], Sort::Bool);
        assert_eq!(
            crate::render_term_canonical(&foreign_terms, foreign_root),
            text
        );
        let foreign = AlethePrinter::new(&foreign_terms);
        assert!(
            dag.render(&foreign, 0).is_none(),
            "identical spelling does not change the owning immutable arena"
        );
        assert!(!dag.bind(&foreign, &text, 0));
        let input = SharedInput::new(&dag, &text, 0).unwrap();
        assert!(input.arguments(&printer, "(f p p p)", "f", 2).is_none());
        let lease = input.arguments(&printer, "(f p p)", "f", 2).unwrap();
        assert!(input.argument_bytes.get() >= 2 * size_of::<&str>());
        drop(lease);
        assert_eq!(input.argument_bytes.get(), 0);
        input.argument_bytes.set(MAX_EQUIVALENCE_BYTES);
        assert!(input.arguments(&printer, "(f p p)", "f", 2).is_none());
    }
}
