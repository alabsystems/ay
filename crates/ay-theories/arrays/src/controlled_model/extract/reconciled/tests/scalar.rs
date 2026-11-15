// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

mod refusals;
mod resources;
mod semantics;

struct Pinned {
    terms: TermStore,
    base: TermId,
    alias: TermId,
    chain: TermId,
    constant: TermId,
    indices: [TermId; 2],
    value: TermId,
    constant_read: TermId,
    reads: [TermId; 2],
    defaults: [TermId; 2],
    roots: [TermId; 6],
    spelling: &'static str,
}

impl Pinned {
    fn new(element: Sort) -> Self {
        let mut terms = TermStore::new();
        let index = Sort::bitvec(64);
        let sort = Sort::array(index.clone(), element.clone());
        let base = terms.mk_var("scalar-base", sort.clone());
        let alias = terms.mk_var("scalar-alias", sort.clone());
        let indices = ["scalar-i", "scalar-j"].map(|n| terms.mk_var(n, index.clone()));
        let (value, spelling) = match &element {
            Sort::Bool => (terms.mk_bool(true), "true"),
            Sort::BitVec(bits) => (terms.mk_bitvec(9u8.into(), bits.width), "9"),
            _ => unreachable!("fixed source fixture domain"),
        };
        let chain = store(&mut terms, base, indices[0], value, &sort);
        let constant = terms.mk_const_array(index, value);
        let constant_read = read(&mut terms, constant, indices[1], &element);
        let reads = [base, alias].map(|a| read(&mut terms, a, indices[1], &element));
        let defaults = [base, alias].map(|a| terms.mk_array_default(a));
        // Raw named equalities retain even Boolean pins as actual equality atoms.
        let roots = [
            (alias, chain),
            (reads[0], value),
            (reads[1], value),
            (defaults[0], value),
            (defaults[1], value),
            (constant_read, value),
        ]
        .map(|(a, b)| terms.mk_app(Symbol::named("="), [a, b], Sort::Bool));
        Self {
            terms,
            base,
            alias,
            chain,
            constant,
            indices,
            value,
            constant_read,
            reads,
            defaults,
            roots,
            spelling,
        }
    }

    fn solver(&self) -> ArraySolver<'_> {
        let mut source = ArraySolver::new(&self.terms);
        for &root in &self.roots {
            source.register_atom(root);
            source.assert_literal(root, true);
        }
        source.populate_caches();
        source.rebuild_assign_indices();
        assert!(!source.dirty && !source.assign_dirty && !source.shadow_uf_stale);
        assert!(self
            .reads
            .iter()
            .chain(&self.defaults)
            .all(|t| { !source.eq_adj.get(t).unwrap().is_empty() }));
        source
    }

    fn values(&self) -> HashMap<TermId, String> {
        let mut values = HashMap::default();
        for (&term, value) in self.indices.iter().zip(["0", "1"]) {
            values.insert(term, value.into());
        }
        for &term in self
            .reads
            .iter()
            .chain(&self.defaults)
            .chain([&self.value, &self.constant_read])
        {
            values.insert(term, self.spelling.into());
        }
        values
    }
}

fn refused(source: &ArraySolver<'_>, values: &HashMap<TermId, String>, end: Instant) {
    let original = owner(end, 1_000_000, 128 << 20);
    assert!(matches!(
        original
            .with_work(|work| { source.try_extract_prepared_flat_model_with_budget(values, work) }),
        Err(OriginalAdmissionError::Query(QueryError::Exhausted))
    ));
    assert_eq!(
        original.clone().check(),
        Err(OriginalAdmissionError::Query(QueryError::Exhausted))
    );
}
