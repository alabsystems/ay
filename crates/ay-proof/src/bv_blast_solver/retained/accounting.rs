// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

pub(super) struct Control<'a> {
    pub(super) limits: &'a BvExprProofLimits,
    pub(super) work: u64,
    pub(super) bytes: usize,
}

#[derive(Default, Clone, Copy)]
pub(super) struct Shape {
    pub(super) rows: usize,
    pub(super) literals: usize,
    pub(super) hints: usize,
}

pub(super) fn add(a: usize, b: usize) -> Result<usize, BvExprExportError> {
    a.checked_add(b)
        .ok_or_else(|| malformed("retained refutation size overflow"))
}

pub(super) fn product(a: usize, b: usize) -> Result<usize, BvExprExportError> {
    a.checked_mul(b)
        .ok_or_else(|| malformed("retained refutation size overflow"))
}

pub(super) fn cap(
    name: &'static str,
    actual: usize,
    limit: usize,
) -> Result<(), BvExprExportError> {
    if actual > limit {
        Err(BvExprExportError::ResourceLimit {
            resource: name,
            limit,
            actual,
        })
    } else {
        Ok(())
    }
}

impl Shape {
    fn row(
        &mut self,
        literals: usize,
        hints: usize,
        control: &mut Control<'_>,
        poll: &mut dyn FnMut() -> bool,
    ) -> Result<(), BvExprExportError> {
        control.charge(1, poll)?;
        self.rows = add(self.rows, 1)?;
        self.literals = add(self.literals, literals)?;
        self.hints = add(self.hints, hints)?;
        let limits = &control.limits.resolution;
        cap(
            "retained rows",
            self.rows,
            limits
                .max_derived_steps
                .min(limits.validation.max_derived_steps),
        )?;
        cap(
            "retained literals",
            self.literals,
            limits
                .max_derived_literals
                .min(limits.validation.max_derived_literals),
        )?;
        cap(
            "retained hints",
            self.hints,
            limits.max_hints.min(limits.validation.max_hints),
        )?;
        // Version + terminal + row count, then IDs/lengths and packed fields.
        // Logical fixed-width fields only: NOT a bound on serde JSON bytes.
        let fields = add(
            20,
            add(
                product(self.rows, 24)?,
                add(product(self.literals, 4)?, product(self.hints, 8)?)?,
            )?,
        )?;
        cap(
            "retained encoded fields",
            fields,
            limits.max_proof_output_bytes,
        )
    }
}

impl<'a> Control<'a> {
    pub(super) fn new(limits: &'a BvExprProofLimits) -> Self {
        Self {
            limits,
            work: 0,
            bytes: 0,
        }
    }

    pub(super) fn charge(
        &mut self,
        amount: usize,
        poll: &mut dyn FnMut() -> bool,
    ) -> Result<(), BvExprExportError> {
        let amount = u64::try_from(amount).map_err(|_| malformed("retained work overflow"))?;
        self.work = self
            .work
            .checked_add(amount)
            .ok_or_else(|| malformed("retained work overflow"))?;
        let limit = self.limits.resolution.validation.max_work;
        if self.work > limit {
            return Err(BvExprExportError::ResourceLimit {
                resource: "retained transport work",
                limit: bounded_amount(limit.into()),
                actual: bounded_amount(self.work.into()),
            });
        }
        finish_expr_export(Some(self.limits), poll)
    }

    pub(super) fn retain(&mut self, amount: usize) -> Result<(), BvExprExportError> {
        self.bytes = add(self.bytes, amount)?;
        cap(
            "retained codec bytes",
            self.bytes,
            self.limits.resolution.max_codec_bytes,
        )
    }

    pub(super) fn remaining_bytes(&self, extra: usize) -> Result<usize, BvExprExportError> {
        let used = add(self.bytes, extra)?;
        cap(
            "retained codec bytes",
            used,
            self.limits.resolution.max_codec_bytes,
        )?;
        Ok(self.limits.resolution.max_codec_bytes - used)
    }

    pub(super) fn reserve<T>(
        &mut self,
        count: usize,
        poll: &mut dyn FnMut() -> bool,
    ) -> Result<Vec<T>, BvExprExportError> {
        self.charge(1, poll)?;
        self.retain(product(count, size_of::<T>())?)?;
        let mut out = Vec::new();
        out.try_reserve_exact(count)
            .map_err(|_| BvExprExportError::ResourceLimit {
                resource: "retained allocation",
                limit: self.limits.resolution.max_codec_bytes,
                actual: self.bytes,
            })?;
        self.retain(product(out.capacity() - count, size_of::<T>())?)?;
        Ok(out)
    }

    pub(super) fn graph(
        &mut self,
        graph: &BvBlastProof,
        poll: &mut dyn FnMut() -> bool,
    ) -> Result<usize, BvExprExportError> {
        let before = self.bytes;
        self.charge(1, poll)?;
        self.retain(add(
            size_of::<BvBlastProof>(),
            graph.asserted_smt.capacity(),
        )?)?;
        self.retain(product(graph.vars.roles.capacity(), size_of::<VarRole>())?)?;
        self.retain(product(graph.bit_lemmas.capacity(), size_of::<BitLemma>())?)?;
        self.retain(product(graph.clauses.capacity(), size_of::<Clause>())?)?;
        self.retain(product(
            graph.refutation.steps.capacity(),
            size_of::<ResolutionStep>(),
        )?)?;
        for lemma in &graph.bit_lemmas {
            self.charge(1, poll)?;
            self.retain(product(lemma.ins.capacity(), size_of::<u32>())?)?;
        }
        for clause in &graph.clauses {
            self.charge(1, poll)?;
            self.retain(product(clause.lits.capacity(), size_of::<Lit>())?)?;
        }
        if !graph.refutation.steps.is_empty() {
            return Err(malformed(
                "retained source graph unexpectedly has an expanded proof",
            ));
        }
        Ok(self.bytes - before)
    }

    pub(super) fn dag(
        &mut self,
        dag: &ResolutionDag,
        poll: &mut dyn FnMut() -> bool,
    ) -> Result<Shape, BvExprExportError> {
        self.charge(1, poll)?;
        self.retain(size_of::<ResolutionDag>())?;
        self.retain(product(
            dag.original_clauses.capacity(),
            size_of::<(u64, Vec<Literal>)>(),
        )?)?;
        self.retain(product(dag.derived.capacity(), size_of::<RupStep>())?)?;
        for (_, clause) in &dag.original_clauses {
            self.charge(1, poll)?;
            self.retain(product(clause.capacity(), size_of::<Literal>())?)?;
        }
        let mut shape = Shape::default();
        for row in &dag.derived {
            shape.row(row.clause.len(), row.rup_hints.len(), self, poll)?;
            self.retain(product(row.clause.capacity(), size_of::<Literal>())?)?;
            self.retain(product(row.rup_hints.capacity(), size_of::<u64>())?)?;
        }
        Ok(shape)
    }

    pub(super) fn payload(
        &mut self,
        payload: &RetainedBvRefutation,
        poll: &mut dyn FnMut() -> bool,
    ) -> Result<Shape, BvExprExportError> {
        let mut shape = Shape::default();
        let mut previous = 0;
        for row in &payload.rows {
            shape.row(row.literals.len(), row.hints.len(), self, poll)?;
            if row.id <= previous {
                return Err(malformed("nonmonotone retained row ID"));
            }
            previous = row.id;
        }
        match payload.rows.last() {
            Some(last) if last.id == payload.empty_clause_id && last.literals.is_empty() => {}
            _ => return Err(malformed("missing or mismatched retained terminal row")),
        }
        let bytes = self.payload_bytes(payload, poll)?;
        self.retain(bytes)?;
        Ok(shape)
    }

    pub(super) fn payload_bytes(
        &mut self,
        payload: &RetainedBvRefutation,
        poll: &mut dyn FnMut() -> bool,
    ) -> Result<usize, BvExprExportError> {
        self.charge(1, poll)?;
        let mut bytes = add(
            size_of::<RetainedBvRefutation>(),
            product(payload.rows.capacity(), size_of::<RetainedRupRow>())?,
        )?;
        for row in &payload.rows {
            self.charge(1, poll)?;
            bytes = add(bytes, product(row.literals.capacity(), size_of::<u32>())?)?;
            bytes = add(bytes, product(row.hints.capacity(), size_of::<u64>())?)?;
        }
        Ok(bytes)
    }

    pub(super) fn replay_limits(
        &mut self,
        graph: &BvBlastProof,
        graph_bytes: usize,
        payload_bytes: usize,
        poll: &mut dyn FnMut() -> bool,
    ) -> Result<BvExprProofLimits, BvExprExportError> {
        // Reserve the exact compact binding visits and both final publication
        // polls before opaque replay. Destructors remain opaque intervals.
        let mut binding = add(3, graph.clauses.len())?;
        for clause in &graph.clauses {
            self.charge(1, poll)?;
            binding = add(binding, clause.lits.len())?;
        }
        self.charge(binding, poll)?;
        let mut limits = self.limits.clone();
        limits.resolution.validation.max_work -= self.work;
        let additional = add(graph_bytes, payload_bytes)?;
        cap(
            "retained replay additional bytes",
            additional,
            limits.resolution.validation.max_bytes,
        )?;
        limits.resolution.validation.max_bytes -= additional;
        // Any DAG resource error now reports this residual-stage cap/counter,
        // not the pre-prefix total. The two grants add to the original cap.
        Ok(limits)
    }
}
