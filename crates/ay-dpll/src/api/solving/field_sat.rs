// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
//! Lazy Boolean/prime-field combination. Davis--Putnam variable elimination
//! (Davis and Putnam, JACM 7(3), 1960) emits explicit native resolution;
//! inconsistent algebra assignments contribute independently checked clauses.
//! Every retry spends the SAME caller's admission, without a branch allowance.
use super::{field_solve, tactic_model::TacticModelConverter, tactics::TacticFailure};
use ay_core::term::{
    reserve_counted, CountedBuiltin, CountedTermBuilder, TermConstructionAdmission,
};
use ay_core::{
    AletheRule, Constant, Proof, ProofId, ProofStep, Sort, Symbol, TermData, TermId, TermStore,
    TheoryLemmaKind,
};
mod algebra;

fn failed() -> TacticFailure {
    TacticFailure::new("ff-sat original owner stopped or unsupported typed Boolean/field goal")
}
#[derive(Clone, Copy, PartialEq, Eq)]
enum Polarity {
    Positive,
    Negative,
}
#[derive(Clone, Copy, PartialEq, Eq)]
struct Lit {
    atom: TermId,
    polarity: Polarity,
}
impl Lit {
    fn positive(atom: TermId) -> Self {
        Self {
            atom,
            polarity: Polarity::Positive,
        }
    }
    fn neg(self) -> Self {
        Self {
            atom: self.atom,
            polarity: match self.polarity {
                Polarity::Positive => Polarity::Negative,
                Polarity::Negative => Polarity::Positive,
            },
        }
    }
    fn holds(self, value: bool) -> bool {
        value == (self.polarity == Polarity::Positive)
    }
}
struct Row {
    clause: Vec<Lit>,
    proof: ProofId,
}
type Owner<'a> = &'a dyn TermConstructionAdmission;
fn pay(owner: Owner<'_>, work: usize) -> Result<(), TacticFailure> {
    owner.admit(work, 0).map_err(|_| failed())
}
fn copied<T: Copy>(input: &[T], owner: Owner<'_>) -> Result<Vec<T>, TacticFailure> {
    pay(owner, input.len())?;
    let mut result = Vec::new();
    reserve_counted(&mut result, input.len(), owner).map_err(|_| failed())?;
    result.extend_from_slice(input);
    Ok(result)
}
fn literal(terms: &TermStore, mut id: TermId, owner: Owner<'_>) -> Result<Lit, TacticFailure> {
    let mut result = Lit::positive(id);
    loop {
        pay(owner, 1)?;
        if id.index() >= terms.len() || terms.sort(id) != &Sort::Bool {
            return Err(failed());
        }
        let TermData::Not(child) = terms.get(id) else {
            return Ok(result);
        };
        if child.index() >= id.index() {
            return Err(failed());
        }
        id = *child;
        result = result.neg();
        result.atom = id;
    }
}
fn canonical(
    terms: &TermStore,
    input: &[Lit],
    owner: Owner<'_>,
) -> Result<Option<Vec<Lit>>, TacticFailure> {
    let mut out: Vec<Lit> = Vec::new();
    reserve_counted(&mut out, input.len(), owner).map_err(|_| failed())?;
    for &raw in input {
        let normalized = literal(terms, raw.atom, owner)?;
        let lit = if raw.polarity == Polarity::Positive {
            normalized
        } else {
            normalized.neg()
        };
        pay(owner, out.len().checked_add(1).ok_or_else(failed)?)?;
        match out.binary_search_by_key(&lit.atom.index(), |old| old.atom.index()) {
            Ok(index) if out[index] != lit => return Ok(None),
            Ok(_) => {}
            Err(index) => out.insert(index, lit),
        }
    }
    Ok(Some(out))
}
fn materialize(
    terms: &mut TermStore,
    literals: &[Lit],
    owner: Owner<'_>,
) -> Result<Vec<TermId>, TacticFailure> {
    let mut result = Vec::new();
    reserve_counted(&mut result, literals.len(), owner).map_err(|_| failed())?;
    let borrowed = super::field_to_bv::Borrowed(owner);
    let mut builder = CountedTermBuilder::with_admission(terms, &borrowed).map_err(|_| failed())?;
    for lit in literals {
        pay(owner, 1)?;
        result.push(if lit.polarity == Polarity::Positive {
            lit.atom
        } else {
            builder
                .apply(CountedBuiltin::Not, &[lit.atom])
                .map_err(|_| failed())?
        });
    }
    Ok(result)
}
fn step(proof: &mut Proof, owner: Owner<'_>) -> Result<(), TacticFailure> {
    if u32::try_from(proof.steps.len().checked_add(1).ok_or_else(failed)?).is_err() {
        return Err(failed());
    }
    reserve_counted(&mut proof.steps, 1, owner).map_err(|_| failed())
}
enum ClauseKind {
    Theory(TheoryLemmaKind),
    Boolean(AletheRule),
}
impl From<TheoryLemmaKind> for ClauseKind {
    fn from(kind: TheoryLemmaKind) -> Self {
        Self::Theory(kind)
    }
}
impl From<AletheRule> for ClauseKind {
    fn from(rule: AletheRule) -> Self {
        Self::Boolean(rule)
    }
}
fn lemma(
    terms: &mut TermStore,
    proof: &mut Proof,
    clause: &[Lit],
    kind: impl Into<ClauseKind>,
    owner: Owner<'_>,
) -> Result<Option<Row>, TacticFailure> {
    let Some(canonical_clause) = canonical(terms, clause, owner)? else {
        return Ok(None);
    };
    // Keep the exact gate children in the certificate. The SAT row itself
    // uses negation-parity-normalized literals, as does native resolution.
    let rendered = materialize(terms, clause, owner)?;
    step(proof, owner)?;
    let id = match kind.into() {
        ClauseKind::Theory(kind) => {
            owner.admit(2, 2).map_err(|_| failed())?;
            proof.add_step(ProofStep::TheoryLemma {
                theory: "FF".into(),
                clause: rendered,
                farkas: None,
                kind,
                lia: None,
            })
        }
        ClauseKind::Boolean(rule) => proof.add_rule_step(rule, rendered, Vec::new(), Vec::new()),
    };
    Ok(Some(Row {
        clause: canonical_clause,
        proof: id,
    }))
}
fn push(rows: &mut Vec<Row>, row: Option<Row>, owner: Owner<'_>) -> Result<(), TacticFailure> {
    if let Some(row) = row {
        reserve_counted(rows, 1, owner).map_err(|_| failed())?;
        rows.push(row);
    }
    Ok(())
}
struct BooleanSource {
    variables: Vec<TermId>,
    fields: Vec<TermId>,
    booleans: Vec<TermId>,
    rows: Vec<Row>,
    proof: Proof,
}
enum Gate {
    Implies,
    Equiv,
    Xor,
    Ite,
}
fn small_gate(
    terms: &mut TermStore,
    result: &mut BooleanSource,
    id: TermId,
    children: &[TermId],
    gate: Gate,
    owner: Owner<'_>,
) -> Result<(), TacticFailure> {
    let expected = if matches!(gate, Gate::Ite) { 3 } else { 2 };
    if children.len() != expected {
        return Err(failed());
    }
    let r = Lit::positive(id);
    let mut inputs = [r; 3];
    for (i, &child) in children.iter().enumerate() {
        pay(owner, 1)?;
        if child.index() >= id.index() || terms.sort(child) != &Sort::Bool {
            return Err(failed());
        }
        inputs[i] = Lit::positive(child);
    }
    let [a, b, c] = inputs;
    macro_rules! clause {
        ($rule:ident; $($lit:expr),+) => {{
            let row = lemma(terms, &mut result.proof, &[$($lit),+], AletheRule::$rule, owner)?;
            push(&mut result.rows, row, owner)?;
        }};
    }
    match gate {
        Gate::Implies => {
            clause!(ImpliesPos; r.neg(), a.neg(), b);
            clause!(ImpliesNeg1; r, a);
            clause!(ImpliesNeg2; r, b.neg());
        }
        Gate::Equiv => {
            clause!(EquivPos1; r.neg(), a, b.neg());
            clause!(EquivPos2; r.neg(), a.neg(), b);
            clause!(EquivNeg1; r, a.neg(), b.neg());
            clause!(EquivNeg2; r, a, b);
        }
        Gate::Xor => {
            clause!(XorPos1; r.neg(), a, b);
            clause!(XorPos2; r.neg(), a.neg(), b.neg());
            clause!(XorNeg1; r, a, b.neg());
            clause!(XorNeg2; r, a.neg(), b);
        }
        Gate::Ite => {
            clause!(ItePos1; r.neg(), a, c);
            clause!(ItePos2; r.neg(), a.neg(), b);
            clause!(IteNeg1; r, a, c.neg());
            clause!(IteNeg2; r, a.neg(), b.neg());
        }
    }
    Ok(())
}
fn source(
    terms: &mut TermStore,
    roots: &[TermId],
    owner: Owner<'_>,
) -> Result<BooleanSource, TacticFailure> {
    let count = terms.len();
    let mut seen = Vec::new();
    reserve_counted(&mut seen, count, owner).map_err(|_| failed())?;
    pay(owner, count)?;
    seen.resize(count, false);
    let mut pending = copied(roots, owner)?;
    let mut result = BooleanSource {
        variables: Vec::new(),
        fields: Vec::new(),
        booleans: Vec::new(),
        rows: Vec::new(),
        proof: Proof::new(),
    };
    for &root in roots {
        let lit = literal(terms, root, owner)?;
        step(&mut result.proof, owner)?;
        let proof = result.proof.add_assume(root, None);
        push(
            &mut result.rows,
            Some(Row {
                clause: copied(&[lit], owner)?,
                proof,
            }),
            owner,
        )?;
    }
    while let Some(id) = pending.pop() {
        pay(owner, 1)?;
        let lit = literal(terms, id, owner)?;
        let id = lit.atom;
        if seen[id.index()] {
            continue;
        }
        seen[id.index()] = true;
        reserve_counted(&mut result.variables, 1, owner).map_err(|_| failed())?;
        result.variables.push(id);
        let r = Lit::positive(id);
        match terms.get(id) {
            TermData::Const(Constant::Bool(value)) => {
                let clause = [if *value { r } else { r.neg() }];
                let row = lemma(
                    terms,
                    &mut result.proof,
                    &clause,
                    TheoryLemmaKind::BoolTautology,
                    owner,
                )?;
                push(&mut result.rows, row, owner)?;
            }
            TermData::Var(_, _) => {
                reserve_counted(&mut result.booleans, 1, owner).map_err(|_| failed())?;
                result.booleans.push(id);
            }
            TermData::Ite(a, b, c) => {
                let children = [*a, *b, *c];
                small_gate(terms, &mut result, id, &children, Gate::Ite, owner)?;
                reserve_counted(&mut pending, 3, owner).map_err(|_| failed())?;
                pending.extend_from_slice(&children);
            }
            TermData::App(Symbol::Named(name), args) => {
                pay(
                    owner,
                    name.len().checked_add(args.len()).ok_or_else(failed)?,
                )?;
                if terms.is_declared_function(name) {
                    return Err(failed());
                }
                if args.iter().any(|child| child.index() >= id.index()) {
                    return Err(failed());
                }
                if matches!(name.as_str(), "=" | "distinct")
                    && args.len() >= 2
                    && matches!(terms.sort(args[0]), Sort::FiniteField(_))
                {
                    reserve_counted(&mut result.fields, 1, owner).map_err(|_| failed())?;
                    result.fields.push(id);
                    continue;
                }
                let gate = match name.as_str() {
                    "=>" => Some(Gate::Implies),
                    "=" => Some(Gate::Equiv),
                    "xor" => Some(Gate::Xor),
                    "ite" => Some(Gate::Ite),
                    "and" | "or" => None,
                    _ => return Err(failed()),
                };
                let conjunction = name.as_str() == "and";
                let children = copied(args, owner)?;
                if let Some(gate) = gate {
                    small_gate(terms, &mut result, id, &children, gate, owner)?;
                    reserve_counted(&mut pending, children.len(), owner).map_err(|_| failed())?;
                    pending.extend_from_slice(&children);
                    continue;
                }
                let mut big = copied(&[if conjunction { r } else { r.neg() }], owner)?;
                reserve_counted(&mut big, children.len(), owner).map_err(|_| failed())?;
                reserve_counted(&mut pending, children.len(), owner).map_err(|_| failed())?;
                for child in children {
                    if child.index() >= id.index() {
                        return Err(failed());
                    }
                    if terms.sort(child) != &Sort::Bool {
                        return Err(failed());
                    }
                    let c = Lit::positive(child);
                    pending.push(child);
                    let clause = if conjunction {
                        [r.neg(), c]
                    } else {
                        [r, c.neg()]
                    };
                    let row = lemma(
                        terms,
                        &mut result.proof,
                        &clause,
                        TheoryLemmaKind::BoolTautology,
                        owner,
                    )?;
                    push(&mut result.rows, row, owner)?;
                    big.push(if conjunction { c.neg() } else { c });
                }
                let row = lemma(
                    terms,
                    &mut result.proof,
                    &big,
                    TheoryLemmaKind::BoolTautology,
                    owner,
                )?;
                push(&mut result.rows, row, owner)?;
            }
            _ => return Err(failed()),
        }
    }
    // Validate every field atom before Boolean reasoning can refute a source
    // containing an otherwise unreachable malformed/opaque arithmetic term.
    if !result.fields.is_empty() {
        field_solve::source(terms, &result.fields, owner)?.ok_or_else(failed)?;
    }
    Ok(result)
}
fn resolution(
    terms: &mut TermStore,
    proof: &mut Proof,
    a: &Row,
    b: &Row,
    pivot: TermId,
    owner: Owner<'_>,
) -> Result<Option<Row>, TacticFailure> {
    let mut combined = Vec::new();
    reserve_counted(
        &mut combined,
        a.clause
            .len()
            .checked_add(b.clause.len())
            .ok_or_else(failed)?,
        owner,
    )
    .map_err(|_| failed())?;
    for lit in a.clause.iter().chain(&b.clause) {
        pay(owner, 1)?;
        if lit.atom != pivot {
            combined.push(*lit);
        }
    }
    let Some(clause) = canonical(terms, &combined, owner)? else {
        return Ok(None);
    };
    let rendered = materialize(terms, &clause, owner)?;
    step(proof, owner)?;
    let id = proof.add_resolution(rendered, pivot, a.proof, b.proof);
    Ok(Some(Row { clause, proof: id }))
}
enum BooleanDecision {
    Unsat,
    Model(Vec<Option<bool>>),
}
fn decide(
    terms: &mut TermStore,
    source: &mut BooleanSource,
    owner: Owner<'_>,
) -> Result<BooleanDecision, TacticFailure> {
    let mut rows = Vec::new();
    reserve_counted(&mut rows, source.rows.len(), owner).map_err(|_| failed())?;
    for row in &source.rows {
        rows.push(Row {
            clause: copied(&row.clause, owner)?,
            proof: row.proof,
        });
    }
    let mut eliminated = Vec::new();
    reserve_counted(&mut eliminated, source.variables.len(), owner).map_err(|_| failed())?;
    for &variable in &source.variables {
        let mut positive = Vec::new();
        let mut negative = Vec::new();
        let mut kept = Vec::new();
        for row in rows {
            pay(owner, row.clause.len().checked_add(1).ok_or_else(failed)?)?;
            if row.clause.is_empty() {
                return Ok(BooleanDecision::Unsat);
            }
            let bucket = match row.clause.iter().find(|lit| lit.atom == variable) {
                Some(lit) if lit.polarity == Polarity::Positive => &mut positive,
                Some(_) => &mut negative,
                None => &mut kept,
            };
            reserve_counted(bucket, 1, owner).map_err(|_| failed())?;
            bucket.push(row);
        }
        for a in &positive {
            for b in &negative {
                pay(owner, 1)?;
                let row = resolution(terms, &mut source.proof, a, b, variable, owner)?;
                if row.as_ref().is_some_and(|row| row.clause.is_empty()) {
                    return Ok(BooleanDecision::Unsat);
                }
                push(&mut kept, row, owner)?;
            }
        }
        eliminated.push((variable, positive, negative));
        rows = kept;
    }
    if !rows.is_empty() {
        return Err(failed());
    }
    let mut values = Vec::new();
    reserve_counted(&mut values, terms.len(), owner).map_err(|_| failed())?;
    pay(owner, terms.len())?;
    values.resize(terms.len(), None);
    for (variable, positive, negative) in eliminated.into_iter().rev() {
        let mut required = None;
        for row in positive.iter().chain(&negative) {
            let mut satisfied = false;
            let mut own = None;
            for &lit in &row.clause {
                pay(owner, 1)?;
                if lit.atom == variable {
                    own = Some(lit.polarity == Polarity::Positive);
                } else if lit.holds(values[lit.atom.index()].ok_or_else(failed)?) {
                    satisfied = true;
                }
            }
            if !satisfied {
                let demand = own.ok_or_else(failed)?;
                if required.is_some_and(|prior| prior != demand) {
                    return Err(failed());
                }
                required = Some(demand);
            }
        }
        values[variable.index()] = Some(required.unwrap_or(false));
    }
    Ok(BooleanDecision::Model(values))
}
fn check_refutation(
    terms: &TermStore,
    roots: &[TermId],
    proof: &Proof,
    owner: Owner<'_>,
) -> Result<(), TacticFailure> {
    let mut bytes = proof
        .steps
        .len()
        .checked_mul(std::mem::size_of::<Option<Vec<TermId>>>())
        .ok_or_else(failed)?;
    for step in &proof.steps {
        pay(owner, 1)?;
        let count = match step {
            ProofStep::Assume(_) => 1,
            ProofStep::Resolution { clause, .. }
            | ProofStep::TheoryLemma { clause, .. }
            | ProofStep::Step { clause, .. } => clause.len(),
            _ => return Err(failed()),
        };
        bytes = bytes
            .checked_add(
                count
                    .checked_mul(2 * std::mem::size_of::<TermId>())
                    .ok_or_else(failed)?,
            )
            .ok_or_else(failed)?;
    }
    owner
        .admit(proof.steps.len(), bytes)
        .map_err(|_| failed())?;
    let checked = ay_proof::check_proof_strict_with_context_and_progress(
        proof,
        terms,
        None,
        None,
        Some(roots),
        &mut |w, b| owner.admit(w, b).is_ok(),
    );
    owner.check().map_err(|_| failed())?;
    if checked.is_ok_and(|quality| quality.is_complete()) {
        Ok(())
    } else {
        Err(failed())
    }
}
pub(super) fn apply(
    terms: &mut TermStore,
    roots: &[TermId],
    converter: &TacticModelConverter,
    owner: Owner<'_>,
) -> Result<(Vec<TermId>, TacticModelConverter), TacticFailure> {
    owner.check().map_err(|_| failed())?;
    if !converter.valid(terms) {
        return Err(failed());
    }
    if converter.is_active() {
        if roots.is_empty() {
            // A preceding owned pass already solved this goal. Preserve its
            // exact witness; do not replace it with an empty reconstructed
            // model or open another arithmetic/solve attempt.
            pay(owner, 1)?;
            return Ok((Vec::new(), converter.clone()));
        }
        return Err(failed());
    }
    let mut source = source(terms, roots, owner)?;
    loop {
        owner.check().map_err(|_| failed())?;
        let values = match decide(terms, &mut source, owner)? {
            BooleanDecision::Unsat => {
                check_refutation(terms, roots, &source.proof, owner)?;
                let borrowed = super::field_to_bv::Borrowed(owner);
                let no = CountedTermBuilder::with_admission(terms, &borrowed)
                    .map_err(|_| failed())?
                    .boolean(false)
                    .map_err(|_| failed())?;
                return Ok((copied(&[no], owner)?, converter.clone()));
            }
            BooleanDecision::Model(values) => values,
        };
        let mut signed = Vec::new();
        reserve_counted(&mut signed, source.fields.len(), owner).map_err(|_| failed())?;
        for &atom in &source.fields {
            pay(owner, 1)?;
            let lit = Lit::positive(atom);
            signed.push(if values[atom.index()].ok_or_else(failed)? {
                lit
            } else {
                lit.neg()
            });
        }
        let branch = materialize(terms, &signed, owner)?;
        let candidate = if branch.is_empty() {
            crate::executor::finite_field::TacticFieldCandidate::Model(Vec::new())
        } else {
            // f != 0 iff there exists a fresh field coordinate y with yf=1.
            // These internal existential DATA variables are never returned as
            // authored bindings; independent replay reconstructs its own
            // formal inverse columns from the ORIGINAL signed atoms.
            let encoded = algebra::encode(terms, &signed, converter, owner)?;
            let seen = field_solve::source(terms, &encoded.roots, owner)?.ok_or_else(failed)?;
            match crate::executor::finite_field::tactic_ideal_candidate(
                terms,
                &encoded.roots,
                &seen,
                owner,
            )
            .ok_or_else(failed)?
            {
                crate::executor::finite_field::TacticFieldCandidate::Model(rows) => {
                    let mut fields = Vec::new();
                    reserve_counted(&mut fields, rows.len(), owner).map_err(|_| failed())?;
                    for row in rows {
                        pay(
                            owner,
                            encoded
                                .auxiliaries
                                .len()
                                .checked_add(1)
                                .ok_or_else(failed)?,
                        )?;
                        if !encoded.auxiliaries.contains(&row.0) {
                            fields.push(row);
                        }
                    }
                    crate::executor::finite_field::TacticFieldCandidate::Model(fields)
                }
                other => other,
            }
        };
        match candidate {
            crate::executor::finite_field::TacticFieldCandidate::Model(fields) => {
                let mut booleans = Vec::new();
                reserve_counted(&mut booleans, source.booleans.len(), owner)
                    .map_err(|_| failed())?;
                for &id in &source.booleans {
                    pay(owner, 1)?;
                    booleans.push((id, values[id.index()].ok_or_else(failed)?));
                }
                let converter =
                    converter.fixed_boolean_field(terms, fields, booleans, roots, owner)?;
                owner.check().map_err(|_| failed())?;
                return Ok((Vec::new(), converter));
            }
            crate::executor::finite_field::TacticFieldCandidate::Contradiction => {
                if !field_solve::independent_refutation(terms, &branch, owner)? {
                    return Err(failed());
                }
                let mut clause = Vec::new();
                reserve_counted(&mut clause, signed.len(), owner).map_err(|_| failed())?;
                for lit in signed {
                    pay(owner, 1)?;
                    clause.push(lit.neg());
                }
                let row = lemma(
                    terms,
                    &mut source.proof,
                    &clause,
                    TheoryLemmaKind::FiniteFieldIdeal,
                    owner,
                )?;
                push(&mut source.rows, row, owner)?;
            }
        }
    }
}

#[cfg(test)]
mod tests;
