// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
use super::*;
mod gates;

#[derive(Clone, Copy)]
struct Literal {
    cnf: i32,
    source: SourceLit,
}
impl Literal {
    fn negated(self) -> Self {
        Self {
            cnf: -self.cnf,
            source: self.source.negated(),
        }
    }
}

pub(super) fn run(out: &mut Encoder<'_>, source: &Source) -> Result<()> {
    let mut bridge_index = 0;
    for &id in &source.order {
        out.owner.admit(1, 0)?;
        if source.kinds[id.index()] == Kind::Distinct {
            let bridge = *out.data.bridges.get(bridge_index).ok_or(Error::Invalid)?;
            if bridge.source != id {
                return Err(Error::Invalid);
            }
            distinct(out, bridge)?;
            bridge_index += 1;
        } else {
            node(out, id, source.kinds[id.index()])?;
        }
    }
    for index in 0..out.data.roots.len() {
        out.owner.admit(1, 0)?;
        let root = out.data.roots[index];
        let literal = literal(out, root)?;
        row(out, &[literal], Justification::Root(root))?;
    }
    out.owner.check().map_err(Error::from)
}

fn literal(out: &Encoder<'_>, id: TermId) -> Result<Literal> {
    out.owner.admit(1, 0)?;
    let cnf = out
        .data
        .term_literals
        .get(id.index())
        .copied()
        .flatten()
        .ok_or(Error::Invalid)?;
    Ok(Literal {
        cnf,
        source: SourceLit::positive(id),
    })
}

fn fresh(out: &mut Encoder<'_>, id: TermId) -> Result<Literal> {
    out.owner.admit(1, 0)?;
    let next = out
        .data
        .num_vars
        .checked_add(1)
        .filter(|n| *n <= i32::MAX as u32)
        .ok_or(Error::Unsupported)?;
    out.data.num_vars = next;
    out.data.term_literals[id.index()] = Some(next as i32);
    literal(out, id)
}

fn node(out: &mut Encoder<'_>, id: TermId, kind: Kind) -> Result<()> {
    out.owner.admit(1, 0)?;
    if kind == Kind::Value || out.data.term_literals[id.index()].is_some() {
        return Ok(());
    }
    if kind == Kind::Not {
        let TermData::Not(child) = out.terms.get(id) else {
            return Err(Error::Invalid);
        };
        let lit = literal(out, *child)?;
        out.data.term_literals[id.index()] = Some(-lit.cnf);
        return Ok(());
    }
    let v = fresh(out, id)?;
    match kind {
        Kind::Atom => memory::push(&mut out.data.theory_atoms, id, &out.owner),
        Kind::Variable => Ok(()),
        Kind::Constant(value) => native(
            out,
            id,
            if value {
                AletheRule::True
            } else {
                AletheRule::False
            },
            &[if value { v } else { v.negated() }],
        ),
        Kind::And | Kind::Or => gates::wide(out, id, kind, v),
        Kind::Implies | Kind::Xor | Kind::Eq | Kind::Ite => gates::small(out, id, kind, v),
        _ => Err(Error::Invalid),
    }
}

fn row(out: &mut Encoder<'_>, values: &[Literal], justification: Justification) -> Result<()> {
    let mut literals = Vec::new();
    memory::reserve(&mut literals, values.len(), &out.owner)?;
    out.owner.admit(values.len(), 0)?;
    literals.extend(values.iter().map(|value| value.cnf));
    memory::push(
        &mut out.data.rows,
        Row {
            literals,
            justification,
        },
        &out.owner,
    )
}

fn step(
    out: &mut Encoder<'_>,
    source: TermId,
    rule: AletheRule,
    clause: &[SourceLit],
    premises: Option<[usize; 2]>,
    pivot: Option<TermId>,
) -> Result<usize> {
    let clause = memory::copy(clause, &out.owner)?;
    let index = out.data.steps.len();
    memory::push(
        &mut out.data.steps,
        Step {
            rule,
            source,
            clause,
            premises,
            pivot,
        },
        &out.owner,
    )?;
    Ok(index)
}

fn native(
    out: &mut Encoder<'_>,
    source: TermId,
    rule: AletheRule,
    values: &[Literal],
) -> Result<()> {
    let mut clause = Vec::new();
    memory::reserve(&mut clause, values.len(), &out.owner)?;
    out.owner.admit(values.len(), 0)?;
    clause.extend(values.iter().map(|value| value.source));
    let index = step(out, source, rule, &clause, None, None)?;
    row(out, values, Justification::Step(index))
}

fn distinct(out: &mut Encoder<'_>, bridge: DistinctBridge) -> Result<()> {
    let TermData::App(_, args) = out.terms.get(bridge.equality) else {
        return Err(Error::Invalid);
    };
    let kind = if out.terms.sort(args[0]) == &Sort::Bool {
        Kind::Eq
    } else {
        Kind::Atom
    };
    node(out, bridge.equality, kind)?;
    node(out, bridge.negation, Kind::Not)?;
    let d = fresh(out, bridge.source)?;
    let e = literal(out, bridge.equality)?;
    let n = literal(out, bridge.negation)?;
    let q = SourceLit::positive(bridge.equivalence);
    let unit = step(
        out,
        bridge.source,
        AletheRule::DistinctElim,
        &[q],
        None,
        None,
    )?;
    let pos = step(
        out,
        bridge.equivalence,
        AletheRule::EquivPos1,
        &[q.negated(), d.source, e.source],
        None,
        None,
    )?;
    let neg = step(
        out,
        bridge.equivalence,
        AletheRule::EquivPos2,
        &[q.negated(), d.source.negated(), n.source],
        None,
        None,
    )?;
    for (premise, values) in [(pos, [d, e]), (neg, [d.negated(), n])] {
        let derived = step(
            out,
            bridge.source,
            AletheRule::Resolution,
            &[values[0].source, values[1].source],
            Some([unit, premise]),
            Some(bridge.equivalence),
        )?;
        row(out, &values, Justification::Step(derived))?;
    }
    Ok(())
}
