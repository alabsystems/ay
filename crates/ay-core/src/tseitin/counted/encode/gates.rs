// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
use super::*;

pub(super) fn wide(out: &mut Encoder<'_>, id: TermId, kind: Kind, v: Literal) -> Result<()> {
    let terms = out.terms;
    let TermData::App(_, args) = terms.get(id) else {
        return Err(Error::Invalid);
    };
    let args = args.as_slice();
    let mut large = Vec::new();
    memory::reserve(
        &mut large,
        args.len()
            .checked_add(1)
            .ok_or_else(|| memory::work(&out.owner))?,
        &out.owner,
    )?;
    for (index, &arg) in args.iter().enumerate() {
        let a = literal(out, arg)?;
        if kind == Kind::And {
            let position = u32::try_from(index).map_err(|_| Error::Unsupported)?;
            native(out, id, AletheRule::AndPos(position), &[v.negated(), a])?;
            large.push(a.negated());
        } else {
            native(out, id, AletheRule::OrNeg, &[a.negated(), v])?;
            large.push(a);
        }
    }
    out.owner.admit(1, 0)?;
    large.push(if kind == Kind::And { v } else { v.negated() });
    native(
        out,
        id,
        if kind == Kind::And {
            AletheRule::AndNeg
        } else {
            AletheRule::OrPos(0)
        },
        &large,
    )
}

pub(super) fn small(out: &mut Encoder<'_>, id: TermId, kind: Kind, v: Literal) -> Result<()> {
    if kind == Kind::Ite {
        let TermData::Ite(c, t, e) = out.terms.get(id) else {
            return Err(Error::Invalid);
        };
        let [c, t, e] = [literal(out, *c)?, literal(out, *t)?, literal(out, *e)?];
        native(out, id, AletheRule::ItePos2, &[c.negated(), v.negated(), t])?;
        native(out, id, AletheRule::ItePos1, &[c, v.negated(), e])?;
        native(out, id, AletheRule::IteNeg2, &[c.negated(), t.negated(), v])?;
        return native(out, id, AletheRule::IteNeg1, &[c, e.negated(), v]);
    }
    let TermData::App(_, args) = out.terms.get(id) else {
        return Err(Error::Invalid);
    };
    let [a, b] = [literal(out, args[0])?, literal(out, args[1])?];
    match kind {
        Kind::Implies => {
            native(
                out,
                id,
                AletheRule::ImpliesPos,
                &[v.negated(), a.negated(), b],
            )?;
            native(out, id, AletheRule::ImpliesNeg1, &[v, a])?;
            native(out, id, AletheRule::ImpliesNeg2, &[v, b.negated()])
        }
        Kind::Eq => {
            native(
                out,
                id,
                AletheRule::EquivPos2,
                &[v.negated(), a.negated(), b],
            )?;
            native(
                out,
                id,
                AletheRule::EquivPos1,
                &[v.negated(), a, b.negated()],
            )?;
            native(out, id, AletheRule::EquivNeg2, &[a, b, v])?;
            native(
                out,
                id,
                AletheRule::EquivNeg1,
                &[a.negated(), b.negated(), v],
            )
        }
        Kind::Xor => {
            native(out, id, AletheRule::XorPos1, &[v.negated(), a, b])?;
            native(
                out,
                id,
                AletheRule::XorPos2,
                &[v.negated(), a.negated(), b.negated()],
            )?;
            native(out, id, AletheRule::XorNeg2, &[a.negated(), b, v])?;
            native(out, id, AletheRule::XorNeg1, &[a, b.negated(), v])
        }
        _ => Err(Error::Invalid),
    }
}
