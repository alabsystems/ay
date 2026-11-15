// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

impl<'scope, 'source> ScalarEncoding<'scope, 'source> {
    pub(super) fn attach(
        context: Context<'scope, 'source>,
        cnf: &'scope CountedCnf<'scope>,
    ) -> Result<Self> {
        let owner = context.admission();
        owner.admit(1, 0)?;
        let mut bv = arrays::encoder(context, cnf)?;
        let parts = cleanup::invoke(owner, || prepare(cnf, context, &mut bv, owner));
        match parts {
            Ok((rows, links, offset, num_vars)) => {
                let attached = Self {
                    context,
                    cnf,
                    bv,
                    rows,
                    links,
                    offset,
                    num_vars,
                };
                if let Err(error) = owner.check() {
                    let _ = attached.finish();
                    return Err(error.into());
                }
                Ok(attached)
            }
            Err(error) => {
                bv.finish().map_err(bv_error)?;
                owner.check()?;
                Err(error)
            }
        }
    }
}

type Parts = (Vec<AttachedRow>, Vec<Link>, u32, u32);

fn prepare(
    cnf: &CountedCnf<'_>,
    context: Context<'_, '_>,
    bv: &mut CountedBvEncoder<'_>,
    owner: &CountedAdmission,
) -> Result<Parts> {
    let mut roots = Vec::new();
    memory::push(&mut roots, context.root(), owner)?;
    for variable in 1..=cnf.num_vars() {
        owner.admit(1, 0)?;
        let source = cnf.sat_literal_term(i32::try_from(variable).map_err(|_| Error::IllTyped)?)?;
        memory::push(&mut roots, source, owner)?;
    }
    arrays::roots(context, &mut roots)?;
    // This visits original dead arms as well as proof-introduced representatives.
    // It does NOT assert roots: only the original Boolean CNF activates them.
    let result = bv.encode_terms(&roots).map_err(bv_error);
    drop(roots);
    owner.check()?;
    result?;
    let (offset, num_vars) = layout(cnf.num_vars(), bv.num_vars().map_err(bv_error)?)?;
    let mut rows = ordinary_rows(cnf, bv, offset, owner)?;
    arrays::append(context, bv, offset, &mut rows)?;
    let mut links = Vec::new();
    for variable in 1..=cnf.num_vars() {
        owner.admit(1, 0)?;
        let boolean = i32::try_from(variable).map_err(|_| Error::IllTyped)?;
        let source = cnf.sat_literal_term(boolean)?;
        let bitvector = shifted(bv.literal(source).map_err(bv_error)?, offset)?;
        let index = links.len();
        memory::push(
            &mut links,
            Link {
                source,
                boolean,
                bitvector,
            },
            owner,
        )?;
        append(
            &mut rows,
            &[-boolean, bitvector],
            0,
            RowOrigin::Link {
                index,
                reverse: false,
            },
            owner,
        )?;
        append(
            &mut rows,
            &[boolean, -bitvector],
            0,
            RowOrigin::Link {
                index,
                reverse: true,
            },
            owner,
        )?;
    }
    owner.check()?;
    Ok((rows, links, offset, num_vars))
}

fn ordinary_rows(
    cnf: &CountedCnf<'_>,
    bv: &CountedBvEncoder<'_>,
    offset: u32,
    owner: &CountedAdmission,
) -> Result<Vec<AttachedRow>> {
    let mut rows = Vec::new();
    for (index, row) in cnf.rows().iter().enumerate() {
        append(
            &mut rows,
            row.literals(),
            0,
            RowOrigin::Boolean(index),
            owner,
        )?;
    }
    for (index, row) in bv.clauses().map_err(bv_error)?.iter().enumerate() {
        append(
            &mut rows,
            row.literals(),
            offset,
            RowOrigin::Bitvector(index),
            owner,
        )?;
    }
    Ok(rows)
}

pub(super) fn layout(boolean: u32, bitvector: u32) -> Result<(u32, u32)> {
    let total = boolean.checked_add(bitvector).ok_or(Error::IllTyped)?;
    if total > i32::MAX as u32 {
        return Err(Error::IllTyped);
    }
    Ok((boolean, total))
}

pub(super) fn shifted(literal: i32, offset: u32) -> Result<i32> {
    let magnitude = literal
        .checked_abs()
        .filter(|value| *value != 0)
        .ok_or(Error::IllTyped)?;
    let offset = i32::try_from(offset).map_err(|_| Error::IllTyped)?;
    let shifted = magnitude.checked_add(offset).ok_or(Error::IllTyped)?;
    Ok(if literal < 0 { -shifted } else { shifted })
}

pub(super) fn append(
    rows: &mut Vec<AttachedRow>,
    source: &[i32],
    offset: u32,
    origin: RowOrigin,
    owner: &CountedAdmission,
) -> Result<()> {
    owner.admit(1, 0)?;
    let mut literals = Vec::new();
    memory::reserve(&mut literals, source.len(), owner)?;
    for &literal in source {
        owner.admit(1, 0)?;
        literals.push(shifted(literal, offset)?);
    }
    memory::push(rows, AttachedRow { literals, origin }, owner)
}
