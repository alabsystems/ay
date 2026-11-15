// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

pub(super) fn original(
    encoding: &ScalarEncoding<'_, '_>,
    bindings: &[ScalarValue],
    arrays: &free::Model,
) -> Result<()> {
    let owner = encoding.admission();
    owner.admit(1, 0)?;
    arrays.validate(encoding)?;
    let mut variables = Vec::new();
    memory::reserve(&mut variables, encoding.cnf.terms().len(), owner)?;
    variables.resize(encoding.cnf.terms().len(), None);
    let mut scalar = 0;
    for binding in encoding.context.bindings() {
        owner.admit(1, 0)?;
        if matches!(&binding.original.sort, ChcSort::Array(..)) {
            continue;
        }
        let value = *bindings.get(scalar).ok_or(Error::InvalidCandidate)?;
        scalar += 1;
        match (&binding.original.sort, value) {
            (ChcSort::Bool, ScalarValue::Bool(_)) => {}
            (ChcSort::BitVec(width), ScalarValue::BitVec(bits, actual))
                if *width == actual && operations::canonical(bits, actual) => {}
            _ => return Err(Error::InvalidCandidate),
        }
        let slot = variables
            .get_mut(binding.term.index())
            .ok_or(Error::InvalidCandidate)?;
        if slot.replace(value).is_some() {
            return Err(Error::InvalidCandidate);
        }
    }
    if scalar != bindings.len() {
        return Err(Error::InvalidCandidate);
    }
    let result = if encoding.context.census().has_arrays {
        arrays::original(encoding, &variables, arrays)
    } else {
        evaluate(encoding, &variables)
    };
    drop(variables);
    owner.check()?;
    result
}

fn evaluate(encoding: &ScalarEncoding<'_, '_>, variables: &[Option<ScalarValue>]) -> Result<()> {
    let query = encoding.context.query;
    let owner = encoding.admission();
    let mut values = Vec::new();
    let mut args = Vec::new();
    memory::reserve(&mut values, query.nodes.len(), owner)?;
    for &(source, ty) in &query.nodes {
        owner.admit(1, 0)?;
        args.clear();
        let children = crate::expr::dag::children(source);
        memory::reserve(&mut args, children.len(), owner)?;
        for child in children {
            let index = query.node_index(child)?;
            args.push(*values.get(index).ok_or(Error::InvalidCandidate)?);
        }
        let value = match source {
            ChcExpr::Bool(value) => ScalarValue::Bool(*value),
            ChcExpr::BitVec(value, width) if operations::canonical(*value, *width) => {
                ScalarValue::BitVec(*value, *width)
            }
            ChcExpr::Var(_) => {
                let term = encoding.context.term_for(source)?;
                owner.admit(1, 0)?;
                variables
                    .get(term.index())
                    .copied()
                    .flatten()
                    .ok_or(Error::InvalidCandidate)?
            }
            ChcExpr::Op(op, _) => operations::apply(*op, &args, owner)?,
            _ => return Err(Error::Unsupported),
        };
        match (ty, value) {
            (Type::Bool, ScalarValue::Bool(_)) => {}
            (Type::BitVec(width), ScalarValue::BitVec(_, actual)) if width == actual => {}
            _ => return Err(Error::InvalidCandidate),
        }
        values.push(value);
    }
    let root = query.node_index(query.original)?;
    let valid = values.get(root) == Some(&ScalarValue::Bool(true));
    drop(args);
    drop(values);
    owner.check()?;
    if valid {
        Ok(())
    } else {
        Err(Error::InvalidCandidate)
    }
}
