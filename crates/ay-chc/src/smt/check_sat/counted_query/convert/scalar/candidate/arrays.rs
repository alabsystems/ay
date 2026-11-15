// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Independent original-DAG evaluation of total Bool/BV array witnesses.
//!
//! Read values are evaluated from original constructors, never read from the
//! read-leaf assignment. A persistent store chain represents the full domain,
//! including its genuine constant fill. Free variables use explicit total
//! witnesses, not sampled semantics. Array equality and wide replay still refuse.

use super::*;

#[cfg(test)]
mod tests;

#[derive(Clone, Copy)]
enum Value {
    Scalar(ScalarValue),
    Array(usize),
}

#[derive(Clone, Copy)]
enum Contents {
    Constant(ScalarValue),
    Free(usize),
    Store {
        base: usize,
        index: ScalarValue,
        value: ScalarValue,
    },
}

#[derive(Clone, Copy)]
struct Array {
    shape: Type,
    contents: Contents,
}

pub(super) fn original(
    encoding: &ScalarEncoding<'_, '_>,
    variables: &[Option<ScalarValue>],
    model: &free::Model,
) -> Result<()> {
    let query = encoding.context.query;
    let owner = encoding.admission();
    let mut values = Vec::new();
    let mut arrays = Vec::new();
    let mut args = Vec::new();
    let mut scalar_args = Vec::new();
    let mut native = Vec::new();
    memory::reserve(&mut values, query.nodes.len(), owner)?;
    memory::reserve(&mut native, encoding.cnf.terms().len(), owner)?;
    native.resize(encoding.cnf.terms().len(), None);
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
            ChcExpr::Bool(value) => Value::Scalar(ScalarValue::Bool(*value)),
            ChcExpr::BitVec(value, width) if operations::canonical(*value, *width) => {
                Value::Scalar(ScalarValue::BitVec(*value, *width))
            }
            ChcExpr::Var(_) => {
                let term = encoding.context.term_for(source)?;
                variable(term, ty, variables, model, &mut arrays, owner)?
            }
            ChcExpr::ConstArray(..) => {
                let [Value::Scalar(fill)] = args.as_slice() else {
                    return Err(Error::Unsupported);
                };
                let Type::Array(_, element) = ty else {
                    return Err(Error::InvalidCandidate);
                };
                if scalar_type(*fill) != query.types.get(element)? {
                    return Err(Error::InvalidCandidate);
                }
                insert(
                    &mut arrays,
                    Array {
                        shape: ty,
                        contents: Contents::Constant(*fill),
                    },
                    owner,
                )?
            }
            ChcExpr::Op(op, _) => apply(
                encoding,
                *op,
                ty,
                &args,
                &mut arrays,
                &mut scalar_args,
                model,
            )?,
            _ => return Err(Error::Unsupported),
        };
        if value_type(value, &arrays)? != ty {
            return Err(Error::InvalidCandidate);
        }
        let term = encoding.context.term_for(source)?;
        *native
            .get_mut(term.index())
            .ok_or(Error::InvalidCandidate)? = Some(value);
        values.push(value);
    }
    replay_reads(encoding, &native, &arrays, model)?;
    let root = query.node_index(query.original)?;
    let valid = matches!(
        values.get(root),
        Some(Value::Scalar(ScalarValue::Bool(true)))
    );
    drop(scalar_args);
    drop(args);
    drop(arrays);
    drop(values);
    drop(native);
    owner.check()?;
    if valid {
        Ok(())
    } else {
        Err(Error::InvalidCandidate)
    }
}

fn variable(
    term: TermId,
    ty: Type,
    variables: &[Option<ScalarValue>],
    model: &free::Model,
    arrays: &mut Vec<Array>,
    owner: &CountedAdmission,
) -> Result<Value> {
    owner.admit(1, 0)?;
    if matches!(ty, Type::Array(..)) {
        let index = model.array_index(term, owner)?;
        insert(
            arrays,
            Array {
                shape: ty,
                contents: Contents::Free(index),
            },
            owner,
        )
    } else {
        variables
            .get(term.index())
            .copied()
            .flatten()
            .map(Value::Scalar)
            .ok_or(Error::InvalidCandidate)
    }
}

fn apply(
    encoding: &ScalarEncoding<'_, '_>,
    op: ChcOp,
    ty: Type,
    args: &[Value],
    arrays: &mut Vec<Array>,
    scalar_args: &mut Vec<ScalarValue>,
    model: &free::Model,
) -> Result<Value> {
    let owner = encoding.admission();
    owner.admit(1, 0)?;
    match (op, args) {
        (ChcOp::Ite, [Value::Scalar(ScalarValue::Bool(condition)), yes, no]) => {
            if value_type(*yes, arrays)? != value_type(*no, arrays)? {
                return Err(Error::InvalidCandidate);
            }
            Ok(if *condition { *yes } else { *no })
        }
        (ChcOp::Store, [Value::Array(base), Value::Scalar(index), Value::Scalar(value)]) => {
            let array = arrays.get(*base).ok_or(Error::InvalidCandidate)?;
            let Type::Array(key, element) = array.shape else {
                return Err(Error::InvalidCandidate);
            };
            if array.shape != ty
                || scalar_type(*index) != encoding.context.query.types.get(key)?
                || scalar_type(*value) != encoding.context.query.types.get(element)?
            {
                return Err(Error::InvalidCandidate);
            }
            insert(
                arrays,
                Array {
                    shape: ty,
                    contents: Contents::Store {
                        base: *base,
                        index: *index,
                        value: *value,
                    },
                },
                owner,
            )
        }
        (ChcOp::Select, [Value::Array(array), Value::Scalar(index)]) => {
            let shape = arrays.get(*array).ok_or(Error::InvalidCandidate)?.shape;
            let Type::Array(key, _) = shape else {
                return Err(Error::InvalidCandidate);
            };
            if scalar_type(*index) != encoding.context.query.types.get(key)? {
                return Err(Error::InvalidCandidate);
            }
            read(arrays, *array, *index, model, owner).map(Value::Scalar)
        }
        _ => {
            scalar_args.clear();
            memory::reserve(scalar_args, args.len(), owner)?;
            for arg in args {
                let Value::Scalar(value) = arg else {
                    return Err(Error::Unsupported);
                };
                scalar_args.push(*value);
            }
            operations::apply(op, scalar_args, owner).map(Value::Scalar)
        }
    }
}

fn insert(arrays: &mut Vec<Array>, array: Array, owner: &CountedAdmission) -> Result<Value> {
    let index = arrays.len();
    memory::push(arrays, array, owner)?;
    Ok(Value::Array(index))
}

fn read(
    arrays: &[Array],
    mut at: usize,
    key: ScalarValue,
    model: &free::Model,
    owner: &CountedAdmission,
) -> Result<ScalarValue> {
    loop {
        owner.admit(1, 0)?;
        match arrays.get(at).ok_or(Error::InvalidCandidate)?.contents {
            Contents::Constant(fill) => return Ok(fill),
            Contents::Free(array) => return model.read(array, key, owner),
            Contents::Store { base, index, value } => {
                if key == index {
                    return Ok(value);
                }
                if base >= at {
                    return Err(Error::InvalidCandidate);
                }
                at = base;
            }
        }
    }
}

fn replay_reads(
    encoding: &ScalarEncoding<'_, '_>,
    native: &[Option<Value>],
    arrays: &[Array],
    model: &free::Model,
) -> Result<()> {
    let closure = encoding
        .array_read_obligations()
        .ok_or(Error::InvalidCandidate)?;
    if closure.reads().len() != model.observations().len() {
        return Err(Error::InvalidCandidate);
    }
    for (source, expected) in closure.reads().iter().zip(model.observations()) {
        encoding.admission().admit(1, 0)?;
        let Some(Value::Array(array)) = native.get(source.array.index()).copied().flatten() else {
            return Err(Error::InvalidCandidate);
        };
        let Some(Value::Scalar(index)) = native.get(source.index.index()).copied().flatten() else {
            return Err(Error::InvalidCandidate);
        };
        if index != expected.index
            || read(arrays, array, index, model, encoding.admission())? != expected.value
        {
            return Err(Error::InvalidCandidate);
        }
    }
    Ok(())
}

fn value_type(value: Value, arrays: &[Array]) -> Result<Type> {
    match value {
        Value::Scalar(value) => Ok(scalar_type(value)),
        Value::Array(index) => arrays
            .get(index)
            .map(|array| array.shape)
            .ok_or(Error::InvalidCandidate),
    }
}

fn scalar_type(value: ScalarValue) -> Type {
    match value {
        ScalarValue::Bool(_) => Type::Bool,
        ScalarValue::BitVec(_, width) => Type::BitVec(width),
    }
}
