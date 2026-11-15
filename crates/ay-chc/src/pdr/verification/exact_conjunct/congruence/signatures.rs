// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::{Arena, Classes, Error, Key, Owner, Result};
use crate::ChcOp;
use std::collections::{hash_map::DefaultHasher, HashMap};
use std::hash::{Hash, Hasher};

#[derive(PartialEq, Eq, Hash)]
enum Signature {
    Op(usize, ChcOp, Vec<usize>),
    Array(usize, usize, usize),
}

impl Signature {
    fn weight(&self) -> Result<usize> {
        match self {
            Self::Op(_, _, children) => children.len().checked_add(3).ok_or(Error::Resource),
            Self::Array(..) => Ok(3),
        }
    }
}

pub(super) fn rebuild(arena: &Arena, classes: &mut Classes, owner: &mut Owner) -> Result<bool> {
    let mut table: HashMap<u64, Vec<(Signature, usize)>> = HashMap::new();
    let mut changed = false;
    for id in 0..arena.len() {
        owner.admit(1, 0)?;
        let Some(signature) = signature(arena, id, classes, owner)? else {
            continue;
        };
        let weight = signature.weight()?;
        owner.admit(weight, 0)?;
        let mut hasher = DefaultHasher::new();
        signature.hash(&mut hasher);
        let hash = hasher.finish();
        let mut previous = None;
        if let Some(bucket) = table.get(&hash) {
            for (candidate, candidate_id) in bucket {
                owner.admit(weight.max(candidate.weight()?), 0)?;
                if *candidate == signature {
                    previous = Some(*candidate_id);
                    break;
                }
            }
        }
        if let Some(previous) = previous {
            changed |= classes.union(id, previous, arena, owner)?;
        } else {
            owner.admit(1, 2 * std::mem::size_of::<(Signature, usize)>() + 256)?;
            table.try_reserve(1).map_err(|_| Error::Resource)?;
            let bucket = table.entry(hash).or_default();
            bucket.try_reserve(1).map_err(|_| Error::Resource)?;
            bucket.push((signature, id));
        }
    }
    Ok(changed)
}

fn signature(
    arena: &Arena,
    id: usize,
    classes: &mut Classes,
    owner: &mut Owner,
) -> Result<Option<Signature>> {
    let node = arena.node(id);
    Ok(Some(match &node.key {
        Key::Op(op, args) => {
            let bytes = args
                .len()
                .checked_mul(std::mem::size_of::<usize>())
                .ok_or(Error::Resource)?;
            owner.admit(args.len(), bytes)?;
            let mut children = Vec::new();
            children
                .try_reserve_exact(args.len())
                .map_err(|_| Error::Resource)?;
            for &arg in args {
                children.push(classes.root(arg, owner)?);
            }
            Signature::Op(node.sort, *op, children)
        }
        Key::ConstArray(index, value) => {
            Signature::Array(node.sort, *index, classes.root(*value, owner)?)
        }
        _ => return Ok(None),
    }))
}
