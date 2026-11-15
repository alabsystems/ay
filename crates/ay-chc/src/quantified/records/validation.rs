// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

/// Header comparison only, after complete structural/declaration admission.
pub(super) fn same_sort(left: &ChcSort, right: &ChcSort) -> bool {
    let (mut left, mut right) = (left, right);
    loop {
        match (left, right) {
            (ChcSort::Datatype { name: left, .. }, ChcSort::Datatype { name: right, .. }) => {
                return left == right;
            }
            (ChcSort::Bool, ChcSort::Bool) => return true,
            (ChcSort::BitVec(left), ChcSort::BitVec(right)) => return left == right,
            (ChcSort::Array(lk, lv), ChcSort::Array(rk, rv)) => {
                if !matches!((lk.as_ref(), rk.as_ref()), (ChcSort::BitVec(l), ChcSort::BitVec(r)) if l == r)
                {
                    return false;
                }
                (left, right) = (lv, rv);
            }
            _ => return false,
        }
    }
}

impl Registry {
    pub(crate) fn validate_sort(&self, sort: &ChcSort) -> ChcResult<()> {
        sort_bytes(sort).ok_or_else(|| invalid("unsupported or oversized sort"))?;
        let mut pending = vec![sort];
        while let Some(sort) = pending.pop() {
            if let ChcSort::Array(_, value) = sort {
                pending.push(value);
                continue;
            }
            let ChcSort::Datatype { name, constructors } = sort else {
                continue;
            };
            let ChcSort::Datatype {
                constructors: expected,
                ..
            } = self
                .lookup(name)
                .ok_or_else(|| invalid("undeclared embedded record"))?
            else {
                return Err(invalid("registry record"));
            };
            let [actual] = constructors.as_slice() else {
                return Err(invalid("record constructor"));
            };
            let [expected] = expected.as_slice() else {
                return Err(invalid("registry constructor"));
            };
            if actual.name != expected.name || actual.selectors.len() != expected.selectors.len() {
                return Err(invalid("record metadata disagrees with declaration"));
            }
            for (actual, expected) in actual.selectors.iter().zip(&expected.selectors) {
                if actual.name != expected.name || !same_sort(&actual.sort, &expected.sort) {
                    return Err(invalid("embedded record field metadata disagreement"));
                }
            }
            pending
                .try_reserve(actual.selectors.len())
                .map_err(|_| invalid("record validation allocation"))?;
            pending.extend(actual.selectors.iter().map(|field| &field.sort));
        }
        Ok(())
    }

    pub(super) fn validate_definitions(&self) -> ChcResult<()> {
        // Validate every embedded occurrence, including unused declarations.
        for record in &self.records {
            self.validate_sort(record)?;
        }
        let mut indegree = vec![0usize; self.records.len()];
        let mut edges = vec![Vec::new(); self.records.len()];
        for (index, record) in self.records.iter().enumerate() {
            let ChcSort::Datatype { constructors, .. } = record else {
                return Err(invalid("registry record"));
            };
            let [constructor] = constructors.as_slice() else {
                return Err(invalid("registry constructor"));
            };
            for field in &constructor.selectors {
                let mut sort = &field.sort;
                while let ChcSort::Array(_, value) = sort {
                    sort = value;
                }
                if let ChcSort::Datatype { name, .. } = sort {
                    let target = *self
                        .names
                        .get(name)
                        .ok_or_else(|| invalid("missing record dependency"))?;
                    edges[index].push(target);
                    indegree[target] += 1;
                }
            }
        }
        let mut ready: Vec<_> = indegree
            .iter()
            .enumerate()
            .filter_map(|(i, n)| (*n == 0).then_some(i))
            .collect();
        let mut removed = 0usize;
        while let Some(index) = ready.pop() {
            removed += 1;
            for target in &edges[index] {
                indegree[*target] -= 1;
                if indegree[*target] == 0 {
                    ready.push(*target);
                }
            }
        }
        if removed != self.records.len() {
            return Err(invalid("recursive record dependency"));
        }
        Ok(())
    }
}
