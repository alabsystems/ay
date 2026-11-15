// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use crate::counted_storage::{test_owner, try_reserve};

fn heap_fixture(order: &[u32]) -> VSIDS {
    let mut s = VSIDS::new(order.len());
    for (index, activity) in s.activities.iter_mut().enumerate() {
        *activity = index as f64;
    }
    s.heap.copy_from_slice(order);
    for (position, &variable) in order.iter().enumerate() {
        s.heap_pos[variable as usize] = position as u32;
    }
    s
}

fn permutations(values: &mut [u32], begin: usize, check: &mut impl FnMut(&[u32])) {
    if begin == values.len() {
        check(values);
        return;
    }
    for end in begin..values.len() {
        values.swap(begin, end);
        permutations(values, begin + 1, check);
        values.swap(begin, end);
    }
}

#[test]
fn fast_one_pop_bound_covers_every_small_heap_and_domain_skip() {
    for size in 1..=5 {
        permutations(&mut (0..size as u32).collect::<Vec<_>>(), 0, &mut |order| {
            if (1..size).any(|i| order[(i - 1) / 2] < order[i]) {
                return;
            }
            for assigned in 0usize..(1 << size) {
                let vals: Vec<_> = (0..size * 2)
                    .map(|i| i8::from(assigned & (1 << (i / 2)) != 0))
                    .collect();
                for removed in [false, true] {
                    let mut states = vec![VarState::Active; size];
                    if removed {
                        states[order[0] as usize] = VarState::Eliminated;
                    }
                    for mask in 0usize..(1 << size) {
                        let domain: Vec<_> = (0..size).map(|i| mask & (1 << i) != 0).collect();
                        check_domain_capacity(order, &vals, &states, &domain);
                    }
                }
            }
        });
    }
}

fn check_domain_capacity(order: &[u32], vals: &[i8], states: &[VarState], domain: &[bool]) {
    let mut actual = heap_fixture(order);
    let owner = test_owner(1_000_000, 1_000_000);
    let bound = actual
        .admit_heap_selection(vals, states, Some(domain), &owner)
        .unwrap();
    let mut skipped = Vec::new();
    try_reserve(&owner, &mut skipped, bound).unwrap();
    let scratch_capacity = skipped.capacity();
    let heap_capacity = actual.heap.capacity();
    let result = loop {
        match actual.pick_branching_variable(vals) {
            None => break None,
            Some(var) if states[var.index()].is_removed() => actual.remove_from_heap(var),
            Some(var) if domain[var.index()] => break Some(var),
            Some(var) => {
                actual.remove_from_heap(var);
                skipped.push(var);
                assert!(skipped.len() <= bound);
                assert_eq!(skipped.capacity(), scratch_capacity);
            }
        }
    };
    for var in skipped {
        actual.insert_into_heap(var);
    }
    assert_eq!(actual.heap.capacity(), heap_capacity);
    let expected = order
        .iter()
        .copied()
        .filter(|&var| {
            let i = var as usize;
            vals[i * 2] == 0 && !states[i].is_removed() && domain[i]
        })
        .max()
        .map(Variable::new);
    assert_eq!(result, expected);
    #[cfg(debug_assertions)]
    {
        actual.debug_assert_heap_property();
        actual.debug_assert_heap_pos_consistent();
    }
}

#[test]
fn normal_one_assigned_root_uses_logarithmic_not_whole_heap_debit() {
    let mut s = VSIDS::new(1024);
    for index in 0..1024 {
        s.set_activity(Variable::new(index), index as f64 + 1.0);
    }
    let root = s.heap[0] as usize;
    let mut vals = vec![0; 2048];
    vals[root * 2] = 1;
    let owner = test_owner(100, 0);
    assert_eq!(s.admit_heap_selection(&vals, &[], None, &owner), Ok(0));
    assert!(owner.usage().unwrap().work_admitted < 100);
    assert!(s.pick_branching_variable(&vals).is_some());
}

#[test]
fn vmtf_paid_wraparound_does_not_mutate_cursor_until_real_walk() {
    let mut s = VSIDS::new(6);
    s.vmtf_unassigned = s.vmtf_first;
    let mut vals = vec![1; 12];
    vals[s.vmtf_last as usize * 2] = 0;
    let before = format!("{s:?}");
    let owner = test_owner(1_000, 0);
    s.admit_vmtf_selection(&vals, &[], &owner).unwrap();
    assert_eq!(format!("{s:?}"), before);
    assert_eq!(
        s.pick_branching_variable_vmtf_with_lifecycle(&vals, &[]),
        Some(Variable::new(s.vmtf_last))
    );
    assert_eq!(owner.usage().unwrap().work_admitted, 5);
}

#[test]
fn exhausted_vmtf_admission_leaves_original_cursor_and_links() {
    let s = VSIDS::new(6);
    let before = format!("{s:?}");
    let owner = test_owner(2, 0);
    assert_eq!(
        s.admit_vmtf_selection(&[1; 12], &[], &owner),
        Err(CountedAdmissionError::WorkExhausted)
    );
    assert_eq!(format!("{s:?}"), before);
}
