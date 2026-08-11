// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

#[test]
fn prefetch_null_is_safe() {
    // Prefetching null must not panic or fault.
    prefetch_read_l2(core::ptr::null::<u8>());
}

#[test]
fn prefetch_valid_address() {
    let data = [1u64; 16];
    prefetch_read_l2(data.as_ptr());
}

#[test]
fn prefetch_stack_address() {
    let x = 42u32;
    prefetch_read_l2(&raw const x);
}

#[test]
fn val_at_in_bounds() {
    let vals: Vec<i8> = vec![0, 1, -1, 0, 1, -1];
    assert_eq!(val_at(&vals, 0), 0);
    assert_eq!(val_at(&vals, 1), 1);
    assert_eq!(val_at(&vals, 2), -1);
    assert_eq!(val_at(&vals, 5), -1);
}

#[test]
#[should_panic(expected = "out of bounds")]
fn val_at_out_of_bounds_panics() {
    let vals: Vec<i8> = vec![0, 1, -1];
    let _ = val_at(&vals, 3);
}

#[test]
fn word_at_in_bounds() {
    let words: Vec<u32> = vec![10, 20, 30, 40];
    assert_eq!(word_at(&words, 0), 10);
    assert_eq!(word_at(&words, 3), 40);
}

#[test]
#[should_panic(expected = "out of bounds")]
fn word_at_out_of_bounds_panics() {
    let words: Vec<u32> = vec![10, 20];
    let _ = word_at(&words, 2);
}

#[test]
fn entry_at_in_bounds() {
    let entries: Vec<u64> = vec![0xDEAD_BEEF_0000_0001, 0x1234_5678_9ABC_DEF0];
    assert_eq!(entry_at(&entries, 0), 0xDEAD_BEEF_0000_0001);
    assert_eq!(entry_at(&entries, 1), 0x1234_5678_9ABC_DEF0);
}

#[test]
#[should_panic(expected = "out of bounds")]
fn entry_at_out_of_bounds_panics() {
    let entries: Vec<u64> = vec![42];
    let _ = entry_at(&entries, 1);
}

#[test]
fn entry_set_in_bounds() {
    let mut entries: Vec<u64> = vec![0, 0];
    entry_set(&mut entries, 0, 0xCAFE);
    entry_set(&mut entries, 1, 0xBABE);
    assert_eq!(entries[0], 0xCAFE);
    assert_eq!(entries[1], 0xBABE);
}

#[test]
#[should_panic(expected = "out of bounds")]
fn entry_set_out_of_bounds_panics() {
    let mut entries: Vec<u64> = vec![0];
    entry_set(&mut entries, 1, 42);
}

// --- Tests for raw pointer helpers (#7989) ---

#[test]
fn prefetch_l1_null_is_safe() {
    prefetch_read_l1(core::ptr::null::<u8>());
}

#[test]
fn prefetch_l1_valid_address() {
    let data = [1u64; 16];
    prefetch_read_l1(data.as_ptr());
}

#[test]
fn watch_iter_raw_pointers() {
    let mut entries: Vec<u64> = vec![10, 20, 30];
    let (begin, end) = watch_iter_raw(&mut entries);
    assert!(!begin.is_null());
    // end - begin should equal entries.len()
    let count = unsafe { end.offset_from(begin.cast_const()) } as usize;
    assert_eq!(count, 3);
}

#[test]
fn watch_iter_raw_empty() {
    let mut entries: Vec<u64> = vec![];
    let (begin, end) = watch_iter_raw(&mut entries);
    assert_eq!(begin.cast_const(), end);
}

#[test]
fn arena_literal_raw_reads_correct() {
    // Simulate arena: 5 header words + 3 literal words
    let words: Vec<u32> = vec![3, 0, 2, 0, 0, 100, 200, 300];
    let ptr = words.as_ptr();
    let len = words.len();
    unsafe {
        assert_eq!(arena_literal_raw(ptr, 0, 5, 0, len), 100);
        assert_eq!(arena_literal_raw(ptr, 0, 5, 1, len), 200);
        assert_eq!(arena_literal_raw(ptr, 0, 5, 2, len), 300);
    }
}

#[test]
fn arena_header_word_raw_reads_correct() {
    let words: Vec<u32> = vec![3, 42, 0x0002_0000, 0, 0, 100, 200, 300];
    let ptr = words.as_ptr();
    let len = words.len();
    unsafe {
        assert_eq!(arena_header_word_raw(ptr, 0, 0, len), 3); // len
        assert_eq!(arena_header_word_raw(ptr, 0, 1, len), 42); // activity
        assert_eq!(arena_header_word_raw(ptr, 0, 2, len), 0x0002_0000); // saved_pos | flags
    }
}

#[test]
fn val_raw_reads_correct() {
    let vals: Vec<i8> = vec![0, 1, -1, 0, 1, -1];
    let ptr = vals_ptr(&vals);
    let len = vals.len();
    unsafe {
        assert_eq!(val_raw(ptr, 0, len), 0);
        assert_eq!(val_raw(ptr, 1, len), 1);
        assert_eq!(val_raw(ptr, 2, len), -1);
        assert_eq!(val_raw(ptr, 5, len), -1);
    }
}

#[test]
fn vec_set_len_truncates() {
    let mut v: Vec<u64> = vec![1, 2, 3, 4, 5];
    unsafe { vec_set_len(&mut v, 3) };
    assert_eq!(v.len(), 3);
    assert_eq!(v, vec![1, 2, 3]);
}

#[test]
fn vec_set_len_zero() {
    let mut v: Vec<u64> = vec![1, 2, 3];
    unsafe { vec_set_len(&mut v, 0) };
    assert_eq!(v.len(), 0);
    assert!(v.is_empty());
}

// --- Tests for SoA watch helpers (#8243, #8548) ---

#[test]
fn blocker_at_in_bounds() {
    let blockers: Vec<u32> = vec![10, 20, 30];
    assert_eq!(blocker_at(&blockers, 0), 10);
    assert_eq!(blocker_at(&blockers, 2), 30);
}

#[test]
#[should_panic(expected = "out of bounds")]
fn blocker_at_out_of_bounds_panics() {
    let blockers: Vec<u32> = vec![10, 20];
    let _ = blocker_at(&blockers, 2);
}

#[test]
fn blocker_set_in_bounds() {
    let mut blockers: Vec<u32> = vec![0, 0, 0];
    blocker_set(&mut blockers, 0, 42);
    blocker_set(&mut blockers, 2, 99);
    assert_eq!(blockers[0], 42);
    assert_eq!(blockers[2], 99);
}

#[test]
#[should_panic(expected = "out of bounds")]
fn blocker_set_out_of_bounds_panics() {
    let mut blockers: Vec<u32> = vec![0];
    blocker_set(&mut blockers, 1, 42);
}

#[test]
fn clause_ref_at_in_bounds() {
    let clause_refs: Vec<u64> = vec![100, 200, 300];
    assert_eq!(clause_ref_at(&clause_refs, 0), 100);
    assert_eq!(clause_ref_at(&clause_refs, 2), 300);
}

#[test]
#[should_panic(expected = "out of bounds")]
fn clause_ref_at_out_of_bounds_panics() {
    let clause_refs: Vec<u64> = vec![100];
    let _ = clause_ref_at(&clause_refs, 1);
}

#[test]
fn clause_ref_set_in_bounds() {
    let mut clause_refs: Vec<u64> = vec![0, 0];
    clause_ref_set(&mut clause_refs, 0, 500);
    clause_ref_set(&mut clause_refs, 1, 600);
    assert_eq!(clause_refs[0], 500);
    assert_eq!(clause_refs[1], 600);
}

#[test]
#[should_panic(expected = "out of bounds")]
fn clause_ref_set_out_of_bounds_panics() {
    let mut clause_refs: Vec<u64> = vec![0];
    clause_ref_set(&mut clause_refs, 1, 42);
}

#[test]
fn val_set_in_bounds() {
    let mut vals: Vec<i8> = vec![0, 0, 0, 0];
    val_set(&mut vals, 0, 1);
    val_set(&mut vals, 1, -1);
    assert_eq!(vals[0], 1);
    assert_eq!(vals[1], -1);
    assert_eq!(vals[2], 0);
}

#[test]
#[should_panic(expected = "out of bounds")]
fn val_set_out_of_bounds_panics() {
    let mut vals: Vec<i8> = vec![0, 0];
    val_set(&mut vals, 2, 1);
}

#[test]
fn prefetch_arena_at_in_bounds() {
    let words: Vec<u32> = vec![1, 2, 3, 4, 5];
    // Should not panic even though it's just a hint.
    prefetch_arena_at(&words, 0);
    prefetch_arena_at(&words, 4);
}

#[test]
fn prefetch_arena_at_out_of_bounds_no_fault() {
    // Prefetch is a no-op for out-of-bounds — the CPU silently ignores it.
    let words: Vec<u32> = vec![1, 2, 3];
    prefetch_arena_at(&words, 100);
}

#[test]
fn prefetch_val_l1_no_fault() {
    let vals: Vec<i8> = vec![0, 1, -1, 0];
    prefetch_val_l1(&vals, 0);
    prefetch_val_l1(&vals, 3);
    // Out of bounds is fine -- prefetch never faults.
    prefetch_val_l1(&vals, 100);
}

// --- Debug-mode OOB panic tests for raw pointer helpers ---

#[test]
#[cfg(debug_assertions)]
#[should_panic(expected = "out of bounds")]
fn arena_literal_raw_oob_panics_in_debug() {
    let words: Vec<u32> = vec![3, 0, 2, 0, 0, 100, 200, 300];
    let ptr = words.as_ptr();
    let len = words.len();
    // lit_index 3 is OOB: offset(0) + header(5) + lit(3) = 8 == len
    unsafe {
        let _ = arena_literal_raw(ptr, 0, 5, 3, len);
    }
}

#[test]
#[cfg(debug_assertions)]
#[should_panic(expected = "out of bounds")]
fn arena_header_word_raw_oob_panics_in_debug() {
    let words: Vec<u32> = vec![3, 42, 0x0002_0000];
    let ptr = words.as_ptr();
    let len = words.len();
    // word_index 3 is OOB: offset(0) + word(3) = 3 == len
    unsafe {
        let _ = arena_header_word_raw(ptr, 0, 3, len);
    }
}

#[test]
#[cfg(debug_assertions)]
#[should_panic(expected = "out of bounds")]
fn val_raw_oob_panics_in_debug() {
    let vals: Vec<i8> = vec![0, 1, -1];
    let ptr = vals_ptr(&vals);
    let len = vals.len();
    unsafe {
        let _ = val_raw(ptr, 3, len);
    }
}

// --- Edge case: single-element slices ---

#[test]
fn val_at_single_element() {
    let vals: Vec<i8> = vec![42];
    assert_eq!(val_at(&vals, 0), 42);
}

#[test]
fn word_at_single_element() {
    let words: Vec<u32> = vec![999];
    assert_eq!(word_at(&words, 0), 999);
}

#[test]
fn entry_at_single_element() {
    let entries: Vec<u64> = vec![0xFFFF_FFFF_FFFF_FFFF];
    assert_eq!(entry_at(&entries, 0), 0xFFFF_FFFF_FFFF_FFFF);
}

#[test]
fn blocker_at_single_element() {
    let blockers: Vec<u32> = vec![7];
    assert_eq!(blocker_at(&blockers, 0), 7);
}

#[test]
fn clause_ref_at_single_element() {
    let clause_refs: Vec<u64> = vec![42];
    assert_eq!(clause_ref_at(&clause_refs, 0), 42);
}

// --- Edge case: last valid index ---

#[test]
fn val_at_last_index() {
    let vals: Vec<i8> = vec![10, 20, 30, 40, 50];
    assert_eq!(val_at(&vals, 4), 50);
}

#[test]
fn val_set_last_index() {
    let mut vals: Vec<i8> = vec![0; 5];
    val_set(&mut vals, 4, 127);
    assert_eq!(vals[4], 127);
}

#[test]
fn entry_set_last_index() {
    let mut entries: Vec<u64> = vec![0; 3];
    entry_set(&mut entries, 2, 0xDEAD);
    assert_eq!(entries[2], 0xDEAD);
}

#[test]
fn blocker_set_last_index() {
    let mut blockers: Vec<u32> = vec![0; 4];
    blocker_set(&mut blockers, 3, 77);
    assert_eq!(blockers[3], 77);
}

#[test]
fn clause_ref_set_last_index() {
    let mut clause_refs: Vec<u64> = vec![0; 2];
    clause_ref_set(&mut clause_refs, 1, 888);
    assert_eq!(clause_refs[1], 888);
}

// --- Edge case: arena with non-zero clause_offset ---

#[test]
fn arena_literal_raw_nonzero_offset() {
    // Two clauses: [3,0,0,0,0, 10,20,30] [2,0,0,0,0, 40,50]
    let words: Vec<u32> = vec![3, 0, 0, 0, 0, 10, 20, 30, 2, 0, 0, 0, 0, 40, 50];
    let ptr = words.as_ptr();
    let len = words.len();
    unsafe {
        // Second clause at offset 8, header 5, lit 0 => index 13
        assert_eq!(arena_literal_raw(ptr, 8, 5, 0, len), 40);
        assert_eq!(arena_literal_raw(ptr, 8, 5, 1, len), 50);
    }
}

#[test]
fn arena_header_word_raw_nonzero_offset() {
    let words: Vec<u32> = vec![3, 0, 0, 0, 0, 10, 20, 30, 2, 99, 0, 0, 0, 40, 50];
    let ptr = words.as_ptr();
    let len = words.len();
    unsafe {
        assert_eq!(arena_header_word_raw(ptr, 8, 0, len), 2);
        assert_eq!(arena_header_word_raw(ptr, 8, 1, len), 99);
    }
}

// --- vec_set_len debug_assert ---

#[test]
#[cfg(debug_assertions)]
#[should_panic(expected = "capacity")]
fn vec_set_len_oob_panics_in_debug() {
    let mut v: Vec<u64> = vec![1, 2, 3];
    // capacity is at least 3 but we ask for 100
    unsafe { vec_set_len(&mut v, 100) };
}

// --- Prefetch with empty slices ---

#[test]
fn prefetch_arena_at_empty_slice() {
    let words: Vec<u32> = vec![];
    // Should not panic -- prefetch never faults, even on empty slices.
    prefetch_arena_at(&words, 0);
}

#[test]
fn prefetch_arena_at_l1_empty_slice() {
    let words: Vec<u32> = vec![];
    prefetch_arena_at_l1(&words, 0);
}

#[test]
fn prefetch_val_l1_empty_slice() {
    let vals: Vec<i8> = vec![];
    prefetch_val_l1(&vals, 0);
}
