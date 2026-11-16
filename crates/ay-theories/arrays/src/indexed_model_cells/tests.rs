// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use ay_core::original_query::StopReason;
use std::cell::Cell;
use std::ops::ControlFlow;
use std::rc::Rc;

fn cell<'a>(key: &'a str, value: &'a str) -> ModelCellRow<'a> {
    ModelCellRow {
        key: ModelCellKey::Text(key),
        value,
    }
}

fn checkpoint(end: std::time::Instant) -> impl FnMut() -> ControlFlow<StopReason> {
    move || {
        if std::time::Instant::now() >= end {
            ControlFlow::Break(StopReason::Deadline)
        } else {
            ControlFlow::Continue(())
        }
    }
}

fn text_rows<'a>(rows: &IndexedModelCellRows<'a>) -> Vec<(&'a str, &'a str)> {
    rows.rows()
        .iter()
        .map(|row| {
            let ModelCellKey::Text(key) = row.key else {
                panic!("text fixture")
            };
            (key, row.value)
        })
        .collect()
}

#[test]
fn duplicate_fifo_soft_override_and_first_poison_preserve_partial_authority() {
    let end = std::time::Instant::now() + std::time::Duration::from_secs(20);
    let mut stop = checkpoint(end);
    let mut budget = WorkBudget::new(1_000_000, &mut stop);
    let mut cells = IndexedModelCells::new(12, &mut budget).unwrap();
    for (key, value, authority) in [
        ("concrete", "9", CellAuthority::Concrete),
        ("soft", "0", CellAuthority::Soft),
        ("soft", "older", CellAuthority::Soft),
    ] {
        cells.push_original(cell(key, value), authority).unwrap();
    }
    for (key, value) in [
        ("concrete", "wrong"),
        ("soft", "9"),
        ("fresh", "2"),
        ("fresh", "2"),
        ("soft", "7"),
        ("soft", "9"),
        ("fresh", "3"),
        ("fresh", "2"),
    ] {
        cells.observe(cell(key, value)).unwrap();
    }
    // Poison removes ONLY the first FIFO row; the older duplicate remains.
    let result = cells.finish().unwrap();
    assert!(result.read_conflicted());
    assert_eq!(text_rows(&result), [("concrete", "9"), ("soft", "older")]);
}

#[test]
fn chronological_upsert_exhaustive_sequences_match_the_literal_vector() {
    let end = std::time::Instant::now() + std::time::Duration::from_secs(20);
    let mut stop = checkpoint(end);
    let mut budget = WorkBudget::new(20_000_000, &mut stop);
    let actions = [("a", "0"), ("b", "1"), ("a", "2"), ("c", "3")];
    for sequence in 0..4usize.pow(5) {
        let mut cells = IndexedModelCells::new(8, &mut budget).unwrap();
        let mut plain = vec![("a", "old"), ("a", "oldest"), ("d", "unchanged")];
        for &(key, value) in &plain {
            cells
                .push_original(cell(key, value), CellAuthority::Concrete)
                .unwrap();
        }
        let mut code = sequence;
        for _ in 0..5 {
            let (key, value) = actions[code % 4];
            code /= 4;
            if let Some(position) = plain.iter().position(|(stored, _)| *stored == key) {
                plain.remove(position);
            }
            plain.push((key, value));
            cells.upsert_newest(cell(key, value)).unwrap();
        }
        assert_eq!(
            text_rows(&cells.finish().unwrap()),
            plain,
            "sequence {sequence}"
        );
    }
}

#[test]
fn exact_texts_missing_only_merge_and_original_default_are_not_normalized() {
    let end = std::time::Instant::now() + std::time::Duration::from_secs(20);
    let mut stop = checkpoint(end);
    let mut budget = WorkBudget::new(1_000_000, &mut stop);
    let original = crate::ArrayInterpretation {
        default: Some("23".into()),
        stores: [
            ("#x01", "hex"),
            ("#b00000001", "binary"),
            ("1", "integer"),
            ("01", "symbol"),
        ]
        .into_iter()
        .map(|(k, v)| (k.into(), v.into()))
        .collect(),
        ..Default::default()
    };
    let mut cells = IndexedModelCells::new(5, &mut budget).unwrap();
    for (key, value) in &original.stores {
        cells
            .push_original(cell(key, value), CellAuthority::Concrete)
            .unwrap();
    }
    cells.insert_missing(cell("#x01", "weaker")).unwrap();
    cells.insert_missing(cell("new", "value")).unwrap();
    let rows = cells.finish().unwrap();
    assert_eq!(
        text_rows(&rows),
        [
            ("#x01", "hex"),
            ("#b00000001", "binary"),
            ("1", "integer"),
            ("01", "symbol"),
            ("new", "value")
        ]
    );
    assert_eq!(original.default.as_deref(), Some("23"));
}

#[test]
fn full_bigint_keys_distinguish_high_bits_widths_and_boolean_kind() {
    let end = std::time::Instant::now() + std::time::Duration::from_secs(20);
    let mut stop = checkpoint(end);
    let mut budget = WorkBudget::new(1_000_000, &mut stop);
    let low = BigInt::from(7);
    let high = (BigInt::from(1) << 255usize) + &low;
    let keys = [
        ModelCellKey::BitVec {
            width: 256,
            value: &low,
        },
        ModelCellKey::BitVec {
            width: 256,
            value: &high,
        },
        ModelCellKey::BitVec {
            width: 512,
            value: &high,
        },
        ModelCellKey::Bool(true),
    ];
    let mut cells = IndexedModelCells::new(4, &mut budget).unwrap();
    for (key, value) in keys.into_iter().zip(["low", "high", "wide", "bool"]) {
        cells
            .push_original(ModelCellRow { key, value }, CellAuthority::Concrete)
            .unwrap();
    }
    for (key, value) in keys.into_iter().zip(["low", "high", "wide", "bool"]) {
        assert_eq!(cells.first(key).unwrap().unwrap().value, value);
    }
    assert_eq!(cells.finish().unwrap().rows().len(), 4);
}

#[test]
fn sorted_adversarial_insertions_keep_avl_height_and_linear_population() {
    let end = std::time::Instant::now() + std::time::Duration::from_secs(20);
    let mut stop = checkpoint(end);
    let mut budget = WorkBudget::new(5_000_000, &mut stop);
    let keys: Vec<String> = (0..1024).map(|i| format!("{i:08}")).collect();
    let mut cells = IndexedModelCells::new(keys.len(), &mut budget).unwrap();
    for key in &keys {
        cells
            .push_original(cell(key, "value"), CellAuthority::Concrete)
            .unwrap();
    }
    assert_eq!(cells.rows.len(), keys.len());
    assert_eq!(cells.nodes.len(), keys.len());
    index::assert_balanced(&cells);
    assert_eq!(cells.finish().unwrap().rows().len(), keys.len());
}

#[test]
fn work_one_short_and_row_ceiling_refuse_on_the_same_terminal_ledger() {
    let end = std::time::Instant::now() + std::time::Duration::from_secs(20);
    let mut stop = checkpoint(end);
    let mut budget = WorkBudget::new(0, &mut stop);
    assert!(matches!(
        IndexedModelCells::new(1, &mut budget),
        Err(QueryError::Exhausted)
    ));
    assert_eq!(budget.charge(0), Err(QueryError::Exhausted));
    let mut budget = WorkBudget::new(1_000, &mut stop);
    let mut cells = IndexedModelCells::new(1, &mut budget).unwrap();
    cells
        .push_original(cell("a", "1"), CellAuthority::Concrete)
        .unwrap();
    assert_eq!(
        cells.upsert_newest(cell("a", "2")),
        Err(QueryError::Exhausted)
    );
    assert!(matches!(cells.finish(), Err(QueryError::Exhausted)));
    assert_eq!(budget.charge(0), Err(QueryError::Exhausted));
}

#[test]
fn storage_one_short_refuses_before_reservation_and_cannot_reset_per_array() {
    let end = std::time::Instant::now() + std::time::Duration::from_secs(20);
    let bytes = size_of::<Row<'_>>() + size_of::<Node<'_>>() + size_of::<ModelCellRow<'_>>();
    let mut remaining = bytes - 1;
    let mut admission = |_work: usize, bytes: usize| {
        if std::time::Instant::now() >= end {
            return Err(QueryError::Interrupted(StopReason::Deadline));
        }
        remaining = remaining.checked_sub(bytes).ok_or(QueryError::Exhausted)?;
        Ok(())
    };
    let mut budget = WorkBudget::with_admission(1_000, &mut admission);
    assert!(matches!(
        IndexedModelCells::new(1, &mut budget),
        Err(QueryError::Exhausted)
    ));
    assert!(matches!(
        IndexedModelCells::new(0, &mut budget),
        Err(QueryError::Exhausted)
    ));
    assert_eq!(budget.charge(0), Err(QueryError::Exhausted));
}

#[test]
fn checked_capacity_overflow_and_large_full_key_comparison_are_terminal() {
    let end = std::time::Instant::now() + std::time::Duration::from_secs(20);
    let mut stop = checkpoint(end);
    let mut budget = WorkBudget::new(u64::MAX, &mut stop);
    assert!(matches!(
        IndexedModelCells::new(usize::MAX, &mut budget),
        Err(QueryError::Exhausted)
    ));
    assert_eq!(budget.charge(0), Err(QueryError::Exhausted));
    let mut budget = WorkBudget::new(300, &mut stop);
    let large = "a".repeat(4096);
    let mut cells = IndexedModelCells::new(1, &mut budget).unwrap();
    cells
        .push_original(cell(&large, "1"), CellAuthority::Concrete)
        .unwrap();
    assert_eq!(
        cells.first(ModelCellKey::Text(&large)).err(),
        Some(QueryError::Exhausted)
    );
    assert!(matches!(cells.finish(), Err(QueryError::Exhausted)));
}

#[test]
fn expired_original_deadline_and_observed_raw_reset_cannot_publish() {
    let mut stop = checkpoint(std::time::Instant::now());
    let mut budget = WorkBudget::new(1_000, &mut stop);
    assert!(matches!(
        IndexedModelCells::new(1, &mut budget),
        Err(QueryError::Interrupted(StopReason::Deadline))
    ));
    let raw = Rc::new(Cell::new(false));
    let observed = Rc::clone(&raw);
    let end = std::time::Instant::now() + std::time::Duration::from_secs(20);
    let mut stop = move || {
        if observed.get() {
            ControlFlow::Break(StopReason::Cancelled)
        } else if std::time::Instant::now() >= end {
            ControlFlow::Break(StopReason::Deadline)
        } else {
            ControlFlow::Continue(())
        }
    };
    let mut budget = WorkBudget::new(1_000, &mut stop);
    let mut cells = IndexedModelCells::new(1, &mut budget).unwrap();
    cells
        .push_original(cell("a", "1"), CellAuthority::Concrete)
        .unwrap();
    raw.set(true);
    assert_eq!(
        cells.first(ModelCellKey::Text("a")).err(),
        Some(QueryError::Interrupted(StopReason::Cancelled))
    );
    raw.set(false);
    assert!(matches!(
        cells.finish(),
        Err(QueryError::Interrupted(StopReason::Cancelled))
    ));
    assert_eq!(
        budget.charge(0),
        Err(QueryError::Interrupted(StopReason::Cancelled))
    );
}

#[test]
fn final_poll_after_scratch_disposal_vetoes_publication() {
    let end = std::time::Instant::now() + std::time::Duration::from_secs(20);
    let armed = Rc::new(Cell::new(false));
    let disposed = Rc::new(Cell::new(false));
    let arm = Rc::clone(&armed);
    let disposition = Rc::clone(&disposed);
    let mut admission = move |units: usize, _bytes: usize| {
        if std::time::Instant::now() >= end {
            return Err(QueryError::Interrupted(StopReason::Deadline));
        }
        if disposition.get() {
            return Err(QueryError::Interrupted(StopReason::Cancelled));
        }
        if arm.get() && units == 2 {
            disposition.set(true);
        }
        Ok(())
    };
    let mut budget = WorkBudget::with_admission(1_000, &mut admission);
    let mut cells = IndexedModelCells::new(1, &mut budget).unwrap();
    cells
        .push_original(cell("a", "1"), CellAuthority::Concrete)
        .unwrap();
    armed.set(true);
    assert!(matches!(
        cells.finish(),
        Err(QueryError::Interrupted(StopReason::Cancelled))
    ));
    assert!(disposed.get());
    assert_eq!(
        budget.charge(0),
        Err(QueryError::Interrupted(StopReason::Cancelled))
    );
}
