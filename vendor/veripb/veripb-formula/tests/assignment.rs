use veripb_formula::prelude::*;

const SIZE: usize = 42;
const BIG_SIZE: usize = 420;
const VAR: VarIdx = 12;

#[test]
fn empty() {
    let assign: Assignment<BooleanVar> = Assignment::default();

    assert_eq!(assign.len(), 0);
}

#[test]
fn init_with_size() {
    let assign: Assignment<BooleanVar> = Assignment::with_size(SIZE);

    assert_eq!(assign.len(), SIZE);
}

#[test]
fn increase_size() {
    let mut assign: Assignment<BooleanVar> = Assignment::with_size(SIZE);
    assign.resize(BIG_SIZE);

    assert_eq!(assign.len(), BIG_SIZE);
}

#[test]
fn reduce_size() {
    let mut assign: Assignment<BooleanVar> = Assignment::with_size(BIG_SIZE);
    assign.resize(SIZE);

    assert_eq!(assign.len(), SIZE);
}

#[test]
fn set_get_by_var() {
    let mut assign: Assignment<BooleanVar> = Assignment::with_size(SIZE);
    assert_eq!(assign.get_value(VAR), BoolValue::Unassigned);

    assign.set_value(VAR, BoolValue::Assigned(false));
    assert_eq!(assign.get_value(VAR), BoolValue::Assigned(false));

    assign.set_value(VAR, BoolValue::Assigned(true));
    assert_eq!(assign.get_value(VAR), BoolValue::Assigned(true));
}

#[test]
fn set_get_by_lit() {
    let mut assign: Assignment<BooleanVar> = Assignment::with_size(BIG_SIZE);
    let lit = Lit::from_var(VAR, false);
    assert_eq!(assign.get_lit_value(lit), BoolValue::Unassigned);

    assign.set_lit_value(lit, BoolValue::Assigned(false));
    assert_eq!(assign.get_lit_value(lit), BoolValue::Assigned(false));
    assert_eq!(assign.get_value(VAR), BoolValue::Assigned(false));

    assign.set_lit_value(lit, BoolValue::Assigned(true));
    assert_eq!(assign.get_lit_value(lit), BoolValue::Assigned(true));
    assert_eq!(assign.get_value(VAR), BoolValue::Assigned(true));
}

#[test]
fn set_get_by_negated_lit() {
    let mut assign: Assignment<BooleanVar> = Assignment::with_size(BIG_SIZE);
    let lit = Lit::from_var(VAR, true);
    assert_eq!(assign.get_lit_value(lit), BoolValue::Unassigned);

    assign.set_lit_value(lit, BoolValue::Assigned(false));
    assert_eq!(assign.get_lit_value(lit), BoolValue::Assigned(false));
    assert_eq!(assign.get_value(VAR), BoolValue::Assigned(true));

    assign.set_lit_value(lit, BoolValue::Assigned(true));
    assert_eq!(assign.get_lit_value(lit), BoolValue::Assigned(true));
    assert_eq!(assign.get_value(VAR), BoolValue::Assigned(false));
}

#[test]
fn set_by_var_get_by_lit() {
    let mut assign: Assignment<BooleanVar> = Assignment::with_size(BIG_SIZE);
    let lit = Lit::from_var(VAR, true);

    assign.set_value(VAR, BoolValue::Assigned(false));
    assert_eq!(assign.get_lit_value(lit), BoolValue::Assigned(true));

    assign.set_value(VAR, BoolValue::Assigned(true));
    assert_eq!(assign.get_lit_value(lit), BoolValue::Assigned(false));
}

// The three unchecked accessors on `Assignment` share one safety contract — the literal's
// variable index must be *strictly* less than the assignment's length — and each states it as a
// `debug_assert!`, so that a caller which gets it wrong is a loud debug failure rather than a
// silent out-of-bounds read in release. These tests pin that the assertion is actually there:
// they run only in a debug build, because in release there is no assertion to fire and the call
// would be genuine undefined behaviour.
//
// `is_unassigned_unchecked` shipped without its assertion while its two siblings carried theirs;
// `is_unassigned_at_the_length_is_a_debug_failure` is the test that was missing with it.

#[test]
#[cfg(debug_assertions)]
#[should_panic = "lit.get_var() < self.assignment.len()"]
fn is_unassigned_at_the_length_is_a_debug_failure() {
    let assign: Assignment<BooleanVar> = Assignment::with_size(SIZE);
    // SAFETY: deliberately violated. `SIZE` is the first index with no slot, i.e. the smallest
    // overrun the contract forbids; the `debug_assert!` must catch it before the read happens.
    let _ = unsafe { assign.is_unassigned_unchecked(Lit::from_var(SIZE, false)) };
}

#[test]
#[cfg(debug_assertions)]
#[should_panic = "lit.get_var() < self.assignment.len()"]
fn get_lit_value_at_the_length_is_a_debug_failure() {
    let assign: Assignment<BooleanVar> = Assignment::with_size(SIZE);
    // SAFETY: deliberately violated, as above.
    let _ = unsafe { assign.get_lit_value_unchecked(Lit::from_var(SIZE, false)) };
}

#[test]
#[cfg(debug_assertions)]
#[should_panic = "lit.get_var() < self.assignment.len()"]
fn set_lit_value_at_the_length_is_a_debug_failure() {
    let mut assign: Assignment<BooleanVar> = Assignment::with_size(SIZE);
    // SAFETY: deliberately violated, as above.
    unsafe {
        assign.set_lit_value_unchecked(Lit::from_var(SIZE, false), BoolValue::Assigned(true))
    };
}

#[test]
fn is_unassigned_below_the_length_is_allowed() {
    // The positive control: the largest in-range index must still work, so the assertion is a
    // bound and not an off-by-one that would fire on legitimate calls.
    let mut assign: Assignment<BooleanVar> = Assignment::with_size(SIZE);
    let lit = Lit::from_var(SIZE - 1, false);
    assert!(unsafe { assign.is_unassigned_unchecked(lit) });
    assign.set_lit_value(lit, BoolValue::Assigned(true));
    assert!(!unsafe { assign.is_unassigned_unchecked(lit) });
}
