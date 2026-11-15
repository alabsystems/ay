use veripb_formula::prelude::*;

#[test]
fn create_var() {
    let var = BooleanVar::new();

    assert_eq!(var.get_value(), BoolValue::Unassigned);
}

#[test]
fn var_set_get_value() {
    let mut var = BooleanVar::new();

    var.set_value(BoolValue::Assigned(true));
    assert_eq!(var.get_value(), BoolValue::Assigned(true));

    var.set_value(BoolValue::Assigned(false));
    assert_eq!(var.get_value(), BoolValue::Assigned(false));
}

#[test]
fn assign_and_unassign() {
    let mut var = BooleanVar::new();

    var.set_value(BoolValue::Assigned(true));
    assert_eq!(var.get_value(), BoolValue::Assigned(true));

    var.set_value(BoolValue::Unassigned);
    assert_eq!(var.get_value(), BoolValue::Unassigned);
}
