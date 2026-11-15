use veripb_formula::prelude::*;

#[test]
fn add_var() {
    let mut var_set = VarNameManager::default();

    assert_eq!(var_set.add_by_name("x1"), 0);
}

#[test]
fn add_var_and_get_name() {
    let mut var_set = VarNameManager::default();
    let var = var_set.add_by_name("x1");

    assert_eq!(var_set.get_name(var), "x1");
}

#[test]
fn add_same_var() {
    let mut var_set = VarNameManager::default();

    assert_eq!(var_set.add_by_name("x1"), 0);
    assert_eq!(var_set.add_by_name("x1"), 0);
    assert_eq!(var_set.len(), 1);
}

#[test]
fn add_hundred_thousand_vars() {
    const NUMBER_VARS: usize = 100_000;
    let mut var_set = VarNameManager::with_capacity(NUMBER_VARS);
    for idx in 0..NUMBER_VARS {
        var_set.add_by_name(&idx.to_string());
    }

    assert_eq!(var_set.len(), NUMBER_VARS)
}

/// Test if variable pointer still points to the same variable after adding 1000 variables.
#[test]
fn persistence_after_adding_thousand() {
    const NUMBER_VARS: usize = 1_000;
    let mut var_set = VarNameManager::with_capacity(NUMBER_VARS);
    let var = var_set.add_by_name("x1");

    for idx in 0..NUMBER_VARS {
        var_set.add_by_name(&idx.to_string());
    }

    assert_eq!(var_set.get_name(var), "x1")
}

#[test]
fn add_hundred_thousand_same_vars() {
    const NUMBER_VARS: usize = 100_000;
    let mut var_set = VarNameManager::with_capacity(1);
    for _ in 0..NUMBER_VARS {
        var_set.add_by_name("x1");
    }

    assert_eq!(var_set.len(), 1)
}

#[test]
fn new_var_set() {
    let var_set = VarNameManager::default();

    assert_eq!(var_set.len(), 0);
}

#[test]
fn new_var_set_with_capacity() {
    const NUMBER_VARS: usize = 100_000;
    let var_set = VarNameManager::with_capacity(NUMBER_VARS);

    assert_eq!(var_set.len(), 0);
}
