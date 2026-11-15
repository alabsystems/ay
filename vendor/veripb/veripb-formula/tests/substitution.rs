use veripb_formula::{prelude::*, substitution::Substitutable};

#[test]
fn add_values() {
    let mut sub = Substitution::default();

    sub.set(0, SubstitutionValue::TRUE);
    sub.set(1, SubstitutionValue::FALSE);
    sub.set(2, SubstitutionValue::lit(Lit::from_var(1, false)));

    assert_eq!(sub.len(), 3);
}

#[test]
fn get_value() {
    let mut sub = Substitution::default();

    sub.set(42, SubstitutionValue::FALSE);
    sub.set(41, SubstitutionValue::lit(Lit::from_var(42, true)));

    assert_eq!(sub.get(43), None);
    assert_eq!(
        sub.get(41),
        Some(SubstitutionValue::lit(Lit::from_var(42, true)))
    );
    assert_eq!(sub.get(42), Some(SubstitutionValue::FALSE));
}

#[test]
fn change_substitution() {
    let mut sub = Substitution::default();

    sub.set(42, SubstitutionValue::FALSE);
    assert_eq!(sub.get(42), Some(SubstitutionValue::FALSE));

    sub.set(42, SubstitutionValue::lit(Lit::from_var(41, false)));
    assert_eq!(
        sub.get(42),
        Some(SubstitutionValue::lit(Lit::from_var(41, false)))
    );
}

#[test]
fn get_value_by_lit() {
    let mut sub = Substitution::default();

    sub.set(42, SubstitutionValue::TRUE);
    sub.set(41, SubstitutionValue::lit(Lit::from_var(1, false)));

    assert_eq!(
        sub.get_lit(Lit::from_var(42, false)),
        Some(SubstitutionValue::TRUE)
    );
    assert_eq!(
        sub.get_lit(Lit::from_var(42, true)),
        Some(SubstitutionValue::FALSE)
    );
    assert_eq!(
        sub.get_lit(Lit::from_var(41, false)),
        Some(SubstitutionValue::lit(Lit::from_var(1, false)))
    );
    assert_eq!(
        sub.get_lit(Lit::from_var(41, true)),
        Some(SubstitutionValue::lit(Lit::from_var(1, true)))
    );
}
