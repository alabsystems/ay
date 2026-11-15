// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

pub(super) struct NamePlan {
    pub candidate: u32,
    pub key_bytes: usize,
}

fn include_name(candidate: &mut u32, name: &str) -> Result<()> {
    let Some(suffix) = name.strip_prefix(PREFIX) else {
        return Ok(());
    };
    // Generated decimal suffixes have <=10 ASCII bytes. Other spellings cannot
    // equal a generated name; never parse/copy unbounded caller text.
    if suffix.is_empty() || suffix.len() > 10 || !suffix.bytes().all(|b| b.is_ascii_digit()) {
        return Ok(());
    }
    if let Ok(value) = suffix.parse::<u32>() {
        let after = value
            .checked_add(1)
            .ok_or(ControlledTermInternError::ResourceLimit)?;
        *candidate = (*candidate).max(after);
    }
    Ok(())
}

fn include_term(candidate: &mut u32, term: &TermData, admission: &mut Admission<'_>) -> Result<()> {
    match term {
        TermData::Var(name, id) => {
            let after = id
                .checked_add(1)
                .ok_or(ControlledTermInternError::ResourceLimit)?;
            *candidate = (*candidate).max(after);
            include_name(candidate, name)
        }
        TermData::App(symbol, _) => include_name(candidate, symbol.name()),
        TermData::Let(bindings, _) => {
            for (name, _) in bindings {
                admission.pay(64, 0)?;
                include_name(candidate, name)?;
            }
            Ok(())
        }
        TermData::Forall(bindings, _, _) | TermData::Exists(bindings, _, _) => {
            for (name, _) in bindings {
                admission.pay(64, 0)?;
                include_name(candidate, name)?;
            }
            Ok(())
        }
        TermData::Const(_) | TermData::Not(_) | TermData::Ite(_, _, _) => Ok(()),
    }
}

pub(super) fn scan(store: &TermStore, admission: &mut Admission<'_>) -> Result<NamePlan> {
    admission.pay(16, 0)?;
    let mut candidate = store.var_counter;
    candidate
        .checked_add(1)
        .ok_or(ControlledTermInternError::ResourceLimit)?;
    // Iteration can cross empty/tombstone groups; prepay actual table storage.
    registry::probe(store, admission)?;
    let mut key_bytes = 0usize;
    for name in store.names.keys() {
        admission.pay(64, 0)?;
        key_bytes = key_bytes
            .checked_add(name.len())
            .and_then(|n| n.checked_add(1))
            .ok_or(ControlledTermInternError::ResourceLimit)?;
        include_name(&mut candidate, name)?;
    }
    // The entire arena includes older redeclarations, unregistered fresh vars,
    // function names and Let/quantified binder names, not merely current names.
    for entry in &store.terms {
        admission.pay(64, 0)?;
        include_term(&mut candidate, &entry.term, admission)?;
    }
    candidate
        .checked_add(1)
        .ok_or(ControlledTermInternError::ResourceLimit)?;
    Ok(NamePlan {
        candidate,
        key_bytes,
    })
}

pub(super) fn format(value: u32) -> Result<String> {
    let mut digits = [b'0'; 10];
    let mut cursor = digits.len();
    let mut left = value;
    loop {
        cursor -= 1;
        digits[cursor] = b'0' + (left % 10) as u8;
        left /= 10;
        if left == 0 {
            break;
        }
    }
    let decimal = std::str::from_utf8(&digits[cursor..])
        .map_err(|_| ControlledTermInternError::InvalidInput)?;
    let mut result = String::new();
    result
        .try_reserve_exact(PREFIX.len() + decimal.len())
        .map_err(|_| ControlledTermInternError::ResourceLimit)?;
    result.push_str(PREFIX);
    result.push_str(decimal);
    Ok(result)
}

pub(super) fn copy(source: &str) -> Result<String> {
    let mut result = String::new();
    result
        .try_reserve_exact(source.len())
        .map_err(|_| ControlledTermInternError::ResourceLimit)?;
    result.push_str(source);
    Ok(result)
}
