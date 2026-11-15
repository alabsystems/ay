// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::inventory::Inventory;
use super::transaction::Closure;
use super::{charge, entries, integer_bytes, Atom, Checked, Pay, Probe, Refusal};
use ay_euf::EufModel;
use ay_lia::LiaModel;

fn text(value: &str, pay: &mut Pay<'_>) -> Checked<()> {
    charge(pay, &[value.len(), 1], &[value.len(), 64])?;
    Ok(())
}
fn cloned_text(value: &String, pay: &mut Pay<'_>) -> Checked<()> {
    charge(pay, &[value.len(), 1], &[value.capacity(), 64])?;
    Ok(())
}
fn integer(value: &num_bigint::BigInt, pay: &mut Pay<'_>) -> Checked<()> {
    let bound = integer_bytes(value)?;
    charge(pay, &[bound, 1], &[bound])?;
    Ok(())
}

/// Census EVERY field before clone/hash table allocation. This temporary arena
/// borrows the original check's work/stop/memory owner, never a fresh budget.
fn admit_snapshot(euf: &EufModel, lia: &Option<LiaModel>, pay: &mut Pay<'_>) -> Checked<()> {
    // HashMap/HashSet cloning and iteration can retain/scan bucket capacity
    // much larger than len after pop/retain. Admit EVERY incumbent capacity
    // before even starting these scans, not merely the surviving entries.
    for capacity in [
        euf.sort_elements.capacity(),
        euf.term_values.capacity(),
        euf.function_tables.capacity(),
        euf.function_table_terms.capacity(),
        euf.function_table_conflicts.capacity(),
        euf.func_app_const_terms.capacity(),
        euf.int_values.capacity(),
        euf.speculative_int_terms.capacity(),
        lia.as_ref().map_or(0, |model| model.values.capacity()),
    ] {
        entries(pay, capacity)?;
    }
    for (name, elements) in &euf.sort_elements {
        entries(pay, 1)?;
        cloned_text(name, pay)?;
        entries(pay, elements.capacity())?;
        for value in elements {
            entries(pay, 1)?;
            cloned_text(value, pay)?;
        }
    }
    for value in euf.term_values.values() {
        entries(pay, 1)?;
        cloned_text(value, pay)?;
    }
    for (name, rows) in &euf.function_tables {
        entries(pay, 1)?;
        cloned_text(name, pay)?;
        entries(pay, rows.capacity())?;
        for (arguments, result) in rows {
            entries(pay, 1)?;
            cloned_text(result, pay)?;
            entries(pay, arguments.capacity())?;
            for argument in arguments {
                entries(pay, 1)?;
                cloned_text(argument, pay)?;
            }
        }
    }
    for (name, sources) in &euf.function_table_terms {
        cloned_text(name, pay)?;
        entries(
            pay,
            sources
                .capacity()
                .checked_add(1)
                .ok_or(Refusal::Unsupported)?,
        )?;
    }
    for name in &euf.function_table_conflicts {
        entries(pay, 1)?;
        cloned_text(name, pay)?;
    }
    entries(pay, euf.func_app_const_terms.len())?;
    entries(pay, euf.speculative_int_terms.len())?;
    for value in euf.int_values.values() {
        entries(pay, 1)?;
        integer(value, pay)?;
    }
    if let Some(lia) = lia {
        for value in lia.values.values() {
            entries(pay, 1)?;
            integer(value, pay)?;
        }
    }
    Ok(())
}

pub(super) fn commit(
    inventory: &Inventory<'_>,
    closure: &Closure<'_>,
    euf: &mut EufModel,
    lia: &mut Option<LiaModel>,
    pay: &mut Pay<'_>,
    probe: &Probe,
) -> Checked<()> {
    probe.check("snapshot-admission", None, None);
    admit_snapshot(euf, lia, pay)?;
    let mut staged = euf.clone();
    let mut staged_lia = lia.clone();
    for (index, node) in inventory.nodes.iter().enumerate() {
        probe.check("stage-own-value", Some(node.term), None);
        let value = closure.evaluate(inventory, node.term, pay)?;
        entries(pay, 4)?;
        let rendered = value.render(pay)?;
        staged.term_values.insert(node.term, rendered);
        if let Atom::Int(value) = &value {
            integer(value, pay)?;
            staged.int_values.insert(node.term, value.clone());
            if (node.leaf && closure.is_hard(index, pay)?) || (!node.leaf && node.hard.is_some()) {
                staged.speculative_int_terms.remove(&node.term);
                if let Some(lia) = &mut staged_lia {
                    integer(value, pay)?;
                    lia.values.insert(node.term, value.clone());
                }
            } else {
                staged.speculative_int_terms.insert(node.term);
            }
        }
        // No new func_app_const_terms proof pin, equality, certificate,
        // validated bit, or cleared true-conflict marker is created here.
    }
    // Rebuild each touched free-function table from COMPLETE current root +
    // active-kernel applications, keyed by final typed source values. Old raw
    // concrete row strings are neither a value source nor occurrence authority.
    for (position, app) in inventory.apps.iter().enumerate() {
        let mut already = false;
        for earlier in &inventory.apps[..position] {
            charge(
                pay,
                &[1, app.symbol.name().len(), earlier.symbol.name().len()],
                &[],
            )?;
            already |= earlier.symbol == app.symbol;
        }
        if already {
            continue;
        }
        let mut rows: Vec<(Vec<String>, String)> = Vec::new();
        let mut sources = Vec::new();
        for occurrence in &inventory.apps {
            probe.check(
                "stage-current-row",
                Some(inventory.nodes[occurrence.output].term),
                None,
            );
            charge(
                pay,
                &[1, app.symbol.name().len(), occurrence.symbol.name().len()],
                &[],
            )?;
            if occurrence.symbol != app.symbol {
                continue;
            }
            let mut arguments = Vec::new();
            entries(pay, occurrence.arguments.len())?;
            for &argument in &occurrence.arguments {
                arguments.push(closure.evaluate(inventory, argument, pay)?.render(pay)?);
            }
            let result = closure.value(occurrence.output, pay)?.render(pay)?;
            let mut duplicate = false;
            for (old_args, old_value) in &rows {
                if old_args.len() != arguments.len() {
                    continue;
                }
                let mut equal = true;
                for (old, new) in old_args.iter().zip(&arguments) {
                    charge(pay, &[1, old.len(), new.len()], &[])?;
                    equal &= old == new;
                }
                if equal {
                    charge(pay, &[1, old_value.len(), result.len()], &[])?;
                    if old_value != &result {
                        return Err(Refusal::Conflict);
                    }
                    duplicate = true;
                }
            }
            if !duplicate {
                entries(pay, 2)?;
                rows.push((arguments, result));
                sources.push(inventory.nodes[occurrence.output].term);
            }
        }
        entries(pay, 2)?;
        text(app.symbol.name(), pay)?;
        staged
            .function_tables
            .insert(app.symbol.name().to_owned(), rows);
        text(app.symbol.name(), pay)?;
        staged
            .function_table_terms
            .insert(app.symbol.name().to_owned(), sources);
    }
    // All potentially failing work (including final stop polling) precedes the
    // two infallible swaps. Row retention may subsequently discard one sampled
    // row; coherent own values for every restored occurrence remain available.
    probe.check("commit-stop", None, None);
    pay(0, 0)?;
    *euf = staged;
    *lia = staged_lia;
    Ok(())
}
