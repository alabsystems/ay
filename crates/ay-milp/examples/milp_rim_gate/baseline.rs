// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use std::collections::{BTreeMap, BTreeSet};
use std::fmt::Write as _;
use std::fs;
use std::path::Path;
use std::time::Duration;

use crate::cli::Tier;
use crate::{GateError, GateResult};

const NOTE_TABLES: &[(&str, &str)] = &[
    (
        "not_finished",
        "# NOT PINNED: DOES NOT FINISH. The rim does not reach an optimum on these\n\
         # inside any budget worth spending, so their pivot counts are a function of the\n\
         # DEADLINE rather than of the tableau, and pinning them would pin the box.\n",
    ),
    (
        "absent",
        "# NOT PINNED: NO SUCH MODEL ON THIS MACHINE. Named in the campaign's class\n\
         # lists but present in no corpus here. Listed rather than omitted so the\n\
         # question is answered by the file.\n",
    ),
    (
        "not_pinned",
        "# NOT PINNED: CORPUS NOT REBUILDABLE FROM THIS REPOSITORY. Measured, real, and\n\
         # deliberately left out: a pin that only one machine can check goes SETUP-red\n\
         # everywhere else and is then deleted. Everything pinned above resolves out of\n\
         # the sha256-manifested corpus that `scripts/milp_gate_corpus.py --build`\n\
         # recreates.\n",
    ),
];

#[derive(Clone, Debug)]
pub(crate) struct Row {
    pub(crate) name: String,
    pub(crate) class: String,
    pub(crate) status: String,
    pub(crate) form: String,
    pub(crate) switch_at: i64,
    pub(crate) p1_pivots: i64,
    pub(crate) pivots: i64,
    pub(crate) value: String,
    pub(crate) tier: String,
    pub(crate) wall_s: f64,
    pub(crate) raw: Option<String>,
}

impl Row {
    pub(crate) fn same_pins(&self, other: &Self) -> bool {
        self.status == other.status
            && self.form == other.form
            && self.switch_at == other.switch_at
            && self.p1_pivots == other.p1_pivots
            && self.pivots == other.pivots
            && self.value == other.value
    }
}

#[derive(Default)]
struct PendingRow {
    name: Option<String>,
    class: Option<String>,
    status: Option<String>,
    form: Option<String>,
    switch_at: Option<i64>,
    p1_pivots: Option<i64>,
    pivots: Option<i64>,
    value: Option<String>,
    tier: Option<String>,
    wall_s: Option<f64>,
}

impl PendingRow {
    fn finish(self, line: usize) -> GateResult<Row> {
        macro_rules! required {
            ($field:ident) => {
                self.$field.ok_or_else(|| {
                    GateError::setup(format!(
                        "instance ending near line {line} has no `{}`",
                        stringify!($field)
                    ))
                })?
            };
        }
        Ok(Row {
            name: required!(name),
            class: required!(class),
            status: required!(status),
            form: required!(form),
            switch_at: required!(switch_at),
            p1_pivots: required!(p1_pivots),
            pivots: required!(pivots),
            value: required!(value),
            tier: required!(tier),
            wall_s: required!(wall_s),
            raw: None,
        })
    }
}

pub(crate) struct Ratchet {
    pub(crate) rows: Vec<Row>,
    notes: BTreeMap<String, BTreeMap<String, String>>,
    header: String,
}

impl Ratchet {
    pub(crate) fn for_tier(&self, tier: Tier) -> &[Row] {
        let end = match tier {
            Tier::All => self.rows.len(),
            Tier::Fast => self
                .rows
                .iter()
                .position(|row| row.tier != "fast")
                .unwrap_or(self.rows.len()),
        };
        &self.rows[..end]
    }
}

fn quoted(value: &str) -> &str {
    match (value.find('"'), value.rfind('"')) {
        (Some(first), Some(last)) if last > first => &value[first + 1..last],
        _ => value,
    }
}

fn set_field(row: &mut PendingRow, key: &str, value: &str, line: usize) -> GateResult<()> {
    let integer = |label: &str| {
        value.parse::<i64>().map_err(|error| {
            GateError::setup(format!("line {line}: `{label}` is not an integer: {error}"))
        })
    };
    match key {
        "name" => row.name = Some(value.to_owned()),
        "class" => row.class = Some(value.to_owned()),
        "status" => row.status = Some(value.to_owned()),
        "form" => row.form = Some(value.to_owned()),
        "switch_at" => row.switch_at = Some(integer(key)?),
        "p1_pivots" => row.p1_pivots = Some(integer(key)?),
        "pivots" => row.pivots = Some(integer(key)?),
        "value" => row.value = Some(value.to_owned()),
        "tier" => row.tier = Some(value.to_owned()),
        "wall_s" => {
            row.wall_s = Some(value.parse().map_err(|error| {
                GateError::setup(format!("line {line}: `wall_s` is not a number: {error}"))
            })?);
        }
        other => {
            return Err(GateError::setup(format!(
                "line {line}: unknown key `{other}`"
            )))
        }
    }
    Ok(())
}

fn push_pending(
    pending: &mut Option<PendingRow>,
    rows: &mut Vec<Row>,
    line: usize,
) -> GateResult<()> {
    if let Some(row) = pending.take() {
        let row = row.finish(line)?;
        if rows.iter().any(|old| old.name == row.name) {
            return Err(GateError::setup(format!("{} is pinned twice", row.name)));
        }
        rows.push(row);
    }
    Ok(())
}

fn parse(text: &str) -> GateResult<Ratchet> {
    let mut rows = Vec::new();
    let mut notes: BTreeMap<String, BTreeMap<String, String>> = BTreeMap::new();
    let mut pending = None;
    let mut table: Option<String> = None;
    for (index, raw) in text.lines().enumerate() {
        let line_no = index + 1;
        let line = raw.trim();
        if line.is_empty() || line.starts_with('#') {
            continue;
        }
        if line == "[[instance]]" {
            push_pending(&mut pending, &mut rows, line_no)?;
            pending = Some(PendingRow::default());
            table = None;
            continue;
        }
        if line.starts_with('[') && line.ends_with(']') {
            push_pending(&mut pending, &mut rows, line_no)?;
            let name = line[1..line.len() - 1].to_owned();
            notes.entry(name.clone()).or_default();
            table = Some(name);
            continue;
        }
        let (key, value) = line.split_once('=').ok_or_else(|| {
            GateError::setup(format!(
                "line {line_no}: not a `key = value` line: {line:?}"
            ))
        })?;
        let (key, value) = (key.trim(), quoted(value.trim()));
        if let Some(table) = &table {
            notes
                .entry(table.clone())
                .or_default()
                .insert(key.to_owned(), value.to_owned());
        } else {
            let row = pending.as_mut().ok_or_else(|| {
                GateError::setup(format!("line {line_no}: key `{key}` outside any table"))
            })?;
            set_field(row, key, value, line_no)?;
        }
    }
    push_pending(&mut pending, &mut rows, text.lines().count() + 1)?;
    rows.sort_by_key(|row| (row.tier != "fast", row.name.clone()));
    let cut = text
        .find("\n[[instance]]")
        .ok_or_else(|| GateError::setup("rim baseline contains no [[instance]] table"))?;
    Ok(Ratchet {
        rows,
        notes,
        header: text[..cut].to_owned(),
    })
}

pub(crate) fn load(path: &Path) -> GateResult<Ratchet> {
    let text = fs::read_to_string(path).map_err(|error| {
        GateError::setup(format!(
            "cannot read rim baseline {}: {error}",
            path.display()
        ))
    })?;
    parse(&text)
}

pub(crate) fn list(ratchet: &Ratchet) {
    println!(
        "{:<9} {:<14} {:<6} {:>10} {:>8} {:>8} {:>8}",
        "instance", "class", "tier", "switch_at", "p1_piv", "pivots", "wall_s"
    );
    for row in &ratchet.rows {
        println!(
            "{:<9} {:<14} {:<6} {:>10} {:>8} {:>8} {:>8.3}",
            row.name, row.class, row.tier, row.switch_at, row.p1_pivots, row.pivots, row.wall_s
        );
    }
    for (table, _) in NOTE_TABLES {
        let Some(entries) = ratchet.notes.get(*table) else {
            continue;
        };
        println!("\n{}:", table.replace('_', " "));
        for (name, reason) in entries {
            println!("  {name:<22} {reason}");
        }
    }
}

fn write_row(output: &mut String, row: &Row, wall_s: f64) -> GateResult<()> {
    writeln!(output, "\n[[instance]]")?;
    writeln!(output, "name = \"{}\"", row.name)?;
    writeln!(output, "class = \"{}\"", row.class)?;
    writeln!(output, "status = \"{}\"", row.status)?;
    writeln!(output, "form = \"{}\"", row.form)?;
    writeln!(output, "switch_at = {}", row.switch_at)?;
    writeln!(output, "p1_pivots = {}", row.p1_pivots)?;
    writeln!(output, "pivots = {}", row.pivots)?;
    writeln!(output, "value = \"{}\"", row.value)?;
    writeln!(output, "tier = \"{}\"", row.tier)?;
    writeln!(output, "wall_s = {wall_s:.3}")?;
    Ok(())
}

pub(crate) fn write(
    path: &Path,
    ratchet: &Ratchet,
    measured: &[Row],
    replaced: &[&str],
) -> GateResult<()> {
    let replaced: BTreeSet<&str> = replaced.iter().copied().collect();
    let old: BTreeMap<&str, &Row> = ratchet
        .rows
        .iter()
        .map(|row| (row.name.as_str(), row))
        .collect();
    let mut rows: Vec<Row> = ratchet
        .rows
        .iter()
        .filter(|row| !replaced.contains(row.name.as_str()))
        .cloned()
        .chain(measured.iter().cloned())
        .collect();
    rows.sort_by_key(|row| (row.tier != "fast", row.name.clone()));
    let mut output = ratchet.header.clone();
    for row in &rows {
        let wall = old
            .get(row.name.as_str())
            .filter(|previous| previous.same_pins(row))
            .map_or(row.wall_s, |previous| previous.wall_s);
        write_row(&mut output, row, wall)?;
    }
    for (table, prose) in NOTE_TABLES {
        write!(output, "\n{prose}[{table}]\n")?;
        if let Some(entries) = ratchet.notes.get(*table) {
            for (name, reason) in entries {
                writeln!(output, "{name} = \"{reason}\"")?;
            }
        }
    }
    fs::write(path, output)?;
    Ok(())
}

pub(crate) fn compare(expected: &[Row], actual: &[Row]) -> Vec<String> {
    let by_name: BTreeMap<&str, &Row> = expected
        .iter()
        .map(|row| (row.name.as_str(), row))
        .collect();
    let mut failures = Vec::new();
    for got in actual {
        let Some(want) = by_name.get(got.name.as_str()) else {
            failures.push(format!("{} has no committed pin", got.name));
            continue;
        };
        if got.status != want.status {
            failures.push(format!(
                "{:<9} STATUS     expected {:<11} actual {:<11}{}",
                got.name,
                want.status,
                got.status,
                got.raw
                    .as_deref()
                    .map_or_else(String::new, |raw| format!("   ({raw})"))
            ));
            continue;
        }
        if got.value != want.value {
            failures.push(format!(
                "{:<9} OPTIMUM    expected {}\n                     actual   {}  <- EXACT VALUE MOVED, THIS IS NOT A TUNING RESULT",
                got.name, want.value, got.value
            ));
            continue;
        }
        compare_shape(want, got, &mut failures);
    }
    failures
}

fn compare_shape(want: &Row, got: &Row, failures: &mut Vec<String>) {
    if got.form != want.form {
        failures.push(format!(
            "{:<9} FORM       expected {:<14} actual {:<14} (class {})",
            got.name, want.form, got.form, want.class
        ));
    }
    if got.switch_at != want.switch_at {
        let explanation = if want.switch_at == 0 {
            "FALSE FIRE -- a reduced-class model started converting".to_owned()
        } else if got.switch_at == 0 {
            "LOST -- a converting model stopped converting".to_owned()
        } else if got.switch_at > want.switch_at {
            format!("LATER by {} pivots", got.switch_at - want.switch_at)
        } else {
            format!("EARLIER by {} pivots", want.switch_at - got.switch_at)
        };
        failures.push(format!(
            "{:<9} SWITCH_AT  expected {:<7} actual {:<7} ({explanation})",
            got.name, want.switch_at, got.switch_at
        ));
    }
    for (label, expected, actual) in [
        ("P1_PIVOTS", want.p1_pivots, got.p1_pivots),
        ("PIVOTS", want.pivots, got.pivots),
    ] {
        if actual != expected {
            failures.push(format!(
                "{:<9} {:<10} expected {:<7} actual {:<7}  <- THE PIVOT SEQUENCE MOVED; a representation change must not do this",
                got.name, label, expected, actual
            ));
        }
    }
}

pub(crate) fn report(tier: Tier, expected: &[Row], failures: &[String], wall: Duration) {
    let converting = expected
        .iter()
        .filter(|row| row.class == "fraction-free")
        .count();
    println!(
        "=== milp rim gate: tier {}, {} instances ({} fraction-free, {} reduced), {:.1}s wall ===",
        tier.label(),
        expected.len(),
        converting,
        expected.len() - converting,
        wall.as_secs_f64()
    );
    for failure in failures {
        println!("  FAIL  {failure}");
    }
    if failures.is_empty() {
        println!("  clean: every switch point, pivot count and exact optimum is exact");
    }
    println!("=== {} fail ===", failures.len());
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn parser_rejects_duplicate_instances() {
        let text = "[[instance]]\nname=\"x\"\nclass=\"reduced\"\nstatus=\"OPTIMAL\"\n\
                    form=\"reduced\"\nswitch_at=0\np1_pivots=1\npivots=1\nvalue=\"0\"\n\
                    tier=\"fast\"\nwall_s=0.1\n[[instance]]\nname=\"x\"\nclass=\"reduced\"\n\
                    status=\"OPTIMAL\"\nform=\"reduced\"\nswitch_at=0\np1_pivots=1\n\
                    pivots=1\nvalue=\"0\"\ntier=\"fast\"\nwall_s=0.1\n";
        assert!(parse(text).is_err());
    }
}
