// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The one place this lowering writes proof commands.

use super::{super::CheckableRule, AlethePrinter, MAX_OUTPUT_BYTES};

/// A bounded buffer of proof commands under one fresh label prefix.
pub(super) struct Emitter<'p, 'a> {
    printer: &'p AlethePrinter<'a>,
    prefix: String,
    next: u32,
    pub(super) out: String,
}

impl<'p, 'a> Emitter<'p, 'a> {
    pub(super) fn new(printer: &'p AlethePrinter<'a>, prefix: String) -> Self {
        Self {
            printer,
            prefix,
            next: 0,
            out: String::new(),
        }
    }

    fn fresh(&mut self) -> Option<String> {
        let label = format!("{}{}", self.prefix, self.next);
        self.next = self.next.checked_add(1)?;
        Some(label)
    }

    /// Append already-rendered commands (a decided atom's derivation).
    pub(super) fn append(&mut self, text: &str) -> Option<()> {
        if self.out.len().checked_add(text.len())? > MAX_OUTPUT_BYTES {
            return None;
        }
        self.printer.charge(text.len() as u64);
        if self.printer.work_budget_exhausted() {
            return None;
        }
        self.out.push_str(text);
        Some(())
    }

    /// `(assume label term)`; used only for a problem `define-fun` premise.
    pub(super) fn assume(&mut self, term: &str) -> Option<String> {
        let label = self.fresh()?;
        self.append(&format!("(assume {label} {term})\n"))?;
        Some(label)
    }

    /// A step under a fresh label.
    pub(super) fn step(
        &mut self,
        lits: &[String],
        rule: &'static str,
        premises: &[&str],
        args: Option<&str>,
    ) -> Option<String> {
        let label = self.fresh()?;
        self.command(&label, lits, rule, premises, args)?;
        Some(label)
    }

    /// `(step label (cl lits..) :rule rule [:premises (..)] [:args (..)])`.
    pub(super) fn command(
        &mut self,
        label: &str,
        lits: &[String],
        rule: &'static str,
        premises: &[&str],
        args: Option<&str>,
    ) -> Option<()> {
        let rule = CheckableRule::new(rule)?;
        self.command_with_rule(label, lits, rule, premises, args)
    }

    fn command_with_rule(
        &mut self,
        label: &str,
        lits: &[String],
        rule: CheckableRule,
        premises: &[&str],
        args: Option<&str>,
    ) -> Option<()> {
        let mut text = format!("(step {label} (cl");
        for lit in lits {
            text.push(' ');
            text.push_str(lit);
        }
        text.push_str(&format!(") :rule {rule}"));
        if !premises.is_empty() {
            text.push_str(&format!(" :premises ({})", premises.join(" ")));
        }
        if let Some(args) = args {
            text.push_str(&format!(" :args ({args})"));
        }
        text.push_str(")\n");
        self.append(&text)
    }
}
