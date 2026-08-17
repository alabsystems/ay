// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use std::io::{self, Write};

use super::*;

impl ErProofLog {
    /// Create an empty ER proof log.
    #[must_use]
    pub fn new() -> Self {
        Self::default()
    }

    /// Append one extension-variable definition.
    pub(crate) fn push(&mut self, definition: ErDefinition) {
        self.definitions.push(definition);
    }

    /// Number of extension-variable definitions in the log.
    #[must_use]
    pub fn len(&self) -> usize {
        self.definitions.len()
    }

    /// Whether the log contains no extension-variable definitions.
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.definitions.is_empty()
    }

    /// All extension-variable definitions in emission order.
    #[must_use]
    pub fn definitions(&self) -> &[ErDefinition] {
        &self.definitions
    }

    /// Emit a self-contained Lean-style artifact for replay tooling.
    ///
    /// The generated file checks structural completeness with `native_decide`:
    /// every record has a positive DIMACS extension variable, definition and
    /// derived clauses mention that variable, source IDs are present, and the
    /// mandatory replay obligations are listed. Full RAT/RUP replay remains a
    /// downstream checker obligation.
    pub fn write_proof_replay(&self, writer: &mut dyn Write) -> io::Result<()> {
        writeln!(
            writer,
            "-- Auto-generated Extended Resolution extension-variable log from AY."
        )?;
        writeln!(
            writer,
            "-- Lean 4-ready data artifact; heuristic selection metadata is intentionally omitted."
        )?;
        writeln!(writer, "-- Definitions: {}", self.definitions.len())?;
        writeln!(writer)?;
        writeln!(writer, "namespace AY.ExtendedResolution")?;
        writeln!(writer)?;
        write_lean_prelude(writer)?;
        writeln!(writer, "def extensionDefinitions : List Definition := [")?;
        for (idx, def) in self.definitions.iter().enumerate() {
            let comma = if idx + 1 < self.definitions.len() {
                ","
            } else {
                ""
            };
            write_definition(writer, def, comma)?;
        }
        writeln!(writer, "]")?;
        writeln!(writer)?;
        writeln!(
            writer,
            "def extensionDefinitionCount : Nat := {}",
            self.definitions.len()
        )?;
        writeln!(writer)?;
        writeln!(
            writer,
            "theorem er_extension_log_structural_ok : erLogWellFormed extensionDefinitions = true := by native_decide"
        )?;
        writeln!(writer)?;
        writeln!(writer, "end AY.ExtendedResolution")?;
        Ok(())
    }
}

fn write_lean_prelude(writer: &mut dyn Write) -> io::Result<()> {
    writeln!(writer, "abbrev Literal := Int")?;
    writeln!(writer, "abbrev Clause := List Literal")?;
    writeln!(writer, "abbrev ClauseId := Nat")?;
    writeln!(writer, "abbrev Var := Nat")?;
    writeln!(writer)?;
    writeln!(writer, "inductive Producer where")?;
    writeln!(writer, "  | factor")?;
    writeln!(writer, "  | sbva")?;
    writeln!(writer, "  deriving Repr, BEq, DecidableEq")?;
    writeln!(writer)?;
    writeln!(writer, "inductive Obligation where")?;
    writeln!(writer, "  | freshRatDefinition")?;
    writeln!(writer, "  | witnessRat")?;
    writeln!(writer, "  | derivedClauseRup")?;
    writeln!(writer, "  | sourceDeletion")?;
    writeln!(writer, "  | originalModelProjection")?;
    writeln!(writer, "  deriving Repr, BEq, DecidableEq")?;
    writeln!(writer)?;
    writeln!(writer, "structure Definition where")?;
    writeln!(writer, "  extensionVar : Var")?;
    writeln!(writer, "  producer : Producer")?;
    writeln!(writer, "  definitionClauses : List Clause")?;
    writeln!(writer, "  proofOnlyClauses : List Clause")?;
    writeln!(writer, "  derivedClauses : List Clause")?;
    writeln!(writer, "  sourceClauseIds : List ClauseId")?;
    writeln!(writer, "  obligations : List Obligation")?;
    writeln!(writer, "  deriving Repr, BEq")?;
    writeln!(writer)?;
    writeln!(
        writer,
        "def litMentionsVar (v : Var) (l : Literal) : Bool :="
    )?;
    writeln!(writer, "  l == Int.ofNat v || l == -(Int.ofNat v)")?;
    writeln!(writer)?;
    writeln!(
        writer,
        "def clauseMentionsVar (v : Var) (c : Clause) : Bool :="
    )?;
    writeln!(writer, "  c.any (fun l => litMentionsVar v l)")?;
    writeln!(writer)?;
    writeln!(
        writer,
        "def allClausesMentionVar (v : Var) (cs : List Clause) : Bool :="
    )?;
    writeln!(writer, "  cs.all (fun c => clauseMentionsVar v c)")?;
    writeln!(writer)?;
    writeln!(writer, "def uniqueVars : List Var -> Bool")?;
    writeln!(writer, "  | [] => true")?;
    writeln!(
        writer,
        "  | v :: rest => !rest.contains v && uniqueVars rest"
    )?;
    writeln!(writer)?;
    writeln!(
        writer,
        "def definitionWellFormed (d : Definition) : Bool :="
    )?;
    writeln!(writer, "  d.extensionVar > 0")?;
    writeln!(writer, "  && !d.definitionClauses.isEmpty")?;
    writeln!(writer, "  && !d.derivedClauses.isEmpty")?;
    writeln!(writer, "  && !d.sourceClauseIds.isEmpty")?;
    writeln!(
        writer,
        "  && d.obligations.contains Obligation.freshRatDefinition"
    )?;
    writeln!(
        writer,
        "  && d.obligations.contains Obligation.derivedClauseRup"
    )?;
    writeln!(
        writer,
        "  && d.obligations.contains Obligation.sourceDeletion"
    )?;
    writeln!(
        writer,
        "  && d.obligations.contains Obligation.originalModelProjection"
    )?;
    writeln!(
        writer,
        "  && allClausesMentionVar d.extensionVar d.definitionClauses"
    )?;
    writeln!(
        writer,
        "  && allClausesMentionVar d.extensionVar d.derivedClauses"
    )?;
    writeln!(writer)?;
    writeln!(
        writer,
        "def erLogWellFormed (defs : List Definition) : Bool :="
    )?;
    writeln!(writer, "  defs.all definitionWellFormed")?;
    writeln!(
        writer,
        "  && uniqueVars (defs.map (fun d => d.extensionVar))"
    )?;
    writeln!(writer)?;
    Ok(())
}

fn write_definition(writer: &mut dyn Write, def: &ErDefinition, comma: &str) -> io::Result<()> {
    writeln!(writer, "  {{")?;
    writeln!(
        writer,
        "    extensionVar := {},",
        def.extension_var.index() + 1
    )?;
    writeln!(writer, "    producer := {},", def.producer.lean_ctor())?;
    writeln!(
        writer,
        "    definitionClauses := {},",
        format_clause_list(&def.definition_clauses)
    )?;
    writeln!(
        writer,
        "    proofOnlyClauses := {},",
        format_clause_list(&def.proof_only_clauses)
    )?;
    writeln!(
        writer,
        "    derivedClauses := {},",
        format_clause_list(&def.derived_clauses)
    )?;
    writeln!(
        writer,
        "    sourceClauseIds := {},",
        format_nat_list(&def.source_clause_ids)
    )?;
    writeln!(
        writer,
        "    obligations := {}",
        format_obligation_list(&def.obligations)
    )?;
    writeln!(writer, "  }}{comma}")?;
    Ok(())
}

fn format_clause_list(clauses: &[Vec<Literal>]) -> String {
    if clauses.is_empty() {
        return "[]".to_string();
    }
    let items: Vec<String> = clauses.iter().map(|clause| format_clause(clause)).collect();
    format!("[{}]", items.join(", "))
}

fn format_clause(clause: &[Literal]) -> String {
    if clause.is_empty() {
        return "[]".to_string();
    }
    let items: Vec<String> = clause
        .iter()
        .map(|lit| lit.to_dimacs().to_string())
        .collect();
    format!("[{}]", items.join(", "))
}

fn format_nat_list(values: &[u64]) -> String {
    if values.is_empty() {
        return "[]".to_string();
    }
    let items: Vec<String> = values.iter().map(ToString::to_string).collect();
    format!("[{}]", items.join(", "))
}

fn format_obligation_list(values: &[ErObligationKind]) -> String {
    if values.is_empty() {
        return "[]".to_string();
    }
    let items: Vec<&'static str> = values.iter().map(|kind| kind.lean_ctor()).collect();
    format!("[{}]", items.join(", "))
}
