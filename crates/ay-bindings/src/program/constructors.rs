// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates

//! AYProgram constructors and option setters.

use super::AYProgram;
use crate::constraint::logic;
use std::collections::BTreeMap;

impl AYProgram {
    /// Create a new empty program.
    #[must_use]
    pub fn new() -> Self {
        Self {
            logic: None,
            options: Vec::new(),
            commands: Vec::new(),
            declared_vars: BTreeMap::new(),
            declared_funs: Vec::new(),
            defined_funs: Vec::new(),
            declared_datatypes: BTreeMap::new(),
            declared_rels: Vec::new(),
            declared_chc_vars: Vec::new(),
            context_level: 0,
        }
    }

    /// Create a new program with QF_LIA logic (quantifier-free linear integer arithmetic).
    #[must_use]
    pub fn qf_lia() -> Self {
        let mut program = Self::new();
        program.set_logic(logic::QF_LIA);
        program
    }

    /// Create a new program with QF_LRA logic (quantifier-free linear real arithmetic).
    #[must_use]
    pub fn qf_lra() -> Self {
        let mut program = Self::new();
        program.set_logic(logic::QF_LRA);
        program
    }

    /// Create a new program with QF_NRA logic (quantifier-free nonlinear real arithmetic).
    #[must_use]
    pub fn qf_nra() -> Self {
        let mut program = Self::new();
        program.set_logic(logic::QF_NRA);
        program
    }

    /// Create a new program with QF_UF logic (quantifier-free uninterpreted functions).
    #[must_use]
    pub fn qf_uf() -> Self {
        let mut program = Self::new();
        program.set_logic(logic::QF_UF);
        program
    }

    /// Create a new program with QF_BV logic (quantifier-free bitvectors).
    #[must_use]
    pub fn qf_bv() -> Self {
        let mut program = Self::new();
        program.set_logic(logic::QF_BV);
        program
    }

    /// Create a new program with QF_AUFBV logic (arrays, uninterpreted functions, bitvectors).
    #[must_use]
    pub fn qf_aufbv() -> Self {
        let mut program = Self::new();
        program.set_logic(logic::QF_AUFBV);
        program
    }

    /// Create a new program with QF_FP logic (quantifier-free floating-point).
    #[must_use]
    pub fn qf_fp() -> Self {
        let mut program = Self::new();
        program.set_logic(logic::QF_FP);
        program
    }

    /// Create a new program for Horn clause solving.
    #[must_use]
    pub fn horn() -> Self {
        let mut program = Self::new();
        program.set_logic(logic::HORN);
        program
    }

    /// Set the SMT-LIB2 logic.
    pub fn set_logic(&mut self, logic: impl Into<String>) {
        self.logic = Some(logic.into());
    }

    /// Get the logic string, if set.
    #[must_use]
    pub fn get_logic(&self) -> Option<&str> {
        self.logic.as_deref()
    }

    /// Set a solver option.
    pub fn set_option(&mut self, name: impl Into<String>, value: impl Into<String>) {
        self.options.push((name.into(), value.into()));
    }

    /// Enable model production.
    pub fn produce_models(&mut self) {
        self.set_option("produce-models", "true");
    }

    /// Enable unsat core production.
    pub fn produce_unsat_cores(&mut self) {
        self.set_option("produce-unsat-cores", "true");
    }

    /// Create a new program for BMC (bounded model checking).
    ///
    /// Sets up typical options for BMC verification.
    #[must_use]
    pub fn for_bmc() -> Self {
        let mut program = Self::qf_bv();
        program.produce_models();
        program
    }
}
