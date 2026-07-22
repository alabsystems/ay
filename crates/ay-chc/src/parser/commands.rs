// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Command surface and declaration parsing for the CHC parser.
//!
//! Handles `set-logic`, `declare-rel`/`declare-fun`, `declare-var`,
//! `declare-datatype`/`declare-datatypes`, `rule`, `query`, and `assert`
//! commands. Delegates expression/sort parsing through `self.parse_expr()`
//! and `self.parse_sort()`.

use super::ChcParser;
use crate::expr::{ChcDtConstructor, ChcDtSelector};
use crate::{ChcError, ChcExpr, ChcResult, ChcSort, ChcVar, ClauseBody, ClauseHead, HornClause};
use ay_core::kani_compat::DetHashSet as FxHashSet;
use std::sync::Arc;

impl ChcParser {
    /// Parse a single command
    pub(super) fn parse_command(&mut self) -> ChcResult<()> {
        self.skip_whitespace_and_comments();
        if self.pos >= self.input.len() {
            return Ok(());
        }

        self.expect_char('(')?;
        self.skip_whitespace_and_comments();

        let cmd = self.parse_symbol()?;
        self.skip_whitespace_and_comments();

        match cmd.as_str() {
            "set-logic" => {
                let logic = self.parse_symbol()?;
                // Accept HORN or other logics that might contain CHC
                if !["HORN", "LIA", "LRA", "ALIA", "AUFLIA", "QF_LIA", "QF_LRA"]
                    .contains(&logic.as_str())
                {
                    tracing::warn!(
                        "Unexpected logic '{logic}', expecting HORN or arithmetic logic"
                    );
                }
            }
            "declare-rel" | "declare-fun" => {
                self.parse_declare_predicate(&cmd)?;
            }
            "declare-var" | "declare-const" => {
                self.parse_declare_var()?;
            }
            "declare-datatype" => {
                self.parse_declare_datatype()?;
            }
            "declare-datatypes" => {
                self.parse_declare_datatypes()?;
            }
            "rule" => {
                self.problem.set_fixedpoint_format();
                self.parse_rule()?;
            }
            "ay-declare-action" => {
                self.parse_ay_declare_action()?;
            }
            "ay-action-rule" => {
                self.problem.set_fixedpoint_format();
                self.parse_ay_action_rule()?;
            }
            "query" => {
                self.problem.set_fixedpoint_format();
                self.parse_query()?;
            }
            "check-sat" | "exit" | "set-info" | "set-option" => {
                // Skip until closing paren
                let mut depth = 1;
                while depth > 0 && self.pos < self.input.len() {
                    match self.current_char() {
                        Some('(') => depth += 1,
                        Some(')') => depth -= 1,
                        _ => {}
                    }
                    self.pos += 1;
                }
                return Ok(());
            }
            "assert" => {
                // Parse an assertion (may be a Horn clause)
                self.skip_whitespace_and_comments();
                let expr = self.parse_expr()?;
                self.add_assertion_as_clause(expr)?;
            }
            _ => {
                // Skip unknown command
                tracing::warn!("Unknown command: {cmd}");
                let mut depth = 1;
                while depth > 0 && self.pos < self.input.len() {
                    match self.current_char() {
                        Some('(') => depth += 1,
                        Some(')') => depth -= 1,
                        _ => {}
                    }
                    self.pos += 1;
                }
                return Ok(());
            }
        }

        self.skip_whitespace_and_comments();
        self.expect_char(')')?;
        Ok(())
    }

    /// Parse a declare-rel or declare-fun command
    fn parse_declare_predicate(&mut self, cmd: &str) -> ChcResult<()> {
        self.skip_whitespace_and_comments();
        let name = self.parse_symbol()?;
        self.skip_whitespace_and_comments();

        // Parse argument sorts
        self.expect_char('(')?;
        let mut sorts = Vec::new();
        loop {
            self.skip_whitespace_and_comments();
            if self.peek_char() == Some(')') {
                break;
            }
            sorts.push(self.parse_sort()?);
        }
        self.expect_char(')')?;

        // For declare-fun, also parse return sort
        if cmd == "declare-fun" {
            self.skip_whitespace_and_comments();
            let ret_sort = self.parse_sort()?;
            if ret_sort != ChcSort::Bool {
                // Non-Bool functions are not supported - fail with error (fixes #352)
                return Err(ChcError::Parse(format!(
                    "Non-predicate function declaration: '{name}' with return sort {ret_sort:?}. \
                     Only Bool-returning functions (predicates) are supported in ay-chc."
                )));
            }
        }

        // Register predicate
        let pred_id = self.problem.declare_predicate(&name, sorts.clone());
        self.predicates.insert(name, (pred_id, sorts));

        Ok(())
    }

    /// Parse a declare-var command
    fn parse_declare_var(&mut self) -> ChcResult<()> {
        self.skip_whitespace_and_comments();
        let name = self.parse_symbol()?;
        self.skip_whitespace_and_comments();
        let sort = self.parse_sort()?;

        self.variables.insert(name, sort);
        Ok(())
    }

    /// Parse a declare-datatype command
    /// Syntax: (declare-datatype <name> ((<ctor> (<selector> <sort>)*)*))
    /// Example: (declare-datatype Tuple_bv32_bool ((mk (fld_0 (_ BitVec 32)) (fld_1 Bool))))
    fn parse_declare_datatype(&mut self) -> ChcResult<()> {
        self.skip_whitespace_and_comments();

        // Parse datatype name
        let datatype_name = self.parse_symbol()?;
        self.skip_whitespace_and_comments();

        // Register the name first so recursive sort references resolve during parsing.
        self.declared_sorts.insert(datatype_name.clone());

        // Pass 1: Parse constructor/selector structure, collecting metadata.
        // We need the parsed sorts before we can build ChcSort::Datatype, so we
        // collect (ctor_name, selectors) tuples and register functions after.
        let mut parsed_ctors: Vec<(String, Vec<(String, ChcSort)>)> = Vec::new();

        self.expect_char('(')?;

        loop {
            self.skip_whitespace_and_comments();
            if self.peek_char() == Some(')') {
                break;
            }

            // Parse single constructor: (<ctor> (<selector> <sort>)*)
            self.expect_char('(')?;
            self.skip_whitespace_and_comments();
            let ctor_name = self.parse_symbol()?;
            self.skip_whitespace_and_comments();

            // Parse selectors
            let mut selectors: Vec<(String, ChcSort)> = Vec::new();
            while self.peek_char() == Some('(') {
                self.expect_char('(')?;
                self.skip_whitespace_and_comments();
                let selector_name = self.parse_symbol()?;
                self.skip_whitespace_and_comments();
                let selector_sort = self.parse_sort()?;
                self.skip_whitespace_and_comments();
                self.expect_char(')')?;
                self.skip_whitespace_and_comments();

                selectors.push((selector_name, selector_sort));
            }

            self.skip_whitespace_and_comments();
            self.expect_char(')')?;

            parsed_ctors.push((ctor_name, selectors));
        }

        self.expect_char(')')?;

        // Pass 2: Build ChcSort::Datatype with full metadata.
        let chc_constructors: Vec<ChcDtConstructor> = parsed_ctors
            .iter()
            .map(|(ctor_name, sels)| ChcDtConstructor {
                name: ctor_name.clone(),
                selectors: sels
                    .iter()
                    .map(|(sel_name, sel_sort)| ChcDtSelector {
                        name: sel_name.clone(),
                        sort: sel_sort.clone(),
                    })
                    .collect(),
            })
            .collect();

        let unresolved_datatype_sort = ChcSort::Datatype {
            name: datatype_name.clone(),
            constructors: Arc::new(chc_constructors),
        };

        // Store the initial sort so self-recursive selector references can be
        // resolved after the constructor list has been parsed.
        self.declared_datatype_sorts
            .insert(datatype_name.clone(), unresolved_datatype_sort);
        let datatype_sort = self
            .declared_datatype_sorts
            .get(&datatype_name)
            .map(|sort| self.resolve_dt_sort_refs(sort))
            .expect("datatype sort inserted before resolution");
        self.declared_datatype_sorts
            .insert(datatype_name.clone(), datatype_sort.clone());

        let resolved_ctors: Vec<(String, Vec<(String, ChcSort)>)> = parsed_ctors
            .iter()
            .map(|(ctor_name, sels)| {
                let resolved_sels = sels
                    .iter()
                    .map(|(sel_name, sel_sort)| {
                        (sel_name.clone(), self.resolve_sort_refs(sel_sort))
                    })
                    .collect();
                (ctor_name.clone(), resolved_sels)
            })
            .collect();

        // Propagate DT definition to the problem so SmtContext can emit
        // declare-datatype commands for the executor adapter (#7016).
        self.problem
            .add_datatype_def(datatype_name.clone(), resolved_ctors);

        // Pass 3: Register constructors, selectors, and testers in self.functions.
        for (ctor_name, selectors) in &parsed_ctors {
            // Register each selector: datatype -> field_sort
            let mut selector_sorts: Vec<ChcSort> = Vec::new();
            for (sel_name, sel_sort) in selectors {
                let resolved_sort = self.resolve_sort_refs(sel_sort);
                self.register_function(
                    sel_name.clone(),
                    resolved_sort.clone(),
                    vec![datatype_sort.clone()],
                );
                selector_sorts.push(resolved_sort);
            }

            // Register constructor: (field_sorts) -> datatype
            self.register_function(ctor_name.clone(), datatype_sort.clone(), selector_sorts);

            // Register tester: datatype -> Bool
            let tester_name = format!("is-{ctor_name}");
            self.register_function(tester_name, ChcSort::Bool, vec![datatype_sort.clone()]);
        }
        Ok(())
    }

    /// Parse a declare-datatypes command (plural form for mutually recursive DTs).
    /// Syntax: (declare-datatypes ((T1 0) (T2 0) ...) ((ctors1) (ctors2) ...))
    /// Example: (declare-datatypes ((Tree 0) (Forest 0))
    ///            (((leaf (val Int)) (node (children Forest)))
    ///             ((nil) (cons (head Tree) (tail Forest)))))
    fn parse_declare_datatypes(&mut self) -> ChcResult<()> {
        self.skip_whitespace_and_comments();

        // Step 1: Parse sort declarations: ((T1 arity1) (T2 arity2) ...)
        self.expect_char('(')?;
        let mut sort_names: Vec<String> = Vec::new();
        loop {
            self.skip_whitespace_and_comments();
            if self.peek_char() == Some(')') {
                break;
            }
            self.expect_char('(')?;
            self.skip_whitespace_and_comments();
            let name = self.parse_symbol()?;
            self.skip_whitespace_and_comments();
            // Parse arity (ignored for now — ay-chc doesn't support parametric DTs)
            let _arity = self.parse_numeral()?;
            self.skip_whitespace_and_comments();
            self.expect_char(')')?;
            sort_names.push(name);
        }
        self.expect_char(')')?;
        self.skip_whitespace_and_comments();

        // Step 2: Register ALL names before parsing constructors (mutual recursion).
        for name in &sort_names {
            self.declared_sorts.insert(name.clone());
        }

        // Step 3: Parse constructor lists: ((ctors_for_T1) (ctors_for_T2) ...)
        self.expect_char('(')?;
        let mut all_parsed_ctors: Vec<Vec<(String, Vec<(String, ChcSort)>)>> = Vec::new();
        for _ in &sort_names {
            self.skip_whitespace_and_comments();
            // Parse one datatype's constructors: ((ctor1 ...) (ctor2 ...))
            self.expect_char('(')?;
            let mut parsed_ctors: Vec<(String, Vec<(String, ChcSort)>)> = Vec::new();
            loop {
                self.skip_whitespace_and_comments();
                if self.peek_char() == Some(')') {
                    break;
                }
                self.expect_char('(')?;
                self.skip_whitespace_and_comments();
                let ctor_name = self.parse_symbol()?;
                self.skip_whitespace_and_comments();

                let mut selectors: Vec<(String, ChcSort)> = Vec::new();
                while self.peek_char() == Some('(') {
                    self.expect_char('(')?;
                    self.skip_whitespace_and_comments();
                    let selector_name = self.parse_symbol()?;
                    self.skip_whitespace_and_comments();
                    let selector_sort = self.parse_sort()?;
                    self.skip_whitespace_and_comments();
                    self.expect_char(')')?;
                    self.skip_whitespace_and_comments();
                    selectors.push((selector_name, selector_sort));
                }

                self.skip_whitespace_and_comments();
                self.expect_char(')')?;
                parsed_ctors.push((ctor_name, selectors));
            }
            self.expect_char(')')?;
            all_parsed_ctors.push(parsed_ctors);
        }
        self.expect_char(')')?;

        if sort_names.len() != all_parsed_ctors.len() {
            return Err(ChcError::Parse(
                "declare-datatypes: sort count does not match constructor list count".into(),
            ));
        }

        // Step 4: Build ChcSort::Datatype and register constructors/selectors/testers
        // for each datatype. First pass builds with unresolved cross-references.
        let sort_names_copy: Vec<String> = sort_names.clone();
        for (datatype_name, parsed_ctors) in sort_names.into_iter().zip(all_parsed_ctors.iter()) {
            let chc_constructors: Vec<ChcDtConstructor> = parsed_ctors
                .iter()
                .map(|(ctor_name, sels)| ChcDtConstructor {
                    name: ctor_name.clone(),
                    selectors: sels
                        .iter()
                        .map(|(sel_name, sel_sort)| ChcDtSelector {
                            name: sel_name.clone(),
                            sort: sel_sort.clone(),
                        })
                        .collect(),
                })
                .collect();

            let datatype_sort = ChcSort::Datatype {
                name: datatype_name.clone(),
                constructors: Arc::new(chc_constructors),
            };

            self.problem
                .add_datatype_def(datatype_name.clone(), parsed_ctors.clone());

            self.declared_datatype_sorts
                .insert(datatype_name, datatype_sort.clone());
        }

        // Step 5: Resolve mutual DT references (#8419).
        //
        // During Step 3, cross-referenced DT sorts (e.g., `Result8` inside `State`
        // selectors) are parsed as `Uninterpreted("Result8")` because the full
        // `Datatype{...}` sort hasn't been built yet. Now that all DT sorts are
        // in `declared_datatype_sorts`, rebuild each DT sort with resolved
        // selector sorts.
        //
        // Without this fix, the DT flattener cannot recursively flatten nested
        // DTs — it sees `Uninterpreted("Result8")` and treats it as a scalar,
        // leaving DT operations (constructors/selectors/testers) in the flattened
        // output. This causes DT+BV CHC problems with nested datatypes to fail.
        {
            let resolved_sorts: Vec<(String, ChcSort)> = self
                .declared_datatype_sorts
                .iter()
                .map(|(name, sort)| (name.clone(), self.resolve_dt_sort_refs(sort)))
                .collect();
            for (name, resolved) in resolved_sorts {
                self.declared_datatype_sorts.insert(name, resolved);
            }
            // Also update the problem's datatype defs with resolved sorts.
            for (name, parsed_ctors) in sort_names_copy.iter().zip(all_parsed_ctors.iter()) {
                let resolved_ctors: Vec<(String, Vec<(String, ChcSort)>)> = parsed_ctors
                    .iter()
                    .map(|(ctor_name, sels)| {
                        let resolved_sels: Vec<(String, ChcSort)> = sels
                            .iter()
                            .map(|(sel_name, sel_sort)| {
                                (sel_name.clone(), self.resolve_sort_refs(sel_sort))
                            })
                            .collect();
                        (ctor_name.clone(), resolved_sels)
                    })
                    .collect();
                self.problem.add_datatype_def(name.clone(), resolved_ctors);
            }
        }

        // Step 6: Register constructors, selectors, and testers with resolved sorts.
        for (datatype_name, parsed_ctors) in sort_names_copy.iter().zip(all_parsed_ctors.iter()) {
            let datatype_sort = self
                .declared_datatype_sorts
                .get(datatype_name)
                .expect("DT sort must exist after Step 5")
                .clone();

            for (ctor_name, selectors) in parsed_ctors {
                let mut selector_sorts: Vec<ChcSort> = Vec::new();
                for (sel_name, sel_sort) in selectors {
                    let resolved_sort = self.resolve_sort_refs(sel_sort);
                    self.register_function(
                        sel_name.clone(),
                        resolved_sort.clone(),
                        vec![datatype_sort.clone()],
                    );
                    selector_sorts.push(resolved_sort);
                }
                self.register_function(ctor_name.clone(), datatype_sort.clone(), selector_sorts);
                let tester_name = format!("is-{ctor_name}");
                self.register_function(tester_name, ChcSort::Bool, vec![datatype_sort.clone()]);
            }
        }
        Ok(())
    }

    /// Resolve `Uninterpreted("X")` references inside a sort to `Datatype{...}`
    /// when "X" has been declared as a datatype. Used after Step 4 of
    /// `parse_declare_datatypes` to fix mutual DT references (#8419).
    fn resolve_sort_refs(&self, sort: &ChcSort) -> ChcSort {
        self.resolve_sort_refs_seen(sort, &mut FxHashSet::default())
    }

    fn resolve_sort_refs_seen(
        &self,
        sort: &ChcSort,
        seen_datatypes: &mut FxHashSet<String>,
    ) -> ChcSort {
        match sort {
            ChcSort::Uninterpreted(name) => {
                if let Some(dt_sort) = self.declared_datatype_sorts.get(name) {
                    if !seen_datatypes.insert(name.clone()) {
                        return dt_sort.clone();
                    }
                    let resolved = self.resolve_sort_refs_seen(dt_sort, seen_datatypes);
                    seen_datatypes.remove(name);
                    resolved
                } else {
                    sort.clone()
                }
            }
            ChcSort::Array(key, val) => ChcSort::Array(
                Box::new(self.resolve_sort_refs_seen(key, seen_datatypes)),
                Box::new(self.resolve_sort_refs_seen(val, seen_datatypes)),
            ),
            ChcSort::Datatype { name, constructors } => {
                if !seen_datatypes.insert(name.clone()) {
                    return sort.clone();
                }
                let resolved_ctors: Vec<ChcDtConstructor> = constructors
                    .iter()
                    .map(|ctor| ChcDtConstructor {
                        name: ctor.name.clone(),
                        selectors: ctor
                            .selectors
                            .iter()
                            .map(|sel| ChcDtSelector {
                                name: sel.name.clone(),
                                sort: self.resolve_sort_refs_seen(&sel.sort, seen_datatypes),
                            })
                            .collect(),
                    })
                    .collect();
                seen_datatypes.remove(name);
                ChcSort::Datatype {
                    name: name.clone(),
                    constructors: Arc::new(resolved_ctors),
                }
            }
            // Scalar sorts: no resolution needed.
            _ => sort.clone(),
        }
    }

    /// Resolve DT sort references in a top-level DT sort (convenience wrapper).
    fn resolve_dt_sort_refs(&self, sort: &ChcSort) -> ChcSort {
        self.resolve_sort_refs(sort)
    }

    /// Parse a rule command
    fn parse_rule(&mut self) -> ChcResult<()> {
        self.skip_whitespace_and_comments();
        let expr = self.parse_expr()?;

        // Convert expression to Horn clause
        self.add_expr_as_clause(expr)?;
        Ok(())
    }

    /// Parse a fixture-only action declaration.
    ///
    /// This is intentionally `ay-` prefixed so normal CHC-COMP commands keep
    /// their existing semantics.
    fn parse_ay_declare_action(&mut self) -> ChcResult<()> {
        self.skip_whitespace_and_comments();
        let action_name = self.parse_symbol()?;

        if self.actions.contains_key(&action_name) {
            return Err(ChcError::Parse(format!(
                "Duplicate ay action declaration: {action_name}"
            )));
        }

        let action_id = self.problem.declare_action(action_name.clone());
        self.actions.insert(action_name, action_id);
        Ok(())
    }

    /// Parse a fixture-only action-tagged rule.
    fn parse_ay_action_rule(&mut self) -> ChcResult<()> {
        self.skip_whitespace_and_comments();
        let action_name = self.parse_symbol()?;
        let action_id = self.actions.get(&action_name).copied().ok_or_else(|| {
            ChcError::Parse(format!(
                "Unknown ay action in ay-action-rule: {action_name}. Declare it first with (ay-declare-action {action_name})."
            ))
        })?;

        self.skip_whitespace_and_comments();
        let expr = self.parse_expr()?;
        self.add_expr_as_clause_with_action(expr, action_id)?;
        Ok(())
    }

    /// Parse a query command
    fn parse_query(&mut self) -> ChcResult<()> {
        self.skip_whitespace_and_comments();

        // Query can be a predicate name or an expression
        if self.peek_char() == Some('(') {
            // Expression form
            let expr = self.parse_expr()?;
            // Extract predicates/constraints so the solver can reason about the query predicate.
            // Add as a clause: (preds /\ constraint) => false
            let (preds, constraint) = self.extract_body_parts(&expr);
            let body = if preds.is_empty() && constraint.is_none() {
                ClauseBody::constraint(ChcExpr::Bool(true))
            } else {
                ClauseBody::new(preds, constraint)
            };
            let clause = HornClause::new(body, ClauseHead::False);
            self.problem.add_clause(clause);
        } else {
            // Predicate name form
            let pred_name = self.parse_symbol()?;
            if let Some((pred_id, sorts)) = self.predicates.get(&pred_name).cloned() {
                // Create a query: Pred(x1, ..., xn) => false
                let args: Vec<ChcExpr> = sorts
                    .iter()
                    .enumerate()
                    .map(|(i, sort)| ChcExpr::var(ChcVar::new(format!("_qv{i}"), sort.clone())))
                    .collect();
                let clause = HornClause::new(
                    ClauseBody::new(vec![(pred_id, args)], None),
                    ClauseHead::False,
                );
                self.problem.add_clause(clause);
            } else {
                return Err(ChcError::Parse(format!(
                    "Unknown predicate in query: {pred_name}"
                )));
            }
        }

        Ok(())
    }
}
