// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Parser for SMT-LIB invariant definitions.
//!
//! Expression parsing (recursive-descent for SMT-LIB expressions) is in
//! `parse_expr`.

mod parse_expr;

use crate::error::ChcError;
use crate::{
    ChcDtConstructor, ChcDtSelector, ChcExpr, ChcOp, ChcProblem, ChcResult, ChcSort, ChcVar,
    PredicateId,
};
use ay_core::kani_compat::DetHashMap as FxHashMap;
use std::sync::Arc;

use super::model::{InvariantModel, PredicateInterpretation};

/// Parser for SMT-LIB invariant definitions
pub(crate) struct InvariantParser<'a> {
    input: &'a str,
    pos: usize,
    /// Map from predicate name to predicate info
    pred_map: FxHashMap<String, (PredicateId, Vec<ChcSort>)>,
    /// Datatype constructor/selector/tester signatures visible in invariant
    /// model bodies.
    function_sigs: FxHashMap<String, (ChcSort, Vec<ChcSort>)>,
    /// Declared datatype sorts by name.
    datatype_sorts: FxHashMap<String, ChcSort>,
}

impl<'a> InvariantParser<'a> {
    pub(crate) fn new(input: &'a str, problem: &ChcProblem) -> Self {
        let mut pred_map = FxHashMap::default();
        for pred in problem.predicates() {
            pred_map.insert(pred.name.clone(), (pred.id, pred.arg_sorts.clone()));
        }
        let datatype_sorts = collect_datatype_sorts(problem);
        let function_sigs = datatype_function_signatures(problem, &datatype_sorts);
        Self {
            input,
            pos: 0,
            pred_map,
            function_sigs,
            datatype_sorts,
        }
    }

    pub(crate) fn parse(&mut self) -> ChcResult<InvariantModel> {
        let mut model = InvariantModel::new();

        while self.pos < self.input.len() {
            self.skip_whitespace_and_comments();
            if self.pos >= self.input.len() {
                break;
            }

            // Look for (define-fun ...) or ( (define-fun ...) ) (Spacer format)
            if self.peek_char() == Some('(') {
                self.pos += 1;
                self.skip_whitespace_and_comments();

                // Check for Spacer format wrapper
                if self.peek_char() == Some('(') {
                    // Spacer format: ( (define-fun ...) (define-fun ...) )
                    while self.peek_char() == Some('(') {
                        self.pos += 1;
                        self.skip_whitespace_and_comments();

                        let cmd = self.parse_symbol()?;
                        if cmd == "define-fun" {
                            self.parse_define_fun(&mut model)?;
                        } else {
                            // Skip unknown command
                            self.skip_sexp()?;
                        }
                        self.skip_whitespace_and_comments();
                    }
                    // Skip closing paren of wrapper
                    if self.peek_char() == Some(')') {
                        self.pos += 1;
                    }
                } else {
                    let cmd = self.parse_symbol()?;
                    if cmd == "define-fun" {
                        self.parse_define_fun(&mut model)?;
                    } else {
                        // Skip unknown command
                        self.skip_sexp()?;
                    }
                }
            } else {
                // Skip any other character
                self.pos += 1;
            }
        }

        Ok(model)
    }

    fn parse_define_fun(&mut self, model: &mut InvariantModel) -> ChcResult<()> {
        self.skip_whitespace_and_comments();

        // Parse predicate name
        let pred_name = self.parse_symbol()?;
        self.skip_whitespace_and_comments();

        // Check if this predicate exists in the problem
        let (pred_id, expected_sorts) = match self.pred_map.get(&pred_name) {
            Some((id, sorts)) => (*id, sorts.clone()),
            None => {
                // Skip this definition - predicate not in problem
                self.skip_sexp()?; // params
                self.skip_sexp()?; // return type
                self.skip_sexp()?; // body
                self.expect_char(')')?;
                return Ok(());
            }
        };

        // Parse parameters: ((x Int) (y Bool) ...)
        self.expect_char('(')?;
        let mut vars = Vec::new();
        loop {
            self.skip_whitespace_and_comments();
            if self.peek_char() == Some(')') {
                break;
            }
            self.expect_char('(')?;
            self.skip_whitespace_and_comments();
            let var_name = self.parse_symbol()?;
            self.skip_whitespace_and_comments();
            let parsed_sort = self.parse_sort()?;
            let sort = expected_sorts
                .get(vars.len())
                .filter(|expected| sorts_compatible(expected, &parsed_sort))
                .cloned()
                .unwrap_or(parsed_sort);
            self.skip_whitespace_and_comments();
            self.expect_char(')')?;
            vars.push(ChcVar::new(var_name, sort));
        }
        self.expect_char(')')?;

        // Verify parameter count matches
        if vars.len() != expected_sorts.len() {
            return Err(ChcError::Parse(format!(
                "Parameter count mismatch for {}: expected {}, got {}",
                pred_name,
                expected_sorts.len(),
                vars.len()
            )));
        }

        self.skip_whitespace_and_comments();

        // Parse return type (should be Bool)
        let ret_sort = self.parse_sort()?;
        if ret_sort != ChcSort::Bool {
            return Err(ChcError::Parse(format!(
                "Invariant {pred_name} must return Bool, got {ret_sort:?}"
            )));
        }

        self.skip_whitespace_and_comments();

        // Parse body expression
        let body = self.parse_expr(&vars)?;

        self.skip_whitespace_and_comments();
        self.expect_char(')')?;

        // Create interpretation
        let interp = PredicateInterpretation::new(vars, body);
        model.set(pred_id, interp);

        Ok(())
    }

    fn parse_expr_list(&mut self, vars: &[ChcVar]) -> ChcResult<Vec<ChcExpr>> {
        let mut args = Vec::new();
        loop {
            self.skip_whitespace_and_comments();
            if self.peek_char() == Some(')') {
                break;
            }
            args.push(self.parse_expr(vars)?);
        }
        Ok(args)
    }

    fn parse_sort(&mut self) -> ChcResult<ChcSort> {
        self.skip_whitespace_and_comments();

        if self.peek_char() == Some('(') {
            // Parametric sort like (Array Int Int) or indexed sort like (_ BitVec 32)
            self.pos += 1;
            self.skip_whitespace_and_comments();

            let head = self.parse_symbol()?;
            self.skip_whitespace_and_comments();

            if head == "_" {
                let sort_name = self.parse_symbol()?;
                self.skip_whitespace_and_comments();

                match sort_name.as_str() {
                    "BitVec" => {
                        const MAX_INVARIANT_BITVECTOR_WIDTH: u32 = 1 << 20;
                        let parsed_width = self.parse_numeral()?;
                        let width = u32::try_from(parsed_width).map_err(|_| {
                            ChcError::Parse(format!(
                                "bitvector width {parsed_width} does not fit in u32"
                            ))
                        })?;
                        if width == 0 || width > MAX_INVARIANT_BITVECTOR_WIDTH {
                            return Err(ChcError::Parse(format!(
                                "bitvector width {width} is outside the supported range 1..={MAX_INVARIANT_BITVECTOR_WIDTH}"
                            )));
                        }
                        self.skip_whitespace_and_comments();
                        self.expect_char(')')?;
                        Ok(ChcSort::BitVec(width))
                    }
                    _ => Err(ChcError::Parse(format!(
                        "Unknown indexed sort: {sort_name}"
                    ))),
                }
            } else if head == "Array" {
                let key_sort = self.parse_sort()?;
                self.skip_whitespace_and_comments();
                let val_sort = self.parse_sort()?;
                self.skip_whitespace_and_comments();
                self.expect_char(')')?;
                Ok(ChcSort::Array(Box::new(key_sort), Box::new(val_sort)))
            } else {
                // AY doesn't currently represent parametric sort applications. Consume the
                // arguments to keep parsing consistent and treat it as an uninterpreted sort.
                while self.peek_char() != Some(')') {
                    self.skip_sexp()?;
                    self.skip_whitespace_and_comments();
                }
                self.expect_char(')')?;
                Ok(ChcSort::Uninterpreted(head))
            }
        } else {
            let name = self.parse_symbol()?;
            match name.as_str() {
                "Bool" => Ok(ChcSort::Bool),
                "Int" => Ok(ChcSort::Int),
                "Real" => Ok(ChcSort::Real),
                _ => Ok(self
                    .datatype_sorts
                    .get(&name)
                    .cloned()
                    .unwrap_or(ChcSort::Uninterpreted(name))),
            }
        }
    }

    pub(super) fn function_signature(
        &self,
        name: &str,
        arity: usize,
    ) -> Option<&(ChcSort, Vec<ChcSort>)> {
        self.function_sigs
            .get(name)
            .filter(|(_, args)| args.len() == arity)
    }

    fn parse_symbol(&mut self) -> ChcResult<String> {
        self.skip_whitespace_and_comments();

        let start = self.pos;

        // Check for quoted symbol
        if self.peek_char() == Some('|') {
            self.pos += 1;
            let content_start = self.pos;
            while self.pos < self.input.len() && self.current_char() != Some('|') {
                self.pos += 1;
            }
            let symbol = self.input[content_start..self.pos].to_string();
            if self.current_char() == Some('|') {
                self.pos += 1;
            }
            return Ok(symbol);
        }

        // Regular symbol
        while self.pos < self.input.len() {
            match self.current_char() {
                Some(c) if is_symbol_char(c) => self.pos += 1,
                _ => break,
            }
        }

        if start == self.pos {
            return Err(ChcError::Parse("Expected symbol".into()));
        }

        Ok(self.input[start..self.pos].to_string())
    }

    fn parse_numeral(&mut self) -> ChcResult<i64> {
        self.skip_whitespace_and_comments();

        let start = self.pos;

        while self.pos < self.input.len() {
            match self.current_char() {
                Some(c) if c.is_ascii_digit() => self.pos += 1,
                _ => break,
            }
        }

        if start == self.pos {
            return Err(ChcError::Parse("Expected numeral".into()));
        }

        self.input[start..self.pos]
            .parse()
            .map_err(|_| ChcError::Parse("Invalid numeral".into()))
    }

    fn skip_whitespace_and_comments(&mut self) {
        while self.pos < self.input.len() {
            match self.current_char() {
                Some(c) if c.is_whitespace() => self.pos += 1,
                Some(';') => {
                    // Skip until end of line
                    while self.pos < self.input.len() && self.current_char() != Some('\n') {
                        self.pos += 1;
                    }
                }
                _ => break,
            }
        }
    }

    fn skip_sexp(&mut self) -> ChcResult<()> {
        self.skip_whitespace_and_comments();
        if self.peek_char() == Some('(') {
            let mut depth = 1;
            self.pos += 1;
            while depth > 0 && self.pos < self.input.len() {
                match self.current_char() {
                    Some('(') => depth += 1,
                    Some(')') => depth -= 1,
                    _ => {}
                }
                self.pos += 1;
            }
        } else {
            // Skip single token
            while self.pos < self.input.len() {
                match self.current_char() {
                    Some(c) if c.is_whitespace() || c == ')' => break,
                    _ => self.pos += 1,
                }
            }
        }
        Ok(())
    }

    fn expect_char(&mut self, expected: char) -> ChcResult<()> {
        self.skip_whitespace_and_comments();
        match self.current_char() {
            Some(c) if c == expected => {
                self.pos += 1;
                Ok(())
            }
            Some(c) => Err(ChcError::Parse(format!(
                "Expected '{expected}', found '{c}'"
            ))),
            None => Err(ChcError::Parse(format!(
                "Expected '{expected}', found end of input"
            ))),
        }
    }

    fn current_char(&self) -> Option<char> {
        self.input[self.pos..].chars().next()
    }

    fn peek_char(&self) -> Option<char> {
        self.current_char()
    }
}

fn collect_datatype_sorts(problem: &ChcProblem) -> FxHashMap<String, ChcSort> {
    let mut sorts = FxHashMap::default();
    for pred in problem.predicates() {
        for sort in &pred.arg_sorts {
            collect_datatype_sort(sort, &mut sorts);
        }
    }
    for name in problem.datatype_defs().keys() {
        if !sorts.contains_key(name) {
            if let Some(sort) = build_datatype_sort(name, problem, &mut Vec::new()) {
                sorts.insert(name.clone(), sort);
            }
        }
    }
    sorts
}

fn collect_datatype_sort(sort: &ChcSort, out: &mut FxHashMap<String, ChcSort>) {
    match sort {
        ChcSort::Datatype { name, constructors } => {
            out.entry(name.clone()).or_insert_with(|| sort.clone());
            for ctor in constructors.iter() {
                for selector in &ctor.selectors {
                    collect_datatype_sort(&selector.sort, out);
                }
            }
        }
        ChcSort::Array(key, value) => {
            collect_datatype_sort(key, out);
            collect_datatype_sort(value, out);
        }
        _ => {}
    }
}

fn build_datatype_sort(
    name: &str,
    problem: &ChcProblem,
    stack: &mut Vec<String>,
) -> Option<ChcSort> {
    if stack.iter().any(|seen| seen == name) {
        return Some(ChcSort::Uninterpreted(name.to_string()));
    }
    let ctors = problem.datatype_defs().get(name)?;
    stack.push(name.to_string());
    let constructors = ctors
        .iter()
        .map(|(ctor_name, selectors)| ChcDtConstructor {
            name: ctor_name.clone(),
            selectors: selectors
                .iter()
                .map(|(selector_name, selector_sort)| ChcDtSelector {
                    name: selector_name.clone(),
                    sort: resolve_datatype_sort(selector_sort, problem, stack),
                })
                .collect(),
        })
        .collect();
    stack.pop();
    Some(ChcSort::Datatype {
        name: name.to_string(),
        constructors: Arc::new(constructors),
    })
}

fn resolve_datatype_sort(sort: &ChcSort, problem: &ChcProblem, stack: &mut Vec<String>) -> ChcSort {
    match sort {
        ChcSort::Uninterpreted(name) => {
            build_datatype_sort(name, problem, stack).unwrap_or_else(|| sort.clone())
        }
        ChcSort::Array(key, value) => ChcSort::Array(
            Box::new(resolve_datatype_sort(key, problem, stack)),
            Box::new(resolve_datatype_sort(value, problem, stack)),
        ),
        _ => sort.clone(),
    }
}

fn datatype_function_signatures(
    problem: &ChcProblem,
    datatype_sorts: &FxHashMap<String, ChcSort>,
) -> FxHashMap<String, (ChcSort, Vec<ChcSort>)> {
    let mut signatures = FxHashMap::default();
    for (dt_name, constructors) in problem.datatype_defs() {
        let dt_sort = datatype_sorts
            .get(dt_name)
            .cloned()
            .unwrap_or_else(|| ChcSort::Uninterpreted(dt_name.clone()));
        for (ctor_name, selectors) in constructors {
            let selector_sorts: Vec<ChcSort> =
                selectors.iter().map(|(_, sort)| sort.clone()).collect();
            signatures.insert(ctor_name.clone(), (dt_sort.clone(), selector_sorts));
            signatures.insert(
                format!("is-{ctor_name}"),
                (ChcSort::Bool, vec![dt_sort.clone()]),
            );
            for (selector_name, selector_sort) in selectors {
                signatures.insert(
                    selector_name.clone(),
                    (selector_sort.clone(), vec![dt_sort.clone()]),
                );
            }
        }
    }
    signatures
}

fn sorts_compatible(expected: &ChcSort, actual: &ChcSort) -> bool {
    match (expected, actual) {
        (ChcSort::Array(expected_key, expected_val), ChcSort::Array(actual_key, actual_val)) => {
            sorts_compatible(expected_key, actual_key) && sorts_compatible(expected_val, actual_val)
        }
        (ChcSort::Datatype { name: expected, .. }, ChcSort::Datatype { name: actual, .. })
        | (ChcSort::Datatype { name: expected, .. }, ChcSort::Uninterpreted(actual))
        | (ChcSort::Uninterpreted(expected), ChcSort::Datatype { name: actual, .. }) => {
            expected == actual
        }
        _ => expected == actual,
    }
}

/// Fallibly type-check a parsed invariant body at the strict replay boundary.
///
/// The general model parser is intentionally permissive because solver model
/// syntax varies. Replay artifacts are not: every variable must be one of the
/// predicate binders, every function must be a declared datatype operation,
/// and every operation must be recursively well-sorted with bounded BV widths.
pub(crate) fn validate_qf_expression(
    problem: &ChcProblem,
    vars: &[ChcVar],
    expression: &ChcExpr,
) -> ChcResult<ChcSort> {
    let datatype_sorts = collect_datatype_sorts(problem);
    let function_sigs = datatype_function_signatures(problem, &datatype_sorts);
    let mut bindings = FxHashMap::default();
    for variable in vars {
        validate_qf_sort(&variable.sort)?;
        if bindings
            .insert(variable.name.as_str(), &variable.sort)
            .is_some()
        {
            return Err(ChcError::Parse(format!(
                "duplicate invariant binder `{}`",
                variable.name
            )));
        }
    }
    validate_qf_expression_inner(expression, &bindings, &function_sigs)
}

const MAX_QF_INVARIANT_BITVECTOR_WIDTH: u32 = 1 << 20;

fn validate_qf_sort(sort: &ChcSort) -> ChcResult<()> {
    match sort {
        ChcSort::BitVec(width)
            if *width == 0 || *width > MAX_QF_INVARIANT_BITVECTOR_WIDTH =>
        {
            Err(ChcError::Parse(format!(
                "bitvector width {width} is outside the replay range 1..={MAX_QF_INVARIANT_BITVECTOR_WIDTH}"
            )))
        }
        ChcSort::Array(key, value) => {
            validate_qf_sort(key)?;
            validate_qf_sort(value)
        }
        _ => Ok(()),
    }
}

fn validate_qf_expression_inner(
    expression: &ChcExpr,
    bindings: &FxHashMap<&str, &ChcSort>,
    function_sigs: &FxHashMap<String, (ChcSort, Vec<ChcSort>)>,
) -> ChcResult<ChcSort> {
    match expression {
        ChcExpr::Bool(_) => Ok(ChcSort::Bool),
        ChcExpr::Int(_) => Ok(ChcSort::Int),
        ChcExpr::Real(_, _) => Ok(ChcSort::Real),
        ChcExpr::BitVec(value, width) => {
            let sort = ChcSort::BitVec(*width);
            validate_qf_sort(&sort)?;
            if *width < u128::BITS && *value >= (1_u128 << width) {
                return Err(ChcError::Parse(format!(
                    "bitvector literal {value} does not fit width {width}"
                )));
            }
            Ok(sort)
        }
        ChcExpr::Var(variable) => {
            let Some(expected_sort) = bindings.get(variable.name.as_str()) else {
                return Err(ChcError::Parse(format!(
                    "free invariant variable `{}`",
                    variable.name
                )));
            };
            if !sorts_compatible(expected_sort, &variable.sort) {
                return Err(ChcError::Parse(format!(
                    "invariant variable `{}` has sort {}, expected {}",
                    variable.name, variable.sort, expected_sort
                )));
            }
            Ok((*expected_sort).clone())
        }
        ChcExpr::PredicateApp(name, _, _) => Err(ChcError::Parse(format!(
            "predicate reference `{name}` is not a closed QF interpretation"
        ))),
        ChcExpr::FuncApp(name, return_sort, args) => {
            let Some((expected_return, expected_args)) = function_sigs.get(name) else {
                return Err(ChcError::Parse(format!(
                    "unknown function `{name}` in invariant interpretation"
                )));
            };
            if args.len() != expected_args.len() {
                return Err(ChcError::Parse(format!(
                    "function `{name}` has {} arguments, expected {}",
                    args.len(),
                    expected_args.len()
                )));
            }
            if !sorts_compatible(expected_return, return_sort) {
                return Err(ChcError::Parse(format!(
                    "function `{name}` carries return sort {return_sort}, expected {expected_return}"
                )));
            }
            for (index, (argument, expected_sort)) in
                args.iter().zip(expected_args.iter()).enumerate()
            {
                let actual_sort = validate_qf_expression_inner(argument, bindings, function_sigs)?;
                if !sorts_compatible(expected_sort, &actual_sort) {
                    return Err(ChcError::Parse(format!(
                        "function `{name}` argument {index} has sort {actual_sort}, expected {expected_sort}"
                    )));
                }
            }
            validate_qf_sort(expected_return)?;
            Ok(expected_return.clone())
        }
        ChcExpr::ConstArray(key_sort, value) => {
            validate_qf_sort(key_sort)?;
            let value_sort = validate_qf_expression_inner(value, bindings, function_sigs)?;
            validate_qf_sort(&value_sort)?;
            Ok(ChcSort::Array(
                Box::new(key_sort.clone()),
                Box::new(value_sort),
            ))
        }
        ChcExpr::ConstArrayMarker(_) | ChcExpr::IsTesterMarker(_) => Err(ChcError::Parse(
            "internal parser marker escaped into invariant interpretation".into(),
        )),
        ChcExpr::Op(op, args) => {
            let argument_sorts = args
                .iter()
                .map(|argument| validate_qf_expression_inner(argument, bindings, function_sigs))
                .collect::<ChcResult<Vec<_>>>()?;
            validate_qf_operation(*op, &argument_sorts)
        }
    }
}

fn validate_qf_operation(op: ChcOp, args: &[ChcSort]) -> ChcResult<ChcSort> {
    let arity = |expected: usize| {
        if args.len() == expected {
            Ok(())
        } else {
            Err(ChcError::Parse(format!(
                "operator {op:?} has {} arguments, expected {expected}",
                args.len()
            )))
        }
    };
    let same_sort = |left: &ChcSort, right: &ChcSort| sorts_compatible(left, right);
    let numeric = |sort: &ChcSort| matches!(sort, ChcSort::Int | ChcSort::Real);
    let binary_bv_width = || -> ChcResult<u32> {
        arity(2)?;
        match (&args[0], &args[1]) {
            (ChcSort::BitVec(left), ChcSort::BitVec(right)) if left == right => Ok(*left),
            _ => Err(ChcError::Parse(format!(
                "operator {op:?} requires equal-width bitvector operands"
            ))),
        }
    };

    match op {
        ChcOp::Not => {
            arity(1)?;
            require_sort(&args[0], &ChcSort::Bool, op)?;
            Ok(ChcSort::Bool)
        }
        ChcOp::And | ChcOp::Or => {
            if args.len() < 2 || !args.iter().all(|sort| *sort == ChcSort::Bool) {
                return Err(ChcError::Parse(format!(
                    "operator {op:?} requires at least two Bool operands"
                )));
            }
            Ok(ChcSort::Bool)
        }
        ChcOp::Implies | ChcOp::Iff => {
            arity(2)?;
            require_sort(&args[0], &ChcSort::Bool, op)?;
            require_sort(&args[1], &ChcSort::Bool, op)?;
            Ok(ChcSort::Bool)
        }
        ChcOp::Add | ChcOp::Mul => {
            if args.len() < 2
                || !numeric(&args[0])
                || !args.iter().skip(1).all(|sort| same_sort(&args[0], sort))
            {
                return Err(ChcError::Parse(format!(
                    "operator {op:?} requires at least two same-sorted numeric operands"
                )));
            }
            Ok(args[0].clone())
        }
        ChcOp::Sub | ChcOp::Div => {
            arity(2)?;
            if !numeric(&args[0]) || !same_sort(&args[0], &args[1]) {
                return Err(ChcError::Parse(format!(
                    "operator {op:?} requires same-sorted numeric operands"
                )));
            }
            Ok(args[0].clone())
        }
        ChcOp::Mod => {
            arity(2)?;
            require_sort(&args[0], &ChcSort::Int, op)?;
            require_sort(&args[1], &ChcSort::Int, op)?;
            Ok(ChcSort::Int)
        }
        ChcOp::Neg => {
            arity(1)?;
            if !numeric(&args[0]) {
                return Err(ChcError::Parse(format!(
                    "operator {op:?} requires a numeric operand"
                )));
            }
            Ok(args[0].clone())
        }
        ChcOp::Eq | ChcOp::Ne => {
            arity(2)?;
            if !same_sort(&args[0], &args[1]) {
                return Err(ChcError::Parse(format!(
                    "operator {op:?} requires same-sorted operands"
                )));
            }
            Ok(ChcSort::Bool)
        }
        ChcOp::Lt | ChcOp::Le | ChcOp::Gt | ChcOp::Ge => {
            arity(2)?;
            if !numeric(&args[0]) || !same_sort(&args[0], &args[1]) {
                return Err(ChcError::Parse(format!(
                    "operator {op:?} requires same-sorted numeric operands"
                )));
            }
            Ok(ChcSort::Bool)
        }
        ChcOp::Ite => {
            arity(3)?;
            require_sort(&args[0], &ChcSort::Bool, op)?;
            if !same_sort(&args[1], &args[2]) {
                return Err(ChcError::Parse("ite branches have different sorts".into()));
            }
            Ok(args[1].clone())
        }
        ChcOp::Select => {
            arity(2)?;
            let ChcSort::Array(key, value) = &args[0] else {
                return Err(ChcError::Parse("select target is not an array".into()));
            };
            if !same_sort(key, &args[1]) {
                return Err(ChcError::Parse("select index has the wrong sort".into()));
            }
            Ok((**value).clone())
        }
        ChcOp::Store => {
            arity(3)?;
            let ChcSort::Array(key, value) = &args[0] else {
                return Err(ChcError::Parse("store target is not an array".into()));
            };
            if !same_sort(key, &args[1]) || !same_sort(value, &args[2]) {
                return Err(ChcError::Parse(
                    "store index or value has the wrong sort".into(),
                ));
            }
            Ok(args[0].clone())
        }
        ChcOp::BvAdd
        | ChcOp::BvSub
        | ChcOp::BvMul
        | ChcOp::BvUDiv
        | ChcOp::BvURem
        | ChcOp::BvSDiv
        | ChcOp::BvSRem
        | ChcOp::BvSMod
        | ChcOp::BvAnd
        | ChcOp::BvOr
        | ChcOp::BvXor
        | ChcOp::BvNand
        | ChcOp::BvNor
        | ChcOp::BvXnor
        | ChcOp::BvShl
        | ChcOp::BvLShr
        | ChcOp::BvAShr => Ok(ChcSort::BitVec(binary_bv_width()?)),
        ChcOp::BvULt
        | ChcOp::BvULe
        | ChcOp::BvUGt
        | ChcOp::BvUGe
        | ChcOp::BvSLt
        | ChcOp::BvSLe
        | ChcOp::BvSGt
        | ChcOp::BvSGe => {
            binary_bv_width()?;
            Ok(ChcSort::Bool)
        }
        ChcOp::BvComp => {
            binary_bv_width()?;
            Ok(ChcSort::BitVec(1))
        }
        ChcOp::BvNot | ChcOp::BvNeg => {
            arity(1)?;
            let ChcSort::BitVec(width) = args[0] else {
                return Err(ChcError::Parse(format!(
                    "operator {op:?} requires a bitvector operand"
                )));
            };
            Ok(ChcSort::BitVec(width))
        }
        ChcOp::BvConcat => {
            arity(2)?;
            let (ChcSort::BitVec(left), ChcSort::BitVec(right)) = (&args[0], &args[1]) else {
                return Err(ChcError::Parse(
                    "concat requires two bitvector operands".into(),
                ));
            };
            bounded_bv_result(left.checked_add(*right), "concat")
        }
        ChcOp::Bv2Nat => {
            arity(1)?;
            if !matches!(args[0], ChcSort::BitVec(_)) {
                return Err(ChcError::Parse(
                    "bv2nat requires a bitvector operand".into(),
                ));
            }
            Ok(ChcSort::Int)
        }
        ChcOp::BvExtract(high, low) => {
            arity(1)?;
            let ChcSort::BitVec(width) = args[0] else {
                return Err(ChcError::Parse(
                    "extract requires a bitvector operand".into(),
                ));
            };
            if high < low || high >= width {
                return Err(ChcError::Parse(format!(
                    "extract range {high}:{low} is outside bitvector width {width}"
                )));
            }
            Ok(ChcSort::BitVec(high - low + 1))
        }
        ChcOp::BvZeroExtend(extra) | ChcOp::BvSignExtend(extra) => {
            arity(1)?;
            let ChcSort::BitVec(width) = args[0] else {
                return Err(ChcError::Parse(format!(
                    "operator {op:?} requires a bitvector operand"
                )));
            };
            bounded_bv_result(width.checked_add(extra), "bitvector extension")
        }
        ChcOp::BvRotateLeft(_) | ChcOp::BvRotateRight(_) => {
            arity(1)?;
            let ChcSort::BitVec(width) = args[0] else {
                return Err(ChcError::Parse(format!(
                    "operator {op:?} requires a bitvector operand"
                )));
            };
            Ok(ChcSort::BitVec(width))
        }
        ChcOp::BvRepeat(count) => {
            arity(1)?;
            let ChcSort::BitVec(width) = args[0] else {
                return Err(ChcError::Parse(
                    "repeat requires a bitvector operand".into(),
                ));
            };
            if count == 0 {
                return Err(ChcError::Parse("repeat count must be positive".into()));
            }
            bounded_bv_result(width.checked_mul(count), "bitvector repeat")
        }
        ChcOp::Int2Bv(width) => {
            arity(1)?;
            require_sort(&args[0], &ChcSort::Int, op)?;
            validate_qf_sort(&ChcSort::BitVec(width))?;
            Ok(ChcSort::BitVec(width))
        }
    }
}

fn require_sort(actual: &ChcSort, expected: &ChcSort, op: ChcOp) -> ChcResult<()> {
    if sorts_compatible(expected, actual) {
        Ok(())
    } else {
        Err(ChcError::Parse(format!(
            "operator {op:?} has operand sort {actual}, expected {expected}"
        )))
    }
}

fn bounded_bv_result(width: Option<u32>, operation: &str) -> ChcResult<ChcSort> {
    let Some(width) = width else {
        return Err(ChcError::Parse(format!(
            "{operation} result width overflowed u32"
        )));
    };
    let sort = ChcSort::BitVec(width);
    validate_qf_sort(&sort)?;
    Ok(sort)
}

/// Check if a character is valid in a symbol
fn is_symbol_char(c: char) -> bool {
    c.is_alphanumeric()
        || matches!(
            c,
            '_' | '-'
                | '+'
                | '*'
                | '/'
                | '.'
                | '!'
                | '@'
                | '#'
                | '$'
                | '%'
                | '^'
                | '&'
                | '<'
                | '>'
                | '='
                | '?'
                | '~'
                | '\''
        )
}

#[cfg(test)]
mod tests;
