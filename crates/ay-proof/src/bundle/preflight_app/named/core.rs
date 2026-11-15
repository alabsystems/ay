// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

pub(super) fn validate(app: &mut App<'_, '_>, rule: Rule) -> Result<(), ProofCheckError> {
    let valid = match rule {
        Rule::Equal => {
            app.arity(2)?;
            let (left, right) = (app.arg(0)?, app.arg(1)?);
            matches!(app.result, Sort::Bool) && app.equal_sorts(left, right)?
        }
        Rule::Distinct => distinct(app)?,
        Rule::Not => {
            app.arity(1)?;
            matches!(app.result, Sort::Bool) && matches!(app.arg(0)?, Sort::Bool)
        }
        Rule::Bools => matches!(app.result, Sort::Bool) && app.args_boolean()?,
        Rule::Implies => {
            app.args.len() >= 2 && matches!(app.result, Sort::Bool) && app.args_boolean()?
        }
        Rule::Ite => {
            app.arity(3)?;
            let (condition, left, right) = (app.arg(0)?, app.arg(1)?, app.arg(2)?);
            matches!(condition, Sort::Bool)
                && app.equal_sorts(left, right)?
                && app.equal_sorts(left, app.result)?
        }
        Rule::Select | Rule::Store | Rule::ConstArray => return array(app, rule),
        _ => return Err(ProofCheckError::ResourceLimit),
    };
    if !valid {
        let reason = match rule {
            Rule::Equal => "must return Bool and compare equal-sorted operands",
            Rule::Distinct => "must return Bool and use one operand sort",
            Rule::Not => "must have signature Bool -> Bool",
            Rule::Bools => "must consume and return Bool",
            Rule::Implies => "must consume at least two Bool operands and return Bool",
            Rule::Ite => "condition, branches, and result are inconsistently sorted",
            _ => return Err(ProofCheckError::ResourceLimit),
        };
        return app.invalid(reason);
    }
    Ok(())
}

fn distinct(app: &mut App<'_, '_>) -> Result<bool, ProofCheckError> {
    if !matches!(app.result, Sort::Bool) {
        return Ok(false);
    }
    if app.args.is_empty() {
        return Ok(true);
    }
    let first = app.arg(0)?;
    for index in 1..app.args.len() {
        let next = app.arg(index)?;
        if !app.equal_sorts(first, next)? {
            return Ok(false);
        }
    }
    Ok(true)
}

fn array(app: &mut App<'_, '_>, rule: Rule) -> Result<(), ProofCheckError> {
    let valid = match rule {
        Rule::Select => {
            app.arity(2)?;
            let Sort::Array(array) = app.arg(0)? else {
                return app.invalid("first operand is not an array");
            };
            let index = app.arg(1)?;
            app.equal_sorts(index, &array.index_sort)?
                && app.equal_sorts(app.result, &array.element_sort)?
        }
        Rule::Store => {
            app.arity(3)?;
            let array_sort = app.arg(0)?;
            let Sort::Array(array) = array_sort else {
                return app.invalid("first operand is not an array");
            };
            let (index, value) = (app.arg(1)?, app.arg(2)?);
            app.equal_sorts(index, &array.index_sort)?
                && app.equal_sorts(value, &array.element_sort)?
                && app.equal_sorts(app.result, array_sort)?
        }
        Rule::ConstArray => {
            app.arity(1)?;
            let Sort::Array(array) = app.result else {
                return app.invalid("result is not array-sorted");
            };
            let fill = app.arg(0)?;
            app.equal_sorts(fill, &array.element_sort)?
        }
        _ => return Err(ProofCheckError::ResourceLimit),
    };
    if !valid {
        return app.invalid(match rule {
            Rule::Select => "index or result sort disagrees with its array sort",
            Rule::Store => "index, value, or result sort disagrees with its array sort",
            Rule::ConstArray => "fill sort disagrees with its element sort",
            _ => return Err(ProofCheckError::ResourceLimit),
        });
    }
    Ok(())
}
