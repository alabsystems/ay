use std::rc::Rc;

use crate::prelude::*;
use veripb_formula::prelude::DBConstraint;
use veripb_rules::{EndProof, keywords::PROOF_END};

use super::Checkable;

/// Return an error when the given bool flags indicate an
/// invalid state at the point where [`EndProof`] rule is encountered.
pub fn validate_end_proof_usage(
    has_end_proof: bool,
    has_output: bool,
    has_conclusion: bool,
) -> Result<(), CheckingError> {
    if has_end_proof {
        return Err(CheckingError::DoubleEnd);
    }
    if !has_output || !has_conclusion {
        return Err(CheckingError::WrongFooterOrder(PROOF_END));
    }
    Ok(())
}

impl Checkable for EndProof {
    #[inline]
    fn compute(
        &mut self,
        context: &mut Context,
        _database: &mut Database,
    ) -> Result<Vec<Rc<DBConstraint>>, CheckingError> {
        validate_end_proof_usage(
            context.has_end_proof,
            context.has_output,
            context.has_conclusion,
        )?;
        context.has_end_proof = true;
        Ok(vec![])
    }
}
