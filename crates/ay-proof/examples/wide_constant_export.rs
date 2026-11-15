//! Regression for zero-padding a literal wider than its u128 storage.
//! The legacy expression exporter must not panic or wrap a host shift.
use ay_proof::{
    export_bv_blast_proof_expr, export_bv_blast_proof_expr_bounded, BvExpr, BvExprExportError,
    BvExprProofBudget,
};
use std::{error::Error, time::Duration};

fn equality(lhs: &BvExpr, rhs: &BvExpr, expected: bool) -> Result<(), Box<dyn Error>> {
    // Keep the exporter's top-level result within its existing 64-bit cap.
    // The source operands can be wider inside an explicit Boolean equality.
    let holds = BvExpr::Eq(Box::new(lhs.clone()), Box::new(rhs.clone()));
    match export_bv_blast_proof_expr(&holds, &BvExpr::const_val(1, 1)) {
        Ok(proof) if expected => {
            proof.validate()?;
            Ok(())
        }
        Err(BvExprExportError::NoRefutation) if !expected => Ok(()),
        Ok(_) => Err("false equality produced a refutation".into()),
        Err(error) => Err(format!("unexpected export refusal: {error:?}").into()),
    }
}

fn main() -> Result<(), Box<dyn Error>> {
    let budget = BvExprProofBudget::conservative(Duration::from_secs(5), 200_000)?;
    let mut exports = 0;
    for width in [129, 256] {
        for value in [0, 1, u128::MAX] {
            let literal = BvExpr::Const { value, width };
            let high = BvExpr::extract(literal.clone(), width - 1, 128);
            let high_zero = BvExpr::const_val(0, width - 128);
            equality(&high, &high_zero, true)?;
            equality(&high, &BvExpr::const_val(1, width - 128), false)?;
            // The low stored bits must survive; fixing the high bits must not
            // turn the whole literal into zero or silently truncate the width.
            let low = BvExpr::extract(literal, 127, 0);
            equality(&low, &BvExpr::const_val(value, 128), true)?;
            equality(&low, &BvExpr::const_val(value ^ 1, 128), false)?;
            exports += 4;
            match export_bv_blast_proof_expr_bounded(&high, &high_zero, &budget) {
                Err(BvExprExportError::UnsupportedWidth { got, max })
                    if got == width && max == 128 => {}
                _ => return Err("bounded producer's internal width limit changed".into()),
            }
        }
    }
    for (value, width) in [(1, 0), (2, 1)] {
        let bad = BvExpr::Const { value, width };
        if !matches!(
            export_bv_blast_proof_expr(&bad, &bad),
            Err(BvExprExportError::Malformed(_))
        ) {
            return Err("malformed constant was not rejected".into());
        }
    }
    println!("{exports} exports checked: true graphs replayed, false equalities refused; six bounded width refusals and two malformed controls passed");
    Ok(())
}
