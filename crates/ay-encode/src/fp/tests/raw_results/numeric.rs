// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Whole native words, not sampled bits or Rust/source replay credentials.
use super::*;

mod refusals;
mod resources;
mod semantics;

#[derive(Clone, Copy, Debug)]
enum Kind {
    Signed,
    Unsigned,
}

impl Kind {
    fn operation(self, input: &Expr) -> FpRawOperation<'_> {
        match self {
            Self::Signed => FpRawOperation::SignedIntegerToFpRne(input),
            Self::Unsigned => FpRawOperation::UnsignedIntegerToFpRne(input),
        }
    }
}

fn word_case(
    kind: Kind,
    input_width: u32,
    bits: u64,
    output_width: u32,
    expected: u64,
    budget: &mut WorkBudget<'_>,
    end: Instant,
) {
    for correct in [true, false] {
        budget.admit(FIXTURE, FIXTURE).unwrap();
        let (input, vi) = raw("integer_input", input_width);
        let (output, vo) = raw("integer_output", output_width);
        let results = [FpRawResultRelation {
            operation: kind.operation(&input),
            output: &output,
        }];
        let bindings = [
            FpExprInputBinding {
                source: &input,
                target: &vi,
            },
            FpExprInputBinding {
                source: &output,
                target: &vo,
            },
        ];
        let roots = [Expr::true_(), Expr::true_()];
        let problem = ChcProblem::new();
        let output_pin = pin(&vo, expected, output_width);
        let constraint = conjunction(vec![
            pin(&vi, bits, input_width),
            if correct {
                output_pin
            } else {
                negate(output_pin)
            },
        ]);
        let body = {
            let (body, source) =
                lower_fp_raw_result_clause(&roots, &results, &bindings, &problem, budget)
                    .unwrap()
                    .into_body(ClauseBody::constraint(constraint))
                    .unwrap()
                    .into_parts()
                    .unwrap();
            assert!(std::ptr::eq(source.roots(), roots.as_slice()));
            assert!(std::ptr::eq(source.raw_results(), results.as_slice()));
            assert!(std::ptr::eq(source.bindings()[0].source, &raw const input));
            assert!(std::ptr::eq(source.bindings()[1].source, &raw const output));
            body
        };
        // The negative is ANY different complete output word, not one wrong bit.
        native(body, correct, budget, end);
        drop(roots);
        drop(input);
        drop(output);
        drop(problem);
        budget.charge(0).unwrap();
    }
}
