// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

/// Yun's loop terminates on an input that made a defective version spin forever.
#[test]
fn yun_terminates_on_the_input_that_span_forever() {
    let input = ZPoly::from_coeffs(
        [-2304i64, -384, 512, 56, -39, -2, 1]
            .iter()
            .map(|&k| BigInt::from(k))
            .collect(),
    );
    let d = input
        .square_free_decomposition()
        .expect("a correct Yun answers this input");
    let mut prod = ZPoly::from_coeffs(vec![d.c.clone()]);
    for (f, e) in &d.factors {
        for _ in 0..*e {
            prod = prod.mul(f);
        }
    }
    assert_eq!(prod, input, "c * prod f_i^i must equal the input EXACTLY");
}
