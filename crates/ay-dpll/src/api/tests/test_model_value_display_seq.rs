// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use crate::api::ModelValue;

#[test]
fn test_seq_display() {
    assert_eq!(format!("{}", ModelValue::Seq(Vec::new())), "seq.empty");
    assert_eq!(
        format!("{}", ModelValue::Seq(vec![ModelValue::Int(1.into())])),
        "(seq.unit 1)"
    );
    assert_eq!(
        format!(
            "{}",
            ModelValue::Seq(vec![
                ModelValue::Int(1.into()),
                ModelValue::Int(2.into()),
                ModelValue::Int(3.into()),
            ])
        ),
        "(seq.++ (seq.++ (seq.unit 1) (seq.unit 2)) (seq.unit 3))"
    );
}
