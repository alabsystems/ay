// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Test-only mathematical word evaluator. It is not an accepted certificate
//! or a production model replay path. Opaque BigUint allocation is test work.

use super::*;
use graph::{Binary, Operation};

impl Reference<'_, '_> {
    pub(super) fn evaluate(&mut self, inputs: &[(TermId, BigUint)]) -> Result<(Raw, bool)> {
        self.charge(0, 0)?;
        let mut values = Vec::<BigUint>::new();
        for index in 0..self.nodes.len() {
            self.charge(1, 0)?;
            let node = self.nodes[index];
            let modulus = BigUint::one() << node.width;
            let mask = &modulus - BigUint::one();
            let value = match node.operation {
                Operation::Input(id) => match self.terms.get(id) {
                    TermData::Const(Constant::BitVec { value, .. }) => value.magnitude().clone(),
                    _ => inputs
                        .iter()
                        .find(|(key, _)| *key == id)
                        .map(|(_, value)| value.clone())
                        .ok_or(ReferenceError::Source)?,
                },
                Operation::Small(value) => BigUint::from(value),
                Operation::Ones => mask.clone(),
                Operation::Not(input) => &mask ^ &values[input.0],
                Operation::Resize(input) => &values[input.0] & &mask,
                Operation::Extract(input, _, low) => (&values[input.0] >> low) & &mask,
                Operation::Select(condition, yes, no) => {
                    if values[condition.0].is_zero() {
                        values[no.0].clone()
                    } else {
                        values[yes.0].clone()
                    }
                }
                Operation::Binary(op, a, b) => {
                    let a = &values[a.0];
                    let b = &values[b.0];
                    match op {
                        Binary::Add => (a + b) & &mask,
                        Binary::Sub => ((a + &modulus) - b) & &mask,
                        Binary::Mul => (a * b) & &mask,
                        Binary::And => a & b,
                        Binary::Or => a | b,
                        Binary::Xor => a ^ b,
                        Binary::Eq => BigUint::from(u8::from(a == b)),
                        Binary::Ult => BigUint::from(u8::from(a < b)),
                        Binary::Shl | Binary::Lshr => {
                            if b >= &BigUint::from(node.width) {
                                BigUint::zero()
                            } else {
                                let amount = b.to_usize().expect("bounded test shift");
                                if op == Binary::Shl {
                                    (a << amount) & &mask
                                } else {
                                    a >> amount
                                }
                            }
                        }
                    }
                }
            };
            if value.bits() > u64::from(node.width) {
                return Err(ReferenceError::Source);
            }
            values.push(value);
        }
        let output = self.output.ok_or(ReferenceError::Source)?;
        let value = Raw {
            sign: values[output.sign.0]
                .to_u64()
                .ok_or(ReferenceError::Source)?,
            exponent: values[output.exponent.0]
                .to_u64()
                .ok_or(ReferenceError::Source)?,
            fraction: values[output.fraction.0]
                .to_u128()
                .ok_or(ReferenceError::Source)?,
        };
        let domain = values[output.rm_domain.0] == BigUint::one();
        self.charge(0, 0)?;
        Ok((value, domain))
    }
}
