// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Conservative syntactic identity of planned slices, before circuit
//! allocation. Identity never exempts either side from source validation.

use super::*;

pub(super) fn same(
    left: &Piece,
    right: &Piece,
    poll: &mut dyn FnMut() -> Result<(), String>,
) -> Result<bool, String> {
    let mut pending = vec![(left, right)];
    while let Some((left, right)) = pending.pop() {
        poll()?;
        match (left, right) {
            (
                Piece::Narrow {
                    term: a,
                    high: ah,
                    low: al,
                },
                Piece::Narrow {
                    term: b,
                    high: bh,
                    low: bl,
                },
            ) if (a, ah, al) == (b, bh, bl) => {}
            (
                Piece::Constant {
                    value: a,
                    width: aw,
                },
                Piece::Constant {
                    value: b,
                    width: bw,
                },
            ) if (a, aw) == (b, bw) => {}
            (Piece::Splat { bit: a, width: aw }, Piece::Splat { bit: b, width: bw })
                if aw == bw =>
            {
                pending.push((a, b));
            }
            (
                Piece::Extract {
                    inner: a,
                    high: ah,
                    low: al,
                },
                Piece::Extract {
                    inner: b,
                    high: bh,
                    low: bl,
                },
            ) if (ah, al) == (bh, bl) => {
                pending.push((a, b));
            }
            (
                Piece::Join {
                    upper: au,
                    lower: al,
                    lower_width: aw,
                },
                Piece::Join {
                    upper: bu,
                    lower: bl,
                    lower_width: bw,
                },
            ) if aw == bw => {
                pending.extend([(au.as_ref(), bu.as_ref()), (al.as_ref(), bl.as_ref())]);
            }
            (
                Piece::Arithmetic {
                    operation: ao,
                    lhs: al,
                    rhs: ar,
                    carry: ac,
                    width: aw,
                    part: ap,
                },
                Piece::Arithmetic {
                    operation: bo,
                    lhs: bl,
                    rhs: br,
                    carry: bc,
                    width: bw,
                    part: bp,
                },
            ) if aw == bw && same_operation(*ao, *bo) && same_part(*ap, *bp) => {
                pending.extend([(al.as_ref(), bl.as_ref()), (ar.as_ref(), br.as_ref())]);
                match (ac, bc) {
                    (Some(a), Some(b)) => pending.push((a, b)),
                    (None, None) => {}
                    _ => return Ok(false),
                }
            }
            _ => return Ok(false),
        }
    }
    Ok(true)
}

fn same_operation(left: Arithmetic, right: Arithmetic) -> bool {
    matches!(
        (left, right),
        (Arithmetic::Add, Arithmetic::Add) | (Arithmetic::Sub, Arithmetic::Sub)
    )
}

fn same_part(left: Part, right: Part) -> bool {
    matches!(
        (left, right),
        (Part::Value, Part::Value) | (Part::Carry, Part::Carry)
    )
}
