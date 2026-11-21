// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Owned rule metadata copied by proof-retention caches. An unknown future
//! rule cannot silently acquire an unpriced equality or clone operation.

use ay_core::AletheRule;

pub(super) enum RuleOwnedPayload<'a> {
    Fixed,
    Text(&'a str),
}

pub(super) fn rule_owned_payload(rule: &AletheRule) -> Option<RuleOwnedPayload<'_>> {
    use AletheRule::*;

    match rule {
        Custom(name) => Some(RuleOwnedPayload::Text(name)),
        True | False | NotTrue | NotFalse | And | AndPos(_) | AndNeg | NotAnd | Or | OrPos(_)
        | OrNeg | NotOr | Implies | ImpliesNeg1 | ImpliesNeg2 | NotImplies1 | NotImplies2
        | Equiv | EquivPos1 | EquivPos2 | EquivNeg1 | EquivNeg2 | NotEquiv1 | NotEquiv2 | Ite
        | ItePos1 | ItePos2 | IteNeg1 | IteNeg2 | NotIte1 | NotIte2 | Ite1 | Ite2 | IteIntro
        | XorPos1 | XorPos2 | XorNeg1 | XorNeg2 | ImpliesPos | Resolution | ThResolution
        | Contraction | Weakening | Refl | Symm | Trans | Cong | EqReflexive | EqSymmetric
        | EqTransitive | EqCongruent | EqCongruentPred | DistinctElim | LaTautology | LaGeneric
        | LaDisequality | LaTotality | LaMultPos | LaMultNeg | LiaGeneric | ForallInst | Skolem
        | Subproof | Bind | AllSimplify | BoolSimplify | ArithSimplify | BvBitblast
        | ReadOverWritePos | ReadOverWriteNeg | StorePermutation | ReadOverWriteChain
        | Extensionality | ArrayExtDiffIntro | FpToBv | StringLength | StringDecompose
        | StringCodeInj | Hole | Drup | Trust | Evaluate | QntNegExists | FreshDefBound
        | FreshDefEq | Reordering | QntJoin | DivModDef => Some(RuleOwnedPayload::Fixed),
        _ => None,
    }
}
