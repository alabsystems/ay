//! Hand-written serde impls for [`TheoryLemmaKind`].
//
//! These reproduce byte-for-byte what `#[derive(Serialize, Deserialize)]` with
//! `#[serde(deny_unknown_fields)]` generated for this enum (externally tagged,
//! same variant order, indices, and names; unknown struct-variant fields
//! rejected), written as plain matches with no operation that can panic. The
//! derive expansion carried Trust L0 panic-freedom obligations the verifier
//! could not discharge; this form discharges them by construction.

use super::{BvGateType, FpOp, TheoryLemmaKind};
use serde::de::{
    Deserialize, Deserializer, EnumAccess, Error as DeError, MapAccess, SeqAccess, Unexpected,
    VariantAccess, Visitor,
};
use serde::ser::{Serialize, SerializeStructVariant, Serializer};
use std::fmt;

const VARIANTS: &[&str] = &[
    "EufTransitive",
    "EufReflexive",
    "EufCongruent",
    "EufCongruentPred",
    "EufCongruenceExplanation",
    "LraFarkas",
    "LiaGeneric",
    "LiaModRange",
    "BvLiaTautology",
    "SeqExtensionalCompanionContradiction",
    "BvBitBlast",
    "BvBitBlastGate",
    "ArraySelectStore",
    "ArrayStorePermutation",
    "ArrayRowChain",
    "ArrayDefaultConst",
    "SetCardNonNegative",
    "SetCardMemberLowerBound",
    "SetCardEmpty",
    "SetCardMemberCount",
    "SetCardEmptyByAssertion",
    "SetCardChainRecurrence",
    "SubsetReflexive",
    "SubsetElementInstance",
    "SubsetTransitive",
    "SubsetGroundEval",
    "ArrayExtensionality",
    "FpToBv",
    "StringLengthAxiom",
    "StringLengthLemma",
    "StringContentAxiom",
    "StringNormalForm",
    "StringGroundEval",
    "SeqGroundEval",
    "ArithClauseTautology",
    "IteBranchProjection",
    "ArrayGuardedRowExpansion",
    "RegexIntersectEmpty",
    "StringContainmentIdentity",
    "StringConcatCancellation",
    "StringGroundFactorConflict",
    "RegexLengthLowerBound",
    "DatatypeDistinct",
    "DatatypeEnumPigeonhole",
    "DatatypeSelectorProject",
    "DatatypeTesterEval",
    "DatatypeTesterExclusive",
    "DatatypeExhaustive",
    "DatatypeConstructorReconstruct",
    "DatatypeInjective",
    "DatatypeAcyclicDirect",
    "DatatypeValueEqCongruence",
    "DatatypeGroundConflict",
    "OrderIteTautology",
    "BoolTautology",
    "ArithEqTriangle",
    "ArithEqImpliesBound",
    "IntBoundsTautology",
    "ArithDisequalitySplit",
    "IntBoundLatticeGap",
    "IntCutLatticeGap",
    "IntGuardedSplitGap",
    "IteSame",
    "FpClassification",
    "FpRoundingModeDomain",
    "FpForwardError",
    "NraIntervalUnsat",
    "NraUnivariateUnsat",
    "Generic",
    "RoundingModeDomain",
    "FpGroundEval",
    "ArrayFiniteExtensionality",
    "ArrayFiniteSelectExpansion",
    "QuantifierNegatedExistsDual",
    "GroundEqualitySubstitution",
];

impl Serialize for TheoryLemmaKind {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        match *self {
            TheoryLemmaKind::EufTransitive => {
                serializer.serialize_unit_variant("TheoryLemmaKind", 0, "EufTransitive")
            }
            TheoryLemmaKind::EufReflexive => {
                serializer.serialize_unit_variant("TheoryLemmaKind", 1, "EufReflexive")
            }
            TheoryLemmaKind::EufCongruent => {
                serializer.serialize_unit_variant("TheoryLemmaKind", 2, "EufCongruent")
            }
            TheoryLemmaKind::EufCongruentPred => {
                serializer.serialize_unit_variant("TheoryLemmaKind", 3, "EufCongruentPred")
            }
            TheoryLemmaKind::EufCongruenceExplanation => {
                serializer.serialize_unit_variant("TheoryLemmaKind", 4, "EufCongruenceExplanation")
            }
            TheoryLemmaKind::LraFarkas => {
                serializer.serialize_unit_variant("TheoryLemmaKind", 5, "LraFarkas")
            }
            TheoryLemmaKind::LiaGeneric => {
                serializer.serialize_unit_variant("TheoryLemmaKind", 6, "LiaGeneric")
            }
            TheoryLemmaKind::LiaModRange => {
                serializer.serialize_unit_variant("TheoryLemmaKind", 7, "LiaModRange")
            }
            TheoryLemmaKind::BvLiaTautology => {
                serializer.serialize_unit_variant("TheoryLemmaKind", 8, "BvLiaTautology")
            }
            TheoryLemmaKind::SeqExtensionalCompanionContradiction => serializer
                .serialize_unit_variant(
                    "TheoryLemmaKind",
                    9,
                    "SeqExtensionalCompanionContradiction",
                ),
            TheoryLemmaKind::BvBitBlast => {
                serializer.serialize_unit_variant("TheoryLemmaKind", 10, "BvBitBlast")
            }
            TheoryLemmaKind::BvBitBlastGate {
                ref gate_type,
                ref width,
            } => {
                let mut sv = serializer.serialize_struct_variant(
                    "TheoryLemmaKind",
                    11,
                    "BvBitBlastGate",
                    2,
                )?;
                sv.serialize_field("gate_type", gate_type)?;
                sv.serialize_field("width", width)?;
                sv.end()
            }
            TheoryLemmaKind::ArraySelectStore { ref index_eq } => {
                let mut sv = serializer.serialize_struct_variant(
                    "TheoryLemmaKind",
                    12,
                    "ArraySelectStore",
                    1,
                )?;
                sv.serialize_field("index_eq", index_eq)?;
                sv.end()
            }
            TheoryLemmaKind::ArrayStorePermutation => {
                serializer.serialize_unit_variant("TheoryLemmaKind", 13, "ArrayStorePermutation")
            }
            TheoryLemmaKind::ArrayRowChain => {
                serializer.serialize_unit_variant("TheoryLemmaKind", 14, "ArrayRowChain")
            }
            TheoryLemmaKind::ArrayDefaultConst => {
                serializer.serialize_unit_variant("TheoryLemmaKind", 15, "ArrayDefaultConst")
            }
            TheoryLemmaKind::SetCardNonNegative => {
                serializer.serialize_unit_variant("TheoryLemmaKind", 16, "SetCardNonNegative")
            }
            TheoryLemmaKind::SetCardMemberLowerBound => {
                serializer.serialize_unit_variant("TheoryLemmaKind", 17, "SetCardMemberLowerBound")
            }
            TheoryLemmaKind::SetCardEmpty => {
                serializer.serialize_unit_variant("TheoryLemmaKind", 18, "SetCardEmpty")
            }
            TheoryLemmaKind::SetCardMemberCount => {
                serializer.serialize_unit_variant("TheoryLemmaKind", 19, "SetCardMemberCount")
            }
            TheoryLemmaKind::SetCardEmptyByAssertion => {
                serializer.serialize_unit_variant("TheoryLemmaKind", 20, "SetCardEmptyByAssertion")
            }
            TheoryLemmaKind::SetCardChainRecurrence => {
                serializer.serialize_unit_variant("TheoryLemmaKind", 21, "SetCardChainRecurrence")
            }
            TheoryLemmaKind::SubsetReflexive => {
                serializer.serialize_unit_variant("TheoryLemmaKind", 22, "SubsetReflexive")
            }
            TheoryLemmaKind::SubsetElementInstance => {
                serializer.serialize_unit_variant("TheoryLemmaKind", 23, "SubsetElementInstance")
            }
            TheoryLemmaKind::SubsetTransitive => {
                serializer.serialize_unit_variant("TheoryLemmaKind", 24, "SubsetTransitive")
            }
            TheoryLemmaKind::SubsetGroundEval => {
                serializer.serialize_unit_variant("TheoryLemmaKind", 25, "SubsetGroundEval")
            }
            TheoryLemmaKind::ArrayExtensionality => {
                serializer.serialize_unit_variant("TheoryLemmaKind", 26, "ArrayExtensionality")
            }
            TheoryLemmaKind::FpToBv { ref operation } => {
                let mut sv =
                    serializer.serialize_struct_variant("TheoryLemmaKind", 27, "FpToBv", 1)?;
                sv.serialize_field("operation", operation)?;
                sv.end()
            }
            TheoryLemmaKind::StringLengthAxiom => {
                serializer.serialize_unit_variant("TheoryLemmaKind", 28, "StringLengthAxiom")
            }
            TheoryLemmaKind::StringLengthLemma => {
                serializer.serialize_unit_variant("TheoryLemmaKind", 29, "StringLengthLemma")
            }
            TheoryLemmaKind::StringContentAxiom => {
                serializer.serialize_unit_variant("TheoryLemmaKind", 30, "StringContentAxiom")
            }
            TheoryLemmaKind::StringNormalForm => {
                serializer.serialize_unit_variant("TheoryLemmaKind", 31, "StringNormalForm")
            }
            TheoryLemmaKind::StringGroundEval => {
                serializer.serialize_unit_variant("TheoryLemmaKind", 32, "StringGroundEval")
            }
            TheoryLemmaKind::SeqGroundEval => {
                serializer.serialize_unit_variant("TheoryLemmaKind", 33, "SeqGroundEval")
            }
            TheoryLemmaKind::ArithClauseTautology => {
                serializer.serialize_unit_variant("TheoryLemmaKind", 34, "ArithClauseTautology")
            }
            TheoryLemmaKind::IteBranchProjection => {
                serializer.serialize_unit_variant("TheoryLemmaKind", 35, "IteBranchProjection")
            }
            TheoryLemmaKind::ArrayGuardedRowExpansion => {
                serializer.serialize_unit_variant("TheoryLemmaKind", 36, "ArrayGuardedRowExpansion")
            }
            TheoryLemmaKind::RegexIntersectEmpty => {
                serializer.serialize_unit_variant("TheoryLemmaKind", 37, "RegexIntersectEmpty")
            }
            TheoryLemmaKind::StringContainmentIdentity => serializer.serialize_unit_variant(
                "TheoryLemmaKind",
                38,
                "StringContainmentIdentity",
            ),
            TheoryLemmaKind::StringConcatCancellation => {
                serializer.serialize_unit_variant("TheoryLemmaKind", 39, "StringConcatCancellation")
            }
            TheoryLemmaKind::StringGroundFactorConflict => serializer.serialize_unit_variant(
                "TheoryLemmaKind",
                40,
                "StringGroundFactorConflict",
            ),
            TheoryLemmaKind::RegexLengthLowerBound => {
                serializer.serialize_unit_variant("TheoryLemmaKind", 41, "RegexLengthLowerBound")
            }
            TheoryLemmaKind::DatatypeDistinct => {
                serializer.serialize_unit_variant("TheoryLemmaKind", 42, "DatatypeDistinct")
            }
            TheoryLemmaKind::DatatypeEnumPigeonhole => {
                serializer.serialize_unit_variant("TheoryLemmaKind", 43, "DatatypeEnumPigeonhole")
            }
            TheoryLemmaKind::DatatypeSelectorProject => {
                serializer.serialize_unit_variant("TheoryLemmaKind", 44, "DatatypeSelectorProject")
            }
            TheoryLemmaKind::DatatypeTesterEval => {
                serializer.serialize_unit_variant("TheoryLemmaKind", 45, "DatatypeTesterEval")
            }
            TheoryLemmaKind::DatatypeTesterExclusive => {
                serializer.serialize_unit_variant("TheoryLemmaKind", 46, "DatatypeTesterExclusive")
            }
            TheoryLemmaKind::DatatypeExhaustive => {
                serializer.serialize_unit_variant("TheoryLemmaKind", 47, "DatatypeExhaustive")
            }
            TheoryLemmaKind::DatatypeConstructorReconstruct => serializer.serialize_unit_variant(
                "TheoryLemmaKind",
                48,
                "DatatypeConstructorReconstruct",
            ),
            TheoryLemmaKind::DatatypeInjective => {
                serializer.serialize_unit_variant("TheoryLemmaKind", 49, "DatatypeInjective")
            }
            TheoryLemmaKind::DatatypeAcyclicDirect => {
                serializer.serialize_unit_variant("TheoryLemmaKind", 50, "DatatypeAcyclicDirect")
            }
            TheoryLemmaKind::DatatypeValueEqCongruence => serializer.serialize_unit_variant(
                "TheoryLemmaKind",
                51,
                "DatatypeValueEqCongruence",
            ),
            TheoryLemmaKind::DatatypeGroundConflict => {
                serializer.serialize_unit_variant("TheoryLemmaKind", 52, "DatatypeGroundConflict")
            }
            TheoryLemmaKind::OrderIteTautology => {
                serializer.serialize_unit_variant("TheoryLemmaKind", 53, "OrderIteTautology")
            }
            TheoryLemmaKind::BoolTautology => {
                serializer.serialize_unit_variant("TheoryLemmaKind", 54, "BoolTautology")
            }
            TheoryLemmaKind::ArithEqTriangle => {
                serializer.serialize_unit_variant("TheoryLemmaKind", 55, "ArithEqTriangle")
            }
            TheoryLemmaKind::ArithEqImpliesBound => {
                serializer.serialize_unit_variant("TheoryLemmaKind", 56, "ArithEqImpliesBound")
            }
            TheoryLemmaKind::IntBoundsTautology => {
                serializer.serialize_unit_variant("TheoryLemmaKind", 57, "IntBoundsTautology")
            }
            TheoryLemmaKind::ArithDisequalitySplit => {
                serializer.serialize_unit_variant("TheoryLemmaKind", 58, "ArithDisequalitySplit")
            }
            TheoryLemmaKind::IntBoundLatticeGap => {
                serializer.serialize_unit_variant("TheoryLemmaKind", 59, "IntBoundLatticeGap")
            }
            TheoryLemmaKind::IntCutLatticeGap => {
                serializer.serialize_unit_variant("TheoryLemmaKind", 60, "IntCutLatticeGap")
            }
            TheoryLemmaKind::IntGuardedSplitGap => {
                serializer.serialize_unit_variant("TheoryLemmaKind", 61, "IntGuardedSplitGap")
            }
            TheoryLemmaKind::IteSame => {
                serializer.serialize_unit_variant("TheoryLemmaKind", 62, "IteSame")
            }
            TheoryLemmaKind::FpClassification { ref operation } => {
                let mut sv = serializer.serialize_struct_variant(
                    "TheoryLemmaKind",
                    63,
                    "FpClassification",
                    1,
                )?;
                sv.serialize_field("operation", operation)?;
                sv.end()
            }
            TheoryLemmaKind::FpRoundingModeDomain => {
                serializer.serialize_unit_variant("TheoryLemmaKind", 64, "FpRoundingModeDomain")
            }
            TheoryLemmaKind::FpForwardError => {
                serializer.serialize_unit_variant("TheoryLemmaKind", 65, "FpForwardError")
            }
            TheoryLemmaKind::NraIntervalUnsat => {
                serializer.serialize_unit_variant("TheoryLemmaKind", 66, "NraIntervalUnsat")
            }
            TheoryLemmaKind::NraUnivariateUnsat => {
                serializer.serialize_unit_variant("TheoryLemmaKind", 67, "NraUnivariateUnsat")
            }
            TheoryLemmaKind::Generic => {
                serializer.serialize_unit_variant("TheoryLemmaKind", 68, "Generic")
            }
            TheoryLemmaKind::RoundingModeDomain => {
                serializer.serialize_unit_variant("TheoryLemmaKind", 69, "RoundingModeDomain")
            }
            TheoryLemmaKind::FpGroundEval => {
                serializer.serialize_unit_variant("TheoryLemmaKind", 70, "FpGroundEval")
            }
            TheoryLemmaKind::ArrayFiniteExtensionality => serializer.serialize_unit_variant(
                "TheoryLemmaKind",
                71,
                "ArrayFiniteExtensionality",
            ),
            TheoryLemmaKind::ArrayFiniteSelectExpansion => serializer.serialize_unit_variant(
                "TheoryLemmaKind",
                72,
                "ArrayFiniteSelectExpansion",
            ),
            TheoryLemmaKind::QuantifierNegatedExistsDual => serializer.serialize_unit_variant(
                "TheoryLemmaKind",
                73,
                "QuantifierNegatedExistsDual",
            ),
            TheoryLemmaKind::GroundEqualitySubstitution => serializer.serialize_unit_variant(
                "TheoryLemmaKind",
                74,
                "GroundEqualitySubstitution",
            ),
        }
    }
}

enum VariantTag {
    EufTransitive,
    EufReflexive,
    EufCongruent,
    EufCongruentPred,
    EufCongruenceExplanation,
    LraFarkas,
    LiaGeneric,
    LiaModRange,
    BvLiaTautology,
    SeqExtensionalCompanionContradiction,
    BvBitBlast,
    BvBitBlastGate,
    ArraySelectStore,
    ArrayStorePermutation,
    ArrayRowChain,
    ArrayDefaultConst,
    SetCardNonNegative,
    SetCardMemberLowerBound,
    SetCardEmpty,
    SetCardMemberCount,
    SetCardEmptyByAssertion,
    SetCardChainRecurrence,
    SubsetReflexive,
    SubsetElementInstance,
    SubsetTransitive,
    SubsetGroundEval,
    ArrayExtensionality,
    FpToBv,
    StringLengthAxiom,
    StringLengthLemma,
    StringContentAxiom,
    StringNormalForm,
    StringGroundEval,
    SeqGroundEval,
    ArithClauseTautology,
    IteBranchProjection,
    ArrayGuardedRowExpansion,
    RegexIntersectEmpty,
    StringContainmentIdentity,
    StringConcatCancellation,
    StringGroundFactorConflict,
    RegexLengthLowerBound,
    DatatypeDistinct,
    DatatypeEnumPigeonhole,
    DatatypeSelectorProject,
    DatatypeTesterEval,
    DatatypeTesterExclusive,
    DatatypeExhaustive,
    DatatypeConstructorReconstruct,
    DatatypeInjective,
    DatatypeAcyclicDirect,
    DatatypeValueEqCongruence,
    DatatypeGroundConflict,
    OrderIteTautology,
    BoolTautology,
    ArithEqTriangle,
    ArithEqImpliesBound,
    IntBoundsTautology,
    ArithDisequalitySplit,
    IntBoundLatticeGap,
    IntCutLatticeGap,
    IntGuardedSplitGap,
    IteSame,
    FpClassification,
    FpRoundingModeDomain,
    FpForwardError,
    NraIntervalUnsat,
    NraUnivariateUnsat,
    Generic,
    RoundingModeDomain,
    FpGroundEval,
    ArrayFiniteExtensionality,
    ArrayFiniteSelectExpansion,
    QuantifierNegatedExistsDual,
    GroundEqualitySubstitution,
}

impl<'de> Deserialize<'de> for VariantTag {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        deserializer.deserialize_identifier(VariantTagVisitor)
    }
}

struct VariantTagVisitor;

impl Visitor<'_> for VariantTagVisitor {
    type Value = VariantTag;

    fn expecting(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter.write_str("variant identifier")
    }

    fn visit_u64<E>(self, value: u64) -> Result<Self::Value, E>
    where
        E: DeError,
    {
        match value {
            0 => Ok(VariantTag::EufTransitive),
            1 => Ok(VariantTag::EufReflexive),
            2 => Ok(VariantTag::EufCongruent),
            3 => Ok(VariantTag::EufCongruentPred),
            4 => Ok(VariantTag::EufCongruenceExplanation),
            5 => Ok(VariantTag::LraFarkas),
            6 => Ok(VariantTag::LiaGeneric),
            7 => Ok(VariantTag::LiaModRange),
            8 => Ok(VariantTag::BvLiaTautology),
            9 => Ok(VariantTag::SeqExtensionalCompanionContradiction),
            10 => Ok(VariantTag::BvBitBlast),
            11 => Ok(VariantTag::BvBitBlastGate),
            12 => Ok(VariantTag::ArraySelectStore),
            13 => Ok(VariantTag::ArrayStorePermutation),
            14 => Ok(VariantTag::ArrayRowChain),
            15 => Ok(VariantTag::ArrayDefaultConst),
            16 => Ok(VariantTag::SetCardNonNegative),
            17 => Ok(VariantTag::SetCardMemberLowerBound),
            18 => Ok(VariantTag::SetCardEmpty),
            19 => Ok(VariantTag::SetCardMemberCount),
            20 => Ok(VariantTag::SetCardEmptyByAssertion),
            21 => Ok(VariantTag::SetCardChainRecurrence),
            22 => Ok(VariantTag::SubsetReflexive),
            23 => Ok(VariantTag::SubsetElementInstance),
            24 => Ok(VariantTag::SubsetTransitive),
            25 => Ok(VariantTag::SubsetGroundEval),
            26 => Ok(VariantTag::ArrayExtensionality),
            27 => Ok(VariantTag::FpToBv),
            28 => Ok(VariantTag::StringLengthAxiom),
            29 => Ok(VariantTag::StringLengthLemma),
            30 => Ok(VariantTag::StringContentAxiom),
            31 => Ok(VariantTag::StringNormalForm),
            32 => Ok(VariantTag::StringGroundEval),
            33 => Ok(VariantTag::SeqGroundEval),
            34 => Ok(VariantTag::ArithClauseTautology),
            35 => Ok(VariantTag::IteBranchProjection),
            36 => Ok(VariantTag::ArrayGuardedRowExpansion),
            37 => Ok(VariantTag::RegexIntersectEmpty),
            38 => Ok(VariantTag::StringContainmentIdentity),
            39 => Ok(VariantTag::StringConcatCancellation),
            40 => Ok(VariantTag::StringGroundFactorConflict),
            41 => Ok(VariantTag::RegexLengthLowerBound),
            42 => Ok(VariantTag::DatatypeDistinct),
            43 => Ok(VariantTag::DatatypeEnumPigeonhole),
            44 => Ok(VariantTag::DatatypeSelectorProject),
            45 => Ok(VariantTag::DatatypeTesterEval),
            46 => Ok(VariantTag::DatatypeTesterExclusive),
            47 => Ok(VariantTag::DatatypeExhaustive),
            48 => Ok(VariantTag::DatatypeConstructorReconstruct),
            49 => Ok(VariantTag::DatatypeInjective),
            50 => Ok(VariantTag::DatatypeAcyclicDirect),
            51 => Ok(VariantTag::DatatypeValueEqCongruence),
            52 => Ok(VariantTag::DatatypeGroundConflict),
            53 => Ok(VariantTag::OrderIteTautology),
            54 => Ok(VariantTag::BoolTautology),
            55 => Ok(VariantTag::ArithEqTriangle),
            56 => Ok(VariantTag::ArithEqImpliesBound),
            57 => Ok(VariantTag::IntBoundsTautology),
            58 => Ok(VariantTag::ArithDisequalitySplit),
            59 => Ok(VariantTag::IntBoundLatticeGap),
            60 => Ok(VariantTag::IntCutLatticeGap),
            61 => Ok(VariantTag::IntGuardedSplitGap),
            62 => Ok(VariantTag::IteSame),
            63 => Ok(VariantTag::FpClassification),
            64 => Ok(VariantTag::FpRoundingModeDomain),
            65 => Ok(VariantTag::FpForwardError),
            66 => Ok(VariantTag::NraIntervalUnsat),
            67 => Ok(VariantTag::NraUnivariateUnsat),
            68 => Ok(VariantTag::Generic),
            69 => Ok(VariantTag::RoundingModeDomain),
            70 => Ok(VariantTag::FpGroundEval),
            71 => Ok(VariantTag::ArrayFiniteExtensionality),
            72 => Ok(VariantTag::ArrayFiniteSelectExpansion),
            73 => Ok(VariantTag::QuantifierNegatedExistsDual),
            74 => Ok(VariantTag::GroundEqualitySubstitution),
            _ => Err(DeError::invalid_value(
                Unexpected::Unsigned(value),
                &"variant index 0 <= i < 75",
            )),
        }
    }

    fn visit_str<E>(self, value: &str) -> Result<Self::Value, E>
    where
        E: DeError,
    {
        match value {
            "EufTransitive" => Ok(VariantTag::EufTransitive),
            "EufReflexive" => Ok(VariantTag::EufReflexive),
            "EufCongruent" => Ok(VariantTag::EufCongruent),
            "EufCongruentPred" => Ok(VariantTag::EufCongruentPred),
            "EufCongruenceExplanation" => Ok(VariantTag::EufCongruenceExplanation),
            "LraFarkas" => Ok(VariantTag::LraFarkas),
            "LiaGeneric" => Ok(VariantTag::LiaGeneric),
            "LiaModRange" => Ok(VariantTag::LiaModRange),
            "BvLiaTautology" => Ok(VariantTag::BvLiaTautology),
            "SeqExtensionalCompanionContradiction" => {
                Ok(VariantTag::SeqExtensionalCompanionContradiction)
            }
            "BvBitBlast" => Ok(VariantTag::BvBitBlast),
            "BvBitBlastGate" => Ok(VariantTag::BvBitBlastGate),
            "ArraySelectStore" => Ok(VariantTag::ArraySelectStore),
            "ArrayStorePermutation" => Ok(VariantTag::ArrayStorePermutation),
            "ArrayRowChain" => Ok(VariantTag::ArrayRowChain),
            "ArrayDefaultConst" => Ok(VariantTag::ArrayDefaultConst),
            "SetCardNonNegative" => Ok(VariantTag::SetCardNonNegative),
            "SetCardMemberLowerBound" => Ok(VariantTag::SetCardMemberLowerBound),
            "SetCardEmpty" => Ok(VariantTag::SetCardEmpty),
            "SetCardMemberCount" => Ok(VariantTag::SetCardMemberCount),
            "SetCardEmptyByAssertion" => Ok(VariantTag::SetCardEmptyByAssertion),
            "SetCardChainRecurrence" => Ok(VariantTag::SetCardChainRecurrence),
            "SubsetReflexive" => Ok(VariantTag::SubsetReflexive),
            "SubsetElementInstance" => Ok(VariantTag::SubsetElementInstance),
            "SubsetTransitive" => Ok(VariantTag::SubsetTransitive),
            "SubsetGroundEval" => Ok(VariantTag::SubsetGroundEval),
            "ArrayExtensionality" => Ok(VariantTag::ArrayExtensionality),
            "FpToBv" => Ok(VariantTag::FpToBv),
            "StringLengthAxiom" => Ok(VariantTag::StringLengthAxiom),
            "StringLengthLemma" => Ok(VariantTag::StringLengthLemma),
            "StringContentAxiom" => Ok(VariantTag::StringContentAxiom),
            "StringNormalForm" => Ok(VariantTag::StringNormalForm),
            "StringGroundEval" => Ok(VariantTag::StringGroundEval),
            "SeqGroundEval" => Ok(VariantTag::SeqGroundEval),
            "ArithClauseTautology" => Ok(VariantTag::ArithClauseTautology),
            "IteBranchProjection" => Ok(VariantTag::IteBranchProjection),
            "ArrayGuardedRowExpansion" => Ok(VariantTag::ArrayGuardedRowExpansion),
            "RegexIntersectEmpty" => Ok(VariantTag::RegexIntersectEmpty),
            "StringContainmentIdentity" => Ok(VariantTag::StringContainmentIdentity),
            "StringConcatCancellation" => Ok(VariantTag::StringConcatCancellation),
            "StringGroundFactorConflict" => Ok(VariantTag::StringGroundFactorConflict),
            "RegexLengthLowerBound" => Ok(VariantTag::RegexLengthLowerBound),
            "DatatypeDistinct" => Ok(VariantTag::DatatypeDistinct),
            "DatatypeEnumPigeonhole" => Ok(VariantTag::DatatypeEnumPigeonhole),
            "DatatypeSelectorProject" => Ok(VariantTag::DatatypeSelectorProject),
            "DatatypeTesterEval" => Ok(VariantTag::DatatypeTesterEval),
            "DatatypeTesterExclusive" => Ok(VariantTag::DatatypeTesterExclusive),
            "DatatypeExhaustive" => Ok(VariantTag::DatatypeExhaustive),
            "DatatypeConstructorReconstruct" => Ok(VariantTag::DatatypeConstructorReconstruct),
            "DatatypeInjective" => Ok(VariantTag::DatatypeInjective),
            "DatatypeAcyclicDirect" => Ok(VariantTag::DatatypeAcyclicDirect),
            "DatatypeValueEqCongruence" => Ok(VariantTag::DatatypeValueEqCongruence),
            "DatatypeGroundConflict" => Ok(VariantTag::DatatypeGroundConflict),
            "OrderIteTautology" => Ok(VariantTag::OrderIteTautology),
            "BoolTautology" => Ok(VariantTag::BoolTautology),
            "ArithEqTriangle" => Ok(VariantTag::ArithEqTriangle),
            "ArithEqImpliesBound" => Ok(VariantTag::ArithEqImpliesBound),
            "IntBoundsTautology" => Ok(VariantTag::IntBoundsTautology),
            "ArithDisequalitySplit" => Ok(VariantTag::ArithDisequalitySplit),
            "IntBoundLatticeGap" => Ok(VariantTag::IntBoundLatticeGap),
            "IntCutLatticeGap" => Ok(VariantTag::IntCutLatticeGap),
            "IntGuardedSplitGap" => Ok(VariantTag::IntGuardedSplitGap),
            "IteSame" => Ok(VariantTag::IteSame),
            "FpClassification" => Ok(VariantTag::FpClassification),
            "FpRoundingModeDomain" => Ok(VariantTag::FpRoundingModeDomain),
            "FpForwardError" => Ok(VariantTag::FpForwardError),
            "NraIntervalUnsat" => Ok(VariantTag::NraIntervalUnsat),
            "NraUnivariateUnsat" => Ok(VariantTag::NraUnivariateUnsat),
            "Generic" => Ok(VariantTag::Generic),
            "RoundingModeDomain" => Ok(VariantTag::RoundingModeDomain),
            "FpGroundEval" => Ok(VariantTag::FpGroundEval),
            "ArrayFiniteExtensionality" => Ok(VariantTag::ArrayFiniteExtensionality),
            "ArrayFiniteSelectExpansion" => Ok(VariantTag::ArrayFiniteSelectExpansion),
            "QuantifierNegatedExistsDual" => Ok(VariantTag::QuantifierNegatedExistsDual),
            "GroundEqualitySubstitution" => Ok(VariantTag::GroundEqualitySubstitution),
            _ => Err(DeError::unknown_variant(value, VARIANTS)),
        }
    }

    fn visit_bytes<E>(self, value: &[u8]) -> Result<Self::Value, E>
    where
        E: DeError,
    {
        match value {
            b"EufTransitive" => Ok(VariantTag::EufTransitive),
            b"EufReflexive" => Ok(VariantTag::EufReflexive),
            b"EufCongruent" => Ok(VariantTag::EufCongruent),
            b"EufCongruentPred" => Ok(VariantTag::EufCongruentPred),
            b"EufCongruenceExplanation" => Ok(VariantTag::EufCongruenceExplanation),
            b"LraFarkas" => Ok(VariantTag::LraFarkas),
            b"LiaGeneric" => Ok(VariantTag::LiaGeneric),
            b"LiaModRange" => Ok(VariantTag::LiaModRange),
            b"BvLiaTautology" => Ok(VariantTag::BvLiaTautology),
            b"SeqExtensionalCompanionContradiction" => {
                Ok(VariantTag::SeqExtensionalCompanionContradiction)
            }
            b"BvBitBlast" => Ok(VariantTag::BvBitBlast),
            b"BvBitBlastGate" => Ok(VariantTag::BvBitBlastGate),
            b"ArraySelectStore" => Ok(VariantTag::ArraySelectStore),
            b"ArrayStorePermutation" => Ok(VariantTag::ArrayStorePermutation),
            b"ArrayRowChain" => Ok(VariantTag::ArrayRowChain),
            b"ArrayDefaultConst" => Ok(VariantTag::ArrayDefaultConst),
            b"SetCardNonNegative" => Ok(VariantTag::SetCardNonNegative),
            b"SetCardMemberLowerBound" => Ok(VariantTag::SetCardMemberLowerBound),
            b"SetCardEmpty" => Ok(VariantTag::SetCardEmpty),
            b"SetCardMemberCount" => Ok(VariantTag::SetCardMemberCount),
            b"SetCardEmptyByAssertion" => Ok(VariantTag::SetCardEmptyByAssertion),
            b"SetCardChainRecurrence" => Ok(VariantTag::SetCardChainRecurrence),
            b"SubsetReflexive" => Ok(VariantTag::SubsetReflexive),
            b"SubsetElementInstance" => Ok(VariantTag::SubsetElementInstance),
            b"SubsetTransitive" => Ok(VariantTag::SubsetTransitive),
            b"SubsetGroundEval" => Ok(VariantTag::SubsetGroundEval),
            b"ArrayExtensionality" => Ok(VariantTag::ArrayExtensionality),
            b"FpToBv" => Ok(VariantTag::FpToBv),
            b"StringLengthAxiom" => Ok(VariantTag::StringLengthAxiom),
            b"StringLengthLemma" => Ok(VariantTag::StringLengthLemma),
            b"StringContentAxiom" => Ok(VariantTag::StringContentAxiom),
            b"StringNormalForm" => Ok(VariantTag::StringNormalForm),
            b"StringGroundEval" => Ok(VariantTag::StringGroundEval),
            b"SeqGroundEval" => Ok(VariantTag::SeqGroundEval),
            b"ArithClauseTautology" => Ok(VariantTag::ArithClauseTautology),
            b"IteBranchProjection" => Ok(VariantTag::IteBranchProjection),
            b"ArrayGuardedRowExpansion" => Ok(VariantTag::ArrayGuardedRowExpansion),
            b"RegexIntersectEmpty" => Ok(VariantTag::RegexIntersectEmpty),
            b"StringContainmentIdentity" => Ok(VariantTag::StringContainmentIdentity),
            b"StringConcatCancellation" => Ok(VariantTag::StringConcatCancellation),
            b"StringGroundFactorConflict" => Ok(VariantTag::StringGroundFactorConflict),
            b"RegexLengthLowerBound" => Ok(VariantTag::RegexLengthLowerBound),
            b"DatatypeDistinct" => Ok(VariantTag::DatatypeDistinct),
            b"DatatypeEnumPigeonhole" => Ok(VariantTag::DatatypeEnumPigeonhole),
            b"DatatypeSelectorProject" => Ok(VariantTag::DatatypeSelectorProject),
            b"DatatypeTesterEval" => Ok(VariantTag::DatatypeTesterEval),
            b"DatatypeTesterExclusive" => Ok(VariantTag::DatatypeTesterExclusive),
            b"DatatypeExhaustive" => Ok(VariantTag::DatatypeExhaustive),
            b"DatatypeConstructorReconstruct" => Ok(VariantTag::DatatypeConstructorReconstruct),
            b"DatatypeInjective" => Ok(VariantTag::DatatypeInjective),
            b"DatatypeAcyclicDirect" => Ok(VariantTag::DatatypeAcyclicDirect),
            b"DatatypeValueEqCongruence" => Ok(VariantTag::DatatypeValueEqCongruence),
            b"DatatypeGroundConflict" => Ok(VariantTag::DatatypeGroundConflict),
            b"OrderIteTautology" => Ok(VariantTag::OrderIteTautology),
            b"BoolTautology" => Ok(VariantTag::BoolTautology),
            b"ArithEqTriangle" => Ok(VariantTag::ArithEqTriangle),
            b"ArithEqImpliesBound" => Ok(VariantTag::ArithEqImpliesBound),
            b"IntBoundsTautology" => Ok(VariantTag::IntBoundsTautology),
            b"ArithDisequalitySplit" => Ok(VariantTag::ArithDisequalitySplit),
            b"IntBoundLatticeGap" => Ok(VariantTag::IntBoundLatticeGap),
            b"IntCutLatticeGap" => Ok(VariantTag::IntCutLatticeGap),
            b"IntGuardedSplitGap" => Ok(VariantTag::IntGuardedSplitGap),
            b"IteSame" => Ok(VariantTag::IteSame),
            b"FpClassification" => Ok(VariantTag::FpClassification),
            b"FpRoundingModeDomain" => Ok(VariantTag::FpRoundingModeDomain),
            b"FpForwardError" => Ok(VariantTag::FpForwardError),
            b"NraIntervalUnsat" => Ok(VariantTag::NraIntervalUnsat),
            b"NraUnivariateUnsat" => Ok(VariantTag::NraUnivariateUnsat),
            b"Generic" => Ok(VariantTag::Generic),
            b"RoundingModeDomain" => Ok(VariantTag::RoundingModeDomain),
            b"FpGroundEval" => Ok(VariantTag::FpGroundEval),
            b"ArrayFiniteExtensionality" => Ok(VariantTag::ArrayFiniteExtensionality),
            b"ArrayFiniteSelectExpansion" => Ok(VariantTag::ArrayFiniteSelectExpansion),
            b"QuantifierNegatedExistsDual" => Ok(VariantTag::QuantifierNegatedExistsDual),
            b"GroundEqualitySubstitution" => Ok(VariantTag::GroundEqualitySubstitution),
            _ => Err(DeError::unknown_variant(
                &String::from_utf8_lossy(value),
                VARIANTS,
            )),
        }
    }
}

struct KindVisitor;

impl<'de> Visitor<'de> for KindVisitor {
    type Value = TheoryLemmaKind;

    fn expecting(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter.write_str("enum TheoryLemmaKind")
    }

    fn visit_enum<A>(self, data: A) -> Result<Self::Value, A::Error>
    where
        A: EnumAccess<'de>,
    {
        match data.variant()? {
            (VariantTag::EufTransitive, variant) => {
                variant.unit_variant()?;
                Ok(TheoryLemmaKind::EufTransitive)
            }
            (VariantTag::EufReflexive, variant) => {
                variant.unit_variant()?;
                Ok(TheoryLemmaKind::EufReflexive)
            }
            (VariantTag::EufCongruent, variant) => {
                variant.unit_variant()?;
                Ok(TheoryLemmaKind::EufCongruent)
            }
            (VariantTag::EufCongruentPred, variant) => {
                variant.unit_variant()?;
                Ok(TheoryLemmaKind::EufCongruentPred)
            }
            (VariantTag::EufCongruenceExplanation, variant) => {
                variant.unit_variant()?;
                Ok(TheoryLemmaKind::EufCongruenceExplanation)
            }
            (VariantTag::LraFarkas, variant) => {
                variant.unit_variant()?;
                Ok(TheoryLemmaKind::LraFarkas)
            }
            (VariantTag::LiaGeneric, variant) => {
                variant.unit_variant()?;
                Ok(TheoryLemmaKind::LiaGeneric)
            }
            (VariantTag::LiaModRange, variant) => {
                variant.unit_variant()?;
                Ok(TheoryLemmaKind::LiaModRange)
            }
            (VariantTag::BvLiaTautology, variant) => {
                variant.unit_variant()?;
                Ok(TheoryLemmaKind::BvLiaTautology)
            }
            (VariantTag::SeqExtensionalCompanionContradiction, variant) => {
                variant.unit_variant()?;
                Ok(TheoryLemmaKind::SeqExtensionalCompanionContradiction)
            }
            (VariantTag::BvBitBlast, variant) => {
                variant.unit_variant()?;
                Ok(TheoryLemmaKind::BvBitBlast)
            }
            (VariantTag::BvBitBlastGate, variant) => {
                variant.struct_variant(BV_BIT_BLAST_GATE_FIELDS, BvBitBlastGateVisitor)
            }
            (VariantTag::ArraySelectStore, variant) => {
                variant.struct_variant(ARRAY_SELECT_STORE_FIELDS, ArraySelectStoreVisitor)
            }
            (VariantTag::ArrayStorePermutation, variant) => {
                variant.unit_variant()?;
                Ok(TheoryLemmaKind::ArrayStorePermutation)
            }
            (VariantTag::ArrayRowChain, variant) => {
                variant.unit_variant()?;
                Ok(TheoryLemmaKind::ArrayRowChain)
            }
            (VariantTag::ArrayDefaultConst, variant) => {
                variant.unit_variant()?;
                Ok(TheoryLemmaKind::ArrayDefaultConst)
            }
            (VariantTag::SetCardNonNegative, variant) => {
                variant.unit_variant()?;
                Ok(TheoryLemmaKind::SetCardNonNegative)
            }
            (VariantTag::SetCardMemberLowerBound, variant) => {
                variant.unit_variant()?;
                Ok(TheoryLemmaKind::SetCardMemberLowerBound)
            }
            (VariantTag::SetCardEmpty, variant) => {
                variant.unit_variant()?;
                Ok(TheoryLemmaKind::SetCardEmpty)
            }
            (VariantTag::SetCardMemberCount, variant) => {
                variant.unit_variant()?;
                Ok(TheoryLemmaKind::SetCardMemberCount)
            }
            (VariantTag::SetCardEmptyByAssertion, variant) => {
                variant.unit_variant()?;
                Ok(TheoryLemmaKind::SetCardEmptyByAssertion)
            }
            (VariantTag::SetCardChainRecurrence, variant) => {
                variant.unit_variant()?;
                Ok(TheoryLemmaKind::SetCardChainRecurrence)
            }
            (VariantTag::SubsetReflexive, variant) => {
                variant.unit_variant()?;
                Ok(TheoryLemmaKind::SubsetReflexive)
            }
            (VariantTag::SubsetElementInstance, variant) => {
                variant.unit_variant()?;
                Ok(TheoryLemmaKind::SubsetElementInstance)
            }
            (VariantTag::SubsetTransitive, variant) => {
                variant.unit_variant()?;
                Ok(TheoryLemmaKind::SubsetTransitive)
            }
            (VariantTag::SubsetGroundEval, variant) => {
                variant.unit_variant()?;
                Ok(TheoryLemmaKind::SubsetGroundEval)
            }
            (VariantTag::ArrayExtensionality, variant) => {
                variant.unit_variant()?;
                Ok(TheoryLemmaKind::ArrayExtensionality)
            }
            (VariantTag::FpToBv, variant) => variant.struct_variant(FP_TO_BV_FIELDS, FpToBvVisitor),
            (VariantTag::StringLengthAxiom, variant) => {
                variant.unit_variant()?;
                Ok(TheoryLemmaKind::StringLengthAxiom)
            }
            (VariantTag::StringLengthLemma, variant) => {
                variant.unit_variant()?;
                Ok(TheoryLemmaKind::StringLengthLemma)
            }
            (VariantTag::StringContentAxiom, variant) => {
                variant.unit_variant()?;
                Ok(TheoryLemmaKind::StringContentAxiom)
            }
            (VariantTag::StringNormalForm, variant) => {
                variant.unit_variant()?;
                Ok(TheoryLemmaKind::StringNormalForm)
            }
            (VariantTag::StringGroundEval, variant) => {
                variant.unit_variant()?;
                Ok(TheoryLemmaKind::StringGroundEval)
            }
            (VariantTag::SeqGroundEval, variant) => {
                variant.unit_variant()?;
                Ok(TheoryLemmaKind::SeqGroundEval)
            }
            (VariantTag::ArithClauseTautology, variant) => {
                variant.unit_variant()?;
                Ok(TheoryLemmaKind::ArithClauseTautology)
            }
            (VariantTag::IteBranchProjection, variant) => {
                variant.unit_variant()?;
                Ok(TheoryLemmaKind::IteBranchProjection)
            }
            (VariantTag::ArrayGuardedRowExpansion, variant) => {
                variant.unit_variant()?;
                Ok(TheoryLemmaKind::ArrayGuardedRowExpansion)
            }
            (VariantTag::RegexIntersectEmpty, variant) => {
                variant.unit_variant()?;
                Ok(TheoryLemmaKind::RegexIntersectEmpty)
            }
            (VariantTag::StringContainmentIdentity, variant) => {
                variant.unit_variant()?;
                Ok(TheoryLemmaKind::StringContainmentIdentity)
            }
            (VariantTag::StringConcatCancellation, variant) => {
                variant.unit_variant()?;
                Ok(TheoryLemmaKind::StringConcatCancellation)
            }
            (VariantTag::StringGroundFactorConflict, variant) => {
                variant.unit_variant()?;
                Ok(TheoryLemmaKind::StringGroundFactorConflict)
            }
            (VariantTag::RegexLengthLowerBound, variant) => {
                variant.unit_variant()?;
                Ok(TheoryLemmaKind::RegexLengthLowerBound)
            }
            (VariantTag::DatatypeDistinct, variant) => {
                variant.unit_variant()?;
                Ok(TheoryLemmaKind::DatatypeDistinct)
            }
            (VariantTag::DatatypeEnumPigeonhole, variant) => {
                variant.unit_variant()?;
                Ok(TheoryLemmaKind::DatatypeEnumPigeonhole)
            }
            (VariantTag::DatatypeSelectorProject, variant) => {
                variant.unit_variant()?;
                Ok(TheoryLemmaKind::DatatypeSelectorProject)
            }
            (VariantTag::DatatypeTesterEval, variant) => {
                variant.unit_variant()?;
                Ok(TheoryLemmaKind::DatatypeTesterEval)
            }
            (VariantTag::DatatypeTesterExclusive, variant) => {
                variant.unit_variant()?;
                Ok(TheoryLemmaKind::DatatypeTesterExclusive)
            }
            (VariantTag::DatatypeExhaustive, variant) => {
                variant.unit_variant()?;
                Ok(TheoryLemmaKind::DatatypeExhaustive)
            }
            (VariantTag::DatatypeConstructorReconstruct, variant) => {
                variant.unit_variant()?;
                Ok(TheoryLemmaKind::DatatypeConstructorReconstruct)
            }
            (VariantTag::DatatypeInjective, variant) => {
                variant.unit_variant()?;
                Ok(TheoryLemmaKind::DatatypeInjective)
            }
            (VariantTag::DatatypeAcyclicDirect, variant) => {
                variant.unit_variant()?;
                Ok(TheoryLemmaKind::DatatypeAcyclicDirect)
            }
            (VariantTag::DatatypeValueEqCongruence, variant) => {
                variant.unit_variant()?;
                Ok(TheoryLemmaKind::DatatypeValueEqCongruence)
            }
            (VariantTag::DatatypeGroundConflict, variant) => {
                variant.unit_variant()?;
                Ok(TheoryLemmaKind::DatatypeGroundConflict)
            }
            (VariantTag::OrderIteTautology, variant) => {
                variant.unit_variant()?;
                Ok(TheoryLemmaKind::OrderIteTautology)
            }
            (VariantTag::BoolTautology, variant) => {
                variant.unit_variant()?;
                Ok(TheoryLemmaKind::BoolTautology)
            }
            (VariantTag::ArithEqTriangle, variant) => {
                variant.unit_variant()?;
                Ok(TheoryLemmaKind::ArithEqTriangle)
            }
            (VariantTag::ArithEqImpliesBound, variant) => {
                variant.unit_variant()?;
                Ok(TheoryLemmaKind::ArithEqImpliesBound)
            }
            (VariantTag::IntBoundsTautology, variant) => {
                variant.unit_variant()?;
                Ok(TheoryLemmaKind::IntBoundsTautology)
            }
            (VariantTag::ArithDisequalitySplit, variant) => {
                variant.unit_variant()?;
                Ok(TheoryLemmaKind::ArithDisequalitySplit)
            }
            (VariantTag::IntBoundLatticeGap, variant) => {
                variant.unit_variant()?;
                Ok(TheoryLemmaKind::IntBoundLatticeGap)
            }
            (VariantTag::IntCutLatticeGap, variant) => {
                variant.unit_variant()?;
                Ok(TheoryLemmaKind::IntCutLatticeGap)
            }
            (VariantTag::IntGuardedSplitGap, variant) => {
                variant.unit_variant()?;
                Ok(TheoryLemmaKind::IntGuardedSplitGap)
            }
            (VariantTag::IteSame, variant) => {
                variant.unit_variant()?;
                Ok(TheoryLemmaKind::IteSame)
            }
            (VariantTag::FpClassification, variant) => {
                variant.struct_variant(FP_CLASSIFICATION_FIELDS, FpClassificationVisitor)
            }
            (VariantTag::FpRoundingModeDomain, variant) => {
                variant.unit_variant()?;
                Ok(TheoryLemmaKind::FpRoundingModeDomain)
            }
            (VariantTag::FpForwardError, variant) => {
                variant.unit_variant()?;
                Ok(TheoryLemmaKind::FpForwardError)
            }
            (VariantTag::NraIntervalUnsat, variant) => {
                variant.unit_variant()?;
                Ok(TheoryLemmaKind::NraIntervalUnsat)
            }
            (VariantTag::NraUnivariateUnsat, variant) => {
                variant.unit_variant()?;
                Ok(TheoryLemmaKind::NraUnivariateUnsat)
            }
            (VariantTag::Generic, variant) => {
                variant.unit_variant()?;
                Ok(TheoryLemmaKind::Generic)
            }
            (VariantTag::RoundingModeDomain, variant) => {
                variant.unit_variant()?;
                Ok(TheoryLemmaKind::RoundingModeDomain)
            }
            (VariantTag::FpGroundEval, variant) => {
                variant.unit_variant()?;
                Ok(TheoryLemmaKind::FpGroundEval)
            }
            (VariantTag::ArrayFiniteExtensionality, variant) => {
                variant.unit_variant()?;
                Ok(TheoryLemmaKind::ArrayFiniteExtensionality)
            }
            (VariantTag::ArrayFiniteSelectExpansion, variant) => {
                variant.unit_variant()?;
                Ok(TheoryLemmaKind::ArrayFiniteSelectExpansion)
            }
            (VariantTag::QuantifierNegatedExistsDual, variant) => {
                variant.unit_variant()?;
                Ok(TheoryLemmaKind::QuantifierNegatedExistsDual)
            }
            (VariantTag::GroundEqualitySubstitution, variant) => {
                variant.unit_variant()?;
                Ok(TheoryLemmaKind::GroundEqualitySubstitution)
            }
        }
    }
}

impl<'de> Deserialize<'de> for TheoryLemmaKind {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        deserializer.deserialize_enum("TheoryLemmaKind", VARIANTS, KindVisitor)
    }
}

const BV_BIT_BLAST_GATE_FIELDS: &[&str] = &["gate_type", "width"];

enum BvBitBlastGateField {
    GateType,
    Width,
}

impl<'de> Deserialize<'de> for BvBitBlastGateField {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        deserializer.deserialize_identifier(BvBitBlastGateFieldVisitor)
    }
}

struct BvBitBlastGateFieldVisitor;

impl Visitor<'_> for BvBitBlastGateFieldVisitor {
    type Value = BvBitBlastGateField;

    fn expecting(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter.write_str("field identifier")
    }

    fn visit_u64<E>(self, value: u64) -> Result<Self::Value, E>
    where
        E: DeError,
    {
        match value {
            0 => Ok(BvBitBlastGateField::GateType),
            1 => Ok(BvBitBlastGateField::Width),
            _ => Err(DeError::invalid_value(
                Unexpected::Unsigned(value),
                &"field index 0 <= i < 2",
            )),
        }
    }

    fn visit_str<E>(self, value: &str) -> Result<Self::Value, E>
    where
        E: DeError,
    {
        match value {
            "gate_type" => Ok(BvBitBlastGateField::GateType),
            "width" => Ok(BvBitBlastGateField::Width),
            _ => Err(DeError::unknown_field(value, BV_BIT_BLAST_GATE_FIELDS)),
        }
    }

    fn visit_bytes<E>(self, value: &[u8]) -> Result<Self::Value, E>
    where
        E: DeError,
    {
        match value {
            b"gate_type" => Ok(BvBitBlastGateField::GateType),
            b"width" => Ok(BvBitBlastGateField::Width),
            _ => Err(DeError::unknown_field(
                &String::from_utf8_lossy(value),
                BV_BIT_BLAST_GATE_FIELDS,
            )),
        }
    }
}

struct BvBitBlastGateVisitor;

impl<'de> Visitor<'de> for BvBitBlastGateVisitor {
    type Value = TheoryLemmaKind;

    fn expecting(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter.write_str("struct variant TheoryLemmaKind::BvBitBlastGate")
    }

    fn visit_seq<A>(self, mut seq: A) -> Result<Self::Value, A::Error>
    where
        A: SeqAccess<'de>,
    {
        let gate_type = match seq.next_element::<BvGateType>()? {
            Some(value) => value,
            None => {
                return Err(DeError::invalid_length(
                    0,
                    &"struct variant TheoryLemmaKind::BvBitBlastGate with 2 elements",
                ));
            }
        };
        let width = match seq.next_element::<u32>()? {
            Some(value) => value,
            None => {
                return Err(DeError::invalid_length(
                    1,
                    &"struct variant TheoryLemmaKind::BvBitBlastGate with 2 elements",
                ));
            }
        };
        Ok(TheoryLemmaKind::BvBitBlastGate { gate_type, width })
    }

    fn visit_map<A>(self, mut map: A) -> Result<Self::Value, A::Error>
    where
        A: MapAccess<'de>,
    {
        let mut gate_type: Option<BvGateType> = None;
        let mut width: Option<u32> = None;
        while let Some(key) = map.next_key::<BvBitBlastGateField>()? {
            match key {
                BvBitBlastGateField::GateType => {
                    if gate_type.is_some() {
                        return Err(DeError::duplicate_field("gate_type"));
                    }
                    gate_type = Some(map.next_value()?);
                }
                BvBitBlastGateField::Width => {
                    if width.is_some() {
                        return Err(DeError::duplicate_field("width"));
                    }
                    width = Some(map.next_value()?);
                }
            }
        }
        let Some(gate_type) = gate_type else {
            return Err(DeError::missing_field("gate_type"));
        };
        let Some(width) = width else {
            return Err(DeError::missing_field("width"));
        };
        Ok(TheoryLemmaKind::BvBitBlastGate { gate_type, width })
    }
}

const ARRAY_SELECT_STORE_FIELDS: &[&str] = &["index_eq"];

enum ArraySelectStoreField {
    IndexEq,
}

impl<'de> Deserialize<'de> for ArraySelectStoreField {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        deserializer.deserialize_identifier(ArraySelectStoreFieldVisitor)
    }
}

struct ArraySelectStoreFieldVisitor;

impl Visitor<'_> for ArraySelectStoreFieldVisitor {
    type Value = ArraySelectStoreField;

    fn expecting(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter.write_str("field identifier")
    }

    fn visit_u64<E>(self, value: u64) -> Result<Self::Value, E>
    where
        E: DeError,
    {
        match value {
            0 => Ok(ArraySelectStoreField::IndexEq),
            _ => Err(DeError::invalid_value(
                Unexpected::Unsigned(value),
                &"field index 0 <= i < 1",
            )),
        }
    }

    fn visit_str<E>(self, value: &str) -> Result<Self::Value, E>
    where
        E: DeError,
    {
        match value {
            "index_eq" => Ok(ArraySelectStoreField::IndexEq),
            _ => Err(DeError::unknown_field(value, ARRAY_SELECT_STORE_FIELDS)),
        }
    }

    fn visit_bytes<E>(self, value: &[u8]) -> Result<Self::Value, E>
    where
        E: DeError,
    {
        match value {
            b"index_eq" => Ok(ArraySelectStoreField::IndexEq),
            _ => Err(DeError::unknown_field(
                &String::from_utf8_lossy(value),
                ARRAY_SELECT_STORE_FIELDS,
            )),
        }
    }
}

struct ArraySelectStoreVisitor;

impl<'de> Visitor<'de> for ArraySelectStoreVisitor {
    type Value = TheoryLemmaKind;

    fn expecting(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter.write_str("struct variant TheoryLemmaKind::ArraySelectStore")
    }

    fn visit_seq<A>(self, mut seq: A) -> Result<Self::Value, A::Error>
    where
        A: SeqAccess<'de>,
    {
        let index_eq = match seq.next_element::<bool>()? {
            Some(value) => value,
            None => {
                return Err(DeError::invalid_length(
                    0,
                    &"struct variant TheoryLemmaKind::ArraySelectStore with 1 element",
                ));
            }
        };
        Ok(TheoryLemmaKind::ArraySelectStore { index_eq })
    }

    fn visit_map<A>(self, mut map: A) -> Result<Self::Value, A::Error>
    where
        A: MapAccess<'de>,
    {
        let mut index_eq: Option<bool> = None;
        while let Some(key) = map.next_key::<ArraySelectStoreField>()? {
            match key {
                ArraySelectStoreField::IndexEq => {
                    if index_eq.is_some() {
                        return Err(DeError::duplicate_field("index_eq"));
                    }
                    index_eq = Some(map.next_value()?);
                }
            }
        }
        let Some(index_eq) = index_eq else {
            return Err(DeError::missing_field("index_eq"));
        };
        Ok(TheoryLemmaKind::ArraySelectStore { index_eq })
    }
}

const FP_TO_BV_FIELDS: &[&str] = &["operation"];

enum FpToBvField {
    Operation,
}

impl<'de> Deserialize<'de> for FpToBvField {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        deserializer.deserialize_identifier(FpToBvFieldVisitor)
    }
}

struct FpToBvFieldVisitor;

impl Visitor<'_> for FpToBvFieldVisitor {
    type Value = FpToBvField;

    fn expecting(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter.write_str("field identifier")
    }

    fn visit_u64<E>(self, value: u64) -> Result<Self::Value, E>
    where
        E: DeError,
    {
        match value {
            0 => Ok(FpToBvField::Operation),
            _ => Err(DeError::invalid_value(
                Unexpected::Unsigned(value),
                &"field index 0 <= i < 1",
            )),
        }
    }

    fn visit_str<E>(self, value: &str) -> Result<Self::Value, E>
    where
        E: DeError,
    {
        match value {
            "operation" => Ok(FpToBvField::Operation),
            _ => Err(DeError::unknown_field(value, FP_TO_BV_FIELDS)),
        }
    }

    fn visit_bytes<E>(self, value: &[u8]) -> Result<Self::Value, E>
    where
        E: DeError,
    {
        match value {
            b"operation" => Ok(FpToBvField::Operation),
            _ => Err(DeError::unknown_field(
                &String::from_utf8_lossy(value),
                FP_TO_BV_FIELDS,
            )),
        }
    }
}

struct FpToBvVisitor;

impl<'de> Visitor<'de> for FpToBvVisitor {
    type Value = TheoryLemmaKind;

    fn expecting(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter.write_str("struct variant TheoryLemmaKind::FpToBv")
    }

    fn visit_seq<A>(self, mut seq: A) -> Result<Self::Value, A::Error>
    where
        A: SeqAccess<'de>,
    {
        let operation = match seq.next_element::<FpOp>()? {
            Some(value) => value,
            None => {
                return Err(DeError::invalid_length(
                    0,
                    &"struct variant TheoryLemmaKind::FpToBv with 1 element",
                ));
            }
        };
        Ok(TheoryLemmaKind::FpToBv { operation })
    }

    fn visit_map<A>(self, mut map: A) -> Result<Self::Value, A::Error>
    where
        A: MapAccess<'de>,
    {
        let mut operation: Option<FpOp> = None;
        while let Some(key) = map.next_key::<FpToBvField>()? {
            match key {
                FpToBvField::Operation => {
                    if operation.is_some() {
                        return Err(DeError::duplicate_field("operation"));
                    }
                    operation = Some(map.next_value()?);
                }
            }
        }
        let Some(operation) = operation else {
            return Err(DeError::missing_field("operation"));
        };
        Ok(TheoryLemmaKind::FpToBv { operation })
    }
}

const FP_CLASSIFICATION_FIELDS: &[&str] = &["operation"];

enum FpClassificationField {
    Operation,
}

impl<'de> Deserialize<'de> for FpClassificationField {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        deserializer.deserialize_identifier(FpClassificationFieldVisitor)
    }
}

struct FpClassificationFieldVisitor;

impl Visitor<'_> for FpClassificationFieldVisitor {
    type Value = FpClassificationField;

    fn expecting(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter.write_str("field identifier")
    }

    fn visit_u64<E>(self, value: u64) -> Result<Self::Value, E>
    where
        E: DeError,
    {
        match value {
            0 => Ok(FpClassificationField::Operation),
            _ => Err(DeError::invalid_value(
                Unexpected::Unsigned(value),
                &"field index 0 <= i < 1",
            )),
        }
    }

    fn visit_str<E>(self, value: &str) -> Result<Self::Value, E>
    where
        E: DeError,
    {
        match value {
            "operation" => Ok(FpClassificationField::Operation),
            _ => Err(DeError::unknown_field(value, FP_CLASSIFICATION_FIELDS)),
        }
    }

    fn visit_bytes<E>(self, value: &[u8]) -> Result<Self::Value, E>
    where
        E: DeError,
    {
        match value {
            b"operation" => Ok(FpClassificationField::Operation),
            _ => Err(DeError::unknown_field(
                &String::from_utf8_lossy(value),
                FP_CLASSIFICATION_FIELDS,
            )),
        }
    }
}

struct FpClassificationVisitor;

impl<'de> Visitor<'de> for FpClassificationVisitor {
    type Value = TheoryLemmaKind;

    fn expecting(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter.write_str("struct variant TheoryLemmaKind::FpClassification")
    }

    fn visit_seq<A>(self, mut seq: A) -> Result<Self::Value, A::Error>
    where
        A: SeqAccess<'de>,
    {
        let operation = match seq.next_element::<FpOp>()? {
            Some(value) => value,
            None => {
                return Err(DeError::invalid_length(
                    0,
                    &"struct variant TheoryLemmaKind::FpClassification with 1 element",
                ));
            }
        };
        Ok(TheoryLemmaKind::FpClassification { operation })
    }

    fn visit_map<A>(self, mut map: A) -> Result<Self::Value, A::Error>
    where
        A: MapAccess<'de>,
    {
        let mut operation: Option<FpOp> = None;
        while let Some(key) = map.next_key::<FpClassificationField>()? {
            match key {
                FpClassificationField::Operation => {
                    if operation.is_some() {
                        return Err(DeError::duplicate_field("operation"));
                    }
                    operation = Some(map.next_value()?);
                }
            }
        }
        let Some(operation) = operation else {
            return Err(DeError::missing_field("operation"));
        };
        Ok(TheoryLemmaKind::FpClassification { operation })
    }
}
