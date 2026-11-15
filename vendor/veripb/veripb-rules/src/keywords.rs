//! Some keywords used for elaborating VeriPB rules.

/// The header of a VeriPB proof version 3.0.
pub const HEADER: &str = "pseudo-Boolean proof version 3.0\n";
/// `load_order`-rule name.
pub const LOAD_ORDER: &str = "load_order";
/// `def_order`-rule name.
pub const DEF_ORDER: &str = "def_order";
/// `fresh_aux_1`-rule name.
pub const FRESH_AUX_1: &str = "fresh_aux_1";
/// `fresh_aux_2`-rule name.
pub const FRESH_AUX_2: &str = "fresh_aux_2";
/// `fresh_right`-rule name.
pub const FRESH_RIGHT: &str = "fresh_right";
/// `preserved_add`-rule name.
pub const PRESERVED_ADD: &str = "preserved_add";
/// `preserved_rm`-rule name.
pub const PRESERVED_RM: &str = "preserved_rm";
/// `strengthening_to_core`-rule name.
pub const STRENGTHENING_TO_CORE: &str = "strengthening_to_core";
/// Conclusion `ENUMERATION_COMPLETE`.
pub const ENUMERATION_COMPLETE: &str = "ENUMERATION_COMPLETE";
/// Conclusion `ENUMERATION_PARTIAL`.
pub const ENUMERATION_PARTIAL: &str = "ENUMERATION_PARTIAL";
/// Output guarantee `DERIVABLE`.
pub const DERIVABLE: &str = "DERIVABLE";
/// Output guarantee `EQUISATISFIABLE`.
pub const EQUISAT: &str = "EQUISATISFIABLE";
/// Output guarantee `EQUIOPTIMAL`.
pub const EQUIOPT: &str = "EQUIOPTIMAL";
/// Output guarantee `EQUIENUMERABLE`.
pub const EQUIENUM: &str = "EQUIENUMERABLE";
/// Footer proof line ending the VeriPB proof.
pub const PROOF_END: &str = "end pseudo-Boolean proof;";
