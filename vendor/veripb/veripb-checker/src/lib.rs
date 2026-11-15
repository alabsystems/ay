//! VeriPB forward checking library. Forward checking checks every rule in order from the start to end of the proof.
//!
//! This is done by implementing the [`ProofProcessor`](veripb_parser::pbp_parser::proof_processor::ProofProcessor) trait for the structure [`ForwardsChecker`](checker::ForwardsChecker), so that the [`ForwardsChecker`](checker::ForwardsChecker) can handle rules parsed by the parser crate [`veripb_parser`].
//!
//! To implement the checking functionality for each [`VeriPBRule`](veripb_rules::VeriPBRule), the this crate implements the [`Checkable`](rules::Checkable) trait for each [`VeriPBRule`](veripb_rules::VeriPBRule).

// `clippy::restriction` is allow-by-default and is allowed wholesale in this
// crate and in `veripb-parser`, `veripb-formula` and `veripb-propagator`. It
// is not a lint group in the usual sense -- it is a menu of mutually
// incompatible house styles -- and this codebase has adopted almost none of
// them. Measured with
//
//     cargo clippy -p veripb-checker -p veripb-parser -p veripb-formula \
//       -p veripb-propagator --lib -- --force-warn clippy::restriction
//
// the four attributes hide several thousand findings between them, more than
// half of them accounted for by `implicit_return`, `question_mark_used`,
// `arbitrary_source_item_ordering`, `missing_inline_in_public_items`,
// `min_ident_chars` and `missing_docs_in_private_items` alone. Turning the
// group on is a large style project, not a soundness one.
//
// What the blanket allow *does* cost is visibility of the small robustness
// subset -- `indexing_slicing`, `unwrap_used`, `panic`/`unreachable`/
// `unimplemented` -- and that has bitten. The `wiplvl` slice that aborted the
// release binary on a three-line proof (fixed in `66138cf7`) is flagged by
// `indexing_slicing`; a round-4 triage of the same subset found three more
// live aborts on ordinary input, each now an ordinary refusal pinned by
// `tests/unsupported_inputs_refuse.rs` and
// `veripb-parser/tests/parser_error_paths.rs`.
//
// One member of that subset is deliberately not a defect here.
// `arithmetic_side_effects` flags arithmetic that can abort, and
// `[profile.release]` sets `overflow-checks = true` for exactly that reason:
// a wrapped degree is a wrong verdict, and aborting at the source line is the
// designed behaviour, not an accident to be silenced.
//
// So rather than a blanket removal that would flood the build, the two
// members that are already at zero across these crates are re-enabled by
// name, which costs nothing and cannot regress.
#![allow(clippy::restriction)]
#![warn(clippy::unimplemented, clippy::todo)]

pub mod checked_result;
pub mod checker;
pub mod config;
pub mod context;
pub mod database;
pub mod deletion_sequence;
pub mod error;
pub mod kernel_bridge;
pub mod occurrence_list;
pub mod order;
pub mod order_context;
pub mod prelude;
pub mod proofgoal;
pub mod proofgoal_context;
pub mod rules;
pub mod subproof_context;
pub mod utils;
