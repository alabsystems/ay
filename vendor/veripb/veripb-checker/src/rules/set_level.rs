use std::rc::Rc;

use veripb_formula::prelude::*;
use veripb_rules::SetLevelRule;

use crate::prelude::*;

/// The largest level `setlvl` will materialise bookkeeping for.
///
/// [`Context::level_ids`](crate::context::Context::level_ids) is a dense `Vec<Vec<usize>>`
/// indexed by level, so `setlvl n` allocates `n + 1` empty `Vec`s — 24 bytes each on a 64-bit
/// target — whether or not any constraint is ever tagged with those levels. This is the same
/// shape as the DIMACS variable count that sized the variable-name table: a number read out of
/// an input file used directly as the length of a dense array. `setlvl 1000000000000;` is one
/// line of proof text asking for 24 TB, and before this bound the run simply never came back.
///
/// `1 << 27` levels is 3.2 GiB of empty bookkeeping — already far past anything a proof could
/// use, since a level does nothing until a constraint is stored at it and so the useful level
/// count is bounded by the number of constraints in the proof. It is chosen on the same
/// reasoning as [`MAX_DENSE_VAR_IDX`]: high enough that no real proof reaches it, low enough
/// that the refusal happens before the allocator does.
const MAX_LEVEL: usize = 1 << 27;

impl Checkable for SetLevelRule {
    #[inline]
    fn compute(
        &mut self,
        context: &mut Context,
        _database: &mut Database,
    ) -> Result<Vec<Rc<DBConstraint>>, CheckingError> {
        if self.level > MAX_LEVEL {
            return Err(CheckingError::SetLevelOutOfRange(self.level, MAX_LEVEL));
        }
        if self.level >= context.level_ids.len() {
            context.level_ids.resize(self.level + 1, Default::default());
        }
        context.current_level = Some(self.level);
        Ok(vec![])
    }
}
