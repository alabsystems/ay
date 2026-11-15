use std::{rc::Rc, time::Instant};

use log::warn;
use veripb_formula::prelude::*;
use veripb_rules::StartTimerRule;

use crate::{prelude::*, rules::Checkable};

impl Checkable for StartTimerRule {
    fn compute(
        &mut self,
        context: &mut Context,
        _database: &mut Database,
    ) -> Result<Vec<Rc<DBConstraint>>, CheckingError> {
        if context.config.record_stats {
            context
                .running_timers
                .entry(self.name.clone())
                .and_modify(|_| warn!("The timer '{}' has already been started!", self.name))
                .or_insert_with(Instant::now);
        }
        Ok(vec![])
    }

    fn is_subproof_friendly(&self) -> bool {
        true
    }
}
