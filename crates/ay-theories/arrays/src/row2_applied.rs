//! Acknowledgment metadata for exact clauses derived by current ROW2 work.
//! The bounded global fast cache remains unchanged. One last clause per live
//! obligation survives its eviction; no pair or proposed clause acknowledges
//! itself, and every scope/queue teardown invalidates these records.
use super::*;

impl ArraySolver<'_> {
    pub(crate) fn row2_clause_is_unproductive(
        &mut self,
        store: TermId,
        select: TermId,
        clause: &[TheoryLit],
    ) -> bool {
        let (key, acknowledged) = match self.row2_clause_acknowledged.get_key_value(clause) {
            Some((key, acknowledged)) => (Arc::clone(key), *acknowledged),
            None => (Arc::<[TheoryLit]>::from(clause), false),
        };
        self.row2_last_clause
            .insert((store, select), Arc::clone(&key));
        self.row2_clause_acknowledged.insert(key, acknowledged);
        acknowledged
            || clause
                .iter()
                .any(|lit| self.assigns.get(&lit.term) == Some(&lit.value))
    }

    /// Only the actual add/replay callback may set this bit. A derived shape,
    /// queued pair or planned seen-set entry supplies no acknowledgment.
    pub(crate) fn acknowledge_row2_clause(&mut self, clause: &[TheoryLit]) -> bool {
        match self.row2_clause_acknowledged.get_mut(clause) {
            Some(acknowledged) if !*acknowledged => {
                *acknowledged = true;
                true
            }
            _ => false,
        }
    }

    /// Index reconstruction preserves records only for actual current work.
    /// Borrow clause slices for the temporary census; no clause payload clone.
    pub(crate) fn retain_row2_clause_work(&mut self) {
        self.row2_last_clause
            .retain(|work, _| self.row2_down_work.contains(work));
        let active: HashSet<&[TheoryLit]> =
            self.row2_last_clause.values().map(Arc::as_ref).collect();
        self.row2_clause_acknowledged
            .retain(|clause, _| active.contains(clause.as_ref()));
    }
}
