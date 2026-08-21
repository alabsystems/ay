// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

// Private evaluation state for bounded BV/LIA authentication.

#[derive(Clone, Debug, PartialEq, Eq)]
enum Value {
    Bool(bool),
    Int(BigInt),
    BitVec { value: u64, width: u32 },
}

#[derive(Default)]
struct Environment {
    bools: HashMap<TermId, bool>,
    ints: HashMap<TermId, BigInt>,
    int_limbs: u64,
    bvs: HashMap<TermId, (u64, u32)>,
}

impl Environment {
    fn clear_ints(&mut self) {
        self.ints.clear();
        self.int_limbs = 0;
    }
}

struct CollectedVariables {
    ints: Vec<TermId>,
    bools: Vec<TermId>,
    bitvecs: Vec<(TermId, u32)>,
}

#[derive(Debug)]
enum Dimension {
    Bool(TermId),
    BitVec {
        term: TermId,
        width: u32,
    },
    IntClass {
        members: Vec<TermId>,
        lower: BigInt,
        count: u64,
    },
}

impl Dimension {
    fn count(&self) -> u64 {
        match self {
            Self::Bool(_) => 2,
            Self::BitVec { width, .. } => 1_u64 << width,
            Self::IntClass { count, .. } => *count,
        }
    }
}

#[derive(Clone, Debug, Default)]
struct ClassBounds {
    lower: Option<BigInt>,
    upper: Option<BigInt>,
}

struct IntClasses {
    class_of: HashMap<TermId, usize>,
    members: Vec<Vec<TermId>>,
    bounds: Vec<ClassBounds>,
}

impl IntClasses {
    fn members_for(&self, term: TermId) -> Option<&[TermId]> {
        self.class_of
            .get(&term)
            .map(|&class| self.members[class].as_slice())
    }

    fn semantic_key(&self, term: TermId) -> Option<usize> {
        self.class_of.get(&term).copied()
    }
}

enum QueryDecision {
    Sat,
    Unsat,
}

struct Meter {
    work: u64,
    deadline: Option<Instant>,
}

impl Meter {
    fn charge(&mut self, amount: u64) -> Result<(), BvLiaUnsatAuthenticationError> {
        let previous_work = self.work;
        self.work =
            self.work
                .checked_add(amount)
                .ok_or(BvLiaUnsatAuthenticationError::ResourceLimit {
                    resource: "work accounting",
                })?;
        if self.work > MAX_WORK {
            return Err(BvLiaUnsatAuthenticationError::ResourceLimit {
                resource: "deterministic work budget",
            });
        }
        // Bulk limb charges need not land exactly on a sampling boundary.
        // Compare buckets so crossing one or many boundaries always samples.
        if (previous_work >> 14) != (self.work >> 14)
            && self
                .deadline
                .is_some_and(|deadline| Instant::now() >= deadline)
        {
            return Err(BvLiaUnsatAuthenticationError::ResourceLimit {
                resource: "caller deadline",
            });
        }
        Ok(())
    }

    fn check_entry(&mut self) -> Result<(), BvLiaUnsatAuthenticationError> {
        if self
            .deadline
            .is_some_and(|deadline| Instant::now() >= deadline)
        {
            return Err(BvLiaUnsatAuthenticationError::ResourceLimit {
                resource: "caller deadline",
            });
        }
        self.charge(1)
    }
}
