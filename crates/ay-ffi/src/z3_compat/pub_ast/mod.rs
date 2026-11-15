// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The public AST layer: what a `Z3_ast` names (T5 design §2, phase P1).
//!
//! An untagged `Z3_ast` is `salt << 33 | (PubId + 1)`: an index into this
//! context's [`PubStore`], never an engine term. In phase P1 every node is an
//! [`NodeData::Engine`] leaf, an engine term at a PUBLIC sort, interned by
//! (term, sort). Two public objects that AY's engine stores as one term (the
//! finite-domain value 3 and the integer 3, a `Char` and its code point) are
//! therefore two handles with two sorts, as in z3, where the engine-keyed
//! arena this replaces gave them one handle and one, last-written, sort.
//!
//! Later phases add z3-shaped nodes (applications, variables, quantifiers)
//! beside the engine leaves and delete the leaves at P9.

mod store;

pub(crate) use store::{NodeData, PubId, PubStore, SortId};
