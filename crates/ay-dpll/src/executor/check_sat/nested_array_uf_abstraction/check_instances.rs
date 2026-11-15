// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Checking the axiom instances appended to `alpha(phi)`
//! (#nested-array-checked-rung).
//!
//! An appended root is accepted only when it is, node for node, one of four
//! instance shapes stated over fresh functions whose PREIMAGES in the renaming
//! witness make it an axiom instance. The induced structure interprets each
//! fresh function as its preimage, so an accepted root holds there whatever
//! its leaves denote, and the abstraction keeps every model of the original.
//! This re-derives everything from the store and the witness; it trusts
//! nothing the builder recorded.

use super::build::{classify_sort, ArrayUfAbstraction, SortClass, SymbolKey};
use super::instances::{ground_images, preimages, MAX_AXIOM_INSTANCES};
use super::*;
use ay_core::kani_compat::DetHashSet as HashSet;
use ay_core::{Sort, Symbol};

/// THE INSTANCE CHECK. Accept `instances` as axiom instances over the witness
/// of `abstraction`, or reject. Run only after [`super::is_pure_renaming`]
/// accepted `abstraction`, so every image node below its roots is a checked
/// renaming of an original node.
///
/// Each instance must be one of:
///
/// * `(= (S (C x_1 .. x_n)) x_k)`: `C` renames a constructor of a renamed
///   carrier `D`, `S` renames a selector at `D`, and the store registers the
///   selector's name as `C`'s `k`-th field, at `C`'s `k`-th argument sort;
/// * `(= (R (W a i v) i) v)`: `W` renames `store` and `R` renames `select`,
///   both at the same array sort;
/// * `(or (= i j) (= (R (W a i v) j) (R a j)))`: the same, at any `j`;
/// * `(= (R (K v) j) v)`: `K` renames `const-array` at `R`'s array sort;
///
/// with every sort equal to the image of the preimage's sort, every leaf and
/// every renamed application under an instance head a GROUND image (a subterm
/// of the abstract roots that mentions no quantifier and no bound name), and
/// no array left in the instances. Each `=` may list its two sides in either
/// order (equality is symmetric).
pub(super) fn instances_are_valid(
    terms: &TermStore,
    abstraction: &ArrayUfAbstraction,
    instances: &[TermId],
) -> bool {
    if instances.is_empty() {
        return true;
    }
    if instances.len() > MAX_AXIOM_INSTANCES {
        return false;
    }
    let preimage = preimages(&abstraction.witness);
    if preimage.len() != abstraction.witness.symbols.len() {
        return false;
    }
    let check = InstanceCheck {
        terms,
        abstraction,
        preimage,
        ground: ground_images(terms, abstraction.roots()),
    };
    if !instances
        .iter()
        .all(|&instance| check.is_instance(instance))
    {
        return false;
    }
    let features = StaticFeatures::collect(terms, instances);
    !features.has_arrays && !features.has_nested_arrays
}

struct InstanceCheck<'a> {
    terms: &'a TermStore,
    abstraction: &'a ArrayUfAbstraction,
    preimage: HashMap<Symbol, SymbolKey>,
    ground: HashSet<TermId>,
}

/// The preimage of a renamed `select` or `store`: the original array sort,
/// its index sort and its element sort.
struct ArrayOp<'a> {
    array: &'a Sort,
    index: &'a Sort,
    element: &'a Sort,
}

impl<'a> InstanceCheck<'a> {
    fn is_instance(&self, instance: TermId) -> bool {
        if self.terms.sort(instance) != &Sort::Bool {
            return false;
        }
        match self.interpreted(instance) {
            Some(("=", &[one, other])) => {
                [(one, other), (other, one)].into_iter().any(|(lhs, rhs)| {
                    self.selector_over_constructor(lhs, rhs)
                        || self.read_over_write_hit(lhs, rhs)
                        || self.read_over_constant(lhs, rhs)
                })
            }
            Some(("or", &[same, differ])) => self.read_over_write_miss(same, differ),
            _ => false,
        }
    }

    /// The two sides of an interpreted `=`, in both orders.
    fn equality_sides(&self, term: TermId) -> Option<[(TermId, TermId); 2]> {
        match self.interpreted(term) {
            Some(("=", &[one, other])) => Some([(one, other), (other, one)]),
            _ => None,
        }
    }

    /// `(= (S (C x..)) x_k)`.
    fn selector_over_constructor(&self, lhs: TermId, rhs: TermId) -> bool {
        let Some(((selector, field_sort, selector_args), &[constructed])) = self.renamed(lhs)
        else {
            return false;
        };
        let Some(((constructor, carrier, field_sorts), args)) = self.renamed_ground(constructed)
        else {
            return false;
        };
        let (Symbol::Named(selector_name), Symbol::Named(constructor_name)) =
            (selector, constructor)
        else {
            return false;
        };
        let Some(fields) = self.terms.constructor_field_names(constructor_name) else {
            return false;
        };
        selector_args.as_slice() == std::slice::from_ref(carrier)
            && classify_sort(self.terms, carrier) == SortClass::Carrier
            && fields.len() == args.len()
            && field_sorts.len() == args.len()
            && self.has_image_sort(lhs, field_sort)
            && (0..fields.len()).any(|k| {
                fields[k] == *selector_name && field_sorts[k] == *field_sort && args[k] == rhs
            })
    }

    /// `(= (R (W a i v) i) v)`.
    fn read_over_write_hit(&self, lhs: TermId, rhs: TermId) -> bool {
        let Some((read, &[write, index])) = self.array_op(lhs, "select") else {
            return false;
        };
        let Some((stored, &[_, written, value])) = self.ground_array_op(write, "store") else {
            return false;
        };
        read.array == stored.array && index == written && rhs == value
    }

    /// `(or (= i j) (= (R (W a i v) j) (R a j)))`, either side of each `=`
    /// first.
    fn read_over_write_miss(&self, same: TermId, differ: TermId) -> bool {
        let (Some(same_sides), Some(differ_sides)) =
            (self.equality_sides(same), self.equality_sides(differ))
        else {
            return false;
        };
        same_sides.into_iter().any(|(index, other)| {
            differ_sides
                .into_iter()
                .any(|(above, below)| self.miss_shape(index, other, above, below))
        }) && self.terms.sort(same) == &Sort::Bool
            && self.terms.sort(differ) == &Sort::Bool
    }

    /// One orientation of [`Self::read_over_write_miss`].
    fn miss_shape(&self, index: TermId, other: TermId, above: TermId, below: TermId) -> bool {
        let Some((read_above, &[write, at_above])) = self.array_op(above, "select") else {
            return false;
        };
        let Some((read_below, &[base, at_below])) = self.array_op(below, "select") else {
            return false;
        };
        let Some((stored, &[stored_base, written, _])) = self.ground_array_op(write, "store")
        else {
            return false;
        };
        let head = |term| match self.terms.get(term) {
            TermData::App(symbol, _) => Some(symbol),
            _ => None,
        };
        head(above) == head(below)
            && read_above.array == stored.array
            && read_below.array == stored.array
            && index == written
            && base == stored_base
            && at_above == other
            && at_below == other
            && self.is_ground_image(other, stored.index)
    }

    /// `(= (R (K v) j) v)`.
    fn read_over_constant(&self, lhs: TermId, rhs: TermId) -> bool {
        let Some((read, &[constant, index])) = self.array_op(lhs, "select") else {
            return false;
        };
        let Some(((symbol, array, args), &[value])) = self.renamed_ground(constant) else {
            return false;
        };
        symbol.name() == "const-array"
            && matches!(symbol, Symbol::Named(_))
            && array == read.array
            && args.as_slice() == std::slice::from_ref(read.element)
            && rhs == value
            && self.is_ground_image(index, read.index)
    }

    /// A renamed `select`/`store` application (`name`) at a well-formed array
    /// signature whose image sort is the image of its preimage's result.
    fn array_op(&self, term: TermId, name: &str) -> Option<(ArrayOp<'_>, &'a [TermId])> {
        let ((symbol, result, args), app_args) = self.renamed(term)?;
        if symbol.name() != name || !matches!(symbol, Symbol::Named(_)) {
            return None;
        }
        let array = args.first()?;
        let (index, element) = (array.array_index()?, array.array_element()?);
        let shape_ok = match name {
            "select" => result == element && args.as_slice() == [array.clone(), index.clone()],
            "store" => {
                result == array
                    && args.as_slice() == [array.clone(), index.clone(), element.clone()]
            }
            _ => false,
        };
        (shape_ok
            && classify_sort(self.terms, array) == SortClass::Array
            && self.has_image_sort(term, result))
        .then_some((
            ArrayOp {
                array,
                index,
                element,
            },
            app_args,
        ))
    }

    fn ground_array_op(&self, term: TermId, name: &str) -> Option<(ArrayOp<'_>, &'a [TermId])> {
        self.ground.contains(&term).then_some(())?;
        self.array_op(term, name)
    }

    /// An application of a fresh function, with its witness preimage.
    fn renamed(&self, term: TermId) -> Option<(&SymbolKey, &'a [TermId])> {
        match self.terms.get(term) {
            TermData::App(head, args) => Some((self.preimage.get(head)?, args.as_slice())),
            _ => None,
        }
    }

    /// [`Self::renamed`], restricted to a ground image of the abstract roots.
    fn renamed_ground(&self, term: TermId) -> Option<(&SymbolKey, &'a [TermId])> {
        self.ground.contains(&term).then_some(())?;
        self.renamed(term)
    }

    /// An application of an interpreted head (`=` or `or`), never a fresh one.
    fn interpreted(&self, term: TermId) -> Option<(&'a str, &'a [TermId])> {
        match self.terms.get(term) {
            TermData::App(symbol @ Symbol::Named(name), args)
                if !self.preimage.contains_key(symbol) =>
            {
                Some((name.as_str(), args.as_slice()))
            }
            _ => None,
        }
    }

    fn has_image_sort(&self, term: TermId, original: &Sort) -> bool {
        self.abstraction
            .witness
            .mapped_sort(self.terms, original)
            .is_some_and(|image| &image == self.terms.sort(term))
    }

    fn is_ground_image(&self, term: TermId, original: &Sort) -> bool {
        self.ground.contains(&term) && self.has_image_sort(term, original)
    }
}
