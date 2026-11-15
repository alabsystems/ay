// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Finite array and recursive-datatype contracts against pinned Z3 5.3.3.
//!
//! The array-extensionality implication is specified by `z3_api.h`; the
//! recursive field uses its documented null-sort/index-zero representation.
//! `api_datatype.cpp` keeps constructor containers separate from the AST
//! declarations obtained by query_constructor. Each declaration, sort, AST and
//! model used after another allocation is retained immediately. These cases
//! leave multidimensional arrays, maps, sets, parametric/mutual datatypes,
//! accessor behavior on the wrong constructor, invalid arguments, concurrent
//! contexts and the full argument/lifetime domains outside their scope.

use super::*;

pub(super) const FAMILIES: &[Family] = &[
    Family {
        id: "contract-arrays",
        source: concat!(
            include_str!("../contracts/common.h"),
            include_str!("../contracts/arrays_datatypes_helpers.h"),
            include_str!("../contracts/arrays.c")
        ),
        checks: &[
            "arrays.context-created",
            "arrays.sort-reflection",
            "arrays.term-reflection",
            "arrays.constant-array-value",
            "arrays.select-stored-value",
            "arrays.store-preserves-other-index",
            "arrays.last-store-wins",
            "arrays.symbolic-terms-created",
            "arrays.read-store-identity",
            "arrays.extensional-witness-sort",
            "arrays.distinct-arrays-satisfiable",
            "arrays.extensional-witness-distinguishes",
            "arrays.extensional-scope-restored",
            "arrays.concrete-model-satisfiable",
            "arrays.model-select-values",
            "arrays.retained-model-after-contradiction",
            "arrays.retained-model-after-solver-release",
        ],
    },
    Family {
        id: "contract-datatypes",
        source: concat!(
            include_str!("../contracts/common.h"),
            include_str!("../contracts/arrays_datatypes_helpers.h"),
            include_str!("../contracts/datatypes.c")
        ),
        checks: &[
            "datatypes.context-created",
            "datatypes.constructor-containers",
            "datatypes.recursive-sort",
            "datatypes.queried-declarations",
            "datatypes.reflection-after-container-release",
            "datatypes.declaration-sorts",
            "datatypes.constructor-testers",
            "datatypes.constructor-accessors",
            "datatypes.recursive-accessors",
            "datatypes.disjoint-constructors",
            "datatypes.injective-constructor",
            "datatypes.occurs-check",
            "datatypes.concrete-model-satisfiable",
            "datatypes.model-observations",
            "datatypes.retained-model-after-contradiction",
            "datatypes.retained-model-after-solver-release",
        ],
    },
];

pub(super) const CLAIMS: &[Claim] = &[
    Claim { family: "contract-arrays", check: "arrays.sort-reflection", aspect: Aspect::Output, functions: &["Z3_mk_array_sort", "Z3_get_array_sort_domain", "Z3_get_array_sort_range", "Z3_get_sort_kind", "Z3_is_eq_sort"], statement: "An Int-to-Int array sort reports array kind and the exact supplied domain and range sorts." },
    Claim { family: "contract-arrays", check: "arrays.term-reflection", aspect: Aspect::Output, functions: &["Z3_mk_const_array", "Z3_mk_store", "Z3_mk_select", "Z3_get_sort", "Z3_to_app", "Z3_get_app_decl", "Z3_get_decl_kind"], statement: "The constant-zero array, its store at index 1 and the read at index 1 preserve the array/result types and report CONST_ARRAY, STORE and SELECT declaration kinds." },
    Claim { family: "contract-arrays", check: "arrays.constant-array-value", aspect: Aspect::Output, functions: &["Z3_mk_const_array", "Z3_mk_select", "Z3_simplify", "Z3_get_numeral_int"], statement: "Reading index 2 of the constant-zero Int array simplifies to the integer zero." },
    Claim { family: "contract-arrays", check: "arrays.select-stored-value", aspect: Aspect::State, functions: &["Z3_mk_store", "Z3_mk_select"], statement: "Reading index 1 after storing integer 7 there simplifies to 7." },
    Claim { family: "contract-arrays", check: "arrays.store-preserves-other-index", aspect: Aspect::State, functions: &["Z3_mk_store", "Z3_mk_select"], statement: "Storing 7 at index 1 of a constant-zero array preserves zero at the distinct index 2." },
    Claim { family: "contract-arrays", check: "arrays.last-store-wins", aspect: Aspect::State, functions: &["Z3_mk_store", "Z3_mk_select"], statement: "Overwriting index 1 with 9 replaces the prior 7 at that index." },
    Claim { family: "contract-arrays", check: "arrays.read-store-identity", aspect: Aspect::Output, functions: &["Z3_mk_store", "Z3_mk_select", "Z3_mk_eq", "Z3_mk_not", "Z3_solver_check"], statement: "For an unconstrained array A, the negation of store(A,1,select(A,1))=A is unsatisfiable." },
    Claim { family: "contract-arrays", check: "arrays.extensional-witness-sort", aspect: Aspect::Output, functions: &["Z3_mk_array_ext", "Z3_get_sort"], statement: "The extensionality witness for two Int-indexed arrays is an Int expression usable as both arrays' read index." },
    Claim { family: "contract-arrays", check: "arrays.distinct-arrays-satisfiable", aspect: Aspect::State, functions: &["Z3_solver_reset", "Z3_solver_assert", "Z3_solver_check"], statement: "Two unconstrained Int-to-Int arrays can differ." },
    Claim { family: "contract-arrays", check: "arrays.extensional-witness-distinguishes", aspect: Aspect::Output, functions: &["Z3_mk_array_ext", "Z3_mk_select", "Z3_solver_check"], statement: "Asserting both distinct arrays and equal reads at their array-ext witness is unsatisfiable, matching the pinned header's implication." },
    Claim { family: "contract-arrays", check: "arrays.extensional-scope-restored", aspect: Aspect::State, functions: &["Z3_solver_push", "Z3_solver_pop", "Z3_solver_check"], statement: "Popping the contradictory equality of extensionality-witness reads restores the satisfiable distinct-array state." },
    Claim { family: "contract-arrays", check: "arrays.model-select-values", aspect: Aspect::Output, functions: &["Z3_solver_get_model", "Z3_model_eval", "Z3_get_bool_value"], statement: "The model of A=store(const(0),1,7), B=const(0) evaluates A[1]=7, A[2]=0, B[1]=0, A!=B to true and A=B to false, without model completion." },
    Claim { family: "contract-arrays", check: "arrays.retained-model-after-contradiction", aspect: Aspect::Lifetime, functions: &["Z3_model_inc_ref", "Z3_model_eval"], statement: "The retained concrete array model still evaluates A[1] to 7 after the solver is made inconsistent by A=const(0)." },
    Claim { family: "contract-arrays", check: "arrays.retained-model-after-solver-release", aspect: Aspect::Lifetime, functions: &["Z3_inc_ref", "Z3_dec_ref", "Z3_get_ast_id", "Z3_model_inc_ref", "Z3_model_dec_ref", "Z3_solver_dec_ref"], statement: "Before context destruction, retained array ASTs keep their identity and read semantics and the retained model remains evaluable after solver release." },
    Claim { family: "contract-datatypes", check: "datatypes.constructor-containers", aspect: Aspect::Output, functions: &["Z3_mk_constructor", "Z3_constructor_num_fields"], statement: "The nil and cons constructor containers report zero and two fields; cons uses an Int field and a self-recursive field." },
    Claim { family: "contract-datatypes", check: "datatypes.recursive-sort", aspect: Aspect::Output, functions: &["Z3_mk_datatype", "Z3_is_recursive_datatype_sort", "Z3_get_datatype_sort_num_constructors", "Z3_get_sort_kind"], statement: "The declared nil/cons Int list is classified as a recursive datatype with exactly two constructors." },
    Claim { family: "contract-datatypes", check: "datatypes.queried-declarations", aspect: Aspect::Output, functions: &["Z3_query_constructor", "Z3_get_decl_name", "Z3_get_symbol_kind", "Z3_get_symbol_string"], statement: "Querying both declared constructor containers returns nonnull constructor/tester/accessor declarations with the four supplied constructor and field names." },
    Claim { family: "contract-datatypes", check: "datatypes.reflection-after-container-release", aspect: Aspect::Lifetime, functions: &["Z3_del_constructor", "Z3_func_decl_to_ast", "Z3_inc_ref", "Z3_get_datatype_sort_constructor", "Z3_get_datatype_sort_recognizer", "Z3_get_datatype_sort_constructor_accessor", "Z3_is_eq_func_decl"], statement: "Immediately retained constructor, tester and accessor declarations survive release of their constructor containers and equal the datatype sort's reflected declarations." },
    Claim { family: "contract-datatypes", check: "datatypes.declaration-sorts", aspect: Aspect::Output, functions: &["Z3_get_domain_size", "Z3_get_domain", "Z3_get_range"], statement: "Nil is nullary; cons takes Int and this list sort, returns this list sort, and its two accessors return Int and this list sort." },
    Claim { family: "contract-datatypes", check: "datatypes.constructor-testers", aspect: Aspect::Output, functions: &["Z3_mk_app", "Z3_simplify", "Z3_get_bool_value"], statement: "Nil and cons(7,nil) satisfy their own testers and fail the other constructor's tester." },
    Claim { family: "contract-datatypes", check: "datatypes.constructor-accessors", aspect: Aspect::Output, functions: &["Z3_mk_app", "Z3_simplify", "Z3_get_numeral_int", "Z3_is_eq_ast"], statement: "The head and tail of cons(7,nil) simplify to integer 7 and the original nil AST." },
    Claim { family: "contract-datatypes", check: "datatypes.recursive-accessors", aspect: Aspect::Output, functions: &["Z3_mk_app", "Z3_simplify"], statement: "The tail of cons(9,cons(7,nil)) simplifies to the retained inner list and its head to 7." },
    Claim { family: "contract-datatypes", check: "datatypes.disjoint-constructors", aspect: Aspect::Output, functions: &["Z3_mk_app", "Z3_mk_eq", "Z3_solver_check"], statement: "Equating nil with cons(7,nil) is unsatisfiable." },
    Claim { family: "contract-datatypes", check: "datatypes.injective-constructor", aspect: Aspect::Output, functions: &["Z3_mk_app", "Z3_mk_eq", "Z3_solver_check"], statement: "Equating cons(7,nil) with cons(9,nil) is unsatisfiable, witnessing injectivity of the head field." },
    Claim { family: "contract-datatypes", check: "datatypes.occurs-check", aspect: Aspect::Output, functions: &["Z3_mk_app", "Z3_mk_eq", "Z3_solver_check"], statement: "A list X cannot equal cons(7,X); the recursive cycle equation is unsatisfiable." },
    Claim { family: "contract-datatypes", check: "datatypes.model-observations", aspect: Aspect::Output, functions: &["Z3_solver_get_model", "Z3_model_eval"], statement: "The model of X=cons(7,nil) evaluates its head to 7, tail=nil and is-cons(X) to true, and X=nil to false without model completion." },
    Claim { family: "contract-datatypes", check: "datatypes.retained-model-after-contradiction", aspect: Aspect::Lifetime, functions: &["Z3_model_inc_ref", "Z3_model_eval"], statement: "The retained list model keeps head(X)=7 after adding the contradictory equation X=nil." },
    Claim { family: "contract-datatypes", check: "datatypes.retained-model-after-solver-release", aspect: Aspect::Lifetime, functions: &["Z3_inc_ref", "Z3_dec_ref", "Z3_get_ast_id", "Z3_model_inc_ref", "Z3_model_dec_ref", "Z3_solver_dec_ref"], statement: "Before context destruction, retained list ASTs keep their identity and accessor values and the retained model remains evaluable after solver release." },
];
