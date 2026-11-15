(set-option :auto_config false)
(set-option :smt.mbqi false)
(set-option :smt.case_split 3)
(set-option :smt.qi.eager_threshold 100.0)
(set-option :smt.delay_units true)
(set-option :smt.arith.solver 2)
(set-option :smt.arith.nl false)
(set-option :pi.enabled false)
(set-option :rewriter.sort_disjunctions false)
(declare-sort %%Function%% 0)
(declare-sort FuelId 0)
(declare-sort Fuel 0)
(declare-const zero Fuel)
(declare-fun succ (Fuel) Fuel)
(declare-fun fuel_bool (FuelId) Bool)
(declare-fun fuel_bool_default (FuelId) Bool)
(declare-const fuel_defaults Bool)
(declare-datatypes ((fndef 0)) (((fndef_singleton))))
(declare-sort Poly 0)
(declare-sort Height 0)
(declare-fun I (Int) Poly)
(declare-fun B (Bool) Poly)
(declare-fun R (Real) Poly)
(declare-fun F (fndef) Poly)
(declare-fun %I (Poly) Int)
(declare-fun %B (Poly) Bool)
(declare-fun %R (Poly) Real)
(declare-fun %F (Poly) fndef)
(declare-sort Type 0)
(declare-const BOOL Type)
(declare-const INT Type)
(declare-const NAT Type)
(declare-const REAL Type)
(declare-const CHAR Type)
(declare-const USIZE Type)
(declare-const ISIZE Type)
(declare-const TYPE%tuple%0. Type)
(declare-fun UINT (Int) Type)
(declare-fun SINT (Int) Type)
(declare-fun FLOAT (Int) Type)
(declare-fun CONST_INT (Int) Type)
(declare-fun CONST_BOOL (Bool) Type)
(declare-sort Dcr 0)
(declare-const $ Dcr)
(declare-const $slice Dcr)
(declare-const $dyn Dcr)
(declare-fun DST (Dcr) Dcr)
(declare-fun REF (Dcr) Dcr)
(declare-fun MUT_REF (Dcr) Dcr)
(declare-fun BOX (Dcr Type Dcr) Dcr)
(declare-fun RC (Dcr Type Dcr) Dcr)
(declare-fun ARC (Dcr Type Dcr) Dcr)
(declare-fun GHOST (Dcr) Dcr)
(declare-fun TRACKED (Dcr) Dcr)
(declare-fun NEVER (Dcr) Dcr)
(declare-fun CONST_PTR (Dcr) Dcr)
(declare-fun ARRAY (Dcr Type Dcr Type) Type)
(declare-fun MUTREF (Dcr Type) Type)
(declare-fun SLICE (Dcr Type) Type)
(declare-const STRSLICE Type)
(declare-const ALLOCATOR_GLOBAL Type)
(declare-fun PTR (Dcr Type) Type)
(declare-fun has_type (Poly Type) Bool)
(declare-fun sized (Dcr) Bool)
(declare-fun as_type (Poly Type) Poly)
(declare-fun mk_fun (%%Function%%) %%Function%%)
(declare-fun const_int (Type) Int)
(declare-fun const_bool (Type) Bool)
(declare-fun mut_ref_current% (Poly) Poly)
(declare-fun mut_ref_future% (Poly) Poly)
(declare-fun mut_ref_update_current% (Poly Poly) Poly)
(assert
 (forall ((m Poly) (arg Poly)) (!
   (= (mut_ref_current% (mut_ref_update_current% m arg)) arg)
   :pattern ((mut_ref_update_current% m arg))
   :qid prelude_mut_ref_update_current_current
   :skolemid skolem_prelude_mut_ref_update_current_current
)))
(assert
 (forall ((m Poly) (arg Poly)) (!
   (= (mut_ref_future% (mut_ref_update_current% m arg)) (mut_ref_future% m))
   :pattern ((mut_ref_update_current% m arg))
   :qid prelude_mut_ref_update_current_future
   :skolemid skolem_prelude_mut_ref_update_current_future
)))
(assert
 (forall ((m Poly) (d Dcr) (t Type)) (!
   (=>
    (has_type m (MUTREF d t))
    (has_type (mut_ref_current% m) t)
   )
   :pattern ((has_type m (MUTREF d t)) (mut_ref_current% m))
   :qid prelude_mut_ref_current_has_type
   :skolemid skolem_prelude_mut_ref_current_has_type
)))
(assert
 (forall ((x Int)) (!
   (= x (%I (I x)))
   :pattern ((I x))
   :qid prelude_unbox_box_int
   :skolemid skolem_prelude_unbox_box_int
)))
(declare-fun ext_eq (Bool Type Poly Poly) Bool)
(declare-const SZ Int)
(declare-fun uHi (Int) Int)
(declare-fun iLo (Int) Int)
(declare-fun iHi (Int) Int)
(assert
 (= (uHi 64) 18446744073709551616)
)
(declare-fun nClip (Int) Int)
(declare-fun uClip (Int Int) Int)
(declare-fun iClip (Int Int) Int)
(declare-fun charClip (Int) Int)
(assert
 (forall ((bits Int) (i Int)) (!
   (and
    (<= 0 (uClip bits i))
    (< (uClip bits i) (uHi bits))
    (=>
     (and
      (<= 0 i)
      (< i (uHi bits))
     )
     (= i (uClip bits i))
   ))
   :pattern ((uClip bits i))
   :qid prelude_u_clip
   :skolemid skolem_prelude_u_clip
)))
(declare-fun uInv (Int Int) Bool)
(declare-fun iInv (Int Int) Bool)
(declare-fun charInv (Int) Bool)
(assert
 (forall ((bits Int) (i Int)) (!
   (= (uInv bits i) (and
     (<= 0 i)
     (< i (uHi bits))
   ))
   :pattern ((uInv bits i))
   :qid prelude_u_inv
   :skolemid skolem_prelude_u_inv
)))
(assert
 (forall ((bits Int) (x Poly)) (!
   (=>
    (has_type x (UINT bits))
    (uInv bits (%I x))
   )
   :pattern ((has_type x (UINT bits)))
   :qid prelude_unbox_uint
   :skolemid skolem_prelude_unbox_uint
)))
(declare-fun Add (Int Int) Int)
(declare-fun Sub (Int Int) Int)
(declare-fun Mul (Int Int) Int)
(declare-fun EucDiv (Int Int) Int)
(declare-fun EucMod (Int Int) Int)
(declare-fun RAdd (Real Real) Real)
(declare-fun RSub (Real Real) Real)
(declare-fun RMul (Real Real) Real)
(declare-fun RDiv (Real Real) Real)
(assert
 (forall ((x Int) (y Int)) (!
   (= (Add x y) (+ x y))
   :pattern ((Add x y))
   :qid prelude_add
   :skolemid skolem_prelude_add
)))
(declare-fun bitxor (Poly Poly) Int)
(declare-fun bitand (Poly Poly) Int)
(declare-fun bitor (Poly Poly) Int)
(declare-fun bitshr (Poly Poly) Int)
(declare-fun bitshl (Poly Poly) Int)
(declare-fun bitnot (Poly) Int)
(declare-fun singular_mod (Int Int) Int)
(declare-fun has_resolved (Dcr Type Poly) Bool)
(declare-fun closure_req (Type Dcr Type Poly Poly) Bool)
(declare-fun closure_ens (Type Dcr Type Poly Poly Poly) Bool)
(declare-fun default_ens (Type Dcr Type Poly Poly Poly) Bool)
(declare-fun height (Poly) Height)
(declare-fun height_lt (Height Height) Bool)
(declare-fun fun_from_recursive_field (Poly) Poly)
(declare-fun check_decrease_height (Poly Poly Bool) Bool)
(declare-const fuel%vstd!function.axiom_fn_mut_call_requires. FuelId)
(declare-const fuel%vstd!function.axiom_fn_mut_call_ensures. FuelId)
(declare-const fuel%vstd!array.group_array_axioms. FuelId)
(declare-const fuel%vstd!function.group_function_axioms. FuelId)
(declare-const fuel%vstd!laws_cmp.group_laws_cmp. FuelId)
(declare-const fuel%vstd!laws_eq.bool_laws.group_laws_eq. FuelId)
(declare-const fuel%vstd!laws_eq.u8_laws.group_laws_eq. FuelId)
(declare-const fuel%vstd!laws_eq.i8_laws.group_laws_eq. FuelId)
(declare-const fuel%vstd!laws_eq.u16_laws.group_laws_eq. FuelId)
(declare-const fuel%vstd!laws_eq.i16_laws.group_laws_eq. FuelId)
(declare-const fuel%vstd!laws_eq.u32_laws.group_laws_eq. FuelId)
(declare-const fuel%vstd!laws_eq.i32_laws.group_laws_eq. FuelId)
(declare-const fuel%vstd!laws_eq.u64_laws.group_laws_eq. FuelId)
(declare-const fuel%vstd!laws_eq.i64_laws.group_laws_eq. FuelId)
(declare-const fuel%vstd!laws_eq.u128_laws.group_laws_eq. FuelId)
(declare-const fuel%vstd!laws_eq.i128_laws.group_laws_eq. FuelId)
(declare-const fuel%vstd!laws_eq.usize_laws.group_laws_eq. FuelId)
(declare-const fuel%vstd!laws_eq.isize_laws.group_laws_eq. FuelId)
(declare-const fuel%vstd!laws_eq.group_laws_eq. FuelId)
(declare-const fuel%vstd!layout.group_align_properties. FuelId)
(declare-const fuel%vstd!layout.group_layout_axioms. FuelId)
(declare-const fuel%vstd!map.group_map_axioms. FuelId)
(declare-const fuel%vstd!multiset.group_multiset_axioms. FuelId)
(declare-const fuel%vstd!raw_ptr.group_raw_ptr_axioms. FuelId)
(declare-const fuel%vstd!seq.group_seq_axioms. FuelId)
(declare-const fuel%vstd!seq_lib.group_filter_ensures. FuelId)
(declare-const fuel%vstd!seq_lib.group_seq_lib_default. FuelId)
(declare-const fuel%vstd!set.group_set_axioms. FuelId)
(declare-const fuel%vstd!set_lib.group_set_lib_default. FuelId)
(declare-const fuel%vstd!slice.group_slice_axioms. FuelId)
(declare-const fuel%vstd!string.group_string_axioms. FuelId)
(declare-const fuel%vstd!std_specs.bits.group_bits_axioms. FuelId)
(declare-const fuel%vstd!std_specs.control_flow.group_control_flow_axioms. FuelId)
(declare-const fuel%vstd!std_specs.manually_drop.group_manually_drop_axioms. FuelId)
(declare-const fuel%vstd!std_specs.btree.group_btree_axioms. FuelId)
(declare-const fuel%vstd!std_specs.hash.group_hash_axioms. FuelId)
(declare-const fuel%vstd!std_specs.range.group_range_axioms. FuelId)
(declare-const fuel%vstd!std_specs.slice.group_slice_axioms. FuelId)
(declare-const fuel%vstd!std_specs.vec.group_vec_axioms. FuelId)
(declare-const fuel%vstd!std_specs.vecdeque.group_vec_dequeue_axioms. FuelId)
(declare-const fuel%vstd!group_vstd_default. FuelId)
(declare-fun tr_bound%core!marker.Tuple. (Dcr Type) Bool)
(declare-fun tr_bound%core!ops.function.FnOnce. (Dcr Type Dcr Type) Bool)
(declare-fun tr_bound%core!ops.function.FnMut. (Dcr Type Dcr Type) Bool)
(declare-fun tr_bound%core!ops.function.Fn. (Dcr Type Dcr Type) Bool)
(declare-fun tr_bound%core!alloc.Allocator. (Dcr Type) Bool)
(declare-fun proj%%core!ops.function.FnOnce./Output (Dcr Type Dcr Type) Dcr)
(declare-fun proj%core!ops.function.FnOnce./Output (Dcr Type Dcr Type) Type)
(declare-sort anonymous_closure%11. 0)
(declare-sort anonymous_closure%13. 0)
(declare-sort anonymous_closure%7. 0)
(declare-sort anonymous_closure%9. 0)
(declare-datatypes ((tuple%0. 0) (tuple%1. 0)) (((tuple%0./tuple%0)) ((tuple%1./tuple%1
    (tuple%1./tuple%1/?0 Poly)
))))
(declare-fun tuple%1./tuple%1/0 (tuple%1.) Poly)
(declare-fun TYPE%tuple%1. (Dcr Type) Type)
(declare-const TYPE%anonymous_closure%7. Type)
(declare-const TYPE%anonymous_closure%9. Type)
(declare-const TYPE%anonymous_closure%11. Type)
(declare-const TYPE%anonymous_closure%13. Type)
(declare-fun Poly%anonymous_closure%11. (anonymous_closure%11.) Poly)
(declare-fun %Poly%anonymous_closure%11. (Poly) anonymous_closure%11.)
(declare-fun Poly%anonymous_closure%13. (anonymous_closure%13.) Poly)
(declare-fun %Poly%anonymous_closure%13. (Poly) anonymous_closure%13.)
(declare-fun Poly%anonymous_closure%7. (anonymous_closure%7.) Poly)
(declare-fun %Poly%anonymous_closure%7. (Poly) anonymous_closure%7.)
(declare-fun Poly%anonymous_closure%9. (anonymous_closure%9.) Poly)
(declare-fun %Poly%anonymous_closure%9. (Poly) anonymous_closure%9.)
(declare-fun Poly%tuple%0. (tuple%0.) Poly)
(declare-fun %Poly%tuple%0. (Poly) tuple%0.)
(declare-fun Poly%tuple%1. (tuple%1.) Poly)
(declare-fun %Poly%tuple%1. (Poly) tuple%1.)
(assert
 (forall ((x tuple%1.)) (!
   (= x (%Poly%tuple%1. (Poly%tuple%1. x)))
   :pattern ((Poly%tuple%1. x))
   :qid internal_crate__tuple__1_box_axiom_definition
   :skolemid skolem_internal_crate__tuple__1_box_axiom_definition
)))
(assert
 (forall ((T%0&. Dcr) (T%0& Type) (_0! Poly)) (!
   (=>
    (has_type _0! T%0&)
    (has_type (Poly%tuple%1. (tuple%1./tuple%1 _0!)) (TYPE%tuple%1. T%0&. T%0&))
   )
   :pattern ((has_type (Poly%tuple%1. (tuple%1./tuple%1 _0!)) (TYPE%tuple%1. T%0&. T%0&)))
   :qid internal_tuple__1./tuple__1_constructor_definition
   :skolemid skolem_internal_tuple__1./tuple__1_constructor_definition
)))
(assert
 (forall ((x tuple%1.)) (!
   (= (tuple%1./tuple%1/0 x) (tuple%1./tuple%1/?0 x))
   :pattern ((tuple%1./tuple%1/0 x))
   :qid internal_tuple__1./tuple__1/0_accessor_definition
   :skolemid skolem_internal_tuple__1./tuple__1/0_accessor_definition
)))
(assert
 (forall ((d Dcr) (t Type) (x Poly)) (!
   (=>
    (and
     (has_type x (MUTREF d t))
     (has_resolved $ (MUTREF d t) x)
    )
    (= (mut_ref_current% x) (mut_ref_future% x))
   )
   :pattern ((has_resolved $ (MUTREF d t) x))
   :qid prelude_resolved_mut_ref
   :skolemid skolem_prelude_resolved_mut_ref
)))
(declare-fun req%vstd!pervasive.exec_nonstatic_call. (Dcr Type Dcr Type Dcr Type Poly
  Poly
 ) Bool
)
(declare-const %%global_location_label%%0 Bool)
(assert
 (forall ((Args&. Dcr) (Args& Type) (Output&. Dcr) (Output& Type) (F&. Dcr) (F& Type)
   (f! Poly) (args! Poly)
  ) (!
   (= (req%vstd!pervasive.exec_nonstatic_call. Args&. Args& Output&. Output& F&. F& f!
     args!
    ) (=>
     %%global_location_label%%0
     (closure_req F& Args&. Args& f! args!)
   ))
   :pattern ((req%vstd!pervasive.exec_nonstatic_call. Args&. Args& Output&. Output& F&.
     F& f! args!
   ))
   :qid internal_req__vstd!pervasive.exec_nonstatic_call._definition
   :skolemid skolem_internal_req__vstd!pervasive.exec_nonstatic_call._definition
)))
(declare-fun ens%vstd!pervasive.exec_nonstatic_call. (Dcr Type Dcr Type Dcr Type Poly
  Poly Poly
 ) Bool
)
(assert
 (forall ((Args&. Dcr) (Args& Type) (Output&. Dcr) (Output& Type) (F&. Dcr) (F& Type)
   (f! Poly) (args! Poly) (output! Poly)
  ) (!
   (= (ens%vstd!pervasive.exec_nonstatic_call. Args&. Args& Output&. Output& F&. F& f!
     args! output!
    ) (and
     (has_type output! Output&)
     (closure_ens F& Args&. Args& f! args! output!)
   ))
   :pattern ((ens%vstd!pervasive.exec_nonstatic_call. Args&. Args& Output&. Output& F&.
     F& f! args! output!
   ))
   :qid internal_ens__vstd!pervasive.exec_nonstatic_call._definition
   :skolemid skolem_internal_ens__vstd!pervasive.exec_nonstatic_call._definition
)))
(declare-const no%param Int)
(declare-const a~16@0 Poly)
(declare-const %closure_return~17 tuple%0.)
(declare-const tmp%%1 anonymous_closure%9.)
(declare-const tmp%1 Poly)
(declare-const tmp%2 Poly)
(declare-const tmp%3 anonymous_closure%9.)
(declare-const tmp%4 Poly)
(declare-const tmp%5 tuple%1.)
(declare-const tmp%6 Bool)
(declare-const tmp%7 Poly)
(declare-const tmp%8 Poly)
(declare-const tmp%9 anonymous_closure%9.)
(declare-const tmp%10 Poly)
(declare-const tmp%11 tuple%1.)
(declare-const tmp%12 Bool)
(declare-const c@ anonymous_closure%9.)
(declare-const x@0 Int)
(declare-const y@0 Int)
(declare-const tmp@0 anonymous_closure%9.)
(declare-const tmp$1@0 Int)
(declare-const tmp$2@0 Int)
(declare-const a~16@1 Poly)
(declare-const tmp@1 anonymous_closure%9.)
(declare-const tmp$1@1 Int)
(declare-const x@1 Int)
(declare-const tmp$2@1 Int)
(declare-const y@1 Int)
(declare-const %%location_label%%0 Bool)
(declare-const %%location_label%%1 Bool)
(declare-const %%location_label%%2 Bool)
(declare-const %%location_label%%3 Bool)
(declare-const %%location_label%%4 Bool)
(declare-const %%location_label%%5 Bool)
(assert
 (not (and
   (=>
    (has_type a~16@0 (MUTREF $ (UINT 64)))
    (=>
     (< (%I (mut_ref_current% a~16@0)) 100)
     (and
      (=>
       %%location_label%%0
       (uInv 64 (Add (%I (mut_ref_current% a~16@0)) 1))
      )
      (=>
       (uInv 64 (Add (%I (mut_ref_current% a~16@0)) 1))
       (=>
        (= a~16@1 (mut_ref_update_current% a~16@0 (I (uClip 64 (Add (%I (mut_ref_current% a~16@0))
             1
        )))))
        (=>
         (has_type a~16@1 (MUTREF $ (UINT 64)))
         (=>
          (has_resolved $ (MUTREF $ (UINT 64)) a~16@1)
          (=>
           (= %closure_return~17 tuple%0./tuple%0)
           (=>
            %%location_label%%1
            (= (%I (mut_ref_future% a~16@0)) (Add (%I (mut_ref_current% a~16@0)) 1))
   )))))))))
   (=>
    (and
     (forall ((closure%$ Poly)) (!
       (=>
        (has_type closure%$ (TYPE%tuple%1. $ (MUTREF $ (UINT 64))))
        (=>
         (let
          ((a$ (tuple%1./tuple%1/0 (%Poly%tuple%1. closure%$))))
          (< (%I (mut_ref_current% a$)) 100)
         )
         (closure_req TYPE%anonymous_closure%9. (DST $) (TYPE%tuple%1. $ (MUTREF $ (UINT 64)))
          (Poly%anonymous_closure%9. tmp%%1) closure%$
       )))
       :pattern ((closure_req TYPE%anonymous_closure%9. (DST $) (TYPE%tuple%1. $ (MUTREF $ (
            UINT 64
          ))
         ) (Poly%anonymous_closure%9. tmp%%1) closure%$
       ))
       :qid user_test_crate__test1_6
       :skolemid skolem_user_test_crate__test1_6
     ))
     (forall ((closure%$ Poly) (%closure_return$ Poly)) (!
       (=>
        (and
         (has_type closure%$ (TYPE%tuple%1. $ (MUTREF $ (UINT 64))))
         (has_type %closure_return$ TYPE%tuple%0.)
        )
        (=>
         (closure_ens TYPE%anonymous_closure%9. (DST $) (TYPE%tuple%1. $ (MUTREF $ (UINT 64)))
          (Poly%anonymous_closure%9. tmp%%1) closure%$ %closure_return$
         )
         (let
          ((a$ (tuple%1./tuple%1/0 (%Poly%tuple%1. closure%$))))
          (= (%I (mut_ref_future% a$)) (Add (%I (mut_ref_current% a$)) 1))
       )))
       :pattern ((closure_ens TYPE%anonymous_closure%9. (DST $) (TYPE%tuple%1. $ (MUTREF $ (
            UINT 64
          ))
         ) (Poly%anonymous_closure%9. tmp%%1) closure%$ %closure_return$
       ))
       :qid user_test_crate__test1_7
       :skolemid skolem_user_test_crate__test1_7
    )))
    (=>
     (= tmp@1 tmp%%1)
     (=>
      (has_resolved $ TYPE%anonymous_closure%9. (Poly%anonymous_closure%9. tmp@1))
      (=>
       (= c@ tmp@1)
       (=>
        (has_resolved $ TYPE%anonymous_closure%9. (Poly%anonymous_closure%9. c@))
        (=>
         (= tmp$1@1 0)
         (=>
          (has_resolved $ (UINT 64) (I tmp$1@1))
          (=>
           (= x@0 tmp$1@1)
           (=>
            (= tmp%3 c@)
            (=>
             (has_type tmp%1 (MUTREF $ (UINT 64)))
             (=>
              (= (%I (mut_ref_current% tmp%1)) x@0)
              (=>
               (= tmp%2 tmp%1)
               (=>
                (= x@1 (%I (mut_ref_future% tmp%1)))
                (=>
                 (has_resolved $ (UINT 64) (I x@1))
                 (=>
                  (= tmp%5 (tuple%1./tuple%1 tmp%2))
                  (and
                   (=>
                    %%location_label%%2
                    (req%vstd!pervasive.exec_nonstatic_call. (DST $) (TYPE%tuple%1. $ (MUTREF $ (UINT 64)))
                     $ TYPE%tuple%0. (REF $) TYPE%anonymous_closure%9. (Poly%anonymous_closure%9. tmp%3)
                     (Poly%tuple%1. tmp%5)
                   ))
                   (=>
                    (ens%vstd!pervasive.exec_nonstatic_call. (DST $) (TYPE%tuple%1. $ (MUTREF $ (UINT 64)))
                     $ TYPE%tuple%0. (REF $) TYPE%anonymous_closure%9. (Poly%anonymous_closure%9. tmp%3)
                     (Poly%tuple%1. tmp%5) tmp%4
                    )
                    (=>
                     (= tmp%6 (= x@1 1))
                     (and
                      (=>
                       %%location_label%%3
                       tmp%6
                      )
                      (=>
                       tmp%6
                       (=>
                        (= tmp$2@1 0)
                        (=>
                         (has_resolved $ (UINT 64) (I tmp$2@1))
                         (=>
                          (= y@0 tmp$2@1)
                          (=>
                           (= tmp%9 c@)
                           (=>
                            (has_type tmp%7 (MUTREF $ (UINT 64)))
                            (=>
                             (= (%I (mut_ref_current% tmp%7)) y@0)
                             (=>
                              (= tmp%8 tmp%7)
                              (=>
                               (= y@1 (%I (mut_ref_future% tmp%7)))
                               (=>
                                (has_resolved $ (UINT 64) (I y@1))
                                (=>
                                 (= tmp%11 (tuple%1./tuple%1 tmp%8))
                                 (and
                                  (=>
                                   %%location_label%%4
                                   (req%vstd!pervasive.exec_nonstatic_call. (DST $) (TYPE%tuple%1. $ (MUTREF $ (UINT 64)))
                                    $ TYPE%tuple%0. (REF $) TYPE%anonymous_closure%9. (Poly%anonymous_closure%9. tmp%9)
                                    (Poly%tuple%1. tmp%11)
                                  ))
                                  (=>
                                   (ens%vstd!pervasive.exec_nonstatic_call. (DST $) (TYPE%tuple%1. $ (MUTREF $ (UINT 64)))
                                    $ TYPE%tuple%0. (REF $) TYPE%anonymous_closure%9. (Poly%anonymous_closure%9. tmp%9)
                                    (Poly%tuple%1. tmp%11) tmp%10
                                   )
                                   (=>
                                    (= tmp%12 (= y@1 1))
                                    (=>
                                     %%location_label%%5
                                     tmp%12
)))))))))))))))))))))))))))))))))))))
(set-option :rlimit 30000000)
(check-sat)
