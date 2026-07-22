(* Copyright 2026 Andrew Yates
 * Author: Andrew Yates
 * Licensed under the Apache License, Version 2.0 *)

(** OCaml binding for the AY SMT solver, over its stable C API (ay.h).

    This is a THIN, sound wrapper. Every [sat]/[unsat] verdict and every model
    is computed by the AY solver itself; this module only marshals SMT-LIB text
    in and results out. The term builders below construct SMT-LIB term strings
    (no semantic change), and assertion / checking is delegated to AY's C API. *)

(** {1 Results} *)

type result =
  | Sat
  | Unsat
  | Unknown
  | Error

val string_of_result : result -> string

(** {1 Solver lifecycle} *)

type solver
(** An AY solver instance. Backed by an [AYSolver*] from the C API and finalized
    by the GC; [free] may be called to release it eagerly (idempotent). *)

val mk_solver : ?logic:string -> unit -> solver
(** Create a fresh solver. If [logic] is given (e.g. ["QF_LIA"]) it is declared
    immediately via [set-logic]. Raises [Failure] if AY rejects the logic
    (e.g. an unknown or unsupported logic name). *)

val free : solver -> unit
(** Release the underlying C handle eagerly. Idempotent and safe; the GC would
    do this anyway. *)

val reset : solver -> unit
(** Clear all assertions and declarations. *)

val version : unit -> string
(** The AY build stamp reported by the linked library. *)

(** {1 Sorts and term construction (sound SMT-LIB builders)} *)

type sort = Bool | Int | Real
(** The sorts this thin binding exposes for constant declaration. *)

type term
(** An opaque SMT-LIB term. Internally just its textual rendering; [to_string]
    exposes it. Constructing a term has no effect on any solver. *)

val to_string : term -> string

(** Declare a constant of the given sort on [solver] and return a term
    referring to it. The declaration is emitted via the C API; the returned
    term is the symbol itself. *)
val declare_const : solver -> string -> sort -> term

val bool_const : solver -> string -> term   (** [declare_const s n Bool] *)
val int_const : solver -> string -> term    (** [declare_const s n Int] *)
val real_const : solver -> string -> term   (** [declare_const s n Real] *)

(* Literals *)
val true_ : term
val false_ : term
val int_lit : int -> term      (** integer numeral (negatives rendered as [(- n)]) *)
val bool_lit : bool -> term

(* Boolean connectives *)
val not_ : term -> term
val and_ : term list -> term   (** [(and ...)]; [[]] -> [true], single -> itself *)
val or_ : term list -> term    (** [(or ...)]; [[]] -> [false], single -> itself *)
val implies : term -> term -> term
val iff : term -> term -> term
val ite : term -> term -> term -> term

(* Equality / arithmetic comparison *)
val eq : term -> term -> term
val neq : term -> term -> term
val lt : term -> term -> term
val le : term -> term -> term
val gt : term -> term -> term
val ge : term -> term -> term

(* Arithmetic. Single-element lists return the element ([sub] its negation);
   an empty list raises [Invalid_argument] — the binding is untyped over
   Int/Real, so no sort-safe SMT-LIB identity exists for an empty sum or
   product. *)
val add : term list -> term
val sub : term list -> term
val mul : term list -> term
val neg : term -> term

(** {1 Assertion and checking (delegated to AY)} *)

val assert_ : solver -> term -> unit
(** Add an assertion. Raises [Failure] if AY rejects the term. *)

val check_sat : solver -> result
(** Check satisfiability of the current assertion stack. *)

val push : solver -> unit
val pop : solver -> int -> unit

val get_model : solver -> string option
(** The model from the last [Sat] check, as an SMT-LIB string, or [None]. *)

val last_error : solver -> string option
(** The last error message recorded by the C API, if any. *)

(** {1 Raw batch escape hatch} *)

val solve_smtlib : solver -> string -> result
(** Run a raw block of SMT-LIB commands (set-logic, declarations, asserts,
    check-sat). Returns the verdict of the last [check-sat]. Used by
    [mk_solver]'s [?logic] and available for setup that the typed builders do
    not cover. *)
