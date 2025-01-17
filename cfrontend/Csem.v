(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*          Xavier Leroy, INRIA Paris-Rocquencourt                     *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique.  All rights reserved.  This file is distributed       *)
(*  under the terms of the GNU General Public License as published by  *)
(*  the Free Software Foundation, either version 2 of the License, or  *)
(*  (at your option) any later version.  This file is also distributed *)
(*  under the terms of the INRIA Non-Commercial License Agreement.     *)
(*                                                                     *)
(* *********************************************************************)

(** Dynamic semantics for the Compcert C language *)

Require Import Coqlib.
Require Import Errors.
Require Import Maps.
Require Import Integers.
Require Import Floats.
Require Import Values.
Require Import AST.
Require Import Memory.
Require Import Events.
Require Import Globalenvs.
Require Import Ctypes.
Require Import Cop.
Require Import Csyntax.
Require Import Smallstep.

(** * Operational semantics *)

(** The semantics uses two environments.  The global environment
  maps names of functions and global variables to memory block references,
  and function pointers to their definitions.  (See module [Globalenvs].) *)

Definition genv := Genv.t fundef type.

(** The local environment maps local variables to block references and types.
  The current value of the variable is stored in the associated memory
  block. *)

Definition env := PTree.t (block * type). (* map variable -> location & type *)

Definition empty_env: env := (PTree.empty (block * type)).

(** We keep track of a set of locations that we have written to during
  expression execution.  If two unsequenced writes to the same location, or
  an unsequenced write followed by a read to the same location occur, we
  assign undefined behavior.  Sequence points are captured by emptying this
  set. *)

Definition seqs := ZMap.t Intv.set.
Definition empty_seqs := (ZMap.init (@nil Intv.interv)).

Definition is_not_seq (sq: seqs) (b: block) (ofs: Z) (n: Z) :=
  Intv.set_disjoint1 (ofs, ofs + n) (PMap.get b sq).
Definition add_seq (sq: seqs) (b: block) (ofs: Z) (n: Z) : seqs :=
  PMap.set b ((ofs, ofs + n) :: PMap.get b sq) sq.

Lemma is_not_seq_dec sq b ofs n :
  { is_not_seq sq b ofs n } + { ~is_not_seq sq b ofs n }.
Proof. apply Intv.set_disjoint1_dec. Defined.

(** [deref_loc ty m b ofs t v] computes the value of a datum
  of type [ty] residing in memory [m] at block [b], offset [ofs].
  If the type [ty] indicates an access by value, the corresponding
  memory load is performed.  If the type [ty] indicates an access by
  reference, the pointer [Vptr b ofs] is returned.  [v] is the value
  returned, and [t] the trace of observables (nonempty if this is
  a volatile access). *)

Inductive deref_loc {F V: Type} (ge: Genv.t F V) (ty: type) (m: mem) (sq : seqs)
      (b: block) (ofs: int) : trace -> val -> Prop :=
  | deref_loc_value: forall chunk v,
      access_mode ty = By_value chunk ->
      type_is_volatile ty = false ->
      Mem.loadv chunk m (Vptr b ofs) = Some v ->
      is_not_seq sq b (Int.unsigned ofs) (size_chunk chunk) ->
      deref_loc ge ty m sq b ofs E0 v
  | deref_loc_volatile: forall chunk t v,
      access_mode ty = By_value chunk ->
      type_is_volatile ty = true ->
      volatile_load ge chunk m b ofs t v ->
      is_not_seq sq b (Int.unsigned ofs) (size_chunk chunk) ->
      deref_loc ge ty m sq b ofs t v
  | deref_loc_reference:
      access_mode ty = By_reference ->
      deref_loc ge ty m sq b ofs E0 (Vptr b ofs)
  | deref_loc_copy:
      access_mode ty = By_copy ->
      deref_loc ge ty m sq b ofs E0 (Vptr b ofs).

(** Symmetrically, [assign_loc ty m b ofs v t m'] returns the
  memory state after storing the value [v] in the datum
  of type [ty] residing in memory [m] at block [b], offset [ofs].
  This is allowed only if [ty] indicates an access by value or by copy.
  [m'] is the updated memory state and [t] the trace of observables
  (nonempty if this is a volatile store). *)

Inductive assign_loc {F V: Type} (ge: Genv.t F V) (ty: type) (m: mem) (sq : seqs)
      (b: block) (ofs: int) : val -> trace -> mem -> seqs -> Prop :=
  | assign_loc_value: forall v chunk m',
      access_mode ty = By_value chunk ->
      type_is_volatile ty = false ->
      Mem.storev chunk m (Vptr b ofs) v = Some m' ->
      is_not_seq sq b (Int.unsigned ofs) (size_chunk chunk) ->
      assign_loc ge ty m sq b ofs v E0 m'
        (add_seq sq b (Int.unsigned ofs) (size_chunk chunk))
  | assign_loc_volatile: forall v chunk t m',
      access_mode ty = By_value chunk -> type_is_volatile ty = true ->
      volatile_store ge chunk m b ofs v t m' ->
      is_not_seq sq b (Int.unsigned ofs) (size_chunk chunk) ->
      assign_loc ge ty m sq b ofs v t m'
        (add_seq sq b (Int.unsigned ofs) (size_chunk chunk))
  | assign_loc_copy: forall b' ofs' bytes m',
      access_mode ty = By_copy ->
      (alignof_blockcopy ty | Int.unsigned ofs') ->
      (alignof_blockcopy ty | Int.unsigned ofs) ->
      b' <> b \/ Int.unsigned ofs' = Int.unsigned ofs
              \/ Int.unsigned ofs' + sizeof ty <= Int.unsigned ofs
              \/ Int.unsigned ofs + sizeof ty <= Int.unsigned ofs' ->
      Mem.loadbytes m b' (Int.unsigned ofs') (sizeof ty) = Some bytes ->
      Mem.storebytes m b (Int.unsigned ofs) bytes = Some m' ->
      is_not_seq sq b (Int.unsigned ofs) (list_length_z bytes) ->
      assign_loc ge ty m sq b ofs (Vptr b' ofs') E0 m'
        (add_seq sq b (Int.unsigned ofs) (list_length_z bytes)).

(** Allocation of function-local variables.
  [alloc_variables e1 m1 vars e2 m2] allocates one memory block
  for each variable declared in [vars], and associates the variable
  name with this block.  [e1] and [m1] are the initial local environment
  and memory state.  [e2] and [m2] are the final local environment
  and memory state. *)

Inductive alloc_variables: env -> mem ->
                           list (ident * type) ->
                           env -> mem -> Prop :=
  | alloc_variables_nil:
      forall e m,
      alloc_variables e m nil e m
  | alloc_variables_cons:
      forall e m id ty vars m1 b1 m2 e2,
      Mem.alloc m 0 (sizeof ty) = (m1, b1) ->
      alloc_variables (PTree.set id (b1, ty) e) m1 vars e2 m2 ->
      alloc_variables e m ((id, ty) :: vars) e2 m2.

(** Initialization of local variables that are parameters to a function.
  [bind_parameters e m1 params args m2] stores the values [args]
  in the memory blocks corresponding to the variables [params].
  [m1] is the initial memory state and [m2] the final memory state. *)

Inductive bind_parameters {F V: Type} (ge: Genv.t F V) (e: env):
                           mem -> list (ident * type) -> list val ->
                           mem -> Prop :=
  | bind_parameters_nil:
      forall m,
      bind_parameters ge e m nil nil m
  | bind_parameters_cons:
      forall m id ty params v1 vl b m1 m2 sq,
      PTree.get id e = Some(b, ty) ->
      assign_loc ge ty m empty_seqs b Int.zero v1 E0 m1 sq ->
      bind_parameters ge e m1 params vl m2 ->
      bind_parameters ge e m ((id, ty) :: params) (v1 :: vl) m2.

(** Return the list of blocks in the codomain of [e], with low and high bounds. *)

Definition block_of_binding (id_b_ty: ident * (block * type)) :=
  match id_b_ty with (id, (b, ty)) => (b, 0, sizeof ty) end.

Definition blocks_of_env (e: env) : list (block * Z * Z) :=
  List.map block_of_binding (PTree.elements e).

(** Selection of the appropriate case of a [switch], given the value [n]
  of the selector expression. *)

Fixpoint select_switch_default (sl: labeled_statements): labeled_statements :=
  match sl with
  | LSnil => sl
  | LScons None s sl' => sl
  | LScons (Some i) s sl' => select_switch_default sl'
  end.

Fixpoint select_switch_case (n: int) (sl: labeled_statements): option labeled_statements :=
  match sl with
  | LSnil => None
  | LScons None s sl' => select_switch_case n sl'
  | LScons (Some c) s sl' => if Int.eq c n then Some sl else select_switch_case n sl'
  end.

Definition select_switch (n: int) (sl: labeled_statements): labeled_statements :=
  match select_switch_case n sl with
  | Some sl' => sl'
  | None => select_switch_default sl
  end.

(** Turn a labeled statement into a sequence *)

Fixpoint seq_of_labeled_statement (sl: labeled_statements) : statement :=
  match sl with
  | LSnil => Sskip
  | LScons _ s sl' => Ssequence s (seq_of_labeled_statement sl')
  end.

(** Extract the values from a list of function arguments *)

Inductive cast_arguments: exprlist -> typelist -> list val -> Prop :=
  | cast_args_nil:
      cast_arguments Enil Tnil nil
  | cast_args_cons: forall v ty el targ1 targs v1 vl,
      sem_cast v ty targ1 = Some v1 -> cast_arguments el targs vl ->
      cast_arguments (Econs (Eval v ty) el) (Tcons targ1 targs) (v1 :: vl).

Section SEMANTICS.

Variable ge: genv.

(** ** Reduction semantics for expressions *)

Section EXPR.

Variable e: env.

(** The semantics of expressions follows the popular Wright-Felleisen style.
  It is a small-step semantics that reduces one redex at a time.
  We first define head reductions (at the top of an expression, then
  use reduction contexts to define reduction within an expression. *)

(** Head reduction for l-values. *)

Inductive lred: expr -> mem -> expr -> mem -> Prop :=
  | red_var_local: forall x ty m b,
      e!x = Some(b, ty) ->
      lred (Evar x ty) m
           (Eloc b Int.zero ty) m
  | red_var_global: forall x ty m b,
      e!x = None ->
      Genv.find_symbol ge x = Some b ->
      lred (Evar x ty) m
           (Eloc b Int.zero ty) m
  | red_deref: forall b ofs ty1 ty m,
      lred (Ederef (Eval (Vptr b ofs) ty1) ty) m
           (Eloc b ofs ty) m
  | red_field_struct: forall b ofs id fList a f ty m delta,
      field_offset f fList = OK delta ->
      lred (Efield (Eval (Vptr b ofs) (Tstruct id fList a)) f ty) m
           (Eloc b (Int.add ofs (Int.repr delta)) ty) m
  | red_field_union: forall b ofs id fList a f ty m,
      lred (Efield (Eval (Vptr b ofs) (Tunion id fList a)) f ty) m
           (Eloc b ofs ty) m.

(** Head reductions for r-values *)

Inductive rred: expr -> mem -> seqs -> trace -> expr -> mem -> seqs -> Prop :=
  | red_rvalof: forall b ofs ty m sq t v,
      deref_loc ge ty m sq b ofs t v ->
      rred (Evalof (Eloc b ofs ty) ty) m sq
         t (Eval v ty) m sq
  | red_addrof: forall b ofs ty1 ty m sq,
      rred (Eaddrof (Eloc b ofs ty1) ty) m sq
        E0 (Eval (Vptr b ofs) ty) m sq
  | red_unop: forall op v1 ty1 ty m sq v,
      sem_unary_operation op v1 ty1 = Some v ->
      rred (Eunop op (Eval v1 ty1) ty) m sq
        E0 (Eval v ty) m sq
  | red_binop: forall op v1 ty1 v2 ty2 ty m sq v,
      sem_binary_operation op v1 ty1 v2 ty2 m = Some v ->
      rred (Ebinop op (Eval v1 ty1) (Eval v2 ty2) ty) m sq
        E0 (Eval v ty) m sq
  | red_cast: forall ty v1 ty1 m sq v,
      sem_cast v1 ty1 ty = Some v ->
      rred (Ecast (Eval v1 ty1) ty) m sq
        E0 (Eval v ty) m sq
  | red_seqand_true: forall v1 ty1 r2 ty m sq,
      bool_val v1 ty1 = Some true ->
      rred (Eseqand (Eval v1 ty1) r2 ty) m sq
        E0 (Eparen (Eparen r2 type_bool) ty) m empty_seqs
  | red_seqand_false: forall v1 ty1 r2 ty m sq,
      bool_val v1 ty1 = Some false ->
      rred (Eseqand (Eval v1 ty1) r2 ty) m sq
        E0 (Eval (Vint Int.zero) ty) m sq
  | red_seqor_true: forall v1 ty1 r2 ty m sq,
      bool_val v1 ty1 = Some true ->
      rred (Eseqor (Eval v1 ty1) r2 ty) m sq
        E0 (Eval (Vint Int.one) ty) m sq
  | red_seqor_false: forall v1 ty1 r2 ty m sq,
      bool_val v1 ty1 = Some false ->
      rred (Eseqor (Eval v1 ty1) r2 ty) m sq
        E0 (Eparen (Eparen r2 type_bool) ty) m empty_seqs
  | red_condition: forall v1 ty1 r1 r2 ty b m sq,
      bool_val v1 ty1 = Some b ->
      rred (Econdition (Eval v1 ty1) r1 r2 ty) m sq
        E0 (Eparen (if b then r1 else r2) ty) m empty_seqs
  | red_sizeof: forall ty1 ty m sq,
      rred (Esizeof ty1 ty) m sq
        E0 (Eval (Vint (Int.repr (sizeof ty1))) ty) m sq
  | red_alignof: forall ty1 ty m sq,
      rred (Ealignof ty1 ty) m sq
        E0 (Eval (Vint (Int.repr (alignof ty1))) ty) m sq
  | red_assign: forall b ofs ty1 v2 ty2 m sq v t m' sq',
      sem_cast v2 ty2 ty1 = Some v ->
      assign_loc ge ty1 m sq b ofs v t m' sq' ->
      rred (Eassign (Eloc b ofs ty1) (Eval v2 ty2) ty1) m sq
         t (Eval v ty1) m' sq'
  | red_assignop: forall op b ofs ty1 v2 ty2 tyres m sq t v1,
      deref_loc ge ty1 m sq b ofs t v1 ->
      rred (Eassignop op (Eloc b ofs ty1) (Eval v2 ty2) tyres ty1) m sq
         t (Eassign (Eloc b ofs ty1)
                    (Ebinop op (Eval v1 ty1) (Eval v2 ty2) tyres) ty1) m sq
  | red_postincr: forall id b ofs ty m sq t v1 op,
      deref_loc ge ty m sq b ofs t v1 ->
      op = match id with Incr => Oadd | Decr => Osub end ->
      rred (Epostincr id (Eloc b ofs ty) ty) m sq
         t (Ecomma false (Eassign (Eloc b ofs ty) 
                           (Ebinop op (Eval v1 ty) (Eval (Vint Int.one) type_int32s) (typeconv ty))
                           ty)
                   (Eval v1 ty) ty) m sq
  | red_comma: forall sp v ty1 r2 ty m sq,
      typeof r2 = ty ->
      rred (Ecomma sp (Eval v ty1) r2 ty) m sq
        E0 r2 m (if sp then empty_seqs else sq)
  | red_paren: forall v1 ty1 ty m sq v,
      sem_cast v1 ty1 ty = Some v ->
      rred (Eparen (Eval v1 ty1) ty) m sq
        E0 (Eval v ty) m sq
  | red_builtin: forall ef tyargs el ty m sq vargs t vres m',
      cast_arguments el tyargs vargs ->
      external_call ef ge vargs m t vres m' ->
      rred (Ebuiltin ef tyargs el ty) m sq
         t (Eval vres ty) m' empty_seqs.

(** Head reduction for function calls.
    (More exactly, identification of function calls that can reduce.) *)

Inductive callred: expr -> fundef -> list val -> type -> Prop :=
  | red_Ecall: forall vf tyf tyargs tyres cconv el ty fd vargs,
      Genv.find_funct ge vf = Some fd ->
      cast_arguments el tyargs vargs ->
      type_of_fundef fd = Tfunction tyargs tyres cconv ->
      classify_fun tyf = fun_case_f tyargs tyres cconv ->
      callred (Ecall (Eval vf tyf) el ty)
              fd vargs ty.

(** Reduction contexts.  In accordance with C's nondeterministic semantics,
  we allow reduction both to the left and to the right of a binary operator.
  To enforce C's notion of sequence point, reductions within a conditional
  [a ? b : c] can only take place in [a], not in [b] nor [c];
  reductions within a sequential "or" / "and" [a && b] or [a || b] can
  only take place in [a], not in [b];
  and reductions within a sequence [a, b] can only take place in [a],
  not in [b].

  Reduction contexts are represented by functions [C] from expressions
  to expressions, suitably constrained by the [context from to C]
  predicate below.  Contexts are "kinded" with respect to l-values and
  r-values: [from] is the kind of the hole in the context and [to] is
  the kind of the term resulting from filling the hole.
*)

Inductive kind : Type := LV | RV.

Inductive context: kind -> kind -> (expr -> expr) -> Prop :=
  | ctx_top: forall k,
      context k k (fun x => x)
  | ctx_deref: forall k C ty,
      context k RV C -> context k LV (fun x => Ederef (C x) ty)
  | ctx_field: forall k C f ty,
      context k RV C -> context k LV (fun x => Efield (C x) f ty)
  | ctx_rvalof: forall k C ty,
      context k LV C -> context k RV (fun x => Evalof (C x) ty)
  | ctx_addrof: forall k C ty,
      context k LV C -> context k RV (fun x => Eaddrof (C x) ty)
  | ctx_unop: forall k C op ty,
      context k RV C -> context k RV (fun x => Eunop op (C x) ty)
  | ctx_binop_left: forall k C op e2 ty,
      context k RV C -> context k RV (fun x => Ebinop op (C x) e2 ty)
  | ctx_binop_right: forall k C op e1 ty,
      context k RV C -> context k RV (fun x => Ebinop op e1 (C x) ty)
  | ctx_cast: forall k C ty,
      context k RV C -> context k RV (fun x => Ecast (C x) ty)
  | ctx_seqand: forall k C r2 ty,
      context k RV C -> context k RV (fun x => Eseqand (C x) r2 ty)
  | ctx_seqor: forall k C r2 ty,
      context k RV C -> context k RV (fun x => Eseqor (C x) r2 ty)
  | ctx_condition: forall k C r2 r3 ty,
      context k RV C -> context k RV (fun x => Econdition (C x) r2 r3 ty)
  | ctx_assign_left: forall k C e2 ty,
      context k LV C -> context k RV (fun x => Eassign (C x) e2 ty)
  | ctx_assign_right: forall k C e1 ty,
      context k RV C -> context k RV (fun x => Eassign e1 (C x) ty)
  | ctx_assignop_left: forall k C op e2 tyres ty,
      context k LV C -> context k RV (fun x => Eassignop op (C x) e2 tyres ty)
  | ctx_assignop_right: forall k C op e1 tyres ty,
      context k RV C -> context k RV (fun x => Eassignop op e1 (C x) tyres ty)
  | ctx_postincr: forall k C id ty,
      context k LV C -> context k RV (fun x => Epostincr id (C x) ty)
  | ctx_call_left: forall k C el ty,
      context k RV C -> context k RV (fun x => Ecall (C x) el ty)
  | ctx_call_right: forall k C e1 ty,
      contextlist k C -> context k RV (fun x => Ecall e1 (C x) ty)
  | ctx_builtin: forall k C ef tyargs ty,
      contextlist k C -> context k RV (fun x => Ebuiltin ef tyargs (C x) ty)
  | ctx_comma: forall k C sp e2 ty,
      context k RV C -> context k RV (fun x => Ecomma sp (C x) e2 ty)
  | ctx_paren: forall k C ty,
      context k RV C -> context k RV (fun x => Eparen (C x) ty)

with contextlist: kind -> (expr -> exprlist) -> Prop :=
  | ctx_list_head: forall k C el,
      context k RV C -> contextlist k (fun x => Econs (C x) el)
  | ctx_list_tail: forall k C e1,
      contextlist k C -> contextlist k (fun x => Econs e1 (C x)).

(** In a nondeterministic semantics, expressions can go wrong according
  to one reduction order while being defined according to another.
  Consider for instance [(x = 1) + (10 / x)] where [x] is initially [0].
  This expression goes wrong if evaluated right-to-left, but is defined
  if evaluated left-to-right.  Since our compiler is going to pick one
  particular evaluation order, we must make sure that all orders are safe,
  i.e. never evaluate a subexpression that goes wrong.

  Being safe is a stronger requirement than just not getting stuck during
  reductions.  Consider [f() + (10 / x)], where [f()] does not terminate.
  This expression is never stuck because the evaluation of [f()] can make
  infinitely many transitions.  Yet it contains a subexpression [10 / x]
  that can go wrong if [x = 0], and the compiler may choose to evaluate
  [10 / x] first, before calling [f()].  

  Therefore, we must make sure that not only an expression cannot get stuck,
  but none of its subexpressions can either.  We say that a subexpression
  is not immediately stuck if it is a value (of the appropriate kind)
  or it can reduce (at head or within). *)

Inductive imm_safe: kind -> expr -> mem -> seqs -> Prop :=
  | imm_safe_val: forall v ty m sq,
      imm_safe RV (Eval v ty) m sq
  | imm_safe_loc: forall b ofs ty m sq,
      imm_safe LV (Eloc b ofs ty) m sq
  | imm_safe_lred: forall to C e m sq e' m',
      lred e m e' m' ->
      context LV to C ->
      imm_safe to (C e) m sq
  | imm_safe_rred: forall to C e m sq t e' m' sq',
      rred e m sq t e' m' sq' ->
      context RV to C ->
      imm_safe to (C e) m sq
  | imm_safe_callred: forall to C e m sq fd args ty,
      callred e fd args ty ->
      context RV to C ->
      imm_safe to (C e) m sq.

(* An expression is not stuck if none of the potential redexes contained within
   is immediately stuck. *)
(*
Definition not_stuck (e: expr) (m: mem) : Prop :=
  forall k C e' , 
  context k RV C -> e = C e' -> not_imm_stuck k e' m.
*)
End EXPR. 

(** ** Transition semantics. *)

(** Continuations describe the computations that remain to be performed
    after the statement or expression under consideration has
    evaluated completely. *)

Inductive cont: Type :=
  | Kstop: cont
  | Kdo: cont -> cont       (**r [Kdo k] = after [x] in [x;] *)
  | Kseq: statement -> cont -> cont    (**r [Kseq s2 k] = after [s1] in [s1;s2] *)
  | Kifthenelse: statement -> statement -> cont -> cont     (**r [Kifthenelse s1 s2 k] = after [x] in [if (x) { s1 } else { s2 }] *)
  | Kwhile1: expr -> statement -> cont -> cont      (**r [Kwhile1 x s k] = after [x] in [while(x) s] *)
  | Kwhile2: expr -> statement -> cont -> cont      (**r [Kwhile x s k] = after [s] in [while (x) s] *)
  | Kdowhile1: expr -> statement -> cont -> cont    (**r [Kdowhile1 x s k] = after [s] in [do s while (x)] *)
  | Kdowhile2: expr -> statement -> cont -> cont    (**r [Kdowhile2 x s k] = after [x] in [do s while (x)] *)
  | Kfor2: expr -> statement -> statement -> cont -> cont   (**r [Kfor2 e2 e3 s k] = after [e2] in [for(e1;e2;e3) s] *)
  | Kfor3: expr -> statement -> statement -> cont -> cont   (**r [Kfor3 e2 e3 s k] = after [s] in [for(e1;e2;e3) s] *)
  | Kfor4: expr -> statement -> statement -> cont -> cont   (**r [Kfor4 e2 e3 s k] = after [e3] in [for(e1;e2;e3) s] *)
  | Kswitch1: labeled_statements -> cont -> cont     (**r [Kswitch1 ls k] = after [e] in [switch(e) { ls }] *)
  | Kswitch2: cont -> cont       (**r catches [break] statements arising out of [switch] *)
  | Kreturn: cont -> cont        (**r [Kreturn k] = after [e] in [return e;] *)
  | Kcall: function ->           (**r calling function *)
           env ->                (**r local env of calling function *)
           (expr -> expr) ->     (**r context of the call *)
           type ->               (**r type of call expression *)
           cont -> cont.

(** Pop continuation until a call or stop *)

Fixpoint call_cont (k: cont) : cont :=
  match k with
  | Kstop => k
  | Kdo k => k
  | Kseq s k => call_cont k
  | Kifthenelse s1 s2 k => call_cont k
  | Kwhile1 e s k => call_cont k
  | Kwhile2 e s k => call_cont k
  | Kdowhile1 e s k => call_cont k
  | Kdowhile2 e s k => call_cont k
  | Kfor2 e2 e3 s k => call_cont k
  | Kfor3 e2 e3 s k => call_cont k
  | Kfor4 e2 e3 s k => call_cont k
  | Kswitch1 ls k => call_cont k
  | Kswitch2 k => call_cont k
  | Kreturn k => call_cont k
  | Kcall _ _ _ _ _ => k
  end.

Definition is_call_cont (k: cont) : Prop :=
  match k with
  | Kstop => True
  | Kcall _ _ _ _ _ => True
  | _ => False
  end.

(** Execution states of the program are grouped in 4 classes corresponding
  to the part of the program we are currently executing.  It can be
  a statement ([State]), an expression ([ExprState]), a transition
  from a calling function to a called function ([Callstate]), or
  the symmetrical transition from a function back to its caller
  ([Returnstate]). *)

Inductive state: Type :=
  | State                               (**r execution of a statement *)
      (f: function)
      (s: statement)
      (k: cont)
      (e: env)
      (m: mem) : state
  | ExprState                           (**r reduction of an expression *)
      (f: function)
      (r: expr)
      (k: cont)
      (e: env)
      (m: mem)
      (sq: seqs) : state
  | Callstate                           (**r calling a function *)
      (fd: fundef)
      (args: list val)
      (k: cont)
      (m: mem) : state
  | Returnstate                         (**r returning from a function *)
      (res: val)
      (k: cont)
      (m: mem) : state
  | Stuckstate.                         (**r undefined behavior occurred *)
                 
(** Find the statement and manufacture the continuation 
  corresponding to a label. *)

Fixpoint find_label (lbl: label) (s: statement) (k: cont) 
                    {struct s}: option (statement * cont) :=
  match s with
  | Ssequence s1 s2 =>
      match find_label lbl s1 (Kseq s2 k) with
      | Some sk => Some sk
      | None => find_label lbl s2 k
      end
  | Sifthenelse a s1 s2 =>
      match find_label lbl s1 k with
      | Some sk => Some sk
      | None => find_label lbl s2 k
      end
  | Swhile a s1 =>
      find_label lbl s1 (Kwhile2 a s1 k)
  | Sdowhile a s1 =>
      find_label lbl s1 (Kdowhile1 a s1 k)
  | Sfor a1 a2 a3 s1 =>
      match find_label lbl a1 (Kseq (Sfor Sskip a2 a3 s1) k) with
      | Some sk => Some sk
      | None =>
          match find_label lbl s1 (Kfor3 a2 a3 s1 k) with
          | Some sk => Some sk
          | None => find_label lbl a3 (Kfor4 a2 a3 s1 k)
          end
      end
  | Sswitch e sl =>
      find_label_ls lbl sl (Kswitch2 k)
  | Slabel lbl' s' =>
      if ident_eq lbl lbl' then Some(s', k) else find_label lbl s' k
  | _ => None
  end

with find_label_ls (lbl: label) (sl: labeled_statements) (k: cont) 
                    {struct sl}: option (statement * cont) :=
  match sl with
  | LSnil => None
  | LScons _ s sl' =>
      match find_label lbl s (Kseq (seq_of_labeled_statement sl') k) with
      | Some sk => Some sk
      | None => find_label_ls lbl sl' k
      end
  end.

(** We separate the transition rules in two groups:
- one group that deals with reductions over expressions;
- the other group that deals with everything else: statements, function calls, etc.

This makes it easy to express different reduction strategies for expressions:
the second group of rules can be reused as is. *)

Inductive estep: state -> trace -> state -> Prop :=

  | step_lred: forall C f a k e m sq a' m',
      lred e a m a' m' ->
      context LV RV C ->
      estep (ExprState f (C a) k e m sq)
         E0 (ExprState f (C a') k e m' sq)

  | step_rred: forall C f a k e m sq t a' m' sq',
      rred a m sq t a' m' sq' ->
      context RV RV C ->
      estep (ExprState f (C a) k e m sq)
          t (ExprState f (C a') k e m' sq')

  | step_call: forall C f a k e m sq fd vargs ty,
      callred a fd vargs ty ->
      context RV RV C ->
      estep (ExprState f (C a) k e m sq)
         E0 (Callstate fd vargs (Kcall f e C ty k) m)

  | step_stuck: forall C f a k e m sq K,
      context K RV C -> ~(imm_safe e K a m sq) ->
      estep (ExprState f (C a) k e m sq)
         E0 Stuckstate.

Inductive sstep: state -> trace -> state -> Prop :=

  | step_do_1: forall f x k e m,
      sstep (State f (Sdo x) k e m)
         E0 (ExprState f x (Kdo k) e m empty_seqs)
  | step_do_2: forall f v ty k e m sq,
      sstep (ExprState f (Eval v ty) (Kdo k) e m sq)
         E0 (State f Sskip k e m)

  | step_seq:  forall f s1 s2 k e m,
      sstep (State f (Ssequence s1 s2) k e m)
         E0 (State f s1 (Kseq s2 k) e m)
  | step_skip_seq: forall f s k e m,
      sstep (State f Sskip (Kseq s k) e m)
         E0 (State f s k e m)
  | step_continue_seq: forall f s k e m,
      sstep (State f Scontinue (Kseq s k) e m)
         E0 (State f Scontinue k e m)
  | step_break_seq: forall f s k e m,
      sstep (State f Sbreak (Kseq s k) e m)
         E0 (State f Sbreak k e m)

  | step_ifthenelse_1: forall f a s1 s2 k e m,
      sstep (State f (Sifthenelse a s1 s2) k e m)
         E0 (ExprState f a (Kifthenelse s1 s2 k) e m empty_seqs)
  | step_ifthenelse_2:  forall f v ty s1 s2 k e m sq b,
      bool_val v ty = Some b ->
      sstep (ExprState f (Eval v ty) (Kifthenelse s1 s2 k) e m sq)
         E0 (State f (if b then s1 else s2) k e m)

  | step_while: forall f x s k e m,
      sstep (State f (Swhile x s) k e m)
        E0 (ExprState f x (Kwhile1 x s k) e m empty_seqs)
  | step_while_false: forall f v ty x s k e m sq,
      bool_val v ty = Some false ->
      sstep (ExprState f (Eval v ty) (Kwhile1 x s k) e m sq)
        E0 (State f Sskip k e m)
  | step_while_true: forall f v ty x s k e m sq,
      bool_val v ty = Some true ->
      sstep (ExprState f (Eval v ty) (Kwhile1 x s k) e m sq)
        E0 (State f s (Kwhile2 x s k) e m)
  | step_skip_or_continue_while: forall f s0 x s k e m,
      s0 = Sskip \/ s0 = Scontinue ->
      sstep (State f s0 (Kwhile2 x s k) e m)
        E0 (State f (Swhile x s) k e m)
  | step_break_while: forall f x s k e m,
      sstep (State f Sbreak (Kwhile2 x s k) e m)
        E0 (State f Sskip k e m)

  | step_dowhile: forall f a s k e m,
      sstep (State f (Sdowhile a s) k e m)
        E0 (State f s (Kdowhile1 a s k) e m)
  | step_skip_or_continue_dowhile: forall f s0 x s k e m,
      s0 = Sskip \/ s0 = Scontinue ->
      sstep (State f s0 (Kdowhile1 x s k) e m)
         E0 (ExprState f x (Kdowhile2 x s k) e m empty_seqs)
  | step_dowhile_false: forall f v ty x s k e m sq,
      bool_val v ty = Some false ->
      sstep (ExprState f (Eval v ty) (Kdowhile2 x s k) e m sq)
         E0 (State f Sskip k e m)
  | step_dowhile_true: forall f v ty x s k e m sq,
      bool_val v ty = Some true ->
      sstep (ExprState f (Eval v ty) (Kdowhile2 x s k) e m sq)
         E0 (State f (Sdowhile x s) k e m)
  | step_break_dowhile: forall f a s k e m,
      sstep (State f Sbreak (Kdowhile1 a s k) e m)
         E0 (State f Sskip k e m)

  | step_for_start: forall f a1 a2 a3 s k e m,
      a1 <> Sskip ->
      sstep (State f (Sfor a1 a2 a3 s) k e m)
         E0 (State f a1 (Kseq (Sfor Sskip a2 a3 s) k) e m)
  | step_for: forall f a2 a3 s k e m,
      sstep (State f (Sfor Sskip a2 a3 s) k e m)
         E0 (ExprState f a2 (Kfor2 a2 a3 s k) e m empty_seqs)
  | step_for_false: forall f v ty a2 a3 s k e m sq,
      bool_val v ty = Some false ->
      sstep (ExprState f (Eval v ty) (Kfor2 a2 a3 s k) e m sq)
         E0 (State f Sskip k e m)
  | step_for_true: forall f v ty a2 a3 s k e m sq,
      bool_val v ty = Some true ->
      sstep (ExprState f (Eval v ty) (Kfor2 a2 a3 s k) e m sq)
         E0 (State f s (Kfor3 a2 a3 s k) e m)
  | step_skip_or_continue_for3: forall f x a2 a3 s k e m,
      x = Sskip \/ x = Scontinue ->
      sstep (State f x (Kfor3 a2 a3 s k) e m)
         E0 (State f a3 (Kfor4 a2 a3 s k) e m)
  | step_break_for3: forall f a2 a3 s k e m,
      sstep (State f Sbreak (Kfor3 a2 a3 s k) e m)
         E0 (State f Sskip k e m)
  | step_skip_for4: forall f a2 a3 s k e m,
      sstep (State f Sskip (Kfor4 a2 a3 s k) e m)
         E0 (State f (Sfor Sskip a2 a3 s) k e m)

  | step_return_0: forall f k e m m',
      Mem.free_list m (blocks_of_env e) = Some m' ->
      sstep (State f (Sreturn None) k e m)
         E0 (Returnstate Vundef (call_cont k) m')
  | step_return_1: forall f x k e m,
      sstep (State f (Sreturn (Some x)) k e m)
         E0 (ExprState f x (Kreturn k) e m empty_seqs)
  | step_return_2:  forall f v1 ty k e m v2 m' sq,
      sem_cast v1 ty f.(fn_return) = Some v2 ->
      Mem.free_list m (blocks_of_env e) = Some m' ->
      sstep (ExprState f (Eval v1 ty) (Kreturn k) e m sq)
         E0 (Returnstate v2 (call_cont k) m')
  | step_skip_call: forall f k e m m',
      is_call_cont k ->
      Mem.free_list m (blocks_of_env e) = Some m' ->
      sstep (State f Sskip k e m)
         E0 (Returnstate Vundef k m')

  | step_switch: forall f x sl k e m,
      sstep (State f (Sswitch x sl) k e m)
         E0 (ExprState f x (Kswitch1 sl k) e m empty_seqs)
  | step_expr_switch: forall f n ty sl k e m sq,
      sstep (ExprState f (Eval (Vint n) ty) (Kswitch1 sl k) e m sq)
         E0 (State f (seq_of_labeled_statement (select_switch n sl)) (Kswitch2 k) e m)
  | step_skip_break_switch: forall f x k e m,
      x = Sskip \/ x = Sbreak ->
      sstep (State f x (Kswitch2 k) e m)
         E0 (State f Sskip k e m)
  | step_continue_switch: forall f k e m,
      sstep (State f Scontinue (Kswitch2 k) e m)
         E0 (State f Scontinue k e m)

  | step_label: forall f lbl s k e m,
      sstep (State f (Slabel lbl s) k e m)
         E0 (State f s k e m)

  | step_goto: forall f lbl k e m s' k',
      find_label lbl f.(fn_body) (call_cont k) = Some (s', k') ->
      sstep (State f (Sgoto lbl) k e m)
         E0 (State f s' k' e m)

  | step_internal_function: forall f vargs k m e m1 m2,
      list_norepet (var_names (fn_params f) ++ var_names (fn_vars f)) ->
      alloc_variables empty_env m (f.(fn_params) ++ f.(fn_vars)) e m1 ->
      bind_parameters ge e m1 f.(fn_params) vargs m2 ->
      sstep (Callstate (Internal f) vargs k m)
         E0 (State f f.(fn_body) k e m2)

  | step_external_function: forall ef targs tres cc vargs k m vres t m',
      external_call ef  ge vargs m t vres m' ->
      sstep (Callstate (External ef targs tres cc) vargs k m)
          t (Returnstate vres k m')

  | step_returnstate: forall v f e C ty k m,
      sstep (Returnstate v (Kcall f e C ty k) m)
         E0 (ExprState f (C (Eval v ty)) k e m empty_seqs).

Definition step (S: state) (t: trace) (S': state) : Prop :=
  estep S t S' \/ sstep S t S'.

End SEMANTICS.

(** * Whole-program semantics *)

(** Execution of whole programs are described as sequences of transitions
  from an initial state to a final state.  An initial state is a [Callstate]
  corresponding to the invocation of the ``main'' function of the program
  without arguments and with an empty continuation. *)

Inductive initial_state (p: program): state -> Prop :=
  | initial_state_intro: forall b f m0,
      let ge := Genv.globalenv p in
      Genv.init_mem p = Some m0 ->
      Genv.find_symbol ge p.(prog_main) = Some b ->
      Genv.find_funct_ptr ge b = Some f ->
      type_of_fundef f = Tfunction Tnil type_int32s cc_default ->
      initial_state p (Callstate f nil Kstop m0).

(** A final state is a [Returnstate] with an empty continuation. *)

Inductive final_state: state -> int -> Prop :=
  | final_state_intro: forall r m,
      final_state (Returnstate (Vint r) Kstop m) r.

(** Wrapping up these definitions in a small-step semantics. *)

Definition semantics (p: program) :=
  Semantics step (initial_state p) final_state (Genv.globalenv p).

(** This semantics has the single-event property. *)

Lemma semantics_single_events: 
  forall p, single_events (semantics p).
Proof.
  intros; red; intros. destruct H. 
  set (ge := globalenv (semantics p)) in *.
  assert (DEREF: forall chunk m sq b ofs t v,
    deref_loc ge chunk m sq b ofs t v -> (length t <= 1)%nat).
    intros. inv H0; simpl; try omega. inv H3; simpl; try omega.
  assert (ASSIGN: forall chunk m sq b ofs t v m' sq',
    assign_loc ge chunk m sq b ofs v t m' sq' -> (length t <= 1)%nat).
    intros. inv H0; simpl; try omega. inv H3; simpl; try omega.
  inv H; simpl; try omega. inv H0; eauto; simpl; try omega.
  eapply external_call_trace_length; eauto.
  inv H; simpl; try omega. eapply external_call_trace_length; eauto.
Qed.
