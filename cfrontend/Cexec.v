(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*          Xavier Leroy, INRIA Paris-Rocquencourt                     *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique.  All rights reserved.  This file is distributed       *)
(*  under the terms of the INRIA Non-Commercial License Agreement.     *)
(*                                                                     *)
(* *********************************************************************)

(** Animating the CompCert C semantics *)

Require Import Axioms.
Require Import Classical.
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
Require Import Determinism.
Require Import Ctypes.
Require Import Cop.
Require Import Csyntax.
Require Import Csem.
Require Cstrategy.

(** Error monad with options or lists *)

Notation "'do' X <- A ; B" := (match A with Some X => B | None => None end)
  (at level 200, X ident, A at level 100, B at level 200)
  : option_monad_scope.

Notation "'do' X , Y <- A ; B" := (match A with Some (X, Y) => B | None => None end)
  (at level 200, X ident, Y ident, A at level 100, B at level 200)
  : option_monad_scope.

Notation "'do' X , Y , Z <- A ; B" := (match A with Some (X, Y, Z) => B | None => None end)
  (at level 200, X ident, Y ident, Z ident, A at level 100, B at level 200)
  : option_monad_scope.
Notation "'do' X , Y , Z , U <- A ; B" := (match A with Some (X, Y, Z, U) => B | None => None end)
  (at level 200, X ident, Y ident, Z ident, U ident, A at level 100, B at level 200)
  : option_monad_scope.

Notation " 'check' A ; B" := (if A then B else None)
  (at level 200, A at level 100, B at level 200)
  : option_monad_scope.

Notation "'do' X <- A ; B" := (match A with Some X => B | None => nil end)
  (at level 200, X ident, A at level 100, B at level 200)
  : list_monad_scope.

Notation " 'check' A ; B" := (if A then B else nil)
  (at level 200, A at level 100, B at level 200)
  : list_monad_scope.

Definition is_val (a: expr) : option (val * type) :=
  match a with
  | Eval v ty => Some(v, ty)
  | _ => None
  end.

Lemma is_val_inv:
  forall a v ty, is_val a = Some(v, ty) -> a = Eval v ty.
Proof.
  intros until ty. destruct a; simpl; congruence.
Qed.

Definition is_loc (a: expr) : option (block * int * type) :=
  match a with
  | Eloc b ofs ty => Some(b, ofs, ty)
  | _ => None
  end.

Lemma is_loc_inv:
  forall a b ofs ty, is_loc a = Some(b, ofs, ty) -> a = Eloc b ofs ty.
Proof.
  intros until ty. destruct a; simpl; congruence.
Qed.

Local Open Scope option_monad_scope. 

Fixpoint is_val_list (al: exprlist) : option (list (val * type)) :=
  match al with
  | Enil => Some nil
  | Econs a1 al => do vt1 <- is_val a1; do vtl <- is_val_list al; Some(vt1::vtl)
  end.

Definition is_skip (s: statement) : {s = Sskip} + {s <> Sskip}.
Proof.
  destruct s; (left; congruence) || (right; congruence).
Defined.

(** * Events, volatile memory accesses, and external functions. *)

Section EXEC.

Variable ge: genv.

Definition eventval_of_val (v: val) (t: typ) : option eventval :=
  match v, t with
  | Vint i, AST.Tint => Some (EVint i)
  | Vfloat f, AST.Tfloat => Some (EVfloat f)
  | Vfloat f, AST.Tsingle => if Float.is_single_dec f then Some (EVfloatsingle f) else None
  | Vlong n, AST.Tlong => Some (EVlong n)
  | Vptr b ofs, AST.Tint => do id <- Genv.invert_symbol ge b; Some (EVptr_global id ofs)
  | _, _ => None
  end.

Fixpoint list_eventval_of_val (vl: list val) (tl: list typ) : option (list eventval) :=
  match vl, tl with
  | nil, nil => Some nil
  | v1::vl, t1::tl =>
      do ev1 <- eventval_of_val v1 t1;
      do evl <- list_eventval_of_val vl tl;
      Some (ev1 :: evl)
  | _, _ => None
  end.

Definition val_of_eventval (ev: eventval) (t: typ) : option val :=
  match ev, t with
  | EVint i, AST.Tint => Some (Vint i)
  | EVfloat f, AST.Tfloat => Some (Vfloat f)
  | EVfloatsingle f, AST.Tsingle => if Float.is_single_dec f then Some (Vfloat f) else None
  | EVlong n, AST.Tlong => Some (Vlong n)
  | EVptr_global id ofs, AST.Tint => do b <- Genv.find_symbol ge id; Some (Vptr b ofs)
  | _, _ => None
  end.

Lemma eventval_of_val_sound:
  forall v t ev, eventval_of_val v t = Some ev -> eventval_match ge ev t v.
Proof.
  intros. destruct v; destruct t; simpl in H; inv H.
  constructor.
  constructor.
  constructor.
  destruct (Float.is_single_dec f); inv H1. constructor; auto.
  destruct (Genv.invert_symbol ge b) as [id|] eqn:?; inv H1. 
  constructor. apply Genv.invert_find_symbol; auto.
Qed.

Lemma eventval_of_val_complete:
  forall ev t v, eventval_match ge ev t v -> eventval_of_val v t = Some ev.
Proof.
  induction 1; simpl; auto.
  rewrite pred_dec_true; auto.
  rewrite (Genv.find_invert_symbol _ _ H). auto. 
Qed.

Lemma list_eventval_of_val_sound:
  forall vl tl evl, list_eventval_of_val vl tl = Some evl -> eventval_list_match ge evl tl vl.
Proof with try discriminate.
  induction vl; destruct tl; simpl; intros; inv H.
  constructor.
  destruct (eventval_of_val a t) as [ev1|] eqn:?...
  destruct (list_eventval_of_val vl tl) as [evl'|] eqn:?...
  inv H1. constructor. apply eventval_of_val_sound; auto. eauto.
Qed.

Lemma list_eventval_of_val_complete:
  forall evl tl vl, eventval_list_match ge evl tl vl -> list_eventval_of_val vl tl = Some evl.
Proof.
  induction 1; simpl. auto. 
  rewrite (eventval_of_val_complete _ _ _ H). rewrite IHeventval_list_match. auto.
Qed.

Lemma val_of_eventval_sound:
  forall ev t v, val_of_eventval ev t = Some v -> eventval_match ge ev t v.
Proof.
  intros. destruct ev; destruct t; simpl in H; inv H.
  constructor.
  constructor.
  constructor.
  destruct (Float.is_single_dec f); inv H1. constructor; auto.
  destruct (Genv.find_symbol ge i) as [b|] eqn:?; inv H1.
  constructor. auto.
Qed.

Lemma val_of_eventval_complete:
  forall ev t v, eventval_match ge ev t v -> val_of_eventval ev t = Some v.
Proof.
  induction 1; simpl; auto. rewrite pred_dec_true; auto. rewrite H; auto.
Qed.

(** Volatile memory accesses. *)

Definition do_volatile_load (w: world) (chunk: memory_chunk) (m: mem) (b: block) (ofs: int) 
                             : option (world * trace * val) :=
  if block_is_volatile ge b then
    do id <- Genv.invert_symbol ge b;
    match nextworld_vload w chunk id ofs with
    | None => None
    | Some(res, w') =>
        do vres <- val_of_eventval res (type_of_chunk chunk);
        Some(w', Event_vload chunk id ofs res :: nil, Val.load_result chunk vres)
    end
  else
    do v <- Mem.load chunk m b (Int.unsigned ofs);
    Some(w, E0, v).

Definition do_volatile_store (w: world) (chunk: memory_chunk) (m: mem) (b: block) (ofs: int) (v: val)
                             : option (world * trace * mem) :=
  if block_is_volatile ge b then
    do id <- Genv.invert_symbol ge b;
    do ev <- eventval_of_val (Val.load_result chunk v) (type_of_chunk chunk);
    do w' <- nextworld_vstore w chunk id ofs ev;
    Some(w', Event_vstore chunk id ofs ev :: nil, m)
  else
    do m' <- Mem.store chunk m b (Int.unsigned ofs) v;
    Some(w, E0, m').

Ltac mydestr :=
  match goal with
  | [ |- None = Some _ -> _ ] => intro X; discriminate
  | [ |- Some _ = Some _ -> _ ] => intro X; inv X
  | [ |- match ?x with Some _ => _ | None => _ end = Some _ -> _ ] => destruct x eqn:?; mydestr
  | [ |- match ?x with true => _ | false => _ end = Some _ -> _ ] => destruct x eqn:?; mydestr
  | [ |- match ?x with left _ => _ | right _ => _ end = Some _ -> _ ] => destruct x; mydestr
  | _ => idtac
  end.

Lemma do_volatile_load_sound:
  forall w chunk m b ofs w' t v,
  do_volatile_load w chunk m b ofs = Some(w', t, v) ->
  volatile_load ge chunk m b ofs t v /\ possible_trace w t w'.
Proof.
  intros until v. unfold do_volatile_load. mydestr. 
  destruct p as [ev w'']. mydestr. 
  split. constructor; auto. apply Genv.invert_find_symbol; auto. 
  apply val_of_eventval_sound; auto. 
  econstructor. constructor; eauto. constructor. 
  split. constructor; auto. constructor.
Qed.

Lemma do_volatile_load_complete:
  forall w chunk m b ofs w' t v,
  volatile_load ge chunk m b ofs t v -> possible_trace w t w' ->
  do_volatile_load w chunk m b ofs = Some(w', t, v).
Proof.
  unfold do_volatile_load; intros. inv H. 
  rewrite H1. rewrite (Genv.find_invert_symbol _ _ H2). inv H0. inv H8. inv H6. rewrite H9.
  rewrite (val_of_eventval_complete _ _ _ H3). auto.
  rewrite H1. rewrite H2. inv H0. auto.
Qed.

Lemma do_volatile_store_sound:
  forall w chunk m b ofs v w' t m',
  do_volatile_store w chunk m b ofs v = Some(w', t, m') ->
  volatile_store ge chunk m b ofs v t m' /\ possible_trace w t w'.
Proof.
  intros until m'. unfold do_volatile_store. mydestr. 
  split. constructor; auto. apply Genv.invert_find_symbol; auto. 
  apply eventval_of_val_sound; auto. 
  econstructor. constructor; eauto. constructor. 
  split. constructor; auto. constructor.
Qed.

Lemma do_volatile_store_complete:
  forall w chunk m b ofs v w' t m',
  volatile_store ge chunk m b ofs v t m' -> possible_trace w t w' ->
  do_volatile_store w chunk m b ofs v = Some(w', t, m').
Proof.
  unfold do_volatile_store; intros. inv H. 
  rewrite H1. rewrite (Genv.find_invert_symbol _ _ H2).
  rewrite (eventval_of_val_complete _ _ _ H3).
  inv H0. inv H8. inv H6. rewrite H9. auto.
  rewrite H1. rewrite H2. inv H0. auto.
Qed.

(** Accessing locations *)

Definition do_deref_loc (w: world) (ty: type) (m: mem) (sq: seqs) (b: block) (ofs: int) : option (world * trace * val) :=
  match access_mode ty with
  | By_value chunk =>
      match type_is_volatile ty with
      | false =>
         check (is_not_seq_dec sq b (Int.unsigned ofs) (size_chunk chunk));
         do v <- Mem.loadv chunk m (Vptr b ofs); Some(w, E0, v)
      | true =>
         check (is_not_seq_dec sq b (Int.unsigned ofs) (size_chunk chunk));
         do_volatile_load w chunk m b ofs
      end
  | By_reference => Some(w, E0, Vptr b ofs)
  | By_copy => Some(w, E0, Vptr b ofs)
  | _ => None
  end.

Definition assign_copy_ok (ty: type) (b: block) (ofs: int) (b': block) (ofs': int) : Prop :=
  (alignof_blockcopy ty | Int.unsigned ofs') /\ (alignof_blockcopy ty | Int.unsigned ofs) /\
  (b' <> b \/ Int.unsigned ofs' = Int.unsigned ofs
           \/ Int.unsigned ofs' + sizeof ty <= Int.unsigned ofs
           \/ Int.unsigned ofs + sizeof ty <= Int.unsigned ofs').

Remark check_assign_copy:
  forall (ty: type) (b: block) (ofs: int) (b': block) (ofs': int),
  { assign_copy_ok ty b ofs b' ofs' } + {~ assign_copy_ok ty b ofs b' ofs' }.
Proof with try (right; intuition omega).
  intros. unfold assign_copy_ok. 
  assert (alignof_blockcopy ty > 0) by apply alignof_blockcopy_pos.
  destruct (Zdivide_dec (alignof_blockcopy ty) (Int.unsigned ofs')); auto...
  destruct (Zdivide_dec (alignof_blockcopy ty) (Int.unsigned ofs)); auto...
  assert (Y: {b' <> b \/
              Int.unsigned ofs' = Int.unsigned ofs \/
              Int.unsigned ofs' + sizeof ty <= Int.unsigned ofs \/
              Int.unsigned ofs + sizeof ty <= Int.unsigned ofs'} +
           {~(b' <> b \/
              Int.unsigned ofs' = Int.unsigned ofs \/
              Int.unsigned ofs' + sizeof ty <= Int.unsigned ofs \/
              Int.unsigned ofs + sizeof ty <= Int.unsigned ofs')}).
  destruct (eq_block b' b); auto.
  destruct (zeq (Int.unsigned ofs') (Int.unsigned ofs)); auto.
  destruct (zle (Int.unsigned ofs' + sizeof ty) (Int.unsigned ofs)); auto.
  destruct (zle (Int.unsigned ofs + sizeof ty) (Int.unsigned ofs')); auto.
  right; intuition omega.
  destruct Y... left; intuition omega. 
Defined.

Definition do_assign_loc (w: world) (ty: type) (m: mem) (sq: seqs)
    (b: block) (ofs: int) (v: val): option (world * trace * mem * seqs) :=
  match access_mode ty with
  | By_value chunk =>
      match type_is_volatile ty with
      | false =>
         check (is_not_seq_dec sq b (Int.unsigned ofs) (size_chunk chunk));
         do m' <- Mem.storev chunk m (Vptr b ofs) v;
         Some(w, E0, m', add_seq sq b (Int.unsigned ofs) (size_chunk chunk))
      | true =>
         check (is_not_seq_dec sq b (Int.unsigned ofs) (size_chunk chunk));
         do wtm <- do_volatile_store w chunk m b ofs v;
         Some (wtm, add_seq sq b (Int.unsigned ofs) (size_chunk chunk))
      end
  | By_copy =>
      match v with
      | Vptr b' ofs' =>
          if check_assign_copy ty b ofs b' ofs' then
            do bytes <- Mem.loadbytes m b' (Int.unsigned ofs') (sizeof ty);
            check (is_not_seq_dec sq b (Int.unsigned ofs) (list_length_z bytes));
            do m' <- Mem.storebytes m b (Int.unsigned ofs) bytes;
            Some(w, E0, m', add_seq sq b (Int.unsigned ofs) (list_length_z bytes))
          else None
      | _ => None
      end
  | _ => None
  end.

Lemma do_deref_loc_sound:
  forall w ty m sq b ofs w' t v,
  do_deref_loc w ty m sq b ofs = Some(w', t, v) ->
  deref_loc ge ty m sq b ofs t v /\ possible_trace w t w'.
Proof.
  unfold do_deref_loc; intros until v.
  destruct (access_mode ty) eqn:?; mydestr. 
  intros. exploit do_volatile_load_sound; eauto. intuition. eapply deref_loc_volatile; eauto. 
  split. eapply deref_loc_value; eauto. constructor.
  split. eapply deref_loc_reference; eauto. constructor.
  split. eapply deref_loc_copy; eauto. constructor.
Qed.

Lemma do_deref_loc_complete:
  forall w ty m sq b ofs w' t v,
  deref_loc ge ty m sq b ofs t v -> possible_trace w t w' ->
  do_deref_loc w ty m sq b ofs = Some(w', t, v).
Proof.
  unfold do_deref_loc; intros. inv H.
  inv H0. rewrite H1; rewrite H2; rewrite H3; auto.
  now destruct (is_not_seq_dec _ _ _ _).
  rewrite H1; rewrite H2. destruct (is_not_seq_dec _ _ _ _); try contradiction.
  apply do_volatile_load_complete; auto.
  inv H0. rewrite H1. auto.
  inv H0. rewrite H1. auto.
Qed.

Lemma do_assign_loc_sound:
  forall w ty m sq b ofs v w' t m' sq',
  do_assign_loc w ty m sq b ofs v = Some(w', t, m', sq') ->
  assign_loc ge ty m sq b ofs v t m' sq' /\ possible_trace w t w'.
Proof.
  unfold do_assign_loc; intros until sq'.
  destruct (access_mode ty) eqn:?; mydestr. 
  intros. exploit do_volatile_store_sound; eauto. intuition. eapply assign_loc_volatile; eauto. 
  split. eapply assign_loc_value; eauto. constructor.
  destruct v; mydestr. destruct a as [P [Q R]]. 
  split. eapply assign_loc_copy; eauto. constructor.
Qed.

Lemma do_assign_loc_complete:
  forall w ty m sq b ofs v w' t m' sq',
  assign_loc ge ty m sq b ofs v t m' sq' -> possible_trace w t w' ->
  do_assign_loc w ty m sq b ofs v = Some(w', t, m', sq').
Proof.
  unfold do_assign_loc; intros. inv H.
  inv H0. rewrite H1; rewrite H2; rewrite H3; auto.
  now destruct (is_not_seq_dec _ _ _ _).
  rewrite H1; rewrite H2. destruct (is_not_seq_dec _ _ _ _); try contradiction.
  erewrite do_volatile_store_complete; auto.
  rewrite H1. destruct (check_assign_copy ty b ofs b' ofs').
  inv H0. rewrite H5; rewrite H6; auto. now destruct (is_not_seq_dec _ _ _ _).
  elim n. red; tauto. 
Qed.

(** External calls *)

Variable do_external_function:
  ident -> signature -> genv -> world -> list val -> mem -> option (world * trace * val * mem).

Hypothesis do_external_function_sound:
  forall id sg ge vargs m t vres m' w w',
  do_external_function id sg ge w vargs m = Some(w', t, vres, m') ->
  external_functions_sem id sg ge vargs m t vres m' /\ possible_trace w t w'.

Hypothesis do_external_function_complete:
  forall id sg ge vargs m t vres m' w w',
  external_functions_sem id sg ge vargs m t vres m' ->
  possible_trace w t w' ->
  do_external_function id sg ge w vargs m = Some(w', t, vres, m').

Variable do_inline_assembly:
  ident -> genv -> world -> list val -> mem -> option (world * trace * val * mem).

Hypothesis do_inline_assembly_sound:
  forall txt ge vargs m t vres m' w w',
  do_inline_assembly txt ge w vargs m = Some(w', t, vres, m') ->
  inline_assembly_sem txt ge vargs m t vres m' /\ possible_trace w t w'.

Hypothesis do_inline_assembly_complete:
  forall txt ge vargs m t vres m' w w',
  inline_assembly_sem txt ge vargs m t vres m' ->
  possible_trace w t w' ->
  do_inline_assembly txt ge w vargs m = Some(w', t, vres, m').

Definition do_ef_volatile_load (chunk: memory_chunk)
       (w: world) (vargs: list val) (m: mem) : option (world * trace * val * mem) :=
  match vargs with
  | Vptr b ofs :: nil => do w',t,v <- do_volatile_load w chunk m b ofs; Some(w',t,v,m)
  | _ => None
  end.

Definition do_ef_volatile_store (chunk: memory_chunk)
       (w: world) (vargs: list val) (m: mem) : option (world * trace * val * mem) :=
  match vargs with
  | Vptr b ofs :: v :: nil => do w',t,m' <- do_volatile_store w chunk m b ofs v; Some(w',t,Vundef,m')
  | _ => None
  end.

Definition do_ef_volatile_load_global (chunk: memory_chunk) (id: ident) (ofs: int)
       (w: world) (vargs: list val) (m: mem) : option (world * trace * val * mem) :=
  do b <- Genv.find_symbol ge id; do_ef_volatile_load chunk w (Vptr b ofs :: vargs) m.

Definition do_ef_volatile_store_global (chunk: memory_chunk) (id: ident) (ofs: int)
       (w: world) (vargs: list val) (m: mem) : option (world * trace * val * mem) :=
  do b <- Genv.find_symbol ge id; do_ef_volatile_store chunk w (Vptr b ofs :: vargs) m.

Definition do_ef_malloc
       (w: world) (vargs: list val) (m: mem) : option (world * trace * val * mem) :=
  match vargs with
  | Vint n :: nil =>
      let (m', b) := Mem.alloc m (-4) (Int.unsigned n) in
      do m'' <- Mem.store Mint32 m' b (-4) (Vint n);
      Some(w, E0, Vptr b Int.zero, m'')
  | _ => None
  end.

Definition do_ef_free
       (w: world) (vargs: list val) (m: mem) : option (world * trace * val * mem) :=
  match vargs with
  | Vptr b lo :: nil =>
      do vsz <- Mem.load Mint32 m b (Int.unsigned lo - 4);
      match vsz with
      | Vint sz =>
          check (zlt 0 (Int.unsigned sz));
          do m' <- Mem.free m b (Int.unsigned lo - 4) (Int.unsigned lo + Int.unsigned sz);
          Some(w, E0, Vundef, m')
      | _ => None
      end
  | _ => None
  end.

Definition memcpy_args_ok
  (sz al: Z) (bdst: block) (odst: Z) (bsrc: block) (osrc: Z) : Prop :=
      (al = 1 \/ al = 2 \/ al = 4 \/ al = 8)
   /\ sz >= 0 /\ (al | sz)
   /\ (sz > 0 -> (al | osrc))
   /\ (sz > 0 -> (al | odst))
   /\ (bsrc <> bdst \/ osrc = odst \/ osrc + sz <= odst \/ odst + sz <= osrc).

Remark memcpy_check_args:
  forall sz al bdst odst bsrc osrc,
  {memcpy_args_ok sz al bdst odst bsrc osrc} + {~memcpy_args_ok sz al bdst odst bsrc osrc}.
Proof with try (right; intuition omega).
  intros. 
  assert (X: {al = 1 \/ al = 2 \/ al = 4 \/ al = 8} + {~(al = 1 \/ al = 2 \/ al = 4 \/ al = 8)}).
    destruct (zeq al 1); auto. destruct (zeq al 2); auto.
    destruct (zeq al 4); auto. destruct (zeq al 8); auto...
  unfold memcpy_args_ok. destruct X...
  assert (al > 0) by (intuition omega).
  destruct (zle 0 sz)...
  destruct (Zdivide_dec al sz); auto...
  assert(U: forall x, {sz > 0 -> (al | x)} + {~(sz > 0 -> (al | x))}).
    intros. destruct (zeq sz 0). 
    left; intros; omegaContradiction.
    destruct (Zdivide_dec al x); auto. right; red; intros. elim n0. apply H0. omega. 
  destruct (U osrc); auto...
  destruct (U odst); auto...
  assert (Y: {bsrc <> bdst \/ osrc = odst \/ osrc + sz <= odst \/ odst + sz <= osrc}
           +{~(bsrc <> bdst \/ osrc = odst \/ osrc + sz <= odst \/ odst + sz <= osrc)}).
    destruct (eq_block bsrc bdst); auto.
    destruct (zeq osrc odst); auto.
    destruct (zle (osrc + sz) odst); auto.
    destruct (zle (odst + sz) osrc); auto.
    right; intuition omega.
  destruct Y... left; intuition omega.
Defined.

Definition do_ef_memcpy (sz al: Z)
       (w: world) (vargs: list val) (m: mem) : option (world * trace * val * mem) :=
  match vargs with
  | Vptr bdst odst :: Vptr bsrc osrc :: nil =>
      if memcpy_check_args sz al bdst (Int.unsigned odst) bsrc (Int.unsigned osrc) then
        do bytes <- Mem.loadbytes m bsrc (Int.unsigned osrc) sz;
        do m' <- Mem.storebytes m bdst (Int.unsigned odst) bytes;
        Some(w, E0, Vundef, m')
      else None
  | _ => None
  end.

Definition do_ef_annot (text: ident) (targs: list annot_arg)
       (w: world) (vargs: list val) (m: mem) : option (world * trace * val * mem) :=
  do args <- list_eventval_of_val vargs (annot_args_typ targs);
  Some(w, Event_annot text (annot_eventvals targs args) :: E0, Vundef, m).

Definition do_ef_annot_val (text: ident) (targ: typ)
       (w: world) (vargs: list val) (m: mem) : option (world * trace * val * mem) :=
  match vargs with
  | varg :: nil =>
      do arg <- eventval_of_val varg targ;
      Some(w, Event_annot text (arg :: nil) :: E0, varg, m)
  | _ => None
  end.

Definition do_external (ef: external_function):
       world -> list val -> mem -> option (world * trace * val * mem) :=
  match ef with
  | EF_external name sg => do_external_function name sg ge
  | EF_builtin name sg => do_external_function name sg ge
  | EF_vload chunk => do_ef_volatile_load chunk
  | EF_vstore chunk => do_ef_volatile_store chunk
  | EF_vload_global chunk id ofs => do_ef_volatile_load_global chunk id ofs
  | EF_vstore_global chunk id ofs => do_ef_volatile_store_global chunk id ofs
  | EF_malloc => do_ef_malloc
  | EF_free => do_ef_free
  | EF_memcpy sz al => do_ef_memcpy sz al
  | EF_annot text targs => do_ef_annot text targs
  | EF_annot_val text targ => do_ef_annot_val text targ
  | EF_inline_asm text => do_inline_assembly text ge
  end.

Lemma do_ef_external_sound:
  forall ef w vargs m w' t vres m',
  do_external ef w vargs m = Some(w', t, vres, m') ->
  external_call ef ge vargs m t vres m' /\ possible_trace w t w'.
Proof with try congruence.
  intros until m'.

  assert (VLOAD: forall chunk vargs,
    do_ef_volatile_load chunk w vargs m = Some (w', t, vres, m') ->
    volatile_load_sem chunk ge vargs m t vres m' /\ possible_trace w t w').
  intros chunk vargs'.
  unfold do_ef_volatile_load. destruct vargs'... destruct v... destruct vargs'... 
  mydestr. destruct p as [[w'' t''] v]; mydestr.
  exploit do_volatile_load_sound; eauto. intuition. econstructor; eauto. 

  assert (VSTORE: forall chunk vargs,
    do_ef_volatile_store chunk w vargs m = Some (w', t, vres, m') ->
    volatile_store_sem chunk ge vargs m t vres m' /\ possible_trace w t w').
  intros chunk vargs'.
  unfold do_ef_volatile_store. destruct vargs'... destruct v... destruct vargs'... destruct vargs'... 
  mydestr. destruct p as [[w'' t''] m'']. mydestr. 
  exploit do_volatile_store_sound; eauto. intuition. econstructor; eauto.

  destruct ef; simpl.
(* EF_external *)
  eapply do_external_function_sound; eauto. 
(* EF_builtin *)
  eapply do_external_function_sound; eauto. 
(* EF_vload *)
  auto.
(* EF_vstore *)
  auto.
(* EF_vload_global *)
  rewrite volatile_load_global_charact.
  unfold do_ef_volatile_load_global. destruct (Genv.find_symbol ge)...
  intros. exploit VLOAD; eauto. intros [A B]. split; auto. exists b; auto.
(* EF_vstore_global *)
  rewrite volatile_store_global_charact.
  unfold do_ef_volatile_store_global. destruct (Genv.find_symbol ge)...
  intros. exploit VSTORE; eauto. intros [A B]. split; auto. exists b; auto.
(* EF_malloc *)
  unfold do_ef_malloc. destruct vargs... destruct v... destruct vargs...
  destruct (Mem.alloc m (-4) (Int.unsigned i)) as [m1 b] eqn:?. mydestr.
  split. econstructor; eauto. constructor.
(* EF_free *)
  unfold do_ef_free. destruct vargs... destruct v... destruct vargs... 
  mydestr. destruct v... mydestr. 
  split. econstructor; eauto. omega. constructor.
(* EF_memcpy *)
  unfold do_ef_memcpy. destruct vargs... destruct v... destruct vargs... 
  destruct v... destruct vargs... mydestr. red in m0. 
  split. econstructor; eauto; tauto. constructor.
(* EF_annot *)
  unfold do_ef_annot. mydestr. 
  split. constructor. apply list_eventval_of_val_sound; auto.
  econstructor. constructor; eauto. constructor.
(* EF_annot_val *)
  unfold do_ef_annot_val. destruct vargs... destruct vargs... mydestr. 
  split. constructor. apply eventval_of_val_sound; auto.
  econstructor. constructor; eauto. constructor.
(* EF_inline_asm *)
  eapply do_inline_assembly_sound; eauto.
Qed.

Lemma do_ef_external_complete:
  forall ef w vargs m w' t vres m',
  external_call ef ge vargs m t vres m' -> possible_trace w t w' ->
  do_external ef w vargs m = Some(w', t, vres, m').
Proof.
  intros.
 
  assert (VLOAD: forall chunk vargs,
             volatile_load_sem chunk ge vargs m t vres m' ->
             do_ef_volatile_load chunk w vargs m = Some (w', t, vres, m')).
  intros. inv H1; unfold do_ef_volatile_load.
  exploit do_volatile_load_complete; eauto. intros EQ; rewrite EQ; auto.

  assert (VSTORE: forall chunk vargs,
             volatile_store_sem chunk ge vargs m t vres m' ->
             do_ef_volatile_store chunk w vargs m = Some (w', t, vres, m')).
  intros. inv H1; unfold do_ef_volatile_store.
  exploit do_volatile_store_complete; eauto. intros EQ; rewrite EQ; auto.

  destruct ef; simpl in *.
(* EF_external *)
  eapply do_external_function_complete; eauto.
(* EF_builtin *)
  eapply do_external_function_complete; eauto.
(* EF_vload *)
  auto.
(* EF_vstore *)
  auto.
(* EF_vload_global *)
  rewrite volatile_load_global_charact in H. destruct H as [b [P Q]]. 
  unfold do_ef_volatile_load_global. rewrite P. auto. 
(* EF_vstore *)
  rewrite volatile_store_global_charact in H. destruct H as [b [P Q]]. 
  unfold do_ef_volatile_store_global. rewrite P. auto. 
(* EF_malloc *)
  inv H; unfold do_ef_malloc. 
  inv H0. rewrite H1. rewrite H2. auto.
(* EF_free *)
  inv H; unfold do_ef_free.
  inv H0. rewrite H1. rewrite zlt_true. rewrite H3. auto. omega.
(* EF_memcpy *)
  inv H; unfold do_ef_memcpy.
  inv H0. rewrite pred_dec_true. rewrite H7; rewrite H8; auto.
  red. tauto. 
(* EF_annot *)
  inv H; unfold do_ef_annot. inv H0. inv H6. inv H4. 
  rewrite (list_eventval_of_val_complete _ _ _ H1). auto.
(* EF_annot_val *)
  inv H; unfold do_ef_annot_val. inv H0. inv H6. inv H4. 
  rewrite (eventval_of_val_complete _ _ _ H1). auto.
(* EF_inline_asm *)
  eapply do_inline_assembly_complete; eauto.
Qed.

(** * Reduction of expressions *)

Inductive reduction: Type :=
  | Lred (l': expr) (m': mem) (sq' : seqs)
  | Rred (r': expr) (m': mem) (sq' : seqs) (t: trace)
  | Callred (fd: fundef) (args: list val) (tyres: type) (m': mem)
  | Stuckred.

Section EXPRS.

Variable e: env.
Variable w: world.

Fixpoint sem_cast_arguments (vtl: list (val * type)) (tl: typelist) : option (list val) :=
  match vtl, tl with
  | nil, Tnil => Some nil
  | (v1,t1)::vtl, Tcons t1' tl =>
      do v <- sem_cast v1 t1 t1'; do vl <- sem_cast_arguments vtl tl; Some(v::vl)
  | _, _ => None
  end.

(** The result of stepping an expression is a list [ll] of possible reducts.
  Each element of [ll] is a pair of a context and the result of reducing
  inside this context (see type [reduction] above).
  The list [ll] is empty if the expression is fully reduced
   (it's [Eval] for a r-value and [Eloc] for a l-value).
*)

Definition reducts (A: Type): Type := list ((expr -> A) * reduction).

Definition topred (r: reduction) : reducts expr :=
  ((fun (x: expr) => x), r) :: nil.

Definition stuck : reducts expr :=
  ((fun (x: expr) => x), Stuckred) :: nil.

Definition incontext {A B: Type} (ctx: A -> B) (ll: reducts A) : reducts B :=
  map (fun z => ((fun (x: expr) => ctx(fst z x)), snd z)) ll.

Definition incontext2 {A1 A2 B: Type}
                     (ctx1: A1 -> B) (ll1: reducts A1)
                     (ctx2: A2 -> B) (ll2: reducts A2) : reducts B :=
  incontext ctx1 ll1 ++ incontext ctx2 ll2.

Notation "'do' X <- A ; B" := (match A with Some X => B | None => stuck end)
  (at level 200, X ident, A at level 100, B at level 200)
  : reducts_monad_scope.

Notation "'do' X , Y <- A ; B" := (match A with Some (X, Y) => B | None => stuck end)
  (at level 200, X ident, Y ident, A at level 100, B at level 200)
  : reducts_monad_scope.

Notation "'do' X , Y , Z <- A ; B" := (match A with Some (X, Y, Z) => B | None => stuck end)
  (at level 200, X ident, Y ident, Z ident, A at level 100, B at level 200)
  : reducts_monad_scope.

Notation "'do' X , Y , Z , U <- A ; B" := (match A with Some (X, Y, Z, U) => B | None => stuck end)
  (at level 200, X ident, Y ident, Z ident, U ident, A at level 100, B at level 200)
  : reducts_monad_scope.

Notation " 'check' A ; B" := (if A then B else stuck)
  (at level 200, A at level 100, B at level 200)
  : reducts_monad_scope.

Local Open Scope reducts_monad_scope.

Fixpoint step_expr (k: kind) (a: expr) (m: mem) (sq: seqs) : reducts expr :=
  match k, a with
  | LV, Eloc b ofs ty =>
      nil
  | LV, Evar x ty =>
      match e!x with
      | Some(b, ty') =>
          check type_eq ty ty';
          topred (Lred (Eloc b Int.zero ty) m sq)
      | None =>
          do b <- Genv.find_symbol ge x;
          topred (Lred (Eloc b Int.zero ty) m sq)
      end
  | LV, Ederef r ty =>
      match is_val r with
      | Some(Vptr b ofs, ty') =>
          topred (Lred (Eloc b ofs ty) m sq)
      | Some _ =>
          stuck
      | None =>
          incontext (fun x => Ederef x ty) (step_expr RV r m sq)
      end
  | LV, Efield r f ty =>
      match is_val r with
      | Some(Vptr b ofs, ty') =>
          match ty' with
          | Tstruct id fList _ =>
              match field_offset f fList with
              | Error _ => stuck
              | OK delta => topred (Lred (Eloc b (Int.add ofs (Int.repr delta)) ty) m sq)
              end
          | Tunion id fList _ =>
              topred (Lred (Eloc b ofs ty) m sq)
          | _ => stuck
          end
      | Some _ =>
          stuck
      | None =>
          incontext (fun x => Efield x f ty) (step_expr RV r m sq)
      end
  | RV, Eval v ty =>
      nil
  | RV, Evalof l ty =>
      match is_loc l with
      | Some(b, ofs, ty') =>
          check type_eq ty ty';
          do w',t,v <- do_deref_loc w ty m sq b ofs;
          topred (Rred (Eval v ty) m sq t)
      | None =>
          incontext (fun x => Evalof x ty) (step_expr LV l m sq)
      end
  | RV, Eaddrof l ty =>
      match is_loc l with
      | Some(b, ofs, ty') => topred (Rred (Eval (Vptr b ofs) ty) m sq E0)
      | None => incontext (fun x => Eaddrof x ty) (step_expr LV l m sq)
      end
  | RV, Eunop op r1 ty =>
      match is_val r1 with
      | Some(v1, ty1) =>
          do v <- sem_unary_operation op v1 ty1;
          topred (Rred (Eval v ty) m sq E0)
      | None =>
          incontext (fun x => Eunop op x ty) (step_expr RV r1 m sq)
      end
  | RV, Ebinop op r1 r2 ty =>
      match is_val r1, is_val r2 with
      | Some(v1, ty1), Some(v2, ty2) =>
          do v <- sem_binary_operation op v1 ty1 v2 ty2 m;
          topred (Rred (Eval v ty) m sq E0)
      | _, _ =>
         incontext2 (fun x => Ebinop op x r2 ty) (step_expr RV r1 m sq)
                    (fun x => Ebinop op r1 x ty) (step_expr RV r2 m sq)
      end
  | RV, Ecast r1 ty =>
      match is_val r1 with
      | Some(v1, ty1) =>
          do v <- sem_cast v1 ty1 ty;
          topred (Rred (Eval v ty) m sq E0)
      | None =>
          incontext (fun x => Ecast x ty) (step_expr RV r1 m sq)
      end
  | RV, Eseqand r1 r2 ty =>
      match is_val r1 with
      | Some(v1, ty1) =>
          do b <- bool_val v1 ty1;
          if b then topred (Rred (Eparen (Eparen r2 type_bool) ty) m empty_seqs E0)
               else topred (Rred (Eval (Vint Int.zero) ty) m sq E0)
      | None =>
          incontext (fun x => Eseqand x r2 ty) (step_expr RV r1 m sq)
      end
  | RV, Eseqor r1 r2 ty =>
      match is_val r1 with
      | Some(v1, ty1) =>
          do b <- bool_val v1 ty1;
          if b then topred (Rred (Eval (Vint Int.one) ty) m sq E0)
               else topred (Rred (Eparen (Eparen r2 type_bool) ty) m empty_seqs E0)
      | None =>
          incontext (fun x => Eseqor x r2 ty) (step_expr RV r1 m sq)
      end
  | RV, Econdition r1 r2 r3 ty =>
      match is_val r1 with
      | Some(v1, ty1) =>
          do b <- bool_val v1 ty1;
          topred (Rred (Eparen (if b then r2 else r3) ty) m empty_seqs E0)
      | None =>
          incontext (fun x => Econdition x r2 r3 ty) (step_expr RV r1 m sq)
      end
  | RV, Esizeof ty' ty =>
      topred (Rred (Eval (Vint (Int.repr (sizeof ty'))) ty) m sq E0)
  | RV, Ealignof ty' ty =>
      topred (Rred (Eval (Vint (Int.repr (alignof ty'))) ty) m sq E0)
  | RV, Eassign l1 r2 ty =>
      match is_loc l1, is_val r2 with
      | Some(b, ofs, ty1), Some(v2, ty2) =>
          check type_eq ty1 ty;
          do v <- sem_cast v2 ty2 ty1;
          do w',t,m',sq' <- do_assign_loc w ty1 m sq b ofs v;
          topred (Rred (Eval v ty) m' sq' t)
      | _, _ =>
         incontext2 (fun x => Eassign x r2 ty) (step_expr LV l1 m sq)
                    (fun x => Eassign l1 x ty) (step_expr RV r2 m sq)
      end
  | RV, Eassignop op l1 r2 tyres ty =>
      match is_loc l1, is_val r2 with
      | Some(b, ofs, ty1), Some(v2, ty2) =>
          check type_eq ty1 ty;
          do w',t,v1 <- do_deref_loc w ty1 m sq b ofs;
          let r' := Eassign (Eloc b ofs ty1)
                           (Ebinop op (Eval v1 ty1) (Eval v2 ty2) tyres) ty1 in
          topred (Rred r' m sq t)
      | _, _ =>
         incontext2 (fun x => Eassignop op x r2 tyres ty) (step_expr LV l1 m sq)
                    (fun x => Eassignop op l1 x tyres ty) (step_expr RV r2 m sq)
      end
  | RV, Epostincr id l ty =>
      match is_loc l with
      | Some(b, ofs, ty1) =>
          check type_eq ty1 ty;
          do w',t, v1 <- do_deref_loc w ty m sq b ofs;
          let op := match id with Incr => Oadd | Decr => Osub end in
          let r' :=
            Ecomma false (Eassign (Eloc b ofs ty) 
                           (Ebinop op (Eval v1 ty) (Eval (Vint Int.one) type_int32s) (typeconv ty))
                           ty)
                   (Eval v1 ty) ty in
          topred (Rred r' m sq t)
      | None =>
          incontext (fun x => Epostincr id x ty) (step_expr LV l m sq)
      end
  | RV, Ecomma sp r1 r2 ty =>
      match is_val r1 with
      | Some _ =>
          check type_eq (typeof r2) ty;
          topred (Rred r2 m (if sp then empty_seqs else sq) E0)
      | None =>
          incontext (fun x => Ecomma sp x r2 ty) (step_expr RV r1 m sq)
      end
  | RV, Eparen r1 ty =>
      match is_val r1 with
      | Some (v1, ty1) =>
          do v <- sem_cast v1 ty1 ty;
          topred (Rred (Eval v ty) m sq E0)
      | None =>
          incontext (fun x => Eparen x ty) (step_expr RV r1 m sq)
      end
  | RV, Ecall r1 rargs ty =>
      match is_val r1, is_val_list rargs with
      | Some(vf, tyf), Some vtl =>
          match classify_fun tyf with
          | fun_case_f tyargs tyres cconv =>
              do fd <- Genv.find_funct ge vf;
              do vargs <- sem_cast_arguments vtl tyargs;
              check type_eq (type_of_fundef fd) (Tfunction tyargs tyres cconv);
              topred (Callred fd vargs ty m)
          | _ => stuck
          end
      | _, _ =>
          incontext2 (fun x => Ecall x rargs ty) (step_expr RV r1 m sq)
                     (fun x => Ecall r1 x ty) (step_exprlist rargs m sq)
      end
  | RV, Ebuiltin ef tyargs rargs ty =>
      match is_val_list rargs with
      | Some vtl =>
          do vargs <- sem_cast_arguments vtl tyargs;
          match do_external ef w vargs m with
          | None => stuck
          | Some(w',t,v,m') => topred (Rred (Eval v ty) m' empty_seqs t)
          end
      | _ =>
          incontext (fun x => Ebuiltin ef tyargs x ty) (step_exprlist rargs m sq)
      end
  | _, _ => stuck
  end

with step_exprlist (rl: exprlist) (m: mem) (sq: seqs) : reducts exprlist :=
  match rl with
  | Enil =>
      nil
  | Econs r1 rs =>
      incontext2 (fun x => Econs x rs) (step_expr RV r1 m sq)
                 (fun x => Econs r1 x) (step_exprlist rs m sq)
  end.

(** Technical properties on safe expressions. *)

Inductive imm_safe_t: kind -> expr -> mem -> seqs -> Prop :=
  | imm_safe_t_val: forall v ty m sq,
      imm_safe_t RV (Eval v ty) m sq
  | imm_safe_t_loc: forall b ofs ty m sq,
      imm_safe_t LV (Eloc b ofs ty) m sq
  | imm_safe_t_lred: forall to C l m sq l' m',
      lred ge e l m l' m' ->
      context LV to C ->
      imm_safe_t to (C l) m sq
  | imm_safe_t_rred: forall to C r m sq t r' m' sq' w',
      rred ge r m sq t r' m' sq' -> possible_trace w t w' ->
      context RV to C ->
      imm_safe_t to (C r) m sq
  | imm_safe_t_callred: forall to C r m sq fd args ty,
      callred ge r fd args ty ->
      context RV to C ->
      imm_safe_t to (C r) m sq.

Remark imm_safe_t_imm_safe:
  forall k a m sq, imm_safe_t k a m sq -> imm_safe ge e k a m sq.
Proof.
  induction 1. 
  constructor.
  constructor.
  eapply imm_safe_lred; eauto.
  eapply imm_safe_rred; eauto.
  eapply imm_safe_callred; eauto.
Qed.

(*
Definition not_stuck (a: expr) (m: mem) :=
  forall a' k C, context k RV C -> a = C a' -> imm_safe_t k a' m.

Lemma safe_expr_kind:
  forall k C a m,
  context k RV C ->
  not_stuck (C a) m ->
  k = Cstrategy.expr_kind a.
Proof.
  intros.
  symmetry. eapply Cstrategy.imm_safe_kind. eapply imm_safe_t_imm_safe. eauto.
Qed.
*)

Fixpoint exprlist_all_values (rl: exprlist) : Prop :=
  match rl with
  | Enil => True
  | Econs (Eval v ty) rl' => exprlist_all_values rl'
  | Econs _ _ => False
  end.

Definition invert_expr_prop (a: expr) (m: mem) (sq: seqs) : Prop :=
  match a with
  | Eloc b ofs ty => False
  | Evar x ty =>
      exists b,
      e!x = Some(b, ty)
      \/ (e!x = None /\ Genv.find_symbol ge x = Some b)
  | Ederef (Eval v ty1) ty =>
      exists b, exists ofs, v = Vptr b ofs
  | Efield (Eval v ty1) f ty =>
      exists b, exists ofs, v = Vptr b ofs /\
      match ty1 with
      | Tstruct _ fList _ => exists delta, field_offset f fList = Errors.OK delta
      | Tunion _ _ _ => True
      | _ => False
      end
  | Eval v ty => False
  | Evalof (Eloc b ofs ty') ty =>
      ty' = ty /\ exists t, exists v, exists w', deref_loc ge ty m sq b ofs t v /\ possible_trace w t w'
  | Eunop op (Eval v1 ty1) ty =>
      exists v, sem_unary_operation op v1 ty1 = Some v
  | Ebinop op (Eval v1 ty1) (Eval v2 ty2) ty =>
      exists v, sem_binary_operation op v1 ty1 v2 ty2 m = Some v
  | Ecast (Eval v1 ty1) ty =>
      exists v, sem_cast v1 ty1 ty = Some v
  | Eseqand (Eval v1 ty1) r2 ty =>
      exists b, bool_val v1 ty1 = Some b
  | Eseqor (Eval v1 ty1) r2 ty =>
      exists b, bool_val v1 ty1 = Some b
  | Econdition (Eval v1 ty1) r1 r2 ty =>
      exists b, bool_val v1 ty1 = Some b
  | Eassign (Eloc b ofs ty1) (Eval v2 ty2) ty =>
      exists v, exists m', exists t, exists w', exists sq',
      ty = ty1 /\ sem_cast v2 ty2 ty1 = Some v /\ assign_loc ge ty1 m sq b ofs v t m' sq' /\ possible_trace w t w'
  | Eassignop op (Eloc b ofs ty1) (Eval v2 ty2) tyres ty =>
      exists t, exists v1, exists w',
      ty = ty1 /\ deref_loc ge ty1 m sq b ofs t v1 /\ possible_trace w t w'
  | Epostincr id (Eloc b ofs ty1) ty =>
      exists t, exists v1, exists w', 
      ty = ty1 /\ deref_loc ge ty m sq b ofs t v1 /\ possible_trace w t w'
  | Ecomma _ (Eval v ty1) r2 ty =>
      typeof r2 = ty
  | Eparen (Eval v1 ty1) ty =>
      exists v, sem_cast v1 ty1 ty = Some v
  | Ecall (Eval vf tyf) rargs ty =>
      exprlist_all_values rargs ->
      exists tyargs tyres cconv fd vl,
         classify_fun tyf = fun_case_f tyargs tyres cconv
      /\ Genv.find_funct ge vf = Some fd
      /\ cast_arguments rargs tyargs vl
      /\ type_of_fundef fd = Tfunction tyargs tyres cconv
  | Ebuiltin ef tyargs rargs ty =>
      exprlist_all_values rargs ->
      exists vargs t vres m' w',
         cast_arguments rargs tyargs vargs
      /\ external_call ef ge vargs m t vres m'
      /\ possible_trace w t w'
  | _ => True
  end.

Lemma lred_invert:
  forall l m sq l' m', lred ge e l m l' m' -> invert_expr_prop l m sq.
Proof.
  induction 1; red; auto.
  exists b; auto.
  exists b; auto.
  exists b; exists ofs; auto.
  exists b; exists ofs; split; auto. exists delta; auto.
  exists b; exists ofs; auto.
Qed.

Lemma rred_invert:
  forall w' r m sq t r' m' sq',
  rred ge r m sq t r' m' sq' -> possible_trace w t w' -> invert_expr_prop r m sq.
Proof.
  induction 1; intros; red; auto.
  split; auto; exists t; exists v; exists w'; auto.
  exists v; auto.
  exists v; auto.
  exists v; auto.
  exists true; auto. exists false; auto.
  exists true; auto. exists false; auto.
  exists b; auto.
  exists v; exists m'; exists t; exists w'; exists sq'; auto.
  exists t; exists v1; exists w'; auto.
  exists t; exists v1; exists w'; auto.
  exists v; auto.
  intros; exists vargs; exists t; exists vres; exists m'; exists w'; auto.
Qed.

Lemma callred_invert:
  forall r fd args ty m sq,
  callred ge r fd args ty ->
  invert_expr_prop r m sq.
Proof.
  intros. inv H. simpl.
  intros. exists tyargs, tyres, cconv, fd, args; auto.
Qed.

Scheme context_ind2 := Minimality for context Sort Prop
  with contextlist_ind2 := Minimality for contextlist Sort Prop.
Combined Scheme context_contextlist_ind from context_ind2, contextlist_ind2.

Lemma invert_expr_context:
  (forall from to C, context from to C ->
   forall a m sq,
   invert_expr_prop a m sq ->
   invert_expr_prop (C a) m sq)
/\(forall from C, contextlist from C ->
  forall a m sq,
  invert_expr_prop a m sq ->
  ~exprlist_all_values (C a)).
Proof.
  apply context_contextlist_ind; intros; try (exploit H0; [eauto|intros]); simpl.
  auto.
  destruct (C a); auto; contradiction.
  destruct (C a); auto; contradiction.
  destruct (C a); auto; contradiction.
  auto.
  destruct (C a); auto; contradiction.
  destruct (C a); auto; contradiction.
  destruct e1; auto; destruct (C a); auto; contradiction.
  destruct (C a); auto; contradiction.
  destruct (C a); auto; contradiction.
  destruct (C a); auto; contradiction.
  destruct (C a); auto; contradiction.
  destruct (C a); auto; contradiction.
  destruct e1; auto; destruct (C a); auto; contradiction.
  destruct (C a); auto; contradiction.
  destruct e1; auto; destruct (C a); auto; contradiction.
  destruct (C a); auto; contradiction.
  destruct (C a); auto; contradiction.
  destruct e1; auto. intros. elim (H0 a m sq); auto.
  intros. elim (H0 a m sq); auto.
  destruct (C a); auto; contradiction.
  destruct (C a); auto; contradiction.
  red; intros. destruct (C a); auto. 
  red; intros. destruct e1; auto. elim (H0 a m sq); auto. 
Qed.

Lemma imm_safe_t_inv:
  forall k a m sq,
  imm_safe_t k a m sq ->
  match a with
  | Eloc _ _ _ => True
  | Eval _ _ => True
  | _ => invert_expr_prop a m sq
  end.
Proof.
  destruct invert_expr_context as [A B].
  intros. inv H. 
  auto.
  auto.
  assert (invert_expr_prop (C l) m sq).
    eapply A; eauto. eapply lred_invert; eauto.
  red in H. destruct (C l); auto; contradiction.
  assert (invert_expr_prop (C r) m sq).
    eapply A; eauto. eapply rred_invert; eauto.
  red in H. destruct (C r); auto; contradiction.
  assert (invert_expr_prop (C r) m sq).
    eapply A; eauto. eapply callred_invert; eauto.
  red in H. destruct (C r); auto; contradiction.
Qed.

(** Soundness: if [step_expr] returns [Some ll], then every element
  of [ll] is a reduct. *)

Lemma context_compose:
  forall k2 k3 C2, context k2 k3 C2 ->
  forall k1 C1, context k1 k2 C1 ->
  context k1 k3 (fun x => C2(C1 x))
with contextlist_compose:
  forall k2 C2, contextlist k2 C2 ->
  forall k1 C1, context k1 k2 C1 ->
  contextlist k1 (fun x => C2(C1 x)).
Proof.
  induction 1; intros; try (constructor; eauto).
  replace (fun x => C1 x) with C1. auto. apply extensionality; auto.
  induction 1; intros; constructor; eauto.
Qed.

Hint Constructors context contextlist.
Hint Resolve context_compose contextlist_compose.

Definition reduction_ok (k: kind) (a: expr) (m: mem) (sq: seqs) (rd: reduction) : Prop :=
  match k, rd with
  | LV, Lred l' m' sq' => lred ge e a m l' m' /\ sq' = sq
  | RV, Rred r' m' sq' t => rred ge a m sq t r' m' sq' /\ exists w', possible_trace w t w'
  | RV, Callred fd args tyres m' => callred ge a fd args tyres /\ m' = m
  | LV, Stuckred => ~imm_safe_t k a m sq
  | RV, Stuckred => ~imm_safe_t k a m sq
  | _, _ => False
  end.

Definition reducts_ok (k: kind) (a: expr) (m: mem) (sq: seqs) (ll: reducts expr) : Prop :=
  (forall C rd,
      In (C, rd) ll ->
      exists a', exists k', context k' k C /\ a = C a' /\ reduction_ok k' a' m sq rd)
  /\ (ll = nil -> match k with LV => is_loc a <> None | RV => is_val a <> None end).

Definition list_reducts_ok (al: exprlist) (m: mem) (sq: seqs) (ll: reducts exprlist) : Prop :=
  (forall C rd,
      In (C, rd) ll ->
      exists a', exists k', contextlist k' C /\ al = C a' /\ reduction_ok k' a' m sq rd)
  /\ (ll = nil -> is_val_list al <> None).

Ltac monadInv :=
  match goal with
  | [ H: match ?x with Some _ => _ | None => None end = Some ?y |- _ ] =>
      destruct x eqn:?; [monadInv|discriminate]
  | [ H: match ?x with left _ => _ | right _ => None end = Some ?y |- _ ] =>
      destruct x; [monadInv|discriminate]
  | _ => idtac
  end.

Lemma sem_cast_arguments_sound:
  forall rargs vtl tyargs vargs,
  is_val_list rargs = Some vtl ->
  sem_cast_arguments vtl tyargs = Some vargs ->
  cast_arguments rargs tyargs vargs.
Proof.
  induction rargs; simpl; intros.
  inv H. destruct tyargs; simpl in H0; inv H0. constructor.
  monadInv. inv H. simpl in H0. destruct p as [v1 t1]. destruct tyargs; try congruence. monadInv.
  inv H0. rewrite (is_val_inv _ _ _ Heqo). constructor. auto. eauto. 
Qed.

Lemma sem_cast_arguments_complete:
  forall al tyl vl,
  cast_arguments al tyl vl ->
  exists vtl, is_val_list al = Some vtl /\ sem_cast_arguments vtl tyl = Some vl.
Proof.
  induction 1.
  exists (@nil (val * type)); auto.
  destruct IHcast_arguments as [vtl [A B]]. 
  exists ((v, ty) :: vtl); simpl. rewrite A; rewrite B; rewrite H. auto.
Qed.

Lemma topred_ok:
  forall k a m sq rd,
  reduction_ok k a m sq rd ->
  reducts_ok k a m sq (topred rd).
Proof.
  intros. unfold topred; split; simpl; intros. 
  destruct H0; try contradiction. inv H0. exists a; exists k; auto.
  congruence.
Qed.

Lemma stuck_ok:
  forall k a m sq,
  ~imm_safe_t k a m sq ->
  reducts_ok k a m sq stuck.
Proof.
  intros. unfold stuck; split; simpl; intros.
  destruct H0; try contradiction. inv H0. exists a; exists k; intuition. red. destruct k; auto.
  congruence.
Qed.

Lemma wrong_kind_ok:
  forall k a m sq,
  k <> Cstrategy.expr_kind a ->
  reducts_ok k a m sq stuck.
Proof.
  intros. apply stuck_ok. red; intros. exploit Cstrategy.imm_safe_kind; eauto. 
  eapply imm_safe_t_imm_safe; eauto.
Qed.

Lemma not_invert_ok:
  forall k a m sq,
  match a with
  | Eloc _ _ _ => False
  | Eval _ _ => False
  | _ => invert_expr_prop a m sq -> False
  end ->
  reducts_ok k a m sq stuck.
Proof.
  intros. apply stuck_ok. red; intros. 
  exploit imm_safe_t_inv; eauto. destruct a; auto. 
Qed. 

Lemma incontext_ok:
  forall k a m sq C res k' a',
  reducts_ok k' a' m sq res ->
  a = C a' ->
  context k' k C ->
  match k' with LV => is_loc a' = None | RV => is_val a' = None end ->
  reducts_ok k a m sq (incontext C res).
Proof.
  unfold reducts_ok, incontext; intros. destruct H. split; intros.
  exploit list_in_map_inv; eauto. intros [[C1 rd1] [P Q]]. inv P.
  exploit H; eauto. intros [a'' [k'' [U [V W]]]].
  exists a''; exists k''. split. eapply context_compose; eauto. rewrite V; auto.
  destruct res; simpl in H4; try congruence. destruct k'; intuition congruence.
Qed.

Lemma incontext2_ok:
  forall k a m sq k1 a1 res1 k2 a2 res2 C1 C2,
  reducts_ok k1 a1 m sq res1 ->
  reducts_ok k2 a2 m sq res2 ->
  a = C1 a1 -> a = C2 a2 ->
  context k1 k C1 -> context k2 k C2 ->
  match k1 with LV => is_loc a1 = None | RV => is_val a1 = None end
  \/ match k2 with LV => is_loc a2 = None | RV => is_val a2 = None end ->
  reducts_ok k a m sq (incontext2 C1 res1 C2 res2).
Proof.
  unfold reducts_ok, incontext2, incontext; intros. destruct H; destruct H0; split; intros.
  destruct (in_app_or _ _ _ H8).
  exploit list_in_map_inv; eauto. intros [[C' rd'] [P Q]]. inv P.
  exploit H; eauto. intros [a'' [k'' [U [V W]]]].
  exists a''; exists k''. split. eapply context_compose; eauto. rewrite V; auto.
  exploit list_in_map_inv; eauto. intros [[C' rd'] [P Q]]. inv P.
  exploit H0; eauto. intros [a'' [k'' [U [V W]]]].
  exists a''; exists k''. split. eapply context_compose; eauto. rewrite H2; rewrite V; auto.
  destruct res1; simpl in H8; try congruence. destruct res2; simpl in H8; try congruence.
  destruct H5. destruct k1; intuition congruence. destruct k2; intuition congruence.
Qed.

Lemma incontext_list_ok:
  forall ef tyargs al ty m sq res,
  list_reducts_ok al m sq res ->
  is_val_list al = None ->
  reducts_ok RV (Ebuiltin ef tyargs al ty) m sq
                (incontext (fun x => Ebuiltin ef tyargs x ty) res).
Proof.
  unfold reducts_ok, incontext; intros. destruct H. split; intros.
  exploit list_in_map_inv; eauto. intros [[C1 rd1] [P Q]]. inv P.
  exploit H; eauto. intros [a'' [k'' [U [V W]]]].
  exists a''; exists k''. split. eauto. rewrite V; auto.
  destruct res; simpl in H2. elim H1; auto. congruence.
Qed.

Lemma incontext2_list_ok:
  forall a1 a2 ty m sq res1 res2,
  reducts_ok RV a1 m sq res1 ->
  list_reducts_ok a2 m sq res2 ->
  is_val a1 = None \/ is_val_list a2 = None ->
  reducts_ok RV (Ecall a1 a2 ty) m sq
               (incontext2 (fun x => Ecall x a2 ty) res1
                           (fun x => Ecall a1 x ty) res2).
Proof.
  unfold reducts_ok, incontext2, incontext; intros. destruct H; destruct H0; split; intros.
  destruct (in_app_or _ _ _ H4).
  exploit list_in_map_inv; eauto. intros [[C' rd'] [P Q]]. inv P.
  exploit H; eauto. intros [a'' [k'' [U [V W]]]].
  exists a''; exists k''. split. eauto. rewrite V; auto. 
  exploit list_in_map_inv; eauto. intros [[C' rd'] [P Q]]. inv P.
  exploit H0; eauto. intros [a'' [k'' [U [V W]]]].
  exists a''; exists k''. split. eauto. rewrite V; auto.
  destruct res1; simpl in H4; try congruence. destruct res2; simpl in H4; try congruence.
  tauto.
Qed.

Lemma incontext2_list_ok':
  forall a1 a2 m sq res1 res2,
  reducts_ok RV a1 m sq res1 ->
  list_reducts_ok a2 m sq res2 ->
  list_reducts_ok (Econs a1 a2) m sq
               (incontext2 (fun x => Econs x a2) res1
                           (fun x => Econs a1 x) res2).
Proof.
  unfold reducts_ok, list_reducts_ok, incontext2, incontext; intros.
  destruct H; destruct H0. split; intros.
  destruct (in_app_or _ _ _ H3).
  exploit list_in_map_inv; eauto. intros [[C' rd'] [P Q]]. inv P.
  exploit H; eauto. intros [a'' [k'' [U [V W]]]].
  exists a''; exists k''. split. eauto. rewrite V; auto. 
  exploit list_in_map_inv; eauto. intros [[C' rd'] [P Q]]. inv P.
  exploit H0; eauto. intros [a'' [k'' [U [V W]]]].
  exists a''; exists k''. split. eauto. rewrite V; auto.
  destruct res1; simpl in H3; try congruence. destruct res2; simpl in H3; try congruence.
  simpl. destruct (is_val a1). destruct (is_val_list a2). congruence. intuition congruence. intuition congruence.
Qed.

Lemma is_val_list_all_values:
  forall al vtl, is_val_list al = Some vtl -> exprlist_all_values al.
Proof.
  induction al; simpl; intros. auto. 
  destruct (is_val r1) as [[v ty]|] eqn:?; try discriminate.
  destruct (is_val_list al) as [vtl'|] eqn:?; try discriminate.
  rewrite (is_val_inv _ _ _ Heqo). eauto.
Qed.

Ltac myinv :=
  match goal with
  | [ H: False |- _ ] => destruct H
  | [ H: _ /\ _ |- _ ] => destruct H; myinv
  | [ H: exists _, _ |- _ ] => destruct H; myinv
  | _ => idtac
  end.

Theorem step_expr_sound:
  forall a k m sq, reducts_ok k a m sq (step_expr k a m sq)
with step_exprlist_sound:
  forall al m sq, list_reducts_ok al m sq (step_exprlist al m sq).
Proof with (try (apply not_invert_ok; simpl; intro; myinv; intuition congruence; fail)).
  induction a; intros; simpl; destruct k; try (apply wrong_kind_ok; simpl; congruence).
(* Eval *)
  split; intros. tauto. simpl; congruence.
(* Evar *)
  destruct (e!x) as [[b ty']|] eqn:?.
  destruct (type_eq ty ty')...
  subst. apply topred_ok; auto. split. apply red_var_local; auto. easy.
  destruct (Genv.find_symbol ge x) as [b|] eqn:?...
  apply topred_ok; auto. split. apply red_var_global; auto. easy.
(* Efield *)
  destruct (is_val a) as [[v ty'] | ] eqn:?.
  rewrite (is_val_inv _ _ _ Heqo).
  destruct v...
  destruct ty'... 
  (* top struct *)
  destruct (field_offset f f0) as [delta|] eqn:?...
  apply topred_ok; auto. split. apply red_field_struct; auto. easy.
  (* top union *)
  apply topred_ok; auto. split. apply red_field_union; auto. easy.
  (* in depth *)
  eapply incontext_ok; eauto. 
(* Evalof *)
  destruct (is_loc a) as [[[b ofs] ty'] | ] eqn:?. rewrite (is_loc_inv _ _ _ _ Heqo).
  (* top *)
  destruct (type_eq ty ty')... subst ty'.
  destruct (do_deref_loc w ty m sq b ofs) as [[[w' t] v] | ] eqn:?.
  exploit do_deref_loc_sound; eauto. intros [A B].
  apply topred_ok; auto. red. split. apply red_rvalof; auto. exists w'; auto.
  apply not_invert_ok; simpl; intros; myinv. exploit do_deref_loc_complete; eauto. congruence.
  (* depth *)
  eapply incontext_ok; eauto.
(* Ederef *)
  destruct (is_val a) as [[v ty'] | ] eqn:?. rewrite (is_val_inv _ _ _ Heqo).
  (* top *)
  destruct v... apply topred_ok; auto. split. apply red_deref; auto. easy. 
  (* depth *)
  eapply incontext_ok; eauto.
(* Eaddrof *)
  destruct (is_loc a) as [[[b ofs] ty'] | ] eqn:?. rewrite (is_loc_inv _ _ _ _ Heqo).
  (* top *)
  apply topred_ok; auto. split. apply red_addrof; auto. exists w; constructor.
  (* depth *)
  eapply incontext_ok; eauto.
(* unop *)
  destruct (is_val a) as [[v ty'] | ] eqn:?. rewrite (is_val_inv _ _ _ Heqo). 
  (* top *)
  destruct (sem_unary_operation op v ty') as [v'|] eqn:?...
  apply topred_ok; auto. split. apply red_unop; auto. exists w; constructor. 
  (* depth *)
  eapply incontext_ok; eauto.
(* binop *)
  destruct (is_val a1) as [[v1 ty1] | ] eqn:?. 
  destruct (is_val a2) as [[v2 ty2] | ] eqn:?.
  rewrite (is_val_inv _ _ _ Heqo). rewrite (is_val_inv _ _ _ Heqo0). 
  (* top *)
  destruct (sem_binary_operation op v1 ty1 v2 ty2 m) as [v|] eqn:?...
  apply topred_ok; auto. split. apply red_binop; auto. exists w; constructor.
  (* depth *)
  eapply incontext2_ok; eauto. 
  eapply incontext2_ok; eauto. 
(* cast *)
  destruct (is_val a) as [[v ty'] | ] eqn:?. rewrite (is_val_inv _ _ _ Heqo). 
  (* top *)
  destruct (sem_cast v ty' ty) as [v'|] eqn:?...
  apply topred_ok; auto. split. apply red_cast; auto. exists w; constructor. 
  (* depth *)
  eapply incontext_ok; eauto.
(* seqand *)
  destruct (is_val a1) as [[v ty'] | ] eqn:?. rewrite (is_val_inv _ _ _ Heqo). 
  (* top *)
  destruct (bool_val v ty') as [v'|] eqn:?... destruct v'.
  apply topred_ok; auto. split. eapply red_seqand_true; eauto. exists w; constructor.
  apply topred_ok; auto. split. eapply red_seqand_false; eauto. exists w; constructor.
  (* depth *)
  eapply incontext_ok; eauto.
(* seqor *)
  destruct (is_val a1) as [[v ty'] | ] eqn:?. rewrite (is_val_inv _ _ _ Heqo). 
  (* top *)
  destruct (bool_val v ty') as [v'|] eqn:?... destruct v'.
  apply topred_ok; auto. split. eapply red_seqor_true; eauto. exists w; constructor.
  apply topred_ok; auto. split. eapply red_seqor_false; eauto. exists w; constructor.
  (* depth *)
  eapply incontext_ok; eauto.
(* condition *)
  destruct (is_val a1) as [[v ty'] | ] eqn:?. rewrite (is_val_inv _ _ _ Heqo). 
  (* top *)
  destruct (bool_val v ty') as [v'|] eqn:?...
  apply topred_ok; auto. split. eapply red_condition; eauto. exists w; constructor.
  (* depth *)
  eapply incontext_ok; eauto.
(* sizeof *)
  apply topred_ok; auto. split. apply red_sizeof. exists w; constructor.
(* alignof *)
  apply topred_ok; auto. split. apply red_alignof. exists w; constructor.
(* assign *)
  destruct (is_loc a1) as [[[b ofs] ty1] | ] eqn:?. 
  destruct (is_val a2) as [[v2 ty2] | ] eqn:?. 
  rewrite (is_loc_inv _ _ _ _ Heqo). rewrite (is_val_inv _ _ _ Heqo0).
  (* top *)
  destruct (type_eq ty1 ty)... subst ty1.
  destruct (sem_cast v2 ty2 ty) as [v|] eqn:?...
  destruct (do_assign_loc w ty m sq b ofs v) as [[[[w' t] m'] sq']|] eqn:?.
  exploit do_assign_loc_sound; eauto. intros [P Q].
  apply topred_ok; auto. split. apply red_assign; auto. exists w'; auto.
  apply not_invert_ok; simpl; intros; myinv. exploit do_assign_loc_complete; eauto. congruence.
  (* depth *)
  eapply incontext2_ok; eauto.
  eapply incontext2_ok; eauto.
(* assignop *)
  destruct (is_loc a1) as [[[b ofs] ty1] | ] eqn:?. 
  destruct (is_val a2) as [[v2 ty2] | ] eqn:?. 
  rewrite (is_loc_inv _ _ _ _ Heqo). rewrite (is_val_inv _ _ _ Heqo0). 
  (* top *)
  destruct (type_eq ty1 ty)... subst ty1.
  destruct (do_deref_loc w ty m sq b ofs) as [[[w' t] v] | ] eqn:?.
  exploit do_deref_loc_sound; eauto. intros [A B].
  apply topred_ok; auto. red. split. apply red_assignop; auto. exists w'; auto.
  apply not_invert_ok; simpl; intros; myinv. exploit do_deref_loc_complete; eauto. congruence.
  (* depth *)
  eapply incontext2_ok; eauto.
  eapply incontext2_ok; eauto.
(* postincr *)
  destruct (is_loc a) as [[[b ofs] ty'] | ] eqn:?. rewrite (is_loc_inv _ _ _ _ Heqo). 
  (* top *)
  destruct (type_eq ty' ty)... subst ty'.
  destruct (do_deref_loc w ty m sq b ofs) as [[[w' t] v] | ] eqn:?.
  exploit do_deref_loc_sound; eauto. intros [A B].
  apply topred_ok; auto. red. split. apply red_postincr; auto. exists w'; auto.
  apply not_invert_ok; simpl; intros; myinv. exploit do_deref_loc_complete; eauto. congruence.
  (* depth *)
  eapply incontext_ok; eauto.
(* comma *)
  destruct (is_val a1) as [[v ty'] | ] eqn:?. rewrite (is_val_inv _ _ _ Heqo). 
  (* top *)
  destruct (type_eq (typeof a2) ty)... subst ty.
  apply topred_ok; auto. split. apply red_comma; auto. exists w; constructor.
  (* depth *)
  eapply incontext_ok; eauto.
(* call *)
  destruct (is_val a) as [[vf tyf] | ] eqn:?.  
  destruct (is_val_list rargs) as [vtl | ] eqn:?. 
  rewrite (is_val_inv _ _ _ Heqo). exploit is_val_list_all_values; eauto. intros ALLVAL.
  (* top *)
  destruct (classify_fun tyf) as [tyargs tyres cconv|] eqn:?...
  destruct (Genv.find_funct ge vf) as [fd|] eqn:?...
  destruct (sem_cast_arguments vtl tyargs) as [vargs|] eqn:?... 
  destruct (type_eq (type_of_fundef fd) (Tfunction tyargs tyres cconv))...
  apply topred_ok; auto. red. split; auto. eapply red_Ecall; eauto. 
  eapply sem_cast_arguments_sound; eauto.
  apply not_invert_ok; simpl; intros; myinv. specialize (H ALLVAL). myinv. congruence.
  apply not_invert_ok; simpl; intros; myinv. specialize (H ALLVAL). myinv.
  exploit sem_cast_arguments_complete; eauto. intros [vtl' [P Q]]. congruence.
  apply not_invert_ok; simpl; intros; myinv. specialize (H ALLVAL). myinv. congruence.
  apply not_invert_ok; simpl; intros; myinv. specialize (H ALLVAL). myinv. congruence.
  (* depth *)
  eapply incontext2_list_ok; eauto.
  eapply incontext2_list_ok; eauto.
(* builtin *)
  destruct (is_val_list rargs) as [vtl | ] eqn:?. 
  exploit is_val_list_all_values; eauto. intros ALLVAL.
  (* top *)
  destruct (sem_cast_arguments vtl tyargs) as [vargs|] eqn:?... 
  destruct (do_external ef w vargs m) as [[[[? ?] v] m'] | ] eqn:?...
  exploit do_ef_external_sound; eauto. intros [EC PT].
  apply topred_ok; auto. red. split; auto. eapply red_builtin; eauto. 
  eapply sem_cast_arguments_sound; eauto.
  exists w0; auto.
  apply not_invert_ok; simpl; intros; myinv. specialize (H ALLVAL). myinv.
  assert (x = vargs). 
    exploit sem_cast_arguments_complete; eauto. intros [vtl' [A B]]. congruence.
  subst x. exploit do_ef_external_complete; eauto. congruence.
  apply not_invert_ok; simpl; intros; myinv. specialize (H ALLVAL). myinv. 
  exploit sem_cast_arguments_complete; eauto. intros [vtl' [A B]]. congruence.
  (* depth *)
  eapply incontext_list_ok; eauto.
 
(* loc *)
  split; intros. tauto. simpl; congruence.
(* paren *)
  destruct (is_val a) as [[v ty'] | ] eqn:?. rewrite (is_val_inv _ _ _ Heqo). 
  (* top *)
  destruct (sem_cast v ty' ty) as [v'|] eqn:?...
  apply topred_ok; auto. split. apply red_paren; auto. exists w; constructor. 
  (* depth *)
  eapply incontext_ok; eauto.

  induction al; simpl; intros.
(* nil *)
  split; intros. tauto. simpl; congruence.
(* cons *)
  eapply incontext2_list_ok'; eauto.
Qed.

Lemma step_exprlist_val_list:
  forall m sq al, is_val_list al <> None -> step_exprlist al m sq = nil.
Proof.
  induction al; simpl; intros. 
  auto.
  destruct (is_val r1) as [[v1 ty1]|] eqn:?; try congruence.
  destruct (is_val_list al) eqn:?; try congruence.
  rewrite (is_val_inv _ _ _ Heqo).
  rewrite IHal. auto. congruence.
Qed.

(** Completeness part 1: [step_expr] contains all possible non-error reducts. *)

Lemma lred_topred:
  forall l1 m1 sq1 l2 m2,
  lred ge e l1 m1 l2 m2 ->
  step_expr LV l1 m1 sq1 = topred (Lred l2 m2 sq1).
Proof.
  induction 1; simpl.
(* var local *)
  rewrite H. rewrite dec_eq_true; auto.
(* var global *)
  rewrite H; rewrite H0. auto.
(* deref *) 
  auto.
(* field struct *)
  rewrite H; auto.
(* field union *)
  auto.
Qed.

Lemma rred_topred:
  forall w' r1 m1 sq1 t r2 m2 sq2,
  rred ge r1 m1 sq1 t r2 m2 sq2 -> possible_trace w t w' ->
  step_expr RV r1 m1 sq1 = topred (Rred r2 m2 sq2 t).
Proof.
  induction 1; simpl; intros.
(* valof *)
  rewrite dec_eq_true; auto. rewrite (do_deref_loc_complete _ _ _ _ _ _ _ _ _ H H0). auto. 
(* addrof *)
  inv H. auto.
(* unop *)
  inv H0. rewrite H; auto.
(* binop *)
  inv H0. rewrite H; auto.
(* cast *)
  inv H0. rewrite H; auto.
(* seqand *)
  inv H0. rewrite H; auto.
  inv H0. rewrite H; auto.
(* seqor *)
  inv H0. rewrite H; auto.
  inv H0. rewrite H; auto.
(* condition *)
  inv H0. rewrite H; auto.
(* sizeof *)
  inv H. auto.
(* alignof *)
  inv H. auto.
(* assign *)
  rewrite dec_eq_true; auto. rewrite H. rewrite (do_assign_loc_complete _ _ _ _ _ _ _ _ _ _ _ H0 H1). auto.
(* assignop *)
  rewrite dec_eq_true; auto. rewrite (do_deref_loc_complete _ _ _ _ _ _ _ _ _ H H0). auto. 
(* postincr *)
  rewrite dec_eq_true; auto. subst. rewrite (do_deref_loc_complete _ _ _ _ _ _ _ _ _ H H1). auto.
(* comma *)
  inv H0. rewrite dec_eq_true; auto.
(* paren *)
  inv H0. rewrite H; auto.
(* builtin *)
  exploit sem_cast_arguments_complete; eauto. intros [vtl [A B]].
  exploit do_ef_external_complete; eauto. intros C. 
  rewrite A. rewrite B. rewrite C. auto.
Qed.

Lemma callred_topred:
  forall a fd args ty m sq,
  callred ge a fd args ty ->
  step_expr RV a m sq = topred (Callred fd args ty m).
Proof.
  induction 1; simpl.
  rewrite H2. exploit sem_cast_arguments_complete; eauto. intros [vtl [A B]].
  rewrite A; rewrite H; rewrite B; rewrite H1; rewrite dec_eq_true. auto.
Qed.

Definition reducts_incl {A B: Type} (C: A -> B) (res1: reducts A) (res2: reducts B) : Prop :=
  forall C1 rd, In (C1, rd) res1 -> In ((fun x => C(C1 x)), rd) res2.

Lemma reducts_incl_trans:
  forall (A1 A2: Type) (C: A1 -> A2) res1 res2, reducts_incl C res1 res2 ->
  forall (A3: Type) (C': A2 -> A3) res3,
  reducts_incl C' res2 res3 ->
  reducts_incl (fun x => C'(C x)) res1 res3.
Proof.
  unfold reducts_incl; intros. auto. 
Qed.

Lemma reducts_incl_nil:
  forall (A B: Type) (C: A -> B) res,
  reducts_incl C nil res.
Proof.
  intros; red. intros; contradiction.
Qed.

Lemma reducts_incl_val:
  forall (A: Type) a m sq v ty (C: expr -> A) res,
  is_val a = Some(v, ty) -> reducts_incl C (step_expr RV a m sq) res.
Proof.
  intros. rewrite (is_val_inv _ _ _ H). apply reducts_incl_nil.
Qed.

Lemma reducts_incl_loc:
  forall (A: Type) a m sq b ofs ty (C: expr -> A) res,
  is_loc a = Some(b, ofs, ty) -> reducts_incl C (step_expr LV a m sq) res.
Proof.
  intros. rewrite (is_loc_inv _ _ _ _ H). apply reducts_incl_nil.
Qed.

Lemma reducts_incl_listval:
  forall (A: Type) a m sq vtl (C: exprlist -> A) res,
  is_val_list a = Some vtl -> reducts_incl C (step_exprlist a m sq) res.
Proof.
  intros. rewrite step_exprlist_val_list. apply reducts_incl_nil. congruence.
Qed.

Lemma reducts_incl_incontext:
  forall (A B: Type) (C: A -> B) res,
  reducts_incl C res (incontext C res).
Proof.
  unfold reducts_incl, incontext. intros.
  set (f := fun z : (expr -> A) * reduction => (fun x : expr => C (fst z x), snd z)).
  change (In (f (C1, rd)) (map f res)). apply in_map. auto.
Qed.

Lemma reducts_incl_incontext2_left:
  forall (A1 A2 B: Type) (C1: A1 -> B) res1 (C2: A2 -> B) res2,
  reducts_incl C1 res1 (incontext2 C1 res1 C2 res2).
Proof.
  unfold reducts_incl, incontext2, incontext. intros.
  rewrite in_app_iff. left.
  set (f := fun z : (expr -> A1) * reduction => (fun x : expr => C1 (fst z x), snd z)).
  change (In (f (C0, rd)) (map f res1)). apply in_map; auto.
Qed.

Lemma reducts_incl_incontext2_right:
  forall (A1 A2 B: Type) (C1: A1 -> B) res1 (C2: A2 -> B) res2,
  reducts_incl C2 res2 (incontext2 C1 res1 C2 res2).
Proof.
  unfold reducts_incl, incontext2, incontext. intros.
  rewrite in_app_iff. right.
  set (f := fun z : (expr -> A2) * reduction => (fun x : expr => C2 (fst z x), snd z)).
  change (In (f (C0, rd)) (map f res2)). apply in_map; auto.
Qed.

Hint Resolve reducts_incl_val reducts_incl_loc reducts_incl_listval
             reducts_incl_incontext reducts_incl_incontext2_left reducts_incl_incontext2_right.

Lemma step_expr_context:
  forall from to C, context from to C ->
  forall a m sq, reducts_incl C (step_expr from a m sq) (step_expr to (C a) m sq)
with step_exprlist_context:
  forall from C, contextlist from C ->
  forall a m sq, reducts_incl C (step_expr from a m sq) (step_exprlist (C a) m sq).
Proof.
  induction 1; simpl; intros.
(* top *)
  red. destruct (step_expr k a m); auto.
  try (* no eta in 8.3 *)
   (intros;
    replace (fun x => C1 x) with C1 by (apply extensionality; auto);
    auto).
(* deref *)
  eapply reducts_incl_trans with (C' := fun x => Ederef x ty); eauto.
  destruct (is_val (C a)) as [[v ty']|] eqn:?; eauto.
(* field *)
  eapply reducts_incl_trans with (C' := fun x => Efield x f ty); eauto.
  destruct (is_val (C a)) as [[v ty']|] eqn:?; eauto.
(* valof *)
  eapply reducts_incl_trans with (C' := fun x => Evalof x ty); eauto.
  destruct (is_loc (C a)) as [[[b ofs] ty']|] eqn:?; eauto.
(* addrof *)
  eapply reducts_incl_trans with (C' := fun x => Eaddrof x ty); eauto.
  destruct (is_loc (C a)) as [[[b ofs] ty']|] eqn:?; eauto.
(* unop *)
  eapply reducts_incl_trans with (C' := fun x => Eunop op x ty); eauto.
  destruct (is_val (C a)) as [[v ty']|] eqn:?; eauto.
(* binop left *)
  eapply reducts_incl_trans with (C' := fun x => Ebinop op x e2 ty); eauto.
  destruct (is_val (C a)) as [[v ty']|] eqn:?; eauto.
(* binop right *)
  eapply reducts_incl_trans with (C' := fun x => Ebinop op e1 x ty); eauto.
  destruct (is_val e1) as [[v1 ty1]|] eqn:?; eauto.
  destruct (is_val (C a)) as [[v2 ty2]|] eqn:?; eauto.
(* cast *)
  eapply reducts_incl_trans with (C' := fun x => Ecast x ty); eauto.
  destruct (is_val (C a)) as [[v ty']|] eqn:?; eauto.
(* seqand *)
  eapply reducts_incl_trans with (C' := fun x => Eseqand x r2 ty); eauto.
  destruct (is_val (C a)) as [[v ty']|] eqn:?; eauto.
(* seqor *)
  eapply reducts_incl_trans with (C' := fun x => Eseqor x r2 ty); eauto.
  destruct (is_val (C a)) as [[v ty']|] eqn:?; eauto.
(* condition *)
  eapply reducts_incl_trans with (C' := fun x => Econdition x r2 r3 ty); eauto.
  destruct (is_val (C a)) as [[v ty']|] eqn:?; eauto.
(* assign left *)
  eapply reducts_incl_trans with (C' := fun x => Eassign x e2 ty); eauto.
  destruct (is_loc (C a)) as [[[b ofs] ty']|] eqn:?; eauto.
(* assign right *)
  eapply reducts_incl_trans with (C' := fun x => Eassign e1 x ty); eauto.
  destruct (is_loc e1) as [[[b ofs] ty1]|] eqn:?; eauto.
  destruct (is_val (C a)) as [[v2 ty2]|] eqn:?; eauto.
(* assignop left *)
  eapply reducts_incl_trans with (C' := fun x => Eassignop op x e2 tyres ty); eauto.
  destruct (is_loc (C a)) as [[[b ofs] ty']|] eqn:?; eauto.
(* assignop right *)
  eapply reducts_incl_trans with (C' := fun x => Eassignop op e1 x tyres ty); eauto.
  destruct (is_loc e1) as [[[b ofs] ty1]|] eqn:?; eauto.
  destruct (is_val (C a)) as [[v2 ty2]|] eqn:?; eauto.
(* postincr *)
  eapply reducts_incl_trans with (C' := fun x => Epostincr id x ty); eauto.
  destruct (is_loc (C a)) as [[[b ofs] ty']|] eqn:?; eauto.
(* call left *)
  eapply reducts_incl_trans with (C' := fun x => Ecall x el ty); eauto.
  destruct (is_val (C a)) as [[v ty']|] eqn:?; eauto.
(* call right *)
  eapply reducts_incl_trans with (C' := fun x => Ecall e1 x ty). apply step_exprlist_context. auto. 
  destruct (is_val e1) as [[v1 ty1]|] eqn:?; eauto.
  destruct (is_val_list (C a)) as [vl|] eqn:?; eauto.
(* builtin *)
  eapply reducts_incl_trans with (C' := fun x => Ebuiltin ef tyargs x ty). apply step_exprlist_context. auto. 
  destruct (is_val_list (C a)) as [vl|] eqn:?; eauto.
(* comma *)
  eapply reducts_incl_trans with (C' := fun x => Ecomma sp x e2 ty); eauto.
  destruct (is_val (C a)) as [[v ty']|] eqn:?; eauto.
(* paren *)
  eapply reducts_incl_trans with (C' := fun x => Eparen x ty); eauto.
  destruct (is_val (C a)) as [[v ty']|] eqn:?; eauto.

  induction 1; simpl; intros.
(* cons left *)
  eapply reducts_incl_trans with (C' := fun x => Econs x el).
  apply step_expr_context; eauto. eauto.
(* binop right *)
  eapply reducts_incl_trans with (C' := fun x => Econs e1 x).
  apply step_exprlist_context; eauto. eauto.
Qed.

(** Completeness part 2: if we can reduce to [Stuckstate], [step_expr]
    contains at least one [Stuckred] reduction. *)

Lemma not_stuckred_imm_safe:
  forall m sq a k,
  (forall C, ~In (C, Stuckred) (step_expr k a m sq)) -> imm_safe_t k a m sq.
Proof.
  intros. generalize (step_expr_sound a k m sq). intros [A B]. 
  destruct (step_expr k a m sq) as [|[C rd] res] eqn:?.
  specialize (B (refl_equal _)). destruct k.
  destruct a; simpl in B; try congruence. constructor.
  destruct a; simpl in B; try congruence. constructor.
  assert (NOTSTUCK: rd <> Stuckred).
    red; intros. elim (H C); subst rd; auto with coqlib.
  exploit A. eauto with coqlib. intros [a' [k' [P [Q R]]]]. 
  destruct k'; destruct rd; simpl in R; intuition.
  subst a. eapply imm_safe_t_lred; eauto.
  subst a. destruct H1 as [w' PT]. eapply imm_safe_t_rred; eauto. 
  subst. eapply imm_safe_t_callred; eauto. 
Qed.

Lemma not_imm_safe_stuck_red:
  forall m sq a k C,
  context k RV C ->
  ~imm_safe_t k a m sq ->
  exists C', In (C', Stuckred) (step_expr RV (C a) m sq).
Proof.
  intros. 
  assert (exists C', In (C', Stuckred) (step_expr k a m sq)).
    destruct (classic (exists C', In (C', Stuckred) (step_expr k a m sq))); auto.
    elim H0. apply not_stuckred_imm_safe. apply not_ex_all_not. auto. 
  destruct H1 as [C' IN].
  specialize (step_expr_context _ _ _ H a m). unfold reducts_incl. 
  intro.
  exists (fun x => (C (C' x))). apply H1; auto. 
Qed.

(** Connections between [imm_safe_t] and [imm_safe] *)

Lemma imm_safe_imm_safe_t:
  forall k a m sq,
  imm_safe ge e k a m sq ->
  imm_safe_t k a m sq \/
  exists C, exists a1, exists t, exists a1', exists m', exists sq',
    context RV k C /\ a = C a1 /\ rred ge a1 m sq t a1' m' sq' /\ forall w', ~possible_trace w t w'.
Proof.
  intros. inv H. 
  left. apply imm_safe_t_val.
  left. apply imm_safe_t_loc.
  left. eapply imm_safe_t_lred; eauto.
  destruct (classic (exists w', possible_trace w t w')) as [[w' A] | A].
  left. eapply imm_safe_t_rred; eauto. 
  right. exists C; exists e0; exists t; exists e'; exists m'; exists sq'; intuition. apply A; exists w'; auto.
  left. eapply imm_safe_t_callred; eauto.
Qed.

(** A state can "crash the world" if it can make an observable transition
  whose trace is not accepted by the external world. *)

Definition can_crash_world (w: world) (S: state) : Prop :=
  exists t, exists S', Csem.step ge S t S' /\ forall w', ~possible_trace w t w'.

Theorem not_imm_safe_t:
  forall K C a m sq f k,
  context K RV C ->
  ~imm_safe_t K a m sq ->
  Csem.step ge (ExprState f (C a) k e m sq) E0 Stuckstate \/ can_crash_world w (ExprState f (C a) k e m sq).
Proof.
  intros. destruct (classic (imm_safe ge e K a m sq)).
  exploit imm_safe_imm_safe_t; eauto. 
  intros [A | [C1 [a1 [t [a1' [m' [sq' [A [B [D E]]]]]]]]]]. contradiction.
  right. red. exists t; econstructor; split; auto. 
  left. rewrite B. eapply step_rred with (C := fun x => C(C1 x)). eauto. eauto. 
  left. left. eapply step_stuck; eauto.
Qed.

End EXPRS.

(** * Transitions over states. *)

Fixpoint do_alloc_variables (e: env) (m: mem) (l: list (ident * type)) {struct l} : env * mem :=
  match l with
  | nil => (e,m)
  | (id, ty) :: l' =>
      let (m1,b1) := Mem.alloc m 0 (sizeof ty) in 
      do_alloc_variables (PTree.set id (b1, ty) e) m1 l'
end.

Lemma do_alloc_variables_sound:
  forall l e m, alloc_variables e m l (fst (do_alloc_variables e m l)) (snd (do_alloc_variables e m l)).
Proof.
  induction l; intros; simpl. 
  constructor.
  destruct a as [id ty]. destruct (Mem.alloc m 0 (sizeof ty)) as [m1 b1] eqn:?; simpl.
  econstructor; eauto.
Qed.

Lemma do_alloc_variables_complete:
  forall e1 m1 l e2 m2, alloc_variables e1 m1 l e2 m2 ->
  do_alloc_variables e1 m1 l = (e2, m2).
Proof.
  induction 1; simpl. 
  auto.
  rewrite H; rewrite IHalloc_variables; auto. 
Qed.

Function sem_bind_parameters (w: world) (e: env) (m: mem) (l: list (ident * type)) (lv: list val) 
                          {struct l} : option mem :=
  match l, lv  with
  | nil, nil => Some m
  | (id, ty) :: params, v1::lv =>
      match PTree.get id e with
         | Some (b, ty') =>
             check (type_eq ty ty');
             do w', t, m1, _ <- do_assign_loc w ty m empty_seqs b Int.zero v1;
             match t with nil => sem_bind_parameters w e m1 params lv | _ => None end
        | None => None
      end
   | _, _ => None
end.

Lemma sem_bind_parameters_sound : forall w e m l lv m',
  sem_bind_parameters w e m l lv = Some m' -> 
  bind_parameters ge e m l lv m'.
Proof.
   intros; functional induction (sem_bind_parameters w e m l lv); try discriminate.
   inversion H; constructor; auto.
   exploit do_assign_loc_sound; eauto. intros [A B]. econstructor; eauto.
Qed.

Lemma sem_bind_parameters_complete : forall w e m l lv m',
  bind_parameters ge e m l lv m' ->
  sem_bind_parameters w e m l lv = Some m'.
Proof.
   induction 1; simpl; auto.
   rewrite H. rewrite dec_eq_true.
   assert (possible_trace w E0 w) by constructor.
   rewrite (do_assign_loc_complete _ _ _ _ _ _ _ _ _ _ _ H0 H2).
   simpl. auto. 
Qed.

Definition expr_final_state (f: function) (k: cont) (e: env) (C_rd: (expr -> expr) * reduction) :=
  match snd C_rd with
  | Lred a m sq => (E0, ExprState f (fst C_rd a) k e m sq)
  | Rred a m sq t => (t, ExprState f (fst C_rd a) k e m sq)
  | Callred fd vargs ty m => (E0, Callstate fd vargs (Kcall f e (fst C_rd) ty k) m)
  | Stuck => (E0, Stuckstate)
  end.

Local Open Scope list_monad_scope.

Definition ret (S: state) : list (trace * state) := (E0, S) :: nil.

Definition do_step (w: world) (s: state) : list (trace * state) :=
  match s with

  | ExprState f a k e m sq =>
      match is_val a with
      | Some(v, ty) =>
        match k with
        | Kdo k => ret (State f Sskip k e m )
        | Kifthenelse s1 s2 k =>
            do b <- bool_val v ty; ret (State f (if b then s1 else s2) k e m)
        | Kwhile1 x s k =>
            do b <- bool_val v ty; 
            if b then ret (State f s (Kwhile2 x s k) e m) else ret (State f Sskip k e m)
        | Kdowhile2 x s k =>
            do b <- bool_val v ty;
            if b then ret (State f (Sdowhile x s) k e m) else ret (State f Sskip k e m)
        | Kfor2 a2 a3 s k =>
            do b <- bool_val v ty;
            if b then ret (State f s (Kfor3 a2 a3 s k) e m) else ret (State f Sskip k e m)
        | Kreturn k =>
            do v' <- sem_cast v ty f.(fn_return);
            do m' <- Mem.free_list m (blocks_of_env e);
            ret (Returnstate v' (call_cont k) m')
        | Kswitch1 sl k =>
            match v with
            | Vint n => ret (State f (seq_of_labeled_statement (select_switch n sl)) (Kswitch2 k) e m)
            | _ => nil
            end
        | _ => nil
        end

      | None =>
          map (expr_final_state f k e) (step_expr e w RV a m sq)
      end

  | State f (Sdo x) k e m => ret(ExprState f x (Kdo k) e m empty_seqs)

  | State f (Ssequence s1 s2) k e m => ret(State f s1 (Kseq s2 k) e m)
  | State f Sskip (Kseq s k) e m => ret (State f s k e m)
  | State f Scontinue (Kseq s k) e m => ret (State f Scontinue k e m)
  | State f Sbreak (Kseq s k) e m => ret (State f Sbreak k e m)

  | State f (Sifthenelse a s1 s2) k e m => ret (ExprState f a (Kifthenelse s1 s2 k) e m empty_seqs)

  | State f (Swhile x s) k e m => ret (ExprState f x (Kwhile1 x s k) e m empty_seqs)
  | State f (Sskip|Scontinue) (Kwhile2 x s k) e m => ret (State f (Swhile x s) k e m)
  | State f Sbreak (Kwhile2 x s k) e m => ret (State f Sskip k e m)

  | State f (Sdowhile a s) k e m => ret (State f s (Kdowhile1 a s k) e m)
  | State f (Sskip|Scontinue) (Kdowhile1 x s k) e m => ret (ExprState f x (Kdowhile2 x s k) e m empty_seqs)
  | State f Sbreak (Kdowhile1 x s k) e m => ret (State f Sskip k e m)

  | State f (Sfor a1 a2 a3 s) k e m =>
      if is_skip a1
      then ret (ExprState f a2 (Kfor2 a2 a3 s k) e m empty_seqs)
      else ret (State f a1 (Kseq (Sfor Sskip a2 a3 s) k) e m)
  | State f Sskip (Kfor3 a2 a3 s k) e m => ret (State f a3 (Kfor4 a2 a3 s k) e m)
  | State f Scontinue (Kfor3 a2 a3 s k) e m => ret (State f a3 (Kfor4 a2 a3 s k) e m)
  | State f Sbreak (Kfor3 a2 a3 s k) e m => ret (State f Sskip k e m)
  | State f Sskip (Kfor4 a2 a3 s k) e m => ret (State f (Sfor Sskip a2 a3 s) k e m)

  | State f (Sreturn None) k e m =>
      do m' <- Mem.free_list m (blocks_of_env e);
      ret (Returnstate Vundef (call_cont k) m')
  | State f (Sreturn (Some x)) k e m => ret (ExprState f x (Kreturn k) e m empty_seqs)
  | State f Sskip ((Kstop | Kcall _ _ _ _ _) as k) e m => 
      do m' <- Mem.free_list m (blocks_of_env e);
      ret (Returnstate Vundef k m')

  | State f (Sswitch x sl) k e m => ret (ExprState f x (Kswitch1 sl k) e m empty_seqs)
  | State f (Sskip|Sbreak) (Kswitch2 k) e m => ret (State f Sskip k e m)
  | State f Scontinue (Kswitch2 k) e m => ret (State f Scontinue k e m)

  | State f (Slabel lbl s) k e m => ret (State f s k e m)
  | State f (Sgoto lbl) k e m =>
      match find_label lbl f.(fn_body) (call_cont k) with
      | Some(s', k') => ret (State f s' k' e m)
      | None => nil
      end

  | Callstate (Internal f) vargs k m =>
      check (list_norepet_dec ident_eq (var_names (fn_params f) ++ var_names (fn_vars f)));
      let (e,m1) := do_alloc_variables empty_env m (f.(fn_params) ++ f.(fn_vars)) in
      do m2 <- sem_bind_parameters w e m1 f.(fn_params) vargs;
      ret (State f f.(fn_body) k e m2)
  | Callstate (External ef _ _ _) vargs k m =>
      match do_external ef w vargs m with
      | None => nil
      | Some(w',t,v,m') => (t, Returnstate v k m') :: nil
      end

  | Returnstate v (Kcall f e C ty k) m => ret (ExprState f (C (Eval v ty)) k e m empty_seqs)

  | _ => nil
  end.

Ltac myinv :=
  match goal with
  | [ |- In _ nil -> _ ] => intro X; elim X
  | [ |- In _ (ret _) -> _ ] => 
        intro X; elim X; clear X;
        [intro EQ; unfold ret in EQ; inv EQ; myinv | myinv]
  | [ |- In _ (_ :: nil) -> _ ] => 
        intro X; elim X; clear X; [intro EQ; inv EQ; myinv | myinv]
  | [ |- In _ (match ?x with Some _ => _ | None => _ end) -> _ ] => destruct x eqn:?; myinv
  | [ |- In _ (match ?x with false => _ | true => _ end) -> _ ] => destruct x eqn:?; myinv
  | [ |- In _ (match ?x with left _ => _ | right _ => _ end) -> _ ] => destruct x; myinv
  | _ => idtac
  end.

Hint Extern 3 => exact I.

Theorem do_step_sound:
  forall w S t S',
  In (t, S') (do_step w S) ->
  Csem.step ge S t S' \/ (t = E0 /\ S' = Stuckstate /\ can_crash_world w S).
Proof with try (left; right; econstructor; eauto; fail).
  intros until S'. destruct S; simpl.
(* State *)
  destruct s; myinv...
  (* skip *)
  destruct k; myinv...
  (* break *)
  destruct k; myinv...
  (* continue *)
  destruct k; myinv...
  (* goto *)
  destruct p as [s' k']. myinv...
(* ExprState *)
  destruct (is_val r) as [[v ty]|] eqn:?.
  (* expression is a value *)
  rewrite (is_val_inv _ _ _ Heqo).
  destruct k; myinv...
  destruct v; myinv...
  (* expression reduces *)
  intros. exploit list_in_map_inv; eauto. intros [[C rd] [A B]].
  generalize (step_expr_sound e w r RV m sq). unfold reducts_ok. intros [P Q].
  exploit P; eauto. intros [a' [k' [CTX [EQ RD]]]].
  unfold expr_final_state in A. simpl in A.
  destruct k'; destruct rd; inv A; simpl in RD; try contradiction. 
  (* lred *)
  destruct RD; subst. left; left. apply step_lred; auto.
  (* stuck lred *)
  exploit not_imm_safe_t; eauto. intros [R | R]; eauto.
  (* rred *)
  destruct RD. left; left; apply step_rred; auto.
  (* callred *)
  destruct RD; subst m'. left; left; apply step_call; eauto.
  (* stuck rred *)
  exploit not_imm_safe_t; eauto. intros [R | R]; eauto.
(* callstate *)
  destruct fd; myinv.
  (* internal *)
  destruct (do_alloc_variables empty_env m (fn_params f ++ fn_vars f)) as [e m1] eqn:?.
  myinv. left; right; apply step_internal_function with m1. auto. 
  change e with (fst (e,m1)). change m1 with (snd (e,m1)) at 2. rewrite <- Heqp. 
  apply do_alloc_variables_sound. eapply sem_bind_parameters_sound; eauto.
  (* external *)
  destruct p as [[[w' tr] v] m']. myinv. left; right; constructor. 
  eapply do_ef_external_sound; eauto.
(* returnstate *)
  destruct k; myinv...
(* stuckstate *)
  contradiction.
Qed.

Remark estep_not_val:
  forall f a k e m sq t S,
  estep ge (ExprState f a k e m sq) t S -> is_val a = None.
Proof.
  intros. 
  assert (forall b from to C, context from to C -> (from = to /\ C = fun x => x) \/ is_val (C b) = None).
    induction 1; simpl; auto. 
  inv H. 
  destruct (H0 a0 _ _ _ H10) as [[A B] | A]. subst. inv H9; auto. auto.
  destruct (H0 a0 _ _ _ H10) as [[A B] | A]. subst. inv H9; auto. auto.
  destruct (H0 a0 _ _ _ H10) as [[A B] | A]. subst. inv H9; auto. auto.
  destruct (H0 a0 _ _ _ H9) as [[A B] | A]. subst. destruct a0; auto. elim H10. constructor. auto.
Qed.

Theorem do_step_complete:
  forall w S t S' w', possible_trace w t w' -> Csem.step ge S t S' -> In (t, S') (do_step w S).
Proof with (unfold ret; auto with coqlib).
  intros until w'; intros PT H.
  destruct H. 
  (* Expression step *)
  inversion H; subst; exploit estep_not_val; eauto; intro NOTVAL.
(* lred *)
  unfold do_step; rewrite NOTVAL.
  change (E0, ExprState f (C a') k e m' sq) with (expr_final_state f k e (C, Lred a' m' sq)).
  apply in_map.
  generalize (step_expr_context e w _ _ _ H1 a m). unfold reducts_incl.
  intro. replace C with (fun x => C x). apply H2. 
  rewrite (lred_topred _ _ _ _ _ _ _ H0). unfold topred; auto with coqlib.
  apply extensionality; auto.
(* rred *)
  unfold do_step; rewrite NOTVAL.
  change (t, ExprState f (C a') k e m' sq') with (expr_final_state f k e (C, Rred a' m' sq' t)).
  apply in_map.
  generalize (step_expr_context e w _ _ _ H1 a m). unfold reducts_incl.
  intro. replace C with (fun x => C x). apply H2. 
  rewrite (rred_topred _ _ _ _ _ _ _ _ _ _ H0 PT). unfold topred; auto with coqlib.
  apply extensionality; auto.
(* callred *)
  unfold do_step; rewrite NOTVAL.
  change (E0, Callstate fd vargs (Kcall f e C ty k) m) with (expr_final_state f k e (C, Callred fd vargs ty m)).
  apply in_map.
  generalize (step_expr_context e w _ _ _ H1 a m). unfold reducts_incl.
  intro. replace C with (fun x => C x). apply H2. 
  rewrite (callred_topred _ _ _ _ _ _ _ _ H0). unfold topred; auto with coqlib.
  apply extensionality; auto.
(* stuck *)
  exploit not_imm_safe_stuck_red. eauto. red; intros; elim H1. eapply imm_safe_t_imm_safe. eauto.
  instantiate (1 := w). intros [C' IN].
  simpl do_step. rewrite NOTVAL. 
  change (E0, Stuckstate) with (expr_final_state f k e (C', Stuckred)).
  apply in_map. auto. 

  (* Statement step *)
  inv H; simpl...
  rewrite H0...
  rewrite H0...
  rewrite H0...
  destruct H0; subst s0...
  destruct H0; subst s0...
  rewrite H0...
  rewrite H0...
  rewrite pred_dec_false...
  rewrite H0...
  rewrite H0...
  destruct H0; subst x...
  rewrite H0...
  rewrite H0; rewrite H1...
  rewrite H1. red in H0. destruct k; try contradiction...
  destruct H0; subst x...
  rewrite H0...

  (* Call step *)
  rewrite pred_dec_true; auto. rewrite (do_alloc_variables_complete _ _ _ _ _ H1).
  rewrite (sem_bind_parameters_complete _ _ _ _ _ _ H2)...
  exploit do_ef_external_complete; eauto. intro EQ; rewrite EQ. auto with coqlib.
Qed.

End EXEC.

Local Open Scope option_monad_scope.

Definition do_initial_state (p: program): option (genv * state) :=
  let ge := Genv.globalenv p in
  do m0 <- Genv.init_mem p;
  do b <- Genv.find_symbol ge p.(prog_main);
  do f <- Genv.find_funct_ptr ge b;
  check (type_eq (type_of_fundef f) (Tfunction Tnil type_int32s cc_default));
  Some (ge, Callstate f nil Kstop m0).

Definition at_final_state (S: state): option int :=
  match S with
  | Returnstate (Vint r) Kstop m => Some r
  | _ => None
  end.
