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

(** This module defines the type of values that is used in the dynamic
  semantics of all our intermediate languages. *)

Require Import Coqlib.
Require Import AST.
Require Import Integers.
Require Import Floats.

Definition block : Type := positive.
Definition eq_block := peq.

(** A value is either:
- a machine integer;
- a floating-point number;
- a pointer: a pair of a memory address and an integer offset with respect
  to this address;
- a byte-sized fragment of an opaque pointer. Such fragments are obtained
  by reading the byte representation of a pointer as objects of character
  type;
- the [Vundef] value denoting an arbitrary bit pattern, such as the
  value of an uninitialized variable.
*)

Inductive val: Type :=
  | Vundef: val
  | Vint: int -> val
  | Vlong: int64 -> val
  | Vfloat: float -> val
  | Vptr: block -> int -> val
  | Vptrfrag: block -> int -> nat -> val.

Inductive is_ptrfrag: val -> Prop :=
  intro_is_ptrfrag: forall b ofs i, is_ptrfrag (Vptrfrag b ofs i).

Lemma ptrfrag_dec v : { is_ptrfrag v } + { ~is_ptrfrag v }.
Proof.
 refine
  match v with
  | Vptrfrag _ _ _ => left _
  | _ => right _
  end; first [constructor | inversion 1].
Defined.

Definition Vzero: val := Vint Int.zero.
Definition Vone: val := Vint Int.one.
Definition Vmone: val := Vint Int.mone.

Definition Vtrue: val := Vint Int.one.
Definition Vfalse: val := Vint Int.zero.

(** * Operations over values *)

(** The module [Val] defines a number of arithmetic and logical operations
  over type [val].  Most of these operations are straightforward extensions
  of the corresponding integer or floating-point operations. *)

Module Val.

Definition has_type (v: val) (t: typ) : Prop :=
  match v, t with
  | Vundef, _ => True
  | Vint _, Tint => True
  | Vlong _, Tlong => True
  | Vfloat _, Tfloat => True
  | Vfloat f, Tsingle => Float.is_single f
  | Vptr _ _, Tint => True
  | Vptrfrag _ _ _, Tint => True
  | _, _ => False
  end.

Fixpoint has_type_list (vl: list val) (tl: list typ) {struct vl} : Prop :=
  match vl, tl with
  | nil, nil => True
  | v1 :: vs, t1 :: ts => has_type v1 t1 /\ has_type_list vs ts
  | _, _ => False
  end.

Definition has_opttype (v: val) (ot: option typ) : Prop :=
  match ot with
  | None => v = Vundef
  | Some t => has_type v t
  end.

Lemma has_subtype:
  forall ty1 ty2 v,
  subtype ty1 ty2 = true -> has_type v ty1 -> has_type v ty2.
Proof.
  intros. destruct ty1; destruct ty2; simpl in H; discriminate || assumption || idtac.
  unfold has_type in *. destruct v; auto. 
Qed.

Lemma has_subtype_list:
  forall tyl1 tyl2 vl,
  subtype_list tyl1 tyl2 = true -> has_type_list vl tyl1 -> has_type_list vl tyl2.
Proof.
  induction tyl1; intros; destruct tyl2; try discriminate; destruct vl; try contradiction.
  red; auto.
  simpl in *. InvBooleans. destruct H0. split; auto. eapply has_subtype; eauto.
Qed.

(** Truth values.  Pointers and non-zero integers are treated as [True].
  The integer 0 (also used to represent the null pointer) is [False].
  [Vundef] and floats are neither true nor false. *)

Inductive bool_of_val: val -> bool -> Prop :=
  | bool_of_val_int:
      forall n, bool_of_val (Vint n) (negb (Int.eq n Int.zero))
  | bool_of_val_ptr:
      forall b ofs, bool_of_val (Vptr b ofs) true.

(** Arithmetic operations *)

Definition neg (v: val) : val :=
  match v with
  | Vint n => Vint (Int.neg n)
  | _ => Vundef
  end.

Definition negf (v: val) : val :=
  match v with
  | Vfloat f => Vfloat (Float.neg f)
  | _ => Vundef
  end.

Definition absf (v: val) : val :=
  match v with
  | Vfloat f => Vfloat (Float.abs f)
  | _ => Vundef
  end.

Definition maketotal (ov: option val) : val :=
  match ov with Some v => v | None => Vundef end.

Definition intoffloat (v: val) : option val :=
  match v with
  | Vfloat f => option_map Vint (Float.intoffloat f)
  | _ => None
  end.

Definition intuoffloat (v: val) : option val :=
  match v with
  | Vfloat f => option_map Vint (Float.intuoffloat f)
  | _ => None
  end.

Definition floatofint (v: val) : option val :=
  match v with
  | Vint n => Some (Vfloat (Float.floatofint n))
  | _ => None
  end.

Definition floatofintu (v: val) : option val :=
  match v with
  | Vint n => Some (Vfloat (Float.floatofintu n))
  | _ => None
  end.

Definition negint (v: val) : val :=
  match v with
  | Vint n => Vint (Int.neg n)
  | _ => Vundef
  end.

Definition notint (v: val) : val :=
  match v with
  | Vint n => Vint (Int.not n)
  | _ => Vundef
  end.

Definition of_bool (b: bool): val := if b then Vtrue else Vfalse.

Definition boolval (v: val) : val :=
  match v with
  | Vint n => of_bool (negb (Int.eq n Int.zero))
  | Vptr b ofs => Vtrue
  | _ => Vundef
  end.

Definition notbool (v: val) : val :=
  match v with
  | Vint n => of_bool (Int.eq n Int.zero)
  | Vptr b ofs => Vfalse
  | _ => Vundef
  end.

Definition zero_ext (nbits: Z) (v: val) : val :=
  match v with
  | Vint n => Vint(Int.zero_ext nbits n)
  | _ => Vundef
  end.

Definition sign_ext (nbits: Z) (v: val) : val :=
  match v with
  | Vint n => Vint(Int.sign_ext nbits n)
  | _ => Vundef
  end.

Definition sign_ext_8_alt (v : val) : val :=
  match v with
  | Vint n => Vint (Int.sign_ext 8 n)
  | Vptrfrag b ofs i => Vptrfrag b ofs i
  | _ => Vundef
  end.

Definition singleoffloat (v: val) : val :=
  match v with
  | Vfloat f => Vfloat(Float.singleoffloat f)
  | _ => Vundef
  end.

Definition add (v1 v2: val): val :=
  match v1, v2 with
  | Vint n1, Vint n2 => Vint(Int.add n1 n2)
  | Vptr b1 ofs1, Vint n2 => Vptr b1 (Int.add ofs1 n2)
  | Vint n1, Vptr b2 ofs2 => Vptr b2 (Int.add ofs2 n1)
  | _, _ => Vundef
  end.

Definition sub (v1 v2: val): val :=
  match v1, v2 with
  | Vint n1, Vint n2 => Vint(Int.sub n1 n2)
  | Vptr b1 ofs1, Vint n2 => Vptr b1 (Int.sub ofs1 n2)
  | Vptr b1 ofs1, Vptr b2 ofs2 =>
      if eq_block b1 b2 then Vint(Int.sub ofs1 ofs2) else Vundef
  | _, _ => Vundef
  end.

Definition mul (v1 v2: val): val :=
  match v1, v2 with
  | Vint n1, Vint n2 => Vint(Int.mul n1 n2)
  | _, _ => Vundef
  end.

Definition mulhs (v1 v2: val): val :=
  match v1, v2 with
  | Vint n1, Vint n2 => Vint(Int.mulhs n1 n2)
  | _, _ => Vundef
  end.

Definition mulhu (v1 v2: val): val :=
  match v1, v2 with
  | Vint n1, Vint n2 => Vint(Int.mulhu n1 n2)
  | _, _ => Vundef
  end.

Definition divs (v1 v2: val): option val :=
  match v1, v2 with
  | Vint n1, Vint n2 =>
      if Int.eq n2 Int.zero
      || Int.eq n1 (Int.repr Int.min_signed) && Int.eq n2 Int.mone
      then None
      else Some(Vint(Int.divs n1 n2))
  | _, _ => None
  end.

Definition mods (v1 v2: val): option val :=
  match v1, v2 with
  | Vint n1, Vint n2 =>
      if Int.eq n2 Int.zero
      || Int.eq n1 (Int.repr Int.min_signed) && Int.eq n2 Int.mone
      then None
      else Some(Vint(Int.mods n1 n2))
  | _, _ => None
  end.

Definition divu (v1 v2: val): option val :=
  match v1, v2 with
  | Vint n1, Vint n2 =>
      if Int.eq n2 Int.zero then None else Some(Vint(Int.divu n1 n2))
  | _, _ => None
  end.

Definition modu (v1 v2: val): option val :=
  match v1, v2 with
  | Vint n1, Vint n2 =>
      if Int.eq n2 Int.zero then None else Some(Vint(Int.modu n1 n2))
  | _, _ => None
  end.

Definition add_carry (v1 v2 cin: val): val :=
  match v1, v2, cin with
  | Vint n1, Vint n2, Vint c => Vint(Int.add_carry n1 n2 c)
  | _, _, _ => Vundef
  end.

Definition sub_overflow (v1 v2: val) : val :=
  match v1, v2 with
  | Vint n1, Vint n2 => Vint(Int.sub_overflow n1 n2 Int.zero)
  | _, _ => Vundef
  end.

Definition negative (v: val) : val :=
  match v with
  | Vint n => Vint (Int.negative n)
  | _ => Vundef
  end.

Definition and (v1 v2: val): val :=
  match v1, v2 with
  | Vint n1, Vint n2 => Vint(Int.and n1 n2)
  | _, _ => Vundef
  end.

Definition or (v1 v2: val): val :=
  match v1, v2 with
  | Vint n1, Vint n2 => Vint(Int.or n1 n2)
  | _, _ => Vundef
  end.

Definition xor (v1 v2: val): val :=
  match v1, v2 with
  | Vint n1, Vint n2 => Vint(Int.xor n1 n2)
  | _, _ => Vundef
  end.

Definition shl (v1 v2: val): val :=
  match v1, v2 with
  | Vint n1, Vint n2 =>
     if Int.ltu n2 Int.iwordsize
     then Vint(Int.shl n1 n2)
     else Vundef
  | _, _ => Vundef
  end.

Definition shr (v1 v2: val): val :=
  match v1, v2 with
  | Vint n1, Vint n2 =>
     if Int.ltu n2 Int.iwordsize
     then Vint(Int.shr n1 n2)
     else Vundef
  | _, _ => Vundef
  end.

Definition shr_carry (v1 v2: val): val :=
  match v1, v2 with
  | Vint n1, Vint n2 =>
     if Int.ltu n2 Int.iwordsize
     then Vint(Int.shr_carry n1 n2)
     else Vundef
  | _, _ => Vundef
  end.

Definition shrx (v1 v2: val): option val :=
  match v1, v2 with
  | Vint n1, Vint n2 =>
     if Int.ltu n2 (Int.repr 31)
     then Some(Vint(Int.shrx n1 n2))
     else None
  | _, _ => None
  end.

Definition shru (v1 v2: val): val :=
  match v1, v2 with
  | Vint n1, Vint n2 =>
     if Int.ltu n2 Int.iwordsize
     then Vint(Int.shru n1 n2)
     else Vundef
  | _, _ => Vundef
  end.

Definition rolm (v: val) (amount mask: int): val :=
  match v with
  | Vint n => Vint(Int.rolm n amount mask)
  | _ => Vundef
  end.

Definition ror (v1 v2: val): val :=
  match v1, v2 with
  | Vint n1, Vint n2 =>
     if Int.ltu n2 Int.iwordsize
     then Vint(Int.ror n1 n2)
     else Vundef
  | _, _ => Vundef
  end.

Definition addf (v1 v2: val): val :=
  match v1, v2 with
  | Vfloat f1, Vfloat f2 => Vfloat(Float.add f1 f2)
  | _, _ => Vundef
  end.

Definition subf (v1 v2: val): val :=
  match v1, v2 with
  | Vfloat f1, Vfloat f2 => Vfloat(Float.sub f1 f2)
  | _, _ => Vundef
  end.

Definition mulf (v1 v2: val): val :=
  match v1, v2 with
  | Vfloat f1, Vfloat f2 => Vfloat(Float.mul f1 f2)
  | _, _ => Vundef
  end.

Definition divf (v1 v2: val): val :=
  match v1, v2 with
  | Vfloat f1, Vfloat f2 => Vfloat(Float.div f1 f2)
  | _, _ => Vundef
  end.

Definition floatofwords (v1 v2: val) : val :=
  match v1, v2 with
  | Vint n1, Vint n2 => Vfloat (Float.from_words n1 n2)
  | _, _ => Vundef
  end.

(** Operations on 64-bit integers *)

Definition longofwords (v1 v2: val) : val :=
  match v1, v2 with
  | Vint n1, Vint n2 => Vlong (Int64.ofwords n1 n2)
  | _, _ => Vundef
  end.

Definition loword (v: val) : val :=
  match v with
  | Vlong n  => Vint (Int64.loword n)
  | _ => Vundef
  end.

Definition hiword (v: val) : val :=
  match v with
  | Vlong n  => Vint (Int64.hiword n)
  | _ => Vundef
  end.

Definition negl (v: val) : val :=
  match v with
  | Vlong n => Vlong (Int64.neg n)
  | _ => Vundef
  end.

Definition notl (v: val) : val :=
  match v with
  | Vlong n => Vlong (Int64.not n)
  | _ => Vundef
  end.

Definition longofint (v: val) : val :=
  match v with
  | Vint n => Vlong (Int64.repr (Int.signed n))
  | _ => Vundef
  end.

Definition longofintu (v: val) : val :=
  match v with
  | Vint n => Vlong (Int64.repr (Int.unsigned n))
  | _ => Vundef
  end.

Definition longoffloat (v: val) : option val :=
  match v with
  | Vfloat f => option_map Vlong (Float.longoffloat f)
  | _ => None
  end.

Definition longuoffloat (v: val) : option val :=
  match v with
  | Vfloat f => option_map Vlong (Float.longuoffloat f)
  | _ => None
  end.

Definition floatoflong (v: val) : option val :=
  match v with
  | Vlong n => Some (Vfloat (Float.floatoflong n))
  | _ => None
  end.

Definition floatoflongu (v: val) : option val :=
  match v with
  | Vlong n => Some (Vfloat (Float.floatoflongu n))
  | _ => None
  end.

Definition singleoflong (v: val) : option val :=
  match v with
  | Vlong n => Some (Vfloat (Float.singleoflong n))
  | _ => None
  end.

Definition singleoflongu (v: val) : option val :=
  match v with
  | Vlong n => Some (Vfloat (Float.singleoflongu n))
  | _ => None
  end.

Definition addl (v1 v2: val): val :=
  match v1, v2 with
  | Vlong n1, Vlong n2 => Vlong(Int64.add n1 n2)
  | _, _ => Vundef
  end.

Definition subl (v1 v2: val): val :=
  match v1, v2 with
  | Vlong n1, Vlong n2 => Vlong(Int64.sub n1 n2)
  | _, _ => Vundef
  end.

Definition mull (v1 v2: val): val :=
  match v1, v2 with
  | Vlong n1, Vlong n2 => Vlong(Int64.mul n1 n2)
  | _, _ => Vundef
  end.

Definition mull' (v1 v2: val): val :=
  match v1, v2 with
  | Vint n1, Vint n2 => Vlong(Int64.mul' n1 n2)
  | _, _ => Vundef
  end.

Definition divls (v1 v2: val): option val :=
  match v1, v2 with
  | Vlong n1, Vlong n2 =>
      if Int64.eq n2 Int64.zero
      || Int64.eq n1 (Int64.repr Int64.min_signed) && Int64.eq n2 Int64.mone
      then None
      else Some(Vlong(Int64.divs n1 n2))
  | _, _ => None
  end.

Definition modls (v1 v2: val): option val :=
  match v1, v2 with
  | Vlong n1, Vlong n2 =>
      if Int64.eq n2 Int64.zero
      || Int64.eq n1 (Int64.repr Int64.min_signed) && Int64.eq n2 Int64.mone
      then None
      else Some(Vlong(Int64.mods n1 n2))
  | _, _ => None
  end.

Definition divlu (v1 v2: val): option val :=
  match v1, v2 with
  | Vlong n1, Vlong n2 =>
      if Int64.eq n2 Int64.zero then None else Some(Vlong(Int64.divu n1 n2))
  | _, _ => None
  end.

Definition modlu (v1 v2: val): option val :=
  match v1, v2 with
  | Vlong n1, Vlong n2 =>
      if Int64.eq n2 Int64.zero then None else Some(Vlong(Int64.modu n1 n2))
  | _, _ => None
  end.

Definition andl (v1 v2: val): val :=
  match v1, v2 with
  | Vlong n1, Vlong n2 => Vlong(Int64.and n1 n2)
  | _, _ => Vundef
  end.

Definition orl (v1 v2: val): val :=
  match v1, v2 with
  | Vlong n1, Vlong n2 => Vlong(Int64.or n1 n2)
  | _, _ => Vundef
  end.

Definition xorl (v1 v2: val): val :=
  match v1, v2 with
  | Vlong n1, Vlong n2 => Vlong(Int64.xor n1 n2)
  | _, _ => Vundef
  end.

Definition shll (v1 v2: val): val :=
  match v1, v2 with
  | Vlong n1, Vint n2 =>
     if Int.ltu n2 Int64.iwordsize'
     then Vlong(Int64.shl' n1 n2)
     else Vundef
  | _, _ => Vundef
  end.

Definition shrl (v1 v2: val): val :=
  match v1, v2 with
  | Vlong n1, Vint n2 =>
     if Int.ltu n2 Int64.iwordsize'
     then Vlong(Int64.shr' n1 n2)
     else Vundef
  | _, _ => Vundef
  end.

Definition shrlu (v1 v2: val): val :=
  match v1, v2 with
  | Vlong n1, Vint n2 =>
     if Int.ltu n2 Int64.iwordsize'
     then Vlong(Int64.shru' n1 n2)
     else Vundef
  | _, _ => Vundef
  end.

(** Comparisons *)

Section COMPARISONS.

Variable valid_ptr: block -> Z -> bool.
Let weak_valid_ptr (b: block) (ofs: Z) := valid_ptr b ofs || valid_ptr b (ofs - 1).

Definition cmp_bool (c: comparison) (v1 v2: val): option bool :=
  match v1, v2 with
  | Vint n1, Vint n2 => Some (Int.cmp c n1 n2)
  | _, _ => None
  end.

Definition cmp_different_blocks (c: comparison): option bool :=
  match c with
  | Ceq => Some false
  | Cne => Some true
  | _   => None
  end.

Definition cmpu_bool (c: comparison) (v1 v2: val): option bool :=
  match v1, v2 with
  | Vint n1, Vint n2 =>
      Some (Int.cmpu c n1 n2)
  | Vint n1, Vptr b2 ofs2 =>
      if Int.eq n1 Int.zero then cmp_different_blocks c else None
  | Vptr b1 ofs1, Vptr b2 ofs2 =>
      if eq_block b1 b2 then
        if weak_valid_ptr b1 (Int.unsigned ofs1)
           && weak_valid_ptr b2 (Int.unsigned ofs2)
        then Some (Int.cmpu c ofs1 ofs2)
        else None
      else
        if valid_ptr b1 (Int.unsigned ofs1)
           && valid_ptr b2 (Int.unsigned ofs2)
        then cmp_different_blocks c
        else None
  | Vptr b1 ofs1, Vint n2 =>
      if Int.eq n2 Int.zero then cmp_different_blocks c else None
  | _, _ => None
  end.

Definition cmpf_bool (c: comparison) (v1 v2: val): option bool :=
  match v1, v2 with
  | Vfloat f1, Vfloat f2 => Some (Float.cmp c f1 f2)
  | _, _ => None
  end.

Definition cmpl_bool (c: comparison) (v1 v2: val): option bool :=
  match v1, v2 with
  | Vlong n1, Vlong n2 => Some (Int64.cmp c n1 n2)
  | _, _ => None
  end.

Definition cmplu_bool (c: comparison) (v1 v2: val): option bool :=
  match v1, v2 with
  | Vlong n1, Vlong n2 => Some (Int64.cmpu c n1 n2)
  | _, _ => None
  end.

Definition of_optbool (ob: option bool): val :=
  match ob with Some true => Vtrue | Some false => Vfalse | None => Vundef end.

Definition cmp (c: comparison) (v1 v2: val): val :=
  of_optbool (cmp_bool c v1 v2).

Definition cmpu (c: comparison) (v1 v2: val): val :=
  of_optbool (cmpu_bool c v1 v2).

Definition cmpf (c: comparison) (v1 v2: val): val :=
  of_optbool (cmpf_bool c v1 v2).

Definition cmpl (c: comparison) (v1 v2: val): option val :=
  option_map of_bool (cmpl_bool c v1 v2).

Definition cmplu (c: comparison) (v1 v2: val): option val :=
  option_map of_bool (cmplu_bool c v1 v2).

Definition maskzero_bool (v: val) (mask: int): option bool :=
  match v with
  | Vint n => Some (Int.eq (Int.and n mask) Int.zero)
  | _ => None
  end.

End COMPARISONS.

(** [load_result] reflects the effect of storing a value with a given
  memory chunk, then reading it back with the same chunk.  Depending
  on the chunk and the type of the value, some normalization occurs.
  For instance, consider storing the integer value [0xFFF] on 1 byte
  at a given address, and reading it back.  If it is read back with
  chunk [Mint8unsigned], zero-extension must be performed, resulting
  in [0xFF].  If it is read back as a [Mint8signed], sign-extension is
  performed and [0xFFFFFFFF] is returned. *)

Definition load_result (chunk: memory_chunk) (v: val) :=
  match chunk, v with
  | Mint8signed, Vint n => Vint (Int.sign_ext 8 n)
  | Mint8unsigned, Vint n => Vint (Int.zero_ext 8 n)
  | Mint16signed, Vint n => Vint (Int.sign_ext 16 n)
  | Mint16unsigned, Vint n => Vint (Int.zero_ext 16 n)
  | Mint32, Vint n => Vint n
  | Mint32, Vptr b ofs => Vptr b ofs
  | Mint64, Vlong n => Vlong n
  | (Mint8signed | Mint8unsigned | Mint32), Vptrfrag b ofs i => Vptrfrag b ofs i
  | Mfloat32, Vfloat f => Vfloat(Float.singleoffloat f)
  | Mfloat64, Vfloat f => Vfloat f
  | _, _ => Vundef
  end.

Lemma load_result_type:
  forall chunk v, has_type (load_result chunk v) (type_of_chunk chunk).
Proof.
  intros. destruct chunk; destruct v; simpl; auto. apply Float.singleoffloat_is_single.
Qed.

Lemma load_result_same:
  forall v ty, has_type v ty -> load_result (chunk_of_type ty) v = v.
Proof.
  unfold has_type; intros. destruct v; destruct ty; try contradiction; auto.
  simpl. rewrite Float.singleoffloat_of_single; auto. 
Qed.

(** Theorems on arithmetic operations. *)

Theorem cast8unsigned_and:
  forall x, zero_ext 8 x = and x (Vint(Int.repr 255)).
Proof.
  destruct x; simpl; auto. decEq. 
  change 255 with (two_p 8 - 1). apply Int.zero_ext_and. omega. 
Qed.

Theorem cast16unsigned_and:
  forall x, zero_ext 16 x = and x (Vint(Int.repr 65535)).
Proof.
  destruct x; simpl; auto. decEq. 
  change 65535 with (two_p 16 - 1). apply Int.zero_ext_and. omega.
Qed.

Theorem bool_of_val_of_bool:
  forall b1 b2, bool_of_val (of_bool b1) b2 -> b1 = b2.
Proof.
  intros. destruct b1; simpl in H; inv H; auto.
Qed.

Theorem bool_of_val_of_optbool:
  forall ob b, bool_of_val (of_optbool ob) b -> ob = Some b.
Proof.
  intros. destruct ob; simpl in H. 
  destruct b0; simpl in H; inv H; auto.
  inv H.
Qed.

Theorem notbool_negb_1:
  forall b, of_bool (negb b) = notbool (of_bool b).
Proof.
  destruct b; reflexivity.
Qed.

Theorem notbool_negb_2:
  forall b, of_bool b = notbool (of_bool (negb b)).
Proof.
  destruct b; reflexivity.
Qed.

Theorem notbool_negb_3:
  forall ob, of_optbool (option_map negb ob) = notbool (of_optbool ob).
Proof.
  destruct ob; auto. destruct b; auto.
Qed.

Theorem notbool_idem2:
  forall b, notbool(notbool(of_bool b)) = of_bool b.
Proof.
  destruct b; reflexivity.
Qed.

Theorem notbool_idem3:
  forall x, notbool(notbool(notbool x)) = notbool x.
Proof.
  destruct x; simpl; auto. 
  case (Int.eq i Int.zero); reflexivity.
Qed.

Theorem notbool_idem4:
  forall ob, notbool (notbool (of_optbool ob)) = of_optbool ob.
Proof.
  destruct ob; auto. destruct b; auto.
Qed.

Theorem add_commut: forall x y, add x y = add y x.
Proof.
  destruct x; destruct y; simpl; auto.
  decEq. apply Int.add_commut.
Qed.

Theorem add_assoc: forall x y z, add (add x y) z = add x (add y z).
Proof.
  destruct x; destruct y; destruct z; simpl; auto.
  rewrite Int.add_assoc; auto.
  rewrite Int.add_assoc; auto.
  decEq. decEq. apply Int.add_commut.
  decEq. rewrite Int.add_commut. rewrite <- Int.add_assoc. 
  decEq. apply Int.add_commut.
  decEq. rewrite Int.add_assoc. auto.
Qed.

Theorem add_permut: forall x y z, add x (add y z) = add y (add x z).
Proof.
  intros. rewrite (add_commut y z). rewrite <- add_assoc. apply add_commut.
Qed.

Theorem add_permut_4:
  forall x y z t, add (add x y) (add z t) = add (add x z) (add y t).
Proof.
  intros. rewrite add_permut. rewrite add_assoc. 
  rewrite add_permut. symmetry. apply add_assoc. 
Qed.

Theorem neg_zero: neg Vzero = Vzero.
Proof.
  reflexivity.
Qed.

Theorem neg_add_distr: forall x y, neg(add x y) = add (neg x) (neg y).
Proof.
  destruct x; destruct y; simpl; auto. decEq. apply Int.neg_add_distr.
Qed.

Theorem sub_zero_r: forall x, sub Vzero x = neg x.
Proof.
  destruct x; simpl; auto. 
Qed.

Theorem sub_add_opp: forall x y, sub x (Vint y) = add x (Vint (Int.neg y)).
Proof.
  destruct x; intro y; simpl; auto; rewrite Int.sub_add_opp; auto.
Qed.

Theorem sub_opp_add: forall x y, sub x (Vint (Int.neg y)) = add x (Vint y).
Proof.
  intros. unfold sub, add.
  destruct x; auto; rewrite Int.sub_add_opp; rewrite Int.neg_involutive; auto.
Qed.

Theorem sub_add_l:
  forall v1 v2 i, sub (add v1 (Vint i)) v2 = add (sub v1 v2) (Vint i).
Proof.
  destruct v1; destruct v2; intros; simpl; auto.
  rewrite Int.sub_add_l. auto.
  rewrite Int.sub_add_l. auto.
  case (eq_block b b0); intro. rewrite Int.sub_add_l. auto. reflexivity.
Qed.

Theorem sub_add_r:
  forall v1 v2 i, sub v1 (add v2 (Vint i)) = add (sub v1 v2) (Vint (Int.neg i)).
Proof.
  destruct v1; destruct v2; intros; simpl; auto.
  rewrite Int.sub_add_r. auto.
  repeat rewrite Int.sub_add_opp. decEq. 
  repeat rewrite Int.add_assoc. decEq. apply Int.add_commut.
  decEq. repeat rewrite Int.sub_add_opp. 
  rewrite Int.add_assoc. decEq. apply Int.neg_add_distr.
  case (eq_block b b0); intro. simpl. decEq. 
  repeat rewrite Int.sub_add_opp. rewrite Int.add_assoc. decEq.
  apply Int.neg_add_distr.
  reflexivity.
Qed.

Theorem mul_commut: forall x y, mul x y = mul y x.
Proof.
  destruct x; destruct y; simpl; auto. decEq. apply Int.mul_commut.
Qed.

Theorem mul_assoc: forall x y z, mul (mul x y) z = mul x (mul y z).
Proof.
  destruct x; destruct y; destruct z; simpl; auto.
  decEq. apply Int.mul_assoc.
Qed.

Theorem mul_add_distr_l:
  forall x y z, mul (add x y) z = add (mul x z) (mul y z).
Proof.
  destruct x; destruct y; destruct z; simpl; auto.
  decEq. apply Int.mul_add_distr_l.
Qed.

Theorem mul_add_distr_r:
  forall x y z, mul x (add y z) = add (mul x y) (mul x z).
Proof.
  destruct x; destruct y; destruct z; simpl; auto.
  decEq. apply Int.mul_add_distr_r.
Qed.

Theorem mul_pow2:
  forall x n logn,
  Int.is_power2 n = Some logn ->
  mul x (Vint n) = shl x (Vint logn).
Proof.
  intros; destruct x; simpl; auto.
  change 32 with Int.zwordsize.
  rewrite (Int.is_power2_range _ _ H). decEq. apply Int.mul_pow2. auto.
Qed.  

Theorem mods_divs:
  forall x y z,
  mods x y = Some z -> exists v, divs x y = Some v /\ z = sub x (mul v y).
Proof.
  intros. destruct x; destruct y; simpl in *; try discriminate.
  destruct (Int.eq i0 Int.zero
        || Int.eq i (Int.repr Int.min_signed) && Int.eq i0 Int.mone); inv H.
  exists (Vint (Int.divs i i0)); split; auto. 
  simpl. rewrite Int.mods_divs. auto.
Qed.

Theorem modu_divu:
  forall x y z,
  modu x y = Some z -> exists v, divu x y = Some v /\ z = sub x (mul v y).
Proof.
  intros. destruct x; destruct y; simpl in *; try discriminate.
  destruct (Int.eq i0 Int.zero) eqn:?; inv H. 
  exists (Vint (Int.divu i i0)); split; auto. 
  simpl. rewrite Int.modu_divu. auto.
  generalize (Int.eq_spec i0 Int.zero). rewrite Heqb; auto. 
Qed.

Theorem divs_pow2:
  forall x n logn y,
  Int.is_power2 n = Some logn -> Int.ltu logn (Int.repr 31) = true ->
  divs x (Vint n) = Some y ->
  shrx x (Vint logn) = Some y.
Proof.
  intros; destruct x; simpl in H1; inv H1.
  destruct (Int.eq n Int.zero
         || Int.eq i (Int.repr Int.min_signed) && Int.eq n Int.mone); inv H3.
  simpl. rewrite H0. decEq. decEq. symmetry. apply Int.divs_pow2. auto.
Qed.

Theorem divu_pow2:
  forall x n logn y,
  Int.is_power2 n = Some logn ->
  divu x (Vint n) = Some y ->
  shru x (Vint logn) = y.
Proof.
  intros; destruct x; simpl in H0; inv H0.
  destruct (Int.eq n Int.zero); inv H2. 
  simpl. 
  rewrite (Int.is_power2_range _ _ H).
  decEq. symmetry. apply Int.divu_pow2. auto.
Qed.

Theorem modu_pow2:
  forall x n logn y,
  Int.is_power2 n = Some logn ->
  modu x (Vint n) = Some y ->
  and x (Vint (Int.sub n Int.one)) = y.
Proof.
  intros; destruct x; simpl in H0; inv H0.
  destruct (Int.eq n Int.zero); inv H2. 
  simpl. decEq. symmetry. eapply Int.modu_and; eauto.
Qed.

Lemma and_ptrfrag v1 v2 : ~is_ptrfrag (Val.and v1 v2).
Proof.
  now destruct v1, v2.
Qed.

Theorem and_commut: forall x y, and x y = and y x.
Proof.
  destruct x; destruct y; simpl; auto. decEq. apply Int.and_commut.
Qed.

Theorem and_assoc: forall x y z, and (and x y) z = and x (and y z).
Proof.
  destruct x; destruct y; destruct z; simpl; auto.
  decEq. apply Int.and_assoc.
Qed.

Lemma or_ptrfrag v1 v2 : ~is_ptrfrag (Val.or v1 v2).
Proof.
  now destruct v1, v2.
Qed.

Theorem or_commut: forall x y, or x y = or y x.
Proof.
  destruct x; destruct y; simpl; auto. decEq. apply Int.or_commut.
Qed.

Theorem or_assoc: forall x y z, or (or x y) z = or x (or y z).
Proof.
  destruct x; destruct y; destruct z; simpl; auto.
  decEq. apply Int.or_assoc.
Qed.

Lemma xor_ptrfrag v1 v2 : ~is_ptrfrag (Val.xor v1 v2).
Proof.
  now destruct v1, v2.
Qed.

Theorem xor_commut: forall x y, xor x y = xor y x.
Proof.
  destruct x; destruct y; simpl; auto. decEq. apply Int.xor_commut.
Qed.

Theorem xor_assoc: forall x y z, xor (xor x y) z = xor x (xor y z).
Proof.
  destruct x; destruct y; destruct z; simpl; auto.
  decEq. apply Int.xor_assoc.
Qed.

Theorem not_xor: forall x, notint x = xor x (Vint Int.mone).
Proof.
  destruct x; simpl; auto. 
Qed.

Theorem shl_mul: forall x y, mul x (shl Vone y) = shl x y.
Proof.
  destruct x; destruct y; simpl; auto. 
  case (Int.ltu i0 Int.iwordsize); auto.
  decEq. symmetry. apply Int.shl_mul.
Qed.

Theorem shl_rolm:
  forall x n,
  Int.ltu n Int.iwordsize = true ->
  shl x (Vint n) = rolm x n (Int.shl Int.mone n).
Proof.
  intros; destruct x; simpl; auto.
  rewrite H. decEq. apply Int.shl_rolm. exact H.
Qed.

Theorem shru_rolm:
  forall x n,
  Int.ltu n Int.iwordsize = true ->
  shru x (Vint n) = rolm x (Int.sub Int.iwordsize n) (Int.shru Int.mone n).
Proof.
  intros; destruct x; simpl; auto.
  rewrite H. decEq. apply Int.shru_rolm. exact H.
Qed.

Theorem shrx_carry:
  forall x y z,
  shrx x y = Some z ->
  add (shr x y) (shr_carry x y) = z.
Proof.
  intros. destruct x; destruct y; simpl in H; inv H. 
  destruct (Int.ltu i0 (Int.repr 31)) eqn:?; inv H1.
  exploit Int.ltu_inv; eauto. change (Int.unsigned (Int.repr 31)) with 31. intros.
  assert (Int.ltu i0 Int.iwordsize = true). 
    unfold Int.ltu. apply zlt_true. change (Int.unsigned Int.iwordsize) with 32. omega. 
  simpl. rewrite H0. simpl. decEq. rewrite Int.shrx_carry; auto.
Qed.

Theorem shrx_shr:
  forall x y z,
  shrx x y = Some z ->
  exists p, exists q,
    x = Vint p /\ y = Vint q /\
    z = shr (if Int.lt p Int.zero then add x (Vint (Int.sub (Int.shl Int.one q) Int.one)) else x) (Vint q).
Proof.
  intros. destruct x; destruct y; simpl in H; inv H. 
  destruct (Int.ltu i0 (Int.repr 31)) eqn:?; inv H1.
  exploit Int.ltu_inv; eauto. change (Int.unsigned (Int.repr 31)) with 31. intros.
  assert (Int.ltu i0 Int.iwordsize = true). 
    unfold Int.ltu. apply zlt_true. change (Int.unsigned Int.iwordsize) with 32. omega. 
  exists i; exists i0; intuition. 
  rewrite Int.shrx_shr; auto. destruct (Int.lt i Int.zero); simpl; rewrite H0; auto.
Qed.

Theorem or_rolm:
  forall x n m1 m2,
  or (rolm x n m1) (rolm x n m2) = rolm x n (Int.or m1 m2).
Proof.
  intros; destruct x; simpl; auto.
  decEq. apply Int.or_rolm.
Qed.

Theorem rolm_rolm:
  forall x n1 m1 n2 m2,
  rolm (rolm x n1 m1) n2 m2 =
    rolm x (Int.modu (Int.add n1 n2) Int.iwordsize)
           (Int.and (Int.rol m1 n2) m2).
Proof.
  intros; destruct x; simpl; auto.
  decEq. 
  apply Int.rolm_rolm. apply int_wordsize_divides_modulus.
Qed.

Theorem rolm_zero:
  forall x m,
  rolm x Int.zero m = and x (Vint m).
Proof.
  intros; destruct x; simpl; auto. decEq. apply Int.rolm_zero.
Qed.

Theorem negate_cmp_bool:
  forall c x y, cmp_bool (negate_comparison c) x y = option_map negb (cmp_bool c x y).
Proof.
  destruct x; destruct y; simpl; auto. rewrite Int.negate_cmp. auto.
Qed.

Theorem negate_cmpu_bool:
  forall valid_ptr c x y,
  cmpu_bool valid_ptr (negate_comparison c) x y = option_map negb (cmpu_bool valid_ptr c x y).
Proof.
  assert (forall c,
    cmp_different_blocks (negate_comparison c) = option_map negb (cmp_different_blocks c)).
  destruct c; auto. 
  destruct x; destruct y; simpl; auto.
  rewrite Int.negate_cmpu. auto.
  destruct (Int.eq i Int.zero); auto. 
  destruct (Int.eq i0 Int.zero); auto.
  destruct (eq_block b b0).
  destruct ((valid_ptr b (Int.unsigned i) || valid_ptr b (Int.unsigned i - 1)) &&
            (valid_ptr b0 (Int.unsigned i0) || valid_ptr b0 (Int.unsigned i0 - 1))).
  rewrite Int.negate_cmpu. auto.
  auto.
  destruct (valid_ptr b (Int.unsigned i) && valid_ptr b0 (Int.unsigned i0)); auto.
Qed.

Lemma not_of_optbool:
  forall ob, of_optbool (option_map negb ob) = notbool (of_optbool ob).
Proof.
  destruct ob; auto. destruct b; auto. 
Qed.

Theorem negate_cmp:
  forall c x y,
  cmp (negate_comparison c) x y = notbool (cmp c x y).
Proof.
  intros. unfold cmp. rewrite negate_cmp_bool. apply not_of_optbool.
Qed.

Theorem negate_cmpu:
  forall valid_ptr c x y,
  cmpu valid_ptr (negate_comparison c) x y =
    notbool (cmpu valid_ptr c x y).
Proof.
  intros. unfold cmpu. rewrite negate_cmpu_bool. apply not_of_optbool.
Qed.

Theorem swap_cmp_bool:
  forall c x y,
  cmp_bool (swap_comparison c) x y = cmp_bool c y x.
Proof.
  destruct x; destruct y; simpl; auto. rewrite Int.swap_cmp. auto.
Qed.

Theorem swap_cmpu_bool:
  forall valid_ptr c x y,
  cmpu_bool valid_ptr (swap_comparison c) x y =
    cmpu_bool valid_ptr c y x.
Proof.
  assert (forall c, cmp_different_blocks (swap_comparison c) = cmp_different_blocks c).
    destruct c; auto.
  destruct x; destruct y; simpl; auto.
  rewrite Int.swap_cmpu. auto.
  case (Int.eq i Int.zero); auto.
  case (Int.eq i0 Int.zero); auto.
  destruct (eq_block b b0); subst.
  rewrite dec_eq_true.
  destruct (valid_ptr b0 (Int.unsigned i) || valid_ptr b0 (Int.unsigned i - 1));
  destruct (valid_ptr b0 (Int.unsigned i0) || valid_ptr b0 (Int.unsigned i0 - 1));
  simpl; auto.
  rewrite Int.swap_cmpu. auto.
  rewrite dec_eq_false by auto.
  destruct (valid_ptr b (Int.unsigned i));
    destruct (valid_ptr b0 (Int.unsigned i0)); simpl; auto.
Qed.

Theorem negate_cmpf_eq:
  forall v1 v2, notbool (cmpf Cne v1 v2) = cmpf Ceq v1 v2.
Proof.
  destruct v1; destruct v2; auto. unfold cmpf, cmpf_bool. 
  rewrite Float.cmp_ne_eq. destruct (Float.cmp Ceq f f0); auto.
Qed.

Theorem negate_cmpf_ne:
  forall v1 v2, notbool (cmpf Ceq v1 v2) = cmpf Cne v1 v2.
Proof.
  destruct v1; destruct v2; auto. unfold cmpf, cmpf_bool. 
  rewrite Float.cmp_ne_eq. destruct (Float.cmp Ceq f f0); auto.
Qed.

Theorem cmpf_le:
  forall v1 v2, cmpf Cle v1 v2 = or (cmpf Clt v1 v2) (cmpf Ceq v1 v2).
Proof.
  destruct v1; destruct v2; auto. unfold cmpf, cmpf_bool. 
  rewrite Float.cmp_le_lt_eq.
  destruct (Float.cmp Clt f f0); destruct (Float.cmp Ceq f f0); auto.
Qed.

Theorem cmpf_ge:
  forall v1 v2, cmpf Cge v1 v2 = or (cmpf Cgt v1 v2) (cmpf Ceq v1 v2).
Proof.
  destruct v1; destruct v2; auto. unfold cmpf, cmpf_bool. 
  rewrite Float.cmp_ge_gt_eq.
  destruct (Float.cmp Cgt f f0); destruct (Float.cmp Ceq f f0); auto.
Qed.

Theorem cmp_ne_0_optbool:
  forall ob, cmp Cne (of_optbool ob) (Vint Int.zero) = of_optbool ob.
Proof.
  intros. destruct ob; simpl; auto. destruct b; auto. 
Qed.

Theorem cmp_eq_1_optbool:
  forall ob, cmp Ceq (of_optbool ob) (Vint Int.one) = of_optbool ob.
Proof.
  intros. destruct ob; simpl; auto. destruct b; auto. 
Qed.

Theorem cmp_eq_0_optbool:
  forall ob, cmp Ceq (of_optbool ob) (Vint Int.zero) = of_optbool (option_map negb ob).
Proof.
  intros. destruct ob; simpl; auto. destruct b; auto. 
Qed.

Theorem cmp_ne_1_optbool:
  forall ob, cmp Cne (of_optbool ob) (Vint Int.one) = of_optbool (option_map negb ob).
Proof.
  intros. destruct ob; simpl; auto. destruct b; auto. 
Qed.

Theorem cmpu_ne_0_optbool:
  forall valid_ptr ob,
  cmpu valid_ptr Cne (of_optbool ob) (Vint Int.zero) = of_optbool ob.
Proof.
  intros. destruct ob; simpl; auto. destruct b; auto. 
Qed.

Theorem cmpu_eq_1_optbool:
  forall valid_ptr ob,
  cmpu valid_ptr Ceq (of_optbool ob) (Vint Int.one) = of_optbool ob.
Proof.
  intros. destruct ob; simpl; auto. destruct b; auto. 
Qed.

Theorem cmpu_eq_0_optbool:
  forall valid_ptr ob,
  cmpu valid_ptr Ceq (of_optbool ob) (Vint Int.zero) = of_optbool (option_map negb ob).
Proof.
  intros. destruct ob; simpl; auto. destruct b; auto. 
Qed.

Theorem cmpu_ne_1_optbool:
  forall valid_ptr ob,
  cmpu valid_ptr Cne (of_optbool ob) (Vint Int.one) = of_optbool (option_map negb ob).
Proof.
  intros. destruct ob; simpl; auto. destruct b; auto. 
Qed.

Lemma zero_ext_and:
  forall n v,
  0 < n < Int.zwordsize ->
  Val.zero_ext n v = Val.and v (Vint (Int.repr (two_p n - 1))).
Proof.
  intros. destruct v; simpl; auto. decEq. apply Int.zero_ext_and; auto. omega.
Qed.

Lemma rolm_lt_zero:
  forall v, rolm v Int.one Int.one = cmp Clt v (Vint Int.zero).
Proof.
  intros. unfold cmp, cmp_bool; destruct v; simpl; auto.
  transitivity (Vint (Int.shru i (Int.repr (Int.zwordsize - 1)))).
  decEq. symmetry. rewrite Int.shru_rolm. auto. auto. 
  rewrite Int.shru_lt_zero. destruct (Int.lt i Int.zero); auto. 
Qed.

Lemma rolm_ge_zero:
  forall v,
  xor (rolm v Int.one Int.one) (Vint Int.one) = cmp Cge v (Vint Int.zero).
Proof.
  intros. rewrite rolm_lt_zero. destruct v; simpl; auto.
  unfold cmp; simpl. destruct (Int.lt i Int.zero); auto.
Qed.

(** The ``is less defined'' relation between values. 
    A value is less defined than itself, and [Vundef] is
    less defined than any value. *)

Inductive lessdef: val -> val -> Prop :=
  | lessdef_refl: forall v, lessdef v v
  | lessdef_undef: forall v, lessdef Vundef v.

Lemma lessdef_same:
  forall v1 v2, v1 = v2 -> lessdef v1 v2.
Proof.
  intros. subst v2. constructor.
Qed.

Lemma lessdef_trans:
  forall v1 v2 v3, lessdef v1 v2 -> lessdef v2 v3 -> lessdef v1 v3.
Proof.
  intros. inv H. auto. constructor.
Qed.

Inductive lessdef_list: list val -> list val -> Prop :=
  | lessdef_list_nil:
      lessdef_list nil nil
  | lessdef_list_cons:
      forall v1 v2 vl1 vl2,
      lessdef v1 v2 -> lessdef_list vl1 vl2 ->
      lessdef_list (v1 :: vl1) (v2 :: vl2).

Hint Resolve lessdef_refl lessdef_undef lessdef_list_nil lessdef_list_cons.

Lemma lessdef_list_inv:
  forall vl1 vl2, lessdef_list vl1 vl2 -> vl1 = vl2 \/ In Vundef vl1.
Proof.
  induction 1; simpl.
  tauto.
  inv H. destruct IHlessdef_list. 
  left; congruence. tauto. tauto.
Qed.

(** Compatibility of operations with the [lessdef] relation. *)

Lemma load_result_lessdef:
  forall chunk v1 v2,
  lessdef v1 v2 -> lessdef (load_result chunk v1) (load_result chunk v2).
Proof.
  intros. inv H. auto. destruct chunk; simpl; auto.
Qed.

Lemma zero_ext_lessdef:
  forall n v1 v2, lessdef v1 v2 -> lessdef (zero_ext n v1) (zero_ext n v2).
Proof.
  intros; inv H; simpl; auto.
Qed.

Lemma sign_ext_lessdef:
  forall n v1 v2, lessdef v1 v2 -> lessdef (sign_ext n v1) (sign_ext n v2).
Proof.
  intros; inv H; simpl; auto.
Qed.

Lemma sign_ext_8_alt_lessdef:
  forall v1 v2,
  Val.lessdef v1 v2 ->
  Val.lessdef (sign_ext_8_alt v1) (sign_ext_8_alt v2).
Proof.
  intros; inv H; simpl; auto.
Qed.

Lemma singleoffloat_lessdef:
  forall v1 v2, lessdef v1 v2 -> lessdef (singleoffloat v1) (singleoffloat v2).
Proof.
  intros; inv H; simpl; auto.
Qed.

Lemma add_lessdef:
  forall v1 v1' v2 v2',
  lessdef v1 v1' -> lessdef v2 v2' -> lessdef (add v1 v2) (add v1' v2').
Proof.
  intros. inv H. inv H0. auto. destruct v1'; simpl; auto. simpl; auto.
Qed.

Lemma cmpu_bool_lessdef:
  forall valid_ptr valid_ptr' c v1 v1' v2 v2' b,
  (forall b ofs, valid_ptr b ofs = true -> valid_ptr' b ofs = true) ->
  lessdef v1 v1' -> lessdef v2 v2' ->
  cmpu_bool valid_ptr c v1 v2 = Some b ->
  cmpu_bool valid_ptr' c v1' v2' = Some b.
Proof.
  intros. 
  destruct v1; simpl in H2; try discriminate;
  destruct v2; simpl in H2; try discriminate;
  inv H0; inv H1; simpl; auto.
  destruct (eq_block b0 b1).
  assert (forall b ofs, valid_ptr b ofs || valid_ptr b (ofs - 1) = true ->
                        valid_ptr' b ofs || valid_ptr' b (ofs - 1) = true).
    intros until ofs. rewrite ! orb_true_iff. intuition. 
  destruct (valid_ptr b0 (Int.unsigned i) || valid_ptr b0 (Int.unsigned i - 1)) eqn:?; try discriminate.
  destruct (valid_ptr b1 (Int.unsigned i0) || valid_ptr b1 (Int.unsigned i0 - 1)) eqn:?; try discriminate.
  erewrite !H0 by eauto. auto.
  destruct (valid_ptr b0 (Int.unsigned i)) eqn:?; try discriminate.
  destruct (valid_ptr b1 (Int.unsigned i0)) eqn:?; try discriminate.
  erewrite !H by eauto. auto.
Qed.

Lemma of_optbool_lessdef:
  forall ob ob',
  (forall b, ob = Some b -> ob' = Some b) ->
  lessdef (of_optbool ob) (of_optbool ob').
Proof.
  intros. destruct ob; simpl; auto. rewrite (H b); auto. 
Qed.

Lemma longofwords_lessdef:
  forall v1 v2 v1' v2',
  lessdef v1 v1' -> lessdef v2 v2' -> lessdef (longofwords v1 v2) (longofwords v1' v2').
Proof.
  intros. unfold longofwords. inv H; auto. inv H0; auto. destruct v1'; auto.
Qed.

Lemma loword_lessdef:
  forall v v', lessdef v v' -> lessdef (loword v) (loword v').
Proof.
  intros. inv H; auto. 
Qed.

Lemma hiword_lessdef:
  forall v v', lessdef v v' -> lessdef (hiword v) (hiword v').
Proof.
  intros. inv H; auto. 
Qed.

End Val.

(** * Values and memory injections *)

(** A memory injection [f] is a function from addresses to either [None]
  or [Some] of an address and an offset.  It defines a correspondence
  between the blocks of two memory states [m1] and [m2]:
- if [f b = None], the block [b] of [m1] has no equivalent in [m2];
- if [f b = Some(b', ofs)], the block [b] of [m2] corresponds to
  a sub-block at offset [ofs] of the block [b'] in [m2].
*)

Definition meminj : Type := block -> option (block * Z).

(** A memory injection defines a relation between values that is the
  identity relation, except for pointer values which are shifted
  as prescribed by the memory injection.  Moreover, [Vundef] values
  inject into any other value. *)

Inductive val_inject (mi: meminj): val -> val -> Prop :=
  | val_inject_int:
      forall i, val_inject mi (Vint i) (Vint i)
  | val_inject_long:
      forall i, val_inject mi (Vlong i) (Vlong i)
  | val_inject_float:
      forall f, val_inject mi (Vfloat f) (Vfloat f)
  | val_inject_ptr:
      forall b1 ofs1 b2 ofs2 delta,
      mi b1 = Some (b2, delta) ->
      ofs2 = Int.add ofs1 (Int.repr delta) ->
      val_inject mi (Vptr b1 ofs1) (Vptr b2 ofs2)
  | val_inject_ptrfrag:
      forall b1 ofs1 b2 ofs2 delta i,
      mi b1 = Some (b2, delta) ->
      ofs2 = Int.add ofs1 (Int.repr delta) ->
      val_inject mi (Vptrfrag b1 ofs1 i) (Vptrfrag b2 ofs2 i)
  | val_inject_undef: forall v,
      val_inject mi Vundef v.

Hint Constructors val_inject.

Inductive val_list_inject (mi: meminj): list val -> list val-> Prop:= 
  | val_nil_inject :
      val_list_inject mi nil nil
  | val_cons_inject : forall v v' vl vl' , 
      val_inject mi v v' -> val_list_inject mi vl vl'->
      val_list_inject mi (v :: vl) (v' :: vl').  

Hint Resolve val_nil_inject val_cons_inject.

Section VAL_INJ_OPS.

Variable f: meminj.

Lemma val_load_result_inject:
  forall chunk v1 v2,
  val_inject f v1 v2 ->
  val_inject f (Val.load_result chunk v1) (Val.load_result chunk v2).
Proof.
  intros. inv H; destruct chunk; simpl; econstructor; eauto.
Qed.

Remark val_add_inject:
  forall v1 v1' v2 v2',
  val_inject f v1 v1' ->
  val_inject f v2 v2' ->
  val_inject f (Val.add v1 v2) (Val.add v1' v2').
Proof.
  intros. inv H; inv H0; simpl; econstructor; eauto.
  repeat rewrite Int.add_assoc. decEq. apply Int.add_commut.
  repeat rewrite Int.add_assoc. decEq. apply Int.add_commut.
Qed.

Remark val_sub_inject:
  forall v1 v1' v2 v2',
  val_inject f v1 v1' ->
  val_inject f v2 v2' ->
  val_inject f (Val.sub v1 v2) (Val.sub v1' v2').
Proof.
  intros. inv H; inv H0; simpl; auto.
  econstructor; eauto. rewrite Int.sub_add_l. auto.
  destruct (eq_block b1 b0); auto. subst. rewrite H1 in H. inv H. rewrite dec_eq_true. 
  rewrite Int.sub_shifted. auto.
Qed.

Lemma val_cmp_bool_inject:
  forall c v1 v2 v1' v2' b,
  val_inject f v1 v1' ->
  val_inject f v2 v2' ->
  Val.cmp_bool c v1 v2 = Some b ->
  Val.cmp_bool c v1' v2' = Some b.
Proof.
  intros. inv H; simpl in H1; try discriminate; inv H0; simpl in H1; try discriminate; simpl; auto.
Qed.

Variable (valid_ptr1 valid_ptr2 : block -> Z -> bool).

Let weak_valid_ptr1 b ofs := valid_ptr1 b ofs || valid_ptr1 b (ofs - 1).
Let weak_valid_ptr2 b ofs := valid_ptr2 b ofs || valid_ptr2 b (ofs - 1).

Hypothesis valid_ptr_inj:
  forall b1 ofs b2 delta,
  f b1 = Some(b2, delta) ->
  valid_ptr1 b1 (Int.unsigned ofs) = true ->
  valid_ptr2 b2 (Int.unsigned (Int.add ofs (Int.repr delta))) = true.

Hypothesis weak_valid_ptr_inj:
  forall b1 ofs b2 delta,
  f b1 = Some(b2, delta) ->
  weak_valid_ptr1 b1 (Int.unsigned ofs) = true ->
  weak_valid_ptr2 b2 (Int.unsigned (Int.add ofs (Int.repr delta))) = true.

Hypothesis weak_valid_ptr_no_overflow:
  forall b1 ofs b2 delta,
  f b1 = Some(b2, delta) ->
  weak_valid_ptr1 b1 (Int.unsigned ofs) = true ->
  0 <= Int.unsigned ofs + Int.unsigned (Int.repr delta) <= Int.max_unsigned.

Hypothesis valid_different_ptrs_inj:
  forall b1 ofs1 b2 ofs2 b1' delta1 b2' delta2,
  b1 <> b2 ->
  valid_ptr1 b1 (Int.unsigned ofs1) = true ->
  valid_ptr1 b2 (Int.unsigned ofs2) = true ->
  f b1 = Some (b1', delta1) ->
  f b2 = Some (b2', delta2) ->
  b1' <> b2' \/
  Int.unsigned (Int.add ofs1 (Int.repr delta1)) <> Int.unsigned (Int.add ofs2 (Int.repr delta2)).

Lemma val_cmpu_bool_inject:
  forall c v1 v2 v1' v2' b,
  val_inject f v1 v1' ->
  val_inject f v2 v2' ->
  Val.cmpu_bool valid_ptr1 c v1 v2 = Some b ->
  Val.cmpu_bool valid_ptr2 c v1' v2' = Some b.
Proof.
  Local Opaque Int.add.
  intros. inv H; simpl in H1; try discriminate; inv H0; simpl in H1; try discriminate; simpl; auto.
  fold (weak_valid_ptr1 b1 (Int.unsigned ofs1)) in H1.
  fold (weak_valid_ptr1 b0 (Int.unsigned ofs0)) in H1.
  fold (weak_valid_ptr2 b2 (Int.unsigned (Int.add ofs1 (Int.repr delta)))).
  fold (weak_valid_ptr2 b3 (Int.unsigned (Int.add ofs0 (Int.repr delta0)))). 
  destruct (eq_block b1 b0); subst.
  rewrite H in H2. inv H2. rewrite dec_eq_true.
  destruct (weak_valid_ptr1 b0 (Int.unsigned ofs1)) eqn:?; try discriminate.
  destruct (weak_valid_ptr1 b0 (Int.unsigned ofs0)) eqn:?; try discriminate.
  erewrite !weak_valid_ptr_inj by eauto. simpl.
  rewrite <-H1. simpl. decEq. apply Int.translate_cmpu; eauto.
  destruct (valid_ptr1 b1 (Int.unsigned ofs1)) eqn:?; try discriminate.
  destruct (valid_ptr1 b0 (Int.unsigned ofs0)) eqn:?; try discriminate.
  destruct (eq_block b2 b3); subst.
  assert (valid_ptr_implies: forall b ofs, valid_ptr1 b ofs = true -> weak_valid_ptr1 b ofs = true).
    intros. unfold weak_valid_ptr1. rewrite H0; auto. 
  erewrite !weak_valid_ptr_inj by eauto using valid_ptr_implies. simpl.
  exploit valid_different_ptrs_inj; eauto. intros [?|?]; [congruence |].
  destruct c; simpl in H1; inv H1.
  simpl; decEq. rewrite Int.eq_false; auto. congruence.
  simpl; decEq. rewrite Int.eq_false; auto. congruence.
  now erewrite !valid_ptr_inj by eauto.
Qed.

Lemma val_longofwords_inject:
  forall v1 v2 v1' v2',
  val_inject f v1 v1' -> val_inject f v2 v2' -> val_inject f (Val.longofwords v1 v2) (Val.longofwords v1' v2').
Proof.
  intros. unfold Val.longofwords. inv H; auto. inv H0; auto.
Qed.

Lemma val_loword_inject:
  forall v v', val_inject f v v' -> val_inject f (Val.loword v) (Val.loword v').
Proof.
  intros. unfold Val.loword; inv H; auto. 
Qed.

Lemma val_hiword_inject:
  forall v v', val_inject f v v' -> val_inject f (Val.hiword v) (Val.hiword v').
Proof.
  intros. unfold Val.hiword; inv H; auto. 
Qed.

End VAL_INJ_OPS.

(** Monotone evolution of a memory injection. *)

Definition inject_incr (f1 f2: meminj) : Prop :=
  forall b b' delta, f1 b = Some(b', delta) -> f2 b = Some(b', delta).

Lemma inject_incr_refl :
   forall f , inject_incr f f .
Proof. unfold inject_incr. auto. Qed.

Lemma inject_incr_trans :
  forall f1 f2 f3, 
  inject_incr f1 f2 -> inject_incr f2 f3 -> inject_incr f1 f3 .
Proof.
  unfold inject_incr; intros. eauto. 
Qed.

Lemma val_inject_incr:
  forall f1 f2 v v',
  inject_incr f1 f2 ->
  val_inject f1 v v' ->
  val_inject f2 v v'.
Proof.
  intros. inv H0; econstructor; eauto.
Qed.

Lemma val_list_inject_incr:
  forall f1 f2 vl vl' ,
  inject_incr f1 f2 -> val_list_inject f1 vl vl' ->
  val_list_inject f2 vl vl'.
Proof.
  induction vl; intros; inv H0. auto.
  constructor. eapply val_inject_incr; eauto. auto.
Qed.

Hint Resolve inject_incr_refl val_inject_incr val_list_inject_incr.

(** The identity injection gives rise to the "less defined than" relation. *)

Definition inject_id : meminj := fun b => Some(b, 0).

Lemma val_inject_id:
  forall v1 v2,
  val_inject inject_id v1 v2 <-> Val.lessdef v1 v2.
Proof.
  unfold inject_id. intros; split; intros.
  * inv H; auto. inv H0.
    + rewrite Int.add_zero; auto.
    + inv H0. rewrite Int.add_zero; auto.
  * inv H; auto. destruct v2; econstructor; eauto.
    + rewrite Int.add_zero; auto.
    + rewrite Int.add_zero; auto.
Qed.

Lemma val_list_inject_id:
  forall vl1 vl2, val_list_inject inject_id vl1 vl2 <-> Val.lessdef_list vl1 vl2.
Proof.
  intros; split; induction 1; constructor; try apply val_inject_id; auto.
Qed.

Lemma val_lessdef_inject_compose:
  forall f v1 v2 v3,
  Val.lessdef v1 v2 -> val_inject f v2 v3 -> val_inject f v1 v3.
Proof.
  intros. inv H. auto. auto.
Qed.

Lemma val_inject_lessdef_compose:
  forall f v1 v2 v3,
  val_inject f v1 v2 -> Val.lessdef v2 v3 -> val_inject f v1 v3.
Proof.
  intros. inv H0. auto. inv H. auto.
Qed.

(** Composing two memory injections *)

Definition compose_meminj (f f': meminj) : meminj :=
  fun b =>
    match f b with
    | None => None
    | Some(b', delta) =>
        match f' b' with
        | None => None
        | Some(b'', delta') => Some(b'', delta + delta')
        end
    end.

Lemma val_inject_compose:
  forall f f' v1 v2 v3,
  val_inject f v1 v2 -> val_inject f' v2 v3 ->
  val_inject (compose_meminj f f') v1 v3.
Proof.
  intros. inv H; auto; inv H0; auto.
  * econstructor.
    unfold compose_meminj; rewrite H1; rewrite H3; eauto.
    rewrite Int.add_assoc. decEq. unfold Int.add. apply Int.eqm_samerepr. auto with ints.
  * econstructor.
    unfold compose_meminj; rewrite H1; rewrite H5; eauto.
    rewrite Int.add_assoc. decEq. unfold Int.add. apply Int.eqm_samerepr. auto with ints.
Qed. 
