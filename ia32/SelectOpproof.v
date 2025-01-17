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

(** Correctness of instruction selection for operators *)

Require Import Coqlib.
Require Import AST.
Require Import Integers.
Require Import Floats.
Require Import Values.
Require Import Memory.
Require Import Globalenvs.
Require Import Cminor.
Require Import Op.
Require Import CminorSel.
Require Import SelectOp.

Open Local Scope cminorsel_scope.

(** * Useful lemmas and tactics *)

(** The following are trivial lemmas and custom tactics that help
  perform backward (inversion) and forward reasoning over the evaluation
  of operator applications. *)  

Ltac EvalOp := eapply eval_Eop; eauto with evalexpr.

Ltac InvEval1 :=
  match goal with
  | [ H: (eval_expr _ _ _ _ _ (Eop _ Enil) _) |- _ ] =>
      inv H; InvEval1
  | [ H: (eval_expr _ _ _ _ _ (Eop _ (_ ::: Enil)) _) |- _ ] =>
      inv H; InvEval1
  | [ H: (eval_expr _ _ _ _ _ (Eop _ (_ ::: _ ::: Enil)) _) |- _ ] =>
      inv H; InvEval1
  | [ H: (eval_exprlist _ _ _ _ _ Enil _) |- _ ] =>
      inv H; InvEval1
  | [ H: (eval_exprlist _ _ _ _ _ (_ ::: _) _) |- _ ] =>
      inv H; InvEval1
  | _ =>
      idtac
  end.

Ltac InvEval2 :=
  match goal with
  | [ H: (eval_operation _ _ _ nil _ = Some _) |- _ ] =>
      simpl in H; inv H
  | [ H: (eval_operation _ _ _ (_ :: nil) _ = Some _) |- _ ] =>
      simpl in H; FuncInv
  | [ H: (eval_operation _ _ _ (_ :: _ :: nil) _ = Some _) |- _ ] =>
      simpl in H; FuncInv
  | [ H: (eval_operation _ _ _ (_ :: _ :: _ :: nil) _ = Some _) |- _ ] =>
      simpl in H; FuncInv
  | _ =>
      idtac
  end.

Ltac InvEval := InvEval1; InvEval2; InvEval2.

Ltac TrivialExists :=
  match goal with
  | [ |- exists v, _ /\ Val.lessdef ?a v ] => exists a; split; [EvalOp | auto]
  end.

(** * Correctness of the smart constructors *)

Section CMCONSTR.

Variable ge: genv.
Variable sp: val.
Variable e: env.
Variable m: mem.

(** We now show that the code generated by "smart constructor" functions
  such as [SelectOp.notint] behaves as expected.  Continuing the
  [notint] example, we show that if the expression [e]
  evaluates to some integer value [Vint n], then [SelectOp.notint e]
  evaluates to a value [Vint (Int.not n)] which is indeed the integer
  negation of the value of [e].

  All proofs follow a common pattern:
- Reasoning by case over the result of the classification functions
  (such as [add_match] for integer addition), gathering additional
  information on the shape of the argument expressions in the non-default
  cases.
- Inversion of the evaluations of the arguments, exploiting the additional
  information thus gathered.
- Equational reasoning over the arithmetic operations performed,
  using the lemmas from the [Int] and [Float] modules.
- Construction of an evaluation derivation for the expression returned
  by the smart constructor.
*)

Definition unary_constructor_sound (cstr: expr -> expr) (sem: val -> val) : Prop :=
  forall le a x,
  eval_expr ge sp e m le a x ->
  exists v, eval_expr ge sp e m le (cstr a) v /\ Val.lessdef (sem x) v.

Definition binary_constructor_sound (cstr: expr -> expr -> expr) (sem: val -> val -> val) : Prop :=
  forall le a x b y,
  eval_expr ge sp e m le a x ->
  eval_expr ge sp e m le b y ->
  exists v, eval_expr ge sp e m le (cstr a b) v /\ Val.lessdef (sem x y) v.

Theorem eval_addrsymbol:
  forall le id ofs,
  exists v, eval_expr ge sp e m le (addrsymbol id ofs) v /\ Val.lessdef (symbol_address ge id ofs) v.
Proof.
  intros. unfold addrsymbol. exists (symbol_address ge id ofs); split; auto.
  destruct (symbol_is_external id).
  predSpec Int.eq Int.eq_spec ofs Int.zero.
  subst. EvalOp.
  EvalOp. econstructor. EvalOp. simpl; eauto. econstructor. simpl. 
  unfold symbol_address. destruct (Genv.find_symbol ge id); auto. 
  simpl. rewrite Int.add_commut. rewrite Int.add_zero. auto. 
  EvalOp.
Qed.

Theorem eval_addrstack:
  forall le ofs,
  exists v, eval_expr ge sp e m le (addrstack ofs) v /\ Val.lessdef (Val.add sp (Vint ofs)) v.
Proof.
  intros. unfold addrstack. econstructor; split.
  EvalOp. simpl; eauto. 
  auto.
Qed.

Theorem eval_notint: unary_constructor_sound notint Val.notint.
Proof.
  unfold notint; red; intros. TrivialExists. 
Qed.

Lemma shift_symbol_address:
  forall id ofs n, symbol_address ge id (Int.add ofs n) = Val.add (symbol_address ge id ofs) (Vint n).
Proof.
  intros. unfold symbol_address. destruct (Genv.find_symbol); auto. 
Qed.

Theorem eval_addimm:
  forall n, unary_constructor_sound (addimm n) (fun x => Val.add x (Vint n)).
Proof.
  red; unfold addimm; intros until x.
  predSpec Int.eq Int.eq_spec n Int.zero.
  subst n. intros. exists x; split; auto. 
  destruct x; simpl; auto. rewrite Int.add_zero. auto. rewrite Int.add_zero. auto.
  case (addimm_match a); intros; InvEval; simpl.
  TrivialExists; simpl. rewrite Int.add_commut. auto.
  inv H0. simpl in H6. TrivialExists. simpl. eapply eval_offset_addressing_total; eauto.
  TrivialExists. 
Qed.

Theorem eval_add: binary_constructor_sound add Val.add.
Proof.
  red; intros until y.
  unfold add; case (add_match a b); intros; InvEval.
  rewrite Val.add_commut. apply eval_addimm; auto.
  apply eval_addimm; auto.
  subst. TrivialExists. simpl. rewrite Val.add_permut_4. auto.
  subst. TrivialExists. simpl. rewrite Val.add_assoc. decEq; decEq. rewrite Val.add_permut. auto.
  subst. TrivialExists. simpl. rewrite Val.add_permut_4. rewrite <- Val.add_permut. rewrite <- Val.add_assoc. auto.
  subst. TrivialExists. simpl. rewrite shift_symbol_address. 
    rewrite Val.add_commut. rewrite Val.add_assoc. decEq. decEq. apply Val.add_commut.
  subst. TrivialExists. simpl. rewrite shift_symbol_address. rewrite Val.add_assoc.
    decEq; decEq. apply Val.add_commut.
  subst. TrivialExists. simpl. rewrite shift_symbol_address. rewrite Val.add_commut. 
    rewrite Val.add_assoc. decEq; decEq. apply Val.add_commut.
  subst. TrivialExists. simpl. rewrite shift_symbol_address.
    rewrite Val.add_assoc. decEq; decEq. apply Val.add_commut.
  subst. TrivialExists. simpl. rewrite Val.add_permut. rewrite Val.add_assoc.
    decEq; decEq. apply Val.add_commut.
  subst. TrivialExists.
  subst. TrivialExists. simpl. repeat rewrite Val.add_assoc. decEq; decEq. apply Val.add_commut.
  subst. TrivialExists. simpl. rewrite Val.add_assoc; auto.
  TrivialExists. simpl. destruct x; destruct y; simpl; auto; rewrite Int.add_zero; auto.
Qed.

Theorem eval_sub: binary_constructor_sound sub Val.sub.
Proof.
  red; intros until y.
  unfold sub; case (sub_match a b); intros; InvEval.
  rewrite Val.sub_add_opp. apply eval_addimm; auto.
  subst. rewrite Val.sub_add_l. rewrite Val.sub_add_r. 
    rewrite Val.add_assoc. simpl. rewrite Int.add_commut. rewrite <- Int.sub_add_opp.
    apply eval_addimm; EvalOp.
  subst. rewrite Val.sub_add_l. apply eval_addimm; EvalOp.
  subst. rewrite Val.sub_add_r. apply eval_addimm; EvalOp.
  TrivialExists.
Qed.

Theorem eval_negint: unary_constructor_sound negint (fun v => Val.sub Vzero v).
Proof.
  red; intros. unfold negint. TrivialExists.
Qed.

Theorem eval_shlimm:
  forall n, unary_constructor_sound (fun a => shlimm a n)
                                    (fun x => Val.shl x (Vint n)).
Proof.
  red; intros until x.  unfold shlimm.
  predSpec Int.eq Int.eq_spec n Int.zero.
  intros; subst. exists x; split; auto. destruct x; simpl; auto. rewrite Int.shl_zero; auto.
  destruct (shlimm_match a); intros; InvEval.
  exists (Vint (Int.shl n1 n)); split. EvalOp. 
  simpl. destruct (Int.ltu n Int.iwordsize); auto.
  destruct (Int.ltu (Int.add n n1) Int.iwordsize) eqn:?.
  exists (Val.shl v1 (Vint (Int.add n n1))); split. EvalOp.
  subst. destruct v1; simpl; auto. 
  rewrite Heqb.
  destruct (Int.ltu n1 Int.iwordsize) eqn:?; simpl; auto.
  destruct (Int.ltu n Int.iwordsize) eqn:?; simpl; auto.
  rewrite Int.add_commut. rewrite Int.shl_shl; auto. rewrite Int.add_commut; auto.
  subst. TrivialExists. econstructor. EvalOp. simpl; eauto. constructor. 
  simpl. auto.
  subst. destruct (shift_is_scale n).
  econstructor; split. EvalOp. simpl. eauto.
  destruct v1; simpl; auto. destruct (Int.ltu n Int.iwordsize); auto. 
  rewrite Int.shl_mul. rewrite Int.mul_add_distr_l. rewrite (Int.shl_mul n1). auto.
  TrivialExists. econstructor. EvalOp. simpl; eauto. constructor. auto. 
  destruct (shift_is_scale n).
  econstructor; split. EvalOp. simpl. eauto. 
  destruct x; simpl; auto. destruct (Int.ltu n Int.iwordsize); auto. 
  rewrite Int.add_zero. rewrite Int.shl_mul. auto. 
  TrivialExists.
Qed.

Theorem eval_shruimm:
  forall n, unary_constructor_sound (fun a => shruimm a n)
                                    (fun x => Val.shru x (Vint n)).
Proof.
  red; intros until x.  unfold shruimm.
  predSpec Int.eq Int.eq_spec n Int.zero.
  intros; subst. exists x; split; auto. destruct x; simpl; auto. rewrite Int.shru_zero; auto.
  destruct (shruimm_match a); intros; InvEval.
  exists (Vint (Int.shru n1 n)); split. EvalOp. 
  simpl. destruct (Int.ltu n Int.iwordsize); auto.
  destruct (Int.ltu (Int.add n n1) Int.iwordsize) eqn:?.
  exists (Val.shru v1 (Vint (Int.add n n1))); split. EvalOp.
  subst. destruct v1; simpl; auto. 
  rewrite Heqb.
  destruct (Int.ltu n1 Int.iwordsize) eqn:?; simpl; auto.
  destruct (Int.ltu n Int.iwordsize) eqn:?; simpl; auto.
  rewrite Int.add_commut. rewrite Int.shru_shru; auto. rewrite Int.add_commut; auto.
  subst. TrivialExists. econstructor. EvalOp. simpl; eauto. constructor. 
  simpl. auto.
  TrivialExists.
Qed.

Theorem eval_shrimm:
  forall n, unary_constructor_sound (fun a => shrimm a n)
                                    (fun x => Val.shr x (Vint n)).
Proof.
  red; intros until x.  unfold shrimm.
  predSpec Int.eq Int.eq_spec n Int.zero.
  intros; subst. exists x; split; auto. destruct x; simpl; auto. rewrite Int.shr_zero; auto.
  destruct (shrimm_match a); intros; InvEval.
  exists (Vint (Int.shr n1 n)); split. EvalOp. 
  simpl. destruct (Int.ltu n Int.iwordsize); auto.
  destruct (Int.ltu (Int.add n n1) Int.iwordsize) eqn:?.
  exists (Val.shr v1 (Vint (Int.add n n1))); split. EvalOp.
  subst. destruct v1; simpl; auto. 
  rewrite Heqb.
  destruct (Int.ltu n1 Int.iwordsize) eqn:?; simpl; auto.
  destruct (Int.ltu n Int.iwordsize) eqn:?; simpl; auto.
  rewrite Int.add_commut. rewrite Int.shr_shr; auto. rewrite Int.add_commut; auto.
  subst. TrivialExists. econstructor. EvalOp. simpl; eauto. constructor. 
  simpl. auto.
  TrivialExists.
Qed.

Lemma eval_mulimm_base:
  forall n, unary_constructor_sound (mulimm_base n) (fun x => Val.mul x (Vint n)).
Proof.
  intros; red; intros; unfold mulimm_base. 
  generalize (Int.one_bits_decomp n). 
  generalize (Int.one_bits_range n).
  destruct (Int.one_bits n).
  intros. TrivialExists. 
  destruct l.
  intros. rewrite H1. simpl. 
  rewrite Int.add_zero.
  replace (Vint (Int.shl Int.one i)) with (Val.shl Vone (Vint i)). rewrite Val.shl_mul.
  apply eval_shlimm. auto. simpl. rewrite H0; auto with coqlib.
  destruct l.
  intros. rewrite H1. simpl.
  exploit (eval_shlimm i (x :: le) (Eletvar 0) x). constructor; auto. intros [v1 [A1 B1]].
  exploit (eval_shlimm i0 (x :: le) (Eletvar 0) x). constructor; auto. intros [v2 [A2 B2]].
  exploit eval_add. eexact A1. eexact A2. intros [v3 [A3 B3]].
  exists v3; split. econstructor; eauto. 
  rewrite Int.add_zero.
  replace (Vint (Int.add (Int.shl Int.one i) (Int.shl Int.one i0)))
     with (Val.add (Val.shl Vone (Vint i)) (Val.shl Vone (Vint i0))).
  rewrite Val.mul_add_distr_r.
  repeat rewrite Val.shl_mul. 
  apply Val.lessdef_trans with (Val.add v1 v2); auto. apply Val.add_lessdef; auto. 
  simpl. repeat rewrite H0; auto with coqlib. 
  intros. TrivialExists. 
Qed.

Theorem eval_mulimm:
  forall n, unary_constructor_sound (mulimm n) (fun x => Val.mul x (Vint n)).
Proof.
  intros; red; intros until x; unfold mulimm.
  predSpec Int.eq Int.eq_spec n Int.zero. 
  intros. exists (Vint Int.zero); split. EvalOp. 
  destruct x; simpl; auto. subst n. rewrite Int.mul_zero. auto.
  predSpec Int.eq Int.eq_spec n Int.one.
  intros. exists x; split; auto.
  destruct x; simpl; auto. subst n. rewrite Int.mul_one. auto.
  case (mulimm_match a); intros; InvEval.
  TrivialExists. simpl. rewrite Int.mul_commut; auto.
  subst. rewrite Val.mul_add_distr_l. 
  exploit eval_mulimm_base; eauto. instantiate (1 := n). intros [v' [A1 B1]].
  exploit (eval_addimm (Int.mul n n2) le (mulimm_base n t2) v'). auto. intros [v'' [A2 B2]].
  exists v''; split; auto. eapply Val.lessdef_trans. eapply Val.add_lessdef; eauto. 
  rewrite Val.mul_commut; auto.
  apply eval_mulimm_base; auto.
Qed.

Theorem eval_mul: binary_constructor_sound mul Val.mul.
Proof.
  red; intros until y.
  unfold mul; case (mul_match a b); intros; InvEval.
  rewrite Val.mul_commut. apply eval_mulimm. auto. 
  apply eval_mulimm. auto.
  TrivialExists.
Qed.

Theorem eval_andimm:
  forall n, unary_constructor_sound (andimm n) (fun x => Val.and x (Vint n)).
Proof.
  intros; red; intros until x. unfold andimm.
  predSpec Int.eq Int.eq_spec n Int.zero. 
  intros. exists (Vint Int.zero); split. EvalOp. 
  destruct x; simpl; auto. subst n. rewrite Int.and_zero. auto.
  predSpec Int.eq Int.eq_spec n Int.mone.
  intros. exists x; split; auto.
  destruct x; simpl; auto. subst n. rewrite Int.and_mone. auto.
  case (andimm_match a); intros; InvEval.
  TrivialExists. simpl. rewrite Int.and_commut; auto.
  subst. TrivialExists. simpl. rewrite Val.and_assoc. rewrite Int.and_commut. auto.
  subst. rewrite Val.zero_ext_and. TrivialExists. rewrite Val.and_assoc. 
  rewrite Int.and_commut. auto. compute; auto.
  subst. rewrite Val.zero_ext_and. TrivialExists. rewrite Val.and_assoc. 
  rewrite Int.and_commut. auto. compute; auto.
  TrivialExists.
Qed.

Theorem eval_and: binary_constructor_sound and Val.and.
Proof.
  red; intros until y; unfold and; case (and_match a b); intros; InvEval.
  rewrite Val.and_commut. apply eval_andimm; auto.
  apply eval_andimm; auto.
  TrivialExists.
Qed.

Theorem eval_orimm:
  forall n, unary_constructor_sound (orimm n) (fun x => Val.or x (Vint n)).
Proof.
  intros; red; intros until x. unfold orimm.
  predSpec Int.eq Int.eq_spec n Int.zero. 
  intros. exists x; split. auto.  
  destruct x; simpl; auto. subst n. rewrite Int.or_zero. auto.
  predSpec Int.eq Int.eq_spec n Int.mone.
  intros. exists (Vint Int.mone); split. EvalOp.
  destruct x; simpl; auto. subst n. rewrite Int.or_mone. auto.
  destruct (orimm_match a); intros; InvEval.
  TrivialExists. simpl. rewrite Int.or_commut; auto.
  subst. rewrite Val.or_assoc. simpl. rewrite Int.or_commut. TrivialExists. 
  TrivialExists.
Qed.

Remark eval_same_expr:
  forall a1 a2 le v1 v2,
  same_expr_pure a1 a2 = true ->
  eval_expr ge sp e m le a1 v1 ->
  eval_expr ge sp e m le a2 v2 ->
  a1 = a2 /\ v1 = v2.
Proof.
  intros until v2.
  destruct a1; simpl; try (intros; discriminate). 
  destruct a2; simpl; try (intros; discriminate).
  case (ident_eq i i0); intros.
  subst i0. inversion H0. inversion H1. split. auto. congruence. 
  discriminate.
Qed.

Remark int_add_sub_eq:
  forall x y z, Int.add x y = z -> Int.sub z x = y.
Proof.
  intros. subst z. rewrite Int.sub_add_l. rewrite Int.sub_idem. apply Int.add_zero_l.
Qed.

Lemma eval_or: binary_constructor_sound or Val.or.
Proof.
  red; intros until y; unfold or; case (or_match a b); intros.
(* intconst *)
  InvEval. rewrite Val.or_commut. apply eval_orimm; auto. 
  InvEval. apply eval_orimm; auto.
(* shlimm - shruimm *)
  predSpec Int.eq Int.eq_spec (Int.add n1 n2) Int.iwordsize.
  destruct (same_expr_pure t1 t2) eqn:?.
  InvEval. exploit eval_same_expr; eauto. intros [EQ1 EQ2]; subst. 
  exists (Val.ror v0 (Vint n2)); split. EvalOp.
  destruct v0; simpl; auto. 
  destruct (Int.ltu n1 Int.iwordsize) eqn:?; auto.
  destruct (Int.ltu n2 Int.iwordsize) eqn:?; auto.
  simpl. rewrite <- Int.or_ror; auto.
  InvEval. exists (Val.or x y); split. EvalOp. 
  simpl. erewrite int_add_sub_eq; eauto. rewrite H0; rewrite H; auto. auto.
  TrivialExists. 
(* shruimm - shlimm *) 
  predSpec Int.eq Int.eq_spec (Int.add n1 n2) Int.iwordsize.
  destruct (same_expr_pure t1 t2) eqn:?.
  InvEval. exploit eval_same_expr; eauto. intros [EQ1 EQ2]; subst. 
  exists (Val.ror v1 (Vint n2)); split. EvalOp.
  destruct v1; simpl; auto. 
  destruct (Int.ltu n2 Int.iwordsize) eqn:?; auto.
  destruct (Int.ltu n1 Int.iwordsize) eqn:?; auto.
  simpl. rewrite Int.or_commut. rewrite <- Int.or_ror; auto.
  InvEval. exists (Val.or y x); split. EvalOp. 
  simpl. erewrite int_add_sub_eq; eauto. rewrite H0; rewrite H; auto.
  rewrite Val.or_commut; auto.
  TrivialExists. 
(* default *)
  TrivialExists.
Qed.

Theorem eval_xorimm:
  forall n, unary_constructor_sound (xorimm n) (fun x => Val.xor x (Vint n)).
Proof.
  intros; red; intros until x. unfold xorimm.
  predSpec Int.eq Int.eq_spec n Int.zero. 
  intros. exists x; split. auto.  
  destruct x; simpl; auto. subst n. rewrite Int.xor_zero. auto.
  destruct (xorimm_match a); intros; InvEval.
  TrivialExists. simpl. rewrite Int.xor_commut; auto.
  subst. rewrite Val.xor_assoc. simpl. rewrite Int.xor_commut. TrivialExists. 
  TrivialExists.
Qed.

Theorem eval_xor: binary_constructor_sound xor Val.xor.
Proof.
  red; intros until y; unfold xor; case (xor_match a b); intros; InvEval.
  rewrite Val.xor_commut. apply eval_xorimm; auto.
  apply eval_xorimm; auto.
  TrivialExists.
Qed.

Theorem eval_divs_base:
  forall le a b x y z,
  eval_expr ge sp e m le a x ->
  eval_expr ge sp e m le b y ->
  Val.divs x y = Some z ->
  exists v, eval_expr ge sp e m le (divs_base a b) v /\ Val.lessdef z v.
Proof.
  intros. unfold divs_base. exists z; split. EvalOp. auto.
Qed.

Theorem eval_divu_base:
  forall le a b x y z,
  eval_expr ge sp e m le a x ->
  eval_expr ge sp e m le b y ->
  Val.divu x y = Some z ->
  exists v, eval_expr ge sp e m le (divu_base a b) v /\ Val.lessdef z v.
Proof.
  intros. unfold divu_base. exists z; split. EvalOp. auto.
Qed.

Theorem eval_mods_base:
  forall le a b x y z,
  eval_expr ge sp e m le a x ->
  eval_expr ge sp e m le b y ->
  Val.mods x y = Some z ->
  exists v, eval_expr ge sp e m le (mods_base a b) v /\ Val.lessdef z v.
Proof.
  intros. unfold mods_base. exists z; split. EvalOp. auto.
Qed.

Theorem eval_modu_base:
  forall le a b x y z,
  eval_expr ge sp e m le a x ->
  eval_expr ge sp e m le b y ->
  Val.modu x y = Some z ->
  exists v, eval_expr ge sp e m le (modu_base a b) v /\ Val.lessdef z v.
Proof.
  intros. unfold modu_base. exists z; split. EvalOp. auto.
Qed.

Theorem eval_shrximm:
  forall le a n x z,
  eval_expr ge sp e m le a x ->
  Val.shrx x (Vint n) = Some z ->
  exists v, eval_expr ge sp e m le (shrximm a n) v /\ Val.lessdef z v.
Proof.
  intros. unfold shrximm. 
  predSpec Int.eq Int.eq_spec n Int.zero.
  subst n. exists x; split; auto. 
  destruct x; simpl in H0; try discriminate.
  destruct (Int.ltu Int.zero (Int.repr 31)); inv H0.
  replace (Int.shrx i Int.zero) with i. auto. 
  unfold Int.shrx, Int.divs. rewrite Int.shl_zero. 
  change (Int.signed Int.one) with 1. rewrite Z.quot_1_r. rewrite Int.repr_signed; auto.
  econstructor; split. EvalOp. auto.
Qed.

Theorem eval_shl: binary_constructor_sound shl Val.shl.
Proof.
  red; intros until y; unfold shl; case (shl_match b); intros.
  InvEval. apply eval_shlimm; auto.
  TrivialExists. 
Qed.

Theorem eval_shr: binary_constructor_sound shr Val.shr.
Proof.
  red; intros until y; unfold shr; case (shr_match b); intros.
  InvEval. apply eval_shrimm; auto.
  TrivialExists. 
Qed.

Theorem eval_shru: binary_constructor_sound shru Val.shru.
Proof.
  red; intros until y; unfold shru; case (shru_match b); intros.
  InvEval. apply eval_shruimm; auto.
  TrivialExists. 
Qed.

Theorem eval_negf: unary_constructor_sound negf Val.negf.
Proof.
  red; intros. TrivialExists. 
Qed.

Theorem eval_absf: unary_constructor_sound absf Val.absf.
Proof.
  red; intros. TrivialExists. 
Qed.

Theorem eval_addf: binary_constructor_sound addf Val.addf.
Proof.
  red; intros; TrivialExists.
Qed.
 
Theorem eval_subf: binary_constructor_sound subf Val.subf.
Proof.
  red; intros; TrivialExists.
Qed.

Theorem eval_mulf: binary_constructor_sound mulf Val.mulf.
Proof.
  red; intros; TrivialExists.
Qed.

Theorem eval_divf: binary_constructor_sound divf Val.divf.
Proof.
  red. intros until y. unfold divf. destruct (divf_match b); intros.
- unfold divfimm. destruct (Float.exact_inverse n2) as [n2' | ] eqn:EINV.
  + inv H0. inv H4. simpl in H6. inv H6. econstructor; split.
    EvalOp. constructor. eauto. constructor. EvalOp. simpl; eauto. constructor. 
    simpl; eauto. 
    destruct x; simpl; auto. erewrite Float.div_mul_inverse; eauto. 
  + TrivialExists. 
- TrivialExists.
Qed.

Section COMP_IMM.

Variable default: comparison -> int -> condition.
Variable intsem: comparison -> int -> int -> bool.
Variable sem: comparison -> val -> val -> val.

Hypothesis sem_int: forall c x y, sem c (Vint x) (Vint y) = Val.of_bool (intsem c x y).
Hypothesis sem_undef: forall c v, sem c Vundef v = Vundef.
Hypothesis sem_eq: forall x y, sem Ceq (Vint x) (Vint y) = Val.of_bool (Int.eq x y).
Hypothesis sem_ne: forall x y, sem Cne (Vint x) (Vint y) = Val.of_bool (negb (Int.eq x y)).
Hypothesis sem_default: forall c v n, sem c v (Vint n) = Val.of_optbool (eval_condition (default c n) (v :: nil) m).

Lemma eval_compimm:
  forall le c a n2 x,
  eval_expr ge sp e m le a x ->
  exists v, eval_expr ge sp e m le (compimm default intsem c a n2) v
         /\ Val.lessdef (sem c x (Vint n2)) v.
Proof.
  intros until x.
  unfold compimm; case (compimm_match c a); intros.
(* constant *)
  InvEval. rewrite sem_int. TrivialExists. simpl. destruct (intsem c0 n1 n2); auto.
(* eq cmp *)
  InvEval. inv H. simpl in H5. inv H5. 
  destruct (Int.eq_dec n2 Int.zero). subst n2. TrivialExists. 
  simpl. rewrite eval_negate_condition.
  destruct (eval_condition c0 vl m); simpl.
  unfold Vtrue, Vfalse. destruct b; simpl; rewrite sem_eq; auto.
  rewrite sem_undef; auto.
  destruct (Int.eq_dec n2 Int.one). subst n2. TrivialExists.
  simpl. destruct (eval_condition c0 vl m); simpl.
  unfold Vtrue, Vfalse. destruct b; simpl; rewrite sem_eq; auto.
  rewrite sem_undef; auto.
  exists (Vint Int.zero); split. EvalOp. 
  destruct (eval_condition c0 vl m); simpl.
  unfold Vtrue, Vfalse. destruct b; rewrite sem_eq; rewrite Int.eq_false; auto.
  rewrite sem_undef; auto.
(* ne cmp *)
  InvEval. inv H. simpl in H5. inv H5. 
  destruct (Int.eq_dec n2 Int.zero). subst n2. TrivialExists. 
  simpl. destruct (eval_condition c0 vl m); simpl.
  unfold Vtrue, Vfalse. destruct b; simpl; rewrite sem_ne; auto.
  rewrite sem_undef; auto.
  destruct (Int.eq_dec n2 Int.one). subst n2. TrivialExists.
  simpl. rewrite eval_negate_condition. destruct (eval_condition c0 vl m); simpl.
  unfold Vtrue, Vfalse. destruct b; simpl; rewrite sem_ne; auto.
  rewrite sem_undef; auto.
  exists (Vint Int.one); split. EvalOp. 
  destruct (eval_condition c0 vl m); simpl.
  unfold Vtrue, Vfalse. destruct b; rewrite sem_ne; rewrite Int.eq_false; auto.
  rewrite sem_undef; auto.
(* eq andimm *)
  destruct (Int.eq_dec n2 Int.zero). InvEval; subst.
  econstructor; split. EvalOp. simpl; eauto. 
  destruct v1; simpl; try (rewrite sem_undef; auto). rewrite sem_eq. 
  destruct (Int.eq (Int.and i n1) Int.zero); auto. 
  TrivialExists. simpl. rewrite sem_default. auto.
(* ne andimm *)
  destruct (Int.eq_dec n2 Int.zero). InvEval; subst.
  econstructor; split. EvalOp. simpl; eauto. 
  destruct v1; simpl; try (rewrite sem_undef; auto). rewrite sem_ne. 
  destruct (Int.eq (Int.and i n1) Int.zero); auto. 
  TrivialExists. simpl. rewrite sem_default. auto.
(* default *)
  TrivialExists. simpl. rewrite sem_default. auto.
Qed.

Hypothesis sem_swap:
  forall c x y, sem (swap_comparison c) x y = sem c y x.

Lemma eval_compimm_swap:
  forall le c a n2 x,
  eval_expr ge sp e m le a x ->
  exists v, eval_expr ge sp e m le (compimm default intsem (swap_comparison c) a n2) v
         /\ Val.lessdef (sem c (Vint n2) x) v.
Proof.
  intros. rewrite <- sem_swap. eapply eval_compimm; eauto. 
Qed.

End COMP_IMM.

Theorem eval_comp:
  forall c, binary_constructor_sound (comp c) (Val.cmp c).
Proof.
  intros; red; intros until y. unfold comp; case (comp_match a b); intros; InvEval.
  eapply eval_compimm_swap; eauto. 
  intros. unfold Val.cmp. rewrite Val.swap_cmp_bool; auto.
  eapply eval_compimm; eauto. 
  TrivialExists.
Qed.

Theorem eval_compu:
  forall c, binary_constructor_sound (compu c) (Val.cmpu (Mem.valid_pointer m) c).
Proof.
  intros; red; intros until y. unfold compu; case (compu_match a b); intros; InvEval.
  eapply eval_compimm_swap; eauto. 
  intros. unfold Val.cmpu. rewrite Val.swap_cmpu_bool; auto.
  eapply eval_compimm; eauto. 
  TrivialExists.
Qed.

Theorem eval_compf:
  forall c, binary_constructor_sound (compf c) (Val.cmpf c).
Proof.
  intros; red; intros. unfold compf. TrivialExists.
Qed.

Theorem eval_cast8signed: unary_constructor_sound cast8signed (Val.sign_ext 8).
Proof.
  red; intros. unfold cast8signed. TrivialExists.
Qed.

Theorem eval_cast8unsigned: unary_constructor_sound cast8unsigned (Val.zero_ext 8).
Proof.
  red; intros until x. unfold cast8unsigned. destruct (cast8unsigned_match a); intros; InvEval.
  subst. rewrite Val.zero_ext_and. rewrite Val.and_assoc. 
  rewrite Int.and_commut. TrivialExists. compute; auto.
  TrivialExists.
Qed.

Theorem eval_cast16signed: unary_constructor_sound cast16signed (Val.sign_ext 16).
Proof.
  red; intros. unfold cast16signed. TrivialExists.
Qed.

Theorem eval_cast16unsigned: unary_constructor_sound cast16unsigned (Val.zero_ext 16).
Proof.
  red; intros until x. unfold cast16unsigned. destruct (cast16unsigned_match a); intros; InvEval.
  subst. rewrite Val.zero_ext_and. rewrite Val.and_assoc. 
  rewrite Int.and_commut. TrivialExists. compute; auto.
  TrivialExists.
Qed.

Theorem eval_singleoffloat: unary_constructor_sound singleoffloat Val.singleoffloat.
Proof.
  red; intros. unfold singleoffloat. TrivialExists.
Qed.

Theorem eval_intoffloat:
  forall le a x y,
  eval_expr ge sp e m le a x ->
  Val.intoffloat x = Some y ->
  exists v, eval_expr ge sp e m le (intoffloat a) v /\ Val.lessdef y v.
Proof.
  intros; unfold intoffloat. TrivialExists. 
Qed.

Theorem eval_floatofint:
  forall le a x y,
  eval_expr ge sp e m le a x ->
  Val.floatofint x = Some y ->
  exists v, eval_expr ge sp e m le (floatofint a) v /\ Val.lessdef y v.
Proof.
  intros; unfold floatofint. TrivialExists. 
Qed.

Theorem eval_intuoffloat:
  forall le a x y,
  eval_expr ge sp e m le a x ->
  Val.intuoffloat x = Some y ->
  exists v, eval_expr ge sp e m le (intuoffloat a) v /\ Val.lessdef y v.
Proof.
  intros. destruct x; simpl in H0; try discriminate.
  destruct (Float.intuoffloat f) as [n|] eqn:?; simpl in H0; inv H0.
  exists (Vint n); split; auto. unfold intuoffloat.
  set (im := Int.repr Int.half_modulus).
  set (fm := Float.floatofintu im).
  assert (eval_expr ge sp e m (Vfloat fm :: Vfloat f :: le) (Eletvar (S O)) (Vfloat f)).
    constructor. auto.
  assert (eval_expr ge sp e m (Vfloat fm :: Vfloat f :: le) (Eletvar O) (Vfloat fm)).
    constructor. auto.
  econstructor. eauto.
  econstructor. instantiate (1 := Vfloat fm). EvalOp. 
  eapply eval_Econdition with (va := Float.cmp Clt f fm).
  eauto with evalexpr.
  destruct (Float.cmp Clt f fm) eqn:?.
  exploit Float.intuoffloat_intoffloat_1; eauto. intro EQ.
  EvalOp. simpl. rewrite EQ; auto.
  exploit Float.intuoffloat_intoffloat_2; eauto. 
  change Float.ox8000_0000 with im. fold fm. intro EQ.
  set (t2 := subf (Eletvar (S O)) (Eletvar O)).
  set (t3 := intoffloat t2).
  exploit (eval_subf (Vfloat fm :: Vfloat f :: le) (Eletvar (S O)) (Vfloat f) (Eletvar O)); eauto.
  fold t2. intros [v2 [A2 B2]]. simpl in B2. inv B2. 
  exploit (eval_addimm Float.ox8000_0000 (Vfloat fm :: Vfloat f :: le) t3).
    unfold t3. unfold intoffloat. EvalOp. simpl. rewrite EQ. simpl. eauto. 
  intros [v4 [A4 B4]]. simpl in B4. inv B4. 
  rewrite Int.sub_add_opp in A4. rewrite Int.add_assoc in A4. 
  rewrite (Int.add_commut (Int.neg im)) in A4. 
  rewrite Int.add_neg_zero in A4. 
  rewrite Int.add_zero in A4.
  auto.
Qed.

Theorem eval_floatofintu:
  forall le a x y,
  eval_expr ge sp e m le a x ->
  Val.floatofintu x = Some y ->
  exists v, eval_expr ge sp e m le (floatofintu a) v /\ Val.lessdef y v.
Proof.
  intros. destruct x; simpl in H0; try discriminate. inv H0.
  exists (Vfloat (Float.floatofintu i)); split; auto.
  econstructor. eauto. 
  set (fm := Float.floatofintu Float.ox8000_0000).
  assert (eval_expr ge sp e m (Vint i :: le) (Eletvar O) (Vint i)).
    constructor. auto. 
  eapply eval_Econdition with (va := Int.ltu i Float.ox8000_0000).
  eauto with evalexpr.
  destruct (Int.ltu i Float.ox8000_0000) eqn:?.
  rewrite Float.floatofintu_floatofint_1; auto.
  unfold floatofint. EvalOp. 
  exploit (eval_addimm (Int.neg Float.ox8000_0000) (Vint i :: le) (Eletvar 0)); eauto.
  simpl. intros [v [A B]]. inv B. 
  unfold addf. EvalOp. 
  constructor. unfold floatofint. EvalOp. simpl; eauto. 
  constructor. EvalOp. simpl; eauto. constructor. simpl; eauto. 
  fold fm. rewrite Float.floatofintu_floatofint_2; auto.
  rewrite Int.sub_add_opp. auto.
Qed.

Theorem eval_addressing:
  forall le chunk a v b ofs,
  eval_expr ge sp e m le a v ->
  v = Vptr b ofs ->
  match addressing chunk a with (mode, args) =>
    exists vl,
    eval_exprlist ge sp e m le args vl /\ 
    eval_addressing ge sp mode vl = Some v
  end.
Proof.
  intros until v. unfold addressing; case (addressing_match a); intros; InvEval.
  inv H. exists vl; auto.
  exists (v :: nil); split. constructor; auto. constructor. subst; simpl. rewrite Int.add_zero; auto. 
Qed.

End CMCONSTR.
