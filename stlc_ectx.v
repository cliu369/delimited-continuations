(*
CBV STLC using small-step with evaluation contexts
and de Bruijn indices.

Evaluation contexts are in the style of
https://julesjacobs.com/notes/functionalctxs/functionalctxs.pdf
*)

Require Import Stdlib.Lists.List.
From Stdlib Require Import Psatz.
Require Import Stdlib.Arith.Compare_dec.
From Stdlib Require Import Arith.PeanoNat.
Require Import Stdlib.Arith.Peano_dec.
Require Import Stdlib.Bool.Bool.
From Stdlib Require Import FunctionalExtensionality.
From Stdlib Require Import PropExtensionality.

Import ListNotations.

Require Import tactics.
Require Import env.

Module STLC_ECTX.

Definition id := nat.

Inductive ty : Type := 
  | TBool : ty 
  | TFun  : ty -> ty -> ty
.

Inductive tm : Type :=
  | ttrue : tm
  | tfalse : tm
  | tvar : id -> tm
  | tapp : tm -> tm -> tm
  | tabs : tm -> tm
  | tif : tm -> tm -> tm -> tm
.

Inductive value: tm -> Prop := 
  | vabs : forall t,
    value (tabs t)
  | vtrue : 
    value ttrue
  | vfalse : 
    value tfalse
.

(* Shift term t by d with cutoff c *)
Fixpoint shift (t: tm) (c: nat) (d: nat): tm := 
  match t with 
  | ttrue => ttrue 
  | tfalse => tfalse
  | tvar n => if (c <=? n) then tvar (n + d) else tvar n 
  | tabs t => tabs (shift t (c + 1) d)
  | tapp t1 t2 => tapp (shift t1 c d) (shift t2 c d)
  | tif t1 t2 t3 => tif (shift t1 c d) (shift t2 c d) (shift t3 c d)
  end
.

(* t[j |-> s], e.g. substituting s for j in t *)
Fixpoint subst (t: tm) (j: nat) (s: tm)  : tm := 
  match t with 
  | ttrue => ttrue
  | tfalse => tfalse
  | tvar n => 
      if j =? n then s 
      else if j <? n then tvar (n - 1)
      else tvar n
  | tabs t => tabs (subst (t) (j + 1) (shift s 0 1))
  | tapp t1 t2 => tapp (subst t1 j s) (subst t2 j s)
  | tif t1 t2 t3 => tif (subst t1 j s) (subst t2 j s) (subst t3 j s) 
  end
.

(* Evaluation Contexts *)
Inductive ctx : (tm -> tm) -> Prop :=
  | ctx_if : forall tbranch ebranch, 
    ctx (fun x => tif x tbranch ebranch)
  | ctx_app_l : forall t2,
    ctx (fun x => tapp x t2)
  | ctx_app_r : forall t1,
    value t1 -> 
    ctx (fun x => tapp t1 x)
.

Inductive step : tm -> tm -> Prop := 
  | step_app : forall t v,
    value v ->
    step (tapp (tabs t) v) (subst t 0 v)
  | step_if_t : forall tbranch ebranch,
    step (tif ttrue tbranch ebranch) (tbranch)
  | step_if_f : forall tbranch ebranch,
    step (tif tfalse tbranch ebranch) (ebranch)
  | step_ctx : forall t1 t2 C,
    ctx C -> 
    step t1 t2 -> 
    step (C t1) (C t2)
.

Inductive stepn : tm -> tm -> Prop :=
  | step_refl : forall t,
    stepn t t
  | step_multi : forall t1 t2 t3,
    stepn t1 t2 -> 
    step t2 t3 -> 
    stepn t1 t3
.

Definition tenv := list ty.

Inductive has_type: tenv -> tm -> ty -> Prop := 
| t_true: forall env,
    has_type env ttrue TBool
| t_false: forall env,
    has_type env tfalse TBool
| t_var: forall x env T,
    indexl x env = Some T ->
    has_type env (tvar x) T
| t_app: forall env f t T1 T2,
    has_type env f (TFun T1 T2) ->
    has_type env t T1 ->
    has_type env (tapp f t) T2
| t_abs: forall env t T1 T2,
    has_type (T1 :: env) t T2 -> 
    has_type env (tabs t) (TFun T1 T2)
.

#[global] Hint Unfold tenv : core. 
#[export] Hint Constructors ty: core.
#[export] Hint Constructors tm: core.
#[export] Hint Constructors value: core.

#[export] Hint Constructors has_type: core.
#[export] Hint Constructors step: core.

#[export] Hint Constructors option: core.
#[export] Hint Constructors list: core.


Lemma multi_trans : forall t1 t2 t3, 
  stepn t1 t2 -> 
  stepn t2 t3 -> 
  stepn t1 t3.
Proof.
  intros t1 t2 t3 H12 H23. generalize dependent t1. induction H23.
  - intros. assumption.
  - intros t4 H34. specialize IHstepn with t4. apply IHstepn in H34.
    apply step_multi with (t2 := t2); auto.
Qed.

(* ---------- proof of progress ---------- *)
Lemma canonical_forms_bool : forall env t,
  has_type env t TBool ->
  value t -> 
  (t = ttrue) \/ (t = tfalse).
Proof.
  intros env t HT HV. destruct HV; auto.
  inversion HT.
Qed.

Lemma canonical_forms_fun : forall env t T1 T2,
  has_type env t (TFun T1 T2) -> 
  value t -> 
  exists t', t = tabs t'.
Proof.
  intros env t T1 T2 HT HV. destruct HV.
  - exists t. reflexivity.
  - inversion HT.
  - inversion HT.     
Qed.

Theorem progress : forall t T, 
  has_type [] t T -> 
  value t \/ exists t', step t t'.
Proof.
  intros t T H. remember [] as env. induction H; auto.
  - subst. destruct x; inversion H.
  - subst. destruct (IHhas_type1); destruct (IHhas_type2); 
    (try reflexivity); clear IHhas_type1; clear IHhas_type2; right.
    + apply canonical_forms_fun in H; auto. 
      destruct H as (t' & HF). subst. exists (subst t' 0 t). auto.
    + destruct H2 as (t' & HT). exists (tapp f t').
      apply step_ctx; auto. apply ctx_app_r. apply H1.
    + destruct H1 as (f' & HF). exists (tapp f' t). 
      apply (step_ctx f f' (fun x => tapp x t)); auto.
      apply ctx_app_l.
    + destruct H1 as (f' & HF). exists (tapp f' t).
      apply (step_ctx f f' (fun x => tapp x t)); auto.
      apply ctx_app_l.
Qed.

(* ---------- proof of preservation ---------- *)
Lemma weakening : forall env env' t T,
  has_type env t T -> 
  has_type (env ++ env') t T.
Proof.
  intros env env' t T H. generalize dependent env'. induction H; intros env'; auto.
  - apply t_var. apply indexl_extend. apply H.
  - eapply t_app; eauto.
  - apply t_abs. apply IHhas_type.
Qed.   

Lemma weakening_empty : forall t T env,
  has_type [] t T -> 
  has_type env t T.
Proof.
  intros t T env H. replace (env) with ([] ++ env) by auto.
  apply weakening. apply H.
Qed.

Lemma shift_unchanged : forall env t T d,
  has_type env t T -> 
  has_type env (shift t (length env) d) T.
Proof.
  intros env t T d H. generalize dependent d. 
  induction H; simpl; auto; intros d.
  - bdestruct (length env <=? x); auto. apply indexl_var_none in H0.
    rewrite H in H0. inversion H0.
  - econstructor; eauto.
  - apply t_abs. simpl in IHhas_type. 
    replace (length env + 1) with (S (length env)) by lia. apply IHhas_type.
Qed.

Lemma substitution : forall env env' U t v T,
  has_type (env' ++ [U] ++ env) t T -> 
  has_type [] v U -> 
  has_type (env' ++ env) (subst t (length env') v) T.
Proof.
  intros env env' U t. generalize dependent U. generalize
  dependent env'. generalize dependent env. induction t; 
  intros env env' U v T HT HU.
  - simpl. inversion HT. constructor.
  - simpl. inversion HT. constructor.
  - inversion HT; subst. simpl. bdestruct (length env' =? i).
    + rewrite <- H in H1. 
      replace (env' ++ [U] ++ env) with (env' ++ U :: env) in H1 by reflexivity.
      rewrite indexl_insert in H1. inversion H1. subst. apply weakening_empty.
      apply HU. 
    + bdestruct (length env' <? i).
      * clear H. rename H0 into H. apply t_var. 
        assert (length env' <= i - 1) by lia. 
        apply indexl_mid with (l2 := [U]) (l3 := env) in H0.
        rewrite H0. simpl. replace (i - 1 + 1) with (i) by lia.
        apply H1.  
      * assert (length env' > i) by lia. clear H H0. 
        apply indexl_left with (l2 := [U]) (l3 := env) in H2. 
        apply t_var. rewrite H2. apply H1. 
  - simpl. inversion HT; subst. econstructor; eauto. 
  - simpl. inversion HT; subst. apply t_abs. 
    replace (length env' + 1) with (length (T1 :: env')) by (simpl; lia).
    replace (T1 :: env' ++ env) with ((T1 :: env') ++ env) by auto.
    apply IHt with (U := U); auto. apply shift_unchanged. apply HU.
  - simpl. inversion HT.
Qed. 

Lemma substitution' : forall env U t v T, 
  has_type (U :: env) t T -> 
  has_type [] v U -> 
  has_type env (subst t 0 v) T.
Proof.
  intros env U t v T.
  replace (U :: env) with ([] ++ [U] ++ env) by auto. 
  apply substitution.
Qed.

Theorem preservation : forall t t' T,
  has_type [] t T -> 
  step t t' -> 
  has_type [] t' T.
Proof.
  intros t t' T H. generalize dependent t'. remember [] as env. 
  induction H; intros t' HS.
  - inversion HS; subst; inversion H0; subst; inversion H.
  - inversion HS; subst; inversion H0; subst; inversion H.  
  - subst. destruct x; inversion H.
  - subst. specialize (IHhas_type2 eq_refl). specialize (IHhas_type1 eq_refl).
    inversion HS; subst. 
    + apply substitution' with (U := T1); auto. inversion H. apply H5.  
    + inversion H2; subst; inversion H1; subst.
      * clear H1. econstructor. apply IHhas_type1. apply H3. apply H0.
      * clear H1. econstructor. apply H. apply IHhas_type2. apply H3.    
  - inversion HS; subst. inversion H1; subst; inversion H0.
Qed.

End STLC_ECTX.