(*

Target language for selective CPS transform.

Uses de Bruijn indices.
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

Module STLC_CONT_TARGET.

(* ---------- language syntax ---------- *)

Definition id := nat.

Inductive ty : Type :=
  | TBool  : ty
  | TFun   : ty -> ty -> ty
.

Inductive tm : Type :=
  | ttrue : tm
  | tfalse : tm
  | tif : tm -> tm -> tm -> tm
  | tvar : id -> tm
  | tapp : tm -> tm -> tm
  | tabs : tm -> tm
  | tabsk : tm -> tm  (* binder for continuation variables *)
  | tvark : id -> tm  (* continuation variable *)
.

Inductive vl: Type :=
| vbool :  bool -> vl
| vabs  :  list vl -> list vl -> tm -> vl 
| vabsk :  list vl -> list vl -> tm -> vl
.

Definition venv := list vl.
Definition tenv := list ty. 

Definition vkenv := list vl. 
Definition tkenv := list ty. 

#[global] Hint Unfold venv : core.
#[global] Hint Unfold tenv : core.

#[global] Hint Unfold vkenv : core.
#[global] Hint Unfold tkenv : core.


(* ---------- syntactic typing rules ---------- *)

Inductive has_type : tenv -> tkenv -> tm -> ty -> Prop :=
| t_true: forall env kenv,
    has_type env kenv ttrue TBool
| t_false: forall env kenv,
    has_type env kenv tfalse TBool
| t_if: forall env kenv cond tbranch ebranch T,
    has_type env kenv cond TBool ->
    has_type env kenv tbranch T -> 
    has_type env kenv ebranch T -> 
    has_type env kenv (tif cond tbranch ebranch) T
| t_var: forall x env kenv T,
    indexl x env = Some T ->
    has_type env kenv (tvar x) T
| t_app: forall env kenv f t T1 T2,
    has_type env kenv f (TFun T1 T2) ->
    has_type env kenv t T1 ->
    has_type env kenv (tapp f t) T2
| t_abs: forall env kenv t T1 T2,
    has_type (T1::env) kenv t T2 ->
    has_type env kenv (tabs t) (TFun T1 T2)

| t_absk: forall env kenv t T1 T2, 
    has_type env (T1 :: kenv) t T2 -> 
    has_type env kenv (tabsk t) (TFun T1 T2)

| t_vark: forall x env kenv T,
    indexl x kenv = Some T -> 
    has_type env kenv (tvark x) T
.

(* ---------- operational semantics ---------- *)


Fixpoint teval(n: nat)(env: venv)(kenv : vkenv)(t: tm){struct n}: option (option vl) :=
  match n with
    | 0 => None
    | S n =>
      match t with
        | ttrue      => Some (Some (vbool true))
        | tfalse     => Some (Some (vbool false))
        | tvar x     => Some (indexl x env)
        | tabs y     => Some (Some (vabs env kenv y)) 
        | tvark x    => Some (indexl x kenv)
        | tabsk y    => Some (Some (vabsk env kenv y))
        | tapp ef ex   =>
          match teval n env kenv ef with
            | None => None
            | Some None => Some None
            | Some (Some (vbool _)) => Some None
            | Some (Some (vabs env2 kenv2 ey)) =>
              match teval n env kenv ex with
                | None => None
                | Some None => Some None
                | Some (Some vx) =>
                  teval n (vx::env2) kenv2 ey
              end
            | Some (Some (vabsk env2 kenv2 ey)) => 
              match teval n env kenv ex with 
                | None => None 
                | Some None => Some None 
                | Some (Some vx) => 
                  teval n env2 (vx :: kenv2) ey   
              end
          end
        | tif cond tbranch ebranch => 
            match teval n env kenv cond with 
              | None => None 
              | Some None => Some None 
              | Some (Some (vabs _ _ _)) => Some None
              | Some (Some (vabsk _ _ _)) => Some None
              | Some (Some (vbool true)) => 
                match teval n env kenv tbranch with 
                | None => None  
                | Some None => Some None 
                | Some (Some vt) as res_true => res_true
                end
              | Some (Some (vbool false)) => 
                match teval n env kenv ebranch with 
                | None => None 
                | Some None => Some None 
                | Some (Some vf) as res_false => res_false
                end 
            end
      end
  end.

Definition tevaln env kenv e v := exists nm, forall n, n > nm -> teval n env kenv e = Some (Some v).

(* ---------- LR definitions  ---------- *)

Fixpoint val_type v T : Prop :=
  match v, T with
  | vbool b, TBool =>  
      True
  | vabs H KH ty, TFun T1 T2 => 
      forall vx,
        val_type vx T1 ->
        exists vy,
          tevaln (vx::H) KH ty vy /\
          val_type vy T2
  | vabsk H KH ty, TFun T1 T2 => 
      forall vx, 
        val_type vx T1 -> 
        exists vy,
          tevaln H (vx :: KH) ty vy /\
          val_type vy T2
  | _,_ =>
      False
  end.


Definition exp_type H K t T := 
  exists v,
    tevaln H K t v /\
    val_type v T.

Definition env_type (H: venv) (G: tenv) :=
  length H = length G /\
    forall x T,
      indexl x G = Some T -> (* x : T \in G *)
      exists v,
        indexl x H = Some v /\ (* exists v, x -> v \in H and v T*)
        val_type v T.

Definition kenv_type (KH: vkenv) (KG: tkenv) := 
  length KH = length KG /\ 
    forall x T,
      indexl x KG = Some T -> 
      exists v, 
        indexl x KH = Some v /\ 
        val_type v T.

Definition sem_type G KG t T :=
  forall H KH,
    env_type H G ->
    kenv_type KH KG -> 
    exp_type H KH t T.


#[export] Hint Constructors ty: core.
#[export] Hint Constructors tm: core.
#[export] Hint Constructors vl: core.

#[export] Hint Constructors has_type: core.

#[export] Hint Constructors option: core.
#[export] Hint Constructors list: core.



(* ---------- LR helper lemmas  ---------- *)

Lemma envt_empty:
    env_type [] [].
Proof.
  intros. split. eauto. intros. destruct x; inversion H. 
Qed.

Lemma kenvt_empty:
    kenv_type [] []. 
Proof. 
  intros. split. eauto. intros. destruct x; inversion H.
Qed.

Lemma envt_extend: forall E G v1 T1,
    env_type E G ->
    val_type v1 T1 ->
    env_type (v1::E) (T1::G).
Proof.
  intros. 
  remember H as WFE. clear HeqWFE.
  destruct H. split. simpl. eauto.
  intros x T IX. destruct x.
  - simpl in IX. inversion IX. subst T1. exists v1. auto.
  - simpl in IX. eapply WFE in IX as IX. destruct IX as (v2 & ? & ?).
    exists v2. auto.        
Qed.

Lemma kenvt_extend: forall KE KG v1 T1, 
    kenv_type KE KG -> 
    val_type v1 T1 -> 
    kenv_type (v1 :: KE) (T1 :: KG).
Proof. 
    intros. 
    remember H as WFE. clear HeqWFE.
    destruct H. split. simpl. eauto.
    intros x T IX. destruct x.
    - simpl in IX. inversion IX. subst T1. exists v1. auto.
    - simpl in IX. eapply WFE in IX as IX. destruct IX as (v2 & ? & ?).
      exists v2. auto.        
Qed.


(* ---------- LR compatibility lemmas  ---------- *)

Lemma sem_true: forall G KG,
    sem_type G KG ttrue TBool.
Proof.
  intros. intros E WFE. 
  exists (vbool true). split.
  - exists 0. intros. destruct n. lia. simpl. eauto.
  - simpl. eauto. 
Qed.

Lemma sem_false: forall G KG,
    sem_type G KG tfalse TBool.
Proof.
  intros. intros E WFE. 
  exists (vbool false). split.
  - exists 0. intros. destruct n. lia. simpl. eauto.
  - simpl. eauto. 
Qed.

Lemma sem_var: forall G KG x T,
    indexl x G = Some T ->
    sem_type G KG (tvar x) T.
Proof.
  intros. intros E KE WFE.
  eapply WFE in H as IX. destruct IX as (v & IX & VX).
  exists v. split. 
  - exists 0. intros. destruct n. lia. simpl. rewrite IX. eauto.
  - eauto. 
Qed.

Lemma sem_app: forall G KG f t T1 T2,
    sem_type G KG f (TFun T1 T2) ->
    sem_type G KG t T1 ->
    sem_type G KG (tapp f t) T2.
Proof.
  intros ? ? ? ? ? ? HF HX. intros E KE WFE WFKE. 
  destruct (HF E KE WFE WFKE) as (vf & STF & VF).
  destruct (HX E KE WFE WFKE) as (vx & STX & VX).
  destruct vf; simpl in VF; intuition.
  - edestruct VF as (vy & STY & VY). eauto. exists vy. split.
    + destruct STF as (n1 & STF).
      destruct STX as (n2 & STX).
      destruct STY as (n3 & STY).
      exists (1+n1+n2+n3). intros. destruct n. lia.
      simpl. rewrite STF, STX, STY. 2,3,4: lia.
      eauto.
    + eauto.
  - edestruct VF as (vy & STY & VY). eauto. exists vy. split.
    + destruct STF as (n1 & STF).
      destruct STX as (n2 & STX).
      destruct STY as (n3 & STY).
      exists (1 + n1 + n2 + n3). intros. destruct n. lia.
      simpl. rewrite STF, STX, STY. 2,3,4: lia.
      reflexivity.
    + apply VY.            
Qed.

Lemma sem_abs: forall G KG t T1 T2,
    sem_type (T1::G) KG t T2 ->
    sem_type G KG (tabs t) (TFun T1 T2).
Proof.
  intros ? ? ? ? ? HY. intros E KE WFE WFKE. 
  assert (length E = length G) as L. eapply WFE.
  exists (vabs E KE t). split.
  - exists 0. intros. destruct n. lia. simpl. eauto.
  - simpl. intros. eapply HY. eapply envt_extend; eauto. apply WFKE.
Qed.

Lemma sem_if : forall G KG cond tbranch ebranch T,
  sem_type G KG cond (TBool) -> 
  sem_type G KG tbranch T -> 
  sem_type G KG ebranch T -> 
  sem_type G KG (tif cond tbranch ebranch) T. 
Proof.
  intros G KG cond tbranch ebranch T HC HT HF. 
  intros E KE WFE WFKE. destruct (HC E KE WFE WFKE) as (vc & STC & VC). 
  destruct vc; inversion VC.      
  destruct STC as (nb, STC).
  destruct b.
  - destruct (HT E KE WFE WFKE) as (vt & STT & VT).  
    exists vt. split. destruct STT as (nt, STT).
    exists (1 + nb + nt). intros. destruct n. lia.
    simpl. rewrite STC. rewrite STT; auto. lia. lia.
    auto.
  - destruct (HF E KE WFE WFKE) as (vf & STF & VF).
    exists vf. split. destruct STF as (nf, STF).
    exists (1 + nb + nf). intros. destruct n. lia. 
    simpl. rewrite STC. rewrite STF; auto. lia. lia.
    auto.
Qed. 

Lemma sem_absk : forall G KG t T1 T2, 
  sem_type G (T1 :: KG) t T2 ->
  sem_type G KG (tabsk t) (TFun T1 T2).
Proof.
  intros G KG t T1 T2 HY. intros E KE WFE WFKE.
  assert (length KE = length KG) as L. eapply WFKE.
  exists (vabsk E KE t). split.
  - exists 0. intros. destruct n. lia. simpl. eauto.
  - simpl. intros. eapply HY; auto. eapply kenvt_extend; eauto.
Qed.

Lemma sem_vark: forall G KG x T,
    indexl x KG = Some T ->
    sem_type G KG (tvark x) T.
Proof.
  intros. intros E KE WFE WFKE.
  eapply WFKE in H as IX. destruct IX as (v & IX & VX).
  exists v. split. 
  - exists 0. intros. destruct n. lia. simpl. rewrite IX. eauto.
  - eauto. 
Qed.
                                                       
(* ---------- LR fundamental property  ---------- *)

Theorem fundamental: forall G KG t T,
    has_type G KG t T ->
    sem_type G KG t T.
Proof.
  intros ? ? ? ? W. 
  induction W. 
  - eapply sem_true; eauto.
  - eapply sem_false; eauto.
  - eapply sem_if; eauto. 
  - eapply sem_var; eauto.
  - eapply sem_app; eauto. 
  - eapply sem_abs; eauto.
  - eapply sem_absk; eauto.
  - eapply sem_vark; eauto.
Qed.

Corollary safety: forall t T,
  has_type [] [] t T ->
  exp_type [] [] t T.
Proof. 
  intros. eapply fundamental in H as ST; eauto.
  destruct (ST [] []) as (v & ? & ?).
  eapply envt_empty. eapply kenvt_empty.
  exists v. intuition.
Qed.

Theorem badtm : forall env kenv T, ~has_type env kenv (tapp ttrue tfalse) T.
  intros env kenv T H. inversion H. inversion H4.   
Qed. 

End STLC_CONT_TARGET.
