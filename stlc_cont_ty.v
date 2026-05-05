(*
Transform dispatches on the typing derivation.
*)

From Stdlib Require Import Lists.List.
From Stdlib Require Import Psatz.
Require Import Stdlib.Arith.Compare_dec.
From Stdlib Require Import Arith.Peano_dec.
From Stdlib Require Import Arith.PeanoNat.  
Require Import Stdlib.Bool.Bool.
From Stdlib Require Import FunctionalExtensionality.
From Stdlib Require Import PropExtensionality.

Import ListNotations.

Require Import tactics.
Require Import env.
Require Import stlc_target.

Module STLC_CONT_TY.
Module B := stlc_target.STLC_TARGET. (* B for Base *)

Definition id := nat.

Inductive tm : Type := 
  (* values *)
  | ttrue : tm
  | tfalse : tm 
  | tvar : id -> tm 
  | tabs : tm -> tm
  | tcontabs : tm -> tm (* \x!.t - lambda that requires an implicit capability *)

  (* redexes *)
  | tif : tm -> tm -> tm -> tm
  | tapp : tm -> tm -> tm
  | treset : tm -> tm 
  | tshift : tm -> tm (* tshift t binds continuation in t *)
.

Inductive ty: Type := 
  | TBool : ty
  | TFun : ty -> ty -> ty (* T1 -> T2 *)
  | TKFun : ty -> ty -> ty -> ty (* T1, R !-> T2*)
.

Definition tenv := list ty.

(* \gamma, most recently introduced continuation capability |- tm : ty *)
Inductive has_type : tenv -> (option ty) -> tm -> ty -> Type := 
  (* Values *)
  | t_true : forall env K, 
      has_type env K ttrue TBool
  
  | t_false : forall env K,
      has_type env K tfalse TBool

  | t_var : forall env K x T, 
      indexl x env = Some T -> 
      has_type env K (tvar x) T    

  | t_abs : forall env K t T1 T2,  
      has_type (T1 :: env) None t T2 -> 
      has_type env K (tabs t) (TFun T1 T2)

  | t_contabs : forall env K t T1 R T2, 
      has_type (T1 :: env) (Some R) t T2 -> 
      has_type env K (tcontabs t) (TKFun T1 R T2)

  (* Redexes *)
  | t_if : forall env K cond tbranch ebranch T,
      has_type env K cond TBool -> 
      has_type env K tbranch T -> 
      has_type env K ebranch T -> 
      has_type env K (tif cond tbranch ebranch) T

  | t_app : forall env K f t T1 T2, 
      has_type env K f (TFun T1 T2) -> 
      has_type env K t T1 -> 
      has_type env K (tapp f t) T2 

  | t_reset : forall env K t R, 
      has_type env (Some R) t R ->
      has_type env K (treset t) R
  
  | t_shift : forall env t A R,    
      has_type ((TFun A R) :: env) None t R -> 
      has_type env (Some R) (tshift t) A

  | t_contapp : forall env f t T1 R T2, 
      has_type env (Some R) f (TKFun T1 R T2) -> 
      has_type env (Some R) t T1 -> 
      has_type env (Some R) (tapp f t) T2
.

(* Note: TKFun T1 R T2 translates to 
        T1 -> (T2 -> R) -> R as the continuation is invoked on return value in 
        transform *)
Fixpoint trans_ty (T: ty) : B.ty := 
  match T with 
    | TBool => B.TBool
    | TFun T1 T2 => B.TFun (trans_ty T1) (trans_ty T2)
    | TKFun T1 R T2 => 
        B.TFun (trans_ty T1) (B.TFun 
        (B.TFun (trans_ty T2) (trans_ty R)) (trans_ty R)
       )
  end.

Fixpoint trans_env(env: tenv): B.tenv := 
  match env with 
    | T :: t => (trans_ty T) :: (trans_env t)
    | [] => [] 
  end. 

#[export] Hint Constructors ty: core.
#[export] Hint Constructors tm: core.
#[local] Hint Constructors B.has_type : core.

Fixpoint transform { env K t T } (H : has_type env K t T) : B.tm * bool := 
match H in (has_type _ _ _ _) return (B.tm * bool) with 
  (* Values *)
  | t_true _ _ => (B.ttrue, false)
  | t_false _ _ => (B.tfalse, false)
  | t_var env K x T H => (B.tvar x, false)
  
  | t_abs env K t T1 T2 HT => 
    (B.tabs (fst (transform HT)), false)

  | t_contabs env K t T1 R T2 HT => 
    let (rt, bt) := transform HT in 
    if bt then 
      (B.tabs (B.tabsk (B.tapp rt (B.tvark 0))), false)
    else 
      (B.tabs (B.tabsk (B.tapp (B.tvark 0) rt)), false)

  (* Redexes *)
  | t_if env K cond tbranch ebranch T HTC HTT HTE =>
    let (rc, bc) := (transform HTC) in 
    let (rt, bt) := (transform HTT) in 
    let (re, be) := (transform HTE) in 
    match (bc, bt, be) with 
    | (false, false, false) => (B.tif rc rt re, false)
    | (true, false, false) => (B.tabsk
        (B.tapp rc (B.tabsk (B.tif (B.tvark 0) 
          (B.tapp (B.tvark 1) rt)
          (B.tapp (B.tvark 1) re)
        ))), true)
    | (false, true, false) => (B.tabsk (
        B.tif rc 
        (B.tapp rt (B.tvark 0))
        (B.tapp (B.tvark 0) re)
      ), true)
    | (true, true, false) => (B.tabsk (
        B.tapp rc (B.tabsk (B.tif (B.tvark 0) 
          (B.tapp rt (B.tvark 1))
          (B.tapp (B.tvark 1) re)
        ))
      ), true)
    | (false, false, true) => (B.tabsk (
        B.tif rc 
        (B.tapp (B.tvark 0) rt)
        (B.tapp re (B.tvark 0))
    ), true)
    | (true, false, true) => (B.tabsk (
        B.tapp rc (B.tabsk (B.tif (B.tvark 0)
          (B.tapp (B.tvark 1) rt)
          (B.tapp re (B.tvark 1))
        ))
    ), true) 
    | (false, true, true) => (B.tabsk (
        B.tif rc 
        (B.tapp rt (B.tvark 0))
        (B.tapp re (B.tvark 0))
    ), true)
    | (true, true, true) => (B.tabsk (
        B.tapp rc (B.tabsk (B.tif (B.tvark 0)
          (B.tapp rt (B.tvark 1))
          (B.tapp re (B.tvark 1))
        ))
    ), true)
    end

  | t_app env K f t T1 T2 HF HT =>  
    let (rf, bf) := (transform HF) in 
    let (rt, bt) := (transform HT) in 
    match (bf, bt) with 
    | (false, false) => (B.tapp rf rt, false)

    | (true, false) => ( B.tabsk (
      B.tapp rf (B.tabsk (
        B.tapp (B.tvark 1) (
          B.tapp (B.tvark 0) rt
        )
      ))
    ), true)
    | (false, true) => (B.tabsk (
        B.tapp rt (B.tabsk (
          B.tapp (B.tvark 1) (
            B.tapp rf (B.tvark 0)
          )
        ))
    ), true)
    | (true, true) => (B.tabsk (
        B.tapp rf ( B.tabsk (
          B.tapp rt ( B.tabsk (
            B.tapp (B.tvark 2)
            (B.tapp (B.tvark 1) (B.tvark 0))
          )) 
        ))
    ), true)
    end 

  | t_reset env K t R HT => 
    let (rt, bt) := transform HT in 
    if bt then 
      (B.tapp rt (B.tabs (B.tvar 0)), false)
    else 
      (rt, false)

  | t_shift env t A R HT => 
    (B.tabs (fst (transform HT)),true) 

  | t_contapp env f t T1 R T2 HF HT => 
    let (rf, bf) := (transform HF) in 
    let (rt, bt) := (transform HT) in 
    match (bf, bt) with 
    | (false, false) => (B.tabsk (
        B.tapp (B.tapp rf rt) 
        (B.tvark 0)
      ), true)
    | (true, false) => (B.tabsk (
        B.tapp rf ( B.tabsk (
          B.tapp (B.tapp (B.tvark 0) rt)
          (B.tvark 1)
        ))
    ), true)
    | (false, true) => (B.tabsk (
        B.tapp rt (B.tabsk (
          B.tapp (B.tapp (rf) (B.tvark 0)) 
          (B.tvark 1)
        ))
    ), true) 
    | (true, true) => (B.tabsk (
        B.tapp rf (B.tabsk (
          B.tapp rt (B.tabsk (
            B.tapp (B.tapp (B.tvark 1) (B.tvark 0))
            (B.tvark 2)
          ))
        )) 
    ), true)
    end
end.

Theorem fundamental : forall env K t T (H: has_type env K t T) t' b kenv,
  (t', b) = transform H -> 
  match K with 
  | None => 
    b = false /\
    B.has_type (trans_env env) kenv t' (trans_ty T)
  | Some R => 
    if b then 
      forall k,
      B.has_type (trans_env env) kenv k (B.TFun (trans_ty T) (trans_ty R)) -> 
      B.has_type (trans_env env) kenv (B.tapp t' k) (trans_ty R)
    else 
      B.has_type (trans_env env) kenv t' (trans_ty T)
  end.
Proof. 
  intros env K t T H. induction H; 
  intros t' b kenv HB; try (destruct K as [ Ans |]). 
  (* t_true *)
  - inversion HB. constructor.
  - inversion HB. split; auto.
  (* t_false *) 
  - inversion HB. constructor.
  - inversion HB. split; auto.
  (* t_var *)
  - inversion HB. constructor. apply indexl_map. apply e.
  - inversion HB. split. reflexivity. constructor. apply indexl_map. apply e.
  (* t_abs *)    
  - simpl in *. inversion HB. destruct (transform H).    
    destruct (IHhas_type t0 b0 kenv eq_refl). subst. auto.
  - simpl in *. inversion HB. destruct (transform H). 
    destruct (IHhas_type t0 b0 kenv eq_refl). subst. split; auto.
  (* t_contabs *)
  - simpl in *. destruct (transform H) as (r & br).
    specialize (IHhas_type r br (B.TFun (trans_ty T2) (trans_ty R) :: kenv) eq_refl). 
    destruct br; inversion HB; eauto.
    + econstructor. econstructor. econstructor; eauto. repeat econstructor.
  - simpl in *. destruct (transform H) as (r & br). 
    specialize (IHhas_type r br (B.TFun (trans_ty T2) (trans_ty R) :: kenv) eq_refl).
    destruct br; inversion HB; split; eauto.
    + constructor. constructor. econstructor; eauto. repeat econstructor.
  (* t_if *)
  - simpl in *. 
    destruct (transform H) as (rc & bc).
    destruct (transform H0) as (rt & bt). 
    destruct (transform H1) as (re & be).
    specialize (IHhas_type1 rc bc). 
    specialize (IHhas_type2 rt bt).
    specialize (IHhas_type3 re be).
    destruct bc; destruct bt; destruct be; inversion HB; try (intros k HK).
    (* (true, true, true) *)
    + econstructor; eauto. constructor. apply IHhas_type1; eauto.
      do 2 constructor; eauto. 
    (* (true, true, false) *)
    + econstructor; eauto. constructor. apply IHhas_type1; auto.
      do 2 constructor; eauto. repeat econstructor. eauto.
    (* (true, false, true) *)
    + econstructor; eauto. constructor. apply IHhas_type1; auto.
      do 2 constructor; auto. repeat econstructor. eauto.
    (* (true, false, false) *)
    + econstructor; eauto. constructor. apply IHhas_type1; auto.
      repeat econstructor; eauto.
    (* (false, true, true) *)
    + econstructor; eauto. do 2 constructor; eauto.
    (* (false, true, false) *)
    + econstructor; eauto. do 2 constructor; eauto. repeat econstructor. eauto.
    (* (false, false, true )*)
    + econstructor; eauto. do 2 constructor; eauto. repeat econstructor. eauto.
    + eauto.
  - simpl in *.     
    destruct (transform H) as (rc & bc). 
    destruct (transform H0) as (rt & bt). 
    destruct (transform H1) as (re & be). 
    destruct (IHhas_type1 rc bc kenv eq_refl). subst. 
    destruct (IHhas_type2 rt bt kenv eq_refl). subst. 
    destruct (IHhas_type3 re be kenv eq_refl). subst. 
    inversion HB. split; simpl; auto. 
  (* t_app *)
  - simpl in *.
    destruct (transform H) as (rf & bf).
    destruct (transform H0) as (rt & bt).
    specialize (IHhas_type1 rf bf).
    specialize (IHhas_type2 rt bt). 
    destruct bf; destruct bt; inversion HB; try (intros k HK).  
    (* (true, true) *)
    + econstructor; eauto. constructor. apply IHhas_type1; eauto.
      constructor. apply IHhas_type2; eauto. repeat econstructor.
    (* (true, false) *)
    + econstructor; eauto. constructor. apply IHhas_type1; eauto.
      repeat econstructor. auto.
    + econstructor; eauto. constructor. apply IHhas_type2; eauto.
      repeat econstructor. auto.
    + eauto.
  - simpl in *. 
    destruct (transform H) as (rf & bf).
    destruct (transform H0) as (rt & bt).
    destruct (IHhas_type1 rf bf kenv eq_refl). 
    destruct (IHhas_type2 rt bt kenv eq_refl). subst.
    inversion HB. split; econstructor; eauto.
  (* t_reset *)
  - simpl in *. destruct (transform H) as (r & br).
    specialize (IHhas_type r br kenv eq_refl). destruct br; inversion HB;
    apply IHhas_type. repeat econstructor.
  - simpl in *. destruct (transform H) as (r & br).
    specialize (IHhas_type r br kenv eq_refl). destruct br; inversion HB; auto.
  (* t_shift *)
  - simpl in *. inversion HB. intros k HK. econstructor; eauto. econstructor.
    destruct (transform H). specialize (IHhas_type t0 b0 kenv eq_refl).
    apply IHhas_type. 
  (* t_contapp *)
  - simpl in *.    
    destruct (transform H) as (rf & bf).
    destruct (transform H0) as (rt & bt).
    specialize (IHhas_type1 rf bf). 
    specialize (IHhas_type2 rt bt).
    destruct bf; destruct bt; inversion HB; try (intros K HK).
    (* (true, true) *)
    + econstructor; eauto. constructor. apply IHhas_type1; eauto.
      constructor. apply IHhas_type2. auto. repeat econstructor.
    (* (true, false) *)
    + econstructor; eauto. constructor. apply IHhas_type1; eauto.
      repeat econstructor. eauto.
    (* (false, true) *)
    + econstructor; eauto. constructor. apply IHhas_type2; eauto.
      repeat econstructor. eauto.
    + repeat econstructor; eauto.
Qed.

Theorem transl_pre_types: forall t T (H: has_type [] None t T),
  B.has_type [] [] (fst (transform H)) (trans_ty T).
Proof.
  intros t T H. remember (transform H) as res. 
  destruct (res) as (t' & b). 
  pose proof (fundamental _ _ _ _ H t' b []) as HQ.
  simpl in *. rewrite <- Heqres in HQ. apply HQ.
  reflexivity.
Qed.   

Corollary safety : forall t T (H: has_type [] None t T), 
  B.exp_type [] [] (fst (transform H)) (trans_ty T).
Proof.
  intros. apply B.safety. apply transl_pre_types.
Qed.

End STLC_CONT_TY.




