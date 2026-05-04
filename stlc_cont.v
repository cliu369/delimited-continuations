Require Import Coq.Lists.List.
Require Import Psatz.
Require Import Coq.Arith.Compare_dec.
Require Import Coq.Arith.Peano_dec.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Bool.Bool.
Require Import FunctionalExtensionality.
Require Import PropExtensionality.

Import ListNotations.

Require Import tactics.
Require Import env.

Module STLC_CONT.
Module B := stlc_cont_target.STLC_CONT_TARGET. (* B for Base *)

#[local] Hint Constructors B.has_type : core.

Definition id := nat.

Inductive tm : Type := 
  | ttrue : tm
  | tfalse : tm 
  | tif : tm -> tm -> tm -> tm
  | tvar : id -> tm 
  | tabs : tm -> tm
  | tapp : tm -> tm -> tm
  (* | tlet : tm -> tm -> tm *)
  | treset : tm -> tm 
  | tshift : tm -> tm (* tshift e binds continuation in e *)
  | tcontabs : tm -> tm (* \x!, *)
  | tcontapp : tm -> tm -> tm
.

(* let g = \x.x in g false *)
(* Definition example1 : tm := 
  tlet (tabs (tvar 0)) (tapp (tvar 0) tfalse). *)

(* < if (Sk.(if false then k(true) else k(false))) then true 
     else false > *)
Example example2 : tm := 
  treset (
    tif (
      tshift ( 
        tif tfalse (tapp (tvar 0) ttrue) (tapp (tvar 0) tfalse)
      )
    ) ttrue tfalse 
  ).

Inductive ty: Type := 
  | TBool : ty
  | TFun : ty -> ty -> ty (* T1 -> T2 *)
  | TKFun : ty -> ty -> ty -> ty (* T1 !->R T2*)
(* Note - do we need to make TKFun a restricted type? *)
.
Definition tenv := list ty.

(* \gamma, current continuation capability |- tm : ty *)
Inductive has_type : tenv -> (option ty) -> tm -> ty -> Prop := 
  | t_true : forall env K, 
      has_type env K ttrue TBool
  
  | t_false : forall env K,
      has_type env K tfalse TBool

  | t_if : forall env K cond tbranch ebranch T,
      has_type env K cond TBool -> 
      has_type env K tbranch T -> 
      has_type env K ebranch T -> 
      has_type env K (tif cond tbranch ebranch) T
  
  | t_var : forall x env K T, 
      indexl x env = Some T -> 
      has_type env K (tvar x) T    

  | t_abs : forall env K t T1 T2,  
      has_type (T1 :: env) None t T2 -> 
      has_type env K (tabs t) (TFun T1 T2)

  | t_app : forall env K f t T1 T2, 
      has_type env K f (TFun T1 T2) -> 
      has_type env K t T1 -> 
      has_type env K (tapp f t) T2 

  (* | t_let : forall env K t1 t2 T1 T2, 
      has_type env K t1 T1 -> 
      has_type (T1 :: env) K t2 T2 -> 
      has_type env K (tlet t1 t2) T2 *)

  | t_reset : forall env K t R,  (* R is answer type *)
      has_type env (Some R) t R ->
      has_type env K (treset t) R
  
  | t_shift : forall env t A R,    
      has_type ((TFun A R) :: env) None t R -> 
      has_type env (Some R) (tshift t) A

  | t_contabs : forall env K t T1 R T2, 
      has_type (T1 :: env) (Some R) t T2 -> 
      has_type env K (tcontabs t) (TKFun T1 R T2)

  | t_contapp : forall env f t T1 R T2, 
      has_type env (Some R) f (TKFun T1 R T2) -> 
      has_type env (Some R) t T1 -> 
      has_type env (Some R) (tcontapp f t) T2
.

Example test1 : has_type [] None example2 TBool.
Proof.
  repeat econstructor; auto.
Qed.

Definition id_abs : B.tm := B.tabs (B.tvar 0).

Definition error_tm : B.tm := B.tapp B.ttrue B.tfalse.

Lemma conv_list : forall A (x: A) (l: list A), 
  x :: l = [x] ++ l.
Proof.
  intros A x l. simpl. reflexivity.
Qed. 

Lemma conv_list2 : forall A x y (l: list A),
  x :: y :: l = [x; y] ++ l.
Proof.
  intros A x y l. intuition.
Qed.

(* shift tvark by d if tvark >= c *)
Fixpoint shift (t: B.tm) (c: nat) (d: nat): B.tm := 
  match t with 
  | B.ttrue => B.ttrue 
  | B.tfalse => B.tfalse
  | B.tif cond tbranch ebranch => B.tif (shift cond c d) (shift tbranch c d) (shift ebranch c d)
  | B.tvar n => B.tvar n
  | B.tabs t => B.tabs (shift t c d)
  | B.tapp t1 t2 => B.tapp (shift t1 c d) (shift t2 c d)
  | B.tabsk t => B.tabsk (shift t (c + 1) d)
  | B.tvark n => if (c <=? n) then B.tvark (n + d) else B.tvark n 
  end.

Lemma indexl_add : forall A (l1: list A) l2 i, 
  indexl i l2 = indexl (i + length l1) (l1 ++ l2).
Proof.
  intros A l1. induction l1; intros l2 i.
  - simpl. rewrite Nat.add_0_r. reflexivity. 
  - simpl. rewrite Nat.add_succ_r. simpl. apply IHl1.
Qed.

Lemma indexl_mid : forall A (l1: list A) l2 l3 i,
  length l1 <= i -> 
  indexl i (l1 ++ l3) = indexl (i + length l2) (l1 ++ l2 ++ l3).
Proof.
  intros A l1. induction l1; intros l2 l3 i HL.
  - simpl in *. apply indexl_add.
  - destruct i. inversion HL.
    + simpl in *. apply IHl1. apply le_S_n in HL. apply HL.
Qed.   

Lemma indexl_left : forall A (l1: list A) l2 l3 i, 
  length l1 > i -> 
  indexl i (l1 ++ l3) = indexl (i) (l1 ++ l2 ++ l3).
Proof.
  intros A l1. induction l1; intros l2 l3 i HL.
  - simpl in *. inversion HL.   
  - destruct i. auto. simpl in *. apply le_S_n in HL.
    apply IHl1. apply HL.
Qed.    

Lemma shift_pre_ty_gen : forall env t T c d kenv1 kenv2 kenv kenv',
  kenv1 ++ kenv2 = kenv -> 
  c = length kenv1 -> 
  d = length kenv' -> 
  B.has_type env kenv t T -> 
  B.has_type env (kenv1 ++ kenv' ++ kenv2) (shift t c d) T .
Proof.  
  intros env t. generalize dependent env. induction t;
  intros env T c d kenv1 kenv2 kenv kenv' HK HC HD HT; 
  inversion HT; simpl; try (econstructor; eauto).
  - subst. replace (T1 :: kenv1 ++ kenv' ++ kenv2)
     with ((T1::kenv1) ++ kenv' ++ kenv2) by auto.  
    eapply IHt; eauto. simpl. lia.
  - subst. bdestruct ((length kenv1) <=? i).
    + constructor. rewrite <- indexl_mid; eauto.
    + constructor. rewrite <- indexl_left; eauto.
Qed.

Lemma shift_pre_ty : forall env kenv t T pre,
  B.has_type env kenv t T -> 
  B.has_type env (pre ++ kenv) (shift t 0 (length pre)) T.
Proof.  
  intros env kenv t T pre HT.
  replace (pre ++ kenv) with ([] ++ pre ++ kenv) by auto.
  apply shift_pre_ty_gen with (kenv := kenv); eauto.
Qed.

Fixpoint transform (t: tm) : B.tm := 
  match t with 
  | ttrue => B.ttrue
  | tfalse => B.tfalse 
  | tif cond tbranch ebranch => 
      B.tif (transform cond) (transform tbranch) (transform ebranch)  
  | tvar x => B.tvar x
  | tabs t => B.tabs (transform t)
  | tapp t1 t2 => B.tapp (transform t1) (transform t2)
  | treset e => transformK e id_abs
  | tshift e => error_tm
  | tcontabs e => (B.tabs (B.tabsk (transformK e (B.tvark 0)))) (* \x. \k. [[e]] k *)
  | tcontapp f e => error_tm
  end

with transformK (t: tm) (k: B.tm) : B.tm := 
  match t with 
  | ttrue => (B.tapp k B.ttrue)
  | tfalse => (B.tapp k B.tfalse)
  | tif cond tbranch ebranch => 
      transformK (cond) (B.tabsk
        (B.tif (B.tvark 0) (
          transformK tbranch (shift k 0 1)
        ) (
          transformK ebranch (shift k 0 1)
        )
        )
      )
  | tvar x => B.tapp k (B.tvar x)
  | tabs t => B.tapp k (B.tabs (transform t))
  | tapp f t => 
      transformK f (B.tabsk (
          transformK t ( B.tabsk (
              B.tapp (shift k 0 2) ( B.tapp (B.tvark 1) (B.tvark 0) )
            )
          )
        )
      )
  | treset e => B.tapp k (transformK e id_abs) 
  | tshift e => B.tapp (B.tabs (transform e)) (k)
  | tcontabs e => B.tapp k ((B.tabs (B.tabsk (transformK e (B.tvark 0)))))
  | tcontapp f t => 
      transformK f ( B.tabsk (
          transformK t ( B.tabsk (
              B.tapp (B.tapp (B.tvark 1) (B.tvark 0)) (shift k 0 2)
            )
          )
        )
      )
  end.

Fixpoint remove_id (t : B.tm) : (B.tm) := 
  match t with 
    | B.tapp (B.tabs (B.tvar 0)) e => remove_id e
    | B.tif c t e => B.tif (remove_id c) (remove_id t) (remove_id e)
    | B.tabs e => B.tabs (remove_id e) 
    | B.tapp f e => B.tapp (remove_id f) (remove_id e)
    | B.tabsk e => B.tabsk (remove_id e)
    | v => v
  end. 

Definition ttrans (t: tm) : (B.tm) := remove_id (transform t). 

Definition trans_example2 : B.tm := ttrans example2.

(* Compute trans_example2. *)

(* this one fails if we use tabsk in tif transformK case*)
Example example3 : tm := 
  (tcontabs (tif ttrue tfalse tfalse)).

(* Compute ttrans example3.  *)

(* this one fails if we use tabs in tif transformK case 
   tvar 0 in this case refers to tcontabs 
*)
Example example4 : tm := 
  (tcontabs (tif ttrue (tvar 0) (tvar 0))). 

(* Compute ttrans example4.  *)

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

Lemma indexl_map : forall (A B: Type) (l: list A) (x : nat) (f: A -> B) (v: A), 
  indexl x l = Some (v) ->
  indexl x (map f l) = Some (f v).
Proof.
  intros A B l. induction l; intros x f v H.    
  - destruct x; discriminate H.
  - simpl in H. simpl. destruct x. 
    + injection H as H. subst. simpl. reflexivity. 
    + simpl in *. auto.  
Qed.

#[export] Hint Constructors ty: core.
#[export] Hint Constructors tm: core.

Theorem fundamental : forall G K t T, 
  has_type G K t T -> 
  match K with 
  | None => 
    forall H, 
    B.has_type (trans_env G) H (transform t) (trans_ty T)
  | Some Ans => 
    forall k H,
    B.has_type (trans_env G) (H) k (B.TFun (trans_ty T) (trans_ty Ans)) ->
    B.has_type (trans_env G) (H) (transformK t k) (trans_ty Ans)
  end.
Proof.
  intros G K t T H. induction H.
  - destruct K. 
    + intros k H HT. simpl. econstructor. eapply HT. econstructor.
    + intros H. simpl. econstructor.
  - destruct K.
    + intros k H HT. simpl. econstructor. eapply HT. econstructor.
    + intros H. simpl. econstructor.
  - destruct K as [ K |].                 
    + intros k kenv HT. simpl. apply IHhas_type1. constructor.
      constructor. constructor. auto. apply IHhas_type2. simpl.
      rewrite conv_list. apply shift_pre_ty. apply HT.
      simpl. apply IHhas_type3. rewrite conv_list. apply shift_pre_ty.
      apply HT.
    + intros H2. simpl. econstructor; eauto.
  - destruct K as [ K |].
    + intros k kenv HT. simpl. econstructor; eauto. econstructor.
      apply indexl_map. apply H.
    + intros H2. simpl. econstructor; apply indexl_map. apply H.
  - destruct K as [ Ans |].
    + intros k kenv HT. simpl. econstructor; eauto. simpl. 
      econstructor. simpl in IHhas_type. eauto.
    + intros H2. simpl. econstructor. eauto.
  - destruct K as [ Ans |].
    + intros k kenv HT. simpl. apply IHhas_type1. constructor.
      apply IHhas_type2. constructor. simpl. 
      apply B.t_app with (T1 := (trans_ty T2)). 
      * rewrite conv_list2. apply shift_pre_ty. apply HT.
      * econstructor. econstructor. reflexivity. econstructor.
        reflexivity.
    + intros H1. simpl. econstructor; eauto.
  - destruct K as [ Ans |].
    + intros k kenv HT. simpl. apply B.t_app with (T1 := (trans_ty R));
      auto. apply IHhas_type. repeat econstructor.
    + intros H1. simpl. apply IHhas_type. repeat econstructor.
  - intros k kenv HT. simpl. apply B.t_app with (T1 := (trans_ty (TFun A R))).
    + constructor. apply IHhas_type.
    + auto.
  - destruct K as [ Ans |].
    + intros k kenv HT. simpl. apply B.t_app with (T1 := (trans_ty (TKFun T1 R T2)));
      auto. simpl. constructor. constructor. apply IHhas_type. repeat constructor.
    + intros kenv. simpl. constructor. constructor. apply IHhas_type. 
      repeat constructor.
  - intros k kenv HT. simpl. apply IHhas_type1. constructor. 
    apply IHhas_type2. constructor. apply B.t_app with (T1 := (trans_ty (TFun T2 R))).
    * repeat econstructor.
    * rewrite conv_list2. apply shift_pre_ty. auto.
Qed.   

Theorem transl_pre_types : forall t T,
  has_type [] None t T -> 
  B.has_type [] [] (transform t) (trans_ty T).
Proof.
  intros t T H. apply fundamental in H. apply H.
Qed.

Corollary safety : forall t T,
  has_type [] None t T -> 
  B.exp_type [] [] (transform t) (trans_ty T). 
Proof.
  intros t T H. apply transl_pre_types in H.
  apply B.safety. apply H.
Qed.   

(* 
   extension, instead of just returning bool, 
   return a term with a hole (e.g. function from B.tm -> B.tm)
   so for example for tapp it would return
   [[ f t ]] = [[ f ]] (\v1. [[ t ]] (\v2. [ HOLE ] (f t) )). 
   and if its a subterm supply a
*)
Fixpoint transform2 (t: tm) : B.tm * bool := 
  match t with 
  (* Values *)
  | ttrue => (B.ttrue, false)
  | tfalse => (B.tfalse, false)
  | tvar x => (B.tvar x, false)
  (* In \x.t, the t should never need a cont, should be 
     enforced by type checker *)
  | tabs t => (B.tabs (fst (transform2 t)), false)

  (* In \x!.t, the t always needs a cont, but depending on 
    what t is the cont can be either applied or supplied *)
  | tcontabs t => 
    let (res, b) := transform2 t in
    if b then 
    (B.tabs (B.tabsk (B.tapp res (B.tvark 0))), false)
    else 
    (B.tabs (B.tabsk (B.tapp (B.tvark 0) res)), false)
    (* here we return false even though it needs a continuation 
       because it is specially handled in tcontapp case? *)

  (* Redexes *)
  | tif cond tbranch ebranch => 
    let (rc, bc) := (transform2 cond) in 
    let (rt, bt) := (transform2 tbranch) in 
    let (re, be) := (transform2 ebranch) in 
    match (bc, bt, be) with 
    (* if [[ t1 ]] then [[ t2 ]] eles [[ t3 ]] *)
    | (false, false, false) => (B.tif rc rt re, false)
    (* \k. [[ t1 ]] (\m. if m then  k [[t2]] else k [[t3]])*)
    | (true, false, false) => (B.tabsk
        (B.tapp rc (B.tabsk (B.tif (B.tvark 0) 
          (B.tapp (B.tvark 1) rt)
          (B.tapp (B.tvark 1) re)
        ))), true)
    (* \k. if [[ t1 ]] then [[t2]] k  else k [[ t3 ]]*)
    | (false, true, false) => (B.tabsk (
        B.tif rc 
        (B.tapp rt (B.tvark 0))
        (B.tapp (B.tvark 0) re)
      ), true)
    (* \k. [[ t1 ]] (\m. if m then [[ t2 ]] k else k [[ t3 ]])*)
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

  | tapp f t =>   
    let (rf, bf) := (transform2 f) in 
    let (rt, bt) := (transform2 t) in 
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

  | treset t => 
    let (res, b) := transform2 t in 
    if b then 
      (B.tapp res id_abs, false)
    else 
      (res, false)
  
  | tshift t => 
    let res := fst (transform2 t) in 
    (B.tabs res, true)
  
  | tcontapp f t => 
    let (rf, bf) := (transform2 f) in 
    let (rt, bt) := (transform2 t) in 
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

Theorem bad : forall G t T, 
  has_type G None t T -> 
  forall H t' b, 
  (t', b) = transform2 t -> 
  b = false /\ 
  B.has_type (trans_env G) H t' (trans_ty T).
Proof.
  intros G t T H. induction H. 
  - intros H t' b. simpl. intros. inversion H0. split; auto. 
  - intros H t' b. simpl. intros. inversion H0. split; auto. 
  - intros H2 t' b. simpl. destruct (transform2 cond). 
    destruct (IHhas_type1 H2 t b0 eq_refl). subst. 
    destruct (transform2 tbranch). 
    destruct (IHhas_type2 H2 t0 b0 eq_refl). subst.
    destruct (transform2 ebranch). 
    destruct (IHhas_type3 H2 t1 b0 eq_refl). subst. 
    intros HV. inversion HV. split. auto. econstructor; auto.
  - intros H0 t' b. simpl. intros HV. inversion HV. split. auto.
    constructor. apply indexl_map. apply H.
  - intros kenv t' b. simpl. intros HB. inversion HB.  
    split; auto. econstructor. 
    specialize (IHhas_type kenv (fst (transform2 t)) (snd (transform2 t))).
    destruct (transform2 t). simpl in IHhas_type. subst.
    apply IHhas_type. reflexivity.
  - intros kenv t' b. simpl. destruct (transform2 f) as (rf & bf). 
    destruct (transform2 t) as (rt & bt).  
    destruct (IHhas_type1 kenv rf bf eq_refl). subst.
    destruct (IHhas_type2 kenv rt bt eq_refl). subst.
    intros HB. inversion HB. split. reflexivity. econstructor; eauto.
  - intros kenv t' b. simpl. destruct (transform2 t) as (res, br). 
    destruct (IHhas_type kenv res br eq_refl). subst.
    intros HB. inversion HB. split. reflexivity. auto.
  - intros kenv t' b HB. inversion HB.   
Admitted.
  
(*
can i commit this somewhere
*)  
Theorem fundamental2 : forall G K t T,
  has_type G K t T -> 
  forall t' b H, 
  (t', b) = transform2 t -> 
  match K with 
  | None => 
    b = false /\
    B.has_type (trans_env G) H (fst (transform2 t)) (trans_ty T) 
  | Some Ans => 
    if b then 
      forall k, 
      B.has_type (trans_env G) H k (B.TFun (trans_ty T) (trans_ty Ans)) -> 
      B.has_type (trans_env G) H (B.tapp t' k) (trans_ty Ans)
    else 
      B.has_type (trans_env G) H (t') (trans_ty T)
  end.
Proof. 
  intros G K t T H. induction H; 
  intros t' b kenv HB; try (destruct K as [ Ans |]). 
  (* ttrue *)
  - inversion HB. constructor.
  - inversion HB. split; auto.
  (* tfalse *)
  - inversion HB. constructor.
  - inversion HB. split; auto.
  (* tif *)
  - simpl in HB. 
    destruct (transform2 cond) as (rc & bc).
    destruct (transform2 tbranch) as (rt & bt). 
    destruct (transform2 ebranch) as (re & be).
    specialize (IHhas_type1 rc bc). 
    specialize (IHhas_type2 rt bt).
    specialize (IHhas_type3 re be).
    destruct bc; destruct bt; destruct be; inversion HB;
    try (intros k HK); eauto.
    + econstructor; eauto. econstructor; eauto. apply IHhas_type1; eauto.
      econstructor. econstructor; eauto. 
    + econstructor; eauto. econstructor. apply IHhas_type1; eauto. 
      econstructor. econstructor; eauto. econstructor; eauto. eauto.
    + econstructor; eauto. econstructor; eauto. apply IHhas_type1; eauto.
      econstructor. econstructor; eauto. econstructor; eauto. eauto.
    + econstructor; eauto. econstructor; eauto. apply IHhas_type1; eauto.
      econstructor. econstructor; eauto. econstructor; eauto. 
      econstructor; eauto. econstructor; eauto. eauto.
    + econstructor; eauto. econstructor. econstructor; eauto.
    + econstructor; eauto. econstructor. econstructor; eauto. econstructor; eauto.
      repeat econstructor.
    + econstructor; eauto. econstructor. econstructor; eauto. econstructor; eauto.
      repeat econstructor.   
  - simpl in *. 
    destruct (transform2 cond) as (rc & bc). 
    destruct (transform2 tbranch) as (rt & bt). 
    destruct (transform2 ebranch) as (re & be). 
    destruct (IHhas_type1 rc bc kenv eq_refl). subst. 
    destruct (IHhas_type2 rt bt kenv eq_refl). subst. 
    destruct (IHhas_type3 re be kenv eq_refl). subst. 
    inversion HB. split; simpl; auto. 
  (* tvar *)
  - simpl. inversion HB. constructor. apply indexl_map. apply H.
  - simpl. inversion HB. split. reflexivity. constructor. apply indexl_map. apply H.
  (* tabs *)
  - simpl in *. inversion HB.  
    destruct (transform2 t). 
    destruct (IHhas_type t0 b0 kenv eq_refl). subst. auto.
  - simpl in *. inversion HB. 
    destruct (transform2 t). 
    destruct (IHhas_type t0 b0 kenv eq_refl). subst. split; auto. 
  (* tapp *)
  - simpl in *. destruct (transform2 f) as (rf & bf).
    destruct (transform2 t) as (rt & bt).
    specialize (IHhas_type1 rf bf).
    specialize (IHhas_type2 rt bt). 
    destruct bf; destruct bt; inversion HB; 
    try (intros k HK).
    + econstructor; eauto. econstructor. apply IHhas_type1; eauto.
      econstructor. apply IHhas_type2; eauto. repeat econstructor.
    + econstructor; eauto. econstructor. apply IHhas_type1; eauto.
      repeat econstructor. apply IHhas_type2. reflexivity.
    + econstructor; eauto. econstructor. apply IHhas_type2; eauto.
      repeat econstructor. apply IHhas_type1. reflexivity.
    + econstructor; eauto. 
  - simpl in *. destruct (transform2 f) as (rf & bf).
    destruct (transform2 t) as (rt & bt).
    destruct (IHhas_type1 rf bf kenv eq_refl).
    destruct (IHhas_type2 rt bt kenv eq_refl). subst.
    inversion HB. split; econstructor; eauto.
  (* treset *)
  - simpl in *. destruct (transform2 t) as (r & br).
    specialize (IHhas_type r br kenv eq_refl). destruct br; inversion HB.
    + apply IHhas_type. repeat econstructor.
    + apply IHhas_type.
  - simpl in *. destruct (transform2 t) as (r & br).
    specialize (IHhas_type r br kenv eq_refl). destruct br; inversion HB; auto.
    split. auto. simpl. apply IHhas_type. repeat econstructor.
  (* tshift *)
  - simpl in *. inversion HB. 
    intros k HK. econstructor; eauto. econstructor.
    destruct (transform2 t). specialize (IHhas_type t0 b0 kenv eq_refl).
    apply IHhas_type.
  (* tcontabs *)
  - simpl in *. destruct (transform2 t) as (r & br).
    specialize (IHhas_type r br (B.TFun (trans_ty T2) (trans_ty R) :: kenv) eq_refl). 
    destruct br; inversion HB; eauto.
    + econstructor. econstructor. econstructor; eauto. repeat econstructor.  
  - simpl in *. destruct (transform2 t) as (r & br). 
    specialize (IHhas_type r br (B.TFun (trans_ty T2) (trans_ty R) :: kenv) eq_refl).
    destruct br; inversion HB; split; eauto.
    + constructor. constructor. apply IHhas_type. repeat econstructor.
    + constructor. constructor. econstructor; eauto. repeat econstructor.
  (* tcontapp *)
  - simpl in *.    
    destruct (transform2 f) as (rf & bf).
    destruct (transform2 t) as (rt & bt).
    specialize (IHhas_type1 rf bf). 
    specialize (IHhas_type2 rt bt).
    destruct bf; destruct bt; inversion HB; try (intros K HK).
    + econstructor; eauto. econstructor. apply IHhas_type1; eauto. 
      econstructor. apply IHhas_type2; eauto. repeat econstructor.
    + econstructor; eauto. econstructor. apply IHhas_type1; eauto.
      econstructor. repeat econstructor. apply IHhas_type2. reflexivity.
    + econstructor; eauto. econstructor. apply IHhas_type2; auto.
      repeat econstructor. apply IHhas_type1. reflexivity.
    + repeat econstructor; eauto.
Qed.

Theorem transl_pre_types2 : forall t T,
  has_type [] None t T -> 
  B.has_type [] [] (fst (transform2 t)) (trans_ty T). 
Proof. 
  intros t T H. remember (transform2 t) as res. 
  destruct (res) as (t' & b). 
  simpl. pose proof (fundamental2 _ _ _ _ H t' b []) as HQ.
  simpl in HQ. rewrite <- Heqres in HQ. apply HQ. reflexivity.   
Qed.     

(* g for general *)
Fixpoint gtransform (t: tm) (o: option B.tm) : B.tm := 
  match o with 
  | None =>
    match t with 
    | ttrue => B.ttrue 
    | tfalse => B.tfalse 
    | tif cond tbranch ebranch => 
      B.tif (gtransform cond None) (gtransform tbranch None) (gtransform ebranch None)
    | tvar x => B.tvar x 
    | tabs t => B.tabs (gtransform t None)
    | tapp t1 t2 => B.tapp (gtransform t1 None) (gtransform t2 None)
    | treset e => gtransform e (Some id_abs)
    | tshift e => error_tm 
    | tcontabs e => (B.tabs (B.tabsk (gtransform e (Some (B.tvark 0)))))
    | tcontapp _ _  => error_tm
    end 
  | Some k => 
   match t with 
    | ttrue => (B.tapp k B.ttrue)
    | tfalse => (B.tapp k B.tfalse)
    | tif cond tbranch ebranch => 
        gtransform (cond) (Some (B.tabsk
          (B.tif (B.tvark 0) (
            gtransform tbranch (Some (shift k 0 1))
          ) (
            gtransform ebranch (Some (shift k 0 1))
          )
          )
        ))
    | tvar x => B.tapp k (B.tvar x)
    | tabs t => B.tapp k (B.tabs (gtransform t None))
    | tapp f t => 
        gtransform f (Some (B.tabsk (
            gtransform t (Some (B.tabsk (
                B.tapp (shift k 0 2) ( B.tapp (B.tvark 1) (B.tvark 0) )
              )
            ))
          )
        ))
    | treset e => B.tapp k (gtransform e (Some id_abs)) 
    | tshift e => B.tapp (B.tabs (gtransform e None)) (k)
    | tcontabs e => B.tapp k ((B.tabs (B.tabsk (gtransform e (Some (B.tvark 0))))))
    | tcontapp f t => 
        gtransform f (Some ( B.tabsk (
            gtransform t (Some ( B.tabsk (
                B.tapp (B.tapp (B.tvark 1) (B.tvark 0)) (shift k 0 2)
              )
            ))
          )
        )) 
    end 
  end.

Theorem transl_equiv : forall t k, 
  transform t = gtransform t None /\ transformK t k = gtransform t (Some k).
Proof.
  induction t; intros k; auto.
  - split. 
    + destruct (IHt1 k). destruct (IHt2 k). destruct (IHt3 k). 
      simpl. rewrite H, H1, H3. reflexivity.
    + simpl. destruct (IHt3 (shift k 0 1)). rewrite H0. 
      destruct (IHt2 (shift k 0 1)). rewrite H2. 
      destruct (IHt1 ((B.tabsk 
        (B.tif (B.tvark 0) (gtransform t2 (Some (shift k 0 1)))
        (gtransform t3 (Some (shift k 0 1))))))).
      rewrite H4. reflexivity.
  - split; destruct (IHt k); simpl; rewrite H; reflexivity.
  - split; simpl. destruct (IHt1 k). destruct (IHt2 k). rewrite H. rewrite H1.
    reflexivity. destruct (IHt2 
      (B.tabsk (B.tapp (shift k 0 2) (B.tapp (B.tvark 1) (B.tvark 0))))). 
      rewrite H0. destruct (IHt1 (B.tabsk
     (gtransform t2
        (Some (B.tabsk (B.tapp (shift k 0 2) (B.tapp (B.tvark 1) (B.tvark 0)))))))).
      rewrite H2. reflexivity. 
  - split; simpl; destruct (IHt id_abs); rewrite H0; reflexivity.     
  - split; simpl. reflexivity. destruct (IHt k). rewrite H. reflexivity.
  - split; simpl; destruct (IHt (B.tvark 0)); rewrite H0; reflexivity.
  - split; simpl. reflexivity. 
    destruct (IHt2 (B.tabsk (B.tapp (B.tapp (B.tvark 1) (B.tvark 0)) (shift k 0 2)))).
    rewrite H0. destruct (IHt1 (B.tabsk
     (gtransform t2
        (Some (B.tabsk (B.tapp (B.tapp (B.tvark 1) (B.tvark 0)) (shift k 0 2))))))).
    rewrite H2. reflexivity.  
Qed.

End STLC_CONT.
