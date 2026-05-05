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

(* \gamma, current continuation capability |- tm : ty *)
Inductive has_type : tenv -> (option ty) -> tm -> ty -> Type := 
  (* values *)
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

  (* redexes *)
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

(* Fixpoint transform { env K t T } (H : has_type env K t T) : B.tm := 
match H in (has_type _ _ _ _) return B.tm with 
  | t_true _ _ => B.ttrue
  | t_false _ _ => B.tfalse
  | t_var env R x T H => B.tvar x
  | t_abs env R t T1 T2 HT =>
    B.tabs (transform3 HT)

  | t_if env R cond tbranch ebranch T HTC HTT HTE =>
    B.tif (transform3 HTC) (transform3 HTT) (transform3 HTE)

  | t_app env R f t T1 T2 HF HT =>  
    B.tapp (transform3 HF) (transform3 HT)

  | _ => id_abs
end. *)

End STLC_CONT_TY.




