From Stdlib Require Export Arith.EqNat.
From Stdlib Require Export Init.Nat.
Require Import Stdlib.Arith.Arith.
Require Import Stdlib.Program.Equality.
Require Import Stdlib.Lists.List.
From Stdlib Require Import Psatz. (* for lia *)
Require Import Stdlib.Arith.Compare_dec.
Import ListNotations.

Require Import tactics.

(* Theory of envs as lists of deBruijn levels *)

(* update entry *)
Fixpoint update {A} (σ : list A) (l : nat) (v : A) : list A :=
  match σ with
  | [] => σ
  | a :: σ' =>
      if (Nat.eqb l (length σ')) then (v :: σ') else (a :: (update σ' l v ))
  end.

Fixpoint insert {A} (σ : list A) (l : nat) (v : A) : list A :=
  match σ with
  | [] => σ
  | a :: σ' =>
      if (Nat.eqb l (length σ')) then (a :: v :: σ') else (a :: (insert σ' l v ))
  end.

(* Look up a free variable (deBruijn level) in env   *)
Fixpoint indexr {X : Type} (n : nat) (l : list X) : option X :=
  match l with
    | [] => None
    | a :: l' =>
      if (Nat.eqb n (length l')) then Some a else indexr n l'
  end.

Lemma indexr_head : forall {A} {x : A} {xs}, indexr (length xs) (x :: xs) = Some x.
  intros. simpl. destruct (Nat.eqb (length xs) (length xs)) eqn:Heq. auto.
  apply  Nat.eqb_neq  in Heq. contradiction.
Qed.

Lemma indexr_length : forall {A B} {xs : list A} {ys : list B}, length xs = length ys -> forall {x}, indexr x xs = None <-> indexr x ys = None.
Proof.
  intros A B xs.
  induction xs; intros; destruct ys; split; simpl in *; intros; eauto; try lia.
  - inversion H. destruct (PeanoNat.Nat.eqb x (length xs)). discriminate.
    specialize (IHxs _ H2 x). destruct IHxs. auto.
  - inversion H. rewrite <- H2 in H0. destruct (PeanoNat.Nat.eqb x (length xs)). discriminate.
    specialize (IHxs _ H2 x). destruct IHxs. auto.
Qed.

Lemma indexr_skip : forall {A} {x : A} {xs : list A} {i}, i <> length xs -> indexr i (x :: xs) = indexr i xs.
Proof.
  intros.
  rewrite <- PeanoNat.Nat.eqb_neq in H. auto.
  simpl. rewrite H. reflexivity.
Qed.

Lemma indexr_skips : forall {A} {xs' xs : list A} {i}, i < length xs -> indexr i (xs' ++ xs) = indexr i xs.
  induction xs'; intros; intuition.
  replace ((a :: xs') ++ xs) with (a :: (xs' ++ xs)).
  rewrite indexr_skip. eauto. rewrite length_app. lia. auto.
Qed.

Lemma indexr_var_some :  forall {A} {xs : list A} {i}, (exists x, indexr i xs = Some x) <-> i < length xs.
Proof.
  induction xs; intros; split; intros. inversion H. inversion H0.
  inversion H. inversion H. simpl in H0. destruct (PeanoNat.Nat.eqb i (length xs)) eqn:Heq.
  apply  Nat.eqb_eq  in Heq. rewrite Heq. auto. inversion H.
  simpl in H. rewrite Heq in H. apply IHxs in H. simpl. lia.
  simpl. destruct (PeanoNat.Nat.eqb i (length xs)) eqn:Heq.
  exists a. reflexivity. apply  Nat.eqb_neq  in Heq. simpl in H.
  apply IHxs. lia.
Qed.

(* easier to use for assumptions without existential quantifier *)
Lemma indexr_var_some' :  forall {A} {xs : list A} {i x}, indexr i xs = Some x -> i < length xs.
Proof.
  intros. apply indexr_var_some. exists x. auto.
Qed.

Lemma indexr_var_none :  forall {A} {xs : list A} {i}, indexr i xs = None <-> i >= length xs.
Proof.
  induction xs; intros; split; intros.
  simpl in *. lia. auto.
  simpl in H.
  destruct (PeanoNat.Nat.eqb i (length xs)) eqn:Heq.
  discriminate. apply IHxs in H. apply  Nat.eqb_neq  in Heq. simpl. lia.
  assert (Hleq: i >= length xs). {
    simpl in H. lia.
  }
  apply IHxs in Hleq. rewrite <- Hleq.
  apply indexr_skip. simpl in H. lia.
Qed.

Lemma indexr_insert_ge : forall {A} {xs xs' : list A} {x} {y}, x >= (length xs') -> indexr x (xs ++ xs') = indexr (S x) (xs ++ y :: xs').
  induction xs; intros.
  - repeat rewrite app_nil_l. pose (H' := H).
    rewrite <- indexr_var_none in H'.
    rewrite H'. symmetry. apply indexr_var_none. simpl. lia.
  - replace ((a :: xs) ++ xs') with (a :: (xs ++ xs')); auto.
    replace ((a :: xs) ++ y :: xs') with (a :: (xs ++ y :: xs')); auto.
    simpl. replace (length (xs ++ y :: xs')) with (S (length (xs ++ xs'))).
    destruct (Nat.eqb x (length (xs ++ xs'))) eqn:Heq; auto.
    repeat rewrite length_app. simpl. lia.
Qed.

Lemma indexr_insert_lt : forall {A} {xs xs' : list A} {x} {y}, x < (length xs') -> indexr x (xs ++ xs') = indexr x (xs ++ y :: xs').
  intros.
  rewrite indexr_skips; auto.
  erewrite indexr_skips.
  erewrite indexr_skip. auto.
  lia. simpl. lia.
Qed.

Lemma indexr_insert:  forall {A} {xs xs' : list A} {y}, indexr (length xs') (xs ++ y :: xs') = Some y.
  intros. induction xs.
  - replace ([] ++ y :: xs') with (y :: xs'); auto. apply indexr_head.
  - simpl. rewrite IHxs. rewrite length_app. simpl.
    destruct (PeanoNat.Nat.eqb (length xs') (length xs + S (length xs'))) eqn:Heq; auto.
    apply  Nat.eqb_eq  in Heq. lia.
Qed.

Lemma update_length : forall {A} {σ : list A} {l v}, length σ = length (update σ l v).
  induction σ; simpl; intuition.
  destruct (Nat.eqb l (length σ)) eqn:Heq; intuition.
  simpl. congruence.
Qed.

Lemma extends_length: forall {A} (H' H: list A), length H <= length (H' ++ H).
Proof.  intros. induction H'; simpl. auto. lia.
Qed.
#[global] Hint Resolve extends_length : core.

Lemma indexr_extend : forall  {A} (H' H: list A) x (v:A),
    indexr x H = Some v <-> indexr x (H'++H) = Some v /\ x < length H. 
Proof.
    intros. split; intros; intuition; auto.
    apply indexr_var_some' in H0 as H0'.
    assert (Nat.eqb x (length H) = false) as E. eapply  Nat.eqb_neq; eauto. lia.
    rewrite indexr_skips; auto.
    apply indexr_var_some' in H0. auto.
    rewrite <- H1. rewrite indexr_skips; auto.
 Qed.

Lemma indexr_extend1: forall {A} (H: list A) x v (vx: A),
    indexr x H = Some v <-> indexr x (vx::H) = Some v /\ x < length H. 
Proof. 
    intros. split; intros. 
    eapply indexr_extend with (H' := [vx]) in H0. intuition.
    erewrite indexr_extend with (H' := [vx]); eauto.
Qed.

Lemma update_indexr_miss : forall {A} {σ : list A} {l v l'}, l <> l' ->  indexr l' (update σ l v) = indexr l' σ.
  induction σ; simpl; intuition.
  destruct (Nat.eqb l (length σ)) eqn:Hls; destruct (Nat.eqb l' (length σ)) eqn:Hl's.
  apply  Nat.eqb_eq  in Hls. apply  Nat.eqb_eq  in Hl's. rewrite <- Hl's in Hls. contradiction.
  simpl. rewrite Hl's. auto.
  simpl. rewrite <- update_length. rewrite Hl's. auto.
  simpl. rewrite <- update_length. rewrite Hl's. apply IHσ. auto.
Qed.

Lemma update_indexr_hit : forall {A} {σ : list A} {l v}, l < length σ -> indexr l (update σ l v) = Some v.
  induction σ; simpl; intuition auto with * .
  destruct (Nat.eqb l (length σ)) eqn:Hls.
  apply  Nat.eqb_eq  in Hls. rewrite Hls. apply indexr_head.
  simpl. rewrite <- update_length. rewrite Hls. apply  Nat.eqb_neq  in Hls.
  apply IHσ. lia.
Qed.

Lemma update_commute : forall {A} {σ : list A} {i j vi vj}, i <> j -> (update (update σ i vi) j vj) = (update (update σ j vj) i vi).
  induction σ; simpl; intuition.
  destruct (Nat.eqb i (length σ)) eqn:Heq.
  - assert (Heq' : Nat.eqb j (length σ) = false).
    apply  Nat.eqb_eq  in Heq. rewrite  Nat.eqb_neq . lia.
    rewrite Heq'. simpl. rewrite Heq'. rewrite <- update_length.
    rewrite Heq. auto.
  - destruct (Nat.eqb j (length σ)) eqn:Heq'; simpl.
    all: repeat rewrite <- update_length.
    all: rewrite Heq. all: rewrite Heq'. auto.
    rewrite IHσ; auto.
Qed.

Lemma update_inv : forall {A} {l : list A} {i v}, i > length l -> update l i v = l.
Proof.
  induction l; intros; simpl; auto.
  bdestruct (i =? length l). simpl in H. lia.
  bdestruct (i <? length l). simpl in H. lia.
  assert (length l < i) by lia. f_equal. apply IHl. auto.
Qed.

Lemma indexr_skips' : forall {A} {xs xs' : list A} {i}, i >= length xs -> indexr i (xs' ++ xs) = indexr (i - length xs) xs'.
  induction xs; intros; intuition.
  - rewrite app_nil_r. simpl. rewrite Nat.sub_0_r. auto.
  - simpl in *. destruct i; try lia.
    rewrite <- indexr_insert_ge; try lia.
    rewrite IHxs. simpl. auto. lia.
Qed.

Fixpoint delete_nth (n : nat) {A} (l : list A) : list A :=
  match l with
  | nil       => nil
  | cons x xs => if (Nat.eqb n (length xs)) then xs else x :: (delete_nth n xs)
  end. 

(* Theory of envs as lists of de Bruijn indices *)

(* Look up a free variable (de Bruijn index) in environment *)
Fixpoint indexl {X: Type} (n: nat) (l: list X) : option X := 
  match n, l with 
  | 0, x :: l' => Some x
  | 0, _ => None
  | S m, [] => None
  | S m, x :: t => indexl m t
  end
.

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

Lemma indexl_var_some : forall {A} {l : list A} {i}, 
  (exists v, indexl i l = Some v) <-> i < length l.
Proof.
  induction l; intros; split; intros.
  - inversion H. destruct i; inversion H0.
  - simpl in *. inversion H.
  - simpl. destruct i. apply Nat.lt_0_succ. 
    rewrite <- Nat.succ_lt_mono. apply IHl. 
    destruct H. simpl in H. exists x; assumption.
  - destruct i. exists a. simpl. reflexivity.
    simpl in *. rewrite <- Nat.succ_lt_mono in H. apply IHl. apply H.   
Qed.

Lemma indexl_var_some' : forall {A} {l : list A} {i v}, 
  indexl i l = Some v -> i < length l.
Proof.
  intros. apply indexl_var_some. exists v. assumption.
Qed.

Lemma indexl_var_none : forall {A} {xs : list A} {x}, 
  indexl x xs = None <-> x >= length xs.
Proof.
  induction xs; split; intros.
  - destruct x; simpl in *; lia.
  - destruct x; simpl in *; reflexivity.
  - destruct x; simpl in *. inversion H. apply -> Nat.succ_le_mono.
    apply IHxs. apply H.
  - destruct x; simpl in *. inversion H. apply IHxs.
    apply Nat.succ_le_mono in H. apply H.  
Qed.

Lemma indexl_skips : forall {A} {l l' : list A} {i}, 
  i < length l -> indexl i (l ++ l') = indexl i l.
Proof.
  induction l; intros. 
  - destruct i; simpl in *; inversion H.
  - simpl. destruct i; auto. simpl in *. rewrite <- Nat.succ_lt_mono in H.  
    auto.
Qed.

Lemma indexl_extend : forall A l l' (i: nat) (v: A),
  indexl i l = Some v -> indexl i (l ++ l') = Some v.
Proof.
  induction l; intros.
  - destruct i; simpl in *; inversion H.
  - destruct i; simpl in *; auto. 
Qed.  

Lemma indexl_insert : forall {A} {xs xs' : list A} {y}, 
  indexl (length xs) (xs ++ y :: xs') = Some y.
Proof.
  intros. induction xs.
  - replace ([] ++ y :: xs') with (y :: xs'); auto. 
  - simpl. rewrite IHxs. auto. 
Qed.

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