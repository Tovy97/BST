From FDS Require Import BST.

From Coq Require Import Arith.Arith.
From Coq Require Import Arith.Compare_dec.
From Coq Require Import Arith.EqNat.
From Coq Require Import Init.Decimal.
From Coq Require Import Init.Nat.
From Coq Require Import Bool.Bool.
From Coq Require Import Lists.List.
Import ListNotations.
Require Import Omega.
Require Import Lia.

Theorem correct_iif_correct_fun :
  forall bst,
    correct bst <-> correct_fun bst = true.
Proof.
  intros.
  split; intros.
  {
    induction H; trivial.
    simpl.
    repeat (rewrite andb_true_iff; split); assumption.
  } {
    induction bst; constructor;
    simpl in *;
    repeat (rewrite andb_true_iff in H);
    repeat (destruct H); trivial.
    - apply IHbst1. assumption.
    - apply IHbst2. assumption.
  }
Qed.

Theorem child_correct :
  forall el l r,
    correct (Node l el r) -> correct l /\ correct r.
Proof.
  intros.
  split; inversion H; subst; assumption.
Qed.

Theorem delete2_l :
  forall l r a el,
    correct (Node l el r) -> 
      el ?= a = Gt -> 
      delete2 a (Node l el r) = Node (delete2 a l) el r.
Proof.
  intros.
  remember (Node l el r) as bst eqn:R.
  destruct H; simpl; inversion R; subst; try rewrite H0; trivial.
Qed.

Theorem delete2_r :
  forall l r a el,
    correct (Node l el r) -> 
      el ?= a = Lt -> 
      delete2 a (Node l el r) = Node l el (delete2 a r).
Proof.
  intros.
  remember (Node l el r) as bst eqn:R.
  destruct H; simpl; inversion R; subst; try rewrite H0; trivial.
Qed.

Lemma insert_correct_on_r :
  forall e a bst,
    e < a ->
    correct_on_r e bst = true ->
    correct_on_r e (insert a bst) = true.
Proof.
  intros.
  induction bst; unfold correct_on_r in *; simpl in *.
  - rewrite <- Nat.ltb_lt in H. rewrite andb_true_iff.
    split; try assumption; trivial.
  - destruct (n ?= a) eqn:D; simpl.
    + assumption.
    + rewrite forallb_app. rewrite forallb_app in H0.
      rewrite andb_true_iff. rewrite andb_true_iff in H0. destruct H0.
      split.
      * assumption.
      * apply IHbst1 in H0. simpl. rewrite andb_true_iff. 
        split; simpl in H1; rewrite andb_true_iff in H1; 
        destruct H1; try apply IHbst2 in H2; assumption.
    + rewrite forallb_app. rewrite forallb_app in H0.
      rewrite andb_true_iff. rewrite andb_true_iff in H0. destruct H0.
      split; try apply IHbst1 in H0; assumption. 
Qed.

Lemma insert_correct_on_l :
  forall e a bst,
    a < e ->
    correct_on_l e bst = true ->
    correct_on_l e (insert a bst) = true.
Proof.
  intros.
  induction bst; unfold correct_on_l in *; simpl in *.
  - rewrite <- Nat.ltb_lt in H. rewrite andb_true_iff.
    split; try assumption; trivial.
  - destruct (n ?= a) eqn:D; simpl.
    + assumption.
    + rewrite forallb_app. rewrite forallb_app in H0.
      rewrite andb_true_iff. rewrite andb_true_iff in H0. destruct H0.
      split.
      * assumption.
      * apply IHbst1 in H0. simpl. rewrite andb_true_iff. 
        split; simpl in H1; rewrite andb_true_iff in H1; 
        destruct H1; try apply IHbst2 in H2; assumption.
    + rewrite forallb_app. rewrite forallb_app in H0.
      rewrite andb_true_iff. rewrite andb_true_iff in H0. destruct H0.
      split; try apply IHbst1 in H0; assumption. 
Qed.

Theorem insert_correct :
  forall a bst,
    correct bst -> correct(insert a bst).
Proof.
  intros.
  induction H; simpl in *.
  - constructor; trivial; try constructor.
  - destruct (e ?= a) eqn:D.
    + constructor; assumption.
    + constructor; try assumption.
      apply nat_compare_lt in D.
      apply insert_correct_on_r; assumption.
    + constructor; try assumption. apply nat_compare_gt in D.
      apply insert_correct_on_l; assumption.
Qed.

Theorem fromList_correct :
  forall l,
    correct(fromList l).
Proof.
  intros.
  induction l.
  - simpl. constructor.
  - simpl.  apply insert_correct. assumption.
Qed.

Theorem insert_ismember :
  forall bst el,
    correct bst -> isMember el (insert el bst) = true.
Proof.
  intros.
  induction H.
  - simpl. destruct (el ?= el) eqn:D.
    + trivial.
    + rewrite <- nat_compare_lt in D. omega.
    + rewrite <- nat_compare_gt in D. omega.
  - simpl. destruct (e ?= el) eqn:D.
    + simpl. rewrite D. trivial. 
    + simpl. rewrite D. trivial. 
    + simpl. rewrite D. trivial.
Qed.

Theorem insert_size1 :
  forall bst el,
    correct bst -> 
      isMember el bst = true -> size (insert el bst) = size bst.
Proof.
  intros.
  induction H.
  - simpl in H0. discriminate H0.
  - simpl in *. destruct (e ?= el) eqn : D.
      * trivial.
      * simpl. rewrite IHcorrect2; trivial.
      * simpl. rewrite IHcorrect1; trivial.
Qed.

Theorem insert_size2 :
  forall bst el,
    correct bst -> 
      isMember el bst = false -> size (insert el bst) = size bst + 1.
Proof.
  intros.
  induction H.
  - trivial.
  - simpl in *. destruct (e ?= el) eqn : D.
      * discriminate H0.
      * simpl.  rewrite IHcorrect2; trivial. lia.
      * simpl.  rewrite IHcorrect1; trivial. lia.
Qed.

Theorem insert_size :
  forall bst el,
    correct bst -> 
      (isMember el bst = true -> size (insert el bst) = size bst) /\
      (isMember el bst = false -> size (insert el bst) = size bst + 1).
Proof.
  intros.
  split; intros.
  {
    induction H.
    - simpl in H0. discriminate H0.
    - simpl in *. destruct (e ?= el) eqn : D.
      * trivial.
      * simpl. rewrite IHcorrect2; trivial.
      * simpl. rewrite IHcorrect1; trivial.
  } { 
    induction H.
    - trivial. 
    - simpl in *. destruct (e ?= el) eqn : D.
      * discriminate H0.
      * simpl. rewrite IHcorrect2; trivial. lia.
      * simpl. rewrite IHcorrect1; trivial. lia.
  }
Restart.
  intros.
  split; intros.
  - apply insert_size1; assumption.
  - apply insert_size2; assumption.
Qed.

Theorem toList_size :
  forall bst,
    correct bst -> length (toList bst) = size bst.
Proof.
  intros.
  induction H; trivial.
  simpl in *. 
  rewrite <- IHcorrect1.
  rewrite <- IHcorrect2.
  rewrite app_length. simpl. lia.
Qed.

Theorem size_isEmpty :
  forall bst,
    correct bst ->
    isEmpty bst = true <-> size bst = 0.
Proof.
  intros.
  split;intros.
  {
    destruct H; inversion H0; trivial.
  } {
    destruct H; trivial.
    simpl in *. destruct (size l); destruct (size r); inversion H0.
  }
Qed.

Lemma eq1: 
  forall e el,
  (e =? el) = true <-> e = el.
Proof.
  intros. split; intros.
  - apply beq_nat_true in H. assumption.
  - subst. rewrite <- beq_nat_refl. trivial.
Qed.

Lemma eq2: 
  forall e el,
  (e ?= el) = Eq <-> e = el.
Proof.
  intros. split; intros.
  - apply nat_compare_eq in H. assumption.
  - apply Nat.compare_eq_iff. trivial.
Qed.

Lemma eq3 :
  forall e el,
  (e ?= el) = Eq <-> (e =? el) = true.
Proof.
  intros. split; intros.
  - rewrite eq2 in H. rewrite eq1. trivial.
  - rewrite eq2. rewrite eq1 in H. trivial.
Qed.

Theorem max_height :
  forall bst,
    correct bst ->
    (height bst ?= size(bst) = Lt \/ height bst ?= size(bst) = Eq).
Proof.
  intros.
  induction H; simpl in *.
  - right. trivial.
  - destruct IHcorrect1; destruct IHcorrect2; 
    simpl in *; destruct (size l + size r + 1) eqn : D; 
    try lia; rewrite <- nat_compare_lt; rewrite eq2.
    + rewrite <- nat_compare_lt in H3.
      rewrite <- nat_compare_lt in H4.
      lia.
    + rewrite <- nat_compare_lt in H3.
      apply nat_compare_eq in H4.
      lia.
    + apply nat_compare_eq in H3.
      rewrite <- nat_compare_lt in H4.
      lia.
    + apply nat_compare_eq in H3.
      apply nat_compare_eq in H4.
      destruct n; rewrite plus_comm in D; inversion D.
      * apply plus_is_O in H6. destruct H6. lia.
      * destruct H6. lia.
Qed.

Theorem list_head_last :
  forall bst,
  correct bst ->
    hd_error (toList bst) = getMin bst /\
    hd_error (rev (toList bst)) = getMax bst.
Proof.
  intros.
  split.
  {
    induction H; trivial.
    simpl in *.
    destruct l eqn:D; trivial.
    destruct (toList (Node b1 n b2)) eqn:D1.
    - inversion D1. destruct (toList b1); simpl in *; inversion H4.
    - assumption.
  }
  {
    induction H; trivial.
    simpl in *.
    rewrite rev_app_distr.
    simpl. rewrite <- app_assoc. simpl.
    destruct r eqn:D; simpl in *; trivial.
    destruct (rev (toList b1 ++ n :: toList b2)) eqn:D1; trivial.
    simpl in *.
    destruct (toList b1); simpl in *; inversion D1.
    - destruct (rev (toList b2)); simpl in *; inversion H4.
    - destruct (rev (l0 ++ n :: toList b2)); simpl in *; inversion H4.
  }
Qed.

Theorem delete_correct :
  forall a bst,
    correct bst -> correct(delete a bst).
Proof.
  intros.
  destruct H; unfold delete; apply fromList_correct.
Qed.

Theorem delete2_correct :
  forall a bst,
    correct bst -> correct(delete2 a bst).
Proof.
  intros.
  induction H.
  - constructor.
  - simpl in *. destruct (e ?= a) eqn:D.
    + destruct (getMin r) eqn:D1; try assumption.
      apply nat_compare_eq in D. subst.
      admit.
    + constructor; try assumption. admit.
    + constructor; try assumption. admit.
Admitted.

Lemma insert_ismember2 :
  forall bst a b,
    correct bst ->
    isMember a bst = false ->
    b <> a ->
    isMember a (insert b bst) = false.
Proof.
  intros.
  induction bst.
  - simpl. destruct (b ?= a) eqn:D; trivial.
    apply nat_compare_eq in D. subst. lia.
  - simpl in *. destruct (n ?= b) eqn:D1.
    + assumption.
    + simpl in *. destruct (n ?= a) eqn:D2; try assumption.
      * apply IHbst2; try assumption.
        apply child_correct in H. destruct H; assumption.
    + simpl in *. destruct (n ?= a) eqn:D2; try assumption.
      * apply IHbst1; try assumption.
        apply child_correct in H. destruct H; assumption.
Qed.


Theorem delete_equals_delete2 :
  forall bst el,
    correct bst ->
      BSTequals (delete el bst) (delete2 el bst) = true.
Proof.
  intros.
  induction H; unfold delete; trivial.
  simpl in *. destruct (e =? el) eqn : D; simpl in *.
  - rewrite <- eq3 in D. rewrite D. admit.
  - admit.
Admitted.

Theorem delete_ismember :
  forall bst el,
    correct bst -> isMember el (delete el bst) = false.
Proof.
  intros.
(*   generalize dependent el. *)
  induction H;intros; trivial.
  unfold delete in *. simpl. destruct (toList l).
  - simpl. admit.
  -  simpl. admit.
Admitted.

Theorem delete_size :
  forall bst el,
    correct bst -> 
      (isMember el bst = true -> size (delete el bst) = size bst - 1) /\ 
      (isMember el bst = false -> size (delete el bst) = size bst).
Proof.
  intros.
  unfold delete in *; split; intros.
  {
    induction H; trivial.
    simpl in *.
    destruct (e ?= el) eqn : D.
    - admit.
    - apply IHcorrect2 in H0. admit.
    - apply IHcorrect1 in H0. admit.
  } {
    induction H; trivial.
    simpl in *.
    destruct (e ?= el) eqn : D.
    - admit.
    - apply IHcorrect2 in H0. admit.
    - apply IHcorrect1 in H0. admit.
  }
Admitted.

Fixpoint not_in (l : list nat) (n : nat): bool :=
  match l with
    | nil => true
    | h :: t => 
        match h ?= n with 
          | Eq => false
          | _ => not_in t n
        end
  end.

Fixpoint only_one (l : list nat) (n : nat): bool :=
  match l with
    | nil => false
    | h :: t => 
        match h ?= n with 
          | Eq => not_in t n
          | _ => only_one t n
        end
  end.

Lemma help :
  forall l1 l2 n,
  not_in l1 n = true ->
  not_in l2 n = true ->
  not_in (l1 ++ l2) n = true.
Proof.
  intros.
  induction l1.
  - trivial.
  - simpl in *.
    destruct (a ?= n) eqn:D1.
    + discriminate H.
    + apply IHl1 in H. assumption.
    + apply IHl1 in H. assumption. 
Qed.

Lemma help2 :
  forall l1 l2 n,
  not_in (l1 ++ l2) n = true ->
  not_in l1 n = true /\ not_in l2 n = true.
Proof.
  intros.
  split; intros.
  {
    induction l1.
    - trivial.
    - simpl in *.
      destruct (a ?= n) eqn:D1.
      + discriminate H.
      + apply IHl1 in H. assumption.
      + apply IHl1 in H. assumption.
  } { 
    induction l1.
    - trivial.
    - simpl in *.
      destruct (a ?= n) eqn:D1.
      + discriminate H.
      + apply IHl1 in H. assumption.
      + apply IHl1 in H. assumption.
  }
Qed.

Lemma help3 :
  forall l1 l2 n,
  only_one (l1 ++ l2) n = true ->
  not_in l1 n = true \/ not_in l2 n = true.
Proof.
  intros.
  induction l1.
  - simpl. left. trivial.
  - simpl in *.
    destruct (a ?= n) eqn:D1.
    + apply help2 in H. destruct H. right. assumption.
    + apply IHl1 in H. assumption.
    + apply IHl1 in H. assumption. 
Qed.

Lemma help4 :
  forall l1 l2 n,
  only_one (l1 ++ l2) n = true ->
  only_one l1 n = true \/ only_one l2 n = true.
Proof.
  intros.
  induction l1.
  - simpl in *. right. assumption.
  - simpl in *.
    destruct (a ?= n) eqn:D1.
    + apply help2 in H. destruct H. left. assumption.
    + apply IHl1 in H. assumption.
    + apply IHl1 in H. assumption.
Qed.

Theorem toList_distinct:
  forall bst n,
    correct bst -> 
    (isMember n bst = true -> only_one (toList bst) n = true) /\
    (isMember n bst = false -> not_in (toList bst) n = true).
Proof.
  intros.
  split; intros.
  { induction H;trivial.
    simpl in *. destruct (e ?= n) eqn : D.
    - admit.
    - apply IHcorrect2 in H0. admit.
    - apply IHcorrect1 in H0. admit.
  } {
    induction H;trivial.
    simpl in *. destruct (e ?= n) eqn : D.
    - admit.
    - apply IHcorrect2 in H0. admit.
    - apply IHcorrect1 in H0. admit.
Admitted.

Fixpoint sorted (l : list nat) : bool :=
  match l with
    | nil => true
    | h1 :: t => 
        match t with 
          | nil => true
          | h2 :: _ =>
              match h1 ?= h2 with
                | Lt => sorted t
                | _ => false
              end
        end
  end.

Lemma el_mag_getmax_l :
  forall l el r max,
    correct (Node l el r) ->
    getMax l = Some(max) ->
    max ?= el = Lt.
Proof.
  intros.
  induction H; trivial. 
  - admit.
Admitted.

Lemma el_min_getmin_r :
  forall min l el r,
  correct (Node l el r) ->
    getMin r = Some(min) ->
    el ?= min = Lt.
Proof.
  intros.
  induction H; trivial. 
  - admit.
Admitted.

Theorem toList_sorted :
  forall bst,
    correct bst -> 
      sorted (toList bst) = true.
Proof.
  intros.
  induction H; trivial.
  simpl in *. 
  destruct (toList l) eqn : D1; simpl in *.
  destruct (toList r) eqn : D2; simpl in *; trivial; rewrite IHcorrect2. 
  - admit.
  - admit.
Admitted.