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
    - simpl. 
      destruct (edx ?= el) eqn : D. 
      + discriminate H0. 
      + discriminate H0. 
      + simpl in IHcorrect. assumption.
    - simpl. 
      destruct (esx ?= el) eqn : D. 
      + discriminate H0.
      + simpl in IHcorrect. assumption.
      + discriminate H0. 
    - simpl. 
      destruct (esx ?= el) eqn : D1. 
      + discriminate H2.
      + destruct (edx ?= el) eqn : D2.
        * discriminate H1.
        * discriminate H1.
        * simpl in IHcorrect1. rewrite IHcorrect1. simpl in IHcorrect2. assumption.
      + discriminate H2.
  } {
    induction bst.
    - constructor.
    - destruct bst1; destruct bst2.
      + constructor.
      + constructor. 
        * apply IHbst2. simpl in H.
          destruct (n0 ?= n).
          { discriminate H. }
          { discriminate H. }
          { simpl. assumption. }
        * simpl in H. destruct (n0 ?= n).
          { discriminate H. }
          { discriminate H. }
          { trivial. }
      + constructor.
        * apply IHbst1. simpl in H.
          destruct (n0 ?= n).
          { discriminate H. } 
          { simpl. assumption. }
          { discriminate H. }
        * simpl in H. destruct (n0 ?= n).
          { discriminate H. }
          { trivial. }
          { discriminate H. }
      + constructor.
        * apply IHbst1. simpl in H.
          destruct (n0 ?= n).
          { discriminate H. }
          { destruct (n1 ?= n).
            { discriminate H. }
            { discriminate H. }
            { rewrite andb_true_iff in H. destruct H. simpl. assumption. }
          }
          { discriminate H. }
        * apply IHbst2. simpl in H.
          destruct (n0 ?= n).
          { discriminate H. }
          { destruct (n1 ?= n).
            { discriminate H. }
            { discriminate H. }
            { rewrite andb_true_iff in H. destruct H. simpl. assumption. }
          }
          { discriminate H. }
        * simpl in H. destruct (n0 ?= n).
          { discriminate H. }
          { destruct (n1 ?= n).
            { discriminate H. }
            { discriminate H. }
            { trivial. }
          }
          { discriminate H. }
        * simpl in H. destruct (n0 ?= n).
          { discriminate H. }
          { destruct (n1 ?= n).
            { discriminate H. }
            { discriminate H. }
            { trivial. }
          }
          { discriminate H. }
  }
Qed.

Theorem child_correct :
  forall el sx dx,
    correct (Node sx el dx) -> correct sx /\ correct dx.
Proof.
  intros.
  split.
  - inversion H; subst.
    + constructor.
    + constructor.
    + assumption.
    + assumption.
  - inversion H; subst.
    + constructor.
    + assumption.
    + constructor.
    + assumption.
Qed.

Theorem insert_correct :
  forall a bst,
    correct bst -> correct(insert a bst).
Proof.
  intros.
  induction H; simpl.
  - constructor.
  - destruct (el ?= a) eqn:D.
    + constructor.
    + constructor. 
      * constructor.
      * apply nat_compare_lt in D. apply nat_compare_gt in D. assumption. 
    + constructor.
      * constructor. 
      * apply nat_compare_gt in D. apply nat_compare_lt in D. assumption.
  - destruct (el ?= a) eqn:D1.
    + constructor; assumption.
    + simpl in IHcorrect. destruct (edx ?= a) eqn:D2; constructor; assumption.
    + simpl in IHcorrect. destruct (edx ?= a) eqn:D2.
      * constructor. 
        { constructor. }
        { assumption. }
        { assumption. }
        { apply  nat_compare_Gt_gt in D1. apply nat_compare_lt in D1. assumption. }
      * constructor.
        { constructor. }
        { assumption. }
        {  assumption.  }
        { apply  nat_compare_Gt_gt in D1. apply nat_compare_lt in D1. assumption. } 
      * constructor.
        { constructor. }
        { assumption. }
        { assumption.  }
        { apply  nat_compare_Gt_gt in D1. apply nat_compare_lt in D1. assumption. }
  - destruct (el ?= a) eqn:D1.
    + constructor; assumption.
    + simpl in IHcorrect. destruct (esx ?= a) eqn:D2.
      * constructor. 
        { assumption. }
        { constructor. }
        { apply nat_compare_lt in D1. apply nat_compare_gt in D1. assumption. }
        { assumption.  }
      * constructor.
        { assumption. }
        { constructor. }
        { apply nat_compare_lt in D1. apply nat_compare_gt in D1. assumption. }
        { assumption. } 
      * constructor.
        { assumption. }
        { constructor. }
        { apply nat_compare_lt in D1. apply nat_compare_gt in D1. assumption. }
        { assumption. } 
    + simpl in IHcorrect. destruct (esx ?= a) eqn:D2; constructor; assumption.
  - destruct (el ?= a) eqn:D1.
    + constructor; assumption.
    + simpl in IHcorrect2. destruct (edx ?= a) eqn:D2; constructor; assumption.
    + simpl in IHcorrect1. destruct (esx ?= a) eqn:D2; constructor; assumption.
Qed.

Theorem fromList_correct :
  forall l,
    correct(fromList l).
Proof.
  intros.
  induction l.
  - simpl. constructor.
  - simpl. destruct (fromList l). 
    + simpl. constructor.
    + apply insert_correct. assumption.
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
  - simpl. destruct (el0 ?= el) eqn:D.
    + simpl. destruct (el0 ?= el) eqn:D1.
      * trivial.
      * discriminate D.
      * discriminate D.
    + simpl. destruct (el0 ?= el) eqn:D1.
      * trivial.
      * destruct (el ?= el) eqn:D2.
        { trivial. }
        { rewrite <- nat_compare_lt in D2. omega. }
        { rewrite <- nat_compare_gt in D2. omega. }
      * discriminate D.
    + simpl. destruct (el0 ?= el) eqn:D1.
      * trivial.
      * discriminate D.
      * destruct (el ?= el) eqn:D2.
        { trivial. }
        { rewrite <- nat_compare_lt in D2. omega. }
        { rewrite <- nat_compare_gt in D2. omega. }
  - simpl. destruct (el0 ?= el) eqn:D.
    + simpl. destruct (el0 ?= el) eqn:D1.
      * trivial.
      * discriminate D.
      * discriminate D.
    + simpl in *. destruct (edx ?= el) eqn : D1.
      * simpl in *. destruct (el0 ?= el) eqn:D2.
        { trivial. } 
        { assumption. }
        { discriminate D. }
      * simpl in *. destruct (el0 ?= el) eqn:D2.
        { trivial. } 
        { assumption. }
        { discriminate D. }
      * simpl in *. destruct (el0 ?= el) eqn:D2.
        { trivial. } 
        { assumption. }
        { discriminate D. }
    + simpl. destruct (el0 ?= el) eqn:D1.
      * trivial.
      * discriminate D.
      * simpl. destruct (el ?= el) eqn:D2.
        { trivial. }
        { rewrite <- nat_compare_lt in D2. omega. }
        { rewrite <- nat_compare_gt in D2. omega. }
  - simpl. destruct (el0 ?= el) eqn:D.
    + simpl. destruct (el0 ?= el) eqn:D1.
      * trivial.
      * discriminate D.
      * discriminate D.
    + simpl. destruct (el0 ?= el) eqn:D1.
      * trivial.
      * simpl. destruct (el ?= el) eqn:D2.
        { trivial. }
        { rewrite <- nat_compare_lt in D2. omega. }
        { rewrite <- nat_compare_gt in D2. omega. }
      * discriminate D.
    + simpl in *. destruct (esx ?= el) eqn : D1.
      * simpl in *. destruct (el0 ?= el) eqn:D2.
        { trivial. }  
        { discriminate D. }
        { assumption. }
      * simpl in *. destruct (el0 ?= el) eqn:D2.
        { trivial. } 
        { discriminate D. }
        { assumption. }
      * simpl in *. destruct (el0 ?= el) eqn:D2.
        { trivial. } 
        { discriminate D. }
        { assumption. }
  - simpl. destruct (el0 ?= el) eqn:D.
    + simpl. destruct (el0 ?= el) eqn:D1.
      * trivial.
      * discriminate D.
      * discriminate D.
    + simpl. destruct (el0 ?= el) eqn:D1.
      * trivial.
      * simpl. destruct (el ?= el) eqn:D2.
        { trivial. }
        { rewrite <- nat_compare_lt in D2. omega. }
        { rewrite <- nat_compare_gt in D2. omega. }
      * discriminate D.
    + simpl in *. destruct (esx ?= el) eqn : D1; destruct (edx ?= el) eqn : D2; 
      repeat (
        simpl in *; 
        destruct (el0 ?= el); 
        trivial; 
        try discriminate D; 
        try assumption
      ).
Qed.

Theorem insert_size :
  forall bst el,
    correct bst -> 
      (isMember el bst = true -> size (insert el bst) = size bst) /\
      (isMember el bst = false -> size (insert el bst) = size bst + 1).
Proof.
  intros.
  induction H.
  - split; intros.
    + simpl in H. discriminate H.
    + trivial.
  - split; intros.
    + simpl in *. destruct (el0 ?= el) eqn : D.
      * trivial.
      * discriminate H.
      * discriminate H.
    + simpl in *. destruct (el0 ?= el) eqn : D.
      * discriminate H.
      * trivial.
      * trivial.
  - split; intros.
    + simpl in *. destruct (el0 ?= el) eqn : D.
      * trivial.
      * simpl in *. destruct (edx ?= el) eqn : D2.
        { trivial. }
        { simpl in *. destruct IHcorrect. apply H2 in H1. rewrite H1. trivial. }
        { simpl in *. destruct IHcorrect. apply H2 in H1. rewrite H1. trivial. } 
      * discriminate H1.
    + simpl in *. destruct (el0 ?= el) eqn : D.
      * discriminate H1.
      * simpl in *. destruct (edx ?= el) eqn : D2.
        { discriminate H1. }
        { simpl in *. destruct IHcorrect. apply H3 in H1. rewrite H1. trivial. }
        { simpl in *. destruct IHcorrect. apply H3 in H1. rewrite H1. trivial. }
      * simpl. omega. 
  - split; intros.
    + simpl in *. destruct (el0 ?= el) eqn : D.
      * trivial.
      * discriminate H1.
      * simpl in *. destruct (esx ?= el) eqn : D2.
        { trivial. }
        { simpl in *. destruct IHcorrect. apply H2 in H1. rewrite H1. trivial. }
        { simpl in *. destruct IHcorrect. apply H2 in H1. rewrite H1. trivial. }
    + simpl in *. destruct (el0 ?= el) eqn : D.
      * discriminate H1.
      * simpl. rewrite <- plus_n_O. trivial.
      * simpl in *. destruct (esx ?= el) eqn : D2.
        { discriminate H1. }
        { simpl in *. destruct IHcorrect. apply H3 in H1. rewrite H1. omega. }
        { simpl in *. destruct IHcorrect. apply H3 in H1. rewrite H1. omega. }
    - split; intros.
      + simpl in *. destruct (el0 ?= el) eqn : D.
        * trivial.
        * destruct (edx ?= el) eqn : D2.
          { trivial. }
          { simpl in *. destruct IHcorrect2. apply H4 in H3. rewrite H3. trivial. }
          { simpl in *. destruct IHcorrect2. apply H4 in H3. rewrite H3. trivial. }
        * simpl in *. destruct (esx ?= el) eqn : D2.
          { trivial. }
          { simpl in *. destruct IHcorrect1. apply H4 in H3. rewrite H3. trivial. }
          { simpl in *. destruct IHcorrect1. apply H4 in H3. rewrite H3. trivial. }
      + simpl in *. destruct (el0 ?= el) eqn : D.
        * discriminate H3.
        * destruct (edx ?= el) eqn : D2.
          { discriminate H3. }
          { simpl in *. destruct IHcorrect2. apply H5 in H3. rewrite H3. omega.  }
          { simpl in *. destruct IHcorrect2. apply H5 in H3. rewrite H3. omega.  }
        * simpl in *. destruct (esx ?= el) eqn : D2.
          { discriminate H3. }
          { simpl in *. destruct IHcorrect1. apply H5 in H3. rewrite H3. omega. }
          { simpl in *. destruct IHcorrect1. apply H5 in H3. rewrite H3. omega. }
Qed.

Theorem toList_size :
  forall bst,
    correct bst -> length (toList bst) = size bst.
Proof.
  intros.
  induction H.
  - trivial.
  - trivial.
  - simpl in *. rewrite IHcorrect. omega.
  - simpl in *. rewrite <- plus_n_O. rewrite <- IHcorrect. rewrite app_length. trivial.
  - simpl in *. rewrite app_length. rewrite IHcorrect1. simpl. rewrite IHcorrect2. omega.
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
    destruct H.
      - trivial.
      - inversion H0.
      - simpl in *. destruct (size sdx); destruct (size ddx); inversion H0.
      - simpl in *. destruct (size ssx); destruct (size dsx); inversion H0.
      - simpl in *. destruct (size ssx); destruct (size dsx); inversion H0.
  }
Qed.

Lemma delete_sx :
  forall sx dx a el,
    correct (Node sx el dx) -> 
      el ?= a = Gt -> 
      delete a (Node sx el dx) = Node (delete a sx) el dx.
Proof.
  intros.
  remember (Node sx el dx) as bst eqn:R.
  destruct H; simpl; inversion R; subst; try rewrite H0; trivial.
Qed.

Lemma delete_dx :
  forall sx dx a el,
    correct (Node sx el dx) -> 
      el ?= a = Lt -> 
      delete a (Node sx el dx) = Node sx el (delete a dx).
Proof.
  intros.
  remember (Node sx el dx) as bst eqn:R.
  destruct H; simpl; inversion R; subst; try rewrite H0; trivial.
Qed.

Theorem max_height :
  forall bst,
    correct bst ->
    (height bst ?= size(bst) = Lt \/ height bst ?= size(bst) = Eq).
Proof.
  intros.
    induction H; simpl in *.
    - right. trivial.
    - right. trivial.
    - destruct IHcorrect.
      + left. 
        destruct (size sdx + size ddx + 1) eqn : D.
        * discriminate H1.
        * simpl in *. destruct n.
          { simpl. assumption. }
          { simpl. rewrite plus_comm. simpl. assumption. }
      + right.
        destruct (size sdx + size ddx + 1) eqn : D.
        * discriminate H1.
        * simpl in *. destruct n.
          { simpl. assumption. }
          { simpl. rewrite plus_comm. simpl. assumption. }
    - destruct IHcorrect.
      + left. rewrite <- plus_n_O.
        destruct (size ssx + size dsx + 1) eqn : D.
        * discriminate H1.
        * simpl in *. destruct n.
          { simpl. assumption. }
          { simpl. rewrite plus_comm. simpl. assumption. }
      + right. rewrite <- plus_n_O.
        destruct (size ssx + size dsx + 1) eqn : D.
        * discriminate H1.
        * simpl in *. destruct n.
          { simpl. assumption. }
          { simpl. rewrite plus_comm. simpl. assumption. }
    - destruct IHcorrect1;destruct IHcorrect2.
      + left. destruct (size ssx + size dsx + 1).
        * discriminate H3. 
        * simpl in *. destruct (size sdx + size ddx + 1).
          { discriminate H4. }
          { destruct n; destruct n0; 
              simpl;
              rewrite <- nat_compare_lt;
              rewrite <- nat_compare_lt in H3;
              rewrite <- nat_compare_lt in H4;
              lia.
          }
       + left. destruct (size ssx + size dsx + 1).
        * discriminate H3. 
        * simpl in *. destruct (size sdx + size ddx + 1).
          { discriminate H4. }
          { destruct n; destruct n0;
              simpl;
              rewrite <- nat_compare_lt in H3;
              rewrite <- nat_compare_lt;
              apply nat_compare_eq in H4;
              lia.
          }
      + left. destruct (size ssx + size dsx + 1).
        * discriminate H3. 
        * simpl in *. destruct (size sdx + size ddx + 1).
          { discriminate H4. }
          { destruct n; destruct n0;
              simpl;
              rewrite <- nat_compare_lt in H4;
              rewrite <- nat_compare_lt;
              apply nat_compare_eq in H3;
              lia.
          }
      + left. destruct (size ssx + size dsx + 1).
        * discriminate H3. 
        * simpl in *. destruct (size sdx + size ddx + 1).
          { discriminate H4. }
          { destruct n; destruct n0;
              simpl;
              apply nat_compare_eq in H4;
              rewrite <- nat_compare_lt;
              apply nat_compare_eq in H3;
              lia.
          }
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
    induction H.
    - trivial.
    - trivial.
    - trivial.
    - simpl in *. destruct ssx eqn:D.
      + trivial.
      + destruct (toList (Node b1 n b2) ++ esx :: toList dsx) eqn:D1. 
        * inversion D1. destruct (toList b1); simpl in *; inversion H2. 
        * assumption. 
    - simpl in *. destruct ssx eqn:D.
      + assumption.
      + destruct (toList (Node b1 n b2) ++ esx :: toList dsx) eqn:D1. 
        * inversion D1. destruct (toList b1); simpl in *; inversion H4. 
        * assumption. 
  } {
    induction H.
    - trivial.
    - trivial.
    - simpl in *. destruct ddx eqn:D.
      + destruct (rev (toList sdx ++ edx :: toList empty)) eqn : D1.
        * discriminate IHcorrect.
        * trivial.
      + destruct (rev (toList sdx ++ edx :: toList (Node b1 n b2))) eqn : D1.
        * inversion D1. rewrite rev_app_distr in H2. 
          assert (A: rev (edx :: toList b1 ++ n :: toList b2) = rev (n :: toList b2) ++ rev(edx :: toList b1)).
            { simpl. rewrite rev_app_distr. simpl. rewrite  app_assoc. trivial. }
            { rewrite A in H2. rewrite <- app_assoc in H2. destruct (toList b2).
              { simpl in *. discriminate H2. }
              { simpl in *. rewrite <- app_assoc in H2. rewrite <- app_assoc in H2. destruct (rev l); inversion  H2. }
            }
        * simpl in *. assumption.
    - simpl in *. destruct dsx eqn:D.
      + simpl. rewrite rev_app_distr. trivial.
      + simpl. rewrite rev_app_distr. trivial.
    - simpl in *. destruct ddx eqn:D.
      + destruct (rev (toList sdx ++ edx :: toList empty)) eqn : D1.
        * discriminate IHcorrect2.
        * simpl in *. destruct dsx eqn:D2.
          { simpl. repeat(rewrite rev_app_distr; simpl). trivial. }
          { simpl. repeat(rewrite rev_app_distr; simpl). trivial. }
      + destruct (rev (toList sdx ++ edx :: toList (Node b1 n b2))) eqn : D1.
        * inversion D1. rewrite rev_app_distr in H4. 
          assert (A: rev (edx :: toList b1 ++ n :: toList b2) = rev (n :: toList b2) ++ rev(edx :: toList b1)).
            { simpl. rewrite rev_app_distr. simpl. rewrite  app_assoc. trivial. }
            { rewrite A in H4. rewrite <- app_assoc in H4. destruct (toList b2).
              { simpl in *. discriminate H4. }
              { simpl in *. rewrite <- app_assoc in H4. rewrite <- app_assoc in H4. destruct (rev l); inversion  H4. }
            }
        * inversion D1. rewrite rev_app_distr in H4.  
          assert (A: rev (edx :: toList b1 ++ n :: toList b2) = rev (n :: toList b2) ++ rev(edx :: toList b1)).
            { simpl. rewrite rev_app_distr. simpl. rewrite  app_assoc. trivial. }
            { rewrite A in H4. rewrite <- app_assoc in H4. simpl. destruct (toList b2).
              {  simpl. repeat (rewrite rev_app_distr; simpl).
                rewrite <- H4 in IHcorrect2. simpl in IHcorrect2. assumption.
              }
              {
                simpl. repeat (rewrite rev_app_distr; simpl).
                simpl. simpl in H4. 
                rewrite <- app_assoc in H4. rewrite <- app_assoc in H4. destruct (rev l0).
                { inversion H4. rewrite <- H4 in IHcorrect2. simpl in *. subst. assumption.  }
                { inversion H4. rewrite <- H4 in IHcorrect2. simpl in *. subst. assumption.  }
              }
            }
  }
Qed.

Theorem delete_correct :
  forall a bst,
    correct bst -> correct(delete a bst).
Proof.
  intros.
  induction H.
  - constructor.
  - simpl. destruct (el ?= a); constructor.
  - destruct (el ?= a) eqn : D.
      
Admitted.

Theorem delete_ismember :
  forall bst el,
    correct bst -> isMember el (delete el bst) = false.
Proof.
  
Admitted.

Theorem delete_size :
  forall bst el,
    correct bst -> 
      (isMember el bst = true -> size (delete el bst) = size bst - 1) /\ 
      (isMember el bst = false -> size (delete el bst) = size bst).
Proof.
  intros.
  split; intros.
  induction H; simpl.
  - trivial.
  - inversion H0; subst. destruct (el0 ?= el) eqn : D.
    + trivial.
    + inversion H1.
    + inversion H1.
  - inversion H0; subst. destruct (el0 ?= el) eqn : D.
    + 
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

Theorem toList_distinct:
  forall bst n,
    correct bst -> 
    (isMember n bst = true -> only_one (toList bst) n = true) /\
    (isMember n bst = false -> not_in (toList bst) n = true).
Proof.
  intros.
  induction H.
  - split; intros.
    + inversion H.
    + trivial. 
  - split; intros.
    + simpl in *. destruct (el ?= n) eqn:D.
      * trivial.
      * discriminate H.
      * discriminate H.
    + simpl in *. destruct (el ?= n) eqn:D.
      * discriminate H.
      * trivial.
      * trivial.
  - destruct IHcorrect. split; intros.
    + clear H2. simpl in *. destruct (el ?= n) eqn:D.
      * simpl. destruct (edx ?= n) eqn:D1.
        { apply nat_compare_eq in D. subst. rewrite D1 in H0. discriminate H0. }
        { apply nat_compare_eq in D. subst. rewrite D1 in H0. discriminate H0. }
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

Theorem toList_sorted :
  forall bst,
    correct bst -> 
      sorted (toList bst) = true.
Proof.
  intros.
  induction H.
  - trivial.
  - trivial.
  - simpl in *. destruct (toList sdx ++ edx :: toList ddx) eqn : D.
    + trivial.
    + rewrite IHcorrect. destruct (el ?= n) eqn:D1; trivial.
      * admit. 
      * admit. 
  - destruct (toList (Node ssx esx dsx)) eqn : D.
    + inversion D. simpl. rewrite H2. trivial.
    + simpl in *.
      destruct (toList ssx); destruct (toList dsx); simpl in *.
      * rewrite H0. trivial.
      * inversion D. subst. destruct (n ?= n0) eqn : D1.
        { discriminate IHcorrect. }
Admitted.

