From Coq Require Import Arith.Arith.
From Coq Require Import Arith.Compare_dec.
From Coq Require Import Arith.EqNat.
From Coq Require Import Init.Decimal.
From Coq Require Import Init.Nat.
From Coq Require Import Bool.Bool.
From Coq Require Import Lists.List.
Import ListNotations.

Inductive BST : Type :=
  | Empty : BST
  | Node : BST -> nat -> BST -> BST.

Notation "'empty'" := Empty.
Notation "'(' l e r ')'" := (Node l e r).

Fixpoint insert (El : nat) (bst : BST) : BST :=
  match bst with
    | Empty => Node Empty El Empty
    | Node l el r =>
        match el ?= El with
          | Eq => bst
          | Lt => Node l el (insert El r)
          | Gt => Node (insert El l) el r
        end
  end.

Fixpoint fromList (l : list nat) : BST :=
  match l with
    | nil => Empty
    | h :: t => insert h (fromList t)
  end.

Fixpoint height (bst : BST) : nat :=
  match bst with
    | Empty => 0
    | Node l _ r => 1 + (max (height l) (height r))
  end.

Fixpoint size (bst : BST) : nat :=
  match bst with
    | Empty => 0
    | Node l _ r => (size l) + (size r) + 1
  end.

Definition isEmpty (bst : BST) : bool :=
  match bst with
    | Empty => true
    | _ => false
  end.

Fixpoint toList (bst : BST) : list nat := 
  match bst with
    | Empty => nil
    | Node l el r => toList(l) ++ (el :: nil) ++ toList(r)
  end.

Fixpoint getMin (bst : BST) : option(nat) :=
  match bst with
    | Empty => None
    | Node Empty el _ => Some el
    | Node l _ _ => getMin l 
  end.

Fixpoint getMax (bst : BST) : option(nat) :=
  match bst with
    | Empty => None
    | Node _ el Empty => Some el
    | Node _ _ r => getMax r 
  end.

Fixpoint isMember (El : nat) (bst : BST) : bool :=
  match bst with
    | Empty => false
    | Node l el r =>
        match el ?= El with
          | Eq => true
          | Lt => isMember El r
          | Gt => isMember El l
        end
  end.

Fixpoint delete2 (El : nat) (bst : BST) : BST :=
  match bst with
    | Empty => bst
    | Node l el r =>
        match el ?= El with
          | Eq => 
              match getMin(r) with
                | None => l
                | Some min => Node l min (delete2 min r)
              end
          | Lt => Node l el (delete2 El r)
          | Gt => Node (delete2 El l) el r
        end
  end.

Fixpoint list_beq(l1 : list nat) (l2 : list nat) : bool :=
  match (l1, l2) with
    | (nil, nil) => true
    | (_ :: _, nil) => false
    | (nil, _ :: _) => false
    | (h1 :: t1, h2 :: t2) => 
        match beq_nat h1 h2 with
          | true => list_beq t1 t2
          | false => false
        end
  end.

Definition BSTequals(bst1 : BST)(bst2 : BST) : bool :=
  list_beq (toList bst1) (toList bst2).

Definition delete (El : nat) (bst : BST) : BST :=
  fromList(filter (fun el => negb (beq_nat el El)) (toList bst)).

Definition correct_on_l(root : nat)(l : BST) : bool :=
  forallb (fun el => el <? root)(toList l).

Definition correct_on_r(root : nat)(r : BST) : bool :=
  forallb (fun el => root <? el)(toList r).

Fixpoint correct_fun (bst : BST) : bool :=
  match bst with
    | Empty => true
    | Node l e r =>
        correct_on_l e l && correct_fun l &&
        correct_on_r e r && correct_fun r
  end.

Inductive correct : BST -> Prop :=
  | cor_empty : correct Empty
  | cor_node : 
      forall l e r,
        correct_on_l e l = true ->
        correct l ->
        correct_on_r e r = true ->
        correct r ->
        correct (Node l e r).