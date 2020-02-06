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
Notation "'(' s e d ')'" := (Node s e d).

Fixpoint insert (El : nat) (bst : BST) : BST :=
  match bst with
    | Empty => Node Empty El Empty
    | Node sx el dx =>
        match el ?= El with
          | Eq => bst
          | Lt => Node sx el (insert El dx)
          | Gt => Node (insert El sx) el dx
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
    | Node sx _ dx => 1 + (max (height sx) (height dx))
  end.

Fixpoint size (bst : BST) : nat :=
  match bst with
    | Empty => 0
    | Node sx _ dx => (size sx) + (size dx) + 1
  end.

Definition isEmpty (bst : BST) : bool :=
  match bst with
    | Empty => true
    | _ => false
  end.

Fixpoint toList (bst : BST) : list nat := 
  match bst with
    | Empty => nil
    | Node sx el dx => toList(sx) ++ (el :: nil) ++ toList(dx)
  end.

Fixpoint getMin (bst : BST) : option(nat) :=
  match bst with
    | Empty => None
    | Node Empty el _ => Some el
    | Node sx _ _ => getMin sx 
  end.

Fixpoint getMax (bst : BST) : option(nat) :=
  match bst with
    | Empty => None
    | Node _ el Empty => Some el
    | Node _ _ dx => getMax dx 
  end.

Fixpoint isMember (El : nat) (bst : BST) : bool :=
  match bst with
    | Empty => false
    | Node sx el dx =>
        match el ?= El with
          | Eq => true
          | Lt => isMember El dx
          | Gt => isMember El sx
        end
  end.

Fixpoint delete2 (El : nat) (bst : BST) : BST :=
  match bst with
    | Empty => bst
    | Node sx el dx =>
        match el ?= El with
          | Eq => 
              match getMin(dx) with
                | None => sx
                | Some min => Node sx min (delete2 min dx)
              end
          | Lt => Node sx el (delete2 El dx)
          | Gt => Node (delete2 El sx) el dx
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

Fixpoint correct_fun (bst : BST) : bool :=
  match bst with
    | Empty => true
    | Node sx e dx =>
        match (sx, dx) with
          | (Empty, Empty) => true
          | (Node ssx esx dsx, Empty) => 
              match esx ?= e with
                | Lt => correct_fun sx
                | _ => false
              end
          | (Empty, Node sdx edx ddx) => 
              match edx ?= e with
                | Gt => correct_fun dx
                | _ => false
              end
          | (Node ssx esx dsx, Node sdx edx ddx) => 
              match (esx ?= e, edx ?= e) with
                | (Lt, Gt) => (correct_fun sx) && (correct_fun dx)
                | _ => false
              end
        end
  end.

Inductive correct : BST -> Prop :=
  | cor_empty : correct Empty
  | cor_node_e_e : 
      forall el,
        correct (Node Empty el Empty)
  | cor_node_e_dx :
      forall el sdx edx ddx,
        correct (Node sdx edx ddx) ->
        edx ?= el = Gt ->
        correct (Node Empty el (Node sdx edx ddx))
  | cor_node_sx_e :
      forall ssx esx dsx el,
        correct (Node ssx esx dsx) ->
        esx ?= el = Lt ->
        correct (Node (Node ssx esx dsx) el Empty)
  | cor_node :
      forall ssx esx dsx el sdx edx ddx,
        correct (Node ssx esx dsx) ->
        correct (Node sdx edx ddx) ->
        edx ?= el = Gt ->
        esx ?= el = Lt ->
        correct (Node (Node ssx esx dsx) el (Node sdx edx ddx)).