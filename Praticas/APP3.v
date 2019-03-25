Require Import String List.
Import ListNotations.

Add LoadPath "C:\Users\Francisco\Desktop\LProg\Praticas\".
Load TacticsL8.

Set Implicit Arguments.

Inductive btree X:Type :=
  | Empty
  | Node: X -> btree X -> btree X -> btree X.

Arguments Empty {X}.
Arguments Node {X} _ _ _.

Section Btrees.

Variable X : Type.
Variable Y : Type.

Fixpoint nodes (tree: btree X) : nat :=
match tree with
  | Empty => 0
  | Node _ ltree rtree => 1 + nodes ltree + nodes rtree
end.

Fixpoint leaves (tree: btree X) : nat :=
match tree with
  | Empty => 0
  | Node _ Empty Empty => 1
  | Node _ ltree rtree => leaves ltree + leaves rtree
end.

Fixpoint flatten (tree: btree X) : list X :=
match tree with
  | Empty => []
  | Node Value ltree rtree => Value ::(flatten ltree ++ flatten rtree)
end.

Fixpoint height (tree: btree X) : nat :=
match tree with
  | Empty => 0
  | Node _ ltree rtree => 1 + max (height ltree) (height rtree)
end.

Theorem heigth_nodes: forall tree : btree X,
  height tree <= nodes tree.
Proof.
  intros.
  induction tree.
  - simpl. reflexivity.
  - simpl. linear_arithmetic.
Qed.

Fixpoint maxTree (tree: btree nat) : nat :=
  match tree with
  | Empty => 0
  | Node Value ltree rtree => max Value (max (maxTree ltree) (maxTree rtree))
end.

Fixpoint subTree (tree: btree X) : list (btree X) :=
  match tree with
  | Empty => []
  | Node _ ltree rtree => [tree] ++ subTree ltree ++ subTree rtree
end.

Fixpoint mapBTree (f : X -> Y) (tree: btree X) : btree Y :=
  match tree with
  | Empty => Empty
  | Node Value ltree rtree => Node (f Value) (mapBTree f ltree) (mapBTree f rtree)
end.




