(* Exercise 1 *)

Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.Arith.PeanoNat.

(* 1.1. *)

Definition tl(l: list nat) : list nat :=
  match l with
  | [] => []
  | h::t => t
end.  

Compute tl [1;2;3].

(* 1.2. *)

Definition removelast (l: list nat) : list nat :=
  match l with
  | [] => []
  | h :: t => h :: removelast t
end.

Compute removelast [1;2;3;4;5].

(* 1.3. *)

Definition firstn (n: nat) (l: list nat) : list nat :=
  match n with
  | O => l
  | S n' => match l with
            | [] => []
            | h :: t => h :: firstn n' t
            end
end.

Compute firstn 3 [1;2;3;4;5].

(* 1.4.*)

Definition skipn (n: nat) (l: list nat) : list nat :=
  match n with
  | O => l
  | S n' => match l with
            | [] => []
            | h :: t => skipn n' t
            end
end.

Compute skipn 3 [1;2;3;4;5].

(* 1.5.*)

Inductive option (X :Type) : Type :=
  | Some : X -> option X
  | None : option X.


Arguments Some {X} _.
Arguments None {X}.

Check Some 1.

Fixpoint last {X:Type} (l: list X) : option X := 
  match l with
  | [] => None
  | h :: [] => Some h
  | h :: t => last t
end.

Compute last [].
Compute last [1;2;3].

(* 1.6.*)

Fixpoint seq (start: nat) (len: nat) : list nat :=
  match len with
  | 0 => []
  | S len' => start :: (seq (S start) len')
end.

Compute seq 3 4. 

(* 1.7.*)

Fixpoint split {X Y : Type} (l: list (X*Y)) : (list X)*(list Y) :=
  match l with
  | [] => ([],[])
  | (x, y) :: t => (x :: fst (split t), y :: snd (split t))
end.

Compute split [(1,true);(2,false);(3,true)].

Fixpoint split2 {X Y : Type} (l: list (X*Y)) : (list X)*(list Y) :=
  match l with
  | [] => ([],[])
  | (x, y) :: t => let( left, right) := split t in (x:: left, y::right)
end.

Compute split [(1,true);(2,false);(3,true)].

(* 1.8.*)

Fixpoint append { X : Type} (l1: list X) (l2 : list X) : list X :=
  match l1 with
  | [] => l2
  | h :: t => h :: append t l2
end.

Compute append [1;2;3] [4;5;6].

(* 1.9.*)

Fixpoint rev {X : Type} (l: list X) : list X :=
  match l with
  | [] => []
  | h :: t => append (rev t) [h]
end.

Compute rev [1;2;3].

(* 1.10.*)

Fixpoint existsb {X: Type} (test: X -> bool) (l: list X) : bool :=
  match l with
  | [] => false
  | h :: t => if test h then true
                        else existsb test t
end.

Compute existsb (fun e => e <=? 3) [2;4;5].
Compute existsb (fun e => e <=? 3) [4;5].

(* 1.11.*)

Fixpoint forallb {X: Type} (test: X -> bool) (l: list X) : bool :=
  match l with
  | [] => true
  | h :: t => if test h then forallb test t
                        else false
end.

Compute forallb (fun e => e <=? 3) [1;2;3].
Compute forallb (fun e => e <=? 3) [1;2;4].

(* 1.12.*)

Fixpoint find {X: Type}(test: X -> bool) (l:list X) : option X:=
  match l with
  | [] => None
  | h :: t => if test h then Some h
                        else find test t
end.

Compute find (fun e => e <=? 3) [6;4;1;3;7].
Compute find (fun e => e <=? 3) [6;4;4;5;7].

(* 1.13.*)


(* Exercise 2 *)

(* 2.1. *)

Fixpoint filter {X:Type} (test: X->bool) (l:list X)
                : (list X) :=
  match l with
  | [] => []
  | h :: t => if test h then h :: (filter test t)
                        else filter test t
  end.

Fixpoint partition {X: Type} (test: X -> bool) (l: list X) : (list X) * (list X) :=
  (filter test l , filter (fun e => negb (test e)) l).

Compute partition (fun e => e <=? 3) [6;4;1;3;7].

(* 2.2. *)

Fixpoint map {X Y: Type} (f:X->Y) (l:list X) : (list Y) :=
  match l with
  | [] => []
  | h :: t => (f h) :: (map f t)
  end.

Fixpoint list_prod {X Y: Type} (l1: list X) (l2: list Y) : list (X*Y) :=
  match l1 with
  | [] => []
  | h1 :: t1 => (map (fun e => (h1 , e)) l2) ++ (list_prod t1 l2)
end.

(* Duvida *)

Compute list_prod [1; 2] [true; false].


(* 2.3. *)

Fixpoint fold {X Y: Type} (f: X->Y->Y) (l: list X) (b: Y) : Y :=
  match l with
  | nil => b
  | h :: t => f h (fold f t b)
  end.

Definition length {X : Type} (l: list X) : nat :=
  fold (fun e c => c + 1) l 0.

Compute length [6;4;1;3;7].

(* 2.4. *)

Definition new_map {X Y: Type} (f:X->Y) (l:list X) : (list Y) :=
  fold (fun x y => f x :: y) l [].


Fixpoint list_prod' {X Y: Type} (l1: list X) (l2: list Y) : list (X*Y) :=
  match l1 with
  | [] => []
  | h1 :: t1 => (new_map (fun e => (h1 , e)) l2) ++ (list_prod t1 l2)
end.

Compute list_prod' [1; 2] [true; false].

(* 2.5. *)

Definition new_filter {X:Type} (test: X->bool) (l:list X): (list X) :=
  fold (fun x y => if test x then x :: y else y ) l [].

Fixpoint partition' {X: Type} (test: X -> bool) (l: list X) : (list X) * (list X) :=
  (filter test l , new_filter (fun e => negb (test e)) l).

Compute partition' (fun e => e <=? 3) [6;4;1;3;7].

(* 2.6. *)

Check andb.

Definition new_forallb {X: Type} (test: X -> bool) (l: list X) : bool :=
  fold andb (map test l) true.

Compute new_forallb (fun e => e <=? 3) [1;2;3].
Compute new_forallb (fun e => e <=? 3) [1;2;4].

(* Exercise 3 *)

(* 3.1. *)

Theorem thm_simpl1: forall a b c:nat,
    a = 0 -> b*(a+b) = b*b.
Proof.
  intros.
  rewrite -> H.
  simpl.
  reflexivity.
Qed.

(* 3.2. *)

Theorem thm_simpl2: forall (a b c d:nat) (f: nat -> nat -> nat),
    a=b -> c=d -> (forall x y, f x y = f y x) -> f a c = f d b.
Proof.
  intros.
  rewrite -> H1.
  rewrite -> H.
  rewrite -> H0.
  reflexivity.
Qed.

(* 3.3. *)

Theorem identity_fn_applied_twice :
  forall (f : bool -> bool),
  (forall (x : bool), f x = x) ->
  forall (b : bool), f (f b) = b.
Proof.
  intros.
  rewrite H.
  rewrite H.
  reflexivity.
Qed.

(* 3.4. *)

Theorem negation_fn_applied_twice :
  forall (f : bool -> bool),
  (forall (x : bool), f x = negb x)->
  forall (b : bool), f (f b) = b.
Proof.
  intros.
  rewrite H. rewrite H.
  
  rewrite identity_fn_applied_twice.
  -reflexivity.
  - intros.
    rewrite H.


