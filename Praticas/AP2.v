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

(* Duvida
Fixpoint partition {X: Type} (test: X -> bool) (l: list X) : (list X) * (list X) :=
  match l with
  | [] => []
  | h :: t => if test h then  

*)

(* 2.2. *)

(*

Fixpoint list_prod {X, Y: Type} (l1: list X) (l2: list Y) : list X*Y :=
  match l1 with
  | [] = []
  | h1 :: t1 => match l2 with
                | [] = []
                | h2 :: t2 => (h1 , h2) :: listprod l1 t2
                end

*)
(* 2.3. *)

(* 2.4. *)

(* 2.5. *)

(* 2.6. *)


(* Exercise 3 *)

(* 3.1. *)

(* 3.2. *)

(* 3.3. *)

(* 3.4. *)


