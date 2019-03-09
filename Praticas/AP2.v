(* Exercise 1 *)

Require Import Coq.Lists.List.
Import ListNotations.

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

(* 1.6.*)

(* 1.7.*)

(* 1.8.*)

(* 1.9.*)

(* 1.10.*)

(* 1.11.*)

(* 1.12.*)

(* 1.13.*)


(* Exercise 2 *)

(* 2.1. *)

(* 2.2. *)

(* 2.3. *)

(* 2.4. *)

(* 2.5. *)

(* 2.6. *)


(* Exercise 3 *)

(* 3.1. *)

(* 3.2. *)

(* 3.3. *)

(* 3.4. *)


