(* Exercise 1 *)

Inductive day : Type :=
  | monday : day
  | tuesday : day
  | wednesday : day
  | thursday : day
  | friday : day
  | saturday : day
  | sunday : day.

Definition weekday_to_nat (d:day) : nat :=
  match d with
  | monday => 2
  | tuesday => 3
  | wednesday => 4
  | thursday => 5
  | friday => 6
  | saturday => 7
  | sunday => 1
end.

Compute (weekday_to_nat monday).
Compute (weekday_to_nat friday).

Definition is_weekend (d:day) : bool :=
  match d with
  | saturday => true
  | sunday => true
  | _ => false
end.

Compute (is_weekend monday).
Compute (is_weekend saturday).

(* Exercise 2 *)

Inductive bool : Type :=
  | true : bool
  | false : bool.


Definition negb (b:bool) : bool :=
  match b with
  | true => false
  | false => true
  end.

Definition andb (b1:bool) (b2:bool) : bool :=
  match b1 with
  | true => b2
  | false => false
  end.

Definition orb (b1:bool) (b2:bool) : bool :=
  match b1 with
  | true => true
  | false => b2
  end.

Example test_orb1: (orb true false) = true.

Proof. simpl. reflexivity. Qed.

Example test_orb2: (orb true true) = true.

Proof. simpl. reflexivity. Qed.

Example test_orb3: (orb false true) = true.

Proof. simpl. reflexivity. Qed.

Example test_orb4: (orb false false) = false.

Proof. simpl. reflexivity. Qed.

Notation "~ x" := (negb x).

Notation "x && y" := (andb x y).

Notation "x || y" := (orb x y).

Compute ~true.
Compute false && true.
Compute true || false.

Definition xor (b1:bool) (b2:bool) : bool :=
  match b1 with
  | true => match b2 with
            |true => false
            |false => true
            end
  | false => match b2 with
            |true => true
            |false => false
            end
  end.

Example test_xor1: (xor true false) = true.

Proof. simpl. reflexivity. Qed.

Example test_xor2: (xor true true) = false.

Proof. simpl. reflexivity. Qed.

Example test_xor3: (xor false true) = true.

Proof. simpl. reflexivity. Qed.

Example test_xor4: (xor false false) = false.

Proof. simpl. reflexivity. Qed.



(* Exercise 3 *)

Module NatPlayground.

Inductive nat : Type :=
  | O : nat
  | S : nat -> nat.


Definition minustwo (n : nat) : nat :=
  match n with
    | O => O
    | S O => O
    | S (S n') => n'
  end.

End NatPlayground.

Fixpoint evenb (n : nat) : bool :=
  match n with
    | O => true
    | S O => false
    | S (S n') => evenb n'
end.

Compute evenb 5.
Compute evenb 6.

Definition oddb (n : nat) : bool :=
  match evenb n with 
    | false => true
    | true => false
end.

Compute oddb 5.
Compute oddb 6.

Definition oddb' (n: nat) : bool :=
   ~evenb n.

Compute oddb 23.
Compute oddb 46.

Fixpoint plus (n : nat) (m : nat) : nat :=
  match n with
  | O => m
  | S n' => ( plus n'(S m))
end.

Compute plus 1 1.
Compute plus 24 50.

Fixpoint mult (n : nat) (m : nat) : nat :=
  match n with 
  | O => O
  | S n' => plus (mult n' m) m
end.

Compute mult 2 4.
Compute mult 8 10.

Fixpoint exp (base : nat) (expo : nat) : nat :=
  match expo with
  | O => 1
  | S expo' => mult (exp base expo') base
end.

Compute exp 2 1.
Compute exp 2 2.
Compute exp 2 3.
Compute exp 2 4.
Compute exp 2 5.
Compute exp 2 6.

Fixpoint minus (n : nat) (m : nat) : nat :=
  match n with
  | O => O
  | S n' => match m with
            | O => n
            | S m' => minus n' m'
            end
 end.

Compute minus 5 3.
Compute minus 3 5.

Fixpoint factorial (n : nat) : nat :=
  match n with
  | O => 1
  | S n' => mult n (factorial n')
end.

Compute factorial 2.
Compute factorial 3.
Compute factorial 4.
Compute factorial 5.

Notation "x + y" := (plus x y )
                        (at level 50, left associativity)
                        : nat_scope.

Compute 4 + 3.

Notation "x * y" := (mult x y )
                        (at level 40, left associativity)
                        : nat_scope.

Compute 4 * 3.

Notation "x ** y" := (exp x y )
                          (at level 31, left associativity)
                           : nat_scope.

Compute 2 ** 3.

Notation "x - y" := (minus x y )
                          (at level 50, left associativity)
                           : nat_scope.

Compute 4 - 3.

Notation " x ! " := (factorial x)
                          (at level 39, left associativity)
                           : nat_scope.

Compute 3!.

(*Fixpoint terminates (n:nat): nat :=
  match n with
  | O => 1
  | S n' => terminates (n'*1 - n'*2)
end.*)


Inductive  bin : Type :=
  | Z
  | A (n : bin)
  | B (n : bin).

Fixpoint incr (m:bin) : bin :=
  match m with
  | Z => B m
  | A m' => B m'
  | B m' => A (incr m')
end.

Fixpoint  bin_to_nat(m:bin) : nat :=
  match m with
  | Z => O
  | A n => 2 * bin_to_nat n
  | B n => 1 + 2 * bin_to_nat n
end.

Compute bin_to_nat (B (B (B Z))).

Example test_bin_incr1:
  bin_to_nat (incr Z) = bin_to_nat Z + 1.
Proof. simpl. reflexivity. Qed.

Example test_bin_incr2:
  bin_to_nat (incr (B Z)) = bin_to_nat Z + 2.
Proof. simpl. reflexivity. Qed.

Example test_bin_incr3:
  bin_to_nat (incr (A(B Z))) = bin_to_nat Z + 3.
Proof. simpl. reflexivity. Qed.

Example test_bin_incr4:
  bin_to_nat (incr (B(B Z))) = bin_to_nat Z + 4.
Proof. simpl. reflexivity. Qed.

Example test_bin_incr5:
  bin_to_nat (incr (A(A(B Z)))) = bin_to_nat Z + 5.
Proof. simpl. reflexivity. Qed.

(* Duvida - Nao funciona)
Require Import omega.Omega.
Require Import NAxioms NProperties OrdersFacts.
Include Coq.Init.Nat.

Theorem inc_correct: forall m,
  bin_to_nat (incr m) = bin_to_nat m +1.
Proof. 
  intros. induction m.
  - simpl. reflexivity.
  - simpl. rewrite Nat.add_1_r. rewrite Nat.add_0_r. reflexivity.
  - simpl. rewrite IHm. omega.
Qed. *)
