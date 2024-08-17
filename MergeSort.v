From Coq Require Import Unicode.Utf8.

Require Import Arith.
Require Import PeanoNat.
Require Import Bool.
Require Import List.
Require Import Sorting.Permutation.
From Coq Require Import Recdef.
Import ListNotations.

Fixpoint merge (a: list nat) (b: list nat) :=
let fix merge' (b: list nat) :=
match a, b with
| [], b => b
| a, [] => a
| x::xs, y::ys => if x <=? y
    then x :: merge xs b
    else y :: merge' ys
end
in merge' b.

Compute merge [1; 3; 5; 11] [9; 10; 15; 16].

Fixpoint split (l: list nat) :=
match l with
| [] => ([], [])
| [x] => ([x], [])
| x::y::xs => let (fst, snd) := split xs in
              (x::fst, y::snd)
end.

Compute split [1; 2; 3; 4; 5].

Function sort (l: list nat) { measure length l } : list nat :=
match l with
| nil => l
| [x] => l
| l => let (fst, snd) := split l in
       merge (sort fst) (sort snd)
end.
Proof.
Admitted.

Compute sort [3; 1; 5; 2; 4; 6].

