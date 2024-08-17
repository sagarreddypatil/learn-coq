From Coq Require Import Unicode.Utf8.

Require Import Arith.
Require Import Coq.Arith.PeanoNat.
Require Import Bool.
Require Import List.
Import ListNotations.

Fixpoint insert (i: nat) (l: list nat) :=
match l with
| nil => i :: nil
| h :: t => if i <=? h then i :: h :: t else h :: insert i t
end.

Compute insert 3 [1; 2; 5].

Fixpoint sort (l: list nat) :=
match l with
| nil => nil
| h :: t => insert h (sort t)
end.

Compute sort [3; 1; 2; 5].

Inductive sorted: list nat -> Prop :=
| sorted_nil: sorted []
| sorted_1: ∀ n, sorted [n]
| sorted_cons: ∀ x y l,
    x ≤ y → sorted (y :: l) → sorted (x :: y :: l).


Example sorted_1_2_3: sorted [1; 2; 3].
Proof.
apply sorted_cons.
- auto.
- apply sorted_cons.
  + auto.
  + apply sorted_1.
Qed.

(* Lemma  *)

Theorem insert_sorted (n: nat) (l: list nat): sorted l -> sorted (insert n l).
Proof.
intro h.
induction h.
{ simpl. apply sorted_1. }
{
    simpl. destruct (n <=? n0) eqn: H.
    - apply sorted_cons.
        + apply Nat.leb_le. assumption.
        + apply sorted_1.
    - apply sorted_cons.
        + apply leb_complete_conv in H.
          apply Nat.lt_le_incl.
          assumption.
        + apply sorted_1.
}
{ 
    assert (sorted (x :: y :: l)). apply sorted_cons. auto. assumption.
    simpl insert.
    simpl in IHh.
    destruct (n <=? x) eqn: H1.
    - apply sorted_cons.
        + apply Nat.leb_le. assumption.
        + assumption.
    - assert (x ≤ n).
      apply leb_complete_conv in H1.
      apply Nat.lt_le_incl. assumption.
      destruct (n <=? y).
      apply sorted_cons. assumption. assumption.
      apply sorted_cons. assumption. assumption.
}
Qed.
