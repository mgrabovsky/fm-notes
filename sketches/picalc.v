Require Import Coq.MSets.MSets.
Require Import Coq.Arith.Arith.
Require Import Coq.Lists.List.
Import ListNotations.

Module NatOrderedTypeAlt <: OrderedTypeAlt.
  Definition t := nat.
  Definition compare := Nat.compare.

  Lemma compare_sym : forall {m n}, compare n m = CompOpp (compare m n).
  Proof.
    exact Nat.compare_antisym.
(*
    intros m n.
    destruct (compare n m) eqn:H.
    - rewrite Nat.compare_eq_iff in H; subst.
      now rewrite Nat.compare_refl.
    - rewrite Nat.compare_lt_iff in H.
      assert (compare m n = Gt) as H0 by
        (now apply Nat.compare_gt_iff).
      now rewrite H0.
    - rewrite Nat.compare_gt_iff in H.
      assert (compare m n = Lt) as H0 by
        (now apply Nat.compare_lt_iff).
      now rewrite H0.
*)
  Qed.

  Lemma compare_trans : forall {c m n o}, compare m n = c -> compare n o = c -> compare m o = c.
  Proof.
    intros c m n o Hmn Hno.
    destruct c.
    - rewrite Nat.compare_eq_iff in *; congruence.
    - rewrite Nat.compare_lt_iff in *.
      apply (Nat.lt_trans m n o); trivial.
    - rewrite Nat.compare_gt_iff in *.
      apply (Nat.lt_trans o n m); trivial.
  Qed.
End NatOrderedTypeAlt.

Module NatOrderedType := OT_from_Alt(NatOrderedTypeAlt).

Module NatOrderedTypeWithLeibniz.
  Include NatOrderedType.
  Definition eq_leibniz := Nat.compare_eq.
End NatOrderedTypeWithLeibniz.

Module NatSetMod := MSetList.MakeWithLeibniz(NatOrderedTypeWithLeibniz).
Module NatSetDec := WDecide(NatSetMod).

Notation set   := NatSetMod.t.
Notation elt   := NatSetMod.elt.
Notation empty := NatSetMod.empty.
Notation add   := NatSetMod.add.
Notation union := NatSetMod.union.

Inductive proc :=
| recv : elt -> elt -> proc -> proc
| send : elt -> elt -> proc -> proc
| par : proc -> proc -> proc
| chan : nat -> proc -> proc
| iter : proc -> proc
| term : proc.
Print Module NatSetMod.
Fixpoint bvars p : set :=
  match p with
  | recv _ x P => add x (bvars P)
  | send _ _ P => bvars P
  | par P Q => union (bvars P) (bvars Q)
  | chan x P => add x (bvars P)
  | iter P => bvars P
  | term => empty
  end.
