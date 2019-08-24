Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Import Bvector.
Require Import Setoid.

Definition byte := Bvector 8.
Definition xor  := BVxor.

Lemma xor_commut : forall n x y, @xor n x y = xor y x.
Proof.
  intros.
  unfold xor, BVxor.
  apply (Vector.rect2 (fun m v1 v2 =>
    Vector.map2 (n:=m) xorb v1 v2 = Vector.map2 xorb v2 v1)).
  - reflexivity.
  - intros; cbn.
    now rewrite xorb_comm, H.
Qed.

Lemma xor_assoc : forall n x y z, @xor n x (xor y z) = xor (xor x y) z.
Proof.
  intros.
  unfold xor, BVxor.
  (* TODO: Finish this proof. *)
Admitted.

Lemma xor_nilpotent : forall n x, xor x x = Bvect_false n.
Proof.
  intros.
  unfold xor, BVxor, Bvect_false.
  induction x.
  - reflexivity.
  - now cbn; rewrite IHx, xorb_nilpotent.
Qed.

Lemma xor_false_r : forall n x, xor x (Bvect_false n) = x.
Proof.
  induction x.
  - reflexivity.
  - now cbn; rewrite IHx, xorb_false_r.
Qed.

Lemma xor_false_l : forall n x, xor (Bvect_false n) x = x.
Proof.
  induction x.
  - reflexivity.
  - cbn; rewrite IHx.
    now destruct h.
Qed.

Definition swap (vars : byte * byte) :=
  let '(x, y) := vars in
  let x := xor x y in
  let y := xor y x in
  let x := xor x y in
      (x, y).

Theorem swap_correct : forall x y, swap (x, y) = (y, x).
Proof.
  intros; unfold swap.
  rewrite (xor_commut y (xor x y)), xor_assoc.
  rewrite xor_nilpotent, xor_false_l.
  rewrite <- xor_assoc, xor_nilpotent, xor_false_r.
  reflexivity.
Qed.
