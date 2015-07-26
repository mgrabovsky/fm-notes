(** Source: https://golem.ph.utexas.edu/category/2015/06/semigroup_puzzles.html *)
Require Import Coq.Setoids.Setoid.

Section puzzles.
  Variable A : Type.
  Variable op : A -> A -> A.
  Local Infix "*" := op (at level 40, left associativity).

  Hypothesis assoc : forall x y z, x * y * z = x * (y * z).
  Hypothesis absorp : forall x y, x * y * x = x.

  Lemma puzzle1 : forall x y z, x * y * z = x * z.
  Proof.
    intros x y z.
    rewrite <- (absorp x (y*z)) at 2.
    rewrite (assoc _ x z).
    rewrite (assoc x (y*z) (x*z)).
    rewrite (assoc y _ _).
    rewrite <- (assoc z x z).
    now rewrite absorp.
  Qed.
  Print puzzle1.

  Lemma puzzle2 : forall x, x * x = x.
  Proof.
    intro x.
    rewrite <- (absorp x x) at 1.
    rewrite (assoc x _ x).
    now rewrite absorp.
  Qed.
End puzzles.
