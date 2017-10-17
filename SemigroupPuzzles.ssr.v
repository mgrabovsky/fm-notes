(** Source: https://golem.ph.utexas.edu/category/2015/06/semigroup_puzzles.html *)
From mathcomp Require Import ssreflect.

Section puzzles.
  Variable A : Type.
  Variable op : A -> A -> A.
  Local Infix "*" := op (at level 40, left associativity).

  Hypothesis assoc : forall x y z, x * y * z = x * (y * z).
  Hypothesis absorp : forall x y, x * y * x = x.

  Lemma puzzle1 : forall x y z, x * y * z = x * z.
  Proof.
    move=> x y z.
    rewrite -{2}(absorp x (y*z)) (assoc _ x z) (assoc x (y*z) (x*z)).
    by rewrite (assoc y _ _) -(assoc z x z) absorp.
  Qed.

  Lemma puzzle2 : forall x, x * x = x.
  Proof.
    move=> x.
    by rewrite -{1}(absorp x x) (assoc x _ x) absorp.
  Qed.
End puzzles.
