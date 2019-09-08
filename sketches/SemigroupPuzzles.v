(** Source: https://golem.ph.utexas.edu/category/2015/06/semigroup_puzzles.html *)

Require Import Setoid.
Require Import ssreflect.

Generalizable All Variables.

Section puzzles.
  Variable A : Type.
  Variable op : A -> A -> A.
  Local Infix "*" := op (at level 40, left associativity).

  Hypothesis assoc  : `(x * y * z = x * (y * z)).
  Hypothesis absorp : `(x * y * x = x).

  Section vanilla.
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

    Lemma puzzle2 : forall x, x * x = x.
    Proof.
      intro x.
      rewrite <- (absorp x x) at 1.
      rewrite (assoc x _ x).
      now rewrite absorp.
    Qed.
  End vanilla.

  Section ssr.
    Lemma puzzle1_ssr : forall x y z, x * y * z = x * z.
    Proof.
      move=> x y z.
      rewrite -{2}(absorp x (y*z)) (assoc _ x z) (assoc x (y*z) (x*z)).
      by rewrite (assoc y _ _) -(assoc z x z) absorp.
    Qed.

    Lemma puzzle2_ssr : forall x, x * x = x.
    Proof.
      move=> x.
      by rewrite -{1}(absorp x x) (assoc x _ x) absorp.
    Qed.
  End ssr.
End puzzles.

