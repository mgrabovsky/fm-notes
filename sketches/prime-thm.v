From mathcomp Require Import all_ssreflect.

Lemma odd_alt : forall n, odd n -> ~~odd n.+1.
Proof. by case=> ? //=; rewrite Bool.negb_involutive. Qed.

Goal forall n, n > 2 -> prime n -> ~~prime n.+1.
Proof.
  move=> n Hgt2 H0.
  case: (boolP (odd n)) => H.
  - give_up.
  - pose (even_prime H0) as Hp; clearbody Hp.
    case Hp => H'; [subst; inversion Hgt2 | contradict H'; apply/negP: H].
Qed.
