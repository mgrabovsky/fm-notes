Require Import Nat Omega.

Definition divides m n := exists k, n = k * m.

Goal forall m, divides m 0.
Proof. now exists 0. Qed.

Section GcdFacts.

Lemma gcd_step1 : forall a b, a <> 0 -> gcd a b = gcd (b mod a) a.
Proof.
  destruct a.
  - now intros b H; contradict H.
  - intros b _.
    now cbn [gcd].
Qed.

Lemma gcd_div1 : forall a b, divides (gcd a b) a.
Proof.
  intros a b.
  destruct (Nat.eq_dec a 0) as [Ha | Ha]; subst.
  - now exists 0.
  - rewrite (gcd_step1 a b) by assumption.
    red.
exists m n, m * a = 
    exists (b / (b mod a)).
    unfold gcd.
Admitted.

Lemma gcd_spec : forall a b d1 d2, gcd a b = d1 -> d2 | a -> d2 | b -> d2 <= d1.
Proof.
  intros. unfold divides in *.
Admitted.

Lemma gcd_n_O : forall a, gcd a 0 = a.
Proof.
  destruct a; trivial.
  cbn.
  now rewrite Nat.sub_diag.
Qed.

Goal forall (a b c d : nat), a | (b*c)%nat -> gcd a b = d -> (a/d) | c.
Proof.
  intros a b c d Hdiv Hgcd.
  unfold divides in *.
  destruct Hdiv as [k Hkabc].
Admitted.

End GcdFacts.