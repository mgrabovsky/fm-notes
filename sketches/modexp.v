Require Import PeanoNat.

(* Algorithm from
 *  <https://en.wikipedia.org/wiki/Modular_exponentiation#Memory-efficient_method>
 *)
Fixpoint modexp' m b e c :=
  match e with
  | 0    => c mod m
  | S e' => modexp' m b e' ((b * c) mod m)
  end.
Definition modexp m b e := modexp' m b e 1.

Lemma modexp'_correct : forall m b e c, m <> 0 -> b <> 0 ->
  modexp' m b e c = (b ^ e * c) mod m.
Proof.
  intros m b e.
  induction e; intros.
  - cbn.
    now rewrite Nat.add_0_r.
  - cbn.
    rewrite IHe; auto.
    rewrite Nat.mul_mod_idemp_r; auto.
    now rewrite Nat.mul_assoc, (Nat.mul_comm _ b).
Qed.

Lemma modexp_correct : forall m b e, m <> 0 -> b <> 0 ->
  modexp m b e = (b ^ e) mod m.
Proof.
  intros.
  unfold modexp.
  rewrite modexp'_correct; auto.
  now rewrite Nat.mul_1_r.
Qed.
