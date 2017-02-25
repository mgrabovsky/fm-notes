Require Import Arith.

Inductive even : nat -> Prop :=
| even_O  : even 0
| even_S : forall n, odd n -> even (S n)
with odd : nat -> Prop :=
| odd_S : forall n, even n -> odd (S n).

Lemma even_SS n : even n -> even (S (S n)).
Proof.
  intro.
  constructor; constructor; assumption.
Qed.

Lemma odd_pred n : even (S n) -> odd n.
Proof.
  intro H.
  inversion H; assumption.
Qed.

Goal forall m n, even m -> odd n -> odd (m + n).
Proof.
  intros m n Hm Hn.
  induction m.
  - assumption.
  - inversion_clear Hm; subst.
    cbn; constructor.
Qed.

Check eq.
Check eq_refl.
Check eq_rec.
Print eq_rect.

Definition eq_rect' {A} (x:A) (P:A->Type) (f:P x) (y:A) (e:eq x y) :=
  match e in (eq _ y0) return (P y0) with
  | @eq_refl _ _ => f
  end.

(* eq : (A:Type) -> A -> A -> Prop. *)
(* eq_refl : (A:Type) -> (x:A) -> eq A x x. *)
(* eq_rect : (A:Type) -> (x:A) -> (P:A->Type) -> P x -> (y:A) -> eq x y -> P y *)