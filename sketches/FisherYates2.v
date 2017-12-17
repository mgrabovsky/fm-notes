Require Import Vector2.
Import VectorNotations.

Lemma fin_case : forall {n} (i : Fin.t n),
  match n return Fin.t n -> Type with
  | 0   => fun _ => False
  | S _ => fun i => i = Fin.F1 \/ exists i', i = Fin.FS i'
  end i.
Proof.
  destruct i; eauto.
Defined.

Lemma replace_fact1 {A n} (xs : vec A n) i new : (replace xs i new)[@i] = new.
Proof.
  induction n; [ inversion i | ].
  destruct (fin_case i).
  - now subst.
  - destruct H; subst.
    now simpl; rewrite IHn.
Qed.

Lemma replace_fact2 {A n} (xs : vec A n) x i k : k <> i -> (replace xs i x)[@k] = xs[@k].
Proof.
  induction n; [ inversion i |]; intros Hneq.
  destruct (fin_case i); subst.
  - destruct (fin_case k); subst.
    + contradiction.
    + now firstorder; subst.
  - destruct (fin_case k); subst.
    + now firstorder; subst.
    + firstorder; subst.
      destruct xs; simpl.
      apply IHn; congruence.
Qed.

Lemma replace_fact3 {A n} (xs : vec A n) i : replace xs i xs[@i] = xs.
Proof.
  induction n; [ inversion i | ].
  destruct xs as [x xs].
  destruct (fin_case i); subst; [ auto | ].
  firstorder; subst.
  now simpl; rewrite IHn.
Qed.

Section Swap.
  Context {A : Type}.

  Definition swap {n} (i j : Fin.t n) (xs : vec A n) : vec A n :=
    replace (replace xs i xs[@j]) j xs[@i].

  Lemma swap_same {n} (xs : vec A n) i : swap i i xs = xs.
  Proof.
    apply eq_nth_iff; intro j.
    destruct (Fin.eq_dec j i) as [ Heq | Heq ].
    - subst.
      unfold swap.
      now rewrite replace_fact3, replace_fact3.
    - unfold swap.
      rewrite replace_fact2, replace_fact2; auto.
  Qed.

  Lemma swap_spec : forall n (xs : vec A n) i j k,
    (k <> i -> k <> j -> (swap i j xs)[@k] = xs[@k]) /\
    (                    (swap i j xs)[@j] = xs[@i]) /\
    (                    (swap i j xs)[@i] = xs[@j]).
  Proof.
  Admitted.
End Swap.

Section FisherYates.
  Context {A : Type}.
  Variable Random : Type -> Type.
  Variable (RRet : forall X, X -> Random X).
  Variable (RBind : forall X Y, Random X -> (X -> Random Y) -> Random Y).
  Variable (runif : forall (lo hi : nat), lo <= hi -> Random nat).

  Fixpoint FisherYates_aux {n} (xs : Vector.t A n) k : Random (list A) :=
    match k with
    | 0   => _
    | S _ => _
    end.

(*
  for i from 0 to n−2 do
    j <$ [i, n - 1]
    swap a[i] and a[j]
*)
End FisherYates.
