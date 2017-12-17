Require Fin.
Require Import Vector.

Import Vector.VectorNotations.

Lemma fin_case : forall {n} (i : Fin.t n),
  match n return Fin.t n -> Type with
  | 0   => fun _ => False
  | S _ => fun i => i = Fin.F1 \/ exists i', i = Fin.FS i'
  end i.
Proof.
  destruct i; eauto.
Defined.

Lemma replace_fact1 {A n} (xs : Vector.t A n) i x : (replace xs i x)[@i] = x.
Proof.
  induction xs; [ inversion i | ].
  destruct (fin_case i).
  - subst. auto.
  - firstorder; subst; cbn; auto.
Qed.

Lemma replace_fact2 {A n} (xs : Vector.t A n) x i k : k <> i -> (replace xs i x)[@k] = xs[@k].
Proof.
  induction xs; [ inversion i | ]; intros Hneq.
  destruct (fin_case i); subst.
  - destruct (fin_case k); subst.
    + contradiction.
    + now firstorder; subst.
  - destruct (fin_case k); subst.
    + now firstorder; subst.
    + firstorder; subst. cbn.
      apply IHxs.
      congruence.
Qed.

(*
Lemma vector_case :
  forall A n (P : Vector.t A n -> Type),
    (forall (pf : 0 = n),
      P (eq_rect 0 _ [] n pf)) ->
    (forall n' x (xs : Vector.t A n') (pf : S n' = n),
      P (eq_rect n' _ xs n pf) ->
      P (eq_rect (S n') _ (x :: xs) n pf)) ->
    forall xs, P xs.
Proof.
  intros.
  destruct xs eqn:?.
  - specialize (X eq_refl).
    assumption.
  - specialize (X0 n h t eq_refl).
    assumption.
Qed.

Ltac vector_dep_destruct v :=
  pattern v; apply vector_case; clear v; intros.
*)

Section Swap.
  Context {A : Type}.

  Definition swap {n} (i j : Fin.t n) (xs : Vector.t A n) : Vector.t A n :=
    replace (replace xs i xs[@j]) j xs[@i].

  Lemma replace_fact3 {n} (xs : Vector.t A n) i : replace xs i xs[@i] = xs.
  Proof.
    apply eq_nth_iff.
    intros j p2 []; clear p2.
    destruct (Fin.eq_dec j i) as [ Heq | Hneq ].
    - rewrite Heq; clear Heq j.
      apply replace_fact1.
    - now apply replace_fact2.
  Qed.

  Lemma swap_same {n} (xs : Vector.t A n) i : swap i i xs = xs.
  Proof.
    apply eq_nth_iff.
    intros ? ? []; clear p2.
    destruct (Fin.eq_dec p1 i) as [ Heq | Heq ].
    - rewrite Heq; clear Heq p1.
      unfold swap.
      now rewrite replace_fact3, replace_fact3.
    - unfold swap.
      rewrite replace_fact2, replace_fact2; auto.
  Qed.

  Lemma swap_spec : forall n (xs : Vector.t A n) i j k,
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
