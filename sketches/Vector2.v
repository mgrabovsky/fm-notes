(* TODO: Split facts (and equality?) into submodules *)

Set Implicit Arguments.
Unset Strict Implicit.

Require Fin.

Fixpoint vec (A : Type) (n : nat) : Type :=
  match n with
  | 0   => unit
  | S m => A * vec A m
  end.

Definition cast {A m} (xs : vec A m) : forall n, m = n -> vec A n.
Proof. intros; subst; assumption. Defined.

Definition nil  {A} : vec A 0 := tt.
Definition cons {A n} (x : A) (xs : vec A n) : vec A (S n) := (x, xs).

Definition hd {A n} : vec A (S n) -> A := fst.
Definition tl {A n} : vec A (S n) -> vec A n := snd.

Definition last {A n} (xs : vec A (S n)) : A.
Proof.
  induction n.
  - refine (hd xs).
  - refine (IHn (tl xs)).
Defined.

Definition const {A n} (x : A) : vec A n :=
  nat_rect _ nil (fun _ acc => cons x acc) _.

Definition nth {A n} (xs : vec A n) (i : Fin.t n) : A.
Proof.
  induction i.
  - refine (hd xs).
  - refine (IHi (tl xs)).
Defined.

Definition replace {A n} (xs : vec A n) (i : Fin.t n) (new : A) : vec A n.
Proof.
  induction i.
  - refine (cons new (tl xs)).
  - refine (cons (hd xs) (IHi (tl xs))).
Defined.

Definition append {A m n} (xs : vec A m) (ys : vec A n) : vec A (m + n).
Proof.
  induction m.
  - refine ys.
  - refine (cons (hd xs) (IHm (tl xs))).
Defined.

Definition rev {A n} (xs : vec A n) : vec A n.
Proof.
  induction n as [| n rev ].
  - refine nil.
  - destruct xs as [x xs].
    (* FIXME: Can we do better? *)
    refine (cast (append (rev xs) (cons x nil)) (PeanoNat.Nat.add_1_r _)).
Defined.

Fixpoint map {A B n} (f : A -> B) (xs : vec A n) : vec B n :=
  match n as m return vec A m -> vec B m with
  | 0   => fun _   => nil
  | S _ => fun xs' => cons (f (hd xs')) (map f (tl xs'))
  end xs.

Lemma eq_dec {A n} (Hdec : forall a b : A, {a = b} + {a <> b}) (xs ys : vec A n) : {xs = ys} + {xs <> ys}.
Proof.
  induction n.
  - destruct xs, ys; auto.
  - destruct xs as [x xs], ys as [y ys].
    destruct (Hdec x y).
    + destruct (IHn xs ys).
      * subst; auto.
      * right; congruence.
    + right; congruence.
Defined.

Lemma eq_nth_iff {A n} (xs ys : vec A n) : (forall i, nth xs i = nth ys i) <-> xs = ys.
Proof.
  split; intros.
  - induction n.
    + now destruct xs, ys.
    + destruct xs as [x xs], ys as [y ys]; f_equal.
      * pose (H Fin.F1); eauto.
      * apply IHn.
        intros i.
        apply (H (Fin.R 1 i)).
  - now subst.
Qed.

Lemma eq_nth_iff' {A n} (xs ys : vec A n) : (forall i j, i = j -> nth xs i = nth ys j) <-> xs = ys.
Proof.
  split; intros.
  - induction n.
    + now destruct xs, ys.
    + destruct xs as [x xs], ys as [y ys]; f_equal.
      * pose (H Fin.F1 _ eq_refl); eauto.
      * apply IHn.
        intros i j H0.
        eapply (H _ _ (f_equal (Fin.R 1) H0)).
  - now subst.
Qed.

Require List.

Fixpoint of_list {A} (xs : list A) : vec A (length xs) :=
  match xs with
  | List.nil         => nil
  | List.cons x rest => cons x (of_list rest)
  end.

Definition to_list {A n} (xs : vec A n) : { ys : list A | length ys = n }.
Proof.
  induction n.
  - now exists List.nil.
  - destruct xs as [x xs], (IHn xs) as [ys proof].
    exists (List.cons x ys).
    now cbn; rewrite proof.
Defined.

Module VectorNotations.
  Delimit Scope vector_scope with vector.

  Notation "[ ]":=
    nil (format "[ ]") : vector_scope.
  Notation "h :: t" :=
    (cons h t) (at level 60, right associativity) : vector_scope.
  Notation "[ x ]" :=
    (cons x nil) : vector_scope.
  Notation "[ x ; y ; .. ; z ]" :=
    (cons x (cons y .. (cons z nil) ..)) : vector_scope.
  Notation "v [@ p ]" :=
    (nth v p) (at level 1, format "v [@ p ]") : vector_scope.

  Open Scope vector_scope.
End VectorNotations.
