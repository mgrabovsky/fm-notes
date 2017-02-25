Require Import Coq.Setoids.Setoid Coq.Classes.RelationClasses.

Polymorphic Inductive set : Type :=
  sup : forall A : Type, (A -> set) -> set.

Definition empty :=
  sup False (fun x => match x with end).

Definition pair (E1 E2 : set) :=
  sup bool (fun x => if x then E1 else E2).

Polymorphic Fixpoint Eq (S1 S2 : set) :=
  match S1, S2 with
  | sup A f, sup B g =>
      (forall a:A, exists b:B, Eq (f a) (g b)) /\
      (forall b:B, exists a:A, Eq (f a) (g b))
  end.

Polymorphic Lemma Eq_refl : forall A, Eq A A.
Proof.
  induction 0.
  split; intro a; exists a; apply H.
Qed.

Polymorphic Lemma Eq_sym : forall A B, Eq A B -> Eq B A.
Proof.
  fix s 1.
  induction 0 as [B g H].
  destruct A as [A f]; intros [HEq1 HEq2].
  split.
  - intro b.
    destruct (HEq2 b) as [a ?].
    now exists a; apply s.
  - intro a.
    destruct (HEq1 a) as [b ?].
    now exists b; apply s.
Qed.


Polymorphic Lemma Eq_trans : forall A B C, Eq A B -> Eq B C -> Eq A C.
Proof.
  fix s 2.
  induction 0 as [C h].
  destruct A as [A f], B as [B g].
  intros [HEqAB1 HEqAB2] [HEqBC1 HEqBC2].
  split.
  - intro a.
    destruct (HEqAB1 a) as [b ?]; destruct (HEqBC1 b) as [c ?].
    exists c; eapply s; eauto.
  - intro c.
    destruct (HEqBC2 c) as [b ?]; destruct (HEqAB2 b) as [a ?].
    exists a; eapply s; eauto.
Qed.

Add Relation set Eq
  reflexivity proved by Eq_refl
  symmetry proved by Eq_sym
  transitivity proved by Eq_trans
  as Eq_Equivalence.

Polymorphic Definition In (E S : set) :=
  match S with
  | sup A f => exists a : A, Eq E (f a)
  end.

Goal forall A B, In A (pair A B).
Proof.
  intros; exists true; apply Eq_refl.
Qed.

Goal forall A B, In B (pair A B).
Proof.
  intros; exists false; apply Eq_refl.
Qed.

Goal forall A B C, In C (pair A B) -> Eq A C \/ Eq B C.
Proof.
  intros ? ? ? [[|] ?]; [left | right]; apply Eq_sym; assumption.
Qed.

Goal forall A A' B, In A B -> Eq A A' -> In A' B.
Proof.
  intros.
