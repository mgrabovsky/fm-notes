Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Class Semigroup (A : Type) : Type := mkSemigroup
  { binop : A -> A -> A
  ; assoc : forall a b c : A,
      binop a (binop b c) = binop (binop a b) c
  }.

Inductive Cost : nat -> Type -> Type :=
  mkCost : forall n A, A -> Cost n A.

Definition unCost {n A} (c : Cost n A) :=
  match c with
  | mkCost _ x => x
  end.

Lemma unCost_mkCost_id {n A} : forall x : A, unCost (mkCost n x) = x.
Proof. reflexivity. Qed.

Definition pure {n A} (x : A) := mkCost n x.

Definition bind {m n A B} (ma : Cost m A) (k : A -> Cost n B) : Cost (m + n) B.
  destruct ma as [m A x].
  refine (mkCost _ (unCost (k x))).
Defined.

Fixpoint doTimes {A m} (S : Semigroup A) n (c : Cost m A) (acc : A) : Cost (n * m) A :=
  match n with
  | 0    => pure acc
  | S n' => bind c (fun a => doTimes S n' c (binop acc a))
  end.

Require Import Arith List Program String.

Open Scope string_scope.
Lemma append_assoc (s1 s2 s3 : string) : s1 ++ s2 ++ s3 = (s1 ++ s2) ++ s3.
Proof.
  induction s1.
  - reflexivity.
  - now cbn; rewrite IHs1.
Qed.

Instance list_Semigroup A : Semigroup (list A) :=
  mkSemigroup (@app_assoc A).
Instance string_Semigroup : Semigroup string :=
  mkSemigroup append_assoc.

Program Fixpoint day n : Cost (fact n) string :=
  match n with
  | 0    => pure "."
  | S n' => doTimes string_Semigroup n (day n') "$"
  end.

Compute day 4.
