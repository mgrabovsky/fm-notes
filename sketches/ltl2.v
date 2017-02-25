Set Implicit Arguments.
Unset Strict Implicit.

Require Import Setoid.

(*
Require Import Streams.
*)

Ltac coinduction proof :=
  cofix proof; intros; constructor;
    [ clear proof | try (apply proof; clear proof) ].

Section Sequences.
  Variable A : Type.

  CoInductive Sequence :=
  | Cons : A -> Sequence -> Sequence
  | Nil : Sequence.

  Definition hd s :=
    match s with
    | Cons x _ => Some x
    | Nil      => None
    end.

  Definition tl s :=
    match s with
    | Cons _ xs => Some xs
    | Nil       => None
    end.

  Fixpoint Seq_nth n s :=
    match n, s with
    | _,    Nil       => None
    | 0,    Cons x _  => Some x
    | S n', Cons _ xs => Seq_nth n' xs
    end.

  Fixpoint Seq_nth_tl n s :=
    match n, s with
    | _,    Nil       => None
    | 0,    Cons _ xs => Some xs
    | S n', Cons _ xs => Seq_nth_tl n' xs
    end.

  Reserved Notation "x '==' y" (at level 60).
  CoInductive EqSeq : Sequence -> Sequence -> Prop :=
  | EqCons : forall x y xs ys, x = y -> xs == ys ->
      Cons x xs == Cons y ys
  | EqNil : Nil == Nil
  where "x '==' y" := (EqSeq x y).

  Lemma EqSeq_refl : Reflexive EqSeq.
  Proof.
    cofix EqSeq_refl.
    intro s; destruct s.
    - constructor; [reflexivity | apply EqSeq_refl].
    - constructor.
  Qed.

  Lemma EqSeq_sym : Symmetric EqSeq.
  Proof.
    cofix EqSeq_sym.
    intros s t Hst.
    destruct Hst.
    - constructor; [symmetry | apply EqSeq_sym]; assumption.
    - constructor.
  Qed.

  Lemma EqSeq_trans : Transitive EqSeq.
  Proof.
    cofix EqSeq_trans.
    intros s t u Hst Htu.
    destruct t as [t ts |].
    - destruct s as [s ss |]; [| inversion Hst].
      destruct u as [u us |]; [| inversion Htu].
      constructor.
      + transitivity t; [inversion Hst | inversion Htu]; assumption.
      + apply (EqSeq_trans ss ts us); [inversion Hst | inversion Htu]; assumption.
    - destruct s; [inversion Hst |].
      destruct u; [inversion Htu |].
      constructor.
  Qed.

  Instance EqSeq_Equivalence : Equivalence EqSeq :=
    { Equivalence_Reflexive  := EqSeq_refl
    ; Equivalence_Symmetric  := EqSeq_sym
    ; Equivalence_Transitive := EqSeq_trans }.

  Fixpoint take_to_list n s :=
    match n, s with
    | _,    Nil       => nil
    | 0,    Cons x _  => cons x nil
    | S n', Cons x xs => cons x (take_to_list n' xs)
    end.

  Fixpoint drop n s :=
    match n, s with
    | _,    Nil       => Nil
    | 0,    Cons _ xs => xs
    | S n', Cons _ xs => drop n' xs
    end.

  CoFixpoint append s t :=
    match s with
    | Cons x xs => Cons x (append xs t)
    | Nil       => t
    end.
End Sequences.

Bind Scope Sequence_scope with Sequence.
Open Scope Sequence_scope.
Notation "[ ]" := Nil (format "[ ]") : Sequence_scope.
Notation "[ x ]" := (Cons x Nil) : Sequence_scope.
Notation "[ x | ys ]" :=  (Cons x ys) : Sequence_scope.
Notation "[ x ; y ; .. ; z ]" :=  (Cons x (Cons y .. (Cons z Nil) ..)) : Sequence_scope.
Notation "[ x ; y ; .. ; z | ws ]" :=  (Cons x (Cons y .. (Cons z ws) ..)) : Sequence_scope.


Require Import Ensembles.
Arguments In [U] _ _ /.
Arguments Included [U] _ _ /.
Parameters (U : Type) (AP : Ensemble U).
Inductive Power_set {T} (X : Ensemble T) : Ensemble _ :=
| Power_intro : forall Y, Included Y X -> In (Power_set X) Y.

Definition Sigma := Power_set AP.
Definition containing p := { X | In Sigma X /\ In X p }.
Definition word := Sequence Sigma.
Definition all_words := { w : word | True }.

Inductive formula : Type :=
| ftrue
| ffalse
| fatom (a : Sigma)
| fconj (p q : formula)
| fdisj (p q : formula)
| fimpl (p q : formula)
| fneg (p : formula)
| fnext (p : formula)
| fevent (p : formula)
| funtil (p q : formula).

Fixpoint Mod f :=
  match f with
  | ftrue     => True
  | ffalse    => False
  | fconj p q => Mod p /\ Mod q
  | fdisj p q => Mod p \/ Mod q
  | fimpl p q => Mod p -> Mod q
  | fneg p    => Mod p -> False
  | _         => False
  end.

Compute Mod (fimpl ffalse (fimpl ffalse ftrue)).
Check 