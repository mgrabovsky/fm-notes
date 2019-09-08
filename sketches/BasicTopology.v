Definition P A := A -> Prop.

Notation "{ x : A | P }" := (fun x : A => P).

Definition comp {A} (u : P A) :=
  { x : A | ~u x }.

Definition singleton {A} (x : A) := { y : A | x = y }.

Definition subset {A} (u v : P A) :=
  forall x, u x -> v x.

Notation "u <= v" := (subset u v).

Definition disjoint {A} (u v : P A) :=
  forall x, ~(u x /\ v x).

Notation "'all' x : U , P" := (forall x, U x -> P) (at level 20, x at level 99, only parsing).
Notation "'some' x : U , P" := (exists x, U x /\ P) (at level 20, x at level 99, only parsing).

Definition union {A} (S : P (P A)) :=
  { x : A | some U : S, U x }.

Definition inter {A} (u v : P A) :=
  { x : A | u x /\ v x }.

Definition empty {A} := { x : A | False }.
Definition full  {A} := { x : A | True }.

Structure topology (A : Type) :=
  { open       :> P A -> Prop
  ; empty_open : open empty
  ; full_open  : open full
  ; inter_open : all u : open, all v : open, open (inter u v)
  ; union_open : forall S, S <= open -> open (union S)
  }.

Definition discrete (A : Type) : topology A.
Proof.
  exists full; firstorder.
Defined.

Definition T1 {A} (T : topology A) :=
  forall x y : A,
    x <> y -> some u : T, (u x /\ ~u y).

Definition hausdorff {A} (T : topology A) :=
  forall x y : A,
    x <> y -> some u : T, some v : T,
      (u x /\ v y /\ disjoint u v).

Lemma discrete_hausdorff {A} : hausdorff (discrete A).
Proof.
  intros x y N.
  exists { z : A | x = z }; split; [exact I | ].
  exists { z : A | y = z }; split; [exact I | ].
  repeat split; auto.
  intros z [? ?].
  absurd (x = y); auto.
  transitivity z; auto.
Qed.

(** * Continuity *)

Definition image {A B} (f : A -> B) (S : P A) :=
  { y : B | exists x, S x /\ y = f x }.

Definition preimage {A B} (f : A -> B) (S : P B) :=
  { x : A | S (f x) }.

Definition continuous {A B} (U : topology A) (V : topology B) (f : A -> B) :=
  forall v, open _ V v -> open _ U (preimage f v).

(*
Lemma lem1 : forall A B (U : topology A) (V : topology B) f,
  continuous U V f ->
    forall U', U' <= U -> image f (comp U') <= comp (image f U').
... getting a type error here
*)
