Require Import Setoid.

Variables (A : Set) (join meet : A -> A -> A).

Axiom join_assoc : forall a b c,
  join (join a b) c = join a (join b c).
Axiom meet_assoc : forall a b c,
  meet (meet a b) c = meet a (meet b c).
Axiom join_commut : forall a b,
  join a b = join b a.
Axiom meet_commut : forall a b,
  meet a b = meet b a.
Axiom join_meet : forall a b,
  meet (join a b) a = a.
Axiom meet_join : forall a b,
  join (meet a b) a = a.

Lemma join_idem : forall a, join a a = a.
Proof.
  intro.
  rewrite <- (meet_join a a) at 3.

Axiom distributive : forall a b c,
  meet a (join b c) = join (meet a b) (meet a c).

Goal forall a b c,
  join a (meet b c) = meet (join a b) (join a c).
Proof.
  intros.
  rewrite <- (join_meet b a) at 1.
  rewrite (join_commut b a).
  rewrite (meet_commut (join _ _) _).
  rewrite (distributive b a b).
