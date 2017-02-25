Set Implicit Arguments.
Unset Strict Implicit.

Require Import Coq.Unicode.Utf8.

Module Type Poset.
  Parameter t : Set.

  Parameter eq : t → t → Prop.
  Infix "==" := eq (at level 30).
  Axiom eq_refl    : forall x, x == x.
  Axiom eq_sym     : forall x y, x == y → y == x.
  Axiom eq_trans   : forall x y z, x == y → y == z → x == z.
  Parameter eq_dec : forall x y, {x == y} + {~x == y}.

  Parameter order : t → t → Prop.
  Infix "≤" := order (at level 70).
  Axiom order_refl    : forall x y, x == y → x ≤ y.
  Axiom order_antisym : forall x y, x ≤ y → y ≤ x → x == y.
  Axiom order_trans   : forall x y z, x ≤ y → y ≤ z → x ≤ z.
  Parameter order_dec : forall x y, {x ≤ y} + {~x ≤ y}.
End Poset.

Module Type Lattice.
  Include Poset.

  Parameter join : t → t → t.
  Infix "⋀" := join (at level 40).
  Axiom join_bound1   : forall x y, x ≤ (x ⋀ y).
  Axiom join_bound2   : forall x y, y ≤ (x ⋀ y).
  Axiom join_supremum : forall x y z, x ≤ z → y ≤ z → (x ⋀ y) ≤ z.

  Parameter meet : t → t → t.
  Infix "⋁" := meet (at level 40).
  Axiom meet_bound1  : forall x y, (x ⋁ y) ≤ x.
  Axiom meet_bound2  : forall x y, (x ⋁ y) ≤ y.
  Axiom meet_infimum : forall x y z, z ≤ x → z ≤ y → z ≤ (x ⋁ y).

  Parameter bottom : t.
  Notation "⊥" := bottom.
  Axiom bottom_is_bottom : forall x, ⊥ ≤ x.
End Lattice.

Module Type Heyting.
  Include Lattice.

  Axiom relative_complement : forall a b, { x : t | a ⋀ x ≤ b /\ forall y, a ⋀ y ≤ b → y ≤ x }.
  Infix "⇒" := relative_complement (at level 80).

  Definition complement a := a ⇒ ⊥.
End Heyting.
