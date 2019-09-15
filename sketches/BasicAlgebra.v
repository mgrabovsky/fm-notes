Require Import NArith.
Require Import Setoid.

Set Implicit Arguments.
Unset Strict Implicit.
Generalizable All Variables.

Class has_mul A :=
  { mul : A -> A -> A }.

Infix "*" := mul (left associativity, at level 40).

Class is_assoc {A} (r : A -> A -> A) :=
  { assoc : `(r a (r b c) = r (r a b) c) }.

Class semigroup `(has_mul A) `(is_assoc _ mul).

(* TODO: Complete the following in the same vein. *)

(** * Monoids *)
Module Type monoid.
  Include semigroup.

  (** The neutral (unit) element *)
  Variable e : elt.

  (** Multiplication by the unit is identity *)
  Axiom lunit_id : forall a, e * a = a.
  Axiom runit_id : forall a, a * e = a.

  Hint Resolve lunit_id runit_id : monoid.

  (** Exponentiation *)
  Fixpoint pow (a : elt) (n : nat) :=
    match n with
    | 0    => e
    | S n' => pow a n' * a
    end.

  Definition order a n := (forall i, 1 <= i < n -> pow a i <> e) /\ pow a n = e.

  Require Import Coq.Lists.List.
  Import List.ListNotations.

  Fixpoint prod (xs : list elt) :=
    match xs with
    | [] => e
    | x :: xs => prod xs * x
    end.
End monoid.

Module monoid_facts (Import M : monoid).
  (** Square of the unit is unit *)
  Lemma unit2_unit : M.e * M.e = M.e.
  Proof. now rewrite lunit_id. Qed.

  Lemma pow_O : forall a, pow a 0 = M.e.
  Proof. now cbn. Qed.

  Lemma pow_1 : forall a, pow a 1 = a.
  Proof. now intro; cbn; rewrite M.lunit_id. Qed.

  Lemma pow_unit_unit : forall n, pow M.e n = M.e.
  Proof.
    induction n; [trivial |].
    cbn.
    rewrite IHn.
    apply unit2_unit.
  Qed.

  Lemma pow_lmul : forall a n, a * pow a n = pow a (S n).
  Proof.
    induction n; cbn.
    - now rewrite runit_id, lunit_id.
    - rewrite <- assoc, IHn.
      now cbn.
  Qed.

  Lemma pow_rmul : forall a n, pow a n * a = pow a (S n).
  Proof. reflexivity. Qed.

  Lemma pow_sum : forall a m n, pow a m * pow a n = pow a (m + n).
  Proof.
    induction m; intro.
    - apply lunit_id.
    - cbn.
      rewrite assoc, pow_lmul.
      cbn.
      now rewrite <- assoc, IHm.
  Qed.

  Lemma pow_prod : forall a m n, pow (pow a m) n = pow a (m * n).
  Proof.
    induction n.
    - now rewrite Nat.mul_0_r; cbn. (* now cbn; rewrite pow_unit_unit. *)
    - rewrite Nat.mul_succ_r.
      cbn.
      now rewrite IHn,  pow_sum.
  Qed.
End monoid_facts.

(** * Groups *)
Module Type group.
  Include monoid.

  (** The inverse of an element *)
  Variable inv : elt -> elt.
  Notation "a '⁻¹'" := (inv a) (at level 10, format "a '⁻¹'").

  (** The inverse of an element times the element equals the unit *)
  Axiom linv_unit : forall a, a⁻¹ * a = e.
End group.

Module group_facts (Import G : group).
  Module MFacts := monoid_facts G.
  Include MFacts.

  Lemma lcancel : forall a b c, a * b = a * c -> b = c.
  Proof.
    intros.
    rewrite <- (lunit_id b), <- (lunit_id c), <- (linv_unit a).
    now rewrite assoc, H, <- assoc.
  Qed.

  Lemma runit_id : forall a, a * G.e = a.
  Proof.
    intro a.
    apply (lcancel (G.inv a)).
    rewrite <- assoc, linv_unit.
    apply unit2_unit.
  Qed.

  Lemma rinv_unit : forall a, a * a⁻¹ = G.e.
  Proof.
    intros.
    apply (lcancel (G.inv a)).
    rewrite <- assoc, linv_unit.
    now rewrite lunit_id, runit_id.
  Qed.

  Lemma rcancel : forall a b c, b * a = c * a -> b = c.
  Proof.
    intros.
    rewrite <- (runit_id b), <- (runit_id c), <- (rinv_unit a).
    now rewrite <- assoc, <- assoc, H.
  Qed.

  Lemma unit_inv_unit : (G.e)⁻¹ = G.e.
  Proof.
    now rewrite <- (linv_unit G.e) at 2; rewrite runit_id.
  Qed.

  Lemma inv_inv : forall x, (x⁻¹)⁻¹ = x.
  Proof.
    intro x.
    rewrite <- (lunit_id x) at 2; rewrite <- (linv_unit (G.inv x)).
    now rewrite assoc, linv_unit, runit_id.
  Qed.

  Lemma inv_dist : forall a b, (a * b)⁻¹ = b⁻¹ * a⁻¹.
  Proof.
    intros a b.
    apply (lcancel (a * b)).
    rewrite rinv_unit.
    rewrite assoc, <- (assoc _ (G.inv _) (G.inv _)), rinv_unit, lunit_id.
    now rewrite rinv_unit.
  Qed.

  Lemma lmul_unit_is_inv : forall a b, b * a = G.e -> b = G.inv a.
  Proof.
    intros a b H.
    apply (rcancel a).
    now rewrite H, linv_unit.
  Qed.

  Lemma rmul_unit_is_inv : forall a b, a * b = G.e -> b = G.inv a.
  Proof.
    intros a b H.
    apply (lcancel a).
    now rewrite H, rinv_unit.
  Qed.

  Lemma commut_iff : forall a b, a * b * a⁻¹ * b⁻¹ = G.e <-> a * b = b * a.
  Proof.
    split; intro H.
    - rewrite <- lunit_id, <- H.
      rewrite assoc, <- (assoc _ b a), linv_unit, lunit_id.
      now rewrite assoc, linv_unit, runit_id.
    - rewrite assoc, <- inv_dist, H.
      now rewrite rinv_unit.
  Qed.

  Lemma inv_pow : forall a n, pow (a⁻¹) n = (pow a n)⁻¹.
  Proof.
    induction n.
    - cbn.
      now rewrite unit_inv_unit.
    - cbn.
      rewrite IHn, <- inv_dist.
      now rewrite pow_lmul, pow_rmul.
  Qed.
End group_facts.

Module Type group_homo (G H : group).
  Infix "*" := G.op (left associativity, at level 40).
  Infix "#" := H.op (left associativity, at level 40).

  Parameter f : G.elt -> H.elt.

  Axiom homo_spec : forall a b, f (a * b) = f a # f b.
End group_homo.

Module group_homo_facts (G H : group) (Import Homo : group_homo G H).
  Module GFacts := group_facts G.
  Module HFacts := group_facts H.

  Lemma unit_to_unit : f G.e = H.e.
  Proof.
    apply (HFacts.lcancel (f G.e)).
    rewrite <- homo_spec, GFacts.unit2_unit.
    now rewrite HFacts.runit_id.
  Qed.

  Lemma inv_to_inv : forall a, f (G.inv a) = H.inv (f a).
  Proof.
    intro a.
    apply (HFacts.lcancel (f a)).
    rewrite <- homo_spec, GFacts.rinv_unit.
    now rewrite HFacts.rinv_unit, unit_to_unit.
  Qed.
End group_homo_facts.

Module Type group_direct_prod (G H : group) <: group.
  Definition elt := (G.elt * H.elt)%type.
  Definition e := (G.e, H.e).

  Definition op g h :=
    match g, h with
    | (a, b), (c, d) => (G.op a c, H.op b d)
    end.

  Definition inv a :=
    match a with
    | (g, h) => (G.inv g, H.inv h)
    end.

  Local Infix "*" := op (left associativity, at level 40).

  Lemma assoc : forall a b c, a * b * c = a * (b * c).
  Proof.
    intros [a b] [c d] [e f]; cbn.
    now rewrite G.assoc, H.assoc.
  Qed.

  Lemma lunit_id : forall a, e * a = a.
  Proof.
    intros [a b]; cbn.
    now rewrite G.lunit_id, H.lunit_id.
  Qed.

  Lemma linv_unit : forall a, inv a * a = e.
  Proof.
    intros [a b]; cbn.
    now rewrite G.linv_unit, H.linv_unit.
  Qed.

End group_direct_prod.
