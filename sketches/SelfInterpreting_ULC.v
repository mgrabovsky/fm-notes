Require Import Arith Setoid.

Section UntypedLambda.
  Inductive term : Type :=
  | tvar : nat -> term
  | tapp : term -> term -> term
  | tabs : nat -> term -> term.

  Notation "'@' n" := (tvar n) (at level 60, format "@ n").
  Notation "'λ' n '.' t" := (tabs n t) (at level 60, format "λ n .  t").

  Reserved Notation "t '[' i ':=' s ']'" (at level 8, left associativity, format "t [ i  :=  s ]").
  (* Substitute the term [t] for every free variable in [t] *)
  Fixpoint subst i s t :=
    match t with
    | tvar j    => if i =? j then s else t
    | tapp u v  => tapp u[i := s] v[i := s]
    | tabs j t' => if i =? j then t else tabs j t'[i := s]
    end
  where "t '[' i ':=' s ']'" := (subst i s t).

  Reserved Notation "t '↓' u" (at level 15, left associativity).
  Inductive step : term -> term -> Prop :=
  | srefl : forall t, t ↓ t
  | sapp  : forall i t u, tapp (tabs i t) u ↓ t[i := u]
  | sabs  : forall i t t', t ↓ t' -> tabs i t ↓ tabs i t'
  | sapp1 : forall t t' u, t ↓ t' -> tapp t u ↓ tapp t' u
  | sapp2 : forall t u u', u ↓ u' -> tapp t u ↓ tapp t u'
  where "t '↓' u" := (step t u).

  Lemma step_refl : Reflexive step.
  Proof. constructor. Qed.

  Lemma step_trans : Transitive step.
  Proof.
  Admitted.

  Definition omega := tabs 0 (tapp (tvar 0) (tvar 0)).
  Definition Y := tabs 0 (tapp (tabs 1 (tapp (tvar 0) (tapp (tvar 1) (tvar 1)))) (tabs 1 (tapp (tvar 0) (tapp (tvar 1) (tvar 1))))).

  Definition stuck t := forall t', t ↓ t' -> t = t'.

  Fixpoint godelEncode t :=
    match t with
    | tvar i   => 3^i
    | tapp t u => 2 * 3^(godelEncode t * godelEncode u)
    | tabs i t => 4 * 3^i * 5^(godelEncode t)
    end.

  Require Import Nat.

  Goal 

  Definition churchEncode n :=
    match n with
    | 0   => tabs 0 (tabs 1 (tvar 1))
    | S _ =>
      let go := fix go m :=
          match m with
          | 0    => tvar 1
          | S m' => tapp (tvar 0) (go m')
          end
       in tabs 0 (tabs 1 (go n))
    end.

  Definition quote t := churchEncode (godelEncode t).
