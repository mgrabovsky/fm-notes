Require Import Coq.Numbers.BinNums ZArith.

Open Scope Z_scope.

Definition Q : Set := Z * positive.
Definition eq (p q : Q) : Prop :=
  match p, q with
  | (a, b), (c, d) => a * (Zpos d) = c * (Zpos b)
  end.

Definition eqb (p q : Q) :=
  match p, q with
  | (a, b), (c, d) => a * (Zpos d) =? c * (Zpos b)
  end.

Lemma eqb_eq : forall p q, eqb p q = true <-> eq p q.
Proof.
  split; intro Heq; destruct p, q; cbn in Heq;
    apply Z.eqb_eq in Heq; assumption.
Qed.
