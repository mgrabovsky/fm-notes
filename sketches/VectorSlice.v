Set Implicit Arguments.
Unset Strict Implicit.

Require Fin Vector.

Definition Fin := Fin.t.
Definition Vector := Vector.t.

Definition fin_to_nat {n} (f : Fin n) := proj1_sig (Fin.to_nat f).
Require Import Program.

Program Fixpoint take {A n} (p : Fin n) (v : Vector A n) : Vector A (fin_to_nat p) :=
  match p with
  | Fin.F1    => Vector.nil _
  | Fin.FS p' => _
  end.
  inversion v.
  refine (Vector.cons _ h _ _).
      refine (take _ n p _ v); apply le_S_n; assumption.
Defined.

Print Module Vector.

Check trunc.

Definition slice {A n} (a b : nat) (Ha : a <= b) (Hb : b <= n) (v : t A n) : t A (b - a).