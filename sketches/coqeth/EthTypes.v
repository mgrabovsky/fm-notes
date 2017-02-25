Set Implicit Arguments.
Unset Strict Implicit.

Require Fin Vector.

(* Basic data types *)
Definition bit  := bool.
Definition byte := Vector.t bit 8.
Definition byte_array := list byte.
Definition word    := Vector.t bit 256.
Definition address := Vector.t bit 160.
Definition hash256 := Vector.t bit 256.
Definition hash512 := Vector.t bit 512.

(* Decidable equality for these types *)
Lemma bit_eq_dec : forall x y : bit, {x = y} + {x <> y}.
Proof. apply Bool.bool_dec. Qed.

Definition bit_beq := Bool.eqb.

Lemma byte_eq_dec : forall x y : byte, {x = y} + {x <> y}.
Proof. apply (Vector.eq_dec _ bit_beq Bool.eqb_true_iff). Qed.

Definition byte_beq : byte -> byte -> bool := Vector.eqb _ bit_beq.

Lemma byte_array_eq_dec : forall x y : byte_array, {x = y} + {x <> y}.
Proof. decide equality; apply byte_eq_dec. Qed.

Definition byte_array_beq x y :=
  if byte_array_eq_dec x y then true else false.

Lemma address_eq_dec : forall x y : address, {x = y} + {x <> y}.
Proof. apply (Vector.eq_dec _ bit_beq Bool.eqb_true_iff). Qed.

Lemma hash256_eq_dec : forall x y : hash256, {x = y} + {x <> y}.
Proof. apply (Vector.eq_dec _ bit_beq Bool.eqb_true_iff). Qed.
Lemma hash512_eq_dec : forall x y : hash512, {x = y} + {x <> y}.
Proof. apply (Vector.eq_dec _ bit_beq Bool.eqb_true_iff). Qed.

(* Abstract specification of the Keccak (SHA-3) hash functions *)
Variable KEC256 : list byte -> hash256.
Variable KEC512 : list byte -> hash512.
Definition empty_string_hash := KEC256 nil.
