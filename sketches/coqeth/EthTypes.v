Set Implicit Arguments.
Unset Strict Implicit.

Require Fin Vector.

(* Basic data types *)
Definition bit     := bool.
Definition byte    := Vector.t bit 8.
Definition byteseq := list byte.
Definition word    := Vector.t byte 32.
Definition address := Vector.t byte 20.
Definition hash256 := Vector.t byte 32.
Definition hash512 := Vector.t byte 64.

(* Abstract specification of the Keccak (SHA-3) hash functions *)
Variable KEC256 : list byte -> hash256.
Variable KEC512 : list byte -> hash512.
Definition empty_string_hash := KEC256 nil.
