Set Implicit Arguments.
Unset Strict Implicit.

Require Export EthTypes.

(* Account and world state definitions *)
Record account_state : Type := mkAccount_state
    { acc_nonce : nat (* number of transactions from this address,
                      or number of contract-creations by this acctount *)
    ; balance : nat
    ; storage_root : hash256
    ; code_hash : hash256
    }.

Lemma account_state_eq_dec : forall x y : account_state, {x = y} + {x <> y}.
Proof. decide equality; apply hash256_eq_dec || apply PeanoNat.Nat.eq_dec. Qed.

Definition is_simple_account a :=
  if hash256_eq_dec a.(code_hash) empty_string_hash
    then true
    else false.

(* World state maps an address to the state of its corresponding account if it exists *)
Definition worldState : Type := address -> option account_state.

(* Transactions *)
Record trans_params : Type := mkTrans_params
    { trans_nonce : nat
    ; gas_Price : nat
    ; gas_limit : nat
    ; recipient : option address
    ; value : nat
    ; trans_w : Vector.t bit 5
    ; trans_r : hash256
    ; trans_s : hash256
    }.

Inductive transaction : Type :=
| trans_message_call (t : trans_params) (data : byte_array)
| trans_contract_creation (t : trans_params) (init : byte_array).

Lemma trans_params_eq_dec : forall x y : trans_params, {x = y} + {x <> y}.
Proof.
  decide equality; try (apply PeanoNat.Nat.eq_dec || apply hash256_eq_dec || apply bytearray_eq_dec || apply (Vector.eq_dec _ bit_beq Bool.eqb_true_iff)).
  destruct recipient0, recipient1.
  - destruct (address_eq_dec a2 a3); [now subst; left | right].
    intro; inversion H. apply n, H1.
  - right; intuition; inversion H.
  - right; intuition; inversion H.
  - left; reflexivity.
Qed.

Lemma transaction_eq_dec : forall x y : transaction, {x = y} + {x <> y}.
Proof.
  decide equality; try (apply byte_array_eq_dec || apply trans_params_eq_dec).
Qed.

(* The block *)
Variable bloom_filter : Type.
Record block_header : Type := mkBlock_header
    { parent_hash       : hash256
    ; ommers_hash       : hash256
    ; beneficiary       : address
    ; state_root        : hash256
    ; transactions_root : hash256
    ; receipts_root     : hash256
    ; logs_bloom        : bloom_filter
    ; difficulty        : nat
    ; block_number      : nat
    ; block_gas_limit   : nat
    ; block_gas_used    : nat
    ; timestamp         : nat
    ; extra_data        : byte_array
    ; mix_hash          : hash256
    ; block_nonce       : Vector.t bit 64
    }.

Definition block : Type := block_header * list block_header * list transaction.
