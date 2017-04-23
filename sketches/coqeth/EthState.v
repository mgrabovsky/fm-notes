Set Implicit Arguments.
Unset Strict Implicit.

Require Export EthTypes.

(* Account and world state definitions *)
Record account_state : Type := mkAccount_state
    { acc_nonce    : nat (* number of transactions from this address,
                            or number of contract-creations by this account *)
    ; balance      : nat
    ; storage_root : hash256
    ; code_hash    : hash256
    }.

(*
Definition is_simple_account a :=
  if hash256_eq_dec a.(code_hash) empty_string_hash
    then true
    else false.
*)

(* World state maps an address to the state of its corresponding account if it exists *)
Definition worldState : Type := address -> option account_state.

(* Transactions *)
Record trans_params : Type := mkTrans_params
    { trans_nonce : nat
    ; gas_price   : nat
    ; gas_limit   : nat
    ; recipient   : option address
    ; value       : nat
    ; trans_w     : Vector.t bit 5
    ; trans_r     : hash256
    ; trans_s     : hash256
    }.

Inductive transaction : Type :=
| trans_message_call (t : trans_params) (data : byteseq)
| trans_contract_creation (t : trans_params) (init : byteseq).

(* The block *)
Variable bloom_filter : Type.
Inductive block_header : Type := mkBlock_header
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
    ; extra_data        : byteseq (* <= 32 bytes *)
    ; mix_hash          : hash256
    ; block_nonce       : Vector.t byte 8
    ; ommer_headers     : list block_header
    ; block_transactions : list transaction
    }.

Definition block : Type := block_header * list block_header * list transaction.
