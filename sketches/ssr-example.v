From mathcomp Require Import ssreflect.ssreflect ssrfun ssrbool ssrnat eqtype div prime.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Lemma dvdn_fact m n : 0 < m <= n -> m %| n`!.
Proof.
  case: m => //= m.
  elim: n => //= n IHn.
  rewrite ltnS leq_eqVlt.
  by case/predU1P=> [-> | /IHn];
    [ apply: dvdn_mulr
    | apply: dvdn_mull ].
Qed.

Lemma prime_above m : {p | m < p & prime p}.
Proof.
  have /pdivP[p pr_P p_dv_m1]: 1 < m`! + 1 by rewrite addn1 ltnS fact_gt0.
  exists p => //; rewrite ltnNge; apply: contraL p_dv_m1 => p_le_m.
  by rewrite dvdn_addr ?dvdn_fact ?prime_gt0 // gtnNdvd ?prime_gt1.
Qed.
