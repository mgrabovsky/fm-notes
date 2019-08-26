(* Axiom K is a kind of non-standard (in relation to standard MLTT) eliminator for
 * equality types. *)
Axiom K : forall {A} {x : A} (C : x = x -> Type),
  C eq_refl ->
  forall loop : x = x, C loop.

(* Axiom J is a different statement of the standard equality eliminator. *)
Lemma J : forall {A} {x : A} (C : forall y, x = y -> Type),
  C x eq_refl ->
  forall y (p : x = y), C y p.
Proof.
  destruct p; assumption.
Qed.

(* Assuming Axiom K, all proofs of equality are the reflexivity proofs in Coq. *)
Lemma all_eqs_refls :
  forall {A} {x : A} (p : x = x), p = eq_refl.
Proof.
  intros.
  unshelve eapply (K (fun x => x = eq_refl) _ p);
   reflexivity.
Qed.

(* Consequently, all proofs of equality are equal. *)
Theorem all_eqs_equal :
  forall {A} {x y : A} (p q : x = y), p = q.
Proof.
  destruct q.
  apply all_eqs_refls.
Qed.
