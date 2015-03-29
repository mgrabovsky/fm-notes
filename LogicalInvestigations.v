(* This is a collection of proofs of propositions from the
 * <http://www.nuprl.org/MathLibrary/LogicalInvestigations/ "Logical Investigations,
 * with the Nuprl Proof Assistant"> document
 *)

(* * 2. The Minimal Implicational Calculus *)
Section Chapter2.
  Variables A B C : Prop.

  Theorem thm1 : A -> B -> A.
  Proof.
    intros.
    assumption.
  Qed.

  Theorem thm2 : (A -> B) -> ((A -> (B -> C)) -> (A -> C)).
  Proof.
    intros H1 H2 H3.
    apply H2, H1; assumption.
  Qed.

  Theorem thm3 : (A -> B) -> ((B -> C) -> (A -> C)).
  Proof.
    intros HAB HBC HA.
    apply HBC, HAB, HA.
  Qed.
End Chapter2.

(* * 3. False Propositions and Negation *)
Section Chapter3.
  Variables P Q : Prop.

  Theorem thm4 : ~P -> P -> Q.
  Proof.
    intros.
    (* or just [contradiction.] *)
    absurd P; assumption.
  Qed.

  (* TODO: below here: check for [intro ...; destruct] and
   * [exfalso/contradiction] v. [absurd/elim] *)
  Theorem thm5 : P -> ~~P.
  Proof.
    intro.
    (* this transforms [H : P |- ~~P] into [H : ~P |- ~P] -- a contraposition *)
    contradict H.
    assumption.
  Qed.

  Theorem thm6 : (P -> Q) -> ~Q -> ~P.
  Proof.
    intros HPimplQ HnQ.
    contradict HnQ.
    apply HPimplQ, HnQ.
  Qed.

  Theorem thm7 : (P -> ~P) -> P -> Q.
  Proof.
    intros Himpl HP.
    exfalso.
    apply Himpl; assumption.
  Qed.

  Theorem thm8 : ~(P -> Q) -> P -> ~Q.
  Proof.
    intros Hnimpl HP.
    contradict Hnimpl.
    (* TODO: there must be a shorter way to generate [exact (fun _ => Hnimpl).] *)
    intro; assumption.
  Qed.
End Chapter3.

(* * 4. Conjunction and Disjunction *)
Section Chapter4.
  Variables P Q : Prop.

  Theorem thm9 : (P \/ ~P) -> ~~P -> P.
  Proof.
    intros Hdec HnnP.
    destruct Hdec; [| contradict HnnP]; assumption.
  Qed.

  Theorem thm10 : ~~(P \/ ~P).
  Proof. 
    red.
    intro H.
    (* duplicate the hypothesis *)
    assert (H' := H).
    contradict H'.
    (* we don't have evidence for [P], so we prove its negation *)
    right.
    contradict H.
    left; assumption.
  Qed.

  Theorem thm11 : (~P \/ ~Q) -> ~(P /\ Q).
  Proof.
    intro.
    destruct H; contradict H; apply H.
  Qed.

  (* an alternative proof of Theorem 11 *)
  Theorem thm11a : (~P \/ ~Q) -> ~(P /\ Q).
  Proof.
    intro H.
    contradict H.
    destruct H as [HP HQ].
    contradict HP.
    destruct HP; [assumption | contradiction].
  Qed.

  Theorem thm12 : ~(P \/ Q) -> (~P /\ ~Q).
  Proof.
    intro H.
    split; contradict H; [left | right]; assumption.
  Qed.

  Theorem thm13 : (~P /\ ~Q) -> ~(P \/ Q).
  Proof.
    intro H.
    destruct H as [H1 H2].
    contradict H1.
    destruct H1; [assumption | contradiction].
  Qed.

  Theorem thm14 : (~P \/ Q) -> P -> Q.
  Proof.
    intros H0 HP.
    destruct H0; [contradiction | assumption].
  Qed.

  Theorem thm15 : (P -> Q) -> ~~(~P \/ Q).
  Proof.
    unfold not.
    intros H1 H2.
    assert (H2' := H2).
    destruct H2'.
    left; intro HP.
    destruct H2.
    right.
    exact (H1 HP).
  Qed.

  (* TODO: could be shorter? *)
  Theorem thm16 : ((P -> Q) /\ ((P \/ ~P) \/ (Q \/ ~Q))) -> (~P \/ Q).
  Proof.
    intro H; destruct H, H0, H0.
    - right; apply H, H0.
    - left; assumption.
    - right; assumption.
    - left.
      contradict H.
      red; intro.
      assert (HQ := H1 H).
      contradiction.
  Qed.
End Chapter4.

(* * 5. First-Order Logic: All and Exists *)
Section Chapter5.
  Variables (T : Type) (C : Prop) (P : T -> Prop).

  Theorem thm17a : (C -> (forall x, P x)) -> (forall x, (C -> P x)).
  Proof.
    intros; apply H; assumption.
  Qed.

  Theorem thm17b : (forall x, (C -> P x)) -> (C -> (forall x, P x)).
  Proof.
    intros; apply H; assumption.
  Qed.

  Theorem thm18a : ((exists x, P x) -> C) -> (forall x, P x -> C).
  Proof.
    intros.
    apply H.
    exists x.
    assumption.
  Qed.

  Theorem thm18b : (forall x, P x -> C) -> ((exists x, P x) -> C).
  Proof.
    intros ? [x H0].
    apply H with x, H0.
  Qed.

  Theorem thm19a : (C \/ ~C) -> (exists x : T, True) -> (C -> (exists x, P x)) ->
    (exists x, C -> P x).
  Proof.
    intros Hdec Hinhab Himpl.
    destruct Hdec as [HC | HnC].
    - destruct (Himpl HC) as [x HPx].
      exists x.
      (* TODO: is there a shorthand for this? *)
      intro; assumption.
    - destruct Hinhab as [x _].
      exists x.
      intro H; contradiction.
  Qed.

  Theorem thm19b : (exists x, C -> P x) -> C -> (exists x, P x).
  Proof.
    intros H HC.
    destruct H.
    exists x.
    exact (H HC).
  Qed.
End Chapter5.

(* TODO: ... &c. *)

(* vim: set et ts=2 sts=2 sw=2: *)

