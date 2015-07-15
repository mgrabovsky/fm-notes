(* Compile documentation with [coqdoc --utf8] *)
(** printing ~( $\lnot\lnot$ #¬(# *)
(** printing ~~( $\lnot\lnot$ #¬¬(# *)
(** printing ~~(~ $\lnot\lnot$ #¬¬(¬# *)
(** printing ~~ $\lnot\lnot$ #¬¬# *)

(**
 This is a collection of proofs of propositions from the
 #<a href="http://www.nuprl.org/MathLibrary/LogicalInvestigations/">Logical Investigations,
 with the Nuprl Proof Assistant</a># document
 *)

(** * 2. The Minimal Implicational Calculus *)
Section Chapter2.
  Variables A B C : Prop.

  Theorem thm1 : A -> B -> A.
  Proof.
    intros; assumption.
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

(** * 3. False Propositions and Negation *)
Section Chapter3.
  Variables P Q : Prop.

  Theorem thm4 : ~P -> P -> Q.
  Proof.
    intros.
    (** or just [contradiction.] *)
    absurd P; assumption.
  Qed.

  Theorem thm5 : P -> ~~P.
  Proof.
    intro.
    (** this transforms [H : P |- ~~P] into [H : ~P |- ~P] -- kinda contraposition *)
    contradict H.
    assumption.
  Qed.

  (** An alternative proof of Theorem 5 *)
  Theorem thm5a : P -> ~~P.
  Proof.
    (** reduce the outer negation so that [intros] catches both [P] and [~P] *)
    red.
    intros.
    contradiction.
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
    elim Himpl; assumption.
  Qed.

  Theorem thm8 : ~(P -> Q) -> P -> ~Q.
  Proof.
    intros Hnimpl HP.
    contradict Hnimpl.
    (* TODO: is there a shorthand for this? *)
    intro; assumption.
  Qed.
End Chapter3.

(** * 4. Conjunction and Disjunction *)
Section Chapter4.
  Variables P Q : Prop.

  Theorem thm9 : (P \/ ~P) -> ~~P -> P.
  Proof.
    intros Hdec HnnP.
    destruct Hdec; [ | contradict HnnP]; assumption.
  Qed.

  Theorem thm10 : ~~(P \/ ~P).
  Proof.
    intro H.
    (** duplicate the hypothesis *)
    assert (H' := H).
    contradict H'.
    (** we don't have evidence for [P], so we prove its negation *)
    right.
    contradict H.
    left; assumption.
  Qed.

  Theorem thm11 : (~P \/ ~Q) -> ~(P /\ Q).
  Proof.
    intro H.
    destruct H; contradict H; apply H.
  Qed.

  (** an alternative proof of Theorem 11 *)
  Theorem thm11a : (~P \/ ~Q) -> ~(P /\ Q).
  Proof.
    intro H.
    contradict H.
    destruct H as [HP HQ].
    (** doesn't matter which one *)
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
    intros [HnP HnQ].
    (** doesn't matter which one *)
    contradict HnP.
    destruct HnP; [assumption | contradiction].
  Qed.

  Theorem thm14 : (~P \/ Q) -> P -> Q.
  Proof.
    intros [? | ?] HP; [contradiction | assumption].
  Qed.

  Theorem thm15 : (P -> Q) -> ~~(~P \/ Q).
  Proof.
    red.
    intros H1 H2.
    assert (H2' := H2).
    (** same as [contradict H2'] in this case *)
    destruct H2'.
    left; intro HP.
    destruct H2.
    right.
    (** same as [exact (H1 HP)] *)
    apply H1, HP.
  Qed.

  Theorem thm16 : ((P -> Q) /\ ((P \/ ~P) \/ (Q \/ ~Q))) -> (~P \/ Q).
  Proof.
    intros [Himpl H].
    destruct H as [H | H], H.
    - right; apply Himpl, H.
    - left; assumption.
    - right; assumption.
    - left.
      contradict H.
      apply Himpl, H.
  Qed.
End Chapter4.

(** * 5. First-Order Logic: All and Exists *)
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
    exists x; assumption.
  Qed.

  Theorem thm18b : (forall x, P x -> C) -> ((exists x, P x) -> C).
  Proof.
    intros ? [x H0].
    apply H with x, H0.
  Qed.

  Theorem thm19a : (C \/ ~C) -> (exists _ : T, True) -> (C -> (exists x, P x)) ->
    (exists x, C -> P x).
  Proof.
    intros Hdec Hinhab Himpl.
    destruct Hdec as [HC | HnC].
    - destruct (Himpl HC) as [x HPx].
      exists x.
      intro; assumption.
    - destruct Hinhab as [x _].
      exists x.
      (* TODO: again, is there a shorthand for this? *)
      intro H; contradiction.
  Qed.

  Theorem thm19b : (exists x, C -> P x) -> C -> (exists x, P x).
  Proof.
    intros H HC.
    destruct H as [x H].
    exists x.
    (** same as [exact (H HC).] *)
    apply H, HC.
  Qed.

  (** Now it's getting funky *)
  Theorem thm20a : (C \/ ~C) -> (exists _ : T, True) -> (~(forall x, P x) ->
    (exists x, ~P x)) -> ((forall x, P x) -> C) -> (exists x, P x -> C).
  Proof.
    intros Hdec Hinhab Hmarkov H0.
    destruct Hdec.
    - destruct Hinhab as [x _].
      exists x.
      intro; assumption.
    (* TODO: What's going on around here? It seems that we're introduction the
       consequent of the [~(forall ...) -> (exists ~...)] hypothesis, so we first
       need to prove the antecedent. BUT, generally, [destruct] doesn't act on
       implications, so we're probably [destruct]ing on the [ex] here *)
    - destruct Hmarkov.
      + intro.
        (** [contradict] is sometimes the same as [elim], but additionally removes the
            hypothesis from the context *)
        contradict H.
        (** or [exact (H0 H1).] *)
        apply H0, H1.
      + exists x.
        intro; contradiction.
  Qed.

  Theorem thm20b : (exists x, P x -> C) -> (forall x, P x) -> C.
  Proof.
    intros [x H] Huniv.
    apply H, Huniv.
  Qed.

  Theorem thm21a : (exists _ : T, True) -> ((exists x, P x) \/ C) ->
    (exists x, P x \/ C).
  Proof.
    intros Hex H0.
    destruct H0 as [[x HPx] | HC].
    - exists x.
      left; assumption.
    - destruct Hex as [x _].
      exists x.
      right; assumption.
  Qed.

  Theorem thm21b : (exists x, P x \/ C) -> ((exists x, P x) \/ C).
  Proof.
    intros [x [? | ?]].
    - left; exists x; assumption.
    - right; assumption.
  Qed.

  Theorem thm22a : ((forall x, P x) \/ C) -> (forall x, P x \/ C).
  Proof.
    intros [H x | H].
    - left; apply H.
    - right; assumption.
  Qed.

  Theorem thm22b : (C \/ ~C) -> (forall x, P x \/ C) -> ((forall x, P x) \/ C).
  Proof.
    intros [HC | HnC] H.
    - right; assumption.
    - left.
      intro x.
      destruct (H x); [assumption | contradiction].
  Qed.

  Theorem thm23a : ((exists x, P x) /\ C) -> (exists x, P x /\ C).
  Proof.
    intros [[x H] HC].
    exists x.
    split; assumption.
  Qed.

  Theorem thm23b : (exists x, P x /\ C) -> ((exists x, P x) /\ C).
  Proof.
    intros [x [H HC]].
    split; [exists x | ]; assumption.
  Qed.

  Theorem thm24a : ((forall x, P x) /\ C) -> (forall x, P x /\ C).
  Proof.
    intros [H HC x].
    split; [apply H | apply HC].
  Qed.

  Theorem thm24b : (exists _ : T, True) -> (forall x, P x /\ C) ->
    ((forall x, P x) /\ C).
  Proof.
    intros Hinhab H0.
    split.
    - intro x; apply H0.
    - destruct Hinhab as [x _].
      (** or [destruct (H0 x) as [_ HC]. exact HC] *)
      apply (proj2 (H0 x)).
  Qed.
End Chapter5.

(* vim: set et ts=2 sts=2 sw=2: *)

