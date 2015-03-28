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
    (* TODO: there must be a faster way, e.g. [exact (fun _ => Hnimpl).] *)
    intro; assumption.
  Qed.
End Chapter3.

(* * 4. Conjunction and Disjunction *)
Section Chapter4.
  Variables P Q : Prop.

  Theorem thm9 : (P \/ ~P) -> ~~P -> P.
  Proof.
    intros Hclassical HnnP.
    destruct Hclassical; [|contradict HnnP]; assumption.
  Qed.

  (* TODO: ... &c. *)
End Chapter4.

(* vim: set et ts=2 sw=2: *)

