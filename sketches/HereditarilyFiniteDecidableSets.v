Require List.
Import List.ListNotations.
Require Import Setoid Morphisms.

Coercion is_true b := b = true.

Inductive reflect (P : Prop) : bool -> Type :=
| Reflect_true  :  P -> reflect P true
| Reflect_false : ~P -> reflect P false.

Lemma andP : forall b1 b2 : bool, reflect (b1 /\ b2) (b1 && b2).
Proof.
  intros [] []; constructor.
  1: split; reflexivity.
  all: intro H; inversion H; discriminate.
Qed.

Lemma orP : forall b1 b2 : bool, reflect (b1 \/ b2) (b1 || b2).
Proof.
  intros [] []; constructor;
    [now left | now left | now right | idtac].
  intro H; destruct H; inversion H.
Qed.

Lemma andE : forall b1 b2 : bool, (b1 /\ b2) <-> (b1 && b2)%bool.
Proof.
  split.
  - now intros [H1 H2]; rewrite H1, H2.
  - intro H.
    apply Bool.andb_true_iff in H.
    now destruct H as [H1 H2]; rewrite H1, H2.
Qed.

Lemma orE : forall b1 b2 : bool, (b1 \/ b2) <-> (b1 || b2)%bool.
Proof.
  split.
  - now intros []; intro H; rewrite H; [idtac | destruct b1].
  - intro H.
    destruct b1; [now left | idtac].
    destruct b2; [now right | idtac].
    inversion H.
Qed.

Inductive hf : Set := HF (elts : list hf).

Definition forall_elt (P : hf -> bool) (x : hf) :=
  let (xs) := x in List.forallb P xs.
Definition exists_elt (P : hf -> bool) (x : hf) :=
  let (xs) := x in List.existsb P xs.

Fixpoint eq_hf x y : bool :=
  forall_elt (fun x' => exists_elt (fun y' => eq_hf x' y') y) x &&
  forall_elt (fun y' => exists_elt (fun x' => eq_hf x' y') x) y.
Infix "==" := eq_hf (at level 30).

Definition in_hf x y := exists_elt (fun y' => eq_hf x y') y.

Lemma eq_hf_refl : Reflexive eq_hf.
Proof.
  red. fix this 1.
  intros [elts].
  induction elts.
  - reflexivity.
  - cbn; apply andE; split; apply andE; split.
    * apply orE; left. apply this.
    * inversion IHelts; apply andE in H0; destruct H0.
      apply List.forallb_forall.
      intros x H1; apply orE; right; apply List.existsb_exists; exists x.
      split; [assumption | idtac].
    * apply orE; left. apply this.
    * inversion IHelts; apply andE in H0; destruct H0.
      apply List.forallb_forall.
      intros y H1; apply orE; right; apply List.existsb_exists; exists y.
      split; [assumption | apply this].
Qed.

Lemma eq_hf_sym : Symmetrix eq_hf.
Lemma eq_hf_trans : Transitive eq_hf.
Lemma eq_in_hf_compat : forall x x' y y', x == x' -> y == y' ->
  in_hf x y -> in_hf x' y'.

Definition empty := HF [].
Definition pair x y := HF [x; y].