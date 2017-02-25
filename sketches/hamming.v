Set Implicit Arguments.
Unset Strict Implicit.

Require Import Coq.Lists.List.
Import ListNotations.
Require Import Recdef.
Require Import Coq.Wellfounded.Lexicographic_Product.
Require Import Relation_Operators.
(*Require Import mathcomp.ssreflect.ssreflect.*)

Record metric : Type := {
  A           : Type;
  d           : A -> A -> nat;
  coincidence : forall x y, d x y = 0 <-> x = y;
  symmetry    : forall x y, d x y = d y x;
  triangle    : forall x y z, d x z <= d x y + d y z
}.

Check fun A => lexprod (list A) (fun _ => list A) (fun xs ys => length xs < length ys)
  (fun _ xs ys => length xs < length ys).

Section Hamming.
  Variables (A : Type) (eq_dec : forall x y : A, {x = y} + {x <> y}).

  Check length.
  Definition R (X Y : list A * list A) :=
    match X, Y with
    | (xs, ys), (xs', ys') =>
        length xs < length xs' \/ (length xs = length xs' /\ length ys < length ys')
    end.

  Function hamming' (X : list A * list A) {wf R X} :=
    match X with
    | ([], [])       => 0
    | ((_::xs'), []) => S (hamming' (xs', []))
    | ([], (_::ys')) => S (hamming' ([], ys'))
    | ((x::xs'), (y::ys')) =>
        if eq_dec x y
          then hamming' (xs', ys')
          else S (hamming' (xs', ys'))
    end.
  Proof.
    - right; split; auto.
    - left; auto with arith.
    - left; auto with arith.
    - left; auto with arith.
    - constructor. rename a into X. intros Y H. constructor; intros. SearchAbout Acc.

  Lemma hamming_refl : forall xs, hamming xs xs = 0.
  Proof.
    elim; trivial.
    move=> a l H //=; rewrite eqb_refl //.
 Qed.

  Instance hamming_metric : metric hamming.
    constructor.
    - split; move=> H.
      + give_up.
      + rewrite H hamming_refl //.
    - move=> x y.
      case: x.
      rewrite eqb_sym.
End Hamming.
