Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Defensive Implicit.
Generalizable All Variables.

Require Import Bool List.
Import ListNotations.
Require Import Program.

Inductive Dec (P : Prop) : Type :=
| yes :  P -> Dec P
| no  : ~P -> Dec P.

Record HDec (P : Prop) : Type := hd
  { found : bool
  ; proof : Is_true found -> P
  }.

Arguments hd [P] found proof.

Definition HDecType {P} (p : HDec P) : Type :=
  match p with
  | hd true _  => P
  | hd false _ => True
  end.

Definition evidence {P} (p : HDec P) : HDecType p :=
  match p with
  | hd true p  => p I
  | hd false _ => I
  end.

Definition fromDec {A} (d : Dec A) :=
  match d with
  | yes p => hd true (fun _ => p)
  | no _  => hd false (False_rect _)
  end.

Class IsSearch (t : Prop -> Type) : Type := is_hdec
  { toHDec : forall p, t p -> HDec p }.

Instance HDecIsSearch : IsSearch HDec :=
  is_hdec (fun _ x => x).
Instance DecIsSearch : IsSearch Dec :=
  is_hdec (fun _ p => fromDec p).

Goal forall a b, Is_true (a || b) -> (Is_true a) \/ (Is_true b).
intros [] []; auto.
Qed.

Goal forall a b, Is_true (a && b) -> (Is_true a) /\ (Is_true b).
intros [] []; auto; intros [].
Qed.

(** * Model checking *)

(** ** Transition diagrams *)
Record Diagram (L : Type) (Sigma : Type) : Type := td
  { delta : L * Sigma -> list (L * Sigma)
  ; II    : L
  }.

Arguments td [L Sigma] delta II.

Definition par {L1 L2 Sigma} (d1 : Diagram L1 Sigma) (d2 : Diagram L2 Sigma) :=
  match d1, d2 with
  | td delta1 i1, td delta2 i2 =>
      let delta := fun x => match x with ((l1, l2), sigma) =>
                      map (fun y => ((fst y, l2), snd y)) (delta1 (l1, sigma)) ++
                      map (fun y => ((l1, fst y), snd y)) (delta2 (l2, sigma)) end
       in td delta (i1, i2)
  end.

Definition HiHorse :=
  let delta := fun x => [(fst x, S (snd x))]
   in td delta tt.
Definition LoRoad :=
  let delta := fun x => [(fst x, pred (snd x))]
   in td delta tt.

CoInductive Suspended (A : Type) : Type :=
| delay : A -> Suspended A.

Definition force {A} (s : Suspended A) :=
  match s with
  | delay a => a
  end.

(** ** Computation tree logic *)
Module Type CTL.
  Parameters L Sigma : Type.

  Inductive CT :=
    At : L * Sigma -> Suspended (list CT) -> CT.

  Require FunInd.
  Function follow dia s {measure length (delta dia s)} :=
    let followAll := fix followAll dia xs {struct xs} :=
      match xs with
      | cons s ss => follow dia s :: followAll dia ss
      | nil => nil
      end in
    At s (delay (followAll dia (delta dia s))).

  Definition model (d : Diagram L Sigma) (sigma : Sigma) :=
    match d with
    | td delta i => follow d (i, sigma)
    end.
