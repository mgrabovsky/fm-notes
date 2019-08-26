(** Based on the arithmetic expression example in InductionExercises.v *)

Set Implicit Arguments.
Unset Strict Implicit.

Require Import List.
Require Import PeanoNat.
Import ListNotations.
Import Nat.

(** Syntax definition *)
Inductive expr : Type :=
| Const  (_   : nat)
| Plus   (_ _ : expr)
| Times  (_ _ : expr)
| Modulo (_ _ : expr)
| Ble    (_ _ : expr)
| Beq    (_ _ : expr).

Infix "%+"  := Plus   (left associativity, at level 50).
Infix "%*"  := Times  (left associativity, at level 45).
Infix "%%"  := Modulo (left associativity, at level 51).
Infix "%<=" := Ble    (left associativity, at level 52).
Infix "%="  := Beq    (left associativity, at level 52).

(** Reference evaluator -- denotational semantics *)
Fixpoint eval_expr e :=
  match e with
  | Const n      => n
  | Plus e1 e2   => eval_expr e1 + eval_expr e2
  | Times e1 e2  => eval_expr e1 * eval_expr e2
  | Modulo e1 e2 => modulo (eval_expr e1) (eval_expr e2)
  | Ble e1 e2    => let v1 := eval_expr e1 in
                     let v2 := eval_expr e2 in
                     if v1 <=? v2 then 1 else 0
  | Beq e1 e2    => let v1 := eval_expr e1 in
                     let v2 := eval_expr e2 in
                     if v1 =? v2 then 1 else 0
  end.

(** Continuation-passing-style evaluator *)
Fixpoint eval_expr_cont' {A} e (k : nat -> A) :=
  match e with
  | Const n      => k n
  | Plus e1 e2   => eval_expr_cont' e2 (fun n2 =>
                      eval_expr_cont' e1 (fun n1 =>
                        k (n1 + n2)))
  | Times e1 e2  => eval_expr_cont' e2 (fun n2 =>
                      eval_expr_cont' e1 (fun n1 =>
                        k (n1 * n2)))
  | Modulo e1 e2 => eval_expr_cont' e2 (fun n2 =>
                      eval_expr_cont' e1 (fun n1 =>
                        k (modulo n1 n2)))
  | Ble e1 e2    => eval_expr_cont' e2 (fun n2 =>
                      eval_expr_cont' e1 (fun n1 =>
                        k (if n1 <=? n2 then 1 else 0)))
  | Beq e1 e2    => eval_expr_cont' e2 (fun n2 =>
                      eval_expr_cont' e1 (fun n1 =>
                        k (if n1 =? n2 then 1 else 0)))
  end.

Definition eval_expr_cont e := eval_expr_cont' e (fun x => x).

(** Correctness theorem for the CPS evaluator *)
Lemma eval_expr_cont'_evals : forall A e (k : nat -> A),
  eval_expr_cont' e k = k (eval_expr e).
Proof.
  induction e; intro; cbn; solve [ reflexivity | now rewrite IHe2, IHe1 ].
Qed.

Theorem eval_expr_cont_correct : forall e, eval_expr_cont e = eval_expr e.
Proof.
  intro; unfold eval_expr_cont.
  now rewrite eval_expr_cont'_evals.
Qed.

(** Stack language syntax *)
Inductive  instr := Push (n : nat) | Add | Mul | Mod | Le | Eq.
Definition prog  := list instr.
Definition stack := list nat.

(** Stack language evaluator *)
Fixpoint run (p : prog) (s : stack) : stack :=
  match p with
  | []      => s
  | i :: p' => let s' :=
                  match i with
                  | Push n => n :: s
                  | Add =>
                    match s with
                    | n1 :: n2 :: s' => n1 + n2 :: s'
                    | _              => s
                    end
                  | Mul =>
                    match s with
                    | n1 :: n2 :: s' => n1 * n2 :: s'
                    | _              => s
                    end
                  | Mod =>
                    match s with
                    | n1 :: n2 :: s' => modulo n1 n2 :: s'
                    | _              => s
                    end
                  | Le =>
                    match s with
                    | n1 :: n2 :: s' =>
                      (if n1 <=? n2 then 1 else 0) :: s'
                    | _              => s
                              end
                  | Eq =>
                    match s with
                    | n1 :: n2 :: s' =>
                      (if n1 =? n2 then 1 else 0) :: s'
                    | _              => s
                    end
                  end in
               run p' s'
  end.

(** Compiler from arithmetic expressions to stack language *)
Fixpoint compile (e : expr) : prog :=
  match e with
  | Const n      => [Push n]
  | Plus e1 e2   => compile e2 ++ compile e1 ++ [Add]
  | Times e1 e2  => compile e2 ++ compile e1 ++ [Mul]
  | Modulo e1 e2 => compile e2 ++ compile e1 ++ [Mod]
  | Ble e1 e2    => compile e2 ++ compile e1 ++ [Le]
  | Beq e1 e2    => compile e2 ++ compile e1 ++ [Eq]
  end.

(** Example expression and its compiled program *)
Definition ex1   :=
  (Const 9 %+ Const 1 %+ Const 3 %* Const 7 %% Const 9) %<= Const 9.
Compute ex1.
Definition prog1 := compile ex1.
Definition res1  := run prog1 [].

Compute (prog1, res1).

(** Correctness/correspondence theorem for stack compiler+evaluator *)
Lemma run_app : forall p p' s, run (p ++ p') s = run p' (run p s).
Proof.
  induction p.
  - reflexivity.
  - intros; cbn.
    now rewrite IHp.
Qed.

Lemma compile_correct' : forall e s, run (compile e) s = eval_expr e :: s.
Proof.
  induction e; intro; cbn;
    solve [ reflexivity | now rewrite run_app, IHe2, run_app, IHe1 ].
Qed.

Theorem compile_correct : forall e, run (compile e) [] = [eval_expr e].
Proof.
  now intro; rewrite compile_correct'.
Qed.

(** Operational small-step semantics for the language *)
Reserved Infix "==>" (at level 60).
Inductive step_expr : expr -> expr -> Prop :=
(* TODO: Should we have this rule in the relation?
 * See also note below on [step_deterministic].

| Step_Const : forall n, 
    Const n ==> Const n
*)

| Step_Plus1 : forall e1 e1' e2,
    e1 ==> e1' ->
    e1 %+ e2 ==> e1' %+ e2
| Step_Plus2 : forall n1 e2 e2',
    e2 ==> e2' ->
    Const n1 %+ e2 ==> Const n1 %+ e2'
| Step_Plus3 : forall n1 n2,
    Const n1 %+ Const n2 ==> Const (n1 + n2)

| Step_Times1 : forall e1 e1' e2,
    e1 ==> e1' ->
    e1 %* e2 ==> e1' %* e2
| Step_Times2 : forall n1 e2 e2',
    e2 ==> e2' ->
    Const n1 %* e2 ==> Const n1 %* e2'
| Step_Times3 : forall n1 n2,
    Const n1 %* Const n2 ==> Const (n1 * n2)

| Step_Mod1 : forall e1 e1' e2,
    e1 ==> e1' ->
    e1 %% e2 ==> e1' %% e2
| Step_Mod2 : forall n1 e2 e2',
    e2 ==> e2' ->
    Const n1 %% e2 ==> Const n1 %% e2'
| Step_Mod3 : forall n1 n2,
    Const n1 %% Const n2 ==> Const (n1 mod n2)

| Step_Ble1 : forall e1 e1' e2,
    e1 ==> e1' ->
    e1 %<= e2 ==> e1' %<= e2
| Step_Ble2 : forall n1 e2 e2',
    e2 ==> e2' ->
    Const n1 %<= e2 ==> Const n1 %<= e2'
| Step_Ble3 : forall n1 n2,
    Const n1 %<= Const n2 ==> Const (if n1 <=? n2 then 1 else 0)

| Step_Beq1 : forall e1 e1' e2,
    e1 ==> e1' ->
    e1 %= e2 ==> e1' %= e2
| Step_Beq2 : forall n1 e2 e2',
    e2 ==> e2' ->
    Const n1 %= e2 ==> Const n1 %= e2'
| Step_Beq3 : forall n1 n2,
    Const n1 %= Const n2 ==> Const (if n1 =? n2 then 1 else 0)
where
  "e1 '==>' e2" := (step_expr e1 e2).

Require Import Relation_Operators.
Definition step_expr_star := clos_refl_trans_1n _ step_expr.
Notation "e1 '==>*' e2" := (step_expr_star e1 e2) (at level 60).

(* TODO: Should we consider [==>] or [==>*]? *)
Lemma step_deterministic : forall e, exists! n, e ==>* Const n.
Proof.
  induction e.
  - exists n.
    split; [ constructor | ].
    inversion_clear 1; [ reflexivity | inversion H0 ].
  - destruct IHe1 as [n1 [Hstep1 Hinv1]], IHe2 as [n2 [Hstep2 Hinv2]].
    exists (n1 + n2).
    split.
    + inversion_clear Hstep1; inversion_clear Hstep2.
      * econstructor; [ apply Step_Plus3 | constructor ].
      * econstructor; [ apply Step_Plus2; eassumption | ].
        fold step_expr_star in *.
        (* TODO: Quite tedious... Automate this! *)
Admitted.

