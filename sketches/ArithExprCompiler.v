(** Based on the arithmetic expression example in InductionExercises.v *)

Require Import List PeanoNat.
Import ListNotations Nat.

(** Syntax definition *)
Inductive expr : Type :=
| Const  : nat -> expr
| Plus   : expr -> expr -> expr
| Times  : expr -> expr -> expr
| Modulo : expr -> expr -> expr
| Ble    : expr -> expr -> expr
| Beq    : expr -> expr -> expr.

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
  | i :: p' => let s' := match i with
                         | Push n => n :: s
                         | Add    => match s with
                                     | n1 :: n2 :: s' => n1 + n2 :: s'
                                     | _              => s
                                     end
                         | Mul    => match s with
                                     | n1 :: n2 :: s' => n1 * n2 :: s'
                                     | _              => s
                                     end
                         | Mod    => match s with
                                     | n1 :: n2 :: s' => modulo n1 n2 :: s'
                                     | _              => s
                                     end
                         | Le     => match s with
                                     | n1 :: n2 :: s' =>
                                        (if n1 <=? n2 then 1 else 0) :: s'
                                     | _              => s
                                     end
                         | Eq     => match s with
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
  Beq (Const 5)
      (Plus (Const 1)
            (Modulo (Plus (Const 9) (Plus (Plus (Const 1) (Const 3)) (Const 7))) (Const 5))).
Definition prog1 := compile ex1.
Definition res1  := run prog1 [].

Compute (prog1, res1).
Compute match list_eq_dec eq_dec res1 [eval_expr ex1] with
        | left _  => true
        | right _ => false
        end.

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
  induction e; intro; cbn; solve [ reflexivity | now rewrite run_app, IHe2, run_app, IHe1 ].
Qed.

Theorem compile_correct : forall e, run (compile e) [] = [eval_expr e].
Proof.
  now intro; rewrite compile_correct'.
Qed.
