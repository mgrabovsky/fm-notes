(** Following James Wilcox's 'Exercises on Generalizing the Induction Hypothesis':
    <https://homes.cs.washington.edu/~jrw12/InductionExercises.html>
 *)

Require Import List Arith.
Import ListNotations.

Section SummingLists.
Fixpoint sum l :=
  match l with
  | []      => 0
  | x :: xs => x + sum xs
  end.

(** Tail-recursive sum *)
Fixpoint sum_tail' l acc :=
  match l with
  | []      => acc
  | x :: xs => sum_tail' xs (x + acc)
  end.

Definition sum_tail l := sum_tail' l 0.

Lemma sum_tail'_sums : forall l acc, sum_tail' l acc = sum l + acc.
Proof.
  induction l.
  - reflexivity.
  - intro; cbn.
    rewrite IHl.
    rewrite Nat.add_assoc.
    now rewrite (Nat.add_comm (sum l) _).
Qed.

Theorem sum_tail_correct : forall l, sum_tail l = sum l.
Proof.
  intro; unfold sum_tail.
  rewrite sum_tail'_sums.
  now rewrite Nat.add_0_r.
Qed.

(** Continuation-passing-style sum *)
Fixpoint sum_cont' {A} l (k : nat -> A) :=
  match l with
  | []      => k 0
  | x :: xs => sum_cont' xs (fun ans => k (x + ans))
  end.

Definition sum_cont l := sum_cont' l (fun x => x).

Lemma sum_cont'_sums : forall A l (k : nat -> A), sum_cont' l k = k (sum l).
Proof.
  induction l.
  - reflexivity.
  - intro; cbn.
    now rewrite IHl.
Qed.

Theorem sum_cont_correct : forall l, sum_cont l = sum l.
Proof.
  intro; unfold sum_cont.
  now rewrite sum_cont'_sums.
Qed.
End SummingLists.

Section TailRecursion.
(** Reverse *)
Fixpoint rev_tail' {A} (l acc : list A) :=
  match l with
  | []      => acc
  | x :: xs => rev_tail' xs (x :: acc)
  end.

Definition rev_tail {A} (l : list A) := rev_tail' l [].

Lemma rev_tail'_reverses : forall A (l acc : list A), rev_tail' l acc = rev l ++ acc.
Proof.
  induction l.
  - reflexivity.
  - intro; cbn.
    rewrite IHl.
    now rewrite app_assoc_reverse.
Qed.

Theorem rev_tail_correct : forall A (l : list A), rev_tail l = rev l.
Proof.
  intros; unfold rev_tail.
  rewrite rev_tail'_reverses.
  now rewrite app_nil_r.
Qed.

(** Map *)
Fixpoint map_tail' {A B} (f : A -> B) (l : list A) (acc : list B) :=
  match l with
  | []      => rev_tail acc
  | x :: xs => map_tail' f xs (f x :: acc)
  end.

Definition map_tail {A B} (f : A -> B) l := map_tail' f l [].

Lemma map_tail'_maps : forall A B (f : A -> B) l acc,
  map_tail' f l acc = rev acc ++ map f l.
Proof.
  induction l.
  - intro; cbn.
    now rewrite rev_tail_correct, app_nil_r.
  - intro; cbn.
    rewrite IHl; cbn.
    now rewrite app_assoc_reverse.
Qed.

Theorem map_tail_correct : forall A B (f : A -> B) l,
  map_tail f l = map f l.
Proof.
  intros; unfold map_tail.
  now rewrite map_tail'_maps.
Qed.
End TailRecursion.

Section ArithExpr.
Inductive expr : Type :=
| Const : nat -> expr
| Plus  : expr -> expr -> expr.

Fixpoint eval_expr e :=
  match e with
  | Const n    => n
  | Plus e1 e2 => eval_expr e1 + eval_expr e2
  end.

(** Accumulator-based evaluator *)
Fixpoint eval_expr_acc' e acc :=
  match e with
  | Const n    => n + acc
  | Plus e1 e2 => eval_expr_acc' e2 (eval_expr_acc' e1 acc)
  end.

Definition eval_expr_acc e := eval_expr_acc' e 0.

Lemma eval_expr_acc'_evals : forall e acc, eval_expr_acc' e acc = eval_expr e + acc.
Proof.
  induction e.
  - reflexivity.
  - intro; cbn.
    rewrite IHe1, IHe2.
    now rewrite Nat.add_assoc, (Nat.add_comm (eval_expr e2) _).
Qed.

Theorem eval_expr_correct : forall e, eval_expr_acc e = eval_expr e.
Proof.
  intro; unfold eval_expr_acc.
  rewrite eval_expr_acc'_evals.
  now rewrite Nat.add_0_r.
Qed.

(** Continuation-passing-style evaluator *)
Fixpoint eval_expr_cont' {A} e (k : nat -> A) :=
  match e with
  | Const n    => k n
  | Plus e1 e2 => eval_expr_cont' e2 (fun n2 =>
                    eval_expr_cont' e1 (fun n1 =>
                      k (n1 + n2)))
  end.

Definition eval_expr_cont e := eval_expr_cont' e (fun x => x).

Lemma eval_expr_cont'_evals : forall A e (k : nat -> A),
  eval_expr_cont' e k = k (eval_expr e).
Proof.
  induction e.
  - reflexivity.
  - intro; cbn.
    now rewrite IHe2, IHe1.
Qed.

Theorem eval_expr_cont_correct : forall e, eval_expr_cont e = eval_expr e.
Proof.
  intro; unfold eval_expr_cont.
  now rewrite eval_expr_cont'_evals.
Qed.

(** Compiling to a stack language *)
Inductive instr  := Push (n : nat) | Add.
Definition prog  := list instr.
Definition stack := list nat.

Fixpoint run (p : prog) (s : stack) : stack :=
  match p with
  | []      => s
  | i :: p' => let s' := match i with
                         | Push n => n :: s
                         | Add    => match s with
                                     | n1 :: n2 :: s' => n1 + n2 :: s'
                                     | _              => s
                                     end
                         end in
               run p' s'
  end.

Fixpoint compile (e : expr) : prog :=
  match e with
  | Const n    => [Push n]
  | Plus e1 e2 => compile e1 ++ compile e2 ++ [Add]
  end.

Definition ex1   := Plus (Const 9) (Plus (Plus (Const 1) (Const 3)) (Const 7)).
Definition prog1 := compile ex1.
Definition res1  := run prog1 [].

Compute match list_eq_dec Nat.eq_dec res1 [eval_expr ex1] with
        | left _  => true
        | right _ => false
        end.

Lemma run_app : forall p p' s, run (p ++ p') s = run p' (run p s).
Proof.
  induction p.
  - reflexivity.
  - intros; cbn.
    now rewrite IHp.
Qed.

Lemma run_correct : forall e s, run (compile e) s = eval_expr e :: s.
Proof.
  induction e.
  - reflexivity.
  - intro; cbn.
    rewrite run_app, IHe1, run_app, IHe2; cbn.
    now rewrite Nat.add_comm.
Qed.

Theorem compile_correct : forall e, run (compile e) [] = [eval_expr e].
Proof.
  now intro; rewrite run_correct.
Qed.
End ArithExpr.

Section Fibonacci.
Fixpoint fib n :=
  match n with
  | 0 | 1           => 1
  | S (S n'' as n') => fib n' + fib n''
  end.

Fixpoint fib_tail' n a b :=
  match n with
  | 0    => b
  | S n' => fib_tail' n' (a + b) a
  end.

Definition fib_tail n := fib_tail' n 1 1.

Lemma fib_step : forall n, fib (n + 2) = fib (n + 1) + fib n.
Proof.
  induction n.
  - reflexivity.
  - rewrite !plus_Sn_m.
    cbn.
    rewrite IHn.
    rewrite Nat.add_1_r.
    (* TODO: Could use some Setoid rewriting? *)
    rewrite !Nat.add_succ_r, Nat.add_0_r.
    rewrite (Nat.add_comm (fib (S n)) (fib n)).
    reflexivity.
Qed.

Lemma fib_helper : forall n a b,
  fib_tail' (n + 2) a b = a * fib (n + 1) + b * fib n.
Proof.
  induction n; intros.
  - cbn.
    now rewrite !Nat.mul_1_r.
  - (* LHS *)
    rewrite plus_Sn_m.
    unfold fib_tail'; fold fib_tail'.
    rewrite IHn.
    (* RHS *)
    (* TODO: Could use some Setoid rewriting? *)
    rewrite plus_Snm_nSm, fib_step.
    rewrite Nat.mul_add_distr_l, Nat.mul_add_distr_r.
    rewrite <- Nat.add_assoc, (Nat.add_comm _ (a * fib n)), Nat.add_assoc.
    now rewrite Nat.add_1_r.
Qed.

Lemma SSn_add_r : forall n, S (S n) = n + 2.
Proof.
  intro.
  now rewrite <- Nat.add_1_r, <- Nat.add_1_r, <- Nat.add_assoc, plus_Snm_nSm, Nat.add_0_l.
Qed.

Theorem fib_tail_correct : forall n, fib_tail n = fib n.
Proof.
  destruct 0; [reflexivity | destruct 0; [reflexivity | idtac]].
  unfold fib_tail.
  rewrite SSn_add_r.
  rewrite fib_helper, fib_step.
  now rewrite !Nat.mul_1_l.
Qed.
End Fibonacci.
