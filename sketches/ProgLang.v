Set Implicit Arguments.

Require Import List.
Import ListNotations.

Inductive type : Type :=
| Nat  : type
| Func : type -> type -> type.

Inductive member (A : Type) (elm : A) : list A -> Type :=
| HFirst : forall ls, member elm (elm :: ls)
| HNext  : forall x ls, member elm ls -> member elm (x :: ls).

Inductive term : list type -> type -> Type :=
| Var   : forall G t, member t G -> term G t
| Const : forall G, nat -> term G Nat
| Plus  : forall G, term G Nat -> term G Nat -> term G Nat
| Abs   : forall G dom ran,
            term (dom :: G) ran -> term G (Func dom ran)
| App   : forall G dom ran,
            term G (Func dom ran) -> term G dom -> term G ran
| Let   : forall G t1 t2,
            term G t1 -> term (t1 :: G) t2 -> term G t2.

Lemma ty_eq_dec : forall x y : type, {x = y} + {x <> y}.
Proof. decide equality. Defined.

Lemma term_case :
  forall G t (P : term G t -> Type),
    (forall p, P (Var p)) ->
    (forall n (pf : t = Nat),
        P (eq_rect Nat _ (Const G n) t (eq_sym pf))) ->
    (forall e1 e2 (pf : t = Nat),
        P (eq_rect Nat _ (Plus e1 e2) t (eq_sym pf))) ->
    (forall dom ran (pf : t = Func dom ran) b,
        P (eq_rect (Func dom ran) _ (Abs b) _ (eq_sym pf))) ->
    (forall dom e1 e2, P (App (dom:=dom) e1 e2)) ->
    (forall ty1 e1 e2, P (Let (t1:=ty1) e1 e2)) ->
    forall e, P e.
Proof.
  intros.
  destruct e eqn:?; auto.
  - specialize (X0 n eq_refl); auto.
  - specialize (X1 t0_1 t0_2 eq_refl); auto.
  - specialize (X2 dom ran eq_refl t0); auto.
Qed.

Ltac term_destruct v :=
  pattern v; apply term_case; clear v; intros.

Fixpoint cfold G t (e : term G t) : term G t :=
    match e with
      | @Plus G e1 e2 =>
        let e1' := cfold e1 in
        let e2' := cfold e2 in
        let maybeOpt := match e1' return _ with
                          | Const _ n1 =>
                            match e2' return _ with
                              | Const _ n2 => Some (@Const G (n1 + n2))
                              | _ => None
                            end
                          | _ => None
                        end in
        match maybeOpt with
          | None    => Plus e1' e2'
          | Some e' => e'
        end

      | Abs e1    => Abs (cfold e1)
      | App e1 e2 => App (cfold e1) (cfold e2)

      | Let e1 e2 => Let (cfold e1) (cfold e2)

      | e => e
    end.
