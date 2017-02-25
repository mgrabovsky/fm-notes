Require Import List.
Import ListNotations.

Definition ident := nat.

Inductive type : Set :=
| TyBool | TyNat
| TyArrow : type -> type -> type.
Infix "→" := TyArrow (right associativity, at level 60).

Inductive term : Set :=
| Var : ident -> term
| Abs : ident -> type -> term -> term
| App : term -> term -> term
| True | False
| If : term -> term -> term -> term
| Zero
| Succ : term -> term.

Definition context := list (ident * type).

Reserved Notation "Γ '|-' t '\in' ty" (at level 80).
Inductive has_type : context -> term -> type -> Prop :=
| TyVar   : forall Γ x ty,
                        In (x, ty) Γ ->
                        Γ |- Var x  \in ty
| TyAbs   : forall Γ x b xτ bτ,
             (x, xτ) :: Γ |- b \in bτ ->
                        Γ |- Abs x xτ b \in xτ → bτ
| TyApp   : forall Γ t t' τ τ',
                        Γ |- t      \in τ → τ' ->
                        Γ |- t'     \in τ ->
                        Γ |- App t t' \in τ'
| TyTrue  : forall Γ,   Γ |- True   \in TyBool
| TyFalse : forall Γ,   Γ |- False  \in TyBool
| TyIf    : forall Γ b tthen telse τ,
                        Γ |- b      \in TyBool ->
                        Γ |- tthen  \in τ ->
                        Γ |- telse  \in τ ->
                        Γ |- If b tthen telse \in τ
| TyZero  : forall Γ,   Γ |- Zero   \in TyNat
| TySucc  : forall Γ t, Γ |- t      \in TyNat ->
                        Γ |- Succ t \in TyNat
where "Γ '|-' t '\in' ty" := (has_type Γ t ty).

Hint Constructors has_type.

Fixpoint type_order (τ : type) :=
  match τ with
  | TyBool | TyNat => 0
  | TyArrow τ τ' => max (S (type_order τ)) (type_order τ')
  end.

Example typing1 : forall Γ τ i,
  Γ |- Abs i τ (Var i) \in τ → τ.
Proof.
  intros.
  constructor; constructor.
  cbn; auto.
Qed.

Example typing2 : forall Γ τ τ' i j,
  Γ |- Abs i τ (Abs j τ' (Var i)) \in τ → τ' → τ.
Proof.
  intros.
  constructor; constructor; constructor.
  cbn; auto.
Qed.

Example typing3 : forall Γ τ τ' τ'' i j k,
  Γ |- Abs i (τ → τ' → τ'')
        (Abs j (τ → τ')
          (Abs k τ
            (App (App (Var i) (Var k)) (App (Var j) (Var k)))))
    \in (τ → τ' → τ'') → (τ → τ') → τ → τ''.
Proof.
  repeat try constructor.
  econstructor; econstructor; constructor; cbn; auto.
Qed.

