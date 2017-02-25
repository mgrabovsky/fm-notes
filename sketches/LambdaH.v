Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Import Arith.

Notation Id := nat.
Notation Id_eq_dec := Nat.eq_dec.

Inductive term : Set :=
| TKind
| TType
| TPi   : Id -> term -> term -> term
| TLam  : Id -> term -> term -> term
| TApp  : term -> term -> term
| TConv : term -> conv -> term
with
  conv : Set :=
| CRefl : term -> conv
| CSym  : conv -> conv
| CComp : conv -> conv -> conv
| CBeta : term -> conv
| CIota : term -> conv
(* {E, [V]E}, <E, [V]E> *)
| CApp  : conv -> conv -> conv.

Fixpoint term_eq_dec (t t' : term) : bool :=
  match t, t' with
  | TKind,    TKind
  | TType,    TType    => true
  | TPi x ty u,  TPi y ty' v
  | TLam x ty u, TLam y ty' v =>
      if Id_eq_dec x y
        then if term_eq_dec u v
          then if term_eq_dec ty ty'
            then true
            else false
          else false
        else false
  | TApp u v, TApp u' v' =>
      if term_eq_dec u u'
        then if term_eq_dec v v'
          then true
          else false
        else false
  | TConv u c, TConv v d =>
      if term_eq_dec u v
        then if conv_eq_dec c d
          then true
          else false
        else false
  | _, _ => false
  end
with
conv_eq_dec (c c' : conv) : bool :=
  match c, c' with
  | CRefl t,   CRefl t'
  | CBeta t,   CBeta t'
  | CIota t,   CIota t'   => if term_eq_dec t t' then true else false
  | CSym d,    CSym d'    => if conv_eq_dec d d then true else false
  | CComp d e, CComp d' e'
  | CApp d e,  CApp d' e' =>
      if conv_eq_dec d d'
        then if conv_eq_dec e e'
          then true
          else false
        else false
  | _, _ => false
  end.

Inductive context : Set :=
| CxEmpty
| CxPush : Id -> term -> context.

Inductive judgement : Set :=
| JTy : context -> term -> term -> judgement
| JEq : conv -> term -> term -> judgement.

Inductive judg : judgement -> Prop :=
| JRefl : forall t, judg (JEq (CRefl t) t t)
| JSym  : forall c t t', judg (JEq c t t') -> judg ((JEq (CSym c)) t' t)
| JTrans : forall c d t u v, judg (JEq c t u) -> judg (JEq d u v) -> judg (JEq (CComp c d) t v)
| JBeta  : forall x ty b a, judg (JEq (CBeta (TApp (TLam x ty b) a)) (TApp (TLam x ty b) a) b)
| .
