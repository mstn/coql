Require Import Coq.Bool.Bool.
Require Import Coq.Arith.Arith.
Require Import Coq.Strings.String.

Inductive tm: Type :=
  | tempty: tm
  | terr: string -> tm
  | tnat: nat -> tm
  | tbool: bool -> tm
  | tstring: string -> tm
  | thole: tm
  | tfield: string -> tm -> tm -> tm
  | tfieldr: string -> tm -> tm -> tm
  | tpar: tm -> tm -> tm.

Inductive ty: Type :=
  | TTop: ty
  | TBot: ty    
  | TNat: ty
  | TString: ty
  | TBool: ty
  | TField: string -> ty -> ty -> ty
  | TPar: ty -> ty -> ty.

Inductive value: tm -> Prop :=
  | v_empty:
      value tempty
  | v_err: forall s: string,
      value (terr s)
  | v_nat: forall n: nat,
      value (tnat n)
  | v_bool: forall b: bool,
      value (tbool b)
  | v_string: forall s: string,
      value (tstring s)
  | v_field: forall s v1 v2,
      value v1 ->
      value v2 ->
      value (tfieldr s v1 v2)
  | v_par: forall v1 v2,
      value v1 ->
      value v2 ->
      value (tpar v1 v2).

Hint Constructors value.

Reserved Notation "'|-' t '\in' T" (at level 40).

Inductive has_type: tm -> ty -> Prop :=
  | T_Empty:
    |- tempty \in TBot
  | T_Err: forall s: string,
    |- terr s \in TBot  
  | T_Nat: forall n: nat,
    |- tnat n \in TNat
  | T_Bool: forall b: bool,
    |- tbool b \in TBool
  | T_String: forall s: string,
    |- tstring s \in TString
  | T_Hole:
    |- thole \in TTop
  | T_Field: forall n t1 t2 T1 T2,
    |- t1 \in T1 ->
    |- t2 \in T2 ->
    |- tfield n t1 t2 \in TField n T1 T2
  | T_FieldR: forall n t1 t2 T1 T2,
    |- t1 \in T1 ->
    |- t2 \in T2 ->
    |- tfield n t1 t2 \in TField n T1 T2    
  | T_Par: forall t1 t2 T1 T2,
    |- t1 \in T1 ->
    |- t2 \in T2 ->
    |- tpar t1 t2 \in TPar T1 T2
where "'|-' t \in T" := (has_type t T).

Hint Constructors has_type.

Reserved Notation "T1 '<:' T2" (at level 40).

Inductive subtype: ty -> ty -> Prop :=
  | S_Bot: forall T,
    TBot <: T
  | S_Top: forall T,
    T <: TTop
  | S_Refl: forall T,
    T <: T
  | S_Trans: forall T U S,
    T <: U ->
    U <: S ->
    T <: S
  | S_Field: forall s T1 T2 U1 U2,
    U1 <: T1 ->
    T2 <: U2 ->
    TField s T1 T2 <: TField s U1 U2
  | S_FieldR: forall s T1 T2 U1 U2,
    U1 <: T1 ->
    T2 <: U2 ->
    TField s T1 T2 <: TField s U1 U2
  | S_Width: forall T U,
    TPar T U <: T
  | S_Perm: forall T U,
    TPar T U <: TPar U T
  | S_Depth: forall T1 T2 U1 U2,
    T1 <: T2 ->
    U1 <: U2 ->
    TPar T1 U1 <: TPar T2 U2
where "T1 '<:' T2" := (subtype T1 T2).

Hint Constructors subtype.
