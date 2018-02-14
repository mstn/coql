(** * Core language *)

(** Here, we introduce the syntax and semantics of the language.

    The tentative roadmap can be summarized as follows.

    * Queries are terms with a type.
    * Schemas are types.
    * The execution of a query yields a value following an operational semantics.
    * Execution does not get stuck if the schema type is a subtype of the query type.

    The syntax does not correspond to the formal specification of GraphQL.
    The reason is that we want to define an _abstract_ sytax independent from the particular implementation.

    We follow the Software Foundations book by Pierce et al. 

    This work is in progress: definitions could change and some parts are not polished yet!
*)

Require Import Coq.Bool.Bool.
Require Import Coq.Arith.Arith.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Import ListNotations.

Open Scope string_scope.

(** The syntax of terms (i.e. queries) is defined as:
   
    t ::= 0
        | err
        | n
        | b
        | s
        | [-]
        | m t t
        | m* t t
        | t, t

    where n, b and s are meta-variables for numbers, booleans and strings, respectively.

    m are strings, i.e. the name of a field.
*)

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

(** The syntax of types is defined as:
   
    T ::= Top
        | Bot
        | Nat
        | Bool
        | String
        | m T T
        | T, T

*)
Inductive ty: Type :=
  | TTop: ty
  | TBot: ty    
  | TNat: ty
  | TString: ty
  | TBool: ty
  | TField: string -> ty -> ty -> ty
  | TPar: ty -> ty -> ty.

(**
   Values are a subset of terms.
   Intuitively, values are terms that cannot be reduced any further.
*)
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

(**
    We define a subtype relation.
*)
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

(**
    Every term has a type. 
*)
Reserved Notation "'|-' t '\in' T" (at level 40).

(**
    Every term has a type calculated by the following rules
*)

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
  | T_Sub: forall t T U,
     T <: U ->
     |- t \in T ->
     |- t \in U
where "'|-' t \in T" := (has_type t T).

Hint Constructors has_type.

Definition path := list string.

Inductive error: Type := | err.

(**
    Under the hood, the execution of a query consists of two parts

    1. the operational semantics of the language
    2. the internal logic implemented by resolvers

    As in GraphQL the computation carried out by resolvers is independent from the language.
    This means that the language does not know the internal state of resolvers.

    Hence, the language treats state as a kind of black box and it can peek its value only
    through a special getter function.

    Intuitively, we pile up partial results of query evaluation in a state in such a way that
    other resolvers can use them to carry out their computation.

*)

Definition state (s a: Type) := s -> (a*s).

(**
     a resolver takes a term (value) as an input

     the return value could be an error (e.g. internal server error) or a value

     the value is None, if no value for the given input is found, or a type of the computed value (i.e. run type).

     On the contrary of GraphQL we do not see the actual value (i.e. the parent argument in the ref impl) 
     when a resolver returns. 
     The reason is that its shape depends on the internal implementation used by resolvers.

     A resolver says only that a value as been computed and stored in a opaque state. 
     The type returned by a resolver is NOT the type of the stored value, which can be completely arbitary 
      (e.g. it could be a json object or a hash pointing to a memory location).
     We can think of it as a promise on the type of the current subterm when the execution terminates.

*)

Definition resolver (s: Type) := tm -> (state s ((option ty) + error)).

(**
    a schema returns a resolver for every paths
*)

Definition schema (s: Type) := path -> option (resolver s).

(**
    a getter is a function to transform the internal state into a term
*)
Definition getter(s: Type) := state s (option tm).

Reserved Notation "'<' s ';' get ';' sc ';' p ';' T '>' '|=' t1 '/' st '\\' t2 " (at level 40, get at level 39, t1 at level 39, st at level 39, T at level 39, p at level 39, sc at level 39, s at level 39).

(**
    the evaluation of a term (aka query) is given in terms of a big-step operational semantics
*)
Inductive eval(s: Type): (schema s) -> (getter s) -> path -> ty -> tm -> s -> tm -> Prop :=
  | E_Field: forall sc get p t1 t2 T2 t2' m T r st st',
      value(t1) ->
      sc(m::p) = Some r ->
      (r t1 st) = (inl (Some T2), st') ->
      < s ; sc ; get ; ( m::p ) ; T2 > |= t2 / st' \\ t2' ->
      < s ; sc ; get ; p ; T > |= tfield m t1 t2 / st \\ tfieldr m t1 t2'
  | E_Hole: forall get sc p T t st,
      get st = (Some t, st) ->
      value t -> (* we might ask to be a scalar *)
      < s ; sc ; get ; p ; T > |= thole / st \\ t
  | E_Par: forall get sc p T t1 t2 t1' t2' st,
      < s ; sc ; get ; p ; T > |= t1 / st \\ t1' ->
      < s ; sc ; get ; p ; T > |= t2 / st \\ t2' ->
      < s ; sc ; get ; p ; T > |= tpar t1 t2 / st \\ tpar t1' t2'
where "'<' s ; sc ; get ; p ; T '>' '|=' t1 '/' st '\\' t2" := (eval s sc get p T t1 st t2).

