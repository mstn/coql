Load coql.

(**
    We represent the internal state as a stack.

    Perhaps a stack is not the best data structure 
    since at every step of the evaluation of a query we need at most the top element of the stack.

    However, this is an example to show how the underlying state can be represented in arbitrary ways.

    For example, it could be an SQL table or a JSON object.
*)

Record UserRecord := {
  _id: nat;
  name: string;
  surname: string;
  age: nat;
}.

Inductive data: Type :=
  | mkUser: UserRecord -> data
  | mkString: string -> data
  | mkNat: nat -> data.

Definition Stack := list data.

(**
    This function represents a simple database query
*)

Definition findUserById := fun(id: nat) =>
  match id with
    | 1 => Some {| _id := 1; name := "Johnny"; surname := "Hendrix"; age := 27 |}
    | _ => None
  end.

Definition User: ty := 
    TPar
      (TField "name" TBot TString)
      (TPar
        (TField "surname" TBot TString)
        (TField "age" TBot TNat)).

Definition update: UserRecord -> (state Stack unit) := fun(user: UserRecord)(st: Stack) => (tt, mkUser(user)::st).

Definition findUserByIdResolver: resolver(Stack) := fun(t: tm)(st: Stack) => 
  match t with 
    | tnat userId => 
      match findUserById(userId) with 
        | Some user => 
          let (_, st') := update user st in
            (inl (Some User), st')
        | None => (inl None, st)
      end
    | _ => (inr err, st)
  end.

Definition findUserNameResolver: resolver(Stack) := fun(t: tm)(st: Stack) =>
  match st with 
    | x::st' => 
      match x with 
        | mkUser(x) => ( inl (Some TString),  mkString(name x)::st)
        | _ => (inr err, st)
      end
    | nil => (inr err, st)
  end.

Definition findUserAgeResolver: resolver(Stack) := fun(t: tm)(st: Stack) =>
  match st with 
    | x::st' => 
      match x with 
        | mkUser(x) => ( inl (Some TNat),  mkNat(age x)::st)
        | _ => (inr err, st)
      end
    | nil => (inr err, st)
  end.

Definition Schema: schema(Stack) := fun( p: list string ) =>
  match p with
    | "findUserById" :: nil => Some(findUserByIdResolver)
    | "name" :: "findUserById" :: nil => Some( findUserNameResolver )
    | "age" :: "findUserById" :: nil => Some( findUserAgeResolver )
    | _ => None
  end.


Definition Root: ty := TField "findUserById" TNat User.

Definition get: getter(Stack) := fun(st: Stack) =>
  match st with 
    | x::st' => 
      match x with
        | mkString(s) => (Some (tstring s), st)
        | mkNat(n) => (Some (tnat n), st)
        | _ => (None, st)
      end
    | nil => (None, st)
  end.

Example res1: 
  < Stack ; Schema ; get ; [] ; Root > |= 
    tfield "findUserById" (tnat 1) 
      (tpar
        (tfield "name" tempty thole)
        (tfield "age" tempty thole) ) / []
      \\ tfieldr "findUserById" (tnat 1)
          (tpar
            (tfieldr "name" tempty (tstring "Johnny"))
            (tfieldr "age" tempty (tnat 27))
          ).
Proof. 
  apply E_Field with User findUserByIdResolver [ mkUser {| _id := 1; name := "Johnny"; surname := "Hendrix"; age := 27 |}].
  - trivial.
  - simpl. reflexivity.
  - simpl. reflexivity.
  - apply E_Par.
      apply E_Field with TString findUserNameResolver [ mkString "Johnny" ; mkUser {| _id := 1; name := "Johnny"; surname := "Hendrix"; age := 27 |}].
      trivial.
      simpl. reflexivity.
      trivial.
      apply E_Hole. simpl. reflexivity.
      trivial.
      apply E_Field with TNat findUserAgeResolver [ mkNat 27 ; mkUser {| _id := 1; name := "Johnny"; surname := "Hendrix"; age := 27 |}].
      trivial.
      simpl. reflexivity.
      simpl. reflexivity.
      apply E_Hole. simpl. reflexivity. trivial.
Qed. 