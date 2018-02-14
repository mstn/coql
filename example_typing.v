Load coql.


Example has_type_1 : 
  |-  tfield "user" (tfield "id" tempty (tnat 1))
             (tfield "name" tempty (tfield "addr" tempty (tfield "str" tempty thole) )) 
        \in TField "user" (TField "id" TBot TNat) 
              (TField "name" TBot (TField "addr" TBot (TField "str" TBot TTop) )). 
Proof. 
  apply T_Field.
  apply T_Field.
 apply T_Empty.
 apply T_Nat.
 apply T_Field.
 apply T_Empty.
 apply T_Field.
 apply T_Empty.
 apply T_Field.
 apply T_Empty.
 apply T_Hole.
Qed.
