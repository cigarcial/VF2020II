(*
Verificación Formal - 2020-II
Archivo de definiciones - Lógica Clásica 

Definiciones de lógica clásica. 
*)
Definition cotenable (A B : Prop) := ~ (A -> ~ B).
Notation " A ° B " := ( cotenable A B ) (at level 50, no associativity).
