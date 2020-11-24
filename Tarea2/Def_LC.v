(*
Verificación Formal - 2020-II
Archivo de definiciones - Lógica Clásica 

Definiciones de lógica clásica. 

Se define el operador binario cotenable, además de la definición de la notación para el operador
*)
Definition cotenable (A B : Prop) := ~ (A -> ~ B).
Notation " A ° B " := ( cotenable A B ) (at level 50, no associativity).
