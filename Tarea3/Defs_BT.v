(*
Verificación Formal - 2020-II
Archivo de definiciones - Arreglos flexibles usando árboles de Braun

Importación de los archivos de definiciones y propiedades de BN
*)
From TAREA3 Require Import Defs_BN.
From TAREA3 Require Import Props_BN.


(*
------------------------------------####------------------------------------
------------------------------------####------------------------------------
                Inicio del Fragmento de código visto en clase.
------------------------------------####------------------------------------
------------------------------------####------------------------------------
*)


(*
Definition of binary trees and some of their properties
*)
Parameter (A:Type)
          (eq_dec_A: forall (x y:A),{x=y}+{x<>y})
          (undefA : A).


(*
Binary trees defined here
*)
Inductive BTree : Type :=
  | E : BTree   
  | N : A -> BTree  -> BTree  -> BTree.


Check BTree_ind.


(*
Árbol indefinido
*)
Parameter (undefBTree : BTree).


(*
size on binary trees defined next
*)
Fixpoint bsize (t:BTree): BN :=
match t with
  | E => Z
  | N x s t =>  sucBN ((bsize s) ⊞ (bsize t))
end.

Check bsize.


(*
Balance condition on Braun trees
*)
Inductive bbal : BTree -> Prop:=
  | bbalE : bbal E 
  | bbalN : forall (a: A) (s t: BTree),
            bbal s -> bbal t -> (bsize t) ≤BN (bsize s) ->
            (bsize s) ≤BN (sucBN (bsize t)) ->
            bbal (N a s t).


Check bbal_ind.


Parameter (allBal: forall (t:BTree), bbal t).


(*
Consulta del elemento b-simo
*)
Fixpoint lookup_bn (t:BTree) (b: BN) : A :=
match t,b with
  | E, b => undefA
  | N x s t,Z => x 
  | N x s t, U a => lookup_bn s a   (* U a = 2a+1 *)
  | N x s t, D a => lookup_bn t a   (* D a = 2a + 2 *) 
end.


(*
Actualización del elemento b-simo
*)
Fixpoint update (t:BTree) (b: BN) (x : A) : BTree :=
match t,b with
  | E, b => undefBTree
  | N y s t, Z =>  N x s t
  | N y s t, U a => N y (update s a x) t
  | N y s t, D a => N y s (update t a x)
end.


(*
Inserción de un elento al inicio del arreglo
*)
Fixpoint le (x:A) (t:BTree) : BTree :=
match t with
  | E => N x E E
  | N y s t => N x (le y t) s
end.


(*
Inserción de un elento al final del arreglo
*)
Fixpoint he (x:A) (t:BTree) : BTree  :=
match t with
  | E => N x E E
  | N y l r => match bsize t with
                | Z => undefBTree 
                | U b => N y (he x l) r
                | D b => N y l (he x r)
              end
end.


(*
------------------------------------####------------------------------------
------------------------------------####------------------------------------
                   Fin del fragmento de código visto en clase.
------------------------------------####------------------------------------
------------------------------------####------------------------------------
*)


(*
------------------------------------####------------------------------------
------------------------------------####------------------------------------
                Inicio del fragmento de código implementado.
------------------------------------####------------------------------------
------------------------------------####------------------------------------
*)


(*
Eliminación del primer elemento en el arreglo
*)
Fixpoint lr (t:BTree) : BTree  :=
match t with
  | E => undefBTree
  | N y l r => match l with
                | E => E
                | N x _ _ => N x r (lr l)
               end
end.


(*
Eliminación del últiom elemento en el arreglo
*)
Fixpoint hr (t:BTree) : BTree  :=
match t with
  | E => undefBTree
  | N y E _ => E
  | N y l r => match bsize t with
                | U b => N y l (hr r)
                | D b => N y (hr l) r
                | Z => undefBTree 
               end
end.

