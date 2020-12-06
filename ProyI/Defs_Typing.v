(*
  Verificación Formal - Unam 2020-2
  Ciro Iván García López
  Proyecto 1. Session Type Systems Verification
*)

(*
Archivo de definiciones para el sistema de tipos
*)

From Coq Require Import Lists.List.
From PROYI Require Import  Defs_ProyI.


Inductive Assignment : Type := assig ( x : Name )( A : Proposition ) : Assignment.

Notation " x : A " := (assig x A )(at level 60).

Inductive Assig : Assignment -> Prop :=
  is_assig :  forall (x : Name)(A:Proposition), Process_Name x -> Assig ( x : A).

Inductive Sequent : Type := seqnt ( D F G : list Assignment ) ( P : Prepro ) : Sequent.

Notation " D ';;;'  F '!-' P ':::' G " :=  (seqnt D F G P)(at level 60). 

Inductive Collec : list Assignment -> Prop := is_collect :forall L : list Assignment,
  (forall H : Assignment, (In H L) -> Assig H ) -> Collec L.

Inductive Seqn : Sequent -> Prop :=  is_seqn : forall (D F G : list Assignment)(P : Prepro),
  Process P -> Collec D -> Collec F -> Collec G -> Seqn ( D ;;; F !- P ::: G ).


Inductive Inference : Sequent -> Prop := 
  | idr : forall (D : list Assignment) (x y : Name) (A : Proposition), 
    Collec D -> Process_Name x -> Process_Name y -> 
    Inference ( D ;;; (x:A) !- ([x←→y]) ::: ( y:A ) ).
  
     
  

