(*
  Verificación Formal - Unam 2020-2
  Ciro Iván García López
  Proyecto 1. Session Type Systems Verification
*)
From Coq Require Import Lists.List.
Import ListNotations.
From PROYI Require Import  Defs_Proposition.
From PROYI Require Import  Defs_Process.


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
    Inference ( D ;;; ( cons (x:A) nil ) !- ([x←→y]) ::: [ (y:A) ]  )
    
  | idl : forall (D : list Assignment)(x y : Name)(A : Proposition),
    Collec D -> Process_Name x -> Process_Name y -> 
    Inference ( D ;;; ( (cons (x:A) nil) ++ (cons (x:(A^⊥)) nil) )  !-  ([x←→y]) ::: []  ).



