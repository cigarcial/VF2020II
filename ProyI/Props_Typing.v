(*
  Verificación Formal - Unam 2020-2
  Ciro Iván García López
  Proyecto 1. Session Type Systems Verification
*)
From PROYI Require Import  Defs_Typing.
From PROYI Require Import  Defs_Process.
From PROYI Require Import  Defs_Proposition.


Theorem Soundness : 
forall (D F G : list Assignment)(P Q : Prepro),
  Seqn ( D ;;; F !- P ::: G ) -> (P --> Q) -> Inference ( D ;;; F !- P ::: G ) 
  -> Inference ( D ;;; F !- Q ::: G ).
Proof.
  intros.
  induction H1.
  + inversion H.
  
  
Qed.
    