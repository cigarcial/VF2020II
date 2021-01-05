(*
  Verificación Formal - Unam 2020-2
  Ciro Iván García López
  Proyecto 1. Session Type Systems Verification
*)
From PROYI Require Import  Defs_Typing.
From PROYI Require Import  Defs_Process.
From PROYI Require Import  Defs_Proposition.

Check Inference_ind.

Theorem Soundness : 
forall (D F G : list Assignment)(P Q : Prepro),
  ( D ;;; F !- P ::: G ) -> (P --> Q)
  -> ( D ;;; F !- Q ::: G ).
Proof.
  intros.
  induction H.
  + inversion H0.
  + inversion H0.
  + inversion H0.
  + admit.
  + admit.
  + inversion H0.
  + inversion H0.
  + inversion H0.
    - 
  + inversion H0.
  + admit.
  + inversion H0.
  + admit.
  + inversion H0.
  + inversion H0.
Admitted.
