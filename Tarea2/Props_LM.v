(*
Verificación Formal - 2020-II
Archivo de proposiciones - Lógica Minimal 

Resultados de lógica minimal. 
*)

(*
*)
Lemma Triple_Negacion_LM : 
forall A : Prop, 
~ ~ ~ A <-> ~ A. 
Proof.
  unfold not.
  split.
  - intros.
    apply H.
    intro.
    contradiction.
  - intros.
    contradiction.
Qed.

(*
*)
Lemma Negacion_Conjuncion_LM : 
forall A B : Prop, 
 ~ ~ (A /\ B ) -> ~ ~ A /\ ~ ~ B.
Proof.
  unfold not.
  split.
  - intro. 
    apply H. 
    intro. 
    destruct H1. 
    contradiction.
  - intro. 
    apply H. 
    intro. 
    destruct H1. 
    contradiction.
Qed.

(*
*)
Lemma DobleNeg_CUniversal_LM : 
forall A : Type -> Prop, 
( ~ ~ forall x : Type , (A x) ) -> forall x : Type, ~ ~ (A x).  
Proof.
  unfold not.
  intros.
  apply H.
  intro.
  specialize (H1 x).
  contradiction.
Qed.



