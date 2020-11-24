(*
Verificación Formal - 2020-II
Archivo de proposiciones - Lógica Minimal 

Resultados de lógica minimal. 
*)

(*
Se puede reducir la triple negación a una negación
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
Comportamiento de la doble negación vs conjunción.
*)
Lemma Negacion_Conjuncion_LM : 
forall A B : Prop, 
 ~ ~ (A /\ B ) -> ~ ~ A /\ ~ ~ B.
Proof.
  unfold not.
  split;
    intro;
    apply H; 
    intro; 
    destruct H1; 
    contradiction.
Qed.

(*
Doble negación vs cuantificador universal, 
se puede introducir una doble negación en un cuantificador universal
*)
Lemma DobleNeg_CUniversal_LM : 
forall A : Type -> Prop, 
( ~ ~ forall x : Type , (A x) ) -> forall x : Type, ~ ~ (A x).  
Proof.
  unfold not.
  intros.
  apply H.
  intro.
  assert (H2 := H1 x).
  contradiction.
Qed.
