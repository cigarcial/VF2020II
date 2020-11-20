(*
Verificación Formal - 2020-II
Archivo de proposiciones - Lógica Clásica 

Resultados de lógica clásica. 
*)

Require Import Coq.Logic.Classical.
From TAREA2 Require Import Def_LC.
Parameter a : Type.
Parameter m : Type.


(*
Prueba clásica de la equivalencia de la doble negación
*)
Lemma Doble_Negac : 
forall A : Prop, 
~ ~ A <-> A. 
Proof.
  split.
  - apply NNPP.
  - apply (or_to_imply A (~ ~ A)).
    apply (classic (~A)).
Qed.

(*
*)
Lemma Disyuncion_implicacion : 
forall A B : Prop,
(A -> B) <-> (~A \/ B).
Proof.
  split.
  - apply imply_to_or.
  - apply or_to_imply.
Qed.

(*
*)
Lemma Contrapositiva : 
forall A B : Prop,
(A -> B) <-> (~B -> ~A).
Proof.
  intros.
  do 2 rewrite -> Disyuncion_implicacion.
  rewrite -> Doble_Negac.
  tauto.
Qed.

(*
*)
Lemma DeMorgan_and_or : 
forall A B : Prop, 
(A /\ B) <-> ~ (~A \/ ~B).
Proof. 
  split.
  - intro.
    apply and_not_or.
    do 2 rewrite -> Doble_Negac.
    assumption.
  - intro.
    apply not_or_and in H.
    do 2 rewrite -> Doble_Negac in H.
    assumption.
Qed.

(*
*)
Lemma Cotenable_Conmt : 
forall A B : Prop,
A ° B <-> B ° A.
Proof.
  unfold cotenable.
  intros.
  do 2 rewrite -> Disyuncion_implicacion.
  rewrite <- (or_comm (~A) (~B)).
  tauto.
Qed.

(*
*)
Lemma Cotenable_Asoc : 
forall A B C : Prop, 
(A ° B) ° C <-> A ° (B ° C).
Proof.
  unfold cotenable.
  intros.
  do 4 rewrite -> Disyuncion_implicacion.
  do 2 rewrite -> Doble_Negac.
  rewrite <- (or_assoc (~A) (~B)).
  tauto.
Qed.

(*
*)
Lemma Cotenable_Dist_or : 
forall A B C : Prop,
( (A ° B) \/ (A ° C) ) <-> ( A ° (B \/ C) ).
Proof.
  unfold cotenable.
  intros.
  do 3 rewrite -> Disyuncion_implicacion.
  do 3 rewrite <- DeMorgan_and_or.
  tauto.
Qed.

(*
*)
Lemma Cotenable_Fusion : 
forall A B C : Prop, 
(A -> B -> C) <-> ((A ° B) -> C).
Proof.
  unfold cotenable.
  intros.
  do 4 rewrite -> Disyuncion_implicacion.
  rewrite -> Doble_Negac.
  tauto.
Qed.

(*
*)
Lemma Cotenable_Implicacion : 
forall A B : Prop, 
(A -> B) <-> ( ~ ( A ° (~B) ) ).
Proof.
  unfold cotenable.
  intros.
  do 2 rewrite -> Doble_Negac.
  tauto.
Qed.

(*
*)
Lemma Argumento1 : 
forall A B C : Type -> Prop, 
( ( (exists x : Type, (A x) /\ (B x)) -> forall x : Type, (B x) -> (C x) ) /\ (B a) /\ ~(C a) ) -> 
~(forall x : Type, A x ). 
Proof.
  intros.
  destruct H as [H [HB HC]].
  apply ex_not_not_all.
  remember ( classic (A a) ) as HA.
  destruct HA.
  - assert( HAB : forall x : Type, B x -> C x ).
    + apply H. 
      exists a.
      auto.
    + specialize (HAB a).
      apply HAB in HB.
      contradiction.
  - exists a. 
    assumption.
Qed.

(*
*)
Lemma Argumento2 : 
forall (B G : Type -> Type -> Prop) ( C W : Type -> Prop),
(exists x : Type , ~ (B x m ) /\ (forall y : Type, (C y) -> ~ (G x y )) ) -> 
( forall z : Type, ~ (forall y : Type, (W y) -> ( G z y )) -> (B z m) ) -> 
(forall x : Type, (C x) -> ~ (W x) ).
Proof.
  intros.
  destruct H as [x0 [HB HY]].
  specialize (HY x).
  apply HY in H1.
  specialize (H0 x0).
  rewrite <- (Doble_Negac (B x0 m)) in H0.
  rewrite <- Contrapositiva in H0.
  specialize (H0 HB).
  specialize (H0 x).
  rewrite -> Contrapositiva in H0.
  apply H0. assumption.  
Qed.

(*
*)
Lemma Argumento3 : 

(¬∀x(¬P x ∨ ¬Hx) → ∀x(Cx ∧ ∀y(Ly → Axy)) ) -> 
( ∃x(Hx ∧ ∀y(Ly → Axy)) → ∀x(Rx ∧ ∀yBxy) ) -> 
( ¬∀x∀yBxy → ∀x(¬P x ∨ ¬Hx) ). 
Proof. 


Qed.



