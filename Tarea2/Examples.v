(* 
Verificación Formal - 2020-II
Archivo de proposiciones - Lógica Clásica 

Resultados de lógica clásica. 

Se importa el módulo de lógica clásica de Coq y el archivo de definiciones para lógica clásica
*)
Require Import Coq.Logic.Classical.
From TAREA2 Require Import Props_LC.
(*
Constantes que aparecen en las afirmaciones.
*)
Parameter a : Type.

(*
Prueba de que es posible separar un para todo cuando hay un cuantificador universal
La prueba es minimal, pues no aparecen negaciones. 
*)
Lemma Separacion_and_forall : 
forall A B : Type -> Prop,
(forall x : Type, (A x) /\ (exists y : Type, (B y)) ) <-> 
(forall x : Type, (A x)) /\ (exists y : Type, B y).
Proof.
  split.
  - intros.
    split;
      try intro; assert (H := H x) || assert (H := H a);
      destruct H as [HA HB];
      assumption.
  - intros.
    destruct H as [HA HB].
    split.
    + assert (HA := HA x). assumption.
    + assumption.
Qed.


(*
Prueba del ejemplo 1, 
la prueba es clásica, usa tercio excluido, contrapositiva y doble negación
*)
Lemma Example1 : 
forall A B C D : Prop,
( (A -> B) /\ (~(A \/ C) -> D) /\ ( (A \/ B) -> C) ) -> 
(~ D -> C ).
Proof.
  intros.
  destruct H as [H1 [H2 H3]].
  pose proof (classic C) as HC.
  destruct HC.
  - assumption.
  - pose proof (classic A) as HA.  
    destruct HA.
    + apply H3.
      left.
      assumption.
    + rewrite -> Contrapositiva in H2.
      apply H2 in H0.
      rewrite -> Doble_Negac in H0.
      destruct H0; contradiction.
Qed.

(*
Prueba del ejemplo 2, 
la prueba es clásica, usa doble negacion y contrapositiva
*)
Lemma Example2 : 
forall A B C D : Prop,
( A \/ B ) -> 
(~D -> C) /\ (~ B -> ~A) -> (C -> ~B) -> D.
Proof.
  intros.
  destruct H0.
  destruct H;
    rewrite <- (Doble_Negac C) in H0;
    rewrite <- (Doble_Negac C) in H1;
    rewrite <- Contrapositiva in *;
    auto.
Qed.

(*
Prueba del ejemplo 3, 
la prueba es clásica, usa doble negacion
*)
Lemma Example3 : 
forall P B R : Type -> Prop,
( forall x : Type, (P x) -> ~(B x) ) -> 
( (R a) -> ( forall x : Type, (R x) -> (B x)) -> ~ (P a) ).
Proof.
  intros.
  assert (H := H a).
  assert (H1 := H1 a).
  rewrite <- (Doble_Negac (P a)) in H.
  rewrite <- (Contrapositiva (B a) (~ P a)) in H.
  auto.
Qed.

(*
Prueba del ejemplo 4, 
la prueba es clásica, usa la contrapositiva
*)
Lemma Example4 : 
forall P B R S T : Type -> Prop,
( forall x : Type, ((P x) \/ (B x)) -> ~(R x) ) -> 
( forall x : Type, (S x) -> (R x) ) ->
(forall x :Type, (P x) -> ~(S x) \/ (T x) ).
Proof.
  intros.
  assert (H := H x).
  assert (H0 := H0 x).
  assert (H2 : P x \/ B x). left. assumption.
  apply H in H2.
  rewrite -> Contrapositiva in H0.
  apply H0 in H2.
  left. assumption.
Qed.

(*
Prueba del ejemplo 5, 
la prueba es minimal, ya que no hay negaciones y la prueba de Separacion_and_forall es minimal.
*)
Lemma Example5 : 
forall P B : Type -> Prop,
( forall x : Type, ((P x) /\ exists y :Type, (B y)) ) -> 
( exists x : Type, (P x) /\ (B x) ).
Proof.
  intros.
  rewrite -> Separacion_and_forall in H.
  destruct H as [HP HB].
  destruct HB as [y HB].
  assert (HP := HP y).
  exists y.
  split; assumption.
Qed.

(*
Prueba del ejemplo 6, 
la prueba es minimal, ya que no hay negaciones
*)
Lemma Example6 : 
forall (P : Type -> Prop)(R : Type -> Type -> Prop),
( forall x : Type, exists y : Type, (P x) -> (R x y) ) ->
(forall x : Type, (P x) -> exists y : Type, (R x y ) ).
Proof.
  intros.
  assert (H := H x).
  destruct H.
  exists x0.
  apply H.
  assumption.
Qed.

(*
Prueba del ejemplo 7, 
la prueba es minimal, ya que solo se usa unfold not.
*)
Lemma Example7 :
forall P B : Type -> Prop,
( forall x : Type,  (P x) ->  ~(B x) ) -> 
~ ( exists x : Type, (P x) /\ (B x) ).
Proof.
  unfold not.
  intros.
  destruct H0 as [x [HP HB]].
  apply (H x);
  assumption.
Qed.

(*
Prueba del ejemplo 8, 
la prueba es minimal, ya que no hay negaciones
*)
Lemma Example8 :
forall P : Type -> Type -> Prop,
( exists x : Type, forall y :Type, P x y  ) -> 
( forall y : Type, exists x : Type, P x y ). 
Proof.
  intros.
  destruct H.
  assert (H := H y).
  exists x.
  assumption.
Qed.

