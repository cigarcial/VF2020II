(* 
Verificación Formal - 2020-II
Archivo de proposiciones - Lógica Clásica 

Resultados de lógica clásica. 

Se importa el módulo de lógica clásica de Coq y el archivo de definiciones para lógica clásica
*)
Require Import Coq.Logic.Classical.
From TAREA2 Require Import Defs_LC.
(*
Constantes que aparecen en las afirmaciones.
*)
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
Prueba clásica de la transitividad en la implicación
*)
Lemma Trans_Implicacion : 
forall A B C : Prop, 
((A->B) /\ (B-> C)) -> (A -> C).
Proof.
  intros.
  destruct H.
  apply H1.
  apply H.
  assumption.
Qed.

(*
Prueba clásica de la equivalencia entre la implicación y la disyunción
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
Prueba clásica de la contrapositiva
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
Prueba clásica de la ley de De Morgan para la conjunción
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
La operación cotenable conmuta
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
La operación cotenable es asociativa
*)
Lemma Cotenable_Asoc : 
forall A B C : Prop, 
(A ° B) ° C <-> A ° (B ° C).
Proof.
  unfold cotenable.
  intros.
  do 4 rewrite -> Disyuncion_implicacion.
  do 2 rewrite -> Doble_Negac.
  tauto.
Qed.

(*
La operación cotenable distribuye respecto a la disyunción
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
La operación cotenable se fusiona con la implicación
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
Comportamiento de la operación cotenable, la negación y la implicación
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
Prueba clásica del argumento 1
*)
Lemma Argumento1 : 
forall A B C : Type -> Prop, 
( ( (exists x : Type, (A x) /\ (B x)) -> forall x : Type, (B x) -> (C x) ) /\ (B a) /\ ~(C a) ) -> 
~(forall x : Type, A x ). 
Proof.
  intros.
  destruct H as [H [HB HC]].
  apply ex_not_not_all.
  pose proof (classic (A a)) as HA.
  destruct HA.
  - assert( HAB : forall x : Type, B x -> C x ).
    + apply H. 
      exists a.
      split; assumption.
    + assert (HCN := HAB a HB).
      contradiction.
  - exists a. 
    assumption.
Qed.

(*
Prueba clásica del argumento 2
*)
Lemma Argumento2 : 
forall (B G : Type -> Type -> Prop) ( C W : Type -> Prop),
(exists x : Type , ~ (B x m ) /\ (forall y : Type, (C y) -> ~ (G x y )) ) -> 
( forall z : Type, ~ (forall y : Type, (W y) -> ( G z y )) -> (B z m) ) -> 
(forall x : Type, (C x) -> ~ (W x) ).
Proof.
  intros.
  destruct H as [x0 [HB HY]].
  assert (HG := HY x H1).
  assert (H0 := H0 x0).
  rewrite <- (Doble_Negac (B x0 m)) in H0.
  rewrite <- Contrapositiva in H0.
  assert (H2 := H0 HB x).
  rewrite -> Contrapositiva in H2.
  apply H2. 
  assumption.  
Qed.
 
(*
Negación de un cuentificador universal y una conjunción
*)
Lemma DeMorgan_Cuantificadores : 
forall P Q : Type -> Prop, 
~ (forall x : Type, ~ P x \/ ~ Q x) <-> (exists x : Type, P x /\ Q x).
Proof.
  split.
  - intro. 
    apply not_all_ex_not in H.
    destruct H.
    rewrite <- DeMorgan_and_or in H.
    exists x.
    auto.
  - intro. 
    destruct H as [t HPQ].
    apply ex_not_not_all.
    exists t.
    rewrite <- DeMorgan_and_or.
    assumption.
Qed. 

(*
Prueba clásica del argumento 3
*)
Lemma Argumento3 : 
forall (P H C L R : Type -> Prop)(A B : Type -> Type -> Prop),
( ~(forall x : Type, ~(P x) \/ ~(H x) ) -> (forall x : Type, (C x) /\ (forall y : Type, (L y) -> (A x y) ) ) ) -> 
( (exists x : Type, (H x) /\ forall y : Type, (L y) -> (A x y)) -> (forall x : Type, (R x) /\ forall y : Type, B x y) ) -> 
( ~(forall x y : Type, B x y ) -> forall x : Type, ~(P x) \/ ~(H x) ). 
Proof.
  intros P H C L R A B H0 H1 H2.
  pose proof (classic (forall x : Type, ~ P x \/ ~ H x)) as HG.
  destruct HG.
  - assumption.
  - assert (H0 := H0 H3).
    rewrite -> DeMorgan_Cuantificadores in H3.
    destruct H3 as [t [HP HH]].
    assert (H0 := H0 t).
    destruct H0 as [HC HLA].
    assert ( HHLA : (exists x : Type, H x /\ (forall y : Type, L y -> A x y)) ).
    + exists t. split; assumption.
    + assert (H1 := H1 HHLA).
      apply not_all_ex_not in H2.
      destruct H2 as [z NHB].
      apply not_all_ex_not in NHB.
      destruct NHB as [w NHB].
      assert (H1 := H1 z).  
      destruct H1 as [HZ HB].
      assert (HB := HB w).
      contradiction.
Qed.



