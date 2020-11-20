(*
Verificación Formal - 2020-II
Archivo de proposiciones - Lógica Clásica 

Resultados de lógica clásica. 
*)
 
From TAREA2 Require Import Props_LC.
Parameter a : Type.

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

Lemma Example1 : 
forall A B C D : Prop,
( (A -> B) /\ (~(A \/ C) -> D) /\ (A \/ B -> C) ) -> 
(~ D -> C ).
Proof.
  intros.
  destruct H as [H1 [H2 H3]].
  admit.
Admitted.


Lemma Example2 : 
forall A B C D : Prop,
( A \/ B ) -> 
(~D -> C) /\ (~ B -> ~A) -> (C -> ~B) -> D.
Proof.
  intros.
  destruct H0.
  destruct H.
  - rewrite <- (Doble_Negac C) in H0.
    rewrite <- (Doble_Negac C) in H1. 
    rewrite <- Contrapositiva in *.
    auto.
  - rewrite <- (Doble_Negac C) in H0.
    rewrite <- (Doble_Negac C) in H1.
    rewrite <- Contrapositiva in *.
    auto. 
Qed.

Lemma Example3 : 
forall P B R : Type -> Prop,
( forall x : Type, (P x) -> ~(B x) ) -> 
( (R a) -> ( forall x : Type, (R x) -> (B x)) -> ~ (P a) ).
Proof.
  intros.
  specialize (H a).
  specialize (H1 a).
  rewrite <- (Doble_Negac (P a)) in H.
  rewrite <- (Contrapositiva (B a) (~ P a)) in H.
  auto.
Qed.

Lemma Example5 : 
forall P B : Type -> Prop,
( (forall x : Type, (P x)) /\ exists y :Type, (B y) ) -> 
( exists x : Type, (P x) /\ (B x) ).
Proof.
  intros.
  destruct H as [HP HB].
  destruct HB as [y HB].
  specialize (HP y).
  exists y.
  split; assumption.
Qed.

Lemma Example4 : 
∀x(P x ∨ Bx → ¬Rx), ∀x(Sx → Rx) ->
(forall x :Type, (P x) -> ~(S x) \/ (T x) )





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

∀x(P x ∨ Bx → ¬Rx), ∀x(Sx → Rx) ` ∀x(P x → ¬Sx ∨ T x)

 *)






Lemma Example6 : 
forall (P : Type -> Prop)(R : Type -> Type -> Prop),
( forall x : Type, exists y : Type, (P x) -> (R x y) ) ->
(forall x : Type, (P x) -> exists y : Type, (R x y ) ). 
Proof.
  intros.
  specialize (H x).
  destruct H.
  exists x0.
  apply H.
  assumption.
Qed.



Lemma Example8 :
forall P : Type -> Type -> Prop,
( exists x : Type, forall y :Type, P x y  ) -> 
( forall y : Type, exists x : Type, P x y ). 
Proof.
  intros.
  destruct H.
  specialize (H y).
  exists x.
  assumption.
Qed.

