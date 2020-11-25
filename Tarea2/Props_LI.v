(*
Verificación Formal - 2020-II
Archivo de proposiciones - Lógica Intuicionista

Resultados de lógica intuicionista.
*)

(*
Doble negación vs implicación
*)
Lemma DobleNegacion_Implicacion_LI : 
forall A B : Prop, 
( ~ ~( A -> B) )  <-> ( (~ ~ A) -> (~ ~ B) ). 
Proof.
  unfold not.
  split.
  - intros.
    apply H0.
    intro.
    apply H.
    intro.
    apply H3 in H2.
    contradiction.
  - intros.
    (* Esta parte de la prueba es la sugerencia *)
    apply H;
      intro;
      apply H0;
      intro;
      (*Se generan dos metas, en la primera hay una contradicción
      y en la segunda es una hipotesis*)
      contradiction || assumption.
Qed.



