(*
  Verificación Formal - Unam 2020-2
  Ciro Iván García López 
  Proyecto 1. Session Type Systems Verification
*)
From Coq Require Import Strings.String.
From PROYI Require Import  Defs_Process.


Lemma Aux2 : 
forall x y z : Name ,
Process_Name x -> Process_Name y -> Process_Name z -> ((Subst_name x y z = y) \/ (Subst_name x y z = z)).
Proof.
  intros.
  inversion H. inversion H0. inversion H1.
  specialize (string_dec x2 x0).
  intro.
  inversion H5.
  (* buscar una manera más bonita de probar esto, no es un resultado 'difícil'  *)
  + assert ( HB : String.eqb x2 x0 = true).
    - remember ( eqb_spec x2 x0).
      inversion r; tauto. 
    - simpl. rewrite -> HB.
      auto.
  + assert ( HB : String.eqb x2 x0 = false).
    - remember ( eqb_spec x2 x0).
      inversion r; tauto.
    - simpl. rewrite -> HB. auto.
Qed.

Lemma Aux1 : 
forall ( x y : Name ) (P : Prepro), 
Process P -> Process_Name x -> Process_Name y -> Process ( { y \ x } P ).
Proof.
  intros.
  induction P.
  + auto.
  + inversion H.
    assert (HA : ((Subst_name x y x0 = y) \/ (Subst_name x y x0 = x0)) ). apply Aux2; auto.
    assert (HB : ((Subst_name x y y0 = y) \/ (Subst_name x y y0 = y0)) ). apply Aux2; auto.
    simpl.
    constructor.
    - destruct HA;
       destruct HB;
         try rewrite -> H6; 
         inversion H1; inversion H4;
         constructor.
    - destruct HA;
       destruct HB;
         rewrite -> H7;
         inversion H1; inversion H5;
         constructor.
  + simpl.
    inversion H.
    constructor; auto.
  + inversion H.
    assert (HA : ((Subst_name x y x0 = y) \/ (Subst_name x y x0 = x0)) ). apply Aux2; auto.
    assert (HB : ((Subst_name x y y0 = y) \/ (Subst_name x y y0 = y0)) ). apply Aux2; auto.
    simpl.
    constructor.
    - destruct HA;
       destruct HB;
         try rewrite -> H7;
         inversion H1; inversion H4;
         constructor.
    - destruct HA;
       destruct HB;
         rewrite -> H8;
         inversion H1; inversion H6;
         constructor.
  + inversion H.
    assert (HA : ((Subst_name x y x0 = y) \/ (Subst_name x y x0 = x0)) ). apply Aux2; auto.
    simpl.
    constructor. 
    destruct HA;
      try rewrite -> H4;
      inversion H1; inversion H3;
      constructor.
  + inversion H.
    assert (HA : ((Subst_name x y x0 = y) \/ (Subst_name x y x0 = x0)) ). apply Aux2; auto.
    simpl. 
    constructor.
    - destruct HA;
        try rewrite -> H6;
        inversion H1; inversion H4;
        constructor.
    - auto.
  + admit.
  + admit.
  + admit.
Admitted.




Theorem ProcessReduction_WD : 
forall P Q : Prepro, 
(P --> Q) -> Process(P)  -> Process(Q).
Proof.
  intros. 
  induction H.
  + constructor.
    - assumption.
    - unfold Body in H1.
      destruct H2 as [L HL].
      specialize (H1 y L).
      auto.
  + constructor.
    - constructor.
      * assumption.
      * unfold Body in H1.
        destruct H2 as [L HL].
        specialize (H1 y L).
        auto.
    - inversion H0. auto.
  + inversion H1.
    assumption.
  + inversion H0.
    inversion H4.
    apply Aux1; auto.
  + inversion H0.
    constructor; assumption.
Qed.