(*
  Verificación Formal - Unam 2020-2
  Ciro Iván García López 
  Proyecto 1. Session Type Systems Verification
*)
From Coq Require Import Strings.String.
From Coq Require Import Lists.List.
From Coq Require Import Arith.EqNat.
From PROYI Require Import  Defs_Process.


(*
Axiomas necesarios para las pruebas, son ideas intuitias pero que han sido difíciles de expresar en Coq. 
El último Axioma corresponde con un error de diseño en la definición de Body.
*)
Axiom Eq_Subs_Open : 
forall (x y z : Name) ( P :Prepro), 
((({y \ x} P )^ z) = ({y \ x} P ^ z)).


Axiom Eq_Subs_Close : 
forall (i : nat) ( z x : Name) ( P : Prepro),
({i ~> z} Close_Rec i x P) = P.


Axiom MalDiseno : 
forall (z : Name)( L : list Name ), 
(~ In z L ) -> Process_Name z.


(*
Siempre que se hace una sustitución sobre nombres solo se pueden obtener dos resultados, se remplaza o queda igual.
*)
Lemma Subst_Name_Output : 
forall x y z : Name ,
Process_Name x -> Process_Name y -> Process_Name z -> ((Subst_name x y z = y) \/ (Subst_name x y z = z)).
Proof.
  intros.
  inversion H. inversion H0. inversion H1.
  (*
    En este fragmento se busca probar que dadas dos cadenas o son iguales o son diferentess; buscar una prueba más elegante no es un resultado 'difícil'  
  *)
  specialize (string_dec x2 x0).
  intro.
  inversion H5.
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


(*
Análogamente, al cerrar un nombre solo hay dos opciones, se remplazar o queda igual.
*)
Lemma Close_Name_Output : 
forall ( i : nat) (x y : Name), 
Process_Name x -> Process_Name y -> ( (Close_Name i x y = y) \/ (Close_Name i x y = BName i) ).
Proof.
  intros.
  inversion H. inversion H0.
  specialize (string_dec x1 x0).
  intros.
  inversion H3.
  + assert ( HB : String.eqb x1 x0 = true).
    - remember ( eqb_spec x1 x0).
      inversion r; tauto. 
    - simpl. rewrite -> HB.
      auto.
  + assert ( HB : String.eqb x1 x0 = false).
    - remember ( eqb_spec x1 x0).
      inversion r; tauto. 
    - simpl. rewrite -> HB.
      auto.
Qed.


(*
La apertura de un nombre libre es el mismo nombre libre.
*)
Lemma Open_PName_Output : 
forall ( i : nat )( x y : Name),
Process_Name y -> (Open_Name i x y = y).
Proof. 
  intros.
  inversion H.
  auto.
Qed.


(*
La operación de apertura abre los nombres adecuadamente.
*)
Lemma Open_BName_Output : 
forall ( i : nat ) ( x : Name), 
Process_Name x -> (Open_Name i x (BName i) = x).
Proof.
  intros.
  simpl.
  assert ( HA : Nat.eqb i i = true). auto.
  remember ( beq_nat_refl i ).
  inversion e; tauto.
  rewrite -> HA.
  auto.
Qed.


(*
Al tener un proceso y someterlo a un proceso de cerradura, lo que se obtiene es un body.
*)
Lemma Close_Is_Body:
forall (x : Name)(P : Prepro),
Process_Name x -> Process P -> ( forall(L : list Name) (z : Name), ~ (In z L) -> Process (Close_Rec 0 x P ^ z) ).
Proof.
  intros.
  induction H0.
  + simpl. constructor.
  + unfold Open. simpl.
    assert (HZ : Process_Name z). apply (MalDiseno z L); auto.
    assert (HA : ((Close_Name 0 x x0 = x0) \/ (Close_Name 0 x x0 = BName 0)) ). apply Close_Name_Output; auto.
    assert (HB : ((Close_Name 0 x y = y) \/ (Close_Name 0 x y = BName 0)) ). apply Close_Name_Output; auto. 
    constructor.
    - destruct HA.
      * rewrite -> H3.
        assert (HC : Open_Name 0 z x0 = x0). apply Open_PName_Output; auto.
        rewrite -> HC. auto.
      * rewrite -> H3.
        assert (HC : Open_Name 0 z (BName 0) = z). apply Open_BName_Output; auto.
        rewrite -> HC. auto.
    - destruct HB.
      * rewrite -> H3.
        assert (HC : Open_Name 0 z y = y). apply Open_PName_Output; auto.
        rewrite -> HC. auto.
      * rewrite -> H3.
        assert (HC : Open_Name 0 z (BName 0) = z). apply Open_BName_Output; auto.
        rewrite -> HC. auto.
  + unfold Open. simpl. constructor; auto.
  + unfold Open. simpl.
    assert (HZ : Process_Name z). apply (MalDiseno z L); auto.
    assert (HA : ((Close_Name 0 x x0 = x0) \/ (Close_Name 0 x x0 = BName 0)) ). apply Close_Name_Output; auto.
    assert (HB : ((Close_Name 0 x y = y) \/ (Close_Name 0 x y = BName 0)) ). apply Close_Name_Output; auto.
    constructor.
    - destruct HA.
      * rewrite -> H4.
        assert (HC : Open_Name 0 z x0 = x0). apply Open_PName_Output; auto.
        rewrite -> HC. auto.
      * rewrite -> H4.
        assert (HC : Open_Name 0 z (BName 0) = z). apply Open_BName_Output; auto.
        rewrite -> HC. auto.
    - destruct HB.
      * rewrite -> H4.
        assert (HC : Open_Name 0 z y = y). apply Open_PName_Output; auto.
        rewrite -> HC. auto.
      * rewrite -> H4.
        assert (HC : Open_Name 0 z (BName 0) = z). apply Open_BName_Output; auto.
        rewrite -> HC. auto.
    - auto.
  + unfold Open. simpl.
    assert (HZ : Process_Name z). apply (MalDiseno z L); auto.
    assert (HA : ((Close_Name 0 x x0 = x0) \/ (Close_Name 0 x x0 = BName 0)) ). apply Close_Name_Output; auto.
    constructor.
    destruct HA.
    - rewrite -> H2.
      assert (HC : Open_Name 0 z x0 = x0). apply Open_PName_Output; auto.
      rewrite -> HC. auto.
    - rewrite -> H2.
      assert (HC : Open_Name 0 z (BName 0) = z). apply Open_BName_Output; auto.
      rewrite -> HC. auto.
  + unfold Open. simpl. 
    assert (HZ : Process_Name z). apply (MalDiseno z L); auto.
    constructor.
    - assert (HA : ((Close_Name 0 x x0 = x0) \/ (Close_Name 0 x x0 = BName 0)) ). apply Close_Name_Output; auto.
      destruct HA.
      * rewrite -> H3.
        assert (HC : Open_Name 0 z x0 = x0). apply Open_PName_Output; auto.
        rewrite -> HC. auto.
      * rewrite -> H3.
        assert (HC : Open_Name 0 z (BName 0) = z). apply Open_BName_Output; auto.
        rewrite -> HC. auto.
    - auto.
  + unfold Open. simpl. 
    rewrite -> Eq_Subs_Close.
    apply (Chan_res P L0).
    auto.
  + unfold Open. simpl.
    assert (HZ : Process_Name z). apply (MalDiseno z L); auto.
    rewrite -> Eq_Subs_Close.
    assert (HA : ((Close_Name 0 x x0 = x0) \/ (Close_Name 0 x x0 = BName 0)) ). apply Close_Name_Output; auto.
    destruct HA.
    - rewrite -> H4.
      assert (HC : Open_Name 0 z x0 = x0). apply Open_PName_Output; auto.
      rewrite -> HC.
      apply (Chan_input x0 P L0); auto.
    - rewrite -> H4.
      assert (HC : Open_Name 0 z (BName 0) = z). apply Open_BName_Output; auto.
      rewrite -> HC.
      apply (Chan_input z P L0); auto.
  + unfold Open. simpl.
    rewrite -> Eq_Subs_Close.
    assert (HZ : Process_Name z). apply (MalDiseno z L); auto.
    assert (HA : ((Close_Name 0 x x0 = x0) \/ (Close_Name 0 x x0 = BName 0)) ). apply Close_Name_Output; auto.
    destruct HA.
    - rewrite -> H4.
      assert (HC : Open_Name 0 z x0 = x0). apply Open_PName_Output; auto.
      rewrite -> HC.
      apply (Chan_replicate x0 P L0); auto.
    - rewrite -> H4.
      assert (HC : Open_Name 0 z (BName 0) = z). apply Open_BName_Output; auto.
      rewrite -> HC.
      apply (Chan_replicate z P L0); auto.
Qed.


(*
Al tomar un proceso y cambiarle un nombre libre, se obtiene un proceso. Es decir los procesos no son afectados sustancialmente por cambios de nombres.
*)
Lemma Subst_Process_Is_Process : 
forall ( x y : Name ) (P : Prepro), 
Process P -> Process_Name x -> Process_Name y -> Process ( { y \ x } P ). 
Proof.
  intros.
  induction H.
  + simpl. constructor.
  + simpl. 
    assert (HA : ((Subst_name x y x0 = y) \/ (Subst_name x y x0 = x0)) ). apply Subst_Name_Output; auto.
    assert (HB : ((Subst_name x y y0 = y) \/ (Subst_name x y y0 = y0)) ). apply Subst_Name_Output; auto.
    destruct HA;
     destruct HB;
      rewrite -> H3;
      rewrite -> H4;
      auto.
  + simpl. constructor; auto.
  + assert (HA : ((Subst_name x y x0 = y) \/ (Subst_name x y x0 = x0)) ). apply Subst_Name_Output; auto.
    assert (HB : ((Subst_name x y y0 = y) \/ (Subst_name x y y0 = y0)) ). apply Subst_Name_Output; auto.
    constructor. 
    - destruct HA;
     destruct HB;
      rewrite -> H3 || rewrite -> H4; auto.
    -destruct HA;
     destruct HB;
      rewrite -> H5 || rewrite -> H4; auto.
    - auto. 
  + assert (HA : ((Subst_name x y x0 = y) \/ (Subst_name x y x0 = x0)) ). apply Subst_Name_Output; auto.
    constructor; destruct HA; rewrite -> H2; auto.
  + simpl. constructor.
    - assert (HA : ((Subst_name x y x0 = y) \/ (Subst_name x y x0 = x0)) ). apply Subst_Name_Output; auto.
      destruct HA; rewrite -> H3; auto.
    - assumption.
  + simpl. apply (Chan_res ({y \ x} P) L).
    intros. specialize (H2 x0 H3).
    rewrite -> Eq_Subs_Open.
    assumption.
  + simpl. apply (Chan_input (Subst_name x y x0) ({y \ x} P) L).
    - assert (HA : ((Subst_name x y x0 = y) \/ (Subst_name x y x0 = x0)) ). apply Subst_Name_Output; auto. 
      destruct HA; rewrite -> H4; auto.
    - intros. specialize (H3 x1 H4).
      rewrite -> Eq_Subs_Open.
      assumption.
  + simpl. apply (Chan_replicate (Subst_name x y x0) ({y \ x} P) L).
    - assert (HA : ((Subst_name x y x0 = y) \/ (Subst_name x y x0 = x0)) ). apply Subst_Name_Output; auto. 
      destruct HA; rewrite -> H4; auto.
    - intros. specialize (H3 x1 H4).
      rewrite -> Eq_Subs_Open. auto.
Qed.

Lemma Open_Process_Is_Process : 
forall (x : Name)(P : Prepro),
Process_Name x -> Process P -> Process ( P ^ x) .
Proof.
  intros.
  induction H0.
  + auto.
  + inversion H0. inversion H1. subst.
    unfold Open. simpl. auto.
  + unfold Open. simpl. constructor; auto.
  + inversion H0. inversion H1. subst. 
    unfold Open. simpl. 
    constructor; auto.
  + inversion H0. subst.
    unfold Open. simpl.
    constructor; auto.
  + inversion H0. subst.
    unfold Open. simpl.
    constructor; auto.
  + unfold Open. simpl.
    apply (Chan_res ({1 ~> x} P) L).
    intros. 
  
  
Admitted.



Theorem Congruence_WD : 
forall P Q : Prepro, 
(P === Q) -> Process(P)  -> Process(Q).
Proof.
  intros.
  induction H; auto.
  + inversion H0. inversion H5. subst.
    apply (Chan_res (P ↓ Q) L).
    intros. unfold Open. simpl.
    constructor.
    - specialize (MalDiseno x) as Hx.
      specialize (Hx L H2).
      apply Open_Process_Is_Process; auto.
    - specialize (H7 x H2).
      auto.
Qed.

(*
Resultado fundamental para la representación LNR, al hacer una redución de un proceso se obtiene un proceso.
*)
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
    apply Subst_Process_Is_Process; auto.
  + inversion H0.
    constructor; assumption.
  + inversion H0. apply (Chan_res (Close_Rec 0 x Q) L).
    apply (Close_Is_Body x Q); auto.
  (* + assumption. *)
Qed.