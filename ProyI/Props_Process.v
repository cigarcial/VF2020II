(*
  Verificación Formal - Unam 2020-2
  Ciro Iván García López 
  Proyecto 1. Session Type Systems Verification
*)
From Coq Require Import Strings.String.
From Coq Require Import Lists.List.
From Coq Require Import Arith.EqNat.
From PROYI Require Import  Defs_Process.

Axiom Eq_Subs_Open : 
forall (x y z : Name) ( P :Prepro), 
((({y \ x} P )^ z) = ({y \ x} P ^ z)).

Axiom Eq_Subs_Close : 
forall (i : nat) ( z x : Name) ( P : Prepro),
({i ~> z} Close_Rec i x P) = P.

Axiom MalDiseno : 
forall (z : Name)( L : list Name ), 
(~ In z L ) -> Process_Name z.



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



Lemma Aux3 : 
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



Lemma Aux5 : 
forall ( i : nat )( x y : Name),
Process_Name y -> (Open_Name i x y = y).
Proof. 
  intros.
  inversion H.
  auto.
Qed.



Lemma Aux6 : 
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



Lemma Aux4 :
forall (x : Name)(P : Prepro),
Process_Name x -> Process P -> ( forall(L : list Name) (z : Name), ~ (In z L) -> Process (Close_Rec 0 x P ^ z) ).
Proof.
  intros.
  induction H0.
  + simpl. constructor.
  + unfold Open. simpl.
    assert (HZ : Process_Name z). apply (MalDiseno z L); auto.
    assert (HA : ((Close_Name 0 x x0 = x0) \/ (Close_Name 0 x x0 = BName 0)) ). apply Aux3; auto.
    assert (HB : ((Close_Name 0 x y = y) \/ (Close_Name 0 x y = BName 0)) ). apply Aux3; auto. 
    constructor.
    - destruct HA.
      * rewrite -> H3.
        assert (HC : Open_Name 0 z x0 = x0). apply Aux5; auto.
        rewrite -> HC. auto.
      * rewrite -> H3.
        assert (HC : Open_Name 0 z (BName 0) = z). apply Aux6; auto.
        rewrite -> HC. auto.
    - destruct HB.
      * rewrite -> H3.
        assert (HC : Open_Name 0 z y = y). apply Aux5; auto.
        rewrite -> HC. auto.
      * rewrite -> H3.
        assert (HC : Open_Name 0 z (BName 0) = z). apply Aux6; auto.
        rewrite -> HC. auto.
  + unfold Open. simpl. constructor; auto.
  + unfold Open. simpl.
    assert (HZ : Process_Name z). apply (MalDiseno z L); auto.
    assert (HA : ((Close_Name 0 x x0 = x0) \/ (Close_Name 0 x x0 = BName 0)) ). apply Aux3; auto.
    assert (HB : ((Close_Name 0 x y = y) \/ (Close_Name 0 x y = BName 0)) ). apply Aux3; auto.
    constructor.
    - destruct HA.
      * rewrite -> H3.
        assert (HC : Open_Name 0 z x0 = x0). apply Aux5; auto.
        rewrite -> HC. auto.
      * rewrite -> H3.
        assert (HC : Open_Name 0 z (BName 0) = z). apply Aux6; auto.
        rewrite -> HC. auto.
    - destruct HB.
      * rewrite -> H3.
        assert (HC : Open_Name 0 z y = y). apply Aux5; auto.
        rewrite -> HC. auto.
      * rewrite -> H3.
        assert (HC : Open_Name 0 z (BName 0) = z). apply Aux6; auto.
        rewrite -> HC. auto.
  + unfold Open. simpl.
    assert (HZ : Process_Name z). apply (MalDiseno z L); auto.
    assert (HA : ((Close_Name 0 x x0 = x0) \/ (Close_Name 0 x x0 = BName 0)) ). apply Aux3; auto.
    constructor.
    destruct HA.
    - rewrite -> H2.
      assert (HC : Open_Name 0 z x0 = x0). apply Aux5; auto.
      rewrite -> HC. auto.
    - rewrite -> H2.
      assert (HC : Open_Name 0 z (BName 0) = z). apply Aux6; auto.
      rewrite -> HC. auto.
  + unfold Open. simpl. 
    assert (HZ : Process_Name z). apply (MalDiseno z L); auto.
    constructor.
    - assert (HA : ((Close_Name 0 x x0 = x0) \/ (Close_Name 0 x x0 = BName 0)) ). apply Aux3; auto.
      destruct HA.
      * rewrite -> H3.
        assert (HC : Open_Name 0 z x0 = x0). apply Aux5; auto.
        rewrite -> HC. auto.
      * rewrite -> H3.
        assert (HC : Open_Name 0 z (BName 0) = z). apply Aux6; auto.
        rewrite -> HC. auto.
    - auto.
  + unfold Open. simpl. 
    rewrite -> Eq_Subs_Close.
    apply (Chan_res P L0).
    auto.
  + unfold Open. simpl.
    assert (HZ : Process_Name z). apply (MalDiseno z L); auto.
    rewrite -> Eq_Subs_Close.
    assert (HA : ((Close_Name 0 x x0 = x0) \/ (Close_Name 0 x x0 = BName 0)) ). apply Aux3; auto.
    destruct HA.
    - rewrite -> H4.
      assert (HC : Open_Name 0 z x0 = x0). apply Aux5; auto.
      rewrite -> HC.
      apply (Chan_input x0 P L0); auto.
    - rewrite -> H4.
      assert (HC : Open_Name 0 z (BName 0) = z). apply Aux6; auto.
      rewrite -> HC.
      apply (Chan_input z P L0); auto.
  + unfold Open. simpl.
    rewrite -> Eq_Subs_Close.
    assert (HZ : Process_Name z). apply (MalDiseno z L); auto.
    assert (HA : ((Close_Name 0 x x0 = x0) \/ (Close_Name 0 x x0 = BName 0)) ). apply Aux3; auto.
    destruct HA.
    - rewrite -> H4.
      assert (HC : Open_Name 0 z x0 = x0). apply Aux5; auto.
      rewrite -> HC.
      apply (Chan_replicate x0 P L0); auto.
    - rewrite -> H4.
      assert (HC : Open_Name 0 z (BName 0) = z). apply Aux6; auto.
      rewrite -> HC.
      apply (Chan_replicate z P L0); auto.
Qed.



Lemma Aux1 : 
forall ( x y : Name ) (P : Prepro), 
Process P -> Process_Name x -> Process_Name y -> Process ( { y \ x } P ). 
Proof.
  intros.
  induction H.
  + simpl. constructor.
  + simpl. 
    assert (HA : ((Subst_name x y x0 = y) \/ (Subst_name x y x0 = x0)) ). apply Aux2; auto.
    assert (HB : ((Subst_name x y y0 = y) \/ (Subst_name x y y0 = y0)) ). apply Aux2; auto.
    destruct HA;
     destruct HB;
      rewrite -> H3;
      rewrite -> H4;
      auto.
  + simpl. constructor; auto.
  + assert (HA : ((Subst_name x y x0 = y) \/ (Subst_name x y x0 = x0)) ). apply Aux2; auto.
    assert (HB : ((Subst_name x y y0 = y) \/ (Subst_name x y y0 = y0)) ). apply Aux2; auto.
    constructor;
    destruct HA;
     destruct HB;
      rewrite -> H3 || rewrite -> H4; auto.
  + assert (HA : ((Subst_name x y x0 = y) \/ (Subst_name x y x0 = x0)) ). apply Aux2; auto.
    constructor; destruct HA; rewrite -> H2; auto.
  + simpl. constructor.
    - assert (HA : ((Subst_name x y x0 = y) \/ (Subst_name x y x0 = x0)) ). apply Aux2; auto.
      destruct HA; rewrite -> H3; auto.
    - assumption.
  + simpl. apply (Chan_res ({y \ x} P) L).
    intros. specialize (H2 x0 H3).
    rewrite -> Eq_Subs_Open.
    assumption.
  + simpl. apply (Chan_input (Subst_name x y x0) ({y \ x} P) L).
    - assert (HA : ((Subst_name x y x0 = y) \/ (Subst_name x y x0 = x0)) ). apply Aux2; auto. 
      destruct HA; rewrite -> H4; auto.
    - intros. specialize (H3 x1 H4).
      rewrite -> Eq_Subs_Open.
      assumption.
  + simpl. apply (Chan_replicate (Subst_name x y x0) ({y \ x} P) L).
    - assert (HA : ((Subst_name x y x0 = y) \/ (Subst_name x y x0 = x0)) ). apply Aux2; auto. 
      destruct HA; rewrite -> H4; auto.
    - intros. specialize (H3 x1 H4).
      rewrite -> Eq_Subs_Open. auto.
Qed.



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
  + inversion H0. apply (Chan_res (Close_Rec 0 x Q) L).
    apply (Aux4 x Q); auto.
  (* + assumption. *)
Qed.