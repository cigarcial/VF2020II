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

Al cambiar un nombre por otro, se obtiene lo mismo. En otras palabras la equivalencia alpha 
*)
Axiom Ax_Alpha : 
forall (x y: Name)( P : Prepro),
({y \ x} P ) = P.


(*
Axioma de peligro !!!
Invocar cuando se tenga certeza de lo que se esta haciendo está bien.
*)
Axiom Ax_Process_Name :
forall ( x : Name),
Process_Name x.


Axiom Eq_Subs_Open :
forall (x y z : Name) ( P :Prepro), 
( ( {0 ~> z}({y \ x} P ) )  = ({y \ x} ( {0 ~> z} P ))).


Axiom Eq_Proc_Open : 
forall (x: Name) ( P : Prepro),
({0 ~> x} P) = P.


(*
Si dos cadenas son iguales, su valor de verdad en comparación es true
*)
Lemma Str_True :
forall ( x y : string), 
x = y -> String.eqb x y = true.
Proof.
  intros.
  remember ( eqb_spec x y). 
  inversion r; try contradiction; auto.
Qed.


(*
Si dos cadenas no son iguales, su valor de verdad en comparación es false
*)
Lemma Str_False : 
forall ( x y : string), 
x <> y -> String.eqb x y = false.
Proof.
  intros.
  remember ( eqb_spec x y). 
  inversion r; try contradiction; auto.
Qed.


(*
Al hacer una cerradura y seguidamente una apertura de un nombre, es lo mismo a realizar una sustitución. 
*)
Lemma Eq_Oped_Subst_Name : 
forall ( x y u : Name)(i : nat),
Process_Name x -> Process_Name y -> Process_Name u -> 
Open_Name i y (Close_Name i u x)  = Subst_Name u y x.
Proof.
  intros.
  inversion H. inversion H0. inversion H1. subst.
  specialize (string_dec x0 x2) as HD1.
  inversion HD1.
  + specialize (Str_True x0 x2) as HS.
    simpl. 
    rewrite HS; auto.
    simpl.
    assert ( HA : Nat.eqb i i = true).
      { remember ( beq_nat_refl i ).
        inversion e; tauto. }
    rewrite HA. auto.
  + specialize (Str_False x0 x2) as HS.
    simpl. 
    rewrite HS; auto.
Qed.


(*
Materializa la idea intuitiva que al cerrar y seguidamente abrir un 'Body' es como si se estuviera haciendo un cambio de nombre. Son tres las observaciones: 
  - La primera es notar que se invoca sobre (S i), esto es porque para el caso 0 no es cierta la afirmación. 
  - No se pide la hipótesis de 'Body', suavice las hipótesis ya que no he podido trabajar en el caso que deseo. 
  - Se esta dando uso a Ax_Process_Name, esto no esta mal dado que posteriormente se usa unicamente sobre cuerpo.
*)
Lemma Eq_Subs_Close_Body:
forall (P : Prepro)(i : nat)(x y : Name),
Process_Name x -> Process_Name y ->
{ (S i) ~> y} (Close_Rec (S i) x P) = {y \ x} P.
Proof.
  intro P.
  induction P.
  + auto.
  + intros; simpl.
    specialize (Ax_Process_Name x) as Hx.
    specialize (Ax_Process_Name y) as Hy.
    rewrite Eq_Oped_Subst_Name; auto.
    rewrite Eq_Oped_Subst_Name; auto.
  + intros; simpl.
    rewrite IHP1; auto.
    rewrite IHP2; auto.
  + intros; simpl.
    specialize (Ax_Process_Name x) as Hx.
    specialize (Ax_Process_Name y) as Hy.
    rewrite Eq_Oped_Subst_Name; auto.
    rewrite Eq_Oped_Subst_Name; auto.
    rewrite IHP; auto.
  + intros; simpl.
    specialize (Ax_Process_Name x) as Hx.
    rewrite Eq_Oped_Subst_Name; auto.
  + intros; simpl.
    specialize (Ax_Process_Name x) as Hx.
    rewrite IHP; auto.
    rewrite Eq_Oped_Subst_Name; auto.
  + intros; simpl.
    rewrite IHP; auto.
  + intros; simpl.
    specialize (Ax_Process_Name x) as Hx.
    rewrite IHP; auto.
    rewrite Eq_Oped_Subst_Name; auto.
  + intros; simpl.
    specialize (Ax_Process_Name x) as Hx.
    rewrite IHP; auto.
    rewrite Eq_Oped_Subst_Name; auto.
Qed.


(*
*)
Lemma Eq_Subs_Close:
forall (P : Prepro)(x y : Name),
Process P -> Process_Name x -> Process_Name y ->
{ 0 ~> y} (Close_Rec 0 x P) = {y \ x} P.
Proof.
  intros.
  induction H.
  + auto.
  + simpl. 
    rewrite Eq_Oped_Subst_Name; auto.
    rewrite Eq_Oped_Subst_Name; auto.
  + simpl.
    rewrite IHProcess1.
    rewrite IHProcess2.
    auto. 
  + simpl.
    rewrite IHProcess.
    rewrite Eq_Oped_Subst_Name; auto.
    rewrite Eq_Oped_Subst_Name; auto.
  + simpl.
    rewrite Eq_Oped_Subst_Name; auto.
  + simpl.
    rewrite IHProcess.
    rewrite Eq_Oped_Subst_Name; auto.
  + simpl.
    rewrite Eq_Subs_Close_Body; auto.
  + simpl. 
    rewrite Eq_Oped_Subst_Name; auto.
    rewrite Eq_Subs_Close_Body; auto.
  + simpl. 
    rewrite Eq_Oped_Subst_Name; auto.
    rewrite Eq_Subs_Close_Body; auto.
Qed.

(*
Siempre que se hace una sustitución sobre nombres solo se pueden obtener dos resultados, se remplaza o queda igual.
*)
Lemma Subst_Name_Output : 
forall x y z : Name ,
Process_Name x -> Process_Name y -> Process_Name z -> ((Subst_Name x y z = y) \/ (Subst_Name x y z = z)).
Proof.
  intros.
  inversion H. inversion H0. inversion H1.
  specialize (string_dec x2 x0).
  intro.
  inversion H5.
  + specialize (Str_True x2 x0) as HB.
    simpl. 
    rewrite HB; auto.
  + specialize (Str_False x2 x0) as HB.
    simpl. 
    rewrite HB; auto.
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
  + specialize (Str_True x1 x0) as HB.
    simpl. 
    rewrite -> HB; auto.
  + specialize (Str_False x1 x0) as HB.
    simpl. 
    rewrite -> HB; auto.
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
( forall(L : list Name) (z : Name), Process_Name z ->  ~ (In z L) -> Process ( (Close_Rec 0 x P) ) )
*)
Lemma Close_Is_Body:
forall (x : Name)(P : Prepro),
Process_Name x -> Process P -> Body( Close x P ).
Proof.
  intros.
  induction H0.
  + constructor. auto.
  + constructor; intros.
    simpl.
    specialize (Close_Name_Output 0 x x0) as HA.
    specialize (HA H H0).
    specialize (Close_Name_Output 0 x y) as HB.
    specialize (HB H H1).
    destruct HA.
    - destruct HB.
      * rewrite H4. rewrite H5.
        simpl.
        specialize (Open_PName_Output 0 x1 x0) as HC.
        specialize (HC H0).
        specialize (Open_PName_Output 0 x1 y) as HD.
        specialize (HD H1).
        rewrite HC. rewrite HD. auto.
      * rewrite H4; rewrite H5.
        simpl. 
        specialize (Open_PName_Output 0 x1 x0) as HC.
        specialize (HC H0).
        rewrite HC.
        auto.
    - destruct HB.
      * rewrite H4. rewrite H5.
        simpl. 
        specialize (Open_PName_Output 0 x1 y) as HD.
        specialize (HD H1).
        rewrite HD.
        auto.
      * rewrite H4. rewrite H5.
        simpl. auto.
  + constructor. intros.
    simpl. constructor.
    - inversion IHProcess1; subst.
      specialize (H2 x0 L H0 H1).
      auto.
    - inversion IHProcess2; subst.
      specialize (H2 x0 L H0 H1).
      auto.
  + constructor; intros.
    simpl. constructor.
    - specialize (Close_Name_Output 0 x x0) as HA.
      destruct HA; auto.
      * rewrite H5.
        specialize(Open_PName_Output 0 x1 x0) as HB.
        rewrite HB; auto.
      * rewrite H5.
        auto.
    - specialize (Close_Name_Output 0 x y) as HA.
      destruct HA; auto.
      * rewrite H5.
        specialize(Open_PName_Output 0 x1 y) as HB.
        rewrite HB; auto.
      * rewrite H5.
        auto.
    - inversion IHProcess.
      specialize (H5 x1 L H3 H4).
      auto.
  + constructor; intros.
    simpl. constructor.
    specialize (Close_Name_Output 0 x x0) as HA.
    destruct HA; auto.
    - rewrite H3.
      specialize(Open_PName_Output 0 x1 x0) as HB.
      rewrite HB; auto.
    - rewrite H3. auto.
  + constructor; intros.
    simpl. constructor.
    - specialize (Close_Name_Output 0 x x0) as HA.
      destruct HA; auto.
      * rewrite H4.
        specialize(Open_PName_Output 0 x1 x0) as HB.
        rewrite HB; auto.
      * rewrite H4; auto.
    - inversion IHProcess.
      specialize (H4 x1 L H2 H3).
      auto.
  + constructor; intros.
    simpl.
    rewrite Eq_Subs_Close_Body; auto.
    rewrite Ax_Alpha; auto.
  + constructor; intros.
    simpl.
    rewrite Eq_Subs_Close_Body; auto.
    specialize (Close_Name_Output 0 x x0) as HX.
    destruct HX; 
      try rewrite H5;
      try specialize (Open_PName_Output 0 x1 x0) as HX || specialize (Open_BName_Output 0 x1) as HX;
      try rewrite HX; 
      try rewrite Ax_Alpha; 
      try constructor; auto.
  + constructor; intros.
    simpl. 
    rewrite Eq_Subs_Close_Body; auto.
    specialize (Close_Name_Output 0 x x0) as HX.
    destruct HX; 
      try rewrite H5;
      try specialize (Open_PName_Output 0 x1 x0) as HX || specialize (Open_BName_Output 0 x1) as HX;
      try rewrite HX; 
      try rewrite Ax_Alpha; 
      try constructor; auto.
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
    specialize (Subst_Name_Output x y x0) as HA.
    specialize (Subst_Name_Output x y y0) as HB.
    destruct HA;
      try destruct HB;
      try rewrite H3; 
      try rewrite H4; 
      auto.
  + simpl. constructor; auto.
  + simpl.
    specialize (Subst_Name_Output x y x0) as HA.
    specialize (Subst_Name_Output x y y0) as HB.
    constructor.
    - destruct HA;
      destruct HB;
      try rewrite -> H3 || rewrite -> H4; auto.
    - destruct HA;
      destruct HB;
      try rewrite -> H5 || rewrite -> H4; auto.
    - auto.
  + simpl.
    specialize (Subst_Name_Output x y x0) as HA.
    constructor.
    destruct HA;
      try rewrite H2; auto.
  + simpl. constructor.
    - specialize (Subst_Name_Output x y x0) as HA.
      destruct HA; try rewrite H3;  auto.
    - assumption.
  + simpl. apply (Chan_res ({y \ x} P)).
    intros. specialize (H2 x0 L H3 H4).
    rewrite Eq_Subs_Open.
    assumption.
  + simpl.
    constructor.
    - specialize (Subst_Name_Output x y x0) as HA.
      destruct HA; try rewrite H4; auto.
    - intros.
      specialize (H3 x1 L H4 H5).
      rewrite Eq_Subs_Open.
      assumption.
  + simpl.
    constructor.
    - specialize (Subst_Name_Output x y x0) as HA.
      destruct HA; try rewrite H4; auto.
    - intros.
      specialize (H3 x1 L H4 H5).
      rewrite Eq_Subs_Open.
      assumption.
Qed.

Lemma Open_Process_Is_Process : 
forall (x : Name)(P : Prepro),
Process_Name x -> Process P -> Process ( {0 ~> x} P ).
Proof.
  intros.
  induction H0.
  + auto.
  + simpl.
    specialize (Open_PName_Output 0 x x0) as HA.
    specialize (Open_PName_Output 0 x y) as HB.
    rewrite HA; auto.
    rewrite HB; auto.
  + simpl. constructor; auto.
  + simpl. constructor; auto.
    - specialize (Open_PName_Output 0 x x0) as HA.
      rewrite HA; auto.
    - specialize (Open_PName_Output 0 x y) as HA.
      rewrite HA; auto.
  + simpl. constructor.
    specialize (Open_PName_Output 0 x x0) as HA.
    rewrite HA; auto.
  + simpl.
    constructor.
    - specialize (Open_PName_Output 0 x x0) as HA.
      rewrite HA; auto.
    - auto.
  + rewrite Eq_Proc_Open.
    auto.
  + rewrite Eq_Proc_Open.
    auto.
  + rewrite Eq_Proc_Open.
    auto.
Qed.


(**)
Theorem Congruence_WD : 
forall P Q : Prepro, 
(P === Q) -> Process(P)  -> Process(Q).
Proof.
  intros.
  induction H; auto.
  + inversion H0. inversion H5. subst.
    constructor.
    intros. unfold Open. simpl.
    constructor.
    - apply Open_Process_Is_Process; auto.
    - specialize (H7 x L H2 H3).
      auto.
  + rewrite Ax_Alpha. auto.
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
    - inversion H1. inversion H0. destruct H2. inversion H7. subst.
      specialize (H3 y x0 H13 H2).
      auto.
  + constructor.
    - constructor.
      * assumption.
      * inversion H1. inversion H0.  inversion H7. destruct H2. subst.
        specialize (H3 y x1 H13 H2).
        auto.
    - inversion H0. auto.
  + inversion H1.
    assumption.
  + inversion H0.
    inversion H4.
    apply Subst_Process_Is_Process; auto.
  + inversion H0.
    constructor; assumption.
  + constructor.
    specialize (Close_Is_Body x Q) as HT.
    specialize (HT H2 H1).
    inversion HT.
    auto.
  (* + assumption. *)
Qed.