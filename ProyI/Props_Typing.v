(*
  Verificación Formal - Unam 2020-2
  Ciro Iván García López
  Proyecto 1. Session Type Systems Verification
*)
From PROYI Require Import  Defs_Typing.
From PROYI Require Import  Defs_Process.
From PROYI Require Import  Defs_Proposition.
From Coq Require Import Strings.String.
From PROYI Require Import Props_Process.


(*
Los siguientes lemas apoyan la prueba del teorema 2.1, determinan que algunos de los casos no se reducen a algo.

*)
Lemma No_Red_AX1 : 
forall (x y : Name)(Q : Prepro), 
~([x ←→  y] --> Q ).
Proof. 
  unfold not.
  intros.
  inversion H.
Qed.

Lemma No_Red_AX2 : 
forall (x y : Name)(P Q : Prepro), 
~ ((x !· Close_Rec 0 y P) --> Q).
Proof.
  unfold not.
  intros.
  inversion H.
Qed.

Lemma No_Red_AX3 : 
forall ( x u : Name ) ( P Q : Prepro),
~ ( { x \ u } P --> Q).
Proof.
Admitted.

Lemma No_Red_AX4 : 
forall (x : Name)(P Q: Prepro),
~( (x · P) --> Q ).
Proof.
  unfold not.
  intros.
  inversion H.
Qed. 

Check No_Red_AX4.


Lemma No_Red_AX51 : 
forall (x y : Name)(P Q R: Prepro), 
~( (x « y »· (P ↓ Q)) --> R ).
Proof.
  unfold not.
  intros.
  inversion H.
Qed.


Lemma No_Red_AX52 : 
forall (x : Name)(P Q: Prepro), 
(P = Q ) -> (Open_Rec 0 x P = Open_Rec 0 x Q).
Proof.
  intros.
  rewrite <- H.
  auto.
Qed.

Lemma No_Red_AX55 : 
forall ( x y : Name), 
Process_Name x -> Process_Name y -> (Open_Name 0 x (Close_Name 0 y y)) = x.
Proof.
  intros.
  inversion H. inversion H0.
  specialize (string_dec x1 x1).
  intro.
  inversion H3.
  (* buscar una manera más bonita de probar esto, no es un resultado 'difícil'  *)
  + assert ( HB : String.eqb x1 x1 = true).
    - remember ( eqb_spec x1 x1).
      inversion r; tauto. 
    - simpl. rewrite -> HB. auto.
  + contradiction.
Qed.



Lemma No_Red_AX56 : 
forall ( x y z: Name), 
Process_Name x -> Process_Name y -> 
(Open_Name 0 z (Close_Name 0 y x) = z) \/ (Open_Name 0 z (Close_Name 0 y x) = x).
Proof. 
  intros.
  inversion H. inversion H0.
  specialize (string_dec x0 x1).
  intro.
  inversion H3.
  (* buscar una manera más bonita de probar esto, no es un resultado 'difícil'  *)
  + assert ( HB : String.eqb x0 x1 = true).
    - remember ( eqb_spec x0 x1).
      inversion r; tauto. 
    - simpl. rewrite -> HB. auto.
  + assert ( HB : String.eqb x0 x1 = false).
    - remember ( eqb_spec x0 x1).
      inversion r; tauto. 
    - simpl. rewrite -> HB. auto.
Qed.

Lemma Open_Close_Name_Subst : 
forall ( x y z : Name),
Process_Name x -> Process_Name y -> Process_Name z -> 
(Open_Name 0 x (Close_Name 0 y z)) = (Subst_name y x z).
Proof.
  intros.
  inversion H. inversion H0. inversion H1.
  simpl.
  specialize (string_dec x2 x1).
  intro.
  inversion H5.
  (* buscar una manera más bonita de probar esto, no es un resultado 'difícil'  *)
  + assert ( HB : String.eqb x2 x1 = true).
    - remember ( eqb_spec x2 x1).
      inversion r; tauto. 
    - simpl. rewrite -> HB. auto.
  + assert ( HB : String.eqb x2 x1 = false).
    - remember ( eqb_spec x2 x1).
      inversion r; tauto. 
    - simpl. rewrite -> HB. auto.
Qed.

Lemma No_Red_AX54 : 
forall (x y : Name)(P : Prepro), 
Process_Name x -> Process_Name y -> Process P -> (Open_Rec 0 x (Close_Rec 0 y P)) = ({x \ y} P).
Proof.
  intros.
  induction H1.
  + auto.
  + simpl.
    rewrite -> Open_Close_Name_Subst;
    try rewrite -> Open_Close_Name_Subst;
    auto.
  + simpl.
    rewrite -> IHProcess1;
    try rewrite -> IHProcess2;
    auto.
  + simpl.
    rewrite -> Open_Close_Name_Subst;
    try rewrite -> Open_Close_Name_Subst;
    try rewrite -> IHProcess;
    auto.
  + simpl.
    rewrite -> Open_Close_Name_Subst; auto.
  + simpl.
    rewrite -> Open_Close_Name_Subst; try rewrite -> IHProcess; auto.
  + admit.
  + admit.
  + admit.
Admitted.

Lemma No_Red_AX5 : 
forall (x y : Name)(P Q R: Prepro), 
Process_Name x -> Process_Name y -> Process P -> Process Q ->
~( (ν Close_Rec 0 y (x « y »· (P ↓ Q))) --> R ).
Proof.
  unfold not.
  intros.
  inversion H3.
  apply (No_Red_AX52 x0 _ _ ) in H4.
  rewrite -> Eq_Subs_Close in  H4.
  simpl in H4.
  assert (HB : (Open_Name 0 x0 (Close_Name 0 y x) = x0) \/ (Open_Name 0 x0 (Close_Name 0 y x) = x) ). apply No_Red_AX56; auto.
  do 2  rewrite -> No_Red_AX54 in H4;
  try rewrite -> No_Red_AX55 in H4;
  destruct HB;
    rewrite -> H10 in H4;
    rewrite -> H4 in H8;
    apply No_Red_AX51 in H8; auto.
Qed.

Lemma No_Red_AX6 : 
forall (x : Name)(P Q : Prepro), 
~( ( x ()· P ) --> Q).
Proof.
  unfold not.
  intros.
  inversion H.
Qed.

Lemma No_Red_AX71 :
forall ( x u : Name)( P Q : Prepro),
~((u « x »· P) --> Q).
Proof.
  unfold not.
  intros.
  inversion H.
Qed.

Lemma No_Red_AX7 :
forall ( x u : Name)( P Q : Prepro),
Process_Name x -> Process_Name u -> 
~(ν (Close_Rec 0 x (u « x »· P)) --> Q).
Proof.
  unfold not.
  intros.
  inversion H1.
  apply (No_Red_AX52 x0 _ _ ) in H2.
  rewrite -> Eq_Subs_Close in  H2.
  simpl in H2.
  rewrite -> No_Red_AX55 in H2.
  assert (HB : (Open_Name 0 x0 (Close_Name 0 x u) = x0) \/ (Open_Name 0 x0 (Close_Name 0 x u) = u) ). apply No_Red_AX56; auto.
  destruct HB;
    rewrite -> H8 in H2;
    rewrite -> H2 in H6;
    apply No_Red_AX71 in H6;
    contradiction.
  auto. auto.
Qed.


Lemma No_Red_AX8 : 
forall ( u x : Name) (P Q R : Prepro),
(ν Close_Rec 0 u ((u !· Close_Rec 0 x P) ↓ Q) --> R) -> exists (Q0 : Prepro),( R = ν Close_Rec 0 u ((u !· Close_Rec 0 x P) ↓ Q0) /\ Q --> Q0).
Admitted.


Theorem Soundness : 
forall (D F G : list Assignment)(P Q : Prepro),
  (P --> Q) -> ( D ;;; F !- P ::: G )
  -> ( D ;;; F !- Q ::: G ).
Proof.
  intros.  
  induction H0.
  + apply No_Red_AX1 in H. contradiction.
  + apply No_Red_AX1 in H. contradiction.
  + apply No_Red_AX2 in H. contradiction.
  + apply No_Red_AX3 in H. contradiction.
  + apply No_Red_AX3 in H. contradiction.
  + apply No_Red_AX2 in H. contradiction.
  + apply No_Red_AX4 in H. contradiction.
  + apply No_Red_AX5 in H; try contradiction; auto.
  + apply No_Red_AX4 in H. contradiction.
  + apply No_Red_AX5 in H; try contradiction; auto.
  + apply No_Red_AX4 in H. contradiction.
  + apply No_Red_AX5 in H; try contradiction; auto.
  + apply No_Red_AX6 in H. contradiction.
  + inversion H.
  + apply No_Red_AX6 in H. contradiction.
  + inversion H.
  + apply No_Red_AX7 in H; try contradiction; auto. 
  + apply No_Red_AX7 in H; try contradiction; auto.
  + admit.
Admitted.
