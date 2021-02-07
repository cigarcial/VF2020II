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
  inversion H; inversion H0; subst.
  specialize (string_dec x1 x1) as HX.
  destruct HX.
  + specialize (Str_True x1 x1) as HB.
    simpl.
    rewrite HB; auto.
  + contradiction.
Qed.


(*
*)
Lemma No_Red_AX5 : 
forall (x y : Name)(P Q R: Prepro), 
Process_Name x -> Process_Name y -> Process P -> Process Q ->
~( (ν Close_Rec 0 y (x « y »· (P ↓ Q))) --> R ).
Proof.
  unfold not.
  intros.
  inversion H3; subst.
  apply (No_Red_AX52 x0 _ _ ) in H4.
  unfold Close in H4.
  rewrite Eq_Subs_Close in H4; auto.
  simpl in H4.
  specialize (Close_Name_Output 0 y x) as HX.
  rewrite No_Red_AX55 in H4; auto.
  rewrite Eq_Subs_Close in H4; auto.
  rewrite Eq_Subs_Close in H4; auto.
  do 3 rewrite Ax_Alpha in H4.
  rewrite H4 in H8.
  destruct HX;
    try rewrite H9 in H8;
    try specialize (Open_PName_Output 0 x0 x) as HX || specialize (Open_BName_Output 0 x0) as HX;
    try rewrite HX in H8;
    try apply No_Red_AX51 in H8; auto.
Qed.


(*
*)
Lemma No_Red_AX6 : 
forall (x : Name)(P Q : Prepro), 
~( ( x ()· P ) --> Q).
Proof.
  unfold not.
  intros.
  inversion H.
Qed.


(*
*)
Lemma No_Red_AX71 :
forall ( x u : Name)( P Q : Prepro),
~((u « x »· P) --> Q).
Proof.
  unfold not.
  intros.
  inversion H.
Qed.


(*
*)
Lemma No_Red_AX7 :
forall ( x u : Name)( P Q : Prepro),
Process_Name x -> Process_Name u -> Process P -> 
~(ν (Close_Rec 0 x (u « x »· P)) --> Q).
Proof.
  unfold not.
  intros.
  inversion H2; subst.
  apply (No_Red_AX52 x0 _ _ ) in H3.
  rewrite Eq_Subs_Close in H3; auto.
  rewrite Ax_Alpha in H3.
  simpl in H3.
  rewrite No_Red_AX55 in H3; auto.
  rewrite Eq_Subs_Close in H3; auto.
  rewrite Ax_Alpha in H3.
  rewrite H3 in H7.
  specialize (Close_Name_Output 0 x u) as HX.
  destruct HX; 
    try rewrite H8 in H7;
    try specialize (Open_PName_Output 0 x0 u) as HX || specialize (Open_BName_Output 0 x0) as HX;
    try rewrite HX in H7;
    try apply No_Red_AX71 in H7;
    auto.
Qed.

Lemma No_Red_AX8 : 
forall (x : Name)( Q : Prepro),
~ ((x «»·°) --> Q).
Proof.
  unfold not.
  intros.
  induction Q; try inversion H.
Qed.


Lemma Char_Red_Chanres :
forall (P Q : Prepro),
(ν (P) --> Q ) -> 
exists (Q0 : Prepro), ( Q = (ν (Q0)) /\ P --> Q0).
Proof.
  intros.
  inversion H. subst.
  exists (Close x Q0).
  split; auto.
Admitted.


Lemma Char_Red_Arr :
forall (u : Name)(P Q0 Q1 : Prepro),
( ((u !· P) ↓ Q0) --> Q1 ) -> 
(exists (Q2 : Prepro), ( Q1 = ((u !· P) ↓ Q2) /\ Q0 --> Q2 )).
Proof.
  intros.
  inversion H; subst.
  + admit.
  + exists R.
    split; auto.
Admitted.


Theorem Soundness : 
forall (P : Prepro)(D F G : list Assignment),
  ( D ;;; F !- P ::: G ) -> (forall (Q: Prepro), (P --> Q)
  -> ( D ;;; F !- Q ::: G )).
Proof.
  intros P D F G H.
  induction H; intros.
  + apply No_Red_AX1 in H2. contradiction.
  + apply No_Red_AX1 in H2. contradiction.
  + apply No_Red_AX2 in H4. contradiction.
  + rewrite Ax_Alpha in H6.
    rewrite <- (Ax_Alpha u x Q). 
    constructor; auto.
    apply (ProcessReduction_WD P Q); auto.
  + rewrite Ax_Alpha in H6.
    rewrite <- (Ax_Alpha u x Q). 
    constructor; auto.
    apply (ProcessReduction_WD P Q); auto.
  + apply No_Red_AX2 in H4. contradiction.
  + apply No_Red_AX4 in H6. contradiction.
  + apply No_Red_AX5 in H10; try contradiction; auto.
  + apply No_Red_AX4 in H6. contradiction.
  + apply No_Red_AX5 in H10; try contradiction; auto.
  + apply No_Red_AX4 in H6. contradiction.
  + apply No_Red_AX5 in H10; try contradiction; auto.
  + apply No_Red_AX6 in H5. contradiction.
  + apply No_Red_AX8 in H1. contradiction.
  + apply No_Red_AX6 in H5. contradiction.
  + apply No_Red_AX8 in H1. contradiction.
  + apply No_Red_AX7 in H6; try contradiction; auto. 
  + apply No_Red_AX7 in H6; try contradiction; auto.
  + specialize (Char_Red_Chanres  ((u !· P) ↓ Q) Q0 ) as HX.
    specialize (HX H8).
    destruct HX as [Q1 H9].
    destruct H9.
    rewrite H9.
    specialize (Char_Red_Arr u P Q Q1) as HT.
    specialize (HT H10).
    destruct HT as [Q2 H11].
    destruct H11.
    rewrite H11.
    apply (cutcon D F G x u P Q2 A); auto.
    apply (ProcessReduction_WD Q Q2); auto.
Qed.


