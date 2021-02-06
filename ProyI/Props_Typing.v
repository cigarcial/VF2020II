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


(*
*)
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
  + rewrite Ax_Alpha in H.
    rewrite <- (Ax_Alpha u x Q). 
    constructor; auto.
    apply (ProcessReduction_WD P Q); auto.
  + rewrite Ax_Alpha in H.
    rewrite <- (Ax_Alpha u x Q). 
    constructor; auto.
    apply (ProcessReduction_WD P Q); auto.
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
