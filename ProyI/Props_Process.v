(*
  Verificación Formal - Unam 2020-2
  Ciro Iván García López 
  Proyecto 1. Session Type Systems Verification
*)
From Coq Require Import Bool.Bool.
From Coq Require Import Arith.PeanoNat.
From Coq Require Import Arith.EqNat.
From Coq Require Import Ensembles.
From Coq Require Import Finite_sets.
From Coq Require Import Finite_sets_facts.
From PROYI Require Import  Defs_Process.
From Coq Require Import Lia.


Ltac inversions H := inversion H; subst.
Ltac isBody := constructor; intros; simpl; repeat constructor.


(*
*)
Lemma FVars_Name_Finite :
forall (x : Name),
Finite _ (FVars_Name x).
Proof.
  destruct x.
  + simpl. apply Singleton_is_finite.
  + simpl. constructor.
Qed.


(*
*)
Lemma FVars_Finite :
forall (P : Prepro),
Finite _ (FVars P).
Proof.
  induction P.
  + simpl.
    constructor.
  + simpl. apply Union_preserves_Finite; apply FVars_Name_Finite.
  + simpl. apply Union_preserves_Finite; auto.
  + simpl. apply Union_preserves_Finite; try apply Union_preserves_Finite; try apply FVars_Name_Finite; auto.
  + simpl. apply FVars_Name_Finite.
  + simpl. apply Union_preserves_Finite; try apply Union_preserves_Finite; try apply FVars_Name_Finite; auto.
  + auto.
  + simpl. apply Union_preserves_Finite; try apply Union_preserves_Finite; try apply FVars_Name_Finite; auto.
  + simpl. apply Union_preserves_Finite; try apply Union_preserves_Finite; try apply FVars_Name_Finite; auto.
Qed.


Lemma There_Is_A_Name :
forall ( P : Prepro ),
exists ( x : nat ), ~ ( x ∈ (FVars P) ).
Proof.
Admitted.



(*
*)
Lemma No_Union_No_Each : 
forall (x : nat)( X Y : FVarsE ),
~(x ∈ (X ∪ Y)) -> ~(x ∈ X) /\ ~(x ∈ Y).
Proof.
Admitted.


(*
*)
Lemma FVars_Name_No_Close :
forall (z k : nat)(x : Name),
~ (z ∈ FVars_Name x) -> (Close_Name k z x = x).
Proof.
  unfold not.
  intros.
  destruct x.
  + destruct (bool_dec (x =? z) true).
    - simpl in H. apply Nat.eqb_eq in e.
      rewrite e in H.
      assert ( HB : z ∈ Singleton nat z).
      { unfold In. constructor. }
      contradiction.
    - simpl. apply not_true_iff_false in n.
      rewrite n. auto.
  + auto.
Qed.


(*
*)
Lemma Close_NoFVar_Eq :
forall ( P : Prepro )(z k: nat),
~ ( z ∈ (FVars P) ) -> ( Close_Rec k z P ) = P.
Proof.
  unfold Close.
  induction P; intros.
  + auto.
  + simpl in H.
    apply No_Union_No_Each in H.
    destruct H as [HA HB].
    simpl.
    rewrite FVars_Name_No_Close; auto.
    rewrite FVars_Name_No_Close; auto.
  + simpl in H.
    apply No_Union_No_Each in H.
    destruct H as [HA HB].
    simpl.
    rewrite IHP1; auto.
    rewrite IHP2; auto.
  + simpl in H.
    apply No_Union_No_Each in H.
    destruct H as [H HC].
    simpl in H.
    apply No_Union_No_Each in H.
    destruct H as [HA HB].
    simpl.
    rewrite IHP; auto.
    rewrite FVars_Name_No_Close; auto.
    rewrite FVars_Name_No_Close; auto.
  + simpl in H.
    simpl.
    rewrite FVars_Name_No_Close; auto.
  + simpl in H.
    apply No_Union_No_Each in H.
    destruct H as [HA HB].
    simpl.
    rewrite IHP; auto.
    rewrite FVars_Name_No_Close; auto.
  + simpl in H.
    simpl.
    rewrite IHP; auto.
  + simpl in H.
    apply No_Union_No_Each in H.
    destruct H as [HA HB].
    simpl.
    rewrite FVars_Name_No_Close; auto.
    rewrite IHP; auto.
  + simpl in H.
    apply No_Union_No_Each in H.
    destruct H as [HA HB].
    simpl.
    rewrite FVars_Name_No_Close; auto.
    rewrite IHP; auto.
Qed.

Lemma Body_Process_Equivalence :
forall (P : Prepro),
Body P <-> Process (ν P).
Proof.
  split.
  + intros.
    constructor. inversion H. auto.
  + intros.
    inversion H. constructor. auto.
Qed.




(*
Siempre que se hace una sustitución sobre nombres solo se pueden obtener dos resultados, se remplaza o queda igual.
*)
Lemma Subst_Name_Output :
forall ( x y : nat )( z : Name ),
Process_Name z -> ((Subst_Name x y z = (FName y)) \/ (Subst_Name x y z = z)).
Proof.
  intros.
  inversions H.
  simpl. 
  destruct (bool_dec (x0 =? x) true).
  + rewrite e. auto.
  + apply not_true_iff_false in n.
    rewrite n. auto.
Qed.


(*
Análogamente, al cerrar un nombre solo hay dos opciones, se remplazar o queda igual.
*)
Lemma Close_Name_Output : 
forall ( i x : nat) ( y : Name), 
Process_Name y -> ( (Close_Name i x y = y) \/ (Close_Name i x y = BName i) ).
Proof.
  intros.
  inversion H.
  simpl.
  destruct (bool_dec (x0 =? x) true).
  + rewrite e. auto.
  + apply not_true_iff_false in n.
    rewrite n. auto.
Qed.


Lemma Open_BName_Output :
forall ( k x p : nat),
Open_Name k x (BName p) = BName p \/ Open_Name k x (BName p) = FName x.
Proof.
  intros.
  simpl.
  destruct (bool_dec (k =? p) true).
  - rewrite e; auto.
  - apply not_true_iff_false in n.
    rewrite n; auto.
Qed.


Lemma Output_PName_Output :
forall ( p : Name )( k x : nat ),
Process_Name p -> Open_Name k x p = p.
Proof.
  intros.
  inversions H.
  auto.
Qed.


Lemma Open_BName_IsFName_Eq :
forall ( k x p : nat),
Open_Name k x (BName p) = FName x -> k = p.
Proof.
  intros.
  destruct (bool_dec (k =? p) true).
  + apply beq_nat_true; auto.
  + apply not_true_iff_false in n.
    simpl in H.
    rewrite n in H.
    discriminate.
Qed.

Lemma Open_BName_IsBName_Eq :
forall ( k x p : nat),
Open_Name k x (BName p) = BName p -> k <> p.
Proof.
  intros.
  destruct (bool_dec (k =? p) true).
  + simpl in H.
    rewrite e in H.
    discriminate.
  + apply not_true_iff_false in n.
    apply beq_nat_false; auto.
Qed.


Lemma Eq_Open_Name_Sk_i :
forall ( i y k x p : nat),
i <> (S k) -> 
Open_Name i y (Open_Name (S k) x (BName p)) = Open_Name (S k) x (Open_Name i y (BName p)).
Proof.
  intros.
  specialize ( Open_BName_Output (S k) x p) as HA.
  specialize ( Open_BName_Output i y p) as HB.
  destruct HA.
  + destruct HB.
    - congruence.
    - rewrite ?H0; rewrite ?H1.
      auto.
 + destruct HB.
  - rewrite H1; rewrite H0.
    auto.
  - apply Open_BName_IsFName_Eq in H0.
    apply Open_BName_IsFName_Eq in H1.
    lia.
Qed.



Lemma Exchange_Open_Sk_i :
forall ( P : Prepro)(x y k i : nat),
i <> S k -> 
{i ~> y} ( {S k ~> x} P ) = {S k ~> x} ( {i ~> y} P ).
Proof.
  induction P; intros.
  + auto.
  + simpl.
    destruct x.
    - destruct y.
      * auto.
      * rewrite (Eq_Open_Name_Sk_i i y0 k x0 i0); auto.
    - destruct y.
      * rewrite (Eq_Open_Name_Sk_i i y0 k x0 i0); auto.
      * rewrite (Eq_Open_Name_Sk_i i y0 k x0 i0); auto.
        rewrite (Eq_Open_Name_Sk_i i y0 k x0 i1); auto.
  + simpl. 
    rewrite IHP1; auto.
    rewrite IHP2; auto.
  + simpl.
    rewrite IHP; auto.
     destruct x.
      - destruct y.
        * auto.
        * rewrite (Eq_Open_Name_Sk_i i y0 k x0 i0); auto.
      - destruct y.
        * rewrite (Eq_Open_Name_Sk_i i y0 k x0 i0); auto.
        * rewrite (Eq_Open_Name_Sk_i i y0 k x0 i0); auto.
          rewrite (Eq_Open_Name_Sk_i i y0 k x0 i1); auto.
  + simpl.
    destruct x.
    - auto.
    - rewrite (Eq_Open_Name_Sk_i i y k x0 i0); auto.
  + simpl.
    rewrite IHP; auto.
    destruct x.
    - auto.
    - rewrite (Eq_Open_Name_Sk_i i y k x0 i0); auto.
  + simpl.
    apply f_equal.
    rewrite IHP; auto.
  + simpl.
    rewrite IHP; auto.
    destruct x.
    - auto.
    - rewrite (Eq_Open_Name_Sk_i i y k x0 i0); auto.
  + simpl.
    rewrite IHP; auto.
    destruct x.
    - auto.
    - rewrite (Eq_Open_Name_Sk_i i y k x0 i0); auto.
Qed.




(*
*)
Lemma Process_Name_Process_NameAt :
forall ( x : Name ),
Process_Name x -> Process_Name_At 0 x.
Proof.
  intros.
  inversions H.
  constructor.
Qed.


(*
*)
Lemma Process_Name_Atzero :
forall ( x : Name ),
Process_Name_At 0 x -> (exists (x0 : nat), x = FName x0).
Proof.
  intros.
  destruct x.
  + exists x; auto.
  + inversions H.
    lia.
Qed.


(*
*)
Lemma Process_Name_At_Open :
forall (x : Name)(i x0 : nat),
Process_Name_At i (Open_Name i x0 x) -> 
Process_Name_At (S i) x.
Proof.
  intros.
  destruct x.
  - constructor.
  - simpl in H.
    destruct (bool_dec (i =? i0) true).
    rewrite e in H.
    * constructor.
      apply beq_nat_true in e.
      lia.
    * apply not_true_iff_false in n.
      rewrite n in H.
      inversions H.
      constructor.
      auto.
Qed.


(*
*)
Lemma Process_At_Open_S :
forall ( P : Prepro )( x i: nat),
Process_At i ({i ~> x} P) -> Process_At (S i) P.
Proof.
  intro.
  induction P.
  + intros.
    constructor.
  + intros.
    inversions H.
    constructor.
    - apply (Process_Name_At_Open _ _ x0); auto.
    - apply (Process_Name_At_Open _ _ x0); auto.
  + intros.
    inversions H.
    constructor.
    apply (IHP1 x _); auto.
    apply (IHP2 x _); auto.
  + intros.
    inversions H.
    constructor.
    - apply (Process_Name_At_Open _ _ x0); auto.
    - apply (Process_Name_At_Open _ _ x0); auto.
    - apply (IHP x0 _); auto.
  + intros.
    inversions H.
    constructor.
    apply (Process_Name_At_Open _ _ x0); auto.
  + intros.
    inversions H.
    constructor.
    - apply (Process_Name_At_Open _ _ x0); auto.
    - apply (IHP x0 _); auto.
  + intros.
    constructor.
    simpl in H.
    inversions H.
    specialize (IHP x (S i) H2).
    auto.
  + intros.
    inversions H.
    specialize (IHP x0 (S i) H4).
    constructor.
    - apply (Process_Name_At_Open _ _ x0); auto.
    - auto.
  + intros.
    inversions H.
    specialize (IHP x0 (S i) H4).
    constructor.
    - apply (Process_Name_At_Open _ _ x0); auto.
    - auto.
Qed.


(*
*)
Theorem Process_ProcessAt :
forall ( P : Prepro ), 
Process P -> Process_At 0 P.
Proof.
  intros.
  induction H;  
    constructor; 
    try apply Process_Name_Process_NameAt; 
    try specialize (FVars_Finite P) as FV;
    try specialize (There_Is_A_Name P) as HX;
    try destruct HX;
    try specialize (H0 (FVars P) FV x H1) || specialize (H1 (FVars P) FV x0 H2);
    try apply (Process_At_Open_S _ x _ ) || apply (Process_At_Open_S _ x0 _ );
    auto.
Qed.




















(*

Interacción entre las operaciones de apertura, cerradura y sustitución.

*)


Lemma Body_Parallel_Body_Each :
forall ( P Q : Prepro),
Body (P ↓ Q) -> (Body P /\ Body Q).
Proof.
  constructor; 
    try constructor;
    intros;
    inversions H;
    specialize (H2 L H0 x H1);
    simpl in H2;
    inversions H2; auto.
Qed.

Lemma Open_Process_Process :
forall ( P : Prepro ), Process P -> 
forall ( k x : nat ), Process ( {k ~> x}P ).
Proof.
  intros P H.
  induction H; intros; simpl.
  + auto.
  + rewrite Output_PName_Output; auto.
    rewrite Output_PName_Output; auto.
  + constructor.
    apply IHProcess1.
    apply IHProcess2.
  + rewrite Output_PName_Output; auto.
    rewrite Output_PName_Output; auto.
  + rewrite Output_PName_Output; auto.
  + rewrite Output_PName_Output; auto.
  + simpl.
    isBody.
    specialize (H0 L H1 x0 H2 (S k) x).
    rewrite Exchange_Open_Sk_i; auto.
  + simpl.
    isBody.
    - rewrite Output_PName_Output; auto.
    - specialize (H1 L H2 x1 H3 (S k) x0).
      rewrite Exchange_Open_Sk_i; auto.
  + simpl.
    isBody.
    - rewrite Output_PName_Output; auto.
    - specialize (H1 L H2 x1 H3 (S k) x0).
      rewrite Exchange_Open_Sk_i; auto.
Qed.



Lemma All_Process_Body :
forall (P : Prepro),
Process P -> Body P.
Proof.
  intros.
  constructor.
  intros.
  apply Open_Process_Process; auto.
Qed.




Lemma Subst_BName_Output :
forall ( x y i : nat ),
Subst_Name x y (BName i) = BName i.
Proof.
  intros.
  simpl.
  auto.
Qed.

Lemma Subst_Name_Open_Name_Ex : 
forall ( x : Name )( x0 y0 z w k: nat ),
FName w = Subst_Name x0 y0 (FName z) -> 
Subst_Name x0 y0 (Open_Name k z x) = Open_Name k w (Subst_Name x0 y0 x).
Proof.
  intros.
  destruct x.
  + simpl.
    destruct (bool_dec (x =? x0) true).
    - rewrite e. auto.
    - apply not_true_iff_false in n.
      rewrite n. auto.
  + specialize ( Open_BName_Output k z i ) as HA.
    destruct HA.
    - rewrite Subst_BName_Output.
      rewrite H0.
      specialize ( Open_BName_Output k w i ) as HB.
      destruct HB.
      * rewrite H1; auto.
      * apply Open_BName_IsFName_Eq in H1.
        apply Open_BName_IsBName_Eq in H0.
        contradiction.
    - rewrite Subst_BName_Output.
      rewrite H0.
      specialize ( Open_BName_Output k w i ) as HB.
      destruct HB.
      * apply Open_BName_IsFName_Eq in H0.
        apply Open_BName_IsBName_Eq in H1.
        contradiction.
      * rewrite H1.
        rewrite H.
        auto.
Qed.


Lemma Subst_Open_Exchange :
forall ( P : Prepro )( x y z w k: nat ),
FName w = (Subst_Name x y (FName z)) -> 
{y \ x} ({k ~> z} P) = {k ~> w} ({y \ x} P).
Proof.
  intro.
  induction P; intros.
  + auto.
  + simpl.
    rewrite (Subst_Name_Open_Name_Ex _ _ _ _  w _ ); auto.
    rewrite (Subst_Name_Open_Name_Ex y x0 y0 z w k ); auto.
  + simpl.
    rewrite (IHP1 _ _ _ w _); auto.
    rewrite (IHP2 _ _ _ w _); auto.
  + simpl.
    rewrite (Subst_Name_Open_Name_Ex _ _ _ _ w _ ); auto.
    rewrite (Subst_Name_Open_Name_Ex _ _ _ _ w _ ); auto.
    rewrite (IHP _ _ _ w _); auto.
  + simpl.
    rewrite (Subst_Name_Open_Name_Ex _ _ _ _ w _ ); auto.
  + simpl.
    rewrite (Subst_Name_Open_Name_Ex _ _ _ _ w _ ); auto.
    rewrite (IHP _ _ _ w _); auto.
  + simpl.
    rewrite (IHP x y z w (S k)); auto.
  + simpl.
    rewrite (Subst_Name_Open_Name_Ex x x0 y z w k ); auto.
    rewrite (IHP x0 y z w (S k)); auto.
  + simpl.
    rewrite (Subst_Name_Open_Name_Ex x x0 y z w k ); auto.
    rewrite (IHP x0 y z w (S k)); auto.
Qed.






















Lemma Subst_Body_Body :
forall (P : Prepro),
Body P -> forall (x y : nat), Body ({y \ x} P).
Proof.
Admitted.

(*
*)
Lemma Subst_Process_Process :
forall (P : Prepro)(x y : nat),
Process P -> Process ({y \ x} P).
Proof.
  intros.
  induction H.
  + auto.
  + simpl.
    specialize (Subst_Name_Output x y x0) as HA.
    specialize (Subst_Name_Output x y y0) as HB.
    destruct HA;
      destruct HB;
        try rewrite H1;
        try rewrite H2;
        try constructor; try constructor; auto.
  + simpl.
    constructor; auto.
  + simpl.
    specialize (Subst_Name_Output x y x0) as HA.
    specialize (Subst_Name_Output x y y0) as HB.
    destruct HA;
      destruct HB;
        try rewrite H2;
        try rewrite H3;
        try constructor; try constructor; auto.
  + simpl.
    specialize (Subst_Name_Output x y x0) as HA.
    destruct HA; 
      try rewrite H0;
      try constructor; try constructor; auto.
  + simpl.
    specialize (Subst_Name_Output x y x0) as HA.
    destruct HA; 
      try rewrite H1;
      try constructor; try constructor; auto.
  + simpl.
    constructor.
    intros.
    specialize ( H0 L H1 x0 H2).
    specialize (Subst_Name_Output x y (FName x0)) as HS.
    destruct HS; try constructor.
    - specialize (Subst_Open_Exchange P x y x0 y 0) as HA.
      apply eq_sym in H3.
      specialize (HA H3).
      
      admit.
    - apply eq_sym in H3.
      specialize (Subst_Open_Exchange P x y x0 x0 0) as HA.
      specialize (HA H3).
      rewrite <- HA; auto.
 (*    specialize ( Subst_Body_Body P) as HP.
    simpl.
    assert ( HB : Body P ). constructor; auto.
    specialize ( HP HB x y ).
    inversion HP.
    constructor; auto. *)
  + specialize ( Subst_Body_Body P) as HP.
    simpl.
    assert ( HB : Body P ). constructor; auto.
    specialize ( HP HB x y ).
    inversion HP.
    constructor.
    - specialize (Subst_Name_Output x y x0) as HA.
        destruct HA;
          try rewrite H4;
          try constructor; try constructor; auto.
    - auto.
  + specialize ( Subst_Body_Body P) as HP.
    simpl.
    assert ( HB : Body P ). constructor; auto.
    specialize ( HP HB x y ).
    inversion HP.
    constructor.
    - specialize (Subst_Name_Output x y x0) as HA.
        destruct HA;
          try rewrite H4;
          try constructor; try constructor; auto.
    - auto.
Admitted.



Theorem Congruence_WD :
forall P Q : Prepro, 
(P === Q) -> Process(P)  -> Process(Q).
Proof.
  intros.
  inversions H; inversions H0; auto.
  constructor.
  intros.
  simpl.
  constructor.
  + apply (Open_Process_Process); auto.
  + inversion H6.
    apply (H8 L); auto.
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
  + constructor; auto.
    inversions H1.
    inversions H2.
    specialize (FVars_Finite Q) as HF.
    apply (H3 (FVars Q)); auto.
  + inversions H0.
    inversions H5.
    inversions H6.
    inversions H2.
    specialize (FVars_Finite Q) as HF.
    constructor; auto.
    constructor; auto.
    apply (H11 (FVars Q)); auto.
  + inversions H1; auto.
  + 
    specialize (Subst_Process_Process P x y) as HP.
    specialize (HP H).
    auto.
  + inversions H0.
    constructor; auto.
  + admit.
  + apply IHReduction in H.
    specialize (Congruence_WD Q' Q) as HQ.
    specialize (HQ H2 H).
    auto.
Admitted.









Lemma Close_ISBody2 :
forall ( P : Prepro )(x : nat),
Process P -> Body (Close_Rec 0 x P).
Proof.
  intros.
  induction H.
  + admit.
  + admit.
  + admit.
  + admit.
  + admit.
  + admit.
  + intros.
    constructor.
    intros.
    simpl.
    constructor.
    intros.
Admitted.


Lemma Close_ISBody_At:
forall ( P : Prepro )(x : nat),
Process_At 0 P -> Process_At 1 (Close_Rec 0 x P).
Proof.
  intros.
  induction H.
  + admit.
  + simpl. admit.
  + admit.
  + simpl.
    admit.
  + admit.
  + admit.
  + simpl.
    constructor; auto.
Admitted.








































Lemma Close_ISBody2 :
forall ( P : Prepro ),
Process P -> forall (x : nat), Body (Close x P).

Proof.
  intros P H.
  unfold Close.
  induction P; intros.
  + simpl. isBody.
  + inversions H.
    inversions H2.
    inversions H3.
    simpl.
    destruct (bool_dec (x1 =? x0) true);
      destruct (bool_dec (x =? x0) true);
        try apply not_true_iff_false in n;
        try apply not_true_iff_false in n0;
        try rewrite e || rewrite n0;
        try rewrite e0 || rewrite n;
        isBody.
  + inversions H.
    isBody.
    - specialize (IHP1 H2 x).
      inversions IHP1.
      specialize (H4 L H0 x0 H1).
      auto.
    - specialize (IHP2 H3 x).
      inversions IHP2.
      specialize (H4 L H0 x0 H1).
      auto.
  + inversions H.
    inversions H3.
    inversions H4.
    isBody.
    - destruct (bool_dec (x1 =? x0) true);
        try apply not_true_iff_false in n;
        rewrite e || rewrite n;
        constructor.
    - destruct (bool_dec (x =? x0) true);
        try apply not_true_iff_false in n;
        rewrite e || rewrite n;
        constructor.
    - specialize (IHP H5 x0).
      inversions IHP.
      apply (H2 L); auto.
  + inversions H.
    inversions H1.
    isBody.
    destruct (bool_dec (x1 =? x0) true);
      try apply not_true_iff_false in n;
      rewrite e || rewrite n;
      constructor.
  + inversions H.
    inversions H2.
    isBody.
    - destruct (bool_dec (x1 =? x0) true);
        try apply not_true_iff_false in n;
        rewrite e || rewrite n;
        constructor.
    - specialize (IHP H3 x0).
      inversions IHP.
      apply (H4 L); auto.
  + simpl.
    constructor.
    simpl.
    constructor.
    intros.
    inversions H.
Admitted.


Lemma Open_Body_Eq :
forall (P : Prepro),
Body P -> (forall (x k : nat), {(S k) ~> x} P = P ).
Proof.
Admitted.


Lemma Open_Process_Eq :
forall (P : Prepro),
Process P -> (forall (x k: nat), {k ~> x} P = P).
Proof.
  intros P H.
  induction H; intros.
  + auto.
  + inversions H.
    inversions H0.
    auto.
  + simpl.
    rewrite IHProcess1.
    rewrite IHProcess2.
    auto.
  + inversions H.
    inversions H0.
    simpl.
    rewrite IHProcess.
    auto.
  + inversions H.
    auto.
  + inversions H.
    simpl.
    rewrite IHProcess.
    auto.
  + simpl.
    rewrite (Open_Body_Eq P); try constructor; auto.
  + inversions H.
    simpl.
    rewrite (Open_Body_Eq P); try constructor; auto.
  + inversions H.
    simpl.
    rewrite (Open_Body_Eq P); try constructor; auto.
Admitted.



Lemma Subst_Process_Process2 :
forall (P : Prepro),
Process P -> forall (x y : nat), Process ({y \ x} P).
Proof.
  intros P H.
  induction H; intros.
  + admit.
  + admit.
  + admit.
  + admit.
  + admit.
  + admit.
  + simpl.
    constructor.
    intros.
    specialize (H0 L H1 x0 H2 x y).
Admitted.

Lemma Subst_Body_Body2 :
forall (P : Prepro),
Body P -> forall (x y : nat), Body ({y \ x} P).
Proof.
  intro.
  induction P.
  + admit.
  + admit.
  + admit.
  + admit.
  + admit.
  + admit.
  + intros.
    simpl.
    constructor.
    intros.
    simpl.
    constructor.
    intros.
    inversions H.
    specialize (H4 L H0 x0 H1).
    simpl in H4.
    inversions H4.
    specialize (H6 L H0 x0 H1).
Admitted.


