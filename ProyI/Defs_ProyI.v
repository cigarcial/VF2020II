(*
  Verificación Formal - Unam 2020-2
  Ciro Iván García López
  Proyecto 1. Session Type Systems Verification
*) 
From Coq Require Import Strings.String.
From Coq Require Import Nat. 
From Coq Require Import Lists.List.

 
Inductive ULLType : Type := 
  | ONE : ULLType
  | ABS : ULLType
  | TEN (A : ULLType) (B : ULLType) : ULLType
  | PAR (A : ULLType) (B : ULLType) : ULLType
(*   | ULLT_IMP (A : ULLType) (B : ULLType) : ULLType  *)
  | EXP (A : ULLType) : ULLType
  | MOD (A : ULLType) : ULLType.

Hint Constructors ULLType : core.

(*
Notación de acuerdo al artículo, sin embargo falta definir bien los niveles y la asociatividad 	
*)
Notation "¶" := ONE.
Notation "⊥" := ABS.
Notation "A ⊗ B" := (TEN A B)(at level 70, right associativity).
Notation "A ⅋ B" := (PAR A B)(at level 70, right associativity).
(* Notation "A −∘ B" := (ULLT_IMP A B)(at level 50, left associativity). *)
Notation "! A" := (EXP A)(at level 60, right associativity).
Notation "? A" := (MOD A)(at level 60, right associativity).


Fixpoint Dual_ULLT ( T : ULLType ) : ULLType := 
match T with 
  | ¶ => ⊥
  | ⊥ => ¶
  | A ⊗ B => (Dual_ULLT A) ⅋ (Dual_ULLT B)
  | A ⅋ B => (Dual_ULLT A) ⊗ (Dual_ULLT B)
  | ! A => ? (Dual_ULLT A)
  | ? A => ! (Dual_ULLT A)
end.

Hint Unfold Dual_ULLT : core.

Notation "A '^⊥'" := (Dual_ULLT A)(at level 60, right associativity).
Definition ULLT_IMP (A : ULLType) (B : ULLType) : ULLType := (A^⊥) ⅋ B.

Notation "A −∘ B" := (ULLT_IMP A B)(at level 70, right associativity).


(*

Cuarta aproximación a la mecanización de los procesos, se procede usando la idea de locally named representation
Se introducen FVAR y BVAR para denotar variables libres y ligadas 

Esta vez se utilizan las ideas del artículo de Castro Engineering The Meta-Theory of Session Types

Siguiendo las ideas de LNR se debe definir una nueva gramática que haga la distinción entre las variables libres y ligadas
*)

Inductive Name : Type := 
  | FName ( x : string) : Name
  | BName ( i : nat) : Name.


Inductive Prepro : Type  := 
  (* Ahora vienen los procesos bajo las nuevas ideas *)
  | Prezero : Prepro 
  | Prefuse (x y : Name) : Prepro
  | Preparallel (P Q : Prepro ) : Prepro
  | Preoutput ( x y : Name ) (P : Prepro) : Prepro
  | Prechan_zero (x : Name ) : Prepro
  | Prechan_close ( x : Name ) ( P : Prepro ) : Prepro
  (* preprocesos con variables ligadas *)
  | Prechan_res (P : Prepro ) : Prepro
  | Prechan_input ( x : Name ) (P : Prepro) : Prepro
  | Prechan_replicate ( x : Name)(P : Prepro ) : Prepro.

(*

Observe que la nueva idea es más sencilla, se tienen menos términos no deseados.

La notación cambia bastante, no se fija el tipo de nombre por defecto

Faltan las asociatividades y las prioridades 
*)
Notation "°" :=  Prezero.
Notation "[ x ←→ y ]" := (Prefuse x y ) ( at level 60).
(*Cambio la notación respecto al artículo, 
no uso el | porque genera problemas en las definiciones Inductive *)
Notation "P ↓ Q" :=  (Preparallel P Q ) ( at level 60).
Notation "x  « y »· P " := (Preoutput x y P ) (at level 60).
Notation "x «»·° " :=  (Prechan_zero x ) (at level 60).
Notation "x ()· P" := (Prechan_close x P)(at level 60).
(* procesos con ligadas*)
Notation " 'ν' P " := (Prechan_res P ) ( at level 60).
Notation "x · P " := (Prechan_input x P)(at level 60).
Notation " x !· P " :=  (Prechan_replicate x P)(at level 60).


(*
Se necesitan las nociones de apertura y clausura de variables, por lo que se procede a definirlas apropiadamente. 

Se usa la misma notación del artículo de Charguéraud

Se necesita ahora distinguir dos aperturas uno para preprocesos y otra para los nombres.
*) 
 
Definition Open_Name ( k : nat )(z: string)( N : Name ) : Name := 
match N with 
  | FName x => FName x
  | BName i => if ( k =? i ) then (FName z) else (BName i)
end. 

(* Ahora la apertura de preprocesos bajo la nueva gramática *)
Fixpoint Open_Rec (k : nat)( z : string )( T : Prepro ) {struct T} : Prepro := 
match T with
  | Prezero => Prezero
  | Prefuse x y => Prefuse (Open_Name k z x ) (Open_Name k z y )
  | Preparallel P Q => Preparallel (Open_Rec k z P) (Open_Rec k z Q)
  | Preoutput x y P => Preoutput (Open_Name k z x) (Open_Name k z y) (Open_Rec k z P) 
  | Prechan_zero x => Prechan_zero (Open_Name k z x)
  | Prechan_close x P => Prechan_close (Open_Name k z x) (Open_Rec k z P)
  | Prechan_res P => Prechan_res (Open_Rec (S k) z P)
  | Prechan_input x P => Prechan_input (Open_Name k z x) (Open_Rec (S k) z P)
  | Prechan_replicate x P => Prechan_replicate (Open_Name k z x) (Open_Rec (S k) z P)
end.

Notation "{ k ~> z } P " := (Open_Rec k z P)(at level 60).

Definition Open P z := Open_Rec 0 z P.
Notation "P ^ z" := (Open P z).


(*
Para abrir terminos con un nombre dado, tiene sentido para hablar de {y/x}
*)
Definition Open_wname ( N : Name ) ( T : Prepro ) : Prepro := 
match N with
  | FName z => Open_Rec 0 z T
  | BName z => T
end.


(*
Y como también menciona el artículo de LNR, con la nueva gramática se introducen términos extraños 
que no hacian parte de la gramática original; por lo que se debe definir el predicado local closure 
que básicamente es tomar los términos que si nos sirven y descartar lo demás.

Hay que incluir el hecho que una FName es un nombre de proceso 
*)

Inductive Process_Name : Name -> Prop := 
  | Process_FName : forall (x : string), Process_Name ( FName x).

 
Inductive Process : Prepro -> Prop :=
  | Zero : Process Prezero
  
  | Fuse : forall x y : Name, 
    Process_Name x -> Process_Name y -> Process ( [ x ←→ y] )
    
  | Parallel : forall P Q : Prepro, 
    Process P -> Process Q -> Process (P ↓ Q)
    
  | Output : forall (x y : Name ) (P : Prepro),
    Process_Name x -> Process_Name y -> Process ( x «y»· P)
  
  | Chan_zero : forall x : Name, 
    Process_Name x -> Process ( x «»·° )
    
  | Chan_close : forall (x : Name)(P : Prepro),
    Process_Name x -> Process P -> Process ( x ()· P )
  
  | Chan_res : forall P : Prepro, 
    (exists (z : string), Process (P ^ z) ) -> Process (ν P)
  
  | Chan_input : forall (x : Name ) (P: Prepro), 
    Process_Name x -> (exists (z : string), Process (P ^ z) ) -> Process ( x · P)
   
  | Chan_replicate : forall (x : Name) (P : Prepro),
    Process_Name x -> (exists (z : string), Process (P ^ z) ) -> Process ( x !· P ).


(*
Llegados a este punto es necesario introducir las equivalencias de la definición 2.4, observe que usando NLR no es necesario hablar 
de alpha-equivalencia pero si es necesario introducir las equivalencias entre procesos. 

Observe que hay reglas que no tienen mucho significado bajo la relación de NLR


Observe que no uso explicitamente los constructores ya que la notación se encarga de que tenga sentido
*)
Definition Parallel_Zero ( P : Prepro ) := (P↓°) = P.
Definition Conmt_Parallel ( P Q : Prepro ) := (P↓Q) = (Q↓P).
Definition Res_Zero := ( ν °)  = °.
Definition Asoc_Parallel ( P Q R : Prepro ) := ((P↓Q)↓R) = (P↓(Q↓R)).
Definition Conmt_Fuses ( x y : Name ) := [x ←→ y] = [y ←→ x].
(*
para la última regla no se usa la condición que x no sea nombre libre en P puesto que no tiene sentido por LNR
en vez de ello se debe pedir que sea una expresión bien formada o sea un proceso
*)
Definition Abs_Restriction ( P Q : Prepro ) := Process(P) -> (P↓(ν Q)) = ν (Q↓P).



(*
Se introducen las reducciones de la definición 2.5

Los 'if' quedaron bastante feos, no entiendo porque no acepta el operador && para bool y el =? para cadenas

Bajo la nueva mirada es necesario definir una sustitución para nombres {y/x}

*)

Definition Subst_name ( x y : string)( N : Name ) : Name := 
match N with 
  | FName z => if ( String.eqb x z ) then (FName y) else (FName z)
  | BName i => BName i 
end.

Fixpoint Subst ( x y : string )( T : Prepro ) {struct T} : Prepro := 
match T with
  | Prezero => Prezero 
  | Prefuse u v => Prefuse (Subst_name x y u ) (Subst_name x y v)
  | Preparallel P Q => Preparallel (Subst x y P) (Subst x y Q)
  | Preoutput u v P => Preoutput (Subst_name x y u) (Subst_name x y v) (Subst x y P)
  | Prechan_zero u => Prechan_zero (Subst_name x y u )
  | Prechan_close u P => Prechan_close (Subst_name x y u) (Subst x y P)
  (* preprocesos con variables ligadas *)
  | Prechan_res P => Prechan_res (Subst x y P)
  | Prechan_input u P  => Prechan_input (Subst_name x y u) (Subst x y P)
  | Prechan_replicate u P =>  Prechan_replicate (Subst_name x y u) (Subst x y P)
end.
Notation " { y \ x } P " := (Subst x y P) (at level 60). 



(*
Se define la noción de cerradura de un proceso bajo la restricción ν
Observe que a diferencia del artículo de NLR aquí hay 3 tipos de ligamiento y se debería definir por cada unor
una noción de cerradura diferente
*)

Definition Close_name (k : nat)(z : string)(N : Name) : Name := 
match N with 
  | FName x => if ( String.eqb x z ) then (BName k) else (FName x)
  | BName i => BName i
end.
 
Fixpoint Close_rec (k : nat)( z : string )( T : Prepro ) {struct T} : Prepro := 
match T with
  | Prezero => Prezero
  | Prefuse x y => Prefuse (Close_name k z x) (Close_name k z y)
  | Preparallel P Q => Preparallel (Close_rec k z P) (Close_rec k z Q)
  | Preoutput x y P  => Preoutput (Close_name k z x) (Close_name k z y) (Close_rec k z P)
  | Prechan_zero x => Prechan_zero  (Close_name k z x)
  | Prechan_close x P => Prechan_close (Close_name k z x) (Close_rec k z P)
  (* preprocesos con variables ligadas *)
  | Prechan_res P =>  (Close_rec (S k) z P)
  | Prechan_input x P => Prechan_input (Close_name k z x)  (Close_rec (S k) z P)
  | Prechan_replicate x P => Prechan_replicate (Close_name k z x)  (Close_rec (S k) z P)
end.

Notation "{ k ν<~ z } P " := (ν (Close_rec k z P))(at level 60).

Definition Close_Restriction P z := ν (Close_rec 0 z P).
Notation " z '/ν' P  " := (Close_Restriction P z)(at level 60).
 
Definition Body (P  : Prepro) := exists ( z : string), Process( P ^ z).


Reserved Notation "R '-->' S" (at level 60).
Inductive Reduction : Prepro -> Prepro -> Prop :=

  | Red_chzero_chclose : forall ( Q : Prepro) (x : Name), 
     Process ( x «»·° ) -> Process ( x ()· Q  ) -> ( ( ( x «»·° ) ↓ ( x ()· Q ) ) -->  Q )

  | Red_reduction_parallel : forall ( P Q R : Prepro), 
    Process R -> Process Q -> Process R -> ((P --> R) -> ((P ↓ Q ) --> (P ↓ R)))
  
  | Red_output_input : forall ( x y : Name ) ( P Q : Prepro ), 
    Process P -> Body Q -> (( (x « y »· P)  ↓ (x · Q) ) --> (P ↓ (Open_wname y Q)) )
  
  
  
(* 

| Red_parallel_fuses : forall (x y : Name) (P : Prepro),
    Process P -> Process ([ x ←→ y ]) -> ( ( P ↓ [ x ←→ y] ) --> ( Open_wname x P ) ) 



  | Red_Process_Fuses : forall ( P : PProcess) (x y : string), 
    ( P ↓ ( [ x ←→ y] ) ) -->  P{y/x} *)

where "R '-->' S" := (Reduction R S).
Hint Constructors Reduction : core.

Definition Nofnamein_name (z : string)( N : Name) : Prop :=
match N with 
  | FName x => if (String.eqb x z ) then False else True
  | BName i => True
end.


Fixpoint Nofnamein_rec ( z : string) (T : Prepro) {struct T} : Prop :=
match T with
  | Prezero => True
  | Prefuse x y => (Nofnamein_name z x ) /\ (Nofnamein_name z y)
  | Preparallel P Q => (Nofnamein_rec z P) /\ (Nofnamein_rec z Q)
  | Preoutput x y P  => (Nofnamein_name z x ) /\ (Nofnamein_name z y ) /\ (Nofnamein_rec z P)
  | Prechan_zero x => (Nofnamein_name z x )
  | Prechan_close x P => (Nofnamein_name z x ) /\ (Nofnamein_rec z P)
  (* preprocesos con variables ligadas *)
  | Prechan_res P => (Nofnamein_rec z P)
  | Prechan_input x P => (Nofnamein_name z x ) /\ (Nofnamein_rec z P)
  | Prechan_replicate x P => (Nofnamein_name z x ) /\ (Nofnamein_rec z P)
end.



Lemma Aux1 : 
forall (z : string) ( P : Prepro), 
Body P -> Nofnamein_rec z P -> Process ( P ^ z ).
Proof.
(*   intros.
  induction P.
  + unfold Open. simpl. constructor.
  + unfold Body in H. destruct H as [w H]. unfold Open in H. simpl in H. inversion H.
    inversion H3. inversion H4. unfold Nofnamein_rec in H0. destruct H0 as [HA HB].
    simpl.
  + unfold Body in H. destruct H as [w H]. inversion H.
    inversion H0.
    unfold Open. simpl. constructor.
    - apply IHP1.
      * unfold Body. exists w. assumption.
      * assumption.
    - apply IHP2.
      * unfold Body. exists w. assumption.
      * assumption.
  +  *)
Admitted.









Theorem ProcessReduction_WD : 
forall P Q : Prepro, 
(P --> Q) -> Process(P)  -> Process(Q).
Proof.
  intros. 
  induction H.
  + inversion H1.
    assumption.
  + constructor.
    - inversion H0.
      assumption.
    - assumption.
  + constructor.
    - assumption.
    - inversion H0.
      inversion H4.
      inversion H10.
      unfold Body in H1.
      simpl.
      apply Aux1.
Qed.





(*
Fixpoint IsFreeFor ( y : string )( T : PProcess ) {struct T} : Prop := 
match T with
  | P_FVAR x => ~ ( x = y )
  | P_BVAR i => True
  (* Ahora vienen los procesos bajo la nueva gramática *)
  | P_ZERO => True
  | P_FUSES P Q => (IsFreeFor y P) /\ (IsFreeFor y Q)
  | P_PARALLEL_COMP P Q =>  (IsFreeFor y P) /\ (IsFreeFor y Q)
  | P_CHAN_OUTPUT P Q R => (IsFreeFor y P) /\ (IsFreeFor y Q) /\ (IsFreeFor y R)  
  | P_CHAN_ZERO P => (IsFreeFor y P) 
  | P_CHAN_CLOSE P Q => (IsFreeFor y P) /\ (IsFreeFor y Q) 
  (*Cambian las definiciones para incluir las variables *)
  | P_CHAN_RES P => (IsFreeFor y P) 
  | P_CHAN_INPUT P Q => (IsFreeFor y P) /\ (IsFreeFor y Q) 
  | P_CHAN_REPLICATE P Q => (IsFreeFor y P) /\ (IsFreeFor y Q) 
end.

Locate " \ ".
Definition Open_IsFreeFor (x : string ) ( P : PProcess ) := 
  (Process (P ^ x )) -> (IsFreeFor x P).
Definition Subs_IsFreeFor (x y : string) ( P : PProcess ) := 
  (Process ( { y \ x } P ) ) -> (IsFreeFor x P). 

Lemma Conmt_Fuses_Process :
forall x y : string,
  Process([x ←→ y]) <-> Process([y ←→ x]).
Proof. 
  split.
  - intros.
    constructor.
  - intros.
    constructor.
Qed.

Lemma Equiv_Process_Zero : 
forall P : PProcess, 
Process (P ↓ °) <->  (Process P).
Proof. 
  split.
  - intros.
    inversion H.
    assumption.
  - intros.
    constructor.
    + assumption.
    + constructor.
Qed.


Lemma Aux1 : 
forall (x y : string)( P : PProcess),
 ( (P_FVAR y) = {0 ~> x} P) -> ( ((P_FVAR y) = P) \/ ((P_BVAR 0 ) = P) ).
Proof.
  intros.
  induction P.
  + simpl in H. left. assumption.
  + destruct i.
    - right. auto.
    - discriminate.
  + discriminate.
  + discriminate.
  + discriminate.
  + discriminate.
  + discriminate.
  + discriminate.
  + discriminate.
  + discriminate.
  + discriminate.
Qed.

Lemma Open_Change_Name : 
forall ( x y : string ) ( P : PProcess ),
( IsFreeFor y P ) ->  Process ( P ^ x ) -> Process ( P ^ y ).
Proof.
  intros.
  induction P.
  + simpl in H.
    assert (H1 : P_FVAR x0 ^ y = P_FVAR x0 ).
    - auto.
    - auto. 
  + destruct i.
    - unfold Open.
      simpl.
      constructor.
    - unfold Open in H0.
      simpl in H0.
      unfold Open.
      simpl.
      auto.
  + auto.
  + unfold Open in H0. simpl in H0. inversion H0.
    simpl in H. destruct H as [HP1 HP2].
    apply Aux1 in H2. apply Aux1 in H3.
    unfold Open. simpl.
    destruct H2; 
     destruct H3;
       rewrite <- H; rewrite <- H1;
       simpl; constructor.
  + unfold Open in H0. simpl in H0. inversion H0.
    simpl in H. destruct H as [HP1 HP2].
    unfold Open. simpl. 
    constructor.
    - apply IHP1; assumption.
    - apply IHP2; assumption.
  + unfold Open in H0. simpl in H0. inversion H0.
    unfold Open. simpl. 
    simpl in H. destruct H as [HP1 [HP2 HP3]].
    apply Aux1 in H1. apply Aux1 in H3.
    apply IHP3 in H2.
    - destruct H1;
       destruct H3;
         rewrite <- H; rewrite <- H1; simpl; constructor; auto.
    - auto.
  + simpl in H.
    unfold Open in H0. simpl in H0. inversion H0.
    unfold Open. simpl. 
    apply Aux1 in H2. 
    destruct H2;
      rewrite <- H1; simpl; constructor.
  + unfold Open in H0. simpl in H0. inversion H0.
    unfold Open. simpl.
    simpl in H. destruct H as [HP1 HP2].
    apply Aux1 in H1.
    apply IHP2 in HP2.
    - destruct H1;
        rewrite <- H;
        simpl;
        constructor;
        assumption.
    - auto. 
  + admit. 
  + unfold Open in H0. simpl in H0. inversion H0.
    
 



 Theorem ProcessReduction_WD : 
forall P Q : PProcess, 
(P --> Q) -> Process(P)  -> Process(Q).
Proof.
  intros.
  induction H.
  + inversion H0.
    constructor. 
    - inversion H0.
      inversion H2.
      assumption.
    - 
*)
 

 
 
  
(*  
⊥
⊗
⅋
−∘
^⊥
*)
