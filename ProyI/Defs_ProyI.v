(*
  Verificación Formal - Unam 2020-2
  Ciro Iván García López
  Proyecto 1. Session Type Systems Verification
*) 
From Coq Require Import Strings.String.
From Coq Require Import Nat. 

 
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
Tercera aproximación a la mecanización de los procesos, se procede usando la idea de locally named representation
Se introducen FVAR y BVAR para denotar variables libres y ligadas 

Siguiendo las ideas de LNR se debe definir una nueva gramática que haga la distinción entre las variables libres y ligadas
*)
 
Inductive PProcess : Type  := 
  (*Definición de variables libres y ligadas*)
  | P_FVAR ( x : string) : PProcess
  | P_BVAR ( i : nat ) : PProcess 
  (* Ahora vienen los procesos bajo la nueva gramática *)
  | P_ZERO : PProcess 
  | P_FUSES ( P Q : PProcess ) : PProcess
  | P_PARALLEL_COMP ( P Q : PProcess ) : PProcess
  | P_CHAN_OUTPUT (P Q R : PProcess) : PProcess 
  | P_CHAN_ZERO ( P : PProcess ) : PProcess
  | P_CHAN_CLOSE ( P Q : PProcess) : PProcess 
  (*Cambian las definiciones para incluir las variables *)
  | P_CHAN_RES ( P : PProcess ) : PProcess
  | P_CHAN_INPUT (P Q: PProcess) : PProcess
  | P_CHAN_REPLICATE (P Q : PProcess) : PProcess.


(*
Desde la notación se pone el primer filtro para que los términos tengan el sentido deseado

Faltan las asociatividades y las prioridades 
*)
Notation "°" :=  P_ZERO.
Notation "[ x ←→ y ]" := ( P_FUSES (P_FVAR x) (P_FVAR y) ) (at level 50, left associativity).
(*Cambio la notación, no uso el | porque genera problemas en las definiciones Inductive *)
Notation "P ↓ Q" := (P_PARALLEL_COMP P Q)  (at level 55, left associativity).
Notation "x  « y »· P " :=  (P_CHAN_OUTPUT (P_FVAR x) (P_FVAR y) P )(at level 50, left associativity).
Notation "x «»·° " := (P_CHAN_ZERO (P_FVAR x))(at level 50, left associativity).
Notation "x ()· P" := (P_CHAN_CLOSE (P_FVAR x) P )(at level 50, left associativity).
Notation " 'ν' P " := (P_CHAN_RES P)(at level 50, left associativity).
Notation "x · P " := (P_CHAN_INPUT (P_FVAR x) P)(at level 50, left associativity).
Notation " x !· P " := (P_CHAN_REPLICATE (P_FVAR x) P)(at level 50, left associativity).

(*
Se necesitan las nociones de apertura y clausura de variables, por lo que se procede a definirlas apropiadamente. 

Se usa la misma notación del artículo de Charguéraud

Observe que es necesario definir la apertura para todos los terminos incluidos los basura 
*) 
Fixpoint Open_Rec (k : nat)( z : string )( T : PProcess ) {struct T} : PProcess := 
match T with
  | P_FVAR x => P_FVAR x
  | P_BVAR i => if ( k =? i ) then (P_FVAR z) else (P_BVAR i)
  (* Ahora vienen los procesos bajo la nueva gramática *)
  | P_ZERO => P_ZERO
  | P_FUSES P Q => P_FUSES (Open_Rec k z P) (Open_Rec k z Q)
  | P_PARALLEL_COMP P Q => P_PARALLEL_COMP (Open_Rec k z P) (Open_Rec k z Q)
  | P_CHAN_OUTPUT P Q R => P_CHAN_OUTPUT (Open_Rec k z P) (Open_Rec k z Q) (Open_Rec k z R)
  | P_CHAN_ZERO P => P_CHAN_ZERO (Open_Rec k z P)
  | P_CHAN_CLOSE P Q => P_CHAN_CLOSE (Open_Rec k z P) (Open_Rec k z Q)
  (*Cambian las definiciones para incluir las variables *)
  | P_CHAN_RES P => P_CHAN_RES (Open_Rec (S k) z P)
  | P_CHAN_INPUT P Q   => P_CHAN_INPUT (Open_Rec (S k) z P) (Open_Rec (S k) z Q ) 
  | P_CHAN_REPLICATE P Q  => P_CHAN_REPLICATE (Open_Rec (S k) z P) (Open_Rec (S k) z Q)
end.

Notation "{ k ~> z } P " := (Open_Rec k z P)(at level 60).

Definition Open P z := Open_Rec 0 z P.
Notation "P ^ z" := (Open P z).


(*
Y como también menciona el artículo de LNR, con la nueva gramática se introducen términos extraños 
que no hacian parte de la gramática original; por lo que se debe definir el predicado local closure 
que básicamente es tomar los términos que si nos sirven y descartar lo demás.

Se cambia un poco la perspectiva, se prefiere por el momento la definición usando un existencial y no el conjunto L y un universal 
*)
 
Inductive Process : PProcess -> Prop :=
  | ZERO : Process P_ZERO
  | FVAR : forall (x : string), Process ( P_FVAR x)
  | PARALLEL_COMP : forall (P Q : PProcess), Process(P) -> Process(Q)-> Process ( P_PARALLEL_COMP P Q )
  | FUSES : forall (x y : string), Process (P_FUSES (P_FVAR x) (P_FVAR y))
  | CHAN_ZERO : forall (x : string), Process ( P_CHAN_ZERO (P_FVAR x))
  | CHAN_CLOSE : forall (x : string) (P : PProcess), Process(P) -> Process ( P_CHAN_CLOSE (P_FVAR x) P)
  | CHAN_OUTPUT : forall (x y : string)(P : PProcess), (Process P) -> Process ( P_CHAN_OUTPUT (P_FVAR x) (P_FVAR y) P )
  | CHAN_RES : forall ( P :PProcess), (exists (z : string), Process (P ^ z)) -> Process (P_CHAN_RES P)
  | CHAN_INPUT : forall (x : string) ( P :PProcess), (exists (z : string), Process (P ^ z)) -> Process (P_CHAN_INPUT (P_FVAR x) P)
  | CHAN_REPLICATE : forall (x : string) ( P : PProcess), (exists (z : string), Process (P ^ z)) ->  Process (P_CHAN_REPLICATE (P_FVAR x) P).


(*
Llegados a este punto es necesario introducir las equivalencias de la definición 2.4, observe que usando NLR no es necesario hablar 
de alpha-equivalencia pero si es necesario introducir las equivalencias entre procesos. 

Observe que hay reglas que no tienen mucho significado bajo la relación de NLR


Observe que no uso explicitamente los constructores ya que la notación se encarga de que tenga sentido
*)
Definition Parallel_Zero ( P : PProcess ) := (P↓°) = P.
Definition Conmt_Parallel ( P Q : PProcess ) := (P↓Q) = (Q↓P).
Definition Res_Zero ( x : string ) := ( ν °)  = °.
Definition Asoc_Parallel ( P Q R : PProcess ) := ((P↓Q)↓R) = (Q↓(P↓R)).
Definition Conmt_Fuses ( x y : string ) := [x ←→ y] = [y ←→ x].
(*
para la última regla no se usa la condición que x no sea nombre libre en P puesto que no tiene sentido por LNR
en vez de ello se debe pedir que sea una expresión bien formada o sea un proceso
*)
Definition Abs_Restriction ( P Q : PProcess ) := Process(P) -> (P↓(ν Q)) = ν (Q↓P).


(*
Se introducen las reducciones de la definición 2.5

Los 'if' quedaron bastante feos, no entiendo porque no acepta el operador && para bool y el =? para cadenas

*)
Fixpoint Name_Substitution ( x y : string )( T : PProcess ) {struct T} : PProcess := 
match T with
  | P_FVAR z => if ( String.eqb x z ) then (P_FVAR y) else (P_FVAR z) 
  | P_BVAR i => P_BVAR i
  (* Ahora vienen los procesos bajo la nueva gramática *)
  | P_ZERO => P_ZERO
  | P_FUSES P Q => P_FUSES  (Name_Substitution x y P)  (Name_Substitution x y Q)
  | P_PARALLEL_COMP P Q => P_PARALLEL_COMP  (Name_Substitution x y P) (Name_Substitution x y Q)
  | P_CHAN_OUTPUT P Q R => P_CHAN_OUTPUT  (Name_Substitution x y P) (Name_Substitution x y Q)  (Name_Substitution x y R)
  | P_CHAN_ZERO P => P_CHAN_ZERO  (Name_Substitution x y P)
  | P_CHAN_CLOSE P Q => P_CHAN_CLOSE  (Name_Substitution x y P)  (Name_Substitution x y Q)
  (*Cambian las definiciones para incluir las variables *)
  | P_CHAN_RES P => P_CHAN_RES  (Name_Substitution x y P)
  | P_CHAN_INPUT P Q   => P_CHAN_INPUT  (Name_Substitution x y P)  (Name_Substitution x y Q)
  | P_CHAN_REPLICATE P Q  => P_CHAN_REPLICATE  (Name_Substitution x y P)  (Name_Substitution x y Q)
end.

Notation " { y \ x } P " := (Name_Substitution x y P) (at level 60). 



(*
Se define la noción de cerradura de un proceso bajo la restricción ν
Observe que a diferencia del artículo de NLR aquí hay 3 tipos de ligamiento y se debería definir por cada unor
una noción de cerradura diferente
*)
Fixpoint Close_Rec (k : nat)( z : string )( T : PProcess ) {struct T} : PProcess := 
match T with
  | P_FVAR x => if ( String.eqb x z ) then (P_BVAR k) else (P_FVAR x) 
  | P_BVAR i => P_BVAR i
  (* Ahora vienen los procesos bajo la nueva gramática *)
  | P_ZERO => P_ZERO
  | P_FUSES P Q => P_FUSES (Close_Rec k z P) (Close_Rec k z Q)
  | P_PARALLEL_COMP P Q => P_PARALLEL_COMP (Close_Rec k z P) (Close_Rec k z Q)
  | P_CHAN_OUTPUT P Q R => P_CHAN_OUTPUT (Close_Rec k z P) (Close_Rec k z Q) (Close_Rec k z R)
  | P_CHAN_ZERO P => P_CHAN_ZERO (Close_Rec k z P)
  | P_CHAN_CLOSE P Q => P_CHAN_CLOSE (Close_Rec k z P) (Close_Rec k z Q)
  (*Cambian las definiciones para incluir las variables *)
  | P_CHAN_RES P => P_CHAN_RES (Close_Rec (S k) z P)
  | P_CHAN_INPUT P Q   => P_CHAN_INPUT (Close_Rec (S k) z P) (Close_Rec (S k) z Q ) 
  | P_CHAN_REPLICATE P Q  => P_CHAN_REPLICATE (Close_Rec (S k) z P) (Close_Rec (S k) z Q)
end.

Notation "{ k ν<~ z } P " := (ν (Close_Rec k z P))(at level 60).

Definition Close_Restriction P z := ν (Close_Rec 0 z P).
Notation " z '/ν' P  " := (Close_Restriction P z)(at level 60).


Reserved Notation "R '-->' S" (at level 60).
Inductive ProcessReduction : PProcess -> PProcess -> Prop :=
  | Red_Comp_Input_Output : forall ( P Q : PProcess) (x y : string),
    ( (x « y »· P  ) ↓ ( x · Q ) ) --> ( P ↓ ( Q ^ y ) )

  | Red_Output_Replicate : forall ( P Q : PProcess) (x y : string), 
    ( (x « y »· P  ) ↓ (  x !· Q ) ) --> ( P ↓ ( Q ^ y ) ↓ (  x !· Q ))

  | Red_ChZero_ChClose : forall ( Q : PProcess) (x : string), 
    ( (x «»·° ) ↓ ( x ()· Q ) ) -->  Q

  | Red_Reduction_Parallel : forall ( P Q R : PProcess), 
    (P --> R) -> ((P ↓ Q ) --> (P ↓ R))
  
  | Red_Reduction_Restriction : forall ( P Q : PProcess) ( y : string), 
    (P --> Q) -> ( ( y /ν P ) --> ( y /ν Q ) )
  
(*   | Red_Process_Fuses : forall ( P : PProcess) (x y : string), 
    ( P ↓ ( [ x ←→ y] ) ) -->  P{y/x} *)

where "R '-->' S" := (ProcessReduction R S).
Hint Constructors ProcessReduction : core.


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

 

 
 
  
(*  
⊥
⊗
⅋
−∘
^⊥
*)
