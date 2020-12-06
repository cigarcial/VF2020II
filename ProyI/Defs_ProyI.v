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

Definition Open_Name ( k : nat )(z N : Name ) : Name := 
match N with 
  | FName x => FName x
  | BName i => if ( k =? i ) then z else (BName i)
end. 

(* Ahora la apertura de preprocesos bajo la nueva gramática *)
Fixpoint Open_Rec (k : nat)( z : Name )( T : Prepro ) {struct T} : Prepro := 
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
  
  | Chan_res : forall (P : Prepro)(L : list Name), 
    ( forall (x : Name), ~ (In x L) -> Process (P ^ x) ) -> Process (ν P)
  
  | Chan_input : forall (x : Name ) (P: Prepro)(L : list Name),
    Process_Name x -> ( forall (x : Name), ~ (In x L) -> Process (P ^ x) ) -> Process ( x · P)
   
  | Chan_replicate : forall (x : Name) (P : Prepro)(L : list Name),
    Process_Name x -> ( forall (x : Name), ~ (In x L) -> Process (P ^ x) ) -> Process ( x !· P ).
Hint Constructors Process : core.


(*
Llegados a este punto es necesario introducir las equivalencias de la definición 2.4, observe que usando NLR no es necesario hablar 
de alpha-equivalencia pero si es necesario introducir las equivalencias entre procesos. 
*)



(*
Se introducen las reducciones de la definición 2.5

Los 'if' quedaron bastante feos, no entiendo porque no acepta el operador && para bool y el =? para cadenas

Bajo la nueva mirada es necesario definir una sustitución para nombres {y/x}

*)

Definition Subst_name ( x y N : Name ) : Name :=
match N with 
  | FName n0 => match x with 
                  | FName x0 => if String.eqb n0 x0 then y else N
                  | BName i0 => N
                end
  | BName i => N
end.

Fixpoint Subst ( x y : Name )( T : Prepro ) {struct T} : Prepro := 
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

 
Definition Body (P  : Prepro) := forall (x : Name)(L : list Name), ~ (In x L) -> Process (P ^ x).

(*
  La hipotesis adicional es un mecanizar la idea que todas las sustituciones no involucran variables libres o ligadas
*)
Reserved Notation "R '-->' S" (at level 60).
Inductive Reduction : Prepro -> Prepro -> Prop :=

  | Red_output_input : forall ( x y : Name ) ( P Q : Prepro ), 
    Process P -> Body Q -> (exists (L : list Name) , ~( In y L ) ) -> (( (x « y »· P)  ↓ (x · Q) ) --> (P ↓ (Q ^ y )) )

  | Red_parallel_replicate : forall (x y : Name) (P Q : Prepro),
    Process P -> Body Q -> (exists (L : list Name) , ~( In y L ) ) -> 
      (( (x « y »· P) ↓ (x !· Q )  ) --> ( P ↓ Q^y ↓ (x !· Q) ))

  | Red_chzero_chclose : forall ( Q : Prepro) (x : Name), 
     Process ( x «»·° ) -> Process ( x ()· Q  ) -> ( ( ( x «»·° ) ↓ ( x ()· Q ) ) -->  Q )

  | Red_parallel_fuse : forall ( x y : Name) ( P : Prepro),
    Process P -> ( (P ↓ [x←→y]) --> (Subst x y P) )

  | Red_reduction_parallel : forall ( P Q R : Prepro), 
    Process R -> Process Q -> Process R -> ((P --> R) -> ((P ↓ Q ) --> (P ↓ R)))
  
where "R '-->' S" := (Reduction R S).
Hint Constructors Reduction : core.


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


Definition Parallel_Zero ( P : Prepro ) := (P↓°) = P.
Definition Conmt_Parallel ( P Q : Prepro ) := (P↓Q) = (Q↓P).
Definition Res_Zero := ( ν °)  = °.
Definition Asoc_Parallel ( P Q R : Prepro ) := ((P↓Q)↓R) = (P↓(Q↓R)).
Definition Conmt_Fuses ( x y : Name ) := [x ←→ y] = [y ←→ x].
Definition Abs_Restriction ( P Q : Prepro ) := Process(P) -> (P↓(ν Q)) = ν (Q↓P).





(*
⊥
⊗
⅋
−∘
^⊥
*)
