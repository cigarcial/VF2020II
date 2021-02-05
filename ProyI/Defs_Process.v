(*
  Verificación Formal - Unam 2020-2
  Ciro Iván García López
  Proyecto 1. Session Type Systems Verification
*)
From Coq Require Import Strings.String.
From Coq Require Import Nat.
From Coq Require Import Lists.List.
From PROYI Require Import  Defs_Proposition.


(*
Cuarta aproximación a la mecanización de los procesos usando las nocinoes de 'locally named representation'.

FVAR y BVAR representan la idea de variable libre y ligada, respectivamente. 

Para esta parte se usa como base las ideas expuestas en el artículo de Castro Engineering The Meta-Theory of Session Types

Definición 2.3, por un lado se representan las variables y por el otro los procesos. 
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
Las nuevas ideas son más simples ya que reducen los términos no deseados.

La notación cambia bastante, no se fija el tipo de nombre por defecto

Asociatividad y prioridades de acuerdo a lo expuesto en Sangiorgi - The Pi Calculus. 
*)
Notation "°" :=  Prezero.
Notation "[ x ←→ y ]" := (Prefuse x y ) ( at level 60).
(*
Cambio la notación respecto al artículo, no uso el | porque genera problemas en las definiciones Inductive
*)
Notation "P ↓ Q" :=  (Preparallel P Q ) ( at level 60).
Notation "x  « y »· P " := (Preoutput x y P ) (at level 60).
Notation "x «»·° " :=  (Prechan_zero x ) (at level 60).
Notation "x ()· P" := (Prechan_close x P)(at level 60).
(*
Procesos con variables ligadas
*)
Notation " 'ν' P " := (Prechan_res P ) ( at level 60).
Notation "x · P " := (Prechan_input x P)(at level 60).
Notation " x !· P " :=  (Prechan_replicate x P)(at level 60).


(*
Se necesitan las nociones de apertura y clausura de preprocesos, por lo que se procede a definirlas apropiadamente.

Se usa la misma notación del artículo de Charguéraud

Se necesita ahora distinguir dos aperturas uno para preprocesos y otra para los nombres.
*) 
Definition Open_Name ( k : nat )(z N : Name ) : Name := 
match N with 
  | FName x => FName x
  | BName i => if ( k =? i ) then z else (BName i)
end.


(*
Apertura para los preprocesos
*)
Fixpoint Open_Rec (k : nat)( z : Name )( T : Prepro ) {struct T} : Prepro := 
match T with
  | Prezero => Prezero
  | Prefuse x y => Prefuse (Open_Name k z x ) (Open_Name k z y )
  | Preparallel P Q => Preparallel (Open_Rec k z P) (Open_Rec k z Q)
  | Preoutput x y P => Preoutput (Open_Name k z x) (Open_Name k z y) (Open_Rec k z P) \/
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
De manera análoga se necesitan dos cerraduras; una para nombres y otra para preprocesos.
*)
Definition Close_Name ( k : nat )( z N : Name ) : Name := 
match N with
  | FName n0 => match z with 
                  | FName x0 => if String.eqb n0 x0 then BName k else N
                  | BName i0 => N
                end
  | BName i => N
end. 


(*
Cerradura de preprocesos bajo la nueva gramática
*)
Fixpoint Close_Rec (k : nat)( z : Name )( T : Prepro ) {struct T} : Prepro := 
match T with
  | Prezero => Prezero
  | Prefuse x y => Prefuse (Close_Name k z x ) (Close_Name k z y )
  | Preparallel P Q => Preparallel (Close_Rec k z P) (Close_Rec k z Q)
  | Preoutput x y P => Preoutput (Close_Name k z x) (Close_Name k z y) (Close_Rec k z P) 
  | Prechan_zero x => Prechan_zero (Close_Name k z x)
  | Prechan_close x P => Prechan_close (Close_Name k z x) (Close_Rec k z P)
  | Prechan_res P => Prechan_res (Close_Rec (S k) z P)
  | Prechan_input x P => Prechan_input (Close_Name k z x) (Close_Rec (S k) z P)
  | Prechan_replicate x P => Prechan_replicate (Close_Name k z x) (Close_Rec (S k) z P)
end.


(*
Tal como indica Charguéraud, no todo preproceso resulta ser un proceso bien formado, por lo que se necesita distinguir de aquellos que corresponden con procesos (en el sentido de la definición 2.3) de aquellos que no tienen 'sentido'.

Nuevamente, se parte de la definición para nombres y posteriormente para preprocesos.
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
    Process_Name x -> Process_Name y -> Process P -> Process ( x «y»· P)
  
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
Concepto de Body, presente en el artículo de Charguéraud. Es el concepto clave para determinar los procesos bien formados bajo la presencia de una variable ligada.

Intuitivamente una expresión es un body si al tomar una variable libre y remplazar la ocurrencia de la primera ligada, es un término bien formado. Es decir, solo aparece un nombre ligado que no tiene ligadura. 
*)
Definition Body (P  : Prepro) := forall (x : Name)(L : list Name), ~ (In x L) -> Process (P ^ x).


(*
Sustitución de nombres, observe que bajo LNR no tiene sentido la sustitución de nombres ligados.
*)
Definition Subst_Name ( x y N : Name ) : Name :=
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
  | Prefuse u v => Prefuse (Subst_Name x y u ) (Subst_Name x y v)
  | Preparallel P Q => Preparallel (Subst x y P) (Subst x y Q)
  | Preoutput u v P => Preoutput (Subst_Name x y u) (Subst_Name x y v) (Subst x y P)
  | Prechan_zero u => Prechan_zero (Subst_Name x y u )
  | Prechan_close u P => Prechan_close (Subst_Name x y u) (Subst x y P)
  (* preprocesos con variables ligadas *)
  | Prechan_res P => Prechan_res (Subst x y P)
  | Prechan_input u P  => Prechan_input (Subst_Name x y u) (Subst x y P)
  | Prechan_replicate u P =>  Prechan_replicate (Subst_Name x y u) (Subst x y P)
end.
Notation " { y \ x } P " := (Subst x y P) (at level 60). 


(*
Definición 2.4, equivalencias entre términos, observe que usando NLR no es necesario hablar de alpha-equivalencia pero si es necesario introducir las equivalencias entre procesos.
*)
Reserved Notation "R '===' S" (at level 60).
Inductive Congruence : Prepro -> Prepro -> Prop :=
    | Con_parallel_zero : forall (P : Prepro),
        Process P -> (P↓°) === P
      
    | Con_conmt_parallel : forall (P Q : Prepro),
        Process P -> Process Q -> (P↓Q) === (Q↓P)
      
    | Con_res_zero : ( ν °)  === °
      
    | Con_asoc_parallel : forall (P Q R : Prepro),
        Process P -> Process Q -> Process R -> ((P↓Q)↓R) === (P↓(Q↓R))
      
    | Con_conmt_fuses : forall (x y : Name),
        Process_Name x -> Process_Name y -> [x ←→ y] === [y ←→ x]
      
     | Con_abs_restriction : forall (P Q : Prepro),
        Process P -> Body Q -> (P↓(ν Q)) === ν (P↓Q)
        
     | Con_subst : forall (x y : Name) (P : Prepro), 
        Process P -> ( P === ({y \ x} P))
        
where "R '===' S" := (Congruence R S).
Hint Constructors Congruence : core.


(*
Definición 2.5, reducciones. Observe que la última reducción queda congelada, esto debido a que no ha sido posible reconciliar Coq (genera argumentos circulares) con la prueba en papel.
*)
Reserved Notation "R '-->' S" (at level 60).
Inductive Reduction : Prepro -> Prepro -> Prop :=

  | Red_output_input : forall ( x y : Name ) ( P Q : Prepro ), 
    Process P -> Body Q -> (exists (L : list Name) , ~( In y L ) ) -> 
    (( (x « y »· P)  ↓ (x · Q) ) --> (P ↓ (Q ^ y )) )

  | Red_parallel_replicate : forall (x y : Name) (P Q : Prepro),
    Process P -> Body Q -> (exists (L : list Name) , ~( In y L ) ) -> 
      (( (x « y »· P) ↓ (x !· Q )  ) --> ( P ↓ Q^y ↓ (x !· Q) ))

  | Red_chzero_chclose : forall ( Q : Prepro) (x : Name), 
     Process ( x «»·° ) -> Process ( x ()· Q  ) -> 
     ( ( ( x «»·° ) ↓ ( x ()· Q ) ) -->  Q )

  | Red_parallel_fuse : forall ( x y : Name) ( P : Prepro),
    Process P -> ( (P ↓ [x←→y]) --> 
    (Subst x y P) )

  | Red_reduction_parallel : forall ( P Q R : Prepro), 
    Process R -> Process Q -> Process R -> ((Q --> R) -> ((P ↓ Q ) --> (P ↓ R)))

  | Red_reduction_chanres : forall (P Q : Prepro)( x : Name), 
    Process P -> Process Q -> Process_Name x -> 
    ( P --> Q ) -> ( ν (Close_Rec 0 x P) --> ν (Close_Rec 0 x Q) )
(*
  | Red_reduction_congruence : forall ( P Q P' Q' : Prepro ), 
    Process P -> Process Q -> Process P' -> Process Q' 
    -> Congruence P P' -> Congruence Q Q' -> (P' --> Q') -> 
    P --> Q
*)
where "R '-->' S" := (Reduction R S).
Hint Constructors Reduction : core.