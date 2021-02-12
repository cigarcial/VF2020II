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
  | Preoutput x y P => Preoutput (Open_Name k z x) (Open_Name k z y) (Open_Rec k z P)
  | Prechan_zero x => Prechan_zero (Open_Name k z x)
  | Prechan_close x P => Prechan_close (Open_Name k z x) (Open_Rec k z P)
  | Prechan_res P => Prechan_res (Open_Rec (S k) z P)
  | Prechan_input x P => Prechan_input (Open_Name k z x) (Open_Rec (S k) z P)
  | Prechan_replicate x P => Prechan_replicate (Open_Name k z x) (Open_Rec (S k) z P)
end.
Notation "{ k ~> z } P " := (Open_Rec k z P)(at level 60).


Definition Open ( z : Name )( T : Prepro ): Prepro := 
match T with 
  | Prechan_res P => Open_Rec 0 z P
  | Prechan_input x P => Open_Rec 0 z P
  | Prechan_replicate x P  => Open_Rec 0 z P
  | T => T
end.
Notation "P ^ z" := (Open z P).

