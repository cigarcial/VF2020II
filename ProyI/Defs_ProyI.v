(*
  Verificación Formal - Unam 2020-2
  Ciro Iván García López
  Proyecto 1. Session Type Systems Verification
*)
From Coq Require Import Strings.String.  

Inductive ULLType : Type := 
  | ONE : ULLType
  | ABS : ULLType
  | TEN (A : ULLType) (B : ULLType) : ULLType
  | PAR (A : ULLType) (B : ULLType) : ULLType
(*   | ULLT_IMP (A : ULLType) (B : ULLType) : ULLType  *)
  | EXP (A : ULLType) : ULLType
  | MOD (A : ULLType) : ULLType.
  

(*
Validación del tipo definido para ULLT_EXP
*)
Check EXP.

(*
Notación de acuerdo al artículo, sin embargo falta definir bien los niveles y la asociatividad 	
*)
Notation "¶" := ONE.
Notation "⊥" := ABS.
Notation "A ⊗ B" := (TEN A B)(at level 50, left associativity).
Notation "A ⅋ B" := (PAR A B)(at level 50, left associativity).
(* Notation "A −∘ B" := (ULLT_IMP A B)(at level 50, left associativity). *)
Notation "! A" := (EXP A)(at level 50, left associativity).
Notation "? A" := (MOD A)(at level 50, left associativity).

Fixpoint Dual_ULLT ( T : ULLType ) : ULLType := 
match T with 
  | ¶ => ⊥
  | ⊥ => ¶
  | A ⊗ B => (Dual_ULLT A) ⅋ (Dual_ULLT B)
  | A ⅋ B => (Dual_ULLT A) ⊗ (Dual_ULLT B)
  | ! A => ? (Dual_ULLT A)
  | ? A => ! (Dual_ULLT A)
end.

Notation "A '^⊥'" := (Dual_ULLT A)(at level 50, left associativity).
Definition ULLT_IMP (A : ULLType) (B : ULLType) : ULLType := (A^⊥) ⅋ B.

Notation "A −∘ B" := (ULLT_IMP A B)(at level 50, left associativity).

(*
Primera aproximación a la mecanización de los procesos, un poco timida e inocente
Se tiene que esta notación introduce el problema de la alpha-equivalencia 
*)
Inductive Process : Type  := 
  | ZERO : Process 
  | FUSES ( x : string ) ( y : string ) : Process
  | CHAN_RES (x : string ) ( P : Process ) : Process 
  | PARALLEL_COMP ( P Q : Process ) : Process
  | CHAN_OUTPUT (X Y : string) (P : Process) : Process 
  | CHAN_INPUT (X Y : string) (P : Process ) : Process 
  | CHAN_REPLICATE ( X Y : string  )(P : Process ) : Process 
  | CHAN_ZERO ( X : string) : Process 
  | CHAN_CLOSE ( X : string) : Process.



(*
⊥
⊗
⅋
−∘
^⊥
*)
