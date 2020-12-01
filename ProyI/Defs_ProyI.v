(*
  Verificación Formal - Unam 2020-2
  Ciro Iván García López
  Proyecto 1. Session Type Systems Verification
*)

Inductive ULLType : Type := 
  | ULLT_ONE : ULLType
  | ULLT_ABS : ULLType
  | ULLT_TEN (A : ULLType) (B : ULLType) : ULLType
  | ULLT_PAR (A : ULLType) (B : ULLType) : ULLType
(*   | ULLT_IMP (A : ULLType) (B : ULLType) : ULLType  *)
  | ULLT_MOD (A : ULLType) : ULLType
  | ULLT_EXP (A : ULLType) : ULLType.

(*
Validación del tipo definido para ULLT_EXP
*)
Check ULLT_EXP.

(*
Notación de acuerdo al artículo, sin embargo falta definir bien los niveles y la asociatividad 	
*)
Notation "¶" := ULLT_ONE.
Notation "⊥" := ULLT_ABS.
Notation "A ⊗ B" := (ULLT_TEN A B)(at level 50, left associativity).
Notation "A ⅋ B" := (ULLT_PAR A B)(at level 50, left associativity).
(* Notation "A −∘ B" := (ULLT_IMP A B)(at level 50, left associativity). *)
Notation "! A" := (ULLT_MOD A)(at level 50, left associativity).
Notation "? A" := (ULLT_EXP A)(at level 50, left associativity).

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
⊥
⊗
⅋
−∘
^⊥
*)
