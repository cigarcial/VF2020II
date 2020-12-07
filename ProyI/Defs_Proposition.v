(*
  Verificación Formal - Unam 2020-2
  Ciro Iván García López 
  Proyecto 1. Session Type Systems Verification
*)

Inductive Proposition : Type := 
  | ONE : Proposition
  | ABS : Proposition
  | TEN (A : Proposition) (B : Proposition) : Proposition
  | PAR (A : Proposition) (B : Proposition) : Proposition
(*   | ULLT_IMP (A : ULLType) (B : ULLType) : ULLType  *)
  | EXP (A : Proposition) : Proposition
  | MOD (A : Proposition) : Proposition.

Hint Constructors Proposition : core.

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


Fixpoint Dual_prop ( T : Proposition ) : Proposition := 
match T with 
  | ¶ => ⊥
  | ⊥ => ¶
  | A ⊗ B => (Dual_prop A) ⅋ (Dual_prop B)
  | A ⅋ B => (Dual_prop A) ⊗ (Dual_prop B)
  | ! A => ? (Dual_prop A)
  | ? A => ! (Dual_prop A)
end.

Hint Unfold Dual_prop : core.

Notation "A '^⊥'" := (Dual_prop A)(at level 60, right associativity).
Definition ULLT_IMP (A : Proposition) (B : Proposition) : Proposition := (A^⊥) ⅋ B.

Notation "A −∘ B" := (ULLT_IMP A B)(at level 70, right associativity).

(*
⊥
⊗
⅋
−∘
^⊥
*)
