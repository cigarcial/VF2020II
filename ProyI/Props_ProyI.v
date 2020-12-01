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


Proposition Doble_Duality_ULLT  : 
forall A : ULLType , 
(A^⊥)^⊥ = A. 
Proof.
  intros.
  induction A; auto. 
  - simpl. rewrite -> IHA1. rewrite -> IHA2. reflexivity.
  - simpl. rewrite -> IHA1. rewrite -> IHA2. reflexivity.
  - simpl. rewrite -> IHA. reflexivity. 
  - simpl. rewrite -> IHA. reflexivity. 
Qed.


Definition ULLT_IMP (A : ULLType) (B : ULLType) : ULLType := (A^⊥) ⅋ B.
Notation "A −∘ B" := (ULLT_IMP A B)(at level 50, left associativity).

Proposition Dual_Implication_Tensor : 
forall A B : ULLType , 
(A −∘ B)^⊥ = A ⊗ (B^⊥).
Proof.
  intros.
  unfold ULLT_IMP.
  simpl.
  rewrite -> (Doble_Duality_ULLT A).
  reflexivity.
Qed.

Proposition Dual_Tensor_Implication :  
forall A B : ULLType, 
(A ⊗ B )^⊥ = A −∘ (B^⊥).
Proof.
  intros.
  simpl.
  unfold ULLT_IMP.
  reflexivity.
Qed.

Proposition Doble_Dual_Implication : 
forall A B : ULLType, 
((A −∘ B)^⊥)^⊥ = A −∘ B.
Proof.
  intros.
  unfold ULLT_IMP.
  rewrite -> (Doble_Duality_ULLT).
  reflexivity.
Qed.




(*
⊥
⊗
⅋
−∘
^⊥
*)
