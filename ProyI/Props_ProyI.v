(*
  Verificación Formal - Unam 2020-2
  Ciro Iván García López
  Proyecto 1. Session Type Systems Verification
*)

From Coq Require Import Strings.String.
From PROYI Require Import  Defs_ProyI.


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

Proposition Dual_Implication_Tensor : 
forall A B : ULLType , 
((A −∘ B)^⊥) = (A ⊗ (B^⊥)).
Proof.
  intros.
  unfold ULLT_IMP.
  simpl.
  rewrite -> (Doble_Duality_ULLT A).
  reflexivity.
Qed.

Proposition Dual_Tensor_Implication :  
forall A B : ULLType, 
((A ⊗ B )^⊥) = (A −∘ (B^⊥)).
Proof.
  intros.
  simpl.
  unfold ULLT_IMP.
  reflexivity.
Qed.

Proposition Doble_Dual_Implication : 
forall A B : ULLType, 
(((A −∘ B)^⊥)^⊥) = (A −∘ B).
Proof.
  intros.
  unfold ULLT_IMP.
  rewrite -> (Doble_Duality_ULLT).
  reflexivity.
Qed.


(*
En las definiciones se encuentran las equivalencias de la definición 2.4, sin embargo es necesario indicar que son 'coherentes'
dichas equivalencias. Es decir, si partimos de un proceso obtenemos un proceso.
*)




Lemma Process_IsFreeFor : 
forall ( x : string )( P : PProcess ), 
Process P -> 


(*
Para la definición 2.5 bajo la mirada de NLR es necesario probar que de procesos se obtienen procesos
*)

Theorem ProcessReduction_WD : 
forall P Q : PProcess, 
(P --> Q) -> Process(P)  -> Process(Q).
Proof.






(*
⊥
⊗
⅋
−∘
^⊥
*)
