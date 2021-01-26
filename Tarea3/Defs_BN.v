(*
Verificación Formal - 2020-II
Archivo de definiciones - Números por paridad
*)

(*Datatype for our numerical system with 0, U and D*)
Inductive BN :=
  Z: BN
| U: BN -> BN
| D: BN -> BN.

Check BN_ind.
Check BN_rec.
Check BN_rect.

(* Successor function for BN numbers  *)
Fixpoint sucBN (b:BN) : BN :=
  match b with
      Z => U Z
    | U x => D x (*S(U x) = S(2x + 1) = 2x + 2 = D x*)
    | D x => U (sucBN x) (*S(D x)= S(2x + 2) = S(S(2x + 1)) = S(2x + 1) + 1  *)
                 (* 2(S(x)) + 1 = 2(x+1) + 1 = (2x + 2) + 1 = S(2x + 1) + 1*)  
  end.


(* Predeccesor function with error *)

Parameter (undefBN: BN). (* we assume a constant undefBN:BN representing an undefined BN number *)

Fixpoint predBN (b:BN): BN :=
 match b with
  Z => undefBN
 |U Z => Z
 |U x => D (predBN x)
 |D x => U x
 end.


(* Conversion functions *)

(* Recursive function that converts a number of type BN
 to its respective natural number*)
Fixpoint toN (b:BN) : nat :=
  match b with 
      Z => 0
    | U x => 2*(toN x) + 1
    | D x => 2*(toN x) + 2
  end.


(* Converts a nat value to BN value. 
   Inverse of the above one.*)
Fixpoint toBN (n: nat) : BN :=
  match n with
      0 => Z
    | S x => sucBN (toBN x)
  end.

Eval compute in (toN (predBN (toBN 47))).

Eval compute in toN(D(U(U Z))).

Eval compute in toN(sucBN(D(U(U Z)))).

Eval compute in toBN 16.

(* Definition of sum of BN elements*)

Fixpoint plusBN (a b : BN) : BN :=
  match a,b with
    | Z, b => b
    | a, Z  => a
    | U x, U y => D(plusBN x y)
    | D x, U y => U(sucBN (plusBN x y))
    | U x, D y => U(sucBN (plusBN x y))
    | D x, D y => D(sucBN (plusBN x y))                
  end.

Notation "a ⊞ b" := (plusBN a b) (at level 60).



Inductive ltBN : BN -> BN -> Prop :=
 | ltBNZU : forall (a:BN), ltBN Z (U a)
 | ltBNZD : forall (a:BN), ltBN Z (D a)
 | ltBNUU : forall (a b:BN), ltBN a b -> ltBN (U a) (U b)
 | ltBNUDeq : forall (a :BN), ltBN (U a) (D a) 
 | ltBNUD : forall (a b:BN), ltBN a b -> ltBN (U a) (D b) 
 | ltBNDU : forall (a b:BN), ltBN a b -> ltBN (D a) (U b)
 | ltBNDD : forall (a b:BN), ltBN a b -> ltBN (D a) (D b).


Inductive lteqBN: BN -> BN -> Prop :=
 | lteqBNref: forall (a:BN), lteqBN a a
 | lteqBNl: forall (a b: BN), ltBN a b -> lteqBN a b.


Notation "a <BN b" := (ltBN a b) (at level 70).
Notation "a <BN b <BN c" := (ltBN a b /\ ltBN b c) (at level 70, b at next level).

Notation "a ≤BN b" := (lteqBN a b) (at level 70).














