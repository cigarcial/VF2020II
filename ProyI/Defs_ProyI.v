(*
  Verificación Formal - Unam 2020-2
  Ciro Iván García López
  Proyecto 1. Session Type Systems Verification
*)
From Ltac2 Require Import Bool.
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

Hint Unfold Dual_ULLT : core.

Notation "A '^⊥'" := (Dual_ULLT A)(at level 50, left associativity).
Definition ULLT_IMP (A : ULLType) (B : ULLType) : ULLType := (A^⊥) ⅋ B.

Notation "A −∘ B" := (ULLT_IMP A B)(at level 50, left associativity).

(*
Segunda aproximación a la mecanización de los procesos, se procede usando la idea de locally named representation
Se introducen FVAR y BVAR para denotar variables libres y ligadas 

Siguiendo las ideas de LNR se debe definir una nueva gramática que haga la distinción entre las variables libres y ligadas
*)
 
Inductive PProcess : Type  := 
  | P_ZERO : PProcess 
  | P_FUSES ( x : string ) ( y : string ) : PProcess
  | P_PARALLEL_COMP ( P Q : PProcess ) : PProcess
  | P_CHAN_OUTPUT (x y : string) (P : PProcess) : PProcess 
  | P_CHAN_ZERO ( x : string) : PProcess 
  | P_CHAN_CLOSE ( x : string) ( P : PProcess) : PProcess 
  (*Definición de variables libres y ligadas*)
  | P_FVAR ( x : string) : PProcess
  | P_BVAR ( i : nat ) : PProcess 
  (*Cambian las definiciones para incluir las variables *)
  | P_CHAN_RES ( P : PProcess ) : PProcess
  | P_CHAN_INPUT (x : string) (P : PProcess) : PProcess
  | P_CHAN_REPLICATE (x : string)(P : PProcess) : PProcess.


(*
Faltan las asociatividades y las prioridades 
*)
Notation "°" :=  P_ZERO.
Notation "[ x ←→ y ]" := (P_FUSES x y) (at level 50, left associativity).
(*Cambio la notación, no uso el | porque genera problemas en las definiciones Inductive *)
Notation "P ↓ Q" := (P_PARALLEL_COMP P Q)  (at level 55, left associativity).
Notation "x  « y »· P " :=  (P_CHAN_OUTPUT x y P )(at level 50, left associativity).
Notation "x «»·° " := (P_CHAN_ZERO x )(at level 50, left associativity).
Notation "x ()· P" := (P_CHAN_CLOSE x P )(at level 50, left associativity).
Notation " 'ν' P " := (P_CHAN_RES P)(at level 50, left associativity).
Notation "x · P " := (P_CHAN_INPUT x P)(at level 50, left associativity).
Notation " x !· P " := (P_CHAN_REPLICATE x P)(at level 50, left associativity).

(*
Se necesitan las nociones de apertura y clausura de variables, por lo que se procede a definirlas apropiadamente. 

Se usa la misma notación del artículo de Charguéraud
*)
Fixpoint Open_Rec (k : nat)( z : string )( T : PProcess ) {struct T} : PProcess := 
match T with
  | ° => °
  | [x ←→ y] => [x ←→ y]
  | P ↓ Q  => (Open_Rec k z P) ↓ (Open_Rec k z Q) 
  | x « y »· P => x «y»· (Open_Rec k z P) 
  | x «»·° => x «»·°
  | x ()· P => x ()· (Open_Rec k z P) 
  | P_FVAR x => P_FVAR x 
  | P_BVAR i => if ( k =? i ) then (P_FVAR z) else (P_BVAR i)
  | ν P => ν (Open_Rec (S k) z P) 
  | x · P => x · (Open_Rec (S k) z P) 
  | x !· P =>  x !· (Open_Rec (S k) z P) 
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
  | FUSES : forall (x y : string), Process (P_FUSES x y)
  | PARALLEL_COMP : forall (P Q : PProcess), Process(P) -> Process(Q)-> Process ( P_PARALLEL_COMP P Q )
  | CHAN_OUTPUT : forall (x y : string)(P : PProcess), (Process P) -> Process ( P_CHAN_OUTPUT x y P)
  | CHAN_ZERO : forall (x : string), Process ( P_CHAN_ZERO x)
  | CHAN_CLOSE : forall (x : string) (P : PProcess), Process(P) -> Process ( P_CHAN_CLOSE x P)
  | FVAR : forall (x : string), Process ( P_FVAR x)
  | CHAN_RES : forall ( P :PProcess), (exists (z : string), Process (P ^ z)) -> Process (P_CHAN_RES  P)
  | CHAN_INPUT : forall (x : string) ( P :PProcess), (exists (z : string), Process (P ^ z)) -> Process (P_CHAN_INPUT x P)
  | CHAN_REPLICATE : forall (x : string) ( P : PProcess), (exists (z : string), Process (P ^ z)) ->  Process (P_CHAN_REPLICATE x P).


(*
Llegados a este punto es necesario introducir las equivalencias de la definición 2.4, observe que usando NLR no es necesario hablar 
de alpha-equivalencia pero si es necesario introducir las equivalencias entre procesos. 

Observe que hay reglas que no tienen mucho significado bajo la relación de NLR
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
  | ° => °
  | [z ←→ w] => if ( andb (String.eqb z x) (String.eqb w x) ) then [y ←→ y]  
                else if String.eqb z x then [y ←→ w]
                else if String.eqb w x then [z ←→ y]
                else [z ←→ w]
                
  | P ↓ Q  => (Name_Substitution x y P) ↓ (Name_Substitution x y Q)
                
  | z « w »· P => if ( andb (String.eqb z x) (String.eqb w x )) then  y « y »· (Name_Substitution x y P)
                  else if String.eqb z x then  y « w »· (Name_Substitution x y P)
                  else if String.eqb w x then  z « y »· (Name_Substitution x y P)
                  else  z « w »· (Name_Substitution x y P)
                
  | z «»·° => if String.eqb z x then y «»·°
              else z «»·°
                
  | z ()· P => if String.eqb z x then y ()· (Name_Substitution x y P)
               else z ()· (Name_Substitution x y P)
               
  | P_FVAR z => if String.eqb z x then P_FVAR y
                else P_FVAR z
                
  | P_BVAR i => P_BVAR i
  
  | ν P => ν (Name_Substitution x y P)
           
  | z · P => if String.eqb z x then y · (Name_Substitution x y P)
             else z · (Name_Substitution x y P)
             
  | z !· P =>  if String.eqb z x then y · (Name_Substitution x y P)
               else z · (Name_Substitution x y P)

end.

Notation " P { y / x } " := ( Name_Substitution x y P) (at level 60). 


(*
Se define la noción de cerradura de un proceso bajo la restricción ν
Observe que a diferencia del artículo de NLR aquí hay 3 tipos de ligamiento y se debería definir por cada unor
una noción de cerradura diferente
*)
Fixpoint Close_Rec (k : nat)( z : string )( T : PProcess ) {struct T} : PProcess := 
match T with
  | ° => °
  | [x ←→ y] => [x ←→ y]
  | P ↓ Q  => (Close_Rec k z P) ↓ (Close_Rec k z Q) 
  | x « y »· P => x «y»· (Close_Rec k z P) 
  | x «»·° => x «»·°
  | x ()· P => x ()· (Close_Rec k z P) 
  | P_FVAR x =>  if ( String.eqb x z ) then (P_BVAR k) else (P_FVAR x) 
  | P_BVAR i => P_BVAR i
  | ν P => ν (Close_Rec (S k) z P) 
  | x · P => x · (Close_Rec (S k) z P) 
  | x !· P =>  x !· (Close_Rec (S k) z P) 
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



(*
⊥
⊗
⅋
−∘
^⊥
*)
