(*
  Verificación Formal - Unam 2020-2
  Ciro Iván García López
  Proyecto 1. Session Type Systems Verification
*)
From Coq Require Import Lists.List.
Import ListNotations.
From PROYI Require Import  Defs_Proposition.
From PROYI Require Import  Defs_Process.

Inductive Assignment : Type := assig ( x : Name )( A : Proposition ) : Assignment.

Notation " x : A " := (assig x A )(at level 60).

Inductive Assig : Assignment -> Prop :=
  is_assig :  forall (x : Name)(A:Proposition), Process_Name x -> Assig ( x : A).

Inductive Collec : list Assignment -> Prop := is_collect :forall L : list Assignment,
  (forall H : Assignment, (In H L) -> Assig H ) -> Collec L.

Reserved Notation "D ';;;'  F '!-' P ':::' G" (at level 60).
Inductive Inference : list Assignment -> list Assignment -> list Assignment -> Prepro -> Prop := 
  | idr : forall (D : list Assignment) (x y : Name) ( A : Proposition),
    Collec D -> Process_Name x -> Process_Name y -> 
    ( D ;;; ( cons (x:A) nil ) !- ([x←→y]) ::: [ (y:A) ]  )


  | idl : forall (D : list Assignment)(x y : Name)(A : Proposition),
    Collec D -> Process_Name x -> Process_Name y -> 
    ( D ;;; ( (cons (x:A) nil) ++ (cons (x:(A^⊥)) nil) )  !-  ([x←→y]) ::: []  )


  | repr : forall ( D : list Assignment ) ( x y : Name)( A : Proposition )( P : Prepro ), 
    Collec D -> Process_Name y -> Process_Name x -> Process P ->
    ( D ;;; nil !- P ::: [ (y:A) ] ) -> 
    ( D ;;; nil !- (x !· (Close_Rec 0 y P) ) ::: [ (x:!A)  ] )


  | repl : forall ( D F G : list Assignment ) ( u x : Name)( A : Proposition)(P : Prepro ),
    Collec D -> Collec F -> Collec G -> Process_Name u -> Process_Name x -> Process P -> 
    ( D ;;; ( (cons (u:A) nil) ++ F) !- P ::: G ) -> 
    ( D ;;; ( (cons (x:!A) nil) ++ F) !- ({x \ u }P) ::: G)


  | conr : forall ( D F G : list Assignment ) ( u x : Name)( A : Proposition)(P : Prepro ),
    Collec D -> Collec G -> Collec F -> Process_Name u -> Process_Name x -> Process P -> 
    ( D ;;; ( (cons (u:A) nil) ++ F) !- P ::: G ) -> 
    ( D ;;; F !- ({x \ u }P) ::: ( ( cons (x: (? (A ^⊥) )) nil ) ++ G) )


  | conl : forall ( D : list Assignment ) ( y x : Name)( A : Proposition)(P : Prepro ),
    Collec D -> Process_Name y -> Process_Name x -> Process P -> 
    ( D ;;; (cons (y:A) nil) !- P ::: nil ) -> 
    ( D ;;; (cons (x:? A) nil) !- ( x !· (Close_Rec 0  y P)) ::: nil)


  | recr : forall ( D F G: list Assignment ) ( y x : Name)( A B : Proposition)(P : Prepro ),
    Collec D -> Collec F -> Collec G -> Process_Name x -> Process_Name y -> Process P -> 
    ( D ;;; ( (cons (y:A) nil) ++ F) !- P ::: ( (cons (x:B) nil) ++ G ) ) -> 
    ( D ;;; F !- (x · (Close_Rec 0 y P)) ::: ((cons (x:(A−∘B) ) nil) ++ G ) )


  | recl : forall ( D F G F' G': list Assignment ) ( y x : Name)( A B : Proposition)(P Q: Prepro ),
    Collec D -> Collec F -> Collec G -> Collec F' -> Collec G' -> Process_Name x -> Process_Name y -> Process P  -> Process Q -> 
    ( D ;;; F !- P ::: ( (cons (y:A) nil) ++ G ) ) ->
    ( D ;;; ((cons (x:B) nil) ++ F') !- Q ::: G' ) ->
    ( D ;;; ((cons (x:(A−∘B) ) nil) ++ (F ++ F')) !- (ν (Close_Rec 0 y (x « y »· (P↓Q)))) ::: ( G ++ G') )


  | reccr : forall ( D F G: list Assignment ) ( y x : Name)( A B : Proposition)(P : Prepro ),
    Collec D -> Collec F -> Collec G -> Process_Name x -> Process_Name y -> Process P -> 
    ( D ;;; F !- P ::: ( (cons (x:B) (cons (y:A) nil) ) ++ G ) ) -> 
    ( D ;;; F !- (x · (Close_Rec 0 y P)) ::: ((cons (x:(A⅋B) ) nil) ++ G ) )


  | reccl  : forall ( D F G F' G': list Assignment ) ( y x : Name)( A B : Proposition)(P Q: Prepro ),
    Collec D -> Collec F -> Collec G -> Collec F' -> Collec G' -> Process_Name x -> Process_Name y -> Process P  -> Process Q -> 
    ( D ;;; ( (cons (y:A) nil) ++ F ) !- P ::: G ) ->
    ( D ;;; ((cons (x:B) nil) ++ F') !- Q ::: G' ) ->
    ( D ;;; ((cons (x:(A⅋B) ) nil) ++ (F ++ F')) !- (ν (Close_Rec 0 y (x « y »· (P↓Q)))) ::: ( G ++ G') )
    
    
  | senl : forall ( D F G: list Assignment ) ( y x : Name)( A B : Proposition)(P : Prepro ),
    Collec D -> Collec F -> Collec G -> Process_Name x -> Process_Name y -> Process P -> 
    ( D ;;; ( (cons (x:B) (cons (y:A) nil) ) ++ F) !- P ::: G ) -> 
    ( D ;;; ( (cons (x:(A⊗B) ) nil) ++ F) !- (x · (Close_Rec 0 y P)) ::: G )


  | senr  : forall ( D F G F' G': list Assignment ) ( y x : Name)( A B : Proposition)(P Q: Prepro ),
    Collec D -> Collec F -> Collec G -> Collec F' -> Collec G' -> Process_Name x -> Process_Name y -> Process P  -> Process Q -> 
    ( D ;;; F !- P ::: ( (cons (y:A) nil) ++ G) ) ->
    ( D ;;; F' !- Q ::: ( (cons (x:B) nil) ++ G') ) ->
    ( D ;;; (F ++ F') !- (ν (Close_Rec 0 y (x « y »· (P↓Q)))) ::: ( (cons (x:(A⊗B)) nil) ++ G ++ G') )  
    

  | absr : forall ( D F G: list Assignment )( x : Name) (P : Prepro ),
    Collec D -> Collec F -> Collec G -> Process_Name x -> Process P -> 
    ( D ;;; F !- P ::: G ) -> 
    ( D ;;; F !- (x ()· P) ::: ( (cons (x:⊥) nil) ++ G) )
    
    
  | absl : forall ( D : list Assignment)( x : Name),
    Collec D -> Process_Name x -> 
    ( D ;;; (cons (x:⊥) nil ) !- (x «»·° ) ::: nil )

where "D ';;;'  F '!-' P ':::' G" := (Inference D F G P).
Hint Constructors Inference : core.

    
    
    
    
    
    
    
    
    
    
    
    
    