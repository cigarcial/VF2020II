(*
Verificación Formal - 2020-II
Archivo de proposiciones - Arreglos flexibles usando árboles de Braun 

Convenciones :
  MT : Surgen varías metas pero algunas de estas son triviales

Importación del archivo de definiciones de BN, proposiciones de BN y definiciones de árboles de Braun
*)
From TAREA3 Require Import Defs_BN.
From TAREA3 Require Import Props_BN.
From TAREA3 Require Import Defs_BT.


(*
------------------------------------####------------------------------------
------------------------------------####------------------------------------
                Inicio del Fragmento de código visto en clase.
------------------------------------####------------------------------------
------------------------------------####------------------------------------
*)


Theorem eq_btree_dec: forall (s t:BTree), {s=t} + {s<>t}.
Proof.
intros.
decide equality.
apply eq_dec_A.
Qed.


Lemma nonE_tree: forall (t:BTree), t <> E -> exists (a:A) (t1 t2:BTree), t = N a t1 t2.
Proof.
intros.
destruct t.
intuition.
exists a.
exists t1.
exists t2.
trivial.
Qed.


Lemma bsize_Z: forall (t:BTree), bsize t = Z -> t = E.
Proof.
intros t0.
destruct t0.
intuition.
intros.
simpl in H.
symmetry in H.
contradict H.
apply ZnotSucBN.
Qed.

Lemma bsize_nonZ: forall (t:BTree), t <> E -> bsize t <> Z.
Proof.
intros.
contradict H.
apply bsize_Z.
trivial.
Qed.


Lemma btNonE: forall (t:BTree) (b:BN), t <> E -> 
                       exists (b:BN), bsize t = U b \/ bsize t = D b.
Proof.
intros.
apply bsize_nonZ in H.
apply (bnNonZ (bsize t)) in H.
trivial.
Qed.




Lemma prop_0_U : forall (a:A) (s t:BTree) (b:BN), 
                  bbal (N a s t) -> bsize(N a s t) = U b -> 
                  bsize s = b /\ bsize t = b.
Proof.
intros.
simpl in H0.
assert (H0b:=H0).
rewrite <- plus_U in H0.
apply SucBNinj in H0.
inversion H.
destruct(bbalCond_eqs (bsize s) (bsize t)).
trivial.
trivial.
rewrite <- H8 in H0.
apply addition_a_a in H0.
rewrite <- H8.
intuition.
rewrite H8 in H0b.
rewrite plus_D in H0b.
inversion H0b.
Qed.


Lemma prop_0_D : forall (a:A) (s t:BTree) (b:BN), bbal (N a s t) 
                         -> bsize(N a s t) = D b -> 
                            bsize s = sucBN b /\ bsize t = b.
Proof.
intros.
simpl in H0.
assert (H0b:=H0).
rewrite <- plus_D in H0.
apply SucBNinj in H0.
inversion H.
destruct(bbalCond_eqs (bsize s) (bsize t)).
trivial.
trivial.
rewrite <- H8 in H0b.
rewrite plus_U in H0b.
inversion H0b.
rewrite H8 in H0.
apply addition_SucBNa_a in H0.
rewrite <- H0.
intuition.
Qed.

Corollary size_caseU: forall (a:A) (l r:BTree) (b:BN), 
                        bsize (N a l r) = U b -> bsize l = bsize r.
Proof.
intros.
assert (HBal := allBal (N a l r)).
apply (prop_0_U a l r b) in H.
intuition.
rewrite <- H1 in H0.
intuition. intuition.
Qed.

Corollary size_caseD: forall (a:A) (l r:BTree) (b:BN), 
                        bsize (N a l r) = D b 
                           -> bsize l = sucBN (bsize r).
Proof.
intros.
assert (HBal := allBal (N a l r)).
apply (prop_0_D a l r b) in H.
intuition.
rewrite <- H1 in H0.
intuition. intuition.
Qed.

Corollary bbal_size_r: forall (a:A) (l r:BTree), 
                          bsize (N a l r) = U (bsize r) \/ 
                          bsize (N a l r) = D (bsize r).
Proof.
intros.
assert (HBal:=allBal (N a l r)).
destruct (bnNonZ (bsize (N a l r))).
simpl.
assert (Z <> sucBN (bsize l ⊞ bsize r)).
apply ZnotSucBN.
intuition.
destruct H.
apply prop_0_U in H.
simpl.
destruct H.
rewrite H.
rewrite H0.
rewrite plus_U.
intuition.
trivial.
apply prop_0_D in H.
destruct H.
simpl.
rewrite H.
rewrite H0.
rewrite plus_D.
intuition.
trivial.
Qed.

Theorem bbal_size_r2: forall (a:A) (l r:BTree), (bsize (N a l r)) ≤BN (D (bsize r)). 
Proof.
intros a l r.
destruct (bbal_size_r a l r).
constructor.
rewrite H.
constructor.
rewrite H.
constructor.
Qed.

Theorem bbal_size_l: forall (a:A) (l r:BTree), (bsize (N a l r)) ≤BN (U (bsize l)). 
Proof.
intros.
assert (HBal:=allBal (N a l r)).
destruct (bnNonZ (bsize (N a l r))).
- simpl.
  assert (Z <> sucBN (bsize l ⊞ bsize r)).
  apply ZnotSucBN.
  intuition.
- destruct H.
  + apply prop_0_U in H.
    * simpl.
      destruct H.
      subst.
      rewrite H0. 
      rewrite plus_U.
      constructor.
    * assumption.
  +  apply prop_0_D in H.
    * simpl.
      destruct H.
rewrite H.
rewrite H0.
rewrite plus_D.
constructor.
constructor.
apply lts.
* trivial.
Qed.

(* ============================================= *)
          

Lemma lt_U_bsize: forall (b:BN) (a:A) (t1 t2:BTree), (U b) <BN (bsize (N a t1 t2)) -> b <BN (bsize t1).
Proof.
intros b a t1 t2 H.
assert ((bsize (N a t1 t2)) ≤BN (U (bsize t1))).
apply bbal_size_l.
assert ((U b) <BN (U (bsize t1))).
eapply lt_lteqBN_trans.
eexact H.
trivial.
inversion H1.
trivial.
Qed.



Theorem rightE: forall (a:A) (t1 t2:BTree), bbal(N a t1 t2) -> t2 = E -> (t1 = E \/ exists (aa:A), t1 = (N aa E E)).
Proof.
intros.
inversion H.
destruct (bbalCond_eqs (bsize t1) (bsize t2)).
trivial.
trivial.
rewrite H0 in H8.
simpl in H8.
apply bsize_Z in H8.
intuition.
rewrite H0 in H8.
right.
destruct t1.
simpl in H8.
inversion H8.
simpl in H8.
replace (U Z) with (sucBN Z) in H8.
apply SucBNinj in H8.
apply plusBN_Z_Z in H8.
destruct H8.
apply bsize_Z in H8.
apply bsize_Z in H9.
exists a1.
rewrite H8.
rewrite H9.
trivial.
intuition.
Qed.


Lemma lt_D_bsize: forall (b:BN) (a:A) (t1 t2:BTree), (D b) <BN (bsize (N a t1 t2)) -> b <BN (bsize t2).
Proof.
intros b a t1 t2 H.
assert ((bsize (N a t1 t2)) ≤BN (D (bsize t2))).
apply bbal_size_r2.
assert ((D b) <BN (D (bsize t2))).
eapply lt_lteqBN_trans.
eexact H.
trivial.
inversion H1.
trivial.
Qed.



Lemma bbal_leaf: forall (a:A), bbal (N a E E).
Proof.
intro a.
constructor.
constructor.
constructor.
apply lteqBN_refl. 
apply lteqs.
Qed.



Theorem leftE_leaf: forall (t1 t2:BTree) (a:A), bbal (N a t1 t2) -> t1 = E -> t2 = E.
Proof.
intros t1 t2 c HBal H.
inversion HBal.
rewrite H in H5.
simpl in H5.
inversion H5.
apply bsize_Z in H9.
trivial.
inversion H7.
Qed.



Lemma bbal_inv : 
forall (t:BTree), 
t <> E -> (exists (z:A), t = N z E E)  \/ 
           exists (z:A) (r1 r2:BTree), bbal r1 /\ bbal r2 /\ r1 <> E /\ t = N z r1 r2.
Proof.
  intros.
  destruct t.
  + contradiction.
  + assert ( HBB := allBal (N a t1 t2)).
    destruct t1.
    - apply leftE_leaf in HBB.
      left. exists a. rewrite HBB. auto.
      auto.
    - right.
      exists a. exists (N a0 t1_1 t1_2).
      exists t2.
      inversion HBB.
      subst.
      split.
      auto.
      split.
      auto.
      split.
      intuition.
      discriminate.
      auto.
Qed.


Lemma lkp_upd_BN: forall (t:BTree) (x:A) (b:BN), t <> E -> 
                       b <BN (bsize t) -> 
                       lookup_bn (update t b x) b = x.
Proof.
intros t x.
assert (H:=allBal t).
(*Induction on t*)
induction t.
- (*Base case t = E *)
intuition.
- (*Induction step t = N a t1 t2*)
intros.
(*cases on BNat number b*)
destruct b.
+ (*1. b=Z*)
reflexivity.
+ (*2. b = U b*)
destruct (eq_btree_dec t1 E).
(*Cases on t1*)
* (*i) t1=E A*)
assert (t2 = E).
-- apply (leftE_leaf t1 t2 a).
   ++ eexact H.
   ++ assumption.
-- (*t1=E  and t2=E *)
   subst.
   simpl in H1.
   inversion H1.
   inversion H4.
* (*ii) t1<>E A*)
simpl. 
apply IHt1.
-- inversion H.
   assumption.
-- assumption.
-- eapply lt_U_bsize.
   exact H1.
+ (*3. b = D b*)
  destruct (eq_btree_dec t2 E).
  * destruct (rightE a t1 t2).
    -- assumption.
    -- assumption.
    -- simpl.
       subst.
       simpl in H1.
       inversion H1.
       inversion H4.
    -- destruct H2.
       subst.
       simpl in H1.
       inversion H1.
       inversion H4.
* simpl. 
  apply IHt2.
  -- inversion H.
     assumption.
  -- assumption.
  -- eapply lt_D_bsize.
     exact H1.
Qed.




Lemma lkp_upd_BNindbal: forall (t:BTree) (x:A) (b:BN), t <> E -> 
                       b <BN (bsize t) -> 
                       lookup_bn (update t b x) b = x.
Proof.
intros t x.
assert (H:=allBal t).
induction H.
- intuition.
- intros.
  destruct b.
  + reflexivity.
  + simpl.
    destruct (eq_btree_dec s E).
    * destruct (eq_btree_dec t E).
      -- subst.
         simpl in H4.
         apply lt_U in H4.
         inversion H4.
      -- subst.
         simpl in H1.
         inversion H1. 
         ++ subst.
            apply bsize_nonZ in n.
            contradiction n.  
         ++ inversion H5.
    * apply IHbbal1.
      -- assumption.
      -- apply lt_U.
         eapply lt_lteqBN_trans.
         ++ exact H4.
         ++ apply bbal_size_l.
  + destruct (eq_btree_dec t E).
    * destruct (eq_btree_dec s E). 
       -- subst.
          simpl in H4.
          inversion H4.
          inversion H7.
       -- subst.
          simpl in H2.
          inversion H2.
          ++ simpl in H4.
             rewrite H7 in H4.
             simpl in H4. 
             inversion H4.
             inversion H9.
          ++ subst.
             inversion H5.
             ** contradict n.
             apply bsize_Z.
             intuition. 
             ** inversion H8.
             ** inversion H8.
    *  simpl.
       apply IHbbal2.
       -- assumption.
       -- apply lt_D.
          eapply lt_lteqBN_trans.
          ++ exact H4.
          ++ apply bbal_size_r2.  
Qed.


Lemma elmnt_lkp_upd : forall (t:BTree) (i j:BN), 
                        i <BN (bsize t) -> j <BN (bsize t) -> 
                        i <> j -> 
                        forall (x:A), 
                          lookup_bn (update t i x) j = lookup_bn t j.
Proof.
intros t.
induction t.
(* t = E*)
- intros.
simpl in H0.
inversion H0.
- (* t = N a t1 t2 *)
intros.
assert (tBal:=allBal (N a t1 t2)).
destruct (bbal_inv (N a t1 t2)).
+ discriminate.
+ (* exists z : A, N a t1 t2 = N z E E *)
destruct H2.
inversion H2.
subst.
simpl in H.
inversion H.
* subst.
  simpl in H0.
  inversion H0.
  -- subst. intuition.
  -- reflexivity.
  -- reflexivity. 
* destruct j.
  -- reflexivity.
  -- inversion H5.
  -- inversion H5.
* inversion H5.
+ (*  exists (z : A) (r1 r2 : BTree),
         bbal r1 /\ bbal r2 /\ r1 <> E /\ N a t1 t2 = N z r1 r2 *)
do 4 (destruct H2).
destruct H3.
destruct H4.
destruct H5.
destruct i.
* destruct j. 
  -- intuition.
  -- reflexivity.
  -- reflexivity.
* destruct j.
  -- reflexivity.
  -- simpl.
     apply IHt1. 
     ++ apply lt_U.
        eapply lt_lteqBN_trans.
        ** exact H.
        ** apply bbal_size_l. 
     ++ apply lt_U.
        eapply lt_lteqBN_trans.
        ** exact H0.
        ** apply bbal_size_l.
     ++ contradict H1.
        subst;reflexivity.
   -- reflexivity.
  * destruct j.
    -- reflexivity.
    -- reflexivity.
    -- simpl. 
       apply IHt2. 
     ++ apply lt_D.
        eapply lt_lteqBN_trans.
        ** exact H.
        ** apply bbal_size_r2.
     ++ apply lt_D.
        eapply lt_lteqBN_trans.
        ** exact H0.
        ** apply bbal_size_r2.
     ++ contradict H1.
        subst;reflexivity.
Qed.


Lemma bsize_upd: forall (t:BTree) (x:A) (b:BN), 
                  b <BN bsize t -> bsize t = bsize (update t b x).
Proof.
intro t.
induction t.
- (* Base case *)
intuition.
inversion H.
- (* Inductive step *)
intros.
destruct (bbal_inv (N a t1 t2)).
+ discriminate.
+ destruct H0.
  rewrite H0 in H.
  simpl in H.
  inversion H.
  * (* b = Z *)
   reflexivity.
  * (* U a0 = b, a < Z *)
    inversion H3.
  * (* D a0 = b, a < Z *)
    inversion H3.
+ do 4 (destruct H0).
  destruct H1.
  destruct H2.
  inversion H3.
  subst.
  destruct b.
  * (* Z *)
    reflexivity.
  * (* U b*)
   simpl.
   rewrite (IHt1 x b).
   -- reflexivity.
   -- apply (lt_U_bsize b x0 x1 x2).
      assumption. 
  * (* b = D b *)
    simpl.
    rewrite (IHt2 x b).
    -- reflexivity.
    -- apply (lt_D_bsize b x0 x1 x2).
       assumption.
Qed.
     
  
Lemma bsize_le: forall (t:BTree) (x:A), bsize (le x t) = sucBN (bsize t).
Proof.
intro.
assert (HBal := allBal t).  
induction HBal.
- reflexivity.
- intro.
  simpl.
  rewrite IHHBal2.
  rewrite <- plusSuc.
  rewrite plusComm.
  reflexivity.
Qed.



Lemma bal_le: forall (t:BTree), bbal t -> 
                 forall (x:A), bbal (le x t).
Proof.
intros t HtBal.
induction HtBal.
- simpl.
  apply bbal_leaf.
- intros.
  simpl.
  constructor.
  + apply IHHtBal2.
  + assumption.
  + rewrite bsize_le.
    assumption.
  + rewrite bsize_le.
    apply lteqBN_suc.
    assumption.
Qed.

Lemma le_head: forall (t: BTree) (x:A),  lookup_bn (le x t) Z = x.
Proof.
intros.
destruct t.
- intuition.
- intuition.
Qed.


Lemma le_idx: forall (t:BTree),  bbal t -> 
forall (j:BN), j <BN (bsize t) -> forall (x:A), lookup_bn (le x t) (sucBN j) = lookup_bn t j.
Proof.
intros t B.
induction B.
- intros.
  simpl in H.
  inversion H.
- intros.
  clear IHB1.
  destruct j.
  + simpl.
    apply le_head.
  + reflexivity.
  + simpl.
    apply IHB2.
    apply (lt_D_bsize j a s t).
    assumption.
Qed.


(*High Extension*)

Lemma bsize_he: forall (t:BTree) (x:A), 
                    bsize (he x t) = sucBN (bsize t).
Proof.
intro.
induction t.
- intuition.
- intros.
  destruct (bbal_size_r a t1 t2).
  + simpl in H.
    simpl.
    rewrite H.
    simpl.
    rewrite IHt1.
    rewrite <- plusSuc.
    rewrite H. 
    intuition.
  + simpl in H.
    simpl.
    rewrite H.
    simpl.
    rewrite IHt2.
    rewrite <- plusSuc_2.
    rewrite H.
    intuition.
Qed.


Lemma bal_he : 
forall (t:BTree), 
bbal t -> forall (x:A), bbal (he x t).
Proof.
intros t Ht.
induction t.
- simpl.
  apply bbal_leaf.
- intros.
  inversion Ht.
  subst.
  destruct (bbal_size_r a t1 t2).
  + assert(H6:=H). 
    apply size_caseU in H.
    simpl in H6. 
    simpl.
    rewrite H6.
    constructor; auto.
    * rewrite bsize_he.
      inversion H4.
      -- intuition.
      -- rewrite H. rewrite H in H5. auto.
    * rewrite bsize_he.
      rewrite H.
      intuition.
  + assert(H6:=H).
    apply size_caseD in H.
    simpl in H6.
    simpl.
    rewrite H6.
    constructor; auto. 
    * rewrite bsize_he.
      rewrite H.
      constructor.
    * rewrite bsize_he.
      rewrite <- H.
      intuition.
Qed.


Lemma he_last :
forall (t: BTree) (x:A),
lookup_bn (he x t) (bsize t) = x.
Proof.
  intro.
  induction t.
  + auto.
  + intros.
    simpl.
    destruct (bbal_size_r a t1 t2);
      assert(H1 := H);
      simpl in H1;
      apply size_caseU in H || apply size_caseD in H;
      rewrite H1;
      simpl;
      try rewrite <- H;
      apply IHt1 || apply IHt2.
Qed.



Lemma he_idx :
forall (t:BTree),
bbal t -> forall (j:BN), j <BN (bsize t) -> 
forall (x:A), 
lookup_bn (he x t) j = lookup_bn t j.
Proof.
  intro.
  assert (HBal := allBal t).
  induction t.
  + intros. simpl in H0. apply lt_noZ in H0. contradiction.
  + intros.
    destruct (bbal_size_r a t1 t2).
    - assert( H2 := H1 ).
      simpl in H2.
      simpl. 
      rewrite H2.
      destruct j.
      * auto.
      * simpl.
        rewrite H1 in H0.
        apply size_caseU in H1.
        rewrite <- H1 in H0.
        inversion H0.
        inversion HBal.
        rewrite IHt1; auto.
      * auto.
    - assert( H2 := H1 ).
      simpl in H2.
      simpl. 
      rewrite H2.
      destruct j.
      * auto.
      * auto.
      * simpl.
        rewrite H1 in H0.
        apply size_caseD in H1.
        inversion H0.
        inversion HBal.
        rewrite IHt2; auto.
Qed.


(*
------------------------------------####------------------------------------
------------------------------------####------------------------------------
                   Fin del fragmento de código visto en clase.
------------------------------------####------------------------------------
------------------------------------####------------------------------------
*)


(*
------------------------------------####------------------------------------
------------------------------------####------------------------------------
                Inicio del fragmento de código implementado.
------------------------------------####------------------------------------
------------------------------------####------------------------------------
*)


(*
Un árbol no vacío es no vacío.
*)
Lemma NTree_noE : 
forall (t t1 t2 : BTree)( a : A ),
t = N a t1 t2 -> t <> E.
Proof.
  unfold not.
  intros.
  rewrite H0 in H.
  discriminate.
Qed.


(*
Un árbol no vacío tiene tamaño distinto a cero.
*)
Lemma NTree_noZ : 
forall (t t1 t2 : BTree)( a : A ),
t = N a t1 t2 -> (bsize t) <> Z.
Proof.
  unfold not.
  intros.
  rewrite H in *.
  simpl in H0.
  apply ZnotSucBN_sym in H0.
  contradiction.
Qed.


(*
Simétrico del resultado anterior.
*)
Lemma NTree_noZ_sym : 
forall (t t1 t2 : BTree)( a : A ),
t = N a t1 t2 -> Z <> (bsize t).
Proof.
  intros.
  apply not_eq_sym.
  apply (NTree_noZ t t1 t2 a); auto.
Qed.


(*
Dado dos árboles con el mismo tamaño, si uno de ellos es no vacío en consecuencia el otro tampoco
*)
Lemma trees_eqbsize_noE :
forall (t1 t2 T1 T2 : BTree )( a : A), 
t1 = N a T1 T2 -> bsize t1 = bsize t2 -> t2 <> E.
Proof.
  unfold not.
  intros.
  rewrite H1 in *.
  rewrite H in *.
  simpl in H0.
  apply ZnotSucBN_sym in H0.
  contradiction.
Qed.


(*
Dados dos árboles con el mismo tamaño, si uno de ellos es no vacío en consecuencia el otro tiene tamaño no cero
*)
Lemma trees_eqbsize_noZ :
forall (t1 t2 T1 T2 : BTree )( a : A), 
t1 = N a T1 T2 -> bsize t1 = bsize t2 -> (bsize t2) <> Z.
Proof.
  unfold not.
  intros.
  rewrite H1 in *.
  rewrite H in *.
  simpl in H0.
  apply ZnotSucBN_sym in H0.
  contradiction.
Qed.


(*
Si un árbol tiene tamaño no vacío, entonces no es vacío
*)
Lemma bsize_nZ_nE : 
forall t : BTree,
(bsize t <> Z) -> (t <> E).
Proof.
  unfold not.
  intros. 
  rewrite -> H0 in H.
  simpl in H.
  auto.
Qed.


(*
Al realizar la operación de inserción al final se obtiene un arreglo no vacío
*)
Lemma he_notE : 
forall ( t : BTree)( x : A),
exists (a : A)( t1 t2 : BTree), he x t = N a t1 t2.
Proof.
  intro.
  induction t.
  + intros. simpl.
    exists x. do 2 exists E. auto.
  + intros. simpl.
    destruct (bbal_size_r a t1 t2).
    - assert(H1 := H).
      apply size_caseU in H1.
      simpl in H.
      rewrite H.
      exists a.
      exists (he x t1).
      exists t2.
      auto.
    - assert(H1 := H).
      apply size_caseD in H1.
      simpl in H.
      rewrite H.
      exists a.
      exists t1.
      exists (he x t2).
      auto.
Qed.


(*
Al realizar la operación de inserción al inicio, se obtiene un arreglo no vacío
*)
Lemma le_notE : 
forall ( t : BTree)( x : A),
exists ( t1 t2 : BTree), le x t = N x t1 t2.
Proof. 
  intros.
  induction t.
  + intros. simpl.
    do 2 exists E.
    auto.
  + intros. simpl.
    exists (le a t2).
    exists t1.
    auto.
Qed.


(*
Un árbol puede ser vacío o tener una forma especifica.
*)
Lemma char_BTree : 
forall t : BTree, 
t = E \/ exists (a:A)(t1 t2: BTree), t = N a t1 t2.
Proof.
  intros.
  destruct t.
  + left. auto.
  + right. exists a. exists t1. exists t2. auto.
Qed.


(*
Dados dos árboles con mismo tamaño, si uno de ellos es no vacío la suma de sus tamaños es no cero
*)
Lemma NT_Eqbsize_noZ : 
forall ( s t x0 x1 : BTree ) ( x : A),
s = N x x0 x1 -> bsize s = bsize t -> 
bsize t ⊞ bsize s <> Z.
Proof.
  unfold not.
  intros.
  rewrite <- H0 in H1.
  rewrite H in H1.
  simpl in H1.
  rewrite <- plusSuc in H1.
  apply ZnotSucBN_sym in H1; auto.
Qed.


(*
Verificaciones de la tarea
*)


(*
Punto 2 :
La idea de la prueba es la siguiente: 
  + se parte del hecho que el árbol t está balanceado
  - se analiza inductivamente suponiendo que los arboles estan balanceados y cumplen el resultado del tamaño
  * se analizan los casos en que los subárboles tienen el mismo tamaño o difieren en uno
*)
Lemma bsize_lr : 
forall ( t : BTree),
t <> E -> bsize (lr t) = predBN (bsize t).
Proof.
  intro.
  assert (HBal := allBal t).
  induction HBal.
  + contradiction.
  + intros.
    destruct (bbal_size_r a s t).
    - apply size_caseU in H2.
      destruct (eq_btree_dec s E).
      * assert (Ht : t = E). { 
         (* MT *)
         apply (leftE_leaf s t a); auto.
         constructor; auto. }
        rewrite e.
        rewrite Ht.
        auto.
      * apply nonE_tree in n as H3.
        do 3 destruct H3.
        specialize ( NTree_noZ s x0 x1 x) as Hs.
        specialize (Hs H3).
        specialize (NT_Eqbsize_noZ s t x0 x1 x) as Ht.
        specialize (Ht H3 H2).
        simpl.
        rewrite H3; rewrite <- H3.
        rewrite H2.
        apply IHHBal1 in n.
        simpl.
        rewrite n.
        (* MT *)
        rewrite plusPred; auto.
        (* MT *)
        rewrite  conmt_sucBN_predBN_noZ; auto.
        rewrite H2.
        auto.
    - assert(H3 := H2).
      apply size_caseD in H3.
      simpl in H2.
      destruct (eq_btree_dec s E).
      * assert (Ht : t = E).
        (* MT *)
        apply (leftE_leaf s t a); auto.
         { constructor; auto. }
        rewrite e.
        rewrite Ht.
        auto.
      * apply nonE_tree in n as H4.
        do 3 destruct H4.
        specialize ( NTree_noZ s x0 x1 x) as HT.
        specialize ( HT H4 ).
        simpl.
        rewrite H4; rewrite <- H4.
        rewrite H2.
        apply IHHBal1 in n.
        simpl.
        rewrite n.
        (* MT *)
        rewrite plusPred; auto.
        rewrite  conmt_sucBN_predBN_noZ.
        rewrite plusComm.
        rewrite H2.
        auto.
        rewrite H3.
        rewrite <- plusSuc_2.
        apply ZnotSucBN_sym.
Qed.


(*
Punto 3 :
La idea de la prueba es la siguiente: 
  + se hace inducción sobre el árbol t
  - se analiza el subárbol izquierdo, si es vacío o no
    y proceder por inducción en los casos donde se requiera
*)
Lemma bal_lr : 
forall (t:BTree), 
t <> E -> bbal t -> bbal (lr t).
Proof.
  intros.
  induction t.
  + contradiction.
  + inversion H0. subst.
    destruct (eq_btree_dec t1 E). 
    - assert ( Ht2 : t2 = E). 
       { apply (leftE_leaf t1 t2 a); auto. }
      rewrite e. rewrite Ht2. 
      simpl. constructor.
    - apply nonE_tree in n as H1.
      do 3 destruct H1.
      simpl. 
      rewrite H1; rewrite <- H1.
      specialize ( NTree_noZ t1 x0 x1 x) as HS.
      specialize (HS H1).
      (* MT *)
      constructor; try rewrite bsize_lr; auto.
      * apply lteqBN_suc_pred in H7; auto.
      * apply sucpredBNinv in HS.
        rewrite HS.
        auto.
Qed.


(*
Punto 4 :
La idea de la prueba es la siguiente: 
  + se hace inducción sobre el árbol t
  - se analiza el subárbol izquierdo, si es vacío o no
    y proceder por inducción en los casos donde se requiera
*)
Lemma lkp_lr : 
forall (t:BTree)(j:BN), 
t <> E -> j <BN predBN (bsize t) -> 
lookup_bn (lr t) j = lookup_bn t (sucBN j).
Proof.
  intro.
  assert (HBal := allBal t).
  induction t.
  + contradiction.
  + intros.
    specialize (char_BTree t1) as Ht1.
    destruct Ht1.
    - rewrite H1 in * . 
      assert ( Ht2 : t2 = E).
       { apply (leftE_leaf E t2 a); auto. }
      rewrite Ht2 in *. 
      simpl in H0. apply lt_noZ in H0. 
      contradiction.
    - do 3 destruct H1.
      assert ( HTT : lr (N a t1 t2) = N x t2 (lr t1)). 
       { rewrite H1; auto. }
      rewrite HTT.
      (* MT *)
      destruct j; auto.
      * rewrite H1; auto.
      * simpl.
        specialize (NTree_noE t1 x0 x1 x) as HEt1.
        specialize ( HEt1 H1).
        specialize (NTree_noZ t1 x0 x1 x) as HZt1.
        specialize ( HZt1 H1).
        inversion HBal.
        rewrite IHt1; auto.
        simpl in H0.
        destruct (bbal_size_r a t1 t2).
        ** assert(H10 := H9).
           simpl in H9.
           rewrite H9 in H0.
           simpl in H0.
           apply size_caseU in H10.
           rewrite H10.
           rewrite H10 in HZt1.
           specialize (bnNonZ (bsize t2)) as Hbsize.
           specialize (Hbsize HZt1).
           destruct Hbsize.
           destruct H11;
           rewrite H11 in H0;
           rewrite <- H11 in H0;
           inversion H0;
           auto.
        ** assert(H10 := H9).
           simpl in H9.
           rewrite H9 in H0.
           simpl in H0.
           apply size_caseD in H10.
           inversion H0.
           rewrite change_suc_pred_eq in H10; auto.
           rewrite H10; auto.
Qed.


(*
Punto 5 :
La idea de la prueba es la siguiente: 
  + se hace inducción sobre el árbol t
  - se analiza el subárbol izquierdo, si es vacío o no
    y proceder por inducción en los casos donde se requiera
    se aplica el hecho que le retorna un árbol no vacío
*)
Lemma lr_le : 
forall (t : BTree)(x : A), 
lr (le x t ) = t.
Proof.
  intro.
  (* MT *)
  induction t; auto.
  + intros.
    assert ( le x (N a t1 t2) = N x (le a t2) t1). 
     { auto. }
    rewrite H.
    simpl.
    specialize (le_notE t2 a) as H0.
    do 2 destruct H0.
    rewrite H0; rewrite <- H0.
    rewrite IHt2.
    auto.
Qed.


(*
Punto 6 :
La idea de la prueba es la siguiente: 
  + se hace inducción sobre el árbol t
  - se analiza el subárbol izquierdo, si es vacío o no
    y proceder por inducción en los casos donde se requiera
*)
Lemma le_lkp_lr : 
forall (t : BTree),
t <> E -> le (lookup_bn t Z) (lr t) = t.
Proof.
  intro. 
  assert (HBal := allBal t).
  induction t.
  + contradiction.
  + intros.
    specialize (char_BTree t1) as Ht1.
    destruct Ht1.
    - rewrite H0 in *.
      assert ( Ht2 : t2 = E ). 
       { apply (leftE_leaf E t2 a); auto. }
      rewrite Ht2 in *.
      auto.
    - do 3 destruct H0.
      simpl. 
      rewrite H0; rewrite <- H0.
      simpl.
      assert ( x = (lookup_bn t1 Z)).
       { rewrite H0; auto. }
      rewrite H1.
      inversion HBal.
      apply NTree_noE in H0 as HTE.
      rewrite IHt1; auto.
Qed.


(*
Punto 7 :
La idea de la prueba es la siguiente: 
  + se hace inducción sobre los árboles balanceados
  - corresponde a los casos en que los subárboles tienen el mismo o diferente tamaño
*)
Lemma bsize_hr : 
forall ( t : BTree),
t <> E -> bsize (hr t) = predBN (bsize t).
Proof.
  intros.
  assert (HBal := allBal t).    
  induction HBal.
  + contradiction.
  + destruct (bbal_size_r a s t).
    - assert(H3 := H2).
      apply size_caseU in H3.
      simpl in H2.
      destruct (eq_btree_dec s E).
      * assert (Ht : t = E).
         { apply (leftE_leaf s t a); auto.
           constructor; auto. }
        rewrite e.
        rewrite Ht.
        auto.
      * apply nonE_tree in n as H4.
        do 3 destruct H4.
        simpl.
        rewrite H4; rewrite <- H4.
        rewrite H2.
        specialize (trees_eqbsize_noE s t x0 x1 x) as Ht.
        (* MT *)
        apply IHHBal2 in Ht; auto.
        simpl.
        rewrite Ht.
        specialize (trees_eqbsize_noZ s t x0 x1 x) as H5.
        specialize (H5 H4 H3).
        specialize (NT_Eqbsize_noZ s t x0 x1 x) as HT.
        specialize (HT H4 H3).
        rewrite plusComm in HT.
        (* MT *)
        rewrite plusPred; auto.
        (* MT *)
        rewrite  conmt_sucBN_predBN_noZ; auto.
        rewrite H2.
        auto.
    - assert(H3 := H2).
      apply size_caseD in H3.
      simpl in H2.
      destruct (eq_btree_dec s E).
      * assert (Ht : t = E).
         { apply (leftE_leaf s t a); auto.
           constructor; auto. }
        rewrite e.
        rewrite Ht.
        auto.
      * apply nonE_tree in n as H4.
        do 3 destruct H4.
        simpl.
        rewrite H4; rewrite <- H4.
        rewrite H2.
        apply IHHBal1 in n.
        simpl.
        rewrite n.
        rewrite plusPred_sym.
        rewrite  conmt_sucBN_predBN_noZ.
        rewrite H2.
        auto.
        rewrite H3.
        rewrite <- plusSuc.
        apply ZnotSucBN_sym.
        rewrite H4.
        simpl.
        apply ZnotSucBN_sym.
Qed.


(*
Punto 8 :
La idea de la prueba es la siguiente: 
  + se hace inducción sobre el árbol t
  - se analiza el subárbol izquierdo, si es vacío o no
    y proceder por inducción en los casos donde se requiera
  * corresponde a los casos en que los subárboles tienen el mismo o diferente tamaño
*)
Lemma bal_hr : 
forall (t:BTree), 
t <> E -> bbal t -> bbal (hr t).
Proof.
  intros.
  induction t.
  + contradiction.
  + inversion H0. subst.
    destruct (eq_btree_dec t1 E).
    - assert ( Ht2 : t2 = E).
       { apply (leftE_leaf t1 t2 a); auto. }
      rewrite e. rewrite Ht2. simpl. constructor.
    - destruct (bbal_size_r a t1 t2).
      * assert(H2:=H1).
        apply size_caseU in H1.
        simpl in H2. 
        apply nonE_tree in n.
        destruct n as [b [t11 [t12]]].
        simpl. 
        rewrite H3; rewrite <- H3.
        rewrite H2.
        specialize ( NTree_noE t1 t11 t12 b) as HEt1.
        specialize ( HEt1 H3).
        specialize ( trees_eqbsize_noE t1 t2 t11 t12 b) as HEt2.
        specialize ( HEt2 H3 H1).
        (* MT *)
        constructor; try rewrite -> bsize_hr; auto.
        ++ assert ( HS : Z <BN bsize t2 ).
            { rewrite <- H1. rewrite -> H3. 
              simpl. apply  Z_min_suc. }
           apply (lteqBN_trans _ (bsize t2) _); 
           try apply lt_predBN_lteq in HS;
           auto. 
        ++ specialize ( trees_eqbsize_noZ t1 t2 t11 t12 b) as HS.
           specialize (HS H3 H1).
           apply sucpredBNinv in HS.
           rewrite HS.
           rewrite H1.
           constructor.
      * assert(H2:=H1).
        apply size_caseD in H1.
        simpl in H2. 
        apply nonE_tree in n.
        destruct n as [b [t11 [t12]]].
        simpl. 
        rewrite H3; rewrite <- H3. 
        rewrite H2.
        specialize ( NTree_noE t1 t11 t12 b) as HEt1.
        specialize ( HEt1 H3).
        (* MT *)
        constructor; try rewrite -> bsize_hr; auto.
        ++ rewrite -> H1.
           rewrite predsucBNinv.
           constructor.
        ++ specialize ( NTree_noZ_sym t1 t11 t12 b) as HS.
           specialize ( HS H3).
           apply lt_pred_noZ; auto.
Qed.


(*
Punto 9 :
La idea de la prueba es la siguiente: 
  + se hace inducción sobre el árbol t
  - se analiza el subárbol izquierdo, si es vacío o no
    y proceder por inducción en los casos donde se requiera
  * corresponde a los casos en que los subárboles tienen el mismo o diferente tamaño
*)
Lemma lkp_hr : 
forall (t:BTree)(j:BN), 
t <> E -> j <BN predBN (bsize t) -> 
lookup_bn (hr t) j = lookup_bn t j.
Proof.
  intro.
  assert (HBal := allBal t).
  induction t.
  + contradiction.
  + intros.
    specialize ( char_BTree t1) as Ht1.
    (* casos t1 vacío y no vacío *)
    destruct Ht1.
    (* caso t1 vacío*)
    - rewrite H1 in *. 
      assert ( Ht2 : t2 = E ).
       { apply (leftE_leaf E t2 a); auto. }
      rewrite Ht2 in *.
      simpl.
      (* MT *)
      destruct j; auto.
      simpl in H0. apply ltBN_arefl in H0. contradiction.
    (* caso t1 no vacío *)
    - do 3 destruct H1.
      destruct j.
      (* j = Z *)
      * destruct (bbal_size_r a t1 t2);
           assert(H3 := H2);
           try apply size_caseU in H3;
           try apply size_caseD in H3;
           simpl in H2;
           simpl;
           rewrite H1;
           rewrite <- H1;
           rewrite H2;
           simpl; auto.
      * destruct (bbal_size_r a t1 t2);
          assert(H3 := H2);
           simpl in H2;
           simpl;
           rewrite H1;
           rewrite <- H1;
           rewrite H2;
           simpl; auto.
          (* fin primer tramo*)
          apply size_caseD in H3. 
           simpl in H0.
           rewrite H2 in H0.
           simpl in H0.
           inversion H0.
           rewrite change_suc_pred_eq in H3.
           rewrite <- H3 in H6.
           inversion HBal.
           (* MT *)
           rewrite IHt1; auto.
           unfold not.
           intros. rewrite H14 in H1.
           discriminate.
           unfold not. intros. 
           rewrite H1 in H7. simpl in H7.
            apply ZnotSucBN_sym in H7. auto.
      * destruct (bbal_size_r a t1 t2);
          assert(H3 := H2);
           simpl in H2;
           simpl;
           rewrite H1;
           rewrite <- H1;
           rewrite H2;
           simpl; auto.
          (*fin primer tramo*)
          apply size_caseU in H3. 
           simpl in H0.
           rewrite H2 in H0.
           simpl in H0.
           assert( HT : bsize t2 <> Z). rewrite <- H3. rewrite H1.
           apply ZnotSucBN_sym.
           apply bnNonZ in HT.
           destruct HT.
           specialize (trees_eqbsize_noE t1 t2 x0 x1 x) as HTT.
           destruct H4;
           rewrite  H4 in H0;
           rewrite H4 in IHt2;
           inversion H0;
           inversion HBal;
           rewrite IHt2; auto.
Qed.


(*
Punto 10 :
La idea de la prueba es la siguiente: 
  + se hace inducción sobre el árbol t
  - corresponde a los casos en que los subárboles tienen el mismo o diferente tamaño
    se aplica el hecho que he nos retornar un árbol no vacío
*)
Lemma hr_he : 
forall (t : BTree)(x : A), 
hr (he x t ) = t.
Proof.
  intro.
  induction t.
  + intros. simpl. auto.
  + intros.
    destruct (bbal_size_r a t1 t2).
    - assert(H1 := H).
      apply size_caseU in H1.
      simpl in H.
      simpl.
      rewrite H.
      specialize (he_notE t1 x) as H0.
      do 3 destruct H0.
      simpl. rewrite  H0. rewrite <- H0.
      specialize (bsize_he t1 x) as HS.
      rewrite HS.
      rewrite <- plusSuc.
      simpl.
      rewrite H. simpl.
      specialize (IHt1 x).
      rewrite IHt1.
      auto.
    - assert(H1 := H).
      apply size_caseD in H1.
      simpl in H.
      simpl.
      rewrite H.
      assert ( H0 : exists (a0 : A)(T1 T2 : BTree), t1 = (N a0 T1 T2)).
      destruct t1.
      simpl in H1. apply ZnotSucBN in H1. contradiction.
      exists a0. exists t1_1. exists t1_2. auto.
      do 3 destruct H0.
      simpl. rewrite H0. rewrite <- H0.
      assert ( HS : bsize t1 = bsize (he x t2)). 
      rewrite H1. apply eq_sym. apply bsize_he.
      rewrite HS. rewrite  plus_U.
      specialize (IHt2 x).
      rewrite IHt2.
      auto.
Qed.


(*
Punto 11 :
La idea de la prueba es la siguiente: 
  + se hace inducción sobre el árbol t
  - se analiza el subárbol izquierdo, si es vacío o no
    y proceder por inducción en los casos donde se requiera
  * corresponde a los casos en que los subárboles tienen el mismo o diferente tamaño
*)
Lemma he_lkp_hr : 
forall (t : BTree),
t <> E -> he (lookup_bn t (predBN (bsize t))) (hr t) = t.
Proof.
  intro. 
  assert (HBal := allBal t).
  induction t.
  + contradiction.
  + intros.
    specialize (char_BTree t1) as Ht1.
    destruct Ht1.
    - rewrite H0 in *.
      assert ( Ht2 : t2 = E ). apply (leftE_leaf E t2 a); auto.
      rewrite Ht2 in *.
      simpl. 
      auto.
    - do 3 destruct H0.
      destruct (bbal_size_r a t1 t2).
      * assert(H2 := H1).
        simpl in H1.
        apply size_caseU in H2.
        simpl. 
        rewrite H1. simpl.
        specialize (trees_eqbsize_noZ t1 t2 x0 x1 x) as HT.
        specialize (HT H0 H2).
        specialize (trees_eqbsize_noE t1 t2 x0 x1 x) as HTE.
        specialize (HTE H0 H2).
        specialize (bnNonZ (bsize t2)) as Hbsize.
        specialize (Hbsize HT).
        assert ( HQ : bsize t1 ⊞ bsize t2 <> Z ).
          rewrite <- H2.
          rewrite H0.
          simpl. 
          rewrite <- plusSuc.
          apply ZnotSucBN_sym.
        destruct Hbsize.
        destruct H3;
          rewrite H3;
          rewrite H0;
          rewrite <- H0;
          rewrite <- H3;
          simpl;
          rewrite bsize_hr; auto;
          rewrite plusPred; auto;
          rewrite conmt_sucBN_predBN_noZ; auto;
          rewrite H1;
          simpl;
          rewrite H3;
          rewrite <- H3;
          inversion HBal;
          rewrite IHt2; auto.
      * assert(H2 := H1).
        simpl in H1.
        apply size_caseD in H2.
        simpl. 
        specialize (NTree_noE t1 x0 x1 x) as HEt1.
        specialize (HEt1 H0).
        specialize (NTree_noZ t1 x0 x1 x) as HZt1.
        specialize (HZt1 H0).
        assert ( bsize t1 ⊞ bsize t2 <> Z ).
          rewrite H2.
          rewrite <- plusSuc.
          apply ZnotSucBN_sym.
        rewrite H1. simpl. rewrite H0.
        rewrite <- H0. simpl.
        rewrite bsize_hr; auto. 
        rewrite plusPred_sym; auto.
        rewrite conmt_sucBN_predBN_noZ; auto.
        rewrite H1.
        rewrite change_suc_pred_eq in H2; auto.
        simpl.
        rewrite  <- H2.
        inversion HBal.
        rewrite IHt1; auto.
Qed.

