(*
Verificación Formal - 2020-II
Archivo de definiciones - Números por paridad
*)

From TAREA3 Require Import Defs_BN.
From TAREA3 Require Import Props_BN.
From TAREA3 Require Import Defs_BT.


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
Admitted.


Lemma he_idx: forall (t:BTree),  bbal t -> 
forall (j:BN), j <BN (bsize t) -> forall (x:A), lookup_bn (he x t) j = lookup_bn t j.
Admitted. (* Tarea moral *)


(*
Fin del fragmento de código visto en clase

-----------------------------------------------------------
-----------------------------------------------------------
-----------------------------------------------------------
-----------------------------------------------------------
-----------------------------------------------------------
-----------------------------------------------------------

Inicio del fragmento de código propio
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
        apply (leftE_leaf s t a).
        constructor; auto.
        auto.
        rewrite e.
        rewrite Ht.
        simpl. 
        auto.
      * apply nonE_tree in n as H4.
        do 3 destruct H4.
        simpl. 
        rewrite H4.
        rewrite <- H4.
        rewrite H2.
        assert ( Ht : t <> E ). unfold not. intros. rewrite H5 in H3.
        rewrite H4 in H3. simpl in H3. remember (ZnotSucBN_sym (bsize x0 ⊞ bsize x1)). contradiction.
        apply IHHBal2 in Ht.
        simpl. 
        rewrite Ht.
        assert ( bsize t <> Z ). rewrite <- H3. rewrite H4. simpl. apply ZnotSucBN_sym.
        rewrite plusPred.
        rewrite  conmt_sucBN_predBN_noZ.
        rewrite H2.
        auto.
        rewrite H3.
        unfold not.
        intros.
        apply plusBN_Z_Z in H6.
        destruct H6. contradiction.
        auto.
    - assert(H3 := H2).
      apply size_caseD in H3.
      simpl in H2.
      destruct (eq_btree_dec s E).
      * assert (Ht : t = E).
        apply (leftE_leaf s t a).
        constructor; auto.
        auto.
        rewrite e.
        rewrite Ht.
        simpl. 
        auto.
      * apply nonE_tree in n as H4.
        do 3 destruct H4.
        simpl. 
        rewrite H4.
        rewrite <- H4.
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

Lemma bal_hr : 
forall (t:BTree), 
t <> E -> bbal t -> bbal (hr t).
Proof.
  intros.
  induction t.
  + contradiction.
  + inversion H0. subst.
    destruct (eq_btree_dec t1 E).
    - assert ( Ht2 : t2 = E). apply (leftE_leaf t1 t2 a); auto.
      rewrite e. rewrite Ht2. simpl. constructor.
    - destruct (bbal_size_r a t1 t2).
      * assert(H2:=H1). 
        apply size_caseU in H1.
        simpl in H2. 
        apply nonE_tree in n.
        destruct n as [b [t11 [t12]]].
        simpl. rewrite H3. rewrite <- H3. rewrite H2.
        assert ( HEt1 : t1 <> E ). apply bsize_nZ_nE. rewrite H3. simpl. apply ZnotSucBN_sym. 
        assert ( HEt2 : t2 <> E ). apply bsize_nZ_nE. rewrite <- H1. rewrite H3. simpl. apply ZnotSucBN_sym. 
        constructor; auto.
        ++ rewrite -> bsize_hr.
           assert ( HS : Z <BN bsize t2 ). rewrite <- H1. rewrite -> H3. simpl. apply  Z_min_suc.
           apply (lteqBN_trans _ (bsize t2) _); 
           try apply lt_predBN_lteq in HS;
           auto. auto.
        ++ rewrite -> bsize_hr.
           assert ( HS : Z <> bsize t2 ). rewrite <- H1. rewrite -> H3. simpl. apply ZnotSucBN.
           apply not_eq_sym in HS.
           apply sucpredBNinv in HS.
           rewrite HS.
           rewrite H1.
           constructor.
           auto.
      * assert(H2:=H1).
        apply size_caseD in H1.
        simpl in H2. 
        apply nonE_tree in n.
        destruct n as [b [t11 [t12]]].
        simpl. rewrite H3. rewrite <- H3. rewrite H2.
        assert ( HEt1 : t1 <> E ). apply bsize_nZ_nE. rewrite H3. simpl. apply ZnotSucBN_sym. 
        constructor; auto.
        ++ rewrite -> bsize_hr.
           rewrite -> H1.
           rewrite predsucBNinv.
           constructor.
           auto. 
        ++ rewrite -> bsize_hr.
           assert (HS : Z <> bsize t1). rewrite H3. simpl. apply ZnotSucBN.
           apply lt_pred_noZ; auto.
           auto.
Qed.


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
      assert ( H0 : exists (a0 : A)(T1 T2 : BTree), (he x t1) = (N a0 T1 T2)). apply he_notE.
      do 3 destruct H0.
      simpl. rewrite  H0. rewrite <- H0. 
      assert ( HS : bsize (he x t1) = sucBN ( bsize t1)). apply bsize_he.
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

Lemma change_suc_pred_eq : 
forall a b : BN, 
a = sucBN (b) <-> predBN a = b.
Admitted.

Lemma char_BTree : 
forall t : BTree, 
t = E \/ exists (a:A)(t1 t2: BTree), t = N a t1 t2.
Proof.
  intros.
  destruct t.
  + left. auto.
  + right. exists a. exists t1. exists t2. auto.
Qed.

Lemma lkp_he : 
forall (t:BTree) (x:A) (j:BN), 
t <> E -> j <BN predBN (bsize t) -> lookup_bn (hr t) j = lookup_bn t j.
Proof.
  intro.
  assert (HBal := allBal t).
  induction t.
  + contradiction.
  + intros.
    assert ( Ht1 : t1 = E \/ exists (a0 : A )(t1_1 t1_2 : BTree), t1 = N a0 t1_1 t1_2). apply char_BTree.
    (* casos t1 vacío y no vacío *)
    destruct Ht1.
    (* caso t1 vacío*)
    - rewrite H1 in *. assert ( Ht2 : t2 = E ). apply (leftE_leaf E t2 a); auto.
      rewrite Ht2 in *.
      simpl.
      destruct j; auto.
      * simpl in H0. apply ltBN_arefl in H0. contradiction.
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
           rewrite IHt1; auto.
           unfold not.
           intros. rewrite H14 in H1.
           discriminate.
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
           assert ( HTT : t2 <> E ). unfold not. intros. rewrite H5 in H3.
           rewrite H1 in H3. simpl in H3. apply ZnotSucBN_sym in H3. auto.
           destruct H4;
           rewrite  H4 in H0;
           rewrite H4 in IHt2;
           inversion H0;
           inversion HBal;
           rewrite IHt2; auto.
Qed.











