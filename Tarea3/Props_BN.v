(*
Verificación Formal - 2020-II
Archivo de definiciones - Números por paridad
*)

From TAREA3 Require Import Defs_BN.
Require Import ArithRing.



Lemma UInj: forall (a b:BN), U a = U b -> a = b.
Proof.
intros.
inversion H.
trivial.
Qed.

Lemma DInj: forall (a b:BN), D a = D b -> a = b.
Proof.
intros.
inversion H.
trivial.
Qed.


Lemma ZnotU: forall (a:BN), Z <> U a.
Proof.
intros.
discriminate.
Qed.

Lemma ZnotU_sym: forall (a:BN), U a <> Z.
Proof.
intros.
apply not_eq_sym.
apply ZnotU.
Qed.

Lemma ZnotD : forall (a:BN), Z <> D a.
Proof.
intros.
discriminate.
Qed.

Lemma ZnotD_sym : forall (a:BN), D a <> Z.
Proof.
intros.
apply not_eq_sym.
apply ZnotD.
Qed.

  (* Lemma UnotD: forall (a:BN), U a <> D a. La cambié por la siguiente. C.V. 29/nov/2016 *)
Lemma UnotD: forall (a b:BN), U a <> D b.
Proof.
intros.
discriminate.
Qed.

Lemma DnotU: forall (a b:BN), D a <> U b. (* La agregué. C.V. 29/nov/2016 *)
Proof.
intros.
discriminate.
Qed.

Lemma bnotU : forall (a:BN), U a <> a.
Proof.
intros.
induction a.
(*a = Z*)
intuition.
inversion H.
(*a=U a*)
intuition.
inversion H.
apply IHa in H1.
trivial.
(*a=D a*)
intuition.
inversion H.
Qed.

Lemma bnotD : forall (a:BN), D a <> a.
Proof.
intros.
induction a.
(*a = Z*)
intuition.
inversion H.
(*a=U a*)
intuition.
inversion H.
(*a=D a*)
intuition.
inversion H.
apply IHa in H1.
trivial.
Qed.

Theorem dec_eq_BN: forall (a b:BN), {a = b} + {a <> b}.
Proof. (* This can be done fully automatic with decide equality *)
decide equality.
Qed.




Lemma sucBNDU : forall (a:BN), a <> Z -> sucBN (D a) = U (sucBN a).
Proof.
intros.
destruct a.
contradict H.
trivial.
reflexivity.
reflexivity.
Qed.


Lemma ZnotSucBN: forall (a:BN), Z <> sucBN a.
Proof.
intros.
induction a.
simpl.
discriminate.
simpl.
discriminate.
simpl.
discriminate.
Qed.

Lemma ZnotSucBN_sym : forall (a:BN), sucBN a <> Z.
Proof.
  intros.
  apply not_eq_sym.
  apply ZnotSucBN.
Qed.

Lemma notSucBN : forall (a:BN), a <> sucBN a.
Proof.
intros.
destruct a.
simpl; discriminate.
simpl; discriminate.
simpl; discriminate.
Qed.


Lemma bnNonZ: forall (b:BN), b <> Z -> exists (c:BN), b = U c \/ b = D c.
Proof.
intros.
destruct b.
intuition.
exists b;left;trivial.
exists b;right;trivial.
Qed.




Lemma predBNUD: forall (a:BN), a <> Z -> predBN (U a) = D (predBN a).
Proof.
intros.
destruct a.
contradict H.
trivial.
reflexivity.
reflexivity.
Qed.

Lemma U_not: forall (i j :BN), U i <> U j -> i <> j.
Proof.
intros.
contradict H.
apply f_equal.
trivial.
Qed.

Lemma D_not: forall (i j :BN), D i <> D j -> i <> j.
Proof.
intros.
contradict H.
apply f_equal.
trivial.
Qed.


Lemma predsucBNinv: forall (a:BN), predBN (sucBN a) = a.
Proof.
intros.
induction a; intuition.
+ destruct a; intuition.
  - rewrite -> sucBNDU.
    rewrite -> predBNUD.
    rewrite -> IHa. auto.
    apply ZnotSucBN_sym.
    apply ZnotD_sym.
Qed.

Lemma DobleUUZ : 
forall (a : BN), Z <> (U (U a)) -> Z <> U a.
Proof.
  intros.
  induction a; apply ZnotU.
Qed.

Lemma sucpredBNinv: forall (a:BN), a <> Z -> sucBN (predBN a) = a.
Proof.
  intros.
  apply not_eq_sym in H.
  induction a; intuition.
  destruct a; intuition.
  destruct a; intuition.
  apply DobleUUZ in H as HA.
  rewrite -> predBNUD.
  rewrite -> sucBNDU.
  rewrite -> IHa. auto.
  auto.
  apply not_eq_sym.
  simpl. apply ZnotD.
  auto.
Qed.



Lemma toN_sucBN : forall (b : BN), toN(sucBN b) = S(toN b).
Proof.
induction b.
simpl.
trivial.

simpl.
ring.

simpl.
rewrite IHb.
ring.
Qed.

Lemma sucBN_toBN : forall (n : nat), sucBN (toBN n) = toBN (S n).
Proof.
destruct n.
simpl.
trivial.
simpl.
trivial.
Qed.

Lemma inverse_op : forall (n : nat), toN(toBN n) = n.
Proof.
induction n.
simpl.
trivial.
simpl.
rewrite toN_sucBN.
rewrite IHn.
trivial.
Qed.



Lemma SucBNinj: forall (a b : BN), sucBN a = sucBN b -> a = b.
Proof.
  intros.
  destruct a.
  induction b; auto.
  + simpl in H. discriminate.
  + simpl in H. inversion H. apply ZnotSucBN in H1. contradiction.
  + simpl in H. 
    apply (f_equal predBN) in H.
    rewrite -> predsucBNinv in H.
    simpl in H. auto.
  + simpl in H.
    apply (f_equal predBN) in H.
    rewrite -> predsucBNinv in H.
    rewrite -> predBNUD in H.
    rewrite -> predsucBNinv in H. auto.
    apply ZnotSucBN_sym.
Qed.



Lemma plusBN_toN : forall (a b : BN), toN(a ⊞ b) = toN a + toN b.
Proof.
intro.
induction a.
simpl.
trivial.
intros.
destruct b.
simpl.
ring.
simpl.
rewrite IHa.
ring.
simpl.
rewrite toN_sucBN.
rewrite IHa.
ring.
destruct b.
simpl.
ring.
simpl.
rewrite toN_sucBN.
rewrite IHa.
ring.
simpl.
rewrite toN_sucBN.
rewrite IHa.
ring.
Qed.



Lemma plus_neutro: forall (b:BN), b ⊞ Z = b.
Proof.
intros.
destruct b.
simpl;trivial.
simpl;trivial.
simpl;trivial.
Qed.


Lemma plus_neutro_l: forall (b:BN), Z ⊞ b = b.
Proof.
intros.
destruct b.
simpl;trivial.
simpl;trivial.
simpl;trivial.
Qed.

Lemma plus_U: forall (b : BN),  sucBN (b ⊞ b) = U b.
Proof.
intros.
induction b.
simpl.
trivial.
simpl.
rewrite IHb.
trivial.
simpl.
rewrite IHb.
simpl.
trivial.
Qed.



Lemma plus_D: forall (b : BN),  sucBN (sucBN b ⊞ b) = D b.
Proof.
intros.
induction b.
simpl.
trivial.
simpl.
rewrite plus_U.
trivial.
simpl.
rewrite IHb.
trivial.
Qed.


Lemma plusSuc : forall (b c: BN), sucBN (b ⊞ c) = sucBN b ⊞ c.
Proof.
  intro.
  induction b.
  + intros.
    rewrite -> plus_neutro_l.
    destruct c; auto.
  + intros.
    destruct c; auto.
  + intros.
    destruct c; try simpl; try specialize (IHb c); try rewrite -> IHb; auto.
Qed.


Lemma plus_toBN:  forall (n m: nat), toBN(n + m) = toBN n ⊞ toBN m.
Proof.
intros.
induction n.
simpl.
trivial.
simpl.
rewrite IHn.
rewrite <- plusSuc.
trivial.
Qed.


Lemma plus_UZ : forall a : BN, 
a ⊞ (U Z) = sucBN a.
Proof.
  intros.
  induction a.
  + auto.
  + simpl. 
    rewrite -> plus_neutro.
    auto.
  + simpl. rewrite -> plus_neutro.
    auto.
Qed.


Lemma plus_DZ : forall a : BN, 
a ⊞ (D Z) = sucBN ( sucBN a).
Proof.
  intros.
  induction a.
  + auto.
  + simpl. 
    rewrite -> plus_neutro.
    auto.
  + simpl. rewrite -> plus_neutro.
    auto.
Qed.

Lemma inverse_op_2 : forall (b:BN), toBN(toN b) = b.
Proof.
  intros.
  induction b.
  + auto.
  + simpl.
    do 2 rewrite -> plus_toBN.
    rewrite <- plus_n_O.
    rewrite -> IHb.
    simpl. rewrite -> plus_UZ.
    rewrite -> plus_U.
    auto.
  + simpl. do 2 rewrite -> plus_toBN.
    rewrite <- plus_n_O.
    rewrite -> IHb.
    simpl.
    rewrite -> plus_DZ.
    rewrite -> plusSuc.
    rewrite -> plus_D.
    auto.
Qed.


Lemma plusComm: forall (a b:BN), (a ⊞ b) = (b ⊞ a).
Proof.
  intro.
  induction a.
  + intros. rewrite -> plus_neutro. rewrite -> plus_neutro_l. auto.
  + destruct b; simpl; try specialize (IHa b); try rewrite -> IHa; auto.
  + destruct b; simpl; try specialize (IHa b); try rewrite -> IHa; auto.
Qed.


Lemma plusSuc_2 : forall (b c: BN), sucBN (b ⊞ c) = b ⊞ sucBN c.
Proof.
  intro.
  induction b.
  + simpl. auto.
  + destruct c; simpl; try specialize (IHb c); try rewrite -> IHb; try rewrite -> plus_neutro; auto.
  + destruct c;
    simpl;
    try rewrite -> plus_neutro;
    try specialize (IHb c);
    try rewrite -> IHb;
    auto.
Qed.

Lemma plusBN_Z_Z: forall (x y:BN), 
x ⊞ y = Z -> x = Z /\ y = Z.
Proof.
  intro.
  induction x;
  try destruct y;
      try intros;
      try simpl in H;
      try apply eq_sym in H;
      try apply ZnotD in H;
      try apply ZnotU in H;
      try contradiction;
      auto.
Qed.


Lemma UDCase: forall (x:BN), x <> Z -> exists (b:BN), x = U b \/ x = D b.
Proof.
intros.
destruct x.
intuition.
exists x;left;trivial.
exists x;right;trivial.
Qed.

Lemma suc_not_zero: forall (x:BN), sucBN x <> Z.
Proof.
intros.
destruct x.
simpl;discriminate.
simpl;discriminate.
simpl;discriminate.
Qed.

Lemma addition_a_a : forall (a b:BN), a ⊞ a = b ⊞ b -> a = b.
Proof.
intros.
apply (f_equal sucBN) in H.
rewrite plus_U in H.
rewrite plus_U in H.
apply UInj.
trivial.
Qed.

Lemma addition_SucBNa_a : forall (a b:BN), sucBN a ⊞ a = sucBN b ⊞ b -> a = b.
Proof.
intros.
rewrite <- plusSuc in H.
rewrite <- plusSuc in H.
apply SucBNinj in H.
apply (f_equal sucBN) in H.
rewrite plus_U in H.
rewrite plus_U in H.
apply UInj.
trivial.
Qed.


Lemma ltBN_arefl: forall (a:BN), ~ a <BN a.
Proof.
intros.
induction a.
unfold not.
intros.
inversion H.
contradict IHa.
inversion IHa.
trivial.
contradict IHa.
inversion IHa.
trivial.
Qed.

Create HintDb PNatDb.

Hint Resolve ltBN_arefl: PNatDb.

Lemma ltBN_asym: forall (a b:BN), a <BN b -> ~ b <BN a.
Proof.
intros.
induction H.
unfold not;intros.
inversion H.
unfold not;intros.
inversion H.
contradict IHltBN.
inversion IHltBN.
trivial.
unfold not;intros.
inversion H.
apply (ltBN_arefl a).
trivial.
(*exact (ltBN_arefl a H2).*)
unfold not;intros.
inversion H0.
intuition.
contradict IHltBN.
inversion IHltBN.
rewrite H2 in H.
trivial.
trivial.
contradict IHltBN.
inversion IHltBN.
trivial.
Qed.

Hint Resolve ltBN_asym: PNatDb.

(*Lemma ltBN_antisym: forall (a b:BN), ltBN a b -> ltBN b a -> *)

Lemma lt_noZ :
forall a : BN,
~ ( a <BN Z ).
Proof.
  unfold not.
  induction a; try apply ltBN_arefl; try intros; try inversion H. 
Qed.


Lemma ltBN_tr : 
forall (b c:BN), 
b <BN c -> forall (a:BN), a <BN b -> a <BN c.
Proof.
  intro.
  intro. intro.
  induction H.
  + intros.
    apply lt_noZ in H. contradiction.
  + intros.
    apply lt_noZ in H. contradiction.
  + intros.
    inversion H0.
    - constructor.
    - subst.
      constructor.
      specialize (IHltBN a1).
      apply IHltBN in H3. auto.
    - subst.
      constructor.
      specialize (IHltBN a1).
      apply IHltBN in H3. auto.
  + intros.
    inversion H.
    - constructor.
    - subst.
      constructor. auto.
    - subst.
      constructor. auto.
  + intros.
    inversion H0.
    - constructor.
    - subst.
      constructor.
      specialize (IHltBN a1).
      apply IHltBN in H3. auto.
    - subst. constructor.
      specialize (IHltBN a1).
      apply IHltBN in H3. auto.
  + intros. inversion H0.
    - constructor.
    - subst. constructor. auto.
    - subst. constructor.
      specialize (IHltBN a1).
      apply IHltBN in H3. auto.
    - constructor. specialize (IHltBN a1).
      apply IHltBN in H3. auto.
  + intros. inversion H0.
    - constructor.
    - subst. constructor. auto.
    - subst. constructor.
      specialize (IHltBN a1).
      apply IHltBN in H3. auto.
    - subst. constructor.
      specialize (IHltBN a1).
      apply IHltBN in H3. auto.
Qed.

Hint Resolve ltBN_tr: PNatDb.


Lemma ltBN_trans: forall (a b c:BN), a <BN b -> b <BN c -> a <BN c.
Proof.
intros.
eapply ltBN_tr.
eexact H0.
trivial.
Qed.

Hint Resolve ltBN_trans: PNatDb.

Lemma lt_lteqBN_trans: forall (a b c:BN), a <BN b -> b ≤BN c -> a <BN c.
Proof.
intros.
inversion H0.
rewrite H2 in H.
trivial.
eapply ltBN_trans.
eexact H.
trivial.
Qed.

Hint Resolve lt_lteqBN_trans: PNatDb.

Lemma lteqBN_trans: forall (a b c:BN), a ≤BN b -> b ≤BN c -> a ≤BN c.
Proof.
intros.
inversion H.
trivial.
inversion H0.
rewrite H5 in H.
trivial.
constructor.
eapply ltBN_trans.
eexact H1.
trivial.
Qed.

Hint Resolve lteqBN_trans: PNatDb.

Lemma ltDs: forall (a:BN), (D a) <BN (U (sucBN a)).
Proof.
intros.
induction a.
simpl.
constructor.
constructor.
simpl.
constructor.
constructor.
simpl.
constructor.
trivial.
Qed.

Hint Resolve ltDs: PNatDb.

Lemma lts: forall (a:BN), a <BN (sucBN a).
Proof.
intros.
induction a.
constructor.
simpl.
constructor.
simpl.
constructor.
trivial.
Qed.

Hint Resolve lts: PNatDb.

Lemma lteqs: forall (a:BN), a ≤BN (sucBN a).
Proof.
intros.
induction a.
constructor.
constructor.
simpl.
constructor.
constructor.
simpl.
constructor.
constructor.
inversion IHa.
contradict H0.
apply notSucBN.
trivial.
Qed.

Hint Resolve lteqs: PNatDb.

Lemma ltpred :
forall (a:BN),
a <> Z -> (predBN a) <BN a.
Proof.
  intros.
  apply bnNonZ in H.
  do 2 destruct H.
  + subst. induction x.
    - simpl. constructor.
    - simpl. constructor. auto.
    - simpl. do 2 constructor.
  + rewrite H. simpl.
    constructor.
Qed.


Hint Resolve ltpred: PNatDb.


Lemma lt1 : 
forall ( b a : BN), 
a <BN (sucBN b) -> a ≤BN b.
Proof.
  intros.
  destruct b.
  + simpl in H. destruct a.
    - constructor.
    - inversion H. apply lt_noZ in H2. contradiction.
    - inversion H. apply lt_noZ in H2. contradiction.
  + simpl in H. destruct a; inversion H; repeat constructor; auto.
  + simpl in H. inversion H.
    - repeat constructor.
    - repeat constructor.
Admitted.

    

Hint Resolve lt1: PNatDb.

Lemma Z_min_suc : 
forall a : BN, 
Z <BN sucBN (a).
Proof.
  induction a; constructor.
Qed.


Lemma le_lesuc : 
forall a b : BN, 
a <BN b -> a <BN sucBN b.
Proof.
  intros.
  induction H.
  + subst. apply Z_min_suc.
  + subst. apply Z_min_suc.
  + subst. simpl. constructor. auto.
  + subst. simpl. constructor. apply lts.
  + subst. simpl. constructor. auto.
  + subst. simpl. constructor. auto.
  + subst. simpl. constructor. auto.
Qed.

Lemma lt2 : 
forall (a b:BN), 
a ≤BN b -> a <BN (sucBN b).
Proof.
  intros.
  inversion H.
  + subst.
    apply lts.
  + subst.
    apply le_lesuc.
    auto.
Qed.


Hint Resolve lt2: PNatDb.

Lemma lteqBN_suc_pred : forall (a b:BN), a <> Z -> a ≤BN (sucBN b) -> (predBN a) ≤BN b.
Proof.
intros.
assert ((predBN a) <BN a).
apply ltpred.
trivial.
assert (predBN a <BN sucBN b).
eapply lt_lteqBN_trans.
eexact H1.
trivial.
apply lt1.
trivial.
Qed.

Hint Resolve lteqBN_suc_pred: PNatDb.


Lemma ltaux1: 
forall (j:BN), 
Z ≤BN (D j) -> Z ≤BN j.
Proof.
  intros.
  induction j; repeat constructor.
Qed.
  

Lemma lteqBN_refl : forall (b:BN), b ≤BN b.
Proof.
intros.
constructor.
Qed.

Lemma lteqBN_Z : forall (b:BN), Z ≤BN b.
Proof.
intros.
destruct b.
constructor.
constructor;constructor.
constructor;constructor.
Qed.

Theorem not_lt_suc : 
forall (a:BN), 
~ exists (b:BN), a <BN b /\ b <BN (sucBN a).
Proof.
Admitted.


Lemma trichotomy: forall (a b:BN), a <BN b \/ a=b \/ b <BN a.
Proof.
Admitted.
  

Lemma not_lt: forall (a b:BN), b ≤BN a -> ~ a <BN b.
Proof.
  unfold not.
  intros.
  inversion H.
  + subst. apply ltBN_arefl in H0. auto.
  + subst. apply ltBN_asym in H0. contradiction.
Qed.


Lemma sucBN_lt: forall (a b:BN), sucBN a <> b -> a <BN b -> (sucBN a) <BN b.
Proof.
Admitted.


Lemma lt_suc_lteq: forall (a b:BN), a <BN b -> (sucBN a) ≤BN b.
Proof.
Admitted.

Lemma lteqBN_suc: forall (a b:BN), a ≤BN b -> (sucBN a) ≤BN (sucBN b). 
Proof.
intros.
inversion H.
constructor.
apply lt_suc_lteq.
apply lt2.
trivial.
Qed.

(* Next lemmas are used for Okasaki's size *)

Lemma lteqBN_U_U:forall (a b:BN), (U a) ≤BN (U b) -> a ≤BN b.
Proof.
intros.
inversion H.
constructor.
inversion H0.
constructor.
trivial.
Qed.

Lemma lteqBN_D_D : forall (a b : BN), (D a) ≤BN (D b)-> a ≤BN b.
Proof.
intros.
inversion H.
constructor.
inversion H0.
constructor.
trivial.
Qed.

Lemma lteqBN_U_D:forall (a b:BN), (U a) ≤BN (D b) -> a ≤BN b.
Proof.
intros.
inversion H.
inversion H0.
constructor.
constructor.
trivial.
Qed.

Lemma lteqBN_D_U:forall (a b:BN), (D a) ≤BN (U b) -> a ≤BN b.
Proof.
intros.
inversion H.
inversion H0.
constructor.
trivial.
Qed.

Lemma bbalCond_eqs: forall (s t:BN), t ≤BN s -> s ≤BN sucBN t -> s = t \/ s = sucBN t.  (* nov-2016, C.V. *)
Proof.
intros.
inversion H.
intuition.
inversion H0.
intuition.
exfalso.
eapply not_lt_suc.
exists s.
split.
exact H1.
assumption.
Qed.


Lemma lt_U : 
forall (a b:BN), 
a <BN b <-> (U a) <BN U b.
Proof.
  split.
  + constructor. auto.
  + intros. inversion H. auto.
Qed.


Lemma lt_D: forall (a b:BN), a <BN b <-> (D a) <BN D b.
Proof.
  split.
  + constructor. auto.
  + intros. inversion H. auto.
Qed.


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

Lemma lt_Z_diff : 
forall a : BN,
Z <BN a -> a <> Z.
Proof.
  intros.
  intuition.
  rewrite <- H0 in H.
  apply ltBN_arefl in H.
  auto.
Qed.

Lemma lt_predBN_lteq : 
forall a : BN,
Z <BN a -> (predBN a) ≤BN a.
Proof.
  intros.
  apply lt_Z_diff in H.
  constructor.
  apply ltpred.
  auto.
Qed.

Lemma lt_imp_lteq :
forall ( a b : BN),
a <BN b -> a ≤BN b.
Proof.
  intros. constructor. auto.
Qed.

Lemma lt_pred_noZ : 
forall ( b a : BN), 
Z <> a -> a ≤BN b -> (predBN a) ≤BN b.
Proof.
  intros.
  apply not_eq_sym in H.
  apply ltpred in H.
  apply lt_imp_lteq in H.
  apply (lteqBN_trans _ a _ ); auto.
Qed.

Lemma conmt_sucBN_predBN_noZ : 
forall a : BN, 
a <> Z -> sucBN ( predBN a) = predBN (sucBN a).
Proof.
  induction a.
  + contradiction.
  + intros. destruct a.
    - simpl.  auto.
    - assert ( HA : U a <> Z). apply ZnotU_sym.
      assert ( HB : predBN (U (U a )) = D (predBN  (U a))). auto.
      rewrite HB.
      assert ( HC : sucBN (D (predBN (U a)))  = U (sucBN (predBN (U a)))). auto.
      rewrite HC.
      apply IHa in HA.
      rewrite HA.
      simpl.  auto.
    - auto.
  + intros. destruct a.
    - auto.
    - auto.
    - assert ( HA : D a <> Z). apply ZnotD_sym.
      apply IHa in HA.
      assert ( HB : sucBN (D (D a)) = U ( sucBN ( D a))). auto.
      rewrite HB.
      assert ( HC : predBN (U (sucBN (D a))) = D (predBN (sucBN (D a)))). auto.
      rewrite HC.
      rewrite <- HA.
      auto.
Qed.

Lemma plus_Ub_notZ : 
forall a b : BN,
a ⊞ U b <> Z.
Proof.
  unfold not.
  intros.
  apply plusBN_Z_Z in H.
  destruct H.
  apply ZnotU_sym in H0.
  auto.
Qed.

Lemma plus_Db_notZ : 
forall a b : BN,
a ⊞ D b <> Z.
Proof.
  unfold not.
  intros.
  apply plusBN_Z_Z in H.
  destruct H.
  apply ZnotD_sym in H0.
  auto.
Qed.

Lemma plusPred : 
forall a b : BN ,
b <> Z -> a ⊞ predBN (b) = predBN ( a ⊞ b).
Proof.
  intro.
  induction a.
  + simpl. auto.
  + intros. destruct b.
    - contradiction.
    - destruct b.
      * simpl.
        rewrite (plus_neutro a).
        auto.
      * assert ( U b <> Z ). apply ZnotU_sym. 
        assert ( predBN (U ( U b )) = D ( predBN ( U b))). auto.
        rewrite H1.
        specialize (IHa (U b) ).
        apply IHa in H0 as HT.
        simpl. 
        simpl in HT.
        rewrite HT.
        rewrite sucpredBNinv. auto.
        apply plus_Ub_notZ.
      * assert ( D b <> Z ). apply ZnotD_sym. 
        assert ( predBN (U ( D b )) = D ( predBN ( D b))). auto.
        rewrite H1.
        assert ( U a ⊞ D (predBN (D b)) = U( sucBN ( a ⊞ predBN (D b) )) ). auto.
        rewrite H2.
        specialize (IHa (D b)).
        apply IHa in H0 as HT.
        rewrite HT. 
        rewrite sucpredBNinv. auto.
        apply plus_Db_notZ.
    - simpl.
      destruct (bnNonZ (sucBN (a ⊞ b))).
      apply ZnotSucBN_sym.
      destruct H0;
       rewrite H0; rewrite <- H0;
       rewrite predsucBNinv; auto.
  + intros. destruct b.
    - contradiction.
    - destruct b.
      * simpl. rewrite plus_neutro.
        destruct (bnNonZ (sucBN a)). apply ZnotSucBN_sym.
        destruct H0; 
         rewrite  H0; rewrite <- H0;
         rewrite predsucBNinv; auto.
      * assert ( U b <> Z ). apply ZnotU_sym. 
        assert ( predBN (U ( U b )) = D ( predBN ( U b))). auto.
        rewrite H1.
        specialize (IHa (U b)).
        assert ( D a ⊞ D (predBN (U b)) = D ( sucBN ( a ⊞ predBN (U b)))). auto.
        rewrite H2. 
        apply IHa in H0 as HT.
        rewrite HT.
        assert ( D a ⊞ U (U b) =   U(sucBN ( a ⊞ (U b)))). auto.
        rewrite H3.
        simpl.
        destruct (bnNonZ (sucBN (a ⊞ U b))). apply ZnotSucBN_sym.
        assert ( a ⊞ U b <> Z). apply plus_Ub_notZ.
        destruct H4; 
         rewrite  H4; rewrite <- H4;
         rewrite predsucBNinv; rewrite sucpredBNinv; auto.
      * simpl.
        assert ( sucBN (a ⊞ U b) = a ⊞ (D b)). rewrite (plusComm a (U b)).
        rewrite plusSuc. rewrite (plusComm (sucBN (U b)) a). auto.
        destruct (bnNonZ (sucBN (a ⊞ D b))). apply ZnotSucBN_sym.
        destruct H1;
         rewrite H1; rewrite <- H1; rewrite H0; 
         rewrite predsucBNinv; auto.
    - simpl.
      auto.
Qed.

Lemma plusPred_sym : 
forall a b : BN ,
a<> Z -> (predBN a) ⊞ b = predBN ( a ⊞ b).
Proof.
  intros.
  rewrite (plusComm (predBN a) b).
  rewrite plusPred.
  rewrite (plusComm b a).
  auto.
  auto.
Qed.

