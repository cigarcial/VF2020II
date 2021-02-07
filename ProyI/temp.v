
Fixpoint Open ( z : Name )( T : Prepro ) {struct T} : Prepro := 
match T with 
  | Prechan_res P => Open_Rec 0 z P.
  | Prechan_input x P => Open_Rec 0 z P.
  | Prechan_replicate x P  => Open_Rec 0 z P.
  | _ => Open_Rec 0 z T.
end.



  induction P.
  + simpl. constructor.
  + simpl. inversion H0. 
    assert (HZ : Process_Name z ). apply (MalDiseno z L); auto.
    assert (HA : ((Close_Name 0 x x0 = x0) \/ (Close_Name 0 x x0 = BName 0)) ). apply Aux3; auto.
    assert (HB : ((Close_Name 0 x y = y) \/ (Close_Name 0 x y = BName 0)) ). apply Aux3; auto.
    destruct HA.
    - destruct HB.
      * rewrite -> H6.
    rewrite -> H7.
    unfold Open.
    simpl.
    assert (HC : Open_Name 0 z x0 = x0). apply Aux5; auto.
    assert (HD : Open_Name 0 z y = y). apply Aux5; auto.
    rewrite -> HC.
    rewrite -> HD.
    auto.
      * rewrite -> H6.
    rewrite -> H7.
    unfold Open.
    simpl. 
    assert (HC : Open_Name 0 z x0 = x0). apply Aux5; auto.
    rewrite -> HC.
    auto.
    - destruct HB.
      * rewrite -> H6.
      rewrite -> H7.
      unfold Open.
      simpl.
      assert (HC : Open_Name 0 z y = y). apply Aux5; auto.
      rewrite -> HC.
      auto.
      * rewrite -> H6.
      rewrite -> H7.
      unfold Open. simpl.
      auto.
  + unfold Open. simpl. inversion H0.
    constructor; apply IHP1 || apply IHP2; auto.
  + unfold Open. simpl. inversion H0.
    assert (HZ : Process_Name z ). apply (MalDiseno z L). auto.
    assert (HA : ((Close_Name 0 x x0 = x0) \/ (Close_Name 0 x x0 = BName 0)) ). apply Aux3; auto.
    assert (HB : ((Close_Name 0 x y = y) \/ (Close_Name 0 x y = BName 0)) ). apply Aux3; auto.
    constructor.
      - destruct HA.
        * rewrite -> H7.
          assert (HC : Open_Name 0 z x0 = x0). apply Aux5; auto.
          rewrite -> HC. auto.
        * rewrite -> H7.
          assert (HC : Open_Name 0 z (BName 0) = z). apply Aux6; auto.
          rewrite -> HC.
          auto.
      - destruct HB.
        * rewrite -> H7.
          assert (HC : Open_Name 0 z y = y). apply Aux5; auto.
          rewrite -> HC. auto.
        * rewrite -> H7.
          assert (HC : Open_Name 0 z (BName 0) = z). apply Aux6; auto.
          rewrite -> HC.
          auto.
  + unfold Open. simpl. 
    assert (HZ : Process_Name z). apply (MalDiseno z L); auto.
    inversion H0.
    assert (HA : ((Close_Name 0 x x0 = x0) \/ (Close_Name 0 x x0 = BName 0)) ). apply Aux3; auto.
    constructor.
    destruct HA.
    - rewrite -> H4.
      assert (HC : Open_Name 0 z x0 = x0). apply Aux5; auto.
      rewrite -> HC. auto.
    - rewrite -> H4.
      assert (HC : Open_Name 0 z (BName 0) = z). apply Aux6; auto.
      rewrite -> HC. auto.
  + unfold Open. simpl. inversion H0.
    constructor.
    - admit.
    - auto.
  + unfold Open. simpl. 
    intros. admit.
  + admit.
  + admit.
Admitted.
     
    
    
    
    
    
    
    
    

Inductive Sequent : Type := seqnt ( D F G : list Assignment ) ( P : Prepro ) : Sequent.

Notation " D ';;;'  F '!-' P ':::' G " :=  (seqnt D F G P)(at level 60). 





inversion H.
  + rewrite <- H7 in H0. apply No_Red_AX1 in H0. contradiction.
  + rewrite <- H7 in H0. apply No_Red_AX1 in H0. contradiction.
  + rewrite <- H9 in H0. apply No_Red_AX2 in H0. contradiction.
  + admit. 
  + admit. 
  + rewrite <- H9 in H0. apply No_Red_AX2 in H0. contradiction.
  + rewrite <- H11 in H0. apply No_Red_AX4 in H0. contradiction.
  + rewrite <- H15 in H0. apply No_Red_AX5 in H0; try contradiction;
    auto.
  + rewrite <- H11 in H0. apply No_Red_AX4 in H0. contradiction.
  + rewrite <- H15 in H0. apply No_Red_AX5 in H0; try contradiction;
    auto.
  + rewrite <- H11 in H0. apply No_Red_AX4 in H0. contradiction.
  + rewrite <- H15 in H0. apply No_Red_AX5 in H0; try contradiction; 
    auto.
  + rewrite <- H10 in H0. apply No_Red_AX6 in H0. contradiction.
  + rewrite <- H6 in H0. inversion H0.
  + rewrite <- H10 in H0. apply No_Red_AX6 in H0. contradiction.
  + rewrite <- H6 in H0. inversion H0.
  + rewrite <- H11 in H0. apply No_Red_AX7 in H0; try contradiction; 
    auto. 
  + rewrite <- H11 in H0. apply No_Red_AX7 in H0; try contradiction; auto.
  +






















