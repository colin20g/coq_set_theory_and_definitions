(** This file provide hilbert systems for propositional logic,
and various tautologies that will be used in the other systems we'll define. *)

Section Intuitionnist_propositional_implicative_logic_tool_kit.

  Variable P:Type.
  Variable C:P -> P -> P.
  Variable T: P -> Type.
  Variable KA: forall x y:P, T (C x (C y x)).
  Variable SA: forall x y z:P, T (C (C x (C y z)) (C (C x y) (C x z))).
  Variable MP: forall x y:P, T (C x y) -> T x -> T y.

  Notation "|- f" := (T f) (at level 61).
  Notation kf := (fun x y:P => C x (C y x)).
  Notation sf := (fun x y z:P => C (C x (C y z)) (C (C x y) (C x z))).
  Notation iF := (fun x:P => C x x).
  Notation bf := (fun x y z:P => C (C y z) (C (C x y) (C x z))).
    
  Ltac ka := apply KA.
  Ltac sa := apply SA.
  Ltac mp z := apply MP with (x:=z).
  
  Notation hs_sk_hypothetical_modus_ponens:=
       (fun (x y z : P) (prcxcyz : |- C x (C y z)) (prcxy : |- C x y) =>
          MP (C x y) (C x z) (MP (C x (C y z)) (C (C x y) (C x z)) (SA x y z) prcxcyz) prcxy).

  Ltac hmp t:= apply hs_sk_hypothetical_modus_ponens with (y:=t).
  
  Notation hs_sk_weakening:=
    (fun (x y : P) (prx : |- x) => MP x (C y x) (KA x y) prx).
  
  Ltac we := apply hs_sk_weakening.
  
  Definition hs_sk_i (x:P): |- C x x.
  Proof.
    hmp (C x x). ka. ka.
  Defined.
  
  Ltac ia := apply hs_sk_i.

  Definition hs_sk_syllogism (x y z:P) (prcxy: |- C x y) (prcyz: |- C y z): |- C x z.
  Proof.
    hmp y.
    mp (C y z). ka.
    assumption.
    assumption.
  Defined.

  Ltac syl t:= apply hs_sk_syllogism with (y:=t).
  
  Definition hs_sk_b (x y z:P): |- C (C y z) (C (C x y) (C x z)).
  Proof.
    syl (C x (C y z)). ka. sa.
  Defined.

  Ltac ba := apply hs_sk_b.

  Definition hs_sk_permutation (x y z:P) (prcxcyz: |- C x (C y z)) (pry: |- y): |- C x z.
  Proof.
    hmp y.
    assumption.
    mp y. ka. assumption.
  Defined.
  
  Ltac sw1 t:= apply hs_sk_permutation with (y:=t).
  
  Definition hs_sk_polarity_left (x y z:P) (pr: |- C x y): |- C (C y z) (C x z).
  Proof.
    sw1 (C x y). ba. assumption.
  Defined.

  Ltac pl := apply hs_sk_polarity_left.
  
  Definition hs_sk_polarity_right (x y z:P) (pr: |- C x y): |- C (C z x) (C z y).
  Proof.
    mp (C z (C x y)). sa.
    mp (C x y). ka. assumption.
  Defined.

  Ltac pr := apply hs_sk_polarity_right.
  
  Definition hs_sk_w (x y:P): |- C (C x (C x y)) (C x y).
  Proof.
    hmp (C x x). sa.
    mp (kf x (C x y)). sa. ka.
  Defined.

  Ltac wa := apply hs_sk_w.
  
  Definition hs_sk_permutation2 (x y z:P) (pr: |- C x (C y z)): |- C y (C x z).
  Proof.
    mp (kf y x).
    pr.
    mp (C x (C y z)). sa. assumption. ka.
  Defined.

  Ltac sw2 := apply hs_sk_permutation2.
  
  Definition hs_sk_q (x y z:P): |- C (C x y) (C (C y z) (C x z)).
  Proof.
    sw2; ba.  
  Defined.      

  Ltac qa := apply hs_sk_q.
  
  Definition hs_sk_t (x y:P): |- C x (C (C x y) y).
  Proof.
    sw2; ia.
  Defined.

  Definition hs_sk_c (x y z:P): |- C (C x (C y z)) (C y (C x z)).
  Proof.
    sw1 (kf y x).
    syl (C (C x y) (C x z)). sa. ba. ka.
  Defined.
  
End Intuitionnist_propositional_implicative_logic_tool_kit.

Record classical_propositional_implies_wrong_system:=
  make_cpiw
    {
      CPIW_Sentence: Type;
      cpiw_implies: CPIW_Sentence -> CPIW_Sentence -> CPIW_Sentence;
      cpiw_wrong: CPIW_Sentence;
      cpiw_theorem: CPIW_Sentence -> Type;
      cpiw_k: forall a b:CPIW_Sentence,
          cpiw_theorem (cpiw_implies a (cpiw_implies b a));
      cpiw_s: forall a b c:CPIW_Sentence,
          cpiw_theorem
            (cpiw_implies
               (cpiw_implies a (cpiw_implies b c))
               (cpiw_implies (cpiw_implies a b) (cpiw_implies a c)));
      cpiw_absurd: forall a:CPIW_Sentence,
          cpiw_theorem
            (cpiw_implies (cpiw_implies (cpiw_implies a cpiw_wrong) cpiw_wrong) a);
      cpiw_modus_ponens: forall a b:CPIW_Sentence,
          cpiw_theorem (cpiw_implies a b) ->
          cpiw_theorem a ->
          cpiw_theorem b
    }.

Section adding_hypotheses_to_a_theory.

  Variable P:Type.
  Variable T: P -> Type.
  Variable h: P.

  Inductive cpiw_add_hypothesis: P -> Type:=
  |cpiw_new_hypothesis: cpiw_add_hypothesis h
  |cpiw_base_hypothesis: forall x:P, T x -> cpiw_add_hypothesis x.
  
End adding_hypotheses_to_a_theory.


Section first_sample_theorems.

  Variable X:classical_propositional_implies_wrong_system.

  Notation P:= (CPIW_Sentence X).
  Notation C:= (cpiw_implies X).
  Notation T := (cpiw_theorem X).
  Notation W:= (cpiw_wrong X).
  Notation MP := (cpiw_modus_ponens X).
  Notation KA:= (cpiw_k X).
  Notation SA:= (cpiw_s X).
  Notation AA:= (cpiw_absurd X).                  

  Notation "|- f":= (cpiw_theorem X f) (at level 61).

  Definition cpiw_k_weakening (x y:P) (pry: |- y): |- C x y.
  Proof.
    apply MP with (a:=y). apply KA. assumption.
  Defined.

  Definition cpiw_i (a:P): |- C a a := hs_sk_i P C T KA SA MP a.

  Notation IA := cpiw_i.
  
  Definition cpiw_syllogism (x y z:P) (prcxy:|- C x y) (prcyz: |- C y z): |- C x z:=
    hs_sk_syllogism P C T KA SA MP x y z prcxy prcyz.

  Notation SYL:= cpiw_syllogism.

  Definition cpiw_permutation (x y z:P) (prcxcyz: |- C x (C y z)) (pry: |- y): |- C x z:=
    hs_sk_permutation P C T KA SA MP x y z prcxcyz pry.
  
  Notation PER := cpiw_permutation.
  
  Definition cpiw_weak_peirce (x:P) (prccxwx: |- C (C x W) x): |- x:=
    MP (C (C x W) W) x (AA x)
       (MP (C (C x W) x) (C (C x W) W)
           (MP (C (C x W) (C x W)) (C (C (C x W) x)
                                      (C (C x W) W)) (SA (C x W) x W) (IA (C x W)))
           prccxwx).

  Notation WP:= cpiw_weak_peirce.

  Definition cpiw_b (x y z:P):|- C (C y z) (C (C x y) (C x z)):=
    hs_sk_b P C T KA SA MP x y z.
  
  Notation BA := cpiw_b.
    
  Definition cpiw_w (x y:P): |- C (C x (C x y)) (C x y):=
    hs_sk_w P C T KA SA MP x y.

  Definition cpiw_t (x y:P): |- C x (C (C x y) y):=
    hs_sk_t P C T KA SA MP x y.

  Definition cpiw_q (x y z:P):|- C (C x y) (C (C y z) (C x z)):=
    hs_sk_q P C T KA SA MP x y z.

  Definition cpiw_c (x y z:P):|- C (C x (C y z)) (C y (C x z)):=
    hs_sk_c P C T KA SA MP x y z.
  
  Definition cpiw_cases (x y:P) (prcxy: |- C x y) (prccxwy: |- C (C x W) y): |- y:=
    WP y (SYL (C y W) (C x W) y (PER (C y W) (C x y) (C x W) (BA x y W) prcxy) prccxwy).
  
End first_sample_theorems.

Section the_deduction_procedure.

  Variable P:Type.
  Variable C:P -> P -> P.
  Variable W:P.

  Notation add_hyp := (cpiw_add_hypothesis P).
  Notation new_hyp := (cpiw_new_hypothesis P).
  Notation base_hyp := (cpiw_base_hypothesis P).

  Section Hilbert_System_proofs.

    Variable T:P -> Type.

    Inductive CPIW_Hilbert_Proof: P -> Type:=
    |cpiwhp_ax: forall x:P, T x -> CPIW_Hilbert_Proof x
    |cpiwhp_k_axiom: forall a b:P,
          CPIW_Hilbert_Proof (C a (C b a))
    |cpiwhp_s_axiom: forall a b c:P,
          CPIW_Hilbert_Proof (C (C a (C b c)) (C (C a b) (C a c)))
    |cpiwhp_absurd_axiom: forall a:P,
          CPIW_Hilbert_Proof (C (C (C a W) W) a)
    |cpiwhp_modus_ponens: forall a b:P,
          CPIW_Hilbert_Proof (C a b) ->
          CPIW_Hilbert_Proof a ->
          CPIW_Hilbert_Proof b.

    Definition CPIWHP: classical_propositional_implies_wrong_system:=
      make_cpiw P C W CPIW_Hilbert_Proof cpiwhp_k_axiom cpiwhp_s_axiom
                cpiwhp_absurd_axiom cpiwhp_modus_ponens.

    Definition cpiwhp_k_weakening: forall x y:P,
        CPIW_Hilbert_Proof y -> CPIW_Hilbert_Proof (C x y):=
      cpiw_k_weakening (CPIWHP).

    Definition cpiwhp_i:forall a:P, CPIW_Hilbert_Proof (C a a):= cpiw_i (CPIWHP).

    Definition cpiwhp_syllogism: forall x y z:P,
        CPIW_Hilbert_Proof (C x y) ->
        CPIW_Hilbert_Proof (C y z) ->
        CPIW_Hilbert_Proof (C x z) := cpiw_syllogism (CPIWHP).       

    Definition cpiwhp_permutation: forall x y z:P,
        CPIW_Hilbert_Proof (C x (C y z)) ->
        CPIW_Hilbert_Proof y ->
        CPIW_Hilbert_Proof (C x z):= cpiw_permutation (CPIWHP).    
    
  End Hilbert_System_proofs.
  
  Section the_main_results.

    Variable T: P -> Type.
    Variable h:P.
    
    Notation T' := (add_hyp T h).
    Notation "U |- x" := (CPIW_Hilbert_Proof U x) (at level 61).

    Section general_weakening.

      Variable U:P -> Type.
      Variable subtheory: forall x:P, T x -> U x.

      Fixpoint cpiwhp_general_weakening (f:P) (pr: T |- f):
        U |- f:=
        match pr in (_ |- p) return (U |- p) with
        | cpiwhp_ax _ x t => cpiwhp_ax U x (subtheory x t)
        | cpiwhp_k_axiom _ a b => cpiwhp_k_axiom U a b
        | cpiwhp_s_axiom _ a b c => cpiwhp_s_axiom U a b c
        | cpiwhp_absurd_axiom _ a => cpiwhp_absurd_axiom U a
        | cpiwhp_modus_ponens _ a b pr1 pr2 =>
          cpiwhp_modus_ponens U a b (cpiwhp_general_weakening (C a b) pr1)
                              (cpiwhp_general_weakening a pr2)
        end.
      
    End general_weakening.

    Definition cpiwhp_hypothesis_weakening (x:P) (prx: T |- x): T' |- x:=
      cpiwhp_general_weakening T' (base_hyp T h) x prx.
    
    Fixpoint cpiwhp_unoptimized_deduction_theorem
             (f:P)
             (pr: T' |- f)
             {struct pr}:
      T |- C h f:=
      match pr in (_ |- p) return (T |- C h p) with
      | cpiwhp_ax _ _ a =>
        match a in (cpiw_add_hypothesis _ _ _ y) return (T |- C h y) with
        | cpiw_new_hypothesis _ _ _ => cpiw_i (CPIWHP T) h
        | cpiw_base_hypothesis _ _ _ x0 t =>
          cpiw_k_weakening (CPIWHP T) h x0 (cpiwhp_ax T x0 t)
        end
      | cpiwhp_k_axiom _ a b => cpiw_k_weakening
                                  (CPIWHP T) h (C a (C b a)) (cpiwhp_k_axiom T a b)
      | cpiwhp_s_axiom _ a b c =>
        cpiw_k_weakening (CPIWHP T) h (C (C a (C b c)) (C (C a b) (C a c)))
                         (cpiwhp_s_axiom T a b c)
      | cpiwhp_absurd_axiom _ a =>
        cpiw_k_weakening (CPIWHP T) h (C (C (C a W) W) a) (cpiwhp_absurd_axiom T a)
      | cpiwhp_modus_ponens _ a b pr1 pr2 =>
        cpiwhp_modus_ponens
          T (C h a) (C h b)
          (cpiwhp_modus_ponens
             T (C h (C a b)) (C (C h a) (C h b)) (cpiwhp_s_axiom T h a b)
             (cpiwhp_unoptimized_deduction_theorem (C a b) pr1))
          (cpiwhp_unoptimized_deduction_theorem a pr2)
      end.

    (** Just above we defined the most well known version of the deduction theorem.
     Now we give another one which produce smaller files. This is the one we'll use
     further in the text.*)
    
    Fixpoint cpiw_proof_hypothesis_usage
             (f:P)
             (pr:T'|- f)
             {struct pr}:bool * bool.
    Proof.
      destruct pr.
      destruct c. apply (true,true).
      apply (false,false).
      apply (false,false).
      apply (false,false).
      apply (false,false).
      apply (false, orb (snd (cpiw_proof_hypothesis_usage (C a b) pr1))
                        (snd (cpiw_proof_hypothesis_usage a pr2))).
    Defined.
    
    Definition cpiw_phu_extract_id: forall
        (f:P)
        (pr: T' |- f)
        (e:fst (cpiw_proof_hypothesis_usage f pr) = true), f = h.
    Proof.
      intros.
      destruct pr.
      simpl in e. destruct c. reflexivity. 
      simpl in e. inversion e.
      simpl in e. inversion e.
      simpl in e. inversion e.
      simpl in e. inversion e.
      simpl in e. inversion e.            
    Defined.

    Definition ciw_bool_cases (R:Type) (b:bool):
      (b = true -> R) -> (b = false -> R) -> R.
    Proof.
      destruct b.
      intros. apply X; reflexivity.
      intros. apply X0; reflexivity.
    Defined.
    
    Fixpoint cpiw_phu_extract_unused
             (f:P)
             (pr:T' |- f)
             {struct pr}:
      snd (cpiw_proof_hypothesis_usage f pr) = false ->
      T |- f.
    Proof.
      intros.
      destruct pr.
      destruct c. simpl in H. inversion H.
      apply cpiwhp_ax. assumption.
      apply cpiwhp_k_axiom.
      apply cpiwhp_s_axiom.
      apply cpiwhp_absurd_axiom.      
      simpl in H.
      apply ciw_bool_cases with (b:= snd (cpiw_proof_hypothesis_usage (C a b) pr1)).
      intro.
      rewrite H0 in H. simpl in H. inversion H.
      intro.
      apply ciw_bool_cases with (b:= snd (cpiw_proof_hypothesis_usage a pr2)).
      intro.
      rewrite H0 in H; rewrite H1 in H; simpl in H. inversion H.
      intro. apply cpiwhp_modus_ponens with (a:=a).
      apply cpiw_phu_extract_unused with (pr:= pr1). assumption.
      apply cpiw_phu_extract_unused with (pr:= pr2). assumption.
    Defined.

    (** We give inlined versions of functions we've already used.*)
    
    Notation idp_tool:=
      (cpiwhp_modus_ponens
         T (C h (C h h)) (C h h)
         (cpiwhp_modus_ponens
            T (C h (C (C h h) h)) (C (C h (C h h)) (C h h))
            (cpiwhp_s_axiom
               T h (C h h) h) (cpiwhp_k_axiom T h (C h h))) (cpiwhp_k_axiom T h h)).

    Notation we_tool:=
      (fun (x : P) (px : T |- x) => cpiwhp_modus_ponens T x (C h x) (cpiwhp_k_axiom T x h) px).

    Notation syl_tool:=
      (fun (x y : P) (prcxy : T |- C x y) (prchx : T |- C h x) =>
         cpiwhp_modus_ponens
           T (C h x) (C h y)
           (cpiwhp_modus_ponens
              T (C h (C x y)) (C (C h x) (C h y)) (cpiwhp_s_axiom T h x y)
              (cpiwhp_modus_ponens
                 T (C x y) (C h (C x y)) (cpiwhp_k_axiom T (C x y) h) prcxy)) prchx).

    Notation perm_tool:=
      (fun (x y : P) (prchcxy : T |- C h (C x y)) (prx : T |- x) =>
         cpiwhp_modus_ponens
           T (C h x) (C h y)
           (cpiwhp_modus_ponens
              T (C h (C x y)) (C (C h x) (C h y)) (cpiwhp_s_axiom T h x y) prchcxy)
           (cpiwhp_modus_ponens T x (C h x) (cpiwhp_k_axiom T x h) prx)).
   
    Fixpoint cpiwhp_deduction_theorem
             (f:P)
             (pr:T' |- f)
             {struct pr}:
      T |- (C h f).
    Proof.
      destruct pr.
      destruct c.
      apply cpiw_i with (X:= CPIWHP T).
      apply we_tool.
      apply cpiwhp_ax; assumption.
      apply we_tool; apply cpiwhp_k_axiom.
      apply we_tool; apply cpiwhp_s_axiom.
      apply we_tool; apply cpiwhp_absurd_axiom.
      apply ciw_bool_cases with (b:=snd (cpiw_proof_hypothesis_usage (C a b) pr1)).
      intros.
      apply ciw_bool_cases with (b:=snd (cpiw_proof_hypothesis_usage a pr2)).
      intros. 
      apply cpiwhp_modus_ponens with (a:= C h a).
      apply cpiwhp_modus_ponens with (a:= C h (C a b)).
      apply cpiwhp_s_axiom.
      apply cpiwhp_deduction_theorem; apply pr1.
      apply cpiwhp_deduction_theorem; apply pr2.
      intros.
      apply cpiw_phu_extract_unused in H0.
      apply perm_tool with (x:=a).
      apply cpiwhp_deduction_theorem; apply pr1. assumption.
      intros.
      apply cpiw_phu_extract_unused in H.
      apply ciw_bool_cases with (b:=fst (cpiw_proof_hypothesis_usage a pr2)).
      intros. apply cpiw_phu_extract_id in H0. rewrite <- H0. assumption.
      apply ciw_bool_cases with (b:=snd (cpiw_proof_hypothesis_usage a pr2)).
      intros. apply syl_tool with (x:=a).
      assumption. apply cpiwhp_deduction_theorem. assumption. 
      intros.
      apply cpiwhp_modus_ponens with (a:=b). apply cpiwhp_k_axiom.
      apply cpiwhp_modus_ponens with (a:=a). assumption.
      apply cpiw_phu_extract_unused in H0. assumption. 
    Defined.
      
  End the_main_results.

  Section Hilbert_systems_theorems.

    Ltac ax := apply cpiwhp_ax.
    Ltac ka := apply cpiwhp_k_axiom.
    Ltac sa := apply cpiwhp_s_axiom.
    Ltac aa := apply cpiwhp_absurd_axiom.
    Ltac mp v := apply cpiwhp_modus_ponens with (a:=v).
    Ltac ded := apply cpiwhp_deduction_theorem.
    Ltac nh := apply new_hyp.
    Ltac bh := apply base_hyp.
    Ltac hw := apply cpiwhp_hypothesis_weakening.
    
    Notation "U |- x" := (CPIW_Hilbert_Proof U x) (at level 61).

    Definition cpiwhp_explosion: forall (T: P -> Type) (x:P),
        T |- W -> T |- x.
    Proof.
      intros.
      mp (C (C x W) W). aa.
      mp W. ka. assumption.
    Defined.

    Definition cpiwhp_explosion_formula: forall (T: P -> Type) (x:P),
        T |- C W x.
    Proof.
      intros.
      ded.
      apply cpiwhp_explosion.
      ax; nh.
    Defined.
    
    Definition cpiwhp_cases_formula: forall (T:P -> Type) (x y:P),
        T |- C (C (C x W) y) (C (C x y) y).
    Proof.
      intros.
      ded; ded.
      apply cpiw_cases with (X := CPIWHP (add_hyp (add_hyp T (C (C x W) y)) (C x y)))(x:=x).
      simpl.
      ax; nh.
      ax; bh; nh.
    Defined.

    Definition cpiwhp_implicative_cases_formula: forall (T:P -> Type) (x y z:P),
        T |- C (C (C x z) y) (C (C x y) y).
    Proof.
      intros.
      ded; ded.
      mp (C (C y W) W).
      aa.
      ded.
      mp (C x z).
      ded.
      mp y.
      ax; bh; nh.
      mp (C x z).
      ax; bh; bh; bh; nh.
      ax; nh.
      ded.
      mp (C (C z W) W).
      aa.
      mp W.
      ka.
      mp y.
      ax; bh; nh.
      mp x.
      ax; bh; bh; nh.
      ax; nh.
    Defined.      
      
    Definition cpiwhp_peirce: forall (T:P -> Type) (x y:P),
        T |- C (C (C x y) x) x.
    Proof.
      intros.
      ded.
      mp (C (C x W) W). aa.
      ded.
      mp (C x y).
      ded.
      mp x.
      ax; bh; nh.
      mp (C x y).
      ax; bh; bh; nh.
      ax; nh.
      ded.
      mp W.
      ded.
      mp (C (C y W) W).
      aa.
      mp W.
      ka.
      ax; nh.
      mp x.
      ax; bh; nh.
      ax; nh.
      Defined. 

    Notation iw_neg:= (fun x:P => C x W).
    Notation iw_or:= (fun x y:P => C (C x W) y).
    Notation iw_and:= (fun x y:P => C (C x (C y W)) W).
    Notation iw_equiv:= (fun x y:P => iw_and (C x y) (C y x)).

    Definition cpiwhp_and_intro: forall (T: P -> Type) (x y:P),
        T |- x -> T |- y -> T |- iw_and x y.
    Proof.
      intros.
      ded.
      mp y.
      mp x.
      ax; nh.
      hw; assumption.
      hw; assumption.
    Defined.      

    Definition cpiwhp_and_intro_formula:
      forall (T:P -> Type) (x y:P),
        T|- C x (C y (iw_and x y)).
    Proof.
      intros.
      ded; ded; apply cpiwhp_and_intro.
      ax; bh; nh.
      ax; nh.
    Defined.
    
    Definition cpiwhp_and_left_elim: forall (T:P -> Type) (x y:P),
        T |- iw_and x y -> T |- x.
    Proof.
      intros.
      mp (C (C x W) W). aa.
      ded.
      mp (C x (C y W)).
      hw; assumption.
      ded; ded. mp x.
      ax; bh; bh; nh.
      ax; bh; nh.
    Defined.

    Definition cpiwhp_and_left_elim_formula: forall (T:P -> Type) (x y:P),
        T |- C (iw_and x y) x.
    Proof.
      intros.
      ded; apply cpiwhp_and_left_elim with (y:=y).
      ax; nh.
    Defined.

    Definition cpiwhp_and_right_elim: forall (T:P -> Type) (x y:P),
        T |- iw_and x y -> T |- y.
    Proof.
      intros.
      mp (C (C y W) W). aa.
      ded.
      mp (C x (C y W)).
      hw; assumption.
      ded; ded. mp y.
      ax; bh; bh; nh.
      ax; nh.
    Defined.

    Definition cpiwhp_and_right_elim_formula: forall (T:P -> Type) (x y:P),
        T |- C (iw_and x y) y.
    Proof.
      intros.
      intros.
      ded; apply cpiwhp_and_right_elim with (x:=x).
      ax; nh.
    Defined.

    Definition cpiwhp_or_left_intro: forall (T: P -> Type) (x y:P),
        T |- x -> T |- iw_or x y.
    Proof.
      intros.
      ded.
      apply cpiwhp_explosion.
      mp x.
      ax; nh. hw; assumption.
    Defined.

    Definition cpiwhp_or_left_intro_formula: forall (T: P -> Type) (x y:P),
        T |- C x (iw_or x y).
    Proof.
      intros.
      ded.
      apply cpiwhp_or_left_intro.
      ax; nh.
    Defined.

    Definition cpiwhp_or_right_intro: forall (T: P -> Type) (x y:P),
        T |- y -> T |- iw_or x y.
    Proof.
      intros.
      mp y. ka. assumption.
    Defined.

    Definition cpiwhp_or_right_intro_formula: forall (T: P -> Type) (x y:P),
        T |- C y (iw_or x y).
    Proof.
      intros. ka.
    Defined.

    Definition cpiwhp_or_elim: forall (T: P -> Type) (x y z:P),
        (T |- C x z) ->
        (T |- C y z) ->
        (T |- iw_or x y) ->
        T |- z.
    Proof.
      intros.
      apply cpiw_cases with (X:= CPIWHP T) (x:=x).
      simpl; assumption.
      simpl.
      apply cpiw_syllogism with (X:= CPIWHP T) (y:=y).
      simpl; assumption.
      simpl; assumption.
    Defined.

    Definition cpiwhp_or_elim_formula: forall (T: P -> Type) (x y z:P),
        T |- C (C x z) (C (C y z) (C (iw_or x y) z)). 
    Proof.
      intros.
      ded; ded; ded.
      apply cpiwhp_or_elim with (x:=x) (y:=y).
      ax; bh; bh; nh.
      ax; bh; nh.
      ax; nh.
    Defined.

    Definition cpiwhp_equiv_intro: forall (T: P -> Type) (x y:P),
        (T |- C x y) ->
        (T |- C y x) ->
        T |- iw_equiv x y.
    Proof.
      intros T x y.
      apply cpiwhp_and_intro.
    Defined.

    Definition cpiwhp_equiv_intro_formula: forall (T: P -> Type) (x y:P),
        T |- C (C x y) (C (C y x) (iw_equiv x y)).
    Proof.
      intros T x y.
      apply cpiwhp_and_intro_formula.
    Defined.

    Definition cpiwhp_equiv_left_elim: forall (T: P -> Type) (x y:P),
        T |- iw_equiv x y -> T |- C x y.
    Proof.
      intros T x y.
      apply cpiwhp_and_left_elim.
    Defined.
    
    Definition cpiwhp_equiv_left_elim_formula: forall (T: P -> Type) (x y:P),
        T |- C (iw_equiv x y) (C x y).
    Proof.
      intros T x y.
      apply cpiwhp_and_left_elim_formula.
    Defined.

    Definition cpiwhp_equiv_right_elim: forall (T: P -> Type) (x y:P),
        T |- iw_equiv x y -> T |- C y x.
    Proof.
      intros T x y.
      apply cpiwhp_and_right_elim.
    Defined.
    
    Definition cpiwhp_equiv_right_elim_formula: forall (T: P -> Type) (x y:P),
        T |- C (iw_equiv x y) (C y x).
    Proof.
      intros T x y.
      apply cpiwhp_and_right_elim_formula.
    Defined.
    
    Definition cpiwhp_equiv_reflexivity: forall (T: P -> Type) (x:P),
        T |- iw_equiv x x.
    Proof.
      intros.
      ded.
      mp (C x x).
      mp (C x x).
      ax; nh.
      apply cpiw_i with (X:= CPIWHP (add_hyp T (C (C x x) (C (C x x) W)))).
      apply cpiw_i with (X:= CPIWHP (add_hyp T (C (C x x) (C (C x x) W)))).
    Defined.

    Definition cpiwhp_and_symmetry_formula: forall (T: P -> Type) (x y:P),
        T |- C (iw_and x y) (iw_and y x).
    Proof.
      intros.
      apply
        (hs_sk_polarity_left
           P C (CPIW_Hilbert_Proof T)
           (cpiwhp_k_axiom T) (cpiwhp_s_axiom T) (cpiwhp_modus_ponens T)) with (z:= W).
      apply
        (hs_sk_c
           P C (CPIW_Hilbert_Proof T)
           (cpiwhp_k_axiom T) (cpiwhp_s_axiom T) (cpiwhp_modus_ponens T)) with (z:= W).
    Defined.
      
    Definition cpiwhp_equiv_symmetry_formula: forall (T: P -> Type) (x y:P),
        T |- C (iw_equiv x y) (iw_equiv y x).
    Proof.
      intros.
      apply cpiwhp_and_symmetry_formula.
    Defined.
    
    Definition cpiwhp_equiv_transitivity: forall (T:P -> Type) (x y z:P),
        (T |- iw_equiv x y) ->
        (T |- iw_equiv y z) ->
        (T |- iw_equiv x z).
    Proof.
      intros.
      apply cpiwhp_and_intro.
      apply cpiw_syllogism with (X:= CPIWHP T) (y:=y).
      simpl; apply cpiwhp_and_left_elim with (y:= C y x); assumption.
      simpl; apply cpiwhp_and_left_elim with (y:= C z y); assumption.
      apply cpiw_syllogism with (X:= CPIWHP T) (y:=y).
      simpl; apply cpiwhp_and_right_elim with (x:= C y z); assumption.
      simpl; apply cpiwhp_and_right_elim with (x:= C x y); assumption.
    Defined.

    Definition cpiwhp_equiv_transitivity_formula: forall (T:P -> Type) (x y z:P),
        T |- C (iw_equiv x y) (C (iw_equiv y z) (iw_equiv x z)).
    Proof.
      intros.
      ded; ded; apply cpiwhp_equiv_transitivity with (y:=y).
      ax; bh; nh.
      ax; nh.
    Defined.

    Definition cpiwhp_equiv_implies: forall (T:P -> Type) (x x' y y':P),
        (T |- iw_equiv x x') ->
        (T |- iw_equiv y y') ->
        T |- iw_equiv (C x y) (C x' y').
    Proof.
      intros.
      apply cpiwhp_and_intro.
      ded.
      apply cpiw_syllogism with (X:= CPIWHP (add_hyp T (C x y))) (y:=y).
      simpl; apply cpiw_syllogism with (X:= CPIWHP (add_hyp T (C x y))) (y:=x).
      simpl; hw; apply cpiwhp_and_right_elim with (x:= C x x'); assumption.
      simpl; ax; nh.
      simpl; hw; apply cpiwhp_and_left_elim with (y:= C y' y); assumption.
      ded.
      apply cpiw_syllogism with (X:= CPIWHP (add_hyp T (C x' y'))) (y:=y').
      simpl; apply cpiw_syllogism with (X:= CPIWHP (add_hyp T (C x' y'))) (y:=x').
      simpl; hw; apply cpiwhp_and_left_elim with (y:= C x' x); assumption.
      simpl; ax; nh.
      simpl; hw; apply cpiwhp_and_right_elim with (x:= C y y'); assumption.
    Defined.

    Definition cpiwhp_equiv_implies_formula: forall (T:P -> Type) (x x' y y':P),
        T |- C (iw_equiv x x') (C (iw_equiv y y') (iw_equiv (C x y) (C x' y'))).
    Proof.
      intros.
      ded; ded.
      apply cpiwhp_equiv_implies.
      ax; bh; nh.
      ax; nh.
    Defined.
    
  End Hilbert_systems_theorems.
  
End the_deduction_procedure.

Section Catalogue_of_applications_of_Hilbert_systems_to_CIWP_systems.

  Variable X:classical_propositional_implies_wrong_system.

  Notation P:= (CPIW_Sentence X).
  Notation C:= (cpiw_implies X).
  Notation W:= (cpiw_wrong X).
  Notation MP := (cpiw_modus_ponens X).
  Notation KA:= (cpiw_k X).
  Notation SA:= (cpiw_s X).
  Notation AA:= (cpiw_absurd X).                  

  Notation "|- f":= (cpiw_theorem X f) (at level 61).

  Notation HP := (CPIW_Hilbert_Proof P C W).
  
  Fixpoint cpiw_proof_transfert
           (T:P -> Type) (SUBTH: forall x:P, T x -> |- x)
           (f:P) (pr: HP T f) {struct pr}: |- f:=
    match pr in (CPIW_Hilbert_Proof _ _ _ _ y) return (|- y) with
    | cpiwhp_ax _ _ _ _ x t => SUBTH x t
    | cpiwhp_k_axiom _ _ _ _ a b => KA a b
    | cpiwhp_s_axiom _ _ _ _ a b c => SA a b c
    | cpiwhp_absurd_axiom _ _ _ _ a => AA a
    | cpiwhp_modus_ponens _ _ _ _ a b pr1 pr2 =>
      MP a b (cpiw_proof_transfert T SUBTH (C a b) pr1) (cpiw_proof_transfert T SUBTH a pr2)
    end.
    
  Definition cpiwhp_to_cpiw (x:P):
    HP (cpiw_theorem X) x -> |- x:=
    cpiw_proof_transfert (cpiw_theorem X) (fun (x0 : P) (X0 : |- x0) => X0) x.

    Ltac ca := apply cpiwhp_ax; assumption.

    Definition cpiw_explosion: forall (x:P),
        |- W -> |- x.
    Proof.
      intros.
      apply cpiwhp_to_cpiw; apply cpiwhp_explosion.
      ca.
    Defined.

    Definition cpiw_explosion_formula: forall  (x:P),
        |- C W x.
    Proof.
      intros.
      apply cpiwhp_to_cpiw; apply cpiwhp_explosion_formula.
    Defined.
    
    Definition cpiw_cases_formula: forall (x y:P),
        |- C (C (C x W) y) (C (C x y) y).
    Proof.
      intros.
      apply cpiwhp_to_cpiw; apply cpiwhp_cases_formula.
    Defined.

    Definition cpiw_implicative_cases_formula: forall (x y z:P),
        |- C (C (C x z) y) (C (C x y) y).
    Proof.
      intros.
      apply cpiwhp_to_cpiw; apply cpiwhp_implicative_cases_formula.
    Defined.

    Definition cpiw_peirce: forall (x y:P),
        |- C (C (C x y) x) x.
    Proof.
      intros.
      apply cpiwhp_to_cpiw; apply cpiwhp_peirce.
    Defined. 

    Notation iw_neg:= (fun x:P => C x W).
    Notation iw_or:= (fun x y:P => C (C x W) y).
    Notation iw_and:= (fun x y:P => C (C x (C y W)) W).
    Notation iw_equiv:= (fun x y:P => iw_and (C x y) (C y x)).

    Definition cpiw_and_intro: forall (x y:P),
        |- x -> |- y -> |- iw_and x y.
    Proof.
      intros.
      apply cpiwhp_to_cpiw; apply cpiwhp_and_intro.
      ca. ca.
    Defined.      

    Definition cpiw_and_intro_formula:
      forall (x y:P),
        |- C x (C y (iw_and x y)).
    Proof.
      intros.
      apply cpiwhp_to_cpiw; apply cpiwhp_and_intro_formula.
    Defined.
    
    Definition cpiw_and_left_elim: forall  (x y:P),
        |- iw_and x y -> |- x.
    Proof.
      intros.
      apply cpiwhp_to_cpiw; apply cpiwhp_and_left_elim with (y:=y).
      ca.
    Defined.

    Definition cpiw_and_left_elim_formula: forall  (x y:P),
        |- C (iw_and x y) x.
    Proof.
      intros.
      apply cpiwhp_to_cpiw; apply cpiwhp_and_left_elim_formula.
    Defined.

    Definition cpiw_and_right_elim: forall  (x y:P),
        |- iw_and x y -> |- y.
    Proof.
      intros.
      apply cpiwhp_to_cpiw; apply cpiwhp_and_right_elim with (x:=x).
      ca.
    Defined.

    Definition cpiw_and_right_elim_formula: forall  (x y:P),
        |- C (iw_and x y) y.
    Proof.
      intros.
      apply cpiwhp_to_cpiw; apply cpiwhp_and_right_elim_formula.
    Defined.

    Definition cpiw_or_left_intro: forall (x y:P),
        |- x -> |- iw_or x y.
    Proof.
      intros.
      apply cpiwhp_to_cpiw; apply cpiwhp_or_left_intro.
      ca.
    Defined.

    Definition cpiw_or_left_intro_formula: forall (x y:P),
        |- C x (iw_or x y).
    Proof.
      intros.
      apply cpiwhp_to_cpiw; apply cpiwhp_or_left_intro_formula.
    Defined.

    Definition cpiw_or_right_intro: forall (x y:P),
        |- y -> |- iw_or x y.
    Proof.
      intros.
      apply cpiwhp_to_cpiw; apply cpiwhp_or_right_intro.
      ca.
    Defined.

    Definition cpiw_or_right_intro_formula: forall (x y:P),
        |- C y (iw_or x y).
    Proof.
      intros. apply KA.
    Defined.

    Definition cpiw_or_elim: forall (x y z:P),
        (|- C x z) ->
        (|- C y z) ->
        (|- iw_or x y) ->
        |- z.
    Proof.
      intros.
      apply cpiwhp_to_cpiw; apply cpiwhp_or_elim with (x:=x) (y:=y).
      ca. ca. ca.
    Defined.    

    Definition cpiw_or_elim_formula: forall (x y z:P),
        |- C (C x z) (C (C y z) (C (iw_or x y) z)). 
    Proof.
      intros.
      apply cpiwhp_to_cpiw; apply cpiwhp_or_elim_formula.
    Defined.

    Definition cpiw_equiv_intro: forall (x y:P),
        (|- C x y) ->
        (|- C y x) ->
        |- iw_equiv x y.
    Proof.
      intros.
      apply cpiwhp_to_cpiw; apply cpiwhp_equiv_intro.
      ca. ca.
    Defined.

    Definition cpiw_equiv_intro_formula: forall (x y:P),
        |- C (C x y) (C (C y x) (iw_equiv x y)).
    Proof.
      intros.
      apply cpiwhp_to_cpiw; apply cpiwhp_equiv_intro_formula.
    Defined.

    Definition cpiw_equiv_left_elim: forall (x y:P),
        |- iw_equiv x y -> |- C x y.
    Proof.
      intros.
      apply cpiwhp_to_cpiw; apply cpiwhp_equiv_left_elim.
      ca.
    Defined.
    
    Definition cpiw_equiv_left_elim_formula: forall (x y:P),
        |- C (iw_equiv x y) (C x y).
    Proof.
      intros.
      apply cpiwhp_to_cpiw; apply cpiwhp_equiv_left_elim_formula.
    Defined.

    Definition cpiw_equiv_right_elim: forall (x y:P),
        |- iw_equiv x y -> |- C y x.
    Proof.
      intros.
      apply cpiwhp_to_cpiw; apply cpiwhp_equiv_right_elim.
      ca.
    Defined.
    
    Definition cpiw_equiv_right_elim_formula: forall (x y:P),
        |- C (iw_equiv x y) (C y x).
    Proof.
      intros.
      apply cpiwhp_to_cpiw; apply cpiwhp_equiv_right_elim_formula.
    Defined.
    
    Definition cpiw_equiv_reflexivity: forall (x:P),
        |- iw_equiv x x.
    Proof.
      intros.
      apply cpiwhp_to_cpiw; apply cpiwhp_equiv_reflexivity.
    Defined.

    Definition cpiw_and_symmetry_formula: forall (x y:P),
        |- C (iw_and x y) (iw_and y x).
    Proof.
      intros.
      apply cpiwhp_to_cpiw; apply cpiwhp_and_symmetry_formula.
    Defined.
      
    Definition cpiw_equiv_symmetry_formula: forall (x y:P),
        |- C (iw_equiv x y) (iw_equiv y x).
    Proof.
      intros.
      apply cpiwhp_to_cpiw; apply cpiwhp_equiv_symmetry_formula.
    Defined.

    Definition cpiw_equiv_symmetry: forall (x y:P),
        |- (iw_equiv x y) -> |- (iw_equiv y x).
    Proof.
      intros.
      apply cpiw_modus_ponens with (a:=iw_equiv x y).
      apply cpiw_equiv_symmetry_formula.
      assumption.
    Defined.
    
    Definition cpiw_equiv_transitivity: forall (x y z:P),
        (|- iw_equiv x y) ->
        (|- iw_equiv y z) ->
        (|- iw_equiv x z).
    Proof.
      intros.
      apply cpiwhp_to_cpiw; apply cpiwhp_equiv_transitivity with (y:=y).
      ca. ca.
    Defined.

    Definition cpiw_equiv_transitivity_formula: forall (x y z:P),
        |- C (iw_equiv x y) (C (iw_equiv y z) (iw_equiv x z)).
    Proof.
      intros.
      apply cpiwhp_to_cpiw; apply cpiwhp_equiv_transitivity_formula.
    Defined.

    Definition cpiw_equiv_implies: forall (x x' y y':P),
        (|- iw_equiv x x') ->
        (|- iw_equiv y y') ->
        |- iw_equiv (C x y) (C x' y').
    Proof.
      intros.
      apply cpiwhp_to_cpiw; apply cpiwhp_equiv_implies.
      ca. ca.
    Defined.

    Definition cpiw_equiv_implies_formula: forall (x x' y y':P),
        |- C (iw_equiv x x') (C (iw_equiv y y') (iw_equiv (C x y) (C x' y'))).
    Proof.
      intros.
      apply cpiwhp_to_cpiw; apply cpiwhp_equiv_implies_formula.
    Defined.
  
End Catalogue_of_applications_of_Hilbert_systems_to_CIWP_systems.

Section When_there_is_no_wrong_sentence.

  Variable P:Type.
  Variable C:P -> P -> P.
  Variable T: P -> Type.
  Variable KA: forall x y:P, T (C x (C y x)).
  Variable SA: forall x y z:P, T (C (C x (C y z)) (C (C x y) (C x z))).
  Variable PA: forall x y:P, T (C (C (C x y) x) x).
  Variable MP: forall x y:P, T (C x y) -> T x -> T y.

  Notation "|- f" := (T f) (at level 61).
  Notation kf := (fun x y:P => C x (C y x)).
  Notation sf := (fun x y z:P => C (C x (C y z)) (C (C x y) (C x z))).
  Notation pf := (fun x y:P => C (C (C x y) x) x).
  Notation iF := (fun x:P => C x x).
  Notation bf := (fun x y z:P => C (C y z) (C (C x y) (C x z))).
    
  Ltac ka := apply KA.
  Ltac sa := apply SA.
  Ltac pa := apply PA.
  Ltac mp z := apply MP with (x:=z).

  Notation hs_sk_hypothetical_modus_ponens:=
       (fun (x y z : P) (prcxcyz : |- C x (C y z)) (prcxy : |- C x y) =>
          MP (C x y) (C x z) (MP (C x (C y z)) (C (C x y) (C x z)) (SA x y z) prcxcyz) prcxy).

  Ltac hmp t:= apply hs_sk_hypothetical_modus_ponens with (y:=t).
  
  Notation hs_sk_weakening:=
    (fun (x y : P) (prx : |- x) => MP x (C y x) (KA x y) prx).
  
  Ltac we := apply hs_sk_weakening. 
  
  Ltac ia := apply (hs_sk_i P C T KA SA MP).
  Ltac syl t:= apply (hs_sk_syllogism P C T KA SA MP) with (y:=t).
  Ltac ba := apply (hs_sk_b P C T KA SA MP).  
  Ltac sw1 t:= apply (hs_sk_permutation P C T KA SA MP) with (y:=t).  
  Ltac pl := apply (hs_sk_polarity_left P C T KA SA MP).  
  Ltac pr := apply (hs_sk_polarity_right P C T KA SA MP).
  Ltac wa := apply (hs_sk_w P C T KA SA MP).
  Ltac sw2 := apply (hs_sk_permutation2 P C T KA SA MP).
  Ltac qa := apply (hs_sk_q P C T KA SA MP).
    
  Definition skp_or_permutation (x y:P) (pr:|- C (C x y) y): |- C (C y x) x.
  Proof.
    hmp (C (C x y) x). we. pa. pl. assumption.
  Defined.

  Ltac op := apply skp_or_permutation.
  
  Definition skp_or_modus_ponens: forall (f x y:P),
      |- C (C f (C x y)) (C x y) -> |- C (C f x) x -> |- C (C f y) y. 
  Proof.
    intros.
    op.
    hmp (C (C x y) f).
    we. op. assumption.
    hmp (C (C x y) (C x f)).
    hmp (C (C x f) f).
    we. ba. we. op. assumption. ba.
  Defined.

  Ltac omp t:= apply skp_or_modus_ponens with (x:= t).
  
  Definition skp_or_absurd (f x:P): |- (C (C f (C (C (C x f) f) x))) (C (C (C x f) f) x).
  Proof.
    intros.
    omp (pf x f).
    omp (C f x).
    we. syl (C (C (C x f) f) (C (C x f) x)). ba. qa. wa.
    we. pa.
  Defined.

  Definition skp_or_k (f x y: P): |- C (C f (kf x y)) (kf x y).
  Proof.
    we; ka.
  Defined.
  
  Definition skp_or_s (f x y z:P): |- C (C f (sf x y z)) (sf x y z).
  Proof.
    we; sa.
  Defined.

  Section skp_as_cpiw.

    Variable f:P.
    
    Definition CPIW_SKP:=
      make_cpiw P C f (fun x:P => |- C (C f x) x)
                (skp_or_k f) (skp_or_s f) (skp_or_absurd f) (skp_or_modus_ponens f).

  End skp_as_cpiw.  
  
End When_there_is_no_wrong_sentence.

Section extra_theorems.

  Variable X:classical_propositional_implies_wrong_system.

  Notation P:= (CPIW_Sentence X).
  Notation C:= (cpiw_implies X).
  Notation W:= (cpiw_wrong X).
  Notation MP := (cpiw_modus_ponens X).
  Notation KA:= (cpiw_k X).
  Notation SA:= (cpiw_s X).
  Notation AA:= (cpiw_absurd X).                  

  Notation "|- f":= (cpiw_theorem X f) (at level 61).

  Notation HP := (CPIW_Hilbert_Proof P C W).

  Ltac mp z:= apply (cpiw_modus_ponens X) with (a:=z).
  Ltac syl b := apply (hs_sk_syllogism P C (cpiw_theorem X) KA SA MP) with (y:=b).  
  Ltac per b := apply (hs_sk_permutation P C (cpiw_theorem X) KA SA MP) with (y:=b).  
  Ltac per2 := apply (hs_sk_permutation2 P C (cpiw_theorem X) KA SA MP).  
  Ltac lap t := apply t with (X:=X).
  
  Definition cpiw_neg_elimination_formulas (x y:P):
    prod (|- C (C x W) (C x y)) (|- C x (C (C x W) y)):=
    let L := MP (C W y) (C (C x W) (C x y)) (cpiw_b X x W y) (cpiw_explosion_formula X y) in
    (L, hs_sk_permutation2 P C (fun c : P => |- c) KA SA MP (C x W) x y L).

  Notation iw_neg:= (fun x:P => C x W).
  Notation iw_or:= (fun x y:P => C (C x W) y).
  Notation iw_and:= (fun x y:P => C (C x (C y W)) W).
  Notation iw_equiv:= (fun x y:P => iw_and (C x y) (C y x)).

  Definition cpiw_positive_case_in_case_definition (x y z:P) (pr: |- x):
  |- iw_equiv (iw_and (C x y) (C (iw_neg x) z)) y.
  Proof.    
    mp (C y (iw_and (C x y) (C (iw_neg x) z))).
    mp (C (iw_and (C x y) (C (iw_neg x) z)) y).
    lap cpiw_and_intro_formula.
    syl (C x y).
    lap cpiw_and_left_elim_formula.
    per x.
    lap cpiw_i. assumption.
    syl (C x y). apply KA.
    per2.
    per (C (C x W) z). lap cpiw_c. mp x. apply cpiw_neg_elimination_formulas.
    assumption.
  Defined.
  
  Definition cpiw_negative_case_in_case_definition (x y z:P) (pr: |- iw_neg x):
  |- iw_equiv (iw_and (C x y) (C (iw_neg x) z)) z.
  Proof.    
    mp (C z (iw_and (C x y) (C (iw_neg x) z))).
    mp (C (iw_and (C x y) (C (iw_neg x) z)) z).
    lap cpiw_and_intro_formula.
    syl (C (iw_neg x) z).
    lap cpiw_and_right_elim_formula.
    per (iw_neg x).
    lap cpiw_i. assumption.
    syl (C (C x W) z). apply KA.
    per2. mp (C x y).
    lap cpiw_t. 
    apply (hs_sk_syllogism P C (cpiw_theorem X) KA SA MP) with (y:=W).
    assumption.
    lap cpiw_explosion_formula.
  Defined.   

End extra_theorems.
