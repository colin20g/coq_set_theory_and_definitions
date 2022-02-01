Require Import SetDef.add_items_to_theories_and_other_tools.
Require Import SetDef.propositional_implies_wrong_logic.
Require Import SetDef.first_order_set_language.
Require Import SetDef.set_language_with_definition_operator.
Require Import SetDef.first_axiom_system_for_definition_operator.

(** In this file we define the second axiom system for d_prop.
Natural deduction rules for every connector are proven.
*)

Section main.

  Notation DP := D_Prop.
  Notation DT := D_Term.

  Inductive second_d_logical_axiom : forall C : Type, C -> DP C -> Type :=
  | sd_if_exun: forall (C : Type) (k : C) (p: DP (option C)),
      second_d_logical_axiom
        C k (d_implies C (d_exists_unique C p) (d_prop_specify C (d_def C p) p))
  | sd_if_not_exun: forall (C : Type) (k : C) (p: DP (option C)),
      second_d_logical_axiom
        C k (d_implies C (d_neg C (d_exists_unique C p))
                       (d_equal C (d_def C p) (d_letter C k)))
  | sd_k_ax : forall (C : Type) (k : C) (a b : DP C),
      second_d_logical_axiom C k (d_implies C a (d_implies C b a))                             
  | sd_s_ax : forall (C : Type) (k : C) (a b c : DP C),
      second_d_logical_axiom
        C k (d_implies C (d_implies C a (d_implies C b c))
                       (d_implies C (d_implies C a b) (d_implies C a c)))
  | sd_abs_ax : forall (C : Type) (k : C) (a : DP C),
      second_d_logical_axiom
        C k (d_implies C (d_implies C (d_implies C a (d_wrong C)) (d_wrong C)) a)             
  | sd_special_case_ax : forall (C : Type) (k : C) (f : DP (option C)) (t : DT C),
      second_d_logical_axiom C k (d_implies C (d_forall C f)
                                            (d_prop_specify C t f))
  | sd_forall_const_ax : forall (C : Type) (k : C) (f : DP C),
      second_d_logical_axiom C k (d_implies C f (d_forall C (d_prop_constant_embedding C f)))
  | sd_forall_mp_ax : forall (C : Type) (k : C) (f g : DP (option C)),
      second_d_logical_axiom
        C k (d_implies C (d_forall C (d_implies (option C) f g))
                       (d_implies C (d_forall C f) (d_forall C g)))
  | sd_universal_closure : forall (C : Type) (k : C) (f : DP (option C)),
      second_d_logical_axiom (option C) (Some k) f ->
      second_d_logical_axiom C k (d_forall C f).

  Section definition_of_proofs.
    
    Variable C:Type.
    Variable k:C.
    Variable T: DP C -> Type.

    Inductive second_d_proof: DP C -> Type :=
      sd_theory_axiom : forall p : DP C, T p -> second_d_proof p
    | sd_logical_axiom :
        forall p : DP C, second_d_logical_axiom C k p -> second_d_proof p
    | sd_implies_elim : forall a b : DP C,
        second_d_proof (d_implies C a b) ->
        second_d_proof a -> second_d_proof b.

    Definition SDCPIW: classical_propositional_implies_wrong_system.
    Proof.
      apply (make_cpiw (DP C) (d_implies C) (d_wrong C) second_d_proof).
      intros; apply sd_logical_axiom; apply sd_k_ax.
      intros; apply sd_logical_axiom; apply sd_s_ax.
      intros; apply sd_logical_axiom; apply sd_abs_ax.
      apply sd_implies_elim.
    Defined.
    
  End definition_of_proofs.

    Definition sd_letter_special_case:
      forall (C:Type) (k x:C) (T:DP C -> Type) (f: DP (option C)),
        second_d_proof C k T (d_implies C (d_forall C f) (d_prop_letter_specify C x f)).
    Proof.
      intros.
      rewrite d_prop_letter_specify_identity.
      apply sd_logical_axiom.
      apply sd_special_case_ax.
    Defined.

  Fixpoint sd_weakening
           (C:Type) (k:C) (T:DP C -> Type)
           (f : DP C) (pr : second_d_proof C k T f) (U : DP C -> Type)
           (SUBTH : forall x : DP C, T x -> U x) {struct pr} : second_d_proof C k U f :=
    match pr with
    | sd_theory_axiom _ _ _ p t => sd_theory_axiom C k U p (SUBTH p t)
    | sd_logical_axiom _ _ _ p f0 => sd_logical_axiom C k U p f0
    | sd_implies_elim _ _ _ a b pr1 pr2 =>
      sd_implies_elim C k U a b (sd_weakening C k T (d_implies C a b) pr1 U SUBTH)
                       (sd_weakening C k T a pr2 U SUBTH)
    end.

  Definition sd_weakening_hypothesis (C:Type) (k:C) (T:DP C -> Type) (h x:DP C)
             (pr:second_d_proof C k T x):
    second_d_proof C k (add_item (DP C) T h) x:=
    sd_weakening C k T x pr (add_item (DP C) T h)
                  (base_item (DP C) T h).

  Notation add_hyp_d:= (fun C:Type => add_item (DP C)).
  Ltac nh:= apply new_item.
  Ltac bh:= apply base_item.
  Ltac papp D l U z := apply z with (X:= SDCPIW D l U). 
  Ltac mp y := apply sd_implies_elim with (a:=y).
  
  Section the_deduction_theorem_for_sd.

    Variable C:Type.
    Variable k:C.
    Variable T: DP C -> Type.
    Variable h: DP C.

    Fixpoint sd_implies_intro (x:DP C) (pr: second_d_proof C k (add_hyp_d C T h) x)
             {struct pr}:
      second_d_proof C k T (d_implies C h x).
    Proof.
      destruct pr.
      destruct a.
      papp C k T cpiw_i.   
      mp x. apply sd_logical_axiom.
      apply sd_k_ax. apply sd_theory_axiom; assumption.
      mp p. apply sd_logical_axiom.
      apply sd_k_ax. apply sd_logical_axiom; assumption.
      mp (d_implies C h a). mp (d_implies C h (d_implies C a b)).
      apply sd_logical_axiom; apply sd_s_ax.
      apply sd_implies_intro; assumption.
      apply sd_implies_intro; assumption.
    Defined.      
    
  End the_deduction_theorem_for_sd.

  Ltac ded := apply sd_implies_intro.
  
  Section the_generalization_rule_for_sd.

    Variable C:Type.
    Variable k:C.
    Variable T: DP C -> Type.

    Fixpoint sd_forall_intro
             (f: DP (option C))
             (pr: second_d_proof (option C) (Some k) (d_theory_constant_embedding C T) f)
             {struct pr}:
      second_d_proof C k T (d_forall C f).
    Proof.
      destruct pr.
      destruct d.
      mp p. apply sd_logical_axiom; apply sd_forall_const_ax. apply sd_theory_axiom.
      assumption.
      apply sd_logical_axiom; apply sd_universal_closure; assumption.
      mp (d_forall C a).
      mp (d_forall C (d_implies (option C) a b)).
      apply sd_logical_axiom; apply sd_forall_mp_ax.
      apply sd_forall_intro; assumption.
      apply sd_forall_intro; assumption.
    Defined.      
    
  End the_generalization_rule_for_sd.
    
  Section substitution_in_proofs.

    Fixpoint second_d_logical_axiom_substitution
             (C:Type) (k_c:C)
             (p: DP C) (l: second_d_logical_axiom C k_c p)
             (D:Type) (k_d:D) (env: C -> DT D)
             (eqk: env k_c = d_letter D k_d)
             {struct l}:
      second_d_logical_axiom D k_d (d_prop_substitution C p D env).
    Proof.
      destruct l.
      rewrite d_implies_subst_eq.
      rewrite d_exists_unique_subst_eq. 
      assert (
          d_prop_substitution C (d_prop_specify C (d_def C p) p) D env
          =
          d_prop_specify
            D
            (d_def
               D
               (d_prop_substitution
                  (option C) p (option D)
                  (option_rect (fun _ : option C => DT (option D))
                               (fun a : C => d_term_constant_embedding D (env a)) 
                               (d_letter (option D) None)))
            )
            (d_prop_substitution
               (option C) p (option D)
               (option_rect (fun _ : option C => DT (option D))
                            (fun a : C => d_term_constant_embedding D (env a)) 
                            (d_letter (option D) None)))
        ) as E1.
      unfold d_prop_specify.
      repeat rewrite d_prop_double_substitution.
      apply d_prop_subst_pointwise_equality.
      intros.
      destruct x.
      simpl. unfold d_term_constant_embedding.
      simpl.
      rewrite d_term_coc_subst_commutation with
          (D:=D) (env_var_ddo := fun v:D => v) (env_term_cd := d_letter D).
      rewrite d_term_coc_identity_equality.
      rewrite d_term_subst_identity_equality; reflexivity.
      simpl; reflexivity.      
      intros.
      simpl; reflexivity.
      rewrite E1.
      apply sd_if_exun.
      rewrite d_implies_subst_eq.
      rewrite d_neg_subst_eq.
      rewrite d_exists_unique_subst_eq.
      rewrite d_equal_subst_eq.
      simpl.
      rewrite eqk.
      apply sd_if_not_exun.
      simpl; apply sd_k_ax.
      simpl; apply sd_s_ax.
      simpl; apply sd_abs_ax.
      simpl.
      assert (
          d_prop_substitution C (d_prop_specify C t f) D env
          =
          d_prop_specify
            D
            (d_term_substitution C t D env)
            (d_prop_substitution
               (option C) f (option D)
               (option_rect (fun _ : option C => DT (option D))
                            (fun a : C => d_term_constant_embedding D (env a)) 
                            (d_letter (option D) None))) 
        ) as E2.
      unfold d_prop_specify.
      rewrite d_prop_double_substitution with
          (D:=C) (C:=option C).
      rewrite d_prop_double_substitution.
      apply d_prop_subst_pointwise_equality.
      intros; destruct x. simpl.
      simpl. unfold d_term_constant_embedding.
      simpl.
      rewrite d_term_coc_subst_commutation with
          (D:=D) (env_var_ddo := fun v:D => v) (env_term_cd := d_letter D).
      rewrite d_term_coc_identity_equality.
      rewrite d_term_subst_identity_equality; reflexivity.
      simpl; reflexivity.
      simpl; reflexivity.
      rewrite E2; apply sd_special_case_ax.
      rewrite d_implies_subst_eq.
      rewrite d_forall_subst_eq.
      assert (
          d_prop_substitution
            (option C) (d_prop_constant_embedding C f) 
            (option D)
            (option_rect (fun _ : option C => DT (option D))
                         (fun a : C => d_term_constant_embedding D (env a)) 
                         (d_letter (option D) None))
          =
          d_prop_constant_embedding D (d_prop_substitution C f D env)
        ) as E3.
      unfold d_prop_constant_embedding.
      apply d_prop_coc_subst_commutation.
      intros; simpl; reflexivity.
      rewrite E3; apply sd_forall_const_ax.
      simpl; apply sd_forall_mp_ax.
      simpl; apply sd_universal_closure.
      apply second_d_logical_axiom_substitution with (k_c := Some k).
      assumption.
      simpl; rewrite eqk. unfold d_term_constant_embedding.
      simpl; reflexivity.
    Defined.

    Fixpoint second_d_proof_substitution
             (C D:Type) (k_c:C) (k_d:D)
             (env: C -> DT D) (eqk: env k_c = d_letter D k_d) (T: DP C -> Type)
             (f: DP C) (pr:second_d_proof C k_c T f) {struct pr}:
               second_d_proof D k_d
                              (d_theory_substitution C T D env)
                              (d_prop_substitution C f D env).
    Proof.
      destruct pr.
      apply sd_theory_axiom; apply dtsubst_intro; assumption.
      apply sd_logical_axiom. apply second_d_logical_axiom_substitution with (k_c := k_c).
      assumption. assumption.
      apply second_d_proof_substitution with (D:=D) (k_d:=k_d) (env:=env) in pr1.
      apply second_d_proof_substitution with (D:=D) (k_d:=k_d) (env:=env) in pr2.
      simpl in pr1. simpl in pr2.
      mp (d_prop_substitution C a D env).
      assumption. assumption. assumption. assumption.
    Defined.                                                    
      
  End substitution_in_proofs.

  Section change_of_context_in_proofs.

    Definition second_d_proof_context_change:
      forall (C : Type) (k : C) (T : DP C -> Type) (D : Type) (env : C -> D) (p : DP C),
        second_d_proof C k T p ->
        second_d_proof D (env k) (d_theory_context_change C T D env)
                       (d_prop_change_of_context C p D env).
    Proof.
      intros.
      rewrite d_prop_coc_subst_equal with (envt := fun l:C => d_letter D (env l)).
      apply sd_weakening with
          (T:= d_theory_substitution C T D (fun l:C => d_letter D (env l))). 
      apply second_d_proof_substitution with (k_c := k). reflexivity.
      assumption.
      intros. destruct X0.
      rewrite <- d_prop_coc_subst_equal with (envc := env). apply dtcc_intro. assumption.
      intros; reflexivity.
      intros; reflexivity.
    Defined. 
      
  End change_of_context_in_proofs.

  Section natural_deduction_inference_rules.

    Section natural_deduction_rules_for_propositional_connectors.

      Variable C:Type.
      Variable k:C.
      Variable T: DP C -> Type.

      Notation "H |- a":= (second_d_proof C k H a) (at level 61).
      Notation wr := (d_wrong C). 
      
      Definition sd_neg_intro: forall a:DP C,
          add_hyp_d C T a |- wr -> T |- d_neg C a.
      Proof.
        intros. ded. assumption.
      Defined.
                                                                  
      Definition sd_neg_elim: forall a: DP C,
          T |- a -> T |- d_neg C a -> T |- wr.
      Proof.
        intros. mp a. assumption. assumption.
      Defined.

      Definition sd_classical_absurdity: forall a:DP C,
          add_hyp_d C T (d_neg C a) |- wr -> T |- a.
      Proof.
        intros. mp (d_implies C (d_implies C a wr) wr).
        apply sd_logical_axiom; apply sd_abs_ax.
        ded. assumption.
      Defined.

      Definition sd_and_intro: forall a b:DP C,
          T |- a -> T |- b -> T |- d_and C a b.
      Proof.
        papp C k T cpiw_and_intro.
      Defined.

      Definition sd_and_left_elim: forall a b:DP C,
          T |- d_and C a b -> T |- a.
      Proof.
        papp C k T cpiw_and_left_elim.
      Defined.

      Definition sd_and_right_elim: forall a b:DP C,
          T |- d_and C a b -> T |- b.
      Proof.
        papp C k T cpiw_and_right_elim.
      Defined.

      Definition sd_or_left_intro: forall a b:DP C,
          T |- a -> T |- d_or C a b.
      Proof.
        papp C k T cpiw_or_left_intro.
      Defined.
        
      Definition sd_or_right_intro: forall a b:DP C,
          T |- b -> T |- d_or C a b.
      Proof.
        papp C k T cpiw_or_right_intro.
      Defined.

      Definition sd_or_elim2:  forall a b f:DP C,
          (T |- d_implies C a f) ->
          (T |- d_implies C b f) ->
          (T |- d_or C a b) ->
          T |- f.
      Proof.
        papp C k T cpiw_or_elim.
      Defined.

      Definition sd_or_elim:  forall a b f:DP C,
          (add_hyp_d C T a |- f) ->
          (add_hyp_d C T b |- f) ->
          (T |- d_or C a b) ->
          T |- f.
      Proof.
        intros.
        apply sd_or_elim2 with (a:=a) (b:=b).
        ded; assumption.
        ded; assumption.
        assumption.
      Defined.
        
    End natural_deduction_rules_for_propositional_connectors. 

    Section natural_deduction_rules_for_quantifiers.  
      
      Definition sd_forall_inverse_intro:
        forall (C:Type) (k:C) (T:DP C-> Type) (f:DP (option C)),
          second_d_proof C k T (d_forall C f) ->
          second_d_proof (option C) (Some k) (d_theory_constant_embedding C T) f.
      Proof.
        intros.
        assert (d_prop_letter_specify
                  (option C)
                  None
                  (d_prop_change_of_context
                     (option C) f (option (option C))
                     (option_rect
                        (fun _:option C => option (option C))
                        (fun x:C => Some (Some x))
                        None
                     )
                  ) =
                f
               ) as E.
        apply eq_trans with
            (y:= d_prop_change_of_context (option C) f (option C) (fun v:option C => v)).
        unfold d_prop_letter_specify.
        rewrite <- d_prop_coc_composition_equality.
        apply d_prop_coc_pointwise_equality.
        intros.
        destruct x. simpl; reflexivity.
        simpl; reflexivity.
        apply d_prop_coc_identity_equality.
        rewrite <- E.
        mp (d_prop_change_of_context C (d_forall C f) (option C) Some).
        simpl. rewrite d_prop_letter_specify_identity.
        apply sd_logical_axiom. apply sd_special_case_ax.
        apply second_d_proof_context_change. assumption.
      Defined.

      Definition sd_exists_elim:
        forall (C:Type) (k:C) (T:DP C-> Type) (f:DP (option C)) (g:DP C),
          second_d_proof C k T (d_exists C f) ->
          second_d_proof
            (option C) (Some k)
            (add_hyp_d
               (option C)
               (d_theory_constant_embedding C T) f) (d_prop_constant_embedding C g) ->
          second_d_proof C k T g.
      Proof.
        intros.
        mp (d_implies C (d_implies C g (d_wrong C)) (d_wrong C)).
        apply sd_logical_axiom. apply sd_abs_ax.
        apply cpiw_syllogism with (X:= SDCPIW C k T) (y:= d_forall C (d_neg (option C) f)).
        simpl. apply sd_implies_intro.
        apply sd_forall_intro.
        unfold d_neg.
        apply cpiw_syllogism with
            (X:= SDCPIW
                   (option C) (Some k)
                   (d_theory_constant_embedding
                      C
                      (add_item
                         (DP C) T (d_implies C g (d_wrong C)))))
            (y:= d_prop_constant_embedding C g).
        simpl.
        apply sd_weakening with (T:=d_theory_constant_embedding C T).
        apply sd_implies_intro.
        assumption.
        intros.
        destruct X1.
        apply dtcc_intro. bh. assumption.
        simpl.
        assert
          (
            d_implies (option C) (d_prop_constant_embedding C g) (d_wrong (option C))
            =
            d_prop_constant_embedding C (d_implies C g (d_wrong C))) as E.
        unfold d_prop_constant_embedding; simpl; reflexivity.
        rewrite E.
        apply sd_theory_axiom.
        apply dtcc_intro. nh.
        simpl. apply X.
      Defined.

      Definition sd_forall_elim:
        forall (C:Type) (k:C) (T: DP C -> Type) (f: DP (option C)) (t:DT C),
          second_d_proof C k T (d_forall C f) ->
          second_d_proof C k T (d_prop_specify C t f).
      Proof.
        intros. mp (d_forall C f). apply sd_logical_axiom; apply sd_special_case_ax.
        assumption.
      Defined.

      Definition sd_exists_intro:
        forall (C:Type) (k:C) (T: DP C -> Type) (f: DP (option C)) (t:DT C),
          second_d_proof C k T (d_prop_specify C t f) ->
          second_d_proof C k T (d_exists C f).
      Proof.
        intros.
        apply cpiw_permutation with (X:= SDCPIW C k T) (y:= d_prop_specify C t f).
        simpl. apply sd_logical_axiom.
        apply sd_special_case_ax with (t:=t). simpl; assumption.
      Defined.
      
    End natural_deduction_rules_for_quantifiers.

  End natural_deduction_inference_rules.
  
  Section equality_manipulation_tools.
    
    Definition sd_equal_belongs_equiv_elim:
      forall (C:Type) (k:C) (T: DP C -> Type) (a b t:DT C),
        (second_d_proof C k T (d_equal C a b)) ->
        prod
          (second_d_proof C k T (d_equiv C (d_belongs C a t) (d_belongs C b t))) 
          (second_d_proof C k T (d_equiv C (d_belongs C t a) (d_belongs C t b))).
    Proof.
      intros.
      split.
      apply cpiw_and_left_elim with (X:= SDCPIW C k T) in X. simpl in X.
      apply sd_forall_elim with (t:= t) in X. unfold d_prop_specify in X.
      rewrite d_equiv_subst_eq in X. simpl in X. unfold d_term_constant_embedding in X.
      rewrite d_term_coc_subst_commutation with
          (D:=C) (env_var_ddo := fun (v:C) => v) (env_term_cd := d_letter C) in X.
      rewrite d_term_coc_subst_commutation with
          (D:=C) (env_var_ddo := fun (v:C) => v) (env_term_cd := d_letter C) in X.
      repeat rewrite d_term_subst_identity_equality in X.
      repeat rewrite d_term_coc_identity_equality in X. assumption.
      intros; simpl; reflexivity. intros; simpl; reflexivity.
      apply cpiw_and_right_elim with (X:= SDCPIW C k T) in X. simpl in X.
      apply sd_forall_elim with (t:= t) in X. unfold d_prop_specify in X.
      rewrite d_equiv_subst_eq in X. simpl in X. unfold d_term_constant_embedding in X.
      rewrite d_term_coc_subst_commutation with
          (D:=C) (env_var_ddo := fun (v:C) => v) (env_term_cd := d_letter C) in X.
      rewrite d_term_coc_subst_commutation with
          (D:=C) (env_var_ddo := fun (v:C) => v) (env_term_cd := d_letter C) in X.
      repeat rewrite d_term_subst_identity_equality in X.
      repeat rewrite d_term_coc_identity_equality in X. assumption.
      intros; simpl; reflexivity. intros; simpl; reflexivity.
    Defined.    

    Definition sd_equal_belongs_implies_left_elim:
      forall (C:Type) (k:C) (T: DP C -> Type) (a b t:DT C),
        (second_d_proof C k T (d_equal C a b)) ->
        prod
          (second_d_proof C k T (d_implies C (d_belongs C a t) (d_belongs C b t))) 
          (second_d_proof C k T (d_implies C (d_belongs C t a) (d_belongs C t b))).
    Proof.
      intros.
      split.
      papp C k T cpiw_equiv_left_elim.
      apply sd_equal_belongs_equiv_elim. assumption.
      papp C k T cpiw_equiv_left_elim.
      apply sd_equal_belongs_equiv_elim. assumption.
    Defined.

    Definition sd_equal_belongs_implies_right_elim:
      forall (C:Type) (k:C) (T: DP C -> Type) (a b t:DT C),
        (second_d_proof C k T (d_equal C a b)) ->
        prod
          (second_d_proof C k T (d_implies C (d_belongs C b t) (d_belongs C a t))) 
          (second_d_proof C k T (d_implies C (d_belongs C t b) (d_belongs C t a))).
    Proof.
      intros.
      split.
      papp C k T cpiw_equiv_right_elim.
      apply sd_equal_belongs_equiv_elim. assumption.
      papp C k T cpiw_equiv_right_elim.
      apply sd_equal_belongs_equiv_elim. assumption.
    Defined.

    Definition sd_equality_reflexivity:
      forall (C:Type) (k:C) (T: DP C -> Type) (x:DT C),
        second_d_proof C k T (d_equal C x x).
    Proof.
      intros.
      apply cpiw_and_intro with (X:= SDCPIW C k T).
      simpl; apply sd_forall_intro;
        papp (option C) (Some k) (d_theory_constant_embedding C T) cpiw_equiv_reflexivity.
      simpl; apply sd_forall_intro;
        papp (option C) (Some k) (d_theory_constant_embedding C T) cpiw_equiv_reflexivity.
    Defined.
    
    Definition sd_equality_symmetry:
      forall (C:Type) (k:C) (T: DP C -> Type) (x y:DT C),
        second_d_proof C k T (d_equal C x y) -> second_d_proof C k T (d_equal C y x).
    Proof.
      intros.
      apply cpiw_and_intro with (X:= SDCPIW C k T). simpl.
      apply sd_forall_intro. 
      papp (option C) (Some k) (d_theory_constant_embedding C T) cpiw_equiv_symmetry.
      apply sd_forall_inverse_intro.
      apply (cpiw_and_left_elim (SDCPIW C k T)) in X.
      assumption.
      apply sd_forall_intro. 
      papp (option C) (Some k) (d_theory_constant_embedding C T) cpiw_equiv_symmetry.
      apply sd_forall_inverse_intro.
      apply (cpiw_and_right_elim (SDCPIW C k T)) in X.
      assumption.    
    Defined.

    Definition sd_equality_transitivity:
      forall (C:Type) (k:C) (T: DP C -> Type) (x y z:DT C),
        second_d_proof C k T (d_equal C x y) ->
        second_d_proof C k T (d_equal C y z) ->
        second_d_proof C k T (d_equal C x z).
    Proof.
      intros.
      apply cpiw_and_intro with (X:= SDCPIW C k T). simpl.
      apply sd_forall_intro.
      apply cpiw_equiv_transitivity
        with
          (X:= SDCPIW (option C) (Some k) (d_theory_constant_embedding C T))     
          (y:=d_belongs
                (option C)
                (d_term_constant_embedding C y) (d_letter (option C) None)).
      apply sd_forall_inverse_intro.
      apply (cpiw_and_left_elim (SDCPIW C k T)) in X.
      assumption.
      apply sd_forall_inverse_intro.
      apply (cpiw_and_left_elim (SDCPIW C k T)) in X0.
      assumption.
      apply sd_forall_intro.
            apply cpiw_equiv_transitivity
        with
          (X:= SDCPIW (option C) (Some k) (d_theory_constant_embedding C T))     
          (y:=d_belongs
                (option C)
                (d_letter (option C) None) (d_term_constant_embedding C y)).
      apply sd_forall_inverse_intro.
      apply (cpiw_and_right_elim (SDCPIW C k T)) in X.
      assumption.
      apply sd_forall_inverse_intro.
      apply (cpiw_and_right_elim (SDCPIW C k T)) in X0.
      assumption.
    Defined.    

    Definition sd_unique_elim:
      forall (C:Type) (k:C) (T: DP C ->Type) (f:DP (option C)) (s t:DT C),
        second_d_proof C k T (d_unique C f) ->
        second_d_proof C k T (d_prop_specify C s f) ->
        second_d_proof C k T (d_prop_specify C t f) ->
        second_d_proof C k T (d_equal C s t).
    Proof.
      intros.
      unfold d_unique in X.
      mp (d_prop_specify C t f).
      mp (d_prop_specify C s f).  
      assert (
          d_implies
            C (d_prop_specify C s f)            
            (d_implies
               C (d_prop_specify C t f) (d_equal C s t))
          =
          d_prop_specify
            C s
            (d_prop_specify
               (option C)
               (d_term_constant_embedding C t)
               (
                 d_implies (option (option C))
                 (d_prop_change_of_context (option C) f (option (option C))
                    (option_rect (fun _ : option C => option (option C))
                       (fun a : C => Some (Some a)) (Some None)))
                 (d_implies (option (option C))
                    (d_prop_change_of_context (option C) f (option (option C))
                       (option_rect (fun _ : option C => option (option C))
                          (fun a : C => Some (Some a)) None))
                    (d_equal (option (option C)) (d_letter (option (option C)) (Some None))
                       (d_letter (option (option C)) None))))
              )                   
        ) as E1. unfold d_prop_specify.
      repeat rewrite d_implies_subst_eq.
      apply f_equal2.
      rewrite d_prop_double_substitution.
      rewrite d_prop_coc_subst_commutation with
          (D:=C) (env_var_ddo := fun v:C => v)
          (env_term_cd := option_rect (fun _ : option C => DT C) (d_letter C) s).
      rewrite d_prop_coc_identity_equality; reflexivity.
      intros.
      destruct x.
      simpl; reflexivity. 
      simpl. apply eq_sym; apply d_term_coc_identity_equality. 
      repeat apply f_equal2.
      rewrite d_prop_double_substitution.
      rewrite d_prop_coc_subst_commutation with
          (D:=C) (env_var_ddo := fun v:C => v)
          (env_term_cd := option_rect (fun _ : option C => DT C) (d_letter C) t).
      rewrite d_prop_coc_identity_equality; reflexivity.
      intros.
      destruct x.
      simpl; reflexivity.
      unfold d_term_constant_embedding; simpl.
      rewrite d_term_coc_subst_commutation with
          (D:=C) (env_var_ddo := fun v:C => v)
          (env_term_cd := d_letter C).
      rewrite d_term_subst_identity_equality; reflexivity.
      intros; simpl; reflexivity.
      rewrite d_prop_double_substitution.
      rewrite d_equal_subst_eq.
      unfold d_term_constant_embedding.
      simpl. 
      rewrite d_term_coc_subst_commutation with
          (D:=C) (env_var_ddo := fun v:C => v)
          (env_term_cd := d_letter C).
      rewrite d_term_coc_identity_equality.
      rewrite d_term_subst_identity_equality. reflexivity.
      intros.
      simpl; reflexivity. 
      rewrite E1.
      apply sd_forall_elim.
      apply sd_forall_intro.
      apply sd_forall_elim.
      apply sd_forall_inverse_intro. assumption. assumption. assumption.
    Defined.
    
  End equality_manipulation_tools.

  Ltac eqbee := apply sd_equal_belongs_equiv_elim.
  Ltac eqbile := apply sd_equal_belongs_implies_left_elim.
  Ltac eqbire := apply sd_equal_belongs_implies_right_elim.
  Ltac sdeqr:= apply sd_equality_reflexivity. 
  Ltac sdeqs := apply sd_equality_symmetry.               
  Ltac sdeqt b:= apply sd_equality_transitivity with (y:=b).               
  Ltac uee z := apply sd_unique_elim with (f:=z).

  Section equivalence_manipulation_tools.

    Ltac ap := assumption.
    
    Definition second_d_equivalence_reflexivity_proof
               (C:Type) (k:C) (T:DP C -> Type) (p:DP C): 
      second_d_proof C k T (d_equiv C p p):=
      cpiw_equiv_reflexivity (SDCPIW C k T) p.

    Ltac er := apply second_d_equivalence_reflexivity_proof.
    
    Definition second_d_equivalence_symmetry_proof
               (C:Type) (k:C) (T:DP C -> Type) (p q:DP C): 
      second_d_proof C k T (d_equiv C p q) ->
      second_d_proof C k T (d_equiv C q p) :=
      cpiw_equiv_symmetry (SDCPIW C k T) p q.

    Ltac es := apply second_d_equivalence_symmetry_proof.

    Definition second_d_equivalence_transitivity_proof
               (C:Type) (k:C) (T:DP C -> Type) (p q r:DP C): 
      second_d_proof C k T (d_equiv C p q) ->
      second_d_proof C k T (d_equiv C q r) ->
      second_d_proof C k T (d_equiv C p r) :=
      cpiw_equiv_transitivity (SDCPIW C k T) p q r.

    Ltac et z := apply second_d_equivalence_transitivity_proof with (q:=z).

    Definition second_d_equivalence_implies_proof
               (C:Type) (k:C) (T:DP C -> Type) (a a' b b':DP C): 
      second_d_proof C k T (d_equiv C a a') ->
      second_d_proof C k T (d_equiv C b b') ->
      second_d_proof C k T (d_equiv C (d_implies C a b) (d_implies C a' b')) :=
      cpiw_equiv_implies (SDCPIW C k T) a a' b b'.

    Ltac ei := apply second_d_equivalence_implies_proof.
    
    Definition second_d_equivalence_neg_proof
               (C:Type) (k:C) (T:DP C -> Type) (p q:DP C): 
      second_d_proof C k T (d_equiv C p q) ->
      second_d_proof C k T (d_equiv C (d_neg C p) (d_neg C q)).
    Proof.
      intros. ei. ap. er.
    Defined.        

    Ltac en := apply second_d_equivalence_neg_proof.
    
    Definition second_d_equivalence_and_proof
               (C:Type) (k:C) (T:DP C -> Type) (a a' b b':DP C): 
      second_d_proof C k T (d_equiv C a a') ->
      second_d_proof C k T (d_equiv C b b') ->
      second_d_proof C k T (d_equiv C (d_and C a b) (d_and C a' b')).
    Proof.
      intros. ei. ei. ap. en. ap. er.
    Defined.
    
    Ltac ea := apply second_d_equivalence_and_proof.

    Definition second_d_equivalence_or_proof
               (C:Type) (k:C) (T:DP C -> Type) (a a' b b':DP C): 
      second_d_proof C k T (d_equiv C a a') ->
      second_d_proof C k T (d_equiv C b b') ->
      second_d_proof C k T (d_equiv C (d_or C a b) (d_or C a' b')).
    Proof.
      intros. ei. en. ap. ap.
    Defined.
    
    Ltac eo := apply second_d_equivalence_or_proof.

    Definition second_d_equivalence_equiv_proof
               (C:Type) (k:C) (T:DP C -> Type) (a a' b b':DP C): 
      second_d_proof C k T (d_equiv C a a') ->
      second_d_proof C k T (d_equiv C b b') ->
      second_d_proof C k T (d_equiv C (d_equiv C a b) (d_equiv C a' b')).
    Proof.
      intros. ea. ei. ap. ap. ei. ap. ap.        
    Defined.
    
    Ltac ee := apply second_d_equivalence_equiv_proof.
    
    Definition second_d_equivalence_forall_proof:
      forall (C:Type) (k:C) (T:DP C -> Type) (a b:DP (option C)),
        second_d_proof (option C) (Some k) (d_theory_constant_embedding C T)
                      (d_equiv (option C) a b) -> 
        second_d_proof C k T (d_equiv C (d_forall C a) (d_forall C b)).
    Proof.
      intros.
      apply (cpiw_equiv_intro (SDCPIW C k T)).
      simpl.
      mp (d_forall C (d_implies (option C) a b)).
      apply sd_logical_axiom; apply sd_forall_mp_ax.
      apply sd_forall_intro.
      apply (cpiw_equiv_left_elim
               (SDCPIW (option C) (Some k) (d_theory_constant_embedding C T))).              
      apply X.
      mp (d_forall C (d_implies (option C) b a)).
      apply sd_logical_axiom; apply sd_forall_mp_ax.
      apply sd_forall_intro.
      apply (cpiw_equiv_right_elim
               (SDCPIW (option C) (Some k) (d_theory_constant_embedding C T))).
      apply X.
    Defined.      

    Ltac ef := apply second_d_equivalence_forall_proof.
    
    Definition second_d_equivalence_exists_proof:
      forall (C:Type) (k:C) (T:DP C -> Type) (a b:DP (option C)),
        second_d_proof (option C) (Some k) (d_theory_constant_embedding C T)
                      (d_equiv (option C) a b) -> 
        second_d_proof C k T (d_equiv C (d_exists C a) (d_exists C b)).
    Proof.
      intros. ei. ef. ei. ap. er. er.
    Defined.

    Ltac eex := apply second_d_equivalence_exists_proof.

    Definition second_d_equivalence_unique_proof:
      forall (C:Type) (k:C) (T:DP C -> Type) (a b:DP (option C)),
        second_d_proof (option C) (Some k) (d_theory_constant_embedding C T)
                      (d_equiv (option C) a b) -> 
        second_d_proof C k T (d_equiv C (d_unique C a) (d_unique C b)).
    Proof.
      intros. ef. ef. ei. rewrite <- d_equiv_coc_eq.
      unfold d_theory_constant_embedding. rewrite d_prop_coc_composition_equality.
      rewrite d_prop_coc_pointwise_equality with (env2:= Some).
      apply second_d_proof_context_change.
      rewrite d_prop_coc_identity_equality. ap.
      intros.
      destruct x. simpl; reflexivity. simpl; reflexivity.
      ei.
      rewrite <- d_equiv_coc_eq.
      apply sd_weakening with
          (T:= d_theory_context_change
                 (option C) (d_theory_constant_embedding C T)
                 (option (option C))
                 (option_rect
                    (fun _ : option C => option (option C))
                    (fun a0 : C => Some (Some a0)) None)
          ).
      assert (Some (Some k) =
              option_rect
                (fun _ : option C => option (option C))
                (fun a0 : C => Some (Some a0)) None
                (Some k)
             ) as E1.
      simpl; reflexivity. rewrite E1.        
      apply second_d_proof_context_change.
      assumption.
      intros; destruct X0.
      assert (
          (d_prop_change_of_context
             (option C) p (option (option C))
             (option_rect
                (fun _ : option C => option (option C))
                (fun a0 : C => Some (Some a0))
                None))
          =
          d_prop_constant_embedding (option C) p
        ) as E2.
      destruct d.
      unfold d_prop_constant_embedding.
      repeat rewrite <- d_prop_coc_composition_equality.
      apply d_prop_coc_pointwise_equality.
      intros.
      simpl; reflexivity.
      rewrite E2.
      apply dtcc_intro; assumption.
      er.
    Defined.        

    Ltac eu := apply second_d_equivalence_unique_proof.

    Definition sd_forall_letter_elim:
      forall (C:Type) (T: DP C -> Type) (f: DP (option C)) (k l:C),
        second_d_proof C k T (d_forall C f) ->
        second_d_proof C k T (d_prop_letter_specify C l f).
    Proof.
      intros.
      mp (d_forall C f).
      apply sd_letter_special_case. ap.
    Defined.        

    Definition sd_equal_elim_belongs_letter:
      forall (C:Type) (T: DP C -> Type) (s t:DT C) (k x:C),
        second_d_proof C k T (d_equal C s t) ->
        prod
          (second_d_proof
             C k T 
             (d_equiv C (d_belongs C s (d_letter C x)) (d_belongs C t (d_letter C x))))
          (second_d_proof
             C k T 
             (d_equiv C (d_belongs C (d_letter C x) s) (d_belongs C (d_letter C x) t))).
    Proof.
      intros.
      assert
        (forall u: DT C,
            d_term_change_of_context
              (option C) (d_term_constant_embedding C u) C
              (option_rect (fun _ : option C => C) (fun x : C => x) x)
            =
            u)
        as E.
      intros.
      unfold d_term_constant_embedding.
      rewrite <- d_term_coc_composition_equality.
      rewrite d_term_coc_pointwise_equality with (env2 := fun a:C => a).
      apply d_term_coc_identity_equality.
      intros; simpl; reflexivity.               
      split.
      apply (cpiw_and_left_elim (SDCPIW C k T)) in X.
      simpl in X.
      apply sd_forall_letter_elim with (l:=x) in X.
      unfold d_prop_letter_specify in X.
      rewrite d_equiv_coc_eq in X.
      repeat rewrite d_belongs_coc_eq in X.
      repeat rewrite E in X.
      simpl in X.
      ap.
      apply (cpiw_and_right_elim (SDCPIW C k T)) in X.
      simpl in X.
      apply sd_forall_letter_elim with (l:=x) in X.
      unfold d_prop_letter_specify in X.
      rewrite d_equiv_coc_eq in X.
      repeat rewrite d_belongs_coc_eq in X.
      repeat rewrite E in X.
      simpl in X.
      ap.
    Defined.
    
    Definition second_d_equivalence_exists_unique_proof:
      forall (C:Type) (k:C) (T:DP C -> Type) (a b:DP (option C)),
        second_d_proof (option C) (Some k) (d_theory_constant_embedding C T)
                      (d_equiv (option C) a b) -> 
        second_d_proof C k T (d_equiv C (d_exists_unique C a) (d_exists_unique C b)).
    Proof.
      intros. ea. eex. ap. eu. ap.
    Defined.
    
    Definition sd_extensionality_of_definitions:
      forall (C:Type) (k:C) (T: DP C -> Type) (p q: DP (option C)),
        second_d_proof (option C) (Some k) (d_theory_constant_embedding C T)
                       (d_equiv (option C) p q) ->
        second_d_proof C k T (d_equal C (d_def C p) (d_def C q)).
    Proof.
      intros.
      assert
        (second_d_proof C k T (d_equiv C (d_exists_unique C p) (d_exists_unique C q))) as EEU.
      apply second_d_equivalence_exists_unique_proof; assumption.
      apply cpiw_cases with (X:= SDCPIW C k T) (x:= d_exists_unique C p).
      simpl. ded. apply sd_unique_elim with (f:=p).
      apply sd_and_right_elim with (a:= d_exists C p). apply sd_theory_axiom; nh.
      mp (d_exists_unique C p). apply sd_logical_axiom; apply sd_if_exun.
      apply sd_theory_axiom; nh.
      mp (d_prop_specify C (d_def C q) q).
      apply sd_weakening_hypothesis; apply cpiw_equiv_right_elim with (X:= SDCPIW C k T).
      simpl. apply sd_forall_intro in X. apply sd_forall_elim with (t:= d_def C q) in X.
      unfold d_prop_specify in X. rewrite d_equiv_subst_eq in X.
      unfold d_prop_specify; assumption.
      mp (d_exists_unique C q). apply sd_logical_axiom; apply sd_if_exun.
      mp (d_exists_unique C p).
      apply sd_weakening_hypothesis; apply cpiw_equiv_left_elim with (X:= SDCPIW C k T).
      assumption. apply sd_theory_axiom; nh.
      assert
        (second_d_proof
           C k T
           (d_equiv
              C (d_neg C (d_exists_unique C p)) (d_neg C (d_exists_unique C q)))) as NEEU.
      apply second_d_equivalence_neg_proof. assumption.
      ded. sdeqt (d_letter C k). mp (d_neg C (d_exists_unique C p)).
      apply sd_logical_axiom; apply sd_if_not_exun. apply sd_theory_axiom; nh.
      sdeqs. mp (d_neg C (d_exists_unique C q)).
      apply sd_logical_axiom; apply sd_if_not_exun.
      mp (d_neg C (d_exists_unique C p)). 
      apply sd_weakening_hypothesis; apply cpiw_equiv_left_elim with (X:= SDCPIW C k T).
      assumption. apply sd_theory_axiom; nh.
    Defined.      

    Fixpoint sd_general_equality_elimination_prop
             (C:Type) (p:DP C)
             (D:Type)
             (k:D) (T:DP D -> Type) 
             (env1 env2: C -> DT D)
             (eqpr: forall x:C, second_d_proof D k T (d_equal D (env1 x) (env2 x)))
             {struct p}:
      second_d_proof
        D k T (d_equiv D (d_prop_substitution C p D env1) (d_prop_substitution C p D env2))
    with
    sd_general_equality_elimination_term
      (C:Type) (t:DT C)
      (D:Type)
      (k:D) (T:DP D -> Type) 
      (env1 env2: C -> DT D)
      (eqpr: forall x:C, second_d_proof D k T (d_equal D (env1 x) (env2 x)))
      {struct t}:
      second_d_proof
        D k T
        (d_equal
           D 
           (d_term_substitution C t D env1) (d_term_substitution C t D env2)).
    Proof.
      destruct p.
      simpl.
      et (d_belongs D (d_term_substitution C d D env1) (d_term_substitution C d0 D env2)).
      eqbee. apply sd_general_equality_elimination_term; ap.
      eqbee. apply sd_general_equality_elimination_term; ap.
      simpl; er.
      simpl. ei. apply sd_general_equality_elimination_prop; ap. apply sd_general_equality_elimination_prop; ap.
      simpl. ef. apply sd_general_equality_elimination_prop.
      intros. destruct x.      
      simpl. unfold d_term_constant_embedding.
      rewrite <- d_equal_coc_eq.
      apply second_d_proof_context_change. apply eqpr.
      simpl. sdeqr.
      destruct t.
      simpl. apply eqpr.
      simpl. apply sd_extensionality_of_definitions.
      apply sd_general_equality_elimination_prop.
      intros. destruct x.      
      simpl. unfold d_term_constant_embedding.
      rewrite <- d_equal_coc_eq.
      apply second_d_proof_context_change. apply eqpr.
      simpl. sdeqr.
    Defined.   
   
   Definition sd_equal_prop_elim:
     forall (C:Type) (k:C) (T: DP C -> Type) (s t:DT C) (p: DP (option C)),
       second_d_proof C k T (d_equal C s t) ->
       second_d_proof C k T (d_equiv C (d_prop_specify C s p) (d_prop_specify C t p)).
   Proof.
     intros.
     unfold d_prop_specify.
     apply sd_general_equality_elimination_prop.
     intros.
     destruct x. simpl. sdeqr. simpl. assumption.
   Defined.
   
   Definition sd_equal_term_elim:
     forall (C:Type) (k:C) (T: DP C -> Type) (s t:DT C) (u: DT (option C)),
       second_d_proof C k T (d_equal C s t) ->
       second_d_proof C k T (d_equal C (d_term_specify C s u) (d_term_specify C t u)).
   Proof.
     intros.
     unfold d_term_specify.
     apply sd_general_equality_elimination_term.
     intros.
     destruct x. simpl. sdeqr. simpl. assumption.
   Defined.

   Section introduction_of_unicity.
     
     (** We define a tool for introducing two fresh variables to any context; 
      then we build a natural inference rule to derive the unicity of the 
      objects potentially satisfying a given predicate. The definition of
      "d_unique C p" expressing the unicity of an object satisfying p is 
      somewhat obfuscated and we hope that this tool, along with 
      "sd_unique_intro" defined above, will help convince the user that 
      "d_unique" has actually the intended behavior. *)

     Variable C:Type.
     Variable k:C.
     Variable T:DP C -> Type.
     Variable p: DP (option C).
     
     Inductive add_two_vars:Type:=
     |atv_new_var1:add_two_vars
     |atv_new_var2:add_two_vars
     |atv_base_var: C -> add_two_vars.
     
     Definition d_theory_embed_atv:= d_theory_context_change C T add_two_vars atv_base_var. 

     (** We introduce shorter notations in order (hopefully) to make the statement of the 
      result more clear *)
     
     Notation A:= add_two_vars.
     Notation x1 := atv_new_var1.
     Notation x2 := atv_new_var2.
     Notation k':= (atv_base_var k).
     Notation p_A:=
       (d_prop_change_of_context
          (option C) p (option A) (extend_map_to_bound_variables C A atv_base_var)).

     Notation T_and_p_new_var1_and_p_new_var2:=
       (add_hyp_d A (add_hyp_d A d_theory_embed_atv (d_prop_letter_specify A x1 p_A))
                  (d_prop_letter_specify A x2 p_A)).
       
     (** This auxiliary map will be used in this proof only*)
     Let cvar_aux (l:add_two_vars): option (option C):=
       match l with
       |atv_new_var1 => Some None
       |atv_new_var2 => None
       |atv_base_var u => Some (Some u)
       end.

     Definition sd_unique_intro: 
       second_d_proof A k' T_and_p_new_var1_and_p_new_var2
                      (d_equal A (d_letter A x1) (d_letter A x2)) ->
       second_d_proof C k T (d_unique C p).
     Proof.
       intros.
       unfold d_unique.
       apply sd_forall_intro.
       apply sd_forall_intro.
       assert (
           d_implies
             (option (option C))
             (d_prop_change_of_context
                (option C) p (option (option C))
                (option_rect
                   (fun _ : option C => option (option C)) (fun a : C => Some (Some a))
                   (Some None)))
             (d_implies
                (option (option C))
                (d_prop_change_of_context
                   (option C) p (option (option C))
                   (option_rect
                      (fun _ : option C => option (option C)) (fun a : C => Some (Some a))
                      None))
                (d_equal (option (option C)) (d_letter (option (option C)) (Some None))
                         (d_letter (option (option C)) None)))
           =
           d_prop_change_of_context
             A
             (d_implies
                A
                (d_prop_letter_specify A x1 p_A)
                (d_implies
                   A (d_prop_letter_specify A x2 p_A)
                   (d_equal A (d_letter A x1) (d_letter A x2)))
             )
             (option (option C)) cvar_aux
         ) as E1.
       rewrite d_implies_coc_eq.
       rewrite d_implies_coc_eq.
       rewrite d_equal_coc_eq.
       apply f_equal2.
       unfold d_prop_letter_specify.
       repeat rewrite <- d_prop_coc_composition_equality.
       apply d_prop_coc_pointwise_equality.
       intros. destruct x. simpl; reflexivity. simpl; reflexivity.
       apply f_equal2.
       unfold d_prop_letter_specify.
       repeat rewrite <- d_prop_coc_composition_equality.
       apply d_prop_coc_pointwise_equality.
       intros. destruct x. simpl; reflexivity. simpl. reflexivity.
       apply f_equal2. simpl; reflexivity. simpl; reflexivity.
       rewrite E1.
       apply sd_weakening with
           (T:= d_theory_context_change
                  A (d_theory_embed_atv)
                  (option (option C)) cvar_aux).
       assert (Some (Some k) = cvar_aux k') as E2.
       simpl; reflexivity. rewrite E2.
       apply second_d_proof_context_change.
       ded; ded; assumption.
       intros.
       unfold d_theory_embed_atv in X0.
       destruct X0. destruct d.
       unfold d_theory_constant_embedding.
       assert (
           d_prop_change_of_context
             A (d_prop_change_of_context C p0 A atv_base_var)
             (option (option C)) cvar_aux
           =
           d_prop_change_of_context
             (option C)
             (d_prop_change_of_context C p0 (option C) Some)
             (option (option C)) Some
         ) as E3.
       repeat rewrite <- d_prop_coc_composition_equality.       
       apply d_prop_coc_pointwise_equality.
       intros. simpl; reflexivity. rewrite E3. repeat apply dtcc_intro; assumption.
     Defined.
       
   End introduction_of_unicity.
   
  End equivalence_manipulation_tools.
  
  Section proof_of_the_fd_axiom_about_d_def.
 
    Definition sd_exun_belongs_letter_prop:
      forall (C:Type) (k x:C) (T: DP C -> Type) (p: DP (option C)),
        second_d_proof
          C k T
          (d_equiv
             C
             (d_belongs C (d_letter C x) (d_def C p))
             (d_exun_belongs_letter_prop C k x p)                  
          ).
    Proof.
      intros.
      unfold d_exun_belongs_letter_prop.
      papp C k T cpiw_equiv_intro. simpl. ded.
      papp C k (add_hyp_d C T (d_belongs C (d_letter C x) (d_def C p))) cpiw_and_intro.
      simpl. ded. apply sd_forall_intro.
      apply cpiw_permutation with
          (X:= 
             SDCPIW
               (option C) (Some k) 
               (d_theory_constant_embedding
                  C (add_item
                       (DP C)
                       (add_item
                          (DP C) T
                          (d_belongs C (d_letter C x) (d_def C p))) (d_exists_unique C p))))
               (y := d_prop_constant_embedding C (d_belongs C (d_letter C x) (d_def C p))).   
      simpl. ded. eqbile.
      uee (d_prop_change_of_context
             (option C) p (option (option C))
             (option_rect
                (fun _ : option C => option (option C)) (fun a : C => Some (Some a))
                None)).
      assert (
          d_unique
            (option C)
            (d_prop_change_of_context
               (option C) p (option (option C))
               (option_rect
                  (fun _ : option C => option (option C)) (fun a : C => Some (Some a))
                  None))
          =
          d_prop_constant_embedding C (d_unique C p)
        ) as E1.
      unfold d_prop_constant_embedding.
      rewrite d_unique_coc_eq.
      unfold extend_map_to_bound_variables; reflexivity.
      rewrite E1. unfold d_theory_constant_embedding. unfold d_prop_constant_embedding.
      apply sd_weakening_hypothesis.
      apply second_d_proof_context_change.
      apply cpiw_and_right_elim with
          (X:= SDCPIW
                 C k
                 (add_item
                    (DP C)
                    (add_item
                       (DP C) T
                       (d_belongs C (d_letter C x) (d_def C p))) (d_exists_unique C p)))
          (x:= d_exists C p). simpl. apply sd_theory_axiom. nh.
      mp (d_prop_constant_embedding C (d_exists_unique C p)).
      unfold d_prop_constant_embedding.
      rewrite d_exists_unique_coc_eq.
      apply sd_logical_axiom.
      apply sd_if_exun.
      apply sd_theory_axiom. bh.
      apply dtcc_intro; nh.
      rewrite <- d_prop_letter_specify_identity.
      unfold d_prop_letter_specify.
      rewrite <- d_prop_coc_composition_equality.
      rewrite d_prop_coc_pointwise_equality with (env2 := fun v:option C => v).
      rewrite d_prop_coc_identity_equality.
      apply sd_theory_axiom; nh.
      intros. destruct x0. simpl; reflexivity. simpl; reflexivity.
      simpl.
      apply sd_theory_axiom; apply dtcc_intro; bh; nh.
      apply cpiw_permutation with (y:= d_belongs C (d_letter C x) (d_def C p)).
      simpl. ded. eqbile. mp (d_neg C (d_exists_unique C p)).
      apply sd_logical_axiom. apply sd_if_not_exun.
      apply sd_theory_axiom; nh. apply sd_theory_axiom; nh.
      apply cpiw_cases with (x:= d_exists_unique C p).
      simpl. ded. ded. mp (d_prop_specify C (d_def C p) p).
      assert(
          d_implies C (d_prop_specify C (d_def C p) p) (d_belongs C (d_letter C x) (d_def C p))
          =          
          d_prop_specify
            C (d_def C p)
            (d_implies (option C) p (d_belongs
                                       (option C)
                                       (d_letter (option C) (Some x))
                                       (d_letter (option C) None)))
        ) as E2.
      unfold d_prop_specify.
      rewrite d_implies_subst_eq.
      rewrite d_belongs_subst_eq.
      simpl; reflexivity.
      rewrite E2.
      apply sd_forall_elim. mp (d_exists_unique C p).
      apply cpiw_and_left_elim with
          (X:=
             SDCPIW
               C k
               (add_item
                  (DP C)
                  (add_item
                     (DP C) T (d_exists_unique C p))
                  (d_and
                     C
                     (d_implies
                        C (d_exists_unique C p)
                        (d_forall
                           C
                           (d_implies
                              (option C) p
                              (d_belongs
                                 (option C) (d_letter (option C) (Some x))
                                 (d_letter (option C) None)))))
                     (d_implies
                        C (d_neg C (d_exists_unique C p))
                        (d_belongs C (d_letter C x) (d_letter C k))))
          )) (y:= d_implies C (d_neg C (d_exists_unique C p))
             (d_belongs C (d_letter C x) (d_letter C k))).
      simpl. apply sd_theory_axiom; nh. apply sd_theory_axiom; bh; nh.
      mp (d_exists_unique C p).
      apply sd_logical_axiom.
      apply sd_if_exun.
      apply sd_theory_axiom; bh; nh.
      simpl. ded. ded.
      mp (d_belongs C (d_letter C x) (d_letter C k)).
      eqbire. mp (d_neg C (d_exists_unique C p)).
      apply sd_logical_axiom.
      apply sd_if_not_exun.
      apply sd_theory_axiom; bh; nh. mp (d_neg C (d_exists_unique C p)).      
      apply cpiw_and_right_elim with
          (X:=
             SDCPIW
               C k
               (add_item
                  (DP C)
                  (add_item
                     (DP C) T (d_neg C (d_exists_unique C p)))
                  (d_and
                     C
                     (d_implies
                        C (d_exists_unique C p)
                        (d_forall
                           C
                           (d_implies
                              (option C) p
                              (d_belongs
                                 (option C) (d_letter (option C) (Some x))
                                 (d_letter (option C) None)))))
                     (d_implies
                        C (d_neg C (d_exists_unique C p))
                        (d_belongs C (d_letter C x) (d_letter C k))))
          )) (x:=
                d_implies
                  C (d_exists_unique C p)
                  (d_forall
                     C
                     (d_implies
                        (option C) p
                        (d_belongs
                           (option C) (d_letter (option C) (Some x))
                           (d_letter (option C) None))))
             ).
      apply sd_theory_axiom; nh.  apply sd_theory_axiom; bh; nh.
    Defined. 
      

    Definition sd_exun_belongs_letter_term:
      forall (C:Type) (k x:C) (T: DP C -> Type) (t: DT C),
        second_d_proof
          C k T
          (d_equiv
             C
             (d_belongs C (d_letter C x) t)
             (d_exun_belongs_letter_term C k x t)                  
          ).
    Proof.
      intros.
      destruct t.
      simpl.
      papp C k T cpiw_equiv_reflexivity.
      simpl; apply sd_exun_belongs_letter_prop.
    Defined.   

    Definition sd_exun_belongs_prop_term:
      forall (C:Type) (k:C) (T: DP C -> Type) (p: DP (option C)) (t: DT C),
        second_d_proof
          C k T
          (d_equiv
             C
             (d_belongs C (d_def C p) t)
             (d_exun_belongs_prop_term C k p t)                  
          ).
    Proof.      
      intros.
      unfold d_exun_belongs_prop_term.
      papp C k T cpiw_equiv_intro. simpl. ded.
      papp C k (add_hyp_d C T (d_belongs C (d_def C p) t)) cpiw_and_intro.
      simpl. ded. apply sd_forall_intro.
      apply cpiw_permutation with
          (X:= 
             SDCPIW
               (option C) (Some k) 
               (d_theory_constant_embedding
                  C (add_item
                       (DP C)
                       (add_item
                          (DP C) T
                          (d_belongs C (d_def C p) t)) (d_exists_unique C p))))
               (y := d_prop_constant_embedding C (d_belongs C (d_def C p) t)).   
      simpl. ded.      
      apply cpiw_syllogism with
          (X := SDCPIW
                  (option C) (Some k)
                  (add_item
                     (DP (option C))
                     (d_theory_constant_embedding
                        C
                        (add_item
                           (DP C)
                           (add_item
                              (DP C) T
                              (d_belongs C (d_def C p) t)) (d_exists_unique C p))) p)
          )
          (y:= d_belongs (option C) (d_letter (option C) None)
                         (d_term_constant_embedding C t)).
      simpl. unfold d_prop_constant_embedding. rewrite d_belongs_coc_eq.
      unfold d_term_constant_embedding.
      eqbile.
      uee (d_prop_change_of_context
             (option C) p (option (option C))
             (option_rect
                (fun _ : option C => option (option C)) (fun a : C => Some (Some a))
                None)).
      assert (
          d_unique
            (option C)
            (d_prop_change_of_context
               (option C) p (option (option C))
               (option_rect
                  (fun _ : option C => option (option C)) (fun a : C => Some (Some a))
                  None))
          =
          d_prop_constant_embedding C (d_unique C p)
        ) as E1.
      unfold d_prop_constant_embedding.
      rewrite d_unique_coc_eq.
      unfold extend_map_to_bound_variables; reflexivity.
      rewrite E1. unfold d_theory_constant_embedding. unfold d_prop_constant_embedding.
      apply sd_weakening_hypothesis.
      apply second_d_proof_context_change.
      apply cpiw_and_right_elim with
          (X:= SDCPIW
                 C k
                 (add_item
                    (DP C)
                    (add_item
                       (DP C) T
                       (d_belongs C (d_def C p) t)) (d_exists_unique C p)))
          (x:= d_exists C p). simpl. apply sd_theory_axiom. nh.
      mp (d_prop_constant_embedding C (d_exists_unique C p)).
      unfold d_prop_constant_embedding.
      rewrite d_exists_unique_coc_eq.
      apply sd_logical_axiom.
      apply sd_if_exun.
      apply sd_theory_axiom. bh.
      apply dtcc_intro; nh.
      rewrite <- d_prop_letter_specify_identity.
      unfold d_prop_letter_specify.
      rewrite <- d_prop_coc_composition_equality.
      rewrite d_prop_coc_pointwise_equality with (env2 := fun v:option C => v).
      rewrite d_prop_coc_identity_equality.
      apply sd_theory_axiom; nh.
      intros. destruct x. simpl; reflexivity. simpl; reflexivity.
      simpl.
      papp
        (option C) (Some k)
        (add_item
           (DP (option C))
           (d_theory_constant_embedding
              C
              (add_item
                 (DP C)
                 (add_item
                    (DP C) T
                    (d_belongs C (d_def C p) t)) (d_exists_unique C p))) p) 
        cpiw_equiv_left_elim.
      simpl. apply sd_exun_belongs_letter_term.      
      apply sd_theory_axiom; apply dtcc_intro; bh; nh.
      apply cpiw_permutation with (y:= d_belongs C (d_def C p) t).
      simpl. ded.
      apply cpiw_syllogism with
          (X:= SDCPIW
                 C k
                 (add_item
                    (DP C)
                    (add_item
                       (DP C) T (d_belongs C (d_def C p) t))
                    (d_neg C (d_exists_unique C p)))   
          ) (y:= d_belongs C (d_letter C k) t). simpl.      
      eqbile. mp (d_neg C (d_exists_unique C p)).
      apply sd_logical_axiom. apply sd_if_not_exun.
      apply sd_theory_axiom; nh.
      apply cpiw_equiv_left_elim. simpl. apply sd_exun_belongs_letter_term.
      apply sd_theory_axiom; nh.
      apply cpiw_cases with (x:= d_exists_unique C p).
      simpl. ded. ded. mp (d_prop_specify C (d_def C p) p).
      assert(
          d_implies C (d_prop_specify C (d_def C p) p) (d_belongs C (d_def C p) t)
          =          
          d_prop_specify
            C (d_def C p)
            (d_implies (option C) p (d_belongs
                                       (option C)
                                       (d_letter (option C) None)
                                       (d_term_constant_embedding C t)))       
        ) as E2.
      unfold d_prop_specify.
      rewrite d_implies_subst_eq.
      rewrite d_belongs_subst_eq.
      simpl. repeat apply f_equal.
      unfold d_term_constant_embedding.
      rewrite d_term_coc_subst_commutation with (D:=C) (env_var_ddo := fun (v:C) => v)
                                                (env_term_cd := d_letter C).
      rewrite d_term_subst_identity_equality. rewrite d_term_coc_identity_equality.
      reflexivity.
      intros; simpl; reflexivity.
      rewrite E2.
      apply cpiw_syllogism with
          (X:=
             SDCPIW C k 
             (add_item
                (DP C)
                (add_item
                   (DP C) T (d_exists_unique C p))
                (d_and
                   C
                   (d_implies
                      C (d_exists_unique C p)
                      (d_forall
                         C
                         (d_implies
                            (option C) p
                            (d_exun_belongs_letter_term
                               (option C) (Some k) None
                               (d_term_constant_embedding C t)))))
                   (d_implies
                      C (d_neg C (d_exists_unique C p)) (d_exun_belongs_letter_term C k k t))))
          )
          (y:= d_prop_specify
                 C
                 (d_def C p)
                 (d_exun_belongs_letter_term
                    (option C) (Some k) None (d_term_constant_embedding C t))
          ). fold d_prop_substitution. simpl.
      unfold d_prop_specify.
      rewrite <- d_implies_subst_eq.
      assert (
          d_prop_substitution
            (option C)
            (d_implies
               (option C) p
               (d_exun_belongs_letter_term
                  (option C) (Some k) None (d_term_constant_embedding C t)))
            C (option_rect (fun _ : option C => DT C) (d_letter C) (d_def C p))
          =
          d_prop_specify
            C (d_def C p)
            (d_implies
               (option C) p
               (d_exun_belongs_letter_term
                  (option C) (Some k) None (d_term_constant_embedding C t)))
        ) as E3. unfold d_prop_specify; reflexivity. rewrite E3.      
      apply sd_forall_elim. mp (d_exists_unique C p).
      apply cpiw_and_left_elim with
          (X:=
             SDCPIW
               C k
               (add_item
                  (DP C)
                  (add_item
                     (DP C) T (d_exists_unique C p))
                  (d_and
                     C
                     (d_implies
                        C (d_exists_unique C p)
                        (d_forall
                           C
                           (d_implies
                              (option C) p
                              (d_exun_belongs_letter_term
                                 (option C) (Some k) None                                 
                                 (d_term_constant_embedding C t)))))
                     (d_implies
                        C (d_neg C (d_exists_unique C p))
                        (d_exun_belongs_letter_term C k k t)))
          )) (y:= d_implies C (d_neg C (d_exists_unique C p))
             (d_exun_belongs_letter_term C k k t)).
      simpl. apply sd_theory_axiom. nh. apply sd_theory_axiom; bh; nh.
      mp (d_exists_unique C p). fold d_term_substitution. simpl.
      assert (
          d_implies
            C
            (d_prop_specify
               C (d_def C p)
               (d_exun_belongs_letter_term (option C) (Some k) None
                                           (d_term_constant_embedding C t)))
            (d_belongs
               C (d_def C p)
               (d_term_substitution
                  (option C) (d_term_constant_embedding C t) C
                  (option_rect (fun _ : option C => DT C) (d_letter C) (d_def C p))))
          =
          d_prop_specify
            C (d_def C p)
            (d_implies
               (option C)
               (d_exun_belongs_letter_term (option C) (Some k) None
                                           (d_term_constant_embedding C t))
               (d_belongs (option C) (d_letter (option C) None)
                          (d_term_constant_embedding C t))
            )             
          
        ) as E4.
      unfold d_prop_specify. simpl; reflexivity.
      rewrite E4. ded.
      apply sd_forall_elim.
      apply sd_forall_intro.
      papp
        (option C) (Some k)        
        (d_theory_constant_embedding
           C
           (add_item
              (DP C)
              (add_item
                 (DP C)
                 (add_item
                    (DP C)
                    T
                    (d_exists_unique C p))
                 (d_and
                    C
                    (d_implies
                       C (d_exists_unique C p)
                       (d_forall
                          C
                          (d_implies
                             (option C) p
                             (d_exun_belongs_letter_term
                                (option C) (Some k) None
                                (d_term_constant_embedding C t)))))
                    (d_implies C (d_neg C (d_exists_unique C p))
                               (d_exun_belongs_letter_term C k k t)))) (d_exists_unique C p))
        )
        cpiw_equiv_right_elim. simpl. apply sd_exun_belongs_letter_term.
      apply sd_theory_axiom; bh; nh.
      mp (d_exists_unique C p).
      apply sd_logical_axiom.
      apply sd_if_exun.
      apply sd_theory_axiom; bh; nh.
      simpl. ded. ded.
      mp (d_belongs C (d_letter C k) t).
      eqbire. mp (d_neg C (d_exists_unique C p)).
      apply sd_logical_axiom.
      apply sd_if_not_exun.
      apply sd_theory_axiom; bh; nh. mp (d_neg C (d_exists_unique C p)).
      apply cpiw_syllogism with
          (X:=
             SDCPIW
               C k
               (add_item
                  (DP C)
                  (add_item
                     (DP C) T
                     (d_implies C (d_exists_unique C p) (d_wrong C)))
                  (d_and
                     C
                     (d_implies
                        C (d_exists_unique C p)
                        (d_forall
                           C
                           (d_implies
                              (option C) p
                              (d_exun_belongs_letter_term
                                 (option C) (Some k) None
                                 (d_term_constant_embedding C t)))))
                     (d_implies
                        C
                        (d_neg C (d_exists_unique C p)) (d_exun_belongs_letter_term C k k t))))
          ) (y:= d_exun_belongs_letter_term C k k t).      
      apply cpiw_and_right_elim with
          (X:=
             SDCPIW
               C k
               (add_item
                  (DP C)
                  (add_item
                     (DP C) T
                     (d_implies C (d_exists_unique C p) (d_wrong C)))
                  (d_and
                     C
                     (d_implies
                        C (d_exists_unique C p)
                        (d_forall
                           C
                           (d_implies
                              (option C) p
                              (d_exun_belongs_letter_term
                                 (option C) (Some k) None
                                 (d_term_constant_embedding C t)))))
                     (d_implies
                        C
                        (d_neg C (d_exists_unique C p)) (d_exun_belongs_letter_term C k k t))))
          ) (x:=
               d_implies
                 C (d_exists_unique C p)
                 (d_forall
                    C
                    (d_implies
                       (option C) p
                       (d_exun_belongs_letter_term
                          (option C) (Some k) None
                          (d_term_constant_embedding C t))))
            ). simpl.
      apply sd_theory_axiom; nh. simpl.
      apply cpiw_equiv_right_elim with
          (X:=
             SDCPIW
               C k
               (add_item
                  (DP C)
                  (add_item
                     (DP C) T
                     (d_implies C (d_exists_unique C p) (d_wrong C)))
                  (d_and
                     C
                     (d_implies
                        C (d_exists_unique C p)
                        (d_forall
                           C
                           (d_implies
                              (option C) p
                              (d_exun_belongs_letter_term
                                 (option C) (Some k) None
                                 (d_term_constant_embedding C t)))))
                     (d_implies
                        C
                        (d_neg C (d_exists_unique C p)) (d_exun_belongs_letter_term C k k t))))
          ). simpl. apply sd_exun_belongs_letter_term.
      apply sd_theory_axiom; bh; nh.
    Defined.

    Definition sd_exun_belongs_term_term:
      forall (C:Type) (k:C) (T: DP C -> Type) (s t: DT C),
        second_d_proof
          C k T
          (d_equiv
             C
             (d_belongs C s t)
             (d_exun_belongs_term_term C k s t)                  
          ).
    Proof.
      intros.
      destruct s.
      apply sd_exun_belongs_letter_term.
      apply sd_exun_belongs_prop_term.
    Defined.
    
  End proof_of_the_fd_axiom_about_d_def.

  Section conversions.

    Fixpoint sd_first_d_logical_axiom
             (C:Type) (k:C) (p: DP C) (l:first_d_logical_axiom C k p)
             (T: DP C -> Type) {struct l}:
      second_d_proof C k T p.
    Proof.
      destruct l.
      apply sd_exun_belongs_term_term.
      apply sd_logical_axiom; apply sd_k_ax.
      apply sd_logical_axiom; apply sd_s_ax.
      apply sd_logical_axiom; apply sd_abs_ax.
      apply sd_letter_special_case.
      apply sd_logical_axiom; apply sd_forall_const_ax.
      apply sd_logical_axiom; apply sd_forall_mp_ax.
      apply sd_forall_intro. apply sd_first_d_logical_axiom; assumption.
    Defined.
      
    Fixpoint fd_to_sd (C:Type) (k:C) (T:DP C -> Type) (f: DP C)
             (pr: first_d_proof C k T f) {struct pr}:
      second_d_proof C k T f.
    Proof.
      destruct pr.
      apply sd_theory_axiom; assumption.
      apply sd_first_d_logical_axiom; assumption.
      apply sd_implies_elim with (a:=a).
      apply fd_to_sd; assumption. apply fd_to_sd; assumption.
    Defined.

    Fixpoint fd_second_d_logical_axiom
             (C:Type) (k:C) (p: DP C) (l:second_d_logical_axiom C k p)
             (T: DP C -> Type) {struct l}:
      first_d_proof C k T p.
    Proof.
      destruct l.
      apply fd_def_property_if_exun.
      apply fd_def_property_if_not_exun.      
      apply fd_logical_axiom; apply fd_k_ax.
      apply fd_logical_axiom; apply fd_s_ax.
      apply fd_logical_axiom; apply fd_abs_ax.
      apply fd_special_case.
      apply fd_logical_axiom; apply fd_forall_const_ax.
      apply fd_logical_axiom; apply fd_forall_mp_ax.
      apply fd_forall_intro. apply fd_second_d_logical_axiom; assumption.
    Defined.
    
    Fixpoint sd_to_fd (C:Type) (k:C) (T:DP C -> Type) (f: DP C)
             (pr: second_d_proof C k T f) {struct pr}:
      first_d_proof C k T f.
    Proof.
      destruct pr.
      apply fd_theory_axiom; assumption.
      apply fd_second_d_logical_axiom; assumption.
      apply fd_implies_elim with (a:=a).
      apply sd_to_fd; assumption. apply sd_to_fd; assumption.
    Defined.
      
  End conversions.

  Section conservativity_theorems.

    Definition second_d_conservativity_theorem:
      forall (C : Type) (k : C) (T : Set_Formula C -> Type) (f : Set_Formula C),
        prod
          (hs_proof C T f
           -> second_d_proof C k (sf_to_d_theory C T) (sf_to_d_translation C f)) 
          (second_d_proof C k (sf_to_d_theory C T) (sf_to_d_translation C f)
           -> hs_proof C T f).
    Proof.
      intros.
      split.
      intros.
      apply fd_to_sd. apply first_d_conservativity_theorem; assumption.
      intros. apply first_d_conservativity_theorem with (k:=k). apply sd_to_fd.
      assumption.
    Defined.

    Definition second_d_prop_elimination_of_definitions:
      forall (C : Type) (p : DP C) (k : C) (T : DP C -> Type),
        second_d_proof
          C k T
          (d_equiv C p (sf_to_d_translation C (d_exun_translation_prop C k p))).
    Proof.
      intros.
      apply fd_to_sd.
      apply first_d_prop_elimination_of_definitions.
    Defined.

    Fixpoint fd_conservatively_equal_equal (C:Type) (k:C) (T:DP C -> Type)
             (a b: DT C) (ce: conservatively_equal C k T a b) {struct ce}:
      first_d_proof C k T (d_equal C a b).
    Proof.
      destruct ce.
      apply fd_equality_reflexivity.
      apply fd_equal_iff_overwhelmingly_equal.
      apply overwhelmingly_equal_predicate.
      assumption.
    Defined.
    
    Definition second_d_term_elimination_of_definitions:
      forall (C : Type) (t : DT C) (k : C) (T : DP C -> Type),
        second_d_proof
          C k T
          (d_equal C t (sf_to_d_translation_term C (d_exun_translation_term C k t))).
    Proof.
      intros.
      apply fd_to_sd.
      apply fd_conservatively_equal_equal.
      apply first_d_term_elimination_of_definitions.
    Defined.
      
  End conservativity_theorems.
    
End main.


