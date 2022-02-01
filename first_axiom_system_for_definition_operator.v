Require Import SetDef.add_items_to_theories_and_other_tools.
Require Import SetDef.first_order_set_language.
Require Import SetDef.propositional_implies_wrong_logic.
Require Import SetDef.set_language_with_definition_operator.

(** We introduce two equivalent Hilbert systems for d_prop. they both make the d_prop system 
we've built a conservative extension of first order logic. 
In this file the first one that is defined is designed to make the conservativity theorem 
straightforward to prove. In a further file the second system has more intuitive axioms but 
the conservativity proof is more complicated (in fact we prove that the first and the second 
axiom systems are equivalent). 

We assume there is at least one constant k in 
the context of the language. The axioms will give the intended meaning for the d_def operator:
if p is any prpoperty, then if there is an unique object x such that p(x),
d_def p will denote such an object. in any other case, d_def p denotes k. The idea is to 
ensure that d_def p always denote something even if p is not a legitimate definition. The 
k constant is treated as an error term.
*)

Section A_first_proof_system_for_D_Prop.

  Notation DP:= D_Prop.
  Notation DT:= D_Term.

  Definition d_prop_letter_specify (C:Type) (t:C) (f:DP (option C)): DP C:=
    d_prop_change_of_context
      (option C) f C (option_rect (fun _ : option C => C) (fun x : C => x) t).

  Definition d_term_letter_specify (C:Type) (t:C) (s:DT (option C)): DT C:=
    d_term_change_of_context
      (option C) s C (option_rect (fun _ : option C => C) (fun x : C => x) t).

  
  Notation d_k_formula:=
    (fun (C:Type) (a b:DP C) => d_implies C a (d_implies C b a)).
  Notation d_s_formula:=
    (fun (C:Type) (a b c:DP C) =>
       d_implies
         C
         (d_implies C a (d_implies C b c))
         (d_implies C (d_implies C a b) (d_implies C a c))
    ).
  Notation d_abs_formula:=
    (fun (C:Type) (a:DP C) =>
       d_implies C (d_implies C (d_implies C a (d_wrong C)) (d_wrong C)) a).
  Notation d_letter_special_case_formula:=
    (fun (C:Type) (f:DP (option C)) (t:C) =>
       d_implies C (d_forall C f) (d_prop_letter_specify C t f)).
  Notation d_forall_const_formula:=
    (fun (C:Type) (f:DP C) =>
       d_implies C f (d_forall C (d_prop_constant_embedding C f))).
  Notation d_forall_mp_formula:=
    (fun (C:Type) (f g:DP (option C)) =>
       d_implies
         C
         (d_forall C (d_implies (option C) f g))
         (d_implies C (d_forall C f) (d_forall C g))).

  Inductive first_d_logical_axiom: forall (C:Type), C -> DP C -> Type:=
  |fd_belongs_characterization_ax: forall (C:Type)(k:C) (s t: DT C),
      first_d_logical_axiom 
        C k (d_equiv C (d_belongs C s t) (d_exun_belongs_term_term C k s t))
  |fd_k_ax: forall (C:Type)(k:C) (a b: DP C),
      first_d_logical_axiom C k (d_k_formula C a b)
  |fd_s_ax: forall (C:Type)(k:C) (a b c: DP C),
      first_d_logical_axiom C k (d_s_formula C a b c)
  |fd_abs_ax: forall (C:Type)(k:C) (a:DP C),
      first_d_logical_axiom C k (d_abs_formula C a)      
  |fd_letter_special_case_ax: forall (C:Type)(k:C) (f:DP (option C)) (t:C),
      first_d_logical_axiom C k (d_letter_special_case_formula C f t)
  |fd_forall_const_ax: forall (C:Type)(k:C) (f:DP C),
      first_d_logical_axiom C k (d_forall_const_formula C f)
  |fd_forall_mp_ax: forall (C:Type)(k:C) (f g:DP (option C)),
      first_d_logical_axiom C k (d_forall_mp_formula C f g)
  |fd_universal_closure: forall (C:Type) (k:C) (f:DP (option C)),
      first_d_logical_axiom (option C) (Some k) f ->
      first_d_logical_axiom C k (d_forall C f).

  Fixpoint sf_to_d_la_to_fd_la
           (C:Type) (f:Set_Formula C) (l:logical_axiom C f) (k:C) {struct l}:
    first_d_logical_axiom C k (sf_to_d_translation C f).
  Proof.
    destruct l.
    apply fd_k_ax.
    apply fd_s_ax.
    apply fd_abs_ax.
    simpl.
    assert (sf_to_d_translation C (specify C t a) =
            d_prop_letter_specify C t (sf_to_d_translation (option C) a)) as E1.
    unfold specify.
    unfold d_prop_letter_specify.
    rewrite sf_to_d_coc_eq; reflexivity.
    rewrite E1; apply fd_letter_special_case_ax.
    simpl.
    assert (sf_to_d_translation (option C) (constant_formula_embedding C b) =
            d_prop_constant_embedding C (sf_to_d_translation C b)) as E2.
    unfold constant_formula_embedding.
    unfold d_prop_constant_embedding.
    rewrite sf_to_d_coc_eq; reflexivity.
    rewrite E2; apply fd_forall_const_ax.
    apply fd_forall_mp_ax.
    simpl; apply fd_universal_closure.
    apply sf_to_d_la_to_fd_la; assumption.
  Defined.

  Fixpoint d_to_sf_exun_fd_la_to_la
           (C:Type) (k:C) (p:DP C) (l:first_d_logical_axiom C k p)
           (T:Set_Formula C -> Type) {struct l}:
    hs_proof C T (d_exun_translation_prop C k p).
  Proof.
    destruct l.
    apply sf_exun_translation_belongs_definition_tautology_proof.
    apply hs_logical_axiom; apply K_ax.
    apply hs_logical_axiom; apply S_ax.
    apply hs_logical_axiom; apply ABS_ax.
    simpl.
    assert (d_exun_translation_prop C k (d_prop_letter_specify C t f)=
            specify C t (d_exun_translation_prop (option C) (Some k) f) 
           ) as E1.
    unfold specify.
    unfold d_prop_letter_specify.
    rewrite d_to_sf_exun_coc_prop_eq; reflexivity.
    rewrite E1; apply hs_logical_axiom; apply special_case_ax.
    simpl.
    assert (d_exun_translation_prop (option C) (Some k) (d_prop_constant_embedding C f) =
            constant_formula_embedding C (d_exun_translation_prop C k f)) as E2.
    unfold constant_formula_embedding.
    unfold d_prop_constant_embedding.
    rewrite d_to_sf_exun_coc_prop_eq; reflexivity.
    rewrite E2; apply hs_logical_axiom; apply forall_const_ax.
    simpl; apply hs_logical_axiom; apply forall_mp_ax.
    simpl; apply hs_forall_intro.
    apply d_to_sf_exun_fd_la_to_la; assumption.
  Defined.

  Section definition_of_the_proof_system.

    Variable C:Type.
    Variable k: C.
    Variable T: DP C -> Type.

    Inductive first_d_proof: (DP C -> Type):=
    |fd_theory_axiom: forall p:DP C, T p -> first_d_proof p
    |fd_logical_axiom: forall p:DP C, first_d_logical_axiom C k p -> first_d_proof p
    |fd_implies_elim: forall a b:DP C,
        first_d_proof (d_implies C a b) ->
        first_d_proof a ->
        first_d_proof b.

    Definition FDCPIW: classical_propositional_implies_wrong_system.
    Proof.
      apply (make_cpiw (DP C) (d_implies C) (d_wrong C) (first_d_proof)).
      intros; apply fd_logical_axiom; apply fd_k_ax.
      intros; apply fd_logical_axiom; apply fd_s_ax.
      intros; apply fd_logical_axiom; apply fd_abs_ax.
      apply fd_implies_elim.
    Defined.

    Inductive d_to_sf_exun_theory: Set_Formula C -> Type:=
    |d_to_sf_exun_t_intro: forall p:DP C, T p -> d_to_sf_exun_theory (d_exun_translation_prop C k p).
    
    Inductive sf_to_d_theory (U:Set_Formula C -> Type): DP C -> Type:=
    |sf_to_d_t_intro: forall (f: Set_Formula C),
        U f -> sf_to_d_theory U (sf_to_d_translation C f). 

    Fixpoint d_to_sf_exun_proof (p:DP C) (pr: first_d_proof p) {struct pr}:
      hs_proof C d_to_sf_exun_theory (d_exun_translation_prop C k p).
    Proof.
      destruct pr.
      apply hs_theory_axiom; apply d_to_sf_exun_t_intro; assumption.
      apply d_to_sf_exun_fd_la_to_la; assumption.
      apply d_to_sf_exun_proof in pr1.
      apply d_to_sf_exun_proof in pr2.
      apply hs_implies_elim with (a:=d_exun_translation_prop C k a).
      simpl in pr1.
      assumption.
      assumption.
    Defined.      
    
  End definition_of_the_proof_system.

  Fixpoint sf_to_d_exun_proof
           (C:Type) (k:C) (T: Set_Formula C -> Type)
           (f:Set_Formula C) (pr: hs_proof C T f) {struct pr}:
    first_d_proof C k (sf_to_d_theory C T) (sf_to_d_translation C f).
  Proof.
    destruct pr.
    apply fd_theory_axiom; apply sf_to_d_t_intro; assumption.
    apply fd_logical_axiom; apply sf_to_d_la_to_fd_la; assumption.
    apply sf_to_d_exun_proof with (k:=k) in pr1.
    apply sf_to_d_exun_proof with (k:=k) in pr2.
    apply fd_implies_elim with (a:=sf_to_d_translation C a).
    simpl in pr1.
    assumption.
    assumption.
  Defined.

  Definition first_d_conservativity_theorem:
    forall (C:Type) (k:C) (T:Set_Formula C -> Type) (f:Set_Formula C),
      prod
        (hs_proof C T f -> first_d_proof C k (sf_to_d_theory C T) (sf_to_d_translation C f))
        (first_d_proof C k (sf_to_d_theory C T) (sf_to_d_translation C f) -> hs_proof C T f).
  Proof.
    intros.
    split.
    apply sf_to_d_exun_proof.
    intros.
    apply hs_weakening with (T:= d_to_sf_exun_theory C k (sf_to_d_theory C T)).
    intros.
    destruct X0.
    destruct s.
    rewrite sf_to_d_involution.
    assumption.
    rewrite <- sf_to_d_involution with (k:=k).
    apply d_to_sf_exun_proof.
    assumption.
  Defined.

  Notation add_hyp_d :=
    (fun (C:Type) => add_item (DP C)).
  Notation new_hyp_d :=
    (fun (C:Type) => new_item (DP C)).
  Notation base_hyp_d :=
    (fun (C:Type) => base_item (DP C)).       
  
  Section deduction_and_generalization_for_first_d_proof.

    Variable C:Type.
    Variable k:C.
    Variable T:DP C -> Type.
    Variable h:DP C.

    Fixpoint fd_implies_intro
             (f:DP C) (pr: first_d_proof C k (add_hyp_d C T h) f) {struct pr}:
      first_d_proof C k T (d_implies C h f).
    Proof.
      destruct pr.
      destruct a.
      apply (cpiw_i (FDCPIW C k T)).
      apply (cpiw_k_weakening (FDCPIW C k T)).
      apply fd_theory_axiom; assumption.
      apply (cpiw_k_weakening (FDCPIW C k T)).
      apply fd_logical_axiom; assumption.
      apply fd_implies_elim with (a:= d_implies C h a).
      apply fd_implies_elim with (a:= d_implies C h (d_implies C a b)).
      apply fd_logical_axiom; apply fd_s_ax.
      apply fd_implies_intro; assumption.
      apply fd_implies_intro; assumption.
    Defined.  

    Fixpoint fd_weakening (f:DP C) (pr:first_d_proof C k T f)
             (U:DP C -> Type) (SUBTH: forall x:DP C, T x -> U x) {struct pr}:
      first_d_proof C k U f:=
      match pr in (first_d_proof _ _ _ d) return (first_d_proof C k U d) with
      | fd_theory_axiom _ _ _ p t => fd_theory_axiom C k U p (SUBTH p t)
      | fd_logical_axiom _ _ _ p f0 => fd_logical_axiom C k U p f0
      | fd_implies_elim _ _ _ a b pr1 pr2 =>
        fd_implies_elim C k U a b (fd_weakening (d_implies C a b) pr1 U SUBTH)
                        (fd_weakening a pr2 U SUBTH)
      end.

    Definition fd_weakening_hypothesis (x:DP C) (pr: first_d_proof C k T x):
      first_d_proof C k (add_hyp_d C T h) x:=
      fd_weakening x pr (add_item (DP C) T h)
                   (base_item (DP C) T h).      

    Fixpoint first_d_logical_axiom_context_change
             (A:Type) (ka:A) (p:DP A) (l: first_d_logical_axiom A ka p)
             (B:Type) (env: A -> B){struct l}:
      first_d_logical_axiom B (env ka) (d_prop_change_of_context A p B env).
    Proof.
      destruct l.
      rewrite d_fd_belongs_characterization_coc_eq.
      apply fd_belongs_characterization_ax.
      apply fd_k_ax.
      apply fd_s_ax.
      apply fd_abs_ax.
      simpl.
      assert (
          d_prop_change_of_context C0 (d_prop_letter_specify C0 t f) B env =
          d_prop_letter_specify
            B (env t)
            (d_prop_change_of_context
               (option C0) f (option B)
               (option_rect (fun _ : option C0 => option B)
                            (fun a : C0 => Some (env a)) None))              
        )  
        as E1.
      unfold d_prop_letter_specify.
      repeat rewrite <- d_prop_coc_composition_equality.
      apply d_prop_coc_pointwise_equality.
      intros; destruct x.
      simpl; reflexivity.
      simpl; reflexivity.
      rewrite E1; apply fd_letter_special_case_ax.
      simpl.
      assert (
          d_prop_change_of_context
            (option C0) (d_prop_constant_embedding C0 f) 
            (option B)
            (option_rect (fun _ : option C0 => option B) (fun a : C0 => Some (env a)) None)
          =
          d_prop_constant_embedding B (d_prop_change_of_context C0 f B env)
        ) as E2.
      unfold d_prop_constant_embedding.
      repeat rewrite <- d_prop_coc_composition_equality.
      apply d_prop_coc_pointwise_equality.
      intros; simpl; reflexivity.
      rewrite E2.
      apply fd_forall_const_ax.
      simpl; apply fd_forall_mp_ax.
      simpl. apply fd_universal_closure.
      apply first_d_logical_axiom_context_change
        with (env := (option_rect
                        (fun _ : option C0 => option B) (fun a : C0 => Some (env a)) None))
        in l.
      simpl in l. assumption.
    Defined.                
    
    Fixpoint first_d_proof_context_change (D:Type) (env: C -> D) (p: DP C) 
             (pr: first_d_proof C k T p) {struct pr}:
      first_d_proof D (env k) (d_theory_context_change C T D env)
                    (d_prop_change_of_context C p D env).
    Proof.
      destruct pr.
      apply fd_theory_axiom.
      apply dtcc_intro; assumption.
      apply fd_logical_axiom.
      apply first_d_logical_axiom_context_change; assumption.
      apply fd_implies_elim with (a:=d_prop_change_of_context C a D env).
      apply (first_d_proof_context_change D env) in pr1.
      simpl in pr1. assumption.
      apply (first_d_proof_context_change D env) in pr2.
      simpl in pr2. assumption.
    Defined.
    
    Definition d_theory_constant_embedding: DP (option C) -> Type:=
      d_theory_context_change C T (option C) Some.

    Ltac mp z := apply fd_implies_elim with (a:=z).
    
    Fixpoint fd_forall_intro
             (g:DP (option C))
             (pr: first_d_proof (option C) (Some k) d_theory_constant_embedding g)
             {struct pr}:
      first_d_proof C k T (d_forall C g).
    Proof.
      destruct pr.
      destruct d.
      mp p.
      apply fd_logical_axiom.
      apply fd_forall_const_ax.
      apply fd_theory_axiom; assumption.
      apply fd_logical_axiom; apply fd_universal_closure; assumption.
      apply fd_forall_intro in pr1.
      apply fd_forall_intro in pr2.
      mp (d_forall C a).
      mp (d_forall C (d_implies (option C) a b)).
      apply fd_logical_axiom; apply fd_forall_mp_ax.
      assumption.
      assumption.
    Defined.

    Definition fd_letter_forall_elim: forall (q: DP (option C)) (l:C),
        first_d_proof C k T (d_forall C q) ->
        first_d_proof C k T (d_prop_letter_specify C l q).
    Proof.
      intros.
      mp (d_forall C q).
      apply fd_logical_axiom; apply fd_letter_special_case_ax. assumption.
    Defined.          
    
  End deduction_and_generalization_for_first_d_proof.

  Section core_technical_results.

    Ltac mp z := apply fd_implies_elim with (a:=z).
    Ltac ap := assumption.
    
    Definition first_d_equivalence_reflexivity_proof
               (C:Type) (k:C) (T:DP C -> Type) (p:DP C): 
      first_d_proof C k T (d_equiv C p p):=
      cpiw_equiv_reflexivity (FDCPIW C k T) p.

    Ltac er := apply first_d_equivalence_reflexivity_proof.
    
    Definition first_d_equivalence_symmetry_proof
               (C:Type) (k:C) (T:DP C -> Type) (p q:DP C): 
      first_d_proof C k T (d_equiv C p q) ->
      first_d_proof C k T (d_equiv C q p) :=
      cpiw_equiv_symmetry (FDCPIW C k T) p q.

    Ltac es := apply first_d_equivalence_symmetry_proof.

    Definition first_d_equivalence_transitivity_proof
               (C:Type) (k:C) (T:DP C -> Type) (p q r:DP C): 
      first_d_proof C k T (d_equiv C p q) ->
      first_d_proof C k T (d_equiv C q r) ->
      first_d_proof C k T (d_equiv C p r) :=
      cpiw_equiv_transitivity (FDCPIW C k T) p q r.

    Ltac et z := apply first_d_equivalence_transitivity_proof with (q:=z).

    Definition first_d_equivalence_implies_proof
               (C:Type) (k:C) (T:DP C -> Type) (a a' b b':DP C): 
      first_d_proof C k T (d_equiv C a a') ->
      first_d_proof C k T (d_equiv C b b') ->
      first_d_proof C k T (d_equiv C (d_implies C a b) (d_implies C a' b')) :=
      cpiw_equiv_implies (FDCPIW C k T) a a' b b'.

    Ltac ei := apply first_d_equivalence_implies_proof.
    
    Definition first_d_equivalence_neg_proof
               (C:Type) (k:C) (T:DP C -> Type) (p q:DP C): 
      first_d_proof C k T (d_equiv C p q) ->
      first_d_proof C k T (d_equiv C (d_neg C p) (d_neg C q)).
    Proof.
      intros. ei. ap. er.
    Defined.        

    Ltac en := apply first_d_equivalence_neg_proof.
    
    Definition first_d_equivalence_and_proof
               (C:Type) (k:C) (T:DP C -> Type) (a a' b b':DP C): 
      first_d_proof C k T (d_equiv C a a') ->
      first_d_proof C k T (d_equiv C b b') ->
      first_d_proof C k T (d_equiv C (d_and C a b) (d_and C a' b')).
    Proof.
      intros. ei. ei. ap. en. ap. er.
    Defined.
    
    Ltac ea := apply first_d_equivalence_and_proof.

    Definition first_d_equivalence_or_proof
               (C:Type) (k:C) (T:DP C -> Type) (a a' b b':DP C): 
      first_d_proof C k T (d_equiv C a a') ->
      first_d_proof C k T (d_equiv C b b') ->
      first_d_proof C k T (d_equiv C (d_or C a b) (d_or C a' b')).
    Proof.
      intros. ei. en. ap. ap.
    Defined.
    
    Ltac eo := apply first_d_equivalence_or_proof.

    Definition first_d_equivalence_equiv_proof
               (C:Type) (k:C) (T:DP C -> Type) (a a' b b':DP C): 
      first_d_proof C k T (d_equiv C a a') ->
      first_d_proof C k T (d_equiv C b b') ->
      first_d_proof C k T (d_equiv C (d_equiv C a b) (d_equiv C a' b')).
    Proof.
      intros. ea. ei. ap. ap. ei. ap. ap.        
    Defined.
    
    Ltac ee := apply first_d_equivalence_equiv_proof.
    
    Definition first_d_equivalence_forall_proof:
      forall (C:Type) (k:C) (T:DP C -> Type) (a b:DP (option C)),
        first_d_proof (option C) (Some k) (d_theory_constant_embedding C T)
                      (d_equiv (option C) a b) -> 
        first_d_proof C k T (d_equiv C (d_forall C a) (d_forall C b)).
    Proof.
      intros.
      apply (cpiw_equiv_intro (FDCPIW C k T)).
      simpl.
      mp (d_forall C (d_implies (option C) a b)).
      apply fd_logical_axiom; apply fd_forall_mp_ax.
      apply fd_forall_intro.
      apply (cpiw_equiv_left_elim
               (FDCPIW (option C) (Some k) (d_theory_constant_embedding C T))).              
      apply X.
      mp (d_forall C (d_implies (option C) b a)).
      apply fd_logical_axiom; apply fd_forall_mp_ax.
      apply fd_forall_intro.
      apply (cpiw_equiv_right_elim
               (FDCPIW (option C) (Some k) (d_theory_constant_embedding C T))).
      apply X.
    Defined.      

    Ltac ef := apply first_d_equivalence_forall_proof.
    
    Definition first_d_equivalence_exists_proof:
      forall (C:Type) (k:C) (T:DP C -> Type) (a b:DP (option C)),
        first_d_proof (option C) (Some k) (d_theory_constant_embedding C T)
                      (d_equiv (option C) a b) -> 
        first_d_proof C k T (d_equiv C (d_exists C a) (d_exists C b)).
    Proof.
      intros. ei. ef. ei. ap. er. er.
    Defined.

    Ltac eex := apply first_d_equivalence_exists_proof.

    Definition first_d_equivalence_unique_proof:
      forall (C:Type) (k:C) (T:DP C -> Type) (a b:DP (option C)),
        first_d_proof (option C) (Some k) (d_theory_constant_embedding C T)
                      (d_equiv (option C) a b) -> 
        first_d_proof C k T (d_equiv C (d_unique C a) (d_unique C b)).
    Proof.
      intros. ef. ef. ei. rewrite <- d_equiv_coc_eq.
      unfold d_theory_constant_embedding. rewrite d_prop_coc_composition_equality.
      rewrite d_prop_coc_pointwise_equality with (env2:= Some).
      apply first_d_proof_context_change.
      rewrite d_prop_coc_identity_equality. ap.
      intros.
      destruct x. simpl; reflexivity. simpl; reflexivity.
      ei.
      rewrite <- d_equiv_coc_eq.
      apply fd_weakening with
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
      apply first_d_proof_context_change.
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

    Ltac eu := apply first_d_equivalence_unique_proof.

    Definition fd_forall_letter_elim:
      forall (C:Type) (T: DP C -> Type) (f: DP (option C)) (k l:C),
        first_d_proof C k T (d_forall C f) ->
        first_d_proof C k T (d_prop_letter_specify C l f).
    Proof.
      intros.
      mp (d_forall C f).
      apply fd_logical_axiom. apply fd_letter_special_case_ax. ap.
    Defined.        

    Definition fd_equal_elim_belongs_letter:
      forall (C:Type) (T: DP C -> Type) (s t:DT C) (k x:C),
        first_d_proof C k T (d_equal C s t) ->
        prod
          (first_d_proof
             C k T 
             (d_equiv C (d_belongs C s (d_letter C x)) (d_belongs C t (d_letter C x))))
          (first_d_proof
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
      apply (cpiw_and_left_elim (FDCPIW C k T)) in X.
      simpl in X.
      apply fd_forall_letter_elim with (l:=x) in X.
      unfold d_prop_letter_specify in X.
      rewrite d_equiv_coc_eq in X.
      repeat rewrite d_belongs_coc_eq in X.
      repeat rewrite E in X.
      simpl in X.
      ap.
      apply (cpiw_and_right_elim (FDCPIW C k T)) in X.
      simpl in X.
      apply fd_forall_letter_elim with (l:=x) in X.
      unfold d_prop_letter_specify in X.
      rewrite d_equiv_coc_eq in X.
      repeat rewrite d_belongs_coc_eq in X.
      repeat rewrite E in X.
      simpl in X.
      ap.
    Defined.

    Ltac ele := apply fd_equal_elim_belongs_letter.
    
    Definition first_d_equivalence_exists_unique_proof:
      forall (C:Type) (k:C) (T:DP C -> Type) (a b:DP (option C)),
        first_d_proof (option C) (Some k) (d_theory_constant_embedding C T)
                      (d_equiv (option C) a b) -> 
        first_d_proof C k T (d_equiv C (d_exists_unique C a) (d_exists_unique C b)).
    Proof.
      intros. ea. eex. ap. eu. ap.
    Defined.
    
    Ltac eeu := apply first_d_equivalence_exists_unique_proof.

    Definition fd_forall_inverse_intro:
      forall (C:Type) (k:C) (T:DP C-> Type) (f:DP (option C)),
        first_d_proof C k T (d_forall C f) ->
        first_d_proof (option C) (Some k) (d_theory_constant_embedding C T) f.
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
      simpl.
      apply fd_logical_axiom. apply fd_letter_special_case_ax.
      apply first_d_proof_context_change. ap.
    Defined.

    Definition fd_exists_elim:
      forall (C:Type) (k:C) (T:DP C-> Type) (f:DP (option C)) (g:DP C),
        first_d_proof C k T (d_exists C f) ->
        first_d_proof
          (option C) (Some k)
          (add_hyp_d
             (option C)
             (d_theory_constant_embedding C T) f) (d_prop_constant_embedding C g) ->
        first_d_proof C k T g.
    Proof.
      intros.
      mp (d_implies C (d_implies C g (d_wrong C)) (d_wrong C)).
      apply fd_logical_axiom. apply fd_abs_ax.
      apply cpiw_syllogism with (X:= FDCPIW C k T) (y:= d_forall C (d_neg (option C) f)).
      simpl. apply fd_implies_intro.
      apply fd_forall_intro.
      unfold d_neg.
      apply cpiw_syllogism with
          (X:= FDCPIW
                 (option C) (Some k)
                 (d_theory_constant_embedding
                    C
                    (add_item
                       (DP C) T (d_implies C g (d_wrong C)))))
          (y:= d_prop_constant_embedding C g).
      simpl.
      apply fd_weakening with (T:=d_theory_constant_embedding C T).
      apply fd_implies_intro.
      assumption.
      intros.
      destruct X1.
      apply dtcc_intro. apply base_hyp_d. assumption.
      simpl.
      assert
        (
          d_implies (option C) (d_prop_constant_embedding C g) (d_wrong (option C))
          =
          d_prop_constant_embedding C (d_implies C g (d_wrong C))) as E.
      unfold d_prop_constant_embedding; simpl; reflexivity.
      rewrite E.
      apply fd_theory_axiom.
      apply dtcc_intro. apply new_hyp_d.
      simpl. apply X.
    Defined.
    
    Definition fd_equality_reflexivity:
      forall (C:Type) (k:C) (T: DP C -> Type) (x:DT C),
        first_d_proof C k T (d_equal C x x).
    Proof.
      intros.
      apply cpiw_and_intro with (X:= FDCPIW C k T).
      simpl; apply fd_forall_intro; er.
      simpl; apply fd_forall_intro; er.
    Defined.


    Ltac fdrefl:= apply fd_equality_reflexivity. 
    
    Definition fd_equality_symmetry:
      forall (C:Type) (k:C) (T: DP C -> Type) (x y:DT C),
        first_d_proof C k T (d_equal C x y) -> first_d_proof C k T (d_equal C y x).
    Proof.
      intros.
      apply cpiw_and_intro with (X:= FDCPIW C k T). simpl.
      apply fd_forall_intro. es.
      apply fd_forall_inverse_intro.
      apply (cpiw_and_left_elim (FDCPIW C k T)) in X.
      assumption.
      apply fd_forall_intro. es.
      apply fd_forall_inverse_intro.
      apply (cpiw_and_right_elim (FDCPIW C k T)) in X.
      assumption.    
    Defined.

    Ltac fdsym:= apply fd_equality_symmetry. 

    Definition fd_equality_transitivity:
      forall (C:Type) (k:C) (T: DP C -> Type) (x y z:DT C),
        first_d_proof C k T (d_equal C x y) ->
        first_d_proof C k T (d_equal C y z) ->
        first_d_proof C k T (d_equal C x z).
    Proof.
      intros.
      apply cpiw_and_intro with (X:= FDCPIW C k T). simpl.
      apply fd_forall_intro.
      et (d_belongs (option C) (d_term_constant_embedding C y) (d_letter (option C) None)).
      apply fd_forall_inverse_intro.
      apply (cpiw_and_left_elim (FDCPIW C k T)) in X.
      assumption.
      apply fd_forall_inverse_intro.
      apply (cpiw_and_left_elim (FDCPIW C k T)) in X0.
      assumption.
      apply fd_forall_intro.
      et (d_belongs (option C) (d_letter (option C) None) (d_term_constant_embedding C y)).
      apply fd_forall_inverse_intro.
      apply (cpiw_and_right_elim (FDCPIW C k T)) in X.
      assumption.
      apply fd_forall_inverse_intro.
      apply (cpiw_and_right_elim (FDCPIW C k T)) in X0.
      assumption.
    Defined.
    
    Ltac fdtrans b:= apply fd_equality_transitivity with (y:=b).               
    
    Definition first_d_equivalence_exun_belongs_letter_prop_proof0:
      forall (C:Type) (k x y:C) (T:DP C -> Type) (a b:DP (option C)),
        first_d_proof C k T (d_equal C (d_letter C x) (d_letter C y)) ->
        first_d_proof (option C) (Some k) (d_theory_constant_embedding C T)
                      (d_equiv (option C) a b) -> 
        first_d_proof
          C k T
          (d_equiv C
                   (d_exun_belongs_letter_prop C k x a)
                   (d_exun_belongs_letter_prop C k y b)).
    Proof.
      intros. ea. ei. eeu. ap.
      assert
        (first_d_proof C k T (d_equal C (d_letter C x) (d_letter C y))) as Xc.
      ap. apply (cpiw_and_left_elim (FDCPIW C k T)) in X. simpl in X.
      ef. ei. ap. ele. apply first_d_proof_context_change with (D:= option C) (env := Some)
        in Xc. apply Xc. ei. en. eeu. ap. ele. ap.        
    Defined.

    Ltac edxlp0 := apply first_d_equivalence_exun_belongs_letter_prop_proof0.        

    Definition first_d_equivalence_exun_belongs_letter_term_proof0:
      forall (C:Type) (k x y:C) (T:DP C -> Type) (a b:DT C),
        first_d_proof C k T (d_equal C (d_letter C x) (d_letter C y)) ->
        first_d_proof C k T (d_equal C a b) -> 
        first_d_proof
          C k T
          (d_equiv C
                   (d_exun_belongs_letter_term C k x a)
                   (d_exun_belongs_letter_term C k y b)).
    Proof.
      intros.
      destruct a. destruct b.
      simpl. et (d_belongs C (d_letter C x) (d_letter C c0)).
      ele; ap. ele; ap.
      simpl.
      et (d_belongs C (d_letter C y) (d_letter C c)). ele; ap.
      et (d_belongs C (d_letter C y) (d_def C d)).
      ele; ap.
      apply fd_logical_axiom.
      apply fd_belongs_characterization_ax.
      destruct b.
      simpl.
      et (d_exun_belongs_letter_prop C k y d).
      edxlp0. ap. er.
      et (d_belongs C (d_letter C y) (d_def C d)). es.
      apply fd_logical_axiom.
      apply fd_belongs_characterization_ax. ele; ap.
      simpl.
      et (d_belongs C (d_letter C x) (d_def C d)). es.
      apply fd_logical_axiom.
      apply fd_belongs_characterization_ax.
      et (d_belongs C (d_letter C x) (d_def C d0)). ele; ap.
      et (d_exun_belongs_letter_prop C k x d0). 
      apply fd_logical_axiom.
      apply fd_belongs_characterization_ax.
      edxlp0. ap. er.
    Defined.

    Ltac edxlt0 := apply first_d_equivalence_exun_belongs_letter_term_proof0.        

    Definition first_d_equivalence_exun_belongs_prop_term_proof0:
      forall (C:Type) (k:C) (T:DP C -> Type) (a b:DP (option C)) (s t:DT C),
        first_d_proof (option C) (Some k) (d_theory_constant_embedding C T)
                      (d_equiv (option C) a b) ->
        first_d_proof C k T (d_equal C s t) ->
        first_d_proof
          C k T
          (d_equiv C
                   (d_exun_belongs_prop_term C k a s)
                   (d_exun_belongs_prop_term C k b t)).
    Proof.
      intros. unfold d_exun_belongs_prop_term.
      ea. ei. eeu. ap. ef. ei. ap. edxlt0. fdrefl.
      apply first_d_proof_context_change with (D:= option C) (env := Some) in X0.
      rewrite d_equal_coc_eq in X0. ap.
      ei. en. eeu. ap. edxlt0. fdrefl. ap.
    Defined.
    
    Ltac edxpt0:= apply first_d_equivalence_exun_belongs_prop_term_proof0.      

    Definition first_d_equivalence_exun_belongs_letter_prop_proof:
      forall (C:Type) (k x:C) (T:DP C -> Type) (a b:DP (option C)),
        first_d_proof (option C) (Some k) (d_theory_constant_embedding C T)
                      (d_equiv (option C) a b) -> 
        first_d_proof
          C k T
          (d_equiv C
                   (d_belongs C (d_letter C x) (d_def C a))
                   (d_belongs C (d_letter C x) (d_def C b))).
    Proof.
      intros. et (d_exun_belongs_letter_prop C k x a).
      apply fd_logical_axiom; apply fd_belongs_characterization_ax. 
      et (d_exun_belongs_letter_prop C k x b).
      edxlp0. fdrefl. ap. es.
      apply fd_logical_axiom; apply fd_belongs_characterization_ax. 
    Defined.
    
    Ltac edxlp := apply first_d_equivalence_exun_belongs_letter_prop_proof.        

    Definition first_d_equivalence_exun_belongs_prop_term_proof:
      forall (C:Type) (k:C) (T:DP C -> Type) (a b:DP (option C)) (t:DT C),
        first_d_proof (option C) (Some k) (d_theory_constant_embedding C T)
                      (d_equiv (option C) a b) -> 
        first_d_proof
          C k T
          (d_equiv C
                   (d_belongs C (d_def C a) t)
                   (d_belongs C (d_def C b) t)).                    
    Proof.
      intros.
      et (d_exun_belongs_prop_term C k a t).
      apply fd_logical_axiom; apply fd_belongs_characterization_ax. 
      et (d_exun_belongs_prop_term C k b t).
      edxpt0. ap. fdrefl. es.        
      apply fd_logical_axiom; apply fd_belongs_characterization_ax.         
    Defined.

    Ltac edxpt:= apply first_d_equivalence_exun_belongs_prop_term_proof.

    Definition first_d_equivalence_exun_belongs_prop_term_proof_equality:
      forall (C:Type) (k:C) (T:DP C -> Type) (a b:DP (option C)),
        first_d_proof (option C) (Some k) (d_theory_constant_embedding C T)
                      (d_equiv (option C) a b) ->
        first_d_proof C k T (d_equal C (d_def C a) (d_def C b)).
    Proof.
      intros.
      apply (cpiw_and_intro (FDCPIW C k T)).
      simpl.
      apply fd_forall_intro. 
      unfold d_term_constant_embedding.
      simpl.
      edxpt.
      apply first_d_proof_context_change with
          (D:= option (option C))
          (env := option_rect
                    (fun _:option C => option (option C))
                    (fun v:C => Some (Some v))
                    None
          )
        in X.
      apply fd_weakening with
          (T:= d_theory_context_change 
                 (option C) (d_theory_constant_embedding C T)
                 (option (option C))
                 (option_rect
                    (fun _ : option C => option (option C)) (fun v : C => Some (Some v))
                    None)).
      ap.
      intros.
      destruct X0.
      destruct d.
      assert (
          d_prop_change_of_context
            (option C) (d_prop_change_of_context C p (option C) Some)
            (option (option C))
            (option_rect
               (fun _ : option C => option (option C)) (fun v : C => Some (Some v)) None)
          =
          d_prop_constant_embedding (option C) (d_prop_constant_embedding C p)
        ) as E1.
      unfold d_prop_constant_embedding.
      repeat rewrite <- d_prop_coc_composition_equality.
      apply d_prop_coc_pointwise_equality.
      intros. simpl; reflexivity. rewrite E1.
      repeat apply dtcc_intro; assumption.        
      simpl.
      apply fd_forall_intro. 
      unfold d_term_constant_embedding.
      simpl.
      edxlp.
      apply first_d_proof_context_change with
          (D:= option (option C))
          (env := option_rect
                    (fun _:option C => option (option C))
                    (fun v:C => Some (Some v))
                    None
          )
        in X.
      apply fd_weakening with
          (T:= d_theory_context_change 
                 (option C) (d_theory_constant_embedding C T)
                 (option (option C))
                 (option_rect
                    (fun _ : option C => option (option C)) (fun v : C => Some (Some v))
                    None)).
      ap.
      intros.
      destruct X0.
      destruct d.
      assert (
          d_prop_change_of_context
            (option C) (d_prop_change_of_context C p (option C) Some)
            (option (option C))
            (option_rect
               (fun _ : option C => option (option C)) (fun v : C => Some (Some v)) None)
          =
          d_prop_constant_embedding (option C) (d_prop_constant_embedding C p)
        ) as E2.
      unfold d_prop_constant_embedding.
      repeat rewrite <- d_prop_coc_composition_equality.
      apply d_prop_coc_pointwise_equality.
      intros. simpl; reflexivity. rewrite E2.
      repeat apply dtcc_intro; assumption.
    Defined.

    Ltac peq := apply first_d_equivalence_exun_belongs_prop_term_proof_equality.
    
    Inductive conservatively_equal (C:Type) (k:C) (T:DP C -> Type): DT C -> DT C -> Type:=
    |ce_letter: forall x:C, conservatively_equal C k T (d_letter C x) (d_letter C x)
    |ce_predicate: forall (p q: DP (option C)),
        first_d_proof (option C) (Some k) (d_theory_constant_embedding C T)
                      (d_equiv (option C) p q) ->
        conservatively_equal C k T (d_def C p) (d_def C q).


    
    Fixpoint first_d_prop_elimination_of_definitions
             (C:Type) (p:DP C) (k:C) (T: DP C -> Type) {struct p}:
      first_d_proof
        C k T
        (d_equiv C p (sf_to_d_translation C (d_exun_translation_prop C k p)))
    with first_d_term_elimination_of_definitions
           (C:Type) (t:DT C) (k:C) (T: DP C -> Type) {struct t}:
           conservatively_equal
             C k T t
             (sf_to_d_translation_term C (d_exun_translation_term C k t)).
    Proof.
      destruct p.      
      simpl.
      rewrite d_exun_belongs_term_term_sftd_eq.      
      destruct first_d_term_elimination_of_definitions with (T:=T) (k:=k) (t:=d).
      destruct first_d_term_elimination_of_definitions with (T:=T) (k:=k) (t:=d0).
      er.  
      simpl.
      et (d_exun_belongs_letter_prop C k x p).
      apply fd_logical_axiom; apply fd_belongs_characterization_ax.
      edxlp0. fdrefl. ap.
      destruct first_d_term_elimination_of_definitions with (T:=T) (k:=k) (t:=d0).
      simpl.
      et (d_exun_belongs_prop_term C k p (d_letter C x)).
      apply fd_logical_axiom; apply fd_belongs_characterization_ax.
      edxpt0. ap. fdrefl.
      simpl.
      et (d_exun_belongs_prop_term C k p (d_def C p0)).
      apply fd_logical_axiom; apply fd_belongs_characterization_ax.
      et (d_exun_belongs_prop_term C k p (d_def C q0)).
      edxpt0. er. peq. ap. edxpt0. ap. fdrefl.
      simpl; er.
      simpl; ei. apply first_d_prop_elimination_of_definitions.
      apply first_d_prop_elimination_of_definitions.
      simpl.
      ef.
      apply first_d_prop_elimination_of_definitions.
      destruct t.
      simpl. apply ce_letter.
      simpl.
      apply ce_predicate.
      apply first_d_prop_elimination_of_definitions.
    Defined.              

    Definition strongly_equal (C:Type) (k:C) (T:DP C -> Type) (s t:DT C):=
      prod
        (forall u:DT C, first_d_proof C k T (d_equiv C (d_belongs C s u) (d_belongs C t u)))
        (forall u:DT C, first_d_proof C k T (d_equiv C (d_belongs C u s) (d_belongs C u t))).

    Definition overwhelmingly_equal (C:Type) (k:C) (T:DP C -> Type) (s t:DT C):=
      forall (D:Type) (env: C -> D),
        strongly_equal
          D (env k) (d_theory_context_change C T D env)
          (d_term_change_of_context C s D env)
          (d_term_change_of_context C t D env).

    Definition oe_to_se: forall (C:Type) (k:C) (T:DP C -> Type) (s t:DT C),
        overwhelmingly_equal C k T s t -> strongly_equal C k T s t.
    Proof.
      intros.
      destruct X with (D:=C) (env := fun x:C => x).
      split.
      intros.
      rewrite <- d_prop_coc_identity_equality.
      rewrite d_equiv_coc_eq.
      repeat rewrite d_belongs_coc_eq.
      apply fd_weakening with (T:= d_theory_context_change C T C (fun x:C => x)).
      apply f. intros. destruct X0. rewrite d_prop_coc_identity_equality; ap.
      intros.
      rewrite <- d_prop_coc_identity_equality.
      rewrite d_equiv_coc_eq.
      repeat rewrite d_belongs_coc_eq.
      apply fd_weakening with (T:= d_theory_context_change C T C (fun x:C => x)).
      apply f0. intros. destruct X0. rewrite d_prop_coc_identity_equality; ap.
    Defined.

    Definition oe_composition:
      forall (C:Type) (k:C) (T:DP C -> Type) (s t:DT C) (D:Type) (env: C -> D),
        overwhelmingly_equal C k T s t ->
        overwhelmingly_equal D (env k) (d_theory_context_change C T D env)
                             (d_term_change_of_context C s D env)
                             (d_term_change_of_context C t D env).
    Proof.
      intros.
      unfold overwhelmingly_equal.      
      intros.
      repeat rewrite <- d_term_coc_composition_equality.      
      destruct X with (D:=D0) (env := fun v: C => env0 (env v)).
      split.
      intros.
      apply fd_weakening with (T:= d_theory_context_change C T D0 (fun v:C => env0 (env v))).
      apply f.
      intros.  destruct X0. rewrite d_prop_coc_composition_equality.  repeat apply dtcc_intro.
      ap.
      intros.
      apply fd_weakening with (T:= d_theory_context_change C T D0 (fun v:C => env0 (env v))).
      apply f0.
      intros.  destruct X0. rewrite d_prop_coc_composition_equality.  repeat apply dtcc_intro.
      ap.
    Defined.    
    
    Definition strongly_equal_predicate:
      forall (C:Type) (k:C) (T: DP C -> Type) (a b: DP (option C)),
        first_d_proof (option C) (Some k) (d_theory_constant_embedding C T)
                      (d_equiv (option C) a b) -> 
        strongly_equal C k T (d_def C a) (d_def C b).
    Proof.
      intros.
      split.
      intros. simpl.
      edxpt. ap.
      intros.
      et (d_exun_belongs_term_term C k u (d_def C a)).
      apply fd_logical_axiom; apply fd_belongs_characterization_ax.
      et (d_exun_belongs_term_term C k u (d_def C b)).      
      destruct u.
      simpl.
      edxlp0. fdrefl. ap.
      simpl.
      edxpt0. er. peq. ap. es.
      apply fd_logical_axiom; apply fd_belongs_characterization_ax.
    Defined.
    
    Definition overwhelmingly_equal_predicate:
      forall (C:Type) (k:C) (T: DP C -> Type) (a b: DP (option C)),
        first_d_proof (option C) (Some k) (d_theory_constant_embedding C T)
                      (d_equiv (option C) a b) -> 
        overwhelmingly_equal C k T (d_def C a) (d_def C b).
    Proof.
      intros.
      unfold overwhelmingly_equal.
      intros.
      simpl.
      apply strongly_equal_predicate.
      rewrite <- d_equiv_coc_eq.
      apply fd_weakening with
          (T:= d_theory_context_change
                 (option C)
                 (d_theory_constant_embedding C T)
                 (option D)
                 (option_rect
                    (fun _ : option C => option D) (fun a0 : C => Some (env a0)) None)
          ).
      assert (Some (env k) =
              (option_rect
                 (fun _ : option C => option D) (fun a0 : C => Some (env a0)) None)
                (Some k)
             ) as E.
      simpl; reflexivity.
      rewrite E.             
      apply first_d_proof_context_change. ap.
      intros.
      destruct X0.
      destruct d.
      rewrite <- d_prop_coc_composition_equality.
      rewrite d_prop_coc_pointwise_equality with
          (env2 := fun v:C => Some (env v)).
      rewrite d_prop_coc_composition_equality.
      repeat apply dtcc_intro; ap.
      intros; simpl; reflexivity.
    Defined.
    
    Definition strongly_equal_letter:
      forall (C:Type) (k:C) (T: DP C -> Type) (x y: C),
        first_d_proof C k T (d_equal C (d_letter C x) (d_letter C y)) ->
        strongly_equal C k T (d_letter C x) (d_letter C y).
    Proof.
      intros.
      split.
      intros.
      et (d_exun_belongs_letter_term C k x u).
      apply fd_logical_axiom; apply fd_belongs_characterization_ax.
      et (d_exun_belongs_letter_term C k y u).            
      edxlt0. ap. fdrefl. es.
      apply fd_logical_axiom; apply fd_belongs_characterization_ax.
      intros.
      et (d_exun_belongs_term_term C k u (d_letter C x)).
      apply fd_logical_axiom; apply fd_belongs_characterization_ax.
      et (d_exun_belongs_term_term C k u (d_letter C y)).
      destruct u.
      simpl. ele. ap.
      simpl.      
      edxpt0. er. ap. es.
      apply fd_logical_axiom; apply fd_belongs_characterization_ax.
    Defined.
    
    
    Fixpoint fd_oe_transfer_prop
             (C:Type) (p:DP C)
             (D:Type)
             (k:D) (T:DP D -> Type) 
             (env1 env2: C -> DT D)
             (eqpr: forall x:C, overwhelmingly_equal D k T (env1 x) (env2 x))
             {struct p}:
      first_d_proof
        D k T (d_equiv D (d_prop_substitution C p D env1) (d_prop_substitution C p D env2))
    with
    fd_oe_transfer_term
      (C:Type) (t:DT C)
      (D:Type)
      (k:D) (T:DP D -> Type) 
      (env1 env2: C -> DT D)
      (eqpr: forall x:C, overwhelmingly_equal D k T (env1 x) (env2 x))
      {struct t}:
      overwhelmingly_equal
        D k T
        (d_term_substitution C t D env1) (d_term_substitution C t D env2).
    Proof.
      destruct p.
      simpl.
      et (d_belongs D (d_term_substitution C d D env1) (d_term_substitution C d0 D env2)).
      apply oe_to_se. apply fd_oe_transfer_term; ap.
      apply oe_to_se. apply fd_oe_transfer_term; ap.
      simpl; er.
      simpl. ei. apply fd_oe_transfer_prop; ap. apply fd_oe_transfer_prop; ap.
      simpl. ef. apply fd_oe_transfer_prop.
      intros. destruct x.      
      simpl. split. intros.
      unfold d_term_constant_embedding. apply oe_composition. apply eqpr.
      intros.
      simpl.
      unfold d_term_constant_embedding. apply oe_composition. apply eqpr.
      simpl. split.
      intros; er. intros; er.
      destruct t.
      simpl. apply eqpr.
      simpl.
      apply overwhelmingly_equal_predicate.
      apply fd_oe_transfer_prop. 
      intros. destruct x. simpl.
      apply oe_composition. apply eqpr.
      simpl. split. intros; er. intros; er.
    Defined.   

    Definition fd_term_letter_equality_if_not_exun:
      forall (C:Type) (k x:C) (T: DP C -> Type) (q: DP (option C)),
        first_d_proof C k T (d_neg C (d_exists_unique C q)) ->
        prod (first_d_proof
                C k T
                (d_equiv C
                         (d_belongs C (d_def C q) (d_letter C x))
                         (d_belongs C (d_letter C k) (d_letter C x))))
             (first_d_proof
                C k T
                (d_equiv C
                         (d_belongs C  (d_letter C x) (d_def C q))
                         (d_belongs C  (d_letter C x) (d_letter C k)))).    
    Proof.
      intros.
      split.
      et (d_exun_belongs_term_term C k (d_def C q) (d_letter C x)).
      apply fd_logical_axiom; apply fd_belongs_characterization_ax.
      simpl.
      unfold d_exun_belongs_prop_term.
      apply cpiw_negative_case_in_case_definition
        with (X:= FDCPIW C k T).
      simpl. ap.
      et (d_exun_belongs_letter_prop C k x q).                                     
      apply fd_logical_axiom; apply fd_belongs_characterization_ax.
      unfold d_exun_belongs_letter_prop.
      apply cpiw_negative_case_in_case_definition
        with (X:= FDCPIW C k T).
      simpl. ap.
    Defined.

    Definition fd_term_equality_if_not_exun:
      forall (C:Type) (k:C) (T: DP C -> Type) (q: DP (option C)),
        first_d_proof C k T (d_neg C (d_exists_unique C q)) ->
        first_d_proof C k T (d_equal C (d_def C q) (d_letter C k)).
    Proof.
      intros.
      apply first_d_proof_context_change with (D:=option C) (env:=Some) in X.
      rewrite d_neg_coc_eq in X.
      rewrite d_exists_unique_coc_eq in X.
      apply cpiw_and_intro with (X:= FDCPIW C k T).
      apply fd_forall_intro.
      apply fd_term_letter_equality_if_not_exun.
      apply X.
      apply fd_forall_intro.
      apply fd_term_letter_equality_if_not_exun.
      apply X.
    Defined.          
    
    Definition fd_term_overwhelming_equality_if_not_exun:
      forall (C:Type) (k:C) (T: DP C -> Type) (q: DP (option C)),
        first_d_proof C k T (d_neg C (d_exists_unique C q)) ->
        overwhelmingly_equal C k T (d_def C q) (d_letter C k).
    Proof.
      intros.
      unfold overwhelmingly_equal.
      intros.
      apply first_d_proof_context_change with (D:=D) (env:=env) in X.
      rewrite d_neg_coc_eq in X.
      rewrite d_exists_unique_coc_eq in X.
      split. intros.
      et (d_exun_belongs_term_term D (env k)
                                   (d_term_change_of_context C (d_def C q) D env) u).
      apply fd_logical_axiom; apply fd_belongs_characterization_ax.
      et (d_exun_belongs_letter_term D (env k) (env k) u).
      simpl.
      unfold d_exun_belongs_prop_term.
      unfold extend_map_to_bound_variables in X. 
      apply cpiw_negative_case_in_case_definition
        with (X:= FDCPIW D (env k) (d_theory_context_change C T D env)).
      simpl. ap.
      es; apply fd_logical_axiom; apply fd_belongs_characterization_ax.
      intros.
      et (d_exun_belongs_term_term D (env k) 
                                   u (d_term_change_of_context C (d_def C q) D env)).
      apply fd_logical_axiom; apply fd_belongs_characterization_ax.
      et (d_exun_belongs_term_term D (env k) u (d_letter D (env k))).      
      destruct u.
      simpl. unfold d_exun_belongs_letter_prop.
      apply cpiw_negative_case_in_case_definition
        with (X:= FDCPIW D (env k) (d_theory_context_change C T D env)).
      unfold extend_map_to_bound_variables in X. simpl. ap.
      simpl.
      edxpt0. er.
      apply fd_term_equality_if_not_exun. ap.
      es; apply fd_logical_axiom; apply fd_belongs_characterization_ax.
    Defined.

    Definition fd_letter_unique_elim:
      forall (C:Type) (k x y:C) (T: DP C -> Type) (q: DP (option C)),
        first_d_proof C k T (d_unique C q) ->
        first_d_proof C k T (d_prop_letter_specify C x q) ->
        first_d_proof C k T (d_prop_letter_specify C y q) ->
        first_d_proof C k T (d_equal C (d_letter C x) (d_letter C y)).
    Proof.
      intros.
      unfold d_unique in X.
      apply fd_implies_elim with (a:= d_prop_letter_specify C y q).
      apply fd_implies_elim with (a:= d_prop_letter_specify C x q).  
      assert (
          d_implies
            C (d_prop_letter_specify C x q)            
            (d_implies
               C (d_prop_letter_specify C y q)
               (d_equal C (d_letter C x) (d_letter C y)))
          =
          d_prop_letter_specify
            C x
            (d_prop_letter_specify
               (option C)
               (Some y)
               (
                 d_implies
                   (option (option C))
                   (d_prop_change_of_context
                      (option C) q (option (option C))
                      (option_rect (fun _ : option C => option (option C))
                                   (fun a : C => Some (Some a)) (Some None)))
                   (d_implies
                      (option (option C))
                      (d_prop_change_of_context
                         (option C) q (option (option C))
                         (option_rect
                            (fun _ : option C => option (option C))
                            (fun a : C => Some (Some a)) None))
                      (d_equal (option (option C)) (d_letter (option (option C)) (Some None))
                               (d_letter (option (option C)) None))))
            )                   
        ) as E1. unfold d_prop_letter_specify.
      repeat rewrite d_implies_coc_eq.
      apply f_equal2.
      repeat rewrite <- d_prop_coc_composition_equality.
      apply d_prop_coc_pointwise_equality.
      intros.
      destruct x0.
      simpl; reflexivity.
      simpl; reflexivity.
      repeat apply f_equal2.
      repeat rewrite <- d_prop_coc_composition_equality.
      apply d_prop_coc_pointwise_equality.
      intros.
      destruct x0.
      simpl; reflexivity.
      simpl; reflexivity.
      simpl; reflexivity.
      rewrite E1.
      apply fd_letter_forall_elim.
      apply fd_forall_intro.
      apply fd_letter_forall_elim.
      apply fd_forall_inverse_intro. ap. ap. ap.
    Defined.
    
    Definition fd_term_letter_equality_if_exun:
      forall (C:Type) (k x u:C) (T: DP C -> Type) (q: DP (option C)),
        first_d_proof C k T (d_exists_unique C q) ->
        first_d_proof C k T (d_prop_letter_specify C u q) ->
        prod (first_d_proof
                C k T
                (d_equiv C
                         (d_belongs C (d_def C q) (d_letter C x))
                         (d_belongs C (d_letter C u) (d_letter C x))))
             (first_d_proof
                C k T
                (d_equiv C
                         (d_belongs C  (d_letter C x) (d_def C q))
                         (d_belongs C  (d_letter C x) (d_letter C u)))).    
    Proof.
      intros.
      split.
      et (d_exun_belongs_term_term C k (d_def C q) (d_letter C x)).
      apply fd_logical_axiom; apply fd_belongs_characterization_ax.
      simpl.
      et (d_forall
            C (d_implies
                 (option C) q
                 (d_belongs
                    (option C)
                    (d_letter (option C) None)
                    (d_letter (option C) (Some x))))).      
      unfold d_exun_belongs_letter_prop.
      apply cpiw_positive_case_in_case_definition
        with (X:= FDCPIW C k T). simpl. ap.
      apply cpiw_and_intro with (X:= FDCPIW C k T).
      apply cpiw_permutation with (X:= FDCPIW C k T) (y:= (d_prop_letter_specify C u q)).
      simpl. apply fd_logical_axiom.
      assert (
          d_implies C (d_prop_letter_specify C u q) (d_belongs C (d_letter C u) (d_letter C x))
          =
          d_prop_letter_specify
            C u
            (d_implies
               (option C) q
               (d_belongs
                  (option C) (d_letter (option C) None) (d_letter (option C) (Some x))))
        ) as E1.
      unfold d_prop_letter_specify. simpl; reflexivity.
      rewrite E1. apply fd_letter_special_case_ax. ap.
      simpl. apply fd_implies_intro.
      apply fd_forall_intro.
      apply fd_implies_intro.
      apply fd_implies_elim with
          (a:= d_belongs (option C)
                         (d_letter (option C) (Some u)) (d_letter (option C) (Some x))).
      apply cpiw_equiv_left_elim with
          (X:= FDCPIW
                 (option C) (Some k)
                 (add_item
                    (DP (option C))
                    (d_theory_constant_embedding
                       C
                       (add_item
                          (DP C) T
                          (d_belongs C (d_letter C u) (d_letter C x)))) q)
          ).
      simpl.
      apply fd_equal_elim_belongs_letter.
      apply fd_letter_unique_elim with
          (q:=d_prop_change_of_context
                (option C) q (option (option C))
                (extend_map_to_bound_variables C (option C) Some)).
      apply fd_weakening_hypothesis. rewrite <- d_unique_coc_eq.
      unfold d_theory_constant_embedding.  apply first_d_proof_context_change.
      apply fd_weakening_hypothesis. apply (cpiw_and_right_elim (FDCPIW C k T)) in X. ap.
      assert (
          d_prop_letter_specify
            (option C) (Some u)
            (d_prop_change_of_context (option C) q (option (option C))
                                      (extend_map_to_bound_variables C (option C) Some))
          =
          d_prop_change_of_context
            C
            (d_prop_letter_specify C u q)
            (option C) Some 
        ) as E2.
      unfold d_prop_letter_specify.
      repeat rewrite <- d_prop_coc_composition_equality.
      apply d_prop_coc_pointwise_equality.
      intros.
      destruct x0.
      simpl; reflexivity.
      simpl; reflexivity.
      rewrite E2.
      apply fd_weakening_hypothesis.
      unfold d_theory_constant_embedding.  apply first_d_proof_context_change.
      apply fd_weakening_hypothesis. ap.
      assert (
          d_prop_letter_specify
            (option C) None
            (d_prop_change_of_context
               (option C) q (option (option C))
               (extend_map_to_bound_variables C (option C) Some))
          =
          d_prop_change_of_context (option C) q (option C) (fun v:option C => v)
        ) as E3.
      unfold d_prop_letter_specify.
      repeat rewrite <- d_prop_coc_composition_equality.
      apply d_prop_coc_pointwise_equality.
      intros.
      destruct x0.
      simpl; reflexivity.
      simpl; reflexivity.
      rewrite E3.
      rewrite d_prop_coc_identity_equality. apply fd_theory_axiom.
      apply new_item.
      apply fd_weakening_hypothesis. unfold d_theory_constant_embedding.
      assert (
          d_belongs (option C) (d_letter (option C) (Some u)) (d_letter (option C) (Some x))
          =
          d_prop_change_of_context
            C (d_belongs C (d_letter C u) (d_letter C x)) (option C) Some
        )
        as E4.
      simpl; reflexivity. rewrite E4. 
      unfold d_theory_constant_embedding.  apply first_d_proof_context_change.
      apply fd_theory_axiom. apply new_item.
      
      et (d_exun_belongs_term_term C k (d_letter C x) (d_def C q)).
      apply fd_logical_axiom; apply fd_belongs_characterization_ax.
      simpl. 
      et (d_forall
            C (d_implies
                 (option C) q
                 (d_belongs
                    (option C)
                    (d_letter (option C) (Some x))
                    (d_letter (option C) None)))).      
      unfold d_exun_belongs_letter_prop.
      apply cpiw_positive_case_in_case_definition
        with (X:= FDCPIW C k T). simpl. ap.
      apply cpiw_and_intro with (X:= FDCPIW C k T).
      apply cpiw_permutation with (X:= FDCPIW C k T) (y:= (d_prop_letter_specify C u q)).
      simpl. apply fd_logical_axiom.
      assert (
          d_implies C (d_prop_letter_specify C u q) (d_belongs C (d_letter C x) (d_letter C u))
          =
          d_prop_letter_specify
            C u
            (d_implies
               (option C) q
               (d_belongs
                  (option C) (d_letter (option C) (Some x)) (d_letter (option C) None)))
        ) as EE1.
      unfold d_prop_letter_specify. simpl; reflexivity.
      rewrite EE1. apply fd_letter_special_case_ax. ap.
      simpl. apply fd_implies_intro.
      apply fd_forall_intro.
      apply fd_implies_intro.
      apply fd_implies_elim with
          (a:= d_belongs (option C)
                         (d_letter (option C) (Some x)) (d_letter (option C) (Some u))).
      apply cpiw_equiv_left_elim with
          (X:= FDCPIW
                 (option C) (Some k)
                 (add_item (DP (option C))
                           (d_theory_constant_embedding C
                                                        (add_item (DP C) T
                                                                  (d_belongs C (d_letter C x) (d_letter C u)))) q)
          ).
      simpl.
      apply fd_equal_elim_belongs_letter.
      apply fd_letter_unique_elim with
          (d_prop_change_of_context
             (option C) q (option (option C))
             (extend_map_to_bound_variables C (option C) Some)).
      apply fd_weakening_hypothesis. rewrite <- d_unique_coc_eq.
      unfold d_theory_constant_embedding.  apply first_d_proof_context_change.
      apply fd_weakening_hypothesis. apply (cpiw_and_right_elim (FDCPIW C k T)) in X. ap.
      assert (
          d_prop_letter_specify
            (option C) (Some u)
            (d_prop_change_of_context (option C) q (option (option C))
                                      (extend_map_to_bound_variables C (option C) Some))
          =
          d_prop_change_of_context
            C
            (d_prop_letter_specify C u q)
            (option C) Some 
        ) as EE2.
      unfold d_prop_letter_specify.
      repeat rewrite <- d_prop_coc_composition_equality.
      apply d_prop_coc_pointwise_equality.
      intros.
      destruct x0.
      simpl; reflexivity.
      simpl; reflexivity.
      rewrite EE2.
      apply fd_weakening_hypothesis.
      unfold d_theory_constant_embedding.  apply first_d_proof_context_change.
      apply fd_weakening_hypothesis. ap.
      assert (
          d_prop_letter_specify
            (option C) None
            (d_prop_change_of_context
               (option C) q (option (option C))
               (extend_map_to_bound_variables C (option C) Some))
          =
          d_prop_change_of_context (option C) q (option C) (fun v:option C => v)
        ) as EE3.
      unfold d_prop_letter_specify.
      repeat rewrite <- d_prop_coc_composition_equality.
      apply d_prop_coc_pointwise_equality.
      intros.
      destruct x0.
      simpl; reflexivity.
      simpl; reflexivity.
      rewrite EE3.
      rewrite d_prop_coc_identity_equality. apply fd_theory_axiom.
      apply new_item.
      apply fd_weakening_hypothesis. unfold d_theory_constant_embedding.
      assert (
          d_belongs (option C) (d_letter (option C) (Some x)) (d_letter (option C) (Some u))
          =
          d_prop_change_of_context
            C (d_belongs C (d_letter C x) (d_letter C u)) (option C) Some
        )
        as EE4.
      simpl; reflexivity. rewrite EE4. 
      unfold d_theory_constant_embedding.  apply first_d_proof_context_change.
      apply fd_theory_axiom. apply new_item.
    Defined.            
    
    Definition fd_term_equality_if_exun:
      forall (C:Type) (k u:C) (T: DP C -> Type) (q: DP (option C)),
        first_d_proof C k T (d_exists_unique C q) ->
        first_d_proof C k T (d_prop_letter_specify C u q) ->
        first_d_proof C k T (d_equal C (d_def C q) (d_letter C u)).
    Proof.
      intros.
      apply first_d_proof_context_change with (D:=option C) (env:=Some) in X.
      rewrite d_exists_unique_coc_eq in X.
      apply first_d_proof_context_change with (D:=option C) (env:=Some) in X0.
      assert
        (d_prop_change_of_context C (d_prop_letter_specify C u q) (option C) Some
         =
         d_prop_letter_specify
           (option C) (Some u)
           (d_prop_change_of_context (option C) q (option (option C))
                                     (extend_map_to_bound_variables C (option C) Some))
        ) as E.
      unfold d_prop_letter_specify.
      repeat rewrite <- d_prop_coc_composition_equality.
      apply d_prop_coc_pointwise_equality.
      intros.
      destruct x.
      simpl; reflexivity.
      simpl; reflexivity.
      rewrite E in X0.
      apply cpiw_and_intro with (X:= FDCPIW C k T).
      apply fd_forall_intro.      
      apply fd_term_letter_equality_if_exun.
      apply X. apply X0. 
      apply fd_forall_intro. 
      apply fd_term_letter_equality_if_exun.
      apply X. apply X0.
    Defined.          

    Definition fd_term_overwhelming_equality_if_exun:
      forall (C:Type) (k u:C) (T: DP C -> Type) (q: DP (option C)),
        first_d_proof C k T (d_exists_unique C q) ->
        first_d_proof C k T (d_prop_letter_specify C u q) ->
        overwhelmingly_equal C k T (d_def C q) (d_letter C u).
    Proof.
      intros.
      unfold overwhelmingly_equal.
      intros.
      unfold strongly_equal.
      split.
      intros r.
      et (d_exun_belongs_term_term
            D (env k) (d_term_change_of_context C (d_def C q) D env) r).
      apply fd_logical_axiom; apply fd_belongs_characterization_ax.
      et (d_exun_belongs_letter_term D (env k) (env u) r).
      simpl.
      et (d_forall
            D (d_implies
                 (option D) (d_prop_change_of_context (option C) q (option D)
                                                      (extend_map_to_bound_variables C D env))
                 (d_exun_belongs_letter_term
                    (option D) (Some (env k))
                    None
                    (d_term_constant_embedding D r
         )))).
      unfold extend_map_to_bound_variables.
      unfold d_exun_belongs_prop_term.
      apply cpiw_positive_case_in_case_definition
        with (X:= FDCPIW D (env k) (d_theory_context_change C T D env)). simpl.
      apply first_d_proof_context_change with (D:=D) (env := env) in X.
      rewrite d_exists_unique_coc_eq in X. ap.     
      apply cpiw_and_intro with (X:= FDCPIW D (env k) (d_theory_context_change C T D env)).
      apply cpiw_permutation with
          (X:= FDCPIW D (env k) (d_theory_context_change C T D env))
          (y:= (d_prop_letter_specify
                  D (env u)
                  (d_prop_change_of_context (option C) q (option D)
                                            (extend_map_to_bound_variables C D env)))).
      simpl. 
      apply fd_logical_axiom.
      assert (
          d_implies
            D
            (d_prop_letter_specify
               D (env u)
               (d_prop_change_of_context (option C) q (option D)
                                         (extend_map_to_bound_variables C D env)))            
            (d_exun_belongs_letter_term D (env k) (env u) r)
          =
          d_prop_letter_specify
            D (env u)
            (d_implies (option D)
                       (d_prop_change_of_context (option C) q (option D)
                                                 (extend_map_to_bound_variables C D env))
                       (d_exun_belongs_letter_term (option D) (Some (env k)) None
                                                   (d_term_constant_embedding D r))
            )
        ) as E1.
      unfold d_prop_letter_specify. simpl. apply f_equal.
      rewrite d_exun_belongs_letter_term_coc_eq.
      simpl. apply f_equal. unfold d_term_constant_embedding.
      rewrite <- d_term_coc_composition_equality.
      rewrite d_term_coc_pointwise_equality with (env2 := fun v:D => v).
      apply eq_sym; apply d_term_coc_identity_equality.
      intros; simpl; reflexivity.      
      rewrite E1. apply fd_letter_special_case_ax. simpl.
      assert
        (d_prop_letter_specify
           D (env u)
           (d_prop_change_of_context (option C) q (option D)
                                     (extend_map_to_bound_variables C D env))
         =
         d_prop_change_of_context C (d_prop_letter_specify C u q) D env
        ) as F1.
      unfold d_prop_letter_specify.
      repeat rewrite <- d_prop_coc_composition_equality.
      apply d_prop_coc_pointwise_equality.
      intros.
      destruct x.
      simpl; reflexivity.
      simpl; reflexivity.
      rewrite F1.
      apply first_d_proof_context_change. ap.
      simpl. apply fd_implies_intro.
      apply fd_forall_intro.
      apply fd_implies_intro.
      apply fd_implies_elim with
          (a:= d_exun_belongs_letter_term
                 (option D)
                 (Some (env k))
                 (Some (env u))
                 (d_term_constant_embedding D r)).
      apply cpiw_equiv_left_elim with
          (X:= FDCPIW
                 (option D) (Some (env k))
                 (add_item
                    (DP (option D))
                    (d_theory_constant_embedding
                       D
                       (add_item
                          (DP D)
                          (d_theory_context_change C T D env)
                          (d_exun_belongs_letter_term D (env k) (env u) r)))
                    (d_prop_change_of_context (option C) q (option D)
                                              (extend_map_to_bound_variables C D env)))   
          ).
      simpl.
      edxlt0.
      apply fd_letter_unique_elim with
          (q:=d_prop_change_of_context
                (option D)
                (d_prop_change_of_context (option C) q (option D)
                                          (extend_map_to_bound_variables C D env))
                (option (option D))
                (extend_map_to_bound_variables D (option D) Some)).
      apply fd_weakening_hypothesis. rewrite <- d_unique_coc_eq.
      unfold d_theory_constant_embedding.  apply first_d_proof_context_change.
      apply fd_weakening_hypothesis.
      apply (cpiw_and_right_elim (FDCPIW C k T)) in X.
      apply first_d_proof_context_change with (D:=D) (env:=env) in X.
      rewrite d_unique_coc_eq in X. ap.
      assert ( 
          d_prop_letter_specify
            (option D) (Some (env u))
            (d_prop_change_of_context
               (option D)
               (d_prop_change_of_context
                  (option C) q (option D)
                  (extend_map_to_bound_variables C D env))
               (option (option D))
               (extend_map_to_bound_variables D (option D) Some)
            )
          =
          d_prop_change_of_context
            D             
            (d_prop_letter_specify
               D (env u)
               (d_prop_change_of_context
                  (option C) q (option D)
                  (extend_map_to_bound_variables C D env)))            
            (option D)
            Some
        ) as E2.
      unfold d_prop_letter_specify.
      repeat rewrite <- d_prop_coc_composition_equality.
      apply d_prop_coc_pointwise_equality.
      intros.
      destruct x.
      simpl; reflexivity.
      simpl; reflexivity.
      rewrite E2.
      apply fd_weakening_hypothesis.
      unfold d_theory_constant_embedding.  apply first_d_proof_context_change.
      apply fd_weakening_hypothesis.
      assert (
          d_prop_letter_specify
            D (env u)
            (d_prop_change_of_context (option C) q (option D)
                                      (extend_map_to_bound_variables C D env))
          =
          d_prop_change_of_context C (d_prop_letter_specify C u q) D env
        )
        as F2.
      unfold d_prop_letter_specify.
      repeat rewrite <- d_prop_coc_composition_equality.
      apply d_prop_coc_pointwise_equality.
      intros.
      destruct x.
      simpl; reflexivity.
      simpl; reflexivity. rewrite F2. apply first_d_proof_context_change. ap.
      assert (
          d_prop_letter_specify
            (option D) None
            (d_prop_change_of_context
               (option D)
               (d_prop_change_of_context
                  (option C) q (option D)
                  (extend_map_to_bound_variables C D env)) (option (option D))
               (extend_map_to_bound_variables D (option D) Some))
          =
          d_prop_change_of_context (option C) q (option D)
                                   (extend_map_to_bound_variables C D env)
        ) as E3.
      unfold d_prop_letter_specify.
      repeat rewrite <- d_prop_coc_composition_equality.
      apply d_prop_coc_pointwise_equality.
      intros.
      destruct x.
      simpl; reflexivity.
      simpl; reflexivity.
      rewrite E3.
      apply fd_theory_axiom. apply new_item. fdrefl.
      apply fd_weakening_hypothesis. unfold d_theory_constant_embedding.
      assert (
          d_exun_belongs_letter_term
            (option D) (Some (env k))
            (Some (env u)) (d_term_constant_embedding D r)
          =
          d_prop_change_of_context
            D (d_exun_belongs_letter_term D (env k) (env u) r) (option D) Some
        )
        as E4.
      apply eq_sym; apply d_exun_belongs_letter_term_coc_eq. rewrite E4. 
      unfold d_theory_constant_embedding. apply first_d_proof_context_change.
      apply fd_theory_axiom. apply new_item.
      simpl. es. apply fd_logical_axiom; apply fd_belongs_characterization_ax.

      intros r.
      et (d_exun_belongs_term_term
            D (env k) r (d_term_change_of_context C (d_def C q) D env)).
      apply fd_logical_axiom; apply fd_belongs_characterization_ax.
      simpl.
      et (d_exun_belongs_term_term
            D (env k) r (d_term_change_of_context C (d_letter C u) D env)).
      destruct r.
      edxlt0. fdrefl. simpl. 
      apply fd_term_equality_if_exun.
      apply first_d_proof_context_change with (D:=D) (env := env) in X.
      rewrite d_exists_unique_coc_eq in X. ap.
      apply first_d_proof_context_change with (D:=D) (env := env) in X0.
      unfold d_prop_letter_specify. unfold d_prop_letter_specify in X0.
      rewrite <- d_prop_coc_composition_equality.
      rewrite <- d_prop_coc_composition_equality in X0.   
      rewrite d_prop_coc_pointwise_equality with
          (env2 := (fun v : option C =>
                      env (option_rect (fun _ : option C => C) (fun x : C => x) u v))). ap.
      intros; destruct x.
      simpl; reflexivity.
      simpl; reflexivity.
      edxpt0. er. simpl.
      apply fd_term_equality_if_exun.
      apply first_d_proof_context_change with (D:=D) (env := env) in X.
      rewrite d_exists_unique_coc_eq in X. ap.
      apply first_d_proof_context_change with (D:=D) (env := env) in X0.
      unfold d_prop_letter_specify. unfold d_prop_letter_specify in X0.
      rewrite <- d_prop_coc_composition_equality.
      rewrite <- d_prop_coc_composition_equality in X0.   
      rewrite d_prop_coc_pointwise_equality with
          (env2 := (fun v : option C =>
                      env (option_rect (fun _ : option C => C) (fun x : C => x) u v))). ap.
      intros; destruct x.
      simpl; reflexivity.
      simpl; reflexivity.
      es. apply fd_logical_axiom; apply fd_belongs_characterization_ax.
    Defined.

    Definition d_prop_letter_specify_identity: forall (C:Type) (l: C) (f: DP (option C)),
        d_prop_letter_specify C l f = d_prop_specify C (d_letter C l) f.
    Proof.
      intros.
      unfold d_prop_specify.
      unfold d_prop_letter_specify.
      apply d_prop_coc_subst_equal.
      intros. destruct x.
      simpl; reflexivity.
      simpl; reflexivity.
    Defined.

    Definition d_prop_coc_specify_identity:
      forall (C D:Type) (t: DT C) (f: DP (option C)) (env: C -> D),
        d_prop_specify
          D (d_term_change_of_context C t D env)
          (d_prop_change_of_context (option C) f (option D)
                                    (extend_map_to_bound_variables C D env))
        =
        d_prop_change_of_context C (d_prop_specify C t f) D env.
    Proof.
      intros.
      unfold d_prop_specify.
      apply d_prop_coc_subst_commutation.
      intros.
      destruct x.
      simpl; reflexivity.
      simpl; reflexivity.
    Defined.
    
    Definition fd_forall_elim:
      forall (C:Type) (k:C) (f: DP (option C)) (t: DT C)(T: DP C -> Type),
        first_d_proof C k T (d_forall C f) ->
        first_d_proof C k T (d_prop_specify C t f).
    Proof.
      intros.
      destruct t.
      rewrite <- d_prop_letter_specify_identity.
      apply fd_implies_elim with (a:= d_forall C f).
      apply fd_logical_axiom; apply fd_letter_special_case_ax. ap.
      apply cpiw_cases with (X := FDCPIW C k T) (x:= d_exists_unique C d).
      simpl.
      apply fd_implies_intro.
      apply fd_exists_elim with (f:=d).
      apply cpiw_and_left_elim with (X := FDCPIW C k (add_hyp_d C T (d_exists_unique C d)))
                                    (y:= d_unique C d).
      simpl. apply fd_theory_axiom; apply new_hyp_d.
      unfold d_prop_constant_embedding.
      rewrite <- d_prop_coc_specify_identity.
      apply fd_implies_elim with
          (a:= d_prop_specify
                 (option C) (d_letter (option C) None)
                 (d_prop_change_of_context
                    (option C) f (option (option C))
                    (extend_map_to_bound_variables C (option C) Some))).
      apply cpiw_equiv_right_elim with
          (X:= FDCPIW
                 (option C) (Some k)
                 (add_item
                    (DP (option C))
                    (d_theory_constant_embedding
                       C
                       (add_item
                          (DP C) T (d_exists_unique C d)))
                    d)
          ).
      simpl.
      apply fd_oe_transfer_prop.
      intros.
      destruct x.
      simpl. unfold overwhelmingly_equal.
      intros.
      split.
      intros. er. intros. er.
      simpl. 
      apply fd_term_overwhelming_equality_if_exun.
      apply fd_theory_axiom.
      apply base_hyp_d.
      assert (
          d_exists_unique
            (option C)
            (d_prop_change_of_context
               (option C) d (option (option C))
               (option_rect
                  (fun _ : option C => option (option C)) (fun a : C => Some (Some a))
                  None)) =
          d_prop_constant_embedding C (d_exists_unique C d)
        ) as E1.
      unfold d_prop_constant_embedding.
      rewrite d_exists_unique_coc_eq. unfold extend_map_to_bound_variables. reflexivity.
      rewrite E1.
      unfold d_theory_constant_embedding; unfold d_prop_constant_embedding. apply dtcc_intro.
      apply new_hyp_d.
      unfold d_prop_letter_specify.
      rewrite <- d_prop_coc_composition_equality.
      rewrite d_prop_coc_pointwise_equality with (env2 := fun v: option C => v).
      rewrite d_prop_coc_identity_equality.
      apply fd_theory_axiom; apply new_hyp_d.
      intros. destruct x. simpl; reflexivity. simpl; reflexivity.
      rewrite <- d_prop_letter_specify_identity.
      unfold d_prop_letter_specify.
      rewrite <- d_prop_coc_composition_equality.
      rewrite d_prop_coc_pointwise_equality with (env2 := fun v: option C => v).
      rewrite d_prop_coc_identity_equality.
      apply fd_weakening_hypothesis. apply fd_forall_inverse_intro.
      apply fd_weakening_hypothesis. ap.
      intros. destruct x. simpl; reflexivity. simpl; reflexivity.
      simpl.
      apply fd_implies_intro.
      apply fd_implies_elim with
          (a:= d_prop_specify C (d_letter C k) f).
      apply cpiw_equiv_right_elim with
          (X:= FDCPIW C k (add_hyp_d C T (d_implies C (d_exists_unique C d) (d_wrong C)))).
      simpl.
      apply fd_oe_transfer_prop.
      intros. destruct x.
      simpl. unfold overwhelmingly_equal.
      intros.
      split.
      intros. er. intros. er.
      simpl. 
      apply fd_term_overwhelming_equality_if_not_exun.
      apply fd_theory_axiom; apply new_hyp_d.
      rewrite <- d_prop_letter_specify_identity.
      apply fd_weakening_hypothesis.
      apply fd_implies_elim with (a := d_forall C f).
      apply fd_logical_axiom; apply fd_letter_special_case_ax. ap.
    Defined.        
    
    Definition fd_special_case:
      forall (C:Type) (k:C) (f: DP (option C)) (t: DT C)(T: DP C -> Type),
        first_d_proof C k T (d_implies C (d_forall C f) (d_prop_specify C t f)). 
    Proof.
      intros.
      destruct t.
      rewrite <- d_prop_letter_specify_identity.
      apply fd_logical_axiom; apply fd_letter_special_case_ax.
      apply fd_implies_intro.
      apply fd_forall_elim.
      apply fd_theory_axiom; apply new_hyp_d.
    Defined.     

    Definition fd_equal_iff_overwhelmingly_equal:
      forall (C:Type) (k:C) (T: DP C -> Type) (x y:DT C),
        prod
          (first_d_proof C k T (d_equal C x y) -> overwhelmingly_equal C k T x y)
          (overwhelmingly_equal C k T x y -> first_d_proof C k T (d_equal C x y)).
    Proof.
      intros.
      split.
      intros.
      unfold overwhelmingly_equal.
      intros. unfold strongly_equal. split. intros.
      assert (
          d_equiv D (d_belongs D (d_term_change_of_context C x D env) u)
                  (d_belongs D (d_term_change_of_context C y D env) u)
          =
          d_prop_specify
            D u (d_equiv
                   (option D)
                   (d_belongs
                      (option D)
                      (d_term_constant_embedding D (d_term_change_of_context C x D env))
                      (d_letter (option D) None)
                   )
                   (d_belongs
                      (option D)
                      (d_term_constant_embedding D (d_term_change_of_context C y D env))
                      (d_letter (option D) None)
                   )
                )
        ) as E1.
      unfold d_prop_specify. unfold d_term_constant_embedding.
      simpl. repeat rewrite <- d_term_coc_composition_equality.
      repeat rewrite d_term_coc_subst_commutation with (D :=  C) (env_var_ddo := env)
                                                       (env_term_cd:= d_letter C).
      repeat rewrite <- d_term_coc_subst_equal with (envc := fun (v:C) => v)
                                                    (envt := d_letter C).
      repeat rewrite d_term_coc_identity_equality. reflexivity.
      intros; reflexivity.
      intros; reflexivity.
      intros; simpl; reflexivity.
      intros; simpl; reflexivity.
      rewrite E1. apply fd_forall_elim.
      apply first_d_proof_context_change with (D:=D) (env := env) in X.
      rewrite d_equal_coc_eq in X. 
      apply cpiw_and_left_elim with (X:= FDCPIW D (env k) (d_theory_context_change C T D env))
        in X. assumption.  intros.
      assert (
          d_equiv D (d_belongs D u (d_term_change_of_context C x D env))
                  (d_belongs D u (d_term_change_of_context C y D env))
          =
          d_prop_specify
            D u (d_equiv
                   (option D)
                   (d_belongs
                      (option D)
                      (d_letter (option D) None)
                      (d_term_constant_embedding D (d_term_change_of_context C x D env))
                   )
                   (d_belongs
                      (option D)
                      (d_letter (option D) None)
                      (d_term_constant_embedding D (d_term_change_of_context C y D env))
                   )
                )
        ) as E2.
      unfold d_prop_specify. unfold d_term_constant_embedding.
      simpl. repeat rewrite <- d_term_coc_composition_equality.
      repeat rewrite d_term_coc_subst_commutation with (D :=  C) (env_var_ddo := env)
                                                       (env_term_cd:= d_letter C).
      repeat rewrite <- d_term_coc_subst_equal with (envc := fun (v:C) => v)
                                                    (envt := d_letter C).
      repeat rewrite d_term_coc_identity_equality. reflexivity.
      intros; reflexivity.
      intros; reflexivity.
      intros; simpl; reflexivity.
      intros; simpl; reflexivity.
      rewrite E2. apply fd_forall_elim.
      apply first_d_proof_context_change with (D:=D) (env := env) in X.
      rewrite d_equal_coc_eq in X. 
      apply cpiw_and_right_elim with (X:= FDCPIW D (env k) (d_theory_context_change C T D env))
        in X. assumption.
      intros.
      apply cpiw_and_intro with (X:= FDCPIW C k T).
      apply fd_forall_intro.
      unfold d_theory_constant_embedding.
      unfold d_term_constant_embedding.
      apply X.
      apply fd_forall_intro.
      unfold d_theory_constant_embedding.
      unfold d_term_constant_embedding.
      apply X.
    Defined.

    Definition fd_eq_transfer_prop
               (C:Type) (p:DP C)
               (D:Type)
               (k:D) (T:DP D -> Type) 
               (env1 env2: C -> DT D)
               (eqpr: forall x:C, first_d_proof D k T (d_equal D (env1 x) (env2 x))):
      first_d_proof
        D k T (d_equiv D (d_prop_substitution C p D env1) (d_prop_substitution C p D env2)).
    Proof.
      apply fd_oe_transfer_prop.
      intros.
      apply fd_equal_iff_overwhelmingly_equal.
      apply eqpr.
    Defined.

    Definition fd_eq_transfer_term
               (C:Type) (t:DT C)
               (D:Type)
               (k:D) (T:DP D -> Type) 
               (env1 env2: C -> DT D)
               (eqpr: forall x:C, first_d_proof D k T (d_equal D (env1 x) (env2 x))):
      first_d_proof
        D k T
        (d_equal D (d_term_substitution C t D env1) (d_term_substitution C t D env2)).
    Proof.
      apply fd_equal_iff_overwhelmingly_equal.
      apply fd_oe_transfer_term.
      intros.
      apply fd_equal_iff_overwhelmingly_equal. apply eqpr.
    Defined.

    Definition fd_equality_elimination_prop:
      forall (C:Type) (k:C) (T: DP C -> Type) (s t:DT C) (p: DP (option C)),
        first_d_proof C k T (d_equal C s t) ->
        first_d_proof C k T (d_equiv C (d_prop_specify C s p) (d_prop_specify C t p)).
    Proof.
      intros.
      unfold d_prop_specify.
      apply fd_eq_transfer_prop.
      intros.
      destruct x. simpl. fdrefl. simpl. ap.
    Defined.
    
    Definition fd_equality_elimination_term:
      forall (C:Type) (k:C) (T: DP C -> Type) (s t:DT C) (u: DT (option C)),
        first_d_proof C k T (d_equal C s t) ->
        first_d_proof C k T (d_equal C (d_term_specify C s u) (d_term_specify C t u)).
    Proof.
      intros.
      unfold d_term_specify.
      apply fd_eq_transfer_term.
      intros.
      destruct x. simpl. fdrefl. simpl. ap.
    Defined.

    Definition fd_def_property_if_not_exun:
      forall (C:Type) (k:C) (T: DP C -> Type) (p:DP (option C)),
        first_d_proof
          C k T
          (d_implies
             C (d_neg C (d_exists_unique C p)) (d_equal C (d_def C p) (d_letter C k))).
    Proof.
      intros.
      apply fd_implies_intro.
      apply fd_term_equality_if_not_exun.
      apply fd_theory_axiom.
      apply new_hyp_d.
    Defined.

    Definition fd_def_property_if_exun:
      forall (C:Type) (k:C) (T: DP C -> Type) (p:DP (option C)),
        first_d_proof
          C k T
          (d_implies C (d_exists_unique C p) (d_prop_specify C (d_def C p) p)).
    Proof.
      intros.
      apply fd_implies_intro.
      apply fd_exists_elim with (f:=p).
      apply cpiw_and_left_elim with
          (X:= FDCPIW C k (add_hyp_d C T (d_exists_unique C p))) (y:= d_unique C p).
      simpl.
      apply fd_theory_axiom; apply new_hyp_d.
      unfold d_prop_constant_embedding. rewrite <- d_prop_coc_specify_identity.
      simpl.     
      apply fd_implies_elim with
          (a:=d_prop_specify
                (option C)
                (d_letter (option C) None)
                (d_prop_change_of_context
                   (option C) p (option (option C))
                   (option_rect
                      (fun _ : option C => option (option C)) (fun a : C => Some (Some a))
                      None))
          ).
      apply cpiw_equiv_left_elim with
          (X:= FDCPIW
                 (option C) (Some k)
                 (add_item
                    (DP (option C))
                    (d_theory_constant_embedding
                       C
                       (add_item
                          (DP C) T (d_exists_unique C p))) p)    
          ).
      simpl.
      unfold d_prop_specify. es.      
      apply fd_oe_transfer_prop.
      intros.
      destruct x.
      simpl. unfold overwhelmingly_equal.
      intros. split. intros. er. intros. er.
      simpl.     
      apply fd_term_overwhelming_equality_if_exun.
      rewrite <- d_exists_unique_coc_eq with (D:= option C) (env := Some).
      apply fd_weakening_hypothesis.
      unfold d_theory_constant_embedding. apply fd_theory_axiom.
      apply dtcc_intro. apply new_hyp_d.
      unfold d_prop_constant_embedding. unfold d_prop_letter_specify.
      rewrite <- d_prop_coc_composition_equality.
      rewrite d_prop_coc_pointwise_equality with (env2 := fun (v:option C) => v).
      rewrite d_prop_coc_identity_equality.
      apply fd_theory_axiom; apply new_hyp_d.
      intros.
      destruct x. simpl; reflexivity. simpl; reflexivity.
      rewrite <- d_prop_letter_specify_identity.
      unfold d_prop_letter_specify.
      rewrite <- d_prop_coc_composition_equality.
      rewrite d_prop_coc_pointwise_equality with (env2 := fun (v:option C) => v).
      rewrite d_prop_coc_identity_equality.
      apply fd_theory_axiom; apply new_hyp_d.
      intros.
      destruct x. simpl; reflexivity. simpl; reflexivity.
    Defined.
    
  End core_technical_results.      
  
End A_first_proof_system_for_D_Prop.  

