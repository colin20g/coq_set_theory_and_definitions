Require Import SetDef.add_items_to_theories_and_other_tools.

(** In this file we define first order logic for a signature consisting of a single
binary relationship symbol "belongs". Introducing an equality symbol is not necessary;
indeed we define "x equals y" by "[forall z (z belongs to x iff z b)] and [forall t
(x belongs to t iff y belongs to t)]" and it turns out that this definition of equality
satisfies the Leibniz property. Moreover, when (one of the equivalent versions of) the 
extensionality axiom is assumed, it can be proven that two objects are equal in this sense
if and only if they have the same elements.    
 *)

Section basic_definitions.

(** the map below does basically the same thing as "option_map"; 
but we didn't know the latter at the time the majority of this program was written.*)
  
  Definition extend_map_to_bound_variables (C D:Type) (f:C -> D): (option C) -> (option D):=
    option_rect (fun _ : option C => option D) (fun a : C => Some (f a)) None.        

(** In order to implement first order formulas, we need a mechanism to manage bound variables.
    We use nested abstract syntax, as in https://math.unice.fr/~ah/div/fsubwf.pdf .
    New variables are added to he cirent context with the option operator.  
*)
  
  Inductive Set_Formula: Type -> Type:=
  |sf_belongs: forall C:Type,C -> C -> Set_Formula C
  |sf_wrong: forall C:Type, Set_Formula C
  |sf_implies: forall C:Type, Set_Formula C -> Set_Formula C -> Set_Formula C
  |sf_forall: forall C:Type, Set_Formula (option C) -> Set_Formula C.

  Notation add_hyp := (fun C:Type => add_item (Set_Formula C)).
  Notation new_hyp := (fun C:Type => new_item (Set_Formula C)).
  Notation base_hyp := (fun C:Type => base_item (Set_Formula C)).
  
  Section definitions_of_propositional_connectors.

    Variable C:Type.
    Notation F:= (Set_Formula C).
    Notation impl:= (sf_implies C).
    Notation wr:= (sf_wrong C).
    
    Definition sf_neg (a:F):= impl a wr.
    Definition sf_or (a b:F):= impl (sf_neg a) b.
    Definition sf_and (a b:F):= sf_neg (impl a (sf_neg b)). 
    Definition sf_equiv (a b:F):= sf_and (impl a b) (impl b a).
    
  End definitions_of_propositional_connectors.

  Section definitions_of_quantifiers_related_formulas.

    Variable C:Type.

    Notation bel := (sf_belongs (option C)).


    Definition sf_equal (x y:C):Set_Formula C:=
      sf_and C
             (        sf_forall C
                                (sf_equiv (option C)
                                          (bel (Some x) (None))
                                          (bel (Some y) (None))
                                )
             )
             (        sf_forall C
                                (sf_equiv (option C)
                                          (bel None (Some x))
                                          (bel None (Some y))
                                )
             ).      
    
    (** the definition of equality below will be used with extensionality we'll develop 
        further*)
    
    Definition sf_ext_equal (x y:C):=
      sf_forall C
                (sf_equiv (option C)
                          (bel (None) (Some x))
                          (bel (None) (Some y))
                ).

    Definition sf_exists (f: Set_Formula (option C)):=
      sf_neg C (sf_forall C (sf_neg (option C) f)).

    Definition sf_is_the_set_of (x:C) (A:Set_Formula (option C)):=
      sf_forall C
                (
                  sf_equiv (option C)                           
                           (bel (None) (Some x))
                           A
                ).         
        
  End definitions_of_quantifiers_related_formulas.

  Section definition_of_change_of_variables_maps.

    Fixpoint change_of_context (A B:Type)(chvar:A -> B)(u:Set_Formula A) {struct u}:
      (Set_Formula B):=
      match u in (Set_Formula T) return ((T -> B) -> Set_Formula B) with
      | sf_belongs C c c0 => fun f : C -> B => sf_belongs B (f c) (f c0)
      | sf_wrong C => fun _ : C -> B => sf_wrong B
      | sf_implies C u1 u2 =>
        fun f : C -> B =>
          sf_implies B (change_of_context C B f u1) (change_of_context C B f u2)
      | sf_forall C u0 =>
        fun f : C -> B =>
          sf_forall B
                    (change_of_context (option C) (option B)
                                       (extend_map_to_bound_variables C B f) u0)
      end chvar.

    Definition constant_formula_embedding
               (C:Type) (u:Set_Formula C):(Set_Formula (option C)):=
      change_of_context C (option C) (Some) u.
    
    Definition specify (C:Type) (t:C): Set_Formula (option C) -> Set_Formula C:=
      change_of_context (option C) C (option_rect (fun _:option C => C)
                                                  (fun x:C => x)
                                                  t).

    Definition predicate_embedding
               (C:Type): (Set_Formula (option C)) -> (Set_Formula (option (option C))):=
      change_of_context (option C)
                        (option (option C))
                        (option_rect (fun _:option C => option (option C))
                                     (fun x:C => Some (Some x))
                                     None).
    
    Section compatibility_theorems_about_specify_and_constant_embedding.

      Definition coc_pointwise_equality: forall (A B:Type) (f g: A -> B),
        (forall x:A, f x = g x) -> forall (u: Set_Formula A),
          change_of_context A B f u = change_of_context A B g u.
      Proof.
        assert (let aux := fun (A:Type) (u: Set_Formula A) =>
                             forall (B:Type) (f g:A -> B),
                               (forall x:A, f x = g x) ->
                               change_of_context A B f u = change_of_context A B g u
                in
                forall (C:Type) (v:Set_Formula C), aux C v
               ) as AUX_RECT.
        apply Set_Formula_rect.
        intros.
        simpl.
        rewrite H with (x:=c).
        rewrite H with (x:=c0).
        reflexivity.
        intros.
        simpl; reflexivity.
        intros.
        simpl.
        rewrite H with (g:=g).
        rewrite H0 with (g:=g).
        reflexivity.
        assumption.
        assumption.
        intros.
        simpl.
        apply f_equal.
        apply H.
        intros.
        destruct x.
        simpl; rewrite H0 with (x:=c); reflexivity.
        simpl; reflexivity.
        simpl in AUX_RECT.
        intros.
        apply AUX_RECT.
        assumption.
      Defined.

      Definition coc_composition_equality:
        forall (A B C:Type) (f: A -> B) (g: B -> C) (u: Set_Formula A),
          change_of_context A C (fun (v:A) => g (f v)) u =
          change_of_context B C g (change_of_context A B f u).
      Proof.
        assert (let aux := fun (A:Type) (u: Set_Formula A) =>
                             forall (B C:Type) (f:A -> B) (g: B -> C),
                               change_of_context A C (fun (v:A) => g (f v)) u =
                               change_of_context B C g (change_of_context A B f u)
                in
                forall (C:Type) (v:Set_Formula C), aux C v
               ) as AUX_RECT.
        apply Set_Formula_rect.
        intros.
        simpl.
        reflexivity.
        intros; simpl.
        reflexivity.
        intros; simpl.
        rewrite H.
        rewrite H0; reflexivity.
        intros; simpl.
        apply f_equal.
        rewrite <- H.
        apply coc_pointwise_equality.
        intros.
        destruct x.
        simpl; reflexivity.
        simpl; reflexivity.
        simpl in AUX_RECT.
        intros; apply AUX_RECT.
      Defined.

      Definition coc_identity_equality:
        forall (A:Type) (u: Set_Formula A),
          change_of_context A A (fun (v:A) => v) u = u.
      Proof.
        induction u.
        simpl; reflexivity.
        simpl; reflexivity.
        simpl; rewrite IHu1; rewrite IHu2; reflexivity.
        simpl.
        apply f_equal.
        unfold extend_map_to_bound_variables.
        rewrite coc_pointwise_equality with (g:= fun v:option C  => v).
        assumption.
        intros.
        destruct x.
        reflexivity.
        reflexivity.
      Defined.
      
    End compatibility_theorems_about_specify_and_constant_embedding.
    
  End definition_of_change_of_variables_maps. 
  
  Section further_language_definitions.

    Variable C:Type.

    Notation F:= (Set_Formula C).
    Notation P:= (Set_Formula (option C)) (** "predicate", or property*).

    Notation forall_x := (sf_forall C).
    Notation forall_y := (sf_forall (option C)).
    
    Notation C' := (option C).
    Notation C'' := (option (option C)).
    
    Notation X:= (None).
    Notation x:= (Some (None)).
    Notation y:= (None).
    
    Definition sf_is_a_set (A:P):=
      sf_exists C
                (sf_is_the_set_of (option C)
                               (None)
                               (predicate_embedding C A)
                ).

    Let var_embed2 (a:C):option (option C):= Some (Some a).

    Definition map_specify
               (M N:Type) (e: M -> N) (s:N): Set_Formula (option M) -> Set_Formula N:=
      change_of_context (option M) N (option_rect (fun _:option M => N) e s).

    Notation local_map_specify :=
             (fun (M N:Type) (e: M -> N) (s:N) =>
                change_of_context (option M) N (option_rect (fun _:option M => N) e s)).
    
    Definition sf_unique (A:P):=
      forall_x
        (forall_y
           (sf_implies
              C''
              (local_map_specify C C'' var_embed2 x A)
              (sf_implies
                 C''
                 (local_map_specify C C'' var_embed2 y A)
                 (sf_equal C'' x y)
              ) 
           )
        ).

    Definition sf_exists_unique (A: Set_Formula (option C)):=
      sf_and C (sf_exists C A) (sf_unique A). 
    
  End further_language_definitions.

  Section Hilbert_systems_and_natural_deduction_for_Set_Formulas.

    Notation KF:=
      (fun (C:Type) (a b:Set_Formula C) => sf_implies C a (sf_implies C b a)).

    Notation SF:=
      (fun (C:Type)
           (a b c:Set_Formula C) =>
         sf_implies
           C
           (sf_implies C a (sf_implies C b c))
           (sf_implies C (sf_implies C a b) (sf_implies C a c))).

    Notation ABSF:=
      (fun (C:Type) (a:Set_Formula C) =>
         sf_implies
           C
           (sf_implies C (sf_implies C a (sf_wrong C)) (sf_wrong C))
           a
      ).

    Notation special_case_F:=
      (fun (C:Type) (a: Set_Formula (option C)) (t: C) =>
         sf_implies C
                    (sf_forall C a)
                    (specify C t a)
      ).

    Notation forall_const_F:=
      (fun (C:Type) (b:Set_Formula C) =>
         sf_implies C
                    b
                    (sf_forall C (constant_formula_embedding C b))
      ).

    Notation forall_mp_F:=
      (fun (C:Type) (a b: Set_Formula (option C)) =>
         sf_implies C
                    (sf_forall C (sf_implies (option C) a b))
                    (sf_implies C
                                (sf_forall C a)
                                (sf_forall C b)
                    )
      ).

    Inductive logical_axiom: forall C:Type, Set_Formula C -> Type:=
    |K_ax: forall (C:Type) (a b:Set_Formula C), logical_axiom C (KF C a b)
    |S_ax: forall (C:Type) (a b c:Set_Formula C), logical_axiom C (SF C a b c)
    |ABS_ax: forall (C:Type) (a:Set_Formula C), logical_axiom C (ABSF C a)
    |special_case_ax: forall (C:Type) (a:Set_Formula (option C)) (t:C),
        logical_axiom C (special_case_F C a t)
    |forall_const_ax:  forall (C:Type) (b:Set_Formula C),
        logical_axiom C (forall_const_F C b)
    |forall_mp_ax: forall (C:Type) (a b:Set_Formula (option C)),
        logical_axiom C (forall_mp_F C a b)
    |universal_closure:  forall (C:Type) (f:Set_Formula (option C)),
        logical_axiom (option C) f -> logical_axiom C (sf_forall C f).

    Section Hilbert_systems_definition.

      Variable C:Type.
      Variable T: Set_Formula C -> Type.

      Notation F := (Set_Formula C).
      Notation "a § b" := (sf_implies C a b) (right associativity, at level 51).

      Inductive hs_proof: F -> Type :=
      |hs_theory_axiom: forall x:F, T x -> hs_proof x
      |hs_logical_axiom: forall y:F, logical_axiom C y -> hs_proof y
      |hs_implies_elim: forall a b:F,
          hs_proof (sf_implies C a b) -> hs_proof a -> hs_proof b.

      Definition hs_identity: forall a:F,
          hs_proof (sf_implies C a a).
      Proof.
        intros.
        apply hs_implies_elim with (a § (a § a)).
        apply hs_implies_elim with (a § (a § a) § a).
        apply hs_logical_axiom; apply S_ax.
        apply hs_logical_axiom; apply K_ax.
        apply hs_logical_axiom; apply K_ax.
      Defined.   

      Notation wr := (sf_wrong C).
      
      Definition hs_absurd: forall a:F,
          hs_proof ((a § wr) § wr) -> hs_proof a.
      Proof.
        intros.
        apply hs_implies_elim with (a:= (a § wr) § wr).
        apply hs_logical_axiom.
        apply ABS_ax.
        assumption.
      Defined.

      Definition hs_all_elim: forall (a: Set_Formula (option C)) (t:C),
          hs_proof (sf_forall C a) -> hs_proof (specify C t a).
      Proof.
        intros.
        apply hs_implies_elim with (a:= sf_forall C a).
        apply hs_logical_axiom.
        apply special_case_ax.
        assumption.
      Defined.
      
    End Hilbert_systems_definition.

    Section Hilbert_systems_deduction_properties.
      
      Variable C:Type.
      Variable T: Set_Formula C -> Type.
      Variable h: Set_Formula C.

      Notation F := (Set_Formula C).
      Notation "a § b" := (sf_implies C a b) (right associativity, at level 51).
      
      Definition hs_implies_intro: forall u:F,
          hs_proof C (add_hyp C T h) u -> hs_proof C T (h § u).
      Proof.
        apply hs_proof_rect.
        intros.
        destruct t.
        apply hs_identity.
        apply hs_implies_elim with (a:=x).
        apply hs_logical_axiom; apply K_ax.
        apply hs_theory_axiom.
        assumption.
        intros.
        apply hs_implies_elim with (a:=y).
        apply hs_logical_axiom; apply K_ax.
        apply hs_logical_axiom.
        assumption.
        intros.
        apply hs_implies_elim with (a:= h § a).
        apply hs_implies_elim with (a:= h § a § b).
        apply hs_logical_axiom; apply S_ax.
        assumption.
        assumption.
      Defined.       

      Definition hs_weakening:
        forall (U: Set_Formula C -> Type) (w: forall f:Set_Formula C, T f -> U f)
               (g:Set_Formula C),
         hs_proof C T g -> hs_proof C U g.
      Proof.
        intros U w.
        apply hs_proof_rect.
        intros; apply hs_theory_axiom; apply w; assumption.
        apply hs_logical_axiom.
        intros; apply hs_implies_elim with (a:=a); assumption; assumption.
      Defined.
        
    End Hilbert_systems_deduction_properties.

    Section Hilbert_systems_generalization_properties.

      Variable C:Type.
      Variable T: Set_Formula C -> Type.
      Variable h: Set_Formula C.

      Notation F := (Set_Formula C).
      Notation "a § b" := (sf_implies C a b) (right associativity, at level 51).

      Inductive constant_theory_embedding: Set_Formula (option C) -> Type :=
        ct_embed: forall x:F, T x ->
                              constant_theory_embedding (constant_formula_embedding C x).

      Definition hs_forall_intro: forall a: Set_Formula (option C),
          hs_proof (option C) (constant_theory_embedding) a ->
          hs_proof C T (sf_forall C a).
      Proof.
        apply hs_proof_rect.
        intros.
        destruct t.
        apply hs_implies_elim with (a:=x).
        apply hs_logical_axiom.
        apply forall_const_ax.
        apply hs_theory_axiom.
        assumption.
        intros.
        apply hs_logical_axiom.
        apply universal_closure; assumption.
        intros.
        apply hs_implies_elim with (a:= sf_forall C a).
        apply hs_implies_elim with (a:= sf_forall C (sf_implies (option C) a b)).
        apply hs_logical_axiom; apply forall_mp_ax.
        assumption.
        assumption.
      Defined.

    End Hilbert_systems_generalization_properties.

    (** We provide a natural deduction system for the language we have defined. Although it will
      be seldom used in the text, the idea is to show what we do is familiar to the reader.
     We show below that the Hilbert system we have defined proves the same theorems as 
     this natural deduction system.*)
                      
    Inductive nd_proof: forall C:Type, ((Set_Formula C) -> Type) -> Set_Formula C -> Type:=
    |nd_ax: forall (C:Type) (T: Set_Formula C -> Type)(f:Set_Formula C),
        T f -> nd_proof C T f
    |nd_impl_e: forall (C:Type) (T: Set_Formula C -> Type)(f g:Set_Formula C),
        nd_proof C T (sf_implies C f g) -> nd_proof C T f -> nd_proof C T g
    |nd_impl_i: forall (C:Type) (T: Set_Formula C -> Type)(f g:Set_Formula C),
        nd_proof C (add_hyp C T f) g -> nd_proof C T (sf_implies C f g)
    |nd_absurd: forall (C:Type) (T: Set_Formula C -> Type)(f:Set_Formula C),
        nd_proof C T (sf_implies C (sf_implies C f (sf_wrong C)) (sf_wrong C)) ->
        nd_proof C T f
    |nd_all_e: forall (C:Type) (T: Set_Formula C -> Type) (f:Set_Formula (option C)) (t:C),
        nd_proof C T (sf_forall C f) -> nd_proof C T (specify C t f)
    |nd_all_i: forall (C:Type) (T: Set_Formula C -> Type) (f:Set_Formula (option C)),
        nd_proof (option C) (constant_theory_embedding C T) f ->
        nd_proof C T (sf_forall C f).
    
    Section nd_and_hs_are_equivalent.

      Definition nd_forall_mp:
        forall (C:Type)(T:Set_Formula C -> Type)(a b:Set_Formula (option C)),
          nd_proof C T (forall_mp_F C a b).
      Proof.
        intros.
        assert (forall x:Set_Formula (option C),
                   specify (option C)
                           (None)
                           (change_of_context (option C) (option (option C))
                                              (extend_map_to_bound_variables C (option C)
                                                                        (Some))
                                              x
                           )
                   =
                   x
               ) as E.
        intros.
        unfold specify.
        unfold map_specify.
        apply eq_trans with
            (y:= change_of_context (option C) (option C) (fun t:option C => t) x).
        rewrite <- coc_composition_equality.
        apply coc_pointwise_equality.
        intros.
        destruct x0.
        simpl.
        reflexivity.
        simpl.
        reflexivity.
        apply coc_identity_equality.
        assert (
            nd_proof (option C)
                     (constant_theory_embedding
                        C
                        (add_hyp C (add_hyp C T (sf_forall C (sf_implies (option C) a b))
                                   )
                                 (sf_forall C a)
                        )                        
                     )                     
                     (constant_formula_embedding C
                                                 (sf_forall C (sf_implies (option C) a b))))
          as HAB.
        apply nd_ax.
        apply ct_embed.
        apply base_hyp; apply new_hyp.
        assert (
            nd_proof (option C)
                     (constant_theory_embedding
                        C
                        (add_hyp C (add_hyp C T (sf_forall C (sf_implies (option C) a b))
                                   )
                                 (sf_forall C a)
                        )                        
                     )                     
                     (constant_formula_embedding C
                                                 (sf_forall C a)))
          as HA.
        apply nd_ax.
        apply ct_embed.
        apply new_hyp.                                
        apply nd_impl_i.
        apply nd_impl_i.
        apply nd_all_i.
        apply nd_impl_e with (f:=a).        
        apply eq_rect with            
            (x:= specify
                   (option C)
                   (None)
                   (change_of_context (option C)
                                      (option (option C))
                                      (extend_map_to_bound_variables C (option C)
                                                                (Some)
                                      )
                                      (sf_implies (option C) a b)
                   )
            ).
        apply nd_all_e.
        apply HAB.
        apply E.
        apply eq_rect with            
            (x:= specify
                   (option C)
                   (None)
                   (change_of_context (option C)
                                      (option (option C))
                                      (extend_map_to_bound_variables C (option C)
                                                                (Some)
                                      )
                                      a
                   )
            ).
        apply nd_all_e.
        apply HA.
        apply E.
      Defined.       
      
      Definition nd_to_hs: forall (C:Type) (T: Set_Formula C -> Type) (f:Set_Formula C),
        nd_proof C T f -> hs_proof C T f.
      Proof.
        apply nd_proof_rect.
        intros.
        apply hs_theory_axiom.
        assumption.
        intros.
        apply hs_implies_elim with (a:=f).
        assumption.
        assumption.
        intros.
        apply hs_implies_intro.
        assumption.
        intros.
        apply hs_absurd; assumption.
        intros.
        apply hs_all_elim; assumption.
        intros.
        apply hs_forall_intro.
        assumption.
      Defined.
      
      Definition logical_axiom_to_nd:
        forall (C:Type) (f: Set_Formula C),
          logical_axiom C f -> forall (T:Set_Formula C -> Type), nd_proof C T f.
      Proof.
        assert (let aux := fun (D:Type) (g: Set_Formula D) =>
                             forall U:Set_Formula D -> Type,
                               nd_proof D U g
                in
                forall (C:Type) (f:Set_Formula C),
                  logical_axiom C f -> aux C f
          ) as AUX_RECT.
        apply logical_axiom_rect.
        intros.
        apply nd_impl_i.
        apply nd_impl_i.
        apply nd_ax.
        apply base_hyp; apply new_hyp.
        intros.
        apply nd_impl_i.
        apply nd_impl_i.
        apply nd_impl_i.
        apply nd_impl_e with (f:=b).
        apply nd_impl_e with (f:=a).
        apply nd_ax.
        apply base_hyp; apply base_hyp; apply new_hyp.
        apply nd_ax.
        apply new_hyp.
        apply nd_impl_e with (f:= a).
        apply nd_ax.
        apply base_hyp; apply new_hyp.
        apply nd_ax.
        apply new_hyp.
        intros.
        apply nd_impl_i.
        apply nd_absurd.
        apply nd_ax.
        apply new_hyp.
        intros.
        apply nd_impl_i.
        apply nd_all_e.
        apply nd_ax.
        apply new_hyp.
        intros.
        apply nd_impl_i.
        apply nd_all_i.
        apply nd_ax.
        apply ct_embed.
        apply new_hyp.
        intros.
        apply nd_forall_mp.
        intros.
        apply nd_all_i.
        apply X.
        simpl in AUX_RECT.
        assumption.
      Defined.  

      Definition hs_to_nd: forall (C:Type)(T: Set_Formula C -> Type) (u:Set_Formula C),
          hs_proof C T u -> nd_proof C T u.
      Proof.
        intros C T.
        apply hs_proof_rect.
        apply nd_ax.
        intros; apply logical_axiom_to_nd; assumption.
        intros.
        apply nd_impl_e with (f:=a).
        assumption.
        assumption.
      Defined.
      
    End nd_and_hs_are_equivalent.

    Section morphisms_of_theories_and_proofs.

      Inductive theory_context_change
                (C D:Type) (f:C -> D) (T: Set_Formula C -> Type): (Set_Formula D -> Type):=
      |tcc_embed: forall u:Set_Formula C,
          T u -> theory_context_change C D f T (change_of_context C D f u).    

      Definition logical_axiom_context_change:
        forall (C:Type) (D:Type) (f:C -> D) (u: Set_Formula C),
          logical_axiom C u -> logical_axiom D (change_of_context C D f u).
      Proof.
        assert (let aux := fun (M:Type) (x:Set_Formula M) =>
                             forall (N:Type)(h:M -> N),
                               logical_axiom N (change_of_context M N h x)
                in
                forall (C:Type)(u:Set_Formula C), logical_axiom C u -> aux C u  
               ) as AUX_RECT.
        apply logical_axiom_rect.
        intros; apply K_ax.
        intros; apply S_ax.
        intros; apply ABS_ax.
        intros.
        assert (change_of_context C N h (specify C t a)=
                specify N (h t) (change_of_context (option C)
                                                   (option N)
                                                   (extend_map_to_bound_variables C N h)
                                                   a)
               ) as E.
        unfold specify.
        unfold map_specify.
        rewrite <- coc_composition_equality.
        rewrite <- coc_composition_equality.
        apply coc_pointwise_equality.
        intros; destruct x.
        simpl.
        reflexivity.
        simpl.
        reflexivity.
        simpl.
        rewrite E.
        apply special_case_ax.
        intros.
        simpl.
        assert (
            change_of_context (option C) (option N)(extend_map_to_bound_variables C N h)
                              (constant_formula_embedding C b)
            =
            (constant_formula_embedding N (change_of_context C N h b))
               ) as E'.
        unfold constant_formula_embedding.
        rewrite <- coc_composition_equality.
        rewrite <- coc_composition_equality.
        apply coc_pointwise_equality.
        intros; simpl; reflexivity.
        rewrite E'.
        apply forall_const_ax.
        intros; simpl; apply forall_mp_ax.
        intros.
        simpl.
        apply universal_closure.
        apply X.
        simpl in AUX_RECT.
        intros.
        apply AUX_RECT.
        assumption.
      Defined.

      Definition hs_proof_context_change:
        forall (C:Type) (D:Type) (T: Set_Formula C -> Type) (f:C -> D) (u: Set_Formula C),
          hs_proof C T u ->
          hs_proof D (theory_context_change C D f T) (change_of_context C D f u).
      Proof.
        intros C D T f.
        apply hs_proof_rect.
        intros; apply hs_theory_axiom; apply tcc_embed.
        assumption.
        intros; apply hs_logical_axiom; apply logical_axiom_context_change; assumption.
        intros; apply hs_implies_elim with (a:=change_of_context C D f a);
          assumption; assumption.
      Defined.      

      Definition ct_embed_proof: forall (C:Type) (T:Set_Formula C -> Type) (u:Set_Formula C),
          hs_proof C T u -> hs_proof (option C)(constant_theory_embedding C T)
                                     (constant_formula_embedding C u).
      Proof.
        intros.
        apply hs_weakening with (T:= theory_context_change C (option C) (Some )T).
        intros.
        destruct X0.
        apply ct_embed.
        assumption.
        apply hs_proof_context_change.
        assumption.
      Defined.
        
    End morphisms_of_theories_and_proofs.

    Section some_propositional_inference_rules.

      (** These may be formulated with natural deduction, but we'll stick to Hilbert systems
        because they're easier to handle for some of our purposes*)

      Variable (C:Type).
      Variable (T:Set_Formula C -> Type).
    
      Ltac mp x:= apply hs_implies_elim with (a:=x).
      Ltac lax := apply hs_logical_axiom.
      Ltac ded := apply hs_implies_intro.
      Ltac ax := apply hs_theory_axiom.
      Ltac ka := apply hs_logical_axiom; apply K_ax.     
      Ltac sa := apply hs_logical_axiom; apply S_ax.
      Ltac abs := apply hs_absurd.
      Ltac we R:= apply hs_weakening with (T:=R).
      Ltac wet:= apply hs_weakening with (T:=T).
      Ltac bh := apply base_hyp.
      Ltac nh := apply new_hyp.
      Ltac asp := assumption.
      
      Notation F:= (Set_Formula C).  
      Notation "U |- m" := (hs_proof C U m) (at level 61).
      Notation "x § y" := (sf_implies C x y) (right associativity, at level 51).
      Notation wr := (sf_wrong C).

      Definition hs_weakening_hypothesis: forall (U: F -> Type) (h x:F),
          U |- x -> (add_hyp C U h) |- x.
      Proof.
        intros.
        we U.
        bh.
        asp.
      Defined.

      Ltac wh := apply hs_weakening_hypothesis.

      Section combinator_like_tautologies.

        Definition hs_b_syllogism_formula: forall x y z:F,
          T |- (y § z) § (x § y) § (x § z).
        Proof.
          intros.
          mp ((y § z) § (x § y § z)).
          mp ((y § z) § SF C x y z).
          sa.
          mp (SF C x y z).
          ka.
          sa.
          ka.
        Defined.
        
        Definition hs_q_syllogism_formula: forall x y z:F,
            T|- (x § y) § (y § z) § (x § z).
        Proof.
          intros.
          mp (KF C (x § y) (y § z)).
          mp ((x § y) § ((y § z) § x § y) § (y § z) § x § z).
          sa.
          mp (((y § z) § x § y) § (y § z) § x § z).
          ka.
          mp ((y § z) § (x § y) § x § z).
          sa.
          apply hs_b_syllogism_formula.
          ka.
        Defined.

        Notation BF := (fun (x y z:F) => (y § z) § (x § y) § x § z).
        
        Definition hs_permutation_formula: forall x y z:F,
            T |- (x § y § z) § (y § x § z).
        Proof.
          intros.
          mp ((x § y § z) § y § x § y).
          mp ((x § y § z) § (y § x § y) § y § x § z).
          sa.
          mp (SF C x y z).
          mp ((x § y § z) § ((x § y) § x § z) § (y § x § y) § y § x § z).
          sa.
          mp (((x § y) § x § z) § (y § x § y) § y § x § z).
          ka.
          apply hs_b_syllogism_formula.
          sa.
          mp (y § x § y).
          ka.
          ka.
        Defined.

      End combinator_like_tautologies.

      Definition hs_double_negation_formula: forall x:F,
          T |- x § (x § wr) § wr.
      Proof.
        intros.
        ded.
        ded.
        mp x.
        ax; nh.
        ax; bh; nh.
      Defined.

      Definition hs_double_negation: forall x:F,
          T |- x -> T|- (x § wr) § wr.
      Proof.
        intros.
        mp x.
        apply hs_double_negation_formula.
        asp.
      Defined.

      Definition hs_contraposition_formula: forall a b:F,
          T|- (a § b) § (sf_neg C b) § (sf_neg C a).
      Proof.
        intros.
        apply hs_q_syllogism_formula.
      Defined.

      Definition hs_contraposition: forall a b:F,
          T|- (a § b) -> T |- (sf_neg C b) § (sf_neg C a).
      Proof.
        intros.
        mp (a § b).
        apply hs_contraposition_formula.
        asp.
      Defined.

      Definition hs_syllogism: forall (x y z:F),
          T |- x § y -> T |- y § z -> T |- x § z.
      Proof.
        intros.
        mp (x § y).
        mp (y § z).
        apply hs_b_syllogism_formula.
        asp.
        asp.
      Defined.

      Ltac syl u := apply hs_syllogism with (y:=u).
      
      Definition hs_absurd2_formula: forall x y:F,
          T |- ((sf_neg C y) § (sf_neg C x)) § x § y.
      Proof.
        intros.
        syl (x § (y § wr) § wr).
        apply hs_permutation_formula.
        mp ((sf_neg C (sf_neg C y)) § y).
        apply hs_b_syllogism_formula.
        lax.
        apply ABS_ax.
      Defined.

      Definition hs_absurd2: forall x y:F,
          T |- ((sf_neg C y) § (sf_neg C x)) -> T |- x § y.
      Proof.
        intros.
        mp ((sf_neg C y) § (sf_neg C x)).
        apply hs_absurd2_formula.
        asp.
      Defined.

      Definition hs_and_intro_formula: forall a b:F,
          T |- a § b § (sf_and C a b).
      Proof.
        intros.
        ded; ded; ded.
        mp b.
        mp a.
        ax.
        nh.
        wh; wh; ax; nh.
        ax; bh; nh.
      Defined.
      
      Definition hs_and_intro: forall a b:F,
          T |- a -> T |- b -> T |- sf_and C a b.
      Proof.
        intros.
        mp b.
        mp a.
        apply hs_and_intro_formula.
        asp.
        asp.        
      Defined.

      Definition hs_explosion_formula: forall (U:F -> Type)(x:F),
          U |- wr § x.
      Proof.
        intros.
        ded.
        abs.
        ded.
        ax; bh; nh.
      Defined.

      Definition hs_explosion: forall (U:F -> Type) (x:F),
          U |- wr -> U |- x.
      Proof.
        intros.
        mp (sf_wrong C).
        apply hs_explosion_formula.
        asp.
      Defined.        
      
      Definition hs_and_elim_left_formula: forall a b:F,
          T|- (sf_and C a b) § a.
      Proof.
        intros.
        ded.
        abs.
        ded.
        mp (a § sf_neg C b).
        ax; bh; nh.
        ded.
        apply hs_explosion.
        mp a.
        ax; bh; nh.
        ax; nh.
      Defined.
        
      Definition hs_and_elim_right_formula: forall a b:F,
          T|- (sf_and C a b § b).
      Proof.
        intros.
        ded.
        abs.
        ded.
        mp (a § b § wr).
        ax; bh; nh.
        mp (b § wr).
        ka.
        ax; nh.
      Defined.
      
      Definition hs_and_elim_left: forall a b:F,
          T|- sf_and C a b -> T |- a.
      Proof.
        intros.
        mp (sf_and C a b).
        apply hs_and_elim_left_formula.
        asp.
      Defined.
      
      Definition hs_and_elim_right: forall a b:F,
          T|- sf_and C a b -> T |- b.
      Proof.
        intros.
        mp (sf_and C a b).
        apply hs_and_elim_right_formula.
        asp.
      Defined.
      
      Definition hs_or_intro_l_formula: forall a b:F,
          T |- a § (sf_or C a b).
      Proof.
        intros.
        ded.
        ded.
        mp (sf_wrong C).
        apply hs_explosion_formula.
        mp a.
        ax; nh.
        ax; bh; nh.
      Defined.
      
      Definition hs_or_intro_r_formula: forall a b:F,
          T |- (b § sf_or C a b).
      Proof.
        intros.
        ka.
      Defined.

      Definition hs_or_intro_l: forall a b:F,
          T |- a -> T |- sf_or C a b.
      Proof.
        intros.
        mp a.
        apply hs_or_intro_l_formula.
        asp.
      Defined.

      Definition hs_or_intro_r: forall a b:F,
          T |- b -> T |- sf_or C a b.
      Proof.
        intros.
        mp b.
        apply hs_or_intro_r_formula.
        asp.
      Defined.

      Definition hs_peirce: forall a b:F,
          T|- ((a § b) § a) § a.
      Proof.
        intros.
        ded.
        abs.
        ded.
        mp a.
        ax; nh.
        mp (a § b).
        ax; bh; nh.
        ded.
        apply hs_explosion.
        mp a.
        ax; bh; nh.
        ax; nh.
      Defined.

      Definition hs_absurd3: forall x:F,
          (add_hyp C T (sf_neg C x)) |- x -> T |- x.
      Proof.
        intros.
        mp ((sf_neg C x) § x).
        apply hs_peirce.
        ded.
        assumption.
      Defined.
      
      Definition hs_or_elim_formula: forall a b x:F,
          T|- (a § x) § (b § x) § (sf_or C a b) § x.
      Proof.
        intros.
        ded.
        ded.
        ded.
        abs.
        ded.
        mp b.
        ded.
        mp x.
        ax; bh; nh.
        mp b.
        ax; bh; bh; bh; nh.
        mp (a § wr).
        ax; bh; bh; nh.
        ded.
        mp x.
        ax; bh; bh; nh.
        mp a.
        ax; bh; bh; bh; bh; bh; nh.
        ax; nh.
        mp (a § wr).
        ax; bh; nh.
        ded.
        mp x.
        ax; bh; nh.
        mp a.
        ax; bh; bh; bh; bh; nh.
        ax; nh.
      Defined.           
      
      Definition hs_or_elim: forall a b x:F,
          (add_hyp C T a) |- x -> (add_hyp C T b) |- x -> T |- sf_or C a b -> T |- x.
      Proof.
        intros.
        mp (sf_or C a b).
        mp (b § x).
        mp (a § x).
        apply hs_or_elim_formula.
        ded.
        asp.
        ded.
        asp.
        asp.
      Defined.

      Definition hs_equiv_symmetry_formula:
        forall a b:F,
          T|- sf_implies C (sf_equiv C a b) (sf_equiv C b a).
      Proof.
        intros.
        mp
          (sf_implies
             C
             (sf_implies C (sf_implies C b a) (sf_implies C (sf_implies C a b) (sf_wrong C)))
             (sf_implies C (sf_implies C a b) (sf_implies C (sf_implies C b a) (sf_wrong C)))
          ).
        apply hs_q_syllogism_formula.
        apply hs_permutation_formula.
      Defined.
      
      Definition hs_equiv_reflexivity: forall a :F,
          T|- sf_equiv C a a.
      Proof.
        intros.
        apply hs_and_intro.
        apply hs_identity.
        apply hs_identity.
      Defined.

      Definition hs_equiv_symmetry: forall a b:F,
          T|- sf_equiv C a b -> T|- sf_equiv C b a.
      Proof.
        intros.
        mp (sf_equiv C a b).
        apply hs_equiv_symmetry_formula.
        assumption.
      Defined.

      Definition hs_equiv_transitivity: forall a b c:F,
          T|- sf_equiv C a b -> T|- sf_equiv C b c ->  T|- sf_equiv C a c.
      Proof.
        intros.
        apply hs_and_intro.
        apply hs_syllogism with (y:=b).
        apply hs_and_elim_left with (b:= b § a).
        assumption.
        apply hs_and_elim_left with (b:= c § b).
        assumption.
        apply hs_syllogism with (y:=b).        
        apply hs_and_elim_right with (a:= b § c).
        assumption.
        apply hs_and_elim_right with (a:= a § b).
        assumption.
      Defined.
      
      Definition hs_equiv_intro: forall a b:F,
          add_hyp C T a |- b ->
                           add_hyp C T b |- a ->
                           T|- sf_equiv C a b.
      Proof.
        intros.
        apply hs_and_intro.
        ded; assumption.
        ded; assumption.
      Defined.

      Definition hs_elim_left_right: forall a b:F,
          T |- sf_equiv C a b -> T |- a -> T |- b.
      Proof.
        intros.
        mp a.
        apply hs_and_elim_left with (b:= b § a).
        assumption.
        assumption.
      Defined.

      Definition hs_elim_right_left: forall a b:F,
          T |- sf_equiv C a b -> T |- b -> T |- a.
      Proof.
        intros.
        mp b.
        apply hs_and_elim_right with (a:= a § b).
        assumption.
        assumption.
      Defined.
      
    End some_propositional_inference_rules.

    Definition hs_equiv_transitivity_formula:
      forall (C:Type) (T: Set_Formula C -> Type) (a b c:Set_Formula C),
        hs_proof C T
                 (sf_implies C (sf_equiv C a b)
                             (sf_implies C (sf_equiv C b c) (sf_equiv C a c))).
    Proof.
      intros.
      apply hs_implies_intro.
      apply hs_implies_intro.
      apply hs_equiv_transitivity with (b:=b).
      apply hs_theory_axiom.
      apply base_hyp.
      apply new_hyp.      
      apply hs_theory_axiom.
      apply new_hyp.
    Defined.

    Section some_quantifier_based_inference_rules.

      (** We now introduce some quantification rules*)
      
      Variable (C:Type).
      Variable (T:Set_Formula C -> Type).
    
      Ltac mp x:= apply hs_implies_elim with (a:=x).
      Ltac lax := apply hs_logical_axiom.
      Ltac ded := apply hs_implies_intro.
      Ltac ax := apply hs_theory_axiom.
      Ltac ka := apply hs_logical_axiom; apply K_ax.     
      Ltac sa := apply hs_logical_axiom; apply S_ax.
      Ltac abs := apply hs_absurd.
      Ltac we R:= apply hs_weakening with (T:=R).
      Ltac wet:= apply hs_weakening with (T:=T).
      Ltac bh := apply base_hyp.
      Ltac nh := apply new_hyp.
      Ltac asp := assumption.
      
      Notation F:= (Set_Formula C).  
      Notation "U |- m" := (hs_proof C U m) (at level 61).
      Notation "x § y" := (sf_implies C x y) (right associativity, at level 51).
      Notation wr := (sf_wrong C).
      
      Definition hs_forall_intro2:
        forall (a:F) (b: Set_Formula (option C)),
          hs_proof (option C)
                   (constant_theory_embedding C T)
                   (sf_implies (option C) (constant_formula_embedding C a) b) ->
          T |- a § (sf_forall C b).
      Proof.
        intros.
        ded.
        apply hs_forall_intro.
        mp (constant_formula_embedding C a).
        we (constant_theory_embedding C T).
        intros.
        destruct X0.
        apply ct_embed.
        bh; asp.
        asp.
        ax.
        apply ct_embed.
        nh.
      Defined.
      
      Definition hs_exists_elim2: 
        forall (a:F) (b: Set_Formula (option C)),
          hs_proof (option C)
                   (constant_theory_embedding C T)
                   (sf_implies (option C) b (constant_formula_embedding C a)) ->
          T |- (sf_exists C b) § a.
      Proof.
        intros.
        apply hs_syllogism with (y := sf_neg C (sf_neg C a)).
        apply hs_contraposition.
        apply hs_forall_intro2.
        assert
          (constant_formula_embedding C (sf_neg C a) =
           sf_neg (option C)(constant_formula_embedding C a)) as E.
        unfold constant_formula_embedding.
        simpl.
        reflexivity.
        rewrite E.
        apply hs_contraposition.
        asp.
        lax.
        apply ABS_ax.
      Defined.
      
      Definition hs_exists_elim: 
        forall (a:F) (b: Set_Formula (option C)),
          hs_proof C T (sf_exists C b) ->
          hs_proof (option C)
                   (add_hyp (option C) (constant_theory_embedding C T) b)
                   (constant_formula_embedding C a) ->
          T |- a.
      Proof.
        intros.
        mp (sf_exists C b).
        apply hs_exists_elim2.
        ded.
        asp.
        asp.
      Defined.
      
      Definition hs_exists_intro_formula: forall (b: Set_Formula (option C)) (t:C),
          T |- (specify C t b) § (sf_exists C b).
      Proof.
        intros.
        apply hs_syllogism with (y:= sf_neg C (specify C t (sf_neg (option C) b))).
        unfold specify.
        unfold map_specify.
        simpl.
        apply hs_double_negation_formula.
        apply hs_contraposition.
        lax.
        apply special_case_ax.
      Defined.

      Definition hs_exists_intro: forall (b: Set_Formula (option C)) (t:C),
          T |- (specify C t b) -> T |- (sf_exists C b).
      Proof.
        intros.
        mp (specify C t b).
        apply hs_exists_intro_formula.
        asp.
      Defined.

      Definition hs_double_special_case:
        forall (x y:C) (f: Set_Formula (option (option C))),
          hs_proof C T (sf_forall C (sf_forall (option C) f)) ->
          hs_proof C T (specify C x (specify (option C) (Some y) f)).
      Proof.
        intros.
        apply hs_all_elim.
        mp (sf_forall C (sf_forall (option C) f)).
        mp (sf_forall C (sf_implies (option C)
                                    (sf_forall (option C) f)
                                    (specify (option C) (Some y) f))).
        lax; apply forall_mp_ax.
        apply hs_forall_intro.
        lax; apply special_case_ax.
        assumption.
      Defined.
      
      Definition hs_reverted_forall_intro:
        forall (f: Set_Formula (option C)),
          hs_proof C T (sf_forall C f) ->
          hs_proof (option C) (constant_theory_embedding C T) f.
      Proof.
        intros.
        assert (specify
                  (option C)
                  (None)
                  (change_of_context (option C) (option (option C))
                                     (extend_map_to_bound_variables
                                        C (option C)
                                        (Some)) f) = f
               ) as E1.
        unfold specify.
        unfold map_specify.
        rewrite <- coc_composition_equality.
        apply eq_trans with
            (y:= change_of_context (option C) (option C)
                                   (fun (x: option C) => x)
                                   f
            ).
        apply coc_pointwise_equality.
        intros.
        destruct x.
        simpl.
        reflexivity.
        simpl.
        reflexivity.
        apply coc_identity_equality.
        rewrite <- E1.
        apply hs_all_elim.
        assert (sf_forall
                  (option C)
                  (change_of_context (option C)
                                     (option (option C))
                                     (extend_map_to_bound_variables C (option C) (Some))
                                     f
                  )
                =
                constant_formula_embedding C (sf_forall C f)
               ) as E2.
        unfold constant_formula_embedding.
        simpl.
        reflexivity.
        rewrite E2.
        unfold constant_formula_embedding.
        we (theory_context_change C (option C) (Some) T).
        intros.
        destruct X0.
        apply ct_embed.
        assumption.
        apply hs_proof_context_change.
        assumption.
      Defined.      


      Section forall_with_implies_and_equiv.

        Notation P:= (Set_Formula (option C)).

        Definition sf_subpredicate (f g:P):= sf_forall C (sf_implies (option C) f g).
        Definition sf_eq_predicate (f g:P):= sf_forall C (sf_equiv (option C) f g).

        Definition hs_subpredicate_reflexivity: forall f:P,
            T|- sf_subpredicate f f.
        Proof.
          intros.
          apply hs_forall_intro.
          apply hs_identity.
        Defined.

        Definition hs_subpredicate_transitivity_formula: forall (a b c:P),
            T|- sf_implies
                  C
                  (sf_subpredicate a b)
                  (sf_implies C
                              (sf_subpredicate b c)
                              (sf_subpredicate a c)
                  ).
        Proof.
          intros.
          apply hs_syllogism with
              (y:=
                 sf_forall
                   C
                   (sf_implies
                      (option C)
                      (sf_implies (option C) b c)
                      (sf_implies (option C) a c)
                   )
              ).
          mp (sf_forall
                C
                (sf_implies
                   (option C)
                   (sf_implies (option C) a b)
                   (sf_implies
                      (option C)
                      (sf_implies (option C) b c)
                      (sf_implies (option C) a c)
                   )
                )
             ).
          apply hs_logical_axiom.
          apply forall_mp_ax.
          apply hs_forall_intro.
          apply hs_q_syllogism_formula.
          apply hs_logical_axiom.
          apply forall_mp_ax.
        Defined. 
        
        Definition hs_subpredicate_transitivity: forall (a b c:P),
            T|- sf_subpredicate a b ->
                T|- sf_subpredicate b c ->
                    T|- sf_subpredicate a c.
        Proof.
          intros.
          apply hs_forall_intro.          
          apply hs_syllogism with (y:=b).
          apply hs_reverted_forall_intro.
          assumption.
          apply hs_reverted_forall_intro.
          assumption.                  
        Defined.
        
        Definition hs_eq_predicate_reflexivity: forall f:P,
            T|- sf_eq_predicate f f.
        Proof.
          intros.
          apply hs_forall_intro.
          apply hs_and_intro.
          apply hs_identity.
          apply hs_identity.
        Defined.

        Definition hs_eq_predicate_symmetry_formula: forall a b:P,
            T|- sf_implies C (sf_eq_predicate a b) (sf_eq_predicate b a).
        Proof.
          intros.
          mp (sf_forall
                C
                (sf_implies
                   (option C)
                   (sf_equiv (option C) a b)
                   (sf_equiv (option C) b a)
                )                
             ).
          lax; apply forall_mp_ax.
          apply hs_forall_intro.
          apply hs_equiv_symmetry_formula.
        Defined.  
        
        Definition hs_eq_predicate_symmetry: forall a b:P,
            T|- sf_eq_predicate a b -> T |- sf_eq_predicate b a.
        Proof.
          intros.
          mp (sf_eq_predicate a b).
          apply hs_eq_predicate_symmetry_formula.
          assumption.
        Defined.

        Definition hs_eq_predicate_transitivity_formula: forall (a b c:P),
            T|- sf_implies
                  C
                  (sf_eq_predicate a b)
                  (sf_implies C
                              (sf_eq_predicate b c)
                              (sf_eq_predicate a c)
                  ).
        Proof.
          intros.
          apply hs_syllogism with
              (y:=
                 sf_forall
                   C
                   (sf_implies
                      (option C)
                      (sf_equiv (option C) b c)
                      (sf_equiv (option C) a c)
                   )
              ).
          mp (sf_forall
                C
                (sf_implies
                   (option C)
                   (sf_equiv (option C) a b)
                   (sf_implies
                      (option C)
                      (sf_equiv (option C) b c)
                      (sf_equiv (option C) a c)
                   )
                )
             ).
          apply hs_logical_axiom.
          apply forall_mp_ax.
          apply hs_forall_intro.
          apply hs_equiv_transitivity_formula.
          apply hs_logical_axiom.
          apply forall_mp_ax.
        Defined. 

        Definition hs_eq_predicate_transitivity: forall (a b c:P),
            T|- sf_eq_predicate a b ->
                T|- sf_eq_predicate b c ->
                    T|- sf_eq_predicate a c.
        Proof.
          intros.
          apply hs_forall_intro.          
          apply hs_equiv_transitivity with (b:=b).
          apply hs_reverted_forall_intro.          
          assumption.
          apply hs_reverted_forall_intro.
          assumption.                  
        Defined. 
        
      End forall_with_implies_and_equiv.
      
    End some_quantifier_based_inference_rules.
    
    Section witnesses.

      Section the_general_case.

        Variable (C:Type).
        Variable (T:Set_Formula C -> Type).
        Variable u: Set_Formula (option C).
        Variable pex: hs_proof C T (sf_exists C u).
        
        Ltac mp x:= apply hs_implies_elim with (a:=x).
        Ltac lax := apply hs_logical_axiom.
        Ltac ded := apply hs_implies_intro.
        Ltac ax := apply hs_theory_axiom.
        Ltac ka := apply hs_logical_axiom; apply K_ax.     
        Ltac sa := apply hs_logical_axiom; apply S_ax.
        Ltac abs := apply hs_absurd.
        Ltac we R:= apply hs_weakening with (T:=R).
        Ltac wet:= apply hs_weakening with (T:=T).
        Ltac bh := apply base_hyp.
        Ltac nh := apply new_hyp.
        Ltac asp := assumption.
        
        Notation F:= (Set_Formula C).  
        Notation "U |- m" := (hs_proof C U m) (at level 61).
        Notation "x § y" := (sf_implies C x y) (right associativity, at level 51).
        Notation wr := (sf_wrong C).

        Definition hs_generic_witness_property:
          forall (g:F) (a:Set_Formula (option C)),
            hs_proof (option C)
                     (constant_theory_embedding C T)
                     (sf_implies
                        (option C)
                        (sf_implies
                           (option C)
                           a
                           (constant_formula_embedding C (sf_forall C a))
                        )
                        (constant_formula_embedding C g)) ->
            T |- g.
        Proof.
          intros.
          apply hs_absurd3.
          mp (sf_forall C a).
          mp (sf_exists C u).
          apply hs_exists_elim2.
          mp (constant_formula_embedding C ((sf_forall C a) § g)).
          ka.
          we (constant_theory_embedding C T).
          intros.
          destruct X0.
          apply ct_embed.
          bh.
          asp.
          apply hs_syllogism with
              (y:= sf_implies (option C) a (constant_formula_embedding C (sf_forall C a))).
          ka.
          simpl.
          asp.
          we T.
          bh.
          asp.
          apply hs_forall_intro.
          mp (sf_implies (option C) (sf_implies
                                        (option C)
                                        a
                                        (constant_formula_embedding C (sf_forall C a))) a).
          apply hs_peirce.
          apply hs_syllogism with (y:= constant_formula_embedding C g).
          we (constant_theory_embedding C T).
          intros.
          destruct X0.
          apply ct_embed.
          bh.
          asp.
          asp.
          ded.
          apply hs_explosion.
          mp (constant_formula_embedding C g).
          ax.
          assert (sf_implies (option C)
                             (constant_formula_embedding C g)
                             (sf_wrong (option C)) =
                  constant_formula_embedding C (sf_neg C g) 
                 ) as E.
          simpl; reflexivity.
          rewrite E.
          bh.
          apply ct_embed.
          nh.
          ax; nh.
        Defined.
        
        Definition hs_existential_witness_property:
          forall (g:F) (a:Set_Formula (option C)),
            hs_proof (option C)
                     (constant_theory_embedding C T)
                     (sf_implies
                        (option C)
                        (sf_implies
                           (option C)                         
                           (constant_formula_embedding C (sf_exists C a))
                           a
                        )
                        (constant_formula_embedding C g)) ->
            T |- g.
        Proof.
          intros.
          apply hs_generic_witness_property with (a:= sf_neg (option C) a).
          apply hs_syllogism with (y:=
                                     sf_implies
                                       (option C)                         
                                       (constant_formula_embedding C (sf_exists C a))
                                       (sf_neg (option C) (sf_neg (option C) a))
                                  ).
          unfold sf_exists; simpl.
          unfold constant_formula_embedding.
          simpl.
          apply hs_contraposition_formula.
          apply hs_syllogism with (y:=
                                     sf_implies
                                       (option C)                         
                                       (constant_formula_embedding C (sf_exists C a))
                                       a
                                  ).
          mp (sf_implies (option C)
                         (sf_neg (option C) (sf_neg (option C) a))
                         a
             ).
          apply hs_b_syllogism_formula.
          lax; apply ABS_ax.
          asp.
        Defined.

      End the_general_case.

      Section when_the_context_is_not_empty.

        Variable (C:Type).
        Variable (T:Set_Formula C -> Type).
        Variable l: C.

        Ltac mp x:= apply hs_implies_elim with (a:=x).
        Ltac lax := apply hs_logical_axiom.
        Ltac ded := apply hs_implies_intro.
        Ltac ax := apply hs_theory_axiom.
        Ltac ka := apply hs_logical_axiom; apply K_ax.     
        Ltac sa := apply hs_logical_axiom; apply S_ax.
        Ltac abs := apply hs_absurd.
        Ltac we R:= apply hs_weakening with (T:=R).
        Ltac wet:= apply hs_weakening with (T:=T).
        Ltac bh := apply base_hyp.
        Ltac nh := apply new_hyp.
        Ltac asp := assumption.
        
        Notation F:= (Set_Formula C).  
        Notation "U |- m" := (hs_proof C U m) (at level 61).
        Notation "x § y" := (sf_implies C x y) (right associativity, at level 51).
        Notation wr := (sf_wrong C).

        Definition constant_true_class:Set_Formula (option C):=
          sf_neg (option C) (sf_wrong (option C)).

        Definition non_empty_universe: T |- sf_exists C constant_true_class.
        Proof.
          apply hs_exists_intro with (t:=l).
          apply hs_all_elim.
          apply hs_forall_intro.
          unfold constant_true_class.
          apply hs_identity.
        Defined.
        
        Definition hs_generic_witness_property_with_non_empty_context:
          forall (g:F) (a:Set_Formula (option C)),
            hs_proof (option C)
                     (constant_theory_embedding C T)
                     (sf_implies
                        (option C)
                        (sf_implies
                           (option C)
                           a
                           (constant_formula_embedding C (sf_forall C a))
                        )
                        (constant_formula_embedding C g)) ->
            T |- g.
        Proof.
          apply hs_generic_witness_property with (u:= constant_true_class).
          apply non_empty_universe.
        Defined.
        
        Definition hs_existential_witness_property_with_non_empty_context:
          forall (g:F) (a:Set_Formula (option C)),
            hs_proof (option C)
                     (constant_theory_embedding C T)
                     (sf_implies
                        (option C)
                        (sf_implies
                           (option C)                         
                           (constant_formula_embedding C (sf_exists C a))
                           a
                        )
                        (constant_formula_embedding C g)) ->
            T |- g.
        Proof.
          apply hs_existential_witness_property with (u:= constant_true_class).
          apply non_empty_universe.
        Defined.
          
      End when_the_context_is_not_empty.
      
    End witnesses.
    
  End Hilbert_systems_and_natural_deduction_for_Set_Formulas.

  Section Equality_properties_and_extensionality.
    
    Section Definition_of_extensionality.

      Variable C:Type.

      Notation bel := (fun (a b:(option C)) => sf_belongs (option C) a b).

      (** two sets are said to be (extensionally) equal whenever they have the same 
      elements *)
      
      Definition sf_Leibniz_implication (x y:C):=
        sf_forall C
                  (sf_implies (option C)
                            (bel (Some x) (None))
                            (bel (Some y) (None))
                  ).


      Definition sf_Leibniz_equal (x y:C):=
        sf_forall C
                  (sf_equiv (option C)
                            (bel (Some x) (None))
                            (bel (Some y) (None))
                  ).
      
    End Definition_of_extensionality.

    Definition hs_equiv_implies_formula
               (C:Type) (T:Set_Formula C -> Type) (a a' b b':Set_Formula C):
      hs_proof
        C T
        (sf_implies C (sf_equiv C a a')
                    (sf_implies C (sf_equiv C b b')
                                (sf_equiv C (sf_implies C a b) (sf_implies C a' b')))).
    Proof.
      apply hs_implies_intro.
      apply hs_implies_intro.
      apply hs_equiv_intro.
      apply hs_implies_intro.
      apply hs_elim_left_right with (a:=b).
      apply hs_theory_axiom; apply base_hyp; apply base_hyp; apply new_hyp.
      apply hs_implies_elim with (a:=a).
      apply hs_theory_axiom; apply base_hyp; apply new_hyp.
      apply hs_elim_right_left with (b:=a').
      apply hs_theory_axiom; apply base_hyp; apply base_hyp; apply base_hyp; apply new_hyp.
      apply hs_theory_axiom; apply new_hyp.
      apply hs_implies_intro.
      apply hs_elim_right_left with (b:=b').
      apply hs_theory_axiom; apply base_hyp; apply base_hyp; apply new_hyp.
      apply hs_implies_elim with (a:=a').
      apply hs_theory_axiom; apply base_hyp; apply new_hyp.
      apply hs_elim_left_right with (a:=a).
      apply hs_theory_axiom; apply base_hyp; apply base_hyp; apply base_hyp; apply new_hyp.
      apply hs_theory_axiom; apply new_hyp.
    Defined.
     
    Definition hs_equiv_implies
               (C:Type) (T:Set_Formula C -> Type) (a a' b b':Set_Formula C):
      hs_proof C T (sf_equiv C a a') -> 
      hs_proof C T (sf_equiv C b b') ->
      hs_proof C T (sf_equiv C (sf_implies C a b) (sf_implies C a' b')).
    Proof.
      intros.
      apply hs_implies_elim with (a:= sf_equiv C b b').
      apply hs_implies_elim with (a:= sf_equiv C a a').
      apply hs_equiv_implies_formula.
      assumption.
      assumption.
    Defined.

    Definition hs_forall_equiv_formula
               (C:Type) (T: Set_Formula C -> Type)(f g:Set_Formula (option C)):
      hs_proof
        C T
        (sf_implies
           C
           (sf_forall C (sf_equiv (option C) f g))
           (sf_equiv
              C
              (sf_forall C f)
              (sf_forall C g)
           )
        ).
    Proof.
      apply hs_implies_intro.
      apply hs_and_intro.
      apply hs_implies_elim with (a:= sf_forall C (sf_implies (option C) f g)).
      apply hs_logical_axiom; apply forall_mp_ax.
      apply hs_forall_intro.
      apply hs_and_elim_left with (b:= sf_implies (option C) g f).
      apply hs_reverted_forall_intro.
      apply hs_theory_axiom; apply new_hyp.
      apply hs_implies_elim with (a:= sf_forall C (sf_implies (option C) g f)).
      apply hs_logical_axiom; apply forall_mp_ax.
      apply hs_forall_intro.
      apply hs_and_elim_right with (a:= sf_implies (option C) f g).
      apply hs_reverted_forall_intro.
      apply hs_theory_axiom; apply new_hyp.
    Defined.

    Definition hs_forall_equiv
               (C:Type) (T: Set_Formula C -> Type)(f g:Set_Formula (option C)):
      hs_proof C T (sf_forall C (sf_equiv (option C) f g)) ->
      hs_proof C T (sf_equiv C (sf_forall C f) (sf_forall C g)).           
    Proof.
      apply hs_implies_elim with (a:= sf_forall C (sf_equiv (option C) f g)).
      apply hs_forall_equiv_formula.
    Defined.  

    Definition hs_equality_reflexivity
               (C:Type) (T: Set_Formula C -> Type) (x:C):
      hs_proof C T (sf_equal C x x).
    Proof.
      apply hs_and_intro.
      apply hs_forall_intro.
      apply hs_equiv_reflexivity.
      apply hs_forall_intro.
      apply hs_equiv_reflexivity.
    Defined.
    
    Fixpoint hs_equality_general_elimination
             (C:Type)
             (f:Set_Formula C)
             (D:Type)
             (T: Set_Formula D -> Type)
             (envl envr: C -> D)
             (eqenv: forall x:C,
                 hs_proof D T (sf_equal D (envl x) (envr x)))
             {struct f}:
      hs_proof D T (sf_equiv D
                             (change_of_context C D envl f)
                             (change_of_context C D envr f)).
    Proof.
      destruct f.
      simpl.
      apply hs_equiv_transitivity with (b:= sf_belongs D (envl c) (envr c0)).
      apply hs_implies_elim with
          (a:=sf_forall D (sf_equiv
                         (option D)
                         (sf_belongs (option D) None (Some (envl c0)))
                         (sf_belongs (option D) None (Some (envr c0))))).
      apply hs_logical_axiom.
      apply special_case_ax with (t:= envl c).
      apply hs_implies_elim with (a:= sf_equal D (envl c0) (envr c0)).
      apply hs_and_elim_right_formula.
      apply eqenv.
      apply hs_implies_elim with
          (a:=sf_forall D (sf_equiv
                         (option D)
                         (sf_belongs (option D) (Some (envl c)) None)
                         (sf_belongs (option D) (Some (envr c)) None))).
      apply hs_logical_axiom.
      apply special_case_ax with (t:= envr c0).
      apply hs_implies_elim with (a:= sf_equal D (envl c) (envr c)).
      apply hs_and_elim_left_formula.
      apply eqenv.
      simpl.
      apply hs_equiv_reflexivity.
      simpl.
      apply hs_equiv_implies.
      apply hs_equality_general_elimination; assumption.
      apply hs_equality_general_elimination; assumption.
      simpl.
      apply hs_forall_equiv.
      apply hs_forall_intro.
      apply hs_equality_general_elimination.
      intros.
      simpl.
      destruct x.
      simpl.
      apply ct_embed_proof with (u:= sf_equal D (envl c) (envr c)).
      apply eqenv.
      simpl; apply hs_equality_reflexivity.
    Defined.           

    Definition hs_equality_elim:
      forall (C:Type) (T:Set_Formula C -> Type) (f:Set_Formula (option C)) (x y:C),
        hs_proof C T (sf_equal C x y) ->
        hs_proof C T (specify C x f) ->
        hs_proof C T (specify C y f).
    Proof.
      intros.
      apply hs_elim_left_right with (a:= specify C x f).
      apply hs_equality_general_elimination.
      intros; simpl.
      destruct x0.
      simpl; apply hs_equality_reflexivity.
      simpl; assumption.
      assumption.
    Defined.
      
    (** Below is the extensionality axiom (but we call it "extensionality property" 
      and save the expression "extensionality axiom" for later).*)
    
    Definition extensionality_property (C:Type):=
      sf_forall C
                (sf_forall (option C)
                           (sf_implies (option (option C))
                                     (sf_ext_equal (option (option C))
                                               (Some None)         
                                               None
                                     )
                                     (sf_Leibniz_implication (option (option C))
                                                             (Some None)         
                                                             None 
                                     )
                           )
                ).        
    
  End Equality_properties_and_extensionality.
  
  Section Equality_according_to_Leibniz.

    Ltac mp x:= apply hs_implies_elim with (a:=x).
    Ltac lax := apply hs_logical_axiom.
    Ltac ded := apply hs_implies_intro.
    Ltac ax := apply hs_theory_axiom.
    Ltac ka := apply hs_logical_axiom; apply K_ax.     
    Ltac sa := apply hs_logical_axiom; apply S_ax.
    Ltac abs := apply hs_absurd.
    Ltac we R:= apply hs_weakening with (T:=R).
    Ltac bh := apply base_hyp.
    Ltac nh := apply new_hyp.
    Ltac asp := assumption.    
    
    Definition ext_ax_context_change: forall (C D:Type) (f: C -> D),
        change_of_context C D f (extensionality_property C) = extensionality_property D.
    Proof.
      intros.
      simpl.
      reflexivity.
    Defined.

    Definition var_eq_test (C:Type) (x: option C): sum (None = x)
                                                 ((None = x) -> Empty_set).
    Proof.
      destruct x.
      right; discriminate.
      left; reflexivity.   
    Defined.

    Section equality_as_an_equivalence_relationship.

      (** the properties proven in this section don't rely on the extensionality axiom*)
      
      Definition hs_extensional_equality_reflexivity:
        forall (C:Type) (T:Set_Formula C -> Type) (x:C),
          hs_proof C T (sf_ext_equal C x x).
      Proof.
        intros.
        apply hs_eq_predicate_reflexivity.
      Defined.

      Definition hs_extensional_equality_symmetry:
        forall (C:Type) (T:Set_Formula C -> Type) (x y:C),
          hs_proof C T (sf_ext_equal C x y) ->
          hs_proof C T (sf_ext_equal C y x).
      Proof.
        intros C T x y.
        apply hs_eq_predicate_symmetry.
      Defined.
      
      Definition hs_extensional_equality_transitivity:
        forall (C:Type) (T:Set_Formula C -> Type) (x y z:C),
          hs_proof C T (sf_ext_equal C x y) ->
          hs_proof C T (sf_ext_equal C y z) ->
          hs_proof C T (sf_ext_equal C x z).
      Proof.
        intros C T x y z.
        apply hs_eq_predicate_transitivity.
      Defined.
        
    End equality_as_an_equivalence_relationship.
    
    Definition hs_set_extensional_equality_elim:
      forall (C:Type) (T:Set_Formula C -> Type) (f:Set_Formula (option C)) (x y:C),
        hs_proof C T (extensionality_property C) ->
        hs_proof C T (sf_ext_equal C x y) ->
        hs_proof C T (specify C x f) ->
        hs_proof C T (specify C y f).
    Proof.
      intros.
      apply hs_equality_elim with (x:=x).
      apply hs_and_intro.
      apply hs_forall_intro.
      apply hs_and_intro.
      apply hs_reverted_forall_intro.      
      mp (sf_ext_equal C x y).
      apply hs_double_special_case with (x:=x) (y:=y) in X.
      assumption.
      assumption.
      apply hs_reverted_forall_intro.      
      mp (sf_ext_equal C y x).
      apply hs_double_special_case with (x:=y) (y:=x) in X.
      assumption.
      apply hs_extensional_equality_symmetry.
      assumption.
      assumption.
      assumption.
    Defined.   
      
  End Equality_according_to_Leibniz.
  
End basic_definitions.

