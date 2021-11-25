Require Import SetDef.first_order_set_language.
(*Require Import propositional_implies_wrong_logic.*)

Section main.

(** We define an extended language on top of first order logic, by adding a 
constructor d_def which takes a predicate p and return a term "d_def p", whose meaning is
intended to be "the object defined by p". Axioms provided later will give it its meaning. 

Again, the formulas are implemented with the nested abstract syntax (see the first order set 
language file), relying on the option operator to introduce bound variables. 
*)
  
  Inductive D_Prop (context:Type):Type:=
  |d_belongs: (D_Term context) ->(D_Term context) -> D_Prop context
  |d_wrong: D_Prop context
  |d_implies: (D_Prop context) -> (D_Prop context) -> (D_Prop context)
  |d_forall: (D_Prop (option context)) -> (D_Prop context)
  with D_Term (context:Type):Type:=
  |d_letter: context -> D_Term context
  |d_def: (D_Prop (option context)) -> D_Term context.

  Notation DP:= D_Prop.
  Notation DT:= D_Term.

  Fixpoint sf_to_d_translation (C:Type) (f:Set_Formula C) {struct f}:DP C:=
    match f in (Set_Formula T) return (DP T) with
    | sf_belongs C0 x y => d_belongs C0 (d_letter C0 x) (d_letter C0 y)
    | sf_wrong C0 => d_wrong C0
    | sf_implies C0 a b =>
      d_implies C0 (sf_to_d_translation C0 a) (sf_to_d_translation C0 b)
    | sf_forall C0 g => d_forall C0 (sf_to_d_translation (option C0) g)
    end.
  
  Definition d_neg (C:Type) (a:DP C):(DP C):= d_implies C a (d_wrong C).
  Definition d_true (C:Type): (DP C):= d_neg C (d_wrong C).
  Definition d_or (C:Type) (a b:DP C):(DP C):= d_implies C (d_neg C a) b.
  Definition d_and (C:Type) (a b:DP C):(DP C):= d_neg C (d_implies C a (d_neg C b)).
  Definition d_equiv (C:Type) (a b:DP C):DP C:= d_and C (d_implies C a b) (d_implies C b a).
  Definition d_exists (C:Type) (f:DP (option C)):DP C:=
    d_neg C (d_forall C (d_neg (option C) f)).

  (** The rest of this file deals with substitution of variable and establishes syntactic 
     equalities between objects when various transformations are applied to them. *)
  
  Fixpoint d_prop_change_of_context (C:Type) (f:DP C) (D:Type) (env:C -> D) {struct f}:
    DP D:=
    match f with
    | d_belongs _ b b0 =>
      d_belongs D (d_term_change_of_context C b D env) (d_term_change_of_context C b0 D env)
    | d_wrong _ => d_wrong D
    | d_implies _ f1 f2 =>
      d_implies D (d_prop_change_of_context C f1 D env)
                (d_prop_change_of_context C f2 D env)
    | d_forall _ f0 =>
      d_forall D
               (d_prop_change_of_context
                  (option C) f0 (option D)
                  (option_rect (fun _ : option C => option D)
                               (fun a : C => Some (env a)) None))
    end
  with d_term_change_of_context
         (C : Type) (t : DT C) (D : Type) (env : C -> D) {struct t}:
         DT D :=
         match t with
         | d_letter _ c => d_letter D (env c)
         | d_def _ b =>
           d_def
             D
             (d_prop_change_of_context
                (option C) b (option D)
                (option_rect (fun _ : option C => option D) (fun a : C => Some (env a)) None))
         end.

  Section change_of_context_equality_tools.

    Fixpoint d_prop_coc_pointwise_equality
             (C:Type) (p:DP C) (D:Type) (env1 env2: C -> D)
             (eqenv: forall x:C, env1 x = env2 x){struct p}:
      d_prop_change_of_context C p D env1 = d_prop_change_of_context C p D env2
    with d_term_coc_pointwise_equality
           (C:Type) (t:DT C) (D:Type) (env1 env2: C -> D)
           (eqenv: forall x:C, env1 x = env2 x){struct t}:
           d_term_change_of_context C t D env1 = d_term_change_of_context C t D env2.
    Proof.
      destruct p.
      simpl; repeat rewrite d_term_coc_pointwise_equality with (env1:=env1) (env2 := env2).
      reflexivity. assumption. assumption.
      simpl; reflexivity.
      simpl; repeat rewrite d_prop_coc_pointwise_equality with (env1:=env1) (env2 := env2).
      reflexivity. assumption. assumption.
      simpl; apply f_equal; apply d_prop_coc_pointwise_equality.
      intros. destruct x. simpl. apply f_equal; apply eqenv. reflexivity.
      destruct t. simpl. apply f_equal; apply eqenv.
      simpl; apply f_equal; apply d_prop_coc_pointwise_equality.
      intros. destruct x. simpl. apply f_equal; apply eqenv. reflexivity.
    Defined.           
    
      Fixpoint d_prop_coc_composition_equality
               (C:Type) (p: DP C) (D E:Type) (env_cd: C -> D) (env_de: D -> E)
               {struct p}:
        d_prop_change_of_context C p E (fun v:C => env_de (env_cd v)) =
        d_prop_change_of_context D (d_prop_change_of_context C p D env_cd) E env_de
      with d_term_coc_composition_equality
               (C:Type) (t: DT C) (D E:Type) (env_cd: C -> D) (env_de: D -> E)
               {struct t}:
        d_term_change_of_context C t E (fun v:C => env_de (env_cd v)) =
        d_term_change_of_context D (d_term_change_of_context C t D env_cd) E env_de.
      Proof.
        destruct p.
        simpl; repeat rewrite <- d_term_coc_composition_equality; reflexivity.
        simpl; reflexivity.
        simpl; repeat rewrite <- d_prop_coc_composition_equality; reflexivity.
        simpl; apply f_equal. rewrite <- d_prop_coc_composition_equality.
        apply d_prop_coc_pointwise_equality.
        intros.
        destruct x.
        simpl; reflexivity.
        simpl; reflexivity.
        destruct t.
        simpl; reflexivity.
        simpl; apply f_equal. rewrite <- d_prop_coc_composition_equality.
        apply d_prop_coc_pointwise_equality.
        intros.
        destruct x.
        simpl; reflexivity.
        simpl; reflexivity.
      Defined.      
      
      Fixpoint d_prop_coc_identity_equality
               (C:Type) (p:DP C) 
               {struct p}:
        d_prop_change_of_context C p C (fun v:C => v) = p
      with d_term_coc_identity_equality
             (C:Type) (t:DT C) 
             {struct t}:
             d_term_change_of_context C t C (fun v:C => v) = t.
      Proof.
        destruct p.
        simpl; repeat rewrite d_term_coc_identity_equality; reflexivity.
        simpl; reflexivity.
        simpl; repeat rewrite d_prop_coc_identity_equality; reflexivity.
        simpl; rewrite d_prop_coc_pointwise_equality with (env2 := fun v:option C => v).
        apply f_equal. apply d_prop_coc_identity_equality.
        intros. destruct x. simpl; reflexivity. simpl; reflexivity.
        destruct t.
        simpl; reflexivity.
        simpl; rewrite d_prop_coc_pointwise_equality with (env2 := fun v:option C => v).
        apply f_equal. apply d_prop_coc_identity_equality.
        intros. destruct x. simpl; reflexivity. simpl; reflexivity.
      Defined.  
      
  End change_of_context_equality_tools.
  
  Definition d_prop_constant_embedding (C:Type) (f: DP C):DP (option C):=
    d_prop_change_of_context C f (option C) Some.
  
  Definition d_term_constant_embedding (C:Type) (t: DT C):DT (option C):=
    d_term_change_of_context C t (option C) Some.

  Definition d_equal (C:Type) (x y:DT C):DP C:=
    d_and
      C
      (d_forall
         C
         (d_equiv
            (option C)                  
            (d_belongs (option C) (d_term_constant_embedding C x) (d_letter (option C) None))
            (d_belongs (option C) (d_term_constant_embedding C y) (d_letter (option C) None))
         )
      )
    (d_forall
         C
         (d_equiv
            (option C)                  
            (d_belongs (option C) (d_letter (option C) None) (d_term_constant_embedding C x))
            (d_belongs (option C) (d_letter (option C) None) (d_term_constant_embedding C y))
         )
      ).

  Definition d_ext_equal (C:Type) (x y:DT C):DP C:=
    d_forall
      C
      (d_equiv
         (option C)                  
         (d_belongs (option C) (d_letter (option C) None) (d_term_constant_embedding C x))
         (d_belongs (option C) (d_letter (option C) None) (d_term_constant_embedding C y))
      ).
  
  Section further_def_language_definitions.

    Variable C:Type.

    Notation F:= (D_Prop C).
    Notation P:= (D_Prop (option C)).

    Notation forall_x := (d_forall C).
    Notation forall_y := (d_forall (option C)).
    
    Notation C' := (option C).
    Notation C'' := (option (option C)).
    
    Notation X:= (None).
    Notation x:= (Some (None)).
    Notation y:= (None).
    Notation t2:= (d_letter (option (option C))).
    
    Notation var_embed2 := (fun (a:C) => Some (Some a)).

    Notation d_map_specify:=
      (fun (M N:Type) (e: M -> N) (s:N) (f:DP (option M)) => 
        d_prop_change_of_context (option M) f N (option_rect (fun _:option M => N) e s)).
    
    Definition d_unique (A:P):=
      forall_x
        (forall_y
           (d_implies
              C''
              (d_map_specify C C'' var_embed2 x A)
              (d_implies
                 C''
                 (d_map_specify C C'' var_embed2 y A)
                 (d_equal C'' (t2 x) (t2 y))
              ) 
           )
        ).

    Definition d_exists_unique (A: D_Prop (option C)):=
      d_and C (d_exists C A) (d_unique A). 
    
  End further_def_language_definitions.
    
  Fixpoint d_prop_substitution (C:Type) (f:DP C) (D:Type) (env:C -> DT D) {struct f}:
    DP D:=
    match f with
    | d_belongs _ b b0 =>
      d_belongs D (d_term_substitution C b D env) (d_term_substitution C b0 D env)
    | d_wrong _ => d_wrong D
    | d_implies _ f1 f2 =>
      d_implies D (d_prop_substitution C f1 D env)
                (d_prop_substitution C f2 D env)
    | d_forall _ f0 =>
      d_forall D
               (d_prop_substitution
                  (option C) f0 (option D)
                  (option_rect (fun _ : option C => DT (option D))
                               (fun a : C => d_term_constant_embedding D (env a))
                               (d_letter (option D) None)))
    end
  with d_term_substitution
         (C : Type) (t : DT C) (D : Type) (env : C -> DT D) {struct t}:
         DT D :=
         match t with
         | d_letter _ c => env c
         | d_def _ b =>
           d_def
             D
             (d_prop_substitution
                (option C) b (option D)
                (option_rect (fun _ : option C => DT (option D))
                             (fun a : C => d_term_constant_embedding D (env a))
                             (d_letter (option D) None)))
         end.
  
  Definition d_prop_specify (C:Type) (t: DT C) (f:DP (option C)):DP C:=
    d_prop_substitution (option C) f C
                          (option_rect (fun _: option C => DT C)
                                       (d_letter C)
                                       t
                          ).
  
  Definition d_term_specify (C:Type) (t: DT C) (s:DT (option C)):DT C:=
    d_term_substitution (option C) s C
                          (option_rect (fun _: option C => DT C)
                                       (d_letter C)
                                       t
                          ).
  Section change_of_context_and_substitution_for_theories.

    Variable C: Type.
    Variable T: DP C -> Type.

    Inductive d_theory_context_change (D:Type) (env: C -> D): DP D -> Type:=
      dtcc_intro: forall p:DP C,
        T p -> d_theory_context_change D env (d_prop_change_of_context C p D env).


    Inductive d_theory_substitution (D:Type) (env: C -> DT D): DP D -> Type:=
      dtsubst_intro: forall p:DP C,
        T p -> d_theory_substitution D env (d_prop_substitution C p D env).
    
  End change_of_context_and_substitution_for_theories.

  
  Section double_substitution_and_relationship_between_variable_change_and_substitution.

    Fixpoint d_prop_coc_subst_equal (C:Type) (p:DP C)
             (D:Type) (envc: C -> D) (envt: C -> DT D)
             (eqenv: forall x:C, d_letter D (envc x) = envt x){struct p}:
      d_prop_change_of_context C p D envc = d_prop_substitution C p D envt
    with
    d_term_coc_subst_equal (C:Type) (t:DT C)
                         (D:Type) (envc: C -> D) (envt: C -> DT D)
                         (eqenv: forall x:C, d_letter D (envc x) = envt x){struct t}:
      d_term_change_of_context C t D envc = d_term_substitution C t D envt.
    Proof.
      destruct p.
      simpl.
      repeat rewrite d_term_coc_subst_equal with (envt := envt). reflexivity. assumption.
      assumption. simpl. reflexivity.
      simpl. apply f_equal2. apply d_prop_coc_subst_equal with (envt := envt).
      assumption. apply d_prop_coc_subst_equal with (envt := envt).
      assumption.
      simpl. apply f_equal. apply d_prop_coc_subst_equal.
      intros. destruct x. unfold d_term_constant_embedding.
      simpl.  rewrite <- eqenv. simpl. reflexivity. simpl; reflexivity.
      destruct t. simpl. apply eqenv. simpl. apply f_equal.
      apply d_prop_coc_subst_equal.
      intros. destruct x. unfold d_term_constant_embedding.
      simpl.  rewrite <- eqenv. simpl. reflexivity. simpl; reflexivity.
    Defined.

    Fixpoint d_prop_subst_pointwise_equality
             (C:Type) (p: DP C) (D:Type) (env1 env2: C -> DT D)
             (eqenv: forall x:C, env1 x = env2 x) {struct p}:
      d_prop_substitution C p D env1 = d_prop_substitution C p D env2
    with d_term_subst_pointwise_equality
             (C:Type) (t: DT C) (D:Type) (env1 env2: C -> DT D)
             (eqenv: forall x:C, env1 x = env2 x) {struct t}:
           d_term_substitution C t D env1 = d_term_substitution C t D env2.
    Proof.
      destruct p.
      simpl. 
      repeat rewrite d_term_subst_pointwise_equality with (env1 := env1) (env2 := env2).
      reflexivity. apply eqenv. apply eqenv.
      simpl; reflexivity.
      simpl; repeat rewrite d_prop_subst_pointwise_equality with (env1 := env1) (env2 := env2).
      reflexivity. assumption. assumption.
      simpl. apply f_equal. apply d_prop_subst_pointwise_equality.
      intros; destruct x. simpl; rewrite eqenv; reflexivity. simpl; reflexivity.
      destruct t.
      simpl; apply eqenv.
      simpl. apply f_equal. apply d_prop_subst_pointwise_equality.
      intros; destruct x. simpl; rewrite eqenv; reflexivity. simpl; reflexivity.
    Defined.

    Fixpoint d_prop_subst_identity_equality
             (C:Type) (p: DP C) {struct p}:
      d_prop_substitution C p C (d_letter C) = p
    with d_term_subst_identity_equality
             (C:Type) (t: DT C) {struct t}:
           d_term_substitution C t C (d_letter C) = t.
    Proof.
      destruct p.
      simpl; repeat rewrite d_term_subst_identity_equality; reflexivity.
      simpl; reflexivity.
      simpl; repeat rewrite d_prop_subst_identity_equality; reflexivity.
      simpl; apply f_equal.
      rewrite d_prop_subst_pointwise_equality with (env2 := d_letter (option C)).
      apply d_prop_subst_identity_equality.
      intros; destruct x. simpl; reflexivity. simpl; reflexivity.
      destruct t.
      simpl; reflexivity.
      simpl; apply f_equal.
      rewrite d_prop_subst_pointwise_equality with (env2 := d_letter (option C)).
      apply d_prop_subst_identity_equality.
      intros; destruct x. simpl; reflexivity. simpl; reflexivity.
    Defined.           

    Fixpoint d_prop_coc_subst_commutation
             (C:Type) (p: DP C) (Co D Do:Type)
             (env_var_cco: C -> Co) (env_var_ddo: D -> Do)
             (env_term_cd: C -> DT D) (env_term_codo: Co -> DT Do)
             (eqenv: forall x:C,
                 env_term_codo (env_var_cco x) =
                 d_term_change_of_context D (env_term_cd x) Do env_var_ddo)
             {struct p}:
      d_prop_substitution Co (d_prop_change_of_context C p Co env_var_cco) Do env_term_codo = 
      d_prop_change_of_context D (d_prop_substitution C p D env_term_cd) Do env_var_ddo
    with d_term_coc_subst_commutation
             (C:Type) (t: DT C) (Co D Do:Type)
             (env_var_cco: C -> Co) (env_var_ddo: D -> Do)
             (env_term_cd: C -> DT D) (env_term_codo: Co -> DT Do)
             (eqenv: forall x:C,
                 env_term_codo (env_var_cco x) =
                 d_term_change_of_context D (env_term_cd x) Do env_var_ddo)
             {struct t}:
      d_term_substitution Co (d_term_change_of_context C t Co env_var_cco) Do env_term_codo = 
      d_term_change_of_context D (d_term_substitution C t D env_term_cd) Do env_var_ddo.
    Proof.
      destruct p. 
      simpl; apply f_equal2. apply d_term_coc_subst_commutation. assumption.
      apply d_term_coc_subst_commutation. assumption.
      simpl; reflexivity.
      simpl; apply f_equal2. apply d_prop_coc_subst_commutation. assumption.
      apply d_prop_coc_subst_commutation. assumption.
      simpl; apply f_equal. apply d_prop_coc_subst_commutation. intros. destruct x.
      simpl. unfold d_term_constant_embedding. rewrite eqenv.
      repeat rewrite <- d_term_coc_composition_equality. 
      apply d_term_coc_pointwise_equality.
      intros. simpl; reflexivity.
      simpl; reflexivity.
      destruct t.
      simpl; apply eqenv.
      simpl; apply f_equal. apply d_prop_coc_subst_commutation. intros. destruct x.
      simpl. unfold d_term_constant_embedding. rewrite eqenv.
      repeat rewrite <- d_term_coc_composition_equality. 
      apply d_term_coc_pointwise_equality.
      intros. simpl; reflexivity.
      simpl; reflexivity.
    Defined.       
      
    Fixpoint d_prop_double_substitution
             (C:Type) (p: DP C) (D E:Type) (envcd: C -> DT D) (envde: D -> DT E)
             {struct p}:
      d_prop_substitution D (d_prop_substitution C p D envcd) E envde =
      d_prop_substitution C p E (fun l:C => d_term_substitution D (envcd l) E envde)
    with d_term_double_substitution
             (C:Type) (t: DT C) (D E:Type) (envcd: C -> DT D) (envde: D -> DT E)
             {struct t}:
      d_term_substitution D (d_term_substitution C t D envcd) E envde =
      d_term_substitution C t E (fun l:C => d_term_substitution D (envcd l) E envde).
    Proof.
      destruct p.
      simpl. repeat rewrite d_term_double_substitution. reflexivity.
      simpl; reflexivity.
      simpl; repeat rewrite d_prop_double_substitution. reflexivity.
      simpl. rewrite d_prop_double_substitution. 
      apply f_equal. apply d_prop_subst_pointwise_equality.
      intros; destruct x. simpl. unfold d_term_constant_embedding.
      apply d_term_coc_subst_commutation.
      intros. simpl; reflexivity. simpl; reflexivity.
      destruct t.
      simpl; reflexivity.
      simpl. rewrite d_prop_double_substitution. 
      apply f_equal. apply d_prop_subst_pointwise_equality.
      intros; destruct x. simpl. unfold d_term_constant_embedding.
      apply d_term_coc_subst_commutation.
      intros. simpl; reflexivity. simpl; reflexivity.
    Defined.
             
  End double_substitution_and_relationship_between_variable_change_and_substitution.
  
  Section addendum_to_set_language.

    Variable C:Type.    
    
    Inductive sf_term:Type:=
    |sf_letter: C -> sf_term
    |sf_predicate: Set_Formula (option C) -> sf_term.
              
  End addendum_to_set_language.

  Section exist_unique_translation_tools.
    
    Definition d_exun_belongs_letter_prop (C:Type) (k x:C) (P:DP (option C)):DP C:=
      d_and
        C
        (d_implies
           C
           (d_exists_unique C P)
           (d_forall C (d_implies (option C) P (d_belongs
                                                  (option C)
                                                  (d_letter (option C) (Some x))
                                                  (d_letter (option C) None)
        ))))
        (d_implies
           C
           (d_neg C (d_exists_unique C P))
           (d_belongs C (d_letter C x) (d_letter C k))
        ).

    Definition d_exun_belongs_letter_term (C:Type) (k x:C) (t:DT C):DP C:=
      match t with
      |d_letter _ y => d_belongs C (d_letter C x) (d_letter C y)
      |d_def _ P => d_exun_belongs_letter_prop C k x P
      end.
    
    Definition d_exun_belongs_prop_term (C:Type) (k:C) (Q:DP (option C)) (t:DT C):DP C:=
      d_and
        C
        (d_implies
           C
           (d_exists_unique C Q)
           (d_forall C (d_implies (option C) Q (d_exun_belongs_letter_term 
                                                  (option C)
                                                  (Some k)
                                                  None
                                                  (d_term_constant_embedding C t)
        ))))
        (d_implies
           C
           (d_neg C (d_exists_unique C Q))
           (d_exun_belongs_letter_term C k k t)
        ).

    Definition d_exun_belongs_term_term (C:Type) (k:C) (t u: DT C):DP C:=
      match t with
      |d_letter _ x => d_exun_belongs_letter_term C k x u
      |d_def _ P => d_exun_belongs_prop_term C k P u
      end. 
    
    Definition sf_exun_belongs_letter_prop
               (C:Type) (k x:C) (P:Set_Formula (option C)):Set_Formula C:=
      sf_and
        C
        (sf_implies
           C
           (sf_exists_unique C P)
           (sf_forall C (sf_implies (option C) P (sf_belongs
                                                    (option C)
                                                    (Some x)
                                                    None
        ))))
        (sf_implies
           C
           (sf_neg C (sf_exists_unique C P))
           (sf_belongs C x k)
        ).

    Definition sf_exun_belongs_letter_term (C:Type) (k x:C) (t:sf_term C):Set_Formula C:=
      match t with
      |sf_letter _ y => sf_belongs C x y
      |sf_predicate _ P => sf_exun_belongs_letter_prop C k x P
      end.

    Definition sf_term_change_of_context (C D:Type) (env: C -> D) (t:sf_term C):sf_term D:=
      match t with
      |sf_letter _ l => sf_letter D (env l)
      |sf_predicate _ f => sf_predicate
                             D
                             (change_of_context
                                (option C) (option D)
                                (extend_map_to_bound_variables C D env) f)
      end.
    
    Definition sf_term_constant_embedding (C:Type):sf_term C -> sf_term (option C):=
      sf_term_change_of_context C (option C) Some.
      
    Definition sf_exun_belongs_prop_term
               (C:Type) (k:C) (Q:Set_Formula (option C)) (t:sf_term C):Set_Formula C:=
      sf_and
        C
        (sf_implies
           C
           (sf_exists_unique C Q)
           (sf_forall C (sf_implies (option C) Q (sf_exun_belongs_letter_term 
                                                    (option C)
                                                    (Some k)
                                                    None
                                                    (sf_term_constant_embedding C t)
        ))))
        (sf_implies
           C
           (sf_neg C (sf_exists_unique C Q))
           (sf_exun_belongs_letter_term C k k t)
        ).

    Definition sf_exun_belongs_term_term (C:Type) (k:C) (t u: sf_term C):Set_Formula C:=
      match t with
      |sf_letter _ x => sf_exun_belongs_letter_term C k x u
      |sf_predicate _ P => sf_exun_belongs_prop_term C k P u
      end. 

    Fixpoint d_exun_translation_prop (C:Type) (k:C) (p:DP C) {struct p}:Set_Formula C:=
      match p with
      |d_belongs _ t u => sf_exun_belongs_term_term
                            C k (d_exun_translation_term C k t) (d_exun_translation_term C k u)
      |d_wrong _ => sf_wrong C
      |d_implies _ q r => sf_implies
                            C (d_exun_translation_prop C k q) (d_exun_translation_prop C k r)
      |d_forall _ s => sf_forall C (d_exun_translation_prop (option C) (Some k) s)    
      end
    with d_exun_translation_term (C:Type) (k:C) (t: DT C){struct t}:sf_term C:=
           match t with
           | d_letter _ l => sf_letter C l
           | d_def _ f => sf_predicate C (d_exun_translation_prop (option C) (Some k) f)
           end.
    
    Definition d_to_sf_exun_equal_eq: forall (C:Type) (k x y:C),
        d_exun_translation_prop C k (d_equal C (d_letter C x) (d_letter C y)) =
        sf_equal C x y.
    Proof.
      intros.
      simpl; reflexivity.
    Defined.

    Definition coc_sf_exun_belongs_letter_prop_eq:
      forall (C D:Type) (env: C -> D) (k:C) (x:C) (p: Set_Formula (option C)),
        change_of_context C D env (sf_exun_belongs_letter_prop C k x p) =
        sf_exun_belongs_letter_prop
          D (env k)
          (env x) (change_of_context (option C) (option D)
                                     (extend_map_to_bound_variables C D env) p).
    Proof.
      intros.
      assert (
          change_of_context
            (option (option C)) (option (option D))
            (option_rect
               (fun _ : option (option C) => option (option D))
               (fun a : option C =>
                  Some
                    (option_rect
                       (fun _ : option C => option D) (fun a0 : C => Some (env a0)) None a))
               None)
            (change_of_context
               (option C) (option (option C))
               (option_rect
                  (fun _ : option C => option (option C)) (fun a : C => Some (Some a))
                  (Some None)) p) =
          change_of_context
            (option D) (option (option D))
            (option_rect (fun _ : option D => option (option D)) (fun a : D => Some (Some a))
                         (Some None))
            (change_of_context
               (option C) (option D)
               (option_rect (fun _ : option C => option D) (fun a : C => Some (env a)) None) p)
        ) as E1.
      rewrite <- coc_composition_equality.
      rewrite <- coc_composition_equality.
      apply coc_pointwise_equality.
      intros.
      destruct x0.
      simpl; reflexivity.
      simpl; reflexivity.
      assert (
          change_of_context
            (option (option C)) (option (option D))
            (option_rect 
               (fun _ : option (option C) => option (option D))
               (fun a : option C =>
                  Some (option_rect
                          (fun _ : option C => option D) (fun a0 : C => Some (env a0)) None a))
               None)
            (change_of_context
               (option C) (option (option C))
               (option_rect (
                    fun _ : option C => option (option C)) (fun a : C => Some (Some a)) None)
               p) =
          change_of_context
            (option D) (option (option D))
            (option_rect
               (fun _ : option D => option (option D)) (fun a : D => Some (Some a)) None)
            (change_of_context
               (option C) (option D)
               (option_rect (fun _ : option C => option D) (fun a : C => Some (env a)) None) p)
        ) as E2.
      rewrite <- coc_composition_equality.
      rewrite <- coc_composition_equality.
      apply coc_pointwise_equality.
      intros.
      destruct x0.
      simpl; reflexivity.
      simpl; reflexivity.
      simpl.
      unfold extend_map_to_bound_variables.
      unfold sf_exun_belongs_letter_prop.
      unfold sf_exists_unique.
      unfold sf_unique.
      unfold sf_exists.
      simpl.
      unfold sf_and.
      unfold sf_neg.
      rewrite E1. rewrite E2.
      reflexivity.
    Defined.
    
    Definition coc_sf_exun_belongs_letter_term_eq:
      forall (C D:Type) (env: C -> D) (k:C) (x:C) (t: sf_term C),
        change_of_context C D env (sf_exun_belongs_letter_term C k x t) =
        sf_exun_belongs_letter_term
          D (env k)
          (env x) (sf_term_change_of_context C D env t).
    Proof.
      intros.
      destruct t.
      simpl; reflexivity.
      unfold sf_exun_belongs_letter_term.
      rewrite coc_sf_exun_belongs_letter_prop_eq.
      reflexivity.
    Defined.

    Definition coc_sf_exun_belongs_prop_term_eq:
      forall (C D:Type) (env: C -> D) (k:C) (p:Set_Formula (option C)) (t: sf_term C),
        change_of_context C D env (sf_exun_belongs_prop_term C k p t) =
        sf_exun_belongs_prop_term
          D (env k)
          (change_of_context (option C) (option D) (extend_map_to_bound_variables C D env) p)
          (sf_term_change_of_context C D env t).
    Proof.
      intros.
      assert (
          change_of_context
            (option (option C)) (option (option D))
            (option_rect
               (fun _ : option (option C) => option (option D))
               (fun a : option C =>
                  Some
                    (option_rect
                       (fun _ : option C => option D) (fun a0 : C => Some (env a0)) None a))
               None)
            (change_of_context
               (option C) (option (option C))
               (option_rect
                  (fun _ : option C => option (option C)) (fun a : C => Some (Some a))
                  (Some None)) p) =
          change_of_context
            (option D) (option (option D))
            (option_rect (fun _ : option D => option (option D)) (fun a : D => Some (Some a))
                         (Some None))
            (change_of_context
               (option C) (option D)
               (option_rect (fun _ : option C => option D) (fun a : C => Some (env a)) None) p)
        ) as E1.
      rewrite <- coc_composition_equality.
      rewrite <- coc_composition_equality.
      apply coc_pointwise_equality.
      intros.
      destruct x.
      simpl; reflexivity.
      simpl; reflexivity.
      assert (
          change_of_context
            (option (option C)) (option (option D))
            (option_rect 
               (fun _ : option (option C) => option (option D))
               (fun a : option C =>
                  Some (option_rect
                          (fun _ : option C => option D) (fun a0 : C => Some (env a0)) None a))
               None)
            (change_of_context
               (option C) (option (option C))
               (option_rect (
                    fun _ : option C => option (option C)) (fun a : C => Some (Some a)) None)
               p) =
          change_of_context
            (option D) (option (option D))
            (option_rect
               (fun _ : option D => option (option D)) (fun a : D => Some (Some a)) None)
            (change_of_context
               (option C) (option D)
               (option_rect (fun _ : option C => option D) (fun a : C => Some (env a)) None) p)
        ) as E2.
      rewrite <- coc_composition_equality.
      rewrite <- coc_composition_equality.
      apply coc_pointwise_equality.
      intros.
      destruct x.
      simpl; reflexivity.
      simpl; reflexivity.
      assert
        (
          sf_term_change_of_context
            (option C) (option D)
            (option_rect (fun _ : option C => option D) (fun a : C => Some (env a)) None)
            (sf_term_constant_embedding C t) =
          sf_term_constant_embedding D (sf_term_change_of_context C D env t)
        ) as E3.
      destruct t.
      simpl; reflexivity.
      simpl. apply f_equal.
      rewrite <- coc_composition_equality.
      rewrite <- coc_composition_equality.
      apply coc_pointwise_equality.
      intros.
      destruct x.
      simpl; reflexivity.
      simpl; reflexivity.      
      unfold sf_exun_belongs_prop_term.     
      simpl.
      repeat rewrite coc_sf_exun_belongs_letter_term_eq.
      unfold extend_map_to_bound_variables.
      unfold sf_exun_belongs_letter_prop.
      unfold sf_exists_unique.
      unfold sf_unique.
      unfold sf_exists.
      simpl.
      unfold sf_and.
      unfold sf_neg.
      rewrite E1.
      rewrite E2.
      rewrite E3.
      reflexivity.
    Defined.
    
    Definition coc_sf_exun_belongs_term_term_eq:
      forall (C D:Type) (env: C -> D) (k:C) (s t:sf_term C),
        change_of_context C D env (sf_exun_belongs_term_term C k s t) =
        sf_exun_belongs_term_term
          D (env k)
          (sf_term_change_of_context C D env s) (sf_term_change_of_context C D env t).
    Proof.
      intros.
      destruct s.
      apply coc_sf_exun_belongs_letter_term_eq.
      apply coc_sf_exun_belongs_prop_term_eq.
    Defined.
    
    Fixpoint d_to_sf_exun_coc_prop_eq (C:Type) (p: DP C) (k:C) (D:Type) (env: C -> D) {struct p}:
      change_of_context C D env (d_exun_translation_prop C k p) =
      d_exun_translation_prop D (env k) (d_prop_change_of_context C p D env)
    with
    d_to_sf_exun_coc_term_eq (C:Type) (t: DT C) (k:C) (D:Type) (env: C -> D) {struct t}:
      sf_term_change_of_context C D env (d_exun_translation_term C k t) =
      d_exun_translation_term D (env k) (d_term_change_of_context C t D env).
    Proof.
      destruct p.
      simpl.
      rewrite coc_sf_exun_belongs_term_term_eq.
      rewrite d_to_sf_exun_coc_term_eq.
      rewrite d_to_sf_exun_coc_term_eq.
      reflexivity.
      simpl; reflexivity.
      simpl.
      rewrite d_to_sf_exun_coc_prop_eq.
      rewrite d_to_sf_exun_coc_prop_eq.
      reflexivity.
      simpl.
      apply f_equal.
      apply d_to_sf_exun_coc_prop_eq.
      destruct t.
      simpl; reflexivity.
      simpl.
      apply f_equal.
      apply d_to_sf_exun_coc_prop_eq.
    Defined.
    
    Definition d_to_sf_exun_unique_eq: forall (C:Type) (k:C) (f: DP (option C)),
        d_exun_translation_prop C k (d_unique C f) =
        sf_unique C (d_exun_translation_prop (option C) (Some k) f).
    Proof.
      intros.
      unfold sf_unique.
      rewrite <- d_to_sf_exun_equal_eq with (k:= Some (Some k)).
      unfold d_unique.
      simpl.
      repeat rewrite d_to_sf_exun_coc_prop_eq.
      reflexivity.
    Defined.

    Definition d_to_sf_exun_exists_eq: forall (C:Type) (k:C) (f: DP (option C)),
        d_exun_translation_prop C k (d_exists C f) =
        sf_exists C (d_exun_translation_prop (option C) (Some k) f).
    Proof.
      intros.
      simpl.
      repeat rewrite d_to_sf_exun_coc_prop_eq.
      reflexivity.
    Defined.

    Definition d_to_sf_exun_and_eq: forall (C:Type) (k:C) (p q:DP C),
            d_exun_translation_prop C k (d_and C p q) =
            sf_and C (d_exun_translation_prop C k p) (d_exun_translation_prop C k q).
    Proof.
      intros. simpl; reflexivity.
    Defined.

    Definition d_to_sf_exun_neg_eq: forall (C:Type) (k:C) (p:DP C),
            d_exun_translation_prop C k (d_neg C p) =
            sf_neg C (d_exun_translation_prop C k p).
    Proof.
      intros. simpl; reflexivity.
    Defined.

    Definition d_to_sf_exun_implies_eq: forall (C:Type) (k:C) (p q:DP C),
            d_exun_translation_prop C k (d_implies C p q) =
            sf_implies C (d_exun_translation_prop C k p) (d_exun_translation_prop C k q).
    Proof.
      intros. simpl; reflexivity.
    Defined.

    Definition d_to_sf_exun_equiv_eq: forall (C:Type) (k:C) (p q:DP C),
            d_exun_translation_prop C k (d_equiv C p q) =
            sf_equiv C (d_exun_translation_prop C k p) (d_exun_translation_prop C k q).
    Proof.
      intros. simpl; reflexivity.
    Defined.
    
    Definition d_to_sf_exun_forall_eq: forall (C:Type) (k:C) (f:DP (option C)),
            d_exun_translation_prop C k (d_forall C f) =
            sf_forall C (d_exun_translation_prop (option C) (Some k) f).
    Proof.
      intros. simpl; reflexivity.
    Defined.
    
    Definition d_to_sf_exun_exists_unique_eq: forall (C:Type) (k:C) (f: DP (option C)),
        d_exun_translation_prop C k (d_exists_unique C f) =
        sf_exists_unique C (d_exun_translation_prop (option C) (Some k) f).
    Proof.
      intros.
      unfold d_exists_unique.
      rewrite d_to_sf_exun_and_eq.
      unfold sf_exists_unique.
      rewrite d_to_sf_exun_unique_eq.
      rewrite d_to_sf_exun_exists_eq.
      reflexivity.
    Defined.

    Definition d_to_sf_exun_belongs_eq: forall (C:Type) (k:C) (s t:DT C),
        d_exun_translation_prop C k (d_belongs C s t) =
        sf_exun_belongs_term_term
          C k (d_exun_translation_term C k s) (d_exun_translation_term C k t).
    Proof.
      intros.
      destruct s.
      destruct t.
      simpl; reflexivity.
      simpl; reflexivity.
      destruct t.
      simpl; reflexivity.
      simpl; reflexivity.
    Defined.
    
    Definition d_to_sf_exun_belongs_letter_prop_eq:
      forall (C:Type) (k:C) (x:C) (p: DP (option C)),
        d_exun_translation_prop C k (d_exun_belongs_letter_prop C k x p) =
        sf_exun_belongs_letter_prop C k x (d_exun_translation_prop (option C) (Some k) p).
    Proof.
      intros.
      unfold d_exun_belongs_letter_prop.
      rewrite d_to_sf_exun_and_eq.
      rewrite d_to_sf_exun_implies_eq.
      unfold sf_exun_belongs_letter_prop.           
      repeat rewrite d_to_sf_exun_exists_unique_eq.
      apply f_equal2.
      apply f_equal.
      simpl; reflexivity.
      rewrite d_to_sf_exun_implies_eq.
      repeat rewrite d_to_sf_exun_exists_unique_eq.
      apply f_equal2.
      repeat rewrite d_to_sf_exun_exists_unique_eq.
      rewrite d_to_sf_exun_neg_eq.
      rewrite d_to_sf_exun_exists_unique_eq.
      reflexivity.
      simpl; reflexivity.
    Defined.
      
    Definition d_to_sf_exun_belongs_letter_term_eq:
      forall (C:Type) (k:C) (x:C) (t: DT C),
        d_exun_translation_prop C k (d_exun_belongs_letter_term C k x t) =
        sf_exun_belongs_letter_term C k x (d_exun_translation_term C k t).
    Proof.
      intros.
      destruct t.
      simpl.
      reflexivity.
      unfold sf_exun_belongs_letter_term.
      unfold d_exun_belongs_letter_term.
      rewrite d_to_sf_exun_belongs_letter_prop_eq.
      reflexivity.
    Defined.

    Ltac ri := rewrite d_to_sf_exun_implies_eq.
    Ltac ra := rewrite d_to_sf_exun_and_eq.
    Ltac rn := rewrite d_to_sf_exun_neg_eq.
    Ltac fe := apply f_equal.
    Ltac fe2 := apply f_equal2.
    Ltac re := rewrite d_to_sf_exun_exists_eq.
    Ltac reu := rewrite d_to_sf_exun_exists_unique_eq.
    Ltac rf := rewrite d_to_sf_exun_forall_eq.
    
    Definition d_to_sf_exun_belongs_prop_term_eq:
      forall (C:Type) (k:C) (q: DP (option C)) (t:DT C),
        d_exun_translation_prop C k (d_exun_belongs_prop_term C k q t) =
        sf_exun_belongs_prop_term
          C k
          (d_exun_translation_prop (option C) (Some k) q)
          (d_exun_translation_term C k t).
    Proof.
      intros.
      unfold d_exun_belongs_prop_term.
      unfold sf_exun_belongs_prop_term.
      ra. fe2. ri. reu. unfold d_term_constant_embedding. fe. rf.
      fe. ri. fe. rewrite d_to_sf_exun_belongs_letter_term_eq.
      fe. rewrite <- d_to_sf_exun_coc_term_eq.
      unfold sf_term_constant_embedding; reflexivity.
      ri. rn. reu. fe. rewrite d_to_sf_exun_belongs_letter_term_eq. reflexivity.
    Defined.
      
    Definition d_to_sf_exun_belongs_term_term_eq:
      forall (C:Type) (k:C) (s t:DT C),
        d_exun_translation_prop C k (d_exun_belongs_term_term C k s t) =
        sf_exun_belongs_term_term
          C k
          (d_exun_translation_term C k s)
          (d_exun_translation_term C k t).
    Proof.
      intros.
      unfold d_exun_belongs_term_term.
      unfold sf_exun_belongs_term_term.
      destruct s.
      apply d_to_sf_exun_belongs_letter_term_eq.
      apply d_to_sf_exun_belongs_prop_term_eq.
    Defined.

    Definition sf_exun_translation_belongs_definition_tautology:
      forall (C:Type) (k:C) (s t:DT C),
        d_exun_translation_prop
          C k
          (d_equiv C (d_belongs C s t) (d_exun_belongs_term_term C k s t)) 
        =
        sf_equiv
          C
          (sf_exun_belongs_term_term
             C k (d_exun_translation_term C k s) (d_exun_translation_term C k t))
          (sf_exun_belongs_term_term
             C k (d_exun_translation_term C k s) (d_exun_translation_term C k t)).
    Proof.
      intros.
      rewrite d_to_sf_exun_equiv_eq.
      rewrite d_to_sf_exun_belongs_eq.
      rewrite d_to_sf_exun_belongs_term_term_eq.
      reflexivity.
    Defined.
      
    Definition sf_exun_translation_belongs_definition_tautology_proof:
      forall (C:Type) (k:C) (T: Set_Formula C -> Type) (s t:DT C),
        hs_proof
          C T
          (d_exun_translation_prop
             C k (d_equiv C (d_belongs C s t) (d_exun_belongs_term_term C k s t))).
    Proof.
      intros.
      rewrite sf_exun_translation_belongs_definition_tautology.
      apply hs_equiv_reflexivity.
    Defined.

    Fixpoint sf_to_d_involution (C:Type) (f:Set_Formula C) (k:C) {struct f}:
      d_exun_translation_prop C k (sf_to_d_translation C f) = f.
    Proof.
      destruct f.
      simpl; reflexivity.
      simpl; reflexivity.
      simpl; repeat rewrite sf_to_d_involution; reflexivity.
      simpl; rewrite sf_to_d_involution; reflexivity.
    Defined.
      
    Fixpoint sf_to_d_coc_eq (C:Type) (f:Set_Formula C) (D:Type) (env: C -> D) {struct f}:
      d_prop_change_of_context C (sf_to_d_translation C f) D env =  
      sf_to_d_translation D (change_of_context C D env f).
    Proof.
      destruct f.
      simpl; reflexivity.
      simpl; reflexivity.
      simpl; repeat rewrite sf_to_d_coc_eq; reflexivity.
      simpl; rewrite sf_to_d_coc_eq. unfold extend_map_to_bound_variables. reflexivity.
    Defined.

    Section d_exun_formulas_in_change_of_contexts.

      Ltac fe := apply f_equal.
      Ltac fe2 := apply f_equal2. 

      Definition d_implies_coc_eq:
        forall (C D:Type) (env: C -> D) (a b:DP C),
          d_prop_change_of_context C (d_implies C a b) D env
          = 
          d_implies D (d_prop_change_of_context C a D env)
                      (d_prop_change_of_context C b D env).
      Proof.
        intros; simpl; reflexivity.
      Defined.

      Ltac ei := rewrite d_implies_coc_eq; apply f_equal2. 
      
      Definition d_and_coc_eq:
        forall (C D:Type) (env: C -> D) (a b:DP C),
          d_prop_change_of_context C (d_and C a b) D env
          = 
          d_and D (d_prop_change_of_context C a D env)
                      (d_prop_change_of_context C b D env).
      Proof.
        intros; simpl; reflexivity.
      Defined.

      Ltac ea := rewrite d_and_coc_eq; apply f_equal2.

      Definition d_equiv_coc_eq:
        forall (C D:Type) (env: C -> D) (a b:DP C),
          d_prop_change_of_context C (d_equiv C a b) D env
          = 
          d_equiv D (d_prop_change_of_context C a D env)
                      (d_prop_change_of_context C b D env).
      Proof.
        intros; simpl; reflexivity.
      Defined.

      Ltac ee := rewrite d_equiv_coc_eq; apply f_equal2.

      Definition d_neg_coc_eq:
        forall (C D:Type) (env: C -> D) (a:DP C),
          d_prop_change_of_context C (d_neg C a) D env
          = 
          d_neg D (d_prop_change_of_context C a D env).
      Proof.
        intros; simpl; reflexivity.
      Defined.

      Ltac en := rewrite d_neg_coc_eq; apply f_equal.
      
      Definition d_forall_coc_eq:
        forall (C D:Type) (env: C -> D) (p:DP (option C)),
          d_prop_change_of_context C (d_forall C p) D env
          =
          d_forall D (d_prop_change_of_context
                        (option C) p (option D)
                        (extend_map_to_bound_variables C D env)).
      Proof.
        intros. simpl. apply f_equal.
        apply d_prop_coc_pointwise_equality.
        intros. destruct x. simpl; reflexivity. simpl; reflexivity.
      Defined.

      Ltac ef:= rewrite d_forall_coc_eq; apply f_equal.
 
      Definition d_exists_coc_eq:
        forall (C D:Type) (env: C -> D) (p:DP (option C)),
          d_prop_change_of_context C (d_exists C p) D env
          =
          d_exists D (d_prop_change_of_context
                        (option C) p (option D)
                        (extend_map_to_bound_variables C D env)).
      Proof.
        intros. unfold d_exists. en. ef. en. reflexivity.
      Defined.

      Ltac eex:= rewrite d_exists_coc_eq; apply f_equal.

      Definition d_belongs_coc_eq:
        forall (C D:Type) (env: C -> D) (s t:DT C),
          d_prop_change_of_context C (d_belongs C s t) D env
          = 
          d_belongs D (d_term_change_of_context C s D env)
                      (d_term_change_of_context C t D env).
      Proof.
        intros; simpl; reflexivity.
      Defined.
      
      Ltac eb:= rewrite d_belongs_coc_eq; apply f_equal2.
      
      Definition d_equal_coc_eq:
        forall (C D:Type) (env: C -> D) (s t:DT C),
          d_prop_change_of_context C (d_equal C s t) D env
          = 
          d_equal D (d_term_change_of_context C s D env)
                      (d_term_change_of_context C t D env).
      Proof.
        intros. unfold d_equal. ea. ef. ee. eb.
        unfold d_term_constant_embedding.
        repeat rewrite <- d_term_coc_composition_equality.
        apply d_term_coc_pointwise_equality.
        intros.
        simpl; reflexivity.
        simpl; reflexivity.
        eb. unfold d_term_constant_embedding.
        repeat rewrite <- d_term_coc_composition_equality.
        apply d_term_coc_pointwise_equality.
        simpl; reflexivity.
        simpl; reflexivity.
        ef. ee. eb.
        simpl; reflexivity.
        unfold d_term_constant_embedding.
        repeat rewrite <- d_term_coc_composition_equality.
        apply d_term_coc_pointwise_equality.
        intros.
        simpl; reflexivity.
        eb.
        simpl; reflexivity.
        unfold d_term_constant_embedding.
        repeat rewrite <- d_term_coc_composition_equality.
        apply d_term_coc_pointwise_equality.
        intros.
        simpl; reflexivity.                  
      Defined.

      Ltac eeq := rewrite d_equal_coc_eq; apply f_equal2.      
      
      Definition d_unique_coc_eq:
        forall (C D:Type) (env: C -> D) (p:DP (option C)),
          d_prop_change_of_context C (d_unique C p) D env
          =
          d_unique D (d_prop_change_of_context
                        (option C) p (option D)
                        (extend_map_to_bound_variables C D env)).
      Proof.
        intros. unfold d_unique. ef. 
        ef. ei. repeat rewrite <- d_prop_coc_composition_equality.
        apply d_prop_coc_pointwise_equality. intros.
        destruct x. simpl; reflexivity. simpl; reflexivity.
        ei.
        repeat rewrite <- d_prop_coc_composition_equality.
        apply d_prop_coc_pointwise_equality. intros.
        destruct x. simpl; reflexivity. simpl; reflexivity.
        eeq.
        simpl; reflexivity.
        simpl; reflexivity.
      Defined.

      Ltac eu:= rewrite d_unique_coc_eq; apply f_equal.
      
      Definition d_exists_unique_coc_eq:        
        forall (C D:Type) (env: C -> D) (p:DP (option C)),
          d_prop_change_of_context C (d_exists_unique C p) D env
          =
          d_exists_unique D (d_prop_change_of_context
                               (option C) p (option D)
                               (extend_map_to_bound_variables C D env)).          
      Proof.
        intros. 
        unfold d_exists_unique. ea. eex. reflexivity. eu. reflexivity.
      Defined.

      Ltac eeu:= rewrite d_exists_unique_coc_eq; apply f_equal.      
      Ltac eeua:= apply d_exists_unique_coc_eq.      
      
      Definition d_exun_belongs_letter_prop_coc_eq:        
        forall (C D:Type) (k:C) (env: C -> D) (x:C) (p:DP (option C)),
          d_prop_change_of_context C (d_exun_belongs_letter_prop C k x p) D env
          =
          d_exun_belongs_letter_prop
            D (env k) (env x)
            (d_prop_change_of_context (option C) p (option D)
                                       (extend_map_to_bound_variables C D env)).
      Proof.
        intros.
        unfold d_exun_belongs_letter_prop.
        ea. ei. eeua. ef. ei; reflexivity.
        ei. en. eeua. eb.
        simpl; reflexivity.
        simpl; reflexivity.
      Defined.      
      
      Definition d_exun_belongs_letter_term_coc_eq:        
        forall (C D:Type) (k:C) (env: C -> D) (x:C) (t:DT C),
          d_prop_change_of_context C (d_exun_belongs_letter_term C k x t) D env
          =
          d_exun_belongs_letter_term
            D (env k) (env x) (d_term_change_of_context C t D env).
      Proof.
        intros.
        destruct t.
        simpl; reflexivity.
        apply d_exun_belongs_letter_prop_coc_eq.
      Defined.      
      
      Definition d_exun_belongs_prop_term_coc_eq:        
        forall (C D:Type) (k:C) (env: C -> D) (q:DP (option C)) (t:DT C),
          d_prop_change_of_context C (d_exun_belongs_prop_term C k q t) D env
          =
          d_exun_belongs_prop_term
            D (env k)
            (d_prop_change_of_context (option C) q (option D)
                                       (extend_map_to_bound_variables C D env))
            (d_term_change_of_context C t D env).
      Proof.
        intros.
        unfold d_exun_belongs_prop_term.
        ea. ei. eeua. ef. ei. reflexivity. rewrite d_exun_belongs_letter_term_coc_eq.
        apply f_equal.
        unfold d_term_constant_embedding.
        repeat rewrite <- d_term_coc_composition_equality.
        apply d_term_coc_pointwise_equality.
        intros.
        simpl; reflexivity.
        ei. en. eeua. 
        apply d_exun_belongs_letter_term_coc_eq.
      Defined.             
      
      Definition d_exun_belongs_term_term_coc_eq:        
        forall (C D:Type) (k:C) (env: C -> D) (s t:DT C),
          d_prop_change_of_context C (d_exun_belongs_term_term C k s t) D env
          =
          d_exun_belongs_term_term
            D (env k)
            (d_term_change_of_context C s D env)
            (d_term_change_of_context C t D env).
      Proof.
        intros.
        destruct s.
        apply d_exun_belongs_letter_term_coc_eq.
        apply d_exun_belongs_prop_term_coc_eq.
      Defined.

      Definition d_fd_belongs_characterization_coc_eq:        
        forall (C D:Type) (k:C) (env: C -> D) (s t:DT C),
          d_prop_change_of_context
            C
            (d_equiv C (d_belongs C s t)
                     (d_exun_belongs_term_term C k s t)) D env
          =
          d_equiv
            D
            (d_belongs D
                       (d_term_change_of_context C s D env)
                       (d_term_change_of_context C t D env))
            (d_exun_belongs_term_term
               D (env k)
               (d_term_change_of_context C s D env)
               (d_term_change_of_context C t D env)).
      Proof.
        intros.
        ee. apply d_belongs_coc_eq.
        apply d_exun_belongs_term_term_coc_eq.
      Defined.
      
    End d_exun_formulas_in_change_of_contexts.    

    Section d_exun_formulas_in_substitutions.

      Ltac fe := apply f_equal.
      Ltac fe2 := apply f_equal2. 

      Definition d_implies_subst_eq:
        forall (C D:Type) (env: C -> DT D) (a b:DP C),
          d_prop_substitution C (d_implies C a b) D env
          = 
          d_implies D (d_prop_substitution C a D env)
                      (d_prop_substitution C b D env).
      Proof.
        intros; simpl; reflexivity.
      Defined.

      Ltac ei := rewrite d_implies_subst_eq; apply f_equal2. 
      
      Definition d_and_subst_eq:
        forall (C D:Type) (env: C -> DT D) (a b:DP C),
          d_prop_substitution C (d_and C a b) D env
          = 
          d_and D (d_prop_substitution C a D env)
                      (d_prop_substitution C b D env).
      Proof.
        intros; simpl; reflexivity.
      Defined.

      Ltac ea := rewrite d_and_subst_eq; apply f_equal2.

      Definition d_equiv_subst_eq:
        forall (C D:Type) (env: C -> DT D) (a b:DP C),
          d_prop_substitution C (d_equiv C a b) D env
          = 
          d_equiv D (d_prop_substitution C a D env)
                      (d_prop_substitution C b D env).
      Proof.
        intros; simpl; reflexivity.
      Defined.

      Ltac ee := rewrite d_equiv_subst_eq; apply f_equal2.

      Definition d_neg_subst_eq:
        forall (C D:Type) (env: C -> DT D) (a:DP C),
          d_prop_substitution C (d_neg C a) D env
          = 
          d_neg D (d_prop_substitution C a D env).
      Proof.
        intros; simpl; reflexivity.
      Defined.

      Ltac en := rewrite d_neg_subst_eq; apply f_equal.
      
      Definition d_forall_subst_eq:
        forall (C D:Type) (env: C -> DT D) (p:DP (option C)),
          d_prop_substitution C (d_forall C p) D env
          =
          d_forall D (d_prop_substitution
                        (option C) p (option D)
                        (option_rect
                           (fun _: option C => DT (option D))
                           (fun a:C => d_term_constant_embedding D (env a))
                           (d_letter (option D) None)
                        )
                     ).
      Proof.
        intros. simpl. apply f_equal.
        apply d_prop_subst_pointwise_equality.
        intros. destruct x. simpl; reflexivity. simpl; reflexivity.
      Defined.

      Ltac ef:= rewrite d_forall_subst_eq; apply f_equal.
 
      Definition d_exists_subst_eq:
        forall (C D:Type) (env: C -> DT D) (p:DP (option C)),
          d_prop_substitution C (d_exists C p) D env
          =
          d_exists D (d_prop_substitution
                        (option C) p (option D)
                        (option_rect
                           (fun _: option C => DT (option D))
                           (fun a:C => d_term_constant_embedding D (env a))
                           (d_letter (option D) None)
                        )
                     ).
      Proof.
        intros. unfold d_exists. en. ef. en. reflexivity.
      Defined.

      Ltac eex:= rewrite d_exists_subst_eq; apply f_equal.

      Definition d_belongs_subst_eq:
        forall (C D:Type) (env: C -> DT D) (s t:DT C),
          d_prop_substitution C (d_belongs C s t) D env
          = 
          d_belongs D (d_term_substitution C s D env)
                      (d_term_substitution C t D env).
      Proof.
        intros; simpl; reflexivity.
      Defined.
      
      Ltac eb:= rewrite d_belongs_subst_eq; apply f_equal2.
      
      Definition d_equal_subst_eq:
        forall (C D:Type) (env: C -> DT D) (s t:DT C),
          d_prop_substitution C (d_equal C s t) D env
          = 
          d_equal D (d_term_substitution C s D env)
                      (d_term_substitution C t D env).
      Proof.
        intros. unfold d_equal. ea. ef. ee. eb.
        unfold d_term_constant_embedding.
        repeat rewrite <- d_term_subst_composition_equality.
        apply d_term_coc_subst_commutation.
        intros.
        simpl; reflexivity.
        simpl; reflexivity.
        eb. unfold d_term_constant_embedding.
        repeat rewrite <- d_term_subst_composition_equality.
        apply d_term_coc_subst_commutation.
        simpl; reflexivity.
        simpl; reflexivity.
        ef. ee. eb.
        simpl; reflexivity.
        unfold d_term_constant_embedding.
        repeat rewrite <- d_term_subst_composition_equality.
        apply d_term_coc_subst_commutation.
        intros.
        simpl; reflexivity.
        eb.
        simpl; reflexivity.
        unfold d_term_constant_embedding.
        repeat rewrite <- d_term_subst_composition_equality.
        apply d_term_coc_subst_commutation.
        intros.
        simpl; reflexivity.                  
      Defined.

      Ltac eeq := rewrite d_equal_subst_eq; apply f_equal2.      
      
      Definition d_unique_subst_eq:
        forall (C D:Type) (env: C -> DT D) (p:DP (option C)),
          d_prop_substitution C (d_unique C p) D env
          =
          d_unique D (d_prop_substitution
                        (option C) p (option D)
                        (option_rect
                           (fun _: option C => DT (option D))
                           (fun a:C => d_term_constant_embedding D (env a))
                           (d_letter (option D) None)
                        )
                     ).
      Proof.
        intros. unfold d_unique. ef. 
        ef. ei. repeat rewrite <- d_prop_subst_composition_equality.
        apply d_prop_coc_subst_commutation. intros.
        destruct x. simpl. unfold d_term_constant_embedding.
        repeat rewrite <- d_term_coc_composition_equality.
        apply d_term_coc_pointwise_equality. intros.
        simpl; reflexivity. simpl; reflexivity.
        ei.
        repeat rewrite <- d_prop_subst_composition_equality.
        apply d_prop_coc_subst_commutation. intros.
        destruct x. simpl. unfold d_term_constant_embedding.
        repeat rewrite <- d_term_coc_composition_equality.
        apply d_term_coc_pointwise_equality. intros.
        simpl; reflexivity. simpl; reflexivity.
        eeq.
        simpl; reflexivity.
        simpl; reflexivity.
      Defined.

      Ltac eu:= rewrite d_unique_subst_eq; apply f_equal.
      
      Definition d_exists_unique_subst_eq:        
        forall (C D:Type) (env: C -> DT D) (p:DP (option C)),
          d_prop_substitution C (d_exists_unique C p) D env
          =
          d_exists_unique D (d_prop_substitution
                               (option C) p (option D)
                               (option_rect
                                  (fun _: option C => DT (option D))
                                  (fun a:C => d_term_constant_embedding D (env a))
                                  (d_letter (option D) None)
                               )
                            ).
      Proof.
        intros. 
        unfold d_exists_unique. ea. eex. reflexivity. eu. reflexivity.
      Defined.
      
    End d_exun_formulas_in_substitutions.
    
    Section d_exun_formulas_in_sf_to_d.

      Ltac fe := apply f_equal.
      Ltac fe2 := apply f_equal2. 

      Definition d_implies_sftd_eq:
        forall (C:Type) (a b:Set_Formula C),
          sf_to_d_translation C (sf_implies C a b) 
          = 
          d_implies C (sf_to_d_translation C a)
                      (sf_to_d_translation C b).
      Proof.
        intros; simpl; reflexivity.
      Defined.

      Ltac ei := rewrite d_implies_sftd_eq; apply f_equal2. 
      
      Definition d_and_sftd_eq:
        forall (C:Type) (a b:Set_Formula C),
          sf_to_d_translation C (sf_and C a b)
          = 
          d_and C (sf_to_d_translation C a)
                      (sf_to_d_translation C b).
      Proof.
        intros; simpl; reflexivity.
      Defined.

      Ltac ea := rewrite d_and_sftd_eq; apply f_equal2.

      Definition d_equiv_sftd_eq:
        forall (C:Type)  (a b:Set_Formula C),
          sf_to_d_translation C (sf_equiv C a b)
          = 
          d_equiv C (sf_to_d_translation C a)
                      (sf_to_d_translation C b).
      Proof.
        intros; simpl; reflexivity.
      Defined.

      Ltac ee := rewrite d_equiv_sftd_eq; apply f_equal2.

      Definition d_neg_sftd_eq:
        forall (C:Type)  (a:Set_Formula C),
          sf_to_d_translation C (sf_neg C a)
          = 
          d_neg C (sf_to_d_translation C a).
      Proof.
        intros; simpl; reflexivity.
      Defined.

      Ltac en := rewrite d_neg_sftd_eq; apply f_equal.
      
      Definition d_forall_sftd_eq:
        forall (C:Type)  (p:Set_Formula (option C)),
          sf_to_d_translation C (sf_forall C p)
          =
          d_forall C (sf_to_d_translation
                        (option C) p).
      Proof.
        intros. simpl. apply f_equal. reflexivity.
      Defined.

      Ltac ef:= rewrite d_forall_sftd_eq; apply f_equal.
 
      Definition d_exists_sftd_eq:
        forall (C:Type)  (p:Set_Formula (option C)),
          sf_to_d_translation C (sf_exists C p)
          =
          d_exists C (sf_to_d_translation
                        (option C) p).
      Proof.
        intros. unfold d_exists. unfold sf_exists. en. ef. en. reflexivity.
      Defined.

      Ltac eex:= rewrite d_exists_sftd_eq; apply f_equal.

      Definition d_belongs_sftd_eq:
        forall (C:Type)  (s t:C),
          sf_to_d_translation C (sf_belongs C s t)
          = 
          d_belongs C (d_letter C s)
                      (d_letter C t).
      Proof.
        intros; simpl; reflexivity.
      Defined.
      
      Ltac eb:= rewrite d_belongs_sftd_eq; apply f_equal2.
      
      Definition d_equal_sftd_eq:
        forall (C:Type)  (s t:C),
          sf_to_d_translation C (sf_equal C s t)
          = 
          d_equal C (d_letter C s)
                      (d_letter C t).
      Proof.
        intros; simpl; reflexivity.
      Defined.

      Ltac eeq := rewrite d_equal_sftd_eq; apply f_equal2.      
      
      Definition d_unique_sftd_eq:
        forall (C:Type)  (p:Set_Formula (option C)),
          sf_to_d_translation C (sf_unique C p)
          =
          d_unique C (sf_to_d_translation
                        (option C) p).
      Proof.
        intros. unfold d_unique. unfold sf_unique. ef. 
        ef. ei. rewrite sf_to_d_coc_eq. reflexivity.
        ei. rewrite sf_to_d_coc_eq. reflexivity.
        eeq. simpl; reflexivity.
        reflexivity.
      Defined.

      Ltac eu:= rewrite d_unique_sftd_eq; apply f_equal.
      
      Definition d_exists_unique_sftd_eq:        
        forall (C:Type)  (p:Set_Formula (option C)),
          sf_to_d_translation C (sf_exists_unique C p)
          =
          d_exists_unique C (sf_to_d_translation
                               (option C) p).          
      Proof.
        intros. 
        unfold d_exists_unique. unfold sf_exists_unique. ea. eex. reflexivity. eu. reflexivity.
      Defined.

      Ltac eeu:= rewrite d_exists_unique_sftd_eq; apply f_equal.      
      Ltac eeua:= apply d_exists_unique_sftd_eq.      
      
      Definition d_exun_belongs_letter_prop_sftd_eq:        
        forall (C:Type) (k:C)  (x:C) (p:Set_Formula (option C)),
          sf_to_d_translation C (sf_exun_belongs_letter_prop C k x p)
          =
          d_exun_belongs_letter_prop
            C k x
            (sf_to_d_translation (option C) p).
      Proof.
        intros.
        unfold d_exun_belongs_letter_prop. unfold sf_exun_belongs_letter_prop.
        ea. ei. eeua. ef. ei; reflexivity.
        ei. en. eeua. eb.
        simpl; reflexivity.
        simpl; reflexivity.
      Defined.      

      Definition sf_to_d_translation_term (C:Type) (t:sf_term C):DT C:=
        match t with
        |sf_letter _ l => d_letter C l
        |sf_predicate _ p => d_def C (sf_to_d_translation (option C) p)
        end.                 
      
      Definition d_exun_belongs_letter_term_sftd_eq:        
        forall (C:Type) (k:C)  (x:C) (t:sf_term C),
          sf_to_d_translation C (sf_exun_belongs_letter_term C k x t)
          =
          d_exun_belongs_letter_term
            C k x (sf_to_d_translation_term C t).
      Proof.
        intros.
        destruct t.
        simpl; reflexivity.
        apply d_exun_belongs_letter_prop_sftd_eq.
      Defined.      
      
      Definition d_exun_belongs_prop_term_sftd_eq:        
        forall (C:Type) (k:C)  (q:Set_Formula (option C)) (t:sf_term C),
          sf_to_d_translation C (sf_exun_belongs_prop_term C k q t)
          =
          d_exun_belongs_prop_term
            C k
            (sf_to_d_translation (option C) q)
            (sf_to_d_translation_term C t).
      Proof.
        intros.
        unfold d_exun_belongs_prop_term. unfold sf_exun_belongs_prop_term.
        ea. ei. eeua. ef. ei. reflexivity. rewrite d_exun_belongs_letter_term_sftd_eq.
        apply f_equal.
        unfold d_term_constant_embedding.
        destruct t. simpl; reflexivity. simpl.
        rewrite sf_to_d_coc_eq. reflexivity.
        ei. en. eeua. 
        apply d_exun_belongs_letter_term_sftd_eq.
      Defined.             
      
      Definition d_exun_belongs_term_term_sftd_eq:        
        forall (C:Type) (k:C)  (s t:sf_term C),
          sf_to_d_translation C (sf_exun_belongs_term_term C k s t)
          =
          d_exun_belongs_term_term
            C k
            (sf_to_d_translation_term C s)
            (sf_to_d_translation_term C t).
      Proof.
        intros.
        destruct s.
        apply d_exun_belongs_letter_term_sftd_eq.
        apply d_exun_belongs_prop_term_sftd_eq.
      Defined.
      
    End d_exun_formulas_in_sf_to_d.
    
  End exist_unique_translation_tools.
  
End main.
