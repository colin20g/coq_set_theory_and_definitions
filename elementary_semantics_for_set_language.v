Require Import SetDef.first_order_set_language.

Section regularity.  

  Definition regular (F:Prop):Prop:= (~ (~ F)) -> F.

  Definition regular_implies: forall A B:Prop, regular B -> regular (A -> B) :=
    fun (A B : Prop) (ra : regular B) (rcab : ~ ~ (A -> B)) (a : A) =>
      ra (fun wb : ~ B => rcab (fun cab : A -> B => wb (cab a))).

  Definition regular_wrong: regular (False):= fun wf : ~ ~ False => wf (fun f : False => f).

  Definition regular_forall (X:Type) (P: X -> Prop):
    (forall s:X, regular (P s)) -> regular (forall t:X, P t):=
    fun (ra : forall s : X, regular (P s))
        (wap : ~ ~ (forall t : X, P t)) (t : X) =>
      ra t (fun wpt : ~ P t => wap (fun ap : forall t0 : X, P t0 => wpt (ap t))).

  Definition regular_not: forall F:Prop, regular (~ F):=
    fun (F : Prop) (nnnf : ~ ~ ~ F) (f : F) => nnnf (fun nf : ~ F => nf f).  
  
End regularity.

Section the_general_regular_case.

  Variable Univ: Type.
  Variable R: Univ -> Univ -> Prop.
  Hypothesis REG: forall x y:Univ, regular (R x y).

  Fixpoint sf_interpretation
           (context: Type) (p: Set_Formula context)(env: context -> Univ){struct p}:Prop:=
    match p in (Set_Formula T) return ((T -> Univ) -> Prop) with
    | sf_belongs C x y => fun env0 : C -> Univ => R (env0 x) (env0 y)
    | sf_wrong C => fun _ : C -> Univ => False
    | sf_implies C q r =>
      fun env0 : C -> Univ => (sf_interpretation C q env0) -> (sf_interpretation C r env0)
    | sf_forall C p0 =>
      fun env0 : C -> Univ =>
        all
          (fun u : Univ =>
             sf_interpretation (option C) p0 (option_rect (fun _ : option C => Univ) env0 u))
    end env.

  Fixpoint sf_interpretation_regularity
           (context:Type) (p: Set_Formula context) (env: context -> Univ){struct p}:
    regular (sf_interpretation context p env):=
    match
      p as s in (Set_Formula T)
      return (forall env0 : T -> Univ, regular (sf_interpretation T s env0))
    with
    | sf_belongs C c c0 => fun env0 : C -> Univ => REG (env0 c) (env0 c0)
    | sf_wrong C => fun env0 : C -> Univ => regular_wrong
    | sf_implies C p1 p2 =>
      fun env0 : C -> Univ =>
        regular_implies (sf_interpretation C p1 env0) (sf_interpretation C p2 env0)
                        (sf_interpretation_regularity C p2 env0)
    | sf_forall C p0 =>
      fun env0 : C -> Univ =>
        regular_forall
          Univ
          (fun u : Univ =>
             sf_interpretation (option C) p0 (option_rect (fun _ : option C => Univ) env0 u))
          (fun s : Univ =>
             sf_interpretation_regularity (option C) p0
                                          (option_rect (fun _ : option C => Univ) env0 s))
    end env.

  Definition iff_forall: forall (P Q: Univ -> Prop),
      (forall x:Univ, P x <-> Q x) -> ((all P) <-> (all Q)).
  Proof.
    intros; split.
    intros. intro. apply H. apply H0.
    intros. intro. apply H. apply H0.
  Defined.
  
  Fixpoint sf_interpretation_pointwise_equality
           (C:Type) (f:Set_Formula C) (env1 env2:C -> Univ)
           (eqenv: forall x:C, env1 x = env2 x) {struct f}:
    sf_interpretation C f env1 <-> sf_interpretation C f env2.
  Proof.
    destruct f.
    simpl; repeat rewrite eqenv; apply iff_refl.
    simpl; apply iff_refl.
    simpl. apply iff_trans with
               (B:= (sf_interpretation C f1 env2) ->                      
                    (sf_interpretation C f2 env1)
               ).
    apply imp_iff_compat_r. apply sf_interpretation_pointwise_equality. assumption.
    apply imp_iff_compat_l. apply sf_interpretation_pointwise_equality. assumption.
    simpl.
    apply iff_forall. intros. apply sf_interpretation_pointwise_equality.
    intros. destruct x0. simpl; apply eqenv. simpl; reflexivity.
  Defined.
  
  Fixpoint sf_coc_interpretation_commutation
           (C:Type) (f:Set_Formula C) (D:Type) (envcd: C -> D) (envdu: D -> Univ) {struct f}:
    sf_interpretation D (change_of_context C D envcd f) envdu <->
    sf_interpretation C f (fun l:C => envdu (envcd l)).
  Proof.
    destruct f.
    simpl; apply iff_refl.
    simpl; apply iff_refl.
    simpl. apply iff_trans with
               (B:= (sf_interpretation
                       C f1 (fun l:C => envdu (envcd l))) ->
                    (sf_interpretation D (change_of_context C D envcd f2) envdu)

               ).
    apply imp_iff_compat_r. apply sf_coc_interpretation_commutation.
    apply imp_iff_compat_l. apply sf_coc_interpretation_commutation.
    simpl; apply iff_forall.
    intros.
    apply iff_trans with
        (B:= sf_interpretation
               (option C) f
               ( fun (l:option C) =>
                 (option_rect
                  (fun _:option D => Univ)
                  envdu x
                  (extend_map_to_bound_variables C D envcd l)
                 )
               )
        ).
    apply sf_coc_interpretation_commutation.
    apply sf_interpretation_pointwise_equality.
    intros; destruct x0. simpl; reflexivity. simpl; reflexivity.
  Defined.

  Fixpoint logical_axioms_soundness
           (C:Type) (f:Set_Formula C) (l:logical_axiom C f) (env: C -> Univ) {struct l}:
    sf_interpretation C f env.
  Proof.
    destruct l.
    simpl; intros; assumption.
    simpl; intros. apply H. apply H1. apply H0. apply H1.
    simpl; apply sf_interpretation_regularity.
    simpl; unfold specify. intro. apply sf_coc_interpretation_commutation.
    apply sf_interpretation_pointwise_equality with
        (env2:= option_rect (fun _:option C => Univ) env (env t)).
    intros. destruct x. simpl; reflexivity. simpl; reflexivity. apply H.
    simpl.
    intros. intro u.
    unfold constant_formula_embedding.
    apply sf_coc_interpretation_commutation.
    apply sf_interpretation_pointwise_equality with (env2 := env).
    intros; simpl; reflexivity. assumption.
    simpl.
    intros. intro u.
    apply H. apply H0.
    simpl.
    intro u.
    apply logical_axioms_soundness. assumption.
  Defined.

  Section the_soundness_theorem.

    Variable context:Type.
    Variable environment: context -> Univ.
    Variable theory: Set_Formula context -> Type.
    Variable model: forall a:Set_Formula context,
        theory a -> sf_interpretation context a environment.

    Fixpoint sf_interpretation_soundness
             (f:Set_Formula context) (pr: hs_proof context theory f) {struct pr}:
      sf_interpretation context f environment.
    Proof.
      destruct pr.
      apply model; assumption.
      apply logical_axioms_soundness; assumption.
      apply sf_interpretation_soundness in pr1.
      apply sf_interpretation_soundness in pr2.
      apply pr1. repeat assumption.
    Defined.          
      
  End the_soundness_theorem.         
    
End the_general_regular_case.

Section the_double_negation_translation.

  Variable X: Type.
  Variable R: X -> X -> Prop.
  Variable C: Type.
  Variable env: C -> X.
  
  Definition sf_double_negation_interpretation (f:Set_Formula C): Prop:=
    sf_interpretation X (fun x y:X => ~ ~ R x y) C f env.

  Definition sf_double_negation_interpretation_soundness:
    forall (T:Set_Formula C -> Type)
           (m: forall g:Set_Formula C, T g -> sf_double_negation_interpretation g)
           (f:Set_Formula C),
      hs_proof C T f -> sf_double_negation_interpretation f.
  Proof.
    intros.
    unfold sf_double_negation_interpretation.
    apply sf_interpretation_soundness with (theory := T).
    intros; apply regular_not.
    assumption.
    assumption.
  Defined.             
  
End the_double_negation_translation.

  
