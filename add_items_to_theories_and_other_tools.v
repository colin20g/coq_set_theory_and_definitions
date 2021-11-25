Section add_hypotheses_to_general_theories.
(** This basic device will be used to add an hypothesis to a theory.
    In our formalism, a theory is a map from a certain type
    of sentences, to Type.
*)
  Variable P:Type.
  Variable T: P -> Type.
  Variable h:P.

  Inductive add_item: P -> Type:=
  |new_item: add_item h
  |base_item: forall x:P, T x -> add_item x.  
  
End add_hypotheses_to_general_theories.

Section nat_equality_test.

  (** This is an equality test between natural integers *)
  
  Fixpoint nat_eqdec (p q:nat) {struct p}:sumbool (p = q) (p <> q).
  Proof.
    destruct p.
    destruct q.
    left; reflexivity.
    right; discriminate.
    destruct q.
    right; discriminate.
    destruct nat_eqdec with (p:=p) (q:=q).
    left; rewrite e; reflexivity.
    right; intro. apply n. apply eq_add_S. assumption.
  Defined.
  
End nat_equality_test.
