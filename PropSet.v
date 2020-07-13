Require Import Setoid.

(* ...these are like Coq Ensembles without extensionality *)
Section PropSets.

  Definition propset {A} := A -> Prop.

  Definition propset_in {A} (x : A) (s : propset) := s x.
  
  Definition propset_extensional_eq {A} (s : propset) (t : propset) :=
    forall x : A, propset_in x s <-> propset_in x t.
  
  Lemma propset_extensional_eq_refl {A} :
    forall s : @propset A, propset_extensional_eq s s.
  Proof.
    split; auto.
  Qed.

  Lemma propset_extensional_eq_sym {A} :
    forall (s t : @propset A), propset_extensional_eq s t -> propset_extensional_eq t s.
  Proof.
    split; intros; apply H; auto.
  Qed.

  Lemma propset_extensional_eq_trans {A} :
    forall (s t u : @propset A), propset_extensional_eq s t ->
                                 propset_extensional_eq t u ->
                                 propset_extensional_eq s u.
  Proof.
    split; intros.
    apply H0. apply H. auto.
    apply H. apply H0. auto.
  Qed.
  
  Global Instance propset_extensional_eq_Equivalence {A} :
    Equivalence (@propset_extensional_eq A) | 10 :=
    {
      Equivalence_Reflexive := propset_extensional_eq_refl ;
      Equivalence_Symmetric := propset_extensional_eq_sym ;
      Equivalence_Transitive := propset_extensional_eq_trans
    }.

End PropSets.

Notation "x '=e=' y" := (propset_extensional_eq x y) (at level 50) : propset_scope.
Notation "x '<e>' y" := (~ propset_extensional_eq x y) (at level 50) : propset_scope.
  
Open Scope propset_scope.
