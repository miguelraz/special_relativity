Require Import Reals.
Require Import Recdef Morphisms.
Require Import Program.Tactics.
Require Import Thesis.FourVector.

(* First theory SpecRel of unaccelerated observers
   From paper "A logic road from special relativity to general relativity"
   https://arxiv.org/pdf/1005.0960v2.pdf *)

Section SpecRel.
  Variable body : Type.
  Variable IB : body -> Prop.
  Variable Ph : body -> Prop.
  Variable W : body -> body -> v4 -> Prop.

  Definition Ob m := exists b v, W m b v.
  Definition IOb m := IB m /\ Ob m.

  Definition eveq b1 v1 b2 v2 := forall b, W b1 b v1 <-> W b2 b v2.
  (* yes, this will rapidly fall out of use as an event terminology is developed *)

  Record specrel : Prop :=
    {
      AxPh :
        forall m, exists c, forall x y,
          IOb m ->
          (exists p, Ph p /\ W m p x /\ W m p y) <->
          |[ y^s -v- x^s ]| = c * |[ y^t -v- x^t ]| ;

      AxEv :
        forall m k,
          IOb m /\ IOb k ->
          forall x, exists y, eveq m x k y ;

      AxSf :
        forall m,
          IOb m ->
          (forall v, W m m v <-> v _x = 0 /\ v _y = 0 /\ v _z = 0) ;

      AxSm1 :
        forall m k,
          IOb m /\ IOb k ->
          forall x y x' y', x^t = y^t /\ x'^t = y'^t /\
                            eveq m x k x' /\ eveq m y k y' ->
                            |[ x^s -v- y^s ]| = |[ x'^s -v- y'^s ]| ;

      AxSm2 :
        forall m,
          IOb m -> exists p, Ph p /\ W m p (0, 0, 0, 0) /\ W m p (1, 0, 0, 1)
    }.
  
  Section SpecRelTheory.
    
    Require Import Thesis.PropSet.
    
    Variable SR : specrel.

    Let ax_ph := SR.(AxPh).
    Let ax_ev := SR.(AxEv).
    Let ax_sf := SR.(AxSf).
    Let ax_sm1 := SR.(AxSm1).
    Let ax_sm2 := SR.(AxSm2).
    
    (* speed of light is 1 by AxSm2, so let's just incorporate it *)
    Lemma ax_ph' :
      forall m, forall x y,
        IOb m ->
        (exists p, Ph p /\ W m p x /\ W m p y) <-> |[ y^s -v- x^s ]| = |[ y^t -v- x^t ]|.
    Proof.
      intros.
      (* use ax_sm2 to solve out for c in ax_ph *)
      (* obtain ax_ph formulated for the ax_sm2 photon *)
      pose (ax_sm2 m H).
      pose (ax_ph m).
      inversion e0; clear e0.
      rewrite H0 in e; auto.

      (* solve for x0 *)
      real_simpl.
      subst.

      (* now prove each case *)
      destruct_coords.
      split; intros.
      - apply H0 in H1; real_crush.
      - apply H0; real_crush.
    Qed.
    Hint Resolve ax_ph'.
    
    (* also, let's rewrite ax_sf in terms of ^s *)
    Lemma ax_sf' :
      forall m,
        IOb m -> forall v, W m m v <-> v ^s = (0, 0, 0, 0).
    Proof.
      split; intros.
      - rewrite ax_sf in H0; destruct_coords; destruct_pairs; auto.
      - destruct_coords; rewrite ax_sf; auto.
    Qed.

    Ltac induce_total_order a b :=
      assert (a < b \/ a = b \/ a > b) by apply Rtotal_order.
    
    Ltac induce_decidability a b :=
      assert (a = b \/ a <> b) by apply Req_dec.
    
    Ltac destruct_ors :=
      match goal with
        | [ H : _ \/ _ |- _ ] => destruct H; destruct_ors
        | _ => idtac
      end.

    (* THEORY OF EVENTS *)
    Section SpecRelEvents.

      (* geometric lemma used in ev_diff:
         if two x <> y, there is z s.t. a photon goes x <-> z, but no photon goes y <-> z. *)
      Lemma ph_distinct :
        forall x y, x <> y -> exists z,
                                |[ x^s -v- z^s ]| = |[ x^t -v- z^t ]| /\
                                |[ y^s -v- z^s ]| <> |[ y^t -v- z^t ]|.
      Proof.
        intros.
      
        (* pick the point with opposite time difference *)
        induce_total_order (x _t) (y _t).
        destruct_ors.
        (* proofs proceed by boiling down vector expressions *)
        - exists (x^t +v+ y^s +v+ (0, 0, 0, -|[(y -v- x)^s]|)).
          split; destruct_coords; real_crush.

          rewrite sqrt_square;
            [ apply Rlt_dichotomy_converse; left | unfold "<="; left ];
          real_crush.
        - exists (x^t +v+ y^s +v+ (0, 0, 0, |[(y -v- x)^s]|)).
          split; destruct_coords; real_crush.
          + apply Rlt_dichotomy_converse; left.
            assert (r5 = r2 \/ r5 <> r2) by apply Req_dec.
            assert (r6 = r3 \/ r6 <> r3) by apply Req_dec.
            assert (r4 = r1 \/ r4 <> r1) by apply Req_dec.
            repeat match goal with
                     | [ H : _ \/ _ |- _ ] => destruct H
                   end;
              subst;
              [ assert ((r2, r3, r1, r) = (r2, r3, r1, r)) by auto; contradiction | .. ];
              real_crush.
        - exists (x^t +v+ y^s +v+ (0, 0, 0, |[(y -v- x)^s]|)).
          split; destruct_coords; real_crush.

          rewrite <- Rmult_opp_opp.
          rewrite sqrt_square;
            [ apply Rlt_dichotomy_converse; left | unfold "<="; left ];
          real_crush.
      Qed.
    
      (* we can discuss events more explicitly *)
      Definition ev (b : body) (x : v4) := fun m => W b m x.

      (* we prove the contrapositive of the stronger principle because it is easier. *)
      (* it may be possible to directly prove the stronger principle by constructing photons *)
      Lemma ev_diff' :
        forall b x y, IOb b -> (ev b x <e> ev b y) <-> x <> y.
      Proof.
        autounfold in *; unfold "=e=" in *; unfold propset_in in *; unfold ev in *; split; intros.
        - subst.
          apply H0.
          split; auto.
        - (* construct a photon leading to contradiction *)
          apply ph_distinct in H0.
          destruct_exists.
          destruct_pairs.
          rewrite <- ax_ph' in H2; eauto.
          destruct_exists.
          rewrite H1 in H4.
          assert (exists p, Ph p /\ W b p H0 /\ W b p y) by eauto.
          apply ax_ph' in H5; auto.
      Qed.
    
      (* we can use decidability of the reals to prove the stronger principle *)
      (* however, this axiom on the reals is classical *)
      Lemma ev_diff :
        forall b, IOb b -> forall x y, ev b x =e= ev b y <-> x = y.
      Proof.
        autounfold in *; unfold "=e=" in *; split; intros.
        - assert (x = y \/ x <> y) by apply v4eq_dec.
          destruct H1; auto.
          rewrite <- ev_diff' in H1; eauto.
          autounfold in *; unfold "=e=" in *.
          contradiction.
        - rewrite H0; split; auto.
      Qed.
      
      (* ways to avoid unfolding *)
      Lemma ev_rewrite :
        forall a b m x y, W a m x -> ev a x =e= ev b y -> W b m y.
      Proof.
        unfold "=e="; unfold ev; unfold propset_in; intros.
        apply H0; auto.
      Qed.
      Hint Resolve ev_rewrite.

      (* rephrase ax_ev to use new event terminology *)
      Lemma ax_ev' :
        forall m k : body,
          IOb m -> IOb k -> forall x : v4, exists y : v4, ev m x =e= ev k y.
      Proof.
        unfold "=e="; unfold propset_in; unfold ev; unfold eveq in ax_ev.
        intros.
        apply ax_ev.
        auto.
      Qed.
      
      (* rephrase ax_sm1 as well *)
      Lemma ax_sm1' :
        forall m k,
          IOb m -> IOb k ->
          forall x y x' y', x^t = y^t ->
                            x'^t = y'^t ->
                            ev m x =e= ev k x' ->
                            ev m y =e= ev k y' ->
                            |[ x^s -v- y^s ]| = |[ x'^s -v- y'^s ]|.
      Proof.
        unfold "=e="; unfold propset_in; unfold ev; unfold eveq in ax_sm1.
        intros.
        apply (ax_sm1 m k); auto.
      Qed.
    
    End SpecRelEvents.
    
    (* THEORY OF AUTOMORPHISMS *)
    (* following the proof of Zeeman 1964, we will show that
       any causality-preserving automorphism is an element of the Poincare group *)
    (* and we will then show that the transform between observers
       is a causality-preserving automorphism. *)
    Section SpecRelCausality.

      (* spacetime interval and categorization of values *)
      Definition interval (v : v4) : R := (v _t)^2 - (v _x)^2 - (v _y)^2 - (v _z)^2.
      Definition lightlike (v : v4) : Prop := interval v = 0.
      Definition timelike (v : v4) : Prop := interval v > 0.
      Definition spacelike (v : v4) : Prop := interval v < 0.
      
      Lemma lightlike_eq :
        forall x y, lightlike (y -v- x) <-> |[ y^s -v- x^s ]| = |[ y^t -v- x^t ]|.
      Proof.
        unfold lightlike; unfold interval; unfold v4abs; unfold Rminus; split; intros.
        - apply sqrt_eq.
          destruct_coords.
          real_crush.
        - apply sqrt_inj in H; real_crush.
          destruct_coords.
          real_crush.
      Qed.
    
      Lemma lightlike_has_ph :
        forall m, forall x y,
          IOb m ->
          (exists p, Ph p /\ W m p x /\ W m p y) <-> lightlike (y -v- x).
      Proof.
        intros.
        rewrite lightlike_eq.
        auto.
      Qed.
    
      (* causality *)
      Definition cause (x y : v4) := timelike (y -v- x) /\ x _t < y _t.
      Definition causeP (x y : v4) := lightlike (y -v- x) /\ x _t < y _t.
      
      (* more facts about < that let us substitute when we think we can *)
      Lemma Rplus_lt_sub_r :
        forall a b c d, b < a -> c + a < d -> c + b < d.
      Proof.
        intros.
        assert (c + b < c + a) by real_crush.
        apply (Rlt_trans _ (c + a)); auto.
      Qed.
      Lemma Rplus_lt_sub_l :
        forall a b c d, b < a -> a + c < d -> b + c < d.
      Proof.
        intros.
        assert (b + c < a + c) by real_crush.
        apply (Rlt_trans _ (a + c)); auto.
      Qed.
      Lemma Rplus_le_lt_sub_r :
        forall a b c d, b <= a -> c + a < d -> c + b < d.
      Proof.
        intros.
        assert (c + b <= c + a) by real_crush.
        apply (Rle_lt_trans _ (c + a)); auto.
      Qed.
      Lemma Rplus_le_lt_sub_l :
        forall a b c d, b <= a -> a + c < d -> b + c < d.
      Proof.
        intros.
        assert (b + c <= a + c) by real_crush.
        apply (Rle_lt_trans _ (a + c)); auto.
      Qed.
      
      (* `cause` is transitive (`causeP` is not) *)
      Lemma cause_trans :
        forall x y, cause x y -> forall z, cause y z -> cause x z.
      Proof.
        unfold cause; unfold timelike; unfold interval; intros; destruct_pairs; split; real_crush.
        
        destruct_coords.
        unfold Rminus in *.
        real_normalize_bal; real_crush.
        
        (* massage inequalities to permit adding them *)
        apply sqrt_lt_1 in H; real_crush.
        rewrite sqrt_square in H; real_crush.

        apply sqrt_lt_1 in H0; real_crush.
        rewrite sqrt_square in H0; real_crush.
        
        apply sqrt_lt_0; real_crush.
        rewrite sqrt_square; real_crush.
 
        apply (Rplus_lt_sub_r _ _ _ _ H) in H0; real_crush.
        eapply (Rplus_le_lt_sub_l _ _ _ _ _ H0).
        Unshelve. (* XXX *)
        
        (* change goals momentarily ---
           the following obtains from the triangle inequality,
           and also boils down (nearly) immediately to the desired. *)
        assert (let y := (r6, r7, r5, 0) in
                let x := (r9, r10, r8, 0) in
                let z := (r3, r4, r2, 0) in
                |[ (z -v- y) +v+ (y -v- x) ]| <= |[ (z -v- y) ]| + |[ (y -v- x) ]|).
        apply v4triangle.
        real_crush.
        (* XXX automate this *)
        rewrite (Rplus_assoc _ (- r6) r6) in H3.
        rewrite (Rplus_assoc _ (- r7) r7) in H3.
        rewrite (Rplus_assoc _ (- r5) r5) in H3.
        repeat rewrite Rplus_opp_l in H3.
        real_crush.
      Qed.
      
    End SpecRelCausality.
    
    Lemma sqrt_neq_0 :
      forall x, sqrt x <> 0 -> x <> 0.
    Proof.
      unfold not in *.
      intros.
      subst.
      apply H.
      apply sqrt_0.
    Qed.

    Lemma no_luminal_iob :
      forall m k, forall x y, W m k x /\ W m k y ->
                              x <> y /\ IOb m /\ IOb k ->
                              |[ y^s -v- x^s ]| <> |[ y^t -v- x^t ]|.
    Proof.
      intros; unfold not; intros; destruct_pairs.

      (* we now prove a contradiction *)

        (* construct a photon *)
        rewrite <- ax_ph' in H1; [ | apply H2 ].
        inversion H1; clear H1; destruct_pairs.
        
        (* show distinct points in k's ref frame *)
        assert (ev m x <e> ev m y) by (apply ev_diff'; auto).
        pose (ax_ev' m k H2 H3 x) as e; inversion e; clear e.
        pose (ax_ev' m k H2 H3 y) as e; inversion e; clear e.
        assert (ev k x1 <e> ev k x2).
        autounfold.
        autounfold in H7.
        intros.
        apply H7.
        rewrite H8.
        rewrite H9.
        auto.
        assert (x1 <> x2) by (rewrite ev_diff' in H10; auto).
        
        (* show zero spatial component in k's ref frame *)
        (* TODO automate this reasoning *)
        assert (W k k x1).
        unfold "=e=" in H8; unfold propset_in in H8; unfold ev in H8.
        apply H8; auto.
        apply ax_sf in H12; auto.
        assert (W k k x2).
        unfold "=e=" in H9; unfold propset_in in H9; unfold ev in H9.
        apply H9; auto.
        apply ax_sf in H13; auto.
        destruct_pairs.

        (* show x1 x2 form a lightline in k's ref frame *)
        assert (W k x0 x1).
        unfold "=e=" in H8; unfold propset_in in H8; unfold ev in H8.
        apply H8; auto.
        assert (W k x0 x2).
        unfold "=e=" in H9; unfold propset_in in H9; unfold ev in H9.
        apply H9; auto.
        (* and construct the photon in question *)
        assert (exists p, Ph p /\ W k p x1 /\ W k p x2) by eauto.
        rewrite ax_ph' in H20; auto.
        
        (* demonstrate x1 ^t = x2 ^t produces contradiction *)
        assert (|[ x2 ^s -v- x1 ^s ]| = 0).
        destruct_coords; real_crush.
        rewrite H21 in H20.
        destruct_coords; real_crush.
        (* producing contradiction *)
        apply eq_sym in H20.
        apply sqrt_eq_0 in H20; real_crush.
        apply Rmult_integral in H20; destruct H20;
        assert (r = r0) by real_crush;
        rewrite H13 in H11; auto.
    Qed.

  End SpecRelTheory.

End SpecRel.