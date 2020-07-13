Require Import Reals.
Require Import Omega.
Require Import Coq.Program.Tactics.
Require Import Fourier.

(* expose reals to everyone *)
Export Reals.
Open Scope R_scope.

(* four-vectors are just 4-tuples for now *)
(* there is a lot of notation for your notational convenience *)
(* for some reason simpl doesn't like it, so use cbn liberally *)
Definition v4 : Set := R*R*R*R.

Definition v4x (v:v4) : R := fst (fst (fst v)).
Definition v4y (v:v4) := snd (fst (fst v)).
Definition v4z (v:v4) := snd (fst v).
Definition v4t (v:v4) := snd v.
Global Arguments v4x v : simpl never.
Global Arguments v4y v : simpl never.
Global Arguments v4z v : simpl never.
Global Arguments v4t v : simpl never.
Notation "v '_x'" := (v4x v) (at level 35).
Notation "v '_y'" := (v4y v) (at level 35).
Notation "v '_z'" := (v4z v) (at level 35).
Notation "v '_t'" := (v4t v) (at level 35).

(* simple ops *)
Definition v4abs (v:v4) := sqrt((v _x)^2 + (v _y)^2 + (v _z)^2 + (v _t)^2).
Global Arguments v4abs v : simpl never.
Notation "|[ x ]|" := (v4abs x) (at level 45).

Definition v4add (v1 v2:v4) :=
  match v1 with
  | (x1,y1,z1,t1) => match v2 with
                     | (x2,y2,z2,t2) => (x1+x2,y1+y2,z1+z2,t1+t2)
                     end
  end.
Infix "+v+" := v4add (at level 55).

Definition v4neg (v:v4) :=
  match v with
  | (x1,y1,z1,t1) => (-x1,-y1,-z1,-t1)
  end.
Notation "-v- v" := (v4neg v) (at level 40).

Definition v4sub (v1 v2:v4) := v1 +v+ (-v- v2).
Global Arguments v4sub v1 v2 : simpl never.
Infix "-v-" := v4sub (at level 55).

Definition v4dot (v1 v2:v4) :=
  match v1 with
  | (x1,y1,z1,t1) => match v2 with
                     | (x2,y2,z2,t2) => x1*x2 + y1*y2 + z1*z2 + t1*t2
                     end
  end.
(*
Infix ".v." := v4dot (at level 47).
*)

Definition v4mul (r:R) (v:v4) :=
  match v with
  | (x1,y1,z1,t1) => (r*x1,r*y1,r*z1,r*t1)
  end.
Infix "*v*" := v4mul (at level 50).

Definition v4div (v:v4) (r:R) := (1 / r) *v* v.
Infix "/v/" := v4div (at level 50).

(* projections *)
Definition v4sp (v:v4) := (fst v, 0).
Definition v4tp (v:v4) := ((0, 0, 0), snd v).
Global Arguments v4sp v : simpl never.
Global Arguments v4tp v : simpl never.
Notation "v ^s " := (v4sp v) (at level 35).
Notation "v ^t " := (v4tp v) (at level 35).

Lemma sqrt_eq :
  forall x y, x = y -> sqrt x = sqrt y.
Proof.
  intros.
  rewrite H.
  auto.
Qed.

(* precision unfold/simpl *)
Ltac vec_simpl :=
  cbn in *;
  match goal with
    | [ H : context [ pair _ _ = pair _ _ ] |- _ ] => inversion H; subst; clear H; vec_simpl
    | [ |- pair _ _ = pair _ _ ] => apply injective_projections; simpl; vec_simpl
    | [ H : context [ v4x (_, _, _, _) ] |- _ ] => unfold "_x" in H; cbn in H; vec_simpl
    | [ |- context [ v4x (_, _, _, _) ] ] => unfold "_x"; cbn; vec_simpl
    | [ H : context [ v4y (_, _, _, _) ] |- _ ] => unfold "_y" in H; cbn in H; vec_simpl
    | [ |- context [ v4y (_, _, _, _) ] ] => unfold "_y"; cbn; vec_simpl
    | [ H : context [ v4z (_, _, _, _) ] |- _ ] => unfold "_z" in H; cbn in H; vec_simpl
    | [ |- context [ v4z (_, _, _, _) ] ] => unfold "_z"; cbn; vec_simpl
    | [ H : context [ v4t (_, _, _, _) ] |- _ ] => unfold "_t" in H; cbn in H; vec_simpl
    | [ |- context [ v4t (_, _, _, _) ] ] => unfold "_t"; cbn; vec_simpl
    | [ H : context [ v4sp (_, _, _, _) ] |- _ ] => unfold "^s" in H; cbn in H; vec_simpl
    | [ |- context [ v4sp (_, _, _, _) ] ] => unfold "^s"; cbn; vec_simpl
    | [ H : context [ v4tp (_, _, _, _) ] |- _ ] => unfold "^t" in H; cbn in H; vec_simpl
    | [ |- context [ v4tp (_, _, _, _) ] ] => unfold "^t"; cbn; vec_simpl
    | [ H : context [ v4abs (_, _, _, _) ] |- _ ] => unfold "|[ _ ]|" in H; cbn in H; vec_simpl
    | [ |- context [ v4abs (_, _, _, _) ] ] => unfold "|[ _ ]|"; cbn; vec_simpl
    | [ H : context [ v4neg (_, _, _, _) ] |- _ ] => unfold "-v- _" in H; cbn in H; vec_simpl
    | [ |- context [ v4neg (_, _, _, _) ] ] => unfold "-v- _"; cbn; vec_simpl
    | [ H : context [ v4add (_, _, _, _) (_, _, _, _) ] |- _ ] =>
      unfold "+v+" in H; cbn in H; vec_simpl
    | [ |- context [ v4add (_, _, _, _) (_, _, _, _) ] ] => unfold "+v+"; cbn; vec_simpl
    | [ H : context [ v4sub (_, _, _, _) (_, _, _, _) ] |- _ ] =>
      unfold "_ -v- _" in H; cbn in H; vec_simpl
    | [ |- context [ v4sub (_, _, _, _) (_, _, _, _) ] ] => unfold "_ -v- _"; cbn; vec_simpl
    | [ H : context [ v4dot (_, _, _, _) (_, _, _, _) ] |- _ ] =>
      (*unfold ".v." in H;*) cbn in H; vec_simpl
    | [ |- context [ v4dot (_, _, _, _) (_, _, _, _) ] ] => (*unfold ".v.";*) cbn; vec_simpl
    | [ H : context [ v4mul _ (_, _, _, _) ] |- _ ] => unfold "*v*" in H; cbn in H; vec_simpl
    | [ |- context [ v4mul _ (_, _, _, _) ] ] => unfold "*v*"; cbn; vec_simpl
    | [ H : context [ v4div (_, _, _, _) _ ] |- _ ] => unfold "/v/" in H; cbn in H; vec_simpl
    | [ |- context [ v4div (_, _, _, _) _ ] ] => unfold "/v/"; cbn; vec_simpl
    | _ => idtac
  end.

Ltac destruct_coords :=
  repeat (match goal with
           | [ H : v4 |- _ ] => destruct H; destruct_coords
           | [ H : _ * R |- _ ] => destruct H; destruct_coords
           | _ => idtac
         end; vec_simpl).

(* massive expression simplification tactic---boils things down as far as they go *)
Ltac real_simpl' := (*idtac 0;*)
  vec_simpl;
  match goal with
    (* - 0 *)
    | [ H : context [ Ropp 0 ] |- _ ] => rewrite Ropp_0 in H; real_simpl'
    | [ |- context [ Ropp 0 ] ] => rewrite Ropp_0; real_simpl'
    (* 0 + _, _ + 0 *)
    | [ H : context [ Rplus _ 0 ] |- _ ] => try rewrite Rplus_0_r in H; real_simpl'
    | [ |- context [ Rplus _ 0 ] ] => try rewrite Rplus_0_r; real_simpl'
    | [ H : context [ Rplus 0 _ ] |- _ ] => rewrite Rplus_0_l in H; real_simpl'
    | [ |- context [ Rplus 0 _ ] ] => rewrite Rplus_0_l; real_simpl'
    (* 1 * _, _ * 1 *)
    | [ H : context [ Rmult 1 _ ] |- _ ] => rewrite Rmult_1_l in H; real_simpl'
    | [ |- context [ Rmult 1 _ ] ] => rewrite Rmult_1_l; real_simpl'
    | [ H : context [ Rmult _ 1 ] |- _ ] => rewrite Rmult_1_r in H; real_simpl'
    | [ |- context [ Rmult _ 1 ] ] => rewrite Rmult_1_r; real_simpl'
    (* 0 * _, _ * 0 *)
    | [ H : context [ Rmult 0 _ ] |- _ ] => rewrite Rmult_0_l in H; real_simpl'
    | [ |- context [ Rmult 0 _ ] ] => rewrite Rmult_0_l; real_simpl'
    | [ H : context [ Rmult _ 0 ] |- _ ] => rewrite Rmult_0_r in H; real_simpl'
    | [ |- context [ Rmult _ 0 ] ] => rewrite Rmult_0_r; real_simpl'
    (* sqrt 0 = 0 *)
    | [ H : context [ (sqrt 0) ] |- _ ] => rewrite sqrt_0 in H; real_simpl'
    | [ |- context [ (sqrt 0) ] ] => rewrite sqrt_0; real_simpl'
    (* sqrt 1 = 1 --- in lieu of dividing both sides by the same thing *)
    | [ H : context [ (sqrt 1) ] |- _ ] => rewrite sqrt_1 in H; real_simpl'
    | [ |- context [ (sqrt 1) ] ] => rewrite sqrt_1; real_simpl'
    (* r + -r *)
    | [ H : context [ Rplus ?x (Ropp ?x) ] |- _ ] => rewrite Rplus_opp_r in H; real_simpl'
    | [ |- context [ Rplus ?x (Ropp ?x) ] ] => rewrite Rplus_opp_r; real_simpl'
    | [ H : context [ Rplus (Ropp ?x) ?x ] |- _ ] => rewrite Rplus_opp_l in H; real_simpl'
    | [ |- context [ Rplus (Ropp ?x) ?x ] ] => rewrite Rplus_opp_l; real_simpl'
    (* - (r1 + r2) -> - r1 + - r2 *)
    | [ H : context [ - (_ + _) ] |- _ ] => rewrite Ropp_plus_distr in H; real_simpl'
    | [ |- context [ - (_ + _) ] ] => rewrite Ropp_plus_distr; real_simpl'
    (* - - x -> x *)
    | [ H : context [ - - _ ] |- _ ] => rewrite Ropp_involutive in H; real_simpl'
    | [ |- context [ - - _ ] ] => rewrite Ropp_involutive; real_simpl'
    (* sqrt x * sqrt x *)
    | [ H : context [ sqrt ?x * sqrt ?x ] |- _ ] => rewrite sqrt_sqrt in H; real_simpl'
    | [ |- context [ sqrt ?x * sqrt ?x ] ] => rewrite sqrt_sqrt; real_simpl'
    (* - _ * - _ *)
    | [ H : context [ - _ * - _ ] |- _ ] => rewrite Rmult_opp_opp in H; real_simpl'
    | [ |- context [ - _ * - _ ] ] => rewrite Rmult_opp_opp; real_simpl'
    (* - _ * _ *)
    | [ H : context [ - _ * _ ] |- _ ] => rewrite Ropp_mult_distr_l_reverse in H; real_simpl'
    | [ |- context [ - _ * _ ] ] => rewrite Ropp_mult_distr_l_reverse; real_simpl'
    | [ H : context [ _ * - _ ] |- _ ] => rewrite Ropp_mult_distr_r_reverse in H; real_simpl'
    | [ |- context [ _ * - _ ] ] => rewrite Ropp_mult_distr_r_reverse; real_simpl'
    (* sqrt (x * x) *)
                                                                         (*
    | [ H : context [ sqrt (?x * ?x) ] |- _ ] => rewrite sqrt_square; real_simpl
    | [ |- context [ sqrt (?x * ?x) ] ] => rewrite sqrt_square; real_simpl
*)
    | _ => idtac (*1*)
  end.
Ltac real_simpl := (*idtac 2;*)real_simpl'.

Ltac real_distr :=
  match goal with
    (* x * (y + z) *)
    | [ H : context [ _ * (_ + _) ] |- _ ] => rewrite Rmult_plus_distr_l; real_distr
    | [ |- context [ _ * (_ + _) ] ] => rewrite Rmult_plus_distr_l; real_distr
    (* (y + z) * x *)
    | [ H : context [ (_ + _) * _ ] |- _ ] => rewrite Rmult_plus_distr_r; real_distr
    | [ |- context [ (_ + _) * _ ] ] => rewrite Rmult_plus_distr_r; real_distr
    | _ => idtac
  end.

(* pulls a term x to the front---operates on normalized sums *)
Ltac front_Rplus_g x :=
  repeat rewrite <- Rplus_assoc;
  match goal with
    | [ |- context [x + ?y] ] => rewrite (Rplus_comm x y); front_Rplus_g x
    | [ |- context [(?y + x) + ?z] ] =>
      rewrite (Rplus_assoc y x z);
        rewrite (Rplus_comm x z);
        rewrite <- (Rplus_assoc y z x); front_Rplus_g x
    | _ => idtac
  end.

Ltac front_Rplus_h x H :=
  match type of H with
    | context [x + ?y] => rewrite (Rplus_comm x y) in H; front_Rplus_h x H
    | context [(?y + x) + ?z] =>
      rewrite (Rplus_assoc y x z) in H;
        rewrite (Rplus_comm x z) in H;
        rewrite <- (Rplus_assoc y z x) in H; front_Rplus_h x H
    | _ => idtac
  end.

(* front the tail end of the given sum *)
Ltac rs_cycsimpl_fronter_g sum :=
  match sum with
    | _ + ?sum' => front_Rplus_g sum'
    | ?sum' => front_Rplus_g sum'
  end.

Ltac rs_cycsimpl_cyc_g sum :=
  match sum with
    | ?sum' + _ => rs_cycsimpl_cyc_g sum'
    | ?x => front_Rplus_g x
  end.

(* pass the length of the given sum to the specified tactic, in continuation *)
Ltac rs_len sum tac :=
  match sum with
    | ?sum' + _ => rs_len sum' ltac:(fun x => tac (S x))
    | _ => tac 0%nat
  end.

Ltac rs_cycsimpl_g sz :=
  let iter := match goal with
                | [ |- context [ _ <= ?x ] ] => rs_cycsimpl_fronter_g x;
                                               try apply Rplus_le_compat_r; auto;
                                               rs_cycsimpl_cyc_g x
                | [ |- context [ _ < ?x ] ] => rs_cycsimpl_fronter_g x;
                                              try apply Rplus_lt_compat_r; auto;
                                              rs_cycsimpl_cyc_g x
                | [ |- context [ _ = ?x ] ] => rs_cycsimpl_fronter_g x;
                                              try apply Rplus_eq_compat_r; auto;
                                              rs_cycsimpl_cyc_g x
                | _ => idtac
              end in
  match sz with
    | S ?sz' => iter; rs_cycsimpl_g sz'
    | _ => iter
  end.

Ltac real_sum_cycsimpl_g :=
  match goal with
    | [ |- context [ _ <= ?sum ] ] => rs_len sum rs_cycsimpl_g
    | [ |- context [ _ < ?sum ] ] => rs_len sum rs_cycsimpl_g
    | [ |- context [ _ = ?sum ] ] => rs_len sum rs_cycsimpl_g
    | _ => idtac
  end.

(* normalize equalities and inequalities of sums *)
(* final form: no negations on either side *)
Ltac real_normalize_bal :=
  (* simplify equalities of sums *)
  repeat (rewrite <- Rplus_assoc in *); (* normalize the adds *)
  repeat match goal with (* flip inequalities *)
           | [ |- _ > _ ] => apply Rlt_gt
           | [ H : _ > _ |- _ ] => apply Rgt_lt in H
           | [ |- _ >= _ ] => apply Rle_ge
           | [ H : _ >= _ |- _ ] => apply Rge_le in H
         end;
  match goal with (* move things over an equality/inequality *)
    (* for goals *)
    (* recognize there's a negation on one side *)
    | [ |- context [ - ?x ] ] =>
      front_Rplus_g (- x);
        match goal with
          | [ |- _ = _ ] => apply (Rplus_eq_reg_r x)
          | [ |- _ < _ ] => apply (Rplus_lt_reg_r x)
          | [ |- _ <= _ ] => apply (Rplus_le_reg_r x)
        end;
        rewrite (Rplus_assoc _ (- x) x);
        rewrite (Rplus_opp_l x);
        try rewrite Rplus_0_r;
        real_normalize_bal
    (* for hypotheses *)
    | [ H : context[ - ?x ] |- _ ] =>
      front_Rplus_h (- x) H;
        match goal with
          | [ |- _ = _ ] => apply (Rplus_eq_compat_r x) in H
          | [ |- _ < _ ] => apply (Rplus_lt_compat_r x) in H
          | [ |- _ <= _ ] => apply (Rplus_le_compat_r x) in H
        end;
        rewrite (Rplus_assoc _ (-x) x) in H;
        rewrite (Rplus_opp_l x) in H;
        try rewrite Rplus_0_r in H;
        real_normalize_bal
    | _ => idtac
  end.

Ltac front_Rplus_sqrt_g :=
  match goal with
    | [ |- context [sqrt ?x + ?y] ] => rewrite (Rplus_comm x y); front_Rplus_sqrt_g x
    | [ |- context [(?y + sqrt ?x) + ?z] ] =>
      match z with
        | context [sqrt _] => fail 1
        | _ => rewrite (Rplus_assoc y (sqrt x) z);
              rewrite (Rplus_comm (sqrt x) z);
              rewrite <- (Rplus_assoc y z (sqrt x)); front_Rplus_sqrt_g
      end
    | _ => idtac
  end.

(* normalizing for inequality-solver tactic *)
Ltac real_normalize_right :=
  (* simplify equalities of sums *)
  repeat (rewrite <- Rplus_assoc in *); (* normalize the adds *)
  repeat match goal with (* flip inequalities *)
           | [ |- _ > _ ] => apply Rlt_gt
           | [ H : _ > _ |- _ ] => apply Rgt_lt in H
           | [ |- _ >= _ ] => apply Rle_ge
           | [ H : _ >= _ |- _ ] => apply Rge_le in H
         end;
  (*rewrite <- Rplus_0_r;
  rewrite <- Rplus_0_r at 1;*) (* adding a 0 to both sides *)
  match goal with (* move things over an equality/inequality *)
    (* for goals *)
    | [ |- ?x = _ ] =>
      match x with
        | 0 => fail 1
        | _ => apply (Rplus_eq_reg_r (- x));
              rewrite Rplus_opp_r;
              try rewrite Rplus_0_r;
              real_normalize_right
      end
    | [ |- ?x < _ ] =>
      match x with
        | 0 => fail 1
        | _ => apply (Rplus_lt_reg_r (- x));
              rewrite Rplus_opp_r;
              try rewrite Rplus_0_r;
              real_normalize_right
      end
    | [ |- ?x <= _ ] =>
      match x with
        | 0 => fail 1
        | _ => apply (Rplus_le_reg_r (- x));
              rewrite Rplus_opp_r;
              try rewrite Rplus_0_r;
              real_normalize_right
      end
    (* for hypotheses *)
    | [ H : ?x = _ |- _ ] =>
      match x with
        | 0 => fail 1
        | _ => apply (Rplus_eq_reg_r (- x)) in H;
              rewrite Rplus_opp_r in H;
              try rewrite Rplus_0_r in H;
              real_normalize_right
      end
    | [ H : ?x < _ |- _ ] =>
      match x with
        | 0 => fail 1
        | _ => apply (Rplus_lt_reg_r (- x));
              rewrite Rplus_opp_r;
              try rewrite Rplus_0_r;
              real_normalize_right
      end
    | [ H : ?x <= _ |- _ ] =>
      match x with
        | 0 => fail 1
        | _ => apply (Rplus_le_reg_r (- x));
              rewrite Rplus_opp_r;
              try rewrite Rplus_0_r;
              real_normalize_right
      end
    | _ => idtac
  end; front_Rplus_sqrt_g.

(* normalize in preparation to try to apply field tactic *)
Ltac real_normalize_field :=
  (* simplify equalities of sums *)
  repeat (rewrite <- Rplus_assoc in *); (* normalize the adds *)
  repeat match goal with (* flip inequalities *)
           | [ |- _ > _ ] => apply Rlt_gt
           | [ H : _ > _ |- _ ] => apply Rgt_lt in H
           | [ |- _ >= _ ] => apply Rle_ge
           | [ H : _ >= _ |- _ ] => apply Rge_le in H
         end;
  match goal with (* move things over an equality/inequality *)
    (* for goals *)
    | [ |- _ = ?x ] =>
      match x with
        | 0 => fail 1
        | _ => apply (Rplus_eq_reg_r (- x));
              rewrite Rplus_opp_r;
              try rewrite Rplus_0_r;
              real_normalize_field
      end
    | [ |- _ < ?x ] =>
      match x with
        | 0 => fail 1
        | _ => apply (Rplus_lt_reg_r (- x));
              rewrite Rplus_opp_r;
              try rewrite Rplus_0_r;
              real_normalize_field
      end
    | [ |- _ <= ?x ] =>
      match x with
        | 0 => fail 1
        | _ => apply (Rplus_le_reg_r (- x));
              rewrite Rplus_opp_r;
              try rewrite Rplus_0_r;
              real_normalize_field
      end
    (* for hypotheses *)
    | [ H : _ + ?x = _ |- _ ] =>
      apply (Rplus_eq_compat_r (- x)) in H;
        rewrite (Rplus_assoc _ x (- x)) in H;
        rewrite Rplus_opp_r in H;
        try rewrite Rplus_0_r in H;
        real_normalize_field
    | [ H : _ + ?x < _ |- _ ] =>
      apply (Rplus_lt_compat_r (- x)) in H;
        rewrite (Rplus_assoc _ x (- x)) in H;
        rewrite Rplus_opp_r in H;
        try rewrite Rplus_0_r in H;
        real_normalize_field
    | [ H : _ + ?x <= _ |- _ ] =>
      apply (Rplus_le_compat_r (- x)) in H;
        rewrite (Rplus_assoc _ x (- x)) in H;
        rewrite Rplus_opp_r in H;
        try rewrite Rplus_0_r in H;
        real_normalize_field
    | _ => idtac
  end.

Ltac real_crush' :=
  repeat (cbn in *;
           subst;
          real_simpl;
          try (real_normalize_bal; real_sum_cycsimpl_g));
  try (repeat (real_normalize_field; subst; real_simpl); field);
  try discrR; try fourier;
  real_normalize_bal; auto.

Ltac real_ineq_crush := (*try (idtac 4; fail);*)
  real_crush';(* try (idtac 5; fail);*)
  match goal with
    | [ |- sqrt _ = sqrt _ ] => apply sqrt_eq; real_ineq_crush; fail
    | _ => auto
  end;
  real_normalize_right; repeat real_simpl;
  match goal with
    | [ |- 0 < ?r * ?r ] => apply (Rlt_0_sqr r); real_ineq_crush; fail
    | [ |- 0 < sqrt _ ] => apply sqrt_lt_R0; real_ineq_crush; fail
    | [ |- 0 < _ + _ ] => apply Rplus_lt_0_compat; real_ineq_crush; fail
    | [ |- 0 < _ + _ ] => apply Rplus_lt_le_0_compat; real_ineq_crush; fail
    | [ |- 0 < _ + _ ] => apply Rplus_le_lt_0_compat; real_ineq_crush; fail
    | [ |- 0 <= sqrt _ ] => apply sqrt_positivity; real_ineq_crush; fail
    | [ |- 0 <= ?r * ?r ] => apply (Rle_0_sqr r); real_ineq_crush; fail
    | [ |- 0 <= _ + _ ] => apply Rplus_le_le_0_compat; real_ineq_crush; fail
    | [ |- 0 <= _ * _ ] => apply Rmult_le_pos; real_ineq_crush; fail
    | [ |- 0 < _ * _ ] => apply Rmult_lt_0_compat; real_ineq_crush; fail
    | _ => apply Rminus_eq_contra; real_ineq_crush; fail
    | _ => auto; fail
  end.

Ltac real_crush := real_crush'; try real_ineq_crush; auto.

Global Hint Resolve Rplus_opp_r.
Global Hint Resolve Rlt_dichotomy_converse.
Global Hint Resolve Rlt_0_sqr.

Theorem v4eq_0 : forall U V, U = V <-> U -v- V = (0,0,0,0).
Proof.
  split; intros; destruct_coords; real_crush.
Qed.

Theorem v4eq_dec : forall (U V : v4), U = V \/ U <> V.
Proof.
  intros.
  destruct_coords.
  assert (r5 = r2 \/ r5 <> r2) by apply Req_dec.
  assert (r6 = r3 \/ r6 <> r3) by apply Req_dec.
  assert (r4 = r1 \/ r4 <> r1) by apply Req_dec.
  assert (r0 = r  \/ r0 <> r ) by apply Req_dec.
  repeat match goal with
  | [ H : _ \/ _ |- _ ] => destruct H
  end;
  [ left; subst; auto | right; congruence .. ].
Qed.

Lemma le_square :
  forall x y, 0 <= x -> 0 <= y -> x * x <= y * y -> x <= y.
Proof.
  intros.
  apply sqrt_le_1_alt in H1.
  rewrite sqrt_square in H1; auto.
  rewrite sqrt_square in H1; auto.
Qed.

(*
Lemma square_lt_sum :
  forall x y z, 0 <= x -> 0 <= y -> 0 <= z -> x * x <= y * y + z * z -> x <= y + z.
Proof.
  (* very manhandley *)
  intros.
  apply (Rplus_le_compat 0 (y * z + z * y) _ _) in H2; real_crush.
  assert (y * z + z * y + y * y + z * z = (y + z) * (y + z)) by (real_distr; real_crush).
  rewrite H3 in H2.
  apply sqrt_le_1 in H2; auto; real_crush.
  - rewrite sqrt_square in H2; real_crush.
    rewrite sqrt_square in H2; real_crush.
Qed.
*)

Lemma v4abs_distr : forall (A B : v4),
  (|[ A +v+ B ]|) * (|[ A +v+ B ]|) =
  (|[ A ]|) * (|[ A ]|) + (|[ B ]|) * (|[ B ]|) + v4dot A B + v4dot B A.
Proof.
  intros.
  destruct_coords.
  real_crush.
Qed.

Theorem v4cauchy : forall (A B : v4),
  v4dot A B <= (|[ A ]|) * (|[ B ]|).
Proof.
  intros.
  destruct_coords.
  real_crush.
  (* Check sqrt_cauchy. *)
Admitted.

Theorem v4triangle : forall (A B : v4), |[ A +v+ B ]| <= |[ A ]| + |[ B ]|.
Proof.
  intros.
  apply le_square.
  - destruct_coords; real_crush.
  - destruct_coords; real_crush.
  - rewrite v4abs_distr.
    real_distr.
    real_crush.
    apply Rplus_le_compat; apply v4cauchy.
Qed.
