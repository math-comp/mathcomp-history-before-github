Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq choice fintype.
Require Import bigop ssralg orderedalg zint qnum poly polydiv polyorder.
Require Import perm matrix mxpoly polyXY binomial generic_quotient2.
Require Import cauchyreals.

Import GRing.Theory ORing.Theory AbsrNotation EpsilonReasonning.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Reserved Notation "{ 'realalg' T }" (at level 0, format "{ 'realalg'  T }").
Reserved Notation "{ 'alg' T }" (at level 0, format "{ 'alg'  T }").

Module RealAlg.

Local Open Scope ring_scope.

Section RealAlg.

Variable F : archiFieldType.

CoInductive algcreal := AlgCReal {
  creal_of_alg :> creal F;
  annul_creal : {poly F};
  _ : monic annul_creal;
  _ : (annul_creal.[creal_of_alg] == 0)%CR
}.

CoInductive algdom := AlgDom {
  annul_algdom : {poly F};
  center_alg : F;
  radius_alg : F;
  _ : monic annul_algdom;
  _ : radius_alg >= 0;
  _ : annul_algdom.[center_alg - radius_alg]
      * annul_algdom.[center_alg + radius_alg] <= 0
}.

Lemma radius_alg_ge0 x : 0 <= radius_alg x. Proof. by case: x. Qed.

Lemma monic_annul_algdom x : monic (annul_algdom x). Proof. by case: x. Qed.
Hint Resolve monic_annul_algdom.

Lemma annul_algdom_eq0 x : (annul_algdom x == 0) = false.
Proof. by rewrite (negPf (monic_neq0 _)). Qed.

Lemma algdomP x : (annul_algdom x).[center_alg x - radius_alg x]
  * (annul_algdom x).[center_alg x + radius_alg x] <= 0.
Proof. by case: x. Qed.

Definition algdom' := seq F.

Definition encode_algdom (x : algdom) : algdom' :=
  [:: center_alg x, radius_alg x & (annul_algdom x)].

Definition decode_algdom  (x : algdom') : option algdom :=
  if x is [::c, r & p']
  then let p := Poly p' in
    if (monic p =P true, (r >= 0) =P true,
       (p.[c - r] * p.[c + r] <= 0) =P true)
    is (ReflectT monic_p, ReflectT r_gt0, ReflectT hp)
      then Some (AlgDom monic_p r_gt0 hp)
      else None
  else None.

Lemma encode_algdomK : pcancel encode_algdom decode_algdom.
Proof.
case=> p c r monic_p r_ge0 hp /=; rewrite polyseqK.
do 3?[case: eqP; rewrite ?monic_p ?r_ge0 ?monic_p //] => monic_p' r_ge0' hp'.
by congr (Some (AlgDom _ _ _)); apply: bool_irrelevance.
Qed.

Definition algdom_EqMixin := PcanEqMixin encode_algdomK.
Canonical algdom_eqType := EqType algdom algdom_EqMixin.

Definition algdom_ChoiceMixin := PcanChoiceMixin encode_algdomK.
Canonical algdom_choiceType := ChoiceType algdom algdom_ChoiceMixin.

Fixpoint to_algcreal_of (p : {poly F}) (c r : F) (i : nat) : F :=
  match i with
    | 0 => c
    | i.+1 =>
      let c' := to_algcreal_of p c r i in
        if p.[c' - r / 2%:R ^+ i] * p.[c'] <= 0
          then c' - r / 2%:R ^+ i.+1
          else c' + r / 2%:R ^+ i.+1
  end.


Lemma to_algcreal_of_recP p c r i : 0 <= r ->
  `|to_algcreal_of p c r i.+1 - to_algcreal_of p c r i| <= r * 2%:R ^- i.+1.
Proof.
move=> r_ge0 /=; case: ifP=> _; rewrite addrAC subrr add0r ?absrN ger0_abs //;
by rewrite mulr_ge0 ?invr_ge0 ?exprn_ge0 ?ler0n.
Qed.

Lemma to_algcreal_ofP p c r i j : 0 <= r -> (i <= j)%N ->
  `|to_algcreal_of p c r j - to_algcreal_of p c r i| <= r * 2%:R ^- i.
Proof.
move=> r_ge0 leij; pose r' := r * 2%:R ^- j * (2%:R ^+ (j - i) - 1).
rewrite (@ler_trans _ r') //; last first.
  rewrite /r' -mulrA ler_wpmul2l // ler_pdivr_mull ?exprn_gt0 ?ltr0n //.
  rewrite -{2}(subnK leij) exprn_addr mulfK ?gtr_eqF ?exprn_gt0 ?ltr0n //.
  by rewrite ger_addl lerN10.
rewrite /r' subr_expn_1 addrK mul1r -{1 2}(subnK leij); set f := _  c r.
elim: (_ - _)%N=> [|k ihk]; first by rewrite subrr absr0 big_ord0 mulr0 lerr.
rewrite addSn big_ord_recl /= mulr_addr.
rewrite (ler_trans (ler_dist_add (f (k + i)%N) _ _)) //.
rewrite ler_add ?expr0 ?mulr1 ?to_algcreal_of_recP // (ler_trans ihk) //.
rewrite exprSr invf_mul -!mulrA !ler_wpmul2l ?invr_ge0 ?exprn_ge0 ?ler0n //.
by rewrite -mulr_sumr ler_sum // => l _ /=; rewrite exprS mulKf ?pnatr_eq0.
Qed.

Lemma alg_to_crealP (x : algdom) :
  creal_axiom (to_algcreal_of (annul_algdom x) (center_alg x) (radius_alg x)).
Proof.
pose_big_modulus m F.
  exists m=> e i j e_gt0 hi hj.
  wlog leij : i j {hi} hj / (j <= i)%N.
    move=> hwlog; case/orP: (leq_total i j)=> /hwlog; last exact.
    by rewrite distrC; apply.
  rewrite (ler_lt_trans (to_algcreal_ofP _ _ _ _)) ?radius_alg_ge0 //.
  rewrite ltr_pdivr_mulr ?gtr0E // -ltr_pdivr_mull //.
  by rewrite upper_nthrootP //; big.
by close.
Qed.

Definition alg_to_creal x := CReal (alg_to_crealP x).

Lemma exp2k_crealP : @creal_axiom F (fun i => 2%:R ^- i).
Proof.
pose_big_modulus m F.
  exists m=> e i j e_gt0 hi hj.
  wlog leij : i j {hj} hi / (i <= j)%N.
    move=> hwlog; case/orP: (leq_total i j)=> /hwlog; first exact.
    by rewrite distrC; apply.
  rewrite ger0_abs ?subr_ge0; last first.
    by rewrite ?ler_pinv -?topredE /= ?gtr0E // ler_eexpn2l ?ltr1n.
  rewrite -(@ltr_pmul2l _ (2%:R ^+ i )) ?gtr0E //.
  rewrite mulr_subr mulfV ?gtr_eqF ?gtr0E //.
  rewrite (@ler_lt_trans _ 1) // ?ger_addl ?oppr_le0 ?mulr_ge0 ?ger0E //.
  by rewrite -ltr_pdivr_mulr // mul1r upper_nthrootP //; big.
by close.
Qed.
Definition exp2k_creal := CReal exp2k_crealP.

Lemma exp2k_creal_eq0 : (exp2k_creal == 0)%CR.
Proof.
apply: eq_crealP; exists_big_modulus m F.
  move=> e i e_gt0 hi /=.
  rewrite subr0 gtr0_abs ?gtr0E // -ltr_pinv -?topredE /= ?gtr0E //.
  by rewrite invrK upper_nthrootP //; big.
by close.
Qed.

Notation lbound0_of p := (@lbound0P _ _ p _ _ _).

Lemma to_algcrealP (x : algdom) : ((annul_algdom x).[alg_to_creal x] == 0)%CR.
Proof.
set u := alg_to_creal _; set p := annul_algdom _.
pose r := radius_alg x; pose cr := cst_creal r.
have: ((p).[u - cr * exp2k_creal] *  (p).[u + cr * exp2k_creal] <= 0)%CR.
  apply: (@le_crealP _ 0%N)=> i _ /=.
  rewrite -/p -/r; set c := center_alg _.
  elim: i=> /= [|i].
    by rewrite !expr0 divr1 algdomP.
  set c' := to_algcreal_of _ _ _=> ihi.
  have [] := lerP (_ * p.[c' i]).
    rewrite addrNK -addrA -oppr_add -mulr2n -[_ / _ *+ _]mulr_natr.
    by rewrite -mulrA exprSr invf_mul mulfVK ?pnatr_eq0.
  rewrite addrK -addrA -mulr2n -[_ / _ *+ _]mulr_natr.
  rewrite -mulrA exprSr invf_mul mulfVK ?pnatr_eq0 // => /ler_pmul2l<-.
  rewrite mulr0 mulrCA !mulrA [X in X * _]mulrAC -mulrA.
  by rewrite mulr_ge0_le0 // -expr2 exprn_even_ge0.
rewrite exp2k_creal_eq0 mul_creal0 opp_creal0 add_creal0.
move=> hu pu0; apply: hu; pose e := (lbound pu0).
pose_big_enough i.
  apply: (@lt_crealP _ (e * e) i i); do ?by big.
    by rewrite !pmulr_rgt0 ?invr_gt0 ?ltr0n ?lbound_gt0.
  rewrite add0r [u]lock /= -!expr2.
  rewrite -[_.[_] ^+ _]ger0_abs ?exprn_even_ge0 // absrX.
  rewrite ler_pexpn2r -?topredE /= ?lbound_ge0 ?absr_ge0 //.
  by rewrite -lock (ler_trans _ (lbound0_of pu0)) //; do ?big.
by close.
Qed.

Definition to_algcreal_rec (x : algdom) :=
  AlgCReal (monic_annul_algdom x) (@to_algcrealP x).
Definition to_algcreal := locked to_algcreal_rec.

Lemma monic_annul_creal x : monic (annul_creal x).
Proof. by case: x. Qed.
Hint Resolve monic_annul_creal.

Lemma annul_creal_eq0 x : (annul_creal x == 0) = false.
Proof. by rewrite (negPf (monic_neq0 _)). Qed.

Lemma root_annul_creal x : ((annul_creal x).[x] == 0)%CR.
Proof. by case: x. Qed.
Hint Resolve root_annul_creal.

Lemma to_algdom_exists (x : algcreal) :
  { y : algdom | (to_algcreal y == x)%CR }.
Proof.
pose p := annul_creal x.
move: {2}(size p) (leqnn (size p))=> n.
elim: n x @p=> [x p|n ihn x p le_sp_Sn].
  by rewrite leqn0 size_poly_eq0 /p annul_creal_eq0.
move: le_sp_Sn; rewrite leq_eqVlt.
have [|//|eq_sp_Sn _] := ltngtP.
  by rewrite ltnS=> /ihn ihnp _; apply: ihnp.
have px0 := @root_annul_creal x; rewrite -/p -/root in px0.
have [|ncop] := boolP (coprimep p p^`()).
  move/coprimep_root => /(_ _ px0) /deriv_neq0_mono [r r_gt0 [i ir sm]].
  have p_chg_sign : p.[x i - r] * p.[x i + r] <= 0.
    have [/accr_pos_incr hp|/accr_neg_decr hp] := sm.
      have hpxj : forall j, (i <= j)%N ->
        (p.[x i - r] <= p.[x j]) * (p.[x j] <= p.[x i + r]).
        move=> j hj.
          suff:  p.[x i - r] <= p.[x j] <= p.[x i + r] by case/andP=> -> ->.
        rewrite !hp 1?addrAC ?subrr ?add0r ?absrN;
        rewrite ?(gtr0_abs r_gt0) //;
          do ?by rewrite ltrW ?cauchymodP ?(leq_trans _ hj).
        by rewrite -ler_distl ltrW ?cauchymodP ?(leq_trans _ hj).
      rewrite mulr_le0_ge0 //; apply/le_creal_cst; rewrite -px0;
      by apply: (@le_crealP _ i)=> h hj /=; rewrite hpxj.
    have hpxj : forall j, (i <= j)%N ->
      (p.[x i + r] <= p.[x j]) * (p.[x j] <= p.[x i - r]).
      move=> j hj.
        suff:  p.[x i + r] <= p.[x j] <= p.[x i - r] by case/andP=> -> ->.
      rewrite !hp 1?addrAC ?subrr ?add0r ?absrN;
      rewrite ?(gtr0_abs r_gt0) //;
        do ?by rewrite ltrW ?cauchymodP ?(leq_trans _ hj).
      by rewrite andbC -ler_distl ltrW ?cauchymodP ?(leq_trans _ hj).
    rewrite mulr_ge0_le0 //; apply/le_creal_cst; rewrite -px0;
    by apply: (@le_crealP _ i)=> h hj /=; rewrite hpxj.
  pose y := (AlgDom (monic_annul_creal x) (ltrW r_gt0) p_chg_sign).
  have eq_py_px: (p.[to_algcreal y] == p.[x])%CR.
    rewrite /to_algcreal -lock.
    by have := @to_algcrealP y; rewrite /= -/p=> ->; apply: eq_creal_sym.
  exists y.
  move: sm=> /strong_mono_bound [k k_gt0 hk].
  rewrite -/p; apply: eq_crealP.
  exists_big_modulus m F.
    move=> e j e_gt0 hj; rewrite (ler_lt_trans (hk _ _ _ _)) //.
    + rewrite /to_algcreal -lock.
      rewrite (ler_trans (to_algcreal_ofP _ _ _ (leq0n _))) ?(ltrW r_gt0) //.
      by rewrite expr0 divr1.
    + rewrite ltrW // cauchymodP //; do ?by big.
    rewrite -ltr_pdivl_mull //.
    by rewrite (@eqmodP _ _ _ eq_py_px) // ?pmulr_rgt0 ?invr_gt0 //; big.
  by close.
case: (@smaller_factor _ p p^`() x); rewrite ?monic_annul_creal //.
  rewrite gtNdvdp // -?size_poly_eq0 size_deriv eq_sp_Sn //=.
  apply: contra ncop=> /eqP n_eq0; move: eq_sp_Sn; rewrite n_eq0.
  by move=> /eqP /size1P [c c_neq0 ->]; rewrite derivC coprimep0 polyC_eqp1.
move=> r /andP [hsr monic_r rx_eq0].
apply: (ihn (AlgCReal monic_r rx_eq0))=> /=.
by rewrite -ltnS -eq_sp_Sn.
Qed.

Definition to_algdom x := projT1 (to_algdom_exists x).

Lemma to_algdomK x : (to_algcreal (to_algdom x) == x)%CR.
Proof. by rewrite /to_algdom; case: to_algdom_exists. Qed.

Hint Resolve eq_creal_refl.
Hint Resolve le_creal_refl.

Lemma eq_algcreal_dec (x y : algcreal) :
  {(x == y)%CR} + {(x != y)%CR}.
Proof.
pose p := annul_creal x; pose q := annul_creal y.
move: {2}(_ + _)%N (leqnn (size p + size q))=> n.
elim: n x y @p @q => [x y p q|n ihn x y p q le_sp_Sn].
  by rewrite leqn0 addn_eq0 !size_poly_eq0 /p /q  annul_creal_eq0.
move: le_sp_Sn; rewrite leq_eqVlt; have [|//|eq_sp_Sn _] := ltngtP.
  by rewrite ltnS=> /ihn ihnp _; apply: ihnp.
have px0 : (p.[x] == 0)%CR by apply: root_annul_creal.
have qy0 : (q.[y] == 0)%CR by apply: root_annul_creal.
have [cpq|ncpq] := boolP (coprimep p q).
  right; move: (cpq)=> /coprimep_root /(_ px0).
  rewrite -qy0=> neq_qx_qy.
  pose_big_enough i.
    apply: (@neq_crealP _ (lbound neq_qx_qy
      / poly_accr_bound q 0 (maxr (ubound x) (ubound y))) i i); do ?by big.
    + by rewrite ?pmulr_rgt0 ?invr_gt0 ?lbound_gt0 ?poly_accr_bound_gt0.
    rewrite ler_pdivr_mulr ?poly_accr_bound_gt0 //.
    rewrite (ler_trans _ (poly_accr_bound1P _ _ _));
    by rewrite ?subr0 ?ler_maxr ?uboundP ?orbT //; apply: lboundP; do ?big.
  by close.
have [eq_pq|] := altP (p =P q).
  move: (qy0); rewrite -eq_pq=> py0.
  have [cpp'|ncpp'] := boolP (coprimep p p^`()).
    have p'x_neq0 := coprimep_root cpp' px0.
    have p'y_neq0 := coprimep_root cpp' py0.
    have [rx rx_gt0 [i hi smpx]] := deriv_neq0_mono p'x_neq0.
    have [ry ry_gt0 [j hj smpy]] := deriv_neq0_mono p'y_neq0.
    have [eq_xy|neq_xy] := lerP `|x i - y j| (rx + ry).
      have smpxy := merge_mono _ _ _ smpx smpy.
      have [//|//|//|cx cx_gt0 hcx] := strong_mono_bound (smpxy _ _ _).
      left; apply: eq_crealP.
      have eq_px_py : (p.[x] == p.[y])%CR by rewrite px0 py0.
      exists_big_modulus m F.
        move=> e k e_gt0 hk.
        rewrite (ler_lt_trans (hcx _ _ _ _)) ?split_interval //.
        + by rewrite ltrW ?cauchymodP //; big.
        + by rewrite orbC ltrW ?cauchymodP //; big.
        rewrite -ltr_pdivl_mull //.
        by rewrite (@eqmodP _ _ _ eq_px_py) // ?pmulr_rgt0 ?invr_gt0 //; big.
      by close.
    right; pose_big_enough k.
      apply: (@neq_crealP _ (`|x i - y j| - (rx + ry)) k k); do ?by big.
        by rewrite subr_gt0.
      rewrite -(ler_add2r (rx + ry)) addrNK addrA.
      rewrite (ler_trans (ler_dist_add (y k) _ _)) ?ler_add //.
        rewrite distrC (ler_trans (ler_dist_add (x k) _ _)) ?ler_add //.
          by rewrite distrC.
        by rewrite ltrW // cauchymodP //; big.
      by rewrite ltrW // cauchymodP //; big.
    by close.
  case: (@smaller_factor _ p p^`() x); rewrite ?monic_annul_creal //.
    have sp_gt1 : (1 < size p)%N.
      have [|//|/eqP /size1P [c c_neq0 eq_pc]] := ltngtP.
         rewrite ltnS leqn0=> /eqP sp_eq0.
         by move: eq_sp_Sn; rewrite -eq_pq sp_eq0.
      by move/negPf: ncpp'<-; rewrite eq_pc derivC coprimep0 polyC_eqp1.
    by rewrite gtNdvdp // -?size_poly_eq0 size_deriv -(subnKC sp_gt1).
  move=> r /andP [hsr monic_r rx_eq0].
  apply: (ihn (AlgCReal monic_r rx_eq0))=> /=.
  by rewrite -ltnS -eq_sp_Sn ltn_add2r.
rewrite -monic_eqp /p /q // /eqp negb_and.
have [ndiv_pq _|_ /= ndiv_qp] := boolP (~~ _).
  case: (@smaller_factor _ p q x); rewrite /p //.
  move=> r /andP[r_gt0 monic_r rx_eq0].
  apply: (ihn (AlgCReal monic_r rx_eq0) y)=> /=.
  by rewrite -ltnS -eq_sp_Sn ltn_add2r.
case: (@smaller_factor _ q p y); do ?by rewrite /q 1?coprimep_sym.
move=> r /andP[r_gt0 monic_r ry_eq0].
apply: (ihn x (AlgCReal monic_r ry_eq0))=> /=.
by rewrite -ltnS -eq_sp_Sn ltn_add2l.
Qed.

Definition eq_algcreal : rel algcreal := eq_algcreal_dec.

Lemma eq_algcrealP (x y : algcreal) : reflect (x == y)%CR (eq_algcreal x y).
Proof. by rewrite /eq_algcreal; case: eq_algcreal_dec=> /=; constructor. Qed.
Implicit Arguments eq_algcrealP [x y].

Lemma neq_algcrealP (x y : algcreal) : reflect (x != y)%CR (~~ eq_algcreal x y).
Proof. by rewrite /eq_algcreal; case: eq_algcreal_dec=> /=; constructor. Qed.
Implicit Arguments neq_algcrealP [x y].
Prenex Implicits eq_algcrealP neq_algcrealP.

Lemma eq_algcreal_refl : reflexive eq_algcreal.
Proof. by move=> x; apply/eq_algcrealP; apply: eq_creal_refl. Qed.

Lemma eq_algcreal_sym : symmetric eq_algcreal.
Proof. by move=> x y; apply/eq_algcrealP/eq_algcrealP=> /eq_creal_sym. Qed.

Lemma eq_algcreal_trans : transitive eq_algcreal.
Proof.
by move=> x y z /eq_algcrealP /eq_creal_trans h /eq_algcrealP /h /eq_algcrealP.
Qed.

Lemma eq_algcreal_to_algdom x : eq_algcreal (to_algcreal (to_algdom x)) x.
Proof. by apply/eq_algcrealP; apply: to_algdomK. Qed.

Canonical eq_algcreal_rel :=
  EquivRelIndirect eq_algcreal_refl eq_algcreal_sym eq_algcreal_trans eq_algcreal_to_algdom.

Definition alg := [qT algcreal %/ eq_algcreal]%qT.

Definition alg_of of (phant F) := alg.
Identity Coercion type_alg_of : alg_of >-> alg.

Notation "{ 'alg'  F }" := (alg_of (Phant F)).

Canonical alg_eqType := [eqType of alg].
Canonical alg_choiceType := [choiceType of alg].
Canonical alg_quotType := [quotType of alg].
Canonical alg_of_eqType := [eqType of {alg F}].
Canonical alg_of_choiceType := [choiceType of {alg F}].
Canonical alg_of_quotType := [quotType of {alg F}].

Local Open Scope quotient_scope.

Definition cst_algcreal (x : F) :=
  AlgCReal (monic_factor _) (@root_cst_creal _ x).

Lemma size_annul_creal_gt1 (x : algcreal) :
  (1 < size (annul_creal x))%N.
Proof.
apply: (@has_root_creal_size_gt1 _ x).
  by rewrite monic_neq0 // monic_annul_creal.
exact: root_annul_creal.
Qed.

Lemma is_root_annul_creal (x : algcreal) (y : creal F) :
  (x == y)%CR -> ((annul_creal x).[y] == 0)%CR.
Proof. by move <-. Qed.

Definition AlgCRealOf (p : {poly F}) (x : creal F)
  (p_neq0 : p != 0) (px_eq0 : (p.[x] == 0)%CR) :=
  AlgCReal (monic_monic_from_neq0 p_neq0) (root_monic_from_neq0 px_eq0).

Lemma annul_sub_algcreal_neq0 (x y : algcreal) :
  annul_sub (annul_creal x) (annul_creal y) != 0.
Proof. by rewrite annul_sub_neq0 ?monic_neq0. Qed.

Lemma root_sub_algcreal (x y : algcreal) :
  ((annul_sub (annul_creal x) (annul_creal y)).[x - y] == 0)%CR.
Proof. by rewrite root_annul_sub_creal ?root_annul_creal ?monic_neq0. Qed.

Definition sub_algcreal (x y : algcreal) : algcreal :=
  AlgCRealOf (annul_sub_algcreal_neq0 x y) (@root_sub_algcreal x y).

Lemma root_opp_algcreal (x : algcreal) :
  ((annul_creal (sub_algcreal (cst_algcreal 0) x)).[- x] == 0)%CR.
Proof. by apply: is_root_annul_creal; rewrite /= add_0creal. Qed.

Definition opp_algcreal (x : algcreal) : algcreal :=
  AlgCReal (@monic_annul_creal _) (@root_opp_algcreal x).

Local Notation m0 := (fun _ => 0%N).

Lemma root_add_algcreal (x y : algcreal) :
  ((annul_creal (sub_algcreal x (opp_algcreal y))).[x + y] == 0)%CR.
Proof.
apply: is_root_annul_creal; apply: eq_crealP.
by exists m0=> * /=; rewrite opprK subrr absr0.
Qed.

Definition add_algcreal (x y : algcreal) : algcreal :=
  AlgCReal (@monic_annul_creal _) (@root_add_algcreal x y).

Lemma annul_div_algcreal_neq0 (x y : algcreal) :
   (annul_creal y).[0] != 0 ->
   annul_div (annul_creal x) (annul_creal y) != 0.
Proof. by move=> ?; rewrite annul_div_neq0 ?monic_neq0. Qed.

Lemma root_div_algcreal (x y : algcreal) (y_neq0 : (y != 0)%CR) :
  (annul_creal y).[0] != 0 ->
  ((annul_div (annul_creal x) (annul_creal y)).[x / y_neq0] == 0)%CR.
Proof. by move=> hx; rewrite root_annul_div_creal ?monic_neq0. Qed.

Lemma simplify_algcreal (x : algcreal) (x_neq0 : (x != 0)%CR) :
  {y | ((annul_creal y).[0] != 0) & ((y != 0)%CR * (x == y)%CR)%type}.
Proof.
elim: size {-3}x x_neq0 (leqnn (size (annul_creal x))) =>
  {x} [|n ihn] x x_neq0 hx.
  by move: hx; rewrite leqn0 size_poly_eq0 annul_creal_eq0.
have [dvdX|ndvdX] := boolP ('X %| annul_creal x); last first.
  by exists x=> //; rewrite -rootE -dvdp_factorl subr0.
have monic_p: monic (@annul_creal x %/ 'X).
  by rewrite -(monic_mulr _ (@monicX _)) divpK //.
have root_p: ((@annul_creal x %/ 'X).[x] == 0)%CR.
  have := @eq_creal_refl _ ((annul_creal x).[x])%CR.
  rewrite -{1}(divpK dvdX) horner_crealM // root_annul_creal.
  by case/poly_mul_creal_eq0=> //; rewrite horner_crealX.
have [//|/=|y *] := ihn (AlgCReal monic_p root_p); last by exists y.
by rewrite size_divp ?size_polyX ?polyX_eq0 ?leq_sub_add ?add1n.
Qed.

Definition div_algcreal (x y : algcreal) :=
  match eq_algcreal_dec y (cst_algcreal 0) with
    | left y_eq0 => cst_algcreal 0
    | right y_neq0 =>
      let: exist2 y' py'0_neq0 (y'_neq0, _) := simplify_algcreal y_neq0 in
      AlgCRealOf (annul_div_algcreal_neq0 x py'0_neq0)
                 (@root_div_algcreal x y' y'_neq0 py'0_neq0)
  end.

Lemma root_inv_algcreal (x : algcreal) (x_neq0 : (x != 0)%CR) :
  ((annul_creal (div_algcreal (cst_algcreal 1) x)).[x_neq0^-1] == 0)%CR.
Proof.
rewrite /div_algcreal; case: eq_algcreal_dec=> [/(_ x_neq0)|x_neq0'] //=.
case: simplify_algcreal=> x' px'0_neq0 [x'_neq0 eq_xx'].
apply: is_root_annul_creal;rewrite /= -(@eq_creal_inv _ _ _ x_neq0) //.
by apply: eq_crealP; exists m0=> * /=; rewrite div1r subrr absr0.
Qed.

Definition inv_algcreal (x : algcreal) :=
  match eq_algcreal_dec x (cst_algcreal 0) with
    | left x_eq0 => cst_algcreal 0
    | right x_neq0 =>
      AlgCReal (@monic_annul_creal _) (@root_inv_algcreal _ x_neq0)
  end.

Lemma div_creal_creal (y : creal F) (y_neq0 : (y != 0)%CR) :
  (y / y_neq0 == 1%:CR)%CR.
Proof.
apply: eq_crealP; exists_big_modulus m F.
  move=> e i e_gt0 hi; rewrite /= divff ?subrr ?absr0 //.
  by rewrite (@creal_neq_always _ _ 0%CR); do ?big.
by close.
Qed.

Lemma root_mul_algcreal (x y : algcreal) :
  ((annul_creal (div_algcreal x (inv_algcreal y))).[x * y] == 0)%CR.
Proof.
rewrite /div_algcreal /inv_algcreal.
case: (eq_algcreal_dec y)=> [->|y_neq0]; apply: is_root_annul_creal.
  rewrite mul_creal0; case: eq_algcreal_dec=> // neq_00.
  by move: (eq_creal_refl neq_00).
case: eq_algcreal_dec=> /= [yV_eq0|yV_neq0].
  have: (y * y_neq0^-1 == 0)%CR by rewrite yV_eq0 mul_creal0.
  by rewrite div_creal_creal=> /eq_creal_cst; rewrite oner_eq0.
case: simplify_algcreal=> y' py'0_neq0 [y'_neq0 /= eq_yy'].
rewrite -(@eq_creal_inv _ _ _ yV_neq0) //.
by apply: eq_crealP; exists m0=> * /=; rewrite invrK subrr absr0.
Qed.

Definition mul_algcreal (x y : algcreal) :=
  AlgCReal (@monic_annul_creal _) (@root_mul_algcreal x y).

Local Open Scope quotient_scope.

Local Notation zero_algcreal := (cst_algcreal 0).
Local Notation one_algcreal := (cst_algcreal 1).

Definition to_alg : F -> {alg F} := locked (\pi \o cst_algcreal).
Notation "x %:RA" := (to_alg x)
  (at level 2, left associativity, format "x %:RA").

Lemma to_algE x : x%:RA = \pi (cst_algcreal x).
Proof. by unlock to_alg. Qed.

Canonical to_algE_pi_morph x := PiMorph (x%:RA) (to_algE x).

Local Notation zero_alg := 0%:RA.
Local Notation one_alg := 1%:RA.

Lemma equiv_alg (x y : algcreal) : (x == y)%CR <-> (x = y %[m {alg F}]).
Proof.
split; first by move=> /eq_algcrealP /equivP.
by move=> /equivP /eq_algcrealP.
Qed.

Lemma nequiv_alg (x y : algcreal) : reflect (x != y)%CR (x != y %[m {alg F}]).
Proof. by rewrite equivE; apply: neq_algcrealP. Qed.
Implicit Arguments nequiv_alg [x y].
Prenex Implicits nequiv_alg.

Lemma pi_algK (x : algcreal) : (repr (\pi_{alg F} x) == x)%CR.
Proof. by apply/equiv_alg; rewrite reprK. Qed.

Definition add_alg : {alg F} -> {alg F} -> {alg F} :=
  locked (fun x y => \pi (add_algcreal (repr x) (repr y))).

Lemma pi_add : {morph \pi_{alg F} : x y / add_algcreal x y >-> add_alg x y}.
Proof. by unlock add_alg=> x y; rewrite -equiv_alg /= !pi_algK. Qed.

Canonical add_pi_morph := PiMorph2 add_alg pi_add.

Definition opp_alg : {alg F} -> {alg F} :=
  locked (fun x => \pi (opp_algcreal (repr x))).

Lemma pi_opp : {morph \pi_{alg F} : x / opp_algcreal x >-> opp_alg x}.
Proof. by unlock opp_alg=> x; rewrite -equiv_alg /= !pi_algK. Qed.

Canonical opp_pi_morph := PiMorph1 opp_alg pi_opp.

Definition mul_alg : {alg F} -> {alg F} -> {alg F} :=
  locked (fun x y => \pi (mul_algcreal (repr x) (repr y))).

Lemma pi_mul : {morph \pi_{alg F} : x y / mul_algcreal x y >-> mul_alg x y}.
Proof. by unlock mul_alg=> x y; rewrite -equiv_alg /= !pi_algK. Qed.

Canonical mul_pi_morph := PiMorph2 mul_alg pi_mul.

Definition inv_alg : {alg F} -> {alg F} :=
  locked (fun x => \pi (inv_algcreal (repr x))).

Lemma pi_inv : {morph \pi_{alg F} : x / inv_algcreal x >-> inv_alg x}.
Proof.
unlock inv_alg=> x; symmetry; rewrite -equiv_alg /= /inv_algcreal.
case: eq_algcreal_dec=> /= [|x'_neq0].
  by rewrite pi_algK; case: eq_algcreal_dec.
move: x'_neq0 (x'_neq0); rewrite {1}pi_algK.
case: eq_algcreal_dec=> // x'_neq0' x_neq0 x'_neq0 /=.
by apply: eq_creal_inv; rewrite pi_algK.
Qed.

Canonical inv_pi_morph := PiMorph1 inv_alg pi_inv.

Lemma add_algA : associative add_alg.
Proof.
elim/quotW=> x; elim/quotW=> y; elim/quotW=> z; rewrite !piE -equiv_alg.
by apply: eq_crealP; exists m0=> * /=; rewrite addrA subrr absr0.
Qed.

Lemma add_algC : commutative add_alg.
Proof.
elim/quotW=> x; elim/quotW=> y; rewrite !piE -equiv_alg /=.
by apply: eq_crealP; exists m0=> * /=; rewrite [X in _ - X]addrC subrr absr0.
Qed.


Lemma add_0alg : left_id zero_alg add_alg.
Proof. by elim/quotW=> x; rewrite !piE -equiv_alg /= add_0creal. Qed.

Lemma add_Nalg : left_inverse zero_alg opp_alg add_alg.
Proof.
elim/quotW=> x; rewrite !piE -equiv_alg /=.
by apply: eq_crealP; exists m0=> *; rewrite /= addNr subr0 absr0.
Qed.

Definition alg_zmodMixin :=  ZmodMixin add_algA add_algC add_0alg add_Nalg.
Canonical alg_zmodType := Eval hnf in ZmodType alg alg_zmodMixin.
Canonical alg_of_zmodType := Eval hnf in ZmodType {alg F} alg_zmodMixin.

Lemma add_pi x y : \pi_{alg F} x + \pi_{alg F} y
  = \pi_{alg F} (add_algcreal x y).
Proof. by rewrite [_ + _]piE. Qed.

Lemma opp_pi x : - \pi_{alg F} x  = \pi_{alg F} (opp_algcreal x).
Proof. by rewrite [- _]piE. Qed.

Lemma zeroE : 0 = \pi_{alg F} zero_algcreal.
Proof. by rewrite [0]piE. Qed.

Lemma sub_pi x y : \pi_{alg F} x - \pi_{alg F} y
  = \pi_{alg F} (add_algcreal x (opp_algcreal y)).
Proof. by rewrite [_ - _]piE. Qed.

Lemma mul_algC : commutative mul_alg.
Proof.
elim/quotW=> x; elim/quotW=> y; rewrite !piE -equiv_alg /=.
by apply: eq_crealP; exists m0=> * /=; rewrite mulrC subrr absr0.
Qed.

Lemma mul_algA : associative mul_alg.
Proof.
elim/quotW=> x; elim/quotW=> y; elim/quotW=> z; rewrite !piE -equiv_alg /=.
by apply: eq_crealP; exists m0=> * /=; rewrite mulrA subrr absr0.
Qed.

Lemma mul_1alg : left_id one_alg mul_alg.
Proof. by elim/quotW=> x; rewrite piE -equiv_alg /= mul_1creal. Qed.

Lemma mul_alg_addl : left_distributive mul_alg add_alg.
Proof.
elim/quotW=> x; elim/quotW=> y; elim/quotW=> z; rewrite !piE -equiv_alg /=.
by apply: eq_crealP; exists m0=> * /=; rewrite mulr_addl subrr absr0.
Qed.

Implicit Arguments neq_creal_cst [F x y].
Prenex Implicits neq_creal_cst.

Lemma nonzero1_alg : one_alg != zero_alg.
Proof. by rewrite !piE -(rwP nequiv_alg) (rwP neq_creal_cst) oner_eq0. Qed.

Definition alg_comRingMixin :=
  ComRingMixin mul_algA mul_algC mul_1alg mul_alg_addl nonzero1_alg.
Canonical alg_Ring := Eval hnf in RingType alg alg_comRingMixin.
Canonical alg_comRing := Eval hnf in ComRingType alg mul_algC.
Canonical alg_of_Ring := Eval hnf in RingType {alg F} alg_comRingMixin.
Canonical alg_of_comRing := Eval hnf in ComRingType {alg F} mul_algC.

Lemma mul_pi x y : \pi_{alg F} x * \pi_{alg F} y
  = \pi_{alg F} (mul_algcreal x y).
Proof. by rewrite [_ * _]piE. Qed.

Lemma oneE : 1 = \pi_{alg F} one_algcreal.
Proof. by rewrite [1]piE. Qed.

Lemma mul_Valg (x : alg) : x != zero_alg -> mul_alg (inv_alg x) x = one_alg.
Proof.
elim/quotW: x=> x; rewrite !piE /= -(rwP nequiv_alg) -equiv_alg /= => x_neq0.
rewrite /inv_algcreal; case: eq_algcreal_dec=> [/(_ x_neq0) //|/= x_neq0'].
apply: eq_crealP; exists_big_modulus m F.
  by move=> * /=; rewrite mulVf ?subrr ?absr0 ?creal_neq0_always //; big.
by close.
Qed.

Lemma inv_alg0 : inv_alg zero_alg = zero_alg.
Proof.
rewrite !piE -equiv_alg /= /inv_algcreal.
by case: eq_algcreal_dec=> //= zero_neq0; move: (eq_creal_refl zero_neq0).
Qed.

Definition AlgFieldUnitMixin := FieldUnitMixin mul_Valg inv_alg0.
Canonical alg_unitRing :=
  Eval hnf in UnitRingType alg AlgFieldUnitMixin.
Canonical alg_comUnitRing := Eval hnf in [comUnitRingType of alg].
Canonical alg_of_unitRing :=
  Eval hnf in UnitRingType {alg F} AlgFieldUnitMixin.
Canonical alg_of_comUnitRing := Eval hnf in [comUnitRingType of {alg F}].

Lemma field_axiom : GRing.Field.mixin_of alg_unitRing. Proof. exact. Qed.

Definition AlgFieldIdomainMixin := (FieldIdomainMixin field_axiom).
Canonical alg_iDomain :=
  Eval hnf in IdomainType alg (FieldIdomainMixin field_axiom).
Canonical alg_fieldType := FieldType alg field_axiom.
Canonical alg_of_iDomain :=
  Eval hnf in IdomainType {alg F} (FieldIdomainMixin field_axiom).
Canonical alg_of_fieldType := FieldType {alg F} field_axiom.

Lemma inv_pi x : (\pi_{alg F} x)^-1  = \pi_{alg F} (inv_algcreal x).
Proof. by rewrite [_^-1]piE. Qed.

Lemma div_pi x y : \pi_{alg F} x / \pi_{alg F} y
  = \pi_{alg F} (mul_algcreal x (inv_algcreal y)).
Proof. by rewrite [_ / _]piE. Qed.

Lemma ltVge_algcreal_dec (x y : algcreal) : {(x < y)%CR} + {(y <= x)%CR}.
Proof.
have [eq_xy|/neq_creal_ltVgt [lt_xy|lt_yx]] := eq_algcreal_dec x y;
by [right; rewrite eq_xy | left | right; apply: lt_crealW].
Qed.

Definition lt_algcreal : rel algcreal := ltVge_algcreal_dec.

Definition lt_alg : rel {alg F} :=
  locked (fun x y => lt_algcreal (repr x) (repr y)).

Lemma lt_alg_pi : {mono \pi_{alg F} : x y / lt_algcreal x y >-> lt_alg x y}.
Proof.
move=> x y; unlock lt_alg; rewrite /lt_algcreal.
by do 2!case: ltVge_algcreal_dec=> //=; rewrite !pi_algK.
Qed.

Lemma lt_algcrealP (x y : algcreal) : reflect (x <  y)%CR (lt_algcreal x y).
Proof. by rewrite /lt_algcreal; case: ltVge_algcreal_dec; constructor. Qed.
Implicit Arguments lt_algcrealP [x y].

Lemma le_algcrealP (x y : algcreal) : reflect (y <= x)%CR (~~ lt_algcreal x y).
Proof. by rewrite /lt_algcreal; case: ltVge_algcreal_dec; constructor. Qed.
Implicit Arguments le_algcrealP [x y].
Prenex Implicits lt_algcrealP le_algcrealP.

Lemma add_alg_gt0 x y : lt_alg zero_alg x -> lt_alg zero_alg y ->
  lt_alg zero_alg (add_alg x y).
Proof.
rewrite -[x]reprK -[y]reprK !piE !lt_alg_pi -!(rwP lt_algcrealP).
move=> x_gt0 y_gt0; pose_big_enough i.
  apply: (@lt_crealP _ (diff x_gt0 + diff y_gt0) i i); do ?by big.
    by rewrite addr_gt0 ?diff_gt0.
  by rewrite /= add0r ler_add // ?diff0P //; big.
by close.
Qed.

Lemma mul_alg_gt0 x y : lt_alg zero_alg x -> lt_alg zero_alg y ->
  lt_alg zero_alg (mul_alg x y).
Proof.
rewrite -[x]reprK -[y]reprK !piE !lt_alg_pi -!(rwP lt_algcrealP).
move=> x_gt0 y_gt0; pose_big_enough i.
  apply: (@lt_crealP _ (diff x_gt0 * diff y_gt0) i i); do ?by big.
    by rewrite pmulr_rgt0 ?diff_gt0.
  rewrite /= add0r (@ler_trans _ (diff x_gt0 * (repr y) i)) //.
    by rewrite ler_wpmul2l ?(ltrW (diff_gt0 _)) // diff0P //; big.
  by rewrite ler_wpmul2r ?diff0P ?ltrW ?creal_gt0_always //; big.
by close.
Qed.

Lemma opp_alg_ngt0 x : lt_alg zero_alg x -> ~~ lt_alg zero_alg (opp_alg x).
Proof.
rewrite -[x]reprK !piE !lt_alg_pi -!(rwP lt_algcrealP, rwP (le_algcrealP)).
move=> hx; pose_big_enough i.
  apply: (@le_crealP _ i)=> j /= hj.
  by rewrite oppr_le0 ltrW // creal_gt0_always //; big.
by close.
Qed.

Lemma sub_alg_gt0 x y : lt_alg zero_alg (add_alg y (opp_alg x)) = lt_alg x y.
Proof.
rewrite -[x]reprK -[y]reprK !piE !lt_alg_pi.
apply/lt_algcrealP/lt_algcrealP=> /= hxy.
  pose_big_enough i.
    apply: (@lt_crealP _ (diff hxy) i i); rewrite ?diff_gt0 //; do ?by big.
    by rewrite (monoLR (addNKr _) (ler_add2l _)) addrC diff0P //; big.
  by close.
pose_big_enough i.
  apply: (@lt_crealP _ (diff hxy) i i); rewrite ?diff_gt0 //; do ?by big.
  by rewrite (monoRL (addrK _) (ler_add2r _)) add0r addrC diffP //; big.
by close.
Qed.

Lemma lt0_alg_total (x : alg) : x != zero_alg ->
  lt_alg zero_alg x || lt_alg zero_alg (opp_alg x).
Proof.
rewrite -[x]reprK !piE !lt_alg_pi -(rwP nequiv_alg) /= => x_neq0.
apply/orP; rewrite -!(rwP lt_algcrealP).
case/neq_creal_ltVgt: x_neq0=> /= [lt_x0|lt_0x]; [right|by left].
pose_big_enough i.
  apply: (@lt_crealP _ (diff lt_x0) i i); rewrite ?diff_gt0 //; do ?by big.
  by rewrite add0r -subr_le0 opprK addrC diffP //; big.
by close.
Qed.

Definition AlgPOFieldMixin := TotalOrder_PartialLtMixin
  add_alg_gt0 mul_alg_gt0 opp_alg_ngt0 sub_alg_gt0 lt0_alg_total.
Canonical alg_poIdomainType := POIdomainType alg AlgPOFieldMixin.
Canonical alg_poFieldType := POFieldType alg AlgPOFieldMixin.
Canonical alg_of_poIdomainType := POIdomainType {alg F} AlgPOFieldMixin.
Canonical alg_of_poFieldType := POFieldType {alg F} AlgPOFieldMixin.

Definition AlgOFieldMixin := TotalOrderLtMixin lt0_alg_total.
Canonical alg_oIdomainType := OIdomainType alg AlgOFieldMixin.
Canonical alg_oFieldType := OFieldType alg AlgOFieldMixin.
Canonical alg_of_oIdomainType := OIdomainType {alg F} AlgOFieldMixin.
Canonical alg_of_oFieldType := OFieldType {alg F} AlgOFieldMixin.

Lemma lt_pi x y : \pi_{alg F} x < \pi y = lt_algcreal x y.
Proof. by rewrite [_ < _]lt_alg_pi. Qed.

Lemma le_pi x y : \pi_{alg F} y <= \pi x = ~~ lt_algcreal x y.
Proof. by rewrite lerNgt lt_pi. Qed.

Lemma lt_algP (x y : algcreal) : reflect (x < y)%CR (\pi_{alg F} x < \pi y).
Proof. by rewrite lt_pi; apply: lt_algcrealP. Qed.
Implicit Arguments lt_algP [x y].

Lemma le_algP (x y : algcreal) : reflect (x <= y)%CR (\pi_{alg F} x <= \pi y).
Proof. by rewrite le_pi; apply: le_algcrealP. Qed.
Implicit Arguments le_algP [x y].
Prenex Implicits lt_algP le_algP.

Lemma to_alg_additive : additive to_alg.
Proof.
move=> x y /=; rewrite !to_algE sub_pi -equiv_alg /=.
by apply: eq_crealP; exists m0=> * /=; rewrite subrr absr0.
Qed.

Canonical to_alg_is_additive := Additive to_alg_additive.

Lemma to_alg_multiplicative : multiplicative to_alg.
Proof.
split=> [x y |] //; rewrite !to_algE mul_pi -equiv_alg.
by apply: eq_crealP; exists m0=> * /=; rewrite subrr absr0.
Qed.

Canonical to_alg_is_rmorphism := AddRMorphism to_alg_multiplicative.

Definition annul_alg : {alg F} -> {poly F} := locked (annul_creal \o repr).

Local Notation "p ^ f" := (map_poly f p) : ring_scope.
Notation "'Y" := 'X%:P.

Definition exp_algcreal x n := iterop n mul_algcreal x one_algcreal.

Lemma exp_algcrealE x n : (exp_algcreal x n == x ^+ n)%CR.
Proof.
case: n=> // n; rewrite /exp_algcreal /exp_creal !iteropS.
by elim: n=> //= n ->.
Qed.

Lemma expn_pi (x : algcreal) (n : nat) :
  (\pi_{alg F} x) ^+ n = \pi (exp_algcreal x n).
Proof.
rewrite /exp_algcreal; case: n=> [|n]; first by rewrite expr0 oneE.
rewrite exprS iteropS; elim: n=> /= [|n ihn]; rewrite ?expr0 ?mulr1 //.
by rewrite exprS ihn mul_pi.
Qed.

Definition horner_algcreal (p : {poly F}) x : algcreal :=
  \big[add_algcreal/zero_algcreal]_(i < size p)
   mul_algcreal (cst_algcreal p`_i) (exp_algcreal x i).

Lemma horner_pi (p : {poly F}) (x : algcreal) :
  (p ^ to_alg).[\pi_alg x] = \pi (horner_algcreal p x).
Proof.
rewrite horner_coef /horner_algcreal size_map_poly.
apply: (big_ind2 (fun x y => x = \pi_alg y)).
+ by rewrite zeroE.
+ by move=> u u' v v' -> ->; rewrite [_ + _]piE.
by move=> i /= _; rewrite expn_pi coef_map /= [_ * _]piE.
Qed.

Lemma horner_algcrealE p x : (horner_algcreal p x == p.[x])%CR.
Proof.
rewrite horner_coef_creal.
apply: (big_ind2 (fun (u : algcreal) v => u == v)%CR)=> //.
  by move=> u u' v v' /= -> ->.
by move=> i _ /=; rewrite exp_algcrealE.
Qed.

Lemma root_annul_algcreal (x : algcreal) : ((annul_alg (\pi x)).[x] == 0)%CR.
Proof. by unlock annul_alg; rewrite /= -pi_algK root_annul_creal. Qed.

Lemma root_annul_alg (x : {alg F}) : root ((annul_alg x) ^ to_alg) x.
Proof.
apply/rootP; rewrite -[x]reprK horner_pi /= zeroE -equiv_alg.
by rewrite horner_algcrealE root_annul_algcreal.
Qed.

Lemma monic_annul_alg (x : {alg F}) : monic (annul_alg x).
Proof. by unlock annul_alg; rewrite monic_annul_creal. Qed.

Lemma annul_alg_neq0 (x : {alg F}) : annul_alg x != 0.
Proof. by rewrite monic_neq0 ?monic_annul_alg. Qed.

Require Import separable.

Definition alg_seq_poly := ({alg F} * seq {poly F})%type.
Definition seq_seqF := seq (seq F).

Definition encode_alg_seq_poly (ap : alg_seq_poly) : seq_seqF :=
  encode_algdom (to_algdom (repr ap.1)) :: map (@polyseq _) ap.2.

Definition decode_alg_seq_poly (s : seq_seqF) : option alg_seq_poly :=
  if decode_algdom (head [::] s) is Some a
    then Some (\pi (to_algcreal a), map Poly (behead s)) else None.

Lemma code_alg_seq_polyK : pcancel encode_alg_seq_poly decode_alg_seq_poly.
Proof.
move=> []; elim/quotW=> x sp; rewrite /encode_alg_seq_poly /=.
rewrite [encode_algdom _]lock /decode_alg_seq_poly /=.
rewrite -lock encode_algdomK; congr (Some (_, _)).
  by rewrite -equiv_alg to_algdomK equiv_alg reprK.
by rewrite -map_comp map_id_in // => p _ /=; rewrite polyseqK.
Qed.

Canonical alg_seq_poly_eqMixin := PcanEqMixin code_alg_seq_polyK.
Canonical alg_seq_poly_eqType := EqType alg_seq_poly alg_seq_poly_eqMixin.
Canonical alg_seq_poly_choiceMixin := PcanChoiceMixin code_alg_seq_polyK.
Canonical alg_seq_poly_ChoiceType :=
  ChoiceType alg_seq_poly alg_seq_poly_choiceMixin.

Require Import zmodp.

Lemma map_poly_comp (aR : fieldType) (rR : idomainType) (f : {rmorphism aR -> rR})
   (p q : {poly aR}) : (p \Po q) ^ f = (p ^ f) \Po (q ^ f).
Proof.
rewrite !comp_polyE size_map_poly; apply: (big_ind2 (fun x y => x ^ f = y)).
+ by rewrite rmorph0.
+ by move=> u u' v v' /=; rewrite rmorphD /= => -> ->.
move=> /= i _; rewrite -mul_polyC rmorphM /= map_polyC mul_polyC.
by rewrite coef_map rmorphX.
Qed.

Lemma pet_alg_proof (s : seq alg) :
  { ap : alg_seq_poly |
    forallb i : 'I_(size s), (ap.2`_i ^ to_alg).[ap.1] == s`_i
    &  size ap.2 = size s }.
Proof.
apply: sig2_eqW; elim: s; first by exists (0,[::])=> //; apply/forallP=> [] [].
move=> x s [[a sp] /forallP /= hs hsize].
have := PET_char0 _ (root_annul_alg a) _ (root_annul_alg x).
rewrite !annul_alg_neq0=> /(_ isT isT (char_po _)) /= [n [[p hp] [q hq]]].
exists (x *+ n - a, q :: [seq r \Po p | r <- sp]); last first.
  by rewrite /= size_map hsize.
apply/forallP=> /=; rewrite -add1n=> i; apply/eqP.
have [k->|l->] := splitP i; first by rewrite !ord1.
rewrite add1n /= (nth_map 0) ?hsize // map_poly_comp /=.
by rewrite horner_comp_poly hp; apply/eqP.
Qed.

Definition pet_alg s : {alg F} :=
  let: exist2 (a, _) _ _ := pet_alg_proof s in a.
Definition pet_alg_poly s : seq {poly F}:=
  let: exist2 (_, sp) _ _ := pet_alg_proof s in sp.

Lemma size_pet_alg_poly s : size (pet_alg_poly s) = size s.
Proof. by unlock pet_alg_poly; case: pet_alg_proof. Qed.

Lemma pet_algK s i :
   ((pet_alg_poly s)`_i ^ to_alg).[pet_alg s] = s`_i.
Proof.
rewrite /pet_alg /pet_alg_poly; case: pet_alg_proof.
move=> [a sp] /= /forallP hs hsize; have [lt_is|le_si] := ltnP i (size s).
  by rewrite -[i]/(val (Ordinal lt_is)); apply/eqP; apply: hs.
by rewrite !nth_default ?hsize // rmorph0 horner0.
Qed.

Lemma ler_to_alg : {mono to_alg : x y / x <= y}.
Proof.
apply: homo_mono=> x y lt_xy; rewrite !to_algE -(rwP lt_algP).
by apply/lt_creal_cst; rewrite lt_xy.
Qed.

Lemma ltr_to_alg : {mono to_alg : x y / x < y}.
Proof. by apply: lerW_mono; apply: ler_to_alg. Qed.

Lemma inf_alg_proof x : {d | 0 < d & 0 < x -> (d%:RA < x)}.
Proof.
have [|] := lerP; first by exists 1.
elim/quotW: x=> x; rewrite zeroE=> /lt_algP /= x_gt0.
exists (diff x_gt0 / 2%:R); first by rewrite pmulr_rgt0 ?gtr0E ?diff_gt0.
rewrite to_algE -(rwP lt_algP) /= => _; pose_big_enough i.
  apply: (@lt_crealP _ (diff x_gt0 / 2%:R) i i); do ?by big.
    by rewrite pmulr_rgt0 ?gtr0E ?diff_gt0.
  by rewrite -[_ + _](splitf 2) diff0P //; big.
by close.
Qed.

Definition inf_alg (x : {alg F}) : F :=
  let: exist2 d _ _ := inf_alg_proof x in d.

Lemma inf_alg_gt0 x : 0 < inf_alg x.
Proof. by rewrite /inf_alg; case: inf_alg_proof. Qed.

Lemma inf_lt_alg x : 0 < x -> (inf_alg x)%:RA < x.
Proof. by rewrite /inf_alg=> x_gt0; case: inf_alg_proof=> d _ /(_ x_gt0). Qed.

Definition abs_algcreal (x : algcreal) :=
  if ~~ lt_algcreal x zero_algcreal then x else opp_algcreal x.

Lemma abs_algcrealE (x : algcreal) : (abs_algcreal x == `| x |)%CR.
Proof.
rewrite /abs_algcreal -lt_pi.
have [/lt_algP|/lt_algP|/equiv_alg] /= := ltrgtP; last first.
+ by move<-; apply: eq_crealP; exists m0=> * /=; rewrite !(absr0, subrr).
+ move=> x_lt0; apply: eq_crealP; exists_big_modulus m F.
    move=> e i e_gt0 hi /=; rewrite [`|x i|]ler0_abs ?subrr ?absr0 //.
    by rewrite ltrW // [_ < 0%CR i]creal_lt_always //; do ?big.
  by close.
move=> x_gt0; apply: eq_crealP; exists_big_modulus m F.
  move=> e i e_gt0 hi /=; rewrite [`|x i|]ger0_abs ?subrr ?absr0 //.
  by rewrite ltrW // creal_gt0_always //; do ?big.
by close.
Qed.

Lemma abs_pi (x : algcreal) : `|\pi_{alg F} x| = \pi (abs_algcreal x).
Proof. by rewrite /abs_algcreal -lt_pi -zeroE -lerNgt fun_if -opp_pi. Qed.

Lemma approx_proof x e : {y | 0 < e -> `|x - y%:RA| < e}.
Proof.
elim/quotW:x => x; pose_big_enough i.
  exists (x i)=> e_gt0; rewrite (ltr_trans _ (inf_lt_alg _)) //.
  rewrite !to_algE sub_pi abs_pi -(rwP lt_algP) /= abs_algcrealE /=.
  pose_big_enough j.
    apply: (@lt_crealP  _ (inf_alg e / 2%:R) j j); do ?by big.
      by rewrite pmulr_rgt0 ?gtr0E ?inf_alg_gt0.
    rewrite /= {2}[inf_alg e](splitf 2) /= ler_add2r.
    rewrite ltrW // cauchymodP //; do ?by big.
    by rewrite pmulr_rgt0 ?gtr0E ?inf_alg_gt0.
  by close.
by close.
Qed.

Definition approx := locked
  (fun (x : alg) (e : alg) => projT1 (approx_proof x e) : F).

Lemma approxP (x e e': alg) : 0 < e -> e <= e' -> `|x - (approx x e)%:RA| < e'.
Proof.
by unlock approx; case: approx_proof=> /= y hy /hy /ltr_le_trans hy' /hy'.
Qed.

Definition poly_ground := locked (fun (p : {poly {alg F}}) =>
  swapXY (Poly (pet_alg_poly p)) : {poly {poly F}}).

Lemma sizeY_poly_ground p : sizeY (poly_ground p) = size p.
Proof.
unlock poly_ground; rewrite sizeYE swapXYK; have [->|p_neq0] := eqVneq p 0.
  apply/eqP; rewrite size_poly0 eqn_leq leq0n (leq_trans (size_Poly _)) //.
  by rewrite size_pet_alg_poly size_poly0.
rewrite (@PolyK _ 0) -?nth_last ?size_pet_alg_poly //.
have /eqP := (pet_algK p (size p).-1); apply: contraL=> /eqP->.
by rewrite rmorph0 horner0 -lead_coefE eq_sym lead_coef_eq0.
Qed.

Lemma poly_ground_eq0 p : (poly_ground p == 0) = (p == 0).
Proof. by rewrite -sizeY_eq0 sizeY_poly_ground size_poly_eq0. Qed.

Lemma poly_ground0 : poly_ground 0 = 0.
Proof. by apply/eqP; rewrite poly_ground_eq0. Qed.

Lemma poly_groundK p :
  ((poly_ground p) ^ (map_poly to_alg)).[(pet_alg p)%:P] = p.
Proof.
have [->|p_neq0] := eqVneq p 0; first by rewrite poly_ground0 rmorph0 horner0.
unlock poly_ground; rewrite horner_polyC /eval /= swapXY_map_poly2 swapXYK.
apply/polyP=> i /=; rewrite coef_map_id0_poly ?horner0 // coef_map /=.
by rewrite coef_Poly pet_algK.
Qed.

Lemma weak_ivt (p : {poly F}) (a b : F) : a <= b -> p.[a] <= 0 <= p.[b] ->
  { x : alg | a%:RA <= x <= b%:RA & root (p ^ to_alg) x }.
Proof.
move=> le_ab; have [->  _|p_neq0] := eqVneq p 0.
  by exists a%:RA; rewrite ?lerr ?ler_to_alg // rmorph0 root0.
move=> /andP[pa_le0 pb_ge0]; apply/sig2W.
have hpab: p.[a] * p.[b] <= 0 by rewrite mulr_le0_ge0.
move=> {pa_le0 pb_ge0}; wlog monic_p : p hpab p_neq0 / monic p.
  set q := (lead_coef p) ^-1 *: p => /(_ q).
  rewrite !horner_scaler mulrCA !mulrA -mulrA mulr_ge0_le0 //; last first.
    by rewrite (@exprn_even_ge0 _ 2).
  have mq: monic q by rewrite /monic lead_coef_scale mulVf ?lead_coef_eq0.
  rewrite monic_neq0 ?mq=> // [] [] // x hx hqx; exists x=> //.
  move: hqx; rewrite /q -mul_polyC rmorphM /= root_mul map_polyC rootC.
  by rewrite fmorph_eq0 invr_eq0 lead_coef_eq0 (negPf p_neq0).
pose c := mid a b; pose r := mid b (-a).
have r_ge0 : 0 <= r by rewrite mulr_ge0 ?ger0E // subr_ge0.
have hab: ((c - r = a)%R * (c + r = b)%R)%type.
  rewrite -mulr_addl -mulr_subl oppr_add addrA addrK opprK.
  rewrite addrAC addrA [a + _ + _]addrAC subrr add0r.
  by rewrite !mulr_addl -![_ + _](splitf 2).
have hp: p.[c - r] * p.[c + r] <= 0 by rewrite !hab.
pose x := AlgDom monic_p r_ge0 hp; exists (\pi_alg (to_algcreal x)).
  rewrite !to_algE; apply/andP; rewrite -!(rwP le_algP) /=.
  split;
  by do [ unlock to_algcreal=> /=; apply: (@le_crealP _ 0%N)=> /= j _;
          have := @to_algcreal_ofP p c r 0%N j r_ge0 isT;
          rewrite ler_distl /= expr0 divr1 !hab=> /andP []].
apply/rootP. rewrite horner_pi zeroE -equiv_alg horner_algcrealE /=.
by rewrite -(@to_algcrealP x); unlock to_algcreal.
Qed.

Definition alg_archi_bound := locked (fun x => archi_bound (approx x 1%:RA + 1)).

Lemma alg_archi x : 0 <= x -> x < (alg_archi_bound x)%:R.
Proof.
move=> x_ge0; unlock alg_archi_bound; set a := approx _ _.
have := @archi_boundP _ (a + 1); rewrite -ltr_to_alg rmorph_nat.
have := @approxP x _ _ ltr01 (lerr _); rewrite ltr_distl -/a => /andP [_ hxa].
rewrite -ler_to_alg rmorphD /= (ler_trans _ (ltrW hxa)) //.
by move=> /(_ isT) /(ltr_trans _)->.
Qed.

Definition alg_archiMixin := ArchimedianMixin alg_archi.
Canonical alg_archiFieldType := ArchiFieldType alg alg_archiMixin.
Canonical alg_of_archiFieldType := ArchiFieldType {alg F} alg_archiMixin.

Lemma absr_to_alg : { morph to_alg : x / `|x| }.
Proof.
move=> x /=; do 2!have [] := absrP; rewrite ?rmorph0 ?rmorphN ?oppr0 //=;
  do ?by rewrite ltr_to_alg=> /ltr_trans h /h; rewrite ltrr.
by move->; rewrite oppr0.
Qed.

Lemma annul_from_alg_proof (p : {poly alg}) (q : {poly F}) :
  p != 0 -> q != 0 -> root (q ^ to_alg) (pet_alg p)
  -> {r | resultant (poly_ground p) (r ^ polyC) != 0
        & (r != 0) && (root (r ^ to_alg) (pet_alg p))}.
Proof.
move=> p_neq0; elim: (size q) {-2}q (leqnn (size q))=> {q} [|n ihn] q.
  by rewrite size_poly_leq0=> ->.
move=> size_q q_neq0 hq; apply/sig2_eqW.
have [|apq_neq0] :=
  eqVneq (resultant (poly_ground p) (q ^ polyC)) 0; last first.
  by exists q=> //; rewrite q_neq0.
move/eqP; rewrite resultant_eq0 ltn_neqAle eq_sym -coprimep_def.
move=> /andP[] /(bezout_coprimepPn _ _) [].
+ by rewrite poly_ground_eq0.
+ by rewrite map_polyC_eq0.
move=> [u v] /and3P [] /andP [u_neq0 ltn_uq] v_neq0 ltn_vp hpq.
rewrite ?size_map_polyC in ltn_uq ltn_vp.
rewrite ?size_poly_gt0 in u_neq0 v_neq0.
pose a := pet_alg p.
have := erefl (size ((u * poly_ground p) ^ (map_poly to_alg)).[a%:P]).
rewrite {2}hpq !{1}rmorphM /= !{1}horner_mul poly_groundK -map_comp_poly /=.
have /eq_map_poly-> : (map_poly to_alg) \o polyC =1 polyC \o to_alg.
  by move=> r /=; rewrite map_polyC.
rewrite map_comp_poly horner_map (rootP hq) mulr0 size_poly0.
move/eqP; rewrite size_poly_eq0 mulf_eq0 (negPf p_neq0) orbF.
pose u' : {poly F} := lead_coef (swapXY u).
have [/rootP u'a_eq0|u'a_neq0] := eqVneq (u' ^ to_alg).[a] 0; last first.
  rewrite horner_polyC -lead_coef_eq0 lead_coef_map_eq /=;
  by do ?rewrite swapXY_map_poly2 /= lead_coef_map_eq /=
        ?map_poly_eq0 ?lead_coef_eq0 ?swapXY_eq0 ?(negPf u'a_neq0).
have u'_neq0 : u' != 0 by rewrite lead_coef_eq0 swapXY_eq0.
have size_u' : (size u' < size q)%N.
  by rewrite /u' (leq_ltn_trans (leq_size_lead_coef _)) // sizeYE swapXYK.
move: u'a_eq0=> /ihn [] //; first by rewrite -ltnS (leq_trans size_u').
by move=> r; exists r.
Qed.

Definition annul_pet_alg (p : {poly {alg F}}) : {poly F} :=
    if (p != 0) =P true is ReflectT p_neq0 then
      let: exist2 r _ _ :=
        annul_from_alg_proof p_neq0 (annul_alg_neq0 _) (root_annul_alg _) in r
      else 0.

Lemma root_annul_pet_alg p : root (annul_pet_alg p ^ to_alg) (pet_alg p).
Proof.
rewrite /annul_pet_alg; case: eqP=> /=; last by rewrite ?rmorph0 ?root0.
by move=> p_neq0; case: annul_from_alg_proof=> ? ? /andP[].
Qed.

Definition annul_from_alg p :=
  if (size (poly_ground p) == 1)%N then lead_coef (poly_ground p)
    else resultant (poly_ground p) (annul_pet_alg p ^ polyC).

Lemma annul_from_alg_neq0 p : p != 0 -> annul_from_alg p != 0.
Proof.
move=> p_neq0; rewrite /annul_from_alg.
case: ifP; first by rewrite lead_coef_eq0 poly_ground_eq0.
rewrite /annul_pet_alg; case: eqP p_neq0=> //= p_neq0 _.
by case: annul_from_alg_proof.
Qed.

Lemma annul_pet_alg_neq0 p : p != 0 -> annul_pet_alg p != 0.
Proof.
rewrite /annul_pet_alg; case: eqP=> /=; last by rewrite ?rmorph0 ?root0.
by move=> p_neq0; case: annul_from_alg_proof=> ? ? /andP[].
Qed.

End RealAlg.

Implicit Arguments to_alg [F].

Notation "x %:RA" := (to_alg x) (at level 2, left associativity, format "x %:RA").

Lemma upper_nthrootVP (F : archiFieldType) (x : F) (i : nat) :
   0 < x -> (archi_bound (x ^-1) <= i)%N -> 2%:R ^- i < x.
Proof.
move=> x_gt0 hx; rewrite -ltr_pinv -?topredE //= ?gtr0E //.
by rewrite invrK upper_nthrootP.
Qed.

Implicit Arguments to_alg [[F]].

Notation "{ 'alg'  F }" := (alg_of (Phant F)).

Section AlgAlg.

Variable F : archiFieldType.

Local Open Scope ring_scope.

Local Notation "p ^ f" := (map_poly f p) : ring_scope.
Local Notation "'Y" := 'X%:P.

Definition approx2 (x : {alg {alg F}}) i :=
  approx (approx x (2%:R ^- i)) (2%:R ^- i).

Lemma asympt_approx2 x : { asympt e : i / `|(approx2 x i)%:RA%:RA - x| < e }.
Proof.
exists_big_modulus m {alg {alg F}}.
  move=> e i e_gt0 hi; rewrite distrC /approx2.
  rewrite (@split_dist_add _ (approx x (2%:R ^- i))%:RA) //.
    rewrite approxP ?gtr0E // ltrW //.
    by rewrite upper_nthrootVP ?divrn_gt0 ?ltr_to_alg //; big.
  rewrite (ltr_trans _ (inf_lt_alg _)) ?divrn_gt0 //.
  rewrite -rmorph_sub -absr_to_alg ltr_to_alg approxP ?gtr0E // ltrW //.
  by rewrite upper_nthrootVP ?divrn_gt0 ?inf_alg_gt0 ?ltr_to_alg //; big.
by close.
Qed.

Lemma from_alg_crealP (x : {alg {alg F}}) : creal_axiom (approx2 x).
Proof.
exists_big_modulus m F.
  move=> e i j e_gt0 hi hj; rewrite -2!ltr_to_alg !absr_to_alg !rmorph_sub /=.
  rewrite (@split_dist_add _ x) // ?[`|_ - _%:RA|]distrC;
  rewrite (@asympt1modP _ _ (asympt_approx2 x)) //; do ?[by big];
  by rewrite ?divrn_gt0 ?ltr_to_alg.
by close.
Qed.

Definition from_alg_creal := locked (fun x => CReal (from_alg_crealP x)).

Lemma to_alg_crealP (x : creal F) :  creal_axiom (fun i => to_alg (x i)).
Proof.
exists_big_modulus m (alg F).
  move=> e i j e_gt0 hi hj.
  rewrite -rmorph_sub -absr_to_alg (ltr_trans _ (inf_lt_alg _)) //.
  by rewrite ltr_to_alg cauchymodP ?inf_alg_gt0 //; big.
by close.
Qed.
Definition to_alg_creal x := CReal (to_alg_crealP x).

Local Notation m0 := (fun _ => 0%N).

Lemma horner_to_alg_creal p x :
  ((p ^ to_alg).[to_alg_creal x] == to_alg_creal p.[x])%CR.
Proof.
by apply: eq_crealP; exists m0=> * /=; rewrite horner_map subrr absr0.
Qed.

Lemma neq_to_alg_creal x y :
  (to_alg_creal x != to_alg_creal y)%CR <-> (x != y)%CR.
Proof.
split=> neq_xy.
  pose_big_enough i.
    apply: (@neq_crealP _ (inf_alg (lbound neq_xy)) i i); do ?by big.
      by rewrite inf_alg_gt0.
    rewrite -ler_to_alg absr_to_alg rmorph_sub /= ltrW //.
    by rewrite (ltr_le_trans (inf_lt_alg _)) ?lbound_gt0 ?lboundP //; big.
  by close.
pose_big_enough i.
  apply: (@neq_crealP _ (lbound neq_xy)%:RA i i); do ?by big.
    by rewrite ltr_to_alg lbound_gt0.
  by rewrite -rmorph_sub -absr_to_alg ler_to_alg lboundP //; big.
by close.
Qed.

Lemma eq_to_alg_creal x y :
  (to_alg_creal x == to_alg_creal y)%CR -> (x == y)%CR.
Proof. by move=> hxy /neq_to_alg_creal. Qed.

Lemma to_alg_creal0 : (to_alg_creal 0 == 0)%CR.
Proof. by apply: eq_crealP; exists m0=> * /=; rewrite subrr absr0. Qed.

Import Setoid.

Add Morphism to_alg_creal
 with signature (@eq_creal _) ==> (@eq_creal _) as to_alg_creal_morph.
Proof. by move=> x y hxy /neq_to_alg_creal. Qed.
Global Existing Instance to_alg_creal_morph_Proper.

Lemma to_alg_creal_repr (x : {alg F}) : (to_alg_creal (repr x) == x%:CR)%CR.
Proof.
apply: eq_crealP; exists_big_modulus m {alg F}.
  move=> e i e_gt0 hi /=; rewrite (ler_lt_trans _ (inf_lt_alg _)) //.
  rewrite -{2}[x]reprK !to_algE sub_pi abs_pi.
  rewrite -(rwP (le_algP _ _)) abs_algcrealE /=; pose_big_enough j.
    apply: (@le_crealP _ j)=> k hk /=.
    by rewrite ltrW // cauchymodP ?inf_alg_gt0 //; big.
  by close.
by close.
Qed.

Local Open Scope quotient_scope.

Lemma cst_pi (x : algcreal F) : ((\pi_{alg F} x)%:CR == to_alg_creal x)%CR.
Proof.
apply: eq_crealP; exists_big_modulus m {alg F}.
  move=> e i e_gt0 hi /=; rewrite (ltr_trans _ (inf_lt_alg _)) //.
  rewrite !to_algE sub_pi abs_pi /= -(rwP (lt_algP _ _)) abs_algcrealE /=.
  pose_big_enough j.
    apply: (@lt_crealP _ (inf_alg e / 2%:R) j j); do ?by big.
      by rewrite ?divrn_gt0 ?inf_alg_gt0.
    rewrite /= {2}[inf_alg _](splitf 2) ler_add2r ltrW // distrC.
    by rewrite cauchymodP ?divrn_gt0 ?inf_alg_gt0 //; big.
  by close.
by close.
Qed.

End AlgAlg.

Section AlgAlgAlg.

Variable F : archiFieldType.

Local Open Scope ring_scope.

Local Notation "p ^ f" := (map_poly f p) : ring_scope.
Local Notation "'Y" := 'X%:P.

Lemma from_alg_crealK (x : {alg {alg F}}) :
  (to_alg_creal (to_alg_creal (from_alg_creal x)) == x%:CR)%CR.
Proof.
apply: eq_crealP; exists_big_modulus m {alg {alg F}}.
  move=> e i e_gt0 hi; unlock from_alg_creal=> /=.
  by rewrite (@asympt1modP _ _ (asympt_approx2 x)) //; big.
by close.
Qed.

Lemma root_annul_from_alg_creal (x : {alg {alg F}}) :
  ((annul_from_alg (annul_alg x)).[from_alg_creal x] == 0)%CR.
Proof.
do 2!apply: eq_to_alg_creal.
rewrite -!horner_to_alg_creal from_alg_crealK !to_alg_creal0.
rewrite horner_creal_cst; apply/eq_creal_cst; rewrite -rootE.
rewrite /annul_from_alg; have [/size1P [c c_neq0 hc]|sp_neq1] := boolP (_ == _).
  set p := _ ^ _; suff ->: p = (annul_alg x) ^ to_alg by apply: root_annul_alg.
  congr (_ ^ _); rewrite -{2}[annul_alg x]poly_groundK /=.
  by rewrite !hc lead_coefC map_polyC /= hornerC.
have [||[u v] /= [hu hv] hpq] := @resultant_in_ideal _
  (poly_ground (annul_alg x)) (annul_pet_alg (annul_alg x) ^ polyC).
+ rewrite ltn_neqAle eq_sym sp_neq1 //= lt0n size_poly_eq0.
  by rewrite poly_ground_eq0 annul_alg_neq0.
+ rewrite size_map_polyC -(size_map_poly [rmorphism of to_alg]) /=.
  rewrite (has_root_size_gt1 _ (root_annul_pet_alg _)) //.
  by rewrite map_poly_eq0 annul_pet_alg_neq0 ?annul_alg_neq0.
move: hpq=> /(f_equal (map_poly (map_poly to_alg))).
rewrite map_polyC /= => /(f_equal (eval (pet_alg (annul_alg x))%:P)).
rewrite {1}/eval hornerC !rmorphD !{1}rmorphM /= /eval /= => ->.
rewrite -map_comp_poly /=.
have /eq_map_poly->: (map_poly (@to_alg F)) \o polyC =1 polyC \o (@to_alg F).
  by move=> r /=; rewrite map_polyC.
rewrite map_comp_poly horner_map /= (rootP (root_annul_pet_alg _)) mulr0 addr0.
by rewrite rmorphM /= root_mul orbC poly_groundK root_annul_alg.
Qed.

Lemma annul_alg_from_alg_creal_neq0 (x : {alg {alg F}}) :
  annul_from_alg (annul_alg x) != 0.
Proof. by rewrite annul_from_alg_neq0 ?annul_alg_neq0. Qed.

Definition from_alg_algcreal x :=
  AlgCRealOf (@annul_alg_from_alg_creal_neq0 x) (@root_annul_from_alg_creal x).

Definition from_alg : {alg {alg F}} -> {alg F} :=
  locked (\pi%qT \o from_alg_algcreal).

Lemma from_algK : cancel from_alg to_alg.
Proof.
move=> x; unlock from_alg; rewrite -{2}[x]reprK to_algE -equiv_alg /= cst_pi.
by apply: eq_to_alg_creal; rewrite from_alg_crealK to_alg_creal_repr.
Qed.

Lemma ivt (p : {poly (alg F)}) (a b : alg F) : a <= b ->
  p.[a] <= 0 <= p.[b] -> { x : alg F | a <= x <= b & root p x }.
Proof.
move=> le_ab hp; have [x /andP [hax hxb]] := @weak_ivt _ _ _ _ le_ab hp.
rewrite -[x]from_algK fmorph_root=> rpx; exists (from_alg x)=> //.
by rewrite -ler_to_alg from_algK hax -ler_to_alg from_algK.
Qed.

Definition alg_rcfMixin := RcfMixin ivt.
Canonical alg_rcfType := RcfType (alg F) alg_rcfMixin.
Canonical alg_of_rcfType := RcfType {alg F} alg_rcfMixin.

End AlgAlgAlg.
End RealAlg.

Notation "{ 'realalg'  F }" := (RealAlg.alg_of (Phant F)).

Canonical RealAlg.alg_eqType.
Canonical RealAlg.alg_choiceType.
Canonical RealAlg.alg_zmodType.
Canonical RealAlg.alg_Ring.
Canonical RealAlg.alg_comRing.
Canonical RealAlg.alg_unitRing.
Canonical RealAlg.alg_comUnitRing.
Canonical RealAlg.alg_iDomain.
Canonical RealAlg.alg_fieldType.
Canonical RealAlg.alg_poIdomainType.
Canonical RealAlg.alg_poFieldType.
Canonical RealAlg.alg_oIdomainType.
Canonical RealAlg.alg_oFieldType.
Canonical RealAlg.alg_archiFieldType.
Canonical RealAlg.alg_rcfType.

Canonical RealAlg.alg_of_eqType.
Canonical RealAlg.alg_of_choiceType.
Canonical RealAlg.alg_of_zmodType.
Canonical RealAlg.alg_of_Ring.
Canonical RealAlg.alg_of_comRing.
Canonical RealAlg.alg_of_unitRing.
Canonical RealAlg.alg_of_comUnitRing.
Canonical RealAlg.alg_of_iDomain.
Canonical RealAlg.alg_of_fieldType.
Canonical RealAlg.alg_of_poIdomainType.
Canonical RealAlg.alg_of_poFieldType.
Canonical RealAlg.alg_of_oIdomainType.
Canonical RealAlg.alg_of_oFieldType.
Canonical RealAlg.alg_of_archiFieldType.
Canonical RealAlg.alg_of_rcfType.