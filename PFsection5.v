(* (c) Copyright Microsoft Corporation and Inria. All rights reserved. *)
Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq path div choice.
Require Import fintype tuple finfun bigop prime ssralg poly finset center.
Require Import fingroup morphism perm automorphism quotient action zmodp.
Require Import gfunctor gproduct cyclic pgroup frobenius.
Require Import matrix mxalgebra mxrepresentation vector algC classfun character.
Require Import inertia vcharacter PFsection1.

(******************************************************************************)
(* This file covers Peterfalvi, Section 5: coherence                          *)
(* Defined here:                                                              *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Import GroupScope GRing.Theory.
Local Open Scope ring_scope.

Lemma mulr_sign (R : ringType) (b : bool) (x : R) :
  (-1) ^+ b * x = (if b then - x else x).
Proof. by case: b; rewrite ?mulNr mul1r. Qed.

Lemma scaler_sign (R : ringType) (V : lmodType R) (b : bool) (u : V) :
  (-1) ^+ b *: u = (if b then - u else u).
Proof. by case: b; rewrite ?scaleNr scale1r. Qed.

Section MoreVector.

Variables (F : fieldType) (V : vectType F).

Lemma scalev_eq0 (a : F) (v : V) : (a *: v == 0) = (a == 0) || (v == 0).
Proof. by rewrite -!memv0 memvZ. Qed.

End MoreVector.

Section MoreAlgC.

Implicit Types (x y z : algC) (m n p : nat) (b : bool).

Lemma leC_opp x y : (- x <= - y) = (y <= x).
Proof. by rewrite -leC_sub opprK addrC leC_sub. Qed.

Lemma ltC_opp x y : (- x < - y) = (y < x).
Proof. by rewrite ltC_sub opprK addrC -ltC_sub. Qed.

Lemma posC_opp x : (0 <= - x) = (x <= 0).
Proof. by rewrite -{1}oppr0 leC_opp. Qed.

Lemma sposC_opp x : (0 < - x) = (x < 0).
Proof. by rewrite -{1}oppr0 ltC_opp. Qed.

Lemma sposC1 : 0 < 1.
Proof. by rewrite -(ltn_ltC 0 1). Qed.

Lemma ltC_geF x y : x < y -> (y <= x) = false.
Proof. by case/andP=> neq_yx le_xy; apply: contraNF neq_yx => /leC_anti->. Qed.

Lemma leC_gtF x y : x <= y -> (y < x) = false.
Proof. by apply: contraTF => /ltC_geF->. Qed.

Lemma leC_eqVlt x y : (x <= y) = (x == y) || (x < y).
Proof. by rewrite /ltC eq_sym ; case: eqP => // ->; exact: leC_refl. Qed.

Lemma eqC_leC x y : (x == y) = (x <= y) && (y <= x).
Proof.
by apply/eqP/andP=> [-> | [le_xy le_yx]]; [rewrite leC_refl | exact: leC_anti].
Qed.

Lemma signC_inj : injective (fun b => (-1) ^+ b : algC).
Proof.
apply: can_inj (fun x => ~~ (0 <= x)) _ => [[]]; rewrite ?posC1 //.
by rewrite posC_opp // ltC_geF ?sposC1.
Qed.

Lemma normC_opp x : normC (- x) = normC x.
Proof. by rewrite /normC rmorphN mulrN mulNr opprK. Qed.

Lemma normCK x : normC x ^+ 2 = x * x^*.
Proof. exact: sqrtCK. Qed.

Lemma normC_mul_sign n x : normC ((-1) ^+ n * x) = normC x.
Proof. by rewrite -signr_odd mulr_sign fun_if normC_opp if_same. Qed.

Definition isRealC x := (x^* == x).

Lemma isZC_real x : isZC x -> isRealC x.
Proof. by move/isZC_conj/eqP. Qed.

Lemma realC_leP x : reflect (x <= 0 \/ 0 <= x) (isRealC x).
Proof.
rewrite -posC_opp; apply: (iffP eqP) => [r_x | [] /posC_conjK//]; last first.
  by rewrite rmorphN => /oppr_inj.
apply/orP; suffices: normC x \in pred2 x (- x).
  by case/pred2P=> <-; rewrite posC_norm ?orbT.
by rewrite !inE -addr_eq0 -(subr_eq0 _ x) -mulf_eq0 -subr_sqr normCK r_x subrr.
Qed.

Lemma real_normCK x : isRealC x -> normC x ^+ 2 = x ^+ 2.
Proof. by rewrite normCK => /eqP->. Qed.

Lemma int_normCK x : isZC x -> normC x ^+ 2 = x ^+ 2.
Proof. by move/isZC_real/real_normCK. Qed.

Lemma real_signE x : isRealC x -> x = (-1) ^+ (x < 0)%C * normC x.
Proof.
rewrite mulr_sign; case/realC_leP=> [ge0x | le0x]; last first.
  by rewrite normC_pos ?leC_gtF.
rewrite ltCE ge0x andbT -normC_opp normC_pos ?opprK ?posC_opp //.
by case: eqP => // <-; rewrite oppr0.
Qed.

Lemma isZC_signE x : isZC x -> x = (-1) ^+ (x < 0)%C * normC x.
Proof. by move/isZC_real/real_signE. Qed.

Lemma isZC_opp x : isZC (- x) = isZC x.
Proof. by rewrite !isZCE opprK orbC. Qed.

Lemma isZC_mulr_sign n x : isZC ((-1) ^+ n * x) = isZC x.
Proof. by rewrite -signr_odd mulr_sign fun_if isZC_opp if_same. Qed.

Lemma isZC_sign n : isZC ((-1) ^+ n).
Proof. by rewrite -[_ ^+ _]mulr1 isZC_mulr_sign (isZC_nat 1). Qed.

Lemma normCZ_nat x : isZC x -> isNatC (normC x).
Proof.
by rewrite isZCE => /orP[]/eqP => [|/(canRL (@opprK _))] ->;
  rewrite ?normC_opp normC_nat isNatC_nat.
Qed.

Lemma isNatC_Zpos x : isNatC x = isZC x && (0 <= x).
Proof.
apply/idP/andP=> [Nx | [Zx x_ge0]]; first by rewrite (eqP Nx) isZC_nat posC_nat.
by rewrite (isZC_signE Zx) mulr_sign leC_gtF // normCZ_nat.
Qed.

End MoreAlgC.

(* Notation for the norm; level should be 8, but classfun WRONGLY sets 10. *)
Notation "''[' phi ]_ G" := ('[phi, phi]_G)
  (at level 10, G at level 2, format "''[' phi ]_ G").

Section MoreCfun.

Variable gT : finGroupType.
Implicit Types (L G H : {group gT}) (A B : {set gT}) (R S : seq {cfun gT}).
Implicit Types (xi phi psi theta pi : {cfun gT}).

Definition inner_prodZr := inner_prodZ.
Lemma inner_prodZl a phi psi G : '[a *: phi, psi]_G = a * '[phi, psi]_G.
Proof. by rewrite -!inner_prodbE linearZ. Qed.
Lemma inner_prodNl phi psi G : '[- phi, psi]_G = - '[phi, psi]_G.
Proof. by rewrite -!inner_prodbE linearN. Qed.
Lemma inner_prodDl phi xi psi G :
  '[phi + xi, psi]_G = '[phi, psi]_G + '[xi, psi]_G.
Proof. by rewrite -!inner_prodbE linearD. Qed.
Lemma inner_prodNr phi psi G : '[phi, - psi]_G = - '[phi, psi]_G.
Proof. exact: raddfN. Qed.
Lemma inner_prodDr phi xi psi G :
  '[phi, psi + xi]_G = '[phi, psi]_G + '[phi, xi]_G.
Proof. exact: raddfD. Qed.

Lemma inner_normZ a phi G : '[a *: phi]_G = normC a ^+ 2 * '[phi]_G.
Proof. by rewrite inner_prodZl inner_prodZr mulrA normCK. Qed.

Lemma inner_normN phi G : '[- phi]_G = '[phi]_G.
Proof. by rewrite inner_prodNl raddfN opprK. Qed.

Lemma inner_normD phi psi G :
  let d := '[phi, psi]_G in '[phi + psi]_G = '[phi]_G + '[psi]_G + (d + d^*).
Proof. by rewrite /= addrAC -inner_conj inner_prodDl !inner_prodDr !addrA. Qed.

Definition orthogonal A R S :=
  all [pred phi | all [pred psi | '[phi, psi]_A == 0] S] R.

Lemma orthogonalP A R S :
  reflect {in R & S, forall phi psi, '[phi, psi]_A = 0} (orthogonal A R S).
Proof.
apply: (iffP allP) => oRS phi => [psi /oRS/allP opS /opS/eqP // | /oRS opS].
by apply/allP=> psi /= /opS->.
Qed.

Lemma orthogonal_sym G : symmetric (orthogonal G).
Proof.
apply: symmetric_from_pre => R S /orthogonalP oRS.
by apply/orthogonalP=> phi psi Sphi Rpsi; rewrite inner_conj oRS ?rmorph0.
Qed.

Lemma eq_orthogonal A R1 R2 S1 S2 :
  R1 =i R2 -> S1 =i S2 -> orthogonal A R1 S1 = orthogonal A R2 S2.
Proof.
move=> eqR eqS; apply/orthogonalP/orthogonalP=> oRS phi psi;
  by rewrite ?eqR ?eqS => *; rewrite oRS ?eqR ?eqS.
Qed.

Lemma orthogonal_catl A R1 R2 S :
  orthogonal A (R1 ++ R2) S = orthogonal A R1 S && orthogonal A R2 S.
Proof. exact: all_cat. Qed.

Lemma orthogonal_catr A R S1 S2 :
  orthogonal A R (S1 ++ S2) = orthogonal A R S1 && orthogonal A R S2.
Proof. by rewrite -all_predI; apply: eq_all => phi /=; rewrite all_cat. Qed.

(* We exclude 0 and ill-typed functions from pairwise orthogonal sets. *)
Fixpoint pairwise_orthogonal A S := 
  if S is psi :: S' then
    [&& psi \in 'CF(A), psi != 0, orthogonal A [:: psi] S'
      & pairwise_orthogonal A S']
  else true.

Lemma pairwise_orthogonalP G S :
  reflect [/\ {subset S <= 'CF(G)}, uniq (0 :: S)
            & {in S &, forall phi psi, phi != psi -> '[phi, psi]_G = 0}]
          (pairwise_orthogonal G S).
Proof.
elim: S => [|phi S IH] /=; first by left.
case CFphi: (phi \in 'CF(G)); last first.
  by right=> [[CF_S]]; rewrite CF_S ?mem_head in CFphi.
rewrite inE eq_sym; have [_ | /= nz_phi] := altP eqP; first by right; case.
have [opS | not_opS] := altP allP; last first.
  right=> [[_ /and3P[_ notSp _] opS]].
  have [psi Spsi /eqP[]] := allPn not_opS.
  by rewrite opS ?mem_head 1?mem_behead //; apply: contraNneq notSp => ->.
have -> /=: (phi \notin S).
  by apply: contra nz_phi => /opS /=; rewrite inner_prod0.
apply: (iffP IH) => [] [CF_S uniqS oSS]; last first.
  split=> // [psi Spsi | psi xi Spsi Sxi]; first by rewrite CF_S 1?mem_behead.
  by apply: oSS; exact: mem_behead.
split=> // [psi | psi xi] /predU1P[-> // | ]; first by move/CF_S.
  by case/predU1P=> [-> | /opS] /eqP.
move=> Spsi /predU1P[-> _ | Sxi /oSS-> //]; move/opS/eqP: Spsi => o_phi_psi.
by rewrite inner_conj o_phi_psi rmorph0.
Qed.

Lemma pairwise_orthogonal_cat A R S :
  pairwise_orthogonal A (R ++ S) =
    [&& pairwise_orthogonal A R, pairwise_orthogonal A S & orthogonal A R S].
Proof.
by elim: R => [|phi R /= ->]; rewrite !andbT // all_cat -!andbA; do !bool_congr.
Qed.

Lemma inner_norm_orthogonal G S :
    pairwise_orthogonal G S ->
  '[\sum_(phi <- S) phi]_G = \sum_(phi <- S) '[phi]_G.
Proof.
case/pairwise_orthogonalP=> [_ /andP[_ uniqS] oSS].
rewrite raddf_sum /= !(big_tnth _ _ S); apply: eq_bigr => i _.
rewrite -inner_prodbE linear_sum /= /inner_prodb.
rewrite (bigD1 i) // big1 /= ?addr0 // => j neq_ji.
by rewrite !(tnth_nth 0) /= oSS ?mem_nth ?nth_uniq.
Qed.

Lemma orthogonal_free G S : pairwise_orthogonal G S -> free S.
Proof.
case/pairwise_orthogonalP=> [CF_S /andP[notS0 uniqS] oSS].
apply/(freeP (in_tuple S)) => a aS0 i; have S_i: S`_i \in S by exact: mem_nth.
have /eqP: '[S`_i, 0]_G = 0 := inner_prod0r G _.
rewrite -{2}aS0 raddf_sum /= (bigD1 i) //= big1 => [|j neq_ji]; last 1 first.
  by rewrite inner_prodZr oSS ?mulr0 ?mem_nth // eq_sym nth_uniq.
rewrite addr0 inner_prodZr mulf_eq0 conjC_eq0 inner_prod0 ?CF_S //.
by case/pred2P=> // Si0; rewrite -Si0 S_i in notS0.
Qed.

Definition orthonormal A S :=
  all [pred psi |'[psi]_A == 1] S && pairwise_orthogonal A S.

Lemma orthonormal_cat A R S :
  orthonormal A (R ++ S) =
   [&& orthonormal A R, orthonormal A S & orthogonal A R S].
Proof.
by rewrite /orthonormal pairwise_orthogonal_cat all_cat -!andbA; do !bool_congr.
Qed.

Lemma orthonormal_pairwise_orthogonal G S :
  orthonormal G S -> pairwise_orthogonal G S.
Proof. by case/andP. Qed.

Lemma orthonormal_free G S : orthonormal G S -> free S.
Proof. by move/orthonormal_pairwise_orthogonal/orthogonal_free. Qed.

Lemma orthonormalP G S :
  reflect [/\ {subset S <= 'CF(G)}, uniq S
            & {in S &, forall phi psi, '[phi, psi]_G = (phi == psi)%:R}]
          (orthonormal G S).
Proof.
rewrite /orthonormal; have [normS | not_normS] := altP allP; last first.
  right=> [[_ _ o1S]]; have [phi Sphi /eqP[]] := allPn not_normS.
  by rewrite o1S ?eqxx.
apply: (iffP (pairwise_orthogonalP G S)) => [] [CF_S uniqS oSS].
  split=> // [|phi psi]; first by case/andP: uniqS.
  by have [-> _ /normS/eqP | /oSS] := altP eqP.
split=> // [|phi psi Sphi Spsi /negbTE]; last by rewrite oSS // => ->.
rewrite /= uniqS andbT; apply/negP=> S_0.
by move/eqP: (oSS 0 0 S_0 S_0); rewrite inner_prod0r eq_sym eqxx oner_eq0.
Qed.

Definition isometry A B tau :=
  forall phi psi, '[tau phi, tau psi]_B = '[phi, psi]_A.

Definition conjC_closed S :=
  {in S, forall phi, (phi^*)%CH \in [predD1 S & phi]}.

Fact cfun_conjC_is_rmorphism : rmorphism (@cfun_conjC gT).
Proof.
split=> [phi xi|]; first by apply/ffunP=> x; rewrite !ffunE rmorph_sub.
by split=> [phi xi|]; apply/ffunP=> x; rewrite !ffunE (rmorphM, rmorph1).
Qed.
Canonical cfun_conjC_additive := Additive cfun_conjC_is_rmorphism.
Canonical cfun_conjC_rmorphism := RMorphism cfun_conjC_is_rmorphism.

Lemma cfun_conjC_Z a phi : ((a *: phi)^*)%CH = a^* *: (phi^*)%CH.
Proof. by apply/ffunP=> x; rewrite !ffunE rmorphM. Qed.

Lemma conjC_closed_not0 S : conjC_closed S -> 0 \notin S.
Proof. by move=> clC_S; rewrite (contra (clC_S 0)) // rmorph0 !inE eqxx. Qed.

End MoreCfun.

Section MoreChar.

Variables (gT : finGroupType) (G : {group gT}).
Implicit Types (a : algC) (b : bool) (i : Iirr G).

Lemma eq_scaled_irr a1 a2 i1 i2 :
  (a1 *: 'xi_i1 == a2 *: 'xi_i2) = (a1 == a2) && ((a1 == 0) || (i1 == i2)).
Proof.
apply/eqP/andP=> [|[/eqP-> /pred2P[]-> //]]; last by rewrite !scale0r.
move/(congr1 (coord (irr G)))/ffunP; rewrite !linearZ=> eq_a12.
move: {eq_a12}(eq_a12 i1) (esym (eq_a12 i2)); rewrite !ffunE /*:%R /=.
rewrite !(coord_inner_prodE _ (memc_irr _)) !irr_orthonormal !eqxx ?mulr1.
by rewrite !mulr_natr eq_sym !mulrb orbC; case: ifP => _ -> -> /=. 
Qed.

Lemma eq_signed_irr b1 b2 i1 i2 :
  ((-1) ^+ b1 *: 'xi_i1 == (-1) ^+ b2 *: 'xi_i2) = (b1 == b2) && (i1 == i2).
Proof. by rewrite eq_scaled_irr signr_eq0 (inj_eq signC_inj). Qed.

End MoreChar.

(* This should be the definition f the 'Z[..] syntax -- the one in vcharacter
   is missing a scope, and prints with spurious whitespace.
Delimit Scope vchar_scope with VC.
Open Scope vchar_scope.
Notation "''Z[' S , A ]" := (virtual_char_pred S A)
  (at level 0, format "''Z[' S ,  A ]") : vchar_scope.
Notation "''Z[' S ]" := ('Z[S, setT])
  (at level 0, format "''Z[' S ]") : vchar_scope.
*)

Section MoreVChar.

Variables (gT : finGroupType) (m : nat).
Implicit Types (G : {group gT}) (A : {set gT}) (S : m.-tuple {cfun gT}).

Lemma vchar_sign S A xi n : ((-1) ^+ n *: xi \in 'Z[S, A]) = (xi \in 'Z[S, A]).
Proof.
rewrite -signr_odd scaler_sign; case: ifP => // _.
by apply/idP/idP=> /vchar_opp; rewrite ?opprK.
Qed.

Lemma memc_Zirr G : {subset 'Z[irr G] <= 'CF(G)}.
Proof.
by move=> _ /vcharP[xi1 [xi2 [? ? ->]]]; rewrite memv_sub ?memc_is_char.
Qed.

Lemma isZC_inner_Zirr G :
  {in 'Z[irr G] &, forall phi psi, isZC ('[phi, psi]_G)}.
Proof.
move=> phi psi Zphi Zpsi; rewrite /= (inner_prod_vchar Zphi Zpsi).
by apply: isZC_sum => k _; rewrite isZC_mul ?(@isZC_inner_prod_vchar _ G setT).
Qed.

Lemma vchar_orthonormalP G (S : seq {cfun gT}) :
    {subset S <= 'Z[irr G]} ->
  reflect (exists I : {set Iirr G}, exists b : Iirr G -> bool,
           perm_eq S [seq (-1) ^+ b i *: 'xi_i | i <- enum I])
          (orthonormal G S).
Proof.
move=> vcS; apply: (equivP (orthonormalP _ _)).
split=> [[CF_S uniqS oSS] | [I [b defS]]]; last first.
  split=> [xi||xi1 xi2]; rewrite ?(perm_eq_mem defS).
  - by case/mapP=> [i _ ->]; rewrite memvZ memc_irr orbT.
  - rewrite (perm_eq_uniq defS) map_inj_uniq ?enum_uniq // => i j /eqP.
    by rewrite eq_signed_irr => /andP[_ /eqP].
  case/mapP=> [i _ ->] /mapP[j _ ->]; rewrite eq_signed_irr.
  rewrite inner_prodZl inner_prodZr rmorph_sign mulrA irr_orthonormal. 
  rewrite -signr_addb mulr_natr mulrb andbC.
  by case: eqP => //= ->; rewrite addbb eqxx.
pose I := [set i : Iirr G | ('xi_i \in S) || (- 'xi_i \in S)].
pose b (i : Iirr G) := - 'xi_i \in S; exists I, b.
apply: uniq_perm_eq => // [|xi].
  rewrite map_inj_uniq ?enum_uniq // => i j /eqP.
  by rewrite eq_signed_irr => /andP[_ /eqP].
apply/idP/mapP=> [Sxi | [i Ii ->{xi}]]; last first.
  move: Ii; rewrite mem_enum inE orbC -/(b i).
  by case b_i: (b i); rewrite (scale1r, scaleN1r).
have: '[xi]_G = 1 by rewrite oSS ?eqxx.
have vc_xi := vcS _ Sxi; rewrite (inner_prod_vchar vc_xi vc_xi).
case/isNatC_sum_eq1 => [i _ || i]; rewrite /index_enum -?enumT ?enum_uniq //.
  have Zxii := isZC_inner_prod_vchar i vc_xi.
  by rewrite -expr2 -int_normCK // isNatC_mul // normCZ_nat.
case=> _ _ /eqP; rewrite -subr_eq0 subr_sqr_1 mulf_eq0 subr_eq0 addr_eq0.
move=> def_b xi_xi_i; suffices def_xi: xi = (-1) ^+ b i *: 'xi_i.
  exists i; rewrite // mem_enum inE -/(b i) orbC.
  by case: (b i) def_xi Sxi => // ->; rewrite scale1r.
have:= sum_inner_prodE (memc_Zirr vc_xi); rewrite (bigD1 i) //=.
rewrite big1 ?addr0 => [|j /xi_xi_i/(_ (mem_enum _ _) isT)/eqP]; last first.
  by rewrite mulf_eq0 orbb => /eqP->; rewrite scale0r.
case/pred2P: def_b => -> def_xi; case def_b: (b i) => //; last first.
  by rewrite /b -scaleN1r def_xi Sxi in def_b.
have /eqP/idPn[] := oSS _ _ Sxi def_b.
rewrite raddfN /= -def_xi {1}scale1r irr_orthonormal eqxx.
by rewrite -scaleN1r (eq_signed_irr false true) oppr_eq0 oner_eq0.
Qed.

End MoreVChar.

Section Four.

(* This is Peterfalvi (4.1). *)

Variable gT : finGroupType.

Lemma vchar_pairs_orthonormal (X : {group gT}) a b c d u v :
    {subset [:: a; b] <= 'Z[irr X]} /\ {subset [:: c; d] <= 'Z[irr X]} ->
    orthonormal X [:: a; b] && orthonormal X [:: c; d] ->
    [&& isRealC u,  isRealC v, u != 0 & v != 0] ->
    [&& '[a - b, u *: c - v *: d]_X == 0,
         (a - b) 1%g == 0 & (u *: c - v *: d) 1%g == 0] ->
    orthonormal X [:: a; b; c; d].
Proof.
have osym2 e f: orthonormal X [:: e; f] -> orthonormal X [:: f; e].
  by rewrite !(orthonormal_cat X [::_] [::_]) orthogonal_sym andbCA.
have def_o f S: orthonormal X (f :: S) -> f \in 'Z[irr X] ->
  exists ie : Iirr X * bool, f = (-1) ^+ ie.2 *: 'xi_ie.1.
- rewrite (orthonormal_cat X [:: f]) => /andP[o_f _] vc_f {S}.
  have [|S [e def_f]] := vchar_orthonormalP _ o_f.
    by apply/allP; rewrite /= andbT.
  have:= mem_head f [::]; rewrite (perm_eq_mem def_f) => /mapP[i _ ->].
  by exists (i, e i).
case=> /allP/and3P[Za Zb _] /allP/and3P[Zc Zd _] /andP[o_ab o_cd].
rewrite (orthonormal_cat X [:: a; b]) o_ab o_cd.
case/and4P=> /eqP r_u /eqP r_v nz_u nz_v /and3P[o_abcd ab1 cd1].
wlog suff: a b c d u v Za Zb Zc Zd o_ab o_cd r_u r_v nz_u nz_v o_abcd ab1 cd1 /
  '[a, c]_X == 0.
- move=> IH; rewrite /= (IH a b c d u v) //.
  have vc_sym (e f : {cfun gT}) : ((e - f) 1%g == 0) = ((f - e) 1%g == 0).
    by rewrite -oppr_sub ffunE oppr_eq0.
  have ab_sym e: ('[b - a, e]_X == 0) = ('[a - b, e]_X == 0).
    by rewrite -oppr_sub inner_prodNl oppr_eq0.
  rewrite (IH b a c d u v) // 1?osym2 1?vc_sym ?ab_sym //=.
  rewrite -oppr_eq0 -inner_prodNr oppr_sub in o_abcd.
  by rewrite (IH a b d c v u) ?(IH b a d c v u) // 1?osym2 1?vc_sym ?ab_sym.
apply: contraLR cd1 => nz_ac.
have [iea def_a] := def_o a _ o_ab Za.
have{nz_ac} [e defc]: exists e : bool, c = (-1) ^+ e *: a.
  have [iec def_c] := def_o c _ o_cd Zc; exists (iec.2 (+) iea.2).
  move: nz_ac; rewrite def_a def_c scalerA; rewrite -signr_addb addbK.
  rewrite inner_prodZl inner_prodZr irr_orthonormal mulrA mulrC mulf_eq0.
  by have [-> // | _]:= iea.1 =P iec.1; rewrite eqxx.
have /andP[/andP[/eqP a1 _] /and4P[_ _ /andP[/andP[/eqP ab0 _] _] _]] := o_ab.
have /andP[_ /and4P[_ _ /andP[/andP[/eqP cd0 _] _] _]] := o_cd.
have def_vbd: v * '[b, d]_X = - ((-1) ^+ e * u).
  apply/eqP; have:= o_abcd; rewrite inner_prodDl inner_prodNl !raddf_sub /=.
  rewrite defc !inner_prodZr a1 (inner_conj X b a) ab0 rmorph0 mulr1.
  rewrite -[a]scale1r -{2}[1]/((-1) ^+ false) -(addbb e) signr_addb -scalerA.
  rewrite -defc inner_prodZl cd0 !mulr0 opprK addrA !subr0 mulrC addrC addr_eq0.
  by rewrite rmorph_sign r_u r_v.
have nz_bd: '[b, d]_X != 0.
  move/esym/eqP: def_vbd; apply: contraTneq => ->.
  by rewrite mulr0 oppr_eq0 mulf_eq0 signr_eq0.
have{nz_bd} defd: d = '[b, d]_X *: b.
  move: nz_bd; have [ieb ->] := def_o b _ (osym2 _ _ o_ab) Zb.
  have [ied ->] := def_o d _ (osym2 _ _ o_cd) Zd.
  rewrite scalerA inner_prodZl inner_prodZr rmorph_sign mulrA irr_orthonormal.
  have [-> _ | _] := ieb.1 =P ied.1; last by rewrite !mulr0 eqxx.
  by rewrite mulr1 mulrAC -!signr_addb addbb.
rewrite defd scalerA def_vbd scaleNr opprK defc scalerA mulrC -raddfD ffunE.
rewrite !mulf_neq0 ?signr_eq0 // -(subrK a b) -oppr_sub addrCA 2!ffunE.
rewrite (eqP ab1) oppr0 add0r ffunE -mulr2n -mulr_natl mulf_eq0 -(eqN_eqC _ 0).
by rewrite /= def_a ffunE mulf_eq0 signr_eq0 /= irr1_neq0.
Qed.

End Four.

Section Five.

Variable gT : finGroupType.

(* This is Peterfalvi, Definition (5.1). *)
(* It is unclear whether the non-triviality condiiton is used at all. *)
Definition coherent m L G (S : m.-tuple {cfun gT}) A tau
                           of {in 'Z[S, A], isometry L G tau} :=
  [/\ exists2 theta, theta \in 'Z[S, A] & theta != 0
    & exists tau1 : {additive {cfun gT} -> {cfun gT}},
      [/\ {in 'Z[S] &, isometry L G tau1},
          {in 'Z[S], forall phi, tau1 phi \in 'Z[irr G]}
        & {in 'Z[S, A], tau1 =1 tau}]].

(* This is Peterfalvi, Hypothesis (5.2). *)
(* The Z-linearity constraint on tau will be expressed by an additive or      *)
(* linear structure on tau. Also, we allow S to contain virtual character.    *)
Definition precoherent m L G (S : m.-tuple {cfun gT}) tau R :=
  [/\ (*a*) {subset S <= 'Z[irr L]} /\ conjC_closed S,
      (*b*) {in 'Z[S, L^#] &, isometry L G tau}
            /\ {in 'Z[S, L^#], forall phi, tau phi \in 'Z[irr G, G^#]},
      (*c*) pairwise_orthogonal L S,
      (*d*) {in S, forall xi : {cfun gT},
              [/\ {subset R xi <= 'Z[irr G]}, orthonormal G (R xi)
                & tau (xi - xi^*)%CH = \sum_(alpha <- R xi) alpha]}
    & (*e*) {in S &, forall xi phi,
              orthogonal L [:: phi] [:: xi; (xi^*)%CH] ->
              orthogonal G (R phi) (R xi)}].

(* This is Peterfalvi (5.2)(a). *)
Lemma irr_precoherent m (L G : {group gT}) (S : m.-tuple {cfun gT}) tau :
    [/\ uniq S, {subset S <= irr L} & conjC_closed S] ->
    {in 'Z[S, L^#] &, isometry L G tau}
      /\ {in 'Z[S, L^#], forall phi, tau phi \in 'Z[irr G, G^#]} ->
  {R : {cfun gT} -> seq {cfun gT} | precoherent L G S tau R}.
Proof.
move=> [U_S irrS clC_S] [iso_tau VCtau].
pose beta xi := tau (xi - xi^*)%CH.
pose R xi :=
  filter (predC1 0) [seq '[beta xi, 'xi_i]_G *: 'xi_i | i <- enum (Iirr G)].
exists R.
have vcS: {subset S <= 'Z[irr L]}.
  move=> _ /irrS/irrIP[i <-]; exact: vchar_irr.
have orthS: pairwise_orthogonal L S.
  apply/orthonormal_pairwise_orthogonal/orthonormalP.
  split=> // [_ /vcS/memc_Zirr// | _ _ /irrS/irrIP[i1 <-] /irrS/irrIP[i2 <-]].
  by rewrite (inj_eq (@xi_inj _ L)) irr_orthonormal.
have freeS := orthogonal_free orthS.
have subT (A : pred gT) : A \subset setT by apply/subsetP=> x; rewrite inE.
have dom_beta: {in S, forall xi, xi - (xi^*)%CH \in 'Z[S, L^#]}.
  move=> xi Sxi.
  have [/irrIP[i def_xi] /andP[_ Sxib]] := (irrS _ Sxi, clC_S _ Sxi).
  rewrite vchar_split vchar_sub ?memv_vchar ?subT //= -def_xi.
  rewrite -(eq_subset (in_set _)) subsetD1 (eq_subset (in_set _)).
  rewrite !inE !ffunE negbK isNatC_conj ?isNatC_irr1 // subrr eqxx andbT.
  by rewrite (@support_memc _ L) // -conj_idxE memv_sub ?memc_irr.
have szR: {in S, forall xi,
  [/\  beta xi = \sum_(alpha <- R xi) alpha,
       {subset R xi <= 'Z[irr G]},
       orthonormal G (R xi) & size (R xi) = 2%N]}.
- move=> xi Sxi; have /andP[/= neq_xi_b Sxib] := clC_S _ Sxi.
  have /irrIP[i def_xi] := irrS _ Sxi.
  have irr_beta: beta xi \in 'Z[irr G, G^#] by rewrite VCtau ?dom_beta.
  have def_beta: beta xi = \sum_(alpha <- R xi) alpha.
  rewrite -(sum_inner_prodE (memc_vchar irr_beta)).
    rewrite big_filter big_map [in R in _ = R]big_mkcond enumT.
    by apply: eq_bigr => j _ /=; case: eqP.
  have norm_beta: '[beta xi]_G = 2%:R.
    rewrite iso_tau ?dom_beta // -inner_prodbE linear_sub /= !inner_prodbE.
    rewrite !raddf_sub /= opprK -def_xi -conj_idxE !irr_orthonormal !eqxx.
    rewrite eq_sym -(inj_eq (@xi_inj _ L)) conj_idxE def_xi (negbTE neq_xi_b).
    by rewrite !addrA !subr0.
  have vcR: {subset R xi <= 'Z[irr G]}.
    move=> alpha; rewrite mem_filter => /andP[_ /mapP[k _ ->{alpha}]].
    rewrite (eqP (isZC_inner_prod_vchar k irr_beta)); case: (getZC _) => b n.
    by rewrite -scalerA vchar_sign scaler_nat vchar_scal ?vchar_irr.
  have orthR: pairwise_orthogonal G (R xi).
    apply/pairwise_orthogonalP; split=> [_ /vcR/memc_Zirr//|| a1 a2].
      rewrite /= mem_filter /= eqxx /= [R _]filter_map.
      rewrite map_inj_in_uniq 1?filter_uniq ?enum_uniq // => k1 k2.
      rewrite mem_filter /preim /= scalev_eq0 => /andP[/norP[nz_bk1 _] _] _.
      by move/eqP; rewrite eq_scaled_irr (negbTE nz_bk1) /= => /andP[_ /eqP].
    rewrite !mem_filter => /andP[_ /mapP[k1 _ ->]] /andP[_ /mapP[k2 _ ->]].
    rewrite eq_scaled_irr inner_prodZl inner_prodZr irr_orthonormal.
    by case: (k1 =P k2) => [-> | _]; rewrite ?eqxx ?orbT ?mulr0.
  have normR: {in R xi, forall a, '[a]_G = 1}.
    move=> /= a Ra; have [n def_a]: exists2 n, '[a]_G = (n ^ 2)%:R & a != 0.
      move: Ra; rewrite mem_filter /= => /andP[-> /mapP[k _ ->]].
      exists (getNatC (normC ('[beta xi, 'xi_k]_G))) => //.
      rewrite natr_exp inner_normZ irr_orthonormal eqxx mulr1; congr (_ ^+ _).
      exact/eqP/normCZ_nat/(isZC_inner_prod_vchar _ irr_beta).
    rewrite -(inner_prod0 (memc_Zirr (vcR a Ra))) def_a -(eqN_eqC _ 0).
    suffices: (n ^ 2 <= 2)%N by case: (n) => [|[|?]]; rewrite 1?(sqrn_add 2).
    rewrite leq_leC -norm_beta -def_a def_beta inner_norm_orthogonal //.
    have [k R' defR] := rot_to Ra.
    rewrite (eq_big_perm (a :: R')) ?big_cons //=; last first.
      by rewrite -defR perm_eq_sym perm_rot.
    by rewrite addrC -leC_sub addrK posC_sum // => b _; exact: posC_inner_prod.
  split=> //; first by apply/andP; split=> //; apply/allP=> a /= /normR->.
  apply/eqP; rewrite eqN_eqC -norm_beta def_beta inner_norm_orthogonal //.
  rewrite big_cond_seq (eq_bigr _ normR) -(big_cond_seq xpredT) big_const_seq.
  by rewrite count_predT -Monoid.iteropE.
split=> // [xi /szR[] // | xi phi Sxi Sphi /= /andP[/and3P[opx opx' _] _]].
have obpx: '[beta phi, beta xi]_G = 0.
  rewrite iso_tau ?dom_beta // inner_prodDl inner_prodNl !raddf_sub //=.
  rewrite -{3}[xi]cfun_conjCK !cfun_conjC_inner (eqP opx) (eqP opx').
  by rewrite rmorph0 !oppr0 !addr0.
case: (R phi) (szR _ Sphi) => /= [|a [|b [|? ?]]] [dbp Zab o_ab // _].
case: (R xi) (szR _ Sxi) => /= [|c [|d [|? ?]]] [dbx Zcd o_cd // _].
suffices: orthonormal G [:: a; - b; c; d].
  rewrite (orthonormal_cat G [:: a; _]) andbA; case/andP=> _ /=.
  by rewrite !inner_prodNl !oppr_eq0 !andbT.
apply: (@vchar_pairs_orthonormal _ G _ _ _ _ 1 (-1)).
- by split=> //; apply/allP; case/allP/and3P: Zab => /= -> /vchar_opp->.
- rewrite o_cd andbT /orthonormal /= inner_normN inner_prodNr !oppr_eq0.
  by rewrite memvN.
- by rewrite /isRealC oppr_eq0 oner_eq0 rmorphN rmorph1 !eqxx.
rewrite !big_cons !big_nil !addr0 in dbp dbx.
rewrite scale1r scaleN1r !opprK -dbp -dbx obpx eqxx /=.
by rewrite !(cfunS0 (memc_vchar (VCtau _ _))) ?dom_beta ?inE ?eqxx.
Qed.

End Five.