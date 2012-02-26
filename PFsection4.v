(* (c) Copyright Microsoft Corporation and Inria. All rights reserved. *)
Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq path div choice.
Require Import fintype tuple finfun bigop prime ssralg poly finset center.
Require Import fingroup morphism perm automorphism quotient action zmodp.
Require Import gfunctor gproduct cyclic pgroup frobenius.
Require Import matrix mxalgebra mxrepresentation vector algC classfun character.
Require Import inertia vcharacter PFsection1 PFsection2 PFsection3.

(******************************************************************************)
(* This file covers Peterfalvi, Section 4: The Dade isometry of a certain     *)
(* type of subgroup.                                                          *)
(* Defined here:                                                              *)
(* cyclicDade_hypothesis L K W W1 W2 ==                                       *)
(*         W is the direct sum of W1 W2 (two non-trivial cyclic groups of odd *)
(*           cardinal)                                                        *)
(*         L is the semi direct sum of K and W1                               *)
(*         W1 is a subgroup of Hall of L                                      *)
(*         W2 is the centraliser in K of all the elements of W1^#.            *)
(*         This is Peterfalvi (4.2).                                          *)
(*    ecTIirr i j ==  the virtual character that corresponds to               *)
(*                       w_ i j - w_ 0 j                                      *)
(*                   where w_ i j = acTIirr i j .                             *)
(*  ecTIirr_base  == the base of 'CF(W, W :\: W2) composed of the ecTIirr i j.*)
(* Dade_delta i j == a boolean associated to i an index of an irreducible     *)
(*                     character of W1 and j an index of an irreducible       *)
(*                     character of W2.                                       *)
(*   Dade_mu2 i j == an index of an irreducible character of L such that      *)
(*               'Ind[L] (e_ i j) =                                           *)
(*                   (-1) ^+ (delta j) *: ('chi_(mu2 i j) - 'chi_(mu2 0 j))   *)
(*                   where e_ i j = ecTIirr i j                               *)
(*                      delta i j = Dade_delta i j                            *)
(*                        mu2 i j = Dade_mu2 i j.                             *)
(*      Dade_mu j == the sum of all the 'chi_(mu2 i j) with i in Iirr W1.     *)
(*     Dade_chi j == the restriction to K of 'chi_(mu2 0 j).                  *)
(*   uniform_Dade_mu_seq k                                                    *)
(*                == the predicates that checks if a non zero index j is such *)
(*                       mu j 1 = mu k 1.                                     *)
(*                                                                            *)
(* centralDade_hypothesis A G H L K W W1 W2                                   *)
(*               == the hypothesis that corresponds to Peterfalvi (4.6).      *)
(* For cdH : centralDade_hypothesis A G H L K W W1 W2 we have                 *)
(* cDade_cTI_h   == the cyclic hypothesis between G W W1 and W2.              *)
(* cDade_cDa_h   == the cyclic dade hypothesis between L K W W1 W2.           *)
(* cDade_dAd_h   == the date hypothesis between G L and A0                    *)
(*                  where A0 is                                               *)
(*                     A :|: class_support (cyclicTIset cDade_cTI_h) L.       *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GroupScope GRing.Theory.
Local Open Scope ring_scope.

Section Four.

(* This is Peterfalvi (4.1). *)

Variable gT : finGroupType.

Lemma vchar_pairs_orthonormal (X : {group gT}) (a b c d : 'CF(X)) u v :
    {subset (a :: b) <= 'Z[irr X]} /\ {subset (c :: d) <= 'Z[irr X]} ->
    orthonormal (a :: b) && orthonormal (c :: d) ->
    [&& isRealC u, isRealC v, u != 0 & v != 0] ->
    [&& '[a - b, u *: c - v *: d] == 0,
         (a - b) 1%g == 0 & (u *: c - v *: d) 1%g == 0] ->
    orthonormal [:: a; b; c; d].
Proof.
have osym2 (e f : 'CF(X)) : orthonormal (e :: f) -> orthonormal (f :: e).
  by rewrite !(orthonormal_cat [::_] [::_]) orthogonal_sym andbCA.
have def_o f S: orthonormal (f :: S) -> '[f : 'CF(X)] = 1.
  by case/andP=> /andP[/eqP].
case=> /allP/and3P[Za Zb _] /allP/and3P[Zc Zd _] /andP[o_ab o_cd].
rewrite (orthonormal_cat (a :: b)) o_ab o_cd /=.
case/and4P=> /eqP r_u /eqP r_v nz_u nz_v /and3P[o_abcd ab1 cd1].
wlog suff: a b c d u v Za Zb Zc Zd o_ab o_cd r_u r_v nz_u nz_v o_abcd ab1 cd1 /
  '[a, c]_X == 0.
- move=> IH; rewrite /orthogonal /= !andbT (IH a b c d u v) //=.
  have vc_sym (e f : 'CF(X)) : ((e - f) 1%g == 0) = ((f - e) 1%g == 0).
    by rewrite -opprB cfunE oppr_eq0.
  have ab_sym e: ('[b - a, e] == 0) = ('[a - b, e] == 0).
    by rewrite -opprB cfdotNl oppr_eq0.
  rewrite (IH b a c d u v) // 1?osym2 1?vc_sym ?ab_sym //=.
  rewrite -oppr_eq0 -cfdotNr opprB in o_abcd.
  by rewrite (IH a b d c v u) ?(IH b a d c v u) // 1?osym2 1?vc_sym ?ab_sym.
apply: contraLR cd1 => nz_ac.
have [/orthonormal2P[ab0 a1 b1] /orthonormal2P[cd0 c1 d1]] := (o_ab, o_cd).
have [ea [ia def_a]] := vchar_norm1P Za a1.
have{nz_ac} [e defc]: exists e : bool, c = (-1) ^+ e *: a.
  have [ec [ic def_c]] := vchar_norm1P Zc c1; exists (ec (+) ea).
  move: nz_ac; rewrite def_a def_c scalerA; rewrite -signr_addb addbK.
  rewrite cfdotZl cfdotZr cfdot_irr mulrA mulrC mulf_eq0.
  by have [-> // | _]:= ia =P ic; rewrite eqxx.
have def_vbd: v * '[b, d]_X = - ((-1) ^+ e * u).
  apply/eqP; have:= o_abcd; rewrite cfdotDl cfdotNl !raddfB /=.
  rewrite defc !cfdotZr a1 (cfdotC b) ab0 rmorph0 mulr1.
  rewrite -[a]scale1r -{2}[1]/((-1) ^+ false) -(addbb e) signr_addb -scalerA.
  rewrite -defc cfdotZl cd0 !mulr0 opprK addrA !subr0 mulrC addrC addr_eq0.
  by rewrite rmorph_sign r_u r_v.
have nz_bd: '[b, d] != 0.
  move/esym/eqP: def_vbd; apply: contraTneq => ->.
  by rewrite mulr0 oppr_eq0 mulf_eq0 signr_eq0.
have{nz_bd} defd: d = '[b, d] *: b.
  move: nz_bd; have [eb [ib ->]] := vchar_norm1P Zb b1.
  have [ed [id ->]] := vchar_norm1P Zd d1.
  rewrite scalerA cfdotZl cfdotZr rmorph_sign mulrA cfdot_irr.
  have [-> _ | _] := ib =P id; last by rewrite !mulr0 eqxx.
  by rewrite mulr1 mulrAC -!signr_addb addbb.
rewrite defd scalerA def_vbd scaleNr opprK defc scalerA mulrC -raddfD cfunE.
rewrite !mulf_neq0 ?signr_eq0 // -(subrK a b) -opprB addrCA 2!cfunE.
rewrite (eqP ab1) oppr0 add0r cfunE -mulr2n -mulr_natl mulf_eq0 -(eqN_eqC _ 0).
by rewrite /= def_a cfunE mulf_eq0 signr_eq0 /= irr1_neq0.
Qed.

Lemma orthonormal_vchar_diff_ortho (X : {group gT}) (a b c d : 'CF(X)) :
    {subset a :: b <= 'Z[irr X]} /\ {subset c :: d <= 'Z[irr X]} ->
    orthonormal (a :: b) && orthonormal (c :: d) ->
    [&& '[a - b, c - d] == 0, (a - b) 1%g == 0 & (c - d) 1%g == 0] ->
  '[a, c] = 0.
Proof.
move=> Zabcd Oabcd; rewrite -[c - d]scale1r scalerBr.
move/(vchar_pairs_orthonormal Zabcd Oabcd) => /implyP.
rewrite /isRealC conjC1 eqxx oner_eq0 (orthonormal_cat (a :: b)) /=.
by case/and3P=> _ _ /andP[] /andP[] /eqP.
Qed.


Section CyclicDade.

Section Definitions.

Variables (L K W W1 W2 : {set gT}).

Definition cyclicDade_hypothesis :=
  [/\ [/\ K ><| W1 = L, W1 != 1%g, Hall L W1 & cyclic W1],
      [/\ W2 != 1%g, W2 \subset K, cyclic W2 & {in W1^#, forall x, 'C_K[x] = W2}]
   &  [/\ W1 \x W2 = W & odd #|W|]].

End Definitions.

Variables (L K W W1 W2 : {group gT}).

Hypothesis HC : cyclicDade_hypothesis L K W W1 W2.

Let Hcoprime : coprime #|W1| #|W2|.
Proof.
case: HC=> [[SdP _ H_Hall _] [_ WsK _ _] _].
apply: coprime_dvdr (cardSg WsK) _.
by rewrite coprime_sym (coprime_sdprod_Hall SdP) (sdprod_Hall SdP).
Qed.

Let dW1 : W1 != 1%G.
Proof. by case: HC=> [[]]. Qed.

Let dW2 : W2 != 1%G.
Proof. by case: HC=> [_ []]. Qed.

Let CW1 : cyclic W1.
Proof. by case: HC=> [[]]. Qed.

Let CW2 : cyclic W2.
Proof. by case: HC=> [_ []]. Qed.

Let SdP :  K ><| W1 = L.
Proof. by case: HC=> [[]]. Qed.

Let HdP : W1 \x W2 = W.
Proof. by case: HC=> [_ _ []]. Qed.

Let KsL : K \subset L.
Proof.
by case/sdprodP: SdP=> _ <- *; apply: mulg_subl (group1 _).
Qed.

Let W1sL : W1 \subset L.
Proof.
by case/sdprodP: SdP=> _ <- *; apply: mulg_subr (group1 _).
Qed.

Let W2sK : W2 \subset K.
Proof. by case: HC=> [_ []]. Qed.

Let CW : cyclic W.
Proof. by rewrite (cyclic_dprod HdP). Qed.

Let Hcent : {in W1^#, forall x, 'C_K[x] = W2}.
Proof. by case: HC=> [_ []]. Qed.

Lemma cyclicDade_conj a g :
  a \in W :\: W2 -> g \in L -> (a ^ g \in W :\: W2) -> (g \in W).
Proof.
rewrite inE=> /andP [] HH.
case/(mem_dprod HdP)=> x [y [XiW YiW Hxy _]].
move: HH; rewrite {}Hxy => HH GiL.
have XdiW: x \in W1^#.
  rewrite inE XiW andbT inE.
  by apply: contra HH => /eqP->; rewrite mul1g.
rewrite {HH}inE andbC => /andP [].
case/(mem_dprod HdP)=> x1 [y1 [X1iW Y1iW XYeX1Y1] _ JJ].
have XGeX1 : x^ g = x1.
  case: (Bezoutl #|W1| (cardG_gt0 W2))=> u Hu /dvdnP [] v.
  move: Hcoprime; rewrite coprime_sym /coprime => /eqP-> HH.
  have F1 x2 y2 : (x2 \in W1 -> y2 \in W2 -> (x2 * y2) ^+ (v * #|W2|)%N = x2)%g.
    move=> X2iW Y2iW.
    have: commute x2 y2.
      case/dprodP: HdP=> _ _.
      by move/subsetP /(_ _ Y2iW) /centP /(_ _ X2iW) /commute_sym.
    move/expgMn=> ->.
    rewrite -{1}HH expgD expg1 mulnC [(v * _)%N]mulnC !expgM.
    move/order_dvdG: X2iW=> /dvdnP=> [[k1 ->]].
    move/order_dvdG: Y2iW=> /dvdnP=> [[k2 ->]].
    by rewrite mulnC [(k2 * _)%N]mulnC !expgM !expg_order !expg1n !mulg1.
  by rewrite -(F1 _ _ X1iW Y1iW) -XYeX1Y1 -conjXg F1.
have /(mem_sdprod SdP) [k1 [x2 [K1iK X2iW _ Hu]]] : 
        x ^ g \in L by rewrite groupJ // (subsetP W1sL).
case: {Hu}(Hu _ _ (group1 _) (X1iW)) (Hu)=> [| <- <- Hu]; first by rewrite mul1g.
case: (mem_sdprod SdP GiL) XGeX1 Hu => k [x3 [KiK X3iW] -> _] <- Hu.
move: HdP; rewrite dprodC; case/dprodP=> _ <- _ _.
apply/imset2P; exists k x3; rewrite //.
rewrite -(Hcent XdiW); apply /subcent1P; split=> //.
apply: (mulgI k^-1%g); rewrite !mulgA mulVg mul1g -mulgA -[(_ * _)%g]/(x ^ k).
apply: (conjg_inj x3); rewrite -conjgM.
move: (cyclic_abelian CW1)=> /subsetP /(_ _ X3iW) /centP /(_ _ XiW) Cxx3.
rewrite [_ ^ x3]conjgE -Cxx3 mulgA mulVg mul1g.
move: KiK; rewrite -(memJ_conjg _ x3).
case/sdprodP: SdP=> _ _ /subsetP /(_ _ X3iW) /normP -> _ HH.
pose k' := k ^ x3.
move: (HH); rewrite -(memJ_conjg _ x^-1).
case/sdprodP: SdP=> _ _ /subsetP /(_ _ (groupVr XiW)) /normP -> _ HH1.
pose k'' := k' ^ x^-1.
have: (k'^-1 * k'' \in K)%g by rewrite groupM // groupV.
move/Hu=> /(_ _ XiW) []=> [| _ //].
rewrite !conjgE -!mulgA mulVg mulg1 !mulgA; do 2 congr (_ * _)%g.
rewrite /k' !conjgE !invMg !invgK.
by rewrite  -!mulgA; do 2 congr (_ * _)%g; rewrite !mulgA Cxx3 mulgK.
Qed.

Let WsL : W \subset L.
Proof.
case/sdprodP: SdP=> _ <- _ _.
move: HdP; rewrite dprodC => /dprodP [] _ <- _ _.
by apply: mulSg; case: HC=> _ [].
Qed.

Let WmW1W2_neq0 : W :\: (W1 :|: W2) != set0.
Proof.
apply/eqP=> HS0.
case/trivgPn: dW1=> x XiW1 Dx1; case/trivgPn: dW2=> y YiW2 Dy1.
suff: (x * y)%g \in W :\: (W1 :|: W2) by rewrite HS0 inE.
rewrite !inE negb_or.
case: (boolP (_ \in W1))=> /= [XYiW1|XYniW1].
   have: y \in W1 :&: W2 by rewrite inE YiW2 andbT -(groupMl _ XiW1).
   by case/dprodP: HdP=> _ _ _ ->; rewrite inE (negPf Dy1).
case: (boolP (_ \in W2))=> /= [XYiW2|XYniW2].
   have: x \in W1 :&: W2 by rewrite inE XiW1 -(groupMr _ YiW2).
   by case/dprodP: HdP=> _ _ _ ->; rewrite inE (negPf Dx1).
by case/dprodP: HdP=> _ <- _ _; apply/imset2P; exists x y.
Qed.

Let WmW1W2sWmW2 :  W :\: (W1 :|: W2) \subset W :\: W2.
Proof.
by apply/subsetP=> i; rewrite !inE negb_or -andbA => /and3P [] _ ->.
Qed.

Let NirrW1Gt: (1 <  Nirr W1)%N.
Proof.
have:= cyclic_abelian CW1; rewrite card_classes_abelian => /eqP HH.
by rewrite NirrE HH cardG_gt1; case: HC=> [[]].
Qed.

(* First part of PeterFalvi (4.3a). *)
Lemma normedTI_Dade_W2 : normedTI (W :\: W2) L W.
Proof.
have F : W :\: W2 != set0.
  by apply: contra WmW1W2_neq0=> HH; rewrite -subset0 -(eqP HH).
apply/(normedTI_memJ_P F); split=> // a g AdiW GiL; apply/idP/idP=> GG.
  by apply: cyclicDade_conj GG.
move: (AdiW); rewrite inE => /andP [] _ AiW.
rewrite conjgE.
move/cyclic_abelian: CW => /subsetP /(_ _ AiW) /centP /(_ _ GG) ->.
by rewrite mulgA mulVg mul1g.
Qed.

(* Second part of PeterFalvi (4.3a). *)
Lemma cyclicTI_Dade : cyclicTIhypothesis L W W1 W2.
Proof.
split; try split; rewrite ?(cyclic_dprod HdP) //; first by case: HC=> _ _ [].
have F : W :\: (W1 :|: W2) != set0.
  apply/eqP=> HS0.
  case/trivgPn: dW1=> x XiW1 Dx1; case/trivgPn: dW2=> y YiW2 Dy1.
  suff: (x * y)%g \in W :\: (W1 :|: W2) by rewrite HS0 inE.
  rewrite !inE negb_or.
  case: (boolP (_ \in W1))=> /= [XYiW1|XYniW1].
     have: y \in W1 :&: W2 by rewrite inE YiW2 andbT -(groupMl _ XiW1).
     by case/dprodP: HdP=> _ _ _ ->; rewrite inE (negPf Dy1).
  case: (boolP (_ \in W2))=> /= [XYiW2|XYniW2].
     have: x \in W1 :&: W2 by rewrite inE XiW1 -(groupMr _ YiW2).
     by case/dprodP: HdP=> _ _ _ ->; rewrite inE (negPf Dx1).
  by case/dprodP: HdP=> _ <- _ _; apply/imset2P; exists x y.
apply/(normedTI_memJ_P F); split=> // a g AdiW GiL; apply/idP/idP=> GG.
  pose SS := (subsetP WmW1W2sWmW2).
  by apply: (cyclicDade_conj (SS _ _) _ (SS _ GG)).
move: (AdiW); rewrite inE => /andP [] _ AiW.
rewrite conjgE.
move/cyclic_abelian: CW => /subsetP /(_ _ AiW) /centP /(_ _ GG) ->.
by rewrite mulgA mulVg mul1g.
Qed.

Local Notation sigma := (cyclicTIsigma L W W1 W2).
Local Notation w_ := (@cyclicTIirr gT W W1 W2).

Let odd_neq2 m : odd m -> (2 == m)%N = false.
Proof. by case: eqP => // <-. Qed.

Let W1xW2 : W1 \x W2 = W. Proof. by have [[]] := cyclicTI_Dade. Defined.

Let W1sW : W1 \subset W. Proof. by have [_ /mulG_sub[]] := dprodP W1xW2. Qed.
Let W2sW : W2 \subset W. Proof. by have [_ /mulG_sub[]] := dprodP W1xW2. Qed.
Let oddW : odd #|W|. Proof. by have [[]] := cyclicTI_Dade. Qed.
Let oddW1 : odd #|W1|. Proof. exact: oddSg oddW. Qed.

Definition ecTIirr i j := w_ i j - w_ 0 j.
Local Notation e_ := ecTIirr.

Definition ecTIirr_base := image (prod_curry e_) (setX [set~ ord0] setT).

Lemma ecTIirr_base_free : free ecTIirr_base.
Proof.
have FF  (HH : W1 \x W2 = W) i1 i2 j1 j2 :
    dprod_Iirr HH (i1,j1) == dprod_Iirr HH (i2, j2) = ((i1 == i2) && ((j1 == j2))).
  apply/eqP/andP=> [/dprod_Iirr_inj [] -> -> | [/eqP -> /eqP ->] //].
  by rewrite eqxx.
have PP i1 j1 i2 j2 : i1 != 0 -> i2 != 0 ->
   '[e_ i1 j1, w_ i2 j2] = ((i1 == i2) && (j1 == j2))%:R.
  move=> Di1 Di2; rewrite cfdot_subl !(cTIirrE cyclicTI_Dade) !cfdot_irr !FF.
  case: (j1 == _); last by rewrite !andbF subrr.
  case: (boolP (0 == i2))=> [/eqP HH|_]; last by rewrite subr0.
  by case/eqP: Di2; apply/val_eqP=> /=; rewrite -HH.
apply/freeP=> /= s Hs u.
have: ecTIirr_base`_u \in ecTIirr_base.
  by apply: mem_nth; rewrite size_image.
case/imageP=> [[/= i1 j1]]; rewrite !inE=> /andP [] /= Hi1 _ He.
suff: s u = 
  '[\sum_(i < #|setX [set~ ord0] [set: Iirr W2]|) s i *: ecTIirr_base`_ i,
    w_ i1 j1] by rewrite Hs cfdot0l.
rewrite cfdot_suml (bigD1 u) //= big1 ?addr0.
  by rewrite He cfdotZl PP // !eqxx mulr1.
move=> v Hv.
have: ecTIirr_base`_v \in ecTIirr_base.
  by apply: mem_nth; rewrite size_image.
case/imageP=> [[/= i2 j2]]; rewrite !inE=> /andP [] /= Hi2 _ He1.
rewrite He1  cfdotZl PP //.
case: (boolP (j2 == _))=> [/eqP HH1|]; last by rewrite !andbF mulr0.
case: (boolP (i2 == _))=> [/eqP HH2|]; last by rewrite mulr0.
have: ecTIirr_base`_u == ecTIirr_base`_v by rewrite He1 HH1 HH2 He.
rewrite nth_uniq ?size_image //.
  by move=> /val_eqP HK; case/negP: Hv; rewrite HK.
rewrite map_inj_in_uniq.
 (* Why apply: enum_uniq => [] [/= i3 j3] [/= i4 j4]. does not work>?? *)
apply: enum_uniq.
move=> [/= i3 j3] [/= i4 j4].
  rewrite !mem_enum !inE !andbT /= => Hi3 Hi4 HE.
have: '[e_ i3 j3, w_ i3 j3] == '[e_ i4 j4, w_ i3 j3].
  by rewrite HE.
rewrite !PP // !eqxx.
case: (boolP (j4 == _))=> [/eqP ->| _]; last first.
  by rewrite andbF -(eqN_eqC 1 0).
case: (boolP (i4 == _))=> [/eqP -> //| _]; last first.
by rewrite -(eqN_eqC 1 0).
Qed.

Lemma dim_cyclicTIcfun2 : \dim 'CF(W, W :\: W2) = (#|Iirr W1|.-1 * #|Iirr W2|)%N.
Proof.
rewrite !card_ord dim_cfun_on_abelian ?(cyclic_abelian, subsetDl) // !NirrE.
have:= cyclic_abelian CW1; rewrite card_classes_abelian => /eqP ->.
have:= cyclic_abelian CW2; rewrite card_classes_abelian => /eqP ->.
rewrite cardsD -(dprod_card W1xW2).
move/setIidPr: W2sW->.
by rewrite -{2}[#|W2|]mul1n -mulnBl subn1.
Qed.

Lemma memc_ecTIirr i j : e_ i j \in 'CF(W, W :\: W2).
Proof.
have linearW1 := cTIirr_linearW1 cyclicTI_Dade.
apply/cfun_onP=> x; rewrite !inE negb_and negbK orbC.
have [Wx /=  XiW2 | /cfun0->//] := boolP (x \in W).
rewrite !cfunE !(cTIirrE cyclicTI_Dade) !dprod_IirrE -[x]mul1g !cfDprodE //.
by rewrite  !lin_char1 // subrr.
Qed.

Lemma ecTIirr_base_is_basis : is_basis 'CF(W, W :\: W2) ecTIirr_base.
Proof.
rewrite /is_basis ecTIirr_base_free andbT /is_span -dimv_leqif_eq.
  by rewrite (eqnP ecTIirr_base_free) size_tuple cardsX !cardsC1 
             dim_cyclicTIcfun2 cardsT.
rewrite -span_subsetl; apply/allP=> _ /imageP[[i j] _ ->].
by exact: memc_ecTIirr.
Qed.

Definition Dade_mudelta := 
   odflt ([ffun => [ffun => 0]], [ffun => true]) 
    [pick mudelta : ({ffun Iirr W1 -> {ffun Iirr W2 -> Iirr L}} *
                 {ffun Iirr W2 -> bool}) |
        let (mu,delta) := mudelta in
          injectiveb (prod_curry (fun a b => mu a b)) &&
          forallb i : Iirr W1, forallb j : Iirr W2,
       'Ind[L] (e_ i j) ==
            (-1) ^+ (delta j) *: ('chi_(mu i j) - 'chi_(mu 0 j))].

Definition Dade_mu2 (i : Iirr W1) (j : Iirr W2) : Iirr L := 
  Dade_mudelta.1 i j. 
Local Notation mu2 := Dade_mu2.

Definition Dade_delta (i : Iirr W2) : bool := Dade_mudelta.2 i.
Local Notation delta := Dade_delta.

Lemma Dade_mudelta_spec :
        injective (prod_curry mu2) /\
        forall i j,
       'Ind[L] (e_ i j) =
            (-1) ^+ (delta j) *: ('chi_(mu2 i j) - 'chi_(mu2 0 j)).
Proof.
have linearW := cTIirr_linearW cyclicTI_Dade.
rewrite /Dade_mu2 /Dade_delta /Dade_mudelta; case: pickP=> /= [[mu2 delta]|].
  move/andP=> [] /injectiveP Hi /forallP Hp; split=> // i j; apply/eqP.
  by move: (Hp i)=> /forallP /(_ j).
pose md  (j : Iirr W2)  := 
   odflt ([ffun => 0], true) 
    [pick mudelta : ({ffun Iirr W1 -> Iirr L} * bool) |
        let (mu,delta) := mudelta in
          injectiveb mu &&
          forallb i : Iirr W1, 
       'Ind[L] (e_ i j) ==
            (-1) ^+ delta *: ('chi_(mu i) - 'chi_(mu 0))].
move/(_ ([ffun i : Iirr W1 => [ffun j => (md j).1 i]], [ffun j => (md j).2])).
move/idP=> [].
have FF: W :\: W2 \subset L^#.
  apply/subsetP=> u; rewrite !inE=> /andP [Hu Hw].
  case: (boolP (u == _))=> [HH| _ /=]; last by apply: (subsetP WsL).
  by case/negP: Hu; rewrite (eqP HH) group1.
pose TH := normedTI_isometry FF normedTI_Dade_W2.
have: forall j, injective (md j).1 /\   
        forall i, 'Ind[L] (e_ i j) = 
                      (-1) ^+ (md j).2 *: ('chi_((md j).1 i) - 'chi_((md j).1 0)).
  move=> j; rewrite /md; case: pickP=> [[/= mu d] /andP [] |].
    by move/injectiveP=> Hi /forallP Hf; split=> // i; apply/eqP.
  (* All the conditions to apply 1.3 *)
  pose Chi :=  [tuple of [seq w_ i j | i <- ord_tuple (Nirr W1)]].
  have ChiW i : w_ i j \in Chi by apply/imageP; exists i.
  have Chi_nth (i : Iirr W1) : Chi`_i = w_ i j.
    rewrite (nth_map 0) -?cardE ?card_ord //=.
    move: (tnth_ord_tuple i)=> /=.
    by rewrite (tnth_nth 0) -?cardE ?card_ord //= => ->.
  have ChiS: {subset Chi <= irr W}.
    by move=> c /mapP [k KiI ->]; exact: irr_chi.
  have ChiF: free Chi.
    apply: orthonormal_free; apply/orthonormalP; split=> [|c1 c2].
      apply/injectiveP=> u v; rewrite !(cTIirrE cyclicTI_Dade).
      by move/chi_inj=> /dprod_Iirr_inj []. 
    move=> /mapP [i1 Hi1 ->] /mapP [i2 Hi2 ->].
    apply/eqP; rewrite cfdot_irr -eqN_eqC; apply/eqP; congr nat_of_bool.
    by rewrite /cyclicTIirr; apply/eqP/eqP=> [-> | /chi_inj].
  have Chi1: (forall chi, chi \in Chi -> chi 1%g = Chi`_0 1%g).
    have->: 0%N = (0 : Iirr W1) by [].
    move=> c; rewrite Chi_nth => /mapP [k KiI ->].
    rewrite /cyclicTIirr !lin_char1 //.
  have ChiC (i : Iirr W1) :  Chi`_i - Chi`_0 \in 'CF(W, W :\: W2).
    have->: 0%N = (0 : Iirr W1) by [].
    by rewrite !Chi_nth memc_ecTIirr.
  have ChiI:  {in 'Z[Chi, W :\: W2], isometry 'Ind[L], to 'Z[irr L, L^#]}.
    split=> [u v U V |fi Hfi]; first by apply: TH (vchar_on U) (vchar_on V).
    have Wfi: fi \in 'Z[irr W].
      have: {subset Chi <= 'Z[irr W]}.
        by move=> u /mapP [i1 Hi1 ->]; exact: irr_vchar.
      by move/vchar_sub_irr; apply; apply: vcharW Hfi.
    rewrite vchar_split cfInd_vchar //.
    apply: irr_vchar_on.
    rewrite vcharD1E cfInd_vchar // cfInd1 //.
    case: (boolP (fi 1%g == 0))=> [/eqP->|HH]; first by rewrite mulr0 eqxx.
    move: (vchar_on Hfi); rewrite cfun_onE=> /subsetP /(_ _ HH).
    by rewrite inE (group1 W2).
  (* Now we can apply 1.3 *)
  case: (vchar_isometry_base NirrW1Gt ChiS ChiF Chi1 ChiC ChiI)
         => t Ut [eps Hind].
  move/(_ ([ffun i : Iirr W1 => t`_i], eps))=> /idP [].
  apply/andP; split.
    apply/injectiveP=> /= n1 n2 /eqP.
    rewrite !ffunE (nth_uniq _ _ _ Ut) ?size_tuple ?card_ord //.
    by move=> HH; apply/val_eqP.
  apply/forallP=> i; apply/eqP; rewrite !ffunE //.
  by rewrite /ecTIirr-!Chi_nth Hind.
move=> HH; apply/andP; split; last first.
  apply/forallP=> i; apply/forallP=> j.
  by case: (HH j)=> _ ->; rewrite !ffunE.
  (* This is the application of 4.1 *)
have Horth: forall i1 i2 j1 j2, i1 != 0 -> i2 != 0 -> j1 != j2 ->
         orthonormal [::'chi_((md j1).1 i1); 'chi_((md j1).1 0);
                        'chi_((md j2).1 i2); 'chi_((md j2).1 0)].
  move=> i1 i2 j1 j2 NZi1 NZi2 Dj1j2.
  have UU : [&& isRealC 1, isRealC 1, 1 != 0 :> algC & 1 != 0 :> algC].
    by rewrite !isIntC_Real ?isIntC_1 // -(eqN_eqC 1 0).
  apply: vchar_pairs_orthonormal UU _.
  - by split=> k; rewrite 2!inE => /orP [] /eqP->; exact: irr_vchar.
  - rewrite /orthonormal /=; rewrite !{1}cfdot_irr !{1}eqxx.
    case: ((md j1).1 i1 =P _)=> [|_].
      by case: (HH j1)=> HHx _; move/HHx=> /eqP Zi1; case/negP: NZi1.
    case: ((md j2).1 i2 =P _)=> [|_]; last by rewrite !eqxx.
    by case: (HH j2)=> HHx _; move/HHx=> /eqP Zi2; case/negP: NZi2.
  have F i j : ('chi_((md j).1 i) - 'chi_((md j).1 0)) 1%g = 0.
     have: 'Ind[L] (e_ i j) 1%g == 0.
       by rewrite cfInd1 //!cfunE !(lin_char1 (linearW _)) subrr mulr0 //.
     case: (HH j)=> _ /(_ i) ->.
     by rewrite cfunE (mulf_eq0) signr_eq0 /= => /eqP.
  rewrite !{1}scale1r !{1}F eqxx !andbT. 
  case: (HH j1)=> _ /(_ i1) /= Ii1j1; case: (HH j2)=> _ /(_ i2) /= Ii2j2.
  move: (TH _ _ (memc_ecTIirr i1 j1) (memc_ecTIirr i2 j2)).
  have->: '[e_ i1 j1, e_ i2 j2] = 0.
    by rewrite cfdot_subl 2!cfdot_subr !(cfdot_cTIirr cyclicTI_Dade) 
               (negPf Dj1j2) !andbF subrr.
  rewrite Ii1j1 Ii2j2 cfdotZl cfdotZr mulrA.
  move/eqP; rewrite mulf_eq0 => /orP [] //.
  by rewrite isIntC_conj ?isIntC_sign // -signr_addb signr_eq0.
apply/injectiveP=> [[i1 j1] [i2 j2] /=]; rewrite !ffunE.
case: (boolP (j1 == j2)) => [/eqP <-| Dj1j2 Eqm].
  by case : (HH j1)=> Hv _; move/Hv<-.
suff: '['chi_((md j1).1 i1), 'chi_((md j2).1 i2)] == 0.
  by rewrite cfdot_irr {1}Eqm eqxx -(eqN_eqC 1 0).
pose i3 : Iirr W1  := inZp 1.
have NZi3 : i3 != 0.
  by apply/eqP; move/val_eqP=> /=; rewrite modn_small.
case: (i1 =P 0)=> [Zi1 | /eqP NZi1]; case: (i2 =P 0)=> [Zi2 | /eqP NZi2].
  - case/orthonormalP: (Horth _ _ _ _ NZi3 NZi3 Dj1j2)=> /and4P [] _ /negP [].
    by rewrite -{1}[0]Zi1 -{1}[0]Zi2 {1}Eqm !in_cons eqxx !orbT.
  - case/orthonormalP: (Horth _ _ _ _ NZi3 NZi2 Dj1j2)=> /and4P [] _ /negP [].
    by rewrite -{1}[0]Zi1 {1}Eqm !in_cons eqxx.
  - case/orthonormalP: (Horth _ _ _ _ NZi1 NZi3 Dj1j2)=> /and4P [] /negP [].
    by rewrite -{2}[0]Zi2 {1}Eqm !in_cons eqxx !orbT.
case/orthonormalP: (Horth _ _ _ _ NZi1 NZi2 Dj1j2)=> /and4P [] /negP [].
by rewrite {1}Eqm !in_cons eqxx !orbT.
Qed.

Lemma Dade_mu2_inj i1 i2 j1 j2 :
  mu2 i1 j1 = mu2 i2 j2 -> (i1, j1) = (i2, j2).
Proof. by case: Dade_mudelta_spec=> HH _; apply: (HH (_,_) (_,_)). Qed.

(* First part of PeterFalvi (4.3b). *)
Lemma Dade_mu2_ind :
        forall i j,
       'Ind[L] (e_ i j) =
            (-1) ^+ (delta j) *: ('chi_(mu2 i j) - 'chi_(mu2 0 j)).
Proof. by case: Dade_mudelta_spec. Qed.

(* This is Peterfalvi (4.3c). *) 
Lemma Dade_mu2_restrict :
  (forall i j,  
   {in W :\: W2, 'chi_(mu2 i j) =1 (-1) ^+ delta j *: w_ i j})
  /\
  (forall k,
    (forall i j, 'chi_k != 'chi_(mu2 i j)) ->
       {in W :\: W2, forall x, 'chi_k x = 0}).
Proof.
pose m (k : Iirr W) : 'CF(L) := 
  let (i,j) := inv_dprod_Iirr W1xW2 k in (-1) ^+ delta j *: 'chi_(mu2 i j).
pose t := [tuple of ecTIirr_base].
have F1 : is_basis 'CF(W, W :\: W2) t by apply:  ecTIirr_base_is_basis.
have F2 i j : '[m i, m j] = (i == j)%:R.
  rewrite -{2}[i](inv_dprod_IirrK W1xW2) -{2}[j](inv_dprod_IirrK W1xW2).
  rewrite /m; (do 2 case: (inv_dprod_Iirr _ _))=> i2 j2 i1 j1.
  rewrite cfdotZl cfdotZr cfdot_irr mulrA isIntC_conj ?isIntC_sign // -signr_addb.
  case: (_ (i1,_) =P _).
    by case/dprod_Iirr_inj=> <- <-; rewrite -negb_eqb !eqxx expr0 mul1r.
  case: (_ =P _); last by rewrite mulr0.
  by case/Dade_mu2_inj=> <- <- [].
case: (equiv_restrict_compl_ortho _ _  F1 F2)=> // [|k|HH1 HH].
- rewrite /normal subsetDl.
  by case/andP: normedTI_Dade_W2=> _ /eqP {1}<-; exact: subsetIr.
- have: t`_k \in t by apply: mem_nth; rewrite size_tuple.
  case/imageP=> [[/= i1 j1]]; rewrite !inE => /= /andP [] Hi1 _ ->.
  have NZi1: i1 != 0%N :> nat by apply: contra Hi1=> HH. 
  pose dP i j := dprod_Iirr W1xW2 (i, j).
  have FdP : dP 0 j1 != dP i1 j1.
    by apply/negP=> /eqP /dprod_Iirr_inj [] HH; case/eqP: Hi1.
  rewrite Dade_mu2_ind (bigD1 (dP i1 j1)) // (bigD1 (dP 0 j1)) //=.
  rewrite big1 ?addr0=> [|i /andP [] iDi1 iD0]; last first.
    by rewrite !cfdot_subl !(cTIirrE cyclicTI_Dade) !cfdot_irr eq_sym (negPf iDi1) 
               eq_sym (negPf iD0) subrr scale0r.
  rewrite !cfdot_subl  !(cTIirrE cyclicTI_Dade) !cfdot_irr !{1}eqxx.
  rewrite [_ == dP 0 _]eq_sym (negPf FdP).
  by rewrite /m !dprod_IirrK !subr0 sub0r scaleNr !scale1r -scalerBr.
split=> [i j x XiW|k Hk].
  move: (HH1 (dprod_Iirr W1xW2 (i, j)) _ XiW).
  rewrite /m dprod_IirrK !cfunE !(cTIirrE cyclicTI_Dade) => <-.
  by rewrite mulrA -signr_addb -negb_eqb !eqxx expr0 mul1r.
apply: HH=> i; rewrite /m; case: inv_dprod_Iirr=> i1 j1.
rewrite cfdotZr cfdot_irr; case: (_ =P _)=> [Heq|Hneq]; last by rewrite mulr0.
by case/eqP: (Hk i1 j1); rewrite Heq.
Qed.

(* Last part of PeterFalvi (4.3b). *)
Lemma Dade_mu2_sigma i j :
  sigma (w_ i j) = (-1) ^+ delta j *: 'chi_(mu2 i j).
Proof.
apply: sym_equal; apply: (@cyclicTI_dirr  _ _ _ _ _ cyclicTI_Dade)=> [|g].
  by rewrite dirr_sign dirr_chi.
rewrite !inE !cfunE -/(w_ i j) negb_or -andbA => /and3P [GniW1 GniW2 GiW].
case: Dade_mu2_restrict=> ->; last by rewrite inE GniW2.
by rewrite cfunE mulrA -signr_addb -negb_eqb eqxx expr0 mul1r.
Qed.

Let classesW1 : #|classes W1| = #|W1|.
Proof.
by have:= cyclic_abelian CW1; rewrite card_classes_abelian => /eqP ->.
Qed.

Let classesW2 : #|classes W2| = #|W2|.
Proof.
by have:= cyclic_abelian CW2; rewrite card_classes_abelian => /eqP ->.
Qed.

(* This is PeterFalvi (4.3d). *)
Lemma Dade_mu2_mod i j : 
  {a | isIntC a /\ 'chi_(mu2 i j) 1%g = (-1) ^+ delta j + a *+ #|W1| }.
Proof.
pose rD := 'Res[W1] 'chi_(mu2 i j) - 'Res[W1] ((-1) ^+ delta j *: w_ i j). 
have rDV: rD \in 'Z[irr W1].
  by rewrite sub_vchar // cfRes_vchar ?sign_vchar // irr_vchar.
have rDF: rD \in 'CF(W1, 1%g).
  apply/cfun_onP=> g Gni1. 
  case: (boolP (g \in W1))=> [GiW1|GniW1]; last by rewrite cfun0.
  rewrite !cfunE !cfResE // !cfunE.
  case: (Dade_mu2_restrict)=> ->; rewrite ?(cfunE, subrr) //.
  rewrite inE (subsetP W1sW) // andbT.
  apply: contra Gni1=> GiW2.
  by case/dprodP: W1xW2=> _ _ _ <-; rewrite inE GiW1.
pose a k := '[rD, 'chi_k].
pose LW1 i := lin_char1 (cTIirr_linearW1 cyclicTI_Dade i).
pose LW i := lin_char1 (cTIirr_linearW cyclicTI_Dade i).
have Ha k: a k = a 0.
  rewrite /a !cfdotE (bigD1 1%g) //= big1=> [|u /andP [_ NOu]]; last first.
    by rewrite (cfun_on0 rDF) ?mul0r // inE.
  rewrite (bigD1 1%g) //= big1=> [|u /andP [_ NOu]]; last first.
    by rewrite (cfun_on0 rDF) ?mul0r // inE.
  by rewrite !LW1.
exists (a 0); split.
  by apply: cfdot_vchar_irr_Int.
suff<-: rD 1%g =  a 0 *+ #|W1|.
  by rewrite !cfunE !cfResE ?group1 // !cfunE LW mulr1 addrC subrK.
rewrite {1}[rD]cfun_sum_cfdot sum_cfunE (eq_bigr (fun _ => a 0))=> [|u Hu].
  by rewrite sumr_const cardT size_enum_ord NirrE classesW1.
by rewrite -/(a u) Ha cfunE LW1 mulr1.
Qed.

Lemma Dade_delta_aut u j : delta (aut_Iirr u j) = delta j.
Proof.
have/esym/cfunP/(_ 1%g) := cfAut_cycTIiso cyclicTI_Dade u (w_ 0 j).
rewrite -(cycTIirr_aut cyclicTI_Dade) aut_Iirr0 !Dade_mu2_sigma !cfunE.
rewrite rmorphM rmorph_sign=> /(canLR (signrMK _))/(congr1 (fun x => x > 0)).
rewrite rmorph_NatC ?isNatC_irr1 // ltC_irr1 mulrA -signr_addb -negb_eqb.
by case: eqP => [-> // | _]; rewrite mulN1r sposC_opp leC_gtF // ltCW ?ltC_irr1.
Qed.

Lemma Dade_mu2_aut u i j :
  'chi_(mu2 (aut_Iirr u i) (aut_Iirr u j)) = cfAut u 'chi_(mu2 i j).
Proof.
rewrite -!(canLR (signrZK _) (Dade_mu2_sigma _ _)).
rewrite Dade_delta_aut cfAutZ rmorph_sign; congr (_ *: _).
by rewrite (cycTIirr_aut cyclicTI_Dade) (cfAut_cycTIiso cyclicTI_Dade).
Qed.

Definition Dade_mu j : 'CF(L) := \sum_(i < Nirr W1) 'chi_(mu2 i j).
Local Notation mu := Dade_mu.

Lemma Dade_mu_aut u j : mu (aut_Iirr u j) = cfAut u (mu j).
Proof.
rewrite raddf_sum [mu _](reindex_inj (aut_Iirr_inj u)).
by apply: eq_bigr => i _; rewrite /= Dade_mu2_aut.
Qed.

Lemma cfdot_mu i j : '[mu i, mu j] = ((i == j) * #|W1|)%:R.
Proof.
rewrite /mu  cfdot_suml; case: eqP=> [->|/eqP Dij]; last first.
  rewrite big1 // => i1 _.
  rewrite cfdot_sumr big1 // => k2 _; rewrite cfdot_irr.
  by case: eqP=> //; case/Dade_mu2_inj=> _ /eqP ; rewrite (negPf Dij).
have<-: \sum_(i < Nirr W1) 1 = (true * #|W1|)%:R :> algC.
  by rewrite sumr_const cardT size_enum_ord NirrE classesW1 mul1n.
apply: eq_bigr=> i1 _.
rewrite cfdot_sumr (bigD1 i1) // big1  //= ?addr0.
  by rewrite cfdot_irr eqxx.
move=> i2 Di1i2; rewrite cfdot_irr.
by case: eqP=> // /Dade_mu2_inj [HH]; case/eqP: Di1i2.
Qed.

Lemma Dade_mu_neq0 i : mu i != 0.
Proof. by rewrite -cfnorm_eq0 cfdot_mu eqxx mul1n neq0GC. Qed.

Lemma Dade_mu_inj : injective mu.
Proof.
move=> j1 j2 Ej1j2.
move: (cfdot_mu j1 j2); case: eqP=> // _ /eqP.
by rewrite Ej1j2 cfnorm_eq0 (negPf (Dade_mu_neq0 _)).
Qed. 

Definition Dade_chi j : Iirr K := 
  odflt 0 [pick i | 'chi_i == 'Res[K] 'chi_(mu2 0 j)]. 
Local Notation chi := Dade_chi.

Let W1isoLqK : W1 \isog (L / K)%g.
Proof. exact: isog_sdprod_factor. Qed.

Let Dade_delta0_mu20 : (delta 0 == false) && (mu2 0 0 == 0).
Proof.
have F1: 'Res[W] 'chi[L]_0 = 'chi[W]_0.
  apply/cfunP=> g.
  case: (boolP (g \in W))=> [GiW|GniW]; last by rewrite !cfun0.
  by rewrite cfResE // !chi0_1 !cfun1E (subsetP WsL) GiW.
have F2: 'chi_0 \in dirr L by apply: dirr_chi.
have F3: {in cyclicTIset cyclicTI_Dade, 'chi[L]_0 =1 w_ 0 0}.
  move=> g; rewrite inE=> [/andP [_ GiW]].
  rewrite (cTIirr00 cyclicTI_Dade) chi0_1 !cfun1E.
  by rewrite (subsetP WsL) GiW.
move: (cyclicTI_dirr F2 F3); rewrite Dade_mu2_sigma.
case: (delta 0); rewrite (expr0, expr1).
  rewrite scaleN1r=> HH.
  have: 0 < 'chi[L]_0 1%g + 'chi_(mu2 0 0) 1%g.
    by apply: sposC_addl; try apply: ltCW; apply: ltC_irr1.
  by rewrite HH cfunE addNr ltCE eqxx.
by rewrite scale1r => /chi_inj<-.
Qed.

Lemma Dade_delta0 : delta 0 = false.
Proof. by case/andP: Dade_delta0_mu20=> /eqP. Qed.

Lemma Dade_mu20 : mu2 0 0 = 0.
Proof. by case/andP: Dade_delta0_mu20=> _ /eqP. Qed.

(* This is PeterFalvi (4.4). *)
Lemma Dade_mu2_subset_cfker :
 [set i |  K \subset cfker 'chi[L]_i] = [set (mu2 i 0) | i <- Iirr W1]. 
Proof.
have KnL: K <| L by case/sdprod_context: SdP.
apply/eqP; rewrite eqEcard; apply/andP; split.
  apply/subsetP=> j; rewrite !inE=> KsK.
  have Ab: abelian (L / K).
    rewrite -(isog_abelian W1isoLqK).
    by apply: cyclic_abelian CW1.
  have: 'Res[W] 'chi[L]_j \in irr W.
    apply: lin_char_irr. 
    rewrite /lin_char cfRes_char ?irr_char //= cfResE ?group1 //.
    rewrite -(cfQuoE KnL) // (coset_id (group1 _)) -quo_IirrE //.
    by rewrite lin_char1 //; move/char_abelianP: Ab; apply.
  case/irrP=> j1 Hj1.
  pose i : Iirr W1 := (inv_dprod_Iirr HdP j1).1.
  have F1: 'chi_j1 = w_ i 0.
    apply/cfunP=> g.
    case: (boolP (g \in W))=> [|GniW]; last by rewrite !cfun0.
    case/dprodP: HdP=> _ {1}<- _ _ /imset2P [h1 h2 H1iW1 H2iW2 ->].
    suff->: 'chi_j1 (h1 * h2)%g = 'chi_j1 (h1 * 1)%g.
      rewrite -[j1](inv_dprod_IirrK HdP) /i.
      case: (inv_dprod_Iirr HdP j1)=> /= i2 j2.
      rewrite (cTIirrE cyclicTI_Dade) !dprod_IirrE !cfDprodE //.
      pose LW2 i := lin_char1 (cTIirr_linearW2 cyclicTI_Dade i).
      by rewrite !LW2 // chi0_1 cfun1E H2iW2.
    have H1iW: h1 \in W by apply: (subsetP W1sW _).
    have H2iW: h2 \in W by apply: (subsetP W2sW _).
    rewrite mulg1 -!Hj1 !cfResE ?groupM //.
    by rewrite cfkerMr // (subsetP KsK) // (subsetP W2sK).
  apply/imsetP; exists i=> //.
  have F2: 'chi_j \in dirr L by apply: dirr_chi.
  have F3: {in cyclicTIset cyclicTI_Dade, 'chi_j =1 w_ i 0}.
    move=> g; rewrite inE=> [/andP [_ HH]].
    by rewrite -F1 -Hj1 cfResE.
  move: (cyclicTI_dirr F2 F3); rewrite Dade_mu2_sigma.
  by rewrite Dade_delta0 scale1r=> /chi_inj.
 (* could be improved surely *)
rewrite imset_card card_image => [|x y]; last by case/Dade_mu2_inj.
rewrite card_ord //  NirrE classesW1.
have->: #|W1| = #|[image (mod_Iirr i) | i <- Iirr(L/K)]|.
  rewrite card_in_image => [|g h GiQ hiQ].
    rewrite card_ord // NirrE.
    move: W1isoLqK; rewrite isog_cyclic_card // => /andP [CQ /eqP<-].
    by have:= cyclic_abelian CQ; rewrite card_classes_abelian => /eqP ->.
    by case: (mod_Iirr_bij KnL)=> f /on_can_inj HH _ /HH; apply;
       rewrite !inE -quo_IirrKeq // mod_IirrK.
apply: subset_leq_card; apply/subsetP=> g.
rewrite /= !inE=> /imageP [i IiQ ->].
by rewrite -quo_IirrKeq // mod_IirrK.
Qed.

Let KnL : K <| L. Proof. by case/sdprod_context: SdP. Qed.

Let KIW :  K :&: W = W2.
Proof.
apply/eqP; rewrite eqEsubset; apply/andP; split; apply/subsetP=> g; last first.
  move=> GiW2; rewrite !inE (subsetP W2sK) //.
  by case/dprodP: HdP=> _ <- _ _; rewrite (subsetP (mulg_subr _ _)).
rewrite inE => /andP [] GiK GiW; move: GiW GiK.
case/dprodP: HdP=> _ <- _ _; case/imset2P=> w1 w2 W1iW1 W2iW2 -> W1W2iK.
suff: w1 \in 1%G by rewrite inE => /eqP ->; rewrite mul1g.
case/sdprodP: SdP=> _ _  _ /= <-; rewrite inE W1iW1 andbT.
by move: W1W2iK; rewrite groupMr // (subsetP W2sK).
Qed.

Lemma Dade_chi_eq i j : 'Res[K] 'chi_(mu2 i j) = 'Res[K] 'chi_(mu2 0 j).
Proof.
apply/cfunP=> g.
case: (boolP (g \in K))=> [GiK|GniK]; last by rewrite !cfun0.
rewrite !cfResE //.
suff: 'Ind[L] (e_ i j) g == 0.
  by rewrite Dade_mu2_ind !cfunE mulf_eq0 signr_eq0 /= subr_eq0 => /eqP.
rewrite cfIndE ?big1 ?mulr0 // => h HiL.
move/cfun_onP: (memc_ecTIirr i j); apply.
rewrite !inE negb_and negbK.
case: (boolP (_ \in W))=> [GiW|]; rewrite !(orbT, orbF) //.
rewrite -KIW inE GiW andbT.
move: HiL; case/sdprodP: SdP=> _ <- /subsetP HH _.
case/imset2P=> k w KiK WiW ->; rewrite conjgM.
by move/normP: (HH _ WiW)<-; rewrite memJ_conjg groupJ.
Qed.

Let Dade_Ind_DI i j : 
  'Ind[L] 'chi_i = 
      \sum_(i0 < Nirr W1) '['Res[K] 'chi_(mu2 i0 j), 'chi_i] *: 'chi_(mu2 i0 j) +
      \sum_(i0 < Nirr L | i0 \notin [image mu2 i1 j  | i1 <- Iirr W1])
          '['Res[K] 'chi_i0, 'chi_i] *: 'chi_i0.
Proof.
rewrite [X in X = _]cfun_sum_cfdot.
rewrite (eq_bigr (fun k => '['Res[K] 'chi_k, 'chi_i] *: 'chi_k)); last first.
  move=> k; rewrite -cfdot_Res_r cfdotC isNatC_conj //.
  by apply: cfdot_char_irr_Nat (cfRes_char _ (irr_char _)).
rewrite (bigID [pred k | k \in [image (mu2 i j) | i <- Iirr W1]]) /=.
congr (_ + _).
pose h i := odflt 0 [pick k | mu2 k j == i].
rewrite (reindex_onto (mu2^~ j) h)=> [/= | i1]; last first.
  case/imageP=> i2 i2Irr ->.
  by rewrite /h; case: pickP=> [u /eqP | /(_ i2)]; rewrite ?eqxx.
rewrite (eq_bigl xpredT)=> [|i1] //.
rewrite (@image_f _  _ (mu2^~ j)) //.
rewrite /h; case: pickP=> [i2 /eqP | /(_ i1)]; last by rewrite eqxx.
by case/Dade_mu2_inj=> /eqP.
Qed.

Let Dade_indexE : #|L : K| = #|W1|.
Proof.
move: (LaGrange KsL)=> /eqP; rewrite -{1}(sdprod_card SdP) eqn_mul2l.
by case: #|K| (cardG_gt0 K)=> //= _ _ /eqP.
Qed.

(* These are the first two parts of PeterFalvi (4.5a). *)
Lemma Dade_chiE i j : 'chi_(chi j) = 'Res[K] 'chi_(mu2 i j).
Proof.
rewrite {i}Dade_chi_eq /chi; case: pickP=> [k /eqP // | /=].
suff /irrP[k -> /(_ k)]: 'Res[K] 'chi_(mu2 0 j) \in irr K.
  by rewrite eqxx.
set v := 'Res[_] _.
have Cv : is_char v := cfRes_char _ (irr_char _).
have /neq0_has_constt[i HiC]: v != 0.
  move: (irr1_neq0 (mu2 0 j)); rewrite /v -(cfResE _ KsL (group1 _)).
  by apply: contra=> /eqP->; rewrite cfunE.
apply/irrP; exists i.
suff HF: 'chi_i 1%g = v 1%g.
  suff TH k : '[v, 'chi_k] == (k == i)%:R.
    rewrite [v]cfun_sum_cfdot (bigD1 i) // big1 /= => [|k Hk].
      by rewrite addr0 (eqP (TH _)) eqxx scale1r.
    by rewrite (eqP (TH _)) (negPf Hk) scale0r.
  suff:
    ('[v, 'chi_k] *: 'chi_k - if k ==  i then 'chi_k else 0) 1%g == 0.
    case: (k == _); rewrite ?(subr0, cfunE).
      by rewrite  -[X in _ - X == _]mul1r -mulrBl mulf_eq0 
               (negPf (irr1_neq0 _)) orbF // subr_eq0.
    by rewrite  mulf_eq0 (negPf (irr1_neq0 _)) orbF.
  apply/eqP; move: k is_true_true.
  apply: posC_sum_eq0 => [k _|]; last first.
    rewrite -sum_cfunE sumrB -cfun_sum_cfdot 2!cfunE -big_mkcond /=.
    rewrite (bigD1 i) // big1=> [|k]; last by case: (_ == _).
    by rewrite !cfunE addr0 HF subrr.
  case: (_ =P _)=> [->|_]; rewrite !cfunE ?subr0; last first.
     by apply: posC_mul; apply: posC_Nat;
          [apply: (cfdot_char_irr_Nat k Cv) | exact: isNatC_irr1 k].
  rewrite  -[X in _ <= _ - X]mul1r -mulrBl.
  apply: posC_mul; last by apply: posC_Nat (isNatC_irr1 _).
  rewrite leC_sub; move: HiC; rewrite irr_consttE.
  case/isNatCP: (cfdot_char_irr_Nat i Cv)=> n ->.
  by rewrite -(eqN_eqC _ 0) -(leq_leC 1); case: n.
apply: leC_anti.
  by move: (char1_ge_constt Cv HiC); rewrite (cfResE _ KsL (group1 _)).
have /leC_pmul2l<- : 0 <  #|W1|%:R by rewrite -(ltn_ltC 0) cardG_gt0.
rewrite -{2}Dade_indexE -(cfInd1 'chi_i KsL) (Dade_Ind_DI _ j).
have->: #|W1|%:R * v 1%g = \sum_i 'chi_(mu2 i j) 1%g.
  rewrite (eq_bigr (fun k => v 1%g))=> [| k _].
    rewrite sumr_const cardT -cardE /= card_ord mulr_natl NirrE.
    by have:= cyclic_abelian CW1; rewrite card_classes_abelian => /eqP ->.
  by rewrite -(cfResE _ KsL) // Dade_chi_eq (cfResE _ KsL).
rewrite -leC_sub !cfunE !sum_cfunE addrAC -sumrB.
apply: posC_add; apply: posC_sum=> k _; rewrite !cfunE; last first.
   by apply: posC_mul; apply: posC_Nat;
          [apply: (cfdot_char_irr_Nat i  (cfRes_char _ (irr_char _)))
             | exact: isNatC_irr1 k].
  rewrite  -[X in _ <= _ - X]mul1r -mulrBl.
  apply: posC_mul; last by apply: posC_Nat (isNatC_irr1 _).
  rewrite leC_sub; move: HiC; rewrite irr_consttE Dade_chi_eq -/v.
  case/isNatCP: (cfdot_char_irr_Nat i Cv)=> n ->.
  by rewrite -(eqN_eqC _ 0) -(leq_leC 1); case: n.
Qed.

(* This is the last part of PeterFalvi (4.5a). *)
Lemma Dade_Ind_chi j : 'Ind[L] 'chi_(chi j) = mu j.
Proof.
move: (cfInd1 'chi_(chi j) KsL).
rewrite (Dade_Ind_DI _ j) Dade_indexE.
rewrite (eq_bigr (fun k => 'chi_(mu2 k j)))=> [| k _]; last first.
  by rewrite -Dade_chiE cfdot_irr eqxx scale1r.
rewrite !cfunE !sum_cfunE.
rewrite (eq_bigr (fun k => 'chi_(mu2 0 j) 1%g))=> [| k _]; last first.
  by rewrite -(cfResE _ KsL) // Dade_chi_eq (cfResE _ KsL).
rewrite sumr_const cardT -cardE /= card_ord [#|W1|%:R * _]mulr_natl.
rewrite (Dade_chiE 0) (cfResE _ KsL) // {1}(NirrE W1).
have:= cyclic_abelian CW1; rewrite card_classes_abelian => /eqP ->.
move/eqP; rewrite addrC -subr_eq0 addrK=> HH.
rewrite [X in _ + X = _]big1 ?addr0 // => i Hi.
suff: forall k, k \notin [image mu2 i1 j  | i1 <- Iirr W1] ->
     ('['Res[K] 'chi_k, 'Res[K] 'chi_(mu2 0 j)] *: 'chi_k) 1%g = 0.
  move/(_ _ Hi)=> /eqP.
  rewrite cfunE  mulf_eq0 (negPf (irr1_neq0 _)) orbF => /eqP ->.
  by rewrite scale0r.
apply: (posC_sum_eq0 _ (eqP HH))=> k _; rewrite cfunE.
apply: posC_mul; last by apply: posC_Nat (isNatC_irr1 _).
rewrite -Dade_chiE posC_Nat // cfdot_char_irr_Nat //.
by apply: cfRes_char _ (irr_char _).
Qed.

Lemma Dade_chi_aut u j : 'chi_(chi (aut_Iirr u j)) = cfAut u ('chi_(chi j)).
Proof.
by rewrite (Dade_chiE (aut_Iirr u 0)) Dade_mu2_aut -cfAutRes -Dade_chiE.
Qed.

Lemma Dade_chi0 : 'chi_(chi 0) = 1.
Proof. by rewrite (Dade_chiE 0) Dade_mu20 chi0_1 cfRes_cfun1. Qed.

Lemma Dade_mu0 : mu 0 = #|W1|%:R *: '1_K.
Proof.
rewrite -Dade_Ind_chi Dade_chi0 cfInd_cfun1 //.
by rewrite -divgS // -(sdprod_card SdP) mulKn.
Qed.

Let W1cK: coprime #|W1| #|K|.
Proof.
case: HC => [[_ _ H_Hall _] [_ WsK _ _] _].
by rewrite coprime_sym (coprime_sdprod_Hall SdP) (sdprod_Hall SdP).
Qed.

Lemma Dade_chi_inj : injective chi.
Proof.
by move=> j1 j2 Dj; apply: Dade_mu_inj; rewrite -!Dade_Ind_chi Dj.
Qed.

(* This is the first assertion of Peterfalvi (4.5b). *)
Theorem Dade_Ind_chi'_irr k :
    k \notin codom chi ->
  let phi := 'Ind 'chi_k in phi \in irr L /\ (forall i j, phi != 'chi_(mu2 i j)).
Proof.
move=> KniC phi.
suff IeK: 'I_L['chi_k] = K.
  have PiI: phi \in irr L by apply: inertia_Ind_irr; rewrite ?IeK.
  split=> // i j; apply/eqP => PeJ; case/negP: (irr_neq0 (mu2 i j)).
  rewrite -cfnorm_eq0 -{1}PeJ -Frobenius_reciprocity -Dade_chiE cfdot_irr.
  by case: (k =P _) => // KeJ; case/negP: KniC; apply/imageP; exists j.
have KsI := sub_inertia 'chi_k KnL.
apply/eqP; rewrite eqEsubset KsI andbT.
apply/subsetP=> g; rewrite !inE => /andP [/andP []].
case/sdprodP: SdP => _ <- _ _; case/imset2P=> k1 w1 K1iK W1iW -> _.
case: (boolP (w1 == 1%g)) => [/eqP-> |W1no]; first by rewrite mulg1.
move: (subsetP KsI _ K1iK); rewrite inE => /andP [K1iNL /eqP ChiE].
have K1iN: k1 \in 'N(K) by move: K1iNL; rewrite inE; case/andP. 
have W1iN: w1 \in 'N(K).
  by case/andP: KnL=> _ /subsetP; apply; apply: (subsetP W1sL).
rewrite cfConjgMnorm // ChiE => /eqP ChiW1E.
have actIirrK: is_action L (@conjg_Iirr _ K).
  split=> [y j k2 eq_jk2 | j y z Gy Gz].
    by apply/chi_inj/(can_inj (cfConjgK y)); rewrite -!conjg_IirrE eq_jk2.
  by apply: chi_inj; rewrite !conjg_IirrE (cfConjgM _ KnL).
pose ito := Action actIirrK.
suff FeC: 'Fix_ito[w1] = [set i | i \in codom chi].
  suff: k \in 'Fix_ito[w1] by rewrite FeC inE => HH; case/negP: KniC.
  rewrite inE; apply/subsetP=> w2; rewrite !inE => /eqP->.
  by apply/eqP; apply: chi_inj; rewrite conjg_IirrE.
have W1iL := (subsetP W1sL _ W1iW).
apply/eqP; rewrite eq_sym eqEcard; apply/andP; split.
  apply/subsetP=> i1; rewrite inE; case/imageP=> /= i2 I2iIW2 ->.
  rewrite inE; apply/subsetP=> w2; rewrite !inE => /eqP->.
  apply/eqP; apply: chi_inj; rewrite conjg_IirrE.
  apply/cfunP=> u; case: (boolP (u \in K))=> [UiK|UniK]; last by rewrite !cfun0.
  have UWiK : u ^ w1 \in K.
    by rewrite -mem_conjgV; case/normalP: KnL=> _ ->; rewrite ?groupV.
  have UWIiK : u ^ w1^-1 \in K by rewrite -mem_conjg; case/normalP: KnL=> _ ->.
  by rewrite !(Dade_chiE 0) cfConjgE // !cfResE // cfunJ // groupV.
have ->: #|[set i \in codom chi]| = #|W2|.
  rewrite  -classesW2 -NirrE.
  suff {2}<-: #|codom chi| = Nirr W2  by apply: eq_card=> i; rewrite inE.
  by rewrite card_codom  ?card_ord //; exact: Dade_chi_inj.
have acts_Js : [acts L, on classes K | 'Js].
  apply/subsetP=> y YiL.
  have YiNK : y \in 'N(K) by case/andP: KnL=> _ /subsetP /(_ _ YiL).
  rewrite !inE; apply/subsetP=> _ /imsetP[z ZiK ->]; rewrite !inE /=.
  rewrite -class_rcoset norm_rlcoset // class_lcoset //.
  by apply: mem_imset; rewrite memJ_norm.
have acts_JsL : [acts L, on classes K | ('Js \ (subsetT L))%act].
  by rewrite astabs_ract subsetIidl.
rewrite (card_afix_irr_classes W1iL acts_JsL); last first.
  move=> k2 g1 h1 G1iK .
  case/imsetP=> x /imsetP [h2 H2iK ->] ->.
  by rewrite conjg_IirrE cfConjgEnorm // cfunJ.
pose f (C : {set gT}) := odflt 1%g [pick i | i \in C :&: W2].
set S := 'Fix_(_ | _)[_].
have SE (C : {set gT}) : C \in S -> (C \in classes K) && (C :^ w1 == C)%g.
  rewrite !inE; case/andP=> -> /subsetP /(_ w1).
  by rewrite !inE => /(_ (eqxx _)).
suff FE : forall C, C \in S -> f C \in C :&: W2.
  suff: {in S &, injective f}.
    move/card_in_imset=> <-; rewrite subset_leqif_card //.
    apply/subsetP=> i /imsetP=> [[x _ ->]].
    by rewrite /f; case: pickP=> //=  u; rewrite !inE=> /andP [].
  move=> C1 C2 /= C1iS C2iS F1eF2.
  move: (SE _ C1iS) (SE _ C2iS) (FE _ C1iS) (FE _ C2iS); rewrite -F1eF2.
  move=> /andP [/imsetP [u UiK ->] _] /andP [/imsetP [v ViK ->] _].
  rewrite inE => /andP  [FUi _]; rewrite inE => /andP  [FVi _].
  by rewrite -(class_transr FUi) (class_transr FVi).
move=> C /SE /andP [CiS /eqP CiK]; rewrite /f; case: pickP=> // CiW2.
have acts_J : [acts <[w1]>, on C | 'J].
  apply/actsP=> x /cycleP [n ->] h /=.
  suff {1}<-: C :^ (w1 ^+ n) = C.
    by apply/imsetP/idP=> [[c CiC] /conjg_inj -> // | HiC]; exists h.
  elim: n=> [|n IH]; first by rewrite expg0 conjsg1.
  by rewrite expgSr conjsgM IH CiK.
have CeOmW : (#|C| = #|orbit 'J <[w1]>%G @: C| * #[w1])%N.
  apply: card_uniform_partition (orbit_partition acts_J)=> o.
  case/imsetP=> c CiC ->; rewrite -[X in X = _]muln1.
  suff<-: #|'C_<[w1]>[c | 'J]| = 1%N.
    by apply: card_orbit_in_stab; apply/subsetP=> h; rewrite inE.
  rewrite -(cards1 (1%g : gT)).
  apply: eq_card=> h; rewrite  astab1J [X in _ = X]inE.
  apply/idP/eqP=> [|->]; last by rewrite group1.
  rewrite inE=> /andP [HiG HiC].
  case: (boolP (h == 1%g))=> [/eqP //| Hn1].
  suff CiCW2: c \in C :&: W2 by move: (CiW2 c); rewrite CiCW2.
  have HiW1: h \in W1^#.
    by rewrite !inE Hn1; move: W1iW; rewrite -cycle_subG; move/subsetP; apply.
  rewrite inE CiC -(Hcent HiW1) inE cent1C HiC.
  case/repr_classesP: CiS CiC => RiK -> /imsetP [h1 H1iK ->].
  by rewrite groupJ.
case/negP: W1no; rewrite -order_eq1.
move: W1cK; rewrite -dvdn1 /coprime => /eqP <-.
rewrite dvdn_gcd cardSg; last first.
  by rewrite gen_subG; apply/subsetP=> h; rewrite inE => /eqP->.
have CdK : #|C| %| #|K| by case/repr_classesP: CiS=> RiK ->; apply: dvdn_orbit.
apply: dvdn_trans CdK; rewrite CeOmW.
by apply: dvdn_mull (dvdnn _).
Qed.

(* Implicit elementary converse to the above. *)
Lemma Dade_mu_not_irr j : mu j \notin irr L.
Proof.
rewrite irr_char1E; apply/nandP; right; rewrite -[mu j](big_map _ xpredT id).
rewrite /index_enum -enumT cfnorm_map_orthonormal //.
  rewrite size_map -cardE card_ord -(eqN_eqC _ 1) NirrE neq_ltn orbC.
  by rewrite classes_gt1; have [[_ ->] _ _] := HC.
apply/orthonormalP; split=> [|_ _ /mapP[i1 _ ->] /mapP[i2 _ ->]].
  by rewrite map_inj_uniq ?enum_uniq // => ? ? /chi_inj/Dade_mu2_inj[].
by rewrite cfdot_irr (inj_eq chi_inj).
Qed.

(* This is the second assertion of Peterfalvi (4.5b). *)
Theorem Ptype_irr_mu2Vchi'Ind ell (phi := 'chi_ell) :
   {i : _ & {j | phi = 'chi_(mu2 i j)}}
     + {k | k \notin codom chi & phi = 'Ind 'chi_k}.
Proof.
pose l := odflt 0 [pick i | i \in irr_constt ('Res[K] phi)].
have: ell \in irr_constt ('Ind[L] 'chi_l).
  rewrite constt_Ind_constt_Res /l.
  case: pickP=> //=.
  case/neq0_has_constt: (Res_irr_neq0 ell KsL)=> j1 Hj1 /(_ j1).
  by rewrite Hj1.
case: (boolP (l \in codom chi))=> [JiC|JniC EiI]; last first.
  right; exists l=> //.
  move: EiI; rewrite irr_consttE /phi.
  case/Dade_Ind_chi'_irr: JniC=> /irrP [j1 ->] _.
  by rewrite cfdot_irr; case: (j1 =P _)=> [->|]; rewrite // eqxx.
pose j := odflt 0 [pick j | l == chi j].
have ->: l = chi j.
  rewrite /j; case: pickP=> [j1 /eqP //|].
  by case/imageP: JiC=> j1 Hj1 -> /(_ j1); rewrite eqxx.
pose i := odflt 0 [pick i | phi == 'chi_(mu2 i j)].
rewrite Dade_Ind_chi irr_consttE cfdot_suml=> CDots.
left; exists i; exists j.
rewrite /i; case: pickP=> [i1 /eqP //| FEq].
case/eqP: CDots; rewrite big1=> // k _.
rewrite cfdot_irr eq_sym; case: eqP=> // Eq.
by move: (FEq k); rewrite -Eq eqxx.
Qed.

End CyclicDade.

 (* Move to character *)

Lemma cfker_char_res (K G : {group gT}) (chi : 'CF(G)) :
    is_char chi -> K \subset G -> cfker ('Res[K] chi) \subset cfker chi.
Proof.
move=> ICC KsG; apply/subsetP=> g.
rewrite !cfker_charE ?cfRes_char // !inE.
by case: (boolP (_ \in K))=> // GiK; rewrite (subsetP KsG _ GiK) !cfResE.
Qed.

Section CentralDade.

Variable (A : {set gT}) (G H L K W W1 W2 : {group gT}).
 
Record centralDade_hypothesis : Prop :=  CentralDadeHypothesis {
  cDade_cTI_h    :> cyclicTIhypothesis G W W1 W2;
  cDade_cDa_h    :> cyclicDade_hypothesis L K W W1 W2;
  cDade_V        := cyclicTIset cDade_cTI_h;
  cDade_A0       := A :|: class_support cDade_V L;
  cDade_dAd_h    :> Dade_hypothesis G L cDade_A0;
  cDade_sigma    := cyclicTIsigma G W W1 W2;
  cDade_w        := (@cyclicTIirr _ W W1 W2);
  cDade_mu       := (@Dade_mu L W W1 W2);
  cDade_mu2 i j  := 'chi_(@Dade_mu2 L W W1 W2 i j);
  cDade_chi i    := 'chi_(@Dade_chi L K W W1 W2 i);
  cDade_delta i  := ((-1)^+ (@Dade_delta L W W1 W2 i) : algC);
  cDade_tau      := Dade cDade_dAd_h;
      _            : [/\  H <| L, (W2 \subset H /\ H \subset K), A <| L, 
                         \bigcup_(h \in H^#)('C_K[h]^#) \subset A  
                      &   A \subset K^#]
}.

Hypothesis CDH : centralDade_hypothesis.

Local Notation V := (cyclicTIset (cDade_cTI_h CDH)).

Local Notation A0 := (A :|: class_support V L).

Let OH := match CDH with
  CentralDadeHypothesis _ _ _ HH => HH end.

Let AnL : A <| L.
Proof. by case: OH. Qed.

Lemma cDade_DGA : Dade_hypothesis G L A.
Proof. 
exact: (restr_Dade_hyp CDH (subsetUl _ _) (normal_norm _)).
Qed.

Let HnL : H <| L.
Proof. by case: OH. Qed.

Let HsK : H \subset K.
Proof. by case: OH => _ []. Qed.

Let KsL : K \subset L.
Proof. 
case: (cDade_cDa_h CDH)=> [] [] /sdprodP [] _ <- *.
by apply: mulg_subl (group1 _).
Qed.

Let CupA: \bigcup_(h0 \in H^#) ('C_K[h0])^# \subset A.
Proof. by case: OH. Qed.

Let W2sH : W2 \subset H.
Proof. by case: OH => _ []. Qed.

Let HdP :  W1 \x W2 = W.
Proof. by case: CDH=> [[[]]]. Qed.

Let dW1 :  W1 != 1%g :> {set gT}.
Proof. by case: CDH=> [[]] p []. Qed.

Let dW2 :  W2 != 1%g :> {set gT}.
Proof. by case: CDH=> [[]] p []. Qed.

Local Notation sigma := (cyclicTIsigma G W W1 W2).
Local Notation w_ :=  (@cyclicTIirr _ W W1 W2).
Local Notation mu := (@Dade_mu L W W1 W2).
Local Notation mu2 i j := ('chi_(@Dade_mu2 L W W1 W2 i j)).
Local Notation chi i := ('chi_(@Dade_chi L K W W1 W2 i)).
Local Notation delta i := ((-1) ^+ (@Dade_delta L W W1 W2 i) : algC).
Local Notation tau := (Dade (cDade_dAd_h CDH)).

(* This is the first part of PeterFalvi (4.7). *) 
Lemma cDade_cfker_cfun_on i : 
   ~ H \subset cfker 'chi[K]_i  -> 'chi_i \in 'CF(K, A :|: 1%G).
Proof.
move=> HnsC; apply/cfun_onP=> g GniA.
case: (boolP (g \in K))=> [GiK|GniK]; last by rewrite cfun0.
apply:  (not_in_ker_char0 GiK (normalS _ _ HnL) HnsC)=> //.
suff: [group of 'C_H[g]] = 1%G by move/val_eqP=> /= /eqP.
apply/trivGP; apply/subsetP=> h /= HiC.
case: (boolP (h \in _))=> [Hi1|] //.
rewrite inE=> Hn1; case/negP: GniA; rewrite inE.
case: (boolP (_ \in 1%G)); first by rewrite orbT.
rewrite inE orbF=> Gn1.
apply: (subsetP CupA); apply/bigcupP; exists h.
  by move: HiC; rewrite !inE Hn1; case/andP.
rewrite 3!inE Gn1 GiK /=.
by move: HiC; rewrite inE cent1C; case/andP.
Qed.

(* This is the second part of PeterFalvi (4.7). *) 
Lemma cDade_cfker_cfun_on_ind i : 
   ~ H \subset cfker 'chi[K]_i -> 'Ind[L] 'chi_i \in 'CF(L, A :|: 1%G).
Proof.
move/cDade_cfker_cfun_on=> CiCF; apply/cfun_onP=> g GiG.
rewrite cfIndE // big1 ?mulr0 // => h HiL; move/cfun_onP: CiCF; apply.
apply: contra GiG; rewrite !inE; case/orP; last first.
  by rewrite -{1}(conj1g h); move/eqP=> /conjg_inj /eqP ->; rewrite orbT.
case/normalP: AnL => [] _ /(_ _ HiL) {1}<-.
by rewrite memJ_conjg => ->.
Qed.

Let cDade_chi_cher j : j != 0 ->  ~ H \subset cfker (chi j).
Proof.
move=> NZj HsC; case/eqP: NZj.
suff: w_ 0 j = 1.
  rewrite -(cTIirr00 CDH) !(cTIirrE CDH).
  by move/chi_inj=> /dprod_Iirr_inj [].
apply/cfunP=> g.
rewrite !cfun1E; case: (boolP (_ \in _))=> [|GnI]; last first.
  by rewrite cfun0.
case/dprodP: HdP=> _ {1}<- _ _; case/imset2P=> x y XiW1 YiW2->.
case/trivgPn: dW1=> x1 X1iW1 NOx1.
suff<-: w_ 0 j (x1 * y)%g = true%:R.
  rewrite !(cTIirrE CDH) dprod_IirrE !cfDprodE ?group1 // chi0_1.
  by rewrite !cfun1E XiW1 X1iW1.
have X1niW2 : x1 \notin W2.
  apply: contra NOx1=> X1iW2.
  have: x1 \in W1 :&: W2 by rewrite !inE X1iW1.
  by case/dprodP: HdP=> _ _ _ ->; rewrite inE.
have X1iWW2 : x1 \in W :\: W2.
  rewrite !inE X1niW2 -[x1]mulg1.
  by case/dprodP: HdP=> _ {1}<- _ _; rewrite mem_mulg.
have X1YiWW2 : (x1 * y)%g \in W :\: W2.
  rewrite !inE.
  case/dprodP: HdP=> _ {1}<- _ _.
  rewrite mem_mulg // andbT; apply: contra NOx1=> X1YiW2.
  have: x1 \in W1 :&: W2.
    by rewrite inE X1iW1 -(mulgK y x1) groupM // groupV.
  by case/dprodP: HdP=> _ _ _ ->; rewrite inE.
case: (Dade_mu2_restrict CDH)=> DMR _.
have: mu2 0 j (x1 * y)%g = mu2 0 j x1.
  apply: cfkerMr.
  apply: (subsetP (cfker_char_res (irr_char _) KsL)).
  rewrite -(Dade_chiE CDH).
  by apply: (subsetP HsC); apply: (subsetP W2sH).
rewrite (DMR 0 j _ X1YiWW2) (DMR 0 j _ X1iWW2) !cfunE.
move/(mulfI _)->.
rewrite -[x1]mulg1 (cTIirrE CDH) !dprod_IirrE !cfDprodE //.
  rewrite chi0_1 cfun1E X1iW1 mul1r.
  by rewrite  !(lin_char1 (cTIirr_linearW2 CDH _)).
by rewrite (signr_eq0 algC _).
Qed.

(* Third part of PeterFalvi (4.7). *)
Lemma cDade_chi_support j : j != 0 -> chi j \in 'CF(K, A :|: 1%G).
Proof. by move/cDade_chi_cher; exact: cDade_cfker_cfun_on. Qed.

(* Last part of PeterFalvi (4.7). *)
Lemma cDade_mu_support j : j != 0 -> mu j \in 'CF(L, A :|: 1%G).
Proof. 
by rewrite -(Dade_Ind_chi CDH)=> /cDade_chi_cher /cDade_cfker_cfun_on_ind.
Qed.

Let odd_neq2 m : odd m -> (2 == m)%N = false. Proof. by case: eqP => // <-. Qed.

Let oddW : odd #|W|. Proof. by have [[]] := (cyclicTI_Dade CDH). Qed.

Let W1sW : W1 \subset W. Proof. by have [_ /mulG_sub[]] := dprodP HdP. Qed.

Let W2sW : W2 \subset W. Proof. by have [_ /mulG_sub[]] := dprodP HdP. Qed.

Let oddW1 : odd #|W1|. Proof. exact: oddSg oddW. Qed.

Let oddW2 : odd #|W2|. Proof. exact: oddSg oddW. Qed.

Let tLW1 : (2 < #|W1|)%N.
Proof. rewrite ltn_neqAle cardG_gt1 odd_neq2 //. Qed.

Let tLW2 : (2 < #|W2|)%N.
Proof. rewrite ltn_neqAle cardG_gt1 odd_neq2 //. Qed.

(* Second part of PeterFalvi (4.8). *)
Lemma cDade_mu2_delta i j k : 
  mu2 i j 1%g = mu2 i k 1%g -> delta j = delta k.
Proof.
case: (Dade_mu2_mod CDH i j)=> a [Ia -> /=].
case: (Dade_mu2_mod CDH i k)=> b [Ib -> /=].
wlog Hn : j k a b Ia Ib / a <= b=> [WL|].
  have: isIntC (a - b) by apply: isIntC_sub.
  case/isIntCP=> [[]] [n]; 
       rewrite ?(expr0, expr1, mul1r, mulr1, mulN1r)=> Hn Hd.
    by rewrite (WL j k _ _ Ia Ib) // -leC_sub -[_ - _]opprK opprB Hn 
               opprK posC_nat.
  by rewrite (WL k j _ _ Ib Ia) // -leC_sub Hn posC_nat.
case: (boolP (a == b))=> [/eqP->|Dab HH]; first by move/addIr.
have Pw1: 0 < #|W1|%:R by rewrite -(ltn_ltC 0) cardG_gt0.
have: delta j - delta k < (b - a) *+ #|W1|.
  suff: delta j - delta k < #|W1|%:R.
    move/ltC_leC_trans; apply.
    rewrite -mulr_natr -[X in _ <= X]mulr_natr leC_mul2r ?posC_nat //.
    have<-: `|b - a| = b - a.
      suff: isNatC (b - a) by case/isNatCP=> m ->; exact: normC_nat.
      by rewrite -isIntC_pos ?isIntC_sub // leC_sub.
    by apply: isIntC_normC_ge1; rewrite ?isIntC_sub // subr_eq0 eq_sym.
  do 2 case: (Dade_delta _ _);rewrite ?(expr0, expr1, subrr) //.
    apply: leC_ltC_trans Pw1.
    by rewrite -leC_sub opprB opprK add0r -(natrD _ 1 1) -(leq_leC 0).
  by rewrite opprK -(natrD _ 1 1) -ltn_ltC add1n.
  rewrite -(ltC_add2l (a *+ #|W1|)) !addrA [X in X - _ < _]addrC HH.
by rewrite [X in X - _ < _]addrC addrK mulrnBl addrC subrK /ltC eqxx.
Qed.

Let SdP : K ><| W1 = L. Proof. by case: (cDade_cDa_h CDH)=> [[]]. Qed.

Let Hcoprime : coprime #|W1| #|K|.
Proof.
case: (cDade_cDa_h CDH)=> [[_ _ H_Hall _] [_ WsK _ _] _].
by rewrite coprime_sym (coprime_sdprod_Hall SdP) (sdprod_Hall SdP).
Qed.

(* First part of PeterFalvi (4.8). *)
Lemma cDade_mu2_on i j k : j != 0 -> k != 0 -> mu2 i j 1%g = mu2 i k 1%g ->
      mu2 i j - mu2 i k \in 'CF(L, A0). 
Proof.
move=> NZj NZk Emu1.
have HF g : g \in W1^# -> mu2 i j g - mu2 i k g = 0.
  rewrite !inE=> /andP [Dg1 GiW1].
  have GiWmW2: g \in W :\: W2.
    rewrite inE (subsetP W1sW) // andbT; apply: contra Dg1=> GiW2.
    have: g \in W1 :&: W2 by rewrite inE GiW1.
    by case/dprodP: HdP=> _ _  _ ->; rewrite inE.
  case: (Dade_mu2_restrict CDH)=> HH _.
  rewrite !HH // (cDade_mu2_delta Emu1) !cfunE -mulrBr -[g]mulg1.
  rewrite !(cTIirrE CDH) !dprod_IirrE !cfDprodE //.
  by rewrite !(lin_char1 (cTIirr_linearW2 CDH _)) subrr mulr0.
apply/cfun_onP=> g; rewrite !inE negb_or !cfunE.
case/andP=> GniA GniCL.
case: (boolP (g \in L))=> [GiL | GniL]; last by rewrite !cfun0 // subrr.
case: (boolP (g \in 1%G))=> [| Dg1].
  by rewrite inE => /eqP->; rewrite Emu1 subrr.
case: (boolP (g \in W1))=> [GiW1 | GniW1].
  by apply: HF; first by move: Dg1; rewrite !inE => ->.
case: (boolP (g \in K))=> [GiK|GniK]; last first.
  move: GiL GniK GniW1 GniCL.
  case/(mem_sdprod SdP)=> k1 [x1 [K1iK X1iW1] -> _] K1X1niK.
  have: x1 \in W1^#.
    by rewrite !inE X1iW1 andbT; apply: contra K1X1niK=> /eqP->; rewrite mulg1.
  case: (cDade_cDa_h CDH)=> [] _ [_ _ _ HH _] /HH=> EW2.
  have CKx: coprime #|K| #[x1].
    move: X1iW1; rewrite -cycle_subG=> /cardSg /coprime_dvdr; apply.
    by rewrite coprime_sym.
  have X1iNK: x1 \in 'N(K) by case/sdprodP: SdP=> _ _ /subsetP ->.
  have: (k1 * x1)%g \in K :* x1.
    by apply/imset2P; exists k1 x1; rewrite ?inE //.
  case: (partition_cent_rcoset X1iNK CKx)=> /cover_partition<- _.
  rewrite cover_imset => /bigcupP [k2 K2iK] /imsetP [w /imset2P [x2 x]].
  rewrite EW2 inE=> X2iW2 /eqP-> -> -> X2X1CniW1.
  have X2X1iW : (x2 * x1)%g \in W.
    by apply: groupM; [rewrite (subsetP W2sW) | rewrite (subsetP W1sW)].
  case: (boolP ((x2 * x1)%g \in W1))=> [X2X1iW1 _ |X2X1niW1 /negP []].
    rewrite !cfunJ ?(subsetP KsL) // HF // !inE X2X1iW1 andbT.
    by apply: contra X2X1CniW1=> /eqP->; rewrite conj1g group1.
  apply: mem_class_support; last by apply: (subsetP KsL).
  rewrite !inE negb_or -andbA; apply/and3P; split=> //.
  apply: contra K1X1niK=> X1XiW2.
  have: x1 \in W1 :&: W2 by rewrite inE X1iW1 -(groupMl _ X2iW2).
  by case/dprodP: HdP=> _ _ _  ->; rewrite inE => /eqP->; rewrite mulg1. 
have GniA1 : g \notin A :|: 1%G by rewrite inE negb_or GniA.
move/cfun_onP: (cDade_chi_support NZj)=> /(_ _ GniA1).
rewrite (Dade_chiE CDH i) cfResE // => ->.
move/cfun_onP: (cDade_chi_support NZk)=> /(_ _ GniA1).
rewrite (Dade_chiE CDH i) cfResE // => ->.
by rewrite subrr.
Qed.

Local Notation NC := (cyclicTI_NC W W1 W2).

(* This is last part of PeterFalvi (4.8). *)
Lemma cDade_mu2_tau i j k : j != 0 -> k != 0 -> mu2 i j 1%g = mu2 i k 1%g -> 
   tau (mu2 i j - mu2 i k) =  delta j *: (sigma (w_ i j) - sigma (w_ i k)).
Proof.
move=> NZj NZk Emu1; have cTI_h := cDade_cTI_h CDH.
case: (boolP (j == k))=> [/eqP<-| Djk].
  by rewrite !subrr scaler0 linear0.
apply/eqP; rewrite -subr_eq0; apply/eqP; set phi := _ + _.
have Zphi: {in V, forall x, phi x = 0}=> [g GiV|].
  rewrite !cfunE Dade_id; last first.
    by rewrite inE -[g]conjg1 mem_class_support // orbT.
  rewrite !cfunE.
  have GiWW2: g \in W :\: W2.
    by move: GiV; rewrite !inE negb_or -andbA; case/andP.
  case: (Dade_mu2_restrict CDH)=> HH _; rewrite !HH //.
  rewrite !(cyclicTIsigma_restrict _ GiV) // !cfunE (cDade_mu2_delta Emu1).
  by rewrite -mulrBr subrr.
have Cmu: mu2 i j - mu2 i k \in 'CF(L, A0).
  by rewrite cDade_mu2_on // andbT sub_vchar // irr_vchar.
have Zmu: tau (mu2 i j - mu2 i k) \in 'Z[irr G, G^#].
  case: (Dade_Zisometry CDH)=> _ -> //.
  by rewrite vchar_split sub_vchar ?irr_vchar.
have /(vchar_norm2 Zmu) [/= i1 [i2 Di1i2] Etau]: 
             '[tau (mu2 i j - mu2 i k)] = 2%:R.
  rewrite (Dade_isometry CDH) // cfdot_subl !cfdot_subr !cfdot_irr.
  rewrite !eqxx eq_sym; case: (_ =P _); last first.
    by rewrite opprB !subr0 -natrD.
  by case/(Dade_mu2_inj CDH)=> Ejk; case/eqP: Djk.
move: Zphi; rewrite /phi {phi}Etau; move: (Dade_delta _ _ _ _)=> d.
wlog : d j k NZj NZk {Cmu Zmu Emu1}Djk /  d = false=> [WL|->].
  case: d; last by apply: WL.
  rewrite -[true]negbK signC_negb scaleNr -scalerN opprB.
  by apply: WL; rewrite // eq_sym.
rewrite scale1r opprB addrA.
pose cB k := forallb ij,  '['chi_k, sigma (w_ ij.1 ij.2)] == 0.
pose dB1 x := (subrr, sub0r, subr0, oppr0, subrK,
                add0r, addr0, addrK, opprK, (I, opprD),
             (I, natrD algC 1%N), (I, natrD algC x 1%N),
             (I, natrD algC 1%N 1%N), (I, natrD),
             oppr_eq0, (I, eqN_eqC 1 0), (I,  eqN_eqC x 0)).
pose dB2 :=  (eqr_opp, eqr_oppLR, opprK, (sigma_opp_neq CDH)).
wlog : i1 i2  j k Di1i2 NZj NZk Djk / 
 '['chi_i1 - 'chi_i2 + sigma (w_ i k) - sigma (w_ i j), sigma (w_ i j)] != 0.
  set phi := _ - _ => WL Zphi.
  case: (boolP ('[phi, sigma (w_ i j)] == 0))=> [Zij|NZij]; last by apply: WL.
  case: (boolP ('[phi, sigma (w_ i k)] == 0))=> [Zik|NZik]; last first.
    apply/eqP; rewrite /phi -addrA -oppr_eq0 opprD !opprB addrA; apply/eqP.
    apply: WL=> //; try by rewrite eq_sym.
      by rewrite -addrA -oppr_eq0 -cfdotNl opprD !opprB addrA.
    move=> v ViV; rewrite /= !cfunE.
    apply/eqP; rewrite /phi -addrA -oppr_eq0 opprD !opprB addrA; apply/eqP.
    by move: (Zphi _ ViV); rewrite !cfunE.
  move: Zij Zik.
  have DD0 : sigma (w_ i j) != sigma (w_ i k).
    by rewrite (sigma_eqE CDH) eqxx (negPf Djk).
  rewrite !(cfdotDl, cfdot_subl, cfdot_sigma CDH, cfdotNl) !eqxx [k == j]eq_sym.
  rewrite (negPf Djk) addr0 !cfdot_dirr ?(dirr_chi, dirr_sigma CDH) // /phi.
  case: ('chi_i1 =P _)=> [->|DD1].
    rewrite !dB2 (negPf DD0) !dB1.
    case: ('chi_i2 == _); first by rewrite !dB1.
    by case: ('chi_i2 == _); rewrite !dB1.
  case: ('chi_i1 =P _)=> [->|DD2].
    rewrite !dB2 (negPf DD0) /=.
    case: ('chi_i2 =P _)=> [->|DD3]; first by rewrite !dB1.
    case: ('chi_i2 =P _)=> [->|DD4]; first by rewrite !dB1.
    case: ('chi_i2 =P _)=> [->|DD5]; first by rewrite !dB1.
    by case: ('chi_i2 =P _)=> [->|DD6]; rewrite !dB1.
  case: ('chi_i2 =P _)=> [->|DD3].
    rewrite !dB2 (negPf DD0) /=.
    case: ('chi_i1 =P _)=> [-> _|DD4].
      by rewrite [- sigma _ + _]addrC subrK !subrr.
    by case: ('chi_i1 =P _)=> [->|DD5]; rewrite !dB1.
  by case: ('chi_i2 =P _)=> [->|DD4]; rewrite !dB1.
have Dchi : 'chi_i1 <> 'chi_i2.
  by move/chi_inj=> /eqP; rewrite eq_sym (negPf Di1i2).
have Dochi : 'chi_i1 <> - 'chi_i2.
  move=> HH; suff: 0 < 'chi_i1 1%g + 'chi_i2 1%g.
    by rewrite HH !cfunE addNr /ltC eqxx.
  by rewrite sposC_addl // ?ltCW // ltC_irr1.
set phi := _ + _ => NZphi Vphi.
have: (NC phi < 2 * minn #|W1| #|W2|)%N.
  suff:  (NC phi <= 2 * 2)%N.
    move/leq_ltn_trans; apply.
    by rewrite ltn_mul2l /= leq_min // tLW1.
  apply: leq_trans (cyclicTI_NC_sub _ _ _ _ _) _.
  have->: (2 * 2 = 1 + 1 + 1 + 1)%N by [].
  apply: leq_add; last by rewrite (cyclicTI_NC_sigma CDH).
  apply: leq_trans (cyclicTI_NC_add _ _ _ _ _) _.
  apply: leq_add; last by rewrite (cyclicTI_NC_sigma CDH).
  apply: leq_trans (cyclicTI_NC_sub _ _ _ _ _) _.
  by apply: leq_add; apply: (cyclicTI_NC_irr CDH).
have DD0 : sigma (w_ i j) != sigma (w_ i k).
  by rewrite (sigma_eqE CDH) eqxx (negPf Djk).
  (* Now we go brute force! *)
move/(cyclicTI_NC_split Vphi)=> /(_ _ _ NZphi) []; last first.
  move/(_ i k); rewrite eqxx mul1r -!/(w_ _ _).
  have->: cyclicTIsigma G W W1 W2 = sigma by done.
  move/eqP => HH.
  move: NZphi HH Dochi; rewrite /phi !(cfdotDl, cfdot_subl, cfdotNl).
  rewrite !(cfdot_sigma CDH) !eqxx [k == j]eq_sym (negPf Djk) subr0 !addr0.
  rewrite !cfdot_dirr ?(dirr_chi, dirr_sigma CDH) //.
  case: ('chi_i1 =P _)=> [->|DD1].
    rewrite !dB2 (negPf DD0) /=.
    case: ('chi_i2 =P _)=> [-> _|DD2].
      by rewrite !dB2 (negPf DD0) /= !dB1 -subr_eq0 !dB1.
    rewrite !dB1.
    case: ('chi_i2 =P _)=> [-> //|DD3 _].
    case: ('chi_i2 =P _)=> [->|DD4]; first by rewrite !dB1 -subr_eq0 !dB1.
    case: ('chi_i2 =P _)=> [->|DD5]; rewrite -subr_eq0 !dB1 //.
    by rewrite addNr !dB1.
  case: ('chi_i1 =P _)=> [->|DD2].
    rewrite !dB2 (negPf DD0) /= !dB1.
    case: ('chi_i2 =P _)=> [-> //|DD2]; first by rewrite !dB1.
    case: ('chi_i2 =P _)=> [-> _|DD3 ]; last by rewrite !dB1 eqxx.
    by rewrite !dB2 (negPf DD0) /= !dB1 -subr_eq0 !dB1.
  case: ('chi_i1 =P _)=> [-> _|DD3].
    case: ('chi_i2 =P _)=> [->|DD3]; rewrite !dB1.
      rewrite !dB2 [sigma _ == _]eq_sym (negPf DD0) /=.
      by rewrite  addNr -subr_eq0 !dB1.
    case: ('chi_i2 =P _)=> [->//|DD4].
    case: ('chi_i2 =P _)=> [-> _|DD5]; first by rewrite opprB !dB1.
    by case: ('chi_i2 =P _)=> [->|DD6]; rewrite addNr eq_sym !dB1.
  case: ('chi_i2 =P _)=> [->|DD4 _]; rewrite !dB1 ?addrN ?eqxx //.
  case: ('chi_i1 =P _)=> [->|DD5].
    case: ('chi_i2 =P _)=> [->|DD5].
      by rewrite !dB2 !dB1 -subr_eq0 !dB1.
    case: ('chi_i2 =P _)=> [->|DD6].
      rewrite [sigma _ == _]eq_sym (negPf DD0) /= !dB1.
      by rewrite -subr_eq0 !dB1.
    by case: ('chi_i2 =P _)=> [->|DD7]; rewrite !dB1 -subr_eq0 !dB1.
  case: ('chi_i2 =P _)=> [->|DD6].
    by rewrite !dB2 !dB1 -subr_eq0 !dB1.
  case: ('chi_i2 =P _)=> [->|DD7].
    rewrite [sigma _ == _]eq_sym (negPf DD0) /=.
    by rewrite !dB1 -subr_eq0 !dB1.
  by case: ('chi_i2 =P _)=> [->|DD8]; rewrite !dB1 -subr_eq0 !dB1.
move=> HH.
have: exists i3, exists i4, [/\ i3 != i, i4 != i & i3 != i4].
  have NN1: (2 < Nirr W1)%N.
    rewrite NirrE.
    have CW1: cyclic W1 by case: CDH=> cc1 [[]].
    by have:= cyclic_abelian CW1; rewrite card_classes_abelian => /eqP ->.
  have NN2: (1 < Nirr W1)%N by apply: leq_trans NN1.
  pose i3 : Iirr W1 := inZp 1; pose i4 : Iirr W1 := inZp 2.
  have NZi1 : i3 != 0.
    by apply/eqP; move/val_eqP=> /=; rewrite modn_small.
  have NZi2 : i4 != 0.
    by apply/eqP; move/val_eqP=> /=; rewrite modn_small.
  have Di3i4 : i3 != i4.
    by apply/eqP; move/val_eqP=> /=; rewrite !modn_small.
  case: (boolP (i == 0))=> [Zi0|NZi0].
    by exists i3; exists i4; rewrite (eqP Zi0) NZi1 NZi2.
  case: (boolP (i == i3))=> [Zi3|NZi3].
    exists 0; exists i4.
    by rewrite (eqP Zi3) eq_sym NZi1 eq_sym Di3i4 eq_sym.
  exists 0; exists i3.
  by rewrite eq_sym NZi0 eq_sym NZi3 eq_sym.
case=> i3 [i4 [Di3i Di4i Di3i4]].
have DD1: sigma (w_ i j) != sigma (w_ i3 j).
  by rewrite (sigma_eqE CDH) eqxx eq_sym (negPf Di3i).
have DD2: sigma (w_ i j) != sigma (w_ i4 j).
  by rewrite (sigma_eqE CDH) eqxx eq_sym (negPf Di4i).
have DD3: sigma (w_ i k) != sigma (w_ i3 j).
  by rewrite (sigma_eqE CDH) [k == _]eq_sym (negPf Djk) andbF.
have DD4: sigma (w_ i k) != sigma (w_ i4 j).
  by rewrite (sigma_eqE CDH) [k == _]eq_sym (negPf Djk) andbF.
have DD5: sigma (w_ i3 j) != sigma (w_ i4 j).
  by rewrite (sigma_eqE CDH) eqxx (negPf Di3i4).
have HH1: '[phi, sigma (w_ i3 j)] == '[phi, sigma (w_ i j)].
  by rewrite HH eqxx mul1r.
have HH2: '[phi, sigma (w_ i4 j)] == '[phi, sigma (w_ i j)].
  by rewrite HH eqxx mul1r.
have HH3: '[phi, sigma (w_ i j)] != 0.
  by rewrite HH eqxx mul1r.
have HH4:  '[phi, sigma (w_ i k)] == 0.
  by rewrite HH (negPf Djk) mul0r.
move: HH1 HH2 HH3 HH4 Dchi Dochi.
rewrite /phi !(cfdotDl, cfdot_subl, cfdotNl).
rewrite !(cfdot_sigma_eq CDH).
rewrite (negPf DD1) (negPf DD2) (negPf DD3) (negPf DD4).
rewrite !eqxx [sigma _ == _]eq_sym !(negPf DD0) !dB1.
rewrite !cfdot_dirr ?(dirr_chi, dirr_sigma CDH) //.
case: ('chi_i1 =P _)=> [->|DD6].
  rewrite !dB2 (negPf DD5) [sigma _ == _]eq_sym (negPf DD1) !dB1.
  rewrite [sigma _ == _]eq_sym (negPf DD3) !dB1.
  case: ('chi_i2 =P _)=> [->//|DD6].
  case: ('chi_i2 =P _)=> [->|DD7].
    by rewrite (negPf DD5) !dB2 -subr_eq0 !dB1.
  case: ('chi_i2 =P _)=> [->|DD8].
    by rewrite eqr_opp eq_sym -subr_eq0 !dB1.
  case: ('chi_i2 =P _)=> [->|DD9].
    by rewrite eqr_opp eq_sym -subr_eq0 !dB1.
  rewrite !dB1=> _; rewrite -subr_eq0 !dB1.
  case: ('chi_i2 =P _)=> [->|DD10]; first by rewrite !dB1.
  case: ('chi_i2 =P _)=> [-> _ _|DD11].
    by rewrite !dB2 [sigma _ == _]eq_sym (negPf DD4) !dB1.
  by rewrite !dB1.
case: ('chi_i1 =P _)=> [->|DD7].
  rewrite !dB2 (negPf DD5) !dB1.
  rewrite [sigma _ == _]eq_sym (negPf DD1) !dB1.
  rewrite [sigma _ == _]eq_sym (negPf DD3) !dB1.
  case: ('chi_i2 =P _)=> [->|DD7].
    by rewrite !dB2 (negPf DD5) !dB1.
  case: ('chi_i2 =P _)=> [-> _|DD8].
    by rewrite !dB2 (negPf DD5) [sigma _ == _]eq_sym (negPf DD1) eq_sym !dB1.
  case: ('chi_i2 =P _)=> [->|DD9].
    by rewrite !dB2 (negPf DD0) !dB1.
  by case: ('chi_i2 =P _)=> [->|DD10]; rewrite -[_ - _ == _]subr_eq0 !dB1.
case: ('chi_i2 =P _)=> [->|DD8]; rewrite !dB1.
  rewrite !dB2 (negPf DD5) !dB1.
  rewrite [sigma _ == _]eq_sym (negPf DD1) !dB1.
  rewrite [sigma _ == _]eq_sym (negPf DD3) !dB1.
  case: ('chi_i1 =P _)=> [->|DD9].
    by rewrite -[1 == _]subr_eq0 !dB1.
  case: ('chi_i1 =P _)=> [->|DD10]; first by rewrite !dB1.
  by rewrite -[1 == _]subr_eq0 !dB1.
case: ('chi_i2 =P _)=> [->|DD9].
  rewrite !dB2 (negPf DD5) !dB1.
  rewrite [sigma _ == _]eq_sym (negPf DD1) !dB1.
  rewrite [sigma _ == _]eq_sym (negPf DD3) !dB1.
  case: ('chi_i1 =P _)=> [->|DD9].
    by rewrite !dB1 eq_sym -subr_eq0 !dB1.
  case: ('chi_i1 =P _)=> [->|DD10]; first by rewrite !dB1.
  case: ('chi_i1 =P _)=> [-> _ _ _|DD11].
    by rewrite !dB2 [sigma _ == _]eq_sym (negPf DD4) !dB1.
  by case: ('chi_i1 =P _)=> [->_ |DD12 _]; rewrite -subr_eq0 !dB1.
case: ('chi_i1 =P _)=> [->|DD10].
  rewrite !dB2 (negPf DD0) !dB1.
  case: ('chi_i2 =P _)=> [->|DD10]; first by rewrite eq_sym !dB1.
  by case: ('chi_i2 =P _)=> [->|DD11]; rewrite eq_sym !dB1.
case: ('chi_i1 =P _)=> [->|DD11].
  rewrite !dB2 (negPf DD0) !dB1.
  case: ('chi_i2 =P _)=> [->|DD11]; first by rewrite !dB1.
  by case: ('chi_i2 =P _)=> [->|DD12]; rewrite !dB1.
case: ('chi_i2 =P _)=> [->|DD12]; first by rewrite !dB1.
by case: ('chi_i2 =P _)=> [->|DD13]; rewrite eq_sym !dB1.
Qed.

Let tiW : cyclicTIhypothesis G W W1 W2 := CDH.
Let PtypeL : cyclicDade_hypothesis L K W W1 W2 := CDH.

Lemma Ptype_TIset_disjoint : cyclicTIset tiW \subset ~: K.
Proof.
have [[/sdprodP[_ _ _ tiKW1] _ _ _] [_ sW2K _ _] _] := PtypeL.
have defW: W1 \x W2 = W := cyclicTIhyp_W1xW2 tiW.
rewrite subDset setUC -subDset setDE setCK setIC.
by rewrite -(dprod_modr defW sW2K) tiKW1 dprod1g subsetUr.
Qed.

Lemma conjC_Irr0 (G1 : {group gT}): conjC_Iirr 0 = 0 :> Iirr G1.
Proof. by apply: chi_inj; rewrite conjC_IirrE chi0_1 cfConjC1. Qed. 

Lemma isRealC0 : isRealC 0.
Proof. by rewrite /isRealC conjC0. Qed.

Lemma isRealC1 : isRealC 1.
Proof. by rewrite /isRealC conjC1. Qed.

Lemma isRealC_add x y : isRealC x -> isRealC y -> isRealC (x + y).
Proof. by move=> Rx Ry; rewrite /isRealC rmorphD (eqP Rx) (eqP Ry). Qed.

Lemma isRealC_sub x y : isRealC x -> isRealC y -> isRealC (x - y).
Proof. by move=> Rx Ry; rewrite /isRealC rmorphB (eqP Rx) (eqP Ry). Qed.

Lemma isRealC_mul x y : isRealC x -> isRealC y -> isRealC (x * y).
Proof. by move=> Rx Ry; rewrite /isRealC rmorphM (eqP Rx) (eqP Ry). Qed.

Lemma isRealC_exp x n : isRealC x -> isRealC (x ^+ n).
Proof. 
move=> Rx; elim: n=> [| n IH]; first by rewrite expr0 isRealC1.
by rewrite exprS isRealC_mul.
Qed.

Lemma posC_real_exp_even x n : isRealC x -> ~~ odd n -> 0 <= x ^+ n.
Proof.
move=> /realC_leP [Hle0 | Hgt0] Oddn; last by apply: posC_exp.
rewrite -[x]opprK exprNn -signr_odd (negPf Oddn) mul1r.
by apply: posC_exp; rewrite posC_opp.
Qed.

Lemma posC_real_exp_odd x n : isRealC x -> odd n -> (0 <= x) = (0 <= x ^+ n).
Proof.
move=> Rx Oddn; case/realC_leP: (Rx) => [Hle0 | Hge0]; last first.
  by rewrite Hge0; apply: sym_equal; apply/idP; apply: posC_exp.
move: Hle0; rewrite leC_eqVlt; case/orP=> [/eqP-> | Hlt0].
  by rewrite leC_refl; case: n Oddn=> // n _; rewrite exprS mul0r leC_refl.
have: 0 < (- x)^+ n by apply: sposC_exp; rewrite sposC_opp.
rewrite exprNn -signr_odd Oddn mulN1r sposC_opp => Hxlt0.
by rewrite !realC_leNgt ?(isRealC0, isRealC_exp) // Hlt0 Hxlt0.
Qed.

Lemma odd_cyclic_conjC_Iirr_diff (G1 : {group gT}) i :
  odd #|G1| -> cyclic G1 ->  i != 0 -> conjC_Iirr i != i :> Iirr G1.
Proof.
move=> OddG CyclG; apply: contra=> conjC.
rewrite -irr_eq1; apply/eqP; apply/cfunP=> g /=.
case: (boolP (g \in G1))=> [GiG | GniG]; last by rewrite !cfun0.
rewrite cfun1Egen genGid GiG.
have Lchi: lin_char 'chi_i 
  by apply/char_abelianP; apply: cyclic_abelian.
have F1: 'chi_i (g ^+ #|G1|)%g = 1.
  suff->: (g ^+ #|G1|)%g = 1%g by case/andP: Lchi=>  _ /eqP.
  by apply/eqP; rewrite -order_dvdn (order_dvdG GiG).
have F2: (0 <= 'chi_i g).
  rewrite (posC_real_exp_odd _ OddG) //.
    by rewrite -lin_charX // F1 posC1.
  by rewrite /isRealC -cfConjCE -conjC_IirrE (eqP conjC).
move: F1; rewrite lin_charX // => /eqP.
have->: #|G1| = #|G1|.-1.+1 by case: #|_| OddG.
by rewrite posC_unit_exp //; apply/eqP.
Qed.

Lemma cfun_scal_conj (G1 : {group gT}) a (f : 'CF(G1)) :
   ((a *: f)^*)%CF = (a^*) *: (f^*)%CF.
Proof. by apply/cfunP=> g; rewrite !cfunE rmorphM. Qed.

Lemma Dade_mu_nreal i : i != 0 -> ~~ cfReal (mu i).
Proof.
move=> NZi; rewrite /cfReal -(Dade_mu_aut PtypeL).
apply/eqP=> /(Dade_mu_inj PtypeL) HH.
have CW2: cyclic W2 by case: PtypeL=> _ [].
by case/eqP: (odd_cyclic_conjC_Iirr_diff oddW2 CW2 NZi).
Qed.

Section OrthoIso.

Variables (G1 M : {group gT}) (S : seq 'CF(G1)) (nu : {linear 'CF(G1) -> 'CF(M)}).
Hypotheses (pogS : pairwise_orthogonal S).

Lemma isometry_on_ortho_base : 
  (forall s1 s2, s1 \in S -> s2 \in S -> '[nu s1, nu s2] = '[s1, s2]) ->
  {in 'Z[S] &, isometry nu}.
Proof.
move=> Hn u v.
case/vchar_expansion=> s1 Hs1 ->.
case/vchar_expansion=> s2 Hs2 ->.
rewrite !linear_sum !cfdot_suml big_seq_cond [X in _ = X]big_seq_cond.
apply: eq_bigr=> i; rewrite andbT => IiS.
rewrite !cfdot_sumr big_seq_cond [X in _ = X]big_seq_cond.
apply: eq_bigr=> j; rewrite andbT => JiS.
by rewrite !linearZ !cfdotZl !cfdotZr Hn.
Qed. 

End OrthoIso.

Let CW : cyclic W.
Proof. by case: tiW=> [[]]. Qed.

Let CW1 : cyclic W1.
Proof. by exact: cyclicS CW. Qed.

Let classesW1 : #|classes W1| = #|W1|.
Proof.
by have:= cyclic_abelian CW1; rewrite card_classes_abelian => /eqP ->.
Qed.

Lemma Dade_mu1_spos i : 0 < mu i 1%g.
Proof.
rewrite /Dade_mu (bigD1 (0 : Iirr W1)) //= cfunE.
rewrite sposC_addr ?ltC_irr1 // sum_cfunE.
by apply: posC_sum=> i1 _; apply: ltCW (ltC_irr1 _).
Qed.

Lemma Dade_mu1_neq0 i : mu i 1%g != 0.
Proof. 
apply/eqP=> HH; move: (Dade_mu1_spos i).
by rewrite HH /ltC eqxx.
Qed.

Definition uniform_Dade_mu_seq k :=
  image mu [pred j | (mu j 1%g == mu k 1%g) && (j != 0)].

(* This is Peterfalvi (4.9).                                                  *)
(* We have added the "obvious" fact that calT is pairwise orthogonal, since   *)
(* we require this to prove membership in 'Z[calT], we encapsulate the        *)
(* construction of tau1, and state its conformance to tau on the "larger"     *)
(* domain 'Z[calT, L^#], so that clients can avoid using the domain equation  *)
(* in part (a).                                                               *)
Theorem uniform_Dade_mu_coherent k (calT := uniform_Dade_mu_seq k) :
    k != 0 ->
  (*a*) [/\ pairwise_orthogonal calT, ~~ has cfReal calT, conjC_closed calT,
            'Z[calT, L^#] =i 'Z[calT, A]
          & exists2 psi, psi != 0 & psi \in 'Z[calT, A]]
  (*b*) /\ (exists2 tau1 : {linear 'CF(L) -> 'CF(G)},
           forall j, tau1 (mu j) = delta k *: (\sum_i sigma (w_ i j))
         & {in 'Z[calT], isometry tau1, to 'Z[irr G]}
        /\ {in 'Z[calT, L^#], tau1 =1 tau}).
Proof. 
move=> NZk.
have Pog : pairwise_orthogonal calT.
 apply/pairwise_orthogonalP; split=> [|x y].
    rewrite cons_uniq; apply/andP; split.
      apply/negP; case/imageP=> i.
      rewrite inE => /andP [_ NZi] HH.
      by case/negP: (Dade_mu_neq0 PtypeL i); rewrite -HH.
    by rewrite map_inj_uniq ?enum_uniq //; exact: (Dade_mu_inj PtypeL).
  case/imageP=> i1; rewrite inE => _ ->.
  case/imageP=> j1; rewrite inE => _ -> HH.
  rewrite (cfdot_mu PtypeL)=> //.
  by case: eqP=> // HH1; case/eqP: HH; rewrite HH1.
have NReal: ~~ has cfReal calT.
  apply/hasPn=> i /imageP [j /andP [_ NZj] ->].
  by exact: Dade_mu_nreal.
have ConjC: conjC_closed calT.
  move=> i /imageP [j /andP [Mui1 NZj] ->].
  apply/imageP; exists (conjC_Iirr j); last first.
    by rewrite -(Dade_mu_aut PtypeL).
  apply/andP; split.
    rewrite (Dade_mu_aut PtypeL) cfunE (eqP Mui1).
    apply: isIntC_Real; apply: isIntC_Nat.
    rewrite sum_cfunE; apply: isNatC_sum => i1 _.
    by apply: isNatC_irr1.
  apply: contra NZj=> /eqP HH.
  by rewrite -[j]conjC_IirrK HH conjC_Iirr0.
have Equiv: 'Z[calT, L^#] =i 'Z[calT, A].
  move=> f; rewrite vcharD1E; apply/idP/idP; last first.
    rewrite (vchar_split _ A)=> /andP [-> FiA] /=.
    apply/eqP; apply: (cfun_onP FiA).
    case: OH=> _ _ _ _ /subsetP=> /(_ 1%g).
    by move/contra; apply; rewrite !inE eqxx.
  case/andP=> Zf Vf1.
  have: f \in 'Z[calT, A :|: 1%G].
    rewrite vchar_split Zf /=.
    case: (vchar_expansion Zf)=> u Hu ->.
    rewrite big_map big_filter.
    apply: memv_suml=> i /andP [_ NZi].
    by apply: memvZl; apply: cDade_mu_support.
  rewrite vchar_split cfun_onE=> /andP [_ Sf].
  rewrite vchar_split Zf /= cfun_onE.
  apply/subsetP=> g GniF.
  move/subsetP: Sf => /(_ _ GniF).
  rewrite !inE => /orP [] // /eqP Ge1.
  by case/negP: GniF; rewrite Ge1.
have NEmpty: exists2 psi, psi != 0 & psi \in 'Z[calT, A].
  have FF : mu k \in calT.
    by apply/imageP; exists k; rewrite // inE eqxx.
  exists (mu (conjC_Iirr k) - mu k).
    rewrite subr_eq0.
    by move/hasPn: NReal => /(_ _ FF); rewrite (Dade_mu_aut PtypeL).
  rewrite -Equiv vcharD1E; apply/andP; split.
    apply: sub_vchar; apply: mem_vchar=> //; try by apply: orthogonal_free.
    by rewrite (Dade_mu_aut PtypeL); apply: ConjC.
  rewrite !cfunE (Dade_mu_aut PtypeL).
  move: (ConjC _ FF); case/imageP=> i1 /andP [/eqP <- _] ->.
  by rewrite subrr.
split; first by split.
pose Lmu := [tuple of mkseq (mu \o inord) (Nirr W2)].
have LmuE : Lmu = [image (mu i) | i <- Iirr W2] :> seq _.
  apply: (@eq_from_nth _ (mu 0)) => /=.
    by rewrite !size_map size_iota -enumT size_enum_ord.
  rewrite size_map size_iota=> i Hi.
  rewrite nth_mkseq //= (nth_map 0) //; last first.
    by rewrite size_map -enumT size_enum_ord.
  have {2}->: i = (inord i : Iirr W2) by rewrite inordK.
  by rewrite nth_ord_enum.
have LmuFree: free Lmu.
  rewrite LmuE; apply: orthogonal_free.
  apply/pairwise_orthogonalP; split=> [|x y].
    rewrite cons_uniq; apply/andP; split.
      apply/negP; case/imageP=> i.
      by move=> _ HH; case/eqP: (Dade_mu_neq0 PtypeL i).
    by rewrite map_inj_uniq ?enum_uniq //; exact: (Dade_mu_inj PtypeL).
  case/imageP=> i1; rewrite inE => _ ->.
  case/imageP=> j1; rewrite inE => _ -> HH.
  rewrite (cfdot_mu PtypeL)=> //.
  by case: eqP=> // HH1; case/eqP: HH; rewrite HH1.
have Emu h : mu h = Lmu`_h by rewrite nth_mkseq //= inord_val.
pose ftau1 (f : 'CF(L)) : 'CF(G) := 
    (-1) ^+ Dade_delta L W W1 k *:
      \sum_j coord Lmu f j *: (\sum_i sigma (w_ i j)).
have ftau1_linear : linear ftau1.
  move=> l /= x y.
  rewrite scalerA mulrC -scalerA -scalerDr; congr (_ *: _).
  rewrite scaler_sumr -big_split /=; apply: eq_bigr => i _.
  by rewrite linearD linearZ !ffunE scalerDl !scalerA.
pose tau1 := locked (Linear ftau1_linear).
have Tau1Mu j : tau1 (mu j) = 
              (-1) ^+ Dade_delta L W W1 k *: (\sum_i sigma (w_ i j)).
  rewrite Emu /tau1; unlock; rewrite /= /ftau1 /= (bigD1 j) //=.
  rewrite [X in _ + X]big1 ?addr0 // => [| i Dij].
    by rewrite free_coordt ?(eqxx, scale1r).
  by rewrite free_coordt // eq_sym (negPf Dij) scale0r.
exists tau1=> //; split.
  split.
    apply: isometry_on_ortho_base.
    move=> u v; case/imageP=> i /andP [H1i H2i ->].
    case/imageP=> j /andP [H1j H2j ->].
    rewrite !Tau1Mu (cfdot_mu PtypeL).
    rewrite cfdotZl cfdotZr isIntC_conj ?isIntC_sign // mulrA.
    rewrite -signr_addb addbb mul1r cfdot_sumr.
    case: eqP=> [->|/eqP Dij]; last first.
      rewrite mul0n big1 // => i1 _.
      rewrite cfdot_suml big1 // => i2 _.
      case: (cyclicTIisometry tiW)=> ->; rewrite ?irr_vchar //.
      by rewrite (cfdot_cTIirr tiW) (negPf Dij) andbF.
    have<-: \sum_(i < Nirr W1) 1 = (true * #|W1|)%:R :> algC.
      by rewrite sumr_const cardT size_enum_ord NirrE classesW1 mul1n.
    apply: eq_bigr=> i1 _.
    rewrite cfdot_suml (bigD1 i1) // big1  //= ?addr0.
      case: (cyclicTIisometry tiW)=> ->; rewrite ?irr_vchar //.
      by rewrite (cfdot_cTIirr tiW) !eqxx.
    move=> i2 Di2i1.
    case: (cyclicTIisometry tiW)=> ->; rewrite ?irr_vchar //.
    by rewrite (cfdot_cTIirr tiW) (negPf Di2i1).
 move=> u; case/vchar_expansion=> s Hs ->.
 rewrite linear_sum big_seq_cond; apply: sum_vchar=> i.
 rewrite andbT=> /imageP [i1 /andP [Hi1 Hi2]] ->.
 rewrite linearZ scale_vchar // Tau1Mu scale_vchar ?isIntC_sign //.
 apply: sum_vchar=> j1 _.
 by case: (cyclicTIisometry tiW)=> _; apply; apply: irr_vchar.
move=> u; rewrite vcharD1E => /andP [] /vchar_expansion [s Hs ->] Hu.
have->: \sum_(a <- calT) s a *: a =
        \sum_(a <- calT | (a \in calT) && (a != mu k)) s a *: (a - mu k).
  move: Hu; rewrite sum_cfunE.
  rewrite  (bigD1_seq (mu k)) /=; last 2 first.
  - by apply/imageP; exists k; rewrite // inE eqxx.
  - by case/pairwise_orthogonalP: Pog; rewrite cons_uniq; case/andP.
  rewrite big_seq_cond (eq_bigr (fun i => s i * mu k 1%g)); last first.
    move=> i /andP [/imageP [i1 /andP [Hi1 Di1 -> _]]].
    by rewrite cfunE (eqP Hi1).
  rewrite cfunE -mulr_suml -mulrDl.
  rewrite mulf_eq0.
  rewrite (negPf (Dade_mu1_neq0 _)) orbF.
  rewrite addr_eq0 => Hk.
  rewrite  (bigD1_seq (mu k)) /=; last 2 first.
  - by apply/imageP; exists k; rewrite // inE eqxx.
  - by case/pairwise_orthogonalP: Pog; rewrite cons_uniq; case/andP.
  rewrite addrC (eqP Hk) scaleNr scaler_suml.
  rewrite big_seq_cond -sumrB.
  by apply: eq_bigr=> i _; rewrite scalerBr.
rewrite linear_sum [X in _ = X]linear_sum /=; apply: eq_bigr=> i.
case/andP=> [/imageP [i1 /andP [HH1 HH2 ->]]] Dik.
rewrite !linearZ /=; congr (_ *: _).
rewrite linearB !Tau1Mu -scalerBr -!sumrB scaler_sumr linear_sum /=.
apply: eq_bigr=> i2 _.
rewrite -[X in _ = tau X]opprB linearN /= cDade_mu2_tau //.
  by rewrite -scalerN opprB.
have FRes l : 'Res[K] (mu2 i2 l) 1%g = (mu2 i2 l) 1%g by rewrite cfResE.
rewrite -2!FRes -!(Dade_chiE PtypeL).
apply: (mulfI (neq0GiC L K)).
by rewrite -!cfInd1 // !(Dade_Ind_chi PtypeL) (eqP HH1).
Qed.

Let WsG : W \subset G.
Proof. by case tiW=> [[]]. Qed.

Let WsL : W \subset L.
Proof.
case/sdprodP: SdP=> _ <- _ _.
move: HdP; rewrite dprodC => /dprodP [] _ <- _ _.
by apply: mulSg; case: PtypeL => _ [].
Qed.

Let LsG : L \subset G.
Proof. by case: (cDade_dAd_h CDH). Qed.

Let DadH := cDade_dAd_h CDH.

(* This is Peterfalvi (4.10). *)
Lemma Dade_tau_sigma_sub i j :
  tau (delta j *: mu2 i j - delta j *: mu2 0 j - mu2 i 0 + mu2 0 0) =
  sigma(w_ i j) - sigma(w_ 0 j) - sigma(w_ i 0) + sigma(w_ 0 0).
Proof.
pose alpha := acTIirr W i j.
have AE : alpha =  w_ i j - w_ 0 j - w_ i 0 + w_ 0 0.
  rewrite -addrA addrC [X in X + _]addrC [X in _ + X]addrC addrA.
  by rewrite (cTIirr00 tiW) -(acTIirrE tiW).
rewrite -![sigma _ - _]linearB -linearD -AE.
set beta := _ + _. 
have BE: beta = 'Ind[L] alpha.
  rewrite /beta -[X in _ + X]opprK -addrA -opprD -[X in _ - X]scale1r.
  have {3}<-: delta 0 = 1 by rewrite (Dade_delta0 PtypeL) expr0.
  rewrite -scalerBr -!(Dade_mu2_ind PtypeL).
  by rewrite -linearB /= opprD opprK addrA -AE.
apply/cfunP=> g.
case: (boolP (g \in class_support V G))=> [/imset2P [w h WiV HG] ->|GniS].
  rewrite !cfunJ // Dade_id; last first.
    by rewrite inE -[w]conjg1 mem_class_support ?orbT //.
  rewrite cyclicTIsigma_restrict // AE !cfunE.
  have WiWdW2: w \in W :\: W2.
    by move: WiV; rewrite !inE => /andP []; rewrite negb_or=> /andP [_ ->].
  case: (Dade_mu2_restrict PtypeL) => HH _; rewrite !HH //.
  rewrite (Dade_delta0 PtypeL) expr0 !scale1r !cfunE !mulrA.
  by rewrite -signr_addb addbb !mul1r.
have CA := memc_acTIirr tiW i j.
rewrite !cyclicTIsigma_ind //.
move/cfun_onP: (cfInd_on_class_support WsG (CA))=> -> //.
rewrite cfunElock; case: pickP=> //= h.
rewrite !inE /cDade_V /=.
case: (boolP (h \in class_support _ _))=> 
          [/imset2P [v l ViV LiL ->] | HinVl]; last first.
  by rewrite BE; move/cfun_onP: (cfInd_on_class_support WsL (CA))=> ->.
rewrite orbT; case/imset2P=> y z /imset2P [u1 u2].
rewrite DadeJ => // /imsetP [v1 Hv1 ->].
rewrite inE => /eqP-> -> ZiG Eg.
case/negP: GniS; rewrite Eg.
suff->: v1 = 1%g.
  by rewrite conj1g mul1g -conjgM mem_class_support ?groupM // (subsetP LsG).
have: v1 \in 'C_G[v].
  rewrite inE (subsetP (Dade_signalizer_sub DadH v)) //.
  by apply: (subsetP (Dade_signalizer_cent DadH _)).
rewrite inE=> /andP [V1iG V1iC] .
have VinA0 : v \in cDade_A0 CDH.
  by rewrite inE -[v]conjg1 mem_class_support ?orbT.
apply/eqP; rewrite -cycle_eq1 trivg_card1 -dvdn1.
move: (Dade_coprime DadH VinA0 VinA0); rewrite /coprime => /eqP<-.
rewrite dvdn_gcd !cardSg //;
    apply/subsetP=> g1 /generatedP; apply; apply/subsetP=> g2; 
    rewrite inE=> /eqP-> //.
rewrite inE V1iC andbT (subsetP WsL) //.
have Vn0: V != set0 by apply/eqP=> HH; move: ViV; rewrite HH inE.
have: normedTI V G W by case: tiW.
move/(normedTI_memJ_P Vn0)=> [] /(_ _ _ ViV) <- // _.
rewrite conjgE.
by move/cent1P: V1iC=> <-; rewrite mulgA mulVg mul1g.
Qed.
 
End CentralDade.

End Four.

