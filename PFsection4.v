(* (c) Copyright Microsoft Corporation and Inria. All rights reserved. *)
Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq path div choice.
Require Import fintype tuple finfun bigop prime ssralg poly finset center.
Require Import fingroup morphism perm automorphism quotient action zmodp.
Require Import gfunctor gproduct cyclic pgroup frobenius ssrnum.
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

Import GroupScope GRing.Theory Num.Theory.
Local Open Scope ring_scope.

Local Notation real := Num.real.

Section Four.

(* This is Peterfalvi (4.1). *)

Variable gT : finGroupType.

Lemma vchar_pairs_orthonormal (X : {group gT}) (a b c d : 'CF(X)) u v :
    {subset (a :: b) <= 'Z[irr X]} /\ {subset (c :: d) <= 'Z[irr X]} ->
    orthonormal (a :: b) && orthonormal (c :: d) ->
    [&& u \is Creal, v \is Creal, u != 0 & v != 0] ->
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
case/and4P=> r_u r_v nz_u nz_v /and3P[o_abcd ab1 cd1].
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
  by rewrite rmorph_sign !conj_Creal.
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
rewrite (eqP ab1) oppr0 add0r cfunE -mulr2n -mulr_natl mulf_eq0 pnatr_eq0.
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
rewrite rpred1 oner_eq0 (orthonormal_cat (a :: b)) /=.
by case/and3P=> _ _ /andP[] /andP[] /eqP.
Qed.

Section CyclicDade.

Section Definitions.

Variables (L K W W1 W2 : {set gT}).

Definition cyclicDade_hypothesis :=
  [/\ [/\ K ><| W1 = L, W1 != 1, Hall L W1 & cyclic W1],
      [/\ W2 != 1, W2 \subset K, cyclic W2 & {in W1^#, forall x, 'C_K[x] = W2}]
   &  [/\ W1 \x W2 = W & odd #|W|]]%g.

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
  move=> Di1 Di2; rewrite cfdotBl !(cTIirrE cyclicTI_Dade) !cfdot_irr !FF.
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
case: (boolP (j4 == _))=> [/eqP ->| _]; last by rewrite andbF eqr_nat.
by case: (boolP (i4 == _))=> [/eqP -> //| _]; rewrite oner_eq0.
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

Lemma ecTIirr_base_basis : basis_of 'CF(W, W :\: W2) ecTIirr_base.
Proof.
rewrite /basis_of ecTIirr_base_free andbT -dimv_leqif_eq.
  by rewrite (eqnP ecTIirr_base_free) size_tuple cardsX !cardsC1 
             dim_cyclicTIcfun2 cardsT.
by apply/span_subvP=> _ /imageP[[i j] _ ->]; apply: memc_ecTIirr.
Qed.

Definition Dade_mudelta := 
   odflt ([ffun => [ffun => 0]], [ffun => true]) 
    [pick mudelta : ({ffun Iirr W1 -> {ffun Iirr W2 -> Iirr L}} *
                 {ffun Iirr W2 -> bool}) |
       let (mu, delta) := mudelta in
       injectiveb (prod_curry (fun a b => mu a b)) &&
       [forall i, forall j,
       'Ind[L] (e_ i j) == (-1) ^+ delta j *: ('chi_(mu i j) - 'chi_(mu 0 j))]].

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
pose md (j : Iirr W2) := 
   odflt ([ffun => 0], true) 
    [pick mudelta : ({ffun Iirr W1 -> Iirr L} * bool) |
        let (mu, delta) := mudelta in
        injectiveb mu &&
        [forall i, 
         'Ind[L] (e_ i j) == (-1) ^+ delta *: ('chi_(mu i) - 'chi_(mu 0))]].
move/(_ ([ffun i : Iirr W1 => [ffun j => (md j).1 i]], [ffun j => (md j).2])).
move/idP=> [].
have FF: W :\: W2 \subset L^#.
  apply/subsetP=> u; rewrite !inE=> /andP [Hu Hw].
  case: (boolP (u == _))=> [HH| _ /=]; last by apply: (subsetP WsL).
  by case/negP: Hu; rewrite (eqP HH) group1.
pose TH := normedTI_isometry FF normedTI_Dade_W2.
have: forall j, injective (md j).1   
      /\ (forall i, 'Ind[L] (e_ i j) = 
                  (-1) ^+ (md j).2 *: ('chi_((md j).1 i) - 'chi_((md j).1 0))).
  move=> j; rewrite /md; case: pickP=> [[/= mu d] /andP [] |].
    by move/injectiveP=> Hi /forallP Hf; split=> // i; apply/eqP.
  (* All the conditions to apply 1.3 *)
  pose Chi := [tuple of [seq w_ i j | i <- ord_tuple (Nirr W1)]].
  have ChiW i : w_ i j \in Chi by apply/imageP; exists i.
  have Chi_nth (i : Iirr W1) : Chi`_i = w_ i j.
    rewrite (nth_map 0) -?cardE ?card_ord //=.
    move: (tnth_ord_tuple i)=> /=.
    by rewrite (tnth_nth 0) -?cardE ?card_ord //= => ->.
  have ChiS: {subset Chi <= irr W}.
    by move=> c /mapP [k KiI ->]; exact: mem_irr.
  have ChiF: free Chi.
    apply: orthonormal_free; apply/orthonormalP; split=> [|c1 c2].
      apply/injectiveP=> u v; rewrite !(cTIirrE cyclicTI_Dade).
      by move/irr_inj=> /dprod_Iirr_inj []. 
    move=> /mapP [i1 Hi1 ->] /mapP [i2 Hi2 ->].
    apply/eqP; rewrite cfdot_irr eqr_nat; apply/eqP; congr nat_of_bool.
    by rewrite /cyclicTIirr; apply/eqP/eqP=> [-> | /irr_inj].
  have Chi1: (forall chi, chi \in Chi -> chi 1%g = Chi`_0 1%g).
    have->: 0%N = (0 : Iirr W1) by [].
    move=> c; rewrite Chi_nth => /mapP [k KiI ->].
    rewrite /cyclicTIirr !lin_char1 //.
  have ChiC (i : Iirr W1) :  Chi`_i - Chi`_0 \in 'CF(W, W :\: W2).
    have->: 0%N = (0 : Iirr W1) by [].
    by rewrite !Chi_nth memc_ecTIirr.
  have ChiI:  {in 'Z[Chi, W :\: W2], isometry 'Ind[L], to 'Z[irr L, L^#]}.
    split=> [u v U V |fi Hfi]; first by apply: TH (zchar_on U) (zchar_on V).
    have Wfi: fi \in 'Z[irr W].
      have: {subset Chi <= 'Z[irr W]}.
        by move=> u /mapP [i1 Hi1 ->]; exact: irr_vchar.
      by move/zchar_sub_irr; apply; apply: zcharW Hfi.
    rewrite zchar_split cfInd_vchar //.
    apply: irr_vchar_on.
    rewrite zcharD1E cfInd_vchar // cfInd1 //.
    case: (boolP (fi 1%g == 0))=> [/eqP->|HH]; first by rewrite mulr0 eqxx.
    move: (zchar_on Hfi); rewrite cfun_onE=> /subsetP /(_ _ HH).
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
  have UU : [&& (1 : algC) \is Creal, (1 : algC) \is Creal,
                 1 != 0 :> algC & 1 != 0 :> algC].
    by rewrite rpred1 oner_eq0.
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
  have ->: '[e_ i1 j1, e_ i2 j2] = 0.
    by rewrite cfdotBl 2!cfdotBr !(cfdot_cTIirr cyclicTI_Dade) 
               (negPf Dj1j2) !andbF subrr.
  rewrite Ii1j1 Ii2j2 cfdotZl cfdotZr mulrA rmorph_sign -signr_addb.
  by move/eqP; rewrite mulf_eq0 signr_eq0.
apply/injectiveP=> [[i1 j1] [i2 j2] /=]; rewrite !ffunE.
case: (boolP (j1 == j2)) => [/eqP <-| Dj1j2 Eqm].
  by case : (HH j1)=> Hv _; move/Hv<-.
suff: '['chi_((md j1).1 i1), 'chi_((md j2).1 i2)] == 0.
  by rewrite cfdot_irr {1}Eqm eqxx oner_eq0.
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
have F1 : basis_of 'CF(W, W :\: W2) t by apply: ecTIirr_base_basis.
have F2 i j : '[m i, m j] = (i == j)%:R.
  rewrite -{2}[i](inv_dprod_IirrK W1xW2) -{2}[j](inv_dprod_IirrK W1xW2).
  rewrite /m; (do 2 case: (inv_dprod_Iirr _ _))=> i2 j2 i1 j1.
  rewrite cfdotZl cfdotZr cfdot_irr mulrA rmorph_sign -signr_addb.
(* GG -- was case: (_ (i1, _) =P _).
   this fails in trunk, possibly due to unwanted additional lifting
   performed by some primitive in pf_abs_evars *)
  case: (dprod_Iirr W1xW2 (i1, j1) =P _).
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
    by rewrite !cfdotBl !(cTIirrE cyclicTI_Dade) !cfdot_irr eq_sym (negPf iDi1) 
               eq_sym (negPf iD0) subrr scale0r.
  rewrite !cfdotBl  !(cTIirrE cyclicTI_Dade) !cfdot_irr !{1}eqxx.
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
  by rewrite dirr_sign dmem_irr.
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

(* This is Peterfalvi (4.3)(d). *)
Lemma Dade_mu2_mod i j : ('chi_(mu2 i j) 1%g == (-1) ^+ delta j %[mod #|W1|])%C.
Proof.
pose rD := 'Res[W1] 'chi_(mu2 i j) - 'Res[W1] ((-1) ^+ delta j *: w_ i j). 
have rDV: rD \in 'Z[irr W1].
  by rewrite rpredB // cfRes_vchar ?rpredZsign ?irr_vchar.
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
apply/dvdCP; exists (a 0); first exact: Cint_cfdot_vchar_irr.
suffices <-: rD 1%g = a 0 * #|W1|%:R.
  by rewrite !cfunE !cfResE ?group1 // !cfunE LW mulr1.
rewrite {1}[rD]cfun_sum_cfdot sum_cfunE (eq_bigr (fun _ => a 0))=> [|u Hu].
  by rewrite sumr_const cardT size_enum_ord NirrE classesW1 mulr_natr.
by rewrite -/(a u) Ha cfunE LW1 mulr1.
Qed.

Lemma Dade_delta_aut u j : delta (aut_Iirr u j) = delta j.
Proof.
have/esym/cfunP/(_ 1%g) := cfAut_cycTIiso cyclicTI_Dade u (w_ 0 j).
rewrite -(cycTIirr_aut cyclicTI_Dade) aut_Iirr0 !Dade_mu2_sigma !cfunE.
rewrite rmorphM rmorph_sign=> /(canLR (signrMK _))/(congr1 (fun x => x > 0)).
rewrite aut_Cnat ?Cnat_irr1 // irr1_gt0 mulrA -signr_addb -negb_eqb.
by case: eqP => [-> // | _]; rewrite mulN1r oppr_gt0 ler_gtF // ltrW ?irr1_gt0.
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
Proof. by rewrite -cfnorm_eq0 cfdot_mu eqxx mul1n neq0CG. Qed.

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
Proof. exact: sdprod_isog. Qed.

Let Dade_delta0_mu20 : (delta 0 == false) && (mu2 0 0 == 0).
Proof.
have F1: 'Res[W] 'chi[L]_0 = 'chi[W]_0.
  apply/cfunP=> g.
  case: (boolP (g \in W))=> [GiW|GniW]; last by rewrite !cfun0.
  by rewrite cfResE // !irr0 !cfun1E (subsetP WsL) GiW.
have F2: 'chi_0 \in dirr L by apply: dmem_irr.
have F3: {in cyclicTIset cyclicTI_Dade, 'chi[L]_0 =1 w_ 0 0}.
  move=> g; rewrite inE=> [/andP [_ GiW]].
  rewrite (cTIirr00 cyclicTI_Dade) irr0 !cfun1E.
  by rewrite (subsetP WsL) GiW.
move: (cyclicTI_dirr F2 F3); rewrite Dade_mu2_sigma.
case: (delta 0); rewrite (expr0, expr1).
  rewrite scaleN1r=> HH.
  have: 0 < 'chi[L]_0 1%g + 'chi_(mu2 0 0) 1%g.
    by apply: ltr_paddl; try apply: ltrW; apply: irr1_gt0.
  by rewrite HH cfunE addNr ltr_def eqxx.
by rewrite scale1r => /irr_inj<-.
Qed.

Lemma Dade_delta0 : delta 0 = false.
Proof. by case/andP: Dade_delta0_mu20=> /eqP. Qed.

Lemma Dade_mu20 : mu2 0 0 = 0.
Proof. by case/andP: Dade_delta0_mu20=> _ /eqP. Qed.

(* This is PeterFalvi (4.4). *)
Lemma Dade_mu2_subset_cfker :
  [set i | K \subset cfker 'chi[L]_i] = [set mu2 i 0 | i : Iirr W1]. 
Proof.
have KnL: K <| L by case/sdprod_context: SdP.
apply/eqP; rewrite eqEcard; apply/andP; split.
  apply/subsetP=> j; rewrite !inE=> KsK.
  have Ab: abelian (L / K).
    rewrite -(isog_abelian W1isoLqK).
    by apply: cyclic_abelian CW1.
  have: 'Res[W] 'chi[L]_j \in irr W.
    apply: lin_char_irr. 
    rewrite qualifE cfRes_char ?irr_char //= cfResE ?group1 //.
    rewrite -(cfQuoE KnL) // morph1 -quo_IirrE //.
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
      by rewrite !LW2 // irr0 cfun1E H2iW2.
    have H1iW: h1 \in W by apply: (subsetP W1sW _).
    have H2iW: h2 \in W by apply: (subsetP W2sW _).
    rewrite mulg1 -!Hj1 !cfResE ?groupM //.
    by rewrite cfkerMr // (subsetP KsK) // (subsetP W2sK).
  apply/imsetP; exists i=> //.
  have F2: 'chi_j \in dirr L by apply: dmem_irr.
  have F3: {in cyclicTIset cyclicTI_Dade, 'chi_j =1 w_ i 0}.
    move=> g; rewrite inE=> [/andP [_ HH]].
    by rewrite -F1 -Hj1 cfResE.
  move: (cyclicTI_dirr F2 F3); rewrite Dade_mu2_sigma.
  by rewrite Dade_delta0 scale1r=> /irr_inj.
 (* could be improved surely *)
rewrite imset_card card_image => [|x y]; last by case/Dade_mu2_inj.
rewrite card_ord //  NirrE classesW1.
have->: #|W1| = #|[seq mod_Iirr i | i : Iirr (L / K)]|.
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
      \sum_(i0 < Nirr W1)
          '['Res[K] 'chi_(mu2 i0 j), 'chi_i] *: 'chi_(mu2 i0 j) +
      \sum_(i0 < Nirr L | i0 \notin [seq mu2 i1 j | i1 : Iirr W1])
          '['Res[K] 'chi_i0, 'chi_i] *: 'chi_i0.
Proof.
rewrite [X in X = _]cfun_sum_cfdot.
rewrite (eq_bigr (fun k => '['Res[K] 'chi_k, 'chi_i] *: 'chi_k)); last first.
  move=> k; rewrite -cfdot_Res_r cfdotC conj_Cnat //.
  by apply: Cnat_cfdot_char_irr (cfRes_char _ (irr_char _)).
rewrite (bigID (mem [seq mu2 i j | i : Iirr W1])) /=; congr (_ + _).
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
move: (Lagrange KsL)=> /eqP; rewrite -{1}(sdprod_card SdP) eqn_mul2l.
by case: #|K| (cardG_gt0 K)=> //= _ _ /eqP.
Qed.

(* These are the first two parts of PeterFalvi (4.5a). *)
Lemma Dade_chiE i j : 'chi_(chi j) = 'Res[K] 'chi_(mu2 i j).
Proof.
rewrite {i}Dade_chi_eq /chi; case: pickP=> [k /eqP // | /=].
suff /irrP[k -> /(_ k)]: 'Res[K] 'chi_(mu2 0 j) \in irr K.
  by rewrite eqxx.
set v := 'Res[_] _.
have Cv: v \is a character := cfRes_char _ (irr_char _).
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
  apply: psumr_eq0P => [k _|]; last first.
    rewrite -sum_cfunE sumrB -cfun_sum_cfdot 2!cfunE -big_mkcond /=.
    rewrite (bigD1 i) // big1=> [|k]; last by case: (_ == _).
    by rewrite !cfunE addr0 HF subrr.
  case: (_ =P _)=> [->|_]; rewrite !cfunE ?subr0; last first.
     by apply: mulr_ge0; apply: Cnat_ge0;
          [apply: (Cnat_cfdot_char_irr k Cv) | exact: Cnat_irr1 k].
  rewrite  -[X in _ <= _ - X]mul1r -mulrBl.
  apply: mulr_ge0; last by apply: Cnat_ge0 (Cnat_irr1 _).
  rewrite subr_ge0; move: HiC; rewrite irr_consttE.
  case/CnatP: (Cnat_cfdot_char_irr i Cv)=> n ->.
  by rewrite pnatr_eq0 ler1n; case: n.
apply: ler_anti; apply/andP; split.
  by move: (char1_ge_constt Cv HiC); rewrite (cfResE _ KsL (group1 _)).
have /ler_pmul2l <- : 0 <  #|W1|%:R :> algC by rewrite ltr0n cardG_gt0.
rewrite -{2}Dade_indexE -(cfInd1 'chi_i KsL) (Dade_Ind_DI _ j).
have->: #|W1|%:R * v 1%g = \sum_i 'chi_(mu2 i j) 1%g.
  rewrite (eq_bigr (fun k => v 1%g))=> [| k _].
    rewrite sumr_const cardT -cardE /= card_ord mulr_natl NirrE.
    by have:= cyclic_abelian CW1; rewrite card_classes_abelian => /eqP ->.
  by rewrite -(cfResE _ KsL) // Dade_chi_eq (cfResE _ KsL).
rewrite -subr_ge0 !cfunE !sum_cfunE addrAC -sumrB.
apply: addr_ge0; apply: sumr_ge0=> k _; rewrite !cfunE; last first.
   by apply: mulr_ge0; apply: Cnat_ge0;
          [apply: (Cnat_cfdot_char_irr i  (cfRes_char _ (irr_char _)))
             | exact: Cnat_irr1 k].
  rewrite  -[X in _ <= _ - X]mul1r -mulrBl.
  apply: mulr_ge0; last by apply: Cnat_ge0 (Cnat_irr1 _).
  rewrite subr_ge0; move: HiC; rewrite irr_consttE Dade_chi_eq -/v.
  case/CnatP: (Cnat_cfdot_char_irr i Cv)=> n ->.
  by rewrite pnatr_eq0 ler1n; case: n.
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
suff: forall k, k \notin [seq mu2 i1 j | i1 : Iirr W1] ->
     ('['Res[K] 'chi_k, 'Res[K] 'chi_(mu2 0 j)] *: 'chi_k) 1%g = 0.
  move/(_ _ Hi)=> /eqP.
  rewrite cfunE  mulf_eq0 (negPf (irr1_neq0 _)) orbF => /eqP ->.
  by rewrite scale0r.
apply: (psumr_eq0P _ (eqP HH))=> k _; rewrite cfunE.
apply: mulr_ge0; last by apply: Cnat_ge0 (Cnat_irr1 _).
rewrite -Dade_chiE Cnat_ge0 // Cnat_cfdot_char_irr //.
by apply: cfRes_char _ (irr_char _).
Qed.

Lemma Dade_chi_aut u j : 'chi_(chi (aut_Iirr u j)) = cfAut u ('chi_(chi j)).
Proof.
by rewrite (Dade_chiE (aut_Iirr u 0)) Dade_mu2_aut -cfAutRes -Dade_chiE.
Qed.

Lemma Dade_chi0 : 'chi_(chi 0) = 1.
Proof. by rewrite (Dade_chiE 0) Dade_mu20 irr0 cfRes_cfun1. Qed.

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

Lemma Dade_irr_inj : injective chi.
Proof.
by move=> j1 j2 Dj; apply: Dade_mu_inj; rewrite -!Dade_Ind_chi Dj.
Qed.

(* This is the first assertion of Peterfalvi (4.5b). *)
Theorem Dade_Ind_chi'_irr k :
    k \notin codom chi ->
    let phi := 'Ind 'chi_k in
  phi \in irr L /\ (forall i j, phi != 'chi_(mu2 i j)).
Proof.
move=> KniC phi.
suff IeK: 'I_L['chi_k] = K.
  have PiI: phi \in irr L by apply: inertia_Ind_irr; rewrite ?IeK.
  split=> // i j; apply/eqP => PeJ; case/negP: (irr_neq0 (mu2 i j)).
  rewrite -cfnorm_eq0 -{1}PeJ -Frobenius_reciprocity -Dade_chiE cfdot_irr.
  by case: (k =P _) => // KeJ; case/negP: KniC; apply/imageP; exists j.
rewrite -(sdprodW (sdprod_modl SdP (sub_inertia _))); apply/mulGidPl.
have KsI := sub_Inertia 'chi_k KsL.
apply/subsetP=> w1 /setIP[W1iW /setIdP[W1iN /eqP ChiW1E]].
have [-> // | ntw1] := eqVneq w1 1%g.
have actIirrK: is_action L (@conjg_Iirr _ K).
  split=> [y j k2 eq_jk2 | j y z Gy Gz].
    by apply/irr_inj/(can_inj (cfConjgK y)); rewrite -!conjg_IirrE eq_jk2.
  by apply: irr_inj; rewrite !conjg_IirrE (cfConjgM _ KnL).
pose ito := Action actIirrK.
suff FeC: 'Fix_ito[w1] = [set i in codom chi].
  suff: k \in 'Fix_ito[w1] by rewrite FeC inE => /idPn[].
  rewrite inE; apply/subsetP=> w2; rewrite !inE => /eqP->.
  by apply/eqP; apply: irr_inj; rewrite conjg_IirrE.
have W1iL := (subsetP W1sL _ W1iW).
apply/eqP; rewrite eq_sym eqEcard; apply/andP; split.
  apply/subsetP=> i1; rewrite inE; case/imageP=> /= i2 I2iIW2 ->.
  rewrite inE; apply/subsetP=> w2; rewrite !inE => /eqP->.
  apply/eqP; apply: irr_inj; rewrite conjg_IirrE.
  apply/cfunP=> u; case: (boolP (u \in K))=> [UiK|UniK]; last by rewrite !cfun0.
  have UWiK : u ^ w1 \in K.
    by rewrite -mem_conjgV; case/normalP: KnL=> _ ->; rewrite ?groupV.
  have UWIiK : u ^ w1^-1 \in K by rewrite -mem_conjg; case/normalP: KnL=> _ ->.
  by rewrite !(Dade_chiE 0) cfConjgE // !cfResE // cfunJ // groupV.
have ->: #|[set i in codom chi]| = #|W2|.
  rewrite  -classesW2 -NirrE.
  suff {2}<-: #|codom chi| = Nirr W2  by apply: eq_card=> i; rewrite inE.
  by rewrite card_codom  ?card_ord //; exact: Dade_irr_inj.
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
  by rewrite conjg_IirrE cfConjgEJ // cfunJ.
pose f (C : {set gT}) := odflt 1%g [pick i in C :&: W2].
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
case/negP: ntw1; rewrite -order_eq1.
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
rewrite irrEchar; apply/nandP; right; rewrite -[mu j](big_map _ xpredT id).
rewrite /index_enum -enumT cfnorm_map_orthonormal //.
  rewrite size_map -cardE card_ord pnatr_eq1 NirrE neq_ltn orbC.
  by rewrite classes_gt1; have [[_ ->] _ _] := HC.
apply/orthonormalP; split=> [|_ _ /mapP[i1 _ ->] /mapP[i2 _ ->]].
  by rewrite map_inj_uniq ?enum_uniq // => ? ? /irr_inj/Dade_mu2_inj[].
by rewrite cfdot_irr (inj_eq irr_inj).
Qed.

(* This is the second assertion of Peterfalvi (4.5b). *)
Theorem Ptype_irr_mu2Vchi'Ind ell (phi := 'chi_ell) :
   {i : _ & {j | phi = 'chi_(mu2 i j)}}
     + {k | k \notin codom chi & phi = 'Ind 'chi_k}.
Proof.
pose l := odflt 0 [pick i in irr_constt ('Res[K] phi)].
have: ell \in irr_constt ('Ind[L] 'chi_l).
  rewrite constt_Ind_constt_Res /l.
  case: pickP=> //=.
  case/neq0_has_constt: (Res_irr_neq0 K ell)=> j1 Hj1 /(_ j1).
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
left; exists i, j; rewrite /i; case: pickP=> [i1 /eqP //| FEq].
case/eqP: CDots; rewrite big1=> // k _.
rewrite cfdot_irr eq_sym; case: eqP=> // Eq.
by move: (FEq k); rewrite -Eq eqxx.
Qed.

End CyclicDade.

Section CentralDade.

Variable (A A0 : {set gT}) (G H L K W W1 W2 : {group gT}).

Definition centralDade_properties :=
  [/\ (*c*) [/\ H <| L, W2 \subset H & H \subset K],
      (*d*) [/\ A <| L, \bigcup_(h in H^#) 'C_K[h]^# \subset A & A \subset K^#]
    &       A0 = A :|: class_support (W :\: (W1 :|: W2)) L].
 
Record centralDade_hypothesis : Prop := CentralDadeHypothesis {
  cDade_cTI_h    :> cyclicTIhypothesis G W W1 W2;
  cDade_cDa_h    :> cyclicDade_hypothesis L K W W1 W2;
  cDade_dAd_h    :> Dade_hypothesis G L A0;
      _          : centralDade_properties;
  cDade_sigma    := cyclicTIsigma G W W1 W2;
  cDade_w        := @cyclicTIirr gT W W1 W2;
  cDade_mu       := @Dade_mu L W W1 W2;
  cDade_mu2 i j  := 'chi_(@Dade_mu2 L W W1 W2 i j);
  cDade_chi i    := 'chi_(@Dade_chi L K W W1 W2 i);
  cDade_delta i  := (-1)^+ @Dade_delta L W W1 W2 i : algC;
  cDade_tau      := Dade cDade_dAd_h
}.

Hypothesis CDH : centralDade_hypothesis.

Local Notation V := (cyclicTIset (cDade_cTI_h CDH)).

Let CDH_P := let: CentralDadeHypothesis _ _ _ CDH_P := CDH in CDH_P.

Let defA0 : A0 = A :|: class_support V L. Proof. by have [] := CDH_P. Qed.

Let AnL : A <| L. Proof. by have [_ []] := CDH_P. Qed.

Let sAA0 : A \subset A0. Proof. by rewrite defA0 subsetUl. Qed.

Lemma cDade_DGA : Dade_hypothesis G L A.
Proof. exact: restr_Dade_hyp CDH sAA0 (normal_norm AnL). Qed.

Let HnL : H <| L. Proof. by have [[]] := CDH_P. Qed.

Let HsK : H \subset K. Proof. by have [[]] := CDH_P. Qed.

Let KsL : K \subset L.
Proof. by have [[/sdprod_context[/andP[]]]] := cDade_cDa_h CDH. Qed.

Let CupA: \bigcup_(h in H^#) 'C_K[h]^# \subset A.
Proof. by have [_ []] := CDH_P. Qed.

Let W2sH : W2 \subset H. Proof. by have [[]] := CDH_P. Qed.

Let HdP :  W1 \x W2 = W. Proof. by have [[[]]] := CDH. Qed.

Let dW1 : W1 :!=: 1%g. Proof. by have [[_ []]] := CDH. Qed.
Let dW2 : W2 :!=: 1%g. Proof. by have [[_ []]] := CDH. Qed.

Local Notation sigma := (cyclicTIsigma G W W1 W2).
Local Notation w_ :=  (@cyclicTIirr _ W W1 W2).
Local Notation mu := (@Dade_mu L W W1 W2).
Local Notation mu2 i j := ('chi_(@Dade_mu2 L W W1 W2 i j)).
Local Notation chi i := ('chi_(@Dade_chi L K W W1 W2 i)).
Local Notation delta i :=
  ((- (GRing.one Algebraics.Implementation.ringType))
       ^+ nat_of_bool (@Dade_delta L W W1 W2 i)).
Local Notation tau := (Dade (cDade_dAd_h CDH)).

(* This is the first part of Peterfalvi (4.7). *) 
Lemma cDade_cfker_cfun_on i : 
   ~~ (H \subset cfker 'chi[K]_i) -> 'chi_i \in 'CF(K, A :|: 1%G).
Proof.
move=> HnsC; apply/cfun_onP=> g GniA.
have [GiK | /cfun0-> //] := boolP (g \in K).
apply: (not_in_ker_char0 GiK (normalS _ _ HnL) HnsC) => //.
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

(* This is the second part of Peterfalvi (4.7). *) 
Lemma cDade_cfker_cfun_on_ind i : 
   ~~ (H \subset cfker 'chi[K]_i) -> 'Ind[L] 'chi_i \in 'CF(L, A :|: 1%G).
Proof.
move/cDade_cfker_cfun_on=> CiCF; apply/cfun_onP=> g GiG.
rewrite cfIndE // big1 ?mulr0 // => h HiL; move/cfun_onP: CiCF; apply.
apply: contra GiG; rewrite !inE; case/orP; last first.
  by rewrite -{1}(conj1g h); move/eqP=> /conjg_inj /eqP ->; rewrite orbT.
case/normalP: AnL => [] _ /(_ _ HiL) {1}<-.
by rewrite memJ_conjg => ->.
Qed.

(* Third part of Peterfalvi (4.7). *)
Lemma not_cDade_core_sub_cfker_chi j : j != 0 ->  ~~ (H \subset cfker (chi j)).
Proof.
apply: contra => HsC; suffices: w_ 0 j = 1.
  by rewrite -(cTIirr00 CDH) !(cTIirrE CDH) => /irr_inj/dprod_Iirr_inj[->].
apply/cfunP=> g.
rewrite !cfun1E; case: (boolP (_ \in _))=> [|GnI]; last first.
  by rewrite cfun0.
case/dprodP: HdP=> _ {1}<- _ _; case/imset2P=> x y XiW1 YiW2->.
case/trivgPn: dW1=> x1 X1iW1 NOx1.
suff<-: w_ 0 j (x1 * y)%g = true%:R.
  rewrite !(cTIirrE CDH) dprod_IirrE !cfDprodE ?group1 // irr0.
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
  have: y \in cfker (chi j) by rewrite (subsetP HsC) ?(subsetP W2sH).
  by rewrite ((Dade_chiE CDH) 0) cfker_Res ?irr_char // => /setIP[_ /cfkerMr->].
rewrite (DMR 0 j _ X1YiWW2) (DMR 0 j _ X1iWW2) !cfunE => /lreg_sign->.
rewrite -[x1]mulg1 (cTIirrE CDH) !dprod_IirrE !cfDprodE //.
by rewrite irr0 cfun1E X1iW1 mul1r !(lin_char1 (cTIirr_linearW2 CDH _)).
Qed.

(* Fourth part of Peterfalvi (4.7). *)
Lemma cDade_chi_support j : j != 0 -> chi j \in 'CF(K, A :|: 1%G).
Proof. by move/not_cDade_core_sub_cfker_chi/cDade_cfker_cfun_on. Qed.

(* Last part of Peterfalvi (4.7). *)
Lemma cDade_mu_support j : j != 0 -> mu j \in 'CF(L, A :|: 1%G).
Proof. 
move/not_cDade_core_sub_cfker_chi/cDade_cfker_cfun_on_ind.
by rewrite (Dade_Ind_chi CDH).
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

Import ssrint.

(* Second part of PeterFalvi (4.8). *)
Lemma cDade_mu2_delta i j k : 
  mu2 i j 1%g = mu2 i k 1%g -> delta j = delta k.
Proof.
move=> eqjk; have /negP: ~~ (#|W1| %| 2) by rewrite gtnNdvd.
have{eqjk}: (delta j == delta k %[mod #|W1|])%C.
  apply: eqCmod_trans (Dade_mu2_mod CDH i k).
  by rewrite eqCmod_sym -eqjk (Dade_mu2_mod CDH).
rewrite /eqCmod -![delta _]intr_sign -rmorphB dvdC_int ?Cint_int //= intCK.
by do 2!case: (Dade_delta L W _ _).
Qed.

Let SdP : K ><| W1 = L. Proof. by case: (cDade_cDa_h CDH)=> [[]]. Qed.

Let Hcoprime : coprime #|W1| #|K|.
Proof.
case: (cDade_cDa_h CDH)=> [[_ _ H_Hall _] [_ WsK _ _] _].
by rewrite coprime_sym (coprime_sdprod_Hall SdP) (sdprod_Hall SdP).
Qed.

(* First part of PeterFalvi (4.8). *)
Lemma cDade_mu2_on i j k :
    j != 0 -> k != 0 -> mu2 i j 1%g = mu2 i k 1%g ->
  mu2 i j - mu2 i k \in 'CF(L, A0). 
Proof.
move=> NZj NZk Emu1.
have HF g : g \in W1 -> mu2 i j g - mu2 i k g = 0.
  have [-> | ntg W1g] := eqVneq g 1%g; first by rewrite Emu1 subrr.
  have GiWmW2: g \in W :\: W2.
    rewrite inE (subsetP W1sW) // andbT; apply: contra ntg => GiW2.
    by rewrite -in_set1 -set1gE; have [_ _ _ <-] := dprodP HdP; rewrite inE W1g.
  case: (Dade_mu2_restrict CDH)=> HH _.
  rewrite !HH // (cDade_mu2_delta Emu1) !cfunE -mulrBr -[g]mulg1.
  rewrite !(cTIirrE CDH) !dprod_IirrE !cfDprodE //.
  by rewrite !(lin_char1 (cTIirr_linearW2 CDH _)) subrr mulr0.
apply/cfun_onP=> g; rewrite defA0 !inE negb_or !cfunE.
case/andP=> GniA GniCL.
case: (boolP (g \in L))=> [GiL | GniL]; last by rewrite !cfun0 // subrr.
case: (boolP (g \in K))=> [GiK | GniK]; last first.
  move: GiL GniK GniCL.
  case/(mem_sdprod SdP)=> k1 [x1 [K1iK X1iW1] -> _] K1X1niK.
  have: x1 \in W1^#.
    by rewrite !inE X1iW1 andbT; apply: contraNneq K1X1niK => ->; rewrite mulg1.
  case: (cDade_cDa_h CDH)=> [] _ [_ _ _ HH _] /HH => EW2.
  have CKx: coprime #|K| #[x1].
    move: X1iW1; rewrite -cycle_subG=> /cardSg /coprime_dvdr; apply.
    by rewrite coprime_sym.
  have X1iNK: x1 \in 'N(K) by case/sdprodP: SdP=> _ _ /subsetP ->.
  have: (k1 * x1)%g \in K :* x1.
    by apply/imset2P; exists k1 x1; rewrite ?inE //.
  case: (partition_cent_rcoset X1iNK CKx) => /cover_partition<- _.
  rewrite cover_imset => /bigcupP [k2 K2iK] /imsetP [w /imset2P [x2 x]].
  rewrite EW2 inE => X2iW2 /eqP-> -> Dkx1; rewrite {}Dkx1 in K1X1niK *.
  have X2X1iW : (x2 * x1)%g \in W.
    by apply: groupM; [rewrite (subsetP W2sW) | rewrite (subsetP W1sW)].
  case: (boolP ((x2 * x1)%g \in W1))=> [X2X1iW1 _ | X2X1niW1 /negP[]].
    by rewrite !cfunJ ?(subsetP KsL) // HF.
  apply: mem_class_support; last by apply: (subsetP KsL).
  rewrite !inE negb_or -andbA; apply/and3P; split=> //.
  apply: contra K1X1niK => X1XiW2.
  by rewrite groupJ //= (subsetP HsK) ?(subsetP W2sH).
have [-> | ntg] := eqVneq g 1%g; first by rewrite Emu1 subrr.   
have GniA1 : g \notin A :|: 1%G by rewrite !inE negb_or GniA.
move/cfun_onP: (cDade_chi_support NZj)=> /(_ _ GniA1).
rewrite (Dade_chiE CDH i) cfResE // => ->.
move/cfun_onP: (cDade_chi_support NZk)=> /(_ _ GniA1).
rewrite (Dade_chiE CDH i) cfResE // => ->.
by rewrite subrr.
Qed.

Local Notation NC := (cyclicTI_NC W W1 W2).
Let tiW : cyclicTIhypothesis G W W1 W2 := CDH.
Let PtypeL : cyclicDade_hypothesis L K W W1 W2 := CDH.

(* This is last part of PeterFalvi (4.8). *)
Lemma cDade_mu2_tau i j k :
    j != 0 -> k != 0 -> mu2 i j 1%g = mu2 i k 1%g -> 
  tau (mu2 i j - mu2 i k) =  delta j *: (sigma (w_ i j) - sigma (w_ i k)).
Proof.
move=> nz_j nz_k eq_mu2jk_1; apply: canRL (signrZK _) _.
have [-> | k'j] := eqVneq j k; first by rewrite !subrr !raddf0.
set dmu2 := _ - _; set dsw := _ - _; set dmu := _ *: _; pose phi := dmu - dsw.
have V'phi: {in V, forall x, phi x = 0}.
  move=> x Vx; have [Dmu2 _] := Dade_mu2_restrict CDH.
  have Wx: x \in W :\: W2 by rewrite (subsetP _ x Vx) // setDS ?subsetUr.
  rewrite !(cfunE, Dade_id) ?(cyclicTIsigma_restrict _ Vx) //; last first.
    by rewrite defA0 inE orbC -[x]conjg1 mem_class_support.
  by rewrite !Dmu2 // (cDade_mu2_delta eq_mu2jk_1) !cfunE -mulrBr signrMK subrr.
have{eq_mu2jk_1} Zmu2: dmu2 \in 'Z[irr L, A0].
  by rewrite zchar_split rpredB ?irr_vchar ?cDade_mu2_on.
have [[Itau Ztau] [_ Zsigma]] := (Dade_Zisometry CDH, cyclicTIisometry CDH).
have Zmu: dmu \in 'Z[irr G, G^#] by rewrite rpredZsign Ztau.
have Zsw: dsw \in 'Z[irr G] by rewrite rpredB ?Zsigma ?irr_vchar.
have n2mu: '[dmu] = 2%:R.
  rewrite cfnorm_sign Itau // cfnormBd ?cfnorm_irr // cfdot_irr.
  by rewrite [_ == _](contraNF _ k'j) // => /eqP/(Dade_mu2_inj CDH)[->].
have n2sw: '[dsw] = 2%:R by rewrite cfnormBd !cfdot_sigma ?eqxx ?(negPf k'j).
have [oImu _ Dmu] := dirr_small_norm (zcharW Zmu) n2mu isT.
have{Zsw} [oIsw _ Dsw] := dirr_small_norm Zsw n2sw isT.
set Imu := dirr_constt _ in oImu Dmu; set Isw := dirr_constt _ in oIsw Dsw.
have mu'sw_lt0 di: di \in Isw :\: Imu -> '[phi, dchi di] < 0.
  case/setDP=> sw_di mu'di; rewrite cfdotBl subr_lt0.
  move: sw_di; rewrite dirr_consttE; apply: ler_lt_trans.
  rewrite real_lerNgt -?dirr_consttE ?real0 ?Creal_Cint //.
  by rewrite Cint_cfdot_vchar ?(zcharW Zmu) ?dchi_vchar.
suffices /eqP eqI_sw_mu: Isw == Imu by rewrite Dmu Dsw eqI_sw_mu.
rewrite eqEcard oImu oIsw andbT -setD_eq0; apply/set0Pn=> [[dj1 mu'dj1]].
have [[sw_dj1 _] phi_j1_lt0] := (setDP mu'dj1, mu'sw_lt0 _ mu'dj1).
have NCtrB := leq_trans (cyclicTI_NC_sub W W1 W2 (_ : 'CF(G)) _) (leq_add _ _).
have ltNCphi: (NC phi < 2 * minn #|W1| #|W2|)%N.
  have NCphi4: (NC phi <= 1 + 1 + (1 + 1))%N.
    rewrite /phi; have [i1 [i2 Di1i2] ->] := vchar_norm2 Zmu n2mu.
    by rewrite !(NCtrB, cyclicTI_NC_irr, cyclicTI_NC_sigma).
  by rewrite (leq_ltn_trans NCphi4) // !addnn -mul2n ltn_pmul2l // leq_min tLW1.
pose swId := dirr_dIirr (fun sj => (-1) ^+ (sj.1 : bool) *: sigma (w_ i sj.2)).
have swIdE s l: dchi (swId (s, l)) = (-1) ^+ s *: sigma (w_ i l).
  by apply: dirr_dIirrE => sj; rewrite rpredZsign (dirr_sigma CDH).
have dot_dj1: '[dsw, dchi dj1] = 1.
  rewrite Dsw cfdot_suml (big_setD1 dj1) //= cfnorm_dchi big1 ?addr0 //.
  move=> dj2 /setD1P[/negPf j1'2 /dirr_constt_oppl]; rewrite cfdot_dchi j1'2.
  by case: eqP => [-> /negP[] | _ _]; rewrite ?subrr ?ndirrK.
have dot_dj2: 0 < '[dsw, dsw - dchi dj1].
  by rewrite cfdotBr dot_dj1 n2sw addrK ltr01.
have{dot_dj1 dot_dj2} [s [j1 [j2 Dj1 sw_j2]]]:
  exists s, exists j1, exists2 j2, swId (s, j1) = dj1 & swId (~~ s, j2) \in Isw.
- move/cfdot_add_dirr_eq1: dot_dj1; rewrite dirr_dchi rpredN !dirr_sigma //.
  case=> // Ddj1; [exists false, j, k | exists true, k, j]; try apply: dirr_inj;
    rewrite ?dirr_consttE swIdE scaler_sign //=.
  + by rewrite addrC Ddj1 addKr in dot_dj2.
  by rewrite Ddj1 addrK in dot_dj2.
rewrite -Dj1 swIdE cfdotZr rmorph_sign in phi_j1_lt0.
have phi_j1_neq0: '[phi, sigma (w_ i j1)] != 0.
  by rewrite -(can_eq (signrMK s)) mulr0 ltr_eqF.
set dj2 := swId _ in sw_j2; have NCj2'_le1 (dI : {set _}):
  dj2 \in dI -> #|dI| = 2%N -> (NC (\sum_(dk in dI :\ dj2) dchi dk)%R <= 1)%N.
- rewrite (cardsD1 dj2) => -> /eqP/cards1P[dk ->].
  by rewrite big_set1 cyclicTI_NC_dirr ?dirr_dchi.
suffices /mu'sw_lt0/ltr_geF/idP[]: dj2 \in Isw :\: Imu.
  rewrite swIdE cfdotZr signrN rmorphN mulNr oppr_ge0 rmorph_sign.
  have := cyclicTI_NC_split V'phi ltNCphi phi_j1_neq0.
  by case=> ->; rewrite mulrCA nmulr_lle0 ?ler0n.
have: (1 + 1 < NC phi)%N.
  apply (@leq_trans (minn #|W1| #|W2|)); first by rewrite leq_min ?tLW1.
  apply: cyclicTI_NC_minn => //; rewrite ltNCphi /NC (cardsD1 (i, j1)) inE /=.
  by rewrite phi_j1_neq0.
rewrite inE sw_j2 andbT ltnNge; apply: contra => mu_j2.
rewrite /phi Dsw (big_setD1 dj2) //= Dmu (big_setD1 dj2) //=.
by rewrite addrAC opprD addNKr addrC NCtrB ?NCj2'_le1.
Qed.

Lemma Ptype_TIset_disjoint : cyclicTIset tiW \subset ~: K.
Proof.
have [[/sdprodP[_ _ _ tiKW1] _ _ _] [_ sW2K _ _] _] := PtypeL.
have defW: W1 \x W2 = W := cyclicTIhyp_W1xW2 tiW.
rewrite subDset setUC -subDset setDE setCK setIC.
by rewrite -(dprod_modr defW sW2K) tiKW1 dprod1g subsetUr.
Qed.

Lemma Dade_mu_nreal i : i != 0 -> ~~ cfReal (mu i).
Proof.
apply: contraNneq; rewrite -(Dade_mu_aut PtypeL) -irr_eq1 -odd_eq_conj_irr1 //.
by rewrite -aut_IirrE => /(Dade_mu_inj PtypeL)->.
Qed.

Let CW : cyclic W. Proof. by case: tiW=> [[]]. Qed.

Let CW1 : cyclic W1. Proof. by exact: cyclicS CW. Qed.

Let classesW1 : #|classes W1| = #|W1|.
Proof.
by have:= cyclic_abelian CW1; rewrite card_classes_abelian => /eqP ->.
Qed.

Lemma Dade_mu1_spos i : 0 < mu i 1%g.
Proof.
rewrite /Dade_mu (bigD1 (0 : Iirr W1)) //= cfunE.
rewrite ltr_spaddl ?irr1_gt0 // sum_cfunE.
by apply: sumr_ge0=> i1 _; apply: ltrW (irr1_gt0 _).
Qed.

Lemma Dade_mu1_neq0 i : mu i 1%g != 0.
Proof. by apply/eqP=> HH; move: (Dade_mu1_spos i); rewrite HH ltrr. Qed.

Definition uniform_Dade_mu_seq k :=
  image mu [pred j | mu j 1%g == mu k 1%g & j != 0].

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
    rewrite (Dade_mu_aut PtypeL) cfunE (eqP Mui1) conj_Cnat //.
    by rewrite Cnat_char1 ?rpred_sum // => i1 _; apply: irr_char.
  apply: contra NZj=> /eqP HH.
  by rewrite -[j]conjC_IirrK HH conjC_Iirr0.
have Equiv: 'Z[calT, L^#] =i 'Z[calT, A].
  move=> f; rewrite zcharD1E; apply/idP/idP; last first.
    rewrite (zchar_split _ A)=> /andP [-> FiA] /=.
    apply/eqP; apply: (cfun_onP FiA).
    by have [_ [_ _ /subsetD1P[]]] := CDH_P.
  case/andP=> Zf Vf1.
  have: f \in 'Z[calT, A :|: 1%G].
    rewrite zchar_split Zf /=.
    case: (zchar_expansion  (free_uniq (orthogonal_free Pog)) Zf) => s Hs ->.
    rewrite big_map big_filter.
    apply: memv_suml=> i /andP [_ NZi].
    by apply: memvZ; apply: cDade_mu_support.
  rewrite zchar_split cfun_onE=> /andP [_ Sf].
  rewrite zchar_split Zf /= cfun_onE.
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
  rewrite -Equiv zcharD1E; apply/andP; split.
    by rewrite rpredB ?mem_zchar // (Dade_mu_aut PtypeL) ConjC.
  rewrite !cfunE (Dade_mu_aut PtypeL).
  move: (ConjC _ FF); case/imageP=> i1 /andP [/eqP <- _] ->.
  by rewrite subrr.
split; first by split.
pose Lmu := [tuple of mkseq (mu \o inord) (Nirr W2)].
have LmuE : Lmu = [seq mu i | i : _] :> seq _.
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
      \sum_j coord Lmu j f *: (\sum_i sigma (w_ i j)).
have ftau1_linear : linear ftau1.
  move=> l /= x y.
  rewrite scalerA mulrC -scalerA -scalerDr; congr (_ *: _).
  rewrite scaler_sumr -big_split /=; apply: eq_bigr => i _.
  by rewrite linearD linearZ scalerDl !scalerA.
pose tau1 := locked (Linear ftau1_linear).
have Tau1Mu j : tau1 (mu j) = delta k *: (\sum_i sigma (w_ i j)).
  rewrite Emu /tau1; unlock; rewrite /= /ftau1 /= (bigD1 j) //=.
  rewrite [X in _ + X]big1 ?addr0 // => [| i Dij].
    by rewrite coord_free ?(eqxx, scale1r).
  by rewrite coord_free // eq_sym (negPf Dij) scale0r.
have Huniq: uniq calT by exact: (free_uniq (orthogonal_free Pog)).
exists tau1 => //; split.
  have [Isigma Zsigma] := cyclicTIisometry tiW.
  split=> [|_ /zchar_expansion[//|s Zs ->]]; last first.
    rewrite linear_sum big_seq rpred_sum // => _ /imageP[i1 _ ->].
    rewrite raddfZ_Cint ?scale_zchar //= Tau1Mu rpredZsign.
    by rewrite rpred_sum // => i _; rewrite Zsigma ?irr_vchar.
  apply: isometry_in_zchar => _ _ /imageP[i _ ->] /imageP[j _ ->] /=.
  rewrite !Tau1Mu (cfdot_mu PtypeL) cfdotZl cfdotZr rmorph_sign signrMK.
  rewrite cfdot_sumr; have [-> | Dij] := altP (i =P j); last first.
    rewrite big1 // => i1 _; rewrite cfdot_suml big1 // => i2 _.
    by rewrite Isigma ?irr_vchar // (cfdot_cTIirr tiW) (negPf Dij) andbF.
  rewrite -classesW1 -NirrE mul1n.
  rewrite (eq_bigr (fun _ => 1)) ?sumr_const ?card_ord // => i1 _.
  rewrite cfdot_suml (bigD1 i1) // big1 //= ?addr0 => [|i2 Di2i1].
    by rewrite Isigma ?irr_vchar ?cfnorm_irr.
  by rewrite Isigma ?irr_vchar // (cfdot_cTIirr tiW) (negPf Di2i1).
move=> u; rewrite zcharD1E => /andP[/zchar_expansion[//|s Hs ->] /eqP Hu].
apply: oppr_inj; rewrite -!linearN.
have ->: - (\sum_(a <- calT) s a *: a) = \sum_(a <- calT) s a *: (mu k - a).
  rewrite (eq_bigr _ (fun _ _ => scalerBr _ _ _)) sumrB -scaler_suml.
  rewrite -{1}sub0r -{1}(scale0r (mu k)); congr (_ *: _ - _).
  apply/(mulIf (Dade_mu1_neq0 k)); rewrite mul0r -{1}Hu sum_cfunE mulr_suml.
  by apply: eq_big_seq => _ /imageP[j /andP[/eqP <- _] ->]; rewrite cfunE.
rewrite !linear_sum; apply: eq_big_seq => _ /imageP[j /andP[/eqP eq_jk nzj] ->].
rewrite !linearZ /=; congr (_ *: _); rewrite linearB !Tau1Mu -scalerBr.
rewrite -!sumrB scaler_sumr linear_sum /=; apply: eq_bigr => i2 _.
suffices Dmu2_1 l: (mu2 i2 l) 1%g = mu l 1%g / #|L : K|%:R.
  by rewrite cDade_mu2_tau // !Dmu2_1 eq_jk.
rewrite -(Dade_Ind_chi PtypeL) mulrC cfInd1 ?mulKf ?neq0CiG //.
by rewrite (Dade_chiE PtypeL i2) cfResE.
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
  tau (delta j *: mu2 i j - delta j *: mu2 0 j - mu2 i 0 + mu2 0 0)
    = sigma(w_ i j) - sigma(w_ 0 j) - sigma(w_ i 0) + sigma(w_ 0 0).
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
    by rewrite defA0 inE -[w]conjg1 mem_class_support ?orbT //.
  rewrite cyclicTIsigma_restrict // AE !cfunE.
  have WiWdW2: w \in W :\: W2.
    by move: WiV; rewrite !inE => /andP []; rewrite negb_or=> /andP [_ ->].
  case: (Dade_mu2_restrict PtypeL) => HH _; rewrite !HH //.
  rewrite (Dade_delta0 PtypeL) expr0 !scale1r !cfunE !mulrA.
  by rewrite -signr_addb addbb !mul1r.
have CA := memc_acTIirr tiW i j.
rewrite !cyclicTIsigma_ind //.
move/cfun_onP: (cfInd_on WsG (CA))=> -> //.
rewrite cfunElock; case: pickP=> //= h.
rewrite {1}defA0 !inE /=.
case: (boolP (h \in class_support _ _)) => 
          [/imset2P [v l ViV LiL ->] | HinVl]; last first.
  by rewrite BE; move/cfun_onP: (cfInd_on WsL (CA))=> ->.
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
have VinA0 : v \in A0.
  by rewrite defA0 inE -[v]conjg1 mem_class_support ?orbT.
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
