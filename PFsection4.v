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
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

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
    by rewrite -oppr_sub cfunE oppr_eq0.
  have ab_sym e: ('[b - a, e] == 0) = ('[a - b, e] == 0).
    by rewrite -oppr_sub cfdotNl oppr_eq0.
  rewrite (IH b a c d u v) // 1?osym2 1?vc_sym ?ab_sym //=.
  rewrite -oppr_eq0 -cfdotNr oppr_sub in o_abcd.
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
  apply/eqP; have:= o_abcd; rewrite cfdotDl cfdotNl !raddf_sub /=.
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
rewrite !mulf_neq0 ?signr_eq0 // -(subrK a b) -oppr_sub addrCA 2!cfunE.
rewrite (eqP ab1) oppr0 add0r cfunE -mulr2n -mulr_natl mulf_eq0 -(eqN_eqC _ 0).
by rewrite /= def_a cfunE mulf_eq0 signr_eq0 /= irr1_neq0.
Qed.

Lemma orthonormal_vchar_diff_ortho (X : {group gT}) (a b c d : 'CF(X)) :
    {subset a :: b <= 'Z[irr X]} /\ {subset c :: d <= 'Z[irr X]} ->
    orthonormal (a :: b) && orthonormal (c :: d) ->
    [&& '[a - b, c - d] == 0, (a - b) 1%g == 0 & (c - d) 1%g == 0] ->
  '[a, c] = 0.
Proof.
move=> Zabcd Oabcd; rewrite -[c - d]scale1r scaler_subr.
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
  case: (bezoutl #|W1| (cardG_gt0 W2))=> u Hu /dvdnP [] v.
  move: Hcoprime; rewrite coprime_sym /coprime => /eqP-> HH.
  have F1 x2 y2 : (x2 \in W1 -> y2 \in W2 -> (x2 * y2) ^+ (v * #|W2|)%N = x2)%g.
    move=> X2iW Y2iW.
    have: commute x2 y2.
      case/dprodP: HdP=> _ _.
      by move/subsetP /(_ _ Y2iW) /centP /(_ _ X2iW) /commute_sym.
    move/expMgn=> ->.
    rewrite -{1}HH expgn_add expg1 mulnC [(v * _)%N]mulnC !expgn_mul.
    move/order_dvdG: X2iW=> /dvdnP=> [[k1 ->]].
    move/order_dvdG: Y2iW=> /dvdnP=> [[k2 ->]].
    by rewrite mulnC [(k2 * _)%N]mulnC !expgn_mul !expg_order !exp1gn !mulg1.
  by rewrite -(F1 _ _ X1iW Y1iW) -XYeX1Y1 -conjXg F1.
have : x ^ g \in L.
  rewrite groupJ // -[x]mul1g; case/sdprodP: SdP=> _ <- _ _.
  by apply/imset2P; exists (1%g : gT) x; rewrite //.
case/(mem_sdprod SdP)=> k1 [x2 [K1iK X2iW _ Hu]].
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

(* First part of 4.3 a *)
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

(* Second part of 4.3 a *)
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
Local Notation w_ := (cyclicTIirr cyclicTI_Dade).

Let odd_neq2 m : odd m -> (2 == m)%N = false.
Proof. by case: eqP => // <-. Qed.

Let W1xW2 : W1 \x W2 = W. Proof. by have [[]] := cyclicTI_Dade. Qed.
Let sW1W : W1 \subset W. Proof. by have [_ /mulG_sub[]] := dprodP W1xW2. Qed.
Let sW2W : W2 \subset W. Proof. by have [_ /mulG_sub[]] := dprodP W1xW2. Qed.
Let oddW : odd #|W|. Proof. by have [[]] := cyclicTI_Dade. Qed.
Let oddW1 : odd #|W1|. Proof. exact: oddSg oddW. Qed.

Definition ecTIirr i j := w_ i j - w_ 0 j.
Notation e_ := ecTIirr.

Definition ecTIirr_base := image (prod_curry e_) (setX [set~ ord0] setT).

Lemma ecTIirr_base_free : free ecTIirr_base.
Proof.
have FF  (HH : W1 \x W2 = W) i1 i2 j1 j2 :
    dprod_Iirr HH (i1,j1) == dprod_Iirr HH (i2, j2) = ((i1 == i2) && ((j1 == j2))).
  apply/eqP/andP=> [/dprod_Iirr_inj [] -> -> | [/eqP -> /eqP ->] //].
  by rewrite eqxx.
have PP i1 j1 i2 j2 : i1 != 0 -> i2 != 0 ->
   '[e_ i1 j1, w_ i2 j2] = ((i1 == i2) && (j1 == j2))%:R.
  move=> Di1 Di2; rewrite cfdot_subl !cfdot_irr !FF.
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
move/setIidPr: sW2W->.
by rewrite -{2}[#|W2|]mul1n -muln_subl subn1.
Qed.

Lemma memc_ecTIirr i j : e_ i j \in 'CF(W, W :\: W2).
Proof.
have linearX1 k : lin_char ('chi[W1]_k).
  by apply/char_abelianP; apply: cyclic_abelian; case: HC=> [].
apply/cfun_onP=> x; rewrite !inE negb_and negbK orbC.
have [Wx /=  XiW2 | /cfun0->//] := boolP (x \in W).
rewrite !cfunE /w_ !dprod_IirrE -[x]mul1g !cfDprodE //.
by rewrite  !(lin_char1 (linearX1 _)) subrr.
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

Definition Dade_mu (i : Iirr W1) (j : Iirr W2) : Iirr L := 
  Dade_mudelta.1 i j. 
Local Notation mu := Dade_mu.

Definition Dade_delta (i : Iirr W2) : bool := Dade_mudelta.2 i.
Local Notation delta := Dade_delta.

Lemma Dade_mudelta_spec :
        injective (prod_curry mu) /\
        forall i j,
       'Ind[L] (e_ i j) =
            (-1) ^+ (delta j) *: ('chi_(mu i j) - 'chi_(mu 0 j)).
Proof.
rewrite /Dade_mu /Dade_delta /Dade_mudelta; case: pickP=> /= [[mu delta]|].
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
  have linearX k : lin_char ('chi[W]_k).
    by apply/char_abelianP; apply: cyclic_abelian; case: HC=> [].
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
      by apply/injectiveP=> u v /chi_inj /dprod_Iirr_inj []. 
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
       have linearX k : lin_char ('chi[W]_k).
         by apply/char_abelianP; apply: cyclic_abelian; case: HC=> [].
       by rewrite cfInd1 //!cfunE !(lin_char1 (linearX _)) subrr mulr0 //.
     case: (HH j)=> _ /(_ i) ->.
     by rewrite cfunE (mulf_eq0) signr_eq0 /= => /eqP.
  rewrite !{1}scale1r !{1}F eqxx !andbT. 
  case: (HH j1)=> _ /(_ i1) /= Ii1j1; case: (HH j2)=> _ /(_ i2) /= Ii2j2.
  move: (TH _ _ (memc_ecTIirr i1 j1) (memc_ecTIirr i2 j2)).
  have->: '[e_ i1 j1, e_ i2 j2] = 0.
    by rewrite cfdot_subl 2!cfdot_subr !cfdot_cTIirr 
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

Lemma Dade_mu_injective : injective (prod_curry mu).
Proof. by case: Dade_mudelta_spec. Qed.

(* First part of 4.3 b *)
Lemma Dade_mu_ind :
        forall i j,
       'Ind[L] (e_ i j) =
            (-1) ^+ (delta j) *: ('chi_(mu i j) - 'chi_(mu 0 j)).
Proof. by case: Dade_mudelta_spec. Qed.
   
End CyclicDade.

Section CentralDade.

Section Definitions.

Variables (A G H L K W W1 W2 : {set gT}).

Definition centralDade_hypothesis (cH : cyclicTIhypothesis G W W1 W2) :=
  [/\ cyclicDade_hypothesis L K W W1 W2,
      [/\ H <| L , W2 \subset H & H \subset K]

   &  [/\ Dade_hypothesis G L A,
          Dade_hypothesis G L (A :|: class_support (cyclicTIset cH) L),
         \bigcup_(h \in H^#)('C_K[h]^#) \subset A
       &  A \subset K^#]].

End Definitions.

End CentralDade.

End Four.
