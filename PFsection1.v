(* (c) Copyright Microsoft Corporation and Inria. All rights reserved. *)
Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq path div choice.
Require Import fintype tuple finfun bigop prime ssralg poly finset center.
Require Import fingroup morphism perm automorphism quotient action zmodp.
Require Import matrix mxalgebra mxrepresentation cyclic.
Require Import vector algC classfun character inertia vcharacter.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Import GroupScope GRing.Theory.
Local Open Scope ring_scope.

(**************************************************************************)
(* This file contains the proof of Section1 of Peterfalvi's book          *)
(**************************************************************************)

Section Main.

Variable (gT : finGroupType).

(* This corresponds to 1.1 in PF *)
Lemma odd_eq_conj_irr1 (G : {group gT}) t :
  odd #|G| -> ((('xi[G]_t)^*)%CH == 'xi_t) = ('xi_t == '1_G).
Proof.
move=> OG; apply/eqP/eqP=> [Ht|->]; last first.
  by apply/ffunP=> g; rewrite ffunE cfuniE conjC_nat.
pose a := (@Zp1 1).
have Aito:
    is_action <[a]> (fun (t : Iirr G) v => if v == a then conj_idx t else t).
  split=> [[[|[]]] //= _  t1 t2 Hj |j [[|[]]] // HH1 [[|[]]] // HH2 ] //=.
    by apply: (inv_inj (@conj_idxK _ _)).
  by rewrite conj_idxK.
pose ito := Action Aito.
have Acto:
    is_action <[a]> (fun (c : {set gT}) v => if v == a then c^-1%g else c).
  split=> [[[|[]]] //= _  t1 t2 Hj |j [[|[]]] // HH1 [[|[]]] // HH2 ] //=.
    by rewrite -[t1]invgK Hj invgK.
  by rewrite invgK.
pose cto := Action Acto.
have F1: [acts <[a]>, on (classes G) | cto].
  apply/subsetP=> j Hj.
  rewrite !inE Hj; apply/subsetP=> u.
  case/imsetP=> g GiG ->.
  by rewrite inE /=; case: (_ == _) => //;
     rewrite -?classVg mem_classes // ?groupV.
have F2:  forall c (t : Iirr G),  c \in classes G ->
   'xi_t (repr c) = 'xi_(ito t a) (repr (cto c a)).
  move=> c t' CiG /=.
  rewrite conj_idxE cfun_conjCE /= -(invg_is_char _ (is_char_irr t')).
  case/imsetP: CiG=> g GiG ->; rewrite -classVg.
  case: (repr_class G g)=> h1 H1iG ->.
  case: (repr_class G g^-1)=> h2 H2iG ->.
  by rewrite conjVg invgK !(cfunJ _ (memc_irr _)).
have F3: forall c, c \in classes G -> c^-1%g = c -> c = 1%g.
  move=> c; case/imsetP => g GiG ->; rewrite -classVg => Hg.
  move: (class_refl G g^-1); rewrite Hg; case/imsetP=> x XiG Hx.
  have F4: (x ^+ 2)%g \in 'C_G[g].
    apply/subcent1P; split; rewrite ?groupM //.
    apply: (mulgI (x * x * g)^-1)%g.
    rewrite mulVg !invMg Hx conjgE !mulgA mulgK.
    rewrite -[(_ * g * x)%g]mulgA -[(_ * (g * _))%g]mulgA -conjgE.
    by rewrite -Hx mulgK mulVg.
  have F5 : x \in 'C_G[g].
    suff->: (x = (x ^+ 2) ^+ (#|G| %/2).+1)%g by apply: groupX.
    rewrite -expgn_mul -[(_%/_).+1]addn1 muln_addr muln1 -{3}addn1 addnA.
    move: (modn2 #|G|); rewrite {1}OG /= => HH; rewrite -{3}HH.
    rewrite [(2 * _)%N]mulnC -divn_eq expgn_add expg1.
    by move: (order_dvdG XiG); rewrite order_dvdn; move/eqP->; rewrite mul1g.
  move: Hx; rewrite conjgE; case/subcent1P: F5=> _ ->.
  rewrite mulgA mulVg mul1g => HH.
  have F6: (g ^+ 2 == 1)%g by rewrite expgS -{1}HH expg1 mulVg.
  suff: #[g] == 1%N by rewrite order_eq1; move/eqP->; apply: class1G.
  move: F6 (order_gt0 g) (order_dvdG GiG); rewrite -order_dvdn.
  move/(dvdn_leq (isT : (0 < 2)%N)); case: #[_]=> // [[|[]]] //.
  by rewrite dvdn2 OG.
apply/eqP; case: (boolP (t == 0))=> // Hd.
  by move/eqP: Hd->; rewrite cfuni_xi0.
move: (action_irr_class_card (cycle_id a) F1 F2).
have->: #|'Fix_(classes G | cto)[a]| = 1%N.
  apply: (@eq_card1 _ 1%g)=> c; apply/idP/idP; rewrite !inE.
    case/andP=> GiG HH; apply/eqP; apply: F3=> //; apply/eqP.
    by move/subsetP: HH; move/(_ a); rewrite !inE eqxx; apply.
  move/eqP->; rewrite classes1.
  apply/subsetP=> b; rewrite !inE; move/eqP=> -> /=.
  by rewrite invg1.
rewrite (cardD1 (0 : Iirr _)).
have->: 0 \in 'Fix_ito[a].
  apply/afixP=> b; rewrite !inE; move/eqP->; rewrite /=.
  apply: xi_inj; apply/ffunP=> g.
  by rewrite conj_idxE cfun_conjCE -cfuni_xi0 ffunE conjC_nat.
rewrite (cardD1 t) //.
suff->: t \in [predD1 'Fix_ito[a] & 0] by [].
rewrite inE /= Hd.
apply/afixP=> b; rewrite !inE; move/eqP->; rewrite /=.
apply: xi_inj; apply/ffunP=> g.
by rewrite conj_idxE Ht.
Qed.

Variable (G H : {group gT}).

(* This corresponds to 1.2 in PF *)
Lemma not_in_ker_char0 t g : g \in G ->
  H <| G -> ~(H \subset cker G 'xi[G]_t) -> 'C_H[g] = 1%g -> 'xi_t g = 0.
Proof.
move=> GiG HnG nHsC CH1.
have: (#|'C_G[g]| <= #|'C_(G/H)[coset H g]|)%N.
  suff->: #|'C_G[g]| = #|'C_G[g] / H|%G.
    by apply: (subset_leq_card (quotient_subcent1 H G g)).
  apply: card_isog.
  apply: isog_trans (second_isog _); last first.
    apply: subset_trans (normal_norm HnG).
    by apply: subcent1_sub.
  suff->: H :&: 'C_G[g] = 1%g by exact: quotient1_isog.
    rewrite -CH1.
    apply/setP=> h; rewrite inE.
    apply/andP/subcent1P; case=> H1 H2; split=> //.
      by move/subcent1P: H2; case.
    apply/subcent1P; split=> //.
    by apply: (subsetP (normal_sub HnG)).
have F1: coset H g \in (G / H)%g by exact: mem_quotient.
rewrite leq_leC.
move: (irr_second_orthogonal_relation GiG GiG).
rewrite class_refl=> <-.
move: (irr_second_orthogonal_relation F1 F1).
rewrite class_refl=> <-; rewrite sum_norm_quo //.
rewrite (bigID (fun i : Iirr G => H \subset cker G 'xi_i)) //=.
set S := \sum_(i | ~~ _) _; set S' := \sum_(i | _) _ => HH.
have F2: 0 = S.
  apply: leC_anti; last by rewrite -(leC_add2l S') addr0.
  by apply: posC_sum=> j _; rewrite /leC subr0; exact: repC_pconj.
apply/eqP;  have: 'xi_t g * ('xi_t g)^* == 0.
  apply/eqP; apply: (posC_sum_eq0 _ (sym_equal F2)).
    by move=> j _; rewrite /leC subr0; exact: repC_pconj.
  by move/negP: nHsC->; rewrite  /index_enum -enumT mem_enum.
rewrite mulf_eq0; case/orP=> //.
by rewrite conjC_eq0.
Qed.

Lemma memc_class_ortho (A : {set gT}) (u v : {cfun gT}) :
   u \in 'CF(H, A) -> v \in 'CF(H, H :\: A) -> '[u, v]_H = 0.
Proof.
rewrite !class_funE /=.
case/memv_sumP=> /= x_ [] Hx ->.
case/memv_sumP=> /= y_ [] Hy ->.
rewrite raddf_sum /=; apply: big1=> /= i Hi.
move: (Hy _ Hi); case/injvP=> ky ->; rewrite inner_prodZ.
rewrite -inner_prodbE linear_sum /= big1 ?mulr0 //= => j Hj.
move: (Hx _ Hj); case/injvP=> kx ->.
rewrite linearZ /= inner_prodbE inner_prod1.
suff: H :&: enum_val j :&: enum_val i = set0.
  move/eqP; rewrite -cards_eq0; move/eqP->.
  by rewrite mul0r scaler0.
apply/setP=> g; rewrite !inE.
case: (boolP (_ \in _))=> // GiG.
case: (boolP (_ \in _))=> // GiE.
case: (boolP (_ \in _))=> // GiE'.
move: (subsetP Hi); move/(_ _ GiE').
move: (subsetP Hj); move/(_ _ GiE).
by rewrite inE => ->.
Qed.

Lemma memc_class_compl (A : {set gT}) :
  A \subset H -> class_support A H = A ->
   ('CF(H, A) + 'CF(H, H :\: A)%SET)%VS = 'CF(H).
Proof.
move=> AsH ClAH.
rewrite [X in _ = X]class_funE.
rewrite (bigID (fun i : 'I_#|classes H| => enum_val i \subset A)) /=.
congr (_ + _)%VS; rewrite class_funE; apply: eq_bigl=> /= i.
  case: (boolP (_ \subset _))=> [HH|]; last by rewrite andbF.
  by apply: sym_equal; rewrite andbT; apply/idP; apply: subset_trans AsH.
apply/idP/andP=> [HH|].
  split; first by apply: subset_trans HH (subsetDl _ _).
  move: HH; have [y YiG ->] := imsetP (enum_valP i).
  move/subsetP; move/(_ _ (class_refl _ _)).
  rewrite inE YiG andbT=> HH; apply/negP=> HH1; case/negP: HH.
  by apply: (subsetP HH1); apply: class_refl.
have [y YiG ->] := imsetP (enum_valP i)=> [] [] HH1 HH2.
apply/subsetP=> g; case/imsetP=> h HiH ->.
rewrite inE groupJ // andbT.
apply/negP=> YHiA; case/negP: HH2.
apply/subsetP=> k; case/imsetP=> k1 K1iH ->.
rewrite -ClAH; apply/imset2P; exists (y^h) (h^-1 * k1)%g=> //.
  by rewrite groupM ?groupV.
by rewrite -conjgM mulgA mulgV mul1g.
Qed.

(* This PF 1.3a *)
Lemma equiv_restrict_compl (A : {set gT}) m (Phi : m.-tuple {cfun gT}) 
                           (mu : {cfun gT}) (d: Iirr H -> algC) :
  H \subset G -> A \subset H -> class_support A H = A ->
  is_basis 'CF(H,A) Phi ->   mu \in 'CF(G) -> 
  ('Res[A] mu == 'Res[A] (\sum_(i : Iirr H) (d i) *: 'xi_i)) =
  forallb j : 'I_m, 
   \sum_(i : Iirr H) '[Phi`_j, 'xi_i]_H * (d i)^* == '['Ind[G,H] Phi`_j, mu]_G.
Proof.
move=> HsG AsH CsA BP Cmu.
have CP : forall i: 'I_m, Phi`_ i \in 'CF(H,A).
  by move=> i; apply: (memv_is_basis BP _); apply: mem_nth; rewrite size_tuple.
rewrite -(crestrict_subset _ AsH).
pose D := 'Res[H] mu - \sum_(i < Nirr H) d i *: 'xi_i.
have CD: D \in 'CF(H).
  apply: memv_sub; first by apply: (memc_restrict HsG).
  by apply: memv_suml=> i _; apply: memvZl; apply: memc_irr.
set vL := _ == _.
set vR := forallb i, _.
have->: vL = (D \in 'CF(H, H :\: A)).
  rewrite memcE  // CD andbT /vL -subr_eq0 -linear_sub /= -/D.
  apply/eqP/subsetP=> [HH g| HH]; last first.
    apply/ffunP=> g; rewrite ffunE [_ 0 g]ffunE.
    move: (HH g); rewrite !inE.
    case: (boolP (D g == 0))=> [/eqP->|_]; first by rewrite mulr0.
    move/(_ is_true_true); case/andP.
    by rewrite ffunE; move/negPf->; rewrite mul0r.
  move/ffunP: HH; move/(_ g).
  rewrite !inE 2!ffunE.
  case: (_ \in _).
    by rewrite mul1r !ffunE => ->; rewrite eqxx.
  case/cfun_memP: CD; move/(_ g).
  by case: (_ \in _)=> //; move/(_ is_true_true)=> ->; rewrite eqxx.
have F0: forall j : 'I_m,
   (\sum_(i < Nirr H) '[Phi`_j, 'xi_i]_H * (d i)^* ==
   '['Ind[G, H] Phi`_j, mu]_G) = ('[Phi`_j, D]_H == 0).
  move=> j.
  rewrite raddf_sub raddf_sum /= (frobenius_reciprocity HsG) //; last first.
    by apply: memcW.
  rewrite subr_eq0 eq_sym; congr (_ == _)=> //.
  by apply: eq_bigr=> i _; rewrite inner_prodZ mulrC.
apply/idP/forallP=> [HH i| HH].
  by rewrite F0; apply/eqP; apply: memc_class_ortho.
have F1: forall j : 'I_m, '[Phi`_j, D]_H = 0.
  by move=> j; move: (HH j); rewrite F0; move/eqP.
move: CD F1; rewrite -(memc_class_compl AsH) //.
case/memv_addP=> /= f [g []] Cf Cg -> F1.
have: '[f, f + g]_H = 0.
  case/andP: BP.
  move/is_span_span; move/(_ _ Cf)=> {1}-> _.
  rewrite -inner_prodbE linear_sum /=; apply: big1=> /= i _.
  by rewrite linearZ /= inner_prodbE F1 scaler0.
rewrite raddfD /= {1}(memc_class_ortho Cf Cg).
rewrite addr0; move/eqP; rewrite  inner_prod0.
  by move/eqP->; rewrite add0r.
by apply: memcW Cf.
Qed.

(* This is PF 1.3b *)
Lemma equiv_restrict_compl_ortho (A : {set gT}) m 
          (Phi : m.-tuple {cfun gT}) (mu_: Iirr H -> {cfun gT}) :
  H \subset G -> A \subset H -> class_support A H = A ->
   is_basis 'CF(H,A) Phi -> 
   (forall i  : Iirr H, mu_ i \in 'CF(G)) ->
   (forall i j : Iirr H, '[mu_ i, mu_ j]_G = (i == j)%:R) ->
   (forall j,
     'Ind[G,H] Phi`_j = \sum_(i : Iirr H) '[Phi`_j, 'xi_i]_H *: mu_ i) ->
  (forall i : Iirr H, 'Res[A] (mu_ i) = 'Res[A] 'xi_i) /\
  (forall mu, mu \in 'CF(G) ->
     (forall i : Iirr H, '[mu, mu_ i]_G = 0) -> 'Res[A] mu = 0).
Proof.
move=> HsG AsH ClA BP Cm Mo IP; split=> [/= i| mu Cmu Om].
  have->: 'xi_i = \sum_(j : Iirr H) ((fun j => (j==i)%:R) j) *: 'xi_j.
    rewrite (bigD1 i) //= eqxx scale1r big1 ?addr0 // => j /negPf->.
    by rewrite scale0r.
  apply/eqP; rewrite (equiv_restrict_compl _ _ _ _ BP) //.
  apply/forallP=> /= j; rewrite IP.
  rewrite (bigD1 i) //= eqxx conjC_nat mulr1.
  rewrite big1 ?addr0=> [|/= k]; last first.
    by move/negPf->; rewrite conjC0 mulr0.
  rewrite -[X in _==X]inner_prodbE linear_sum.
  rewrite (bigD1 i) //= big1 ?addr0 => [|/= k KdI]; 
          rewrite linearZ /= inner_prodbE Mo.
    by rewrite eqxx [_ *: _]mulr1.
  by rewrite (negPf KdI) scaler0.
have->: 0 = 'Res[A] (\sum_(j : Iirr H) 0 *: 'xi_j).
  by rewrite big1 // => *; rewrite ?linear0 // scale0r.
apply/eqP; rewrite (equiv_restrict_compl (fun j => 0) _ _ _ BP) //.
apply/forallP=> /= i.
rewrite big1=> [|j _]; last by rewrite conjC0 mulr0.
rewrite IP -inner_prodbE linear_sum big1 //= => j _.
by rewrite linearZ  /= inner_prodbE ['[_, _]_G]inner_conj Om conjC0 scaler0.
Qed.

Let vchar_isometry_base2 f : f \in 'Z[irr G, G^#] -> '[f]_G = 2%:R ->
   exists e1, exists e2, (f = 'xi[G]_e1 - 'xi[G]_e2) /\ e2 != e1.
Proof.
move=> Hf.
rewrite (inner_prod_vchar Hf) //.
move/memc_vchar: (Hf)=>/memcW F1.
move=> HH.
pose h (t : Iirr G) := getNatC `|'[f, 'xi_t]_G|.
have Hh t: (h t)%:R = `|'[f, 'xi_t]_G|.
  exact/esym/eqP/normCZ_nat/(isZC_inner_prod_vchar t Hf).
have: (\sum_t (h t) * h t = 2)%N.
  apply/eqP; rewrite eqN_eqC -HH natr_sum; apply/eqP.
  apply: eq_bigr=> i _; rewrite natr_mul Hh -expr2 int_normCK //.
  exact: (isZC_inner_prod_vchar _ Hf).
case: (boolP (forallb i : Iirr G, '[f, 'xi_i]_G == 0)).
  move/forallP=> {HH}HH.
  rewrite big1=> // i _.
  apply/eqP; rewrite eqN_eqC natr_mul Hh.
  by rewrite (eqP (HH i)) normC0 mul0r.
rewrite negb_forall; case/existsP=> /= e1 He1.
rewrite (bigD1 e1) //=.
case E1: (h e1)=> [|[|k]] //; first 2 last.
  - by rewrite !mulnS addnA !addnS.
  - by move/eqP: E1; rewrite eqN_eqC Hh normC_eq0 (negPf He1).
case: (boolP (forallb i, (i == e1) || ('[f, 'xi_i]_G == 0))).
  move/forallP=> {HH}HH.
  rewrite big1=> // i Hi.
  apply/eqP; rewrite eqN_eqC natr_mul Hh.
  move: (HH i); rewrite (negPf Hi) /=; move/eqP->.
  by rewrite normC0 mul0r.
rewrite negb_forall; case/existsP=> /= e2; rewrite negb_or.
case/andP=> Hd He2.
rewrite (bigD1 e2) //=.
case E2: (h e2)=> [|[|k]] //.
  by move/eqP: E2; rewrite eqN_eqC Hh normC_eq0 (negPf He2).
do 2 move/addnI; move/eqP; rewrite sum_nat_eq0.
move/forall_inP=> HH1.
have: f 1%g = 0.
  case/and3P: Hf=> _ _; move/off_support; apply.
  by rewrite !inE eqxx.
have Hfc: f = '[f, 'xi_e1]_G *: 'xi_e1 + '[f, 'xi_e2]_G *: 'xi_e2.
  rewrite -{1}(sum_inner_prodE F1) (bigD1 e1) //; congr (_ + _).
  rewrite (bigD1 e2) // big1 /= ?addr0 // => i Hi.
  case Ei: (h i) (HH1 _ Hi)=> // _.
  by move/eqP: Ei; rewrite eqN_eqC Hh normC_eq0; move/eqP->; rewrite scale0r.
rewrite Hfc ffunE [_ 1%g]ffunE [(_ (_ *: _)) 1%g]ffunE.
have /andP[/negP F _]: 0 < 'xi_e1 1%g + 'xi_e2 1%g.
  apply: sposC_addl; try apply: ltCW; apply/andP; split;
     try exact:irr1_neq0; rewrite irr1_degree ; apply: posC_nat.
rewrite (isZC_signE (isZC_inner_prod_vchar e1 Hf)) -Hh E1 mulr1 !scaler_sign.
rewrite (isZC_signE (isZC_inner_prod_vchar e2 Hf)) -Hh E2 mulr1 !scaler_sign.
move/eqP; do 2![case: ifP => _] => //; last by exists e1, e2.
  by rewrite -oppr_add oppr_eq0.
by exists e2, e1; rewrite addrC eq_sym.
Qed.

Let vchar_isometry_base3 f f' : 
  f \in 'Z[irr G, G^#] -> '[f]_G = 2%:R ->
  f' \in 'Z[irr G, G^#] -> '[f']_G = 2%:R ->
  '[f, f']_G = 1%:R ->
   exists es, 
   exists epsilon : bool,
     [/\  f = (-1) ^+ epsilon *: ('xi[G]_es.1.1 - 'xi[G]_es.2),
          f' = (-1) ^+ epsilon *: ('xi[G]_es.1.2 - 'xi[G]_es.2),
          es.1.1 != es.2, es.1.2 != es.2 & es.1.1 != es.1.2].
Proof.
move=> Hf H2f Hf1 H2f1.
case/(vchar_isometry_base2 Hf): ( H2f) => e1 [e2] [-> Hn21].
case/(vchar_isometry_base2 Hf1):(H2f1)=> e3 [e4] [] ->;rewrite eq_sym=> H43.
rewrite raddf_sub /= -!inner_prodbE !linear_sub /= !inner_prodbE.
rewrite !irr_orthonormal.
case eqP=>[->|/eqP H13];  case eqP=>[->|/eqP H23];rewrite ?(negPf H43);
    try case eqP=>[->|/eqP H14];try case eqP=>[->|/eqP H24];move/eqP;
    rewrite ?(subrr,sub0r,subr0) -?(eqN_eqC 0) -?(eqN_eqC 1)//.
- by rewrite opprK -natr_add -eqN_eqC.
- exists (e2,e4,e3); exists true; rewrite expr1 !scaleNr !scale1r !oppr_sub /=.
   by rewrite H23 H14 eq_sym H43.
 (*- by rewrite eq_sym -subr_eq0 opprK -natr_add -(eqN_eqC _ 0).*)
- by rewrite eq_sym -subr_eq0 oppr_sub opprK -!natr_add -(eqN_eqC _ 0).
- by rewrite eq_sym -subr_eq0 opprK -natr_add -(eqN_eqC _ 0).
- by rewrite eq_sym -subr_eq0 opprK -natr_add -(eqN_eqC _ 0).
by exists (e1,e3,e4); exists false; rewrite expr0 !scale1r  H43 H14  H13.
Qed.

Let  vchar_isometry_base4 (eps : bool) i j k n m 
             (f1 :=  ('xi[G]_j - 'xi[G]_i))
             (f2 :=  ('xi[G]_k - 'xi[G]_i))
             (f3 := 'xi[G]_n - 'xi[G]_m) :
  j != k -> j != i -> k != i -> n != m ->
 '[f3, f1]_G = (-1) ^+ eps -> '[f3, f2]_G = (-1) ^+ eps -> 
  if eps then n == i else m == i.
Proof.
move=> Hjk Hij Hik Hnm.   
rewrite /f1 /f2 /f3 !raddf_sub /= -!inner_prodbE !linear_sub /= !inner_prodbE.
rewrite !irr_orthonormal.
have H0: 0 <> (-(1%:R))^+eps :> algC. 
  case: eps.
   by move/eqP;rewrite eq_sym oppr_eq0 -(eqN_eqC 1 0).
   by move/eqP; rewrite -(eqN_eqC 0 1). 
have H1: true%:R + true%:R <> (1 *- 1) ^+ eps :> algC.
  rewrite -natr_add; case: {H0} eps => //. 
    by move/eqP;  rewrite -subr_eq0 opprK  -natr_add -(eqN_eqC _ 0).
  by move/eqP; rewrite -(eqN_eqC _ 1).
have H2: 1 *- 1 <> 1 :> algC.
  by move/eqP; rewrite eq_sym -subr_eq0 opprK -(natr_add _ 1%N) -(eqN_eqC _ 0).
have H3: 1 *- 1 - 1 <> -1 :> algC.
  move/eqP;rewrite -[X in _ == X]addr0;move/eqP; move/addrI.
  by move/eqP; rewrite oppr_eq0 -(eqN_eqC 1 0).
move=> HH HH1; move: Hnm Hik Hij Hjk; move: (HH); rewrite -{1}HH1; move: HH HH1.
do 6 (try (case: (boolP (_ == _)); [move/eqP->| move=> HH HH1 HH2 HH3; 
      move: HH1 HH2 HH3 HH];
      rewrite ?(eqxx,subrr,subr0,sub0r,opprK, raddf0, add0r, addr0) //=)).
  + by move=> _ _; move/(@sym_equal _ _ _).
  + by move=> _ _; move/(@sym_equal _ _ _).
  + by case: {H0 H1} eps .
by case: {H0 H1} eps; move/(@sym_equal _ _ _).
Qed.

(* This is PF 1.4 *)
Lemma vchar_isometry_base m (Chi : m.-tuple {cfun gT}) 
                            (tau : 'End({cfun gT})) (chi1 := Chi`_0) :
    (1 < m)%N -> 
    {subset Chi <= irr H} -> free Chi ->
    (forall chi, chi \in Chi -> chi 1%g = chi1 1%g) ->
    {in 'Z[Chi, H^#], forall f, tau f \in 'Z[irr G, G^#]} ->
    {in 'Z[Chi, H^#] &, forall f1 f2, '[tau f1, tau f2]_G = '[f1, f2]_H} ->
    exists mu : {cfun gT} -> Iirr G,
    exists epsilon : bool,
    (forall i : 'I_m,
        tau (Chi`_i - chi1) =
          (-1) ^+ epsilon *: ('xi_(mu (Chi`_i)) - 'xi_(mu chi1))) /\
      (forall i j : 'I_m, (mu Chi`_i == mu Chi`_j) == (i == j)).
Proof. 
rewrite {}/chi1; move: m Chi tau.
do 2 (case=> //); move=> m Chi tau _ SubC HF Chi1 Htau Hiso.
pose F (i j: 'I_m.+2):= Chi`_i - Chi`_j.
pose tp := is_true_true.
have in_chi: forall i:'I_m.+2, Chi`_i \in Chi.
  by move=> i;rewrite mem_nth // size_tuple.
have Chi_irr: forall i:'I_m.+2, Chi`_i \in irr H by move=>i;apply:SubC.
have FID: forall  i j:'I_m.+2, (F i j) \in 'Z[Chi, H^#].
  move=> i j; rewrite vchar_split; apply/andP; split.
    by apply:vchar_sub;
       apply: memv_vchar=> //; apply/subsetP=> x; rewrite !inE. 
  apply/subsetP=> g; rewrite !inE; apply:contraR.
  rewrite negb_and negbK; case/orP=>[| HH].
    by move/eqP->; rewrite /F !ffunE !Chi1 // subrr. 
  by rewrite /F !ffunE !(cfun0 _ HH) ?subrr //;
   [case/irrIP: (Chi_irr j) | case/irrIP: (Chi_irr i)]=> x <-; rewrite memc_irr.
have htau2 : forall i j : 'I_m.+2, Chi`_i != Chi`_j-> '[tau (F i j)]_G = 2%:R.
  move=> i j Hchij;  rewrite Hiso //.
  rewrite /F !raddf_sub /= -!inner_prodbE !linear_sub /= !inner_prodbE.
  move: Hchij; case/irrIP: (Chi_irr j)=> x <-; case/irrIP: (Chi_irr i)=> y <-.
  rewrite !irr_orthonormal !eqxx.
  move=> Hxij; rewrite eq_sym; case: (boolP (_ == _)).
    by move/eqP=> he; case/eqP : Hxij; rewrite he.
  by rewrite subr0 sub0r opprK -natr_add.
have htau1 (i j : 'I_m.+2) : Chi`_j != Chi`_0 -> Chi`_j != Chi`_i ->
            Chi`_i != Chi`_0 -> '[tau (F i 0), tau (F j 0)]_G = 1%:R.
  rewrite Hiso // /F !raddf_sub.
  case/irrIP: (Chi_irr 0)=> x1 <-; case/irrIP: (Chi_irr i)=> xi <-;
   case/irrIP: (Chi_irr j) => xj <-.
  rewrite /= -!inner_prodbE !linear_sub /= !inner_prodbE.
  rewrite !irr_orthonormal !eqxx.
  move=> Hxj1 Hxji Hxi1;rewrite eq_sym;case:(boolP (_ == _)).
    by move/eqP=> he;case/eqP: Hxji;rewrite he.
  move=> _ ; rewrite eq_sym;case:(boolP (_ == _)).
    by move/eqP=> he; case/eqP : Hxj1;rewrite he.
  move=> _ ;case:(boolP (_ == _)).
    by move/eqP=> he; case/eqP : Hxi1;rewrite he.
  by rewrite /= subr0 !sub0r opprK.
have HChi_ij: forall i j: 'I_m.+2, i != j -> Chi`_i != Chi`_j.
  by move=> i j;case: (boolP (_ == _));
     rewrite nth_uniq ?(size_tuple,(uniq_free HF)).
case: (boolP (m == 0%N)).
  move: (htau2 1 0 (HChi_ij 1 0 tp));
   case/(vchar_isometry_base2 (Htau _ (FID 1 0)))=> e2 [e1 [Ht Hn12]].
  pose mu x:= if x == Chi`_0 then e1 else if x == Chi`_1 then e2 else 0.
  exists mu; exists false => /=.
  have HFi (i : 'I_m.+2) :
    tau (Chi`_i - Chi`_0) = (-1) ^+ 0 *: ('xi_(mu Chi`_i) - 'xi_(mu Chi`_0)).
    move: i; (do 2 case=> //)=> [|[]] //.
    + by move=> i; rewrite /mu eqxx !subrr linear0 expr0 scale1r.
    + move => i; rewrite /mu !eqxx  expr0 scale1r.
      case :(boolP (Chi`_(Ordinal i) == Chi`_0)); last by rewrite -Ht.
      by move/eqP ->;rewrite !subrr linear0.
    by move => n Hn /=; rewrite  (eqP p) in Hn.
  split => //.
    move=> i j;case: (boolP (i  == j)); first by move/eqP ->; rewrite eqxx.
    move => Hij; case e : (mu Chi`_i == mu Chi`_j)=> //.
  have: (mu Chi`_i == mu Chi`_j) by rewrite e.
  move/eqP => Hmuij {e}; move:(HFi i) (HFi j); rewrite !Hmuij => <-.
  rewrite !linear_sub;move/addIr => /= /eqP; rewrite -subr_eq0 -linear_sub /=.
  move/eqP=> Htij; move: (HChi_ij _ _ Hij); rewrite eq_sym; move/(htau2 j i ).
  by rewrite Htij raddf0; move/eqP; rewrite -(eqN_eqC 0).
move => mneq0.
have mgt0: (2 < m.+2)%N by move: mneq0; case: (m).
pose O2 := (Ordinal mgt0).
case: (@vchar_isometry_base3 (tau (F 1 0))(tau (F O2 0))).
  + by apply: (Htau _ (FID 1 0)).
  + by apply:(htau2 1); apply:(HChi_ij _ 0).
  + by apply:Htau; apply: (FID O2). 
  + by apply: (htau2 O2); apply: (HChi_ij _ 0).
  + rewrite Hiso; last by apply: (FID O2).
    move: (HChi_ij 1 0 tp)(HChi_ij O2 0 tp)(HChi_ij O2 1 tp).
    rewrite /F; case/irrIP: (Chi_irr 0) => e0 <-.
    case/irrIP: (Chi_irr 1)=> e1 <-; case/irrIP: (Chi_irr O2)=> e2 <-.
    rewrite !raddf_sub  /= -!inner_prodbE !linear_sub /= !inner_prodbE.
    rewrite !irr_orthonormal !eqxx.
    move=> Hxi2 Hxi1 Hxi3; rewrite eq_sym; case:(boolP (_ == _)).
      by move/eqP=> he; move:Hxi3; rewrite he; move/eqP.
    move => H21'; rewrite eq_sym; case:(boolP (_ == _)).
      by move/eqP=> he20; move:Hxi1; rewrite he20; move/eqP.
    move=> _; case:(boolP (_ == _)).
      by move/eqP=> he10; move:Hxi2; rewrite he10; move/eqP.
    by move=> _; rewrite subr0 !sub0r opprK. 
  by apply: (FID 1).
move=>x [] eps.
set e1:= x.2; set e2 := x.1.1; set e3 := x.1.2; move=> [H1_0 H2_0 H21 H31 H23].
have HFti: forall i:'I_m.+2, exists mun : (Iirr G), 
    tau (Chi`_i - Chi`_0) = (1 *- 1) ^+ eps *:('xi_mun - 'xi_e1) /\
    ((mun == e1) == ( i == 0)).
  move=> i; case: (boolP (i == 0)).
    move/eqP->; exists e1.
    by rewrite linear_sub !subrr scaler0 eqxx.
  move=> neqi0; case: (htau2 i 0 ( HChi_ij _ _ neqi0)).
  case/(vchar_isometry_base2 (Htau _ (FID i 0)))=> mum[mun [HFi1']].
  rewrite eq_sym => Hmn.
  case: (boolP (i == 1)); first by move/eqP->; exists e2;
                                 rewrite (negPf H21) eqxx;split.
  move=> neqi1.
  case: (boolP (i == O2)); first by move/eqP->;  exists e3;
                           rewrite (negPf H31) eqxx;split.
  move=> neqi2.
  move:(@vchar_isometry_base4 eps e1 e2 e3 mum mun H23 H21 H31 Hmn).
  move: (htau1 i 1  (HChi_ij 1 0 tp ) ); rewrite eq_sym => H1.
  have Hips: forall (x y : {cfun gT}) (e : bool) , 
              '[x, (1 *- 1) ^+ e *: y]_G =  (1 *- 1) ^+ e* '[x, y]_G.
    move => x0 y e; rewrite inner_prodZ;congr (_ *_); rewrite isZC_conj //. 
    by case: e;rewrite ?(expr1,expr0) -?mulNrn ?(mulr1n,isZC_opp,(isZC_nat 1)).
  have Hinv1 : forall e : bool, (1 *- 1) ^+ e * ( 1 *- 1) ^+ e = 1.
   by move=> T e;
    case: e; rewrite ?(expr1,expr0)-?mulNrn ?(mulr1n ,mulrN,mulNr,opprK,mulr1).
  move: (H1 (HChi_ij i 1 neqi1) (HChi_ij i 0 neqi0)).
  have : ('xi_e2 - 'xi_e1) = 
        ((1 *- 1) ^+ eps) *: ((( 1 *- 1) ^+ eps) *: ('xi_e2 - 'xi_e1)).
    by rewrite scalerA Hinv1 scale1r.
  move  => ->;rewrite Hips  -HFi1' -H1_0  => ->; rewrite !mulr1 => Ho.
  have Hif: if eps then mum == e1 else mun == e1.
    apply: Ho => //.
    have ->: ('xi_e3 - 'xi_e1) = 
             ((1 *- 1) ^+ eps) *: ((( 1 *- 1) ^+ eps) *: ('xi_e3 - 'xi_e1)).
      by rewrite scalerA Hinv1 scale1r.
    rewrite Hips -H2_0; move: (htau1 i O2 (HChi_ij O2 0 tp )).
    rewrite eq_sym => H2.
    rewrite (H2 (HChi_ij _ _ neqi2) (HChi_ij _ _ neqi0));rewrite ?mulr1 //.
  pose mui := if eps then mun  else mum; exists mui.
  rewrite HFi1' /mui {H1_0 H2_0 mui Ho }.
  case: eps Hif => /eqP Hif.
    rewrite expr1  -mulNrn mulr1n scaleNr scale1r oppr_sub Hif; split => //.
    by rewrite -Hif (eq_sym mun)  (negPf Hmn).
  by rewrite expr0 scale1r Hif;split; rewrite // -Hif  (negPf Hmn).
pose mu  := (fun f : {cfun gT}=> 
            odflt e1 (pick (fun mun : Iirr G =>  
                   (tau (f - Chi`_0) == (1 *- 1) ^+ eps *:('xi_mun - 'xi_e1))))).
exists mu;exists eps.
have HFi1: (forall i : 'I_m.+2,
    tau (Chi`_i - Chi`_0) = (-1) ^+ eps *: ('xi_(mu Chi`_i) - 'xi_(mu Chi`_0))).
  move=> i;case: (HFti i)=> xi;rewrite -mulNrn; case => Hxi Heq.
  suff -> : (mu Chi`_i) = xi.
    suff -> : (mu Chi`_0) = e1 by done.
  rewrite /mu;case:pickP; last by done.
  move=> x0; rewrite subrr linear0 /=.
  case : (boolP (x0 == e1)); first by  move/eqP->.
  move => H01;rewrite eq_sym scaler_eq0; case/orP; last first.
    + by rewrite subr_eq0; move/eqP; move/xi_inj.
    + case: (eps); last by rewrite expr0 oner_eq0.
      by rewrite expr1 -mulNrn mulr1n oppr_eq0 oner_eq0.
  rewrite /mu;  case :pickP; last by move/(_ xi); rewrite Hxi eqxx.
  move=> x0; case : (boolP (x0 == xi));first  by move/eqP->.
  move => H01; rewrite Hxi -subr_eq0 -scaler_subr scaler_eq0 /=;case/orP.
    clear;case: eps; last by rewrite expr0 oner_eq0.
    by rewrite expr1 mulr1n oppr_eq0 oner_eq0.
  by rewrite subr_eq0; move/eqP/addIr/xi_inj.
split => //.
move=> i j; case: (boolP (i  == j)); first by move/eqP ->; rewrite eqxx.
move => Hij; case: (boolP (mu Chi`_i == mu Chi`_j))=> //.
move/eqP=> Hmuij; move:(HFi1 i) (HFi1 j); rewrite !Hmuij=> <-.
rewrite !linear_sub; move/addIr => /=; move/eqP.
rewrite -subr_eq0 -linear_sub /=.
move/eqP=> Htji; rewrite eq_sym in Hij.
move: (htau2 j  i (HChi_ij _ _  Hij)); rewrite Htji. 
by rewrite raddf0; move/eqP; rewrite  -(eqN_eqC 0).
Qed.

(* This is PF 1.5(a) *)
Lemma induced_sum_rcosets t :  H <| G ->
  'Res[H] ('Ind[G,H] 'xi[H]_t) = 
     #|('I_G['xi_t])%CH : H|%:R *: \sum_(f <- cconjugates G 'xi_t) f.
Proof.
move=> HnG; apply/ffunP=> h.
pose GI := ([group of 'I_G['xi_t]])%CH.
rewrite big_map big_filter.
case: (boolP (h \in H))=> [HiH|HniH]; last first.
  rewrite ffunE cfuniE (negPf HniH) mul0r ffunE sum_ffunE ffunE.
  rewrite big1 ?(scaler0,ffunE,mulr0) // => C1.
  case/rcosetsP=> h1 H1iG ->.
  have RiG: repr (GI :* h1) \in G.
    case: (repr_rcosetP GI h1)=> g GiI.
    by rewrite groupM // (subsetP (inertia_sub G 'xi_t)).
  by rewrite -(irr_conjE _ HnG RiG) (cfun0 _ HniH) // memc_irr.
rewrite crestrictE // !(sum_ffunE,ffunE).
apply: (mulfI (neq0GC H)); rewrite !mulrA divff ?(neq0GC H) // mul1r.
rewrite -natr_mul LaGrange ?(subset_inertia, memc_irr) //.
rewrite -mulr_sumr.
rewrite (reindex invg) /=; last by exists invg=> g; rewrite invgK.
rewrite (eq_bigr (fun j => ('xi_t ^ j)%CH h)); last first.
  by move=> g Hg; rewrite cfun_conjE.
have F1: forall g : gT, g^-1%g \in G -> 
  ('I_G['xi_t])%CH :* g \in rcosets ('I_G['xi_t]) G.
  move=> g; rewrite groupV // => GiG; apply/imsetP; exists g=> //.
  by rewrite rcosetE.
rewrite {1}(partition_big _  _ F1) /=.
apply: eq_bigr=> N; case/imsetP=> x XiG ->.
set a := repr _.
rewrite (eq_bigr (fun _ => ('xi_t ^ a)%CH h)); last first.
  move=> i1; case/andP; rewrite groupV /a // => Hi1; move/eqP=> <-.
  suff: ('xi_t ^ i1 == 'xi_t ^ (repr ('I_G['xi_t] :* i1)))%CH by move/eqP<-.
  rewrite (cfun_conj_eqE _ Hi1) ?mem_repr_rcoset //.
  have: ('I_G['xi_t])%CH :* i1 \subset G.
    apply/subsetP=> g; case/imset2P=> h1 h2;rewrite !inE.
    by case/andP=> H1iG _ Eh2 ->; rewrite groupM // (eqP Eh2).
  by move/subsetP; apply; apply: (mem_repr_rcoset [group of 'I_G['xi_t]] i1).
rewrite -(card_rcoset _ x) -sum1_card natr_sum -!mulr_suml.
apply: eq_big=> [i1|i1]; last by rewrite mul1r.
rewrite rcosetE; apply/andP/idP=>[|HH]; last first.
  split; last by apply/eqP; apply: rcoset_transl.
  case/rcosetP: HH=> h1 H1iI ->; rewrite groupV groupM //.
  by apply: (subsetP (inertia_sub G 'xi_t)).
case=> I1iG; move/eqP<-; apply/rcosetP.
by exists 1%g; rewrite ?mul1g // ?(group1 [group of 'I_G[t]]).
Qed.

(*  This 1.5b *)
Lemma induced_prod_index t :
  H <| G -> '['Ind[G,H] 'xi[H]_t]_G = #|('I_G['xi_t])%CH : H|%:R.
Proof.
move=> HnG; have CFi := memc_irr t; have HsG := normal_sub HnG.
rewrite -frobenius_reciprocity ?memc_induced //.
have->: '['xi_t, 'Res[H] ('Ind[G,H] 'xi_t)]_H =
  #|('I_G['xi_t])%CH : H|%:R * '['xi_t, (\sum_(f <- cconjugates G 'xi_t) f)]_H.
 rewrite !inner_prodE mulrA [_%:R * _]mulrC -mulrA -[_%:R * _]mulr_sumr.
 congr (_ * _); apply: eq_bigr=> h HiH.
 rewrite mulrA [_%:R * _]mulrC -mulrA; congr (_ * _).
 by rewrite (induced_sum_rcosets _ HnG) // !ffunE rmorphM conjC_nat.
rewrite big_map big_filter.
rewrite raddf_sum (bigD1 ('I_G['xi_t] :* 1%g)%CH) /=; last first.
  by apply/rcosetsP; exists 1%g; rewrite ?group1.
have F1: repr ('I_G['xi_t] :* 1) \in 'I_G['xi_t].
  by rewrite -{2}[('I_(_)[_])%CH]rcoset1 mem_repr_rcoset.
rewrite big1 ?addr0=> [|j].
  by rewrite (is_irr_inner _ HnG) ?(F1,mulr1,subsetP (inertia_sub G 'xi_t)).
case/andP; case/rcosetsP=> g GiG -> Heq.
rewrite (is_irr_inner _ HnG); last first.
  have: ('I_G['xi_t] :* g \subset G)%CH.
    apply/subsetP=> h; case/rcosetP=> k KiI ->.
    by rewrite groupM // (subsetP (inertia_sub G 'xi_t)).
  by move/subsetP; apply; apply: mem_repr_rcoset.
case E1: (_ \in _)=> //; case/eqP: Heq.
rewrite rcoset1 rcoset_id //.
have: repr ([group of 'I_G['xi_t]] :* g) \in 'I_G['xi_t]%CH by [].
by case: repr_rcosetP=> h HiI HGiH; rewrite -(groupMl _ HiI).
Qed.

(*  This 1.5c *)
Lemma cconjugates_irr_induced t1 t2 : H <| G ->
    if 'xi[H]_t2 \in cconjugates G 'xi[H]_t1
    then 'Ind[G,H] 'xi_t1 = 'Ind[G,H] 'xi_t2 
    else '['Ind[G,H] 'xi_t1, 'Ind[G,H] 'xi_t2]_G = 0.
Proof.
move=> HnG; case: (boolP (_ \in _))=> [IC|NiC].
  by apply: cconjugates_induced=> //; exact: memc_irr.
rewrite -frobenius_reciprocity 
        ?(normal_sub HnG,memc_irr,memc_induced) //.
rewrite (induced_sum_rcosets _ HnG) inner_prodZ raddf_sum.
rewrite big_map big_filter big1 ?mulr0 //=.
move=> C1 HC1.
have RiG: repr C1 \in G.
  case/rcosetsP: HC1=> g GiG ->.
  have: ('I_G['xi_t2])%CH :* g \subset G.
    apply/subsetP=> h; case/rcosetP=> k KiI ->.
    by rewrite groupM // (subsetP (inertia_sub G 'xi_t2)).
  by move/subsetP; apply; apply: mem_repr_rcoset.
move: (irr_orthonormal t1 (irr_conj t2 (repr C1))).
rewrite (irr_conjE _ HnG) // => ->.
case: eqP=> // HH; case/negP: NiC; rewrite HH.
apply/cconjugatesP; exists (repr C1)^-1%g; rewrite ?groupV //.
by rewrite (irr_conjE _ HnG) // -cfun_conjM mulgV cfun_conj1.
Qed.

(* This is PF 1.5(d) *)
Lemma induced_sum_rcosets1 t : H <| G ->
  let chi := 'Ind[G,H] 'xi[H]_t in
  (chi 1%g / '[chi]_G) *: 'Res[H] chi  = #|G : H|%:R *:
       (\sum_(f <- cconjugates G 'xi_t) f 1%g *: f).
Proof.
move=> HnG chi.
rewrite (induced_sum_rcosets _ HnG) (induced_prod_index _ HnG) 
        cinduced1 ?(normal_sub) //.
rewrite !scalerA -!mulrA mulVf ?(mulr1); last first.
  rewrite -neq0N_neqC; move: (indexg_gt0 (inertia_group G 'xi_t) H)=> /=.
  by case: #|_:_|.
rewrite-scalerA scaler_sumr; congr (_ *: _).
rewrite !big_map !big_filter; apply: eq_bigr=> C1 IC1.
by rewrite cfun_conj_val1.
Qed.

(* This is PF 1.5(e) *)
Lemma odd_induced_orthogonal t : H <| G -> odd #|G| -> 
  t != 0 -> '['Ind[G,H] 'xi[H]_t, ('Ind[G,H] 'xi_t)^*%CH]_G = 0. 
Proof.
move=> HnG OG Dii1.
move: (cconjugates_irr_induced t (conj_idx t) HnG).
case: (boolP (_ \in _)); last first.
  rewrite cinduced_conjC => _ <-.
  rewrite !inner_prodE; congr (_ * _); apply: eq_bigr=> g GiG.
  by rewrite conj_idxE.
case/cconjugatesP=> g GiG; rewrite conj_idxE=> HH.
have OH: odd #|H|.
  by apply: (dvdn_odd _ OG); apply: cardSg; apply: normal_sub.
case/eqP: Dii1; apply: xi_inj; rewrite -cfuni_xi0; apply/eqP.
rewrite -odd_eq_conj_irr1 // HH.
have F1: ('xi_t ^ (g ^+ 2))%CH = 'xi_t.
  by rewrite cfun_conjM -HH -cfun_conj_conjC -HH cfun_conjCK.
suff->: g = ((g ^+ 2)^+ (#|G| %/2).+1)%g.
  elim: (_ %/2).+1=> [|n IH]; first by rewrite expg0 cfun_conj1.
  by rewrite expgS cfun_conjM F1.
rewrite -expgn_mul -[(_%/_).+1]addn1 muln_addr muln1 -{3}addn1 addnA.
move: (modn2 #|G|); rewrite {1}OG /= => HH1; rewrite -{3}HH1.
rewrite [(2 * _)%N]mulnC -divn_eq expgn_add expg1.
by move: (order_dvdG GiG); rewrite order_dvdn; move/eqP->; rewrite mul1g.
Qed.

(* This is PF 1.6a *)
Lemma cker_induced_irr_sub (A : {group gT}) t :
  H <| G -> A <| G -> A \subset H ->
  (A \subset cker H 'xi[H]_t) = (A \subset cker G ('Ind[G,H] 'xi_t)).
Proof.
move=> HnG AnG AsH; have HsG := (normal_sub HnG).
have Cht := is_char_irr t; have Cit := is_char_induced Cht HsG.
have Crt := is_char_restrict HsG Cit.
apply/idP/idP=> [AsC|AsI].
  apply /subsetP=> g GiA.
  rewrite cker_charE ?inE //.
  rewrite (subsetP HsG) ?(subsetP AsH) //=.
  rewrite ffunE [X in _ == X]ffunE; apply/eqP.
  congr (_ * _); apply: eq_bigr=> h HiG.
  have: g ^h \in A.
    by case/normalP: AnG=> _; move/(_ _ HiG)<-; apply/imsetP; exists g.
  move/(subsetP AsC).
  by rewrite conj1g cker_charE ?(inE) // => /andP [] _ /eqP.
have: A \subset cker H ('Res[H] ('Ind[G, H] 'xi_t)).
  apply/subsetP=> g GiG.
  move: (subsetP AsI _ GiG).
  rewrite !cker_charE ?inE // => /andP [] _ HH.
  by rewrite !(subsetP AsH, crestrictE).
move/subset_trans; apply.
apply: is_comp_cker=> //.
rewrite induced_sum_rcosets //.
rewrite scaler_sumr -cconjugates_sum //=.
rewrite big_mkcond /=.
pose f (i : Iirr H) := 
  (if 'xi_i \in cconjugates G 'xi_t
       then #|'I_G['xi_t] : H|%:R else 0) *: 'xi_i.
rewrite (eq_bigr f) /f => [|i _]; last first.
  by case: (_ \in _); rewrite // scale0r.
rewrite /is_comp -inner_prodbE linear_sum (bigD1 t) // big1 //= ?addr0.
  have->: 'xi_t \in cconjugates G 'xi_t.
    by apply/cconjugatesP; exists 1%g; rewrite ?(group1, cfun_conj1).
  rewrite linearZ /= inner_prodbE irr_orthonormal eqxx [_ *: _]mulr1.
  rewrite -(eqN_eqC _ 0).
  by case: #|_ : _| (indexg_gt0 'I_G['xi_t] H).
move=> i Dit.
by rewrite linearZ /= inner_prodbE irr_orthonormal (negPf Dit) scaler0.
Qed.
 
(* This is PF 1.6b *)
Lemma induced_quotientE (A : {group gT}) t :
  H <| G -> A <| G -> A \subset cker H 'xi[H]_t ->
   'Ind[G / A, H / A] ('xi_t / A)%CH = ('Ind[G,H] 'xi_t / A)%CH.
Proof.
move=> HnG AnG AsK.
have AsH := subset_trans AsK (cker_sub _ _).
have HsG := normal_sub HnG.
have AnH := normalS AsH HsG AnG.
have HAnGA := quotient_normal A HnG.
move: (AsK); rewrite (cker_induced_irr_sub t HnG)=> // AsKI.
have CHt := is_char_irr t.
have CHq := is_char_qfunc CHt AnH AsK.
have CHi := is_char_induced CHt (normal_sub HnG).
have CHiq := is_char_induced CHq (normal_sub HAnGA).
have CHqi := is_char_qfunc CHi AnG AsKI.
have CFiq := memc_is_char CHiq.
have CFqi := memc_is_char CHqi.
apply/ffunP=> /= h.
apply: (mulfI (neq0GC H)).
case: (boolP (h \in (G / A)%g)) => HiGA; last first. 
  by rewrite (cfun0 CFiq HiGA) (cfun0 CFqi HiGA).
case: (boolP (h \in (H / A)%g))=> HiHA; last first.
  move/off_support: (support_induced (memc_is_char CHq) HAnGA).
  move/(_ _ HiHA)=> ->.
  case/imsetP: HiGA HiHA=> g; rewrite inE => /andP [] GiN GiG /= ->.
  rewrite (qfuncE CHi) // => HH.
  have GniH : g \notin H.
    by apply: contra HH; exact: mem_quotient.
  move/off_support: (support_induced (memc_is_char CHt) HnG).
  by move/(_ _ GniH)=> ->; rewrite !mulr0.
rewrite !ffunE !mulrA (divff ((neq0GC H))) mul1r.
rewrite card_quotient ?normal_norm //.
rewrite -(LaGrange AsH) natr_mul mulfK; last first.
  by rewrite -(eqN_eqC _ 0); case: #|_:_| (indexg_gt0 H A).
rewrite -mulr_sumr.
rewrite {1}(partition_big _  _ (fun x => @mem_quotient _ A x G)) /=.
apply: eq_bigr=> i.
case/imsetP=> g; rewrite inE => /andP [] GiN GiG /= ->.
rewrite (eq_bigl (fun x => x \in (coset A g)))=> [|g1]; last first.
  apply/andP/idP=> [[] G1iG |].
    move/eqP; move/rcoset_kercosetP.
    rewrite val_coset //; apply=> //.
    by apply: (subsetP (normal_norm AnG)).
  rewrite val_coset //; case/rcosetP=> a AiA ->.
  have AGiG: (a * g)%g \in G.
    by rewrite groupM // (subsetP (normal_sub AnG)).
  split=> //; apply/eqP; apply/rcoset_kercosetP=> //; last first.
    by apply/rcosetP; exists a.
  by apply: (subsetP (normal_norm AnG)).
rewrite (eq_bigr (fun x => ('xi_t / A)%CH (h ^ coset A g))).
  by rewrite sumr_const mulr_natl val_coset // card_rcoset.
move=> g1 G1iC.
have<-: coset A (repr h ^ g) = h ^ coset A g.
  by rewrite morphJ /= ?coset_reprK // repr_coset_norm .
have RiH: repr h \in H.
  case/imsetP: HiHA=> h1; rewrite inE /= => /andP [] H1iN H1iH ->.
  move: (mem_repr_coset (coset A h1)); rewrite val_coset //.
  by case/rcosetP=> a AiA->; rewrite groupM // (subsetP AsH).
have JiH : repr h ^ g \in H.
  by rewrite memJ_norm // (subsetP (normal_norm HnG)).
rewrite (qfuncE CHt) //.
move: G1iC; rewrite val_coset //.
rewrite norm_rlcoset //; case/lcosetP=> a AiA ->.
by rewrite conjgM (char_ckerJ CHt) // (subsetP AsK).
Qed.

(* This is PF 1.8 *)
Lemma irr1_bound_quo (B C D : {group gT}) i :
  B <| C -> B \subset cker G 'xi_i -> B \subset D -> D \subset C -> C \subset G ->
  (D/B \subset 'Z(C/B) -> ('xi[G]_i 1)^+2 <= #|G|%:R^+2 * #|C|%:R^-1 * #|D|%:R^-1)%g.
Proof.
move=> BnC BsK BsD DsC CsG QsZ.
case: (boolP ('Res[C] 'xi_i == 0))=> [HH|].
  have: ('Res[C] 'xi_i) 1%g = 0 by rewrite (eqP HH) ffunE.
  by rewrite crestrictE // => HH1; case/eqP: (irr1_neq0 i).
have IC := is_char_restrict CsG (is_char_irr i).
case/(is_comp_neq0 (memc_is_char IC))=> i1 Hi1.
have CIr: is_comp i ('Ind[G,C] 'xi_i1).
  rewrite /is_comp -frobenius_reciprocity ?memc_irr //.
  by rewrite inner_prod_charC ?is_char_irr.
have BsKi : B \subset cker C 'xi_i1.
  suff BsKri: B \subset cker C ('Res[C] 'xi_i).
    by apply: (subset_trans BsKri); exact: (is_comp_cker _ Hi1).
  apply/subsetP=> g GiG.
  have F: g \in C by rewrite (subsetP (subset_trans BsD _)).
  rewrite cker_charE // inE F !crestrictE //.
  by move: (subsetP BsK _ GiG); rewrite cker_irrE inE (subsetP CsG) ?F.
pose i2 := qfunc_idx B i1.
have ZsC: 'Z(C / B)%g \subset  ccenter (C / B)%G 'xi_i2.
    by rewrite (center_bigcap (C/B)); apply: bigcap_inf.
have CBsH: C :&: B \subset D.
    apply/subsetP=> g; rewrite inE; case/andP=> _ HH.
    by apply: (subsetP (BsD)).
have I1B: 'xi_i1 1%g ^+ 2 <= #|C:D|%:R.
  case: (irr1_bound i2)=> HH _; move: HH.
  have->: 'xi_i2 1%g = 'xi_i1 1%g.
    by rewrite qfunc_idxE // -(coset_id (group1 B)) (qfuncE _ BnC) ?is_char_irr.
  move/leC_trans; apply.
  rewrite -leq_leC // -(index_quotient_eq CBsH) ?normal_norm //.
  rewrite -(@leq_pmul2l #|ccenter (C / B)%G 'xi_i2|) ?cardG_gt0 ?ccenter_sub //.
  rewrite  LaGrange ?quotientS ?ccenter_sub //.
  rewrite -(@leq_pmul2l #|(D / B)%g|) ?cardG_gt0 //.
  rewrite mulnA mulnAC LaGrange ?quotientS //.
  rewrite mulnC leq_pmul2l ?cardG_gt0 // subset_leq_card //.
  by apply: (subset_trans QsZ).
have IC': is_char G ('Ind[G, C] 'xi_i1).
  by apply: is_char_induced=> //; exact: is_char_irr.
move: (is_comp_irr1_char1 IC' CIr); rewrite cinduced1 //= => HH1.
apply: (leC_trans (leC_square (posC_char1 (is_char_irr i)) HH1)).
rewrite commr_exp_mull; last by apply: mulrC.
have F8: 0 < #|C|%:R^+2 by apply: sposC_mul; apply sposGC.
rewrite -(leC_pmul2l _ _ F8) mulrA -commr_exp_mull; last by apply: mulrC.
rewrite -natr_mul LaGrange // [#|C|%:R ^+ 2 *_]mulrC -!mulrA.
rewrite !(leC_pmul2l,sposGC) //  [#|D|%:R ^-1 * _]mulrC !mulrA.
rewrite mulVf ?neq0GC // mul1r -(LaGrange DsC) mulrC.
by rewrite natr_mul mulrA mulVf ?(mul1r,neq0GC).
Qed.

End Main.