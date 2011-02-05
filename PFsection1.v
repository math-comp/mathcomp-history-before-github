(* (c) Copyright Microsoft Corporation and Inria. All rights reserved. *)
Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq path div choice.
Require Import fintype tuple finfun bigop prime ssralg poly finset.
Require Import fingroup morphism perm automorphism quotient finalg action zmodp.
Require Import commutator cyclic center pgroup matrix mxalgebra mxpoly.
Require Import mxrepresentation vector algC character.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Import GroupScope GRing.Theory.
Local Open Scope ring_scope.


(**************************************************************************)
(* This file contains the proof of Section1 of Peterfalvi's book          *)
(**************************************************************************)

Section Main.

(* This corresponds to Isaacs' 6.32 *)
Lemma action_irr_class_card : 
  forall (aT gT : finGroupType) (A : {group aT}) (G : {group gT})  
         (ito : action A (irr G))  (cto : action A {set gT}) a,
   a \in A -> {acts A, on (classes G) | cto} -> 
   (forall c (i : irr G),  c \in classes G -> i (repr c) = ito i a (repr (cto c a))) ->
     #|'Fix_ito[a]| = #|'Fix_(classes G| cto)[a]|.
Proof.
move=> aT gT A G ito cto a AiA Acto H.
 (* borrowed to the second orthogonality proof *)
have F0: forall j, (j < #|irr G| -> j < #|classes G|)%N 
  by move=> j; rewrite card_irr.
pose f i := Ordinal (F0 _ (ltn_ord i)).
have G0: forall j, (j < #|classes G| -> j < #|irr G|)%N 
  by move=> j1; rewrite card_irr.
pose g i := Ordinal (G0 _ (ltn_ord i)).
have FG: forall i, f (g i) = i by move=> i; apply/val_eqP.
have GF: forall i, g (f i) = i by move=> i; apply/val_eqP.
pose X := \matrix_(i < #|irr G|, j < #|irr G|) 
  ((enum_val i) (repr (enum_val (f j)))).
pose Y := \matrix_(i < #|irr G|, j < #|irr G|) 
  (let C := enum_val (f i) in #|C|%:R * (#|G|%:R^-1 * (enum_val j) (repr C))^*).
have F2: X *m Y = 1%:M.
  apply/matrixP=> i j; rewrite !mxE.
  have->: (i == j) = (enum_val i == enum_val j).
    by apply/eqP/eqP; [move-> | exact: enum_val_inj].
  rewrite -irr_first_orthogonal_relation -mulr_sumr cfun_sum; last first.
    move=> g1 g2 Hg1 Hg2.
    by rewrite -!char_inv  -conjVg !(cfunJ (char_in_cfun _)) ?groupV.
  rewrite (reindex g) /=; last by apply: onW_bij; exists f=> i1; apply/val_eqP.
  rewrite (reindex (@enum_val _ (fun x => x \in classes G))) /=; last first.
    by apply: (enum_val_bij_in (mem_classes (group1 G))).
  apply: eq_big=> [i1|i1 _]; first by rewrite enum_valP.
  rewrite !mxE /= FG mulrC -!mulrA; congr (_ * _).
  by rewrite rmorphM fmorphV ?conjC_nat // -mulrA [enum_val i _ * _]mulrC.
 (****************************************)
pose Pa : 'M[C]_ _ := 
  \matrix_(i < #|irr G|, j < #|irr G|) (ito (enum_val i) a == (enum_val j))%:R.
apply/eqP; rewrite eqN_eqC.
have <-: \tr Pa = #|'Fix_ito[a]|%:R.
  rewrite /mxtrace (bigID (fun u => (enum_val u) \in 'Fix_ito[a])) /=.
  rewrite (eq_bigr (fun u => 1%:R)); last first.
    move=> i; rewrite inE mxE; move/subsetP=> Hi.
    case: eqP=> // Hv; case: Hv; apply/eqP.
    by move: (Hi a); rewrite !inE; apply.
  rewrite sumr_const big1 ?addr0; last first.
    move=> i; rewrite inE mxE; move/subsetP=> Hi.
    by case: eqP=> // Hv; case: Hi=> b; rewrite !inE; move/eqP->; rewrite Hv.
  rewrite -mulr_natl mulr1 /= -(card_imset  (pred_of_set 'Fix_ito[a]) (@enum_rank_inj _)).
  apply/eqP; rewrite -eqN_eqC; apply/eqP; apply: eq_card=> i.
  apply/idP/imsetP; first by move=> j; exists (enum_val i)=> //; rewrite enum_valK.
  by case=> j Hj ->; rewrite /in_mem /= enum_rankK.
pose Qa : 'M[C]_ _ := 
  \matrix_(i < #|irr G|, j < #|irr G|) (cto (enum_val (f i)) a == (enum_val (f j)))%:R.
have <-: \tr Qa = #|'Fix_(classes G | cto)[a]|%:R.
  rewrite /mxtrace (bigID (fun u => (enum_val (f u)) \in 'Fix_(classes G | cto)[a])) /=.
  rewrite (eq_bigr (fun u => 1%:R)); last first.
    move=> i; rewrite !inE !mxE; case/andP=> H1i; move/subsetP=> H2i.
    case: eqP=> // Hv; case: Hv; apply/eqP.
    by move: (H2i a); rewrite !inE; apply.
  rewrite sumr_const big1 ?addr0; last first.
    move=> i; rewrite !inE !mxE => Hi.
    case: eqP=> //; move/eqP=> Hv; case/negP: Hi; rewrite enum_valP.
    by apply/subsetP=> b; rewrite !inE; move/eqP->.
  rewrite -mulr_natl mulr1 /=.
  have F1: injective (enum_val \o f).
    by move=> i j; move/enum_val_inj; move/val_eqP=> HH; apply/eqP.
  rewrite -(card_imset _ F1).
  apply/eqP; rewrite -eqN_eqC; apply/eqP; apply: eq_card=> i.
  apply/imsetP/idP; first by case=> j Hj ->.
  move=> Hi; move: (Hi); rewrite inE; case/andP=> H1i _.
  by exists (g (enum_rank_in (classes1 _) i));  rewrite /in_mem /= FG enum_rankK_in.
have F3: X \in unitmx by case/mulmx1_unit: F2.
suff->: Qa = invmx X *m Pa *m X.
  rewrite mxtrace_mulC mulmxA mulmxV ?mul1mx //.
rewrite -[Qa]mul1mx -(mulVmx F3) -!mulmxA; congr (_ *m _).
apply/matrixP=> u v; rewrite !mxE.
have [oti H1o H2o]: bijective (ito ^~a).
  apply: injF_bij; apply: act_inj.
have [otc H1co H2co]: bijective (cto ^~a).
  apply: injF_bij; apply: act_inj.
have Hv : otc (enum_val (f v)) \in classes G.
  by rewrite -(Acto a AiA) H2co enum_valP.
pose i1 := enum_rank (ito (enum_val u) a). 
have Hi1: ito (enum_val u) a = enum_val i1 by rewrite enum_rankK.
pose j1 := g (enum_rank_in (classes1 G) (otc (enum_val (f v)))).
have Hj1: cto (enum_val (f j1)) a = enum_val (f v).
  by rewrite FG enum_rankK_in ?H2co.
rewrite (bigD1 j1) // big1 /= ?addr0 => [|i Dii1]; last first.
  rewrite !mxE; case: eqP; rewrite ?mulr0 // -Hj1.
  by move/(can_inj H1co); move/enum_val_inj; move/val_eqP=> /==> HH; case/negP: Dii1.
 (* too slow ! 
rewrite (bigD1 i1) // big1 /= ?addr0=> [|i Dii1]; last first.
 *)
 have->: \sum_(j < #|irr G|) Pa u j * X j v = Pa u i1 * X i1 v.
  rewrite {1}(bigD1 i1) // big1 /= ?addr0=> [|i Dii1] //.
  rewrite !mxE; case: eqP; rewrite ?mul0r // Hi1.
  by move/enum_val_inj=> HH; case/eqP: Dii1.
rewrite !mxE Hi1 Hj1 !(eqxx, mulr1, mul1r).
by rewrite H FG enum_rankK_in // H2co  enum_rankK.
Qed.

Variable (gT : finGroupType).

(* This corresponds to 1.1 in PF *)
Lemma odd_eq_conj_irr1 : forall (G : {group gT}) (i : irr G),
  odd #|G| -> ((i^*)%CH == i) = (i == irr1 G).
Proof.
move=> G i OG; apply/eqP/eqP=> [Hi|->]; last first.
  by apply/cfunP=> g; rewrite cfunE irr1E conjC_nat.
pose a := (@Zp1 1).
have Aito: is_action <[a]> (fun (i : irr G) v => if v == a then irr_conjC i else i).
  split=> [[[|[]]] //= _  j1 j2 Hj |j [[|[]]] // HH1 [[|[]]] // HH2 ] //=.
    by rewrite -[j1]irr_conjCK Hj irr_conjCK.
  by rewrite irr_conjCK.
pose ito := Action Aito.
have Acto: is_action <[a]> (fun (c : {set gT}) v => if v == a then c^-1%g else c).
  split=> [[[|[]]] //= _  j1 j2 Hj |j [[|[]]] // HH1 [[|[]]] // HH2 ] //=.
    by rewrite -[j1]invgK Hj invgK.
  by rewrite invgK.
pose cto := Action Acto.
have F1: {acts <[a]>, on (classes G) | cto}.
  move=> j Hj /= c; case: (_ == _) => //.
  apply/imsetP/imsetP=> [] [g GiG Hc]; exists (g^-1)%g; rewrite ?groupV //.
    by rewrite -[c]invgK Hc class_inv.
  by rewrite Hc class_inv.
have F2:  forall c (i : irr G),  c \in classes G ->
   i (repr c) = ito i a (repr (cto c a)).
  move=> c j CiG /=.
  rewrite irr_conjCE cfun_conjCE -character_inv /=.
  case/imsetP: CiG=> g GiG ->; rewrite class_inv.
  case: (repr_class G g)=> h1 H1iG ->.
  case: (repr_class G g^-1)=> h2 H2iG ->.
  by rewrite conjVg invgK !(cfunJ (irr_in_cfun _)).
have F3: forall c, c \in classes G -> c^-1%g = c -> c = 1%g.
  move=> c; case/imsetP => g GiG ->; rewrite class_inv => Hg.
  move: (class_refl G g^-1); rewrite Hg; case/imsetP=> x XiG Hx.
  have F4: (x ^+ 2)%g \in 'C_G[g].
    apply/subcent1P; split; rewrite ?groupM //.
    apply: (mulgI (x * x * g)^-1%g).
    rewrite mulVg !invMg Hx conjgE !mulgA mulgK.
    rewrite -[(_ * g * x)%g]mulgA -[(_ * (g * _))%g]mulgA -conjgE.
    by rewrite -Hx mulgK mulVg.
  have F5 : x \in 'C_G[g].
    suff->: (x = (x ^+ 2)^+ (#|G| %/2).+1)%g by apply: groupX.
    rewrite -expgn_mul -[(_%/_).+1]addn1 muln_addr muln1 -{3}addn1 addnA.
    move: (modn2 #|G|); rewrite {1}OG /= => HH; rewrite -{3}HH.
    rewrite [(2 * _)%N]mulnC -divn_eq expgn_add expg1.
    by move: (order_dvdG XiG); rewrite order_dvdn; move/eqP->; rewrite mul1g.
  move: Hx; rewrite conjgE; case/subcent1P: F5=> _ ->.
  rewrite mulgA mulVg mul1g => HH.
  have F6: (g^+2 == 1)%g by rewrite expgS -{1}HH expg1 mulVg.
  suff: #[g] == 1%N by rewrite order_eq1; move/eqP->; apply: class1G.
  move: F6 (order_gt0 g) (order_dvdG GiG); rewrite -order_dvdn.
  move/(dvdn_leq (is_true_true: (0<2)%N)); case: #[_]=> // [[|[]]] //.
  by rewrite dvdn2 OG.
apply/eqP; case: (boolP (i == irr1 G))=> // Hd.
move: (action_irr_class_card (cycle_id a) F1 F2).
have->: #|'Fix_(classes G | cto)[a]| = 1%N.
  apply: (@eq_card1 _ 1%g)=> c; apply/idP/idP; rewrite !inE.
    case/andP=> GiG HH; apply/eqP; apply: F3=> //; apply/eqP.
    by move/subsetP: HH; move/(_ a); rewrite !inE eqxx; apply.
  move/eqP->; rewrite classes1.
  apply/subsetP=> b; rewrite !inE; move/eqP=> -> /=.
  by rewrite invg1.
rewrite (cardD1 (irr1 G)).
have->: irr1 G \in 'Fix_ito[a].
  apply/afixP=> b; rewrite !inE; move/eqP->; rewrite /=.
  apply: irr_cfun_inj; apply/cfunP=> g.
  by rewrite irr_conjCE cfun_conjCE !irr1E conjC_nat.
rewrite (cardD1 i) //.
suff->: i \in [predD1 'Fix_ito[a] & irr1 G] by [].
rewrite inE /= Hd.
apply/afixP=> b; rewrite !inE; move/eqP->; rewrite /=.
apply: irr_cfun_inj; apply/cfunP=> g.
by rewrite irr_conjCE Hi.
Qed.

(* This corresponds to 1.2 in PF *)
Lemma not_in_ker_char0: forall (H G: {group gT}) (i : irr G) g,
   g \in G -> H <| G -> ~(H \subset cker G i) -> 'C_H[g] = 1%g -> i g = 0.
Proof.
move=> H G i g InG NN NoN HC.
have: (#|'C_G[g]| <= #|'C_(G/H)[coset H g]|)%N.
  suff->: #|'C_G[g]| = #|'C_G[g] / H|%G.
    by apply: (subset_leq_card (quotient_subcent1 H G g)).
  apply: card_isog.
  apply: isog_trans (second_isog _); last first.
    apply: subset_trans (normal_norm NN).
    by apply: subcent1_sub.
  suff->: H :&: 'C_G[g] = 1%g by exact: quotient1_isog.
    rewrite -HC.
    apply/setP=> h; rewrite inE.
    apply/andP/subcent1P; case=> H1 H2; split=> //.
      by move/subcent1P: H2; case.
    apply/subcent1P; split=> //.
    by apply: (subsetP (normal_sub NN)).
have F1: coset H g \in (G/H)%g.
  by rewrite -imset_coset; apply/imsetP; exists g.
rewrite leq_leC.
move: (irr_second_orthogonal_relation InG InG).
rewrite class_refl=> <-.
move: (irr_second_orthogonal_relation F1 F1).
rewrite class_refl=> <-; rewrite sum_norm_quo //.
rewrite (bigID (fun i : irr G => H \subset cker G i)) //=.
set S := \sum_(i | ~~ _) _; set S' := \sum_(i | _) _ => HH.
have F2: 0 = S.
  apply: leC_anti; last by rewrite -(leC_add2l S') addr0.
  by apply: posC_sum=> j _; rewrite /leC subr0; exact: repC_pconj.
apply/eqP;  have: i g * (i g)^* == 0.
  apply/eqP; apply: (posC_sum_eq0 _ (sym_equal F2)).
    by move=> j _; rewrite /leC subr0; exact: repC_pconj.
  by move/negP: NoN->; rewrite  /index_enum -enumT mem_enum.
rewrite mulf_eq0; case/orP=> //.
by rewrite conjC_eq0.
Qed.

(* This is PF 1.5(a) *)
Lemma induced_sum_rcosets : 
  forall (G H : {group gT}) (HnG : H <| G) (i : irr H),
  'Res[H] ('Ind[G,H] i) = #|inertia HnG i : H|%:R *:
       \sum_(j \in rcosets (inertia HnG i) G) cfun_conj i (repr j).
Proof.
move=> G H HnG i; apply/cfunP=> h.
case: (boolP (h \in H))=> [HiH|HniH]; last first.
  rewrite cfunE (negPf HniH) mul0r cfunE sum_cfunE cfunE.
  rewrite big1 ?(scaler0,cfunE,mulr0) // => C1.
  case/rcosetsP=> h1 H1iG ->.
  have RiG: repr (inertia_group HnG i :* h1) \in G.
    case: (repr_rcosetP (inertia_group HnG i) h1)=> g GiI.
    by rewrite groupM // (subsetP (inertia_sub HnG i)).
  by rewrite -(irr_conjE HnG _ RiG) (cfun0 _ HniH) // irr_in_cfun.
rewrite crestrictE // !(sum_cfunE,cfunE).
apply: (mulfI (neq0GC H)); rewrite !mulrA divff ?(neq0GC H) // mul1r.
rewrite -natr_mul LaGrange ?subset_inertia //.
rewrite -mulr_sumr.
rewrite (reindex invg) /=; last by exists invg=> g; rewrite invgK.
rewrite (eq_bigr (fun j => (cfun_conj i j h))); last first.
  by move=> g Hg; rewrite cfun_conjE.
have F1: forall g : gT, g^-1%g \in G -> 
  (inertia HnG i) :* g \in rcosets (inertia HnG i) G.
  move=> g; rewrite groupV // => GiG; apply/imsetP; exists g=> //.
  by rewrite rcosetE.
rewrite {1}(partition_big _  _ F1) /=.
apply: eq_bigr=> N; case/imsetP=> x XiG ->.
set a := repr _.
rewrite (eq_bigr (fun _ => cfun_conj i a h)); last first.
  move=> i1; case/andP; rewrite groupV /a // => Hi1; move/eqP=> <-.
  suff: cfun_conj i i1 == cfun_conj i (repr ((inertia HnG i) :* i1)).
    by move/eqP<-.
  rewrite (cfun_conj_eqE HnG) ?mem_repr_rcoset //.
  have: inertia HnG i :* i1 \subset G.
    apply/subsetP=> g; case/imset2P=> h1 h2; rewrite !inE.
    by case/andP=> H1iG _ Eh2 ->; rewrite groupM // (eqP Eh2).
  by move/subsetP; apply; apply: (mem_repr_rcoset (inertia_group HnG i) i1).
rewrite -(card_rcoset _ x) -sum1_card natr_sum -!mulr_suml.
apply: eq_big=> [i1|i1]; last by rewrite mul1r.
rewrite rcosetE; apply/andP/idP=>[|HH]; last first.
  split; last by apply/eqP; apply: rcoset_transl.
  case/rcosetP: HH=> h1 H1iI ->; rewrite groupV groupM //.
  by apply: (subsetP (inertia_sub HnG i)).
case=> I1iG; move/eqP<-; apply/rcosetP.
by exists 1%g; rewrite ?mul1g // ?(group1 (inertia_group HnG i)).
Qed.

(*  This 1.5b *)
Lemma induced_prod_index : 
  forall (G H : {group gT}) (HnG : H <| G) (i : irr H),
    '['Ind[G,H] i,'Ind[G,H] i]@G = #|inertia HnG i : H|%:R.
Proof.
move=> G H HnG i; have CFi := irr_in_cfun i; have HsG := normal_sub HnG.
rewrite -freciprocity ?induced_in_cfun //.
have->: '[i, 'Res[H] ('Ind[G,H] i)]@H =
  #|inertia HnG i : H|%:R *
    '[i, \sum_(j \in rcosets (inertia HnG i) G) cfun_conj i (repr j)]@H.
 rewrite !inner_prodE mulrA [_%:R * _]mulrC -mulrA -[_%:R * _]mulr_sumr.
 congr (_ * _); apply: eq_bigr=> h HiH.
 rewrite mulrA [_%:R * _]mulrC -mulrA; congr (_ * _).
 by rewrite (induced_sum_rcosets HnG) // !cfunE rmorphM conjC_nat.
rewrite raddf_sum (bigD1 (inertia HnG i :* 1%g)) /=; last first.
  by apply/rcosetsP; exists 1%g; rewrite ?group1.
have F1: repr (inertia HnG i :* 1) \in inertia HnG i.
  by rewrite -{2}[inertia HnG i]rcoset1 mem_repr_rcoset.
rewrite big1 ?addr0=> [|j].
  by rewrite (is_irr_inner HnG) ?(F1,mulr1,subsetP (inertia_sub HnG i)).
case/andP; case/rcosetsP=> g GiG -> Heq.
rewrite (is_irr_inner HnG); last first.
  have: inertia HnG i :* g \subset G.
    apply/subsetP=> h; case/rcosetP=> k KiI ->.
    by rewrite groupM // (subsetP (inertia_sub HnG i)).
  by move/subsetP; apply; apply: mem_repr_rcoset.
case E1: (_ \in _)=> //; case/eqP: Heq.
rewrite rcoset1 rcoset_id //.
have: repr (inertia_group HnG i :* g) \in inertia HnG i by [].
by case: repr_rcosetP=> h HiI HGiH; rewrite -(groupMl _ HiI).
Qed.

(*  This 1.5c *)
Lemma is_conjugate_irr_induced : 
  forall (G H : {group gT}) (HnG : H <| G) (i j : irr H),
    if is_conjugate G i j then 'Ind[G,H] i = 'Ind[G,H] j else
      '['Ind[G,H] i, 'Ind[G,H] j]@G = 0.
Proof.
move=> G H HnG i j; case: (boolP (is_conjugate G i j))=> [IC|NiC].
  by apply: is_conjugate_induced=> //; exact: irr_in_cfun.
rewrite -freciprocity ?(normal_sub HnG,irr_in_cfun,induced_in_cfun) //.
rewrite (induced_sum_rcosets HnG) inner_prodZ raddf_sum big1 ?mulr0 //=.
move=> C1 HC1.
have RiG: repr C1 \in G.
  case/rcosetsP: HC1=> g GiG ->.
  have: inertia HnG j :* g \subset G.
    apply/subsetP=> h; case/rcosetP=> k KiI ->.
    by rewrite groupM // (subsetP (inertia_sub HnG j)).
  by move/subsetP; apply; apply: mem_repr_rcoset.
move: (irr_orthonormal i (irr_conj HnG j RiG)); rewrite irr_conjE => ->.
case: eqP=> // HH; case/negP: NiC; rewrite HH.
apply/is_conjugateP; exists (repr C1)^-1%g; rewrite ?groupV //.
by rewrite irr_conjE -cfun_conjM mulgV cfun_conj1.
Qed.

(* This is PF 1.5(d) *)
Lemma induced_sum_rcosets1 : 
  forall (G H : {group gT}) (HnG : H <| G) (i : irr H),
  let chi :=  'Ind[G,H] i in
  (chi 1%g / '[chi,chi]@G) *: 'Res[H] chi  = #|G : H|%:R *:
       \sum_(j \in rcosets (inertia HnG i) G) (i ^ (repr j))%CH 1%g *: (i ^ (repr j))%CH.
Proof.
move=> G H HnG i chi.
rewrite (induced_sum_rcosets HnG) (induced_prod_index HnG) induced1 ?(normal_sub) //.
rewrite !scalerA -!mulrA mulVf ?(mulr1); last first.
  rewrite -neq0N_neqC; move: (indexg_gt0 (inertia_group HnG i) H)=> /=.
  by case: #|_:_|.
rewrite-scalerA scaler_sumr; congr (_ *: _); apply: eq_bigr=> C1 IC1.
by rewrite cfun_conj_val1.
Qed.

(* This is PF 1.5(e) *)
Lemma odd_induced_orthogonal : 
  forall (G H : {group gT}) (HnG : H <| G) (i : irr H),
  odd #|G| -> i != irr1 H -> '['Ind[G,H]i,('Ind[G,H]i)^*%CH]@G = 0. 
Proof.
move=> G H HnG i OG Dii1.
move: (is_conjugate_irr_induced HnG i (irr_conjC i)).
case: (boolP (is_conjugate G i (irr_conjC i))); last first.
  rewrite induced_conjC => _ <-.
  rewrite !inner_prodE; congr (_ * _); apply: eq_bigr=> g GiG.
  by rewrite irr_conjCE.
case/is_conjugateP=> g GiG; rewrite irr_conjCE=> HH.
have OH: odd #|H|.
  by apply: (dvdn_odd _ OG); apply: cardSg; apply: normal_sub.
case/negP: Dii1; rewrite -odd_eq_conj_irr1 // HH.
have F1: (i ^ (g ^+ 2))%CH = i.
  by rewrite cfun_conjM -HH -cfun_conj_conjC -HH cfun_conjCK.
suff->: g = ((g ^+ 2)^+ (#|G| %/2).+1)%g.
  elim: (_ %/2).+1=> [|n IH]; first by rewrite expg0 cfun_conj1.
  by rewrite expgS cfun_conjM F1.
rewrite -expgn_mul -[(_%/_).+1]addn1 muln_addr muln1 -{3}addn1 addnA.
move: (modn2 #|G|); rewrite {1}OG /= => HH1; rewrite -{3}HH1.
rewrite [(2 * _)%N]mulnC -divn_eq expgn_add expg1.
by move: (order_dvdG GiG); rewrite order_dvdn; move/eqP->; rewrite mul1g.
Qed.


(* This is PF 1.8 *)
Lemma irr1_bound_quo : forall (G H1 H2 H3 : {group gT}) (i : irr G),
  H1 <| H2 -> H1 \subset cker G i -> H1 \subset H3 -> H3 \subset H2 -> H2 \subset G ->
  (H3/H1 \subset 'Z(H2/H1) -> (i 1)^+2 <= #|G|%:R^+2 * #|H2|%:R^-1 * #|H3|%:R^-1)%g.
Proof.
move=> G H1 H2 H3 i H1nH2 H1sK H1sH3 H3sH2 H2sG QsZ.
pose Cr := irr_rest H2sG i.
case: (boolP (Cr == character0 H2))=> [HH|].
  have: Cr 1%g = 0 by rewrite (eqP HH) cfunE.
  by rewrite crestrictE // => HH1; case/eqP: (irr1_neq0 i).
case/is_comp_neq0=> i1 Hi1.
pose Ir := irr_induced i1 H2sG.
have CIr: is_comp i Ir.
  rewrite /is_comp ncoord_inner_prod ?(induced_in_cfun, char_in_cfun) //.
  rewrite -freciprocity ?char_in_cfun // (inner_prod_charC _ Cr).
  by rewrite  -ncoord_inner_prod // character_in_cfun.
have H1sKi : H1 \subset cker H2 i1.
  suff H1sKri: H1 \subset cker H2 ('Res[H2] i).
    by apply: (subset_trans H1sKri); exact: (is_comp_cker Hi1).
  apply/subsetP=> g GiG.
  have F: g \in H2 by rewrite (subsetP (subset_trans H1sH3 _)).
  rewrite (char_ckerE Cr) inE F !crestrictE //.
  by move: (subsetP H1sK _ GiG); rewrite irr_ckerE inE (subsetP H2sG) ?F.
pose i2 := qirrc H1 i1.
have ZsC: 'Z(H2/H1)%g \subset  ccenter (H2/H1) i2.
    by rewrite (center_bigcap (H2/H1)); apply: bigcap_inf.
have H21sH: H2 :&: H1 \subset H3.
    apply/subsetP=> g; rewrite inE; case/andP=> _ HH.
    by apply: (subsetP (H1sH3)).
have I1B: i1 1%g ^+ 2 <= #|H2:H3|%:R.
  case: (irr1_bound i2)=> HH _; move: HH.
  have->: i2 1%g = i1 1%g.
    by rewrite qirrcE // -(coset_id (group1 H1)) (qfuncE _ H1nH2) ?is_char_irr.
  move/leC_trans; apply.
  rewrite -leq_leC // -(index_quotient_eq H21sH) ?normal_norm //.
  rewrite -(@leq_pmul2l #|ccenter (H2 / H1) i2|) ?cardG_gt0 ?ccenter_sub //.
  rewrite  LaGrange ?quotientS ?ccenter_sub //.
  rewrite -(@leq_pmul2l #|(H3/H1)%g|) ?cardG_gt0 //.
  rewrite mulnA mulnAC LaGrange ?quotientS //.
  rewrite mulnC leq_pmul2l ?cardG_gt0 // subset_leq_card //.
  by apply: (subset_trans QsZ).
move: (is_comp_irr1_char1 CIr); rewrite induced1 //= => HH1.
apply: (leC_trans (leC_square (posC_char1 (character_of_irr i)) HH1)).
rewrite commr_exp_mull; last by apply: mulrC.
have F8: 0 < #|H2|%:R^+2 by apply: sposC_mul; apply sposGC.
rewrite -(leC_pmul2l _ _ F8) mulrA -commr_exp_mull; last by apply: mulrC.
rewrite -natr_mul LaGrange // [#|H2|%:R ^+ 2 *_]mulrC -!mulrA.
rewrite !(leC_pmul2l,sposGC) //  [#|H3|%:R ^-1 * _]mulrC !mulrA.
rewrite mulVf ?neq0GC // mul1r -(LaGrange H3sH2) mulrC.
by rewrite natr_mul mulrA mulVf ?(mul1r,neq0GC).
Qed.

End Main.