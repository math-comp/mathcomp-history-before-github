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
Lemma odd_eq_conj_irr1 : forall (G : {group gT}) (theta : irr G),
  odd #|G| -> ((theta^*)%CH == theta) = (theta == irr1 G).
Proof.
move=> G t OG; apply/eqP/eqP=> [Ht|->]; last first.
  by apply/ffunP=> g; rewrite ffunE irr1E conjC_nat.
pose a := (@Zp1 1).
have Aito:
    is_action <[a]> (fun (t : irr G) v => if v == a then irr_conjC t else t).
  split=> [[[|[]]] //= _  t1 t2 Hj |j [[|[]]] // HH1 [[|[]]] // HH2 ] //=.
    by rewrite -[t1]irr_conjCK Hj irr_conjCK.
  by rewrite irr_conjCK.
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
     rewrite ?class_inv mem_classes // ?groupV.
have F2:  forall c (t : irr G),  c \in classes G ->
   t (repr c) = ito t a (repr (cto c a)).
  move=> c t' CiG /=.
  rewrite irr_conjCE cfun_conjCE /= -(invg_is_char _ (is_char_irr t')).
  case/imsetP: CiG=> g GiG ->; rewrite class_inv.
  case: (repr_class G g)=> h1 H1iG ->.
  case: (repr_class G g^-1)=> h2 H2iG ->.
  by rewrite conjVg invgK !(cfunJ _ (memc_irr _)).
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
  move/(dvdn_leq (is_true_true: (0 < 2)%N)); case: #[_]=> // [[|[]]] //.
  by rewrite dvdn2 OG.
apply/eqP; case: (boolP (t == irr1 G))=> // Hd.
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
  apply: cfun_of_irr_inj; apply/ffunP=> g.
  by rewrite irr_conjCE cfun_conjCE !irr1E conjC_nat.
rewrite (cardD1 t) //.
suff->: t \in [predD1 'Fix_ito[a] & irr1 G] by [].
rewrite inE /= Hd.
apply/afixP=> b; rewrite !inE; move/eqP->; rewrite /=.
apply: cfun_of_irr_inj; apply/ffunP=> g.
by rewrite irr_conjCE Ht.
Qed.

Variable (G H : {group gT}).

(* This corresponds to 1.2 in PF *)
Lemma not_in_ker_char0: forall (theta : irr G) g, g \in G ->
  H <| G -> ~(H \subset cker G theta) -> 'C_H[g] = 1%g -> theta g = 0.
Proof.
move=> t g InG NN NoN HC.
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
apply/eqP;  have: t g * (t g)^* == 0.
  apply/eqP; apply: (posC_sum_eq0 _ (sym_equal F2)).
    by move=> j _; rewrite /leC subr0; exact: repC_pconj.
  by move/negP: NoN->; rewrite  /index_enum -enumT mem_enum.
rewrite mulf_eq0; case/orP=> //.
by rewrite conjC_eq0.
Qed.

Lemma vchar_sub : forall m n (S1 : m.-tuple {cfun gT}) (S2 : n.-tuple _) A,
  free S1 -> free S2 -> {subset S1 <= S2} -> {subset 'Z[S1,A] <= 'Z[S2,A]}.
Proof.
move=> m n S1 S2 A FS1 FS2 Hs f; case/and3P=> Hf Cf Sf; apply/and3P; split=> //.
  by move/subvP: (span_subset Hs); apply.
apply/forallP=> /= i.
case: m S1 FS1 Hs Hf {Sf}Cf=> [|m S1 FS1 Hs Hf Cf].
  (do 2 case)=> //= _ _ _ HH _; move: HH; rewrite span_nil.
  case/injvP=> k; rewrite scaler0=> ->.
  by rewrite linear0 ffunE (isZC_nat 0).
case: n i S2 FS2 Hs=> [|n] i S2 FS2 Hs.
  by move: (uniq_leq_size (free_uniq FS1) Hs); rewrite !size_tuple.
pose g (i : 'I_n.+1) : 'I_m.+1 := locked (inZp (index S2`_i S1)).
pose h (i : 'I_m.+1) : 'I_n.+1 := locked (inZp (index S1`_i S2)).
pose c (i : 'I_n.+1) := if S2`_ i \in S1 then (coord S1 f) (g i) else 0.
suff->: f = \sum_(i < n.+1) c i *: (S2`_i).
  rewrite free_coords // /c /=; case: (boolP (_ \in _))=> Hi; last first.
    by rewrite (isZC_nat 0).
  by move/forallP: Cf; apply.
rewrite (bigID (fun i : 'I_n.+1 =>  S2`_i \in S1)) /= [X in _ + X]big1 ?addr0.
  have F0: forall j : 'I_m.+1, S1`_j \in S2.
    by move=> j;  rewrite Hs // mem_nth // size_tuple.
  have F1: forall j : 'I_m.+1,S2`_(h j) = S1`_j.
    move=> j; rewrite /h; unlock; rewrite /= modn_small ?nth_index //.
    by move: (F0 j); rewrite -index_mem size_tuple.
  have F2: forall j : 'I_n.+1, S2`_j \in S1 -> S1`_(g j) = S2`_j.
    move=> j FF; rewrite /g; unlock; rewrite /= modn_small ?nth_index //.
    by move: FF; rewrite -index_mem size_tuple.
  have F3: forall j, g (h j) = j. 
    move=> j; rewrite /g; unlock; rewrite F1.
    apply/val_eqP=> /= ; rewrite /= modn_small.
      by rewrite index_uniq ?size_tuple // free_uniq.
    by rewrite -{4}(size_tuple S1) index_mem // mem_nth // size_tuple.
  rewrite (eq_bigr (fun i => (coord S1 f) (g i) *: S1`_(g i))); last first.
     by move=> j SiS; rewrite /c SiS F2.
  rewrite (reindex h) /=.
    rewrite (coord_span Hf).
    apply: eq_big=> /= [j|j _].
      by rewrite F1 mem_nth // size_tuple.
    by rewrite F3 free_coords.
  exists g=> u; rewrite inE ? F3 //=.
  move=> FF; rewrite /h; unlock; rewrite F2 //.
  apply/val_eqP=> /= ; rewrite /= modn_small.
   by rewrite index_uniq ?size_tuple // free_uniq.
  by rewrite -{4}(size_tuple S2) index_mem // mem_nth // size_tuple.
by move=> j; rewrite /c; move/negPf->; exact: scale0r.
Qed.

Lemma is_gvchar_split :  forall m (S : m.-tuple _) A (f : {cfun gT}), 
          f \in 'Z[S, A] =  (f \in 'Z[S]) && has_support f A.
Proof.
(move=> m S A f; apply/and3P/andP; case)=> [H1 H2 H3|H1 H2]; split=> //.
- apply/and3P; split=> //.
  by apply/forall_inP=> i; rewrite inE.
- by case/and3P: H1.
by case/and3P: H1.
Qed.

Lemma memv_is_gvchar :  forall m (S : m.-tuple _) A (f : {cfun gT}), 
          free S -> has_support f A -> f \in S -> f \in 'Z[S,A].
Proof.
move=> [|m] S A f HF HS FiS.
  by case: {HF}S FiS; case.
apply/and3P; split=> //; first by apply: memv_span.
apply/forallP=> i.
have->: f = S`_(inZp (index f S): 'I_m.+1).
  by rewrite /= modn_small ?nth_index // -{2}(size_tuple S) index_mem.
by rewrite (free_coordt _ _ HF) isZC_nat.
Qed.

Lemma inner_prod_vchar :
   forall A (chi1 chi2 : {cfun gT}),
   chi1 \in 'Z['Irr(G),A] -> chi2 \in 'Z['Irr(G),A] ->
   '[chi1, chi2]_G = \sum_(theta: irr G) ncoord theta chi1 * ncoord theta chi2.
Proof.
move=> A chi1 chi2 IC1 IC2.
have: chi1 \in 'CF(G).
  move: (IC1); rewrite is_gvchar_split; case/andP.
  case/is_vcharP=> f1 [f2 []] Hf1 Hf2 -> _.
  by apply: memv_sub; exact: memc_is_char.
case/(ncoord_sum)=>{1}->.
have: chi2 \in 'CF(G).
  move: (IC2); rewrite is_gvchar_split; case/andP.
  case/is_vcharP=> f1 [f2 []] Hf1 Hf2 -> _.
  by apply: memv_sub; exact: memc_is_char.
case/(ncoord_sum)=>{1}->.
rewrite -inner_prodbE {1}linear_sum /=.
apply: eq_bigr=> t _; rewrite linearZ /= inner_prodbE.
rewrite raddf_sum  {1}(bigD1 t) // big1 //= ?addr0 => [|j Hj]; last first.
  by rewrite inner_prodZ irr_orthonormal eq_sym (negPf Hj) mulr0.
congr (_ * _); rewrite inner_prodZ irr_orthonormal eqxx mulr1.
apply: isZC_conj.
by case/and3P: IC2=> _; move/forallP; move/(_ (enum_rank t)).
Qed.

Definition absC x := if 0 <= x then x else -x.

Lemma absC_nat : forall n : nat, absC n%:R = n%:R.
Proof. by move=> n; rewrite /absC posC_nat. Qed.

Lemma absC_eq0 : forall x, (absC x == 0) = (x == 0).
Proof.
move=> x; rewrite /absC; case: (_ <= _)=> //.
apply/eqP/eqP=>[|->]; last by rewrite oppr0.
by rewrite -{2}[x]opprK=> ->; rewrite oppr0.
Qed.

Lemma isNatC_absC : forall z, isZC z -> isNatC (absC z).
Proof.
move=> z; rewrite isZCE /absC; case/orP; case/isNatCP=> n Hn.
  by rewrite Hn posC_nat isNatC_nat.
rewrite -{1 2}[z]opprK Hn.
case: (boolP (0 <= _))=> HH; last by exact: isNatC_nat.
rewrite -(leC_anti (posC_nat n)) ?(oppr0,(isNatC_nat 0)) //.
by rewrite -leC_sub sub0r.
Qed.

Lemma isNatC_square : forall z, isZC z -> z * z = absC z * absC z.
Proof.
move=> z; rewrite isZCE /absC; case/orP; case/isNatCP=> n Hn.
  rewrite Hn posC_nat // isNatC_nat.
by case: (_ <= _)=> //; rewrite mulrNN.
Qed.

Let vchar_isometry_base2 : forall f, f \in 'Z['Irr(G),G^#] -> '[f,f]_G = 2%:R ->
   exists e1: irr G, exists e2: irr G, f = e1%:CF - e2%:CF.
Proof.
move=> f Hf.
rewrite (inner_prod_vchar Hf) //.
have F1: f \in 'CF(G).
  move: Hf; rewrite is_gvchar_split; case/andP.
  case/is_vcharP=> f1 [f2 []] Hf1 Hf2 -> _.
  by apply: memv_sub; exact: memc_is_char.
have Ce: forall e : irr G, isZC (ncoord e f).
  move=> e; case/and3P: Hf=> _; move/forallP.
  by move/(_ (enum_rank e)).
move=> HH.
pose h (t : irr G) := getNatC (absC (ncoord t f)).
have Hh: forall t, (h t)%:R = absC (ncoord t f).
move=> t; rewrite /h; case/isNatCP: (isNatC_absC (Ce t))=> n ->.
  by rewrite getNatC_nat.
have: (\sum_t (h t) * h t = 2)%N.
  apply/eqP; rewrite eqN_eqC -HH natr_sum; apply/eqP.
  apply: eq_bigr=> i _; rewrite natr_mul.
  by rewrite Hh -isNatC_square.
case: (boolP (forallb i : irr G, ncoord i f == 0)).
  move/forallP=> {HH}HH.
  rewrite big1=> // i _.
  apply/eqP; rewrite eqN_eqC natr_mul Hh.
  by rewrite (eqP (HH i)) (absC_nat 0) mul0r.
rewrite negb_forall; case/existsP=> /= e1 He1.
rewrite (bigD1 e1) //=.
case E1: (h e1)=> [|[|k]] //; first 2 last.
  - by rewrite !mulnS addnA !addnS.
  - by move/eqP: E1; rewrite eqN_eqC Hh absC_eq0 (negPf He1).
case: (boolP (forallb i, (i == e1) || (ncoord i f == 0))).
  move/forallP=> {HH}HH.
  rewrite big1=> // i Hi.
  apply/eqP; rewrite eqN_eqC natr_mul Hh.
  move: (HH i); rewrite (negPf Hi) /=; move/eqP->.
  by rewrite (absC_nat 0) mul0r.
rewrite negb_forall; case/existsP=> /= e2; rewrite negb_or.
case/andP=> Hd He2.
rewrite (bigD1 e2) //=.
case E2: (h e2)=> [|[|k]] //.
  by move/eqP: E2; rewrite eqN_eqC Hh absC_eq0 (negPf He2).
do 2 move/addnI; move/eqP; rewrite sum_nat_eq0.
move/forall_inP=> HH1.
have: f 1%g = 0.
  apply/eqP; case/and3P: Hf=> _ _; move/forall_inP; apply.
  by rewrite !inE eqxx.
have->: f = ncoord e1 f *: e1%:CF + ncoord e2 f *: e2%:CF.
  rewrite {1}(ncoord_sum F1) (bigD1 e1) //; congr (_ + _).
  rewrite (bigD1 e2) // big1 /= ?addr0 // => i Hi.
  case Ei: (h i) (HH1 _ Hi)=> //.
  by move/eqP: Ei; rewrite eqN_eqC Hh absC_eq0; move/eqP->; rewrite scale0r.
rewrite ffunE [_ 1%g]ffunE [(_ (_ *: _)) 1%g]ffunE.
have F: 0 < e1 1%g + e2 1%g.
  by apply: sposC_addl; try apply: ltCW; apply/andP; split;
     try exact:irr1_neq0; rewrite irr_val1 ; apply: posC_nat.
move/eqP: E1; rewrite eqN_eqC Hh /absC; case: (_ <= _).
  move/eqP->.
  move/eqP: E2; rewrite eqN_eqC Hh /absC; case: (_ <= _).
    move/eqP->; rewrite !scale1r=> HHf.
    by move: F; rewrite HHf -(ltn_ltC 0 0).
  rewrite -{2 3}[ncoord e2 f]opprK; move/eqP=> -> _.
  by exists e1; exists e2; rewrite scaleNr !scale1r.
rewrite -{2 3}[ncoord e1 f]opprK; move/eqP=> ->.
move/eqP: E2; rewrite eqN_eqC Hh /absC; case: (_ <= _).
  move/eqP=> -> _.
  by exists e2; exists e1; rewrite addrC scaleNr !scale1r.
rewrite -{2 3}[ncoord e2 f]opprK; move/eqP->.
rewrite /= -mulr_addr mulN1r=> HH2.
by move: F; rewrite -[X in _ < X]opprK HH2 oppr0 -(ltn_ltC 0 0).
Qed.
 
(* This is PF 1.4 *)
Lemma vchar_isometry_base : 
  forall m (Chi : m.+2.-tuple {cfun gT}) (tau : 'End({cfun gT})) (chi1 := Chi`_0), 
    {subset Chi <= 'Irr(H)} -> free Chi ->
    (forall chi, chi \in Chi -> chi 1%g = chi1 1%g) ->
    (forall f, f \in 'Z[Chi, H^#]-> tau f \in 'Z['Irr(G), G^#]) ->
    (forall f1 f2, f1 \in 'Z[Chi, H^#] -> f2 \in 'Z[Chi, H^#] -> 
                   '[tau f1, tau f2]_G = '[f1,f2]_H) ->
    exists mu : {cfun gT} -> irr G,
    exists epsilon : bool,
    forall i : 'I_m.+2,
        tau (Chi`_i - chi1) = (-(1%R))^+epsilon *: ((mu (Chi`_i))%:CF - (mu chi1)%:CF).
Proof. 
elim=> [[[|chi1 [|chi2[|]]]] // SChi tau /= SubC|].
   have F1: chi1 \in 'Irr(H).
     by apply: SubC; rewrite /in_mem /= eqxx.
   have F2: chi2 \in 'Irr(H).
     by apply: SubC; rewrite /in_mem /= eqxx orbT.
   move: F1 F2 {SubC}SChi.
   case/mapP=> i1 Hi1 ->.
   case/mapP=> i2 Hi2 -> => {chi1 chi2}SChi HF /=.
  pose T := Tuple SChi.
  move: (free_uniq HF); rewrite /= inE andbT=> HD Hs Ho Him.
  pose d : {cfun _} := i2%:CF - i1%:CF.
  have iD : d \in 'Z[T,H^#].
    rewrite is_gvchar_split; apply/andP; split.
    apply: is_vchar_sub; apply:  memv_is_gvchar=> //.
    - by apply/forall_inP=> i; rewrite inE.
    - by rewrite /in_mem /= eqxx orbT.
    - by apply/forall_inP=> i; rewrite inE.
    - by rewrite /in_mem /= eqxx.
    apply/forall_inP=> g; rewrite !inE negb_and negbK.
    case/orP=>[| HH].
      move/eqP->; rewrite /d ffunE (Hs i2).
      by rewrite [X in _ + X]ffunE addrN.
      by rewrite /in_mem /= eqxx orbT.
    rewrite /d ffunE (cfun0 _ HH) ?memc_irr //.
    by rewrite ffunE (cfun0 _ HH) ?(addrN,memc_irr).
  have: '[d,d]_H = 2%:R.
    rewrite /d raddf_sub /= -!inner_prodbE !linear_sub /= !inner_prodbE.
    rewrite !irr_orthonormal !eqxx eq_sym.
    case: (boolP (_ == _))=> HH; first by case/negP: HD; rewrite (eqP HH).
    by rewrite subr0 sub0r opprK -natr_add.
 rewrite -Him //; case/(vchar_isometry_base2 (Ho _ iD))=> e2 [] e1 Ht. 
  pose mu x:= 
     if x == i1%:CF then e1 else
     if x == i2%:CF then e2 else (irr1 G).
  exists mu; exists false.
  (do 2 case=> //)=> [|[]] //= _.
    by rewrite !subrr linear0 scaler0.
  by rewrite /mu !eqxx eq_sym (negPf HD) Ht scale1r.
admit.
Qed.

(* This is PF 1.5(a) *)
Lemma induced_sum_rcosets : 
  forall (theta : irr H),  H <| G ->
  'Res[H] ('Ind[G,H] theta) = 
     #|('I_(G)[theta])%CH : H|%:R *: \sum_(f <- cconjugates G theta) f.
Proof.
move=> t HnG; apply/ffunP=> h.
pose GI := ([group of 'I_(G)[t]])%CH.
rewrite big_map big_filter.
case: (boolP (h \in H))=> [HiH|HniH]; last first.
  rewrite ffunE (negPf HniH) mul0r ffunE sum_ffunE ffunE.
  rewrite big1 ?(scaler0,ffunE,mulr0) // => C1.
  case/rcosetsP=> h1 H1iG ->.
  have RiG: repr (GI :* h1) \in G.
    case: (repr_rcosetP GI h1)=> g GiI.
    by rewrite groupM // (subsetP (inertia_sub G t)).
  by rewrite -(irr_conjE _ HnG RiG) (cfun0 _ HniH) // memc_irr.
rewrite crestrictE // !(sum_ffunE,ffunE).
apply: (mulfI (neq0GC H)); rewrite !mulrA divff ?(neq0GC H) // mul1r.
rewrite -natr_mul LaGrange ?(subset_inertia, memc_irr) //.
rewrite -mulr_sumr.
rewrite (reindex invg) /=; last by exists invg=> g; rewrite invgK.
rewrite (eq_bigr (fun j => (t ^ j)%CH h)); last first.
  by move=> g Hg; rewrite cfun_conjE.
have F1: forall g : gT, g^-1%g \in G -> 
  ('I_(G)[t])%CH :* g \in rcosets ('I_(G)[t]) G.
  move=> g; rewrite groupV // => GiG; apply/imsetP; exists g=> //.
  by rewrite rcosetE.
rewrite {1}(partition_big _  _ F1) /=.
apply: eq_bigr=> N; case/imsetP=> x XiG ->.
set a := repr _.
rewrite (eq_bigr (fun _ => (t ^ a)%CH h)); last first.
  move=> i1; case/andP; rewrite groupV /a // => Hi1; move/eqP=> <-.
  suff: (t ^ i1 == t ^ (repr ('I_(G)[t] :* i1)))%CH by move/eqP<-.
  rewrite (cfun_conj_eqE _ Hi1) ?mem_repr_rcoset //.
  have: ('I_(G)[t])%CH :* i1 \subset G.
    apply/subsetP=> g; case/imset2P=> h1 h2;rewrite !inE.
    by case/andP=> H1iG _ Eh2 ->; rewrite groupM // (eqP Eh2).
  by move/subsetP; apply; apply: (mem_repr_rcoset [group of 'I_(G)[t]] i1).
rewrite -(card_rcoset _ x) -sum1_card natr_sum -!mulr_suml.
apply: eq_big=> [i1|i1]; last by rewrite mul1r.
rewrite rcosetE; apply/andP/idP=>[|HH]; last first.
  split; last by apply/eqP; apply: rcoset_transl.
  case/rcosetP: HH=> h1 H1iI ->; rewrite groupV groupM //.
  by apply: (subsetP (inertia_sub G t)).
case=> I1iG; move/eqP<-; apply/rcosetP.
by exists 1%g; rewrite ?mul1g // ?(group1 [group of 'I_(G)[t]]).
Qed.

(*  This 1.5b *)
Lemma induced_prod_index : forall (theta : irr H),  H <| G -> 
    '['Ind[G,H] theta,'Ind[G,H] theta]_G = #|('I_(G)[theta])%CH : H|%:R.
Proof.
move=> t HnG; have CFi := memc_irr t; have HsG := normal_sub HnG.
rewrite -frobenius_reciprocity ?memc_induced //.
have->: '[t, 'Res[H] ('Ind[G,H] t)]_H =
  #|('I_(G)[t])%CH : H|%:R * '[t, (\sum_(f <- cconjugates G t) f)]_H.
 rewrite !inner_prodE mulrA [_%:R * _]mulrC -mulrA -[_%:R * _]mulr_sumr.
 congr (_ * _); apply: eq_bigr=> h HiH.
 rewrite mulrA [_%:R * _]mulrC -mulrA; congr (_ * _).
 by rewrite (induced_sum_rcosets _ HnG) // !ffunE rmorphM conjC_nat.
rewrite big_map big_filter.
rewrite raddf_sum (bigD1 ('I_(G)[t] :* 1%g)%CH) /=; last first.
  by apply/rcosetsP; exists 1%g; rewrite ?group1.
have F1: (repr ('I_(G)[t] :* 1) \in 'I_(G)[t])%CH.
  by rewrite -{2}[('I_(_)[_])%CH]rcoset1 mem_repr_rcoset.
rewrite big1 ?addr0=> [|j].
  by rewrite (is_irr_inner _ HnG) ?(F1,mulr1,subsetP (inertia_sub G t)).
case/andP; case/rcosetsP=> g GiG -> Heq.
rewrite (is_irr_inner _ HnG); last first.
  have: ('I_(G)[t] :* g \subset G)%CH.
    apply/subsetP=> h; case/rcosetP=> k KiI ->.
    by rewrite groupM // (subsetP (inertia_sub G t)).
  by move/subsetP; apply; apply: mem_repr_rcoset.
case E1: (_ \in _)=> //; case/eqP: Heq.
rewrite rcoset1 rcoset_id //.
have: repr ([group of 'I_(G)[t]] :* g) \in 'I_(G)[t]%CH by [].
by case: repr_rcosetP=> h HiI HGiH; rewrite -(groupMl _ HiI).
Qed.

(*  This 1.5c *)
Lemma cconjugates_irr_induced : 
  forall (theta1 theta2 : irr H), H <| G ->
    if ((theta2 : {cfun _}) \in cconjugates G theta1) 
    then 'Ind[G,H] theta1 = 'Ind[G,H] theta2 
    else '['Ind[G,H] theta1, 'Ind[G,H] theta2]_G = 0.
Proof.
move=> t1 t2 HnG; case: (boolP (_ \in _))=> [IC|NiC].
  by apply: cconjugates_induced=> //; exact: memc_irr.
rewrite -frobenius_reciprocity 
        ?(normal_sub HnG,memc_irr,memc_induced) //.
rewrite (induced_sum_rcosets _ HnG) inner_prodZ raddf_sum.
rewrite big_map big_filter big1 ?mulr0 //=.
move=> C1 HC1.
have RiG: repr C1 \in G.
  case/rcosetsP: HC1=> g GiG ->.
  have: ('I_(G)[t2])%CH :* g \subset G.
    apply/subsetP=> h; case/rcosetP=> k KiI ->.
    by rewrite groupM // (subsetP (inertia_sub G t2)).
  by move/subsetP; apply; apply: mem_repr_rcoset.
move: (irr_orthonormal t1 (irr_conj t2 (repr C1))).
rewrite (irr_conjE _ HnG) // => ->.
case: eqP=> // HH; case/negP: NiC; rewrite HH.
apply/cconjugatesP; exists (repr C1)^-1%g; rewrite ?groupV //.
by rewrite (irr_conjE _ HnG) // -cfun_conjM mulgV cfun_conj1.
Qed.

(* This is PF 1.5(d) *)
Lemma induced_sum_rcosets1 : 
  forall (theta : irr H), H <| G ->
  let chi :=  'Ind[G,H] theta in
  (chi 1%g / '[chi,chi]_G) *: 'Res[H] chi  = #|G : H|%:R *:
       (\sum_(f <- cconjugates G theta) f 1%g *: f).
Proof.
move=> t HnG chi.
rewrite (induced_sum_rcosets _ HnG) (induced_prod_index _ HnG) 
        cinduced1 ?(normal_sub) //.
rewrite !scalerA -!mulrA mulVf ?(mulr1); last first.
  rewrite -neq0N_neqC; move: (indexg_gt0 (inertia_group G t) H)=> /=.
  by case: #|_:_|.
rewrite-scalerA scaler_sumr; congr (_ *: _).
rewrite !big_map !big_filter; apply: eq_bigr=> C1 IC1.
by rewrite cfun_conj_val1.
Qed.

(* This is PF 1.5(e) *)
Lemma odd_induced_orthogonal :  forall (theta : irr H), H <| G -> odd #|G| -> 
  theta != irr1 H -> '['Ind[G,H] theta,('Ind[G,H] theta)^*%CH]_G = 0. 
Proof.
move=> t HnG OG Dii1.
move: (cconjugates_irr_induced t (irr_conjC t) HnG).
case: (boolP (_ \in _)); last first.
  rewrite cinduced_conjC => _ <-.
  rewrite !inner_prodE; congr (_ * _); apply: eq_bigr=> g GiG.
  by rewrite irr_conjCE.
case/cconjugatesP=> g GiG; rewrite irr_conjCE=> HH.
have OH: odd #|H|.
  by apply: (dvdn_odd _ OG); apply: cardSg; apply: normal_sub.
case/negP: Dii1; rewrite -odd_eq_conj_irr1 // HH.
have F1: (t ^ (g ^+ 2))%CH = t.
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
Lemma irr1_bound_quo : forall (B C D : {group gT}) (i : irr G),
  B <| C -> B \subset cker G i -> B \subset D -> D \subset C -> C \subset G ->
  (D/B \subset 'Z(C/B) -> (i 1)^+2 <= #|G|%:R^+2 * #|C|%:R^-1 * #|D|%:R^-1)%g.
Proof.
move=> B C D i BnC BsK BsD DsC CsG QsZ.
case: (boolP ('Res[C] i == 0))=> [HH|].
  have: ('Res[C] i) 1%g = 0 by rewrite (eqP HH) ffunE.
  by rewrite crestrictE // => HH1; case/eqP: (irr1_neq0 i).
have IC := is_char_restrict CsG (is_char_irr i).
case/(is_comp_neq0 (memc_is_char IC))=> i1 Hi1.
have CIr: is_comp i ('Ind[G,C] i1).
  rewrite /is_comp ncoord_inner_prod 
          ?(memc_induced, memc_irr) //.
  rewrite -frobenius_reciprocity ?memc_irr //.
  rewrite inner_prod_charC ?is_char_irr //.
  by rewrite  -ncoord_inner_prod // memc_is_char.
have BsKi : B \subset cker C i1.
  suff BsKri: B \subset cker C ('Res[C] i).
    by apply: (subset_trans BsKri); exact: (is_comp_cker _ Hi1).
  apply/subsetP=> g GiG.
  have F: g \in C by rewrite (subsetP (subset_trans BsD _)).
  rewrite cker_charE // inE F !crestrictE //.
  by move: (subsetP BsK _ GiG); rewrite cker_irrE inE (subsetP CsG) ?F.
pose i2 := qirrc B i1.
have ZsC: 'Z(C/B)%g \subset  ccenter (C/B)%G i2.
    by rewrite (center_bigcap (C/B)); apply: bigcap_inf.
have CBsH: C :&: B \subset D.
    apply/subsetP=> g; rewrite inE; case/andP=> _ HH.
    by apply: (subsetP (BsD)).
have I1B: i1 1%g ^+ 2 <= #|C:D|%:R.
  case: (irr1_bound i2)=> HH _; move: HH.
  have->: i2 1%g = i1 1%g.
    by rewrite qirrcE // -(coset_id (group1 B)) (qfuncE _ BnC) ?is_char_irr.
  move/leC_trans; apply.
  rewrite -leq_leC // -(index_quotient_eq CBsH) ?normal_norm //.
  rewrite -(@leq_pmul2l #|ccenter (C / B)%G i2|) ?cardG_gt0 ?ccenter_sub //.
  rewrite  LaGrange ?quotientS ?ccenter_sub //.
  rewrite -(@leq_pmul2l #|(D/B)%g|) ?cardG_gt0 //.
  rewrite mulnA mulnAC LaGrange ?quotientS //.
  rewrite mulnC leq_pmul2l ?cardG_gt0 // subset_leq_card //.
  by apply: (subset_trans QsZ).
have IC': is_char G ('Ind[G, C] i1).
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