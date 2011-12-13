(* (c) Copyright Microsoft Corporation and Inria. All rights reserved. *)
Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq path div choice.
Require Import fintype tuple finfun bigop prime ssralg poly finset center.
Require Import fingroup morphism perm automorphism quotient action zmodp.
Require Import matrix mxalgebra mxrepresentation cyclic.
Require Import vector algC classfun character inertia vcharacter.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GroupScope GRing.Theory.
Local Open Scope ring_scope.

(**************************************************************************)
(* This file contains the proof of Section1 of Peterfalvi's book          *)
(**************************************************************************)

Section Main.

Variable gT : finGroupType.

(* This is Peterfalvi (1.1). *)
Lemma odd_eq_conj_irr1 (G : {group gT}) t :
  odd #|G| -> (('chi[G]_t)^*%CF == 'chi_t) = ('chi_t == 1).
Proof.
move=> OG; apply/eqP/eqP=> [Ht | ->]; last exact: cfConjC1.
pose a := (@Zp1 1).
have Aito:
    is_action <[a]> (fun (t : Iirr G) v => if v == a then conjC_Iirr t else t).
  split=> [[[|[]]] //= _  t1 t2 Hj |j [[|[]]] // HH1 [[|[]]] // HH2 ] //=.
    by apply: (inv_inj (@conjC_IirrK _ _)).
  by rewrite conjC_IirrK.
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
have F2 u x y: x \in G -> y \in cto (x ^: G) a -> 'chi_u x = 'chi_(ito u a) y.
  rewrite mem_invg -{2}[y]invgK => Gx {y}/imsetP[y Gy ->].
  by rewrite -conjVg cfunJ {y Gy}//= conjC_IirrE cfunE -irr_inv invgK.
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
  by move/eqP: Hd->; rewrite chi0_1.
have:= card_afix_irr_classes (cycle_id a) F1 F2.
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
  apply: chi_inj; apply/cfunP=> g.
  by rewrite conjC_IirrE cfConjCE chi0_1 cfun1E conjC_nat.
rewrite (cardD1 t) //.
suff->: t \in [predD1 'Fix_ito[a] & 0] by [].
rewrite inE /= Hd.
apply/afixP=> b; rewrite !inE; move/eqP->; rewrite /=.
apply: chi_inj; apply/cfunP=> g.
by rewrite conjC_IirrE Ht.
Qed.

Variables G H : {group gT}.

(* This is Peterfalvi (1.2). *)
Lemma not_in_ker_char0 t g : g \in G ->
  H <| G -> ~ (H \subset cfker 'chi[G]_t) -> 'C_H[g] = 1%g -> 'chi_t g = 0.
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
have:= second_orthogonality_relation g GiG.
rewrite mulrb class_refl => <-.
have:= second_orthogonality_relation (coset H g) F1.
rewrite mulrb class_refl => <-; rewrite -!(eq_bigr _ (fun _ _ => normCK _)).
rewrite sum_norm_irr_Quo // (bigID (fun i => H \subset cfker 'chi_i)) //=.
set S := \sum_(i | ~~ _) _; set S' := \sum_(i | _) _ => HH.
have F2: 0 = S.
  apply: leC_anti; last by rewrite -(leC_add2l S') addr0.
  by apply: posC_sum => j _; rewrite posC_mul ?posC_norm.
apply/eqP; have: `|'chi_t g| ^+ 2 == 0.
  apply/eqP; apply: (posC_sum_eq0 _ (sym_equal F2)); last exact/negP.
  by move=> j _; rewrite posC_mul ?posC_norm.
by rewrite mulf_eq0 orbb normC_eq0.
Qed.

Lemma cfdot_complement (A : {set gT}) u v :
  u \in 'CF(H, A) -> v \in 'CF(H, H :\: A) -> '[u, v] = 0.
Proof.
move=> CFu CFv; rewrite (cfdotElr CFu CFv).
by rewrite setDE setICA setICr setI0 big_set0 mulr0.
Qed.

Lemma memc_class_compl A :
  A <| H -> ('CF(H, A) + 'CF(H, H :\: A)%SET = 'CF(H))%VS.
Proof.
case/andP=> AsH nAH; rewrite -cfunGid [X in _ = X]cfun_on_sum.
rewrite (bigID (fun xG : {set gT} => xG \subset A)) /=.
congr (_ + _)%VS; rewrite cfun_on_sum; apply: eq_bigl => /= xG.
  rewrite andbAC; apply/esym/andb_idr=> /andP[/imsetP[x Gx ->] _].
  by rewrite class_subG.
rewrite -andbA; apply: andb_id2l => /imsetP[x Gx ->].
by rewrite !class_sub_norm ?normsD ?normG // inE andbC.
Qed.

(* This is Peterfalvi (1.3)(a) *)
Lemma equiv_restrict_compl A m (Phi : m.-tuple 'CF(H)) (mu : 'CF(G)) d :
    H \subset G -> A <| H -> is_basis 'CF(H, A) Phi ->
  ({in A, mu =1 \sum_i d i *: 'chi_i} <-> 
    (forall j : 'I_m,
        \sum_i '[Phi`_j, 'chi_i] * (d i)^* = '['Ind[G] Phi`_j, mu])).
Proof.
move=> sHG nsAH BPhi; have [sAH nAH] := andP nsAH.
have APhi (i : 'I_m) : Phi`_i \in 'CF(H, A).
  by apply: (memv_is_basis BPhi _); apply: mem_nth; rewrite size_tuple.
pose D := 'Res[H] mu - \sum_i d i *: 'chi_i.
transitivity (D \in 'CF(H, H :\: A)).
  split=> [A'D | /cfun_onP A'D x Ax].
    apply/cfun_onP=> x; rewrite inE negb_and negbK.
    case/orP=> [Ax | /cfun0-> //]; rewrite !cfunE -A'D //.
    by rewrite cfResE ?subrr ?(subsetP sAH).
  have:= A'D x; rewrite !cfunE !inE Ax => /(_ isT)/(canRL (subrK _)).
  by rewrite add0r cfResE // ?(subsetP sAH).
have F0 (j : 'I_m) : 
   (\sum_i '[Phi`_j, 'chi_i] * (d i)^* == '['Ind Phi`_j, mu])
      = ('[Phi`_j, D] == 0).
  rewrite raddf_sub raddf_sum /= Frobenius_reciprocity subr_eq0 eq_sym.
  by congr (_ == _); apply: eq_bigr=> i _; rewrite cfdotZr mulrC.
split=> [HH j | HH].
  by apply/eqP; rewrite F0; apply/eqP; apply: cfdot_complement.
have{F0} F1 (j : 'I_m) : '[Phi`_j, D]_H = 0.
  by have/eqP := HH j; rewrite F0 => /eqP.
have: (D \in 'CF(H))%VS by rewrite memvf.
rewrite -(memc_class_compl nsAH).
case/memv_addP=> /= f [g [Cf Cg defD]].
have: '[f, f + g] = 0.
  rewrite -defD (is_span_span (is_span_is_basis BPhi) Cf) cfdot_suml.
  by rewrite big1 // => i _; rewrite cfdotZl F1 mulr0.
rewrite raddfD /= {1}(cfdot_complement Cf Cg) addr0 => /eqP.
by rewrite cfnorm_eq0 defD => /eqP->; rewrite add0r.
Qed.

(* This is Peterfalvi (1.3)(b). *)
Lemma equiv_restrict_compl_ortho A m  (Phi : m.-tuple 'CF(H)) mu_ :
    H \subset G -> A <| H -> is_basis 'CF(H, A) Phi -> 
     (forall i j, '[mu_ i, mu_ j] = (i == j)%:R) ->
     (forall j : 'I_m, 'Ind[G] Phi`_j = \sum_i '[Phi`_j, 'chi_i] *: mu_ i) ->
   [/\ forall i, {in A, mu_ i =1 'chi_i}
     & forall mu, (forall i, '[mu, mu_ i] = 0) -> {in A, forall x, mu x = 0}].
Proof.
move=> HsG nsAH /equiv_restrict_compl Phi_A Mo IP; split=> [/= i | mu Cmu x Ax].
  have->: 'chi[H]_i = \sum_j (j == i)%:R *: 'chi_j.
    rewrite (bigD1 i) //= eqxx scale1r big1 ?addr0 // => j /negPf->.
    by rewrite scale0r.
  apply/Phi_A=> // j; rewrite IP cfdot_suml.
  by apply: eq_bigr=> k _; rewrite cfdotZl rmorph_nat Mo.
transitivity ((\sum_j 0 *: 'chi[H]_j) x); last first.
  by rewrite sum_cfunE big1 // => j _; rewrite cfunE mul0r.
move: x Ax; apply/Phi_A=> // j.
rewrite mulr_suml rmorph0 mulr0 IP cfdot_suml big1 // => k _.
by rewrite cfdotZl [d in _ * d]cfdotC Cmu rmorph0 mulr0.
Qed.

Let vchar_isometry_base3 f f' : 
  f \in 'Z[irr G, G^#] -> '[f]_G = 2%:R ->
  f' \in 'Z[irr G, G^#] -> '[f']_G = 2%:R ->
  '[f, f'] = 1 ->
   exists es : _ * bool, let: (i, j, k, epsilon) := es in
     [/\  f = (-1) ^+ epsilon *: ('chi_j - 'chi_i),
          f' = (-1) ^+ epsilon *: ('chi_j - 'chi_k)
        & uniq [:: i; j; k]].
Proof.
move=> Hf H2f Hf1 H2f1.
have [j [i neq_ij ->]] := vchar_norm2 Hf H2f.
have [j' [k neq_kj' ->]] := vchar_norm2 Hf1 H2f1.
rewrite cfdot_subl !cfdot_subr !cfdot_irr oppr_sub addrAC !addrA.
do 2!move/(canRL (subrK _)); rewrite -(natr_add _ 1) -!natr_add => /eqP.
rewrite -eqN_eqC; have [eq_jj' | neq_jj'] := altP (j =P j').
  rewrite (eq_sym j) -eq_jj' {1}eq_jj' (negbTE neq_ij) (negbTE neq_kj').
  rewrite eqSS (can_eq oddb) => /eqP neq_ik; exists (i, j, k, false).
  by rewrite !scaler_sign /= !inE neq_ik orbF neq_ij eq_sym eq_jj' neq_kj'.
case: (i =P k) => // eq_ik; exists (j, i, j', true).
rewrite !scaler_sign !oppr_sub /= !inE eq_sym negb_or neq_ij neq_jj'.
by rewrite eq_ik neq_kj'.
Qed.

Let vchar_isometry_base4 (eps : bool) i j k n m :
    let f1 := 'chi_j - 'chi_i in
    let f2 := 'chi_k - 'chi_i in
    let f3 := 'chi_n - 'chi_m in
    j != k -> '[f3, f1]_G = (-1) ^+ eps -> '[f3, f2] = (-1) ^+ eps -> 
  if eps then n == i else m == i.
Proof.
move=> /= Hjk; wlog ->: eps n m / eps = false.
  case: eps; last exact; move/(_ false m n)=> IH nm_ji nm_ki.
  by apply: IH; rewrite // -oppr_sub cfdotNl (nm_ji, nm_ki) opprK.
rewrite !cfdot_subl !cfdot_subr !cfdot_irr !oppr_sub addrAC addrA.
do 2!move/(canRL (subrK _)); rewrite -(natr_add _ 1) -!natr_add.
move/(can_inj getNatC_nat); case: (m == i) => //.
case: eqP => // ->; case: (j == i) => // _.
rewrite subr0 add0r => /(canRL (subrK _)); rewrite -(natr_add _ 1).
by move/(can_inj getNatC_nat); rewrite (negbTE Hjk).
Qed.

(* This is Peterfalvi (1.4). *)
Lemma vchar_isometry_base m L (Chi : m.-tuple 'CF(H)) 
                            (tau : {linear 'CF(H) -> 'CF(G)}) :
    (1 < m)%N -> {subset Chi <= irr H} -> free Chi ->
    (forall chi, chi \in Chi -> chi 1%g = Chi`_0 1%g) ->
    (forall i : 'I_m, (Chi`_i - Chi`_0) \in 'CF(H, L)) ->
    {in 'Z[Chi, L], isometry tau, to 'Z[irr G, G^#]} ->
    exists2 mu : m.-tuple (Iirr G),
      uniq mu
    & exists epsilon : bool, forall i : 'I_m,
      tau (Chi`_i - Chi`_0) = (-1) ^+ epsilon *: ('chi_(mu`_i) - 'chi_(mu`_0)).
Proof. 
case: m Chi => [|[|m]] // Chi _ irrChi uniqChi Chi1 ChiCF [iso_tau Ztau].
rewrite -(tnth_nth 0 _ 0); set chi := tnth Chi.
have chiE i: chi i = Chi`_i by rewrite -tnth_nth.
have inChi i: chi i \in Chi by exact: mem_tnth.
have{irrChi} irrChi i: chi i \in irr H by exact: irrChi.
have eq_chi i j: (chi i == chi j) = (i == j).
  by rewrite /chi !(tnth_nth 0) nth_uniq ?size_tuple ?uniq_free.
have dot_chi i j: '[chi i, chi j] = (i == j)%:R.
  rewrite -eq_chi; have [/irrP[{i}i ->] /irrP[{j}j ->]] := (irrChi i,irrChi j).
  by rewrite cfdot_irr inj_eq //; exact: chi_inj.
pose F i j := chi i - chi j.
have DF i j : F i j =  F i 0 - F j 0 by rewrite /F oppr_sub addrA subrK.
have ZF i j: F i j \in 'Z[Chi, L].
  rewrite vchar_split; apply/andP; split.
    by apply: sub_vchar; apply: mem_vchar.
  by rewrite DF memv_sub // /F !chiE.
have htau2 i j: i != j -> '[tau (F i j)] = 2%:R.
  rewrite iso_tau // cfnorm_sub -cfdotC !dot_chi !eqxx eq_sym => /negbTE->.
  by rewrite -!natr_add subr0.
have htau1 i j: j != 0 -> j != i -> i != 0 -> '[tau (F i 0), tau (F j 0)] = 1.
  rewrite iso_tau // cfdot_subl !cfdot_subr oppr_sub !dot_chi !(eq_sym j).
  by do 3!move/negbTE->; rewrite !subr0 add0r.
have [m0 | nz_m] := boolP (m == 0%N).
  rewrite -2!eqSS eq_sym in m0; move: (htau2 1 0 isT).
  case/(vchar_norm2 (Ztau _ (ZF 1 0))) => [k1 [k0 neq_k01 eq_mu]].
  pose mu := @Tuple _ _ [:: k0; k1] m0.
  exists mu; first by rewrite /= andbT inE.
  exists false => i; rewrite scale1r chiE.
  have: (i : nat) \in iota 0 2 by rewrite mem_iota (eqP m0) (valP i).
  rewrite !inE; case/pred2P=> ->; first by rewrite !subrr linear0.
  by rewrite -eq_mu /F !chiE.
have m_gt2: (2 < m.+2)%N by rewrite !ltnS lt0n.
pose i2 := Ordinal m_gt2.
case: (@vchar_isometry_base3 (tau (F 1 0)) (tau (F i2 0))); auto.
case=> [[[k1 k0] k2] e] []; set d := (-1) ^+ e => eq10 eq20.
rewrite /= !inE => /and3P[/norP[nek10 nek12]]; rewrite eq_sym => nek20 _.
have muP i:
  {k | (i == 0) ==> (k == k0) & tau (F i 0) == d *: ('chi_k0 - 'chi_k)}.
- apply: sig2W; have [-> | nei0] := altP (i =P 0).
    by exists k0; rewrite ?eqxx // /F !subrr !linear0.
  have /(vchar_norm2 (Ztau _ (ZF i 0)))[k [k' nekk' eqFkk']] := htau2 i 0 nei0.
  have [-> | neq_i1] := eqVneq i 1; first by exists k1; rewrite // -eq10.
  have [-> | neq_i2] := eqVneq i i2; first by exists k2; rewrite // -eq20.
  have:= @vchar_isometry_base4 (~~ e) k0 k1 k2 k k' nek12.
  have ZdK u v w: '[u, v - w]_G = (-1) ^+ (~~ e) * '[u, d *: (w - v)].
    rewrite cfdotZr rmorph_sign mulrA -signr_addb addNb addbb mulN1r.
    by rewrite -cfdotNr oppr_sub.
  rewrite -eqFkk' ZdK -eq10 {}ZdK -eq20 !htau1 //; try by rewrite eq_sym.
  move/(_ (mulr1 _) (mulr1 _)); rewrite /d eqFkk'.
  by case e => /eqP <-; [exists k | exists k']; rewrite ?scaler_sign ?oppr_sub.
pose mu := [tuple of [seq s2val (muP i) | i <- ord_tuple m.+2]]; exists mu.
  rewrite map_inj_uniq ?enum_uniq // => i j.
  case: (muP i) (muP j) => /= ki _ /eqP eq_i0 [/= kj _ /eqP eq_j0] eq_kij.
  apply/eqP; rewrite -eq_chi -subr_eq0 -cfnorm_eq0 -iso_tau ?ZF //.
  rewrite -[chi i](subrK (chi 0)) -addrA linearD eq_i0 eq_kij -eq_j0.
  by rewrite -linearD -oppr_sub subrr !raddf0.
exists (~~ e) => i; rewrite -addbT signr_addb -/d -scalerA scaleN1r oppr_sub.
rewrite -!tnth_nth -/(F i 0) tnth_map tnth_ord_tuple.
suffices /= ->: mu`_0 = k0 by case: (muP i) => /= k _ /eqP.
rewrite -(tnth_nth 0 _ 0) tnth_map tnth_ord_tuple.
by case: (muP 0) => /= k /(k =P k0).
Qed.

(* This is Peterfalvi (1.5)(a) *)
Lemma induced_sum_rcosets t : H <| G ->
  'Res[H] ('Ind[G] 'chi_t)
     = #|'I_G['chi_t] : H|%:R *: \sum_(xi <- ('chi_t ^: G)%CF) xi.
Proof.
set T := 'I_G['chi_t] => nsHG; have [sHG nHG] := andP nsHG.
apply/cfun_inP=> h Hh; rewrite cfResE ?cfIndE // cfunE sum_cfunE.
apply: (canLR (mulKf (neq0GC H))).
rewrite mulrA -natr_mul LaGrange ?sub_inertia //= -/T -cfclass_sum //=.
rewrite -mulr_sumr [s in _ = s]big_mkcond /= (reindex_inj invg_inj).
rewrite (partition_big (conjg_Iirr t) xpredT) //=; apply: eq_bigr => i _.
have [[y Gy chi_i] | not_i_t] := cfclassP _ _ _; last first.
  apply: big1 => z; rewrite groupV => /andP[Gz /eqP def_i].
  by case: not_i_t; exists z; rewrite // -def_i conjg_IirrE.
rewrite  -(card_rcoset _ y) mulr_natl -sumr_const; apply: eq_big => z.
  rewrite mem_rcoset inE (setIidPl nHG) groupMr ?groupV //.
  apply: andb_id2l => Gz; rewrite (cfConjgM _ nsHG) ?groupV //.
  rewrite (can2_eq (cfConjgKV y) (cfConjgK y)) -chi_i -conjg_IirrE.
  by rewrite inj_eq //; exact: chi_inj.
rewrite groupV; case/andP=> Gz /eqP <-.
by rewrite conjg_IirrE cfConjgE ?(subsetP nHG).
Qed.

(* This is Peterfalvi (1.5)(b), main formula. *)
Lemma induced_prod_index t :
  H <| G -> '['Ind[G] 'chi[H]_t] = #|'I_G['chi_t] : H|%:R.
Proof.
set r := _%:R => HnG; have HsG := normal_sub HnG.
rewrite -Frobenius_reciprocity induced_sum_rcosets //= cfdotZr rmorph_nat -/r.
rewrite -cfclass_sum // cfdot_sumr (bigD1 t) ?cfclass_refl //= cfdot_irr eqxx.
rewrite big1 ?addr0 ?mulr1 // => j /andP[_ /negbTE].
by rewrite eq_sym cfdot_irr => ->.
Qed.

(* This is Peterfalvi (1.5)(b), irreducibility remark. *)
Lemma inertia_Ind_irr t :
  H <| G -> 'I_G['chi[H]_t] \subset H -> 'Ind[G] 'chi_t \in irr G.
Proof.
rewrite -indexg_eq1 => nsHG /eqP r1.
rewrite char_cfnorm_irrE ?cfInd_char ?irr_char //.
by rewrite induced_prod_index ?r1.
Qed.

(* GG: keeping as is, but it is highly unlikely that the if-then-else style *)
(* conclusion will be usable; as the first part is already covered by       *)
(* cfclass_Ind, it would make sense to only keep the orthogonality part.    *)
(* This is Peterfalvi (1.5)(c). *)
Lemma cfclass_irr_induced t1 t2 : H <| G ->
   if 'chi_t2 \in ('chi[H]_t1 ^: G)%CF
   then 'Ind[G] 'chi_t1 = 'Ind[G] 'chi_t2 
   else '['Ind[G] 'chi_t1, 'Ind[G] 'chi_t2] = 0.
Proof.
move=> nsHG; have [/cfclass_Ind-> // | not_ch1Gt2] := ifPn.
rewrite -Frobenius_reciprocity induced_sum_rcosets // cfdotZr rmorph_nat.
rewrite cfdot_sumr -cfclass_sum // big1 ?mulr0 // => j; rewrite cfdot_irr.
case: eqP => // <- /idPn[]; apply: contra not_ch1Gt2 => /cfclassP[y Gy ->].
by apply/cfclassP; exists y^-1%g; rewrite ?groupV ?cfConjgK.
Qed.

(* A more useful reformulation of (1.5)(c) *)
Lemma not_cfclass_Ind_ortho i j :
    H <| G -> ('chi_i \notin 'chi_j ^: G)%CF ->
  '['Ind[G, H] 'chi_i, 'Ind[G, H] 'chi_j] = 0. 
Proof. by move/(cfclass_irr_induced i j); rewrite cfclass_sym; case: ifP. Qed.

Lemma cfclass_Ind_irrP i j :
    H <| G ->
  reflect ('Ind[G, H] 'chi_i = 'Ind[G, H] 'chi_j) ('chi_i \in 'chi_j ^: G)%CF.
Proof.
move=> nsHG; have [sHG _] := andP nsHG.
case: ifP (cfclass_irr_induced j i nsHG) => [|_ Oji]; first by left.
right=> eq_chijG; have /negP[]: 'Ind[G] 'chi_i != 0 by exact: Ind_irr_neq0.
by rewrite -cfnorm_eq0 {1}eq_chijG Oji.
Qed.

(* This is Peterfalvi (1.5) (d). *)
Lemma induced_sum_rcosets1 t : H <| G ->
  let chiG := 'Ind[G] 'chi_t in
  (chiG 1%g / '[chiG]) *: 'Res[H] chiG
     = #|G : H|%:R *: (\sum_(xi <- ('chi_t ^: G)%CF) xi 1%g *: xi).
Proof.
move=> nsHG chiG; have [sHG _] := andP nsHG.
rewrite induced_sum_rcosets // induced_prod_index // scalerA cfInd1 //.
rewrite divfK -?neq0N_neqC -?lt0n // -scalerA linear_sum -!cfclass_sum //=.
congr (_ *: _); apply: eq_bigr => _ /cfclassP[y _ ->].
by rewrite cfConjg_val1.
Qed.

(* This is Peterfalvi (1.5)(e). *)
Lemma odd_induced_orthogonal t :
     H <| G -> odd #|G| -> t != 0 ->
  '['Ind[G, H] 'chi_t, ('Ind[G] 'chi_t)^*] = 0. 
Proof.
move=> nsHG oddG nz_t; have [sHG _] := andP nsHG.
have:= cfclass_irr_induced t (conjC_Iirr t) nsHG.
rewrite conjC_IirrE conj_cfInd; case: cfclassP => // [[g Gg id_cht]].
have oddH: odd #|H| := pgroup.oddSg sHG oddG.
case/eqP: nz_t; apply: chi_inj; rewrite chi0_1.
apply/eqP; rewrite -odd_eq_conj_irr1 // id_cht; apply/eqP.
have F1: ('chi_t ^ (g ^+ 2))%CF = 'chi_t.
  rewrite (cfConjgM _ nsHG) // -id_cht -cfConjg_conjC -id_cht.
  exact: cfConjCK.
suffices /eqP->: g == ((g ^+ 2) ^+ #|G|./2.+1)%g.
  elim: _./2.+1 => [|n IHn]; first exact: cfConjg1.
  by rewrite expgS (cfConjgM _ nsHG) ?groupX // F1.
rewrite eq_mulVg1 expgS -expgn_mul mul2n -mulgA mulKg -expgS -order_dvdn.
by rewrite -add1n -[1%N](congr1 nat_of_bool oddG) odd_double_half order_dvdG.
Qed.

(* This is Peterfalvi (1.6)(a). *)
Lemma sub_cfker_Ind_irr A i :
    G \subset 'N(A) -> H \subset G ->
  (A \subset cfker ('Ind[G, H] 'chi_i)) = (A \subset cfker 'chi_i).
Proof. by move=> nAG sHG; rewrite cfker_Ind_irr ?sub_gcore. Qed.

Lemma cfInd_irr_eq1 i :
  H <| G -> ('Ind[G, H] 'chi_i == 'Ind[G, H] 1) = (i == 0).
Proof.
case/andP=> sHG nHG; apply/eqP/idP=> [chi1 | /eqP->]; last by rewrite chi0_1.
rewrite -subGcfker -(sub_cfker_Ind_irr _ nHG sHG) chi1 -chi0_1.
by rewrite sub_cfker_Ind_irr ?cfker_chi0.
Qed.

(* This is Peterfalvi (1.6)(b). *)
Lemma induced_quotientE (A : {group gT}) t :
    H <| G -> A <| G -> A \subset cfker 'chi[H]_t ->
  'Ind[G / A] ('chi_t / A)%CF = ('Ind[G] 'chi_t / A)%CF.
Proof.
move=> HnG AnG AsK.
have AsH := subset_trans AsK (cfker_sub _).
have [[HsG nHG] [sAG nAG]] := (andP HnG, andP AnG).
have AnH := normalS AsH HsG AnG.
have HAnGA := quotient_normal A HnG.
move: (AsK); rewrite -(sub_cfker_Ind_irr t nAG HsG) => AsKI.
have CHt := irr_char t.
have CHq := cfQuo_char A CHt.
have CHi := cfInd_char G CHt.
have CHiq := cfInd_char (G / A) CHq.
have CHqi := cfQuo_char A CHi.
apply/cfun_inP=> /= _  /morphimP[g Ng Gg ->]; rewrite cfQuoE //.
have [Hg | notHg] := boolP (g \in H); last first.
  rewrite !(cfun_on0 (cfInd_normal _ _)) //.
  by rewrite -(quotientGK AnH) !(Ng, inE) in notHg.
rewrite !cfIndE ?quotientS //; apply: (canRL (mulKf (neq0GC H))).
rewrite -(LaGrange AsH) natr_mul mulrA -card_quotient ?normal_norm //.
rewrite (mulfK (neq0GC _)) -mulr_sumr.
rewrite (partition_big _  _ (fun x => (mem_quotient A) x G)) /=.
apply: eq_bigr => _ /morphimP[x Nx Gx ->].
rewrite -morphJ // cfQuoE ?memJ_norm ?(subsetP nHG) //.
rewrite -(card_lcoset A x) mulr_natl -sumr_const.
apply: eq_big => [z | _ /lcosetP[a Aa ->]]; last first.
  by have Ha := subsetP AsH a Aa; rewrite conjgM (cfunJ _ _ Ha).
have [Gz | ] := boolP (z \in G).
  have Nz := subsetP nAG z Gz.
  by rewrite -norm_rlcoset // (sameP eqP (rcoset_kercosetP _ _)).
by apply: contraNF => /lcosetP[a Aa ->]; rewrite groupMr // (subsetP sAG).
Qed.

Variable t : Iirr H.

Let T := 'I_G['chi_t]%G.

Hypothesis HnG: H <| G.

Lemma IndGT_chi: ('Ind[G] 'chi_t) = 'Ind[G] ('Ind[T] 'chi_t).
Proof.
apply/cfun_inP=> x Hx; rewrite !cfIndE ?inertia_sub ?normal_sub //.
rewrite -!mulr_sumr; apply:eq_bigr => i Hi.
rewrite !cfIndE; last by rewrite sub_inertia.
rewrite (eq_bigr (fun y => 'chi_t (x ^ i))).
  rewrite  sumr_const -(mulr_natr ('chi_t _))(mulrC #|T|%:R^-1).
  rewrite -!mulrA -mulr_natr  mulfV ?mulr1 //.
  by move: (cardG_gt0 T); rewrite -neq0N_neqC;case: #|T|.
move => y;rewrite inE;case/andP; rewrite inE =>/andP [] _ Hy /eqP {1}<-.
by rewrite cfConjgE // -conjgM mulgV conjg1.
Qed.

(* This is Peterfalvi (1.7) (a). *)
Lemma induced_inertia_irr (i j: Iirr T):
        i \in irr_constt ('Ind[T] 'chi_t) -> 
        j \in irr_constt ('Ind[T] 'chi_t) -> 
        ('Ind[G] 'chi_i) \in irr G /\ 
        (('Ind[G]'chi_i == 'Ind[G]'chi_j) -> (i == j))/\
        'Ind[G] 'chi_t = \sum_(i \in irr_constt ('Ind[T] 'chi_t)) 
                             '['Ind[T] 'chi_t, 'chi_i] *: ('Ind[G] 'chi_i).
Proof.
move=> Hi Hj;
pose Ht1:= (cfun_sum_constt ('Ind[T] 'chi_t));split;[|split].
  - apply: cfInd_constt_inertia_irr =>//.
  by rewrite -constt_Ind_constt_Res.
  - by move=>/eqP/constt_inertia_inj -> //; 
   rewrite inE -constt_Ind_constt_Res.
rewrite IndGT_chi // {1}Ht1 !linear_sum.
by apply:eq_bigr=> i0 _; rewrite linearZ.
Qed.

Hypothesis QTHa : abelian (T / H)%G.

Lemma inertia_quo_cfReg:
            cfMod (cfReg (T / H)%G) = \sum_(i | H \subset cfker 'chi_i) 'chi_i.
Proof.
rewrite cfReg_sum linear_sum (eq_bigr (fun  i => (cfMod 'chi_i)));first last.
  move => i _ ;rewrite linearZ;move/char_abelianP: QTHa; move/(_ i).
  by move/lin_char1 ->; rewrite scale1r.
have HNT: H <| T by apply:(@normalS _ G T H);rewrite ?sub_inertia ?inertia_sub.
rewrite (reindex _ (mod_Iirr_bij HNT)) /=.
by apply/eq_big=> [i | i _]; rewrite mod_IirrE ?cfker_Mod.
Qed.

Lemma inertia_ker_1 (l: Iirr T) x :
          H \subset cfker 'chi_l -> x \in H -> 'chi_l x = 1.
move=>Hl Hx. 
have HNT: H <| T by apply:(@normalS _ G T H);rewrite ?sub_inertia ?inertia_sub.
have [sHT _] := andP HNT.
rewrite -(cfQuoE HNT Hl (subsetP sHT _ Hx)) -quo_IirrE //.
rewrite coset_id; move/char_abelianP: QTHa; move/(_ (quo_Iirr H l))=>//.
by move/lin_char1 ->.
Qed.

Lemma inertia_ker_sum x i1 :(i1 \in irr_constt('Ind[T] 'chi_t)) ->
       (\sum_(l | H \subset cfker 'chi_l) ('chi_l * 'chi_i1) x) =  
          #|T:H|%:R  * (x \in H)%:R * ('chi_i1 x).
move=>Hi1.
have HNT: H <| T by apply:(@normalS _ G T H);rewrite ?sub_inertia ?inertia_sub.
have [sHT nHT] := andP HNT; have [sHG nHG] := andP HnG.
rewrite (eq_bigr (fun l => 'chi_l x * 'chi_i1 x));first last.
  by move=> l Hl; rewrite cfunE.
rewrite mulr_suml -sum_cfunE.
have [HxT | notHxT] := boolP (x \in T); last first.
  by move/supportP:(support_cfun 'chi_i1); move/(_ x notHxT)->; rewrite !mulr0.
rewrite -inertia_quo_cfReg //;congr ( _ * _);rewrite cfModE // ?cfRegE.
rewrite card_quotient //  -mulr_natr.
by rewrite ( sameP eqP (kerP _ (subsetP nHT x HxT))) ker_coset.
Qed.

Lemma  I_K_sum_IndRes i1: (i1 \in irr_constt('Ind[T] 'chi_t) )-> 
  'Ind[T]('Res[H] 'chi_i1) = 
     (\sum_(l | H \subset cfker 'chi_l) ('chi_l * 'chi_i1)).
move=> Hi1.
have HNT: H <| T by apply:(@normalS _ G T H);rewrite ?sub_inertia ?inertia_sub.
have [sHT nHT] := andP HNT; have [sHG nHG] := andP HnG.
apply/cfunP=> x; rewrite sum_cfunE inertia_ker_sum //.
have [HxH | notHxH] := boolP (x \in H); last first.
  suff ->: 'Ind[T] ('Res[H] 'chi_i1) x = 0 by rewrite mulr0 mul0r.
  rewrite  cfIndE //  big1; first by rewrite mulr0.
  move=> y Hy; move/supportP:(support_cfun ('Res[H] 'chi_i1))->=>//.   
  by rewrite memJ_norm //; apply/(subsetP nHT).
rewrite mulr1 cfIndE // (eq_bigr (fun _ => 'chi_i1 x)).
  rewrite sumr_const -(mulr_natl _ #|T|) mulrA  -(LaGrange sHT).
  congr (_ *_); rewrite natr_mul mulrA mulVf ?mul1r //.
  by move: (cardG_gt0 H); rewrite -neq0N_neqC;case: #|H|.
move => y Hy;rewrite cfResE ?cfunJgen ?genGid //.
by rewrite memJ_norm //; apply/(subsetP nHT).
Qed.

Lemma I_K_lpsi i1 i: i1 \in irr_constt('Ind[T] 'chi_t)->
                  i \in irr_constt('Ind[T] 'chi_t)->  
           exists2 l, (H \subset cfker 'chi_l) & ('chi_l * 'chi_i1 = 'chi_i).
move=> Hi1 Hi.
have cRes:(is_char ('Res[H] 'chi_i)) by rewrite cfRes_char // irr_char.
have t_comp: forall (i: Iirr T), 
        i \in irr_constt ('Ind[T] 'chi_t) -> '['Res[H] 'chi_i, 'chi_t] != 0.
  by move=> j Hj; rewrite -irr_consttE -constt_Ind_constt_Res. 
have irr_lpsi: forall (l: Iirr T) i ,  
     H \subset cfker 'chi_l ->('chi_l * 'chi_i) \in (irr T).
  move=> l j Hl; set psii:='chi_j; 
  rewrite char_cfnorm_irrE; last by rewrite mul_char // irr_char.
  rewrite cfdotE (eq_bigr (fun x => (psii x ) * (psii x)^*)).
    by rewrite -cfdotE -char_cfnorm_irrE ?irr_chi ?irr_char.
  move=> x Hx;rewrite !cfunE rmorphM (mulrC _ (psii x)^*) -!mulrA.
  rewrite(mulrC ('chi_l x)) -!mulrA.
  suff->: ('chi_l x)^* *('chi_l x)= 1 by rewrite mulr1.
  have Hlcl:lin_char 'chi_l by rewrite /lin_char irr_char inertia_ker_1 /=.
  by rewrite mulrC -lin_charV_conj // -lin_charM  ?mulgV ?lin_char1 ?groupV.
have H1:  i \in irr_constt ('Ind[T] ('Res[H] 'chi_i1)).
  move:(t_comp i1 Hi1); move/constt_charP=> Hconstt.
  case:Hconstt =>[| x Hx He]; first by rewrite cfRes_char // irr_char.
  have: 'Ind[T] ('Res[H] 'chi_i1)  = 'Ind[T] 'chi_t + 'Ind[T] x.
    by rewrite He linearD.
  case/constt_charP:Hi; first by rewrite cfInd_char// irr_char.
  move=> u Hu -> H1; apply/constt_charP.
    by rewrite cfInd_char // cfRes_char // irr_char.
  by exists (u + 'Ind[T] x);rewrite ?add_char ?cfInd_char // H1 addrA.
  case: (boolP (forallb l : Iirr T, 
    (H \subset cfker 'chi_l)==>('['chi_l * 'chi_i1, 'chi_i] == 0)));last first.
  rewrite negb_forall_in; move/existsP=> [l /andP [Hl1 Hl2]].
  exists l; first by rewrite Hl1.
  move/irrP: (irr_lpsi  l i1 Hl1);case=> i2 Hi2.
  move: Hl2; rewrite Hi2 cfdot_irr.
  case:(boolP (i2 == i)); first by move/eqP ->.
  by rewrite -neq0N_neqC.
move/forallP=> HH1;move: H1; rewrite irr_consttE I_K_sum_IndRes // cfdot_suml big1.
  by rewrite ?eqxx.
by move=> i0 Hi0; move: (HH1 i0); rewrite Hi0 /=; move/eqP.
Qed.

Lemma Ind_inertia_dot i j:
            i \in irr_constt ('Ind[T] 'chi_t) -> 
            j \in irr_constt ('Ind[T] 'chi_t) -> 
            '['Ind[T] 'chi_t, 'chi_i] = '['Ind[T] 'chi_t, 'chi_j].
move=> Hi Hj.
have lpsi_dot i1 :
       forall (l : Iirr T),   H \subset cfker 'chi_l -> 
      '['Ind[T] 'chi_t, 'chi_l * 'chi_i1] = '['chi_t, 'Res[H]'chi_i1].
  move=> l  Hl /=; rewrite -cfdot_Res_r /cfdot; congr (_ * _).
  apply:eq_bigr=> x Hx; congr (_ * _); apply:(inv_inj conjCK);rewrite !conjCK.
  by rewrite !cfResE ?sub_inertia // cfunE inertia_ker_1 // mul1r.
case:(I_K_lpsi Hi Hi) => li Hli <-.
case:(I_K_lpsi Hi Hj)=> lj Hlj <-.
  by rewrite !lpsi_dot  -?cfdot_Res_r.
Qed.

(* This is Peterfalvi (1.7) (b). *)
 Lemma induced_inertia_quo:
      exists e1:algC, 
     let tcomp := irr_constt ('Ind[T] 'chi_t) in 
     (('Ind[G] 'chi_t = e1 *: \sum_(i \in tcomp) ('Ind[G] 'chi_i)) /\
     #|tcomp|%:R * (e1 ^+ 2) = #|T:H|%:R /\ 
     (forall i, i \in tcomp -> 
        ('Ind[G] 'chi_i)(1%g) = #|G:T|%:R * e1 * ('chi_t 1%g))).
Proof.
have HNT: H <| T by apply:(@normalS _ G T H);rewrite ?sub_inertia ?inertia_sub.
have [sHT nHT] := andP HNT; have [sHG nHG] := andP HnG.
have eiN: forall i, (isNatC '['Ind[T] 'chi_t, 'chi_i]).
  by move=> i; apply:cfdot_char_irr_Nat; rewrite cfInd_char ?irr_char.
case: ( neq0_has_constt (Ind_irr_neq0 t sHT)) => i1 Hi1.
pose e1:= '['Ind[T] 'chi_t, 'chi_i1].
pose psi := 'chi_i1.
exists e1=>/=;rewrite IndGT_chi.
have Hdot i: i \in irr_constt ('Ind[T] 'chi_t) -> 
  '['Ind[T] 'chi_t, 'chi_i] = e1  by move=>Hi;rewrite (Ind_inertia_dot Hi Hi1).
have He: 'Ind[T] 'chi_t = e1*: \sum_(i \in irr_constt ('Ind[T] 'chi_t)) 'chi_i.
  rewrite {1}(cfun_sum_constt ('Ind[T] 'chi_t)) scaler_sumr.
  by apply : eq_bigr =>  i Hi;congr (_ *: _); rewrite Hdot.
have HIGT: 'Ind[G] ('Ind[T] 'chi_t) =
e1 *: (\sum_(i \in irr_constt ('Ind['I_G['chi_t]] 'chi_t)) 'Ind[G] 'chi_i).
  by rewrite /= {1}He linearZ  linear_sum.
split=> //.
have Res_psi: 'Res[H] psi = e1 *:'chi_t.
  rewrite constt_Ind_constt_Res in Hi1.
  rewrite /psi (Clifford_Res_sum_cfclass HNT Hi1) cfclass_inertia.
  congr (_ *:_); last by rewrite big_cons big_nil addr0. 
  by rewrite /e1 cfdot_Res_l cfdotC isNatC_conj.
have Hpsi_1 i: i \in irr_constt('Ind[T] 'chi_t)-> 'chi_i 1%g = e1*('chi_t 1%g).
  move=> Hi; case:(I_K_lpsi Hi1 Hi)=>l Hl <-; rewrite cfunE inertia_ker_1 // mul1r.
  by rewrite -(cfResE psi sHT (group1 H)) Res_psi cfunE.
have He1: 'Ind[T] 'chi_t 1%g = 
       #|irr_constt ('Ind['I_G['chi_t]] 'chi_t)|%:R * e1 ^+ 2 * 'chi_t 1%g. 
  rewrite {1}He cfunE sum_cfunE (eq_bigr (fun _ => e1 * ('chi_t 1%g))) //.
  rewrite sumr_const expr2 (mulrC _ (e1 * e1)) -!(mulrA e1); congr (_ * _).
  by rewrite -mulr_natr -mulrA;congr (_ * _); rewrite mulrC.
have: ('Ind[T] ('Res[H] psi))  1%g =
     (\sum_(l | H \subset cfker 'chi_l) ('chi_l * psi)) 1%g by rewrite I_K_sum_IndRes.
rewrite sum_cfunE (inertia_ker_sum 1%g) // Res_psi linearZ cfunE He1 group1 mulr1  Hpsi_1 //.
rewrite (mulrA  #|T : H|%:R e1) (mulrC _ e1) -(mulrA e1  #|T : H|%:R) => H2.
split; last by move=> i Hi; rewrite cfInd1 ?inertia_sub ?Hpsi_1 ?mulrA.
apply:(@mulfI _ ('chi_t 1%g)); rewrite ?irr1_neq0 // !(mulrC ('chi_t 1%g)).
by apply:(@mulfI _ e1); rewrite  -?irr_consttE.
Qed.


(* This is Isaacs (6.28) . *)
(*Require Import nilpotent.

Lemma xxx: forall (N : {group gT}) (t : Iirr N), N <| G -> 
 solvable (G/N)%G -> forall g ,  g \in G -> ('chi_t ^ g)%CF = 'chi_t -> *)

(* This is Peterfalvi (1.7) (c). *)
Lemma induced_inertia_quo1:
     coprime #|H| #|T:H| -> 
     let tcomp := irr_constt ('Ind[T] 'chi_t) in 
     (('Ind[G] 'chi_t = \sum_(i \in tcomp) ('Ind[G] 'chi_i)) /\
     #|tcomp| = #|T:H| /\ 
     (forall i, i \in tcomp -> 
        ('Ind[G] 'chi_i)(1%g) = #|G:T|%:R * ('chi_t 1%g))).
Proof.
move=> HcardHT.
case:induced_inertia_quo=> //.
move=> e1 H1.
move:(H1); suff ->: e1 = 1;first rewrite /= scale1r exp1rn !mulr1.
  case=> ->; case=> /eqP He Hi; split =>//;split => //.
  by move: He; rewrite -eqN_eqC; move/eqP.
(* from Isaacs 6.28*)
have : exists i: Iirr T , (i \in irr_constt ('Ind[T] 'chi_t)) /\ 
                                '['Ind[G] 'chi_t, 'Ind[G]'chi_i] = 1.
admit.
case => i1 [Hin1 Hi1];rewrite -Hi1; move:H1=> [-> []] => _ _.
rewrite cfdotZl  cfdot_suml (bigD1 i1) //= big1.
  rewrite addr0.
  case (induced_inertia_irr Hin1 Hin1) ; rewrite char_cfnorm_irrE.
    by move/eqP ->; rewrite mulr1.
  by rewrite cfInd_char // irr_char.
move => i /andP [Hi He].
case (induced_inertia_irr Hi Hin1); case/irrP=>ii Hii [Hii1 _].
case (induced_inertia_irr Hin1 Hin1); 
case/irrP=> ii1 Hii1e [] _ _.
rewrite Hii1e Hii cfdot_irr.
case:(boolP (ii == ii1))=>// /eqP Hie.
move:(Hii); rewrite Hie -Hii1e;move/eqP/Hii1=> /eqP he.
by move:He; rewrite he eqxx.
Qed.


(* This is Peterfalvi (1.8). *)
Lemma irr1_bound_quo (B C D : {group gT}) i :
    B <| C -> B \subset cfker 'chi[G]_i ->
    B \subset D -> D \subset C -> C \subset G -> (D / B \subset 'Z(C / B))%g ->
  'chi_i 1%g <= #|G : C|%:R * sqrtC #|C : D|%:R.
Proof.
move=> BnC BsK BsD DsC CsG QsZ.
case: (boolP ('Res[C] 'chi_i == 0))=> [HH|].
  have: ('Res[C] 'chi_i) 1%g = 0 by rewrite (eqP HH) cfunE.
  by rewrite cfResE // => HH1; case/eqP: (irr1_neq0 i).
have IC := cfRes_char C (irr_char i).
case/neq0_has_constt=> i1 Hi1.
have CIr: i \in irr_constt ('Ind[G] 'chi_i1).
  by rewrite inE /= -Frobenius_reciprocity /= cfdotC conjC_eq0.
have BsKi : B \subset cfker 'chi_i1.
  suff BsKri: B \subset cfker ('Res[C] 'chi_i).
    by apply: (subset_trans BsKri); exact: (cfker_constt _ Hi1).
  apply/subsetP=> g GiG.
  have F: g \in C by rewrite (subsetP (subset_trans BsD _)).
  rewrite cfker_charE // inE F !cfResE //.
  by move: (subsetP BsK _ GiG); rewrite cfker_irrE inE.
pose i2 := quo_Iirr B i1.
have ZsC: 'Z(C / B)%g \subset 'Z('chi_i2)%CF.
    by rewrite -(cap_cfcenter_irr (C / B)); apply: bigcap_inf.
have CBsH: C :&: B \subset D.
    apply/subsetP=> g; rewrite inE; case/andP=> _ HH.
    by apply: (subsetP (BsD)).
have I1B: 'chi_i1 1%g ^+ 2 <= #|C : D|%:R.
  case: (irr1_bound i2)=> HH _; move: HH.
  have ->: 'chi_i2 1%g = 'chi_i1 1%g.
    by rewrite quo_IirrE // -(coset_id (group1 B)) cfQuoE.
  move/leC_trans; apply.
  rewrite -leq_leC // -(index_quotient_eq CBsH) ?normal_norm //.
  rewrite -(@leq_pmul2l #|'Z('chi_i2)%CF|) ?cardG_gt0 ?cfcenter_sub //.
  rewrite  LaGrange ?quotientS ?cfcenter_sub //.
  rewrite -(@leq_pmul2l #|(D / B)%g|) ?cardG_gt0 //.
  rewrite mulnA mulnAC LaGrange ?quotientS //.
  rewrite mulnC leq_pmul2l ?cardG_gt0 // subset_leq_card //.
  exact: subset_trans QsZ ZsC.
have IC': is_char ('Ind[G] 'chi_i1) := cfInd_char G (irr_char i1).
move: (char1_ge_constt IC' CIr); rewrite cfInd1 //= => /leC_trans-> //.
have chi1_1_ge0: 0 <= 'chi_i1 1%g by rewrite ltCW ?ltC_irr1.
by rewrite leC_pmul2l ?sposGiC // -(@leC_exp2r 2) ?sqrtC_pos ?posC_nat ?sqrtCK.
Qed.

End Main.


