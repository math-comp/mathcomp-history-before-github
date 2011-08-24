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
Lemma vchar_isometry_base m (Chi : m.-tuple 'CF(H)) 
                            (tau : {linear 'CF(H) -> 'CF(G)}) :
    (1 < m)%N -> {subset Chi <= irr H} -> free Chi ->
    (forall chi, chi \in Chi -> chi 1%g = Chi`_0 1%g) ->
    {in 'Z[Chi, H^#], isometry tau, to 'Z[irr G, G^#]} ->
    exists2 mu : m.-tuple (Iirr G),
      uniq mu
    & exists epsilon : bool, forall i : 'I_m,
       tau (Chi`_i - Chi`_0) = (-1) ^+ epsilon *: ('chi_(mu`_i) - 'chi_(mu`_0)).
Proof. 
case: m Chi => [|[|m]] // Chi _ irrChi uniqChi Chi1 [iso_tau Ztau].
rewrite -(tnth_nth 0 _ 0); set chi := tnth Chi.
have chiE i: chi i = Chi`_i by rewrite -tnth_nth.
have inChi i: chi i \in Chi by exact: mem_tnth.
have{irrChi} irrChi i: chi i \in irr H by exact: irrChi.
have eq_chi i j: (chi i == chi j) = (i == j).
  by rewrite /chi !(tnth_nth 0) nth_uniq ?size_tuple ?uniq_free.
have dot_chi i j: '[chi i, chi j] = (i == j)%:R.
  rewrite -eq_chi; have [/irrP[{i}i ->] /irrP[{j}j ->]] := (irrChi i, irrChi j).
  by rewrite cfdot_irr inj_eq //; exact: chi_inj.
pose F i j := chi i - chi j.
have ZF i j: F i j \in 'Z[Chi, H^#].
  by rewrite vchar_split cfunD1E sub_vchar ?mem_vchar //= !cfunE !Chi1 ?subrr.
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
Lemma cfker_induced_irr_sub (A : {group gT}) t :
    H <| G -> A <| G -> A \subset H ->
  (A \subset cfker 'chi[H]_t) = (A \subset cfker ('Ind[G] 'chi_t)).
Proof.
move=> HnG AnG AsH; have [HsG _ ] := andP HnG; have [sAG nAG] := andP AnG.
have Cht := irr_char t.
have Cit := cfInd_char G Cht; have Crt := cfRes_char H Cit.
apply/idP/idP=> [AsC|AsI].
  apply /subsetP=> g GiA; rewrite cfker_charE ?inE ?(subsetP sAG) //=.
  rewrite !cfIndE //=; apply/eqP; congr (_ * _); apply: eq_bigr => h Gh.
  by rewrite conj1g cfker1 ?(subsetP AsC) ?memJ_norm ?(subsetP nAG).
have: A \subset cfker ('Res[H] ('Ind[G] 'chi_t)).
  apply/subsetP=> g Ag.
  move: (subsetP AsI _ Ag).
  rewrite !cfker_charE ?inE // => /andP [] _ HH.
  by rewrite !cfResE ?(subsetP AsH).
move/subset_trans; apply.
apply: cfker_constt => //; rewrite induced_sum_rcosets // scaler_sumr.
rewrite -cfclass_sum //= inE /= cfdot_suml (bigD1 t) ?cfclass_refl //=.
rewrite cfdotZl cfdot_irr eqxx mulr1 big1 ?addr0 => [|j /andP[_]].
  by rewrite -(eqN_eqC _ 0) -lt0n.
by rewrite cfdotZl cfdot_irr => /negbTE->; rewrite mulr0.
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
move: (AsK); rewrite (cfker_induced_irr_sub t HnG) => // AsKI.
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

(* This is Peterfalvi (1.8). *)
Lemma irr1_bound_quo (B C D : {group gT}) i :
    B <| C -> B \subset cfker 'chi[G]_i ->
    B \subset D -> D \subset C -> C \subset G -> (D / B \subset 'Z(C / B))%g ->
  ('chi_i 1%g) ^+ 2 <= #|G|%:R ^+ 2 / #|C|%:R / #|D|%:R.
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
  by move: (subsetP BsK _ GiG); rewrite cfker_irrE inE (subsetP CsG) ?F.
pose i2 := quo_Iirr B i1.
have ZsC: 'Z(C / B)%g \subset 'Z('chi_i2)%CF.
    by rewrite -(cap_cfcenter_irr (C / B)); apply: bigcap_inf.
have CBsH: C :&: B \subset D.
    apply/subsetP=> g; rewrite inE; case/andP=> _ HH.
    by apply: (subsetP (BsD)).
have I1B: 'chi_i1 1%g ^+ 2 <= #|C:D|%:R.
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
move: (char1_ge_constt IC' CIr); rewrite cfInd1 //= => HH1.
apply: (leC_trans (leC_square (char1_pos (irr_char i)) HH1)).
rewrite commr_exp_mull; last by apply: mulrC.
have F8: 0 < #|C|%:R^+2 by apply: sposC_mul; apply sposGC.
rewrite -(leC_pmul2l _ _ F8) mulrA -commr_exp_mull; last by apply: mulrC.
rewrite -natr_mul LaGrange // [#|C|%:R ^+ 2 *_]mulrC -!mulrA.
rewrite !(leC_pmul2l,sposGC) //  [#|D|%:R ^-1 * _]mulrC !mulrA.
rewrite mulVf ?neq0GC // mul1r -(LaGrange DsC) mulrC.
by rewrite natr_mul mulrA mulVf ?(mul1r,neq0GC).
Qed.

End Main.