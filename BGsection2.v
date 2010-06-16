Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq div.
Require Import fintype bigops prime binomial finset ssralg.
Require Import groups morphisms normal automorphism commutators zmodp.
Require Import gprod cyclic center pgroups gseries nilpotent sylow abelian.
Require Import maximal matrix mxrepresentation BGsection1.

(******************************************************************************)
(* This file covers the useful material in B & G, Section 2. This excludes    *)
(* part (c) of Proposition 2.1 and part (b) of Proposition 2.2, which are not *)
(* actually used in the rest of the proof; also the rest of Proposition 2.1   *)
(* is already covered by material in file mxrepresentation.v.                 *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Import GroupScope GRing.Theory.
Open Local Scope ring_scope.

Implicit Arguments socle_exists [F gT G n].

Section BGsection2.

Implicit Type F : fieldType.
Implicit Type gT : finGroupType.
Implicit Type p : nat.

(* File mxrepresentation.v covers B & G, Proposition 2.1 as follows:          *)
(* - Proposition 2.1 (a) is covered by Lemmas mx_abs_irr_cent_scalar and      *)
(*     cent_mx_scalar_abs_irr.                                                *)
(* - Proposition 2.2 (b) is our definition of "absolutely irreducible", and   *)
(*   is thus covered by cent_mx_scalar_abs_irr and mx_abs_irrP.               *)
(* - Proposition 2.2 (c) is partly covered by the construction in submodule   *)
(*   MatrixGenField, which extends the base field with a single element a of  *)
(*   K = Hom_FG(M, M), rather than all of K, thus avoiding the use of the     *)
(*   Wedderburn theorem on finite division rings (by the primitive element    *)
(*   theorem this is actually equivalent). The corresponding representation   *)
(*   is built by MatrixGenField.gen_repr. In B & G, Proposition 2.1(c) is     *)
(*   only used in case II of the proof of Theorem 3.10, which we greatly      *)
(*   simplify by making use of the Wielandt fixpoint formula, following       *)
(*   Peterfalvi (Theorem 9.1). In this formalization the limited form of      *)
(*   2.1(c) is used to streamline the proof that groups of odd order are      *)
(*   p-stable (B & G, Appendix A.5(c)).                                       *)

(* This is B & G, Proposition 2.2 (a), using internal isomorphims (mx_iso).   *)
Lemma mx_irr_prime_index : forall F gT (G H : {group gT}) n M,
    forall (nsHG : H <| G) (rG : mx_representation F G n),
    let rH := subg_repr rG (normal_sub nsHG) in
    group_closure_field F gT -> mx_irreducible rG -> cyclic (G / H)%g ->
    mxsimple rH M -> {in G, forall x, mx_iso rH M (M *m rG x)} ->
  mx_irreducible rH.
Proof.
move=> F gT G H n M nsHG rG rH closedF irrG cycGH simM isoM.
have [modM nzM _] := simM; pose E_H := enveloping_algebra_mx rH.
have absM: forall f, (M *m f <= M)%MS -> {a | (a \in E_H)%MS & M *m a = M *m f}.
  move=> f sMf; set rM := submod_repr modM; set E_M := enveloping_algebra_mx rM.
  pose u := mxvec (in_submod M (val_submod 1%:M *m f)) *m pinvmx E_M.
  have EHu: (gring_mx rH u \in E_H)%MS := gring_mxP rH u.
  exists (gring_mx rH u) => //; rewrite -(in_submodK sMf).
  rewrite -(in_submodK (mxmodule_envelop modM EHu _)) //; congr (val_submod _).
  transitivity (in_submod M M *m gring_mx rM u).
    rewrite /gring_mx /= !mulmx_sum_row !linear_sum; apply: eq_bigr => i /= _.
    by rewrite !linearZ /= !rowK !mxvecK -in_submodJ.
  rewrite /gring_mx /= mulmxKpV ?submx_full ?mxvecK //; last first.
    suffices: mx_absolutely_irreducible rM by case/andP.
    by apply: closedF; exact/submod_mx_irr.
  rewrite {1}[in_submod]lock in_submodE -mulmxA mulmxA -val_submodE -lock.
  by rewrite mulmxA -in_submodE in_submodK.
have [sHG nHG] := andP nsHG; case/cyclicP: cycGH => Hx defGH.
have: Hx \in (G / H)%g by rewrite defGH cycle_id.
case/morphimP=> x nHx Gx defHx.
have{Hx defGH defHx} defG : G :=: <[x]> <*> H.
  rewrite -(quotientGK nsHG) defGH defHx -quotient_cycle //.
  by rewrite mulgenC quotientK ?norm_mulgenEr // cycle_subG.
have [e def1]: exists e, 1%:M = \sum_(z \in G) e z *m (M *m rG z).
  apply/sub_sumsmxP; have [X sXG [<- _]] := Clifford_basis irrG simM.
  by apply/sumsmx_subP=> z Xz; rewrite (sumsmx_sup z) ?(subsetP sXG).
have [phi inj_phi hom_phi defMx] := isoM x Gx.
have Mtau: (M *m (phi *m rG x^-1%g) <= M)%MS.
  by rewrite mulmxA (eqmxMr _ defMx) repr_mxK.
have Mtau': (M *m (rG x *m invmx phi) <= M)%MS.
  by rewrite mulmxA -(eqmxMr _ defMx) mulmxK.
have [[tau Htau defMtau] [tau' Htau' defMtau']] := (absM _ Mtau, absM _ Mtau').
have tau'K: tau' *m tau = 1%:M.
  rewrite -[tau']mul1mx def1 !mulmx_suml; apply: eq_bigr => z Gz.
  have [f _ hom_f] := isoM z Gz; move/eqmxP; case/andP=> _; case/submxP=> v ->.
  rewrite (mulmxA _ v) -2!mulmxA; congr (_ *m _).
  rewrite -(hom_envelop_mxC hom_f) ?envelop_mxM //; congr (_ *m _).
  rewrite mulmxA defMtau' -(mulmxKpV Mtau') -mulmxA defMtau (mulmxA _ M).
  by rewrite mulmxKpV // !mulmxA mulmxKV // repr_mxK.
have cHtau_x: centgmx rH (tau *m rG x).
  apply/centgmxP=> y Hy; have [u defMy] := submxP (mxmoduleP modM y Hy).
  have Gy := subsetP sHG y Hy.
  rewrite mulmxA; apply: (canRL (repr_mxKV rG Gx)).
  rewrite -!mulmxA /= -!repr_mxM ?groupM ?groupV // (conjgC y) mulKVg.
  rewrite -[rG y]mul1mx -{1}[tau]mul1mx def1 !mulmx_suml.
  apply: eq_bigr => z Gz; have [f _ hom_f] := isoM z Gz.
  move/eqmxP; case/andP=> _; case/submxP=> v ->; rewrite -!mulmxA.
  congr (_ *m (_ *m _)); rewrite {v} !(mulmxA M).
  rewrite -!(hom_envelop_mxC hom_f) ?envelop_mxM ?(envelop_mx_id rH) //.
    congr (_ *m f); rewrite !mulmxA defMy -(mulmxA u) defMtau (mulmxA u) -defMy.
    rewrite !mulmxA (hom_mxP hom_phi) // -!mulmxA; congr (M *m (_ *m _)).
    by rewrite /= -!repr_mxM ?groupM ?groupV // -conjgC.
  by rewrite -mem_conjg (normsP nHG).
have{cHtau_x} cGtau_x: centgmx rG (tau *m rG x).
  rewrite /centgmx {1}defG mulgen_subG cycle_subG !inE Gx /= andbC.
  rewrite (subset_trans cHtau_x); last by rewrite rcent_subg subsetIr.
  apply/eqP; rewrite -{2 3}[rG x]mul1mx -tau'K !mulmxA; congr (_ *m _ *m _).
  case/envelop_mxP: Htau' => u ->.
  rewrite !(mulmx_suml, mulmx_sumr); apply: eq_bigr => y Hy.
  by rewrite -!(scalemxAl, scalemxAr) (centgmxP cHtau_x) ?mulmxA.
have{cGtau_x} [a def_tau_x]: exists a, tau *m rG x = a%:M.
  by apply/is_scalar_mxP; apply: mx_abs_irr_cent_scalar cGtau_x; exact: closedF.
apply: mx_iso_simple (eqmx_iso _ _) simM; apply/eqmxP; rewrite submx1 sub1mx.
case/mx_irrP: (irrG) => _ -> //; rewrite /mxmodule {1}defG mulgen_subG /=.
rewrite cycle_subG inE Gx andbC (subset_trans modM) ?rstabs_subg ?subsetIr //=.
rewrite -{1}[M]mulmx1 -tau'K mulmxA -mulmxA def_tau_x mul_mx_scalar.
by rewrite scalemx_sub ?(mxmodule_envelop modM Htau').
Qed.

Import action.
(* This is B & G, Lemma 2.3. Note that this is not used in the FT proof.      *)
Lemma rank_abs_irr_dvd_solvable : forall F gT (G : {group gT}) n rG,
  @mx_absolutely_irreducible F _ G n rG -> solvable G -> n %| #|G|.
Proof.
move=> F gT G n rG absG solG.
wlog closF: F rG absG / group_closure_field F gT.
  move=> IH; apply: (@group_closure_field_exists gT F) => [[F' closF' [f fRM]]].
  by apply: IH (map_repr fRM rG) _ closF'; rewrite map_mx_abs_irr.
elim: {G}_.+1 {-2}G (ltnSn #|G|) => // m IHm G leGm in n rG absG solG *.
case: (trivgVpdiv (G / G^`(1))) => [G'1 | [p p_pr pG']].
  have:= forallP solG G; rewrite subsetI subxx -quotient_sub1 ?commg_norml //.
  rewrite G'1 subxx /=; move/eqP=> G1.
  by rewrite abelian_abs_irr ?G1 ?abelian1 // in absG; rewrite (eqP absG) dvd1n.
have{pG'} [H nsHG oHG]: exists2 H : {group gT}, H <| G & #|G : H| = p.
  pose K := 'O_p^'(G / G^`(1))%G; pose P := (G / _ / K)%G.
  have nilG': nilpotent (G / G^`(1))%G by rewrite abelian_nil ?sub_der1_abelian.
  have oP: #|P| = (#|G / G^`(1)|%g`_p)%N.
    rewrite card_quotient ?gfunc.bgFunc_norm // -?divgS ?pcore_sub //.
    case/dprodP: (nilpotent_pcoreC p nilG') => _ /= defG _ tiG.
    rewrite -{1}defG TI_cardMg // mulnK ?cardG_gt0 //.
    by apply: card_Hall; exact: nilpotent_pcore_Hall.
  have pP: p.-group P by rewrite /pgroup oP part_pnat.
  have [P1 | [M maxM _]] := maximal_exists (sub1G P).
    case/idPn: pG'; rewrite -p'natE // -partn_eq1 ?cardG_gt0 //.
    by rewrite -oP -P1 cards1.
  have nsM := p_maximal_normal pP maxM.
  have [M' defM' sKM' nsM'] := inv_quotientN (pcore_normal _ _) nsM.
  have [H defH sG'H nsH] := inv_quotientN (der_normal _ _) nsM'.
  exists H => //; rewrite -divgS ?normal_sub // -(LaGrange sG'H) .
  have [sHG _] := andP nsH; have [sM'G _] := andP nsM'.
  rewrite -card_quotient ?(subset_trans sHG) ?gfunc.bgFunc_norm //.
  rewrite -divn_divl divgS ?comm_subG // -card_quotient ?gfunc.bgFunc_norm //.
  rewrite -defH -(LaGrange sKM') -divn_divl divgS ?pcore_sub //.
  rewrite -!card_quotient ?(subset_trans _ (gfunc.bgFunc_norm _ _)) //.
  by rewrite -defM' divgS ?normal_sub // (p_maximal_index pP).
pose sHG := normal_sub nsHG; pose rH := subg_repr rG sHG.
have irrG := mx_abs_irrW absG.
wlog [L simL _]: / exists2 L, mxsimple rH L & (L <= 1%:M)%MS.
  by apply: mxsimple_exists; rewrite ?mxmodule1 //; case: irrG.
have ltHG: H \proper G.
  by rewrite properEcard sHG -(LaGrange sHG) oHG ltn_Pmulr // prime_gt1.
have dvLH: \rank L %| #|H|.
  have absL: mx_absolutely_irreducible (submod_repr (mxsimple_module simL)).
    by apply: closF; exact/submod_mx_irr.
  apply: IHm absL (solvableS (normal_sub nsHG) solG).
  by rewrite (leq_trans (proper_card ltHG)).
have [_ [x Gx H'x]] := properP _ _ ltHG.
have prGH: prime #|G / H|%g by rewrite card_quotient ?oHG ?normal_norm.
wlog sH: / socleType rH by exact: socle_exists.
pose W := PackSocle (component_socle sH simL).
have card_sH: #|sH| = #|G : 'C_G[W | 'Cl]|.
  rewrite -cardsT; have ->: setT = orbit 'Cl G W.
    apply/eqP; rewrite eqEsubset subsetT.
    have [W' _ defW'] := imsetP (Clifford_atrans irrG sH).
    have WW': W' \in orbit 'Cl G W by rewrite sub_orbit_sym // -defW' inE.
    by rewrite defW' andbT; apply/subsetP=> W''; exact: sub_orbit_trans.
  rewrite orbit_stabilizer // card_in_imset //. 
  exact: can_in_inj (act_reprK _).
have sHcW: H \subset 'C_G[W | 'Cl].
  apply: subset_trans (subset_trans (mulgen_subl _ _) (Clifford_astab sH)) _.
  apply/subsetP=> z; rewrite !inE; case/andP=> ->; apply: subset_trans.
  exact: subsetT.
have [|] := prime_subgroupVti ('C_G[W | 'Cl] / H)%G prGH.
  rewrite quotientSGK ?normal_norm // => cClG.
  have def_sH: setT = [set W].
    apply/eqP; rewrite eq_sym eqEcard subsetT cards1 cardsT card_sH.
    by rewrite -indexgI (setIidPl cClG) indexgg.
  suffices L1: (L :=: 1%:M)%MS.
    by rewrite L1 mxrank1 in dvLH; exact: dvdn_trans (cardSg sHG).
  apply/eqmxP; rewrite submx1.
  have cycH: cyclic (G / H)%g by rewrite prime_cyclic.
  have [y Gy|_ _] := mx_irr_prime_index closF irrG cycH simL; last first.
    by apply; rewrite ?submx1 //; case simL.
  have simLy: mxsimple rH (L *m rG y) by exact: Clifford_simple.
  pose Wy := PackSocle (component_socle sH simLy).
  have: (L *m rG y <= Wy)%MS by rewrite PackSocleK component_mx_id.
  have ->: Wy = W by apply/set1P; rewrite -def_sH inE.
  by rewrite PackSocleK; exact: component_mx_iso.
rewrite (setIidPl _) ?quotientS ?subsetIl //; move/trivgP.
rewrite quotient_sub1 //; last by rewrite subIset // normal_norm.
move/setIidPl; rewrite (setIidPr sHcW) /= => defH.
rewrite -(LaGrange sHG) -(Clifford_rank_components irrG W) card_sH -defH.
rewrite mulnC dvdn_pmul2r // (_ : W :=: L)%MS //; apply/eqmxP.
have sLW: (L <= W)%MS by rewrite PackSocleK component_mx_id.
rewrite andbC sLW; have [modL nzL _] := simL.
have [_ _] := (Clifford_rstabs_simple irrG W); apply=> //.
rewrite /mxmodule rstabs_subg /= -Clifford_astab1 -astabIdom -defH.
by rewrite -(rstabs_subg rG sHG).
Qed.

(* Some addenda, to move to ssrnat, ssralg & matrix *)

(* This should move to ssrnat *)
Section distn.

Open Scope nat_scope.

Definition distn m n := (m - n) + (n - m).

Lemma distnC : forall m n, distn m n = distn n m.
Proof. move=> m n; exact: addnC. Qed.

Lemma dist0n : forall n, distn 0 n = n.
Proof. by case. Qed.

Lemma distn0 : forall n, distn n 0 = n.
Proof. by move=> m; rewrite distnC dist0n. Qed.

Lemma distn_subRL : forall m n, m <= n -> distn m n = (n - m)%N.
Proof. by move=> m n le_m_n; rewrite /distn (eqnP le_m_n). Qed.

Lemma distn_subLR : forall m n, n <= m -> distn m n = (m - n)%N.
Proof. by move=> m n le_n_m; rewrite distnC distn_subRL. Qed.

Lemma distnn : forall m, distn m m = 0%N.
Proof. by move=> m; rewrite /distn subnn. Qed.

Lemma distn_eq0 : forall m n, (distn m n == 0) = (m == n).
Proof. by move=> m n; rewrite addn_eq0 !subn_eq0 -eqn_leq. Qed.

Lemma leqif_add_distn : forall m n p,
   distn m p <= distn m n + distn n p ?= iff (m <= n <= p) || (p <= n <= m).
Proof.
move=> m n p; apply/leqifP; wlog le_mp : m p / m <= p.
  move=> IH; case/orP: (leq_total m p); move/IH=> //.
  by rewrite addnC orbC (distnC n) !(distnC p).
rewrite distn_subRL //; case: andP => [[le_mn le_np] | ].
  by rewrite /= !distn_subRL // addnC -(eqn_addr m) -addnA !subnK.
move/andP; rewrite negb_and -!ltnNge; case/orP=> [lt_nm | lt_pn].
  have lt_np := leq_trans lt_nm le_mp.
  by rewrite leqNgt lt_np ltn_addl //= distn_subRL ?ltn_sub2l // ltnW.
have lt_mn := leq_ltn_trans le_mp lt_pn.
by rewrite andbC leqNgt lt_mn ltn_addr //= distn_subRL ?ltn_sub2r // ltnW.
Qed.

Lemma leq_add_distn : forall m n p, distn m p <= distn m n + distn n p.
Proof. by move=> m n p; rewrite leqif_add_distn. Qed.

Lemma sqrn_distn : forall m n, distn m n ^ 2 + 2 * (m * n) = m ^ 2 + n ^ 2.
Proof.
move=> m n; wlog le_nm: m n / n <= m.
  move=> IH; case/orP: (leq_total n m); move/IH=> //.
  by rewrite (addnC (n ^ 2)) (mulnC n) distnC.
by rewrite distn_subLR ?sqrn_sub ?subnK ?nat_Cauchy.
Qed.

End distn.

(* This should move to ssralg *)

Section RingPrimitiveRoot.


Variables (R : ringType) (n : nat) (z : R).


Definition GRing_order :=
  (n > 0) && (forallb i : 'I_n, (z ^+ i.+1 == 1) == (i.+1 == n)).


Hypothesis ozn : GRing_order.

Lemma ring_order_gt0 : n > 0. Proof. by case/andP: ozn. Qed.
Let n_gt0 := ring_order_gt0.

Lemma expr_order : z ^+ n = 1.

Proof.
case/andP: ozn => _; rewrite -(prednK n_gt0); move/forallP; move/(_ ord_max).
by rewrite eqxx eqb_id; move/eqP.
Qed.



Lemma expr_modn : forall (x : R) i, x ^+ n = 1 -> x ^+ (i %% n) = x ^+ i.
Proof.
move=> x i xm1; rewrite {2}(divn_eq i n) exprn_addr mulnC exprn_mulr xm1.
by rewrite exp1rn mul1r.
Qed.

Lemma expr_mod_order : forall i, z ^+ (i %% n) = z ^+ i.
Proof. move=> i; exact: expr_modn expr_order. Qed.

Lemma ring_order_dvd : forall i, (n %| i) = (z ^+ i == 1).
Proof.
move=> i; move: n_gt0; rewrite -expr_mod_order /dvdn -(ltn_mod i).
case: {i}(i %% n)%N => [|i] lt_i; first by rewrite !eqxx.
case/andP: ozn => _; move/forallP; move/(_ (Ordinal (ltnW lt_i))).
by move/eqP; rewrite eqn_leq andbC leqNgt lt_i.
Qed.

Lemma eq_expr_mod_order : forall i j, (z ^+ i == z ^+ j) = (i == j %[mod n]).
Proof.
move=> i j; wlog le_ji: i j / j <= i.
  move=> IH; case: (leqP j i); last move/ltnW; move/IH=> //.
  by rewrite eq_sym (eq_sym (j %% n)%N).
rewrite -{1}(subnKC le_ji) exprn_addr -expr_mod_order eqn_mod_dvd //.
rewrite ring_order_dvd; apply/eqP/eqP=> [|->]; last by rewrite mulr1.
move/(congr1 ( *%R (z ^+ (n - j %% n)))); rewrite mulrA -exprn_addr.
by rewrite subnK ?expr_order ?mul1r // ltnW ?ltn_mod.
Qed.

End RingPrimitiveRoot.

(* This should move to poly.v *)
Section MorePoly.
Import poly.

Variables (R : ringType) (rs : seq R).

Lemma prod_factors_monic : monic (\prod_(z <- rs) ('X - z%:P)).
Proof. by apply big_prop=> *; rewrite (monic1, monic_factor, monic_mull). Qed.

Lemma size_prod_factors : size (\prod_(z <- rs) ('X - z%:P)) = (size rs).+1.
Proof.
elim: rs => [|z rs' IHrs]; rewrite (big_nil, big_cons) ?size_poly1 //.
by rewrite size_monic_mul ?monic_factor -?size_poly_eq0 ?IHrs ?seq_factor.
Qed.

Lemma size_dvdp_mon_leqif : forall p q : {poly R},
    monic p -> p %| q -> q != 0 ->
  size p <= size q ?= iff (q == lead_coef q *: p).
Proof.
move=> p q0 mon_p; case/(dvdpPm _ mon_p) => q ->{q0}.
case: (eqVneq q 0) => [-> | nz_q _]; first by rewrite mul0r eqxx.
have q_gt0: size q > 0 by rewrite lt0n size_poly_eq0.
split; first by rewrite size_mul_monic // -(prednK q_gt0) leq_addl.
rewrite lead_coef_mul_monic // [_ *: p]scale_polyE.
apply/idP/eqP=> [|->]; last first.
  by rewrite size_mul_monic // -?size_poly_eq0 size_polyC lead_coef_eq0 nz_q.
rewrite size_mul_monic // eqn_leq; case/andP=> _.
rewrite -subn1 leq_sub_add leq_add2r => le_q_1; congr (_ * _).
by rewrite {1}(size1_polyC le_q_1) lead_coefE -subn1 ((_ - 1 =P 0)%N _).
Qed.

Definition powers_seq (z : R) := mkseq (fun i => z ^+ i).

End MorePoly.

Section MorePolyUniqRoots.
Import poly.

Variable R : unitRingType.

Lemma uniq_roots_dvdp : forall (p : {poly R}) rs,
  all (root p) rs -> uniq_roots rs -> \prod_(z <- rs) ('X - z%:P) %| p.
Proof.
move=> p; elim=> [|z rs IHrs] /=; first by rewrite big_nil dvd1p.
case/andP=> pz0; move/IHrs=> {IHrs}IHrs; case/andP=> diff_z_rs uniq_rs.
have{IHrs uniq_rs} [q def_p]:= dvdpPm _ (prod_factors_monic _) (IHrs uniq_rs).
suffices: q.[z] == 0.
  rewrite def_p; case/factor_theorem=> q' ->; rewrite -mulrA.
  by rewrite -(big_cons 1 *%R z _ xpredT) dvdp_mon_mull ?prod_factors_monic.
move: diff_z_rs pz0; rewrite {p}def_p /root.
elim: rs q => [|t rs IHrs] q /=; first by rewrite big_nil mulr1.
rewrite big_cons -andbA mulrA; case/and3P; move/eqP=> czt inv_zt diff_z_rs.
move/(IHrs _ diff_z_rs) => {rs IHrs diff_z_rs} qtz0.
rewrite -(inj_eq (mulIr inv_zt)) mul0r -oppr_sub mulrN (inv_eq (@opprK _)).
rewrite -oppr0 horner_mul_com /com_poly ?horner_lin // in qtz0.
by rewrite mulr_subl mulr_subr czt.
Qed.

(* This sould replace the proof in poly *)
Lemma max_ring_poly_roots : forall (p : {poly R}) rs,
  p != 0 -> all (root p) rs -> uniq_roots rs -> size rs < size p.
Proof.
move=> p rs nz_p p_rs_0 uniq_rs; rewrite -size_prod_factors.
by rewrite size_dvdp_mon_leqif ?prod_factors_monic ?uniq_roots_dvdp.
Qed.

End MorePolyUniqRoots.

Section YetMorePolyUniqRoots.
Import poly.

Variable R : idomainType.

Lemma root_prod_factors : forall rs (x : R),
  root (\prod_(z <- rs) ('X - z%:P)) x = (x \in rs).
Proof.
rewrite /root => rs x.
elim: rs => [|z rs IHrs]; first by rewrite big_nil hornerC oner_eq0.
by rewrite big_cons horner_mul mulf_eq0 IHrs !horner_lin subr_eq0.
Qed.

End YetMorePolyUniqRoots.

Section PolyPrimitiveRoot.
Import poly.

Variables (F : fieldType) (n : nat) (z : F).
Hypothesis ozn : GRing_order n z.

Lemma uniq_rootsE : forall rs : seq F, uniq_roots rs = uniq rs.
Proof.
elim=> //= r rs ->; congr (_ && _); rewrite -has_pred1 -all_predC.
by apply: eq_all => t; rewrite /diff_roots mulrC eqxx unitfE subr_eq0.
Qed.

Lemma max_poly_roots : forall (p : {poly F}) rs,
  p != 0 -> all (root p) rs -> uniq rs -> size rs < size p.
Proof. by move=> p rs; rewrite -uniq_rootsE; exact: max_ring_poly_roots. Qed.

Lemma uniq_roots_of_unity : uniq_roots (powers_seq z n).
Proof.
rewrite uniq_rootsE; rewrite map_inj_in_uniq ?iota_uniq // => i j.
rewrite !mem_iota => lt_i_n lt_j_n; move/eqP; rewrite (eq_expr_mod_order ozn).
by rewrite !modn_small //; move/eqP.
Qed.

Lemma prod_factors_of_unity :
  \prod_(z_i <- powers_seq z n) ('X - z_i%:P) = 'X^n - 1.
Proof.
set Pz := \prod_(zi <- _) _; set Pn := 'X^n - 1.
have dvd_Pz_Pn : Pz %| Pn.
  apply: uniq_roots_dvdp uniq_roots_of_unity.
  apply/(all_nthP 0)=> i; rewrite size_mkseq => lt_i_n.
  rewrite /root nth_mkseq // !horner_lin hornerXn subr_eq0.
  by rewrite -exprn_mulr -(ring_order_dvd ozn) dvdn_mull.
have n_gt0: n > 0 := ring_order_gt0 ozn.
have szPn: size Pn = n.+1.
  by rewrite size_addl ?size_opp ?size_poly1 ?size_polyXn.
have nzPn: Pn != 0 by rewrite -size_poly_eq0 szPn.
have [_] := size_dvdp_mon_leqif (prod_factors_monic _) dvd_Pz_Pn nzPn.
rewrite size_prod_factors szPn size_mkseq -/Pz eqxx eq_sym; move/esym; move/eqP.
rewrite lead_coefE szPn /= coef_sub coef1 coef_Xn eqxx eqn0Ngt n_gt0 subr0.
by rewrite scale1r.
Qed.

End PolyPrimitiveRoot.

Section Eigenspace.

Variables (F : fieldType) (n : nat) (f : 'M[F]_n).

Definition eigenspace a := kermx (f - a%:M).
Definition eigenvalue : pred F := fun a => eigenspace a != 0.

Lemma eigenspaceP : forall a m (W : 'M_(m, n)),
  reflect (W *m f = a *m: W) (W <= eigenspace a)%MS.
Proof.
move=> a m W; rewrite (sameP sub_kermxP eqP) mulmx_subr subr_eq0 mul_mx_scalar.
exact: eqP.
Qed.

Lemma eigenvalueP : forall a,
  reflect (exists2 v : 'rV_n, v *m f = a *m: v & v != 0) (eigenvalue a).
Proof.
by move=> a; apply: (iffP rowV0Pn) => [] [v]; move/eigenspaceP; exists v.
Qed.

Lemma mxdirect_sum_eigenspace : forall (I : finType) (P : pred I) a_,
  {in P &, injective a_} -> mxdirect (\sum_(i | P i) eigenspace (a_ i)).
Proof.
move=> I P a_; elim: {P}_.+1 {-2}P (ltnSn #|P|) => // m IHm P lePm inj_a.
apply/mxdirect_sumsP=> i Pi; apply/eqP; apply/rowV0P => v.
rewrite sub_capmx; case/andP; case/eigenspaceP=> def_vf.
set Vi' := (\sum_(i | _) _)%MS => Vi'v.
have dxVi': mxdirect Vi'.
  rewrite (cardD1x Pi) in lePm; apply: IHm => //.
  by apply: sub_in2 inj_a => j; case/andP.
case/sub_dsumsmx: Vi'v => // u Vi'u def_v _.
rewrite def_v big1 // => j Pi'j; apply/eqP.
have nz_aij: a_ i - a_ j != 0.
  by case/andP: Pi'j => Pj ne_ji; rewrite subr_eq0 eq_sym (inj_in_eq inj_a).
case: (sub_dsumsmx dxVi' (sub0mx 1 _)) => C _ _ uniqC.
rewrite -(eqmx_eq0 (eqmx_scale _ nz_aij)).
rewrite (uniqC (fun k => (a_ i - a_ k) *m: u k)) => // [|k Pi'k|].
- by rewrite -(uniqC (fun _ => 0)) ?big1 // => k Pi'k; exact: sub0mx.
- by rewrite scalemx_sub ?Vi'u.
rewrite -{1}(subrr (v *m f)) {1}def_vf def_v scalemx_sumr mulmx_suml -sumr_sub.
by apply: eq_bigr => k; move/Vi'u; move/eigenspaceP->; rewrite scalemx_subl.
Qed.

End Eigenspace.

Section SplitAbelian.

Variables (F : fieldType) (gT : finGroupType) (G : {group gT}).

Lemma rank_rV : forall n (v : 'rV[F]_n), \rank v = (v != 0).
Proof.
move=> n v; case: eqP => [-> | nz_v]; first by rewrite mxrank0.
by apply/eqP; rewrite eqn_leq rank_leq_row lt0n mxrank_eq0; exact/eqP.
Qed.

Lemma primitive_root_splitting_abelian : forall z : F,
  GRing_order #|G| z -> abelian G -> group_splitting_field F G.
Proof.
move=> z ozG cGG [|n] rG irrG; first by case/mx_irrP: irrG.
have defPz := prod_factors_of_unity ozG; set Pz := (\prod_(zi <- _) _) in defPz.
case: (pickP [pred x \in G | ~~ is_scalar_mx (rG x)]) => [x | scalG].
  case/andP=> Gx nscal_rGx.
  have: horner_mx (rG x) Pz == 0.
    rewrite defPz (ringM_sub (horner_mxRM _)) horner_mx_C horner_mx_Xn.
    rewrite -repr_mxX ?inE // ((_ ^+ _ =P 1)%g _) ?repr_mx1 ?subrr //.
    by rewrite -order_dvdn order_dvdG.
  case/idPn; rewrite -mxrank_eq0 /Pz; elim: (powers_seq _ _) => [|zi rs IHrs].
    by rewrite big_nil horner_mx_C mxrank1.
  rewrite big_cons /= (ringM_mul (horner_mxRM _)) eqmxMfull {rs IHrs}//.
  rewrite (ringM_sub (horner_mxRM _)) horner_mx_C horner_mx_X.
  rewrite row_full_unit (mx_Schur irrG) //; last first.
    rewrite subr_eq0; case: eqP nscal_rGx => // ->.
    by rewrite scalar_mx_is_scalar.
  rewrite -memmx_cent_envelop linear_sub.
  rewrite addmx_sub ?eqmx_opp ?scalar_mx_cent //= memmx_cent_envelop.
  by apply/centgmxP=> j Zh_j; rewrite -!repr_mxM // (centsP cGG).
pose M := <<delta_mx 0 0 : 'rV[F]_n.+1>>%MS.
have linM: \rank M = 1%N by rewrite genmxE mxrank_delta.
have modM: mxmodule rG M.
  apply/mxmoduleP=> x Gx; move/idPn: (scalG x); rewrite /= Gx negbK.
  by case/is_scalar_mxP=> ? ->; rewrite scalar_mxC submxMl.
apply: linear_mx_abs_irr; apply/eqP; rewrite eq_sym -linM.
by case/mx_irrP: irrG => _; apply; rewrite // -mxrank_eq0 linM.
Qed.

Lemma card_classes_abelian : abelian G -> #|classes G| = #|G|.
Proof.
move=> cGG; rewrite -action.sum_card_class -sum1_card; apply: eq_bigr => xG.
case/imsetP=> x Gx ->; rewrite (@eq_card1 _ x) // => y.
apply/idP/eqP=> [| ->]; last by rewrite class_refl.
by case/imsetP=> z Gz ->; rewrite conjgE (centsP cGG x) ?mulKg.
Qed.

Import poly.
Lemma splitting_cyclic_primitive_root :
    cyclic G -> [char F]^'.-group G -> group_splitting_field F G ->
  classically {z : F | GRing_order #|G| z}.
Proof.
move=> cycG F'G splitG [] //; pose n := #|G| => IH.
have n_gt0: n > 0 by exact: cardG_gt0.
wlog sG: / socleType (regular_repr F G) by exact: socle_exists.
have cGG: abelian G by exact: cyclic_abelian.
have linG := Wedderburn_degree_abelian splitG cGG (_ : sG).
have [g defG] := cyclicP _ cycG; have Gg: g \in G by rewrite defG cycle_id.
have scalG: forall i : sG, {a | socle_repr i g = a%:M}.
  move=> i; move: (socle_repr i); rewrite [\rank _]linG => rG.
  by exists (rG g 0 0); rewrite -mx11_scalar.
pose r i := sval (scalG i); pose rs := map r (enum sG).
have inj_r: injective r.
  rewrite /r => i j; case: (scalG i) => a rGi; case: (scalG j) => b rGj /= ab.
  rewrite -(regular_comp_refl F'G i)  -(regular_comp_refl F'G j).
  apply: regular_comp_rsim=> //; move: rGj rGi; rewrite {a}ab.
  move: (socle_repr i) (socle_repr j); rewrite ![\rank _]linG => ri rj <- eqij.
  exists 1%:M; rewrite ?row_free_unit ?unitmx1 // => x; rewrite {1}defG.
  by case/cycleP=> k ->; rewrite mulmx1 mul1mx !repr_mxX // eqij.
have card_sG: #|sG| = n by rewrite Wedderburn_card // card_classes_abelian.
have sz_rs: size rs = n by rewrite size_map -cardE.
have rn1: forall i, r i ^+ n = 1.
  rewrite /r => i; case: (scalG i) => z def_z /=; move: (socle_repr i) def_z.
  rewrite [\rank _]linG => rG def_z.
  apply: (fieldM_inj (@scalar_mxRM F 0)); rewrite (ringM_exp scalar_mxRM).
  by rewrite -def_z -repr_mxX // /n {2}defG expg_order repr_mx1.
have prim_r: forall z, z ^+ n = 1 -> {i | z = r i}.
  move=> z zn1; case rs_z: (z \in rs).
    exists (nth (principal_comp sG) (enum sG) (index z rs)).
    by case/mapP: rs_z => i sGi ->; rewrite index_map // nth_index.
  have szPn: size ('X^n - 1 : {poly F}) = n.+1.
    by rewrite size_addl ?size_polyXn // size_opp ?size_poly1.
   case/idP: (ltnn n); rewrite -{1}sz_rs -ltnS -szPn -/(size (z :: rs)).
  rewrite max_poly_roots -?size_poly_eq0 ?szPn //; last first.
    by rewrite /= rs_z map_inj_uniq ?enum_uniq.
  apply/allP=> t; rewrite inE /root !horner_lin hornerXn subr_eq0.
  case/predU1P=> [-> |]; first by rewrite zn1.
  by case/mapP=> i _ ->; rewrite rn1.
pose r' := sval (prim_r _ _); pose sG_1 := r' _ (exp1rn _ _).
have sG_VP: (r _)^-1 ^+ n = 1 by move=> i; rewrite expr_inv rn1 invr1.
have sG_MP: (r _ * r _) ^+ n = 1 by move=> i j; rewrite exprn_mull !rn1 mul1r.
pose sG_V := r' _ (sG_VP _); pose sG_M := r' _ (sG_MP _ _).
have r'K: forall z zn1, r (r' z zn1) = z.
  by move=> z zn1; rewrite /r'; case: (prim_r _ _).
have sG_1g: left_id sG_1 sG_M by move=> i; apply: inj_r; rewrite !r'K mul1r.
have sG_Vg: left_inverse sG_1 sG_V sG_M.
  move=> i; apply: inj_r; rewrite !r'K mulVr //.
  by rewrite -(unitr_pexp _ n_gt0) rn1 unitr1.
have sG_Ag: associative sG_M by move=> i j k; apply: inj_r; rewrite !r'K mulrA.
pose sGbg := BaseFinGroupType sG (FinGroup.Mixin sG_Ag sG_1g sG_Vg).
pose sGg := @FinGroupType sGbg sG_Vg.
have morph_r: {in setT &, {morph r : x y / @mulg sGg x y >-> x * y}}.
  by move=> i j /=; rewrite !r'K.
have: @cyclic sGg setT.
  apply: (@field_mul_group_cyclic sGg [set: _] F r morph_r) => i _.
  by split=> [ri1 | ->]; first apply: inj_r; rewrite r'K.
case/cyclicP=> i gen_i; apply: IH; exists (r i).
rewrite -/n /GRing_order n_gt0; apply/forallP=> j.
apply/eqP; apply/eqP/eqP => [rij1 |-> //].
have{rij1}: @expgn sGg i j.+1 == 1%g.
  apply/eqP; apply: inj_r; rewrite r'K -{}rij1.
  elim: {j}j.+1 => [|j IHj]; first by rewrite r'K.
  by rewrite expgS exprS -IHj !r'K.
rewrite -order_dvdn orderE -gen_i cardsT card_sG.
rewrite /dvdn -(modnn n) -{3 6}(prednK n_gt0) -(addn1 n.-1) -addn1.
by rewrite modn_add2r !modn_small //; [move/eqP-> | rewrite prednK].
Qed.

End SplitAbelian.

Implicit Arguments eigenspaceP [F n f a m W].
Implicit Arguments eigenvalueP [F n f a].
Prenex Implicits eigenspaceP eigenvalueP.

(* This section covers the many parts B & G, Lemma 2.4 -- only the last is    *)
(* used in the rest of the proof, and then only in the proof of Theorem 2.5.  *)
Section QuasiRegularCyclic.

Variables (F : fieldType) (q' h : nat) (g : 'M[F]_q'.+1) (eps : F).

Hypothesis gh1 : g ^+ h = 1.
Hypothesis prim_eps : GRing_order h eps.

Let h_gt0 := ring_order_gt0 prim_eps.
Let eps_h := expr_order prim_eps.
Let eps_mod_h := expr_mod_order prim_eps.
Let inj_eps : injective (fun i : 'I_h => eps ^+ i).
Proof.
move=> i j eq_ij; apply/eqP; move/eqP: eq_ij.
by rewrite (eq_expr_mod_order prim_eps) !modn_small.
Qed.

Local Notation q := q'.+1.
Local Notation V := 'rV[F]_q.
Local Notation E := 'M[F]_q.

Let V_ i := eigenspace g (eps ^+ i).
Let n_ i := \rank (V_ i).
Let E_ i := eigenspace (lin_mx (mulmx g^-1 \o mulmxr g)) (eps ^+ i).
Let E2_ i t :=
  (kermx (lin_mx (mulmxr (cokermx (V_ t)) \o mulmx (V_ i)))
   :&: kermx (lin_mx (mulmx (\sum_(j < h | j != i %[mod h]) V_ j)%MS)))%MS.

Local Notation "''V_' i" := (V_ i) (at level 8, i at level 2, format "''V_' i").
Local Notation "''n_' i" := (n_ i) (at level 8, i at level 2, format "''n_' i").
Local Notation "''E_' i" := (E_ i) (at level 8, i at level 2, format "''E_' i").
Local Notation "'E_ ( i )" := (E_ i) (at level 8, only parsing).
Local Notation "e ^g" := (g^-1 *m (e *m g))
  (at level 8, format "e ^g") : ring_scope.
Local Notation "'E_ ( i , t )" := (E2_ i t)
  (at level 8, format "''E_' ( i ,  t )").

Let inj_g : GRing.unit g.
Proof. by rewrite -(unitr_pexp _ h_gt0) gh1 unitr1. Qed.

Let Vi_mod : forall i, 'V_(i %% h) = 'V_i.
Proof. by move=> i; rewrite /V_ eps_mod_h. Qed.

Let g_mod i := expr_modn i gh1.

Let EiP : forall i e, reflect (e^g = eps ^+ i *m: e) (e \in 'E_i)%MS.
Proof.
move=> i e; rewrite (sameP eigenspaceP eqP) mul_vec_lin -linearZ /=.
by rewrite (can_eq mxvecK); exact: eqP.
Qed.

Let inhP : forall m, m %% h < h. Proof. by move=> m; rewrite ltn_mod. Qed.
Let inh m := Ordinal (inhP m).

Let E2iP : forall i t e,
  reflect ('V_i *m e <= 'V_t /\ forall j, j != i %[mod h] -> 'V_j *m e = 0)%MS
          (e \in 'E_(i, t))%MS.
Proof.
move=> i t e; rewrite sub_capmx submxE !(sameP sub_kermxP eqP) /=.
rewrite !mul_vec_lin !mxvec_eq0 /= -submxE -submx0 sumsmxMr.
apply: (iffP andP) => [[->] | [-> Ve0]]; last first.
  by split=> //; apply/sumsmx_subP=> j ne_ji; rewrite Ve0.
move/sumsmx_subP=> Ve0; split=> // j ne_ji; apply: submx0null.
by rewrite -Vi_mod (Ve0 (inh j)) //= modn_mod.
Qed.

Let sumV := (\sum_(i < h) 'V_i)%MS.

Import poly.
(* This is B & G, Proposition 2.4(a) *)
Lemma mxdirect_sum_eigenspace_cycle : (sumV :=: 1%:M)%MS /\ mxdirect sumV.
Proof.
have splitF: group_splitting_field F (Zp_group h).
  move: prim_eps (abelianS (subsetT (Zp h)) (Zp_abelian _)).
  by rewrite -{1}(card_Zp h_gt0); exact: primitive_root_splitting_abelian.
have F'Zh: [char F]^'.-group (Zp h).
  apply/pgroupP=> p p_pr; rewrite card_Zp //.
  case/dvdnP=> d def_h; apply/negP=> /= charFp.
  have d_gt0: d > 0 by move: h_gt0; rewrite def_h; case d.
  have: eps ^+ d == 1.
    rewrite -(inj_eq (fieldM_inj (Frobenius_aut_RM charFp))).
    by rewrite Frobenius_aut_1 Frobenius_autE -exprn_mulr -def_h eps_h.
  by rewrite -(ring_order_dvd prim_eps) gtnNdvd // def_h ltn_Pmulr // prime_gt1.
case: (ltngtP h 1) => [|h_gt1|h1]; last first; last by rewrite ltnNge h_gt0.
  rewrite /sumV mxdirectE /= h1 !big_ord1; split=> //.
  apply/eqmxP; rewrite submx1; apply/eigenspaceP.
  by rewrite mul1mx scale1mx idmxE -gh1 h1.
pose mxZ (i : 'Z_h) := g ^+ i.
have mxZ_repr: mx_repr (Zp h) mxZ.
  by split=> // i j _ _; rewrite /mxZ /= {3}Zp_cast // expr_modn // exprn_addr.
pose rZ := MxRepresentation mxZ_repr.
have ZhT: Zp h = setT by rewrite /Zp h_gt1.
have memZh: _ \in Zp h by move=> i; rewrite ZhT inE.
have def_g: g = rZ Zp1 by [].
have lin_rZ: forall m (U : 'M_(m, q)) a,
  U *m g = a *m: U -> forall i, U *m rZ i%:R = (a ^+ i) *m: U.
- move=> m U a defUg i; rewrite repr_mxX //.
  elim: i => [|i IHi]; first by rewrite mulmx1 scale1mx.
  by rewrite !exprS -scalemxA mulmxA defUg -IHi scalemxAl.
rewrite mxdirect_sum_eigenspace => [|j k _ _]; last exact: inj_eps.
split=> //; apply/eqmxP; rewrite submx1.
wlog [I M /= simM <- _]: / mxsemisimple rZ 1.
  exact: mx_reducible_semisimple (mxmodule1 _) (mx_Maeshke rZ F'Zh) _.
apply/sumsmx_subP=> i _; have simMi := simM i; have [modMi _ _] := simMi.
set v := nz_row (M i); have nz_v: v != 0 by exact: nz_row_mxsimple simMi.
have rankMi: \rank (M i) = 1%N.
  by rewrite (mxsimple_abelian_linear splitF _ simMi) //= ZhT Zp_abelian.
have defMi: (M i :=: v)%MS.
  apply/eqmxP; rewrite andbC -(geq_leqif (mxrank_leqif_eq _)) ?nz_row_sub //.
  by rewrite rankMi lt0n mxrank_eq0.
have [a defvg]: exists a, v *m rZ 1%R = a *m: v.
  by apply/sub_rVP; rewrite -defMi mxmodule_trans ?socle_module ?defMi.
have: root ('X^h - 1) a.
  apply: contraR nz_v => nz_pZa; rewrite -(eqmx_eq0 (eqmx_scale _ nz_pZa)).
  rewrite !horner_lin hornerXn scalemx_subl scale1mx subr_eq0.
  by rewrite -lin_rZ // char_Zp ?mulmx1.
rewrite -(prod_factors_of_unity prim_eps) root_prod_factors.
case/mapP=> k; rewrite mem_iota => lt_kh def_a.
by rewrite defMi (sumsmx_sup (Ordinal lt_kh)) // /V_ -def_a; exact/eigenspaceP.
Qed.

(* This is B & G, Proposition 2.4(b) *)
Lemma rank_step_eigenspace_cycle : forall i, 'n_ (i + h) = 'n_ i.
Proof. by move=> i; rewrite /n_ -Vi_mod modn_addr Vi_mod. Qed.

Let sumE := (\sum_(it : 'I_h * 'I_h) 'E_(it.1, it.2))%MS.

(* This is B & G, Proposition 2.4(c) *)
Lemma mxdirect_sum_proj_eigenspace_cycle : (sumE :=: 1%:M)%MS /\ mxdirect sumE.
Proof.
have [def1V] := mxdirect_sum_eigenspace_cycle; move/mxdirect_sumsP=> dxV.
pose p (i : 'I_h) := proj_mx 'V_i (\sum_(j | j != i) 'V_j)%MS.
have def1p: 1%:M = \sum_i p i.
  rewrite -[\sum_i _]mul1mx; move/eqmxP: def1V; rewrite submx1.
  case/sub_sumsmxP=> u ->; rewrite mulmx_sumr; apply: eq_bigr => i _.
  rewrite (bigD1 i) //= mulmx_addl proj_mx_id ?submxMl ?dxV //.
  rewrite proj_mx_0 ?dxV ?addr0 ?summx_sub // => j ne_ji.
  by rewrite (sumsmx_sup j) ?submxMl.
split; first do [apply/eqmxP; rewrite submx1].
  apply/(@memmx_subP F _ _ q)=> A _; apply/memmx_sumsP.
  pose B i t := p i *m A *m p t.
  exists (fun it => B it.1 it.2) => [|[i t] /=].
    rewrite -(pair_bigA _ B) /= -[A]mul1mx def1p mulmx_suml.
    by apply: eq_bigr => i _; rewrite -mulmx_sumr -def1p mulmx1.
  apply/E2iP; split=> [|j ne_ji]; first by rewrite mulmxA proj_mx_sub.
  rewrite 2!mulmxA -mulmxA proj_mx_0 ?dxV ?mul0mx //.
  rewrite (sumsmx_sup (inh j)) ?Vi_mod //.
  by rewrite (modn_small (valP i)) in ne_ji.
apply/mxdirect_sumsP=> [[i t] _] /=.
apply/eqP; rewrite -submx0; apply/(@memmx_subP F _ _ q)=> A.
rewrite sub_capmx submx0 mxvec_eq0 -submx0.
case/andP; case/E2iP=> ViA Vi'A; case/memmx_sumsP=> B defA sBE.
rewrite -[A]mul1mx -(eqmxMr A def1V) sumsmxMr (bigD1 i) //=.
rewrite big1 ?addsmx0 => [|j ne_ij]; last by rewrite Vi'A ?modn_small.
rewrite -[_ *m A]mulmx1 def1p mulmx_sumr (bigD1 t) //=.
rewrite big1 ?addr0 => [|u ne_ut]; last first.
  by rewrite proj_mx_0 ?dxV ?(sumsmx_sup t) // eq_sym.
rewrite {A ViA Vi'A}defA mulmx_sumr mulmx_suml summx_sub // => [[j u]].
case/E2iP: (sBE (j, u)); rewrite eqE /=; case: eqP => [-> sBu _ ne_ut|].
  by rewrite proj_mx_0 ?dxV ?(sumsmx_sup u).
by move/eqP=> ne_ji _ ->; rewrite ?mul0mx // eq_sym !modn_small.
Qed.

(* This is B & G, Proposition 2.4(d) *)
Lemma rank_proj_eigenspace_cycle :
  forall i t, \rank 'E_(i, t) = ('n_i * 'n_t)%N.
Proof.
have [def1V] := mxdirect_sum_eigenspace_cycle; move/mxdirect_sumsP=> dxV.
pose p (i : 'I_h) := proj_mx 'V_i (\sum_(j | j != i) 'V_j)%MS.
have def1p: 1%:M = \sum_i p i.
  rewrite -[\sum_i _]mul1mx; move/eqmxP: def1V; rewrite submx1.
  case/sub_sumsmxP=> u ->; rewrite mulmx_sumr; apply: eq_bigr => i _.
  rewrite (bigD1 i) //= mulmx_addl proj_mx_id ?submxMl ?dxV //.
  rewrite proj_mx_0 ?dxV ?addr0 ?summx_sub // => j ne_ji.
  by rewrite (sumsmx_sup j) ?submxMl.
move=> i0 t0; pose i := inh i0; pose t := inh t0.
transitivity (\rank 'E_(i, t)); first by rewrite /E2_ !Vi_mod modn_mod.
transitivity ('n_i * 'n_t)%N; last by rewrite /n_ !Vi_mod.
move: {i0 t0}i t => i t; pose Bi := row_base 'V_i; pose Bt := row_base 'V_t.
pose B := lin_mx (mulmx (p i *m pinvmx Bi) \o mulmxr Bt).
pose B' := lin_mx (mulmx Bi \o mulmxr (pinvmx Bt)).
have Bk : B *m B' = 1%:M.
  apply/row_matrixP=> k; rewrite row_mul mul_rV_lin /= rowE mx_rV_lin /=.
  rewrite 3!(mulmxA Bi) proj_mx_id ?dxV ?eq_row_base //.
  have [Bt'' Bt'K] := row_freeP (row_base_free 'V_t).
  rewrite (mulmxA _ _ Bt) -[_ *m _]mulmx1 -Bt'K mulmxA mulmxKpV ?submxMl //.
  have [Bi'' Bi'K] := row_freeP (row_base_free 'V_i).
  rewrite -2!mulmxA Bt'K scalar_mxC -Bi'K 2!(mulmxA (Bi *m _)).
  by rewrite mulmxKpV // Bi'K mul1mx vec_mxK rowE mulmx1.
have <-: \rank B = ('n_i * 'n_t)%N by apply/eqP; apply/row_freeP; exists B'.
apply/eqP; rewrite eqn_leq !mxrankS //.
  apply/row_subP=> k; rewrite rowE mul_rV_lin /=.
  apply/E2iP; split=> [|j ne_ji].
    rewrite 3!mulmxA mulmx_sub ?eq_row_base //.
  rewrite 2!(mulmxA 'V_j) proj_mx_0 ?dxV ?mul0mx //.
  rewrite (sumsmx_sup (inh j)) ?Vi_mod //.
  by rewrite (modn_small (valP i)) in ne_ji.
apply/(@memmx_subP F _ _ q) => A; case/E2iP=> ViA Vi'A.
apply/submxP; exists (mxvec (Bi *m A *m pinvmx Bt)); rewrite mul_vec_lin /=.
rewrite mulmxKpV; last by rewrite eq_row_base (eqmxMr _ (eq_row_base _)).
rewrite mulmxA -[p i]mul1mx mulmxKpV ?eq_row_base ?proj_mx_sub // mul1mx.
rewrite -{1}[A]mul1mx def1p mulmx_suml (bigD1 i) //= big1 ?addr0 // => j neji.
rewrite -[p j]mul1mx -(mulmxKpV (proj_mx_sub _ _ _)) -mulmxA Vi'A ?mulmx0 //.
by rewrite !modn_small.
Qed.

(* This is B & G, Proposition 2.4(e) *)
Lemma proj_eigenspace_cycle_sub_quasi_cent : forall i j,
  ('E_(i, i + j) <= 'E_j)%MS.
Proof.
move=> i j; apply/(@memmx_subP F _ _ q)=> A; case/E2iP=> ViA Vi'A.
apply/EiP; apply: canLR (mulKmx inj_g) _; rewrite -{1}[A]mul1mx -{2}[g]mul1mx.
have: (1%:M <= sumV)%MS by have [->] := mxdirect_sum_eigenspace_cycle.
case/sub_sumsmxP=> p ->; rewrite -!mulmxA !mulmx_suml.
apply: eq_bigr=> k _; case: (eqVneq (k : nat) (i %% h)%N) => [-> | ne_ki].
  rewrite Vi_mod -mulmxA (mulmxA _ A) (eigenspaceP ViA).
  rewrite (mulmxA _ g) (eigenspaceP (submxMl _ _)).
  by rewrite -!(scalemxAl, scalemxAr) scalemxA mulmxA exprn_addr.
rewrite 2!mulmxA (eigenspaceP (submxMl _ _)) -!(scalemxAr, scalemxAl).
by rewrite -(mulmxA _ 'V_k A) Vi'A ?linear0 ?mul0mx // modn_small.
Qed.

Let diagE m :=
  (\sum_(it : 'I_h * 'I_h | it.1 + m == it.2 %[mod h]) 'E_(it.1, it.2))%MS.

(* This is B & G, Proposition 2.4(f) *)
Lemma diag_sum_proj_eigenspace_cycle : forall m,
  (diagE m :=: 'E_m)%MS /\ mxdirect (diagE m).
Proof.
have sub_diagE: forall m, (diagE m <= 'E_m)%MS.
  move=> m; apply/sumsmx_subP=> [[i t] /= def_t].
  apply: submx_trans (proj_eigenspace_cycle_sub_quasi_cent i m).
  by rewrite /E2_ -(Vi_mod (i + m)) (eqP def_t) Vi_mod.
pose sum_diagE := (\sum_(m < h) diagE m)%MS.
pose p (it : 'I_h * 'I_h) := inh (h - it.1 + it.2).
have def_diag: sum_diagE = sumE.
  rewrite /sumE (partition_big p xpredT) //.
  apply: eq_bigr => m _; apply: eq_bigl => [[i t]] /=.
  rewrite /p -val_eqE /= -(modn_add2l (h - i)).
  by rewrite addnA subnK 1?ltnW // modn_addl modn_small.
have [Efull dxE] := mxdirect_sum_proj_eigenspace_cycle.
have: mxdirect sum_diagE.
  apply/mxdirectP; rewrite /= -/sum_diagE def_diag (mxdirectP dxE) /=.
  rewrite (partition_big p xpredT) //.
  apply: eq_bigr => m _; apply: eq_bigl => [[i t]] /=.
  symmetry; rewrite /p -val_eqE /= -(modn_add2l (h - i)).
  by rewrite addnA subnK 1?ltnW // modn_addl modn_small.
case/mxdirect_sumsE=> /= dx_diag rank_diag.
have dx_sumE1: mxdirect (\sum_(i < h) 'E_i).
  apply: mxdirect_sum_eigenspace => i j _ _ eq_ij; apply/eqP.
  by move/eqP: eq_ij; rewrite (eq_expr_mod_order prim_eps) !modn_small. 
have diag_mod: forall m, diagE (m %% h) = diagE m.
  by move=> m; apply: eq_bigl=> it; rewrite modn_addmr.
move=> m; split; last first.
  apply/mxdirectP; rewrite /= -/(diagE m) -diag_mod.
  rewrite (mxdirectP (dx_diag (inh m) _)) //=.
  by apply: eq_bigl=> it; rewrite modn_addmr.
apply/eqmxP; rewrite sub_diagE /=.
rewrite -(capmx_idPl (_ : _ <= sumE))%MS ?Efull ?submx1 //.
rewrite -def_diag /sum_diagE (bigD1 (inh m)) //= addsmxC.
rewrite diag_mod -matrix_modr ?sub_diagE //.
rewrite ((_ :&: _ =P 0)%MS _) ?adds0mx // -submx0.
rewrite -{2}(mxdirect_sumsP dx_sumE1 (inh m)) ?capmxS //.
  by rewrite /E_ eps_mod_h.
by apply/sumsmx_subP=> i ne_i_m; rewrite (sumsmx_sup i) ?sub_diagE.
Qed.

(* This is B & G, Proposition 2.4(g) *)
Lemma rank_quasi_cent_cycle : forall m,
  \rank 'E_m = (\sum_(i < h) 'n_i * 'n_(i + m))%N.
Proof.
move=> m; have [<- dx_diag] := diag_sum_proj_eigenspace_cycle m.
rewrite (mxdirectP dx_diag) /= (reindex (fun i : 'I_h => (i, inh (i + m)))) /=.
  apply: eq_big => [i | i _]; first by rewrite modn_mod eqxx.
  by rewrite rank_proj_eigenspace_cycle /n_ Vi_mod.
exists (@fst _ _) => // [] [i t] /=.
by rewrite !inE /= (modn_small (valP t)) => def_t; apply/eqP; exact/andP.
Qed.


(* This is B & G, Proposition 2.4(h) *)
Lemma diff_rank_quasi_cent_cycle : forall m,
  (2 * \rank 'E_0 = 2 * \rank 'E_m + \sum_(i < h) distn 'n_i 'n_(i + m) ^ 2)%N.
Proof.
move=> m; rewrite !rank_quasi_cent_cycle !{1}mul2n -addnn.
rewrite {1}(reindex (fun i : 'I_h => inh (i + m))) /=; last first.
  exists (fun i : 'I_h => inh (i + (h - m %% h))%N) => i _.
    apply: val_inj; rewrite /= modn_addml -addnA addnCA -modn_addml addnCA.
    by rewrite subnKC 1?ltnW ?ltn_mod // modn_addr modn_small.
  apply: val_inj; rewrite /= modn_addml -modn_addmr -addnA.
  by rewrite subnK 1?ltnW ?ltn_mod // modn_addr modn_small.
rewrite -mul2n big_distrr -!big_split /=; apply: eq_bigr => i _.
by rewrite !addn0 (addnC (2 * _)%N) sqrn_distn addnC /n_ Vi_mod.
Qed.

Definition eq_addn_sign m n delta := if delta then m == n.+1 else m.+1 == n.

Lemma eq_addn_signC : forall m n delta,
  eq_addn_sign m n delta = eq_addn_sign n m (~~ delta).
Proof. by move=> m n d; rewrite /eq_addn_sign if_neg eq_sym -(eq_sym n). Qed.

Lemma eq_addn_signE : forall m n delta,
  eq_addn_sign m n delta = (distn m n == 1%N) && ((n < m) == delta).
Proof.
move=> m n d; rewrite /eq_addn_sign -negb_add addbC -addNb; case: ifP => -> /=.
  apply/eqP/andP=> [-> | [mn1 ltnm]].
    by rewrite leqnn distn_subLR ?leqnSn ?subSnn.
  by rewrite -addn1 -(eqP mn1) distn_subLR ?subnKC 1?ltnW.
rewrite -leqNgt; apply/eqP/andP=> [<- | [mn1 lemn]].
  by rewrite distn_subRL leqnSn ?subSnn.
by rewrite -addn1 -(eqP mn1) distn_subRL ?subnKC.
Qed.

Hypothesis rankEm : forall m, m != 0 %[mod h] -> \rank 'E_0 = (\rank 'E_m).+1.
Import paths.

(* This is B & G, Proposition 2.4(j) *)
Lemma rank_eigenspaces_quasi_homocyclic :
  exists i : 'I_h, exists n, exists2 delta,
    forall j, if j != i %[mod h] then 'n_j = n else eq_addn_sign 'n_j n delta
  & eq_addn_sign q (h * n) delta.
Proof.
have sum_n: (\sum_(i < h) 'n_i)%N = q.
  have [defV dxV] := mxdirect_sum_eigenspace_cycle.
  by rewrite -(mxdirectP dxV) defV mxrank1.
case: (ltngtP h 1) => [|h_gt1|h1]; last first; last by rewrite ltnNge h_gt0.
  rewrite /eq_addn_sign; rewrite h1; exists 0; exists q'; exists true=> [j |].
    by rewrite modn1 /= -sum_n h1 big_ord1 /n_ -Vi_mod h1 modn1.
  by rewrite mul1n.
pose dn1 i := distn 'n_i 'n_(i + 1).
have sum_dn1: (\sum_(0 <= i < h) dn1 i ^ 2 == 2)%N.
  rewrite big_mkord -(eqn_addl (2 * \rank 'E_1)) -diff_rank_quasi_cent_cycle.
  by rewrite -mulnSr -rankEm ?modn_small.
pose diff_n := filter (fun i => dn1 i != 0%N) (index_iota 0 h).
have diff_n_1: all (fun i => dn1 i == 1%N) diff_n.
  apply: contraLR sum_dn1; case/allPn=> i; rewrite mem_filter.
  case def_i: (dn1 i) => [|[|ni]] //=; case/splitPr=> e e' _.
  by rewrite big_cat big_cons /= addnCA def_i -add2n sqrn_add.
have: sorted ltn diff_n.
  by rewrite (sorted_filter ltn_trans) // /index_iota subn0 sorted_ltn_iota.
have: all (ltn^~ h) diff_n.
  by apply/allP=> i; rewrite mem_filter mem_index_iota; case/andP.
have: size diff_n = 2%N.
  move: diff_n_1; rewrite -count_filter -(eqnP sum_dn1) /diff_n.
  elim: (index_iota 0 h) => [|i e IHe]; rewrite (big_nil, big_cons) //=.
  by case def_i: (dn1 i) => [|[]] //=; rewrite def_i //; move/IHe->.
case def_jk: diff_n diff_n_1 => [|j [|k []]] //=; case/and3P=> dn1j dn1k _ _.
case/and3P=> lt_jh lt_kh _; case/andP=> lt_jk _.
have def_n: forall i,
  i <= h -> 'n_i = if i <= j then 'n_0 else if i <= k then 'n_j.+1 else 'n_k.+1.
- elim=> // i IHi lt_ik; move/(_ (ltnW lt_ik)): IHi; rewrite !(leq_eqVlt i).
  have:= erefl (i \in diff_n); rewrite {2}def_jk !inE mem_filter mem_index_iota.
  case: (i =P j) => [-> _ _ | _]; first by rewrite ltnn lt_jk.
  case: (i =P k) => [-> _ _ | _]; first by rewrite ltnNge ltnW // ltnn.
  by rewrite distn_eq0 lt_ik addn1; case: eqP => [->|].
have n_j1: 'n_j.+1 = 'n_k by rewrite (def_n k (ltnW lt_kh)) leqnn leqNgt lt_jk.
have n_k1: 'n_k.+1 = 'n_0.
  rewrite -(rank_step_eigenspace_cycle 0) (def_n h) //.
  by rewrite leqNgt lt_jh leqNgt lt_kh.
case: (leqP k j.+1) => [le_k_j1 | lt_j1_k].
  exists (Ordinal lt_kh); exists 'n_0; exists ('n_0 < 'n_k) => [i|].
    rewrite (modn_small lt_kh) /'n_i -Vi_mod -/'n_(i %% h) if_neg.
    case: ifP; [move/eqP-> | move=> ne_i_k].
      by rewrite eq_addn_signE eqxx andbT -n_k1 -addn1.
    rewrite def_n; last by rewrite ltnW ?ltn_mod.
    case: leqP => [_ // | lt_ji].
    by rewrite leq_eqVlt ne_i_k n_k1 ltnNge (leq_trans le_k_j1).
  rewrite -sum_n (bigD1 (Ordinal lt_kh)) //=.
  rewrite (eq_bigr (fun _ => 'n_0)) => [|i ne_i_k]; last first.
    rewrite def_n; last by rewrite ltnW.
    case: leqP => [_ // | lt_ji].
    by rewrite leqNgt ltn_neqAle eq_sym ne_i_k n_k1 (leq_trans le_k_j1).
  rewrite sum_nat_const cardC1 card_ord -{2}(prednK h_gt0) mulSn.
  by rewrite eq_addn_signE ltn_add2r eqxx andbT /distn !subn_add2r -n_k1 -addn1.
case: (leqP h.-1 (k - j)) => [le_h1_kj | lt_kj_h1].
  have k_h1: k = h.-1.
    apply/eqP; rewrite eqn_leq -ltnS prednK // lt_kh.
    exact: leq_trans (leq_subr j k).
  have j0: j = 0%N.
    apply/eqP; rewrite -leqn0 -(leq_add2l k) -{2}(subnK (ltnW lt_jk)).
    by rewrite addn0 leq_add2r {1}k_h1.
  exists (Ordinal h_gt0); exists 'n_k; exists ('n_k < 'n_0) => [i|].
    rewrite mod0n /'n_i -Vi_mod -/'n_(i %% h) if_neg.
    case: ifP; [move/eqP-> | move=> ne_i_0].
      by rewrite eq_addn_signE eqxx andbT -n_k1 -addn1 distnC.
    rewrite def_n; last by rewrite ltnW ?ltn_mod.
    by rewrite n_j1 j0 leqn0 ne_i_0 -ltnS k_h1 prednK ?ltn_mod ?h_gt0.
  rewrite -sum_n (bigD1 (Ordinal h_gt0)) //=.
  rewrite (eq_bigr (fun _ => 'n_k)) => [|i ne_i_0]; last first.
    rewrite def_n; last by rewrite ltnW.
    by rewrite n_j1 j0 leqn0 -if_neg ne_i_0 {1}k_h1 -ltnS prednK ?(valP i).
  rewrite sum_nat_const cardC1 card_ord -{2}(prednK h_gt0) mulSn.
  rewrite eq_addn_signE ltn_add2r eqxx andbT.
  by rewrite distnC /distn !subn_add2r -n_k1 -addn1.
suffices: \sum_(i < h) distn 'n_i 'n_(i + 2) ^ 2 > 2.
  rewrite -(ltn_add2l (2 * \rank 'E_2)) -diff_rank_quasi_cent_cycle.
  rewrite -mulnSr -rankEm ?ltnn ?modn_small //.
  by rewrite -(prednK h_gt0) ltnS (leq_trans _ lt_kj_h1) // ltnS subn_gt0.
have lt_k1h: k.-1 < h by rewrite ltnW // (ltn_predK lt_jk).
rewrite (bigD1 (Ordinal lt_jh)) // (bigD1 (Ordinal lt_k1h)) /=; last first.
  by rewrite -val_eqE neq_ltn /= orbC -subn1 -ltn_add_sub lt_j1_k.
rewrite (bigD1 (Ordinal lt_kh)) /=; last first.
  by rewrite -!val_eqE !neq_ltn /= lt_jk (ltn_predK lt_jk) leqnn !orbT.
rewrite !addnA ltn_addr // !addn2 (ltn_predK lt_jk) n_k1.
rewrite (def_n j (ltnW lt_jh)) leqnn (def_n _ (ltn_trans lt_j1_k lt_kh)).
rewrite lt_j1_k -if_neg -leqNgt leqnSn n_j1.
rewrite (def_n _ (ltnW lt_k1h)) leq_pred -if_neg -ltnNge.
rewrite -subn1 -ltn_add_sub lt_j1_k n_j1.
suffices ->: 'n_k.+2 = 'n_k.+1.
  by rewrite distnC -n_k1 -(addn1 k) -/(dn1 k) (eqP dn1k).
case: (leqP k.+2 h) => [le_k2h | ].
  by rewrite (def_n _ le_k2h) (leqNgt _ k) leqnSn n_k1 if_same.
rewrite ltnS leq_eqVlt ltnNge lt_kh orbF; move/eqP=> def_h.
rewrite -{1}def_h -add1n rank_step_eigenspace_cycle (def_n _ h_gt0).
rewrite -(leq_subS (ltnW lt_jk)) def_h leq_sub_add in lt_kj_h1.
by rewrite -(leq_add2r k) lt_kj_h1 n_k1.
Qed.

(* This is B & G, Proposition 2.4(k) *)
Lemma rank_eigenspaces_free_quasi_homocyclic :
  q > 1 -> 'n_0 = 0%N -> h = q.+1 /\ (forall j, j != 0 %[mod h] -> 'n_j = 1%N).
Proof.
move=> q_gt1 n0_0.
have [i [n [d def_n def_q]]] := rank_eigenspaces_quasi_homocyclic.
have:= def_n 0%N; rewrite mod0n modn_small // eq_sym n0_0 eq_addn_signE.
rewrite dist0n -(eq_sym d); case: eqP => [i0 | _ /= n0]; last first.
  by rewrite eq_addn_signE -n0 muln0 distn0 eqn_leq leqNgt q_gt1 in def_q.
case/andP; move/eqP=> n1; move/eqP=> dF.
rewrite i0 mod0n dF n1 muln1 /eq_addn_sign /= in def_q def_n.
by rewrite (eqP def_q); split=> // j ne_j0; have:= def_n j; rewrite ne_j0.
Qed.

End QuasiRegularCyclic.

Section Extraspecial.

Variables (p : nat) (gT : finGroupType).
Implicit Types G M S E T U : {group gT}.

Lemma cent1id : forall x : gT, x \in 'C[x]. Proof. move=> x; exact/cent1P. Qed.

Lemma cprod_center_id : forall G : {group gT}, G \* 'Z(G) = G.
Proof. by move=> G; rewrite cprodC cprodE ?mulSGid ?subsetIl ?subsetIr. Qed.

Lemma mulg_normal_maximal : forall G M H : {group gT},
  M <| G -> maximal M G -> H \subset G -> ~~ (H \subset M) -> (M * H = G)%g.
Proof.
move=> G M H; case/andP=> sMG nMG; case/maxgroupP=> _ maxM sHG not_sHM.
apply/eqP; rewrite eqEproper mul_subG // -norm_mulgenEr ?(subset_trans sHG) //.
by apply: contra not_sHM; move/maxM <-; rewrite ?mulgen_subl ?mulgen_subr.
Qed.

Section Basic.

Variable S : {group gT}.
Hypotheses (pS : p.-group S) (esS : extra_special S).

Let pZ : p.-group 'Z(S) := pgroupS (center_sub S) pS.
Lemma extraspecial_prime : prime p.
Proof.
by case: esS => _; move/prime_gt1; rewrite cardG_gt1; case/(pgroup_pdiv pZ).
Qed.

Lemma card_center_extraspecial : #|'Z(S)| = p.
Proof. by apply/eqP; apply: (pgroupP pZ); case: esS. Qed.

Lemma min_card_extraspecial : #|S| >= p ^ 3.
Proof.
have p_gt1 := prime_gt1 extraspecial_prime.
rewrite leqNgt -(part_pnat_id pS) p_part ltn_exp2l // ltnS.
case: esS => [[_ defS']]; apply: contraL; move/(p2group_abelian pS).
by move/commG1P=> S'1; rewrite -defS' [S^`(1)]S'1 cards1.
Qed.

(* This encasulates Aschbacher (23.10)(1). *)
Lemma cent1_extraspecial_maximal : forall x,
  x \in S -> x \notin 'Z(S) -> maximal 'C_S[x] S.
Proof.
move=> x Sx notZx; pose f y := [~ x, y]; have [[_ defS'] prZ] := esS.
have{defS'} fZ: forall y, y \in S -> f y \in 'Z(S).
  by move=> y Sy; rewrite -defS' mem_commg.
have fM: {in S &, {morph f : y z / y * z}}%g.
  move=> y z Sy Sz; rewrite {1}/f commgMJ conjgCV -conjgM (conjg_fixP _) //.
  rewrite (sameP commgP cent1P); apply: subsetP (fZ y Sy).
  by rewrite subIset // orbC -cent_set1 centS // sub1set !(groupM, groupV).
pose fm := Morphism fM.
have fmS: fm @* S = 'Z(S).
  have sfmS: fm @* S \subset 'Z(S).
    by apply/subsetP=> fz; case/morphimP=> z _ Sz ->; exact: fZ.
  apply/eqP; rewrite eqEsubset sfmS; apply: contraR notZx; move/(prime_TIg prZ).
  rewrite (setIidPr _) // => fmS1; rewrite inE Sx; apply/centP=> y Sy.
  by apply/commgP; rewrite -in_set1 -[[set _]]fmS1; exact: mem_morphim. 
have ->: 'C_S[x] = 'ker fm.
  apply/setP=> z; rewrite inE (sameP cent1P commgP) !inE.
  by rewrite -invg_comm eq_invg_mul mulg1.
rewrite p_index_maximal ?subsetIl // -card_quotient ?ker_norm //.
by rewrite (isog_card (first_isog fm)) /= fmS.
Qed.

End Basic.

Lemma normalI : forall G H K, H <| G -> K <| G -> H :&: K <| G.
Proof.
move=> G H K; case/andP=> sHG nHG; case/andP=> _ nKG.
by rewrite /normal subIset ?sHG // normsI.
Qed.

Lemma card_p3group_extraspecial : forall E,
  prime p -> #|E| = (p ^ 3)%N -> #|'Z(E)| = p -> extra_special E.
Proof.
move=> E p_pr oEp3 oZp; have p_gt0 := prime_gt0 p_pr.
have pE: p.-group E by rewrite /pgroup oEp3 pnat_exp pnat_id.
have pEq: p.-group (E / 'Z(E))%g by rewrite quotient_pgroup.
have [sZE nZE] := andP (center_normal E).
have oEq: #|E / 'Z(E)|%g = (p ^ 2)%N.
  by rewrite card_quotient -?divgS // oEp3 oZp expnS mulKn.
have cEEq: abelian (E / 'Z(E))%g by exact: card_p2group_abelian oEq.
have not_cEE: ~~ abelian E.
  have: #|'Z(E)| < #|E| by rewrite oEp3 oZp (ltn_exp2l 1) ?prime_gt1.
  by apply: contraL => cEE; rewrite -leqNgt subset_leq_card // subsetI subxx.
have defE': E^`(1) = 'Z(E).
  apply/eqP; rewrite eqEsubset der1_min //=; apply: contraR not_cEE => not_sE'Z.
  apply/commG1P; apply: (nil_TI_Z (pgroup_nil pE) (der_normal 1 _)).
  by rewrite setIC prime_TIg ?oZp.
split; [split=> // | by rewrite oZp]; apply/eqP.
rewrite eqEsubset andbC -{1}defE' {1}(Phi_mulgen pE) mulgen_subl.
rewrite -quotient_sub1 ?(subset_trans (Phi_sub _)) //.
rewrite subG1 /= (quotient_Phi pE) //= (trivg_Phi pEq); apply/abelemP=> //.
split=> // Zx EqZx; apply/eqP; rewrite -order_dvdn.
rewrite -(part_pnat_id (mem_p_elt pEq EqZx)) p_part (@dvdn_exp2l _ _ 1) //.
rewrite leqNgt -pfactor_dvdn // -oEq; apply: contra not_cEE => sEqZx.
rewrite (@center_cyclic_abelian _ E) ?center_abelian //; apply/cyclicP.
exists Zx; apply/eqP; rewrite eq_sym eqEcard cycle_subG EqZx -orderE.
exact: dvdn_leq sEqZx.
Qed.

(* This is part of Aschbacher (23.13) and (23.14). *)
Theorem extraspecial_structure : forall S, p.-group S -> extra_special S ->
  {Es | all (fun E => (#|E| == p ^ 3)%N && ('Z(E) == 'Z(S))) Es
      & \big[cprod/1%g]_(E <- Es) E \* 'Z(S) = S}.
Proof.
move=> S; elim: {S}_.+1 {-2}S (ltnSn #|S|) => // m IHm S leSm pS esS.
have: #|S| >= p ^ 3 := min_card_extraspecial pS esS.
rewrite leq_eqVlt; case: eqP => /= [oSp3 _| _ gtSp3].
  by exists [:: S]; rewrite /= ?oSp3 ?eqxx // big_seq1 cprod_center_id.
have [p_pr oZp] := (extraspecial_prime pS esS, card_center_extraspecial pS esS).
have [[defPhiS defS'] prZ]:= esS.
have subZeq: forall E T, 'Z(S) \subset E -> E \* T = S -> 'Z(E) = 'Z(S).
  move=> E T sZE; case/cprodP=> _ defS cET.
  have sES: E \subset S by rewrite -defS mulg_subl.
  apply/eqP; rewrite eqEsubset andbC subsetI sZE subIset ?centS ?orbT //=.
  by rewrite subsetI subIset ?sES //= -defS centM setIC setSI.
have [x Sx notZx]: {x | x \in S & x \notin 'Z(S)}.
  case: (set_0Vmem (S :\: 'Z(S))) => [|[x]]; last by case/setDP; exists x.
  move/eqP; rewrite setDeq0; move/subset_leq_card.
  by rewrite leqNgt oZp (leq_ltn_trans _ gtSp3) // (leq_exp2l 1) ?prime_gt1.
have maxCx := cent1_extraspecial_maximal esS Sx notZx.
have [iCx nsCx] := (p_maximal_index pS maxCx, p_maximal_normal pS maxCx).
have [y Sy notCxy]: {y | y \in S & y \notin 'C_S[x]}.
  case: (set_0Vmem (S :\: 'C_S[x])) => [|[y]]; last by case/setDP; exists y.
  by move/eqP; rewrite setDeq0; case/idPn; case/andP: (maxgroupp maxCx).
have notZy: y \notin 'Z(S).
  apply: contra notCxy; apply: subsetP.
  by rewrite setIS // -cent_set1 centS ?sub1set.
have maxCy := cent1_extraspecial_maximal esS Sy notZy.
have [iCy nsCy] := (p_maximal_index pS maxCy, p_maximal_normal pS maxCy).
pose E := <[x]> <*> <[y]> <*> 'Z(S); pose T := 'C_S(E).
have sZE: 'Z(S) \subset E by rewrite mulgen_subr.
have sES: E \subset S by rewrite !mulgen_subG !cycle_subG Sx Sy subsetIl.
have sZT: 'Z(S) \subset T by rewrite setIS ?centS.
have sTS: T \subset S by exact: subsetIl.
have defT: T = 'C_S[x] :&: 'C_S[y].
  rewrite /T !cent_mulgen !cent_cycle -!setIA 3!(setICA S) (setIA S) setIid.
  by rewrite (setIC 'C[y]) ['C_S(_)](setIidPl _) // centsC subsetIr.
have iT: (#|S : T| = p ^ 2)%N.
  rewrite -mulnn -{1}iCx -{1}iCy -!divgS ?subsetIl //= -/T.
  rewrite divn_mulA ?divn_mulAC ?cardSg ?subsetIl //= divn_divl mulnn.
  rewrite mul_cardG -defT -divn_divl; congr (_ %/ _)%N.
  rewrite (mulg_normal_maximal nsCx) ?mulnK ?cardG_gt0 ?subsetIl //.
  by apply: contra notCxy; move/subsetP->; rewrite // inE Sy cent1id.
have{iT gtSp3} [ltTS gtTp]: #|T| < #|S| /\ #|T| > p.
  have p2_gt1: p ^ 2 > 1 by rewrite (ltn_exp2l 0) ?prime_gt1.
  rewrite -(LaGrange sTS) ltn_Pmulr ?cardG_gt0 ?iT //.
  by rewrite -(ltn_pmul2r (ltnW p2_gt1)) -expnS -iT LaGrange.
have defS: (E \* T = S)%g.
  apply/eqP; rewrite cprodC cprodEgen ?subsetIr //= 2!mulgenA -/T defT.
  rewrite -!genM_mulgen group_modr ?cycle_subG 1?inE ?Sx ?cent1id //=.
  rewrite mulgen_idl /= (mulg_normal_maximal nsCy) ?cycle_subG //; last first.
    by rewrite inE cent1C Sx -Sy -in_setI.
  rewrite setIAC setIid -genM_mulgen (mulg_normal_maximal nsCx) ?cycle_subG //.
  by rewrite !(genGid, mulGSid) ?subsetIl.
have defZT: 'Z(T) = 'Z(S) by move: defS; rewrite cprodC; exact: subZeq.
have{gtTp} esT: extra_special T.
  split; last by rewrite defZT.
  have nsTS: T <| S by rewrite /normal sTS defT normsI ?normal_norm.
  have defT': T^`(1) = 'Z(T).
    apply/eqP; rewrite eqEsubset defZT -{1}defS' dergS //=.
    apply: contraLR gtTp; move/(prime_TIg prZ); rewrite setIC -oZp -leqNgt.
    move/(nil_TI_Z (pgroup_nil pS) (char_normal_trans (der_char _ _) nsTS)).
    by move/commG1P=> cEE; rewrite -defZT subset_leq_card // subsetI subxx.
  split=> //; apply/eqP; rewrite (Phi_mulgen (pgroupS sTS pS)) -defT'.
  rewrite eqEsubset mulgen_subl defT' defZT -{2}defPhiS (Phi_mulgen pS).
  by rewrite defS' genS // setUS // MhoS.
have{IHm} [//|Es esEs prodEs] := IHm _ (leq_trans ltTS _) (pgroupS sTS pS) esT.
exists ([group of E] :: Es); last by rewrite big_cons -cprodA -{2}defZT prodEs.
rewrite /= -{2}defZT esEs (subZeq _ _ sZE defS) eqxx !andbT.
apply/eqP; rewrite -(LaGrange sZE) oZp; congr (_ * _)%N.
have [_ nZS] := andP (center_normal S).
have nZx := subsetP nZS x Sx; have nZy := subsetP nZS y Sy. 
rewrite -card_quotient ?(subset_trans sES) //=.
rewrite quotient_mulgen ?mulgen_subG ?cycle_subG ?nZx //.
rewrite quotient_gen ?subUset ?cycle_subG ?nZx //= quotientU -mulgenE.
have abelSq: p.-abelem (S / 'Z(S))%g by rewrite -defPhiS Phi_quotient_abelem.
have cSq := sub_abelian_cent2 (abelem_abelian abelSq).
rewrite norm_mulgenEl ?cents_norm ?cSq ?quotientS ?cycle_subG //=.
rewrite !quotient_cycle //=; have Sq_p := abelem_order_p abelSq.
have oZx: #[coset 'Z(S) x] = p.
  case: (Sq_p (coset _ x)) => //; first exact: mem_morphim.
  by apply: contra notZx; move/eqP => Zx; rewrite coset_idr.
have:= p_pr; rewrite -{1 2}oZx; case/(prime_subgroupVti <[coset _ y]>).
  rewrite cycle_subG; case/cycleP=> k; rewrite -morphX //.
  case/kercoset_rcoset=> // [|z Zz def_x]; first by rewrite groupX.
  case/setIP: Zz => _ cSz; case/negP: notCxy; rewrite inE Sy cent1E.
  by rewrite def_x mulgA -(centP cSz) //= -!mulgA -expgS -expgSr.
rewrite setIC; move/TI_cardMg->; congr (_ * _)%N.
case: (Sq_p (coset _ y)) => //; first exact: mem_morphim.
by apply: contra notZy; move/eqP => Zy; rewrite coset_idr.
Qed.

Section StructureCorollaries.

Variable S : {group gT}.
Hypotheses (pS : p.-group S) (esS : extra_special S).

Let p_pr := extraspecial_prime pS esS.
Let oZp := card_center_extraspecial pS esS.

(* This is Aschbacher (23.10)(2). *)
Lemma card_extraspecial : {n | n > 0 & #|S| = (p ^ n.*2.+1)%N}.
Proof.
exists (logn p #|S|)./2.
  rewrite half_gt0 ltnW // -(leq_exp2l _ _ (prime_gt1 p_pr)) -p_part.
  by rewrite (part_pnat_id pS) min_card_extraspecial.
have [Es] := extraspecial_structure pS esS.
elim: Es {3 4 5}S => [_ _ <-| E s IHs T] /=.
  by rewrite big_nil cprod1g oZp (pfactorK 1).
rewrite -andbA big_cons -cprodA; case/and3P; move/eqP=> oEp3; move/eqP=> defZE.
move/IHs=> {IHs}IHs; case/cprodP=> [[_ U _ defU]]; rewrite defU => defT cEU.
rewrite -(mulnK #|T| (cardG_gt0 (E :&: U))) -defT -mul_cardG /=.
have ->: E :&: U = 'Z(S).
  apply/eqP; rewrite eqEsubset subsetI -{1 2}defZE subsetIl setIS 1?centsC //=.
  by case/cprodP: defU => [[V _ -> _]]  <- _; exact: mulG_subr.
rewrite (IHs U) // oEp3 oZp -expn_add addSn expnS mulKn ?prime_gt0 //.
by rewrite pfactorK //= uphalf_double.
Qed.

Import perm.
(* This the parts of Aschbacher (23.12) and ex. 8.5 that are used in (34.9). *)
Lemma center_aut_extraspecial : forall k, coprime k p ->
  exists2 f, f \in Aut S & forall z, z \in 'Z(S) -> f z = (z ^+ k)%g.
Proof.
move=> k; rewrite coprime_sym => co_p_k.
have [p2 | odd_p] := even_prime p_pr.
  exists 1%g => [|z Zz]; first exact: group1.
  move/order_dvdG: Zz; rewrite oZp p2 order_dvdn; move/eqP=> z_inv.
  have odd_k: odd k by rewrite p2 prime_coprime // dvdn2 negbK in co_p_k.
  rewrite perm1 -(odd_double_half k) odd_k expgS -mul2n expgn_mul z_inv.
  by rewrite exp1gn mulg1.
suff [A [B]]: exists H, exists K, [/\ K ><| H = S, abelian K & 'Z(S) \subset K].
  case; case/sdprodP=> [[K H -> -> {A B}]] defS nKH tiHK cKK sZK.
  have [nsKS cplKH]: K <| S /\ H \in [complements to K in S].
    by rewrite complgC; apply/sdprod_normal_compl; rewrite sdprodE.
  pose fk x := (divgr K H x ^+ k * remgr K H x)%g.
  have fM: {in S &, {morph fk: x y / x * y}%g}.
    move=> x y; rewrite -defS => Sx Sy.
    rewrite mulgA -(mulgA _ _ (_ ^+ k)%g) (conjgCV _ (_ ^+ k)%g).
    rewrite conjXg mulgA -expMgn; last first.
      apply: (centsP cKK); rewrite ?memJ_norm ?mem_divgr // groupV.
      by rewrite (subsetP nKH) ?mem_remgr.
    by rewrite mulgA mulgK 2!mulgA -2!mulgA -invMg -(remgrM cplKH) // -defS.
  pose f := Morphism fM; have inj_f: 'injm f.
    apply/subsetP=> x; rewrite !inE /= -defS -eq_invg_mul; case/andP=> Sx.
    move/eqP=> ker_x; have Kx: x \in K.
      by rewrite (divgr_eq K H x) -ker_x groupM ?groupV ?groupX ?mem_divgr.
    have co_K_k: coprime #|K| k.
      have: p.-group K by apply: pgroupS (pS); rewrite -defS mulG_subl.
      by case/p_natP=> i ->; rewrite coprime_expl // prime_coprime.
    rewrite -eq_invg1 -(expgnK co_K_k Kx) -expVgn.
    by rewrite remgr1 ?divgr_id // in ker_x; rewrite ker_x exp1gn.
  have fS: f @* S = S.
    apply/eqP; rewrite eqEcard card_injm // leqnn andbT.
    apply/subsetP=> fx; case/morphimP=> x _ /=; rewrite -defS => Sx ->{fx}.
    by rewrite mem_mulg ?groupX ?mem_divgr ?mem_remgr.
  exists (aut inj_f fS) => [|x]; first exact: Aut_aut.
  move/(subsetP sZK)=> Kx; rewrite autE ?(subsetP (normal_sub nsKS)) //=.
  by rewrite /fk remgr1 ?divgr_id // mulg1.
have [p_gt1 p_gt0] := (prime_gt1 p_pr, prime_gt0 p_pr).
have [Es] := extraspecial_structure pS esS.
elim: Es {1 5 6}S (subxx S) => [_ _ _ <-| E s IHs T sTS] /=.
  exists 1%g; exists ('Z(S)); rewrite center_abelian.
  by rewrite sdprodg1 big_nil cprod1g.
rewrite -andbA big_cons -cprodA; case/and3P; move/eqP=> oEp3; move/eqP=> defZ.
move/IHs=> {IHs}IHs; case/cprodP=> [[_ U _ defU]]; rewrite defU => defT cEU.
have sUS: U \subset S by rewrite (subset_trans _ sTS) // -defT mulG_subr.
have{IHs s defU sUS} [A [B []]] := IHs U sUS defU.
case/sdprodP=> [[K H -> ->{A B}]] defKH nKH tiHK cKK sZK.
have pE: p.-group E by rewrite /pgroup oEp3 pnat_exp pnat_id.
have nZE: E \subset 'N('Z(S)) by rewrite -defZ normal_norm ?center_normal.
have [[defPhiE defE'] prZ]: special E /\ prime #|'Z(S)|.
  by case: (card_p3group_extraspecial p_pr oEp3); rewrite defZ.
have{defPhiE} sEpZ: forall x, x \in E -> (x ^+ p)%g \in 'Z(S).
  move=> x Ex; rewrite -defZ -defPhiE (Phi_mulgen pE) mem_gen // inE orbC.
  by rewrite (Mho_p_elt 1) // (mem_p_elt pE).
have not_sEZ: ~~ (E \subset 'Z(S)).
  by rewrite proper_subn // properEcard oZp oEp3 -defZ subsetIl (ltn_exp2l 1).
have not_cEE: ~~ abelian E by rewrite -defZ subsetI subxx in not_sEZ.
have [x [Ex notZx oxp]]: exists x, [/\ x \in E, x \notin 'Z(S) & #[x] %| p]%N.
  have [x Ex notZx] := subsetPn not_sEZ.
  case: (prime_subgroupVti <[x ^+ p]> prZ) => [sZxp | ]; last first.
    move/eqP; rewrite (setIidPl _) ?cycle_subG ?sEpZ //.
    by rewrite cycle_eq1 -order_dvdn; exists x.
  have [y Ey notxy]: exists2 y, y \in E & y \notin <[x]>.
    apply/subsetPn; apply: contra not_cEE => sEx.
    by rewrite (abelianS sEx) ?cycle_abelian.
  have: (y ^+ p)%g \in <[x ^+ p]> by rewrite (subsetP sZxp) ?sEpZ.
  case/cycleP=> i def_yp; set xi := (x ^- i)%g.
  have Exi: xi \in E by rewrite groupV groupX.
  exists (y * xi)%g; split; first by rewrite groupM.
    have sxpx: <[x ^+ p]> \subset <[x]> by rewrite cycle_subG mem_cycle.
    apply: contra notxy; move/(subsetP (subset_trans sZxp sxpx)).
    by rewrite groupMr // groupV mem_cycle.
  pose z := [~ xi, y]; have Zz: z \in 'Z(E) by rewrite -defE' mem_commg.
  case: (setIP Zz) => _; move/centP=> cEz.
  rewrite order_dvdn expMg_Rmul; try by apply: commute_sym; apply: cEz.
  rewrite def_yp expVgn -!expgn_mul mulnC mulgV mul1g -order_dvdn.
  by rewrite (dvdn_trans (order_dvdG Zz)) //= defZ oZp bin2odd // dvdn_mulr.
have{oxp} oxp: #[x] = p.
  apply/eqP; case/primeP: p_pr => _ dvd_p; case/orP: (dvd_p _ oxp) => //.
  by rewrite order_eq1; case: eqP notZx => // ->; rewrite group1.
pose xZ := <[x]> <*> 'Z(S).
have ti_xZ: <[x]> :&: 'Z(S) = 1%g.
  rewrite setIC prime_TIg //; apply: contra notZx; rewrite -cycle_subG => sZx.
  by rewrite subEproper eq_sym eqEcard sZx oZp -oxp leqnn.
have s_xZ_E: xZ \subset E by rewrite mulgen_subG cycle_subG Ex -defZ subsetIl.
have o_xZ: #|xZ| = (p ^ 2)%N.
  rewrite /xZ norm_mulgenEl ?cycle_subG ?(subsetP nZE) // TI_cardMg //.
  by rewrite oZp -orderE oxp.
have [y Ey not_xZy]: exists2 y, y \in E & y \notin xZ.
  apply/subsetPn; rewrite proper_subn // properEcard s_xZ_E o_xZ oEp3.
  by rewrite ltn_exp2l.
pose xH := <[x]> <*> H; pose yK := <[y]> <*> K.
have def_xyZ: (<[x]> <*> <[y]>) <*> 'Z(S) = E.
  have s_yxZ_E: <[y]> <*> xZ \subset E by rewrite mulgen_subG cycle_subG Ey.
  apply/eqP; rewrite (mulgenC <[x]>) -mulgenA eqEcard s_yxZ_E oEp3.
  rewrite dvdn_leq ?pfactor_dvdn ?cardG_gt0 // -(ltn_exp2l _ _ p_gt1).
  rewrite -p_part (part_pnat_id (pgroupS _ pE)) // -/xZ /= -o_xZ.
  rewrite (ltn_leqif (subset_leqif_card _)) ?mulgen_subr //.
  by rewrite mulgen_subG subxx andbT cycle_subG.
have def_yKxH: yK <*> xH = T.
  rewrite mulgenA (mulgenC yK) mulgenA -(genGid K) -(setUidPr sZK) mulgenA.
  by rewrite def_xyZ -mulgenA (norm_mulgenEr nKH) defKH cent_mulgenEl.
have sZyK: 'Z(S) \subset yK by rewrite (subset_trans sZK) ?mulgen_subr.
have cyKyK: abelian yK.
  rewrite /yK -genM_mulgen abelian_gen abelianM cycle_abelian cKK.
  rewrite cycle_subG; apply: subsetP Ey; apply: subset_trans cEU _.
  by rewrite -defKH centM subsetIl.
have n_yK_xH: xH \subset 'N(yK).
  move: sTS; rewrite -def_yKxH mulgen_subG; case/andP=> syKS sxHS.
  by rewrite (subset_trans sxHS) // sub_der1_norm //; case: esS => [[_ ->]].
exists xH; exists yK; split; rewrite // sdprodEgen // cardMg_TI //=.
have tiEU: E :&: U = 'Z(S).
  apply/eqP; rewrite eqEsubset subsetI -{1 2}defZ subsetIl setIS 1?centsC //=.
  by rewrite -defKH (subset_trans sZK) ?mulG_subl.
have [cKy cHx]: <[y]> \subset 'C(K) /\ <[x]> \subset 'C(H).
  move: cEU; rewrite -defKH centM -def_xyZ subsetI !mulgen_subG -!andbA.
  by case/and5P.
rewrite -norm_mulgenEr //= def_yKxH -(leq_pmul2r p_gt0) -oZp -{2}tiEU.
rewrite -defT -mul_cardG (cent_mulgenEl cHx) -defKH !TI_cardMg //; last first.
  apply/trivgP; rewrite -ti_xZ subsetI subsetIl -tiEU -defKH.
  by rewrite setISS ?cycle_subG ?mulG_subr.
rewrite mulnAC (cent_mulgenEl cKy) -{1}(mulSGid sZK) mulgA.
rewrite -(norm_mulgenEl (subset_trans _ nZE)) ?cycle_subG //.
set yZ := <[y]> <*> 'Z(S); have <-: yZ :&: K = 'Z(S).
  apply/eqP; rewrite eqEsubset subsetI sZK mulgen_subr.
  by rewrite -tiEU -def_xyZ -mulgenA -defKH setISS ?mulgen_subr ?mulG_subl.
rewrite -mul_cardG /= -/yZ mulnAC mulnA -TI_cardMg.
  rewrite -norm_mulgenEr; first by rewrite mulgenC mulgenA def_xyZ mulnAC mulnA.
  rewrite cycle_subG; apply: subsetP Ex.
  apply: sub_der1_norm; first by rewrite defE' defZ mulgen_subr.
  by rewrite -def_xyZ -mulgenA mulgen_subr.
rewrite setIC prime_TIg -?orderE ?oxp //= -/yZ.
apply: contra not_cEE => sx_yZ; apply: abelianS cyKyK.
by rewrite -def_xyZ -mulgenA -genM_mulgen mulSGid // genGid genS ?setUS.
Qed.

(* This is Aschbacher (34.9), parts (1)-(4). *)
Import finalg.
Theorem representations_extraspecial : forall n (F : fieldType),
    #|S| = (p ^ n.*2.+1)%N -> group_splitting_field F S -> p \notin [char F] ->
    let aS := regular_repr F S in
    forall sS : socleType aS,
  [/\ #|[set i : sS | Wedderburn_degree i == 1%N]| = (p ^ n.*2)%N,
      exists iphi : 'I_p.-1 -> sS, let phi i := socle_repr (iphi i) in
        [/\ injective iphi,
            codom iphi =i [pred i | Wedderburn_degree i > 1],
            forall i, mx_repr_faithful (phi i),
            forall z, z \in 'Z(S)^# ->
              exists2 w, GRing_order p w
                       & forall i, phi i z = (w ^+ i.+1)%:M
          & forall i, Wedderburn_degree (iphi i) = (p ^ n)%N]
    & #|sS| = (p ^ n.*2 + p.-1)%N].            
Proof.
move=> n F oSpn splitF p'F aS sS; set lin_pi := finset _.
have F'S: [char F]^'.-group S by exact: (pi_pnat pS).
have [[defPhiS defS'] prZ] := esS.
have [p_gt1 p_gt0] := (prime_gt1 p_pr, prime_gt0 p_pr).
have nb_lin: #|lin_pi| = (p ^ n.*2)%N.
  rewrite card_linear_comp // -divgS ?der_sub //=.
  by rewrite oSpn defS' oZp expnS mulKn.
have nb_irr: #|sS| = (p ^ n.*2 + p.-1)%N.
  rewrite Wedderburn_card //.
  pose Zcl := classes S ::&: 'Z(S).
  have cardZcl: #|Zcl| = p.
    transitivity #|[set [set z] | z <- 'Z(S)]|; last first.
      by rewrite card_imset //; exact: set1_inj.
    apply: eq_card=> zS; apply/setIdP/imsetP=> [[] | [z]].
      case/imsetP=> z Sz ->{zS} szSZ.
      have Zz: z \in 'Z(S) by rewrite (subsetP szSZ) ?class_refl.
      exists z => //; rewrite inE Sz in Zz.
      apply/eqP; rewrite eq_sym eqEcard sub1set class_refl cards1.
      by rewrite -index_cent1 (setIidPl _) ?indexgg // sub_cent1.
    case/setIP=> Sz cSz ->{zS}; rewrite sub1set inE Sz; split=> //.
    apply/imsetP; exists z; rewrite //.
    apply/eqP; rewrite eqEcard sub1set class_refl cards1.
    by rewrite -index_cent1 (setIidPl _) ?indexgg // sub_cent1.
  move/eqP: (class_formula S); rewrite (bigID (mem Zcl)) /=.
  rewrite (eq_bigr (fun _ => 1%N)) => [|zS]; last first.
    case/andP=> _; case/setIdP; case/imsetP=> z Sz ->{zS}.
    rewrite subsetI; case/andP=> _ cSzS.
    rewrite (setIidPl _) ?indexgg // sub_cent1 (subsetP cSzS) //.
    exact: mem_repr (class_refl S z).
  rewrite sum1dep_card setIdE (setIidPr _) 1?cardsE ?cardZcl; last first.
    by apply/subsetP=> zS; rewrite 2!inE; case/andP.
  have pn_gt0: p ^ n.*2 > 0 by rewrite expn_gt0 p_gt0.
  rewrite oSpn expnS -(prednK pn_gt0) mulnS eqn_addl.
  rewrite (eq_bigr (fun _ => p)) => [|xS]; last first.
    case/andP=> SxS; rewrite inE SxS; case/imsetP: SxS => x Sx ->{xS} notZxS.
    have [y Sy ->] := repr_class S x; apply: p_maximal_index => //.
    apply: cent1_extraspecial_maximal => //; first exact: groupJ.
    apply: contra notZxS => Zxy; rewrite -{1}(lcoset_id Sy) class_lcoset.
    rewrite ((_ ^: _ =P [set x ^ y])%g _) ?sub1set // eq_sym eqEcard.
    rewrite sub1set class_refl cards1 -index_cent1 (setIidPl _) ?indexgg //.
    by rewrite sub_cent1; apply: subsetP Zxy; exact: subsetIr.
  rewrite sum_nat_dep_const mulnC eqn_pmul2l //; move/eqP <-.
  rewrite addSnnS prednK // -cardZcl -[card _](cardsID Zcl) /= addnC.
  by congr (_ + _)%N; apply: eq_card => t; rewrite !inE andbC // andbAC andbb.
have fful_nlin: forall i, i \in ~: lin_pi -> mx_repr_faithful (socle_repr i).
  move=> i; rewrite !inE => nlin_phi.
  apply/trivgP; apply: (nil_TI_Z (pgroup_nil pS) (rker_normal _)).
  rewrite setIC; apply: (prime_TIg prZ); rewrite /= -defS' der1_sub_rker //.
  exact: socle_irr.
have [i0 nlin_i0]: exists i0, i0 \in ~: lin_pi.
  by apply/card_gt0P; rewrite cardsCs setCK nb_irr nb_lin addKn -subn1 subn_gt0.
have [z defZ]: exists z, 'Z(S) = <[z]> by apply/cyclicP; rewrite prime_cyclic.
have Zz: z \in 'Z(S) by [rewrite defZ cycle_id]; have [Sz cSz] := setIP Zz.
have ozp: #[z] = p by [rewrite -oZp defZ].
have ntz: z != 1%g by rewrite -order_gt1 ozp.
pose phi := socle_repr i0; have irr_phi: mx_irreducible phi := socle_irr i0.
have [w phi_z]: exists w, phi z = w%:M.
  apply/is_scalar_mxP; apply: mx_abs_irr_cent_scalar (splitF _ _ irr_phi) _ _.
  by apply/centgmxP=> x Sx; rewrite -!{1}repr_mxM 1?(centP cSz).
have phi_ze: forall e, phi (z ^+ e)%g = (w ^+ e)%:M.
  move: (phi) phi_z; case/mx_irrP: irr_phi => n_gt0 _.
  case: (\rank _) n_gt0 => // d _ fi fi_z e.
  by rewrite repr_mxX // fi_z -(ringM_exp (@scalar_mxRM _ _)).
have injZM: forall i : sS, injective (@scalar_mx F (Wedderburn_degree i)).
  move=> i; rewrite -(prednK (Wedderburn_degree_gt0 i)).
  exact: (fieldM_inj (@scalar_mxRM _ _)).
have wp1: w ^+ p = 1.
  by apply: (injZM i0); rewrite -phi_ze -ozp expg_order repr_mx1.
have prim_w: forall k, 0 < k < p -> GRing_order p (w ^+ k).
  move=> k; case/andP=> k_gt0 lt_k_p; apply/andP; split=> //.
  apply/forallP=> [[d ltdp] /=]; apply/eqP.
  transitivity (z ^+ (k * d.+1) \in rker phi)%g.
    by rewrite inE groupX // phi_ze mul1mx (inj_eq (injZM i0)) exprn_mulr.
  rewrite (trivgP (fful_nlin i0 _)) // inE -order_dvdn ozp.
  rewrite euclid // /dvdn modn_small // eqn0Ngt k_gt0 -(modnn p) /=.
  rewrite -{2 4}[p]prednK // eqSS -{1}(addn1 p.-1) -{1}addn1 modn_add2r.
  by rewrite !modn_small ?prednK.
have [a defAutZ]: exists a, Aut 'Z(S) = <[a]>.
  by apply/cyclicP; rewrite Aut_prime_cyclic ?ozp.
have modIp': forall i : 'I_p.-1, i.+1 %% p = i.+1.
  by case=> i /=; rewrite -ltnS prednK //; exact: modn_small.
have phi_unitP : forall i : 'I_p.-1, GRing.unit (i.+1%:R : 'Z_#[z]).
  move=> i; rewrite /GRing.unit /= ozp val_Zp_nat ?Zp_cast //.
  by rewrite prime_coprime // -lt0n !modIp'.
pose ephi i := invm (injm_Zpm a) (Zp_unitm (Sub _ (phi_unitP i))).
pose j : 'Z_#[z] := val (invm (injm_Zp_unitm z) a).
have co_j_p: coprime j p.
  rewrite coprime_sym /j; case: (invm _ a) => /=.
  by rewrite ozp /GRing.unit /= Zp_cast.
have [alpha Aut_alpha alphaZ] := center_aut_extraspecial co_j_p.
have alpha_i_z: forall i, ((alpha ^+ ephi i) z = z ^+ i.+1)%g.
  move=> i; transitivity ((a ^+ ephi i) z)%g.
    elim: (ephi i : nat) => // e IHe; rewrite !expgS !permM alphaZ //.
    have Aut_a: a \in Aut 'Z(S) by rewrite defAutZ cycle_id.
    rewrite -{2}[a](invmK (injm_Zp_unitm z)); last by rewrite im_Zp_unitm -defZ.
    rewrite /= autE ?cycle_id // -/j /= /cyclem.
    rewrite -(autmE (groupX _ Aut_a)) -(autmE (groupX _ Aut_alpha)).
    by rewrite !morphX //= !autmE IHe.
  rewrite [(a ^+ _)%g](invmK (injm_Zpm a)) /=; last first.
    by rewrite im_Zpm -defAutZ defZ Aut_aut.
  by rewrite autE ?cycle_id //= val_Zp_nat ozp ?modIp'.
have rphiP: forall i, S :==: autm (groupX (ephi i) Aut_alpha) @* S.
  by move=> i; rewrite im_autm.
pose rphi i := morphim_repr (eqg_repr phi (rphiP i)) (subxx S).
have rphi_irr: forall i, mx_irreducible (rphi i).
  by move=> i; apply/morphim_mx_irr; exact/eqg_mx_irr.
have rphi_fful: forall i, mx_repr_faithful (rphi i).
  move=> i; rewrite /mx_repr_faithful rker_morphim rker_eqg.
  by rewrite (trivgP (fful_nlin _ nlin_i0)) morphpreIdom; exact: injm_autm.
have rphi_z: forall i, rphi i z = (w ^+ i.+1)%:M.
  move=> i; rewrite /rphi [phi]lock /= /morphim_mx autmE alpha_i_z -lock.
  by rewrite phi_ze.
pose iphi i := regular_comp sS (rphi i); pose phi_ i := socle_repr (iphi i).
have{phi_ze} phi_ze: forall i e, phi_ i (z ^+ e)%g = (w ^+ (e * i.+1)%N)%:M.
  move=> i e; have: phi_ i z = (w ^+ i.+1)%:M.
    have:= mx_rsim_sym (rsim_regular_comp sS F'S (rphi_irr i)).
    case/mx_rsim_def=> B [B' _ homB]; rewrite /phi_ homB // rphi_z.
    rewrite -{1}scalemx1 -scalemxAr -scalemxAl -{1}(repr_mx1 (rphi i)).
    by rewrite -homB ?repr_mx1 ?scalemx1.
  move: (phi_ i); rewrite -/(Wedderburn_degree (iphi i)).
  rewrite -(prednK (Wedderburn_degree_gt0 _)) => r r_z.
  by rewrite repr_mxX // r_z -(ringM_exp (@scalar_mxRM _ _)) -exprn_mulr mulnC.
have inj_iphi: injective iphi.
  move=> i1 i2 eq_phi12; apply/eqP; move/eqP: (phi_ze i2 1%N).
  rewrite /phi_ -eq_phi12 -/(phi_ i1) phi_ze !mul1n (inj_eq (injZM _)).
  by rewrite (eq_expr_mod_order (prim_w 1%N p_gt1)) !modIp'.
have deg_phi: forall i, Wedderburn_degree (iphi i) = Wedderburn_degree i0.
  by move=> i; case: (rsim_regular_comp sS F'S (rphi_irr i)).
have im_iphi: codom iphi =i [pred i | Wedderburn_degree i != 1%N].
  apply/subset_cardP.
    rewrite card_image // card_ord.
    move/eqP: (cardsC lin_pi); rewrite nb_lin nb_irr eqn_addl.
    by move/eqP <-; apply: eq_card => i; rewrite !inE.
  apply/subsetP=> fi; case/imageP=> i _ ->.
  by rewrite inE /= deg_phi; rewrite !inE in nlin_i0.
split=> //; exists iphi; rewrite -/phi_.
split=> // [i | i | ze | i].
- by rewrite im_iphi !inE neq_ltn ltnNge Wedderburn_degree_gt0.
- have sim_i := rsim_regular_comp sS F'S (rphi_irr i).
  by rewrite -(mx_rsim_faithful sim_i) rphi_fful.
- rewrite {1}defZ 2!inE andbC; case/andP.
  case/cyclePmin=> e; rewrite ozp => lt_e_p ->{ze}.
  case: (posnP e) => [-> | e_gt0 _]; first by rewrite eqxx.
  exists (w ^+ e) => [|i]; first by rewrite prim_w ?e_gt0.
  by rewrite phi_ze exprn_mulr.
rewrite deg_phi {i}; set d := Wedderburn_degree i0.
apply/eqP; move/eqP: (sum_Wedderburn_degree sS F'S splitF).
rewrite (bigID (mem lin_pi)) /=.
rewrite (eq_bigr (fun _ => 1%N)) => [|i]; last by rewrite !inE; move/eqP->.
rewrite sum1_card nb_lin.
rewrite (eq_bigl (codom iphi)) => [|i]; last by rewrite inE -[~~ _]im_iphi.
rewrite (eq_bigr (fun _ => d ^ 2))%N => [|fi]; last first.
  by case/imageP=> i _ ->; rewrite deg_phi.
rewrite sum_nat_const card_image // card_ord oSpn (expnS p) -{3}[p]prednK //.
rewrite mulSn eqn_addl eqn_pmul2l; last by rewrite -ltnS prednK.
by rewrite -muln2 expn_mulr eqn_sqr.
Qed.

(* This is the corolloray of the above that is actually used in the proof of  *)
(* B & G, Theorem 2.5. It encapsulates the dependency on a socle of the       *)
(* regular representation.                                                    *)

Lemma faithful_repr_extraspecial : forall n F,
    #|S| = (p ^ n.*2.+1)%N -> group_splitting_field F S -> p \notin [char F] ->
    forall m (rS : mx_representation F S m) (U : 'M_m),
    mxsimple rS U -> rstab rS U == 1%g -> 
 \rank U = (p ^ n)%N
 /\ let rZ := subg_repr rS (center_sub S) in
    forall V : 'M_m, mxsimple rS V -> mx_iso rZ U V -> mx_iso rS U V.
Proof.
move=> n F oSpn splitF p'F m rS U simU ffulU.
set sZS := center_sub S; set rZ := subg_repr rS sZS.
suffices IH: forall V : 'M_m, mxsimple rS V -> mx_iso rZ U V ->
  [&& \rank U == (p ^ n)%N & mxsimple_iso rS U V].
- split=> [|/= V simV isoUV].
    by case/andP: (IH U simU (mx_iso_refl _ _)); move/eqP.
  by case/andP: (IH V simV isoUV) => _; move/(mxsimple_isoP simU).
move=> V simV isoUV; have F'S: [char F]^'.-group S by exact: (pi_pnat pS).
wlog sS: / socleType (regular_repr F S) by exact: socle_exists.
have [[_ defS'] prZ] := esS.
have{prZ} ntZ: 'Z(S) :!=: 1%g by case: eqP prZ => // ->; rewrite cards1.
have [_ [iphi]] := representations_extraspecial oSpn splitF p'F sS.
set phi := fun i => _ => [] [inj_phi onto_phi _ phiZ dim_phi] _.
have [modU nzU _]:= simU; pose rU := submod_repr modU.
have nlinU: \rank U > 1.
  rewrite ltn_neqAle lt0n mxrank_eq0 nzU andbT eq_sym; apply/eqP.
  move/(rker_linear rU); apply/negP; rewrite /rker rstab_submod.
  by rewrite (eqmx_rstab _ (val_submod1 _)) (eqP ffulU) defS' subG1.
have irrU: mx_irreducible rU by exact/submod_mx_irr.
have rsimU := rsim_regular_comp sS F'S irrU.
set iU := regular_comp sS rU in rsimU.
have [_ degU _ _]:= rsimU; rewrite -/(Wedderburn_degree iU) in degU.
have phiUP: iU \in codom iphi by rewrite onto_phi !inE -degU nlinU.
rewrite degU -(f_iinv phiUP) dim_phi eqxx /=; apply/(mxsimple_isoP simU).
have [modV _ _]:= simV; pose rV := submod_repr modV.
have irrV: mx_irreducible rV by exact/submod_mx_irr.
have rsimV := rsim_regular_comp sS F'S irrV.
set iV := regular_comp sS rV in rsimV.
have [_ degV _ _]:= rsimV; rewrite -/(Wedderburn_degree iV) in degV.
have phiVP: iV \in codom iphi.
  by rewrite onto_phi !inE -degV -(mxrank_iso isoUV).
pose jU := iinv phiUP; pose jV := iinv phiVP.
have [z Zz ntz]:= trivgPn _ ntZ.
have [|w prim_w phi_z] := phiZ z; first by rewrite 2!inE ntz.
suffices eqjUV: jU = jV.
  apply/(mx_rsim_iso modU modV); apply: mx_rsim_trans rsimU _.
  by rewrite -(f_iinv phiUP) -/jU eqjUV f_iinv; exact: mx_rsim_sym.
apply/eqP.
have rsimUV: mx_rsim (subg_repr (phi jU) sZS) (subg_repr (phi jV) sZS).
  have [bU _ bUfree bUhom] := mx_rsim_sym rsimU.
  have [bV _ bVfree bVhom] := rsimV.
  have modUZ := mxmodule_subg sZS modU; have modVZ := mxmodule_subg sZS modV.
  case/(mx_rsim_iso modUZ modVZ): isoUV => [bZ degZ bZfree bZhom].
  rewrite /phi !f_iinv; exists (bU *m bZ *m bV)=> [||x Zx].
  - by rewrite -[\rank _]degU degZ degV.
  - by rewrite /row_free !mxrankMfree.
  have Sx := subsetP sZS x Zx.
  by rewrite 2!mulmxA bUhom // -(mulmxA bU) bZhom // -4!mulmxA bVhom.
have{rsimUV} [B [B' _ homB]] := mx_rsim_def rsimUV.
move/eqP: (phi_z jU); rewrite [phi _ _]homB // phi_z.
rewrite -scalemx1 -scalemxAr -scalemxAl -(repr_mx1 (subg_repr (phi jV) sZS)).
rewrite -{B B'}homB // repr_mx1 scalemx1 eq_sym.
rewrite -/(Wedderburn_degree _) f_iinv -degU -(ltn_predK nlinU).
rewrite (inj_eq (fieldM_inj (@scalar_mxRM _ _))) (eq_expr_mod_order prim_w).
suffices modIp': forall j : 'I_p.-1, (j.+1 %% p = j.+1)%N by rewrite !modIp'.
by case: p p_pr => // p' _ [j ltj]; exact: modn_small.
Qed.

End StructureCorollaries.

End Extraspecial.

(* Lemmas for rfix_mx in mxrepresentation should be generalised to handle *)
(* subgroups.                                                             *)
Lemma rfix_submod : forall F gT (G : {group gT}) n,
    forall (rG : mx_representation F G n) (U : 'M_n) (modU : mxmodule rG U),
    forall (H : {group gT}) (sHG : H \subset G),
  (rfix_mx (submod_repr modU) H :=: in_submod U (U :&: rfix_mx rG H))%MS.
Proof.
move=> F gT G n rG U modU.
move=> H; move/subsetP=> sHG; apply/eqmxP; apply/andP; split; last first.
  apply/rfix_mxP=> x Hx; rewrite -in_submodJ ?capmxSl ?sHG //.
  by rewrite (rfix_mxP H _) ?capmxSr.
rewrite -[rfix_mx _ H]val_submodK submxMr // sub_capmx val_submodP.
by apply/rfix_mxP=> x Gx; rewrite -(val_submodJ modU) ?sHG // (rfix_mxP H _).
Qed.

(* This should slot in just after the definition of gring_proj.      *)
Lemma regular_repr_faithful : forall F gT (G : {group gT}),
  mx_repr_faithful (regular_repr F G).
Proof.
move=> F gT G; apply/subsetP=> x; case/setIdP=> Gx; rewrite mul1mx inE.
move/eqP; move/(congr1 (gring_proj 1%g)).
rewrite -(repr_mx1 (regular_repr F G)) !gring_projE ?group1 // eqxx eq_sym.
by case: (x == _) => //; move/eqP; rewrite eq_sym oner_eq0.
Qed.

Section MoreCenter.

Open Scope group_scope.

Lemma mulg_center_coprime_cent : forall gT (G H : {group gT}),
  coprime #|G| #|H| -> 'Z(G) * 'C_H(G) = 'C_(G * H)(G).
Proof.
move=> gT G H coGH; apply/setP=> xy; apply/imset2P/setIP=> [[x y] | []].
  by case/setIP=> Gx cGx; case/setIP=> Hy cGy ->; rewrite mem_mulg ?groupM.
case/imset2P=> x y Gx Hy ->{xy} cGxy.
suffices cGx: x \in 'C(G).
  by exists x y => //; apply/setIP; rewrite // -(groupMl _ cGx).
rewrite -[x](expgnK (coprime_dvdr (order_dvdG Hy) coGH)) // groupX //.
rewrite -[(x ^+ _)%g]mulg1 -(expg_order y).
elim: #[y] => [|k IHk]; first by rewrite mulg1 group1.
by rewrite expgS expgSr mulgA -(mulgA x) -(centP IHk) // -mulgA groupM.
Qed.

Lemma mulg_coprime_cent_center : forall gT (G H : {group gT}),
  coprime #|G| #|H| -> 'C_G(H) * 'Z(H) = 'C_(G * H)(H).
Proof.
move=> gT G H; rewrite coprime_sym => coHG; apply: invg_inj.
by rewrite invIg !invMg !invGid mulg_center_coprime_cent.
Qed.

End MoreCenter.

Lemma sum_leqif : forall (I : finType) (P C : pred I) (E1 E2 : I -> nat),
  (forall i, P i -> E1 i <= E2 i ?= iff C i) ->
  \sum_(i | P i) E1 i <= \sum_(i | P i) E2 i ?= iff (forallb i, P i ==> C i).
Proof.
move=> I P C E1 E2 leE12; rewrite -big_andE.
elim: (index_enum _) => [|i r IHr]; first by rewrite !big_nil.
rewrite !big_cons; case Pi: (P i) => //=.
by apply: leqif_add; first exact: leE12.
Qed.

Lemma sum_eq0 : forall (I : finType) (P : pred I) (E : I -> nat),
  (\sum_(i | P i) E i == 0)%N = (forallb i, P i ==> (E i == 0))%N.
Proof.
by move=> I P E; rewrite eq_sym -(@sum_leqif I P _ (fun _ => 0%N) E) ?big1_eq.
Qed.

Lemma classG_eq1 : forall gT x (G : {group gT}), (x ^: G == 1)%g = (x == 1)%g.
Proof.
move=> gT x G; apply/eqP/eqP=> [xG1 | ->]; last exact: class1G.
by have:= class_refl G x; rewrite xG1; move/set1P.
Qed.

Import poly hall.
(* This is B & G, Theorem 2.5, used in 3.4 and 15.7.                          *)
Theorem repr_extraspecial_prime_sdprod_cycle :
    forall p n gT (G P H : {group gT}),
    p.-group P -> extra_special P -> P ><| H = G -> cyclic H ->
    let h := #|H| in #|P| = (p ^ n.*2.+1)%N -> coprime p h ->
    {in H^#, forall x, 'C_P[x] = 'Z(P)} ->
  (h %| p ^ n + 1)%N || (h %| p ^ n - 1)%N
  /\ ((h != p ^ n + 1)%N -> forall F q (rG : mx_representation F G q),
      [char F]^'.-group G -> mx_repr_faithful rG -> rfix_mx rG H != 0).
Proof.
move=> p n gT G P H pP esP sdPH_G cycH h oPpn co_p_h primeHP.
set dvd_h_pn := _ || _; set neq_h_pn := h != _.
suffices IH: forall F q (rG : mx_representation F G q),
  [char F]^'.-group G -> mx_repr_faithful rG ->
  dvd_h_pn && (neq_h_pn ==> (rfix_mx rG H != 0)).
- split=> [|ne_h F q rG F'G ffulG]; last first.
    by case/andP: (IH F q rG F'G ffulG) => _; rewrite ne_h.
  pose r := pdiv #|G|.+1.
  have r_pr: prime r by rewrite pdiv_prime // ltnS cardG_gt0.
  have F'G: [char 'F_r]^'.-group G.
    rewrite /pgroup (eq_pnat _ (eq_negn (charf_eq (char_Fp r_pr)))).
    rewrite p'natE // -prime_coprime // (coprime_dvdl (pdiv_dvd _)) //.
    by rewrite /coprime -addn1 gcdnC gcdn_addl gcdn1.
  by case/andP: (IH _ _ _ F'G (regular_repr_faithful _ _)).
move=> F q rG F'G ffulG.
without loss closF: F rG F'G ffulG / group_closure_field F gT.
  move=> IH; apply: (@group_closure_field_exists gT F) => [[Fs clFs [f fM]]].
  rewrite -(map_mx_eq0 fM) (map_rfix_mx fM) {}IH //.
    by rewrite /pgroup (eq_pnat _ (eq_negn (fieldM_char fM))).
  by rewrite (map_mx_repr_faithful fM).
have p_pr := extraspecial_prime pP esP; have p_gt1 := prime_gt1 p_pr.
have oZp := card_center_extraspecial pP esP; have[_ prZ] := esP.
case/sdprodP: sdPH_G => _ defG nPH tiPH.
have [sPG sHG]: P \subset G /\ H \subset G.
  by apply/andP; rewrite -mulG_subG defG.
have nsPG: P <| G by rewrite /normal sPG -defG mul_subG ?normG.
have coPH: coprime #|P| #|H| by rewrite oPpn coprime_pexpl.
have nsZG: 'Z(P) <| G := char_normal_trans (center_char _) nsPG.
have defCP: 'C_G(P) = 'Z(P).
  apply/eqP; rewrite eqEsubset andbC setSI //=.
  rewrite -defG -mulg_center_coprime_cent // mul_subG // -(setD1K (group1 H)).
  apply/subsetP=> x; case/setIP; case/setU1P=> [-> // | H'x].
  rewrite -sub_cent1; move/setIidPl; rewrite primeHP // => defP.
  by have:= min_card_extraspecial pP esP; rewrite -defP oZp (leq_exp2l 3 1).
have F'P: [char F]^'.-group P by exact: pgroupS sPG F'G.
have p'F: p \notin [char F] by rewrite /pgroup oPpn pnat_exp orbF pnatE in F'P.
have F'H: [char F]^'.-group H by exact: pgroupS sHG F'G.
wlog [irrG regZ]: q rG ffulG / mx_irreducible rG /\ rfix_mx rG 'Z(P) = 0.
  move=> IH; wlog [I W /= simW defV _]: / mxsemisimple rG 1%:M.
    exact: (mx_reducible_semisimple (mxmodule1 _) (mx_Maeshke rG F'G)).
  have [z Zz ntz]: exists2 z, z \in 'Z(P) & z != 1%g.
    by apply/trivgPn; rewrite -cardG_gt1 oZp prime_gt1.
  have Gz := subsetP sPG z (subsetP (center_sub P) z Zz).
  case: (pickP (fun i => z \notin rstab rG (W i))) => [i ffZ | z1]; last first.
    case/negP: ntz; rewrite -in_set1 (subsetP ffulG) // inE Gz /=.
    apply/eqP; move/eqmxP: defV; case/andP=> _; case/sub_sumsmxP=> w ->.
    rewrite mulmx_suml; apply: eq_bigr => i _.
    by move/negbFE: (z1 i); move/rstab_act=> -> //; rewrite submxMl.
  have [modW _ _] := simW i; pose rW := submod_repr modW.
  rewrite -(eqmx_rstab _ (val_submod1 (W i))) -(rstab_submod modW) in ffZ.
  have irrW: mx_irreducible rW by exact/submod_mx_irr.
  have regZ: rfix_mx rW 'Z(P)%g = 0.
    apply/eqP; apply: contraR ffZ; case/mx_irrP: irrW => _ minW; move/minW.
    rewrite normal_rfix_mx_module //= -sub1mx inE Gz /=.
    by move/implyP; move/rfix_mxP->.
  have ffulP: P :&: rker rW = 1%g.
    apply: (nil_TI_Z (pgroup_nil pP)).
      by rewrite /normal subsetIl normsI ?normG ?(subset_trans _ (rker_norm _)).
    rewrite /= setIC setIA (setIidPl (center_sub _)); apply: prime_TIg=> //.
    by apply: contra ffZ; move/subsetP->.
  have cPker: rker rW \subset 'C_G(P).
    rewrite subsetI rstab_sub (sameP commG1P trivgP) /= -ffulP subsetI.
    rewrite commg_subl commg_subr (subset_trans sPG) ?rker_norm //.
    by rewrite (subset_trans (rstab_sub _ _)) ?normal_norm.
  have ffulGW: mx_repr_faithful rW.
    move: cPker; rewrite defCP subsetI (sameP setIidPr eqP) eq_sym.
    by rewrite ffulP -subG1; case/andP.
  have [->] := andP (IH _ _ ffulGW (conj irrW regZ)); case: (neq_h_pn) => //.
  apply: contra; rewrite (eqmx_eq0 (rfix_submod modW sHG)); move/eqP->.
  by rewrite capmx0 linear0.
pose rP := subg_repr rG sPG; pose rH := subg_repr rG sHG.
wlog [M simM _]: / exists2 M, mxsimple rP M & (M <= 1%:M)%MS.
  by apply: (mxsimple_exists (mxmodule1 _)); last case irrG.
have{M simM} [irrP def_q]: mx_irreducible rP /\ q = (p ^ n)%N.
  have [modM nzM _]:= simM.
  have [] := faithful_repr_extraspecial _ _ oPpn _ _ simM => // [|<- isoM].
    apply/eqP; apply: (nil_TI_Z (pgroup_nil pP)).
      rewrite /= -(eqmx_rstab _ (val_submod1 M)) -(rstab_submod modM).
      exact: rker_normal.
    rewrite setIC prime_TIg //=; apply: contra nzM => cMZ.
    rewrite -submx0 -regZ; apply/rfix_mxP=> z; move/(subsetP cMZ)=> cMz.
    by rewrite (rstab_act cMz).
  suffices irrP: mx_irreducible rP.
    by split=> //; apply/eqP; rewrite eq_sym; case/mx_irrP: irrP => _; exact.
  apply: (@mx_irr_prime_index F _ G P _ M nsPG) => // [|x Gx].
    by rewrite -defG quotient_mulgr quotient_cyclic.
  rewrite (bool_irrelevance (normal_sub nsPG) sPG).
  apply: isoM; first exact: (@Clifford_simple _ _ _ _ nsPG).
  have cZx: x \in 'C_G('Z(P)).
    rewrite (setIidPl _) // -defG mulG_subG centsC subsetIr.
    rewrite -(setD1K (group1 H)) subUset sub1G /=.
    by apply/subsetP=> y H'y; rewrite -sub_cent1 -(primeHP y H'y) subsetIr.
  by have [f] := Clifford_iso nsZG rG M cZx; exists f.
pose E_P := enveloping_algebra_mx rP; have absP := closF P _ _ irrP.
have EPfull: (1%:M <= E_P)%MS by rewrite sub1mx; case/andP: absP.
pose Z := 'Z(P); have [sZP nZP] := andP (center_normal P : Z <| P).
have nHZ: H \subset 'N(Z) := subset_trans sHG (normal_norm nsZG).
pose clPqH := [set Zx ^: (H / Z) | Zx <- P / Z]%g.
pose b (ZxH : {set coset_of Z}) := repr (repr ZxH).
have Pb: forall ZxH, ZxH \in clPqH -> b ZxH \in P.
  move=> ZxH; case/imsetP=> Zx P_Zx ->{ZxH}.
  rewrite -(quotientGK (center_normal P)) /= -/Z inE repr_coset_norm /=.
  rewrite inE coset_reprK; apply: subsetP (mem_repr _ (class_refl _ _)).
  rewrite -class_support_set1l class_support_sub_norm ?sub1set //.
  by rewrite quotient_norms.
have notZb: forall ZxH, ZxH \in clPqH^# -> b ZxH \in P :\: Z.
  move=> ZxH; case/setD1P=> ntZxH P_ZxH; rewrite inE Pb // andbT.
  apply: contra ntZxH; move/coset_id; rewrite coset_reprK.
  case/imsetP: P_ZxH => Zx _ ->{ZxH} rC1.
  by rewrite -(class_transr (mem_repr _ (class_refl _ _))) rC1 class1G.
have card_clPqH: forall ZxH, ZxH \in clPqH^# -> #|ZxH| = #|H|.
  move=> ZxH; case/setD1P=> ntZxH P_ZxH.
  case/imsetP: P_ZxH ntZxH => Zx P_Zx ->{ZxH}; rewrite classG_eq1 => ntZx.
  rewrite -index_cent1 ['C__[_]](trivgP _).
    rewrite indexg1 card_quotient // -indexgI setICA setIA tiPH.
    by rewrite (setIidPl (sub1G _)) indexg1.
  apply/subsetP=> Zy; case/setIP; case/morphimP=> y Ny.
  rewrite -(setD1K (group1 H)).
  case/setU1P=> [-> | Hy] ->{Zy} cZxy; first by rewrite morph1 set11.
  have: Zx \in 'C_(P / Z)(<[y]> / Z).
    by rewrite inE P_Zx quotient_cycle // cent_cycle cent1C.
  case/idPn; rewrite -coprime_quotient_cent ?cycle_subG ?(pgroup_sol pP) //.
    by rewrite /= cent_cycle primeHP // trivg_quotient inE.
  by apply: coprimegS coPH; rewrite cycle_subG; case/setD1P: Hy.
pose B x := \matrix_(i < #|H|) mxvec (rP (x ^ enum_val i)%g).
have sumB: (\sum_(ZxH \in clPqH) <<B (b ZxH)>> :=: 1%:M)%MS.
  apply/eqmxP; rewrite submx1 (submx_trans EPfull) //.
  apply/row_subP=> ix; set x := enum_val ix; pose ZxH := coset Z x ^: (H / Z)%g.
  have Px: x \in P by [rewrite enum_valP]; have nZx := subsetP nZP _ Px.
  have P_ZxH: ZxH \in clPqH by apply: mem_imset; rewrite mem_quotient.
  have Pbx := Pb _ P_ZxH; have nZbx := subsetP nZP _ Pbx.
  rewrite rowK (sumsmx_sup ZxH) {P_ZxH}// genmxE -/x.
  have: coset Z x \in coset Z (b ZxH) ^: (H / Z)%g.
    by rewrite class_sym coset_reprK (mem_repr _ (class_refl _ _)).
  case/imsetP=> Zy; case/morphimP=> y Ny Hy ->{Zy}.
  rewrite -morphJ //; case/kercoset_rcoset; rewrite ?groupJ // => z Zz ->.
  have [Pz cPz] := setIP Zz; rewrite repr_mxM ?memJ_norm ?(subsetP nPH) //.
  have [a ->]: exists a, rP z = a%:M.
    apply/is_scalar_mxP; apply: (mx_abs_irr_cent_scalar absP).
    by apply/centgmxP=> t Pt; rewrite -!repr_mxM ?(centP cPz).
  rewrite mul_scalar_mx linearZ scalemx_sub //.
  by rewrite (eq_row_sub (gring_index H y)) // rowK gring_indexK.
have Bfree_if: forall ZxH,
  ZxH \in clPqH^# -> \rank <<B (b ZxH)>> <= #|ZxH| ?= iff row_free (B (b ZxH)).
- by move=> ZxH P_ZxH; rewrite genmxE card_clPqH // /leqif rank_leq_row.
have q_gt0: q > 0 by case/andP: absP.
have B1_if: \rank <<B (b 1%g)>> <= 1 ?= iff (<<B (b 1%g)>> == mxvec 1%:M)%MS.
  have r1: \rank (mxvec 1%:M : 'rV[F]_(q ^ 2)) = 1%N.
    by rewrite rank_rV mxvec_eq0 -mxrank_eq0 mxrank1 -lt0n q_gt0.
  rewrite -{1}r1; apply: mxrank_leqif_eq; rewrite genmxE.
  have ->: b 1%g = 1%g by rewrite /b repr_set1 repr_coset1.
  by apply/row_subP=> i; rewrite rowK conj1g repr_mx1.
have rankEP: \rank (1%:M : 'A[F]_q) = (\sum_(ZxH \in clPqH) #|ZxH|)%N.
  rewrite acts_sum_card_orbit ?astabsJ ?quotient_norms // card_quotient //.
  rewrite mxrank1 -divgS // -mulnn oPpn oZp expnS -muln2 expn_mulr -def_q.
  by rewrite mulKn // ltnW.
have cl1: 1%g \in clPqH by apply/imsetP; exists 1%g; rewrite ?group1 ?class1G.
have{B1_if Bfree_if}:= leqif_add B1_if (sum_leqif Bfree_if).
case/(leqif_trans (mxrank_sum_leqif _)) => _ /=.
rewrite -{1}(big_setD1 _ cl1) sumB {}rankEP (big_setD1 1%g) // cards1 eqxx.
move/esym; case/and3P=> dxB; move/eqmxP=> defB1; move/forall_inP=> /= Bfree.
have [yg defH] := cyclicP H cycH; pose g := rG yg.
have Hxg: yg \in H by [rewrite defH cycle_id]; have Gyg := subsetP sHG _ Hxg.
pose gE : 'A_q := lin_mx (mulmx (invmx g) \o mulmxr g).
pose yr := regular_repr F H yg.
have mulBg: forall x, x \in P -> B x *m gE = yr *m B x.
  move=> x; move/(subsetP sPG)=> Gx.
  apply/row_matrixP=> i; have Hi := enum_valP i; have Gi := subsetP sHG _ Hi.
  rewrite 2!row_mul !rowK mul_vec_lin /= -rowE rowK gring_indexK ?groupM //.
  by rewrite conjgM -repr_mxV // -!repr_mxM // ?(groupJ, groupM, groupV).
wlog sH: / socleType (regular_repr F H) by exact: socle_exists.
have linH: forall W : sH, \rank (socle_base W) = 1%N.
  exact: Wedderburn_degree_abelian (closF H) (cyclic_abelian cycH).
have rsH: forall W : sH, \rank W = 1%N.
  by move=> W; have W1 := linH W; rewrite linear_Wedderburn_comp.
wlog [w prim_w]: / {w : F | GRing_order h w}.
  exact: (splitting_cyclic_primitive_root cycH F'H (closF H)).
have card_sH: #|sH| = h.
  by rewrite Wedderburn_card // card_classes_abelian ?cyclic_abelian.
have [Wi Wi_yr]: exists Wi : 'I_h -> sH, forall i, Wi i *m yr = w ^+ i *m: Wi i.
  pose e_w (W : sH) (i: 'I_h) := W *m yr == w ^+ i *m: W.
  exists (fun i => odflt (principal_comp _) [pick W | e_w W i]) => i0.
  case: pickP => [W /=| noW]; [by rewrite /e_w; move/eqP | case: notF].
  have scalH: forall W : sH, {a | socle_repr W yg = a%:M}.
    move=> W; move: (socle_repr W); rewrite linH => rW.
    by exists (rW yg 0 0); rewrite -mx11_scalar.
  pose r i := sval (scalH i); pose rs := map r (enum sH).
  have inj_r: injective r.
    rewrite /r => i j; case: (scalH i) => a rHi; case: (scalH j) => e rHj /= ae.
    rewrite -(regular_comp_refl F'H i)  -(regular_comp_refl F'H j).
    apply: regular_comp_rsim=> //; move: rHj rHi; rewrite {a}ae.
    move: (socle_repr i) (socle_repr j); rewrite !linH => ri rj <- eqij.
    exists 1%:M; rewrite ?row_free_unit ?unitmx1 // => x; rewrite {1}defH.
    by case/cycleP=> k ->; rewrite mulmx1 mul1mx !repr_mxX // eqij.
  have sz_rs: size rs = h by rewrite size_map -cardE.
  have rh1: forall W, r W ^+ h = 1.
    rewrite /r => W; case: (scalH W) => z def_z /=.
    move: (socle_repr W) def_z; rewrite linH => rW def_z.
    apply: (fieldM_inj (@scalar_mxRM F 0)); rewrite (ringM_exp scalar_mxRM).
    by rewrite -def_z -repr_mxX // /h {2}defH expg_order repr_mx1.
  have [|W _ def_rW]:= mapP (_ : w ^+ i0 \in rs).
    have szPh: size ('X^h - 1 : {poly F}) = h.+1.
      rewrite size_addl ?size_polyXn // ltnS.
      by rewrite size_opp size_poly1 cardG_gt0.
    apply: contraFT (ltnn h) => rs_w; rewrite -{1}sz_rs -ltnS -szPh.
    rewrite -/(size (w ^+ i0 :: rs)) max_poly_roots -?size_poly_eq0 ?szPh //.
      apply/allP=> t; rewrite inE /root !horner_lin hornerXn subr_eq0.
      case/predU1P=> [-> |]; last by case/mapP=> i _ ->; rewrite rh1.
      by rewrite -exprn_mulr -(ring_order_dvd prim_w) dvdn_mull.
    by rewrite /= rs_w map_inj_uniq ?enum_uniq.
  rewrite -(noW W) /e_w def_rW /r; case: (scalH W) => a def_a /=.
  have sWW: (W <= socle_base W)%MS.
    by rewrite -linear_Wedderburn_comp //; exact: linH.
  rewrite -(in_submodK sWW) -(val_submodJ (socle_module W)) // def_a.
  by rewrite mul_mx_scalar linearZ.
pose E_ m := eigenspace gE (w ^+ m).
have dxE: mxdirect (\sum_(m < h) E_ m)%MS.
  apply: mxdirect_sum_eigenspace => m1 m2 _ _ eq_m12; apply/eqP.
  by move/eqP: eq_m12; rewrite (eq_expr_mod_order prim_w) !modn_small.
pose B2 ZxH i := <<Wi i *m B (b ZxH)>>%MS.
pose B1 i := (\sum_(ZxH \in clPqH^#) B2 ZxH i)%MS.
pose SB := (<<B (b 1%g)>> + \sum_i B1 i)%MS.
have sB1E: forall i, (B1 i <= E_ i)%MS.
  move=> i; apply/sumsmx_subP=> ZxH; case/setIdP=> _; rewrite genmxE => P_ZxH.
  by apply/eigenspaceP; rewrite -mulmxA mulBg ?Pb // mulmxA Wi_yr scalemxAl.
have defSB: (SB :=: 1%:M)%MS.
  apply/eqmxP; rewrite submx1 -sumB (big_setD1 _ cl1) addsmxS //=.
  apply/sumsmx_subP=> ZxH P_ZxH; rewrite genmxE -[B _]mul1mx.
  rewrite -(reducible_Socle1 sH (mx_Maeshke _ F'H)) /Socle.
  elim: (index_enum _) => [|W eW IHe]; first by rewrite big_nil mul0mx sub0mx.
  rewrite big_cons addsmxMr addsmx_sub {eW}IHe andbT.
  suffices [i defWi]: exists i, Wi i = W.
    by rewrite (sumsmx_sup i) // (sumsmx_sup ZxH) // genmxE submxMr // defWi.
  suffices Wi_onto: {subset sH <= codom Wi}.
    by case/imageP: (Wi_onto W isT) => i; exists i.
  suffices injWi: injective Wi.
    apply/subsetP; rewrite -(geq_leqif (subset_leqif_card _)) ?subset_predT //.
    by rewrite card_image // card_sH card_ord.
  move=> i j eqWij; apply/eqP; suffices: w ^+ i - w ^+ j == 0.
    by rewrite subr_eq0 (eq_expr_mod_order prim_w) !modn_small.
  apply: contraR (nz_socle (Wi i)) => nz_wij.
  rewrite -submx0 -(eqmx_scale _ nz_wij) scalemx_subl {2}eqWij.
  by rewrite -!Wi_yr eqWij subrr.
rewrite mxdirect_addsE /= in dxB; case/and3P: dxB => _ dxB dxB1.
have rankB1: forall i, \rank (B1 i) = #|clPqH^#|.
  move=> i; rewrite -sum1_card (mxdirectP _) /=.
    by apply: eq_bigr => ZxH P_ZxH; rewrite genmxE mxrankMfree ?Bfree.
  apply/mxdirect_sumsP=> ZxH P_ZxH.
  apply/eqP; rewrite -submx0 -{2}(mxdirect_sumsP dxB _ P_ZxH) capmxS //.
    by rewrite !genmxE submxMl.
  by apply/sumsmx_subP=> ZyH P_ZyH; rewrite (sumsmx_sup ZyH) // !genmxE submxMl.
have rankEi: forall i : 'I_h, i != 0%N :> nat -> \rank (E_ i) = #|clPqH^#|.
  move=> i i_gt0; apply/eqP; rewrite -(rankB1 i) (mxrank_leqif_sup _) ?sB1E //.
  rewrite -[E_ i]cap1mx -(cap_eqmx defSB (eqmx_refl _)) /SB.
  rewrite (bigD1 i) //= (addsmxC (B1 i)) addsmxA addsmxC -matrix_modl //.
  rewrite -(addsmx0 (q ^ 2) (B1 i)) addsmxS //.
  rewrite capmxC -{2}(mxdirect_sumsP dxE i) // capmxS //.
  rewrite addsmx_sub // (sumsmx_sup (Ordinal (cardG_gt0 H))) //; last first.
  - rewrite defB1; apply/eigenspaceP; rewrite mul_vec_lin scale1mx /=.
    by rewrite mul1mx mulVmx ?repr_mx_unit.
  - by rewrite eq_sym.
  by apply/sumsmx_subP=> j ne_ji; rewrite (sumsmx_sup j).
have rankE0: forall i : 'I_h, i == 0%N :> nat -> \rank (E_ i) = #|clPqH^#|.+1.
  move=> i i_eq0; rewrite -[E_ i]cap1mx -(cap_eqmx defSB (eqmx_refl _)) /SB.
  rewrite (bigD1 i) // addsmxA -matrix_modl; last first.
    rewrite addsmx_sub // sB1E andbT defB1; apply/eigenspaceP.
    by rewrite mul_vec_lin (eqP i_eq0) scale1mx /= mul1mx mulVmx ?repr_mx_unit.
  rewrite (((_ :&: _)%MS =P 0) _).
    rewrite addsmx0 mxrank_disjoint_sum /=.
      by rewrite defB1 rank_rV rankB1 mxvec_eq0 -mxrank_eq0 mxrank1 -lt0n q_gt0.
    apply/eqP; rewrite -submx0 -(eqP dxB1) capmxS //.
    apply/sumsmx_subP=> ZxH P_ZxH.
    by rewrite (sumsmx_sup ZxH) // !genmxE ?submxMl.
  rewrite -submx0 capmxC /= -{2}(mxdirect_sumsP dxE i) // capmxS //.
  by apply/sumsmx_subP=> j ne_ji; rewrite (sumsmx_sup j).
have{rankE0 rankEi rankB1 dxB dxB1 defSB sB1E B1 B2 dxE SB}: forall m,
  m != 0 %[mod h] -> \rank (E_ 0%N) = (\rank (E_ m)).+1.
- move=> m nz_m; rewrite (rankE0 (Ordinal (cardG_gt0 H))) //.
  rewrite /E_ -(expr_mod_order prim_w); rewrite mod0n in nz_m.
  have lt_m: m %% h < h by rewrite ltn_mod ?cardG_gt0.
  by rewrite (rankEi (Ordinal lt_m)).
rewrite {sH linH rsH card_sH Wi Wi_yr}/E_ {mulBg}/gE.
clear E_P absP EPfull clPqH b Pb notZb card_clPqH B sumB cl1 defB1 Bfree.
clear ffulG irrG rP rH irrP regZ yr.
have: q > 1.
  rewrite def_q (ltn_exp2l 0) // lt0n.
  apply: contraL (min_card_extraspecial pP esP).
  by rewrite oPpn; move/eqP->; rewrite leq_exp2l.
rewrite {}/dvd_h_pn {}/neq_h_pn -{n oPpn}def_q subn1 addn1 /=.
case: q q_gt0 => // q' _ in rG g * => q_gt1 rankE.
have gh1: g ^+ h = 1 by rewrite -repr_mxX // /h defH expg_order repr_mx1.
apply/andP; split.
  have [i [n' [[] _]]]:= rank_eigenspaces_quasi_homocyclic gh1 prim_w rankE.
    by move/eqnP->; rewrite orbC dvdn_mulr.
  by rewrite /eq_addn_sign /=; move/eqP->; rewrite dvdn_mulr.
apply/implyP; apply: contra => regH.
have [|-> //]:= rank_eigenspaces_free_quasi_homocyclic gh1 prim_w rankE q_gt1.
apply/eqP; rewrite mxrank_eq0 -submx0 -(eqP regH).
apply/rV_subP=> v; move/eigenspaceP; rewrite scale1mx => cvg.
apply/rfix_mxP=> y Hy; apply: rstab_act (submx_refl v); apply: subsetP y Hy.
by rewrite defH cycle_subG !inE Gyg /= cvg.
Qed.

(* This is the main part of B & G, Theorem 2.6; it implies 2.6(a) and most of *)
(* 2.6(b).                                                                    *)
Lemma der1_odd_GL2_charf : forall F gT (G : {group gT}),
   forall rG : mx_representation F G 2,
 odd #|G| -> mx_repr_faithful rG -> [char F].-group G^`(1)%g.
Proof.
move=> F gT G.
elim: {G}_.+1 {-2}G (ltnSn #|G|) => // m IHm G le_g_m rG oddG ffG.
apply/pgroupP=> p p_pr pG'; rewrite !inE p_pr /=; apply/idPn=> p_nz.
have [P sylP] := Sylow_exists p G.
have nPG: G \subset 'N(P).
  apply/idPn=> pNG; pose N := 'N_G(P); have sNG: N \subset G := subsetIl _ _.
  have{IHm pNG} p'N': [char F].-group N^`(1)%g.
  apply: IHm (subg_repr_faithful sNG ffG); last exact: oddSg oddG.
    rewrite -ltnS (leq_trans _ le_g_m) // ltnS proper_card //.
    by rewrite /proper sNG subsetI subxx.
  have{p'N'} tiPN': P :&: N^`(1)%g = 1%g.
    rewrite coprime_TIg ?(pnat_coprime (pHall_pgroup sylP)) //= -/N.
    apply: sub_in_pnat p'N' => q _; apply: contraL; move/eqnP->.
    by rewrite !inE p_pr.
    have sPN: P \subset N by rewrite subsetI normG (pHall_sub sylP).
  have{tiPN'} cPN: N \subset 'C(P).
    rewrite (sameP commG1P trivgP) -tiPN' subsetI commgS //.
    by rewrite commg_subr subsetIr.
  case/sdprodP: (Burnside_normal_complement sylP cPN) => _ /=.
  set K := 'O_p^'(G) => defG nKP _.
  have nKG: G \subset 'N(K) by rewrite normal_norm ?pcore_normal.
  suffices p'G': p^'.-group G^`(1)%g by case/eqnP: (pgroupP p'G' p p_pr pG').
  apply: pgroupS (pcore_pgroup p^' G); rewrite -quotient_cents2 //= -/K.
  by rewrite -defG quotient_mulgr /= -/K quotient_cents ?(subset_trans sPN).
pose Q := G^`(1)%g :&: P; have sQG: Q \subset G by rewrite subIset ?der_subS.
have nQG: G \subset 'N(Q) by rewrite normsI // normal_norm ?der_normalS.
have pQ: (p %| #|Q|)%N.
  have sylQ: p.-Sylow(G^`(1)%g) Q by apply: pSylow_normalI (der_normalS _ _) _.
  apply: contraLR pG'; rewrite -!p'natE // (card_Hall sylQ) -!partn_eq1 //.
  by rewrite part_pnat_id ?part_pnat.
have{IHm} abelQ: abelian Q.
  apply/commG1P; apply/eqP; apply/idPn => ntQ'.
  have{IHm} p'Q': [char F].-group Q^`(1)%g.
    apply: IHm (subg_repr_faithful sQG ffG); last exact: oddSg oddG.
    rewrite -ltnS (leq_trans _ le_g_m) // ltnS proper_card //.
    rewrite /proper sQG subsetI //= andbC subEproper.
    case: eqP => [-> /= | _]; last by rewrite /proper (pHall_sub sylP) andbF.
    have: nilpotent P by rewrite (pgroup_nil (pHall_pgroup sylP)).
    move/forallP; move/(_ P); apply: contraL; rewrite subsetI subxx => -> /=.
    apply: contra ntQ'; rewrite /Q; move/eqP=> ->.
    by rewrite (setIidPr _) ?sub1G // commG1.
  case/eqP: ntQ';  have{p'Q'}: P :&: Q^`(1)%g = 1%g.
    rewrite coprime_TIg ?(pnat_coprime (pHall_pgroup sylP)) //= -/Q.
    apply: sub_in_pnat p'Q' => q _; apply: contraL; move/eqnP->.
    by rewrite !inE p_pr.
  by rewrite (setIidPr _) // comm_subG ?subsetIr.
wlog [U]: F p_nz rG ffG / mxnonsimple (subg_repr rG sQG) 1%:M.
  move=> IH_F; pose rQ := subg_repr rG sQG.
  have irrQ: mx_irreducible rQ.
    apply/mxsimpleP; rewrite mxmodule1 nonzero1r; split=> //.
    exact: IH_F ffG.
  case scalQ: (Q \subset [pred x | is_scalar_mx (rG x)]).
    suffices: row_full (pid_mx 1 : 'M[F]_2) by rewrite /row_full rank_pid_mx. 
    case/mx_irrP: irrQ => _; apply; last by rewrite -mxrank_eq0 rank_pid_mx.
    apply/mxmoduleP=> x; move/(subsetP scalQ); case/is_scalar_mxP=> a ->.
    by rewrite scalar_mxC submxMl.
  case/subsetPn: scalQ => x Qx.
  rewrite !inE -mxminpoly_linear_is_scalar -ltnNge => non_scal_rx.
  have cQrx: (centgmx rQ (rG x)).
    by apply/centgmxP=> y Qy; rewrite -!(repr_mxM rQ) // (centsP abelQ).
  have:= MatrixGenField.non_linear_gen_reducible irrQ cQrx non_scal_rx.
  have fRM := MatrixGenField.genRM irrQ cQrx.
  apply: IH_F (map_repr fRM rG) _; last by rewrite map_mx_repr_faithful.
  by rewrite -(ringM_nat fRM) fieldM_eq0.
rewrite -mxrank_eq0 -lt0n mxrank1 -eqn_leq eq_sym; case/and3P=> Umod _ Uscal.
have [|V Vmod sumUV dxUV] := mx_Maeshke _ _ Umod (submx1 U).
  have: p.-group Q by apply: pgroupS (pHall_pgroup sylP); rewrite subsetIr.
  by apply: sub_in_pnat=> q _; move/eqnP->; rewrite !inE p_pr.
have [u defU]: exists u : 'rV_2, (u :=: U)%MS.
  by move: (row_base U) (eq_row_base U); rewrite (eqP Uscal) => u; exists u.
have{dxUV Uscal} [v defV]: exists v : 'rV_2, (v :=: V)%MS.
  move/mxdirectP: dxUV; rewrite /= (eqP Uscal) sumUV mxrank1 => [[Vscal]].
  by move: (row_base V) (eq_row_base V); rewrite -Vscal => v; exists v.
pose B : 'M_(1 + 1) := col_mx u v; have{sumUV} uB: B \in unitmx.
  rewrite -row_full_unit /row_full eqn_leq rank_leq_row {1}addn1.
  by rewrite -addsmxE -(mxrank1 F 2) -sumUV mxrankS // addsmxS ?defU ?defV.
pose Qfix (w : 'rV_2) := {in Q, forall y, w *m rG y <= w}%MS.
have{U defU Umod} u_fix: Qfix u.
  by move=> y Qy; rewrite /= (eqmxMr _ defU) defU (mxmoduleP Umod).
have{V defV Vmod} v_fix: Qfix v.
  by move=> y Qy; rewrite /= (eqmxMr _ defV) defV (mxmoduleP Vmod).
case/Cauchy: pQ => // x Qx oxp; have Gx := subsetP sQG x Qx.
case/submxP: (u_fix x Qx) => a def_ux.
case/submxP: (v_fix x Qx) => b def_vx.
have def_x: rG x = B^-1 *m block_mx a 0 0 b *m B.
  rewrite -mulmxA -[2]/(1 + 1)%N mul_block_col !mul0mx addr0 add0r.
  by rewrite -def_ux -def_vx -mul_col_mx mulKmx.
have ap1: a ^+ p = 1.
  suff: B^-1 *m block_mx (a ^+ p) 0 0 (b ^+ p) *m B = 1.
    move/(canRL (mulmxK uB)); move/(canRL (mulKVmx uB)); rewrite mul1mx.
    by rewrite mulmxV // -[2]/(1 + 1)%N scalar_mx_block; case/eq_block_mx.
  transitivity (rG x ^+ p); last first.
    by rewrite -(repr_mxX (subg_repr rG sQG)) // -oxp expg_order repr_mx1.
  elim: (p) => [|k IHk]; first by rewrite -scalar_mx_block mulmx1 mulVmx.
  rewrite !exprS -IHk def_x -!mulmxE !mulmxA mulmxK // -2!(mulmxA B^-1).
  by rewrite -[2]/(1 + 1)%N mulmx_block !mulmx0 !mul0mx !addr0 mulmxA add0r.
have ab1: a * b = 1.
  have: Q \subset <<[set y \in G | \det (rG y) == 1]>>.
  rewrite subIset // genS //; apply/subsetP=> yz; case/imset2P=> y z Gy Gz ->.
    rewrite inE !repr_mxM ?groupM ?groupV //= !detM (mulrCA _ (\det (rG y))). 
    rewrite -!det_mulmx -!repr_mxM ?groupM ?groupV //.
    by rewrite mulKg mulVg repr_mx1 det1.
  rewrite gen_set_id; last first.
  apply/group_setP; split=> [|y z].
      by rewrite inE group1 /= repr_mx1 det1.
    case/setIdP=> Gy y1; case/setIdP=> Gz z1; rewrite inE groupM ?repr_mxM //=.
    by rewrite detM (eqP y1) (eqP z1) mulr1.
  move/subsetP; move/(_ x Qx); case/setIdP=> _.
  rewrite def_x !detM mulrAC -!detM -mulrA mulKr // -!mulmxE.
  rewrite -[2]/(1 + 1)%N det_lblock // [a]mx11_scalar [b]mx11_scalar.
  by rewrite !det_scalar1 -scalar_mxM; move/eqP->.
have{ab1 ap1 def_x} ne_ab: a != b.
  apply/eqP=> defa; have defb: b = 1.
    rewrite -ap1 (divn_eq p 2) modn2.
    have ->: odd p by rewrite -oxp (oddSg _ oddG) // cycle_subG.
    by rewrite addn1 exprS mulnC exprn_mulr exprS {1 3}defa ab1 exp1rn mulr1.
  suff x1: x \in [1] by rewrite -oxp (set1P x1) order1 in p_pr.
  apply: (subsetP ffG); rewrite inE Gx def_x defa defb -scalar_mx_block mulmx1.
  by rewrite mul1mx mulVmx ?eqxx.
have{a b ne_ab def_ux def_vx} nx_uv: forall w : 'rV_2,
  (w *m rG x <= w -> w <= u \/ w <= v)%MS.
- move=> w; case/submxP=> c; have:= mulmxKV uB w.
  rewrite -[_ *m invmx B]hsubmxK [lsubmx _]mx11_scalar [rsubmx _]mx11_scalar.
  move: (_ 0) (_ 0) => dv du; rewrite mul_row_col !mul_scalar_mx => <-{w}.
  rewrite mulmx_addl -!scalemxAl def_ux def_vx mulmx_addr -!scalemxAr.
  rewrite !scalemxAl -!mul_row_col; move/(can_inj (mulmxK uB)).
  case/eq_row_mx => eqac eqbc; apply/orP.
  case: (eqVneq dv 0) => [-> | nz_dv].
    by rewrite scale0mx addr0 scalemx_sub.
  case: (eqVneq du 0) => [-> | nz_du].
    by rewrite orbC scale0mx add0r scalemx_sub.
  case/eqP: ne_ab; rewrite -[b]scale1mx -(mulVf nz_dv) -[a]scale1mx.
  by rewrite -(mulVf nz_du) -!scalemxA eqac eqbc !scalemxA !mulVf.
have{x Gx Qx oxp nx_uv} redG: forall y (A := rG y),
  y \in G -> (u *m A <= u /\ v *m A <= v)%MS.
- move=> y A Gy; have uA: row_free A by rewrite row_free_unit repr_mx_unit.
  have Ainj: forall w t : 'rV_2, (w *m A <= w -> t *m A <= w -> t *m A <= t)%MS.
    move=> w t; case/sub_rVP=> c ryww; case/sub_rVP=> d rytw.
    rewrite -(submxMfree _ _ uA) rytw -scalemxAl ryww scalemxA mulrC.
    by rewrite -scalemxA scalemx_sub.
  have{Qx nx_uv} nAx: forall w, Qfix w -> (w *m A <= u \/ w *m A <= v)%MS.
    move=> w nwQ; apply: nx_uv; rewrite -mulmxA -repr_mxM // conjgCV.
    rewrite repr_mxM ?groupJ ?groupV // mulmxA submxMr // nwQ // -mem_conjg.
    by rewrite (normsP nQG).
  have [uAu | uAv] := nAx _ u_fix; have [vAu | vAv] := nAx _ v_fix; eauto.
  have [k ->]: exists k, A = A ^+ k.*2.
    exists #[y].+1./2; rewrite -mul2n -divn2 mulnC divnK.
      by rewrite -repr_mxX // expgS expg_order mulg1.
    by rewrite dvdn2 negbK; apply: oddSg oddG; rewrite cycle_subG.
  elim: k => [|k [IHu IHv]]; first by rewrite !mulmx1.
  case/sub_rVP: uAv => c uAc; case/sub_rVP: vAu => d vAd.
  rewrite doubleS !exprS !mulmxA; do 2!rewrite uAc vAd -!scalemxAl.
  by rewrite !scalemx_sub.
suffices trivG': G^`(1)%g = 1%g.
  by rewrite /= trivG' cards1 gtnNdvd ?prime_gt1 in pG'.
apply/trivgP; apply: subset_trans ffG; rewrite gen_subG.
apply/subsetP=> yz; case/imset2P=> y z Gy Gz ->{yz}; rewrite inE groupR //=.
rewrite -(inj_eq (can_inj (mulKmx (repr_mx_unit rG (groupM Gz Gy))))).
rewrite mul1mx mulmx1 -repr_mxM ?(groupR, groupM) // -commgC !repr_mxM //.
rewrite -(inj_eq (can_inj (mulKmx uB))) !mulmxA !mul_col_mx.
case/redG: Gy; case/sub_rVP=> a uya; case/sub_rVP=> b vyb.
case/redG: Gz; case/sub_rVP=> c uzc; case/sub_rVP=> d vzd.
by do 2!rewrite uya vyb uzc vzd -?scalemxAl; rewrite !scalemxA mulrC (mulrC d).
Qed.

(* This is B & G, Theorem 2.6 (a) *)
Theorem charf'_GL2_abelian : forall F gT (G : {group gT}),
    forall rG : mx_representation F G 2,
  odd #|G| -> mx_repr_faithful rG -> [char F]^'.-group G -> abelian G.
Proof.
move=> F gT G rG oddG ffG char'G; apply/commG1P; apply/eqP.
rewrite trivg_card1 (pnat_1 _ (pgroupS _ char'G)) ?comm_subG //=.
exact: der1_odd_GL2_charf ffG.
Qed.

Import finalg.
(* This is B & G, Theorem 2.6 (b) *)
Theorem charf_GL2_der_subS_abelian_Sylow : forall p F gT (G : {group gT}),
    forall rG : mx_representation F G 2,
    odd #|G| -> mx_repr_faithful rG -> p \in [char F] ->
  exists P : {group gT}, [/\ p.-Sylow(G) P, abelian P & G^`(1)%g \subset P].
Proof.
move=> p F gT G rG oddG ffG charFp.
have{oddG} pG': p.-group G^`(1)%g.
  rewrite /pgroup -(eq_pnat _ (charf_eq charFp)).
  exact: der1_odd_GL2_charf ffG.
have{pG'} [P SylP sG'P]:= Sylow_superset (der_sub _ _) pG'.
exists P; split=> {sG'P}//; case/and3P: SylP => sPG pP _.
apply/commG1P; apply/trivgP; apply: subset_trans ffG; rewrite gen_subG.
apply/subsetP=> yz; case/imset2P=> y z Py Pz ->{yz}.
rewrite inE (subsetP sPG) ?groupR //=.
pose rP := subg_repr rG sPG; pose U := rfix_mx rP P.
rewrite -(inj_eq (can_inj (mulKmx (repr_mx_unit rP (groupM Pz Py))))).
rewrite mul1mx mulmx1 -repr_mxM ?(groupR, groupM) // -commgC !repr_mxM //.
have{pP} pP: [char F].-group P by rewrite /pgroup (eq_pnat _ (charf_eq charFp)).
have: U != 0 by exact: rfix_pgroup_char.
rewrite -mxrank_eq0 -lt0n 2!leq_eqVlt ltnNge rank_leq_row orbF orbC eq_sym.
case/orP=> [Ufull | Uscal].
  suff{y z Py Pz} rP1: forall y, y \in P -> rP y = 1%:M by rewrite !rP1 ?mulmx1.
  move=> y Py; apply/row_matrixP=> i.
  by rewrite rowE -row1 (rfix_mxP P _) ?submx_full.
have [u defU]: exists u : 'rV_2, (u :=: U)%MS.
  by move: (row_base U) (eq_row_base U); rewrite -(eqP Uscal) => u; exists u.
have fix_u: {in P, forall x, u *m rP x = u}.
  by move/eqmxP: defU; case/andP; move/rfix_mxP.
have [v defUc]: exists u : 'rV_2, (u :=: U^C)%MS.
  have UCscal: \rank U^C = 1%N by rewrite mxrank_compl -(eqP Uscal).
  by move: (row_base _)%MS (eq_row_base U^C)%MS; rewrite UCscal => v; exists v.
pose B := col_mx u v; have uB: B \in unitmx.
  rewrite -row_full_unit -sub1mx -(eqmxMfull _ (addsmx_compl_full U)).
  by rewrite mulmx1 -addsmxE addsmxS ?defU ?defUc.
have Umod: mxmodule rP U by exact: rfix_mx_module.
pose W := rfix_mx (factmod_repr Umod) P.
have ntW: W != 0. 
  apply: rfix_pgroup_char pP.
  rewrite eqmxMfull ?row_full_unit ?unitmx_inv ?row_ebase_unit //.
  by rewrite rank_copid_mx -(eqP Uscal).
have{ntW} Wfull: row_full W.
  by rewrite -col_leq_rank {1}mxrank_coker -(eqP Uscal) lt0n mxrank_eq0.
have svW: (in_factmod U v <= W)%MS by rewrite submx_full.
have fix_v: {in P, forall x, v *m rG x - v <= u}%MS.
  move=> x Px /=; rewrite -[v *m _](add_sub_fact_mod U) (in_factmodJ Umod) //.
  move/rfix_mxP: svW => -> //; rewrite in_factmodK ?defUc // addrK.
  by rewrite defU val_submodP.
have fixB: {in P, forall x, exists2 a, u *m rG x = u & v *m rG x = v + a *m: u}.
  move=> x Px; case/submxP: (fix_v x Px) => a def_vx.
  exists (a 0 0); first exact: fix_u.
  by rewrite addrC -mul_scalar_mx -mx11_scalar -def_vx subrK.
rewrite -(inj_eq (can_inj (mulKmx uB))) // !mulmxA !mul_col_mx.
case/fixB: Py => a uy vy; case/fixB: Pz => b uz vz.
by rewrite uy uz vy vz !mulmx_addl -!scalemxAl uy uz vy vz addrAC.
Qed.

(* This is B & G, Lemma 2.7. *)
Lemma regular_abelem2_on_abelem2 : forall p q gT (P Q : {group gT}),
  p.-abelem P -> q.-abelem Q -> 'r_p(P) = 2 ->'r_q(Q) = 2 ->
  Q \subset 'N(P) -> 'C_Q(P) = 1%g ->
  (q %| p.-1)%N
  /\ (exists2 a, a \in Q^# & exists r,
      [/\ {in P, forall x, x ^ a = x ^+ r}%g,
          r ^ q = 1 %[mod p] & r != 1 %[mod p]]).
Proof.
move=> p q gT P Q abelP abelQ; rewrite !p_rank_abelem // => logP logQ nPQ regQ.
have ntP: P :!=: 1%g by case: eqP logP => // ->; rewrite cards1 logn1.
have [p_pr _ _]:= pgroup_pdiv (abelem_pgroup abelP) ntP.
have ntQ: Q :!=: 1%g by case: eqP logQ => // ->; rewrite cards1 logn1.
have [q_pr _ _]:= pgroup_pdiv (abelem_pgroup abelQ) ntQ.
pose rQ := abelem_repr abelP ntP nPQ.
have [|P1 simP1 _] := MatrixFormula.dec_mxsimple_exists (mxmodule1 rQ).
  by rewrite oner_eq0.
have [modP1 nzP1 _] := simP1.
have ffulQ: mx_repr_faithful rQ by exact: abelem_repr_faithful.
have linP1: \rank P1 = 1%N.
  apply/eqP; have:= abelem_cyclic abelQ; rewrite logQ; apply: contraFT.
  rewrite neq_ltn ltnNge lt0n mxrank_eq0 nzP1 => P1full.
  have irrQ: mx_irreducible rQ.
    apply: mx_iso_simple simP1; apply: eqmx_iso; apply/eqmxP.
    by rewrite submx1 sub1mx -col_leq_rank {1}(dim_abelemE abelP ntP) logP.
  exact: mx_repr_faithful_irr_abelian_cyclic irrQ (abelem_abelian abelQ).
have ne_qp: q != p.
  move/implyP: (logn_quotient_cent_abelem nPQ abelP).
  by rewrite logP regQ indexg1 /=; case: eqP => // <-; rewrite logQ.
have redQ: mx_completely_reducible rQ 1%:M.
  apply: mx_Maeshke; apply: pi_pnat (abelem_pgroup abelQ) _.
  by rewrite inE /= (charf_eq (char_Fp p_pr)).
have [P2 modP2 sumP12 dxP12] := redQ _ modP1 (submx1 _).
have linP2: \rank P2 = 1%N.
  apply: (@addnI 1%N); rewrite -{1}linP1 -(mxdirectP dxP12) /= sumP12.
  by rewrite mxrank1 (dim_abelemE abelP ntP) logP.
pose lam (Pi : 'M(P)) b := (nz_row Pi *m rQ b *m pinvmx (nz_row Pi)) 0 0.
have rQ_lam: forall Pi b,
  mxmodule rQ Pi -> \rank Pi = 1%N -> b \in Q -> Pi *m rQ b = lam Pi b *m: Pi.
- rewrite /lam => Pi b modPi linPi Qb; set v := nz_row Pi; set a := _ 0.
  have nz_v: v != 0 by rewrite nz_row_eq0 -mxrank_eq0 linPi.
  have sPi_v: (Pi <= v)%MS.
    by rewrite -mxrank_leqif_sup ?nz_row_sub // rank_rV nz_v linPi.
  have [u defPi] := submxP sPi_v; rewrite {2}defPi scalemxAr -mul_scalar_mx.
  rewrite -mx11_scalar !(mulmxA u) -defPi mulmxKpV ?(submx_trans _ sPi_v) //.
  exact: (mxmoduleP modPi).
have lam_q: forall Pi b,
  mxmodule rQ Pi -> \rank Pi = 1%N -> b \in Q -> lam Pi b ^+ q = 1.
- move=> Pi b modPi linPi Qb; apply/eqP; rewrite eq_sym -subr_eq0.
  have: \rank Pi != 0%N by rewrite linPi.
  apply: contraR; move/eqmx_scale=> <-.
  rewrite mxrank_eq0 scalemx_subl subr_eq0 -mul_mx_scalar -(repr_mx1 rQ).
  have <-: (b ^+ q = 1)%g by case/and3P: abelQ => _ _; move/exponentP->.
  apply/eqP; rewrite repr_mxX //.
  elim: (q) => [|k IHk]; first by rewrite scale1mx mulmx1.
  by rewrite !exprS mulmxA rQ_lam // -scalemxAl IHk scalemxA.
pose f b := (lam P1 b, lam P2 b).
have inj_f: {in Q &, injective f}.
  move=> b c Qb Qc /= [eq_bc1 eq_bc2].
  apply/eqP; rewrite eq_mulgV1 -in_set1 (subsetP ffulQ) //.
  rewrite inE groupM ?repr_mxM ?groupV //=.
  have: (1%:M <= P1 + P2)%MS by rewrite sumP12.
  case/sub_addsmxP=> v2; case/submxP=> u1 def_v1; case/submxP=> u2 def_v2.
  rewrite -(subrK v2 1%:M) def_v1 def_v2 mulmx_addl -!mulmxA.
  rewrite {1}(mulmxA P1) {1}[P1 *m _]rQ_lam // eq_bc1 -rQ_lam // repr_mxK //.
  by rewrite {1}(mulmxA P2) {1}[P2 *m _]rQ_lam // eq_bc2 -rQ_lam // repr_mxK.
pose rs := [set x : 'F_p | x ^+ q == 1].
have s_fQ_rs: f @: Q \subset setX rs rs.
  apply/subsetP=> fb; case/imsetP=> b Qb ->{fb}.
  by rewrite !{1}inE /= !{1}lam_q ?eqxx.
have le_rs_q: #|rs| <= q ?= iff (#|rs| == q).
  have roots_rs: all (root ('X^q - 1)) (enum rs).
    by apply/allP=> x; rewrite mem_enum inE /root !horner_lin hornerXn subr_eq0.
  split=> //; have:= max_poly_roots _ roots_rs (enum_uniq _); move/implyP.
  rewrite -cardE -size_poly_eq0 size_addl size_polyXn //.
  by rewrite size_opp size_poly1 ltnS prime_gt0.
have:= subset_leqif_card s_fQ_rs.
rewrite card_in_imset // -(part_pnat_id (abelem_pgroup abelQ)) p_part logQ.
case/(leqif_trans (leqif_mul le_rs_q le_rs_q))=> _; move/esym.
rewrite cardsX eqxx andbb muln_eq0 orbb eqn0Ngt prime_gt0 //=.
case/andP=> rs_q; rewrite subEproper /proper {}s_fQ_rs andbF orbF.
move/eqP=> rs2_Q.
have: ~~(rs \subset [set (1 : 'F_p)]).
  apply: contraL (prime_gt1 q_pr); move/subset_leq_card.
  by rewrite cards1 (eqnP rs_q) leqNgt.
case/subsetPn => r rs_r; rewrite inE => ne_r_1.
have rq1: r ^+ q = 1 by apply/eqP; rewrite inE in rs_r.
split.
  have Ur: GRing.unit r by rewrite -(unitr_pexp _ (prime_gt0 q_pr)) rq1 unitr1.
  pose u : {unit 'F_p} := Sub r Ur; have:= order_dvdG (in_setT u).
  rewrite card_units_Zp ?pdiv_gt0 // {2}/pdiv primes_prime //=.
  rewrite (@phi_pfactor p 1) // muln1; apply: dvdn_trans.
  have: (u ^+ q == 1)%g.
    by rewrite -val_eqE unit_Zp_expgn -Zp_nat natr_exp natr_Zp rq1.
  case/primeP: q_pr => _ q_min; rewrite -order_dvdn; move/q_min.
  by rewrite order_eq1 -val_eqE (negPf ne_r_1) /=; move/eqnP->.
have: (r, r) \in f @: Q by rewrite -rs2_Q inE andbb.
case/imsetP=> a Qa [def_a1 def_a2].
have rQa: rQ a = r%:M.
  have: (1%:M <= P1 + P2)%MS by rewrite sumP12.
  case/sub_addsmxP=> v2; case/submxP=> u1 def_v1; case/submxP=> u2 def_v2.
  rewrite -scalemx1 -[rQ a]mul1mx -(subrK v2 1%:M) def_v1 def_v2.
  rewrite mulmx_addl -!mulmxA !rQ_lam // -def_a1 -def_a2.
  by rewrite -!scalemxAr -linearD.
exists a.
  rewrite !inE Qa andbT; apply: contra ne_r_1 => a1.
  rewrite (eqP a1) repr_mx1 in rQa.
  by rewrite (fieldM_inj scalar_mxRM rQa).
exists r; rewrite -!val_Fp_nat // natr_exp natr_Zp rq1.
split=> // x Px; apply: (@abelem_rV_inj _ _ _ abelP ntP); rewrite ?groupX //.
  by rewrite memJ_norm ?(subsetP nPQ).
by rewrite abelem_rV_X // -mul_mx_scalar natr_Zp -rQa -abelem_rV_J.
Qed.

End BGsection2.
