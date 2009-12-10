Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq div.
Require Import fintype bigops prime binomial finset ssralg.
Require Import groups morphisms normal automorphism commutators zmodp.
Require Import gprod cyclic center pgroups nilpotent sylow maximal.
Require Import matrix mxrepresentation BGsection1 BGsection2.

(******************************************************************************)
(* This file should contain the useful material in B & G, appendices A and B, *)
(* i.e., the proof of the p-stability properties and the ZJ-Theorem (or as it *)
(* were, the ZL-theorem.                                                      *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Open Local Scope ring_scope.
Import GroupScope GRing.Theory.

Section BGappendixA.

Implicit Type gT : finGroupType.
Implicit Type p : nat.

(* This is essentially B & G, Theorem A.4(c) (in Appendix A, not section 16!) *)
(* but without the spurrious ``generality'' of considering a group G in which *)
(* P is not normal, only to state a result that only concerns its normaliser. *)
(* This also gets rid of the 'O_p^'(G) * P <| G premise which clearly plays   *)
(* no part in the proof.                                                      *)
Lemma odd_cent_comm_normal_subset_pcore : forall gT p (G A P : {group gT}),
    odd #|G| -> solvable G ->
    p.-group P -> P <| G ->
    p.-group A -> A \subset G -> [~: P, A, A] = 1 ->
  A / 'C_G(P) \subset 'O_p(G / 'C_G(P)).
Proof.
move=> gT p; move: gT.
pose p_xp gT (E : {group gT}) x := p.-elt x && (x \in 'C([~: E, [set x]])).
suffices: forall gT (E : {group gT}) x y, let G := <<[set x; y]>> in
  [&& odd #|G|, p.-group E & G \subset 'N(E)] ->
  p_xp gT E x && p_xp gT E y -> p.-group (G / 'C(E)).
- move=> IH gT G A P oddG _ pP; case/andP=> _ nPG pA sAG cRA.
  apply/subsetP=> Cx; case/morphimP=> x Nx Ax ->{Cx}.
  have Gx := subsetP sAG x Ax.
  apply: Baer_Suzuki => [|Cy]; first exact: mem_quotient.
  case/morphimP=> y Ny Gy ->{Cy}; rewrite -morphJ // -!morphim_set1 ?groupJ //.
  rewrite -morphimU -morphim_gen ?subUset ?sub1set ?Nx ?groupJ //= -quotientE.
  set G1 := <<_>>.
  have sG1G: G1 \subset G by rewrite mulgen_subG ?sub1set ?groupJ ?Gx.
  rewrite /pgroup -(isog_card (second_isog _)); last first.
    by rewrite mulgen_subG !sub1set Nx groupJ.
  rewrite -setIA setICA (@setIidPr _ G _ _); last first.
    by rewrite mulgen_subG !sub1set Gx groupJ.
  rewrite (isog_card (second_isog _)) //; last first.
    by rewrite norms_cent // mulgen_subG !sub1set groupJ (subsetP nPG).
  apply: IH => //; first by rewrite pP (oddSg sG1G) ?(subset_trans sG1G).
  rewrite /p_xp -{2}(normsP nPG y Gy) -conjg_set1 -conjsRg centJ memJ_conjg.
  rewrite p_eltJ andbb (mem_p_elt pA) // -sub1set centsC (sameP commG1P trivgP).
  by rewrite -cRA !commgSS ?sub1set.
move=> gT E; move: {2}_.+1 (ltnSn #|E|) => n; elim: n => // n IHn in gT E *.
rewrite ltnS => leEn x y G; case/and3P=> oddG pE nEG.
case/and3P; case/andP => p_x cRx p_y cRy.
have [Gx Gy]: x \in G /\ y \in G.
  by apply/andP; rewrite -!sub1set -subUset subset_gen.
apply/idPn=> p'Gc; case/pgroupP: (p'Gc) => q q_pr qGc; apply/idPn => p'q.
have [Q sylQ] := Sylow_exists q [group of G].
have [sQG qQ]: Q \subset G /\ q.-group Q by case/and3P: sylQ.
have{qQ p'q} p'Q: p^'.-group Q by apply: sub_in_pnat qQ => q' _; move/eqnP->.
have{q q_pr sylQ qGc} ncEQ: ~~ (Q \subset 'C(E)).
  apply: contraL qGc => cEQ; rewrite -p'natE // -partn_eq1 //.
  have nCQ: Q \subset 'N('C(E)) by exact: subset_trans (normG _).
  have sylQc: q.-Sylow(G / 'C(E)) (Q / 'C(E)) by rewrite morphim_pSylow.
  by rewrite -(card_Hall sylQc) -trivg_card1 (sameP eqP trivgP) quotient_sub1.
have solE: solvable E := pgroup_sol pE.
have ntE: E :!=: 1 by apply: contra ncEQ; move/eqP->; rewrite cents1.
have{Q ncEQ p'Q sQG} minE_EG: minnormal E (E <*> G).
  apply/mingroupP; split=> [|D]; rewrite mulgen_subG ?ntE ?normG //.
  case/and3P=> ntD nDE nDG sDE; have nDGi := subsetP nDG.
  apply/eqP; rewrite eqEcard sDE leqNgt; apply: contra ncEQ => ltDE.
  have nDQ: Q \subset 'N(D) by rewrite (subset_trans sQG).
  have cDQ: Q \subset 'C(D).
    rewrite -quotient_sub1 ?norms_cent // ?[_ / _]card1_trivg //.
    apply: pnat_1 (morphim_pgroup _ p'Q); apply: pgroupS (quotientS _ sQG) _.
    apply: (IHn _ D (leq_trans ltDE leEn)); first by rewrite oddG (pgroupS sDE).
    rewrite /p_xp p_x p_y /=; apply/andP.
    by split; [move: cRx | move: cRy]; apply: subsetP; rewrite centS ?commSg.
  apply: (stable_factor_cent cDQ) solE; rewrite ?(pnat_coprime pE) //.
  apply/and3P; split; rewrite // -quotient_cents2 // centsC.
  rewrite -quotient_sub1 ?norms_cent ?quotient_norms ?(subset_trans sQG) //=.
  rewrite [(_ / _) / _]card1_trivg //=.
  apply: pnat_1 (morphim_pgroup _ (morphim_pgroup _ p'Q)).
  apply: pgroupS (quotientS _ (quotientS _ sQG)) _.
  have defGq: G / D = <<[set coset D x; coset D y]>>.
    by rewrite quotient_gen -1?gen_subG ?quotientU ?quotient_set1 ?nDGi.
  rewrite /= defGq IHn ?(leq_trans _ leEn) ?ltn_quotient // -?defGq.
    rewrite odd_2'nat -/(pgroup _ _) quotient_norms ?morphim_pgroup //.
    by rewrite /pgroup -odd_2'nat.
  rewrite /p_xp -!sub1set !morph_p_elt -?quotient_set1 ?nDGi //=.
  by rewrite -!quotientR ?quotient_cents ?sub1set ?nDGi.
have abelE: p.-abelem E.
  by apply/andP; case: (minnormal_solvable minE_EG _ solE).
have cEE: abelian E by case/andP: abelE; case/andP.
have{minE_EG} minE: minnormal E G.
  case/mingroupP: minE_EG => _ minE; apply/mingroupP; rewrite ntE.
  split=> // D ntD sDE; apply: minE => //; rewrite mulgen_subG cents_norm //.
  by rewrite centsC (subset_trans sDE).
have nCG: G \subset 'N('C_G(E)) by rewrite normsI ?normG ?norms_cent.
suffices{p'Gc} pG'c: p.-group (G / 'C_G(E))^`(1).
  have [Pc sylPc sGc'Pc]:= Sylow_superset (der_sub _ _) pG'c.
  have nsPc: Pc <| G / 'C_G(E) by rewrite sub_der1_normal ?(pHall_sub sylPc).
  case/negP: p'Gc; rewrite /pgroup -(isog_card (second_isog _)) ?norms_cent //.
  rewrite setIC; apply: pgroupS (pHall_pgroup sylPc) => /=.
  rewrite sub_quotient_pre // mulgen_subG !sub1set !(subsetP nCG, inE) //=.
  by rewrite !(mem_normal_Hall sylPc) ?mem_quotient ?morph_p_elt ?(subsetP nCG).
have defC := ker_abelem_repr abelE ntE nEG; rewrite /= -/G in defC.
set rG := abelem_repr _ _ _ in defC; set r := abelem_mx _ _ _ in rG defC.
case ncxy: (r x *m r y == r y *m r x).
  have Cxy: [~ x, y] \in 'C_G(E).
    rewrite -defC inE groupR //= !rG ?groupM ?groupV //.
    by rewrite (eqP ncxy) -!rG ?groupM ?groupV // mulKg mulVg rG.
  rewrite [_^`(1)](commG1P _) ?pgroup1 //= quotient_gen -gen_subG //= -/G.
  rewrite !gen_subG centsC gen_subG quotient_cents2r ?gen_subG //= -/G. 
  rewrite /commg_set imset2Ul !imset2_set1l !imsetU !imset_set1.
  by rewrite !subUset andbC !sub1set !commgg group1 /= -invg_comm groupV Cxy.
pose Ax : 'M(E) := r x - 1; pose Ay : 'M(E) := r y - 1.
have Ax2: Ax *m Ax = 0.
  apply/row_matrixP=> i; apply/eqP; rewrite row_mul mulmx_subr mulmx1.
  rewrite row0 subr_eq0 -(inj_eq (@rVabelem_inj _ _ _ abelE ntE)).
  rewrite rVabelemJ // conjgE -(centP cRx) ?mulKg //.
  rewrite linear_sub /= addrC row1 rowE rVabelemD rVabelemN rVabelemJ //=.
  by rewrite mem_commg ?set11 ?mem_rVabelem.
have Ay2: Ay *m Ay = 0.
  apply/row_matrixP=> i; apply/eqP; rewrite row_mul mulmx_subr mulmx1.
  rewrite row0 subr_eq0 -(inj_eq (@rVabelem_inj _ _ _ abelE ntE)).
  rewrite rVabelemJ // conjgE -(centP cRy) ?mulKg //.
  rewrite linear_sub /= addrC row1 rowE rVabelemD rVabelemN rVabelemJ //=.
  by rewrite mem_commg ?set11 ?mem_rVabelem.
pose A := Ax *m Ay + Ay *m Ax.
have cAG: mxcentg r [group of G] A.
  suff cAG: G \subset <<[set z \in G | A *m r z == r z *m A]>>.
    apply/mxcentgP=> z; move/(subsetP cAG).
    rewrite gen_set_id; first by case/setIdP=> _; move/eqP.
    apply/group_setP; rewrite inE group1 rG mulmx1 mul1mx; split=> {z}//= z t.
    case/setIdP=> Gz; move/eqP=> cAz; case/setIdP=> Gt; move/eqP=> cAt.
    by rewrite inE groupM //= rG // mulmxA cAz -!mulmxA cAt.
  rewrite genS // subUset !sub1set !inE Gx Gy /=; apply/andP.
  rewrite -[r x](subrK 1%R) -[r y](subrK 1%R) -/Ax -/Ay.
  rewrite 2!(mulmx_addl _ 1 A) 2!(mulmx_addr A _ 1) !mulmx1 !mul1mx.
  rewrite !(inj_eq (@addIr _ A)) ![_ *m A]mulmx_addr ![A *m _]mulmx_addl.
  by rewrite -!mulmxA Ax2 Ay2 !mulmx0 !mulmxA Ax2 Ay2 !mul0mx !addr0 !add0r.
have irrG: mx_irreducible r [group of G] by exact/abelem_mx_irrP.
pose rAG := MatrixGenField.gen_repr rG irrG cAG.
set rA := MatrixGenField.gen_mx _ _ _ in rAG.
pose inFA := MatrixGenField.in_gen rG irrG cAG.
pose valFA := @MatrixGenField.val_gen _ _ _ _ _ _ rG irrG cAG.
set dA := MatrixGenField.gen_dim A in rA rAG inFA valFA.
rewrite -(ker_abelem_repr abelE ntE nEG) -/rG.
rewrite -(MatrixGenField.ker_gen_mx rG irrG cAG) -/rAG.
have dA_gt0: dA > 0.
  have: 'dim E > 0 by [].
  by rewrite -(MatrixGenField.gen_dim_factor rG irrG cAG) muln_gt0; case/andP.
have irrAG: mx_irreducible rA [group of G].
  apply/mx_irrP; split=> // U Umod nzU.
  pose fU v : 'rV(E) := valFA _ (inFA _ v *m cokermx U).
  have fUlin : linear fU.
    move=> a u v; rewrite /fU /inFA MatrixGenField.in_genD.
    rewrite  MatrixGenField.in_genZ mulmx_addl -scalemxAl -/inFA.
    rewrite /valFA MatrixGenField.val_genD MatrixGenField.val_genZ -/valFA.
    by rewrite MatrixGenField.genK mul_mx_scalar.
  pose Ur := kermx (lin1_mx (LinearFun fUlin)).
  have subUr: forall m B, (valFA m B <= Ur)%MR = (B <= U)%MR.
    move=> b M; apply/row_subP/row_subP=> sBU i; move/(_ i): sBU.
      move/subsetmx_kerP; rewrite mul_rV_lin1; move/(congr1 (inFA _)); move/eqP.
      rewrite -MatrixGenField.val_gen_row /= /fU /inFA !MatrixGenField.val_genK.
      by rewrite MatrixGenField.in_gen0; unlock subsetmx.
    unlock {1}subsetmx; move/eqP=> sBU; apply/subsetmx_kerP.
    rewrite mul_rV_lin1 /= /fU /inFA MatrixGenField.in_gen_row.
    by rewrite MatrixGenField.val_genK sBU /valFA MatrixGenField.val_gen0.
  apply/eqP; rewrite -[_ == _]subset1mx -subUr subsetmx_full /row_full //.
  case/mx_irrP: (irrG) => _ -> //; last first.
    apply: contra nzU; move/rowV0P=> Ur0; apply/rowV0P=> v.
    rewrite -subUr; move/Ur0; move/(congr1 (inFA _)).
    by rewrite /inFA MatrixGenField.in_gen0 MatrixGenField.val_genK.
  apply/submodmxP=> z Gz; rewrite -{1}[Ur](MatrixGenField.in_genK rG irrG cAG).
  rewrite -MatrixGenField.val_genJ // subUr -/rA.
  apply: subsetmx_trans (submodmxP _ _ _ Umod z Gz).
  by rewrite subsetmxMr // -subUr /valFA MatrixGenField.in_genK.
have: dA <= 2.
  case Ax0: (Ax == 0).
    rewrite subr_eq0 in Ax0; case/eqP: ncxy.
    by rewrite (eqP Ax0) mulmx1 mul1mx.
  case/rowV0Pn: Ax0 => v; case/subsetmxP => u def_v nzv.
  pose U := col_mx v (v *m Ay); pose UA := <<inFA _ U>>%MR.
  have Umod: submodmx rA [group of G] UA.
    pose N_UA := [set z \in G | UA *m rA z <= UA]%MR.
    suff: G \subset <<N_UA>>.
      rewrite gen_set_id.
        by move/subsetP=> Umod; apply/submodmxP=> z; move/Umod; case/setIdP.
      apply/group_setP; rewrite inE group1 rAG mulmx1; split=> //= z t.
      rewrite !inE {N_UA irrAG}; move: rA rAG UA => rA rAG UA.
      case/andP=> Gz sUzU; case/andP=> Gt sUtU; rewrite andbC groupM ?rAG //.
      by rewrite mulmxA (subsetmx_trans (subsetmxMr _ sUzU)).
    apply: genS.
    have: [set z \in G | U *m r z <= U :+: v *m A]%MR \subset N_UA.
      apply/subsetP=> z; case/setIdP=> Gz; case/sub_gsummxP=> /= UzA nUz nUzA.
      rewrite inE Gz (eqmxMr _ (eqmx_gen _)) eqmx_gen.
      rewrite -MatrixGenField.in_genJ // -[U *m _](subrK UzA).
      rewrite MatrixGenField.in_genD subsetmx_add //.
        exact: MatrixGenField.subsetmx_in_gen.
      pose Af := MatrixGenField.gen_root rG irrG cAG.
      have: (Af *m: inFA _ U <= inFA _ U)%MR by exact: subsetmx_scale.
      apply: subsetmx_trans; rewrite -[Af *m: _]MatrixGenField.val_genK.
      rewrite MatrixGenField.val_genZ MatrixGenField.mxval_root.
      rewrite MatrixGenField.in_genK MatrixGenField.subsetmx_in_gen //.
      by rewrite (subsetmx_trans nUzA) ?subsetmxMr // -eqmx_gsum gsummxSl.
    apply: subset_trans; rewrite subUset !sub1set !inE Gx Gy /=.
    rewrite -[r x](subrK 1%R) -[r y](subrK 1%R) -/Ax -/Ay !(mulmx_addr _ _ 1).
    rewrite !mulmx1 !subsetmx_add //; do [rewrite mul_col_mx | exact: gsummxSl].
      rewrite -eqmx_gsum -mulmxA Ay2 mulmx0 gsummxS ?subset0mx //.
      by rewrite -eqmx_gsum gsummxSr.
    rewrite -mulmxA -[Ay *m Ax](addKr (Ax *m Ay)) -/A addrC (mulmx_subr _ A).
    rewrite {1 3}def_v !mulmxA -(mulmxA u) Ax2 mulmx0 mul0mx subr0.
    by rewrite -eqmx_gsum gsummxS ?subset0mx.
  have nzU: UA != 0.
    rewrite -mxrank_eq0 eqmx_gen mxrank_eq0; apply/eqP.
    move/(canRL ((MatrixGenField.in_genK _ _ _) _)).
    rewrite MatrixGenField.val_gen0; apply/eqP; rewrite -subsetmx0 -eqmx_gsum.
    by rewrite gsummx_sub subsetmx0 negb_and nzv.
  case/mx_irrP: irrAG => _; move/(_ UA Umod nzU) <-.
  by rewrite eqmx_gen rank_leq_row.
rewrite leq_eqVlt ltnS leq_eqVlt ltnNge dA_gt0 orbF orbC; case/pred2P=> def_dA.
  rewrite [_^`(1)](commG1P _) ?pgroup1 // quotient_cents2r // gen_subG.
  apply/subsetP=> zt; case/imset2P=> z t Gz Gt ->{zt}.
  rewrite !inE groupR //= [[~ z, t]]mulgA -invMg -/rA !rAG ?groupV ?groupM //.
  set Az := rA z; set At := rA t; rewrite {1}[rA]lock.
  suffices ->: Az *m At = At *m Az.
    by rewrite -rAG // -lock -rAG ?mulVg ?groupV ?groupM // rAG.
  by move: Az At; rewrite def_dA => Az At; rewrite [Az]mx11_scalar scalar_mxC.
move: (@kquo_mx _ _ _ _ _ _) (kquo_mx_repr _) (kquo_mx_faithful rAG) => /=.
set K := mx_repr_ker _; rewrite def_dA => r2 r2G.
move/der1_odd_GL2_charf; move/implyP.
rewrite odd_2'nat [pnat _ _]morphim_pgroup /pgroup -?odd_2'nat //=.
apply: etrans; apply: esym; apply: eq_pnat; apply: charf_eq.
rewrite (fieldM_char (MatrixGenField.genRM _ _ _)) char_Fp //.
by case: (pgroup_1Vpr pE) (ntE) => [-> | [] //]; rewrite eqxx.
Qed.

End BGappendixA.

