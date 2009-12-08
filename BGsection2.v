Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq div.
Require Import fintype bigops prime binomial finset ssralg.
Require Import groups morphisms normal automorphism commutators zmodp.
Require Import gprod cyclic center pgroups nilpotent sylow maximal.
Require Import matrix mxrepresentation BGsection1 transfer.

(******************************************************************************)
(* This file should contain the useful material in B & G, section 2, that is  *)
(* not implicitly covered in mxrepresentation. We start with the three        *)
(* results that constitute B & G, Theorem 2.6: a main theorem, and the two    *)
(* corrolaries that make up the actual formulation of the theorem.            *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Import GroupScope GRing.Theory.
Open Local Scope ring_scope.

Section BGsection2.

Variable gT : finGroupType.
Implicit Type p : nat.

Lemma der1_odd_GL2_charf :
  forall (F : fieldType) (r : gT -> 'M[F]_2),
  forall (G : {group gT}) (rG : mx_repr r G),
    odd #|G| -> mx_repr_faithful rG -> [char F].-group G^`(1).
Proof.
move=> F r G; elim: {G}_.+1 {-2}G (ltnSn #|G|) => // m IHm G le_g_m rG oddG ffG.
apply/pgroupP=> p p_pr pG'; rewrite !inE p_pr /=; apply/idPn=> p_nz.
have [P sylP] := Sylow_exists p G.
have nPG: G \subset 'N(P).
  apply/idPn=> pNG; pose N := 'N_G(P); have sNG: N \subset G := subsetIl _ _.
  have{IHm pNG} p'N': [char F].-group N^`(1).
    apply: IHm (subg_repr_faithful sNG ffG); last exact: oddSg oddG.
    rewrite -ltnS (leq_trans _ le_g_m) // ltnS proper_card //.
    by rewrite /proper sNG subsetI subxx.
  have{p'N'} tiPN': P :&: N^`(1) = 1%g.
    rewrite coprime_TIg ?(pnat_coprime (pHall_pgroup sylP)) //= -/N.
    apply: sub_in_pnat p'N' => q _; apply: contraL; move/eqnP->.
    by rewrite !inE p_pr.
  have sPN: P \subset N by rewrite subsetI normG (pHall_sub sylP).
  have{tiPN'} cPN: N \subset 'C(P).
    rewrite (sameP commG1P trivgP) -tiPN' subsetI commgS //.
    by rewrite commg_subr subsetIr.
  case/sdprodP: (Burnside_normal_complement sylP cPN) => _ /=.
  set K := 'O__(G) => defG nKP _.
  have nKG: G \subset 'N(K) by rewrite normal_norm ?pcore_normal.
  suffices p'G': p^'.-group G^`(1) by case/eqnP: (pgroupP _ _ p'G' p p_pr pG').
  apply: pgroupS (pcore_pgroup p^' G); rewrite -quotient_cents2 //= -/K.
  by rewrite -defG quotient_mulgr /= -/K quotient_cents ?(subset_trans sPN).
pose Q := G^`(1) :&: P; have sQG: Q \subset G by rewrite subIset ?der_sub.
have nQG: G \subset 'N(Q) by rewrite normsI // normal_norm ?der_normal.
have pQ: p %| #|Q|.
  have sylQ: p.-Sylow(G^`(1)) Q by apply: pSylow_normalI (der_normal _ _) _.
  apply: contraLR pG'; rewrite -!p'natE // (card_Hall sylQ) -!partn_eq1 //.
  by rewrite part_pnat ?pnat_part.
have{IHm} abelQ: abelian Q.
  apply/commG1P; apply/eqP; apply/idPn => ntQ'.
  have{IHm} p'Q': [char F].-group Q^`(1).
    apply: IHm (subg_repr_faithful sQG ffG); last exact: oddSg oddG.
    rewrite -ltnS (leq_trans _ le_g_m) // ltnS proper_card //.
    rewrite /proper sQG subsetI //= andbC subEproper.
    case: eqP => [-> /= | _]; last by rewrite /proper (pHall_sub sylP) andbF.
    have: nilpotent P by rewrite (pgroup_nil (pHall_pgroup sylP)).
    move/forallP; move/(_ P); apply: contraL; rewrite subsetI subxx => -> /=.
    apply: contra ntQ'; rewrite /Q; move/eqP=> ->.
    by rewrite (setIidPr _) ?sub1G // commG1.
  case/eqP: ntQ';  have{p'Q'}: P :&: Q^`(1) = 1%g.
    rewrite coprime_TIg ?(pnat_coprime (pHall_pgroup sylP)) //= -/Q.
    apply: sub_in_pnat p'Q' => q _; apply: contraL; move/eqnP->.
    by rewrite !inE p_pr.
  by rewrite (setIidPr _) // comm_subG ?subsetIr.
wlog: F p_nz r rG ffG / mx_reducible r [group of Q].
  move=> IH_F; have irrQ: mx_irreducible r [group of Q] by exact: IH_F ffG.
  case scalQ: (Q \subset [pred x | is_scalar_mx (r x)]).
    case: irrQ => _; exists (pid_mx 1); rewrite rank_pid_mx ?andbT //.
    apply/submodmxP=> x; move/(subsetP scalQ); case/is_scalar_mxP=> a ->.
    by rewrite scalar_mxC subsetmxMl.
  case/subsetPn: scalQ => x Qx.
  rewrite !inE -mxminpoly_linear_is_scalar -ltnNge => non_scal_rx.
  pose rQ := subg_repr rG sQG.
  have cQrx: (mxcentg r [group of Q] (r x)).
    by apply/mxcentgP=> y Qy; rewrite -!rQ // (centsP abelQ).
  have:= MatrixGenField.non_linear_gen_reducible rQ irrQ cQrx non_scal_rx.
  have fRM := MatrixGenField.genRM rQ irrQ cQrx.
  apply: IH_F (map_mx_repr fRM rG) _; last by rewrite map_mx_repr_faithful.
  by rewrite -(ringM_nat fRM) fieldM_eq0.
case=> // U; rewrite ltnS -eqn_leq eq_sym; case/andP=> Umod Uscal.
case/mx_Maeshke: (Umod) => [||V [Vmod sumUV tiUV]].
- exact: subg_repr rG sQG.
- have: p.-group Q by apply: pgroupS (pHall_pgroup sylP); rewrite subsetIr.
  by apply: sub_in_pnat=> q _; move/eqnP->; rewrite !inE p_pr.
have [u defU]: exists u : 'rV_2, (u :=: U)%MR.
  by move: (row_base U) (eq_row_base U); rewrite (eqP Uscal) => u; exists u.
have{tiUV Uscal} [v defV]: exists v : 'rV_2, (v :=: V)%MR.
  move/mxrank_direct_sum: tiUV; rewrite (eqP Uscal) (eqnP sumUV) => [[Vscal]].
  by move: (row_base V) (eq_row_base V); rewrite -Vscal => v; exists v.
pose B : 'M_(1 + 1) := col_mx u v; have{sumUV} uB: B \in unitmx.
  rewrite -row_full_unit /row_full eqn_leq rank_leq_row {1}addn1.
  by rewrite -eqmx_gsum -{1}(eqnP sumUV) mxrankS // gsummxS ?defU ?defV.
have{U defU Umod} u_mod: {in Q, forall y, u *m r y <= u}%MR.
  by move=> y Qy; rewrite /= (eqmxMr _ defU) defU (submodmxP _ _ _ Umod).
have{V defV Vmod} v_mod: {in Q, forall y, v *m r y <= v}%MR.
  by move=> y Qy; rewrite /= (eqmxMr _ defV) defV (submodmxP _ _ _ Vmod).
case/Cauchy: pQ => // x Qx oxp; have Gx := subsetP sQG x Qx.
case/subsetmxP: (u_mod x Qx) => a def_ux.
case/subsetmxP: (v_mod x Qx) => b def_vx.
have def_x: r x = B^-1 *m block_mx a 0 0 b *m B.
  rewrite -mulmxA -[2]/(1 + 1)%N mul_block_col !mul0mx addr0 add0r.
  by rewrite -def_ux -def_vx -mul_col_mx mulKmx.
have ap1: a ^+ p = 1.
  suff: B^-1 *m block_mx (a ^+ p) 0 0 (b ^+ p) *m B = 1.
    move/(canRL (mulmxK uB)); move/(canRL (mulKVmx uB)); rewrite mul1mx.
    by rewrite mulmxV // -[2]/(1 + 1)%N scalar_mx_block; case/eq_block_mx.
  transitivity (r x ^+ p); last first.
    by rewrite -(mx_reprX (subg_repr rG sQG)) // -oxp expg_order rG.
  elim: (p) => [|k IHk]; first by rewrite -scalar_mx_block mulmx1 mulVmx.
  rewrite !exprS -IHk def_x -!mulmxE !mulmxA mulmxK // -2!(mulmxA B^-1).
  by rewrite -[2]/(1 + 1)%N mulmx_block !mulmx0 !mul0mx !addr0 mulmxA add0r.
have ab1: a * b = 1.
  have: Q \subset <<[set y \in G | \det (r y) == 1]>>.
  rewrite subIset // genS //; apply/subsetP=> yz; case/imset2P=> y z Gy Gz ->.
    rewrite inE !rG ?groupM ?groupV //= !detM (mulrCA _ (\det (r y))). 
    by rewrite -!det_mulmx -!rG ?groupM ?groupV // mulKg mulVg rG det1.
  rewrite gen_set_id; last first.
    apply/group_setP; split=> [|y z]; first by rewrite inE group1 /= rG det1.
    case/setIdP=> Gy y1; case/setIdP=> Gz z1; rewrite inE groupM // rG //=.
    by rewrite detM (eqP y1) (eqP z1) mulr1.
  move/subsetP; move/(_ x Qx); case/setIdP=> _.
  rewrite def_x !detM mulrAC -!detM -mulrA mulKr // -!mulmxE.
  rewrite -[2]/(1 + 1)%N det_lblock // [a]mx11_scalar [b]mx11_scalar.
  by rewrite !det_scalar1 -scalar_mxM; move/eqP->.
have ne_ab: a != b.
  apply/eqP=> defa; have defb: b = 1.
    rewrite -ap1 (divn_eq p 2) modn2.
    have ->: odd p by rewrite -oxp (oddSg _ oddG) // cycle_subG.
    by rewrite addn1 exprS mulnC exprn_mulr exprS {1 3}defa ab1 exp1rn mulr1.
  suff x1: x \in [1] by rewrite -oxp (set1P x1) order1 in p_pr.
  apply: (subsetP ffG); rewrite inE Gx def_x defa defb -scalar_mx_block mulmx1.
  by rewrite mulVmx ?eqxx.
have{ne_ab} eigen_x: forall w : 'rV_2, (w *m r x <= w -> w <= u \/ w <= v)%MR.
  move=> w; case/subsetmxP=> c; have:= (mulmxKV uB w).
  rewrite -[w *m B^-1](@hsubmxK _ 1 1 1).
  rewrite [lsubmx _]mx11_scalar [rsubmx _]mx11_scalar.
  move: (_ 0) (_ 0) => dv du; rewrite mul_row_col => <-{w}.
  rewrite mulmx_addl -!mulmxA def_ux def_vx mulmx_addr !mulmxA -2!mul_row_col.
  move/(can_inj (mulmxK uB)); case/eq_row_mx.
  rewrite !mul_mx_scalar !mul_scalar_mx => eqac eqbc.
  case: (eqVneq du 0) => [-> | nz_du].
    by right; rewrite scale0mx add0r subsetmx_scale.
  case: (eqVneq dv 0) => [-> | nz_dv].
    by left; rewrite scale0mx addr0 subsetmx_scale.
  case/eqP: ne_ab.
  rewrite -[b]scale1mx -(mulVf nz_dv) -[a]scale1mx -(mulVf nz_du).
  by rewrite -!scalemxA eqac eqbc !scalemxA !mulVf.
have redG: {in G, forall y, u *m r y <= u /\ v *m r y <= v}%MR.
  move=> y Gy; case: (eigen_x (u *m r y)) => [|uy_u | uy_v].
  - rewrite -mulmxA -rG // conjgCV rG ?groupJ ?groupV // mulmxA subsetmxMr //.
    by rewrite u_mod // -mem_conjg (normsP nQG).
  - split=> //; case: (eigen_x (v *m r y)) => // [|vy_u].
      rewrite -mulmxA -rG // conjgCV rG ?groupJ ?groupV // mulmxA subsetmxMr //.
      by rewrite v_mod // -mem_conjg (normsP nQG).
    have: (B *m r y <= u)%MR by rewrite mul_col_mx -eqmx_gsum gsummx_sub uy_u.
    move/mxrankS; rewrite leqNgt; case/negP.
    rewrite -{1}[r y]mulmx1 !eqmxMfull ?row_full_unit ?(mx_repr_unit rG) //.
    by rewrite mxrank1 ltnS rank_leq_row.
  case: (eigen_x (v *m r y)) => // [|vy_u|vy_v]; last 1 first.
  - have: (B *m r y <= v)%MR by rewrite mul_col_mx -eqmx_gsum gsummx_sub uy_v.
    move/mxrankS; rewrite leqNgt; case/negP.
    rewrite -{1}[r y]mulmx1 !eqmxMfull ?row_full_unit ?(mx_repr_unit rG) //.
    by rewrite mxrank1 ltnS rank_leq_row.
  - rewrite -mulmxA -rG // conjgCV rG ?groupJ ?groupV // mulmxA subsetmxMr //.
    by rewrite v_mod // -mem_conjg (normsP nQG).
  pose y2 := (y ^+ 2)%g; have [k ->]: exists k, y = (y2 ^+ k)%g.
    exists #[y].+1./2; rewrite -expgn_mul -divn2 mulnC divnK.
      by rewrite expgS expg_order mulg1.
    by rewrite dvdn2 negbK; apply: oddSg oddG; rewrite cycle_subG.
  have{uy_v vy_u} [uy2u vy2v]: (u *m r y2 <= u /\ v *m r y2 <= v)%MR.
    rewrite rG // !mulmxA.
    by split; apply: subsetmx_trans (subsetmxMr _ _) _; eauto.
  elim: k => [|k [IHu IHv]]; first by rewrite !rG !mulmx1.
  rewrite !expgS rG ?groupX // !mulmxA.
  by split; apply: subsetmx_trans (subsetmxMr _ _) _; eauto.
suffices trivG': G^`(1) = 1%g.
  by rewrite /= trivG' cards1 gtnNdvd ?prime_gt1 in pG'.
apply/trivgP; apply: subset_trans ffG; rewrite gen_subG.
apply/subsetP=> yz; case/imset2P=> y z Gy Gz ->{yz}; rewrite inE groupR //=.
rewrite -(inj_eq (can_inj (mulKmx (mx_repr_unit rG Gy)))).
rewrite -(inj_eq (can_inj (mulKmx (mx_repr_unit rG Gz)))).
rewrite mulmx1 -!rG ?(groupR, groupM) // mulgA -commgC.
rewrite -(inj_eq (can_inj (mulKmx uB))) !rG // !mulmxA !mul_col_mx.
case/redG: Gy; case/subsetmxP=> yu defyu; case/subsetmxP=> yv defyv.
case/redG: Gz; case/subsetmxP=> zu defzu; case/subsetmxP=> zv defzv.
do 2!rewrite defyu defyv defzu defzv -?mulmxA.
rewrite [yu]mx11_scalar [yv]mx11_scalar [zu]mx11_scalar [zv]mx11_scalar.
by rewrite !mul_scalar_mx !scalemxA (mulrC (yu _ _)) (mulrC (yv _ _)).
Qed.

(* This is B & G, Theorem 2.6 (a) *)
Theorem charf'_GL2_abelian :
  forall (F : fieldType) (r : gT -> 'M[F]_2),
  forall (G : {group gT}) (rG : mx_repr r G),
    odd #|G| -> mx_repr_faithful rG -> [char F]^'.-group G -> abelian G.
Proof.
move=> F r G rG oddG ffG char'G; apply/commG1P; apply/eqP.
rewrite trivg_card1 (pnat_1 _ (pgroupS _ char'G)) ?comm_subG //=.
exact: der1_odd_GL2_charf ffG.
Qed.

(* This is B & G, Theorem 2.6 (b) *)
Theorem charf_GL2_der_sub_abelian_Sylow :
  forall p (F : fieldType) (r : gT -> 'M[F]_2),
  forall (G : {group gT}) (rG : mx_repr r G),
    odd #|G| -> mx_repr_faithful rG -> p \in [char F] ->
    exists P : {group gT}, [/\ p.-Sylow(G) P, abelian P & G^`(1) \subset P].
Proof.
move=> p F r G rG oddG ffG charFp.
have{oddG} pG': p.-group G^`(1).
  rewrite /pgroup -(eq_pnat _ (charf_eq charFp)).
  exact: der1_odd_GL2_charf ffG.
have{pG'} [P SylP sG'P]:= Sylow_superset (der_sub0 _ _) pG'.
exists P; split=> {sG'P}//; case/and3P: SylP => sPG pP _.
apply/commG1P; apply/trivgP; apply: subset_trans ffG; rewrite gen_subG.
apply/subsetP=> yz; case/imset2P=> y z Py Pz ->{yz}.
rewrite inE (subsetP sPG) ?groupR //=.
pose rP := subg_repr rG sPG; pose U := fixg_mx r P.
rewrite -(inj_eq (can_inj (mulKmx (mx_repr_unit rP Py)))).
rewrite -(inj_eq (can_inj (mulKmx (mx_repr_unit rP Pz)))).
rewrite mulmx1 -!rP ?(groupR, groupM) // mulgA -commgC !rP //.
have{pP} pP: [char F].-group P by rewrite /pgroup (eq_pnat _ (charf_eq charFp)).
have: U != 0 by exact: fixg_pgroup_char rP.
rewrite -mxrank_eq0 -lt0n 2!leq_eqVlt ltnNge rank_leq_row orbF orbC eq_sym.
case/orP=> [Ufull | Uscal].
  suff{y z Py Pz}Ptriv: forall y, y \in P -> r y = 1%:M.
    by rewrite !Ptriv ?mulmx1.
  move=> y Py; apply/row_matrixP=> i; rewrite rowE -row1; set u := row _ _.
  have: (u <= U)%MR by apply: subsetmx_full.
  by move/subsetmx_fixgP->.
have [u defU]: exists u : 'rV_2, (u :=: U)%MR.
  by move: (row_base U) (eq_row_base U); rewrite -(eqP Uscal) => u; exists u.
have fix_u: {in P, forall x, u *m r x = u}.
  by move/eqmxP: defU; case/andP; move/subsetmx_fixgP.
have [v defUc]: exists u : 'rV_2, (u :=: U^C)%MR.
  set V := U^C%MR.
  have Vscal: \rank V = 1%N by rewrite mxrank_compl -(eqP Uscal).
  by move: (row_base V) (eq_row_base V); rewrite Vscal => v; exists v.
pose B := col_mx u v; have uB: B \in unitmx.
  rewrite -row_full_unit -subset1mx -(eqmxMfull _ (gsummx_compl_full U)).
  by rewrite mulmx1 -eqmx_gsum gsummxS ?defU ?defUc.
have Umod: submodmx r P U by exact: fixg_mx_submod.
pose W := fixg_mx (factmod_mx r U) P.
have ntW: W != 0. 
  apply: fixg_pgroup_char pP (factmod_repr Umod rP).
  rewrite eqmxMfull ?row_full_unit ?unitmx_inv ?row_ebase_unit //.
  by rewrite rank_copid_mx -(eqP Uscal).
have{ntW} Wfull: row_full W.
  rewrite /row_full eqn_leq rank_leq_row.
  rewrite {1}eqmxMfull ?row_full_unit ?unitmx_inv ?row_ebase_unit //.
  by rewrite rank_copid_mx -(eqP Uscal) // lt0n mxrank_eq0.
have svW: (in_factmod U v <= W)%MR by rewrite subsetmx_full.
have fix_v: {in P, forall x, v *m r x - v <= u}%MR.
  move=> x Px /=; rewrite -[_ *m r x](sum_sub_fact_mod U) (in_factmodJ Umod) //.
  move/subsetmx_fixgP: svW => -> //; rewrite in_factmodK ?defUc // addrK.
  by rewrite defU val_submodP.
have fixB: {in P, forall x, exists2 a, u *m r x = u & v *m r x = v + a *m: u}.
  move=> x Px; case/subsetmxP: (fix_v x Px) => a def_vx.
  exists (a 0 0); first exact: fix_u.
  by rewrite addrC -mul_scalar_mx -mx11_scalar -def_vx subrK.
rewrite -(inj_eq (can_inj (mulKmx uB))) // !mulmxA !mul_col_mx.
case/fixB: Py => a uy vy; case/fixB: Pz => b uz vz.
by rewrite uy uz vy vz !mulmx_addl -!scalemxAl uy uz vy vz addrAC.
Qed.

End BGsection2.
