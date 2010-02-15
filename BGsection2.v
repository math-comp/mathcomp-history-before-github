Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq div.
Require Import fintype bigops prime binomial finset ssralg.
Require Import groups morphisms normal automorphism commutators zmodp.
Require Import gprod cyclic center pgroups nilpotent sylow abelian maximal.
Require Import matrix mxrepresentation BGsection1.

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
   forall (F : fieldType) (G : {group gT}) (rG : mx_representation F G 2),
 odd #|G| -> mx_repr_faithful rG -> [char F].-group G^`(1).
Proof.
move=> F G; elim: {G}_.+1 {-2}G (ltnSn #|G|) => // m IHm G le_g_m rG oddG ffG.
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
  set K := 'O_p^'(G) => defG nKP _.
  have nKG: G \subset 'N(K) by rewrite normal_norm ?pcore_normal.
  suffices p'G': p^'.-group G^`(1) by case/eqnP: (pgroupP p'G' p p_pr pG').
  apply: pgroupS (pcore_pgroup p^' G); rewrite -quotient_cents2 //= -/K.
  by rewrite -defG quotient_mulgr /= -/K quotient_cents ?(subset_trans sPN).
pose Q := G^`(1) :&: P; have sQG: Q \subset G by rewrite subIset ?der_subS.
have nQG: G \subset 'N(Q) by rewrite normsI // normal_norm ?der_normalS.
have pQ: p %| #|Q|.
  have sylQ: p.-Sylow(G^`(1)) Q by apply: pSylow_normalI (der_normalS _ _) _.
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
wlog: F p_nz rG ffG / mx_reducible (subg_repr rG sQG).
  move=> IH_F; pose rQ := subg_repr rG sQG.
  have irrQ: mx_irreducible rQ by exact: IH_F ffG.
  case scalQ: (Q \subset [pred x | is_scalar_mx (rG x)]).
    case: irrQ => _; exists (pid_mx 1); rewrite rank_pid_mx ?andbT //.
    apply/submodmxP=> x; move/(subsetP scalQ); case/is_scalar_mxP=> a ->.
    by rewrite scalar_mxC subsetmxMl.
  case/subsetPn: scalQ => x Qx.
  rewrite !inE -mxminpoly_linear_is_scalar -ltnNge => non_scal_rx.
  have cQrx: (centgmx rQ (rG x)).
    by apply/centgmxP=> y Qy; rewrite -!(repr_mxM rQ) // (centsP abelQ).
  have:= MatrixGenField.non_linear_gen_reducible irrQ cQrx non_scal_rx.
  have fRM := MatrixGenField.genRM irrQ cQrx.
  apply: IH_F (map_repr fRM rG) _; last by rewrite map_mx_repr_faithful.
  by rewrite -(ringM_nat fRM) fieldM_eq0.
case=> // U; rewrite ltnS -eqn_leq eq_sym; case/andP=> Umod Uscal.
case/mx_Maeshke: (Umod) => [|V [Vmod sumUV tiUV]].
  have: p.-group Q by apply: pgroupS (pHall_pgroup sylP); rewrite subsetIr.
  by apply: sub_in_pnat=> q _; move/eqnP->; rewrite !inE p_pr.
have [u defU]: exists u : 'rV_2, (u :=: U)%MS.
  by move: (row_base U) (eq_row_base U); rewrite (eqP Uscal) => u; exists u.
have{tiUV Uscal} [v defV]: exists v : 'rV_2, (v :=: V)%MS.
  move/mxrank_disjoint_sum: tiUV; rewrite (eqP Uscal) (eqnP sumUV) => [[Vscal]].
  by move: (row_base V) (eq_row_base V); rewrite -Vscal => v; exists v.
pose B : 'M_(1 + 1) := col_mx u v; have{sumUV} uB: B \in unitmx.
  rewrite -row_full_unit /row_full eqn_leq rank_leq_row {1}addn1.
  by rewrite -sumsmxE -{1}(eqnP sumUV) mxrankS // sumsmxS ?defU ?defV.
pose Qfix (w : 'rV_2) := {in Q, forall y, w *m rG y <= w}%MS.
have{U defU Umod} u_fix: Qfix u.
  by move=> y Qy; rewrite /= (eqmxMr _ defU) defU (submodmxP _ _ Umod).
have{V defV Vmod} v_fix: Qfix v.
  by move=> y Qy; rewrite /= (eqmxMr _ defV) defV (submodmxP _ _ Vmod).
case/Cauchy: pQ => // x Qx oxp; have Gx := subsetP sQG x Qx.
case/subsetmxP: (u_fix x Qx) => a def_ux.
case/subsetmxP: (v_fix x Qx) => b def_vx.
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
- move=> w; case/subsetmxP=> c; have:= mulmxKV uB w.
  rewrite -[_ *m invmx B]hsubmxK [lsubmx _]mx11_scalar [rsubmx _]mx11_scalar.
  move: (_ 0) (_ 0) => dv du; rewrite mul_row_col !mul_scalar_mx => <-{w}.
  rewrite mulmx_addl -!scalemxAl def_ux def_vx mulmx_addr -!scalemxAr.
  rewrite !scalemxAl -!mul_row_col; move/(can_inj (mulmxK uB)).
  case/eq_row_mx => eqac eqbc; apply/orP.
  case: (eqVneq dv 0) => [-> | nz_dv].
    by rewrite scale0mx addr0 subsetmx_scale.
  case: (eqVneq du 0) => [-> | nz_du].
    by rewrite orbC scale0mx add0r subsetmx_scale.
  case/eqP: ne_ab; rewrite -[b]scale1mx -(mulVf nz_dv) -[a]scale1mx.
  by rewrite -(mulVf nz_du) -!scalemxA eqac eqbc !scalemxA !mulVf.
have{x Gx Qx oxp nx_uv} redG: forall y (A := rG y),
  y \in G -> (u *m A <= u /\ v *m A <= v)%MS.
- move=> y A Gy; have uA: row_free A by rewrite row_free_unit repr_mx_unit.
  have Ainj: forall w t : 'rV_2, (w *m A <= w -> t *m A <= w -> t *m A <= t)%MS.
    move=> w t; case/sub_rVP=> c ryww; case/sub_rVP=> d rytw.
    rewrite -(subsetmxMfree _ _ uA) rytw -scalemxAl ryww scalemxA mulrC.
    by rewrite -scalemxA subsetmx_scale.
  have{Qx nx_uv} nAx: forall w, Qfix w -> (w *m A <= u \/ w *m A <= v)%MS.
    move=> w nwQ; apply: nx_uv; rewrite -mulmxA -repr_mxM // conjgCV.
    rewrite repr_mxM ?groupJ ?groupV // mulmxA subsetmxMr // nwQ // -mem_conjg.
    by rewrite (normsP nQG).
  have [uAu | uAv] := nAx _ u_fix; have [vAu | vAv] := nAx _ v_fix; eauto.
  have [k ->]: exists k, A = A ^+ k.*2.
    exists #[y].+1./2; rewrite -mul2n -divn2 mulnC divnK.
      by rewrite -repr_mxX // expgS expg_order mulg1.
    by rewrite dvdn2 negbK; apply: oddSg oddG; rewrite cycle_subG.
  elim: k => [|k [IHu IHv]]; first by rewrite !mulmx1.
  case/sub_rVP: uAv => c uAc; case/sub_rVP: vAu => d vAd.
  rewrite doubleS !exprS !mulmxA; do 2!rewrite uAc vAd -!scalemxAl.
  by rewrite !subsetmx_scale.
suff trivG': G^`(1) = 1%g by rewrite /= trivG' cards1 gtnNdvd ?prime_gt1 in pG'.
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
Theorem charf'_GL2_abelian :
    forall (F : fieldType) (G : {group gT}) (rG : mx_representation F G 2),
  odd #|G| -> mx_repr_faithful rG -> [char F]^'.-group G -> abelian G.
Proof.
move=> F G rG oddG ffG char'G; apply/commG1P; apply/eqP.
rewrite trivg_card1 (pnat_1 _ (pgroupS _ char'G)) ?comm_subG //=.
exact: der1_odd_GL2_charf ffG.
Qed.

(* This is B & G, Theorem 2.6 (b) *)
Theorem charf_GL2_der_subS_abelian_Sylow :
    forall p (F : fieldType) (G : {group gT}) (rG : mx_representation F G 2),
    odd #|G| -> mx_repr_faithful rG -> p \in [char F] ->
  exists P : {group gT}, [/\ p.-Sylow(G) P, abelian P & G^`(1) \subset P].
Proof.
move=> p F G rG oddG ffG charFp.
have{oddG} pG': p.-group G^`(1).
  rewrite /pgroup -(eq_pnat _ (charf_eq charFp)).
  exact: der1_odd_GL2_charf ffG.
have{pG'} [P SylP sG'P]:= Sylow_superset (der_sub _ _) pG'.
exists P; split=> {sG'P}//; case/and3P: SylP => sPG pP _.
apply/commG1P; apply/trivgP; apply: subset_trans ffG; rewrite gen_subG.
apply/subsetP=> yz; case/imset2P=> y z Py Pz ->{yz}.
rewrite inE (subsetP sPG) ?groupR //=.
pose rP := subg_repr rG sPG; pose U := rfix_mx rP.
rewrite -(inj_eq (can_inj (mulKmx (repr_mx_unit rP (groupM Pz Py))))).
rewrite mul1mx mulmx1 -repr_mxM ?(groupR, groupM) // -commgC !repr_mxM //.
have{pP} pP: [char F].-group P by rewrite /pgroup (eq_pnat _ (charf_eq charFp)).
have: U != 0 by exact: rfix_pgroup_char.
rewrite -mxrank_eq0 -lt0n 2!leq_eqVlt ltnNge rank_leq_row orbF orbC eq_sym.
case/orP=> [Ufull | Uscal].
  suff{y z Py Pz} rP1: forall y, y \in P -> rP y = 1%:M by rewrite !rP1 ?mulmx1.
  move=> y Py; apply/row_matrixP=> i.
  by rewrite rowE -row1 (subsetmx_rfixP _ _ _) ?subsetmx_full.
have [u defU]: exists u : 'rV_2, (u :=: U)%MS.
  by move: (row_base U) (eq_row_base U); rewrite -(eqP Uscal) => u; exists u.
have fix_u: {in P, forall x, u *m rP x = u}.
  by move/eqmxP: defU; case/andP; move/subsetmx_rfixP.
have [v defUc]: exists u : 'rV_2, (u :=: U^C)%MS.
  have UCscal: \rank U^C = 1%N by rewrite mxrank_compl -(eqP Uscal).
  by move: (row_base _)%MS (eq_row_base U^C)%MS; rewrite UCscal => v; exists v.
pose B := col_mx u v; have uB: B \in unitmx.
  rewrite -row_full_unit -subset1mx -(eqmxMfull _ (sumsmx_compl_full U)).
  by rewrite mulmx1 -sumsmxE sumsmxS ?defU ?defUc.
have Umod: submodmx rP U by exact: rfix_submodmx.
pose W := rfix_mx (factmod_repr Umod).
have ntW: W != 0. 
  apply: rfix_pgroup_char pP;
  rewrite eqmxMfull ?row_full_unit ?unitmx_inv ?row_ebase_unit //.
  by rewrite rank_copid_mx -(eqP Uscal).
have{ntW} Wfull: row_full W.
  by rewrite -col_leq_rank {1}mxrank_coker -(eqP Uscal) lt0n mxrank_eq0.
have svW: (in_factmod U v <= W)%MS by rewrite subsetmx_full.
have fix_v: {in P, forall x, v *m rG x - v <= u}%MS.
  move=> x Px /=; rewrite -[v *m _](sum_sub_fact_mod U) (in_factmodJ Umod) //.
  move/subsetmx_rfixP: svW => -> //; rewrite in_factmodK ?defUc // addrK.
  by rewrite defU val_submodP.
have fixB: {in P, forall x, exists2 a, u *m rG x = u & v *m rG x = v + a *m: u}.
  move=> x Px; case/subsetmxP: (fix_v x Px) => a def_vx.
  exists (a 0 0); first exact: fix_u.
  by rewrite addrC -mul_scalar_mx -mx11_scalar -def_vx subrK.
rewrite -(inj_eq (can_inj (mulKmx uB))) // !mulmxA !mul_col_mx.
case/fixB: Py => a uy vy; case/fixB: Pz => b uz vz.
by rewrite uy uz vy vz !mulmx_addl -!scalemxAl uy uz vy vz addrAC.
Qed.

End BGsection2.
