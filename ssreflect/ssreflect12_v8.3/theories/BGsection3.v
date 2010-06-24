(* (c) Copyright Microsoft Corporation and Inria. All rights reserved. *)
Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq paths div.
Require Import fintype bigops prime binomial finset ssralg.
Require Import groups morphisms normal perm automorphism action commutators.
Require Import finalg zmodp gprod cyclic center pgroups gseries nilpotent sylow.
Require Import abelian maximal hall matrix mxrepresentation.
Require Import BGsection1 BGsection2.

(******************************************************************************)
(*   This file covers the material in B & G, Section 3, with the exception of *)
(* Theorem 3.6, whose long proof is in a sepearate file.                      *)
(*   Basic definitions relative to Frobenius groups are, temporarily, given   *)
(* here. All of this should move to the frobenius file once the relevant      *)
(* background material is available.                                          *)
(*   Note that in spite of the use of Gorenstein 2.7.6, the material in all   *)
(* of Section 3, and in all likelyhood the whole of B & G, does NOT depend on *)
(* the general proof of existence of Frobenius kernels, because results on    *)
(* Frobenius groups are only used when the semidirect product decomposition   *)
(* is already known, and (as we show below) in this case the kernel is always *)
(* equal to the normal complement of the Frobenius complement.                *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Local Open Scope ring_scope.
Import GroupScope GRing.Theory.

Section MoreGroups.

Variable gT : finGroupType.

Lemma conjDg : forall (A B : {set gT}) x, (A :\: B) :^ x = A :^ x :\: B :^ x.
Proof.
by move=> A B x; apply/setP=> y; rewrite mem_conjg !in_setD -!mem_conjg.
Qed.

Lemma conjD1g : forall (A : {set gT}) x, A^# :^ x = (A :^ x)^#.
Proof. by move=> A x; rewrite conjDg conjs1g. Qed.

Lemma normD1 : forall A : {set gT}, 'N(A^#) = 'N(A).
Proof.
move=> A; apply/setP=> x; rewrite !inE conjD1g; apply/idP/idP=> nAx; last exact: setSD.
apply/subsetP=> y Axy;  move/implyP: (subsetP nAx y); rewrite !inE Axy andbT.
by case: eqP Axy => // ->; rewrite mem_conjg conj1g.
Qed.

Lemma groupD1_inj : forall G H : {group gT}, G^# = H^# -> G :=: H.
Proof. by move=> G H; move/(congr1 (setU 1)); rewrite !setD1K. Qed.

End MoreGroups.

Section MoreActions.

Section RawActions.

Variables (aT : finGroupType) (rT : finType) (D : {set aT}) (to : action D rT).

Lemma astabS : forall S1 S2 : {set rT},
  S1 \subset S2 -> 'C(S2 | to) \subset 'C(S1 | to).
Proof.
move=> S1 S2 sS12; apply/subsetP=> x; rewrite !inE; case/andP=> ->.
exact: subset_trans.
Qed.

Lemma afixS : forall A1 A2 : {set aT},
  A1 \subset A2 -> 'Fix_to(A2) \subset 'Fix_to(A1).
Proof.
move=> A1 A2 sA12; apply/subsetP=> u; rewrite !inE; exact: subset_trans.
Qed.

End RawActions.

Section TotalActions.

Variables (aT : finGroupType) (rT : finType) (to : {action aT &-> rT}).

(* These lemmas need to work with arbitrary G-sets *)
Lemma sub_astab1 : forall (A : {set aT}) x,
  (A \subset 'C[x | to]) = (x \in 'Fix_to(A)).
Proof.
move=> A x; apply/subsetP/afixP=> cAx a; move/cAx;
  by rewrite ?(sub1set, inE) /=; move/eqP.
Qed.

Lemma astabC : forall (A : {set aT}) S,
  (A \subset 'C(S | to)) = (S \subset 'Fix_to(A)).
Proof.
move=> A S; apply/subsetP/subsetP.
  move=> sAC x xS; rewrite -sub_astab1; apply/subsetP=> a aA; apply/astab1P.
  by move/astabP: (sAC _ aA) => ->.
move=> sSF a aA; apply/astabP=> x xS; move: (sSF _ xS); rewrite -sub_astab1.
by move/subsetP; move/(_ _ aA); move/astab1P.
Qed.

Lemma afix_cycle : forall x, 'Fix_to(<[x]>) = 'Fix_to[x].
Proof.
move=> x; apply/eqP; rewrite eqEsubset afixS ?sub_gen //.
by rewrite -astabC gen_subG astabC /=.
Qed.

(* Aux material: Aschbacher (5.7) *)

Section Gcore.

Definition gcore (A G : {set aT}) := \bigcap_(x \in G) A :^ x.

Canonical Structure gcore_group (H G : {group aT}) := [group of gcore H G].

Lemma gcore_sub : forall (H : {set aT}) (G : {group aT}), gcore H G \subset H.
Proof. by move=> H G; rewrite (bigcap_min 1) ?conjsg1. Qed.

Lemma gcore_norm : forall (H : {set aT}) (G : {group aT}),
   G \subset 'N(gcore H G).
Proof.
move=> H G; apply/subsetP=> x Gx; rewrite inE; apply/bigcapsP=> y Gy.
by rewrite sub_conjg -conjsgM bigcap_inf ?groupM ?groupV.
Qed.

Lemma gcore_max : forall (H K : {set aT}) (G : {group aT}),
  K \subset H -> G \subset 'N(K) -> K \subset gcore H G.
Proof.
move=> H K G sKH nKG; apply/bigcapsP=> y Gy.
by rewrite -sub_conjgV (normsP nKG) ?groupV.
Qed.

End Gcore.

(* This is the first part of Aschbacher (5.7) *)
Lemma astab_trans_gcore : forall (G : {group aT}) S u,
  [transitive G, on S | to] -> u \in S -> 'C(S | to) = gcore 'C[u | to] G.
Proof.
move=> G S u transG Su; apply/eqP; rewrite eqEsubset.
rewrite gcore_max ?astabS ?sub1set //=; last first.
  exact: subset_trans (atrans_acts transG) (astab_norm _ _).
apply/subsetP=> x cSx; apply/astabP=> uy.
case/(atransP2 transG Su) => y Gy ->{uy}.
by apply/astab1P; rewrite astab1_act (bigcapP cSx).
Qed.

End TotalActions.

Section InternalGroupActions.

Variable gT : finGroupType.

(* This is the second part of Aschbacher (5.7) *)
Lemma astabRs_rcosets : forall H G : {group gT},
  'C(rcosets H G | 'Rs) = gcore H G.
Proof.
move=> H G.
rewrite (astab_trans_gcore (transRs_rcosets H G) (orbit_refl _ G _)).
by rewrite astab1Rs.
Qed.

Lemma card_conjugates : forall (A : {set gT}) (G : {group gT}),
  #|A :^: G| = #|G : 'N_G(A)|.
Proof. by move=> A G; rewrite card_orbit astab1Js. Qed.

End InternalGroupActions.

Section SubAction.

Variables (aT : finGroupType) (D : {group aT}).
Variables (rT : finType) (sP : pred rT) (sT : subFinType sP) (to : action D rT).

Lemma astab_subact : forall S : {set sT},
  'C(S | to^?) = subact_dom sP to :&: 'C(val @: S | to).
Proof.
move=> S; apply/setP=> a; rewrite inE in_setI; apply: andb_id2l => sDa.
have [Da _] := setIP sDa; rewrite !inE Da.
apply/subsetP/subsetP=> [cSa u | cSa x Sx]; rewrite !inE.
  case/imsetP=> x Sx -> {u}.
  by have:= cSa x Sx; rewrite inE -val_eqE val_subact sDa.
by have:= cSa _ (mem_imset val Sx); rewrite inE -val_eqE val_subact sDa.
Qed.

Lemma astabs_subact : forall S : {set sT},
  'N(S | to^?) = subact_dom sP to :&: 'N(val @: S | to).
Proof.
move=> S; apply/setP=> a; rewrite inE in_setI; apply: andb_id2l => sDa.
have [Da _] := setIP sDa; rewrite !inE Da.
apply/subsetP/subsetP=> [nSa u | nSa x Sx]; rewrite !inE.
  case/imsetP=> x Sx -> {u}; have:= nSa x Sx; rewrite inE; move/(mem_imset val).
  by rewrite val_subact sDa.
have:= nSa _ (mem_imset val Sx); rewrite inE; case/imsetP=> y Sy def_y.
by rewrite ((_ a =P y) _) // -val_eqE val_subact sDa def_y.
Qed.

Lemma afix_subact : forall A : {set aT},
    A \subset subact_dom sP to ->
  'Fix_(to^?)(A) = val @^-1: 'Fix_to(A) :> {set sT}.
Proof.
move=> A; move/subsetP=> sAD; apply/setP=> u.
rewrite !inE !(sameP setIidPl eqP); congr (_ == A).
apply/setP=> a; rewrite !inE; apply: andb_id2l => Aa.
by rewrite -val_eqE val_subact sAD.
Qed.

End SubAction.

End MoreActions.

Section FrobeniusDefinitions.

Variables (gT : finGroupType) (G K H : {set gT}).

CoInductive Frobenius_group_with_complement : Prop :=
  FrobeniusGroup (rT : finType) (to : {action gT &-> rT}) S of
    [faithful G, on S | to]
  & [transitive G, on S | to]
  & forall x, x \in G^# -> #|'Fix_(S | to)[x]| <= 1
  & H != 1
  & exists2 u, u \in S & H = 'C_G[u | to].

Definition Frobenius_group_with_kernel_and_complement :=
  Frobenius_group_with_complement /\ K ><| H = G.

End FrobeniusDefinitions.

Notation "{ 'Frobenius' G 'with' 'complement' H }" :=
  (Frobenius_group_with_complement G H)
  (at level 0, G, H at level 50,
   format "{ 'Frobenius'  G  'with'  'complement'  H }") : group_scope.

Notation "{ 'Frobenius' G = K ><| H }" :=
  (Frobenius_group_with_kernel_and_complement G K H)
  (at level 0, G at level 50, K, H at level 35,
   format "{ 'Frobenius'  G  =  K  ><|  H }") : group_scope.

Section FrobeniusBasics.

Variable gT : finGroupType.
Implicit Type G H K : {group gT}.

Lemma TIconjP : forall G H,
  reflect {in G &, forall x y, x * y^-1 \in 'N_G(H) \/ H :^ x :&: H :^ y = 1}
          (trivIset (H^# :^: G)).
Proof.
move=> G H; have defH := setD1K (group1 H).
apply: (iffP trivIsetP) => [tiHG x y Gx Gy | tiHG Hx Hy].
  have [||defHx|tiHxy] := tiHG (H^# :^ x) (H^# :^ y); rewrite ?mem_imset //.
    left; rewrite !inE groupM ?groupV //=.
    by rewrite -defH conjUg conjs1g conjsgM defHx actK.
  by right; apply/trivgP; rewrite -setDeq0 setDIl -!conjD1g disjoint_setI0.
case/imsetP=> x Gx ->{Hx}; case/imsetP=> y Gy ->{Hy}.
rewrite disjointEsetI !conjD1g -setDIl setDeq0.
have [nHxy|->] := tiHG x y Gx Gy; [left | by right].
by case/setIP: nHxy => _ nHxy; rewrite -{2}(normP nHxy) actM actKV.
Qed.
Implicit Arguments TIconjP [G H].

Lemma TIconj_SN_P : forall G H,
    H :!=: 1 -> H \subset G ->
  reflect (forall x, x \in G :\: H -> H :&: H :^ x = 1)
          (trivIset (H^# :^: G) && ('N_G(H) == H)).
Proof.
move=> G H ntH sHG; apply: (iffP idP) => [|sntiHG].
  case/andP; move/TIconjP=> tiHG; move/eqP=> snHG x; case/setDP=> Gx notHx.
  have [//||] := tiHG 1 x _ Gx; rewrite ?conjsg1 //.
  by rewrite  mul1g snHG groupV (negPf notHx).
apply/andP; split.
  apply/TIconjP=> x y Gx Gy.
  have Gxy: x * y^-1 \in G by rewrite groupM ?groupV.
  case Hxy: (x * y^-1 \in H); [left | right].
    by rewrite inE Gxy (subsetP (normG H)).
  by rewrite -(mulgKV y x) actM -conjIg setIC sntiHG ?conjs1g ?inE ?Hxy.
rewrite eqEsubset subsetI sHG normG !andbT -setDeq0 setDE setIAC -setDE.
apply: contraR ntH; case/set0Pn=> x; case/setIP=> Gx nHx.
by rewrite -(sntiHG x Gx) (normP nHx) setIid.
Qed.

Lemma class_supportD1 : forall G H, (class_support H G)^# =  cover (H^# :^: G).
Proof.
move=> G H; apply/setP=> x; apply/idP/idP.
  case/setD1P=> nt_x; case/imset2P=> y z Hy Gz def_x.
  apply/bigcupP; exists (H^# :^ z); first by rewrite mem_imset.
  by rewrite conjD1g !inE nt_x def_x memJ_conjg.
case/bigcupP=> Hz; case/imsetP=> z Gz ->{Hz}; rewrite conjD1g 4!inE.
by case/andP=> ->; case/imsetP=> y Hy ->; rewrite mem_imset2.
Qed.

Lemma Frobenius_TI_SN_P : forall G H,
  reflect {Frobenius G with complement H}
          [&& H \proper G, trivIset (H^# :^: G) & 'N_G(H) == H].
Proof.
move=> G H; apply: (iffP idP).
  rewrite properEneq -andbA; case/and4P=> neqHG sHG tiHG; move/eqP=> snHG.
  pose Hfix x := 'Fix_(rcosets H G | 'Rs)[x].
  have regG: forall x, x \in G^# -> #|Hfix x| <= 1.
    move=> x; case/setD1P=> nt_x Gx.
    have [->|[Hy]] := set_0Vmem (Hfix x); first by rewrite cards0.
    rewrite -(card1 Hy); case/setIP; case/imsetP=> y Gy ->{Hy} cHyx.
    apply: subset_leq_card; apply/subsetP=> Hz.
    case/setIP; case/imsetP=> z Gz ->{Hz} cHzx.
    rewrite -!sub_astab1 !astab1_act !sub1set astab1Rs in cHyx cHzx *.
    rewrite !inE (canF_eq (actK _ _)) -actM /= rcosetE rcoset_id // -snHG.
    have [//| tiHyz] := TIconjP tiHG y z Gy Gz.
    by case/negP: nt_x; rewrite -in_set1 -[[set 1]]tiHyz inE cHyx.
  apply: (FrobeniusGroup _ (transRs_rcosets H G) regG); last 2 first.
  - by apply: contra neqHG; move/eqP=> H1; rewrite -snHG H1 norm1 setIT.
  - by exists (gval H); rewrite ?orbit_refl // astab1Rs (setIidPr sHG).
  apply/subsetP=> y; case/setIP=> Gy cHy; apply: contraR neqHG => nt_y.
  rewrite (index1g sHG) //; apply/eqP; rewrite eqn_leq indexg_gt0 andbT.
  apply: leq_trans (regG y _); last by rewrite setDE 2!inE Gy nt_y /=.
  by rewrite /Hfix (setIidPl _) -1?astabC ?sub1set.
case=> rT to S ffulG transG regG ntH [u Su defH].
have sHG: H \subset G by rewrite defH subsetIl.
rewrite properEneq sHG andbT; apply/andP; split.
  apply: contra ntH; move/eqP=> defG.
  suffices defS: S = [set u] by rewrite -(trivgP ffulG) /= defS -defH.
  apply/eqP; rewrite eq_sym eqEcard sub1set Su.
  by rewrite -(atransP transG u Su) card_orbit -defH defG indexgg cards1.
apply/(TIconj_SN_P ntH sHG)=> x; case/setDP=> Gx notHx.
apply/trivgP; apply/subsetP=> y; rewrite /= defH -sub1set conjIg -astab1_act.
rewrite !(sub_astab1, subsetI) sub1set -andbA; case/and4P=> Gy cuy _ cuxy.
move/implyP: (regG y); rewrite in_setD Gy; apply: contraLR => -> /=.
rewrite (cardD1 u) (cardD1 (to u x)) inE Su cuy inE /= inE cuxy.
rewrite (actsP (atrans_acts transG)) // Su; case: eqP => //.
by move/astab1P=> cux; case/negP: notHx; rewrite defH inE Gx.
Qed.

Lemma Frobenius_partition : forall G H K,
  {Frobenius G = K ><| H} -> partition (gval K |: (H^# :^: K)) G.
Proof.
move=> G H K [frobG]; case/sdprodP=> _ defG nKH tiKH.
have [_ _ _ _ _ _ ntH _] := frobG.
have [sKG sHG]: K \subset G /\ H \subset G.
  by apply/andP; rewrite -mulG_subG defG.
move/Frobenius_TI_SN_P: frobG; case/and3P => ltHG tiHG; move/eqP=> snHG.
set HG := H^# :^: K; set KHG := _ |: _.
have defHG: HG = H^# :^: G.
  apply: atransP (orbit_refl _ _ _).
  apply/(subgroup_transitiveP (orbit_refl _ _ _) sKG (atrans_orbit _ _ _)).
  by rewrite astab1Js normD1 snHG (normC nKH).
have tiKHG: forall Hx, Hx \in HG -> [disjoint K & Hx].
  move=> Hx; case/imsetP=> x Kx ->{Hx}; rewrite disjointEsetI.
  by rewrite conjD1g -(conjGid Kx) setDE setIA -conjIg tiKH conjs1g setICr.
have{tiKHG} tiKHG: trivIset KHG.
  apply/trivIsetP=> U V.
  case/setU1P=> [-> | HG_U]; case/setU1P=> [-> | HG_V]; auto.
    by right; rewrite disjoint_sym tiKHG.
  by apply: (trivIsetP tiHG); rewrite -defHG.
apply/and3P; split=> //; last first.
  rewrite !inE eqEcard cards0 leqNgt cardG_gt0 andbF /=.
  apply/imsetP=> [[x _]]; move/eqP; apply/negP.
  by rewrite eq_sym conjD1g setDeq0 sub_conjg conjs1g subG1.
rewrite eqEcard; apply/andP; split.
  apply/bigcupsP=> U; case/setU1P=> [-> // |].
  case/imsetP=> x Kx ->{U}; rewrite conj_subG ?(subsetP sKG) //.
  by rewrite subDset subsetU ?sHG ?orbT.
rewrite -(eqnP tiKHG) big_setU1 /=; last first.
  apply/imsetP=> [[x _]]; move/setP; move/(_ 1).
  by rewrite conjD1g group1 !inE eqxx.
rewrite (eq_bigr (fun _ => #|H|.-1)) => [|Hx]; last first.
  by case/imsetP=> x _ ->; rewrite cardJg (cardsD1 1 H) group1.
rewrite sum_nat_const card_conjugates normD1.
rewrite -{3}(setIidPl sKG) -setIA snHG tiKH indexg1 -mulnS prednK //.
by rewrite -TI_cardMg ?defG.
Qed.

Lemma Frobenius_cent1_ker : forall G H K,
  {Frobenius G = K ><| H} -> {in K^#, forall x, 'C_G[x] \subset K}.
Proof.
move=> G H K frobG x; case/setD1P=> nt_x Kx.
rewrite -setDeq0 setDE -setIA -disjointEsetI disjoint_sym.
have [partG _ _] := and3P (Frobenius_partition frobG).
rewrite -(eqP partG) bigcup_disjoint // => U; case/setU1P=> [-> |].
  by rewrite disjointEsetI setIAC -setIA setICr setI0.
case/imsetP=> y Ky ->{U}; rewrite disjointEsetI setIAC -subset0 subIset //.
apply/orP; left; rewrite conjD1g setDE setIA -setDE subDset setU0.
rewrite -[x](conjgKV y) -conjg_set1 normJ -conjIg sub_conjg conjs1g.
apply/subsetP=> z; case/setIP=> cxz Hz.
have{frobG} [frobG defG] := frobG; have [_ _ _ _ _ _ ntH _] := frobG.
move/Frobenius_TI_SN_P: frobG; case/andP; case/andP=> sHG _ sntiHG.
rewrite -(TIconj_SN_P ntH sHG sntiHG (x ^ y^-1)).
  by rewrite inE Hz mem_conjg conjgE invgK mulgA -(cent1P cxz) mulgK.
have sKG: K \subset G by case/sdprodP: defG => _ <- _ _; rewrite mulG_subl.
have Kxy: x ^ y^-1 \in K by rewrite groupJ ?groupV.
rewrite inE (subsetP sKG) // andbT; apply: contra nt_x => Hxy.
rewrite -in_set1 -(memJ_conjg _ y^-1) conjs1g.
by case/sdprodP: defG => _ _ _ <-; rewrite inE Kxy.
Qed.

Lemma Frobenius_reg_ker : forall G H K,
  {Frobenius G = K ><| H} -> {in H^#, forall x, 'C_K[x] = 1}.
Proof.
move=> G H K frobG x; case/setD1P=> nt_x Hx; apply/trivgP.
apply/subsetP=> y; case/setIP=> Ky cxy; apply: contraR nt_x => nty.
have K1y: y \in K^# by rewrite inE nty.
have [sHG tiKH]: H \subset G /\ K :&: H = 1.
  by case: frobG => _; case/sdprodP=> _ <- _ ->; rewrite mulG_subr.
suffices: x \in K :&: H by rewrite tiKH inE.
rewrite inE (subsetP (Frobenius_cent1_ker frobG K1y)) //.
by rewrite inE cent1C (subsetP sHG).
Qed.

Lemma Frobenius_dvd_ker1 : forall G H K,
  {Frobenius G = K ><| H} -> #|H| %| #|K|.-1.
Proof.
move=> G H K frobG.
have actsH: [acts H, on K^# | 'J].
  by rewrite astabsJ normD1; case: frobG => _; case/sdprodP.
rewrite (cardsD1 1 K) group1 -(acts_sum_card_orbit actsH) /=.
rewrite (eq_bigr (fun _ => #|H|)) ?sum_nat_const ?dvdn_mull // => xH.
case/imsetP=> x K1x ->; rewrite card_orbit astab1J.
have [sHG tiKH]: H \subset G /\ K :&: H = 1.
  by case: frobG => _; case/sdprodP=> _ <- _ ->; rewrite mulG_subr.
rewrite ['C_H[x]](trivgP _) ?indexg1 //= -tiKH -{1}(setIidPl sHG) -setIA.
by rewrite setIC setSI // (Frobenius_cent1_ker frobG).
Qed.

Lemma Frobenius_coprime : forall G H K,
  {Frobenius G = K ><| H} -> coprime #|K| #|H|.
Proof.
move=> G H K; move/Frobenius_dvd_ker1; case/dvdnP=> q defK1.
rewrite -(prednK (cardG_gt0 K)) -addn1 defK1 -coprime_modl modn_addl_mul.
by rewrite coprime_modl coprime1n.
Qed.

Lemma Frobenius_ker_Hall : forall G H K,
  {Frobenius G = K ><| H} -> Hall G K.
Proof.
move=> G H K frobG; have [_ defG] := frobG.
have sKG: K \subset G by case/sdprodP: defG => _ <- _ _; rewrite mulG_subl.
rewrite /Hall -divgS sKG //= -(sdprod_card defG) mulKn //.
exact: Frobenius_coprime frobG.
Qed.

Lemma Frobenius_compl_Hall : forall G H K,
  {Frobenius G = K ><| H} -> Hall G H.
Proof.
move=> G H K frobG; have [_ defG] := frobG.
have sHG: H \subset G by case/sdprodP: defG => _ <- _ _; rewrite mulG_subr.
rewrite /Hall -divgS sHG //= -(sdprod_card defG) mulnK // coprime_sym.
exact: Frobenius_coprime frobG.
Qed.


End FrobeniusBasics.

(*
Axiom Frobenius_kernel_exists : forall (gT : finGroupType) (G H : {group gT}),
  {Frobenius G with complement H} -> group_set (G :\: cover (H^# :^: G)).
*)

Section BGsection3.

Implicit Type F : fieldType.
Implicit Type gT : finGroupType.
Implicit Type p : nat.

(* This is B & G, Lemma 3.1. *)
Lemma Frobenius_semiregularP : forall gT (G K R : {group gT}),
    K ><| R = G -> K :!=: 1 -> R :!=: 1 ->
  ({in R^#, forall x, 'C_K[x] = 1} <-> {Frobenius G = K ><| R}).
Proof.
move=> gT G K R defG ntK ntR; split=> [regG|]; last exact: Frobenius_reg_ker.
split=> //; apply/Frobenius_TI_SN_P.
have [_ defKR nKR tiKR] := sdprodP defG.
have [sKG sRG]: K \subset G /\ R \subset G.
  by apply/andP; rewrite -mulG_subG defKR.
rewrite /proper sRG -{1}defKR mulG_subG subxx andbT (sameP setIidPl eqP) tiKR.
rewrite eq_sym ntK; apply/(TIconj_SN_P ntR sRG) => x; case/setDP=> Gx notRx.
apply/trivgP; apply: contraR notRx; case/subsetPn=> y; case/setIP=> Hy.
move: Gx; rewrite -defKR -(normC nKR); case/imset2P=> xr xk Rxr Kxk ->{x}.
rewrite groupMl //= conjsgM {xr Rxr}(conjGid Rxr).
case/imsetP=> z Rxz def_y nt_y; rewrite (subsetP (sub1G R)) //.
rewrite -(regG y); last by rewrite !(nt_y, inE).
rewrite inE Kxk -groupV cent1C (sameP cent1P commgP) -in_set1 -[[set 1]]tiKR.
rewrite inE {1}commgEr invgK groupM ?memJ_norm ?groupV ?(subsetP nKR) //=.
by rewrite commgEl {2}def_y actK groupM ?groupV.
Qed.

(* This is B & G, Lemma 3.2. *)
Section FrobeniusQuotient.

Variables (gT : finGroupType) (G K R : {group gT}).

Let frobQuo : forall N : {group gT},
    {Frobenius G = K ><| R} -> solvable K -> N <| G -> N \proper K ->
  {Frobenius G / N = (K / N) ><| (R / N)}.
Proof.
move=> N frobG solK nsNG; case/andP=> sNK ltNK.
have [[_ _ _ _ _ _ ntR _] defG] := frobG.
have [_ defKR nKR tiKR] := sdprodP defG.
have [sKG sRG]: K \subset G /\ R \subset G.
  by apply/andP; rewrite -mulG_subG defKR.
have nsNK := normalS sNK sKG nsNG.
apply/Frobenius_semiregularP=> [|||Nx].
- rewrite sdprodE ?quotient_norms //.
    by rewrite -quotientMl ?defKR ?normal_norm.
  by rewrite -quotientGI // tiKR quotient1.
- by rewrite -subG1 quotient_sub1 ?normal_norm.
- rewrite -subG1 quotient_sub1; last by rewrite (subset_trans sRG) ?normal_norm.
  apply: contra ntR => sRN.
  by rewrite -subG1 -tiKR subsetI (subset_trans sRN) /=.
rewrite !inE andbC; case/andP; case/morphimP=> x nNx Rx ->{Nx} notNx.
apply/trivgP; rewrite /= -cent_cycle -quotient_cycle //.
rewrite -coprime_quotient_cent ?cycle_subG //; last first.
  by apply: coprimegS (Frobenius_coprime frobG); rewrite cycle_subG.
rewrite cent_cycle (Frobenius_reg_ker frobG) ?quotient1 //.
by rewrite !inE Rx andbT; apply: contra notNx; move/eqP->; rewrite morph1.
Qed.

(* This is B & G, Lemma 3.2 (a). *)
Lemma Frobenius_normal_proper_ker : forall N : {group gT},
    {Frobenius G = K ><| R} -> solvable K -> N <| G -> ~~ (K \subset N) ->
  N \proper K.
Proof.
move=> N frobG solK nsNG ltNK; rewrite /proper ltNK andbT.
have [[_ _ _ _ _ _ ntR _] defG] := frobG.
have [_ defKR nKR tiKR] := sdprodP defG.
have [sKG sRG]: K \subset G /\ R \subset G.
  by apply/andP; rewrite -mulG_subG defKR.
have nsKG: K <| G by case/sdprod_normal_compl: defG.
pose H := N :&: K; have nsHG: H <| G by exact: normalI.
have [sNG nNG] := andP nsNG; have [_ nHG] := andP nsHG.
have ltHK: H \proper K by rewrite /proper subsetIr subsetI subxx andbT.
have nRKqH: K / H \subset 'N((N :&: R) / H).
  rewrite cents_norm // centsC quotient_cents2r // commg_subI //.
    by rewrite setIS ?(subset_trans sRG) ?normal_norm.
  by rewrite subsetI subxx ?(subset_trans sKG).
have ntKqH: K / H != 1.
  by rewrite -subG1 quotient_sub1 ?subsetI ?subxx ?andbT // (subset_trans sKG).
case/trivgPn: ntKqH => Hx KqHx ntHx.
have: (N :&: R) / H :&: ((N :&: R) / H) :^ Hx \subset [1].
  have [frobGqH] := frobQuo frobG solK nsHG ltHK.
  case/sdprodP=> _ _ _ tiKRqH.
  have [_ _ _ _ _ _ ntRqH _] := frobGqH.
  move/Frobenius_TI_SN_P: frobGqH; case/andP=> _ tiGqH.
  have GqHx: Hx \in G / H :\: R / H.
    rewrite inE (subsetP (quotientS _ sKG)) //= andbT.
    apply: contra ntHx => RqHx; rewrite -cycle_eq1 -subG1 -tiKRqH cycle_subG.
    by rewrite inE KqHx.
  rewrite -(TIconj_SN_P ntRqH (quotientS _ sRG) tiGqH Hx GqHx).
  by rewrite setISS ?conjSg ?quotientS ?subsetIr.
rewrite (setIidPr _); last by have:= subsetP nRKqH Hx KqHx; rewrite inE.
rewrite sub_conjg conjs1g quotient_sub1; last first.
  by rewrite subIset // (subset_trans sRG) ?orbT.
rewrite subsetI subsetIl (sameP setIidPl eqP) setIAC -setIA tiKR.
rewrite (setIidPr (sub1G N)) eq_sym /= => tiNR; rewrite -(setIidPl sNG).
case/and3P: (Frobenius_partition frobG); move/eqP=> <- _ _.
rewrite big_distrr /=; apply/bigcupsP=> U.
case/setU1P=> [->|]; [exact: subsetIr | case/imsetP=> x Kx ->{U}].
rewrite conjD1g setDE setIA subIset //.
rewrite -(normP (subsetP (subset_trans sKG nNG) x Kx)) -conjIg.
by rewrite (eqP tiNR) conjs1g sub1G.
Qed.

(* This is B & G, Lemma 3.2 (b). *)
Lemma Frobenius_quotient : forall N : {group gT},
    {Frobenius G = K ><| R} -> solvable K -> N <| G -> ~~ (K \subset N) ->
  {Frobenius G / N = (K / N) ><| (R / N)}.
Proof.
move=> N frobG solK nsNG ltKN.
apply: frobQuo => //; exact: (Frobenius_normal_proper_ker frobG).
Qed.

End FrobeniusQuotient.

End BGsection3.
