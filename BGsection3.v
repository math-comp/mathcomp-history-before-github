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
move=> A; apply/setP=> x; rewrite !inE conjD1g.
apply/idP/idP=> nAx; last exact: setSD.
apply/subsetP=> y Axy;  move/implyP: (subsetP nAx y); rewrite !inE Axy andbT.
by case: eqP Axy => // ->; rewrite mem_conjg conj1g.
Qed.

Lemma groupD1_inj : forall G H : {group gT}, G^# = H^# -> G :=: H.
Proof. by move=> G H; move/(congr1 (setU 1)); rewrite !setD1K. Qed.

Lemma sdprod_context : forall G K H : {group gT}, K ><| H = G ->
  [/\ K <| G, H \subset G, K * H = G, H \subset 'N(K) & K :&: H = 1].
Proof.
move=> G K H; case/sdprodP=> _ <- nKH tiKH.
by rewrite /normal mulG_subl mulG_subr mulG_subG normG.
Qed.

Lemma sdprod_Hall : forall G K H : {group gT},
  K ><| H = G -> Hall G K = Hall G H.
Proof.
move=> G K H; case/sdprod_context; case/andP=> sKG _ sHG defG _ tiKH.
by rewrite /Hall sKG sHG -!divgS // -defG TI_cardMg // coprime_sym mulKn ?mulnK.
Qed.

Lemma coprime_sdprod_Hall : forall G K H : {group gT},
  K ><| H = G -> coprime #|K| #|H| = Hall G K.
Proof.
move=> G K H; case/sdprod_context; case/andP=> sKG _ _ defG _ tiKH.
by rewrite /Hall sKG -divgS // -defG TI_cardMg ?mulKn.
Qed.

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

Section PartialActions.

Variables (aT : finGroupType) (rT : finType).
Variables (D : {group aT}) (to : action D rT).
Implicit Types A B : {group aT}.
Implicit Type S : {set rT}.

Lemma orbit_in_transl : forall A x y,
  A \subset D -> y \in orbit to A x -> orbit to A y = orbit to A x.
Proof.
move=> A x y sAD Axy; apply/setP=> z.
by apply/idP/idP; apply: sub_orbit_trans; rewrite // sub_orbit_sym.
Qed.

Lemma card_orbit_in : forall A x,
  A \subset D -> #|orbit to A x| = #|A : 'C_A[x | to]|.
Proof.
move=> A x sAD; rewrite orbit_stabilizer 1?card_in_imset //.
exact: can_in_inj (act_reprK _).
Qed.

Lemma atrans_dvd_index_in : forall A S,
  A \subset D -> [transitive A, on S | to] -> #|S| %| #|A : 'C_A(S | to)|.
Proof.
move=> A S sAD; case/imsetP=> x Sx defS; rewrite {1}defS card_orbit_in //.
by rewrite indexgS // setIS // astabS // sub1set.
Qed.

Lemma atrans_dvd_in : forall A S,
  A \subset D -> [transitive A, on S | to] -> #|S| %| #|A|.
Proof.
move=> A S sAD transA; apply: dvdn_trans (atrans_dvd_index_in sAD transA) _.
exact: dvdn_indexg.
Qed.

Lemma atransPin : forall A S,
     A \subset D -> [transitive A, on S | to] ->
  forall x, x \in S -> orbit to A x = S.
Proof. move=> A S sAD; case/imsetP=> x _ -> y; exact: orbit_in_transl. Qed.

Lemma atransP2in : forall A S,
    A \subset D -> [transitive A, on S | to] ->
  {in S &, forall x y, exists2 a, a \in A & y = to x a}.
Proof.
by move=> A S sAD transA x y; move/(atransPin sAD transA) <-; move/imsetP.
Qed.

Lemma atrans_acts_in : forall (A : {group aT}) (S : {set rT}),
  A \subset D -> [transitive A, on S | to] -> [acts A, on S | to].
Proof.
move=> A S sAD transA; apply/subsetP=> a Aa; rewrite !inE (subsetP sAD) //.
by apply/subsetP=> x; move/(atransPin sAD transA) <-; rewrite inE mem_imset.
Qed.

Lemma subgroup_transitivePin : forall (A B : {group aT}) (S : {set rT}) x,
     x \in S -> B \subset A -> A \subset D -> [transitive A, on S | to] ->
  reflect ('C_A[x | to] * B = A) [transitive B, on S | to].
Proof.
move=> A B S x Sx sBA sAD trA; have sBD := subset_trans sBA sAD.
apply: (iffP idP) => [trB | defA].
  rewrite group_modr //; apply/setIidPl; apply/subsetP=> a Aa.
  have Sxa: to x a \in S by rewrite (acts_act (atrans_acts_in sAD trA)).
  have [b Bb xab]:= atransP2in sBD trB Sxa Sx.
  have Da := subsetP sAD a Aa; have Db := subsetP sBD b Bb.
  rewrite -(mulgK b a) mem_mulg ?groupV // !inE groupM //= sub1set inE.
  by rewrite actMin -?xab.
apply/imsetP; exists x => //; apply/setP=> y; rewrite -(atransPin sAD trA Sx).
apply/imsetP/imsetP=> [] [a]; last by exists a; first exact: (subsetP sBA).
rewrite -defA; case/imset2P=> c b; case/setIP=> _ cxc Bb -> ->.
exists b; rewrite ?actMin ?(astab_dom cxc) ?(subsetP sBD) //.
by rewrite (astab_act cxc) ?inE.
Qed.

End PartialActions.

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

Lemma gacentQ : forall (A : {set gT}) (G : {group gT}), 'C_(|'Q)(A) = 'C(A / G).
Proof.
move=> A G; apply/setP=> Gx; case: (cosetP Gx) => x Nx ->{Gx}.
rewrite -sub_cent1 -astab1J astabC sub1set -(quotientInorm G A).
have defD: qact_dom 'J G = 'N(G) by rewrite qact_domE ?subsetT ?astabsJ.
rewrite !(inE, mem_quotient) //= defD setIC.
apply/subsetP/subsetP=> [cAx Ga | cAx a Aa].
  case/morphimP=> a Na Aa ->{Ga}.
  by move/cAx: Aa; rewrite !inE qactE ?defD ?morphJ.
have [_ Na] := setIP Aa; move/implyP: (cAx (coset G a)); rewrite mem_morphim //.
by rewrite !inE qactE ?defD ?morphJ.
Qed.

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
move=> G H K [frobG]; case/sdprod_context; case/andP=> sKG _ sHG defG nKH tiKH.
have [_ _ _ _ _ _ ntH _] := frobG.
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

Lemma rfix_mx_conjsg : forall F gT (G : {group gT}) n (A : {set gT}) x,
    forall rG : mx_representation F G n,
  x \in G -> A \subset G -> (rfix_mx rG (A :^ x) :=: rfix_mx rG A *m rG x)%MS.
Proof.
move=> F gT G n A x rG Gx sAG; pose rf y := rfix_mx rG (A :^ y).
suffices{x Gx} IH: {in G &, forall y z, rf y *m rG z <= rf (y * z)%g}%MS.
  apply/eqmxP; rewrite -/(rf x) -[A]conjsg1 -/(rf 1%g).
  rewrite -{4}[x] mul1g -{1}[rf x](repr_mxKV rG Gx) -{1}(mulgV x).
  by rewrite submxMr IH ?groupV.
move=> x y Gx Gy; apply/rfix_mxP=> zxy; rewrite actM; case/imsetP=> zx Azx ->.
have Gzx: zx \in G by apply: subsetP Azx; rewrite conj_subG.
rewrite -mulmxA -repr_mxM ?groupM ?groupV // -conjgC repr_mxM // mulmxA.
by rewrite rfix_mx_id.
Qed.

(* This is B & G, Lemma 3.3. *)
Lemma Frobenius_rfix_compl : forall F gT (G K R : {group gT}) n,
    forall rG : mx_representation F G n,
    {Frobenius G = K ><| R} -> [char F]^'.-group K ->
  ~~ (K \subset rker rG) -> rfix_mx rG R != 0.
Proof.
move=> F gT G K R n rG frobG; rewrite /pgroup charf'_nat => nzK.
have [sKG sRG]: K \subset G /\ R \subset G.
  by apply/andP; rewrite -mulG_subG; case: frobG => _; case/sdprodP=> _ <-.
apply: contra; move/eqP=> fixR0; rewrite rfix_mx_rstabC // -(eqmx_scale _ nzK).
pose gsum H := gring_op rG (gset_mx F G H).
have fixsum: forall H : {group gT}, H \subset G -> (gsum H <= rfix_mx rG H)%MS.
  move=> H; move/subsetP=> sHG; apply/rfix_mxP=> x Hx; have Gx := sHG x Hx.
  rewrite -gring_opG // -gring_opM ?envelop_mx_id //; congr (gring_op _ _).
  rewrite {2}/gset_mx (reindex_acts 'R _ Hx) ?astabsR //= mulmx_suml.
  by apply:eq_bigr=> y; move/sHG=> Gy; rewrite repr_mxM.
have: gsum G + rG 1 *+ #|K| = gsum K + \sum_(x \in K) gsum (R :^ x).
  rewrite -gring_opG // -sumr_const -!linear_sum -!linearD; congr gring_op.
  have bigTE := eq_bigl _ _ (fun _ => andbT _); rewrite {1}/gset_mx -bigTE.
  rewrite (set_partition_big _ (Frobenius_partition frobG)) /=.
  rewrite big_setU1 ?bigTE -?addrA /=; last first.
    apply: contraL (group1 K); case/imsetP=> x _ ->.
    by rewrite conjD1g !inE eqxx.
  congr (_ + _); rewrite big_imset /=; last first.
    have [] := frobG; move/Frobenius_TI_SN_P; case/and3P=> _ _; move/eqP=> snRG.
    case/sdprodP=> _ defG _ tiKR.
    move=> x y Kx Ky /= eqRxy; apply/eqP; rewrite eq_mulgV1 -in_set1.
    rewrite -[[set 1]]tiKR -snRG setIA inE -defG (setIidPl (mulG_subl _ _)).
    by rewrite groupM ?groupV //= -normD1 inE conjsgM eqRxy actK.
  rewrite -big_split; apply: eq_bigr => x Kx /=.
  by rewrite bigTE addrC conjD1g -big_setD1 ?group1.
have ->: gsum G = 0.
  apply/eqP; rewrite -submx0 -fixR0; apply: submx_trans (rfix_mxS rG sRG).
  exact: fixsum.
rewrite repr_mx1 -scalemx_nat add0r => ->.
rewrite big1 ?addr0 ?fixsum // => x Kx; have Gx := subsetP sKG x Kx.
apply/eqP; rewrite -submx0 (submx_trans (fixsum _ _)) ?conj_subG //.
by rewrite -(mul0mx _ (rG x)) -fixR0 rfix_mx_conjsg.
Qed.

(* This is B & G, Theorem 3.4. *)
Theorem odd_prime_sdprod_rfix0 : forall F gT (G K R : {group gT}) n,
    forall rG : mx_representation F G n,
    K ><| R = G -> solvable G -> odd #|G| -> coprime #|K| #|R| -> prime #|R| ->
    [char F]^'.-group G -> rfix_mx rG R = 0 ->
  [~: R, K] \subset rker rG.
Proof.
move=> F gT G; move: {2}_.+1 (ltnSn #|G|) => m.
elim: m => // m IHm in gT G *; rewrite ltnS => leGm K R n rG defG solG oddG.
set p := #|R| => coKR p_pr F'G regR.
have [nsKG sRG defKR nKR tiKR] := sdprod_context defG.
have [sKG nKG] := andP nsKG; have solK := solvableS sKG solG.
case: (eqsVneq K 1) => [-> | ntK]; first by rewrite commG1 sub1G.
have ker_ltK: forall H : {group gT},
  H \proper K -> R \subset 'N(H) -> [~: R, H] \subset rker rG.
- move=> H ltKH nHR; have sHK := proper_sub ltKH; set G1 := H <*> R.
  have sG1G: G1 \subset G by rewrite mulgen_subG (subset_trans sHK).
  have coHR := coprimeSg sHK coKR.
  have defG1: H ><| R = G1 by rewrite sdprodEgen // coprime_TIg.
  apply: subset_trans (subsetIr G1 _); rewrite -(rker_subg _ sG1G).
  apply: IHm; rewrite ?(solvableS sG1G) ?(oddSg sG1G) ?(pgroupS sG1G) //.
  apply: leq_trans leGm; rewrite /= norm_mulgenEr // -defKR !coprime_cardMg //.
  by rewrite ltn_pmul2r ?proper_card.
without loss [q q_pr qK]: / exists2 q, prime q & q.-group K.
  move=> IH; set q := pdiv #|K|.
  have q_pr: prime q by rewrite pdiv_prime ?cardG_gt1.
  have exHall := coprime_Hall_exists _ nKR coKR solK.
  have [Q sylQ nQR] := exHall q; have [Q' hallQ' nQ'R] := exHall q^'.
  have [sQK qQ _] := and3P sylQ; have [sQ'K q'Q' _] := and3P hallQ'.
  without loss{IH} ltQK: / Q \proper K.
    by rewrite properEneq; case: eqP IH => [<- -> | _ _ ->] //; exists q.
  have ltQ'K: Q' \proper K.
    rewrite properEneq; case: eqP (pgroupP q'Q' q q_pr) => //= ->.
    by rewrite !inE pdiv_dvd eqxx; apply.
  have nkerG := subset_trans _ (rker_norm rG).
  rewrite -quotient_cents2 ?nkerG //.
  have <-: Q * Q' = K.
    apply/eqP; rewrite eqEcard mulG_subG sQK sQ'K.
    rewrite coprime_cardMg ?(pnat_coprime qQ) //=.
    by rewrite (card_Hall sylQ) (card_Hall hallQ') partnC.
  rewrite quotientMl ?nkerG ?(subset_trans sQK) // centM subsetI.
  by rewrite !quotient_cents2r ?ker_ltK.
without loss{m IHm leGm} [ffulG cycZ]: / rker rG = 1 /\ cyclic 'Z(G).
  move=> IH; wlog [I M /= simM sumM _]: / mxsemisimple rG 1%:M.
    exact: (mx_reducible_semisimple (mxmodule1 _) (mx_Maschke _ F'G)).
  pose not_cRK_M i := ~~ ([~: R, K] \subset rstab rG (M i)).
  case: (pickP not_cRK_M) => [i | cRK_M]; last first.
    rewrite rfix_mx_rstabC ?comm_subG // -sumM.
    apply/sumsmx_subP=> i _; move/negbFE: (cRK_M i).
    by rewrite rfix_mx_rstabC ?comm_subG.
  have [modM ntM _] := simM i; pose rM := kquo_repr (submod_repr modM).
  do [rewrite {+}/not_cRK_M -(rker_submod modM) /=; set N := rker _] in rM *.
  case: (eqVneq N 1) => [N1 _ | ntN].
    apply: IH; split.
      by apply/trivgP; rewrite -N1 /N rker_submod rstabS ?submx1.
    have: mx_irreducible (submod_repr modM) by exact/submod_mx_irr.
    by apply: mx_faithful_irr_center_cyclic; exact/trivgP.
  have tiRN: R :&: N = 1.
    by apply: prime_TIg; rewrite //= rker_submod rfix_mx_rstabC // regR submx0.
  have nsNG: N <| G := rker_normal _; have [sNG nNG] := andP nsNG.
  have nNR := subset_trans sRG nNG.
  have sNK: N \subset K.
    have [pi hallK]: exists pi, pi.-Hall(G) K.
      by apply: HallP; rewrite -(coprime_sdprod_Hall defG).
    rewrite (subset_normal_Hall _ hallK) // /psubgroup sNG /=.
    apply: pnat_dvd (pHall_pgroup hallK).
    rewrite -(dvdn_pmul2r (prime_gt0 p_pr)) -!TI_cardMg // 1?setIC // defKR.
    by rewrite -norm_mulgenEr // cardSg // mulgen_subG sNG.
  have defGq: (K / N) ><| (R / N) = G / N.
    rewrite sdprodE ?quotient_norms -?quotientMr ?defKR //.
    by rewrite -quotientGI // tiKR quotient1.
  case/negP; rewrite -quotient_cents2  ?(subset_trans _ nNG) //= -/N.
  rewrite (sameP commG1P trivgP).
  apply: subset_trans (kquo_mx_faithful (submod_repr modM)).
  rewrite IHm ?quotient_sol ?coprime_morph ?morphim_odd ?quotient_pgroup //.
  - apply: leq_trans leGm; exact: ltn_quotient.
  - by rewrite card_quotient // -indexgI tiRN indexg1.
  apply/eqP; rewrite -submx0 rfix_quo // rfix_submod //.
  by rewrite regR capmx0 linear0 sub0mx.
wlog perfectK: / [~: K, R] = K.
  move=> IH; have: [~: K, R] \subset K by rewrite commg_subl.
  rewrite subEproper; case/predU1P=> //; move/ker_ltK.
  by rewrite commGC commg_normr coprime_commGid // commGC => ->.
have primeR: {in R^#, forall x, 'C_K[x] = 'C_K(R)}.
  move=> x; case/setD1P=> nt_x Rx; rewrite -cent_cycle ((<[x]> =P R) _) //.
  rewrite eqEsubset cycle_subG Rx; apply: contraR nt_x; move/prime_TIg.
  by rewrite -cycle_eq1 (setIidPr _) ?cycle_subG // => ->.
case cKK: (abelian K).
  rewrite commGC perfectK; move/eqP: regR; apply: contraLR.
  apply: Frobenius_rfix_compl => //; last exact: pgroupS F'G.
  rewrite -{2 4}perfectK coprime_abel_cent_TI // in primeR.
  by apply/Frobenius_semiregularP; rewrite // -cardG_gt1 prime_gt1.
have [spK defZK]: special K /\ 'C_K(R) = 'Z(K).
  apply: (abelian_charsimple_special qK) => //.
  apply/bigcupsP=> H; case/andP=> chHK cHH.
  have:= char_sub chHK; rewrite subEproper.
  case/predU1P=> [eqHK | ltHK]; first by rewrite eqHK cKK in cHH.
  have nHR: R \subset 'N(H) := char_norm_trans chHK nKR.
  by rewrite (sameP commG1P trivgP) /= commGC -ffulG ker_ltK.
have{spK} esK: extraspecial K.
  have abelZK := center_special_abelem qK spK.
  have: 'Z(K) != 1.
    by case: spK => _ <-; rewrite (sameP eqP commG1P) -abelianE cKK.
  case/(pgroup_pdiv (abelem_pgroup abelZK)) => _ _ [[|e] oK].
    by split; rewrite ?oK.
  suffices: cyclic 'Z(K) by rewrite (abelem_cyclic abelZK) oK pfactorK.
  rewrite (cyclicS _ cycZ) // subsetI subIset ?sKG //=.
  by rewrite -defKR centM subsetI -{2}defZK !subsetIr.
have [e e_gt0 oKqe] := card_extraspecial qK esK.
have cycR: cyclic R := prime_cyclic p_pr.
have co_q_p: coprime q p by rewrite oKqe coprime_pexpl in coKR.
move/eqP: regR; case/idPn.
rewrite defZK in primeR.
case: (repr_extraspecial_prime_sdprod_cycle _ _ defG _ oKqe) => // _.
apply=> //; last exact/trivgP.
apply: contraL (oddSg sRG oddG); move/eqP->; have:= oddSg sKG oddG.
by rewrite oKqe addn1 /= !odd_exp /= orbC => ->.
Qed.

(* Internal action version of B & G, Theorem 3.4. *)
Theorem odd_prime_sdprod_abelem_cent1 : forall k gT (G K R V : {group gT}),
    solvable G -> odd #|G| ->
    K <| G -> Hall G K -> R \in [complements to K in G] -> prime #|R| ->
    k.-abelem V -> G \subset 'N(V) -> ~~ (k %| #|G|) ->
  'C_V(R) = 1-> [~: R, K] \subset 'C_K(V).
Proof.
move=> k gT G K R V solG oddG nsKG hallK complGKR R_pr abelV nVG k'G regR.
have defG: K ><| R = G by apply/sdprod_normal_compl; rewrite complgC.
rewrite -(coprime_sdprod_Hall defG) in hallK.
have [_ sRG _ nKR _] := sdprod_context defG; rewrite subsetI commg_subr nKR.
case: (eqsVneq V 1) => [-> | ntV]; first exact: cents1.
pose rV := abelem_repr abelV ntV nVG.
apply: subset_trans (_ : rker rV \subset _); last first.
  by rewrite rker_abelem subsetIr.
apply: odd_prime_sdprod_rfix0 => //.
  have k_pr: prime k by case/pgroup_pdiv: (abelem_pgroup abelV).
  by rewrite /pgroup charf'_nat -val_eqE /= val_Fp_nat.
by apply/eqP; rewrite -submx0 rfix_abelem //= regR morphim1 rowg_mx1.
Qed.

(* This is B & G, Theorem 3.5. *)
Theorem Frobenius_prime_rfix1 : forall F gT (G K R : {group gT}) n,
    forall rG : mx_representation F G n,
    K ><| R = G -> solvable G -> prime #|R| -> 'C_K(R) = 1 ->
    [char F]^'.-group G -> \rank (rfix_mx rG R) = 1%N ->
  K^`(1) \subset rker rG.
Proof.
move=> F gT G K R n rG defG solG p_pr regR F'G fixRlin.
wlog closF: F rG F'G fixRlin / group_closure_field F gT.
  move=> IH; apply: (@group_closure_field_exists gT F) => [[Fc closFc [f fM]]].
  rewrite -(rker_map fM) IH //; last by rewrite -map_rfix_mx mxrank_map.
  by rewrite /pgroup charf'_nat -(ringM_nat fM) fieldM_eq0 // -charf'_nat.
move: {2}_.+1 (ltnSn #|K|) => m.
elim: m => // m IHm in gT G K R rG solG p_pr regR F'G closF fixRlin defG *.
rewrite ltnS => leKm.
have [nsKG sRG defKR nKR tiKR] := sdprod_context defG.
have [sKG nKG] := andP nsKG; have solK := solvableS sKG solG.
have cycR := prime_cyclic p_pr.
case: (eqsVneq K 1) => [-> | ntK]; first by rewrite derg1 commG1 sub1G.
have defR: forall x, x \in R^# -> <[x]> = R.  
  move=> x; case/setD1P; rewrite -cycle_subG -cycle_eq1 => ntX sXR.
  apply/eqP; rewrite eqEsubset sXR; apply: contraR ntX; move/(prime_TIg p_pr).
  by rewrite /= (setIidPr sXR) => ->.
have ntR: R :!=: 1 by rewrite -cardG_gt1 prime_gt1.
have frobG: {Frobenius G = K ><| R}.
  by apply/Frobenius_semiregularP=> // x Rx; rewrite -cent_cycle defR.
case: (eqVneq (rker rG) 1) => [ffulG | ntC]; last first.
  set C := rker rG in ntC *; have nsCG: C <| G := rker_normal rG.
  have [sCG nCG] := andP nsCG.
  have nCK := subset_trans sKG nCG; have nCR := subset_trans sRG nCG.
  case sKC: (K \subset C); first exact: subset_trans (der_sub _ _) _.
  have sCK: C \subset K.
    by rewrite proper_sub // (Frobenius_normal_proper_ker frobG) ?sKC.
  have frobGq: {Frobenius G / C = (K / C) ><| (R / C)}.
    by apply: Frobenius_quotient; rewrite ?sKC.
  have [[_ _ _ _ _ _ ntRq _] defGq] := frobGq.
  rewrite -quotient_sub1 ?comm_subG ?quotient_der //= -/C.
  apply: subset_trans (kquo_mx_faithful rG).
  apply: IHm defGq _; rewrite ?quotient_sol ?quotient_pgroup ?rfix_quo //.
  - rewrite card_quotient // -indexgI /= -/C setIC.
    by rewrite -(setIidPl sCK) -setIA tiKR (setIidPr (sub1G _)) indexg1.
  - have: cyclic (R / C) by [rewrite quotient_cyclic]; case/cyclicP=> Cx defRq.
    rewrite /= defRq cent_cycle (Frobenius_reg_ker frobGq) //= !inE defRq.
    by rewrite cycle_id -cycle_eq1 -defRq ntRq.
  - move=> Hq; rewrite -(group_inj (cosetpreK Hq)).
    by apply: quotient_splitting_field; rewrite ?subsetIl.
  by apply: leq_trans leKm; exact: ltn_quotient.
have ltK_abelian: forall N : {group gT},
  R \subset 'N(N) -> N \proper K -> abelian N.
- move=> N nNR ltNK; have [sNK _] := andP ltNK; apply/commG1P; apply/trivgP.
  rewrite -(setIidPr (sub1G (N <*> R))) /= -ffulG; set G1 := N <*> R.
  have sG1: G1 \subset G by rewrite mulgen_subG (subset_trans sNK).
  have defG1: N ><| R = G1.
    by rewrite sdprodEgen //; apply/trivgP; rewrite -tiKR setSI.
  rewrite -(rker_subg _ sG1).
  apply: IHm defG1 _; rewrite ?(solvableS sG1) ?(pgroupS sG1) //.
    by apply/trivgP; rewrite -regR setSI.
  by apply: leq_trans leKm; exact: proper_card.
have cK'K': abelian K^`(1).
  apply: ltK_abelian; first exact: char_norm_trans (der_char _ _) nKR.
  exact: (sol_der1_proper solK).
pose fixG := rfix_mx rG; pose NRmod N (U : 'M_n) := N <*> R \subset rstabs rG U.
have dx_modK_rfix: forall (N : {group gT}) U V,
    N \subset K -> R \subset 'N(N) -> NRmod N U -> NRmod N V ->
  mxdirect (U + V) -> (U <= fixG N)%MS || (V <= fixG N)%MS.
- move=> N U V sNK nNR nUNR nVNR dxUV.
  case: (eqsVneq N 1) => [-> | ntN]; first by rewrite -rfix_mx_rstabC sub1G.
  have sNRG: N <*> R \subset G by rewrite mulgen_subG (subset_trans sNK).
  pose rNR := subg_repr rG sNRG.
  have nfixU: forall W, NRmod N W -> ~~ (W <= fixG N)%MS -> (fixG R <= W)%MS.
    move=> W nWN not_cWN; rewrite (sameP capmx_idPr eqmxP).
    rewrite -(geq_leqif (mxrank_leqif_eq (capmxSr _ _))) fixRlin lt0n.
    rewrite mxrank_eq0 -(in_submodK (capmxSl _ _)) val_submod_eq0.
    have modW: mxmodule rNR W by rewrite /mxmodule rstabs_subg subsetI subxx.
    rewrite -(eqmx_eq0 (rfix_submod modW _)) ?mulgen_subr //.
    apply: Frobenius_rfix_compl (pgroupS (subset_trans sNK sKG) F'G) _.
      apply/Frobenius_semiregularP=> // [|x Rx].
        by rewrite sdprodEgen //; apply/trivgP; rewrite -tiKR setSI.
      by apply/trivgP; rewrite -regR /= -cent_cycle defR ?setSI.
    by rewrite rker_submod rfix_mx_rstabC ?mulgen_subl.
  have: fixG R != 0 by rewrite -mxrank_eq0 fixRlin.
  apply: contraR; case/norP=> not_fixU not_fixW.
  by rewrite -submx0 -(mxdirect_addsP dxUV) sub_capmx !nfixU.
have redG := mx_Maschke rG F'G.
wlog [U simU nfixU]: / exists2 U, mxsimple rG U & ~~ (U <= fixG K)%MS.
  move=> IH; wlog [I U /= simU sumU _]: / mxsemisimple rG 1%:M.
    exact: (mx_reducible_semisimple (mxmodule1 _) redG).
  case: (pickP (fun i => ~~ (U i <= fixG K))%MS) => [i nfixU | fixK].
    by apply: IH; exists (U i).
  apply: (subset_trans (der_sub _ _)); rewrite rfix_mx_rstabC // -sumU.
  by apply/sumsmx_subP=> i _; apply/idPn; rewrite fixK.
have [modU ntU minU] := simU; pose rU := submod_repr modU.
have irrU: mx_irreducible rU by exact/submod_mx_irr.
have [W modW sumUW dxUW] := redG U modU (submx1 U).
have cWK: (W <= fixG K)%MS.
  have:= dx_modK_rfix _ _ _ (subxx _) nKR _ _ dxUW.
  by rewrite /NRmod /= norm_mulgenEr // defKR (negPf nfixU); exact.
have nsK'G: K^`(1) <| G by exact: char_normal_trans (der_char _ _) nsKG.
have [sK'G nK'G] := andP nsK'G.
suffices nregK'U: (rfix_mx rU K^`(1))%MS != 0.
  rewrite rfix_mx_rstabC ?normal_sub // -sumUW addsmx_sub andbC.
  rewrite (submx_trans cWK) ?rfix_mxS ?der_sub //= (sameP capmx_idPl eqmxP).
  rewrite minU ?capmxSl ?capmx_module ?normal_rfix_mx_module //.
  apply: contra nregK'U => cUK'; rewrite (eqmx_eq0 (rfix_submod _ _)) //.
  by rewrite (eqP cUK') linear0.
pose rK := subg_repr rU (normal_sub nsKG); set p := #|R| in p_pr.
wlog sK: / socleType rK by exact: socle_exists.
have [i _ def_sK]: exists2 i, i \in setT & [set: sK] = orbit 'Cl G i.
  by apply/imsetP; exact: Clifford_atrans.
have card_sK: #|[set: sK]| =  #|G : 'C[i | 'Cl]|.
  by rewrite def_sK card_orbit_in ?indexgI.
have ciK: K \subset 'C[i | 'Cl].
  apply: subset_trans (astabS _ (subsetT _)).
  by apply: subset_trans (Clifford_astab _); exact: mulgen_subl.
pose M := socle_base i; have simM: mxsimple rK M := socle_simple i.
have [sKp | sK1 {ciK card_sK}]: #|[set: sK]| = p \/ #|[set: sK]| = 1%N.
- apply/pred2P; rewrite orbC card_sK; case/primeP: p_pr => _; apply.
  by rewrite (_ : p = #|G : K|) ?indexgS // -divgS // -(sdprod_card defG) mulKn.
- have{def_sK} def_sK: [set: sK] = orbit 'Cl R i.
    apply/eqP; rewrite eq_sym -subTset def_sK.
    apply/subsetP=> i_yz; case/imsetP=> yz; rewrite -{1}defKR.
    case/imset2P=> y z; move/(subsetP ciK); rewrite !inE sub1set inE.
    case/andP=> Gy; move/eqP=> ciy Rz -> ->{yz i_yz}.
    by rewrite actMin ?(subsetP sRG z Rz) // ciy mem_orbit.
  have inj_i: {in R &, injective ('Cl%act i)}.
    apply/dinjectiveP; apply/card_uniqP; rewrite size_map -cardE -/p.
    by rewrite -sKp def_sK /orbit Imset.imsetE cardsE.
  pose sM := (\sum_(y \in R) M *m rU y)%MS.
  have dxM: mxdirect sM.
    apply/mxdirect_sumsP=> y Ry; have Gy := subsetP sRG y Ry.
    pose j := 'Cl%act i y.
    apply/eqP; rewrite -submx0 -{2}(mxdirect_sumsP (Socle_direct sK) j) //.
    rewrite capmxS ?val_Clifford_act // ?submxMr ?component_mx_id //.
    apply/sumsmx_subP => z; case/andP=> Rz ne_z_y; have Gz := subsetP sRG z Rz.
    rewrite (sumsmx_sup ('Cl%act i z)) ?(inj_in_eq inj_i) //.
    by rewrite val_Clifford_act // ?submxMr // ?component_mx_id.
  pose inCR := \sum_(x \in R) rU x.
  have im_inCR: (inCR <= rfix_mx rU R)%MS.
    apply/rfix_mxP=> x Rx; have Gx := subsetP sRG x Rx.
    rewrite {2}[inCR](reindex_astabs 'R x) ?astabsR //= mulmx_suml.
    by apply: eq_bigr => y; move/(subsetP sRG)=> Gy; rewrite repr_mxM.
  pose inM := proj_mx M (\sum_(x \in R | x != 1) M *m rU x)%MS.
  have dxM1 := mxdirect_sumsP dxM _ (group1 R).
  rewrite repr_mx1 mulmx1 in dxM1.
  have inCR_K: M *m inCR *m inM = M.
    rewrite mulmx_sumr (bigD1 1) //= repr_mx1 mulmx1 mulmx_addl proj_mx_id //.
    by rewrite proj_mx_0 ?addr0 // summx_sub_sums.
  have [modM ntM _] := simM.
  have linM: \rank M = 1%N.
    apply/eqP; rewrite eqn_leq lt0n mxrank_eq0 ntM andbT.
    rewrite -inCR_K; apply: leq_trans (mxrankM_maxl _ _) _.
    apply: leq_trans (mxrankS (mulmx_sub _ im_inCR)) _.
    rewrite rfix_submod //; apply: leq_trans (mxrankM_maxl _ _) _.
    by rewrite -fixRlin mxrankS ?capmxSr.
  apply: contra (ntM); move/eqP; rewrite -submx0 => <-.
  by rewrite -(rfix_mx_rstabC rK) ?der_sub // -(rker_submod modM) rker_linear.
have{sK i M simM sK1 def_sK} irrK: mx_irreducible rK.
  have cycGq: cyclic (G / K) by rewrite -defKR quotient_mulgr quotient_cyclic.
  apply: (mx_irr_prime_index closF irrU cycGq simM) => x Gx /=.
  apply: (component_mx_iso simM); first exact: Clifford_simple.
  have jP: component_mx rK (M *m rU x) \in socle_enum sK.
    by apply: component_socle; exact: Clifford_simple.
  pose j := PackSocle jP; apply: submx_trans (_ : j <= _)%MS.
    by rewrite PackSocleK component_mx_id //; exact: Clifford_simple.
  have def_i: [set i] == [set: sK] by rewrite eqEcard subsetT cards1 sK1.
  by rewrite ((j =P i) _) // -in_set1 (eqP def_i) inE.
pose G' := K^`(1) <*> R.
have sG'G: G' \subset G by rewrite mulgen_subG sK'G.
pose rG' := subg_repr rU sG'G.
wlog irrG': / mx_irreducible rG'.
  move=> IH; wlog [M simM sM1]: / exists2 M, mxsimple rG' M & (M <= 1%:M)%MS.
    by apply: mxsimple_exists; rewrite ?mxmodule1; case: irrK.
  have [modM ntM _] := simM.
  have [M' modM' sumM dxM] := mx_Maschke rG' (pgroupS sG'G F'G) modM sM1.
  wlog{IH} ntM': / M' != 0.
    case: eqP sumM => [-> M1 _ | _ _ -> //]; apply: IH.
    by apply: mx_iso_simple simM; apply: eqmx_iso; rewrite addsmx0_id in M1.
  suffices: (K^`(1) \subset rstab rG' M) || (K^`(1) \subset rstab rG' M').
    rewrite !rfix_mx_rstabC ?mulgen_subl //; rewrite -!submx0 in ntM ntM' *.
    by case/orP; move/submx_trans=> sM; apply: (contra (sM _ _)).
  rewrite !rstab_subg !rstab_submod !subsetI mulgen_subl !rfix_mx_rstabC //.
  rewrite /mxmodule !rstabs_subg !rstabs_submod !subsetI !subxx in modM modM'.
  do 2!rewrite orbC -genmxE.
  rewrite dx_modK_rfix // /NRmod ?(eqmx_rstabs _ (genmxE _)) ?der_sub //.
    exact: subset_trans sRG nK'G.
  apply/mxdirect_addsP; apply/eqP; rewrite -genmx_cap (eqmx_eq0 (genmxE _)).
  rewrite -(in_submodK (submx_trans (capmxSl _ _) (val_submodP _))).
  rewrite val_submod_eq0 in_submodE -submx0 (submx_trans (capmxMr _ _ _)) //.
  by rewrite -!in_submodE !val_submodK (mxdirect_addsP dxM).
have nsK'K: K^`(1) <| K by exact: der_normal.
pose rK'K := subg_repr rK (normal_sub nsK'K).
have irrK'K: mx_absolutely_irreducible rK'K.
  wlog sK'K: / socleType rK'K by exact: socle_exists.
  have sK'_dv_K: #|[set: sK'K]| %| #|K|.
    exact: atrans_dvd_in (Clifford_atrans _ _).
  have nsK'G': K^`(1) <| G' := normalS (mulgen_subl _ _) sG'G nsK'G.
  pose rK'G' := subg_repr rG' (normal_sub nsK'G').
  wlog sK'G': / socleType rK'G' by exact: socle_exists.
  have coKp: coprime #|K| p := Frobenius_coprime frobG.
  have nK'R := subset_trans sRG nK'G.
  have sK'_dv_p: #|[set: sK'G']| %| p.
    suffices: #|G' : 'C([set: sK'G'] | 'Cl)| %| #|G' : K^`(1)|.
      rewrite -(divgS (mulgen_subl _ _)) /= {2}norm_mulgenEr //.
      rewrite coprime_cardMg ?(coprimeSg (normal_sub nsK'K)) //.
      rewrite mulKn ?cardG_gt0 // -indexgI; apply: dvdn_trans.
      exact: atrans_dvd_index_in (Clifford_atrans _ _).
    rewrite indexgS //; apply: subset_trans (Clifford_astab sK'G').
    exact: mulgen_subl.
  have eq_sK': #|[set: sK'K]| = #|[set: sK'G']|.
    rewrite !cardsT !cardE -!(size_map (fun i => socle_val i)).
    apply: perm_eq_size.
    rewrite uniq_perm_eq 1?(map_inj_uniq val_inj) 1?enum_uniq // => V.
    apply/mapP/mapP=> [] [i _ ->{V}].
      exists (PackSocle (component_socle sK'G' (socle_simple i))).
        by rewrite mem_enum.
      by rewrite PackSocleK.
    exists (PackSocle (component_socle sK'K (socle_simple i))).
      by rewrite mem_enum.
    by rewrite PackSocleK.
  have [i def_i]: exists i, [set: sK'G'] = [set i].
    apply/cards1P; rewrite -dvdn1 -{7}(eqnP coKp) dvdn_gcd.
    by rewrite -{1}eq_sK' sK'_dv_K sK'_dv_p.
  pose M := socle_base i; have simM : mxsimple rK'G' M := socle_simple i.
  have cycGq: cyclic (G' / K^`(1)).
    by rewrite /G' mulgenC quotient_mulgen ?quotient_cyclic.
  apply closF; apply: (mx_irr_prime_index closF irrG' cycGq simM) => x K'x /=.
  apply: (component_mx_iso simM); first exact: Clifford_simple.
  have jP: component_mx rK'G' (M *m rG' x) \in socle_enum sK'G'.
    by apply: component_socle; exact: Clifford_simple.
  pose j := PackSocle jP; apply: submx_trans (_ : j <= _)%MS.
    by rewrite PackSocleK component_mx_id //; exact: Clifford_simple.
  by rewrite ((j =P i) _) // -in_set1 -def_i inE.
have linU: \rank U = 1%N by apply/eqP; rewrite abelian_abs_irr in irrK'K.
case: irrU => _ nz1 _; apply: contra nz1; move/eqP=> fix0.
by rewrite -submx0 -fix0 -(rfix_mx_rstabC rK) ?der_sub // rker_linear.
Qed.

(* Internal action version of B & G, Theorem 3.5. *)
Theorem Frobenius_prime_cent_prime : forall k gT (G K R V : {group gT}),
    solvable G ->
    K <| G -> R \in [complements to K in G] -> prime #|R| -> 'C_K(R) = 1->
    k.-abelem V -> G \subset 'N(V) -> ~~ (k %| #|G|) ->
  #|'C_V(R)| = k -> K^`(1) \subset 'C_K(V).
Proof.
move=> k gT G K R V solG nsKG complGKR R_pr regRK abelV nVG k'G primeRV.
have defG: K ><| R = G by apply/sdprod_normal_compl; rewrite complgC.
have [_ sRG _ nKR _] := sdprod_context defG; rewrite subsetI der_sub.
case: (eqsVneq V 1) => [-> | ntV]; first exact: cents1.
pose rV := abelem_repr abelV ntV nVG.
apply: subset_trans (_ : rker rV \subset _); last first.
  by rewrite rker_abelem subsetIr.
have k_pr: prime k by case/pgroup_pdiv: (abelem_pgroup abelV).
apply: (Frobenius_prime_rfix1 defG) => //.
  by rewrite /pgroup charf'_nat -val_eqE /= val_Fp_nat.
apply/eqP; rewrite rfix_abelem // -(eqn_exp2l _ _ (prime_gt1 k_pr)).
rewrite -{1}(card_Fp k_pr) -card_rowg rowg_mxK.
by rewrite card_injm ?abelem_rV_injm ?subsetIl ?primeRV.
Qed.

(* Because it accounts for nearly half of the length of Section 3 (7 pages    *)
(* out of 16), and it is not used in the rest of Section 3, we have moved the *)
(* proof of B & G, Theorem 3.6 (odd_sdprod_Zgroup_cent_prime_plength1) to its *)
(* own separate file, BGtheorem3_6.v.                                         *)

Theorem prime_FrobeniusP : forall gT (G K R : {group gT}),
    K :!=: 1 -> prime #|R| ->
  ({Frobenius G = K ><| R} <-> K ><| R = G /\ 'C_K(R) = 1).
Proof.
move=> gT G K R ntK R_pr; have ntT: R :!=: 1 by rewrite -cardG_gt1 prime_gt1.
split=> [frobG | [defG regR]].
  have [_ defG] := frobG; split=> //.
  have [x defR] := cyclicP _ (prime_cyclic R_pr).
  rewrite defR cent_cycle (Frobenius_reg_ker frobG) //.
  by rewrite !inE defR cycle_id andbT -cycle_eq1 -defR.
apply/Frobenius_semiregularP=> // x; case/setD1P=> nt_x Rx.
apply/eqP; rewrite -cent_cycle -subG1 -regR setIS ?centS //.
apply: contraR nt_x; rewrite -cycle_eq1; move/(prime_TIg R_pr) <-.
by rewrite (setIidPr _) ?cycle_subG.
Qed.

(* This is B & G, Theorem 3.7. *)
Theorem odd_prime_Frobenius_kernel_nil : forall gT (G K R : {group gT}),
   K ><| R = G -> solvable G -> prime #|R| -> 'C_K(R) = 1 -> nilpotent K.
Proof.
move=> gT G K R defG solG R_pr regR.
elim: {K}_.+1 {-2}K (ltnSn #|K|) => // m IHm K leKm in G defG solG regR *.
have [nsKG sRG defKR nKR tiKR] := sdprod_context defG.
have [sKG nKG] := andP nsKG.
wlog ntK: / K :!=: 1 by case: eqP => [-> _ | _ ->] //; exact: nilpotent1.
have [L maxL _]: {L : {group gT} | maxnormal L K G & [1] \subset L}.
  by apply: maxgroup_exists; rewrite proper1G ntK norms1.
have [ltLK nLG]:= andP (maxgroupp maxL); have [sLK not_sKL]:= andP ltLK.
have{m leKm IHm}nilL: nilpotent L.
  pose G1 := L <*> R; have nLR := subset_trans sRG nLG.
  have sG1G: G1 \subset G by rewrite mulgen_subG (subset_trans sLK).
  have defG1: L ><| R = G1.
    by rewrite sdprodEgen //; apply/eqP; rewrite -subG1 -tiKR setSI.
  apply: (IHm _ _ _ defG1); rewrite ?(solvableS sG1G) ?(oddSg sG1G) //.
    exact: leq_trans (proper_card ltLK) _.
  by apply/eqP; rewrite -subG1 -regR setSI.
have sLG := subset_trans sLK sKG; have nsLG: L <| G by exact/andP.
have sLF: L \subset 'F(G) by exact: Fitting_max.
have frobG: {Frobenius G = K ><| R} by exact/prime_FrobeniusP.
have solK := solvableS sKG solG.
have frobGq := Frobenius_quotient frobG solK nsLG not_sKL.
suffices sKF: K \subset 'F(K) by exact: nilpotentS sKF (Fitting_nil K).
apply: subset_trans (chief_stab_sub_Fitting solG nsKG).
rewrite subsetI subxx; apply/bigcapsP=> [[X Y]] /=; set V := X / Y.
case/andP=> chiefXY sXF; have [maxY nsXG] := andP chiefXY.
have [ltYX nYG] := andP (maxgroupp maxY); have [sYX _]:= andP ltYX.
have [sXG nXG] := andP nsXG; have sXK := subset_trans sXF (Fitting_sub K).
have minV := chief_factor_minnormal chiefXY.
have cVL: L \subset 'C(V | 'Q).
  apply: subset_trans (subset_trans sLF (Fitting_stab_chief solG _)) _ => //.
  exact: (bigcap_inf (X, Y)).
have nVG: {acts G, on group V | 'Q}.
  by split; rewrite ?quotientS ?subsetT // actsQ // normal_norm.
pose V1 := sdpair1 <[nVG]> @* V.
have [p p_pr abelV]: exists2 p, prime p & p.-abelem V.
  apply/is_abelemP; apply: charsimple_solvable (quotient_sol _ _).
    exact: minnormal_charsimple minV.
  exact: nilpotent_sol (nilpotentS sXF (Fitting_nil _)).
have abelV1: p.-abelem V1 by rewrite morphim_abelem.
have injV1 := injm_sdpair1 <[nVG]>.
have ntV1: V1 :!=: 1.
  by rewrite -cardG_gt1 card_injm // cardG_gt1; case/andP: (mingroupp minV).
have nV1_G1 := im_sdpair_norm <[nVG]>.
pose rV := morphim_repr (abelem_repr abelV1 ntV1 nV1_G1) (subxx G).
have def_kerV: rker rV = 'C_G(V | 'Q).
  rewrite rker_morphim rker_abelem morphpreIdom morphpreIim -astabEsd //.
  by rewrite astab_actby setIid.
have kerL: L \subset rker rV by rewrite def_kerV subsetI sLG.
pose rVq := quo_repr kerL nLG.
suffices: K / L \subset rker rVq.
  rewrite rker_quo def_kerV quotientSGK //= 1?subsetI 1?(subset_trans sKG) //.
  by rewrite sLG.
have irrVq: mx_irreducible rVq.
  apply/quo_mx_irr; apply/morphim_mx_irr; apply/abelem_mx_irrP.
  apply/mingroupP; rewrite ntV1; split=> // U1; case/andP=> ntU1 nU1G sU1V.
  rewrite -(morphpreK sU1V); congr (_ @* _).
  case/mingroupP: minV => _; apply; last by rewrite sub_morphpre_injm.
  rewrite -subG1 sub_morphpre_injm ?sub1G // morphim1 subG1 ntU1 /=.
  set U := _ @*^-1 U1; rewrite -(cosetpreK U) quotient_norms //.
  have: [acts G, on U | <[nVG]>] by rewrite actsEsd ?subsetIl // morphpreK.
  rewrite astabs_actby subsetI subxx (setIidPr _) ?subsetIl //=.
  by rewrite -{1}(cosetpreK U) astabsQ ?normal_cosetpre //= -/U subsetI nYG.
have [q q_pr abelKq]: exists2 q, prime q & q.-abelem (K / L).
  apply/is_abelemP; apply: charsimple_solvable (quotient_sol _ solK).
  exact: maxnormal_charsimple maxL.
case (eqVneq q p) => [def_q | neq_qp].
  have sKGq: K / L \subset G / L by exact: quotientS.
  rewrite rfix_mx_rstabC //; have [_ _]:= irrVq; apply; rewrite ?submx1 //.
    by rewrite normal_rfix_mx_module ?quotient_normal.
  rewrite -(rfix_subg _ sKGq) rfix_pgroup_char //.
  apply: pi_pnat (abelem_pgroup abelKq) _.
  by rewrite inE /= q_pr def_q char_Fp_0.
suffices: rfix_mx rVq (R / L) == 0.
  apply: contraLR; apply: (Frobenius_rfix_compl frobGq).
  apply: pi_pnat (abelem_pgroup abelKq) _.
  by rewrite inE /= (charf_eq (char_Fp p_pr)).
rewrite -mxrank_eq0 (rfix_quo _ _ sRG) (rfix_morphim _ _ sRG).
rewrite (rfix_abelem _ _ _ (morphimS _ sRG)) mxrank_eq0 rowg_mx_eq0 -subG1.
rewrite (sub_abelem_rV_im _ _ _ (subsetIl _ _)) -(morphpreSK _ (subsetIl _ _)).
rewrite morphpreIim -gacentEsd gacent_actby gacentQ (setIidPr sRG) /=.
rewrite -coprime_quotient_cent ?(solvableS sXG) ?(subset_trans sRG) //.
  by rewrite {1}['C_X(R)](trivgP _) ?quotient1 ?sub1G // -regR setSI.
by apply: coprimeSg sXK _; exact: Frobenius_coprime frobG.
Qed.

Lemma coprime_mulpG_Hall : forall gT pi (G K R : {group gT}),
    K * R = G -> pi.-group K -> pi^'.-group R ->
  pi.-Hall(G) K /\ pi^'.-Hall(G) R.
Proof.
move=> gT pi G K R defG piK pi'R; apply/andP.
rewrite /pHall piK -!divgS /= -defG ?mulG_subl ?mulg_subr //= pnatNK.
by rewrite coprime_cardMg ?(pnat_coprime piK) // mulKn ?mulnK //; exact/and3P.
Qed.

Lemma coprime_mulGp_Hall : forall gT pi (G K R : {group gT}),
    K * R = G -> pi^'.-group K -> pi.-group R ->
  pi^'.-Hall(G) K /\ pi.-Hall(G) R.
Proof.
move=> gT pi G K R defG pi'K piR; apply/andP; rewrite andbC; apply/andP.
by apply: coprime_mulpG_Hall => //; rewrite -(comm_group_setP _) defG ?groupP.
Qed.

Lemma coprime_p'group : forall gT p (K R : {group gT}),
  coprime #|K| #|R| -> p.-group R -> R :!=: 1 -> p^'.-group K.
Proof.
move=> gT p K R coKR pR ntR; have [p_pr _ [e oK]] := pgroup_pdiv pR ntR.
by rewrite oK coprime_sym coprime_pexpl // prime_coprime // -p'natE in coKR.
Qed.

Lemma Sylow_Hall : forall gT pi p (G H P : {group gT}),
  pi.-Hall(G) H -> p \in pi -> p.-Sylow(H) P -> p.-Sylow(G) P.
Proof.
move=> gT pi p G H P hallH pi_p sylP; have [sHG piH _] := and3P hallH.
rewrite pHallE (subset_trans (pHall_sub sylP) sHG) /=.
by rewrite (card_Hall sylP) (card_Hall hallH) partn_part // => q; move/eqnP->.
Qed.

(* !! Hall lemma in the std library are too weak: subnormal does not require *)
(* solvability!.                                                             *)
Lemma Hall_subnormal : forall gT pi (G K H : {group gT}),
  K <| G -> pi.-Hall(G) H -> pi.-Hall(K) (H :&: K).
Proof.
move=> gT pi G K H nsKG hallH; have [sHG piH _] := and3P hallH.
have [sHK_H sHK_K] := (subsetIl H K, subsetIr H K).
rewrite pHallE sHK_K /= -(part_pnat_id (pgroupS sHK_H piH)); apply/eqP.
rewrite (widen_partn _ (subset_leq_card sHK_K)); apply: eq_bigr => p pi_p.
have [P sylP] := Sylow_exists p H.
have sylPK := pSylow_normalI nsKG (Sylow_Hall hallH pi_p sylP).
rewrite -!p_part -(card_Hall sylPK); symmetry; apply: card_Hall.
by rewrite (pHall_subl _ sHK_K) //= setIC setSI ?(pHall_sub sylP).
Qed.

Lemma coprime_mulG_setI_norm : forall gT (H G K R : {group gT}),
    K * R = G -> G \subset 'N(H) -> coprime #|K| #|R| ->
  (K :&: H) * (R :&: H) = G :&: H.
Proof.
move=> gT H G K R defG nHG coKR; apply/eqP; rewrite eqEcard mulG_subG /= -defG.
rewrite !setSI ?mulG_subl ?mulG_subr //=.
rewrite coprime_cardMg ?(coKR, coprimeSg (subsetIl _ _), coprime_sym) //=.
pose pi := \pi(#|K|); have piK: pi.-group K by exact: pnat_pi.
have pi'R: pi^'.-group R by rewrite /pgroup -coprime_pi'.
have [hallK hallR] := coprime_mulpG_Hall defG piK pi'R.
have nsHG: H :&: G <| G by rewrite /normal subsetIr normsI ?normG.
rewrite -!(setIC H) defG -(partnC pi (cardG_gt0 _)).
rewrite -(card_Hall (Hall_subnormal nsHG hallR)) /= setICA.
rewrite -(card_Hall (Hall_subnormal nsHG hallK)) /= setICA.
by rewrite -defG (setIidPl (mulG_subl _ _)) (setIidPl (mulG_subr _ _)).  
Qed.

(* This is B & G, Theorem 3.8. *)

Theorem odd_sdprod_primact_commg_sub_Fitting : forall gT (G K R : {group gT}),
    K ><| R = G -> odd #|G| -> solvable G ->
  (*1*) coprime #|K| #|R| ->
  (*2*) {in R^#, forall x, 'C_K[x] = 'C_K(R)} ->
  (*3*) 'C_('F(K))(R) = 1 ->
  [~: K, R] \subset 'F(K).
Proof.
move=> gT G; elim: {G}_.+1 {-2}G (ltnSn #|G|) => // n IHn G.
rewrite ltnS => leGn K R defG oddG solG coKR primR regR_F.
have [nsKG sRG defKR nKR tiKR] := sdprod_context defG.
have [sKG nKG] := andP nsKG.
have chF: 'F(K) \char K := Fitting_char K; have nFR := char_norm_trans chF nKR.
have nsFK := char_normal chF; have [sFK nFK] := andP nsFK.
pose KqF := K / 'F(K); have solK := solvableS sKG solG.
wlog [p p_pr pKqF]: / exists2 p, prime p & p.-group KqF.
  move=> IHp;  apply: wlog_neg => IH_KR; rewrite -quotient_cents2 //= -/KqF.
  set Rq := R / 'F(K); have nKRq: Rq \subset 'N(KqF) by exact: quotient_norms.
  rewrite centsC.
  apply: subset_trans (coprime_cent_Fitting nKRq _ _); last first.
  - exact: quotient_sol.
  - exact: coprime_morph.
  rewrite subsetI subxx centsC -['F(KqF)]Sylow_gen gen_subG.
  apply/bigcupsP=> Pq; case/SylowP=> p p_pr; rewrite /= -/KqF => sylPq.
  have chPq: Pq \char KqF.
   apply: char_trans (Fitting_char _); rewrite /= -/KqF.
    by rewrite (nilpotent_Hall_pcore (Fitting_nil _) sylPq) ?pcore_char.
  have [P defPq sFP sPK] := inv_quotientS nsFK (char_sub chPq).
  have nsFP: 'F(K) <| P by rewrite /normal sFP (subset_trans sPK).
  have{chPq} chP: P \char K.
    by apply: char_from_quotient nsFP (Fitting_char _) _; rewrite -defPq.
  have defFP: 'F(P) = 'F(K).
    apply/eqP; rewrite eqEsubset !Fitting_max ?Fitting_nil //.
    by rewrite char_normal ?(char_trans (Fitting_char _)).
  have coPR := coprimeSg sPK coKR.
  have nPR: R \subset 'N(P) := char_norm_trans chP nKR.
  pose G1 := P <*> R.
  have sG1G: G1 \subset G by rewrite /G1 -defKR norm_mulgenEr ?mulSg.
  have defG1: P ><| R = G1 by rewrite sdprodEgen ?coprime_TIg.
  rewrite defPq quotient_cents2r //= -defFP.
  have:= sPK; rewrite subEproper; case/predU1P=> [defP | ltPK].
    rewrite IHp // in IH_KR; exists p => //.
    by rewrite /KqF -{2}defP -defPq (pHall_pgroup sylPq).
  move/IHn: defG1 => ->; rewrite ?(oddSg sG1G) ?(solvableS sG1G) ?defFP //.
    apply: leq_trans leGn; rewrite /= norm_mulgenEr //.
    by rewrite -defKR !coprime_cardMg // ltn_pmul2r ?proper_card.
  by move=> x Rx; rewrite -(setIidPl sPK) -!setIA primR.
wlog r_pr: / prime #|R|; last set r := #|R| in r_pr.
  have [-> _ | [r r_pr]] := trivgVpdiv R; first by rewrite commG1 sub1G.
  case/Cauchy=> // x; rewrite -cycle_subG subEproper orderE; set X := <[x]>.
  case/predU1P=> [-> -> -> // | ltXR rX _]; have sXR := proper_sub ltXR.
  have defCX: 'C_K(X) = 'C_K(R).
    rewrite cent_cycle primR // !inE -order_gt1 orderE rX prime_gt1 //=.
    by rewrite -cycle_subG.
  have primX: {in X^#, forall y, 'C_K[y] = 'C_K(X)}.
    by move=> y; case/setD1P=> nty Xy; rewrite primR // !inE nty (subsetP sXR).
  have nKX := subset_trans sXR nKR; have coKX := coprimegS sXR coKR.
  pose H := K <*> X; have defH: K ><| X = H by rewrite sdprodEgen ?coprime_TIg.
  have sHG: H \subset G by rewrite /H -defKR norm_mulgenEr ?mulgSS.
  have ltHn: #|H| < n.
    rewrite (leq_trans _ leGn) /H ?norm_mulgenEr // -defKR !coprime_cardMg //.
    by rewrite ltn_pmul2l ?proper_card.
  have oddH := oddSg sHG oddG; have solH := solvableS sHG solG.
  have regX_F: 'C_('F(K))(X) = 1.
   by rewrite -regR_F -(setIidPl sFK) -!setIA defCX.
  have:= IHn _ ltHn _ _ defH oddH solH coKX primX regX_F.
  rewrite -!quotient_cents2 ?(subset_trans sXR) //; move/setIidPl <-.
  rewrite -coprime_quotient_cent ?(subset_trans sXR) // defCX.
  by rewrite coprime_quotient_cent ?subsetIr.
apply: subset_trans (chief_stab_sub_Fitting solG nsKG) => //.
rewrite subsetI commg_subl nKR; apply/bigcapsP => [[U V]] /=.
case/andP=> chiefUV sUF; set W := U / V.
have minW := chief_factor_minnormal chiefUV.
have [ntW nWG] := andP (mingroupp minW).
case/andP: (chiefUV); move/maxgroupp; do 2![case/andP]=> sVU _ nVG nsUG.
have sUK := subset_trans sUF sFK; have sVK := subset_trans sVU sUK.
have nVK := subset_trans sKG nVG; have nVR := subset_trans sRG nVG.
have [q q_pr abelW]: exists2 q, prime q & q.-abelem W.
  apply/is_abelemP; apply: charsimple_solvable (minnormal_charsimple minW) _.
  by rewrite quotient_sol // (solvableS sUK).
have regR_W: 'C_(W)(R / V) = 1.
  rewrite -coprime_quotient_cent ?(coprimeSg sUK) ?(solvableS sUK) //.
  by rewrite -(setIidPl sUF) -setIA regR_F (setIidPr _) ?quotient1 ?sub1G.
rewrite sub_astabQ comm_subG ?quotientR //=.
have defGv: (K / V) * (R / V) = G / V by rewrite -defKR quotientMl.
have oRv: #|R / V| = r.
  rewrite card_quotient // -indexgI -(setIidPr sVK) setICA setIA tiKR.
  by rewrite (setIidPl (sub1G _)) indexg1.
have defCW: 'C_(G / V)(W) = 'C_(K / V)(W).
  apply/eqP; rewrite eqEsubset andbC setSI ?quotientS //=.
  rewrite subsetI subsetIr /= andbT.
  rewrite -(coprime_mulG_setI_norm defGv) ?coprime_morph ?norms_cent //=.
  suffices ->: 'C_(R / V)(W) = 1 by rewrite mulg1 subsetIl.
  apply/trivgP; apply/subsetP=> x; case/setIP=> Rx cWx.
  apply: contraR ntW => ntx; rewrite -subG1 -regR_W subsetI subxx centsC /= -/W.
  by apply: contraR ntx; move/prime_TIg <-; rewrite ?oRv // inE Rx.
have [P sylP nPR] := coprime_Hall_exists p nKR coKR solK.
have [sPK pP _] := and3P sylP.
have nVP := subset_trans sPK nVK; have nFP := subset_trans sPK nFK.
have sylPv: p.-Sylow(K / V) (P / V) by rewrite quotient_pHall.
have defKv: (P / V) * 'C_(G / V)(W) = (K / V).
  rewrite defCW; apply/eqP; rewrite eqEsubset mulG_subG subsetIl quotientS //=.
  have sK_PF: K \subset P * 'F(K).
    rewrite (normC nFP) -quotientSK // subEproper eq_sym eqEcard quotientS //=.
    by rewrite (card_Hall (quotient_pHall nFP sylP)) part_pnat_id ?leqnn.
  rewrite (subset_trans (quotientS _ sK_PF)) // quotientMl // mulgS //.
  rewrite subsetI -quotient_astabQ !quotientS //.
  by rewrite (subset_trans (Fitting_stab_chief solG nsKG)) ?(bigcap_inf (U, V)).
have nW_ := subset_trans (quotientS _ _) nWG; have nWK := nW_ _ sKG. 
rewrite -quotient_cents2 ?norms_cent ?(nW_ _ sRG) //.
have [eq_qp | p'q] := eqVneq q p.
  apply: subset_trans (sub1G _); rewrite -trivg_quotient quotientS // centsC.
  apply/setIidPl; case/mingroupP: minW => _; apply; last exact: subsetIl.
  rewrite andbC normsI ?norms_cent // ?quotient_norms //=.
  have nsWK: W <| K / V by rewrite /normal quotientS.
  have sWP: W \subset P / V.
    by rewrite (normal_sub_max_pgroup (Hall_max sylPv)) -?eq_qp ?abelem_pgroup.
  rewrite -defKv centM setIA setIAC /=.
  rewrite ['C_W(_)](setIidPl _); last by rewrite centsC subsetIr.
  have nilPv: nilpotent (P / V) := pgroup_nil (pHall_pgroup sylPv).
  by rewrite -(setIidPl sWP) -setIA nil_meet_Z // (normalS _ (quotientS V sPK)).
rewrite -defKv -quotient_mulg -mulgA mulSGid ?subsetIr // quotient_mulg.
have sPG := subset_trans sPK sKG.
rewrite quotient_cents2 ?norms_cent ?nW_ //= commGC.
pose Hv := (P / V) <*> (R / V).
have sHGv: Hv \subset G / V by rewrite mulgen_subG !quotientS.
have solHv: solvable Hv := solvableS sHGv (quotient_sol V solG).
have sPHv: P / V \subset Hv by exact: mulgen_subl.
have nPRv: R / V \subset 'N(P / V) := quotient_norms _ nPR.
have coPRv: coprime #|P / V| #|R / V| := coprime_morph _ (coprimeSg sPK coKR).
apply: subset_trans (subsetIr (P / V) _).
have oHv: #|Hv| = (#|P / V| * #|R / V|)%N.
  by rewrite /Hv norm_mulgenEr // coprime_cardMg // oRv.
move/(odd_prime_sdprod_abelem_cent1 solHv): (abelW); apply=> //.
- exact: oddSg sHGv (quotient_odd _ _).
- by rewrite /normal sPHv mulgen_subG normG.
- by rewrite /Hall sPHv /= -divgS //= oHv mulKn ?cardG_gt0.
- by rewrite inE coprime_TIg ?eqxx //= norm_mulgenEr.
- by rewrite oRv.
- exact: subset_trans sHGv nWG.
rewrite oHv euclid //; apply/norP; split.
  by apply: contra p'q; exact: (pgroupP (pHall_pgroup sylPv)).
rewrite -p'natE //; apply: coprime_p'group (abelem_pgroup abelW) ntW.
by rewrite coprime_sym coprime_morph // (coprimeSg sUK).
Qed.

Lemma expgn_znat : forall gT (G : {group gT}) x k,
  x \in G -> x ^+ (k%:R : 'Z_(#|G|)) = x ^+ k.
Proof.
move=> gT G x k; case: (eqsVneq G 1) => [-> | ntG Gx].
  by move/set1P->; rewrite !exp1gn.
apply/eqP; rewrite val_Zp_nat ?cardG_gt1 // eq_expg_mod_order.
by rewrite modn_dvdm ?order_dvdG.
Qed.

Lemma natr_negZp : forall p' (p := p'.+2) (x : 'I_p), (- x)%:R = - x.
Proof. by move=> p' p x; apply: val_inj; rewrite /= Zp_nat /= modn_mod. Qed.

Lemma expgn_zneg : forall gT (G : {group gT}) x (k : 'Z_(#|G|)),
  x \in G -> x ^+ (- k) = x ^- k.
Proof.
move=> gT G x k Gx; apply/eqP; rewrite eq_sym eq_invg_mul -expgn_add.
by rewrite -(expgn_znat _ Gx) natr_add natr_Zp natr_negZp subrr.
Qed.

Lemma unitZpE : forall p x, p > 1 -> GRing.unit (x%:R : 'Z_p) = coprime p x.
Proof.
by move=> p x p_gt1; rewrite /GRing.unit /= val_Zp_nat ?Zp_cast ?coprime_modr.
Qed.

Lemma unitFpE : forall p x, prime p -> GRing.unit (x%:R : 'F_p) = coprime p x.
Proof. by move=> p x p_pr; rewrite pdiv_id // unitZpE // prime_gt1. Qed.

Lemma div1r : forall (R : unitRingType) (x : R), (1 / x = x^-1)%R.
Proof. by move=> R x; exact: mul1r. Qed.

Lemma coprimeSn : forall n, coprime n.+1 n.
Proof.
by move=> n; rewrite -coprime_modl (modn_addr 1) coprime_modl coprime1n.
Qed.

Lemma coprimenS : forall n, coprime n n.+1.
Proof. by move=> n; rewrite coprime_sym coprimeSn. Qed.

Lemma coprimePn : forall n, n > 0 -> coprime n.-1 n.
Proof. by case=> // n _; rewrite coprimenS. Qed.

Lemma coprimenP : forall n, n > 0 -> coprime n n.-1.
Proof. by case=> // n _; rewrite coprimeSn. Qed.

(* This is Aschbacher (23.3) *)
Lemma cyclic_pgroup_Aut_structure : forall gT p (G : {group gT}),
    p.-group G -> cyclic G -> G :!=: 1 ->
  let q := #|G| in let n := (logn p q).-1 in
  let A := Aut G in let P := 'O_p(A) in let F := 'O_p^'(A) in
  exists m : {perm gT} -> 'Z_q,
  [/\ [/\ {in A & G, forall a x, x ^+ m a = a x},
          m 1 = 1%R /\ {in A &, {morph m : a b / a * b >-> (a * b)%R}},
          {in A &, injective m} /\ [image m of A] =i GRing.unit,
          forall k, {in A, {morph m : a / a ^+ k >-> (a ^+ k)%R}}
        & {in A, {morph m : a / a^-1 >-> (a^-1)%R}}],
      [/\ abelian A, cyclic F, #|F| = p.-1 & [faithful F, on 'Ohm_1(G) | 'A_G]]
    & if n == 0%N then A = F
 else if odd p then
    [/\ cyclic P,
        exists b, [/\ b \in A, #[b] = (p ^ n)%N, m b = p.+1%:R & P = <[b]>]
      & exists b0, [/\ b0 \in A, #[b0] = p, m b0 = (p ^ n).+1%:R
                     & 'Ohm_1(P) = <[b0]>]]
 else exists c, [/\ c \in A, #[c] = 2, m c = - 1%R
    & if n == 1%N then A = <[c]>
 else exists b, [/\ b \in A, #[b] = (2 ^ n.-1)%N, m b = 5%:R, <[b]> \x <[c]> = A
    & exists b0, [/\ b0 \in A, m b0 = (2 ^ n).+1%:R, m (b0 * c) = (2 ^ n).-1%:R
                   & 'Ohm_1(<[b]>) = <[b0]>]]]].
Proof.
move=> gT p G pG cycG ntG q n0 A P F.
have [x0 defG] := cyclicP _ cycG; have Gx0: x0 \in G by rewrite defG cycle_id.
have [p_pr p_dvd_G [n oG]] := pgroup_pdiv pG ntG.
rewrite {1}/q oG pfactorK //= in n0 *; rewrite {}/n0.
have [p_gt1 min_p] := primeP p_pr; have p_gt0 := ltnW p_gt1.
have q_gt1: q > 1 by rewrite cardG_gt1.
have cAA: abelian A := Aut_cyclic_abelian cycG; have nilA := abelian_nil cAA.
have oA: #|A| = (p.-1 * p ^ n)%N by rewrite card_Aut_cyclic // oG phi_pfactor.
have [sylP hallF]: p.-Sylow(A) P /\ p^'.-Hall(A) F.
  by rewrite !nilpotent_pcore_Hall.
have [defPF tiPF]: P * F = A /\ P :&: F = 1.
  by case/dprodP: (nilpotent_pcoreC p nilA).
have oP: #|P| = (p ^ n)%N.
  by rewrite (card_Hall sylP) oA p_part logn_gauss ?coprimenP ?pfactorK.
have oF: #|F| = p.-1.
  apply/eqP; rewrite -(@eqn_pmul2l #|P|) ?cardG_gt0 // -TI_cardMg // defPF.
  by rewrite oA oP mulnC.
have [m' [inj_m' defA def_m']]: exists m' : {morphism units_Zp q >-> {perm gT}},
  [/\ 'injm m', m' @* setT = A & {in G, forall x u, m' u x = x ^+ val u}].
- rewrite /A /q defG; exists (Zp_unit_morphism x0).
  by have [->]:= isomP (Zp_unit_isom x0); split=> // y Gy u; rewrite permE Gy.
pose m (a : {perm gT}) : 'Z_q := val (invm inj_m' a).
have{def_m'} def_m: {in A & G, forall a x, x ^+ m a = a x}.
  by move=> a x Aa Gx /=; rewrite -{2}[a](invmK inj_m') ?defA ?def_m'.
have m1: m 1 = 1%R by rewrite /m morph1.
have mM: {in A &, {morph m : a b / a * b >-> (a * b)%R}}.
  by move=> a b Aa Ab; rewrite /m morphM ?defA.
have mX: forall k, {in A, {morph m : a / a ^+ k >-> (a ^+ k)%R}}.
  by elim=> // k IHk a Aa; rewrite expgS exprS mM ?groupX ?IHk.
have inj_m: {in A &, injective m}.
  apply: can_in_inj (fun u => m' (insubd (1 : {unit 'Z_q}) u)) _ => a Aa.
  by rewrite valKd invmK ?defA.
have{defA} im_m: [image m of A] =i GRing.unit.
  move=> u; apply/imageP/idP=> [[a Aa ->]| Uu]; first exact: valP.
  exists (m' (Sub u Uu)) => /=; first by rewrite -defA mem_morphim ?inE.
  by rewrite /m invmE ?inE.
have mV: {in A, {morph m : a / a^-1 >-> (a^-1)%R}}.
  move=> a Aa /=; rewrite -div1r; apply: canRL (mulrK (valP _)) _.
  by rewrite -mM ?groupV ?mulVg.
have inv_m: forall u : 'Z_q, coprime q u -> {a | a \in A & m a = u}.
  move=> u; rewrite -?unitZpE // natr_Zp -[_ u]im_m => m_u.
  by exists (iinv m_u); [exact: mem_iinv | rewrite f_iinv].
exists m; split=> {im_m mV}//.
  have Um0: forall a, GRing.unit ((m a)%:R : 'F_p).
    move=> a; have: GRing.unit (m a) by exact: valP.
    by rewrite -{1}[m a]natr_Zp unitFpE ?unitZpE // {1}/q oG coprime_pexpl.
  pose fm0 a : {unit 'F_p} := Sub _ (Um0 a).
  have natZqp: forall u, (u%:R : 'Z_q)%:R = u %:R :> 'F_p.
    by move=> u; rewrite val_Zp_nat // -Fp_nat_mod // modn_dvdm ?Fp_nat_mod.
  have m0M: {in A &, {morph fm0 : a b / a * b}}.
    move=> a b Aa Ab; apply: val_inj; rewrite /= -natr_mul mM //.
    by rewrite -[(_ * _)%R]Zp_nat natZqp.
  pose m0 : {morphism A >-> {unit 'F_p}} := Morphism m0M.
  have im_m0: m0 @* A = [set: {unit 'F_p}].
    apply/setP=> [[/= u Uu]]; rewrite in_setT morphimEdom; apply/imsetP.
    have [|a Aa m_a] := inv_m u%:R.
      by rewrite {1}[q]oG coprime_pexpl // -unitFpE // natZqp natr_Zp.
    by exists a => //; apply: val_inj; rewrite /= m_a natZqp natr_Zp.
  have [x1 defG1]: exists x1, 'Ohm_1(G) = <[x1]>.
    by apply/cyclicP; exact: cyclicS (Ohm_sub _ _) cycG.
  have ox1: #[x1] = p by rewrite orderE -defG1 (Ohm1_cyclic_pgroup_prime _ pG).
  have Gx1: x1 \in G by rewrite -cycle_subG -defG1 Ohm_sub.
  have ker_m0: 'ker m0 = 'C('Ohm_1(G) | 'A_G).
    apply/setP=> a; rewrite inE in_setI; apply: andb_id2l => Aa.
    rewrite 3!inE /= -2!val_eqE /= val_Fp_nat // [1 %% _]modn_small // defG1.
    apply/idP/subsetP=> [ma1 x1i | ma1].
      case/cycleP=> i ->{x1i}; rewrite inE gactX // -[_ a]def_m //.
      by rewrite -(expg_mod_order x1) ox1 (eqP ma1).
    have:= ma1 x1 (cycle_id x1); rewrite inE -[_ a]def_m //.
    by rewrite (eq_expg_mod_order x1 _ 1) ox1 (modn_small p_gt1).
  have card_units_Fp: #|[set: {unit 'F_p}]| = p.-1.
    by rewrite card_units_Zp // pdiv_id // (@phi_pfactor p 1) ?muln1.
  have ker_m0_P: 'ker m0 = P.
    apply: nilpotent_Hall_pcore nilA _.
    rewrite pHallE -(card_Hall sylP) oP subsetIl /=.
    rewrite -(@eqn_pmul2r #|m0 @* A|) ?cardG_gt0 //; apply/eqP.
    rewrite -{1}(isog_card (first_isog _)) card_quotient ?ker_norm //.
    by rewrite LaGrange ?subsetIl // oA im_m0 mulnC card_units_Fp.
  have inj_m0: 'ker_F m0 \subset [1] by rewrite setIC ker_m0_P tiPF.
  split=> //; last by rewrite /faithful -ker_m0.
  have isogF: F \isog [set: {unit 'F_p}].
    have sFA: F \subset A by exact: pcore_sub.
    apply/isogP; exists (restrm_morphism sFA m0); first by rewrite ker_restrm.
    apply/eqP; rewrite eqEcard subsetT card_injm ?ker_restrm //= oF.
    by rewrite card_units_Fp.
  rewrite (isog_cyclic isogF) pdiv_id // -ox1.
  by rewrite (isog_cyclic (Zp_unit_isog x1)) Aut_prime_cyclic // -orderE ox1.
case: posnP => [n0 | n_gt0].
  by apply/eqP; rewrite eq_sym eqEcard pcore_sub oF oA n0 muln1 /=.
have [c Ac mc]: {c | c \in A & m c = -1}.
  apply: inv_m; rewrite /= Zp_cast // coprime_modr modn_small // subn1.
  by rewrite coprimenP // ltnW.
have oc: #[c] = 2.
  apply/eqP; rewrite eqn_leq order_gt1 dvdn_leq ?order_dvdn //=.
    apply/eqP; move/(congr1 m); apply/eqP; rewrite mc m1 eq_sym -subr_eq0.
    rewrite opprK -val_eqE /= Zp_cast ?modn_small // /q oG ltnW //.
    by rewrite (leq_trans (_ : 2 ^ 2 <= p ^ 2)) ?leq_sqr ?leq_exp2l.
  by apply/eqP; apply: inj_m; rewrite ?groupX ?group1 ?mX // mc -signr_odd.
case G4: (~~ odd p && (n == 1%N)).
  case: (even_prime p_pr) G4 => [p2 | -> //]; rewrite p2 /=; move/eqP=> n1.
  exists c; split; rewrite ?n1 //=; apply/eqP; rewrite eq_sym eqEcard.
  by rewrite cycle_subG Ac -orderE oA oc p2 n1.
pose e0 : nat := ~~ odd p.
have{inv_m} [b Ab mb]: {b | b \in A & m b = (p ^ e0.+1).+1%:R}.
  apply: inv_m; rewrite val_Zp_nat // coprime_modr /q oG coprime_pexpl //.
  by rewrite -(@coprime_pexpl e0.+1) // coprimenS.
have le_e0_n: e0 < n.
  by rewrite /e0; case: (~~ _) G4 => //=; rewrite ltn_neqAle eq_sym => ->.
pose b0 := b ^+ (p ^ (n - e0.+1)).
have [mb0 ob0]: m b0 = (p ^ n).+1%:R /\ #[b0] = p.
  have m_be: forall e,
    exists2 k, k = 1 %[mod p] & m (b ^+ (p ^ e)) = (k * p ^ (e + e0.+1)).+1%:R.
  - elim=> [|e [k k1 IHe]]; first by exists 1%N; rewrite ?mul1n.
    rewrite expnSr expgn_mul mX ?groupX // {}IHe -natr_exp -(add1n (k * _)).
    rewrite expn_addl -(prednK p_gt0) 2!big_ord_recl /= prednK // !exp1n bin1.
    rewrite bin0 muln1 mul1n mulnCA -expnS (addSn e).
    set f := (e + _)%N; set s := (\sum_i _)%N.
    exists (s %/ p ^ f.+2 * p + k)%N; first by rewrite modn_addl_mul.
    rewrite -(addnC k) muln_addl -mulnA -expnS divnK // {}/s.
    apply big_prop => [||[i _] /= _]; [exact: dvdn0 | exact: dvdn_add |].
    rewrite exp1n mul1n /bump !add1n expn_mull mulnCA dvdn_mull // -expn_mulr.
    case: (ltnP f.+1 (f * i.+2)) => [le_f_fi|].
      by rewrite dvdn_mull ?dvdn_exp2l.
    rewrite {1}mulnS -(addn1 f) leq_add2l {}/f addnS /e0.
    case: i e => [] // [] //; case odd_p: (odd p) => //= _.
    by rewrite bin2odd // mulnAC dvdn_mulr.
  have [[|d]] := m_be (n - e0.+1)%N; first by rewrite mod0n modn_small.
  move/eqP; rewrite -/b0 eqn_mod_dvd ?subn1 //=; case/dvdnP=> f -> {d}.
  rewrite subnK // mulSn -mulnA -expnS -addSn natr_add natr_mul -oG char_Zp //.
  rewrite mulr0 addr0 => m_b0; split => //.
  have [d _] := m_be (n - e0)%N; rewrite ltn_subS // expnSr expgn_mul -/b0.
  rewrite addSn subnK // -oG  mulrS natr_mul char_Zp // {d}mulr0 addr0. 
  move/eqP; rewrite -m1 (inj_in_eq inj_m) ?group1 ?groupX // -order_dvdn.
  move/min_p; rewrite order_eq1; case/predU1P=> [b0_1 | ]; last by move/eqP.
  move/eqP: m_b0; rewrite eq_sym b0_1 m1 -subr_eq0 mulrSr addrK -val_eqE /=.
  have pf_gt0: p ^ _ > 0 by move=> e; rewrite expn_gt0 p_gt0.
  by rewrite val_Zp_nat // /q oG [_ == _]pfactor_dvdn // pfactorK ?ltnn.
have ob: #[b] = (p ^ (n - e0))%N.
  have: #[b] %| p ^ (n - e0).
    by rewrite order_dvdn ltn_subS // expnSr expgn_mul -order_dvdn ob0.
  case/dvdn_pfactor=> // d; rewrite leq_eqVlt.
  case/predU1P=> [-> // | lt_d ob]; case/idPn: (p_gt1); rewrite -ob0.
  by rewrite order_gt1 negbK -order_dvdn ob dvdn_exp2l // -ltnS -leq_subS.
have p_b: p.-elt b by rewrite /p_elt ob pnat_exp ?pnat_id.
have defB1: 'Ohm_1(<[b]>) = <[b0]>.
  apply/eqP; rewrite eq_sym eqEcard cycle_subG -orderE ob0.
  rewrite (Ohm1_cyclic_pgroup_prime _ p_b) ?cycle_cyclic ?leqnn ?cycle_eq1 //=.
    rewrite (OhmE _ p_b) mem_gen ?groupX //= inE mem_cycle //.
    by rewrite -order_dvdn ob0 ?dvdnn.
  by apply/eqP=> b1; rewrite -ob0 /b0 b1 exp1gn order1 in p_gt1.  
case: (even_prime p_pr) => [p2 | oddp]; last first.
  rewrite {+}/e0 oddp subn0 in b0 ob0 mb0 ob mb defB1 *.
  have ->: P = <[b]>.
    apply/eqP; rewrite eq_sym eqEcard -orderE oP ob leqnn andbT.
    by rewrite cycle_subG (mem_normal_Hall sylP) ?pcore_normal.
  by rewrite cycle_cyclic; split; [ | exists b | exists b0; rewrite ?groupX].
rewrite {+}/e0 p2 subn1 /= in b0 ob0 mb0 ob mb G4 defB1 le_e0_n *.
exists c; split=> //; rewrite G4; exists b; split=> //; last first.
  exists b0; split; rewrite ?groupX //; apply/eqP; rewrite mM ?groupX //.
  rewrite mb0 mc eq_sym mulrN1 -subr_eq0 opprK -natr_add -addSnnS.
  by rewrite prednK ?expn_gt0 // addnn -mul2n -expnS -p2 -oG char_Zp.
suffices TIbc: <[b]> :&: <[c]> = 1.
  rewrite dprodE //; last by rewrite (sub_abelian_cent2 cAA) ?cycle_subG.
  apply/eqP; rewrite eqEcard mulG_subG !cycle_subG Ab Ac oA.
  by rewrite TI_cardMg // -!orderE ob oc p2 mul1n /= -expnSr prednK.
rewrite setIC; apply: prime_TIg; first by rewrite -orderE oc.
rewrite cycle_subG; apply/negP=> Bc.
have: c \in <[b0]>.
  by rewrite -defB1 (OhmE _ p_b) mem_gen // inE Bc -order_dvdn oc p2.
have ->: <[b0]> = [set 1; b0].
  apply/eqP; rewrite eq_sym eqEcard subUset !sub1set group1 cycle_id /=.
  by rewrite -orderE cards2 eq_sym -order_gt1 ob0.
rewrite !inE -order_eq1 oc /=; move/eqP; move/(congr1 m); move/eqP.
rewrite mc mb0 eq_sym -subr_eq0 opprK -mulrSr.
rewrite -val_eqE [val _]val_Zp_nat //= /q oG p2 modn_small //.
by rewrite -addn3 expnS mul2n -addnn leq_add2l (ltn_exp2l 1).
Qed.

(* The odd case of Aschbacher (23.4), minus the actual construction of the   *)
(* modular group 'Mod_p^n.                                                   *)
Lemma extremal_odd_structure : forall gT p (G X : {group gT}),
    p.-group G -> X \subset G ->
    odd #|G| -> ~~ abelian G -> cyclic X -> #|G : X| = p ->
  let n := logn p #|G| in exists y,
  [/\ X ><| <[y]> = G, #[y] = p, n > 2
    & {in X, forall x, x ^ y = x ^+ (p ^ n.-2).+1}].
Proof.
move=> gT p G X pG sXG oddG not_cGG cycX iXp.
have ntG: G :!=: 1 by case: eqP not_cGG => // ->; rewrite abelian1.
have [p_pr _ [[|n] oG]] := pgroup_pdiv pG ntG.
  by rewrite cyclic_abelian // prime_cyclic ?oG in not_cGG.
have [p_gt1 min_p] := primeP p_pr; have p_gt0 := ltnW p_gt1.
have odd_p: odd p by rewrite oG odd_exp in oddG.
have n_gt0: n > 0 by case: n oG not_cGG => //; move/card_p2group_abelian->.
have [x defX] := cyclicP X cycX; have cXX := centsP (cyclic_abelian cycX).
have Xx: x \in X by rewrite defX cycle_id.
have pX := pgroupS sXG pG; have p_x := mem_p_elt pX Xx.
have [oX ox]: #|X| = (p ^ n.+1)%N /\ #[x] = (p ^ n.+1)%N.
  by rewrite orderE -defX -(setIidPr sXG) -divg_index oG iXp expnS mulKn.
have ntX: X :!=: 1 by rewrite -cardG_gt1 oX (ltn_exp2l 0).
have maxX: maximal X G by rewrite p_index_maximal ?iXp.
have nsXG: X <| G := p_maximal_normal pG maxX; have [_ nXG] := andP nsXG.
have XGp: forall y, y \in G -> y ^+ p \in X.
  move=> y Gy; apply: coset_idr; first by rewrite (subsetP nXG) ?groupX.
  apply/eqP; rewrite morphX ?(subsetP nXG) // -order_dvdn -iXp.
  by rewrite -card_quotient // order_dvdG ?mem_quotient.
have defG: forall y, y \in G -> y \notin X -> X * <[y]> = G.
  by move=> y Gy notXy; rewrite (mulg_normal_maximal nsXG) ?cycle_subG.
have [y0 Gy0 def_z]: exists2 y, y \in G & [~ x, y] = x ^+ (p ^ n).
  have [_ [y Gy notXy]] := properP _ _ (maxgroupp maxX).
  pose ay := conj_aut X y; have nXy: y \in 'N(X) := subsetP nXG y Gy.
  have [m []]:= cyclic_pgroup_Aut_structure pX cycX ntX.
  rewrite oX !pfactorK //= odd_p eqn0Ngt n_gt0 in m *; set A := Aut X.
  case=> def_m _ _ _ _ [cAA _ _ _] [_ _ [b [Ab ob m_b defAp1]]].
  have nt_ay: ay != 1.
    apply: contra not_cGG; move/eqP=> ay1; rewrite -(defG y) // abelianM defX.
    rewrite !cycle_abelian cycle_subG /= cent_cycle (sameP cent1P commgP).
    by apply/conjg_fixP; rewrite -(norm_conj_autE nXy Xx) -/ay ay1 perm1.
  have p_ay: p.-elt ay by rewrite morph_p_elt // (mem_p_elt pG).
  have sylAp: p.-Sylow(A) 'O_p(A) := nilpotent_pcore_Hall p (abelian_nil cAA).
  have [i def_ay]: exists i, ay = b ^+ i.
    apply/cycleP; rewrite -defAp1 (OhmE _ (pcore_pgroup _ _)) /= -/A mem_gen //.
    rewrite inE expn1 (mem_normal_Hall sylAp) ?pcore_normal ?Aut_aut // p_ay.
    apply/eqP; apply/permP=> u; rewrite -morphX //= perm1.
    case Xu: (u \in X); last by rewrite permE Xu.
    rewrite conj_autE ?XGp //; apply/conjg_fixP.
    by apply/commgP; apply: cXX; rewrite ?XGp.
  have co_b_i: coprime #[b] i.
    rewrite ob prime_coprime // -ob; apply: contra nt_ay => bi.
    by rewrite def_ay -order_dvdn.
  exists (y ^+ expgn_inv <[b]> i); first by rewrite groupX.
  rewrite /commg -(norm_conj_autE _ Xx) ?groupX // -def_m ?Aut_aut ?morphX //=.
  by rewrite -/ay def_ay expgnK ?cycle_id // m_b -oX expgn_znat // expgS mulKg.
set z := [~ x, y0] in def_z.
have oz: #[z] = p.
  by rewrite def_z orderXdiv ox ?dvdn_exp2l // expnS mulnK // expn_gt0 p_gt0.
have notXy0: y0 \notin X.
  apply: contraL p_gt1 => Xy0; rewrite -oz order_gt1 negbK; apply/commgP.
  exact: cXX.
have [j def_y0p]: exists j, y0 ^- p = x ^+ j.
  by apply/cycleP; rewrite -defX groupV XGp.
have [k def_j]: exists k, (j = k * p)%N.
  apply/dvdnP; apply: contraR not_cGG; rewrite -prime_coprime // => co_p_j.
  rewrite -(defG y0) // mulSGid ?cycle_abelian // defX cycle_subG.
  have{co_p_j} coXj: coprime #|X| j by rewrite oX coprime_expl.
  by rewrite -(expgnK coXj Xx) -def_y0p expVgn  groupV -!expgn_mul mem_cycle.
pose y := y0 * x ^+ k.
have Gy: y \in G by rewrite groupM // (subsetP sXG) ?groupX .
have notXy: y \notin X by rewrite groupMr // groupX.
have oy: #[y] = p.
  suffices: y ^+ p == 1.
    rewrite -order_dvdn; move/min_p; rewrite order_eq1.
    by case/predU1P=> [y1 | ]; [rewrite y1 group1 in notXy | move/eqP].
  have cxz: commute x z by rewrite def_z; exact: commuteX.
  have cy0z: commute y0 z.
    symmetry; apply/commgP; apply/conjg_fixP.
    rewrite def_z conjXg conjg_mulR -/z def_z -expgS -expgn_mul mulSnr.
    rewrite -expn_add expgn_add -{2}(prednK n_gt0) -addSnnS expn_add expgn_mul.
    by rewrite -ox expg_order exp1gn mul1g.
  rewrite expMg_Rmul commXg //; [|exact: commuteX2 | exact: commuteX].
  rewrite -2!expgn_mul -def_j -def_y0p -mulgA mulKVg -order_dvdn dvdn_mull //.
  by rewrite oz bin2odd ?dvdn_mulr.
rewrite oG pfactorK //; exists y; split=> // [|xe].
  rewrite sdprodE ?defG ?cycle_subG ?(subsetP nXG) //.
  by rewrite setIC prime_TIg ?cycle_subG -?orderE ?oy.
rewrite defX; case/cycleP=> e ->{xe}.
rewrite conjXg conjgM (conjg_mulR x) -/z def_z -expgS -expgn_mul mulnC.
by rewrite (conjg_fixP _) -?expgn_mul //; apply/commgP; exact: commuteX2.
Qed.

Lemma rank_cycle : forall gT (x : gT), 'r(<[x]>) = (x != 1).
Proof.
move=> gT x; case: eqP => [->|]; first by rewrite cycle1 rank1.
move/eqP=> ntx; apply/eqP; rewrite eqn_leq rank_gt0 cycle_eq1 ntx andbT.
by rewrite -grank_abelian ?cycle_abelian //= -(cards1 x) grank_min.
Qed.

Lemma abelian_rank1_cyclic :  forall gT (G : {group gT}),
  abelian G -> cyclic G = ('r(G) <= 1).
Proof.
move=> gT G cGG; have [b defG atypG] := abelian_structure cGG.
apply/idP/idP; first by case/cyclicP=> x ->; rewrite rank_cycle leq_b1.
rewrite -size_abelian_type // -{}atypG -{}defG unlock.
by case: b => [|x []] //= _; rewrite ?cyclic1 // dprodg1 cycle_cyclic.
Qed.

Lemma Ohm1_extremal_odd : forall gT (R : {group gT}) p x,
    p.-group R -> odd #|R| -> ~~ cyclic R -> x \in R -> #|R : <[x]>| = p ->
  ('Ohm_1(R))%G \in 'E_p^2(R).
Proof.
move=> gT R p x pR oddR ncycR Rx; set X := <[x]> => iXp; set R1 := 'Ohm_1(R).
have sXR: X \subset R by rewrite cycle_subG.
have ntR: R :!=: 1 by apply: contra ncycR; move/eqP->; exact: cyclic1.
have [p_pr _ [n oR]] := pgroup_pdiv pR ntR.
have sR1R: R1 \subset R by [rewrite Ohm_sub]; have pR1 := pgroupS sR1R pR.
suffices dimR2: logn p #|R1| = 2.
  by rewrite 2!inE sR1R abelem_Ohm1 // (p2group_abelian pR1) dimR2.
have [cRR | notcRR] := orP (orbN (abelian R)).
  apply/eqP; rewrite -p_rank_abelian // -rank_pgroup //= eqn_leq.
  rewrite andbC ltnNge -abelian_rank1_cyclic ?ncycR //=.
  have maxX: maximal X R by rewrite p_index_maximal ?iXp.
  have [_ [y Ry notXy]] := properP _ _ (maxgroupp maxX).
  have <-: #|[set x; y]| = 2.
    by rewrite cards2; case: eqP notXy => // ->; rewrite cycle_id.
  have defR: X * <[y]> = R.
    have nsXR: X <| R := p_maximal_normal pR maxX.
    by rewrite (mulg_normal_maximal nsXR) ?cycle_subG.
  rewrite -grank_abelian // -(genGid R) -defR genM_mulgen.
  by rewrite mulgen_idl mulgen_idr grank_min.
(* This entire segment is really the structure theorem for modular groups,  *)
(* i.e., Aschbacher ex. 8.2.                                                *)
have [y []] := extremal_odd_structure pR sXR oddR notcRR (cycle_cyclic x) iXp.
case/sdprod_context; rewrite /= -/X => nsXR sYR defR nXY tiXY oy.
rewrite oR pfactorK //= ltnS => n_gt1 defxy; have [_ nXR] := andP nsXR.
have{defxy} defxy: x ^ y = x ^+ (p ^ n.-1).+1 by rewrite defxy ?cycle_id.
have defrxy: [~ x, y] = x ^+ (p ^ n.-1) by rewrite /commg defxy expgS mulKg.
have Ry: y \in R by rewrite -cycle_subG. 
have [p_gt1 min_p] := primeP p_pr; have p_gt0 := ltnW p_gt1.
have n_gt0 := ltnW n_gt1; have n1 := prednK n_gt0.
have ox: #[x] = (p ^ n)%N.
  by apply/eqP; rewrite -(eqn_pmul2r p_gt0) -expnSr -{1}iXp LaGrange ?oR.
have cYXp: <[x ^+ p]> \subset 'C(<[y]>).
  rewrite cent_cycle cycle_subG (sameP cent1P commgP) /commg conjXg defxy.
  by rewrite -expgn_mul mulSn expgn_add mulKg -expnSr n1 -ox expg_order.
have oXp: #[x ^+ p] = (p ^ n.-1)%N.
  by rewrite orderXdiv ox ?dvdn_exp // -{1}n1 expnS mulKn.
have [sZR nZR] := andP (center_normal R).
have defZ: 'Z(R) = <[x ^+ p]>.
  apply/eqP; rewrite eq_sym eqEcard subsetI cycle_subG groupX //.
  rewrite -{1}defR centM subsetI cYXp cent_cycle cycle_subG groupX ?cent1id //=.
  have oZ := part_pnat_id (pgroupS sZR pR); rewrite p_part in oZ.
  rewrite -orderE oXp leqNgt -oZ ltn_exp2l // n1; apply: contra notcRR => geZn.
  rewrite (@center_cyclic_abelian _ R) ?center_abelian //.
  have: #|R / 'Z(R)| %| p.
    rewrite -(dvdn_pmul2l (cardG_gt0 'Z(R))) card_quotient // LaGrange //.
    by rewrite oR -oZ -expnSr dvdn_exp2l.
  move/min_p; case/pred2P=> oRZ; first by rewrite (card1_trivg oRZ) cyclic1.
  by rewrite prime_cyclic // oRZ.
have oZ: #|'Z(R)| = (p ^ n.-1)%N by rewrite defZ.
have Z_Xpn1: x ^+ (p ^ n.-1) \in 'Z(R).
  by rewrite -(subnKC n_gt1) expnS expgn_mul defZ mem_cycle.
have defR': R^`(1) = <[x ^+ (p ^ n.-1)]>.
  rewrite -defR -norm_mulgenEr // der1_mulgen_cycles defrxy //.
  by rewrite norm_mulgenEr // defR; case/setIP: Z_Xpn1.
have oR': #|R^`(1)| = p.
  by rewrite defR' -orderE orderXdiv ox -n1 ?dvdn_exp2l // expnS mulnK -?oXp.
have nil2_R: nil_class R = 2.
  apply/eqP; rewrite eqn_leq andbC ltnNge nil_class1 notcRR nil_class2.
  by rewrite defR' cycle_subG.
have defPhi: 'Phi(R) = 'Z(R).
  apply/eqP; rewrite eqEsubset andbC.
  rewrite {1}(Phi_mulgen pR) mulgenC {1}defZ genS //; last first.
    by rewrite sub1set inE (Mho_p_elt 1) // (mem_p_elt pR).
  have nZPhi := subset_trans (Phi_sub R) nZR.
  rewrite -quotient_sub1 //= (quotient_Phi pR) // subG1.
  have pRq := quotient_pgroup 'Z(R) pR.
  rewrite (trivg_Phi pRq); apply/abelem_Ohm1P => //.
    by rewrite sub_der1_abelian // -nil_class2 nil2_R.
  apply/eqP; rewrite eqEsubset Ohm_sub /= (OhmE _ pRq) /=.
  rewrite defZ -{1}defR -defZ quotientMr ?(subset_trans sYR) // mulG_subG /=.
  rewrite !quotient_cycle ?(subsetP nZR) ?genS ?sub1set ?inE ?mem_quotient //=.
    by rewrite -morphX ?(subsetP nZR) // -oy expg_order morph1.
  by rewrite -morphX ?(subsetP nZR) //= defZ coset_id ?cycle_id.
have defRn1: #|R| != 8 -> <[x ^+ p]> \x <[y]> = 'Ohm_(n.-1)(R).
  move=> notMod8; rewrite dprodEgen //=; last first.
    by apply/trivgP; rewrite -tiXY setSI ?cycleX.
  apply/eqP; rewrite (OhmE _ pR) eqEsubset mulgen_subG -oXp.
  have ypn1: forall u, u \in <[y]> -> u ^+ #[x ^+ p] = 1.
    move=> u Yu; apply/eqP; rewrite -order_dvdn (dvdn_trans (order_dvdG Yu)) //.
    by rewrite -orderE oy oXp -(subnKC n_gt1) expnS dvdn_mulr.
  rewrite !cycle_subG ?mem_gen ?inE ?groupX ?Ry ?expg_order ?ypn1 ?cycle_id //=.
  rewrite gen_subG /= cent_mulgenEl // -defR; apply/subsetP=> uv; case/setIdP.
  case/imset2P=> u v Xu Yv ->{uv}.
  have Ru := subsetP sXR u Xu; have Rv := subsetP sYR v Yv.
  have R'r: [~ v, u] \in R^`(1) by rewrite mem_commg.
  have Zr: [~ v, u] \in 'Z(R) by apply: subsetP R'r; rewrite -nil_class2 nil2_R.
  have crR: centralises [~ v, u] R by apply/centP; case/setIP: Zr.
  rewrite expMg_Rmul /commute ?crR // (ypn1 v Yv) oXp.
  rewrite (([~ v, u] ^+ _ =P 1) _) ?mulg1 => [upn1|]; last first.
    rewrite -order_dvdn (dvdn_trans (order_dvdG R'r)) // oR'.
    case: (even_prime p_pr) => [p2 | odd_p]; last first.
      by rewrite -(subnKC n_gt1) bin2odd ?odd_exp // expnS !dvdn_mulr.
    move: n_gt1; rewrite leq_eqVlt; case/predU1P=> [n2 | ].
      by rewrite oR p2 -n2 in notMod8.
    by move/subnKC=> <-; rewrite bin2 p2 !expnS -!mulnA mul2n doubleK dvdn_mulr.
  apply: mem_mulg Yv; have pX := pgroupS sXR pR; have px := mem_p_elt pR Rx.
  have: u \in 'Ohm_(n.-1)(X) by rewrite (OhmE _ pX) mem_gen // inE Xu.
  by rewrite (Ohm_p_cycle _ px) ox pfactorK // -n1 subSnn.
have defRi: #|R| != 8 -> forall i,
  0 < i < n -> <[x ^+ (p ^ (n - i))]> \x <[y]> = 'Ohm_i(R).
- move=> notMod8 i; rewrite -{1}n1 ltnS; case/andP=> i_gt0 le_i_n1.
  have:= Ohm_dprod i (defRn1 notMod8); have p_xp := mem_p_elt pR (groupX p Rx).
  rewrite (Ohm_p_cycle _ p_xp) oXp pfactorK // -expgn_mul -expnS -leq_subS //.
  rewrite n1 (Ohm_p_cycle _ (mem_p_elt pR Ry)) oy (pfactorK 1) // (eqnP i_gt0).
  move->; apply/eqP; rewrite eqEsubset OhmS ?Ohm_sub //=.
  by rewrite -{1}Ohm_id OhmS ?Ohm_leq.
(* finally completing the task at hand... *)
have notMod8: #|R| != 8 by case: eqP oddR => // ->.
rewrite /R1; case/dprodP: (defRi notMod8 1%N n_gt1) => /= _ <- _ tiXY1.
by rewrite TI_cardMg // subn1 /= -defR' oR' -orderE oy (pfactorK 2).
Qed.

(* Replacement for Section 4 proof. *)
Lemma odd_pgroup_rank1_cyclic : forall gT p (G : {group gT}),
  p.-group G -> odd #|G| -> cyclic G = ('r_p(G) <= 1).
Proof.
move=> gT p G pG oddG; apply/idP/idP=> [cycG | dimG1].
  have cGG := cyclic_abelian cycG; rewrite p_rank_abelian //.
  by rewrite -abelem_cyclic ?(cyclicS (Ohm_sub _ _)) ?Ohm1_abelem.
elim: {G}_.+1 {-2}G (ltnSn #|G|) => // n IHn G leGn in pG oddG dimG1 *.
apply: contraLR (dimG1) => ncycG; rewrite -ltnNge.
have ntG: G :!=: 1 by case: eqP ncycG => // ->; rewrite cyclic1.
have [X maxX _]: {X : {group gT} | maximal X G & [1] \subset X}.
  by apply: maxgroup_exists; rewrite proper1G.
have ltXG := maxgroupp maxX; have sXG := proper_sub ltXG.
have iXp: #|G : X| = p := p_maximal_index pG maxX.
have{n IHn leGn} [x defX]: exists x, X :=: <[x]>.
  apply/cyclicP; apply: IHn; rewrite ?(pgroupS sXG) ?(oddSg sXG) //.
    exact: leq_trans (proper_card ltXG) _.
  by apply: leq_trans dimG1; exact: p_rankS.
rewrite defX cycle_subG in sXG iXp.
by apply/p_rank_geP; exists 'Ohm_1(G)%G; exact: Ohm1_extremal_odd iXp.
Qed.

(* This is B & G, Theorem 3.9 (for external action), with the incorrectly *)
(* omitted nontriviality assumption reinstated.                           *)
Theorem ext_odd_regular_pgroup_cyclic : forall (aT rT : finGroupType) p,
    forall (D R : {group aT}) (K H : {group rT}) (to : groupAction D K),
    p.-group R -> odd #|R| -> H :!=: 1 ->
    {acts R, on group H | to} -> {in R^#, forall x, 'C_(H | to)[x] = 1} ->
  cyclic R.
Proof.
move=> aT rT p D R0 K H0 to pR0 oddR0 ntH0 actsR0 regR0.
pose gT := sdprod_groupType <[actsR0]>.
pose H : {group gT} := (sdpair1 <[actsR0]> @* H0)%G.
pose R : {group gT} := (sdpair2 <[actsR0]> @* R0)%G.
pose G : {group gT} := [set: gT]%G.
have{pR0} pR: p.-group R by rewrite morphim_pgroup.
have{oddR0} oddR: odd #|R| by rewrite morphim_odd.
case: (eqsVneq R 1) => [R1 | ntR].
  by rewrite -(im_invm (injm_sdpair2 <[actsR0]>)) {2}R1 morphim1 cyclic1.
have{ntH0} ntH: H :!=: 1.
  apply: contra ntH0; move/eqP => H1.
  by rewrite -(im_invm (injm_sdpair1 <[actsR0]>)) {2}H1 morphim1.
have{regR0 ntR} frobG: {Frobenius G = H ><| R}.
  apply/Frobenius_semiregularP => // [|x]; first exact: sdprod_sdpair.
  case/setD1P=> nt_x; case/morphimP=> x2 _ Rx2 def_x.
  apply/trivgP; rewrite -(morphpreSK _ (subsetIl _ _)) morphpreI.
  rewrite /= -cent_cycle def_x -morphim_cycle // -gacentEsd.
  rewrite injmK ?injm_sdpair1 // (trivgP (injm_sdpair1 _)).
  rewrite -(regR0 x2) ?inE ?Rx2 ?andbT; last first.
    by apply: contra nt_x; rewrite def_x; move/eqP->; rewrite morph1.
  have [sRD sHK]: R0 \subset D /\ H0 \subset K by case actsR0; move/acts_dom.
  have sx2R: <[x2]> \subset R0 by rewrite cycle_subG.
  rewrite gacent_actby setIA setIid (setIidPr sx2R).
  rewrite !gacentE ?cycle_subG ?sub1set ?(subsetP sRD) //.
  by rewrite !setIS ?afixS ?sub_gen.
suffices: cyclic R by rewrite (injm_cyclic (injm_sdpair2 _)).
move: gT H R G => {aT rT to D K H0 R0 actsR0} gT H R G in ntH pR oddR frobG *.
have [_ defG] := frobG; case/sdprodP: defG => _ _ nHR _.
have coHR := Frobenius_coprime frobG.
rewrite (odd_pgroup_rank1_cyclic pR oddR) leqNgt; apply: contra ntH.
case/p_rank_geP=> E; rewrite 2!inE -andbA; case/and3P=> sER abelE dimE2.
have ncycE: ~~ cyclic E by rewrite (abelem_cyclic abelE) (eqP dimE2).
have nHE := subset_trans sER nHR; have coHE := coprimegS sER coHR.
rewrite -subG1 (coprime_abelian_gen_cent1 _ _ nHE) ?(abelem_abelian abelE) //.
rewrite big1 // => x; case/setD1P=> nt_x Ex; apply: val_inj => /=.
by apply: (Frobenius_reg_ker frobG); rewrite !inE nt_x (subsetP sER).
Qed.

(* Internal action version or 3.9 (possibly, the only one we should keep). *)
Theorem odd_regular_pgroup_cyclic : forall gT p (H R : {group gT}),
    p.-group R -> odd #|R| -> H :!=: 1 -> R \subset 'N(H) ->
    {in R^#, forall x, 'C_(H)[x] = 1} ->
  cyclic R.
Proof.
move=> gT p H R pR oddR ntH nHR regR.
have actsR: {acts R, on group H | 'J} by split; rewrite ?subsetT ?astabsJ.
apply: ext_odd_regular_pgroup_cyclic pR oddR ntH actsR _ => // x Rx.
by rewrite gacentJ cent_set1 regR.
Qed.

Lemma regular_norm_coprime : forall gT (H R : {group gT}),
  R \subset 'N(H) -> {in R^#, forall x, 'C_(H)[x] = 1} -> coprime #|H| #|R|.
Proof.
move=> gT H R nHR regR; suffices dvR_H1: #|R| %| #|H|.-1.
  by apply: coprime_dvdr dvR_H1 _; rewrite coprimenP.
have actsR: [acts R, on H^# | 'J] by rewrite astabsJ normD1.
rewrite (cardsD1 1 H) group1 -(acts_sum_card_orbit actsR) /=.
rewrite (eq_bigr (fun _ => #|R|)) ?sum_nat_const ?dvdn_mull // => xR.
case/imsetP=> x; case/setIdP=> ntx Hx ->; rewrite card_orbit astab1J.
rewrite ['C_R[x]](trivgP _) ?indexg1 //=.
apply/subsetP=> y; case/setIP=> Ry cxy; apply: contraR ntx => nty.
by rewrite -[[set 1]](regR y) inE ?nty // Hx cent1C.
Qed.

(* Another variant of the internal action, which avoids Frobenius groups     *)
(* altogether.                                                               *)
Theorem simple_odd_regular_pgroup_cyclic : forall gT p (H R : {group gT}),
    p.-group R -> odd #|R| -> H :!=: 1 -> R \subset 'N(H) ->
    {in R^#, forall x, 'C_(H)[x] = 1} ->
  cyclic R.
Proof.
move=> gT p H R pR oddR ntH nHR regR.
rewrite (odd_pgroup_rank1_cyclic pR oddR) leqNgt; apply: contra ntH.
case/p_rank_geP=> E; rewrite 2!inE -andbA; case/and3P=> sER abelE dimE2.
have ncycE: ~~ cyclic E by rewrite (abelem_cyclic abelE) (eqP dimE2).
have nHE := subset_trans sER nHR.
have coHE := coprimegS sER (regular_norm_coprime nHR regR).
rewrite -subG1 (coprime_abelian_gen_cent1 _ _ nHE) ?(abelem_abelian abelE) //.
rewrite big1 // => x; case/setD1P=> nt_x Ex; apply: val_inj => /=.
by rewrite regR // !inE nt_x (subsetP sER).
Qed.

Theorem solvable_Wielandt_fixpoint : forall (I : finType) gT,
    forall (A : I -> {group gT}) (n m : I -> nat) (G V : {group gT}),
    (forall i, m i + n i > 0 -> A i \subset G) ->
    G \subset 'N(V) -> coprime #|V| #|G| -> solvable V ->
    {in G, forall a, \sum_(i | a \in A i) m i = \sum_(i | a \in A i) n i}%N ->
  (\prod_i #|'C_V(A i)| ^ (m i * #|A i|)
    = \prod_i #|'C_V(A i)| ^ (n i * #|A i|))%N.
Admitted.

Section Wielandt_Frobenius.

Variables (gT : finGroupType) (G K R : {group gT}).
Implicit Type A : {group gT}.

CoInductive Frobenius_Wielandt_cover_spec : Type :=
  FrobeniusWielandtCover (Dm := [set 1%G; G]) (Dn := K |: orbit 'JG K R)
    (m := [fun A => 0%N with 1%G |-> #|K|, G |-> 1%N])
    (n := fun A => (A \in Dn) : nat)
  of (forall A, m A + n A > 0 -> A \subset G)
   & {in G, forall a, \sum_(A : {group gT} | a \in A) m A
                       = \sum_(A : {group gT} | a \in A) n A}%N
   & {in [predC Dm], forall A, m A = 0%N} & G != 1%G
   & {in [predC Dn], forall A, n A = 0%N} &  K \notin (orbit 'JG K R).

Lemma Frobenius_Wielandt_cover :
  {Frobenius G = K ><| R} -> Frobenius_Wielandt_cover_spec.
Proof.
move=> frobG; have [frobGR defG] := frobG; have ntR: R :!=: 1 by case: frobGR.
move/Frobenius_TI_SN_P: frobGR; case/and3P=> ltRG _; move/eqP=> snRG.
have [nsKG sRG _ _ tiKR] := sdprod_context defG; have [sKG _] := andP nsKG.
pose m0 (_ : {group gT}) := 0%N.
pose Dm := [set 1%G; G]; pose Dn := K |: orbit 'JG K R.
pose m := [fun A => 0%N with 1%G |-> #|K|, G |-> 1%N].
pose n A : nat := A \in Dn.
have m_out: {in [predC Dm], m =1 m0}.
  by move=> A; rewrite !inE /=; case/norP; do 2!move/negbTE->.
have n_out: {in [predC Dn], n =1 m0}.
  by rewrite /n => A /=; move/negbTE=> /= ->.
have ntG: G != 1%G by rewrite -proper1G (sub_proper_trans (sub1G R)).
have neqKR: K \notin orbit 'JG K R.
  apply/imsetP=> [[x _ defK]]; have:= Frobenius_dvd_ker1 frobG.
  by rewrite defK cardJg gtnNdvd // ?prednK // -subn1 subn_gt0 cardG_gt1.
split=> //= [A | a Ga].
  case: eqP => [-> | ] _; first by rewrite sub1G.
  rewrite 2!inE; do 2!case: eqP => [-> // | ] _.
  case R_A: (A \in _) => // _; case/imsetP: R_A => x Kx ->{A}.
  by rewrite conj_subG ?(subsetP sKG).
case: (eqVneq a 1) => [-> | nt_a].
  rewrite (bigD1 1%G) ?inE ?eqxx //= (bigD1 G) ?inE ?group1 //=.
  rewrite (negbTE ntG) eqxx big1 ?addn1 => [|A]; last first.
    by rewrite group1 -negb_or -in_set2; exact: m_out.
  rewrite (bigID (mem Dn)) /= addnC big1 => [|A]; last first.
    by rewrite group1; exact: n_out.
  transitivity #|Dn|.
    rewrite cardsU1 neqKR card_orbit astab1JG.
    by rewrite -{3}(setIidPl sKG) -setIA snRG tiKR indexg1.
  by rewrite -sum1_card; apply: eq_big => [A | A ->]; rewrite ?group1.
rewrite (bigD1 G) //= (negbTE ntG) eqxx big1 => [|A]; last first.
  case/andP=> Aa neAG; apply: m_out; rewrite !inE; case: eqP => // A1.
  by rewrite A1 inE (negbTE nt_a) in Aa.
have [partG tiG _] := and3P (Frobenius_partition frobG).
do [rewrite -(eqP partG); set pG := _ |: _] in Ga tiG; pose A := cover_at a pG.
rewrite (bigD1 <<A>>%G) /=; last by rewrite mem_gen // mem_cover_at.
rewrite big1 => [|B]; last first.
  case/andP=> Ba neqBA; rewrite -/(false : nat); congr (nat_of_bool _).
  apply: contraTF neqBA; rewrite negbK -val_eqE /=.
  case/setU1P=> [BK |]; last case/imsetP=> x Kx defB.
    rewrite BK -(cover_at_eq _ tiG) ?Ga -/A ?setU11 //= in Ba.
    by rewrite BK (eqP Ba) genGid.
  have Rx_a: a \in R^# :^ x by rewrite conjD1g !inE nt_a -(congr_group defB).
  rewrite -(cover_at_eq _ tiG) ?Ga -/A /= ?inE ?mem_imset ?orbT // in Rx_a.
  by rewrite defB (eqP Rx_a) /= conjD1g genD1 ?group1 // genGid.
rewrite /A !inE -val_eqE /= -/(true : nat); congr ((_ : bool) + _)%N.
case/setU1P: (cover_at_mem Ga) => [-> |]; first by rewrite genGid eqxx.
case/imsetP=> x Kx ->; symmetry; apply/orP; right; apply/imsetP; exists x => //.
by apply: val_inj; rewrite conjD1g /= genD1 ?group1 // genGid.
Qed.

Lemma Frobenius_Wielandt_fixpoint : forall M : {group gT},
    {Frobenius G = K ><| R} ->
    G \subset 'N(M) -> coprime #|M| #|G| -> solvable M ->
 [/\ (#|'C_M(G)| ^ #|R| * #|M| = #|'C_M(R)| ^ #|R| * #|'C_M(K)|)%N,
     'C_M(R) = 1 -> K \subset 'C(M)
   & 'C_M(K) = 1 -> (#|M| = #|'C_M(R)| ^ #|R|)%N].
Proof.
move=> M frobG nMG coMG solM; have [_ defG] := frobG.
have [Dm Dn m n Gmn partG out_m ntG out_n notK_R] :=
  Frobenius_Wielandt_cover frobG.
move/eqP: (solvable_Wielandt_fixpoint Gmn nMG coMG solM partG).
rewrite (bigD1 1%G) // (bigD1 G) //= eqxx (setIidPl (cents1 _)) cards1 muln1.
rewrite (negbTE ntG) eqxx mul1n -(sdprod_card defG) (mulnC #|K|) expn_mulr.
rewrite mulnA -expn_mull big1 ?muln1 => [|A]; last first.
  by rewrite -negb_or -in_set2; move/out_m; rewrite /m => /= ->.
rewrite mulnC eq_sym (bigID (mem Dn)) /= mulnC.
rewrite big1 ?mul1n => [|A]; last by move/out_n->.
rewrite big_setU1 //= /n setU11 mul1n.
rewrite (eq_bigr (fun _ => #|'C_M(R)| ^ #|R|)%N) => [|A R_A]; last first.
  rewrite inE R_A orbT mul1n; case/imsetP: R_A => x Kx ->.
  suffices nMx: x \in 'N(M) by rewrite -{1}(normP nMx) centJ -conjIg !cardJg.
  have [] := sdprod_context defG; case/andP=> sKG _ _ _ _ _.
  exact: subsetP (subsetP sKG x Kx).
rewrite mulnC prod_nat_const card_orbit astab1JG.
have ->: 'N_K(R) = 1.
  have [] := frobG; move/Frobenius_TI_SN_P; case/and3P=> _ _; move/eqP=> snRG.
  case/sdprod_context; case/andP=> sKG _ _ _ _ tiKR.
  by rewrite -(setIidPl sKG) -setIA snRG tiKR.
rewrite indexg1 -expn_mull eq_sym eqn_exp2r ?cardG_gt0 //; move/eqP=> eq_fix.
split=> // [regR | regK].
  rewrite centsC (sameP setIidPl eqP) eqEcard subsetIl /=.
  move: eq_fix; rewrite regR cards1 exp1n mul1n => <-.
  suffices ->: 'C_M(G) = 1 by rewrite cards1 exp1n mul1n.
  by apply/trivgP; rewrite -regR setIS ?centS //; case/sdprod_context: defG.
move: eq_fix; rewrite regK cards1 muln1 => <-.
suffices ->: 'C_M(G) = 1 by rewrite cards1 exp1n mul1n.
apply/trivgP; rewrite -regK setIS ?centS //.
by case/sdprod_context: defG; case/andP.
Qed.

End Wielandt_Frobenius.

(* This is B & G, Theorem 3.10. *)
Theorem Frobenius_primact : forall gT (G K R M : {group gT}),
    {Frobenius G = K ><| R} -> solvable G ->
    G \subset 'N(M) -> solvable M -> M :!=: 1 ->
  (*1*) coprime #|M| #|G| ->
  (*2*) {in R^#, forall x, 'C_M[x] = 'C_M(R)} ->
  (*3*) 'C_M(K) = 1 ->
  [/\ prime #|R|,
      #|M| = (#|'C_M(R)| ^ #|R|)%N
    & cyclic 'C_M(R) -> K^`(1) \subset 'C_K(M)].
Proof.
move=> gT G K R M; move: {2}_.+1 (ltnSn #|M|) => n.
elim: n => // n IHn in gT G K R M *; rewrite ltnS => leMn.
move=> frobG solG nMG solM ntM coMG primRM tcKM.
case: (Frobenius_Wielandt_fixpoint frobG nMG) => // _ _; move/(_ tcKM)=> oM.
have ntK: K :!=: 1.
  have [] := frobG; move/Frobenius_TI_SN_P; do 2![case/andP]=> _ notsGR _.
  case/sdprodP=> _ defKR _ _; apply: contra notsGR.
  by rewrite -defKR; move/eqP->; rewrite mul1g.  
have Rpr: prime #|R|.
  have [R1 | [r r_pr]] := trivgVpdiv R.
    by case: frobG => [[_ _ _ _ _ _ ntR _]]; case/eqP: ntR.
  case/Cauchy=> // x Rx ox; pose R0 := <[x]>; pose G0 := K <*> R0.
  have [_ defG] := frobG; have [_ defKR nKR tiKR] := sdprodP defG.
  have sR0R: R0 \subset R by rewrite cycle_subG.
  have sG0G: G0 \subset G by rewrite /G0 -genM_mulgen gen_subG -defKR mulgS.
  have nKR0 := subset_trans sR0R nKR; have nMG0 := subset_trans sG0G nMG.
  have ntx: <[x]> != 1 by rewrite cycle_eq1 -order_gt1 ox prime_gt1.
  case: (eqVneq 'C_M(R) 1) => [tcRM | ntcRM].
    by rewrite -cardG_gt1 oM tcRM cards1 exp1n in ntM.
  have frobG0: {Frobenius G0 = K ><| R0}.
    apply/Frobenius_semiregularP=> // [|y].
      by apply: sdprodEgen nKR0 (trivgP _); rewrite -tiKR setIS.
    case/setD1P=> nty x_y; apply: (Frobenius_reg_ker frobG).
    by rewrite !inE nty (subsetP sR0R).
  case: (Frobenius_Wielandt_fixpoint frobG0 nMG0 (coprimegS _ coMG)) => // _ _.
  move/(_ tcKM); move/eqP; rewrite oM cent_cycle.
  rewrite primRM; last by rewrite !inE Rx andbT -cycle_eq1.
  by rewrite eqn_exp2l ?cardG_gt1 // -orderE ox; move/eqP->.
split=> // cyc_cMR.
have nM_MG: M <*> G \subset 'N(M) by rewrite mulgen_subG normG.
have [V minV sVM] := minnormal_exists ntM nM_MG.
have [] := minnormal_solvable minV sVM solM.
rewrite mulgen_subG; case/andP=> nVM nVG ntV; case/is_abelemP=> [q q_pr abelV].
have coVG := coprimeSg sVM coMG; have solV := solvableS sVM solM.
have cVK': K^`(1) \subset 'C_K(V).
  case: (eqVneq 'C_V(R) 1) => [tcVR | ntcRV].
    case: (Frobenius_Wielandt_fixpoint frobG nVG) => // _.
    by move/(_ tcVR)=> cVK _; rewrite (setIidPl cVK) der_sub.
  case/prime_FrobeniusP: frobG => //.
  case/sdprod_normal_compl=> nsKG; rewrite complgC => complR regR.
  have ocVR: #|'C_V(R)| = q.
    have [u def_u]: exists u, 'C_V(R) = <[u]>.
      by apply/cyclicP; apply: cyclicS (setSI _ sVM) cyc_cMR.
    move: ntcRV; rewrite def_u -orderE cycle_eq1.
    by case/(abelem_order_p abelV) => //; rewrite -cycle_subG -def_u subsetIl.
  apply: (Frobenius_prime_cent_prime _ nsKG complR _ _ abelV) => //.
  by rewrite -prime_coprime // -ocVR (coprimeSg (subsetIl _ _)).
have cMK': K^`(1) / V \subset 'C_(K / V)(M / V).
  case: (eqVneq (M / V) 1) => [-> | ntMV].
    by rewrite subsetI cents1 quotientS ?der_sub.
  have coKR := Frobenius_coprime frobG.
  case/prime_FrobeniusP: frobG => //.
  case/sdprod_context=> nsKG sRG defKR nKR tiKR regR; have [sKG _] := andP nsKG.
  have nVK := subset_trans sKG nVG; have nVR := subset_trans sRG nVG.
  have RVpr: prime #|R / V|.
    rewrite card_quotient // -indexgI setIC coprime_TIg ?(coprimegS sRG) //.
    by rewrite indexg1.
  have frobGV: {Frobenius G / V = (K / V) ><| (R / V)}.
    apply/prime_FrobeniusP; rewrite // -?cardG_gt1 ?card_quotient //.
      rewrite -indexgI setIC coprime_TIg ?(coprimegS sKG) //.
      by rewrite indexg1 cardG_gt1.
    rewrite -coprime_norm_quotient_cent ?(coprimegS sRG) //= regR quotient1.
    rewrite -defKR quotientMl // sdprodE ?quotient_norms //.
    by rewrite coprime_TIg ?coprime_morph.
  have ltMVn: #|M / V| < n by apply: leq_trans leMn; rewrite ltn_quotient.
  rewrite quotient_der //; move/IHn: frobGV.
  case/(_ _ ltMVn); rewrite ?quotient_sol ?quotient_norms ?coprime_morph //.
  - move=> Vx; case/setD1P=> ntVx; case/morphimP=> x nVx Rx defVx.
    rewrite defVx /= -cent_cycle -quotient_cycle //; congr 'C__(_ / V).
    apply/eqP; rewrite eqEsubset cycle_subG Rx /=.
    apply: contraR ntVx; move/(prime_TIg Rpr); move/trivgP.
    rewrite defVx /= (setIidPr _) cycle_subG //; move/set1P->.
    by rewrite morph1.
  - rewrite -coprime_norm_quotient_cent ?(coprimegS sKG) ?(subset_trans sKG) //.
    by rewrite tcKM quotient1.
  case=> // _ _ -> //; rewrite -coprime_quotient_cent ?quotient_cyclic //.
  by rewrite (coprimegS sRG).
rewrite !subsetI in cVK' cMK' *.
case/andP: cVK' => sK'K cVK'; case/andP: cMK' => _ cMVK'; rewrite sK'K.
have sKG: K \subset G by case: frobG => _; case/sdprod_context; case/andP.
have coMK': coprime #|M| #|K^`(1)| := coprimegS (subset_trans sK'K sKG) coMG.
rewrite (stable_factor_cent cVK') // /stable_factor /normal sVM nVM !andbT.
by rewrite commGC -quotient_cents2 // (subset_trans (subset_trans sK'K sKG)).
Qed.

End BGsection3.