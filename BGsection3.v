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

End BGsection3.
