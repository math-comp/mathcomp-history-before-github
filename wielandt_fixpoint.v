(* (c) Copyright Microsoft Corporation and Inria. All rights reserved. *)
Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq path div.
Require Import fintype bigop prime binomial finset ssralg fingroup finalg.
Require Import morphism perm automorphism quotient action commutator gproduct.
Require Import zmodp cyclic center pgroup gseries nilpotent sylow finalg.
Require Import finmodule abelian frobenius maximal extremal hall finmodule.
Require Import matrix mxalgebra mxrepresentation mxabelem BGsection1.

(******************************************************************************)
(*   This file is a placeholder for the proof of the Wielandt fixpoint order  *)
(* formula, which is a prerequisite for B & G, Section 3 and Peterfalvi,      *)
(* Section 9.                                                                 *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope ring_scope.
Import GroupScope GRing.Theory.
Import FinRing.Theory.

Section HuppertBlackburn_5_9.

Implicit Types (gT : finGroupType) (p : nat).

Lemma huppert_blackburn_5_9 gT p (A X : {group gT}) :
    abelian A -> p.-group A -> p^'.-group X -> X \subset 'N(A) -> 
  exists2 s : {set {group gT}}, \big[dprod/1]_(B \in s) B = A
      & forall B, B \in s -> [/\ homocyclic B, X \subset 'N(B)
        & acts_irreducibly X (B / 'Phi(B)) 'Q].
Proof.
move: {2}_.+1 (ltnSn #|A|) => m.
elim: m => // m IHm in gT A X *; rewrite ltnS => leAm cAA pA p'X nAX.
have [n1 eA]: {n | exponent A = p ^ n}%N by apply p_natP; rewrite pnat_exponent.
have [-> | ntA] := eqsVneq A 1.
  by exists set0 => [|B]; rewrite ?big_set0 ?inE.
have [p_pr _ _] := pgroup_pdiv pA ntA; have p_gt1 := prime_gt1 p_pr.
case: n1 => [|n] in eA; first by rewrite trivg_exponent eA in ntA.
have nA1X: X \subset 'N('Ohm_1(A)) := char_norm_trans (Ohm_char 1 A) nAX.
have sAnA1: 'Mho^n(A) \subset 'Ohm_1(A).
  rewrite (MhoE n pA) (OhmE 1 pA) genS //.
  apply/subsetP=> xpn; case/imsetP=> x Ax ->{xpn}; rewrite !inE groupX //.
  by rewrite -expgM -expnSr -eA -order_dvdn dvdn_exponent.
have nAnX: X \subset 'N('Mho^n(A)) := char_norm_trans (Mho_char n A) nAX.
have [B minB sBAn]: {B : {group gT} | minnormal B X & B \subset 'Mho^n(A)}.
  apply: mingroup_exists; rewrite nAnX andbT; apply/trivgPn.
  have [x Ax ox] := exponent_witness (abelian_nil cAA).
  exists (x ^+ (p ^ n)); first by rewrite Mho_p_elt ?(mem_p_elt pA).
  by rewrite -order_dvdn -ox eA dvdn_Pexp2l ?ltnn.
have abelA1: p.-abelem 'Ohm_1(A) by rewrite Ohm1_abelem.
have sBA1: B \subset 'Ohm_1(A) := subset_trans sBAn sAnA1.
case/mingroupP: minB; case/andP=> ntB nBX minB.
have{nBX sBA1} [U defA1 nUX] := Maschke_abelem abelA1 p'X sBA1 nA1X nBX.
have [_ mulBU _ tiBU] := dprodP defA1; have{mulBU} [_ sUA1] := mulG_sub mulBU.
have sUA: U \subset A := subset_trans sUA1 (Ohm_sub 1 _).
have [U1 | {defA1 minB}ntU] := eqsVneq U 1.
  rewrite U1 dprodg1 /= in defA1.
  have homoA: homocyclic A.
    apply/(Ohm1_homocyclicP pA cAA); rewrite eA pfactorK //=.
    by apply/eqP; rewrite eqEsubset sAnA1 -defA1 sBAn.
  exists [set A]; rewrite ?big_set1 // => G; move/set1P->; split=> //.
  have OhmMho: forall k, 'Ohm_k(A) = 'Mho^(n.+1 - k)(A).
    by move=> k; rewrite (homocyclic_Ohm_Mho k pA) // eA pfactorK.
  have fM: {in A &, {morph (fun x => x ^+ (p ^ n)) : x y / x * y >-> x * y}}.
    by move=> x y Ax Ay /=; rewrite expgMn // /commute -(centsP cAA).
  pose f := Morphism fM; have ker_f: 'ker f = 'Phi(A).
    apply/setP=> z; rewrite (Phi_Mho pA cAA) -(subSnn n) -OhmMho.
    by rewrite (OhmEabelian pA) ?(abelianS (Ohm_sub n A)) ?inE.
  have [g injg def_g] := first_isom f; rewrite /= {}ker_f in g injg def_g.
  have{f def_g} def_g: forall H, gval H \subset A -> g @* (H / _) = 'Mho^n(H).
    move=> H sHA; rewrite def_g morphimEsub //.
    by rewrite (MhoEabelian n (pgroupS sHA pA) (abelianS sHA cAA)).
  have im_g: g @* (A / 'Phi(A)) = B by rewrite def_g // defA1 OhmMho subn1.
  have defAb: A / 'Phi(A) = g @*^-1 B by rewrite -im_g injmK.
  have nsPhiA: 'Phi(A) <| A := Phi_normal A.
  have nPhiX: X \subset 'N('Phi(A)) := char_norm_trans (Phi_char A) nAX.
  rewrite defAb; apply/mingroupP; split=> [|Hb].
    by rewrite -(morphim_injm_eq1 injg) ?morphpreK /= -?defAb ?im_g ?ntB ?actsQ.
  case/andP=> ntHb actsXHb /= sgHbB; have [sHbA _] := subsetIP sgHbB.
  rewrite -sub_morphim_pre // in sgHbB; rewrite -(minB _ _ sgHbB) ?injmK //.
  rewrite morphim_injm_eq1 // {}ntHb {actsXHb}(subset_trans actsXHb) //=.
  have{sHbA} [H defHb sPhiH sHA] := inv_quotientS nsPhiA sHbA.
  rewrite defHb def_g // (char_norm_trans (Mho_char n H)) //.
  by rewrite astabsQ ?subsetIr ?(normalS sPhiH sHA).
have nsUA: U <| A by rewrite -sub_abelian_normal.
have nUA: A \subset 'N(U) by case/andP: nsUA.
have Au_lt_m: #|A / U| < m := leq_trans (ltn_quotient ntU sUA) leAm.
have cAuAu: abelian (A / U) := quotient_abelian _ cAA.
have pAu: p.-group (A / U) := quotient_pgroup _ pA.
have p'Xu: p^'.-group (X / U) := quotient_pgroup _ p'X.
have nXAu: X / U \subset 'N(A / U) := quotient_norms _ nAX.
have{Au_lt_m p'Xu nXAu} [S defAu simS] := IHm _ _ _ Au_lt_m cAuAu pAu p'Xu nXAu.
have sSAu: forall Ku, Ku \in S -> Ku \subset A / U.
  by move=> Ku S_Ku; rewrite -(bigdprodEY defAu) sub_gen // (bigcup_max Ku).
have{B ntB sBAn tiBU} [Ku S_Ku eKu]: exists2 Ku, Ku \in S & exponent Ku == (p ^ n.+1)%N.
  apply/exists_inP; apply: contraR ntB; rewrite negb_exists_in -subG1 -tiBU.
  move/forall_inP=> expSpn; apply/subsetP=> x Ux; rewrite inE Ux coset_idr //.
    by rewrite (subsetP nUA) // (subsetP (Mho_sub n A)) // (subsetP sBAn).
  have [y Ay ->]: exists2 y, y \in A & x = y ^+ (p ^ n).
    by apply/imsetP; rewrite -MhoEabelian ?(subsetP sBAn).
  rewrite morphX ?(subsetP nUA) // (exponentP _ _ (mem_quotient _ Ay)) //.
  rewrite -sub_Ldiv -OhmEabelian ?(abelianS (Ohm_sub n _)) //=.
  rewrite (OhmE n pAu) /= -(bigdprodEY defAu) genS // subsetI sub_gen //=. 
  apply/bigcupsP=> Ku S_Ku; rewrite sub_LdivT.
  have: exponent Ku %| p ^ n.+1.
    by rewrite (dvdn_trans (exponentS (sSAu _ S_Ku))) // -eA exponent_quotient.
  case/dvdn_pfactor=> // k le_k_n1 expKu; rewrite expKu dvdn_exp2l //.
  by rewrite -ltnS ltn_neqAle le_k_n1 -(eqn_exp2l _ _ p_gt1) -expKu expSpn.
have{sSAu} [sKuA [homoKu nKuX minKu]] := (sSAu Ku S_Ku, simS Ku S_Ku).
have [K defKu sUK sKA] := inv_quotientS nsUA sKuA.
have [cKK cKuKu] := (abelianS sKA cAA, abelianS sKuA cAuAu).
have [pK pKu] := (pgroupS sKA pA, pgroupS sKuA pAu).
have nsUK: U <| K := normalS sUK sKA nsUA; have [_ nUK] := andP nsUK.
have nKX: X \subset 'N(K).
  by rewrite -(quotientSGK nUX) ?normsG ?quotient_normG // -defKu.
pose K1 := 'Mho^1(K); have nsK1K: K1 <| K := Mho_normal 1 K.
have nXKb: X / K1 \subset 'N(K / K1) by exact: quotient_norms.
pose K'u := \big[dprod/1]_(Bu \in S :\ Ku) Bu.
have{S_Ku} defAu_K: K / U \x K'u = A / U by rewrite -defKu -big_setD1.
have [[_ Pu _ defK'u]] := dprodP defAu_K; rewrite defK'u => mulKPu _ tiKPu.
have [_ sPuA] := mulG_sub mulKPu.
have [P defPu sUP sPA] := inv_quotientS nsUA sPuA.
have{simS defK'u} nPX: X \subset 'N(P).
  rewrite -(quotientSGK nUX) ?normsG // quotient_normG ?(normalS sUP sPA) //.
  rewrite -defPu -(bigdprodEY defK'u) norms_gen ?norms_bigcup //.
  by apply/bigcapsP=> Bu; case/setD1P=> _; case/simS.
have abelKb: p.-abelem (K / K1).
  by rewrite -[K1](Phi_Mho pK) ?Phi_quotient_abelem.
have p'Xb: p^'.-group (X / K1) := quotient_pgroup _ p'X.
have sUKb: U / K1 \subset K / K1 := quotientS _ sUK.
have nUXb: X / K1 \subset 'N(U / K1) := quotient_norms _ nUX.
have tiUK1: U :&: K1 = 1.
  apply/trivgP; apply/subsetP=> xp; case/setIP=> Uxp K1xp.
  have{K1xp} [x Kx def_xp]: exists2 x, x \in K & xp = x ^+ p.
    by apply/imsetP; rewrite -(MhoEabelian 1).
  suffices A1x: x \in 'Ohm_1(A).
    by rewrite def_xp inE; case/abelemP: abelA1 => // _ ->.
  have nUx: x \in 'N(U) := subsetP nUK x Kx.
  rewrite -sub1set -(quotientSGK _ sUA1) ?quotient_set1 ?sub1set //.
  apply: (subsetP (quotientS U (subset_trans (MhoS n sKA) sAnA1))).
  rewrite quotientE morphim_Mho //= -quotientE -defKu.
  have ->: 'Mho^n(Ku) = 'Ohm_1(Ku).
    by rewrite (homocyclic_Ohm_Mho 1 pKu) // (eqP eKu) pfactorK ?subn1.
  rewrite (OhmE 1 pKu) ?mem_gen // !inE defKu mem_quotient //=.
  by rewrite -morphX //= -def_xp coset_id.
have [Db defKb nDXb] := Maschke_abelem abelKb p'Xb sUKb nXKb nUXb.
have [_ mulUDb _ tiUDb] := dprodP defKb; have [_ sDKb] := mulG_sub mulUDb.
have [D defDb sK1D sDK] := inv_quotientS (Mho_normal 1 K) sDKb.
have nK1X: X \subset 'N(K1) := char_norm_trans (Mho_char 1 K) nKX.
have [cDU [sK1K nK1K]] := (centSS sUK sDK cKK, andP nsK1K).
have nDX: X \subset 'N(D).
  rewrite -(quotientSGK nK1X) ?normsG // quotient_normG ?(normalS _ sDK) //.
  by rewrite -defDb.
have{mulUDb} mulUD: U * D = K.
  rewrite (centC cDU) -(mulSGid sK1D) -mulgA -(centC cDU).
  rewrite -quotientK ?quotientMr ?(subset_trans _ nK1K) ?mul_subG // -defDb.
  by rewrite mulUDb quotientGK.
have cKP: P \subset 'C(K) := centSS sPA sKA cAA.
have mulKP: K * P = A.
  rewrite -(mulSGid sUK) -mulgA -(quotientGK nsUA) -mulKPu defPu.
  by rewrite -quotientK ?quotientMr ?mul_subG ?(subset_trans _ nUA).
have defKP: K :&: P = U.
  apply/eqP; rewrite eqEsubset subsetI sUK sUP !andbT.
  by rewrite -quotient_sub1 ?subIset ?nUK // -tiKPu defPu quotientI.
have tiUD: U :&: D = 1.
  apply/trivgP; rewrite -tiUK1 subsetI subsetIl.
  rewrite -quotient_sub1; last by rewrite subIset ?(subset_trans sUK).
  by rewrite -tiUDb defDb quotientI.
have tiDP: D :&: P = 1 by rewrite -(setIidPl sDK) -setIA defKP setIC.
have mulDP: D * P = A by rewrite -(mulSGid sUP) mulgA -(centC cDU) mulUD.
have sDA := subset_trans sDK sKA.
have defA: D \x P = A by rewrite dprodE // (centSS sPA sDA).
have ntD: D :!=: 1.
  apply: contraNneq ntA => D1; rewrite trivg_exponent eA -(eqP eKu).
  rewrite -trivg_exponent -subG1 -tiKPu defKu subsetIidl defPu quotientS //.
  by rewrite -(mul1g P) -D1 mulDP.
have ltPm: #|P| < m.
  by rewrite (leq_trans _ leAm) // -(dprod_card defA) ltn_Pmull ?cardG_gt1.
have [cPP pP] := (abelianS sPA cAA, pgroupS sPA pA).
have{S defAu K'u defAu_K} [S defP simS] := IHm _ _ _ ltPm cPP pP p'X nPX.
exists (D |: S) => [ | {defP}B].
  rewrite big_setU1 ?defP //=; apply: contra ntD => S_D.
  by rewrite -subG1 -tiDP subsetIidl -(bigdprodEY defP) sub_gen ?(bigcup_max D).
case/setU1P=> [-> {B S simS} | ]; last exact: simS.
have [[pD cDD] nUD] := (pgroupS sDA pA, abelianS sDA cAA, subset_trans sDA nUA).
have isoD: D \isog Ku by rewrite defKu -mulUD quotientMidl quotient_isog.
rewrite {isoD}(isog_homocyclic isoD); split=> //.
have nPhiDX: X \subset 'N('Phi(D)) := char_norm_trans (Phi_char D) nDX.
have [f [injf im_f act_f]]:
  exists f : {morphism D / 'Phi(D) >-> coset_of 'Phi(Ku)},
    [/\ 'injm f, f @* (D / 'Phi(D)) = Ku / 'Phi(Ku)
      &  {in D / 'Phi(D) & X, morph_act 'Q 'Q f (coset U)}].
- have [/= injf im_f] := isomP (quotient_isom nUD tiUD).
  set f := restrm nUD (coset U) in injf im_f.
  rewrite -quotientMidl mulUD -defKu in im_f.
  have fPhiD: f @* 'Phi(D) = 'Phi(Ku) by rewrite -im_f (morphim_Phi _ pD).
  rewrite -['Phi(Ku)]/(gval 'Phi(Ku)%G) -(group_inj fPhiD).
  exists (quotm_morphism [morphism of f] (Phi_normal _)).
  rewrite (injm_quotm _ injf) morphim_quotm /= -/f im_f.
  split=> // yb x; case/morphimP=> y Ny Dy ->{yb} Xx.
  have [nPhiDx nUx] := (subsetP nPhiDX x Xx, subsetP nUX x Xx).
  have Dyx: y ^ x \in D by rewrite memJ_norm // (subsetP nDX).
  rewrite quotmE // !qactE ?qact_domE ?subsetT ?astabsJ ?quotmE //=.
  - by congr (coset _ _); rewrite /f /restrm morphJ // (subsetP nUD).
  - by rewrite (subsetP (morphim_norm _ _)) ?mem_morphim.
  rewrite morphim_restrm  (setIidPr (Phi_sub _)).
  by rewrite (subsetP (morphim_norm _ _)) ?mem_quotient.
apply/mingroupP; split=> [|Y].
  rewrite -subG1 quotient_sub1 ?(normal_norm (Phi_normal _)) //.
  by rewrite proper_subn ?Phi_proper // actsQ.
case/andP=> ntY actsXY sYD; have{minKu} [_ minKu] := mingroupP minKu.
apply: (injm_morphim_inj injf); rewrite // im_f.
apply: minKu; last by rewrite /= -im_f morphimS.
rewrite morphim_injm_eq1 // ntY.
apply/subsetP=> xb; case/morphimP=> x Nx Xx ->{xb}.
rewrite 2!inE /= qact_domE ?subsetT // astabsJ.
rewrite (subsetP (char_norm_trans (Phi_char _) nKuX)) ?mem_quotient //=.
apply/subsetP=> fy; case/morphimP=> y Dy Yy ->{fy}.
by rewrite inE /= -act_f // morphimEsub // mem_imset // (acts_act actsXY).
Qed.

End HuppertBlackburn_5_9.

Section HuppertBlackburn_12_3.

Implicit Types (gT wT : finGroupType) (m n p q : nat).

Inductive hp123 gT (V G : {group gT}) m : Prop := 
  Hp123 wT (W D G1 : {group wT}) (f : {morphism D >-> gT})
   of homocyclic W & #|W| = (#|V| ^ m)%N
    & 'ker f = 'Mho^1(W) & f @* W = V & f @* G1 = G & W ><| G1 = D.


Lemma huppert_blackburn_12_3 gT (V G : {group gT}) p m :
    minnormal V G -> coprime p #|G| -> p.-abelem V -> m > 0 -> hp123 V G m.
Proof.
move=> minV copG abelV m_gt0; pose q := (p ^ m)%N.
have [ntV nVG] := andP (mingroupp minV).
have [p_pr pVdvdn [n Vpexpn]] := pgroup_pdiv (abelem_pgroup abelV) ntV.
move/(abelem_mx_irrP abelV ntV nVG): (minV) => mx_irrV.
have dim_lt0 : 'dim V > 0 by rewrite (dim_abelemE abelV) // Vpexpn pfactorK.
have q_gt1: q > 1 by rewrite (ltn_exp2l 0) // prime_gt1.
have p_q: p.-nat q by rewrite pnat_exp pnat_id.
have p_dv_q: p %| q := dvdn_exp2l p m_gt0.
pose rG := regular_repr [comUnitRingType of 'Z_q] G; pose MR_G := ('MR rG)%gact.
pose L := (sdpair1 MR_G @* [set: 'rV['Z_q]_#|G|])%G.
have cLL: abelian L by rewrite morphim_abelian // zmod_abelian.
have pL: p.-group L.
  by rewrite morphim_pgroup -?pnat_exponent ?exponent_mx_group.
pose X := (sdpair2 MR_G @* G)%G.
have tVIG : V :&: G = 1 by apply: coprime_TIg; rewrite Vpexpn coprime_pexpl //.
have{copG} p'G: p^'.-group G by rewrite /pgroup p'natE // -prime_coprime.
have p'X: p^'.-group X by rewrite morphim_pgroup.
have nXL: X \subset 'N(L) := im_sdpair_norm MR_G.
have [injL injX] := (injm_sdpair1 MR_G, injm_sdpair2 MR_G).
have [/= S defL im_S] := huppert_blackburn_5_9 cLL pL p'X nXL.
pose gi (z : 'Z_q) := z%:R : 'F_p.
have giM: rmorphism gi.
  split=> [z1 z2|]; last split=> // z1 z2.
    apply: canRL (addrK _) _; apply: val_inj.
    by rewrite -{2}(subrK z2 z1) -natrD /= !val_Fp_nat ?modn_dvdm // Zp_cast.
  by apply: val_inj; rewrite -natrM /= !val_Fp_nat ?modn_dvdm // Zp_cast.
pose g u := map_mx (RMorphism giM) (invm injL u).
have gM: {in L &, {morph g : u v / u * v}}.
  by move=> u v Lu Lv /=; rewrite {1}/g morphM // map_mxD.
have kerg: 'ker (Morphism gM) = 'Phi(L).
  rewrite (Phi_Mho pL cLL) (MhoEabelian 1 pL cLL).
  apply/setP=> u; apply/idP/imsetP=> [ | [v Lv ->{u}]]; last first.
    rewrite !inE groupX //=; apply/eqP/rowP=> i; apply: val_inj.
    rewrite !mxE morphX // mulmxnE Zp_mulrn /= val_Fp_nat //=.
    by move: {i}(_ i); rewrite Zp_cast // => vi; rewrite modn_dvdm // modnMl.
  case/morphpreP; case/morphimP=> v _ _ ->{u}; move/set1P=> /=.
  rewrite /g invmE ?in_setT //; move/rowP=> vp0.
  pose x := sdpair1 MR_G (map_mx (fun t : 'Z_q => (t %/ p)%:R) v).
  exists x; first by rewrite mem_morphim ?inE.
  rewrite -morphX ?in_setT //; congr (sdpair1 MR_G _); apply/rowP=> i.
  rewrite mulmxnE -{1}(natr_Zp (v 0 i)) {1}(divn_eq (v 0 i) p) addnC.
  by have:= congr1 val (vp0 i); rewrite !mxE -mulrnA /= val_Fp_nat // => ->.
pose gx := invm injX; pose aG := regular_repr [fieldType of 'F_p] G.
have Ggx: {in X, forall x, gx x \in G}.
  by move=> x Xx; rewrite -{4}(im_invm injX) mem_morphim.
have gJ: {in L & X, forall u x, g (u ^ x) = g u *m aG (gx x)}.
  move=> u x Lu Xx /=; rewrite -{1}(invmK injL Lu) -{1}(invmK injX Xx) -/(gx x).
  rewrite -sdpair_act ?Ggx ?inE // /g invmE ?inE // [MR_G _]/=.
  by rewrite mx_repr_actE ?Ggx // map_mxM map_regular_mx.
pose gMx U := rowg_mx (Morphism gM @* U).
have simS: forall U, U \in S -> mxsimple aG (gMx U).
  move=> U S_U; have [_ nUX irrU] := im_S U S_U.
  have{irrU} [modU irrU] := mingroupP irrU; have{modU} [ntU _] := andP modU.
  have sUL: U \subset L by rewrite -(bigdprodEY defL) sub_gen // (bigcup_max U).
  split=> [||U2 modU2].
  - rewrite (eqmx_module _ (genmxE _)); apply/mxmoduleP=> x Gx.
    apply/row_subP=> i; rewrite row_mul rowK.
    have [u Lu Uu def_u] := morphimP (enum_valP i).
    rewrite -(invmE injX Gx) def_u -gJ ?mem_morphim //.
    set ux := u ^ _; apply: eq_row_sub (gring_index _ (g ux)) _.
    have Uux: ux \in U by rewrite memJ_norm // (subsetP nUX) ?mem_morphim.
    by rewrite rowK gring_indexK //; apply: mem_morphim; rewrite ?(subsetP sUL).
  - apply: contra ntU; rewrite rowg_mx_eq0.
    rewrite -subG1 sub_morphim_pre // -kerE kerg => sU_Phi.
    rewrite /= quotientS1 //=; rewrite (big_setD1 U) //= in defL.
    have{defL} [[_ U' _ ->] defUU' cUU' tiUU'] := dprodP defL.
    have defL: U \* U' = L by rewrite cprodE.
    have:= cprod_modl (Phi_cprod pL defL) (Phi_sub U).
    rewrite -(setIidPl (Phi_sub U')) setIAC -setIA tiUU' setIg1 cprodg1 => ->.
    by rewrite subsetIidr.
  rewrite -!rowgS stable_rowg_mxK /= => [sU2gU nzU2|]; last first.
    apply/subsetP=> z _; rewrite !inE /=; apply/subsetP=> u gUu.
    by rewrite inE /= /scale_act -[val z]natr_Zp scaler_nat groupX.
  rewrite sub_morphim_pre // -subsetIidl.
  rewrite -(quotientSGK (normal_norm (Phi_normal U))) //=; last first.
    rewrite subsetI Phi_sub (subset_trans (PhiS pL sUL)) //.
    by rewrite -kerg ker_sub_pre.
  rewrite [(U :&: _) / _]irrU //; last by rewrite quotientS ?subsetIl.
  rewrite (contra _ nzU2) /=; last first.
    rewrite -subG1 quotient_sub1; last first.
      by rewrite subIset // normal_norm // Phi_normal.
    rewrite /= -(morphpre_restrm sUL).
    move/(morphimS (restrm_morphism sUL (Morphism gM))).
    rewrite morphpreK ?im_restrm // morphim_restrm => s_U2_1.
    rewrite -trivg_rowg -subG1 (subset_trans s_U2_1) //.
    rewrite -(morphim_ker (Morphism gM)) morphimS // kerg.
    by rewrite subIset ?(PhiS pL) ?orbT.
  rewrite actsQ //; first by rewrite (char_norm_trans (Phi_char U)).
  rewrite normsI //; apply/subsetP=> x Xx; rewrite inE.
  apply/subsetP=> ux; case/imsetP=> u g'U2u ->{ux}.
  have [Lu U2gu] := morphpreP g'U2u; rewrite mem_rowg in U2gu.
  rewrite inE memJ_norm ?(subsetP nXL) // Lu /= inE gJ //.
  by rewrite mem_rowg (mxmodule_trans modU2) ?Ggx.
have im_g: Morphism gM @* L = [set: 'rV_#|G|].
  apply/eqP; rewrite eqEcard subsetT cardsT card_matrix card_Fp //= mul1n.
  rewrite card_morphim kerg setIid (Phi_Mho pL cLL) -divgS ?Mho_sub //.
  rewrite -(mul_card_Ohm_Mho_abelian 1 cLL) mulnK ?cardG_gt0 //.
  rewrite (card_pgroup (pgroupS (Ohm_sub 1 L) pL)) -rank_abelian_pgroup //.
  by rewrite (injm_rank injL) //= rank_mx_group mul1n.
have sumS: (\sum_(U \in S) gMx U :=: 1%:M)%MS.
  apply/eqmxP; rewrite submx1; apply/rV_subP=> v _.
  have: v \in Morphism gM @* L by rewrite im_g inE.
  case/morphimP=> u Lu _ ->{v}.
  rewrite -mem_rowg -sub1set -morphim_set1 // sub_morphim_pre ?sub1set //.
  have [c [Uc -> _]] := mem_bigdprod defL Lu; rewrite group_prod //= => U S_U.
  have sUL: U \subset L by rewrite -(bigdprodEY defL) sub_gen // (bigcup_max U).
  rewrite inE (subsetP sUL) ?Uc // inE mem_rowg (sumsmx_sup U) // -mem_rowg.
  by rewrite (subsetP (sub_rowg_mx _)) // mem_morphim ?(subsetP sUL) ?Uc.
have Fp'G: [char 'F_p]^'.-group G.
  by rewrite (eq_p'group _ (charf_eq (char_Fp p_pr))).
have [VK [modVK defVK]] := rsim_regular_submod mx_irrV Fp'G.
have [U S_U isoUV]: {U | U \in S & mx_iso (regular_repr _ G) (gMx U) VK}.
  apply: hom_mxsemisimple_iso (scalar_mx_hom _ 1 _) _ => [|U S_U _|]; auto.
    by apply/(submod_mx_irr modVK); exact: (mx_rsim_irr defVK).
  by rewrite mulmx1 sumS submx1.
have simU := simS U S_U; have [modU _ _] := simU.
pose rV := abelem_repr abelV ntV nVG.
have{VK modVK defVK isoUV} [h dimU h_free hJ]: mx_rsim (submod_repr modU) rV.
  by apply: mx_rsim_trans (mx_rsim_sym defVK); exact/mx_rsim_iso.
have sUL : U \subset L.
  have [homU _ _] := im_S U S_U; have [cUU _] := andP homU.
  rewrite (big_setD1 U) //= in defL.
  have [[_ U' _ defU'] defUU' _ tiUU'] := dprodP defL.
  rewrite defU' in defL defUU' tiUU'.
  by case/mulG_sub: defUU'.
pose W := [set: 'rV['Z_(p ^ m)](V)]%G.
 have [homU nUX _] := im_S U S_U.
have [cUU _] := andP homU.
have abel_typeU : abelian_type U == nseq ('dim V) (p ^ m)%N.
  rewrite (big_setD1 U) //= in defL.
  have [[_ U' _ defU'] defUU' _ tiUU'] := dprodP defL.
  rewrite defU' in defL defUU' tiUU'.
  have ->: 'dim V = 'r(U).
    apply/eqP; rewrite -dimU -(eqn_exp2l _ _ (prime_gt1 p_pr)).
    rewrite (rank_abelian_pgroup (pgroupS sUL pL) cUU).
    rewrite -(card_pgroup (pgroupS (Ohm_sub 1 U) (pgroupS sUL pL))).
    rewrite -{1}(card_Fp p_pr) -card_rowg stable_rowg_mxK; last first.
      apply/subsetP=> z _; rewrite !inE; apply/subsetP=> v gUv.
      by rewrite inE /= /scale_act -(natr_Zp (val z)) scaler_nat groupX.
    rewrite card_morphim kerg (Phi_Mho pL cLL) (setIidPr sUL) -divgI setIC.
    rewrite -(dprod_modl (Mho_dprod 1 defL) (Mho_sub 1 U)).
    rewrite [_ :&: _](trivgP _); last by rewrite -tiUU' setIC setSI ?Mho_sub.
    by rewrite dprodg1 -(mul_card_Ohm_Mho_abelian 1 cUU) mulnK ?cardG_gt0.
  have isoL: isog L [set: 'rV['Z_q]_#|G|] by rewrite isog_sym sub_isog.
  have homL: homocyclic L by rewrite (isog_homocyclic isoL) mx_group_homocyclic.
  have [-> _] := abelian_type_dprod_homocyclic defL pL homL.
  by rewrite (exponent_isog isoL) // exponent_mx_group.
have pU: p.-group U by rewrite (pgroupS sUL).
have isoWU: isog U W.
  by rewrite eq_abelian_type_isog ?zmod_abelian // abelian_type_mx_group // mul1n.
have {cUU abel_typeU} cardU : #|U| = (#|V| ^ m)%N.
  rewrite card_homocyclic // (exponent_isog isoWU) exponent_mx_group //.
  rewrite -size_abelian_type // (eqP abel_typeU) size_nseq.
  by rewrite (dim_abelemE abelV) // Vpexpn pfactorK // expnAC.
pose f3 w := rVabelem abelV ntV (in_submod _ (g w) *m h).
have f3M: {in U &, {morph f3: w1 w2 / w1 * w2}}.
  move=> w1 w2 Uw1 Uw2 /=; rewrite {1}/f3.
  rewrite gM ?(subsetP sUL) // linearD mulmxDl.
  by rewrite morphM ?mem_im_abelem_rV.
have Ugw w (Uw : w \in U) : ((g w) <= gMx U)%MS.
  rewrite -mem_rowg (subsetP (sub_rowg_mx _)) //.
  by rewrite (mem_morphim (Morphism gM)) ?(subsetP sUL).
have kerg_U: 'ker_U (Morphism gM) = 'Mho^1(U).
  rewrite kerg (Phi_Mho pL cLL); rewrite (big_setD1 U) //= in defL.
  have [[_ U' _ defU'] _ _ tiUU'] := dprodP defL; rewrite defU' in defL tiUU'.
  rewrite setIC -(dprod_modl (Mho_dprod 1 defL) (Mho_sub 1 U)).
  by rewrite [_ :&: _](trivgP _) ?dprodg1 // -tiUU' setIC setSI ?Mho_sub.
have {kerg_U} ker_f3: 'ker (Morphism f3M) = 'Mho^1(U).
  apply/setP=> w; rewrite !inE /=.
  rewrite morph_injm_eq1 ?rVabelem_injm ?mem_im_abelem_rV //=.
  rewrite -[1](mul0mx _ h) (inj_eq (row_free_inj h_free)) in_submod_eq0.
  case Uw: (w \in U) => /=; last first.
    apply/sym_eq; apply: contraFF Uw; exact: (subsetP (Mho_sub _ _)).
  rewrite -[(_ <= _)%MS]andTb -(Ugw _ Uw) -sub_capmx capmx_compl submx0.
  by rewrite -kerg_U !inE (subsetP sUL) // Uw.
have cUU: abelian U := abelianS sUL cLL.
have im_f3: Morphism f3M @* U = V.
  apply/eqP; rewrite eqEcard card_morphim setIid ker_f3.
  apply/andP; split.
    apply/subsetP=> v; case/morphimP=> w _ _ ->; exact: mem_rVabelem.
  rewrite -divgS ?Mho_sub // -(mul_card_Ohm_Mho_abelian 1 cUU).
  rewrite mulnK ?cardG_gt0 // (card_pgroup (pgroupS (Ohm_sub 1 U) pU)).
  rewrite -rank_abelian_pgroup // (isog_rank isoWU) /W.
  by rewrite (dim_abelemE abelV) // rank_mx_group mul1n Vpexpn pfactorK.
have hact:  {in U & X, morph_act 'J 'J (Morphism f3M) gx}.
  move=> u x Uu Xx /=.
  rewrite /f3 gJ ?(subsetP sUL) // in_submodJ; last exact: (Ugw _ Uu).
  by rewrite -mulmxA hJ ?Ggx // mulmxA rVabelemJ ?Ggx.
have sdpUX: U ><| X = U <*> X.
  rewrite norm_joinEr; last by case: (im_S _ S_U).
  rewrite sdprodE //; apply/eqP; rewrite -subG1 -(im_sdpair_TI MR_G). 
  exact: setSI.
pose f := sdprodm sdpUX hact.
have {im_f3} fU : f @*U = V by rewrite morphim_sdprodml.
have fX : f @* X = G by rewrite morphim_sdprodmr //; exact: im_invm.
have kerf : 'ker f = 'Mho^1(U).
  apply/eqP; rewrite eqEsubset; apply/andP; split; apply/subsetP; last first.
  - move=> y; rewrite -ker_f3 kerE; case/morphpreP => /= Uy f3y.
    apply/kerP; first exact: (subsetP (joing_subl _ _)).
    by rewrite /= sdprodmEl //=; apply/eqP; rewrite -in_set1.
  - rewrite ker_sdprodm /= => y; case/imset2P=> u t Uu /setIdP[Xt /eqP fu] ->.
    have : f3 u \in V :&: G.
      rewrite inE -fU  morphim_sdprodml //= (mem_morphim (Morphism f3M)) //.
      rewrite fu -[in X in _ && (_ \in X)]fX morphim_sdprodmr ?mem_morphim //.
   rewrite tVIG in_set1 fu morph_injm_eq1 ?injm_invm //; move/eqP=> t1.
   move: fu; rewrite t1 morph1 invg1 mulg1; move/(kerP (Morphism f3M) Uu).
   by rewrite ker_f3.
exact: Hp123 homU cardU kerf fU fX sdpUX.
Qed.


End HuppertBlackburn_12_3.


(* Shall I export this? for now it is inlined in the proof 
Lemma exprdiv_eq p x y : p > 1 -> 
  (forall n, n > 0 -> x = y %[mod p ^ n]) -> x = y.
Proof.
move=> lt1p h; have /h : 0 < (x.+1 * y.+1)%N by [].
by rewrite !modn_small // 1?[in X in x < X]mulnC expnM 
  !(leq_trans _ (ltn_expl _ _)).
Qed.
*)

(* Same question for that one: *)
Lemma big_morphG (gT1 gT2 : finGroupType)(I : Type)(D : {group gT1}) 
  (f : {morphism D >-> gT2}) (F : I -> gT1) (P : pred I) r : 
  (forall i, P i -> F i \in D) ->
  f (\prod_( i <- r | P i) F i) = \prod_( i <- r | P i) f (F i).
Proof.
move=> hD.
elim/(big_load (fun x => x \in D)): _; elim/big_rec2: _ => [| i x y Pi [Dy h]].
  by rewrite group1 morph1.
by rewrite groupM ?morphM // ?hD // h.
Qed.


Theorem solvable_Wielandt_fixpoint 
  (I : finType) (gT : finGroupType) (A : I -> {group gT}) (n m : I -> nat) 
  (G V : {group gT}) :
    (forall i, m i + n i > 0 -> A i \subset G) ->
    G \subset 'N(V) -> coprime #|V| #|G| -> solvable V ->
    {in G, forall a, \sum_(i | a \in A i) m i = \sum_(i | a \in A i) n i}%N ->
  (\prod_i #|'C_V(A i)| ^ (m i * #|A i|)
    = \prod_i #|'C_V(A i)| ^ (n i * #|A i|))%N.
Proof.
move: {2}_.+1 (ltnSn #|V|) => c; rewrite (bigID (fun i => 0 < m i + n i)) /=.
rewrite mulnC big1 ?mul1n => [|j]; last first.
  by rewrite -eqn0Ngt addn_eq0 => /andP[/eqP-> _].
rewrite [in R in _ = R](bigID (fun i => 0 < m i + n i)) /=.
rewrite [R in (_ * R)%N]big1 ?muln1 => [|j]; last by rewrite addnC; case: (n j).
move=> leVm sAiG nVG copVG solV hGA *.
have {hGA} hGA : {in G, forall a : gT,
  (\sum_(i | (a \in A i) && (0 < m i + n i)) m i)%N = 
  (\sum_(i | (a \in A i) && (0 < m i + n i)) n i)%N}.
  move=> g Gg /=; rewrite -!big_filter_cond !(big_mkcond (fun _ => 0 < _)%N).
  rewrite !big_filter; apply: etrans (etrans (hGA g Gg) (esym _)).
    by apply: eq_bigr => i _; case: (m i); rewrite // if_same.
  by apply: eq_bigr => i _; rewrite addnC; case: (n i); rewrite // if_same.
move: leVm sAiG nVG copVG solV hGA; elim: c  => // c IHc in I gT A G V n m *.
rewrite ltnS => leVm sAiG nVG copVG solV hGA *.
have [V1 | ntV] := eqsVneq V 1.
  by rewrite V1 !big1 // => i _; rewrite setI1g set1gE cards1 exp1n.
have nVP : V <| V <*> G by rewrite normalYl.
wlog minV: / minnormal V (V <*> G).
  have [B minB sBV]: {B : {group gT} | minnormal B (V <*> G) & B \subset V}.
    by apply: mingroup_exists; rewrite ntV normal_norm.
  have [nBP ntB abB] := minnormal_solvable minB sBV solV.
  move/joing_subP: nBP=> /= [nBV nBG].
  have solB := (solvableS sBV solV).
  have [BV | BVproper _] := eqVproper sBV; first by apply; rewrite -{1}BV.
  have cardB : #|B| < c by apply: leq_trans leVm; exact: proper_card.
  have copBG : coprime #|B| #|G| by exact: (coprimeSg sBV).
  have hp mm j : 0 < m j + n j ->  
     (#|'C_V(A j)| ^ (mm j * #|A j|))%N  = 
     ((#|'C_B(A j)| ^ (mm j * #|A j|) * 
     (#|'C_(V / B)(A j / B)|) ^ (mm j * #|A j / B|)))%N.
    move/sAiG => sAjG.
    have nBAj : A j \subset 'N(B) by exact: subset_trans nBG.
    have copBAj : coprime #|B| #|A j| by rewrite (coprimegS sAjG).
    rewrite -(card_isog (quotient_isog _ _)) ?(coprime_TIg copBAj) //.
    rewrite -expnMn.
    suff -> :  #|'C_V(A j)| = (#|'C_B(A j)| * #|'C_(V / B)(A j / B)|)%N by [].
    have copVAj : coprime #|V| #|A j| by exact: (coprimegS sAjG).
    rewrite -(coprime_quotient_cent sBV nBAj copVAj solV).
    have -> : 'C_B(A j) = 'C_V(A j) :&: B.
      by rewrite [_ :&: B]setIC setIA (setIidPl sBV).
    by rewrite card_quotient ?LagrangeI // subIset ?nBV.
  rewrite !(eq_bigr _ (hp _)) {hp} !big_split /=.
  congr (_ * _)%N; first exact: (IHc _ _ _ G).
  have cardQ : #|V / B| < c by apply: leq_trans leVm; apply: ltn_quotient.
  have nQ : G / B \subset 'N(V / B) by apply: quotient_norms.
  have copQ : coprime #|V / B| #|G / B| by exact: coprime_morph.
  have solQ : solvable (V / B) by exact: quotient_sol.
  have sAQ : forall i : I, 0 < m i + n i -> A i / B \subset G / B.
    move=> i si; apply: quotientS; exact: sAiG.
  apply: (IHc _ _ _ (G / B)%G) => // {nQ copQ solQ cardQ}.
  move=> g; case/morphimP=> x /= Nx Gx ->.
  suff hindex j :
    (coset B x \in A j / B) && (0 < m j + n j) = (x \in A j) && (0 < m j + n j).
    rewrite !(eq_bigl _ _ hindex) /=; exact: hGA.
  case lt0s : (0 < m j + n j); rewrite ?andbF ?andbT //.
  have nBAj : A j \subset 'N(B) by apply: subset_trans nBG; exact: sAiG.
  apply/idP/idP; last by move/mem_quotient.
  move/(mem_morphpre (subsetP nBG _ Gx)); rewrite /= quotientK // => BAx.
  have : x \in G :&: (B * A j) by rewrite in_setI Gx.
  rewrite -group_modr //; move: copBG; rewrite coprime_sym ?sAiG //.
  by move/coprime_TIg->; rewrite mul1g.
have [p primep pabV] := is_abelemP (minnormal_solvable_abelem minV solV).
have{minV} minV: minnormal V G.
  apply/mingroupP; split=> [|B nBG sBV]; first by rewrite ntV nVG.
  case/mingroupP: minV => _; apply=> //.
  by rewrite join_subG (sub_abelian_norm (abelem_abelian pabV)).
have coppG : coprime p #|G|.
  apply: (coprime_dvdl _ copVG); move/abelem_pgroup: pabV => /card_pgroup eV.
  rewrite eV; apply: dvdn_exp => //; rewrite lt0n; apply: contra ntV => h0.
  by rewrite trivg_card1 eV (eqP h0) expn0.
pose lp i := logn p #|'C_V(A i)|.
have hindex mn i : 0 < m i + n i -> 
  (#|'C_V(A i)| ^ (mn i * #|A i|) = p ^ (lp i * (mn i) * #|A i|))%N.
  suff: p.-group 'C_V(A i) by move/card_pgroup=> ->; rewrite -expnM mulnA.
  by apply: (pgroupS _ (abelem_pgroup pabV));apply: subsetIl.
rewrite !(eq_bigr _ (hindex _)) {hindex} -!expn_sum; congr (_ ^ _)%N.
have exprdiv_eq q x y : q > 1 -> 
  (forall n, n > 0 -> x = y %[mod q ^ n]) -> x = y.
  move=> lt1p h; have /h : 0 < (x.+1 * y.+1)%N by [].
   by rewrite !modn_small // 1?[in X in x < X]mulnC expnM
     !(leq_trans _ (ltn_expl _ _)).
apply: (exprdiv_eq _ _ _ (prime_gt1 primep)) => k lt0k {exprdiv_eq}.
(* shall we keep lt0k ? *)
pose q := (p ^ k)%N. 
have pk_gt1 : q > 1 by rewrite  -(exp1n k) ltn_exp2r // prime_gt1.
have [wgT W D G1 f homoW oW kerf imfW imfG1 sdD] := 
  huppert_blackburn_12_3 minV coppG pabV lt0k.
have [cWW _] := andP homoW.
have pW: p.-group W.
  by rewrite /pgroup oW pnat_exp -pgroupE (abelem_pgroup pabV).
pose W1 := [set: 'rV['Z_q](V)].
(* let us swap fW and fW' *)
(*have /isogP[fW inj_fW im_fW]: W \isog W1.*)
have /isogP[fW injm_fW im_fW]: W1 \isog W.
  rewrite eq_abelian_type_isog ?zmod_abelian // abelian_type_mx_group // mul1n.
  rewrite abelian_type_homocyclic //.
  have rW: 'r(W) = 'dim V.
    rewrite (rank_abelian_pgroup pW cWW) -(mulnK #|_| (cardG_gt0 'Mho^1(W))).
    rewrite mul_card_Ohm_Mho_abelian // divg_normal ?Mho_normal //=.
    rewrite -(setIidPr (Mho_sub 1 W)) -kerf (card_isog (first_isog_loc _ _)) /=.
      by rewrite imfW (dim_abelemE pabV) //.
    by case/sdprod_context: sdD => /andP[].
  rewrite -max_card_abelian // oW in homoW.
  rewrite (card_pgroup (abelem_pgroup pabV)) -expnM mulnC expnM -/q in homoW.
  rewrite rW -(dim_abelemE pabV) // eqn_exp2r // in homoW.
  by rewrite rW (eqP homoW).
have [fW' [DfW' KfW' /= fWW' im_fW']] := domP (invm_morphism injm_fW) im_fW.
have{KfW'} injm_fW': 'injm fW' by rewrite KfW' injm_invm.
case/sdprodP: (sdD) => _ Dp nG1W WG1.
have sG1D : G1 \subset D by rewrite -Dp; exact: mulG_subr.
pose fG := restrm sG1D f.
have injfG : 'injm fG.
  rewrite -WG1 subsetI /= ker_restrm subsetIl andbT.
  by  apply: subset_trans _ (Mho_sub 1 W); rewrite kerf subsetIr.
pose fG' := invm injfG.
have toWlin g : linear (fun u => (fW' ((fW u) ^ ((val (subg G1 g)))))).
  move=> z /= x y; rewrite (morphM fW) /= ?in_setT // conjMg /=.
  rewrite morphM ?memJ_norm ?(subsetP nG1W) ?subgP //= -?im_fW 
     ?mem_morphim ?in_setT //.
  congr (_ * _); rewrite -(natr_Zp z) !scaler_nat.
  rewrite morphX ?in_setT // conjXg morphX //.
  by rewrite memJ_norm ?(subsetP nG1W) ?subgP // -im_fW mem_morphim // in_setT.
pose rW g := lin1_mx (Linear (toWlin g)).
pose gamma i := \sum_(x \in A i) rW (fG' x).
suff tr_rW_Ai i (hi : 0 < m i + n i) : \tr (gamma i) = (lp i * #|A i|)%:R.
  rewrite -!val_Zp_nat // -!sumrMnr.
  have haux mn i (hi : 0 < m i + n i) :
     (lp i * mn i * #|A i|)%:R = \tr (\sum_(x \in A i) rW (fG' x) *+ mn i).
    by rewrite mulnAC natrM -tr_rW_Ai // mulrC -mxtraceZ scaler_nat sumrMnl.
  rewrite !(eq_bigr _ (haux _)) {haux} -!raddf_sum /=; congr nat_of_ord.
  have side i j (hi : 0 < m i + n i) : j \in A i -> j \in G.
    by apply: (subsetP (sAiG _ _)).
  congr (\tr _);  rewrite !(exchange_big_dep (fun x => x \in G)) //= {side}. 
  apply: eq_bigr => g Gg; rewrite !sumrMnr; congr (_ *+ _).
  transitivity (\sum_(i | (g \in A i) && (0 < m i + n i)) m i)%N.
    by apply: eq_bigl => i; rewrite andbC.
  transitivity (\sum_(i |(g \in A i) &&(0 < m i + n i)) n i)%N.
    exact: hGA.
  by apply: eq_bigl => i; rewrite andbC.
pose Aibar := (fG' @* (A i)).
pose Wbar := (fW @* [set: 'rV(V)])%G; pose rC := 'r([~: Wbar, Aibar]).
(* well Wbar is W *)
suff [[[[Pl Pr] Pu] Pd] /= [P12_id eql eqr]] : 
  exists PlPrPuPd : 'M_('dim V, rC) * 'M_(_, lp i) * 'M_(_, _) *  'M_(_, _),

       let Pl := PlPrPuPd.1.1.1 in let Pr := PlPrPuPd.1.1.2 in
       let Pu := PlPrPuPd.1.2 in let Pd := PlPrPuPd.2 in
       let P1 := row_mx Pl Pr in let P2 := col_mx Pu Pd in 
        [/\ P1 *m P2 = 1%R,
          forall a : gT, a \in A i -> Pd *m (rW (fG' a) *m Pr) = 1%:M & 
            \sum_(a \in A i) Pu *m (rW (fG' a) *m Pl) = 0].
  rewrite -(mulmx1 (gamma i)) idmxE -P12_id mulmxA mxtrace_mulC mul_mx_row.
  rewrite mul_col_row mxtrace_block /gamma !mulmx_suml !mulmx_sumr eqr mxtrace0.
  rewrite add0r (eq_bigr _ eql) sumr_const raddfMn /= mxtrace1.
  by rewrite natrM /= mulr_natr.
have pWbar : p.-group Wbar.
  apply: morphim_pgroup; rewrite -pnat_exponent exponent_mx_group // pnat_exp.
  by rewrite pnat_id.
have homoWbar : homocyclic Wbar.
  have := (sub_isog (subxx _) injm_fW); move/isog_homocyclic<-.
  exact: mx_group_homocyclic.
have expWbar : exponent Wbar = q.
  rewrite exponent_injm ?subxx //; exact: exponent_mx_group.
have im_fG : fG @* G1 = G by rewrite morphim_restrm setIid.
have im_fG' : fG' @* G = G1 by rewrite -im_fG morphim_invm.
have hcent_com :  [~: Wbar, Aibar] \x 'C_(Wbar)(Aibar) = Wbar.
  apply: coprime_abelian_cent_dprod.
  - rewrite /= im_fW; apply: subset_trans nG1W.
    rewrite -[X in _ \subset (pred_of_set X)]im_fG'. (*???*)
    apply: morphimS; exact: sAiG.
  - apply: coprime_morphl; apply: coprime_morphr; apply:(coprimegS (sAiG _ hi)).
    by rewrite cardsT /= card_matrix mul1n /= card_ord Zp_cast ?coprime_expl.
  - by apply: morphim_abelian; apply: zmod_abelian.
have := (abelian_type_dprod_homocyclic hcent_com pWbar homoWbar).
rewrite expWbar => [] [atypel atyper].
have [hc_com  hc_cent] : 
  homocyclic [~: Wbar, Aibar] /\ homocyclic 'C_Wbar(Aibar).
  by apply: (@dprod_homocyclic _ p _ _ _ hcent_com).
have /isogP [isol injm_isol isol_im] : 
  [~: Wbar, Aibar] \isog [set: 'rV['Z_q]_(rC)%N].
  rewrite eq_abelian_type_isog ?zmod_abelian ?atypel //; last first. 
    by case/andP: hc_com.
  by rewrite abelian_type_mx_group // mul1n eqxx.
have dom_fPu: setT \subset 'dom (invm injm_fW \o invm injm_isol).
  rewrite /dom morphpre_invm -isol_im morphimS // -/Wbar.
  by case/dprodP: hcent_com => _ /mulG_sub[].
have mkMxM m1 m2 D1 (g : {morphism gval D1 >-> 'rV['Z_q]_m2}) :
  [set: 'rV['Z_q]_m1] \subset 'dom g -> linear g.
  move/subsetP=> sTD1 z x y; rewrite morphM ?sTD1 ?in_setT //.
  by rewrite -(natr_Zp z) !scaler_nat -zmodXgE morphX ?sTD1 ?in_setT.
pose mkMx sDT1 := lin1_mx (Linear (mkMxM _ _ _ _ sDT1)).
pose Pu := mkMx _ _ _ _ dom_fPu.
have abelCbar : abelian 'C_Wbar(Aibar) by case/andP: hc_cent.
have rCbar : 'r('C_Wbar(Aibar)) = lp i.
    rewrite -['r('C_Wbar(_))]rank_Ohm1.
  have /rank_abelem -> : p.-abelem 'Ohm_1('C_Wbar(Aibar)).
    apply: Ohm1_abelem; rewrite // (pgroupS (subsetIl _ _)) ?morphim_pgroup //.
    by rewrite -pnat_exponent exponent_mx_group // pnat_exp pnat_id.
  congr (logn _ _); rewrite /= -(erefl (gval Wbar)).
  transitivity #|'C_Wbar(Aibar) : 'Mho^1('C_Wbar(Aibar))|.
    by rewrite -divgS ?Mho_sub // -(mul_card_Ohm_Mho_abelian 1 abelCbar) mulnK.
  transitivity #|'C_Wbar(Aibar) : 'Mho^1(Wbar)|.
    symmetry; rewrite -indexgI; congr #|_ : _|.
    have /dprodP[_ /= <- _ _] := Mho_dprod 1 hcent_com.
    rewrite -group_modr ?Mho_sub // [_ :&: _](trivgP _) ?mul1g //= setIC.
    by have /dprodP[_ _ _ <-] := hcent_com; rewrite setSI ?Mho_sub.
  suff /card_isog -> : 'C_V(A i) \isog 'C_Wbar(Aibar) / 'Mho^1(Wbar).
    rewrite card_quotient //; apply: subset_trans (subsetIl _ _) _.
    by case/andP: (Mho_normal 1 Wbar).
  rewrite coprime_quotient_cent ?Mho_sub // /Wbar /= im_fW ?abelian_sol //.
  - case: (first_isom f) => factm ifactm factmim.
    have h: fG' @* A i / 'ker f \subset D / 'ker f.
      apply: quotientS; apply: subset_trans (morphimS _ (sAiG _ hi)) _.
      by rewrite -im_fG morphim_invm.
    have := (injm_subcent ifactm (W / 'ker f) h); rewrite !factmim imfW.
    have -> : f @* (fG' @* A i) = A i.
      rewrite /fG' morphim_invmE /= morphpre_restrm morphim_setIpre imfG1.
      apply/setIidPr; exact: sAiG.
    move<-; rewrite -kerf; rewrite isog_sym; apply: sub_isog => //.
    apply: subset_trans (subsetIl _ _) _; apply: quotientS. 
    by case/sdprodP: sdD=> _ <- _ _; apply: mulG_subl.
  - apply: subset_trans (morphimS _ (sAiG _ hi)) _ => /=.
    rewrite im_fG' -kerf; apply: subset_trans (ker_norm _).
    by case/sdprodP: sdD=> _ <- _ _; rewrite mulG_subr.
  - by rewrite oW coprime_morphr ?coprime_expl //; apply:(coprimegS (sAiG _ hi)).
have /isogP [isor injm_isor isor_im] : 
  'C_Wbar(Aibar) \isog [set: 'rV['Z_q]_(lp i)].
  rewrite eq_abelian_type_isog // ?zmod_abelian //. 
  by rewrite atyper rCbar abelian_type_mx_group // mul1n eqxx.
have dom_fPd: setT \subset 'dom (invm injm_fW \o invm injm_isor).
   by rewrite /dom morphpre_invm -isor_im morphimS // subsetIl.
pose Pd := mkMx _ _ _ _ dom_fPd.
have comWbar: (@pair1g _ _ \o isor) @* 'C_Wbar(Aibar) \subset
        'C((@pairg1 _ _ \o isol) @* [~: Wbar, Aibar]).
  rewrite !morphim_comp morphim_pair1g morphim_pairg1.
  set Ur := isor @* _; set Ul := isol @* _.
  by case/dprodP: (setX_dprod [group of Ul] [group of Ur]).
set fUr := @pair1g _ _ \o _ in comWbar.
have /domP [fUr' [efUr' kerfUr' invfUr' imfUr']] : 
    'dom fUr =  'C_Wbar(Aibar) by rewrite /dom -isor_im injmK.
set fUl := @pairg1 _ _ \o _ in comWbar.
have /domP [fUl' [efUl' kerfUl' invfUl' imfUl']] : 
    'dom fUl = [~: Wbar, Aibar] by rewrite /dom -isol_im injmK.
rewrite -imfUr' -imfUl' in comWbar.
pose isoWbar := dprodm hcent_com comWbar.
pose fPl := (@fst _ _)  \o (isoWbar \o fW).
pose fPr := (@snd _ _)  \o (isoWbar \o fW).
have dom_fPl : setT \subset 'dom fPl by rewrite -!sub_morphim_pre ?subsetT.
have dom_fPr : setT \subset 'dom fPr by rewrite -!sub_morphim_pre ?subsetT.
pose Pl := mkMx _ _ _ _ dom_fPl; pose Pr := mkMx _ _ _ _ dom_fPr.
simpl in fPl, fUl, fUr, fPr, fUr', imfUr', fUl', imfUl', Pl, Pr |- *.
simpl in dom_fPl, dom_fPr |- *.
case/dprodP: (hcent_com) => _ ep sp ip.
exists (Pl, Pr, Pu, Pd) => /=; split.
- apply/row_matrixP=> r; rewrite rowE -row1 mul_row_col linearD /= !mulmxA.
  rewrite  !{1}mul_rV_lin1 /=. (* long rw *)
  apply: (injmP _ injm_fW); rewrite ?in_setT // morphM ?in_setT // efUl' efUr'.
  rewrite /= mulg1 mul1g.
  have aux : fW (row r 1%:M) \in Wbar.
    by apply: mem_morphim; rewrite in_setT.
  have hinr : divgr [~: Wbar, Aibar]
     'C_(Wbar)(Aibar) (fW (row r 1%:M)) \in Wbar.
    rewrite -{3}ep; apply: (subsetP (mulG_subl _ _)); apply: mem_divgr. 
    by rewrite ep.
  have hinl : remgr [~: Wbar, Aibar]
     'C_(Wbar)(Aibar) (fW (row r 1%:M)) \in Wbar.
    rewrite -{3}ep; apply: (subsetP (mulG_subr _ _)); apply: mem_remgr. 
    by rewrite ep.
  rewrite invmE //=; last by apply: mem_divgr; rewrite ep.
  rewrite !{1}invmK //; last first.
    by rewrite invmE //; apply: mem_remgr; rewrite ep.
  rewrite !invmE //; last by apply: mem_remgr; rewrite ep.
  by rewrite -!divgr_eq.
- move=> a Aia; apply/row_matrixP=> j; rewrite rowE !mulmxA !mul_rV_lin1 /=.
  rewrite efUl' efUr' /= mul1g. (*sdpair_act ?in_setT //=; last exact: subgP.*)
  set a' :=  sgval (subg G1 (fG' a)).
  rewrite invmK; last first.
    rewrite -ep. apply: (subsetP (mulG_subr _ _)).
    have : (delta_mx 0 j) \in [set: 'rV['Z_q]_(lp i)]%G by rewrite in_setT.
    by rewrite -isor_im -morphpre_invm; case/morphpreP.
  have hd : (delta_mx 0 j) \in [set: 'rV['Z_q]_(lp i)]%G by rewrite in_setT.
  have a'Aibar :  a' \in Aibar.
    rewrite /a' /Aibar; set x := subg G1 _.
    have {x} -> : sgval x = sgval (subg (fG' @* G) (fG' a)).
      by rewrite /x !val_insubd; case: ifP; rewrite -{1}im_fG'; move->.
    rewrite -(subgmK (morphimS _ (sAiG _ hi))); apply: mem_morphim.
      by rewrite inE.
    apply: mem_morphim => /=; apply: mem_morphim => //=; 
        rewrite ?im_fG; exact: (subsetP (sAiG _ hi)).
    set d := invm _ _.
      have hdC : d \in 'C_Wbar(Aibar).
        have : (delta_mx 0 j) \in [set: 'rV['Z_q]_(lp i)]%G by rewrite in_setT.
        by rewrite -isor_im -morphpre_invm; case/morphpreP.  
      have -> : d ^ a' = d.
        suff hC : commute d a' by rewrite /conjg hC mulKg.
        move: hdC; rewrite in_setI; case/andP=> _; move/centP. 
        by move/(_ _ a'Aibar).
  rewrite remgr_id //; last first.
    by rewrite  DfW' /= invmK // -ep (subsetP (mulG_subr _ _)).
  rewrite DfW' /= invmK; last by rewrite -ep (subsetP (mulG_subr _ _)).
  by rewrite rowE mulmx1 /d invmK // isor_im.
apply/row_matrixP=> j; rewrite rowE mulmx_sumr.
set  d := invm injm_isol (delta_mx 0 j).
have hd : d \in [~: Wbar, Aibar].
  have : (delta_mx 0 j) \in [set: 'rV['Z_q]_(_)]%G by rewrite in_setT.
  by rewrite -isol_im -morphpre_invm; case/morphpreP.
have ha a : a \in A i -> 
    delta_mx 0 j *m (Pu *m (rW (fG' a) *m Pl)) = 
    isol (d ^ (fG' a)).
  move => Aia; set a' :=  sgval (subg G a).
  have ha' : a' \in A i.
    rewrite -(subgmK (sAiG _ hi)); apply: mem_morphim; first by rewrite inE.
    by apply: mem_morphim; rewrite //; apply: (subsetP (sAiG _ hi)).
  have s2a' : fG' a' \in Aibar.
    by rewrite mem_morphim //= im_fG; apply: (subsetP (sAiG _ hi)).
  rewrite !mulmxA !mul_rV_lin1 /= efUl' efUr' /= mulg1 invmK; last first.
    by rewrite -/Wbar -{2}ep; apply: (subsetP (mulG_subl _ _)).
  have Ga : a \in G by apply: (subsetP (sAiG _ hi)).
  set sa := sgval _.
  have {sa} -> : sa = fG' a.
    by rewrite /sa val_insubd -{1}im_fG' mem_morphim //= ?im_fG // im_fW.
  have hdJ : fW (fW' (d ^ (fG' a))) = d ^ fG' a.
    rewrite DfW' invmK // memJ_norm //.
      by rewrite -ep; apply: (subsetP (mulG_subl _ _)).
    rewrite im_fW; apply: (subsetP nG1W).
    by rewrite -im_fG' mem_morphim /= ?im_fG.
  rewrite divgr_id ?hdJ // memJ_norm //= im_fW.
  by apply: (subsetP (commg_normr _ _)); rewrite mem_morphim //= ?im_fG.
rewrite (eq_bigr _ ha).
have he a : a \in A i -> fG (fG' a) = a.
  move=> Aia; rewrite /fG'; apply: invmK; rewrite im_fG.
  exact: (subsetP (sAiG _ hi)).
rewrite (reindex_onto _ _ he) /= {he}.
transitivity (\sum_(a \in Aibar) isol (d ^ a)).
  apply: congr_big => // x; last by case/andP=> _ /eqP ->.
  apply/andP/idP => [[] hAi /eqP <- |Aibara].
    apply: mem_morphim => //=; rewrite im_fG;  exact: (subsetP (sAiG _ hi)).
  split; last first.
     apply/eqP; apply: invmE; rewrite -im_fG'.
     exact: (subsetP (morphimS _ (sAiG _ hi))).
  have <- : fG @* (fG' @* (A i)) = A i.
    by rewrite morphim_invmE; apply: morphpreK; rewrite /= im_fG sAiG. 
  apply: mem_morphim=> //; rewrite -im_fG'. 
  exact: (subsetP (morphimS _ (sAiG _ hi))).
(* may be partition_big_imset is more efficient...*)
have he x : x \in commg_set Wbar Aibar ->
                 \sum_(a \in Aibar) isol (x ^ a) = 0.
  case/imset2P=> w a hw {ha} ha ->.
  have he b : b \in Aibar -> 
      isol ([~ w, a] ^ b) = isol [~ b, w] + isol [~ w, a * b].
    have -> : [~ w, a] ^ b = [~ b, w] * [~ w, a * b].
      by rewrite commgMJ mulgA -(invg_comm b w) mulgV mul1g.
    move=> hb.
    have dc1 : [~ b, w] \in [~: Wbar, Aibar].
      rewrite -[[~ _, _]]invgK groupV invg_comm; exact: mem_commg.
    suff dc2 : [~ w, a * b] \in [~: Wbar, Aibar] by rewrite morphM.
    by apply: mem_commg=> //; rewrite groupM.
  rewrite (eq_bigr _ he) {he} big_split /=.
  rewrite (reindex_inj (mulgI a)) /=.
  have he b : a * b \in Aibar = (b \in Aibar) by rewrite groupMl.
  rewrite (eq_bigl _ _ he).
  have {he} he b : b \in Aibar -> isol [~ a * b, w] = - isol [~ w, a * b].
    move=> bAibar; rewrite -(invg_comm w (a * b)) morphV //.
      by apply: mem_commg=> //; rewrite groupM.
    by rewrite (eq_bigr _ he) sumrN addNr.
  case/gen_prodgP: hd=> r [phi mem_phi] ->.
  pose h a := (\prod_i0 phi i0) ^ a.
  have he' a : a \in Aibar ->  
    isol ((\prod_i0 phi i0) ^ a) =  isol (\prod_i0 (phi i0) ^ a).
    move=> Aibara; congr (fun x => isol x). 
    by apply: (big_morph (conjg^~ a)); rewrite ?conj1g // => ? ?; rewrite conjMg.
  rewrite (eq_bigr _ he') {he'}.
  suff -> : \sum_(i0 \in Aibar) isol (\prod_i1 phi i1 ^ i0)%g = 
    \prod_i1 (\sum_(i0 \in Aibar) isol  (phi i1 ^ i0)%g).
    by rewrite big1 => [|? _]; rewrite ?he // rowE mulmx0.
  rewrite exchange_big; apply: eq_bigr=> b bAibar /=; apply: big_morphG.
  move=> u _; rewrite memJ_norm; first by apply: mem_gen; exact: mem_phi.
  exact: (subsetP (commg_normr _ _)).
Qed.
