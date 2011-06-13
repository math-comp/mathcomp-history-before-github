(* (c) Copyright Microsoft Corporation and Inria. All rights reserved. *)
Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq path div.
Require Import fintype bigop prime binomial finset ssralg fingroup finalg.
Require Import morphism perm automorphism quotient action commutator gproduct.
Require Import zmodp cyclic center pgroup gseries nilpotent sylow finalg finmodule.
Require Import abelian frobenius maximal extremal hall finmodule.
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

(*
Section ExtrasForHuppertBlackburn_5_9.

Implicit Type gT : finGroupType.

Lemma  bigprod_expg : forall gT I r (P : pred I) (F : I -> gT)(G : {group gT}) n, 
  abelian G -> (forall i, P i -> F i \in G) -> 
    (\prod_(i <- r | P i) F i) ^+ n = \prod_(i <- r | P i) (F i ^+ n).
Proof.
move=> gT I r P F G n cGG inG; elim: r => [| x r ih] /=. 
  by rewrite !big_nil exp1gn.
rewrite !big_cons; case Px: (P x) => //; rewrite -ih expMgn //; red.
rewrite -(centsP cGG) //; first exact: group_prod.
exact: inG.
Qed.

Lemma bigprod_norm :  forall gT I r (P : pred I) F (X : {group gT}), 
    (forall i, P i -> X \subset 'N(F i)) -> 
    X \subset 'N( \prod_(i <- r | P i) F i).
Proof.
move=> gT I r P F X Xn; elim: r => [| x r ih] /=.
  by rewrite big_nil norm1 subsetT.
rewrite big_cons; case Px : (P x) => //; rewrite normsM //; exact: Xn.
Qed.

End ExtrasForHuppertBlackburn_5_9.
*)

Section HuppertBlackburn_5_9.

Implicit Types (gT : finGroupType) (p : nat).

Lemma huppert_blackburn_5_9 gT p (A X : {group gT}) :
    abelian A -> p.-group A -> p^'.-group X -> X \subset 'N(A) -> 
  exists2 s : {set {group gT}}, \big[dprod/1]_(B \in s) B = A
      & forall B, B \in s -> [/\ homocyclic B, X \subset 'N(B)
        & acts_irreducibly X (B / 'Phi(B)) 'Q].
Proof. Admitted. (*
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
  by rewrite -expgn_mul -expnSr -eA -order_dvdn dvdn_exponent.
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
    by move=> x y Ax Ay /=; rewrite expMgn // /commute -(centsP cAA).
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
Qed. *)

End HuppertBlackburn_5_9.

Section HuppertBlackburn_12_3.

Implicit Types (gT : finGroupType) (m n p q : nat).

Lemma huppert_blackburn_12_3 gT (V G : {group gT}) p m :
    minnormal V G -> coprime p #|G| -> p.-abelem V -> m > 0 ->
    let W := [set: 'rV['Z_(p ^ m)](V)]%G in
  exists2 f : {morphism V >-> coset_of 'Mho^1(W)},
    isom V (W / 'Mho^1(W)) f
  & exists toW : groupAction G W,
    {in V & G, morph_act 'J (toW / 'Mho^1(W)) f (idm G)}.
Proof. Admitted. (*
move=> minV copG abelV m_gt0; set q := (p ^ m)%N => W.
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
have{copG} p'G: p^'.-group G by rewrite /pgroup p'natE // -prime_coprime.
have p'X: p^'.-group X by rewrite morphim_pgroup.
have nXL: X \subset 'N(L) := im_sdpair_norm MR_G.
have [injL injX] := (injm_sdpair1 MR_G, injm_sdpair2 MR_G).
have [/= S defL im_S] := huppert_blackburn_5_9 cLL pL p'X nXL.
pose gi (z : 'Z_q) := z%:R : 'F_p.
have giM: rmorphism gi.
  split=> [z1 z2|]; last split=> // z1 z2.
    apply: canRL (addrK _) _; apply: val_inj.
    by rewrite -{2}(subrK z2 z1) -natr_add /= !val_Fp_nat ?modn_dvdm // Zp_cast.
  by apply: val_inj; rewrite -natr_mul /= !val_Fp_nat ?modn_dvdm // Zp_cast.
pose g u := map_mx (RMorphism giM) (invm injL u).
have gM: {in L &, {morph g : u v / u * v}}.
  by move=> u v Lu Lv /=; rewrite {1}/g morphM // map_mxD.
have kerg: 'ker (Morphism gM) = 'Phi(L).
  rewrite (Phi_Mho pL cLL) (MhoEabelian 1 pL cLL).
  apply/setP=> u; apply/idP/imsetP=> [ | [v Lv ->{u}]]; last first.
    rewrite !inE groupX //=; apply/eqP/rowP=> i; apply: val_inj.
    rewrite !mxE morphX // mulmxnE Zp_mulrn /= val_Fp_nat //=.
    by move: {i}(_ i); rewrite Zp_cast // => vi; rewrite modn_dvdm // modn_mull.
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
have [sUL isoWU]: U \subset L /\ isog W U.
  have [homU _ _] := im_S U S_U; have [cUU _] := andP homU.
  rewrite eq_abelian_type_isog ?zmod_abelian // abelian_type_mx_group // mul1n.
  rewrite (big_setD1 U) //= in defL.
  have [[_ U' _ defU'] defUU' _ tiUU'] := dprodP defL.
  rewrite defU' in defL defUU' tiUU'.
  have{defUU'} sUL: U \subset L by case/mulG_sub: defUU'.
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
have [f1 injf1 f1W] := isogP isoWU.
have Uf1: f1 _ \in U by move=> w; rewrite -f1W mem_morphim ?inE.
pose f3 w := rVabelem abelV ntV (in_submod _ (g (f1 w)) *m h).
have f3M: {in W &, {morph f3: w1 w2 / w1 * w2}}.
  move=> w1 w2 Ww1 Ww2 /=; rewrite {1}/f3 morphM {Ww1 Ww2}//.
  rewrite gM ?(subsetP sUL) ?Uf1 // linearD mulmx_addl.
  by rewrite morphM ?mem_im_abelem_rV.
have ker_f3: 'ker (Morphism f3M) = 'Mho^1(W).
  apply/setP=> w; rewrite !inE /=.
  rewrite morph_injm_eq1 ?rVabelem_injm ?mem_im_abelem_rV //=.
  rewrite -[1](mul0mx _ h) (inj_eq (row_free_inj h_free)) in_submod_eq0.
  have Ugw: (g (f1 w) <= gMx U)%MS.
    rewrite -mem_rowg (subsetP (sub_rowg_mx _)) //.
    by rewrite (mem_morphim (Morphism gM)) ?(subsetP sUL) ?Uf1.
  rewrite -[(_ <= _)%MS]andTb -Ugw -sub_capmx capmx_compl submx0.
  rewrite /= -{2}(im_invm injf1) -morphim_Mho // morphim_invmE !inE /= f1W.
  suff <-: 'ker_U (Morphism gM) = 'Mho^1(U) by rewrite !inE (subsetP sUL) Uf1.
  rewrite kerg (Phi_Mho pL cLL); rewrite (big_setD1 U) //= in defL.
  have [[_ U' _ defU'] _ _ tiUU'] := dprodP defL; rewrite defU' in defL tiUU'.
  rewrite setIC -(dprod_modl (Mho_dprod 1 defL) (Mho_sub 1 U)).
  by rewrite [_ :&: _](trivgP _) ?dprodg1 // -tiUU' setIC setSI ?Mho_sub.
have im_f3: Morphism f3M @* W = V.
  apply/eqP; rewrite eqEcard card_morphim setIid ker_f3.
  apply/andP; split.
    apply/subsetP=> v; case/morphimP=> w _ _ ->; exact: mem_rVabelem.
  have cWW: abelian W := zmod_abelian _.
  rewrite -divgS ?Mho_sub // -(mul_card_Ohm_Mho_abelian 1 cWW).
  have pW: p.-group W by rewrite (isog_pgroup _ isoWU) (pgroupS sUL).
  rewrite mulnK ?cardG_gt0 // (card_pgroup (pgroupS (Ohm_sub 1 W) pW)).
  rewrite -rank_abelian_pgroup // rank_mx_group mul1n.
  by rewrite (dim_abelemE abelV) // -card_pgroup ?(abelem_pgroup abelV).
have [f' injf' im_f'] := first_isom (Morphism f3M).
rewrite ker_f3 in f' injf' im_f'.
have dom_f: 'dom (invm injf') = V by rewrite /dom /= im_f'.
have [f [def_f ker_f _ im_f]] := domP (invm_morphism injf') dom_f.
exists f.
  apply/isomP; split; first by rewrite ker_f injm_invm.
  by rewrite /= -(im_invm injf') -im_f im_f' im_f3.
pose to w x := invm injf1 (f1 w ^ sdpair2 MR_G x).
have [_ nUX _] := im_S _ S_U.
have Uf1x: f1 _ ^ sdpair2 MR_G _ \in f1 @* W.
  move=> w x; rewrite f1W; case Gx: (x \in G).
    by rewrite memJ_norm ?(subsetP nUX) ?Uf1 ?mem_morphim.
  by rewrite /sdpair2 /insubd insubN ?conjg1 ?Uf1 // inE Gx.
have toJ: is_action G to.
  split=> [x w1 w2 eq_to_w_x | w x1 x2 Gx1 Gx2].
    apply: (injmP _ injf1) (in_setT _) (in_setT _) _.
    apply: (conjg_inj (sdpair2 MR_G x)).
    exact: (injmP _ (injm_invm injf1)) eq_to_w_x.
  by rewrite /to (morphM _ Gx1 Gx2) conjgM invmK.
have toJG: is_groupAction W (Action toJ).
  move=> x Gx /=; rewrite inE; apply/andP; split.
    by apply/subsetP=> ? _; exact: in_setT.
  by apply/morphicP=> w1 w2 Ww1 Ww2; rewrite !permE /= -!(morphM, conjMg).
exists (GroupAction toJG) => v x Vv Gx /=; rewrite /idm.
have [w Nw def_fv] := cosetP (f v).
rewrite def_fv qactE //; last first.
  rewrite (qact_domE (GroupAction toJG)) ?subsetT // inE Gx inE.
  apply/subsetP=> w1 W1w1; rewrite inE -sub1set -morphim_set1 //.
  rewrite sub_morphim_pre sub1set // morphpre_invm.
  rewrite memJ_norm ?mem_morphim ?in_setT //.
  rewrite morphim_Mho // f1W (subsetP (char_norms (Mho_char 1 U))) //.
  by rewrite (subsetP nUX) ?mem_morphim.
apply: (injmP _ injf'); rewrite ?mem_quotient ?in_setT //.
  by rewrite /= -quotientInorm setTI quotientT in_setT.
rewrite def_f invmK; last by rewrite im_f' im_f3 memJ_norm ?(subsetP nVG).
apply: set1_inj; rewrite -morphim_set1 ?mem_quotient ?in_setT //.
rewrite -quotient_set1 ?(subsetP (char_norm (Mho_char 1 _))) ?in_setT //.
rewrite im_f' morphim_set1 ?in_setT //= /f3 invmK //; congr [set _].
rewrite gJ ?(subsetP sUL) ?mem_morphim // /gx invmE //.
rewrite (in_submodJ modU); last first.
  rewrite -mem_rowg (subsetP (sub_rowg_mx _)) //.
  by rewrite (mem_morphim (Morphism gM)) ?(subsetP sUL).
rewrite -mulmxA hJ // mulmxA rVabelemJ //; congr (_ ^ x).
apply: set1_inj; rewrite -(morphim_set1 (Morphism f3M)) ?in_setT //.
rewrite -im_f' quotient_set1 // morphim_set1 ?mem_quotient ?in_setT //.
by rewrite -def_fv def_f invmK // im_f' im_f3.
Qed. *)


End HuppertBlackburn_12_3.

(* Auxiliary lemma for the second part of the proof *)
Lemma expdiv_0 : forall p x, p > 1 -> 
  (forall n, n > 0 -> p ^ n %| x) -> x = 0%N.
Proof.
move=> p x ltp1 hdiv; apply/eqP; case abs: (x == 0%N) => //.
suff [m pmlex] : {m | p ^ m > x}.
  have mgt0 : 0 < m.
    rewrite lt0n; move: pmlex;  case m0: (m == 0%N) => //.
    by rewrite (eqP m0) expn0 ltnS leqn0 abs.
  move: (hdiv _ mgt0); move: (lt0n x); rewrite abs /= => xgt0.
  by move/(dvdn_leq xgt0); rewrite leqNgt pmlex.
elim: x {hdiv abs} => [|n [k hk]]; first by exists 0%N.
exists k.+1.
suff h : (p ^ k).+1 <= p ^k.+1 by apply: leq_trans h.
by rewrite expnS; apply: ltn_Pmull => //; apply: leq_trans hk.
Qed.

Lemma exprdiv_eq : forall p x y, p > 1 -> 
  (forall n, n > 0 -> x = y %[mod p ^ n]) -> x = y.
Proof.
move=> p x y; wlog hwlog : x y / x <= y.
  move=> hwlog lt1p hmod; case: (leqP x y) => hxy; first by exact: hwlog.
  apply: sym_eq; apply: hwlog => // [| n lt0n]; first by rewrite ltnW.
  by apply: sym_eq; apply: hmod.
move=> lt1p hmod; apply/eqP; rewrite eqn_leq hwlog /= -subn_eq0; apply/eqP.
apply: (expdiv_0 lt1p) => n lt0n; rewrite (divn_eq y (p ^ n)).
by rewrite (divn_eq x (p ^ n)) (hmod _ lt0n) subn_add2r -muln_subl dvdn_mull.
Qed.

Lemma muln_sum :  forall (R : ringType) I r P (F : I -> nat),
  \sum_(i <- r | P i) (F i)%:R  = (\sum_(i <- r | P i) F i)%:R :> R.
Proof.
move=> R I r P F; apply: sym_eq.
exact: (big_morph _ (fun x1 y1 : nat => natr_add _ x1 y1) (refl_equal 0%:R)).
Qed.

Theorem solvable_Wielandt_fixpoint : forall (I : finType) (gT : finGroupType),
    forall (A : I -> {group gT}) (n m : I -> nat) (G V : {group gT}),
    (forall i, m i + n i > 0 -> A i \subset G) ->
    G \subset 'N(V) -> coprime #|V| #|G| -> solvable V ->
    {in G, forall a, \sum_(i | a \in A i) m i = \sum_(i | a \in A i) n i}%N ->
  (\prod_i #|'C_V(A i)| ^ (m i * #|A i|)
    = \prod_i #|'C_V(A i)| ^ (n i * #|A i|))%N.
Proof.
move=> I gT A n m G V; move: {2}_.+1 (ltnSn #|V|) => c.
rewrite (bigID (fun i => 0 < m i + n i)) /=.
rewrite (big1 (fun i => ~~ (0 < m i + n i))); last first.
  move=> j; rewrite -eqn0Ngt addn_eq0; case/andP; move/eqP->.
  by rewrite mul0n expn0.
rewrite [(\prod_i _)%N](bigID (fun i => 0 < m i + n i)) /=.
rewrite (big1 (fun i => ~~ (0 < m i + n i))); last first.
  move=> j; rewrite -eqn0Ngt addn_eq0; case/andP=> _; move/eqP->.
  by rewrite mul0n expn0.    
rewrite !muln1 => leVm sAiG nVG copVG solV hGA *.
have {hGA} hGA : {in G, forall a : gT,
  (\sum_(i | (a \in A i) && (0 < m i + n i)) m i)%N = 
  (\sum_(i | (a \in A i) && (0 < m i + n i)) n i)%N}.
  move=> g Gg /=; move: (hGA g Gg).
  rewrite (bigID (fun i => 0 < m i + n i)) /=.
  rewrite (big1 (fun i => _ && ~~ (0 < m i + n i))); last first.
    by move=> j; case/andP=> _; rewrite -eqn0Ngt addn_eq0; case/andP; move/eqP.
  rewrite addn0 => ->; rewrite (bigID (fun i => 0 < m i + n i)) /=.
  rewrite (big1 (fun i => _ && ~~ (0 < m i + n i))) //. 
  by move=> j; case/andP=> _; rewrite -eqn0Ngt addn_eq0; case/andP=> _; move/eqP.
move: leVm sAiG nVG copVG solV hGA.
elim: c  => // c IHc in I gT A G V n m *;
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
  have cardps : forall j : I, A j \subset G ->
 #|'C_V(A j)| = (#|'C_B(A j)| * #|'C_(V / B)(A j / B)|)%N.
    move=> j sAjG.
    have nVAj : A j \subset 'N(V) by exact: subset_trans nVG.
    have nBAj : A j \subset 'N(B) by exact: subset_trans nBG.
    have copVAj : coprime #|V| #|A j| by exact: (coprimegS sAjG).
    have copBAj : coprime #|B| #|A j| by rewrite  (coprimegS sAjG).
    rewrite -(coprime_quotient_cent sBV nBAj copVAj solV).
    have -> : 'C_B(A j) = 'C_V(A j) :&: B.
      by rewrite [_ :&: B]setIC setIA (setIidPl sBV).
    by rewrite card_quotient ?LaGrangeI // subIset ?nBV.
  have hp : forall mm j, 0 < m j + n j ->  
     (#|'C_V(A j)| ^ (mm j * #|A j|))%N  = 
     ((#|'C_B(A j)| ^ (mm j * #|A j|) * 
       (#|'C_(V / B)(A j / B)|) ^ (mm j * #|A j / B|)))%N.
    move=> mm j; move/sAiG=> sAjG.
    have nBAj : A j \subset 'N(B) by exact: subset_trans nBG.
    have copBAj : coprime #|B| #|A j| by rewrite  (coprimegS sAjG).
    rewrite -(card_isog (quotient_isog _ _)) ?(coprime_TIg copBAj) // -expn_mull.
    by rewrite cardps.
  rewrite !(eq_bigr _ (hp _)) !big_split /=; congr (_ * _)%N.
    exact: (IHc _ _ _ G).
  have cardQ : #|V / B| < c by apply: leq_trans leVm; apply: ltn_quotient.
  have sAQ : forall i : I, 0 < m i + n i -> A i / B \subset G / B.
    move=> i si; apply: quotientS; exact: sAiG.
  have nQ : G / B \subset 'N(V / B) by apply: quotient_norms.
  have copQ : coprime #|V / B| #|G / B| by exact: coprime_morph.
  have solQ : solvable (V / B) by exact: quotient_sol.
  apply: (IHc _ _ _ (G / B)%G) => //.
  move=> g; case/morphimP=> x /= Nx Gx ->.
  have hindex : forall i,
    (coset B x \in A i / B) && (0 < m i + n i)%N  = 
  (x \in A i) && (0 < m i + n i)%N.
    move=> j; case lt0s : (0 < m j + n j); rewrite ?andbF ?andbT //.
    have sAjG := sAiG _ lt0s; move/sAQ: lt0s=> sAjBQ; 
    have nBAj : A j \subset 'N(B) by exact: subset_trans nBG.
    apply/idP/idP; last by move/mem_quotient.
    move/(mem_morphpre (subsetP nBG _ Gx)); rewrite /= quotientK // => BAx.
    have : x \in G :&: (B * A j) by rewrite in_setI Gx.
    rewrite -group_modr //; move: copBG; rewrite coprime_sym.
    by move/coprime_TIg->; rewrite mul1g.
  rewrite !(eq_bigl _ _ hindex) /=; exact: hGA.
have [p primep pabV] := is_abelemP (minnormal_solvable_abelem minV solV).
pose f i := logn p #|'C_V(A i)|.
have hindex : forall mn i, 0 < m i + n i -> 
  (#|'C_V(A i)| ^ (mn i * #|A i|) = 
    p ^ (f i * (mn i) * #|A i|))%N.
  move=> mn i _.
  have : p.-group 'C_V(A i).
    by apply: (pgroupS _ (abelem_pgroup pabV));apply: subsetIl.
  by move/card_pgroup=> h; rewrite {1}h {h} -expn_mulr mulnA.
rewrite !(eq_bigr _ (hindex _)) {hindex} -!expn_sum; congr (_ ^ _)%N.
have coppG : coprime p #|G|.
  apply: (coprime_dvdl _ copVG); move/abelem_pgroup: pabV.
  move/card_pgroup=> e; rewrite e; apply: dvdn_exp => //.
  rewrite lt0n; case abs : ( logn p #|V| == 0%N) => //.
  move: e; rewrite (eqP abs) expn0; move/card1_trivg=> e.
  by rewrite e eqxx in ntV.
have{minV} minV: minnormal V G.
  apply/mingroupP; split=> [|B nBG sBV]; first by rewrite ntV nVG.
  case/mingroupP: minV => _; apply=> //.
  by rewrite join_subG (sub_abelian_norm (abelem_abelian pabV)).
have hb123 := huppert_blackburn_12_3 minV coppG pabV.
apply: (exprdiv_eq (prime_gt1 primep)) => k lt0k.
pose q := (p ^ k)%N.
have {hb123} [fVW isomfVW [/= toW htoW]] := (hb123 _ lt0k).
have toWlin: forall g, linear (toW^~ (val (subg G g))).
  move=> g z /= x y; rewrite gactM ?in_setT ?subgP //; congr (_ * _). 
  by rewrite -(natr_Zp z) !scaler_nat gactX ?in_setT ?subgP.
pose rW g := lin1_mx (Linear (toWlin g)).
have is_action_rW : (mx_repr G rW).
  split.
    by apply/matrixP=> i j /=; rewrite mxE /= subgK // act1 !mxE eqxx eq_sym.
  move=> x y Gx Gy /=; apply/row_matrixP=> i; rewrite row_mul mul_rV_lin1 /=.
  by rewrite subgK // !rowK /= !subgK ?groupM // actMin. 
have pk_gt1 : q > 1 by rewrite  -(exp1n k) ltn_exp2r // prime_gt1.
suff tr_rW_Ai : forall i, 0 < m i + n i  ->
  {in A i, forall x : gT, \tr (rW x) = (f i)%:R}.
  pose gamma i := \sum_(x \in A i) rW x.
  have: \sum_(i | 0 < m i + n i) (gamma i) *+ m i = 
        \sum_(i | 0 < m i + n i) (gamma i) *+ n i.
    have hp : forall mn i, 0 < m i + n i -> 
      gamma i *+ mn i = \sum_(x \in A i) (rW x) *+ mn i.
      by move=> mn i _; rewrite sumr_muln.
    rewrite !(eq_bigr _ (hp _)). 
    have side : forall i j, 0 < m i + n i -> j \in A i -> j \in G.
      by move=> i j hmn; apply: (subsetP (sAiG _ _)).
    rewrite !(exchange_big_dep (fun x => x \in G)) // {side} /=. 
    apply: eq_bigr => g Gg; rewrite !sumr_muln_r; congr (_ *+ _).
    transitivity (\sum_(i | (g \in A i) && (0 < m i + n i)) m i)%N.
      by apply: eq_bigl => i; rewrite andbC.
    transitivity (\sum_(i | (g \in A i) && (0 < m i + n i)) n i)%N.
      exact: hGA.
    by apply: eq_bigl => i; rewrite andbC.
  have hp : forall mn i, 0 < m i + n i -> 
    gamma i *+ mn i = \sum_(x \in A i) (rW x) *+ mn i. 
    by move=> mn i; rewrite sumr_muln.
  rewrite !(eq_bigr _ (hp _)); move/(f_equal mxtrace); rewrite !raddf_sum /=. 
  have {hp} hp : forall mn i, 0 < m i + n i -> 
    \tr (\sum_(x \in A i) rW x *+ mn i) = (f i * mn i * #|A i|)%:R.
    move=> mn i hi; rewrite raddf_sum /= !natr_mul !mulr_natr.
    have hp' : forall x, x \in A i -> \tr (rW x *+ mn i) = ((f i)%:R) *+ mn i.
      by move=> x Aix; rewrite raddfMn /= (tr_rW_Ai _ hi _ Aix).
    by rewrite (eq_bigr _ hp') /= sumr_const. 
  rewrite !(eq_bigr _ (hp _)) !muln_sum; move/(f_equal (@nat_of_ord _)).
  by rewrite !val_Zp_nat.
move=> i hi a Aia.
pose Aibar := (sdpair2 toW) @* (A i). 
pose Wbar := ((sdpair1 toW) @* [set: 'rV(V)])%G.
have hcent_com :  [~: Wbar, Aibar] \x 'C_(Wbar)(Aibar) = Wbar.
  apply: coprime_abelian_cent_dprod.
  - by apply: subset_trans (im_sdpair_norm _); apply: morphimS; apply: sAiG.
  (* using external_action_im_coprime is not really shorter *)
  - apply: coprime_morphl; apply: coprime_morphr; apply:(coprimegS (sAiG _ hi)).
    by rewrite cardsT /= card_matrix mul1n /= card_ord Zp_cast ?coprime_expl.
  - by apply: morphim_abelian; apply: zmod_abelian.
have homoWbar : homocyclic Wbar.
  have := (sub_isog (subxx _) (injm_sdpair1 toW)); move/isog_homocyclic<-.
  exact: mx_group_homocyclic.
have pWbar : p.-group Wbar.
  apply: morphim_pgroup; rewrite -pnat_exponent exponent_mx_group // pnat_exp.
  by rewrite pnat_id.
have [hc_com  hc_cent] : 
  homocyclic [~: Wbar, Aibar] /\ homocyclic 'C_Wbar(Aibar).
  apply: (@dprod_homocyclic _ p _ _ _ hcent_com) => //.
have abelCbar : abelian 'C_Wbar(Aibar).
  by rewrite (abelianS (subsetIl _ _)) // morphim_abelian // zmod_abelian.
have rCbar : 'r('C_Wbar(Aibar)) = f i.
  rewrite -['r('C_Wbar(_))]rank_Ohm1.
  have /rank_abelem -> : p.-abelem 'Ohm_1('C_Wbar(Aibar)).
    apply: Ohm1_abelem => //; rewrite (pgroupS (subsetIl _ _)) ?morphim_pgroup //.
    by rewrite -pnat_exponent exponent_mx_group // pnat_exp pnat_id.
  congr (logn _ _); rewrite /= -(erefl (gval Wbar)).
  transitivity #|'C_Wbar(Aibar) : 'Mho^1('C_Wbar(Aibar))|.
    by rewrite -divgS ?Mho_sub // -(mul_card_Ohm_Mho_abelian 1 abelCbar) mulnK.
  transitivity #|'C_Wbar(Aibar) : 'Mho^1(Wbar)|.
    symmetry; rewrite -indexgI; congr #|_ : _|.
    have /dprodP[_ /= <- _ _] := Mho_dprod 1 hcent_com.
    rewrite -group_modr ?Mho_sub // [_ :&: _](trivgP _) ?mul1g //= setIC.
    by have /dprodP[_ _ _ <-] := hcent_com; rewrite setSI ?Mho_sub.
  have -> : 'C_Wbar(Aibar) = sdpair1 toW @* 'C_(|toW)(A i).
    by rewrite gacentEsd -morphpreIim morphpreK ?subsetIl.
  rewrite -morphim_Mho // index_injm ?injm_sdpair1 ?subsetT //=.
  have{sAiG} sAiG: A i \subset G := sAiG i hi; set W1 := 'Mho^1(_).
  transitivity #|'C_(|toW \ sAiG)(A i) / W1|.
    by rewrite gacent_ract setIid card_quotient 1?subIset ?gfunctor.gFnorm.
  have actsAi: [acts A i, on W1 | toW] by rewrite acts_char ?Mho_char.
  have actsAi_r: [acts A i, on W1 | toW \ sAiG] by rewrite acts_ract subxx.
  have cW1W1: abelian W1 := abelianS (Mho_sub _ _) (zmod_abelian _).
  rewrite ext_coprime_quotient_cent ?subsetT ?abelian_sol //= -/W1; last first.
    rewrite (coprimeSg (Mho_sub _ _)) // (coprimegS sAiG) //.
    by rewrite cardsT card_matrix card_ord Zp_cast // !coprime_expl.
  have /isomP[injf im_f] := isomfVW.
  rewrite -(card_injm injf) ?subsetIl ?injmI // gacentE ?qact_domE ?Mho_sub //.
  apply: eq_card => fv /=; rewrite 2!in_setI -{1}im_f.
  apply: andb_id2l => fVfv; have /morphimP[v _ Vv def_fv] := fVfv.
  have /morphimP[w nW1w Ww def_fv_w]: fv \in setT / _ by rewrite -im_f.
  rewrite -(morphpre_invm injf) {2}def_fv 2![in X in _ = X]inE mem_morphim //=.
  rewrite invmE // -afixJ.
  apply/afixP/afixP=> cAv x Ax; have Gx := subsetP sAiG x Ax.
    apply: (injmP _ injf); rewrite ?memJ_norm ?(subsetP nVG) // htoW //.
    rewrite -def_fv -{2}(cAv x Ax) def_fv_w /= !qactE //.
      by rewrite qact_domE ?Mho_sub // (subsetP actsAi_r).
    by rewrite qact_domE ?Mho_sub // (subsetP actsAi).
  rewrite {2}def_fv -(cAv x Ax) htoW // -def_fv def_fv_w !qactE //.
    by rewrite qact_domE ?Mho_sub // (subsetP actsAi).
  by rewrite qact_domE ?Mho_sub // (subsetP actsAi_r).
have expWbar : exponent Wbar = q.
  rewrite exponent_injm ?subxx ?injm_sdpair1 //; exact: exponent_mx_group.
have := (abelian_type_dprod_homocyclic hcent_com pWbar homoWbar).
rewrite expWbar => [] [atypel atyper].
have /isogP [isor injm_isor isor_im] : 'C_Wbar(Aibar) \isog [set: 'rV['Z_q]_(f i)].
  rewrite eq_abelian_type_isog // ?zmod_abelian // atyper rCbar.
  by rewrite abelian_type_mx_group // mul1n eqxx.
pose dV := 'dim V.
pose isoW := (sdpair1_morphism toW).
have injm_isoW : 'injm isoW by exact: injm_sdpair1.
pose rC := 'r([~: Wbar, Aibar]).
have abel_com : abelian [~: Wbar, Aibar] by case/andP: hc_com.
have /isogP [isol injm_isol isol_im] : 
  [~: Wbar, Aibar] \isog [set: 'rV['Z_q]_(rC)%N].
  rewrite eq_abelian_type_isog // ?zmod_abelian // atypel.
  by rewrite abelian_type_mx_group // mul1n eqxx.
have mkMxM m1 m2 D (g : {morphism gval D >-> 'rV['Z_q]_m2}) :
  [set: 'rV['Z_q]_m1] \subset 'dom g -> linear g.
- move/subsetP=> sTD z x y; rewrite morphM ?sTD ?in_setT //.
  by rewrite -(natr_Zp z) !scaler_nat -zmodXgE morphX ?sTD ?in_setT.
pose mkMx sDT := lin1_mx (Linear (mkMxM _ _ _ _ sDT)).
have dom_fPu: setT \subset 'dom (invm injm_isoW \o invm injm_isol).
  rewrite /dom morphpre_invm -isol_im morphimS // -/Wbar.
  by case/dprodP: hcent_com => _ /mulG_sub[].
pose Pu := mkMx _ _ _ _ dom_fPu.
have dom_fPd: setT \subset 'dom (invm injm_isoW \o invm injm_isor).
   by rewrite /dom morphpre_invm -isor_im morphimS // subsetIl.
pose Pd := mkMx _ _ _ _ dom_fPd.
have comWbar: (@pair1g _ _ \o isor) @* 'C_Wbar(Aibar) \subset
        'C((@pairg1 _ _ \o isol) @* [~: Wbar, Aibar]).
  rewrite !morphim_comp morphim_pair1g morphim_pairg1.
  set Ur := isor @* _; set Ul := isol @* _.
  by case/dprodP: (setX_dprod [group of Ul] [group of Ur]).
set fUr := @pair1g _ _ \o _ in comWbar.
have /domP [fUr' [_ _ _ imfUr']] : 
    'dom fUr =  'C_Wbar(Aibar) by rewrite /dom -isor_im injmK.
set fUl := @pairg1 _ _ \o _ in comWbar.
have /domP [fUl' [_ _ _ imfUl']] : 
    'dom fUl = [~: Wbar, Aibar] by rewrite /dom -isol_im injmK.
rewrite -imfUr' -imfUl' in comWbar.
pose isoWbar := dprodm hcent_com comWbar.
have := (morphim_dprodm hcent_com comWbar (subxx _) (subxx _)).
rewrite imfUl' imfUr' /= !morphim_comp /= isol_im isor_im morphim_pair1g.
rewrite morphim_pairg1 setX_prod.
have <- : 
    [set: 'rV['Z_q]_rC * 'rV['Z_q]_(f i)] = setX [set: 'rV_rC]%G [set: 'rV_(f i)]%G.
    by apply/setP=> x; rewrite !inE.
move=> im_isoWbar.
have im_isoW : isoW @* [set: 'rV['Z_q](V)] = ([~: Wbar, Aibar] * 'C_Wbar(Aibar)).
  by rewrite /isoW; case/dprodP: (hcent_com) => _  /= {5}<-.
pose fPl := (@fst_morphism _ _ ) \o (isoWbar \o (isoW)).
have dom_fPl : setT \subset 'dom fPl.
  rewrite /dom /= morphpre_comp /= -sub_morphim_pre //.
  rewrite -im_isoWbar morphimK; last by case/dprodP: (hcent_com) => _ ->.
  rewrite -im_isoW; exact: mulG_subr.
pose Pl := mkMx _ _ _ _ dom_fPl.
pose fPr := (@snd_morphism _ _ ) \o (isoWbar \o (isoW)).
have dom_fPr : setT \subset 'dom fPr.
  rewrite /dom /= morphpre_comp /= -sub_morphim_pre // -im_isoWbar.
  rewrite  morphimK; last by case/dprodP: (hcent_com) => _ ->.
  rewrite -im_isoW; exact: mulG_subr.
pose Pr := mkMx _ _ _ _ dom_fPr.
pose P1 := row_mx Pl Pr; pose P2 := col_mx Pu Pd.
have P12_id : P1 *m P2 = 1%R.
  rewrite mul_row_col.
(*rewrite -(mulr1 (rW a)) -P12_id.*)
Admitted. 
