(* (c) Copyright Microsoft Corporation and Inria. All rights reserved. *)
Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq path div.
Require Import fintype bigop prime binomial finset ssralg fingroup finalg.
Require Import morphism perm automorphism quotient action commutator gproduct.
Require Import zmodp cyclic center pgroup gseries nilpotent sylow finalg finmodule.
Require Import abelian frobenius maximal extremal hall.
Require Import matrix mxalgebra mxrepresentation mxabelem BGsection1 BGsection2.



(******************************************************************************)
(*   This file is a placeholder for the proof of the Wielandt fixpoint order  *)
(* formula, which is a prerequisite for B & G, Section 3 and Peterfalvi,      *)
(* Section 9.                                                                 *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Defensive.

Local Open Scope ring_scope.
Import GroupScope GRing.Theory.
Import FinRing.Theory.

Section ExtrasForHuppertBlackburn_5_9.

Implicit Type gT : finGroupType.

(* This proof's really ugly *)
Lemma morphpre_minnormal : forall gT gT',
  forall (D : {group gT})(f : {morphism D >-> gT'})(R S : {group gT}), 
    'injm f -> R \subset D -> S \subset D -> 
  (minnormal (f @* R)  (f @* S)) = (minnormal R S).
Proof.
move=> gT gT' D f R S injf sRfD sSfD; apply/mingroupP/mingroupP; case. 
- case/andP=> h1 h2 h3.
  have [R1 | ntR] := eqsVneq R 1.
    by move: h1; rewrite /= !R1 morphim1 eqxx.
  rewrite ntR /=; split; first by move/(morphpre_norms f): h2; rewrite !injmK.
  move=> H; case/andP=> Hnt sSNH sHR; apply/eqP; rewrite eqEsubset sHR /=.
  rewrite -(injmSK injf) // (h3 [group of (f @* H)]) ?subxx // ?morphimS //=.
  by rewrite morphim_norms // andbT morphim_injm_eq1 //; apply: subset_trans sRfD.
- case/andP=> ntR sSNR h; rewrite morphim_injm_eq1 // ntR morphim_norms //. 
  split => // H; case/andP=> ntH fSNHS HfRS; apply/eqP; rewrite eqEsubset HfRS /=.
  have HfDS : H \subset f @* D.
    by apply: subset_trans HfRS _; apply: morphimS.
  rewrite -(h [group of (f@*^-1 H)]) /= ?morphpreK ?subxx //. 
  + have pfHnt : f @*^-1 H != 1. 
      apply/negP; move/eqP; move/trivgP. 
      rewrite sub_morphpre_injm //; last by rewrite sub1set group1.
      by rewrite morphim1; move/trivgP=> eH1; rewrite eH1 eqxx in ntH.
    rewrite pfHnt /=; apply: subset_trans (morphpre_norm _ _). 
    by rewrite -sub_morphim_pre.
  + by rewrite sub_morphpre_im //= ker_injm // sub1set group1.
Qed.

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

Section HuppertBlackburn_5_9.

Implicit Type gT : finGroupType.
Implicit Type p : nat.

Lemma huppert_blackburn_5_9 : forall gT p (A X : {group gT}),
  abelian A -> p.-group A -> p^'.-group X -> X \subset 'N(A) -> 
  exists2 s : {set {group gT}}, \big[dprod/1]_(B \in s) B = A
      & forall B, B \in s -> [/\ homocyclic B, X \subset 'N(B)
        & acts_irreducibly X (B / 'Phi(B)) 'Q].
Proof.
move=> gT p A X; move: {2}_.+1 (ltnSn #|A|) => m.
elim: m => // m IHm in gT A X *; rewrite ltnS => leAm cAA pA p'X nAX.
have [n eA]: {n | exponent A = p ^ n}%N by apply: p_natP; rewrite pnat_exponent.
have [-> | ntA] := eqsVneq A 1.
  by exists set0 => [|B]; rewrite ?big_set0 ?inE.
have [p_pr _ _] := pgroup_pdiv pA ntA; have p_gt1 := prime_gt1 p_pr.
case: n => [|n] in eA; first by rewrite trivg_exponent eA in ntA.
have nA1X: X \subset 'N('Ohm_1(A)) := char_norm_trans (Ohm_char 1 A) nAX.
have sAnA1: 'Mho^n(A) \subset 'Ohm_1(A).
  rewrite (MhoE n pA) (OhmE 1 pA) genS //.
  apply/subsetP=> xpn; case/imsetP=> x Ax ->{xpn}; rewrite !inE groupX //.
  by rewrite -expgn_mul -expnSr -eA -order_dvdn dvdn_exponent.
have nAnX: X \subset 'N('Mho^n(A)) := char_norm_trans (Mho_char n A) nAX.
have disjAX : A :&: X = 1 by apply: coprime_TIg; apply: (pnat_coprime pA).
have [B minB sBAn]: {B | minnormal (gval B) X & B \subset 'Mho^n(A)}.
  apply: mingroup_exists; rewrite nAnX andbT.
  have [x Ax ox] := exponent_witness (abelian_nil cAA).
  apply/trivgPn; exists (x ^+ (p ^ n)).
    rewrite /= (MhoEabelian n pA cAA); exact: mem_imset.
  by rewrite -order_dvdn -ox eA dvdn_Pexp2l ?ltnn.
have abelA1: p.-abelem 'Ohm_1(A) by rewrite Ohm1_abelem.
have sBA1 := subset_trans sBAn sAnA1.
have [ntB nBX] := andP (mingroupp minB).
have [U defA1 nUX] := Maschke_abelem abelA1 p'X sBA1 nA1X nBX.
case/dprodP: (defA1) => _ eA1p _ disjBU.
have sUA1 : U \subset 'Ohm_1(A) by rewrite -eA1p mulg_subr. 
have sUA :  U \subset A by apply: subset_trans (Ohm_sub 1 _).
have [U1 | ntU] := eqsVneq U 1.
  have homoA : homocyclic A.
    apply/(Ohm1_homocyclicP pA  cAA); rewrite eA pfactorK //=; apply/eqP.
    by rewrite eqEsubset sAnA1 andbT -eA1p U1 mulg1.
  exists (set1 A); rewrite ?big_set1 // => G; move/set1P->; split=> //.
  have := (homocyclic_Ohm_Mho _ pA homoA); rewrite eA pfactorK // => OhmMho.
  rewrite acts_irrQ ?Phi_normal //;last exact: char_norm_trans (Phi_char _) _.
  rewrite /= (Phi_joing pA) derg1 (_ : [~: A, A] = 1); last by apply/commG1P.
  rewrite joing1G /=.
  have phiM :  {in A &, {morph expgn^~ (p ^ n)%N : x y / x * y >-> x * y}}.
    by move=> x y Ax Ay /=; rewrite expMgn //; red; rewrite -(centsP cAA).
  pose phiA : {morphism A >-> gT} := Morphism phiM.
  have defXA : A ><| X = A <*> X by apply: sdprodEY.
  have phiAiM :  {in A & X, morph_act 'J 'J phiA (idm X)}.
    by move=> x y Ax Ay /=; rewrite /idm conjXg.
  pose g := [morphism of sdprodm defXA phiAiM].
  have kerg : 'ker g = 'Mho^1(A).
    have := (OhmMho n); rewrite subSnn; move<-. 
    rewrite (OhmEabelian pA) ?(abelianS (Ohm_sub _ _)) // ker_sdprodm.
    apply/setP=> z; apply/imset2P/idP; last first.
      rewrite !in_set; case/andP=> Az ez. 
      by exists z (1 : gT); rewrite ?invg1 ?mulg1 // in_set group1 ez.
    case=> a x Aa; rewrite in_set /= /idm; case/andP=> Xx; move/eqP=> ey ex.
    rewrite !in_set ex; move: (ey).
    have -> : x = 1 by apply/set1P; rewrite -set1gE -disjAX inE -{1}ey groupX.
    by rewrite invg1 !mulg1; move->; rewrite eqxx Aa.
  move: minB; rewrite -kerg.
  have -> : B :=: 'Ohm_1(A) by move: eA1p; rewrite U1 mulGSid // sub1set group1.
  have skk : 'ker (coset ('ker g)) \subset 'ker g by rewrite ker_coset.
  have nkA := ker_norm g; pose fact_g := factm skk nkA.
  have -> : 'Ohm_1(A) = fact_g @* (A / 'ker g).
    rewrite morphim_factm  morphim_sdprodml // OhmMho subn1; apply/setP=> x /=.
    rewrite (MhoEabelian n pA) // morphimEdom. 
    by apply/imsetP/imsetP; case=> a Aa ->; exists a.
  have imgX : X :=: fact_g @* (X / 'ker g).
    by rewrite morphim_factm morphim_sdprodmr // morphim_idm.
  have nAA1 : A \subset 'N ('Mho^1(A)) by exact: (normal_norm (Mho_normal 1 A)).
  have nXA1 : X \subset 'N ('Mho^1(A)).
    exact: char_norm_trans (Mho_char _ A) nAX.
  rewrite {29}imgX {imgX}. 
  rewrite morphpre_minnormal ?kerg /= ?morphimY ?joing_subl // ?joing_subr //.
  by apply/injm_factmP; rewrite ker_coset.
have nUA : A \subset 'N(U).
  by apply: subset_trans (cent_sub _); apply: sub_abelian_cent.
have card_AU : #| A / U | < m by apply: leq_trans leAm; apply: ltn_quotient.
have cAUAU : abelian (A / U) by apply: quotient_abelian.
have pAU : p.-group (A / U) by apply: quotient_pgroup.
have p'XU : (p^').-group (X / U) by apply: quotient_pgroup.
have nXUAU : X / U \subset 'N(A / U) by apply: quotient_norms.
case: (IHm _ _ _ card_AU cAUAU pAU p'XU nXUAU) => S AUid hS {card_AU}.
have subBAU : forall G, G \in S -> G \subset A / U.
  move=> G SG; rewrite -(bigdprodEY AUid).
  apply: subset_trans (subset_gen _); exact: bigcup_sup.
have [eAU [K' [SK' eK']]]: (exponent (A / U) = (p ^ n.+1)%N) /\
           exists2 K', K' \in S & exponent K' = (p ^ n.+1)%N.
  case/trivgPn: ntB => x Bx xn1; move/(subsetP sBAn): (Bx).
  rewrite (MhoEabelian _ pA) //; case/imsetP=> a Aa exa.
  have xNU : x \in 'N(U) by apply: (subsetP nUA); rewrite exa groupX.
  have aUPn1 : coset U a ^+ (p ^ n) != 1.
    rewrite -morphX ?(subsetP nUA) // -exa; apply/negP; move/eqP. 
    apply/kerP=> //.
    by rewrite ker_coset -(andTb (x \in U)) -Bx -in_setI disjBU in_set1.
  have order_aUp : #[(coset U a) ^+ (p ^ n)%N ] = p.
    apply: nt_prime_order=> //; rewrite -expgn_mul mulnC -expnS -eA. 
    by apply: (exponentP (exponent_quotient A U)); rewrite mem_quotient.
  have order_aU : #[(coset U a)] = (p ^ n.+1)%N.
    by rewrite expnS mulnC; apply: orderXpfactor.
  have eAU : exponent (A / U) = (p ^ n.+1)%N.
    apply/eqP; rewrite eqn_dvd -{1}eA exponent_quotient /=.
    by rewrite -order_aU; apply: dvdn_exponent; exact: mem_quotient. 
  split=> //; case: (mem_bigdprod AUid (mem_quotient U Aa)) => /= pa.
  case=> a_dec ha_dec a_dec_unic.
  have : existsb i, (i \in S) && ((pa i) ^+ (p ^ n) != 1).
    rewrite -[existsb i, _]negbK negb_exists; apply/negP; move/forallP=> habs.
    move/(f_equal (expgn^~ (p ^ n)%N)): ha_dec.
    have -> : 
      (\prod_(i \in S) pa i) ^+ (p ^ n) = \prod_(i \in S) (pa i ^+ (p ^ n)).
      apply: (bigprod_expg _ _ cAUAU) => i Si; apply: (subsetP (subBAU _ Si)).
      exact: a_dec.
    rewrite big1; first by move/eqP; apply/negP.
    by move=> i Si; move: (habs i); rewrite Si negbK; move/eqP.
  case/existsP=> K'; case/andP=> SK' paK'_nt; exists K' => //.
  apply/eqP; rewrite eqn_dvd -{1}eAU exponentS ?subBAU //.
  suff <- : #[pa K']  = (p ^ n.+1)%N by apply: dvdn_exponent; exact: a_dec.
  rewrite expnS mulnC; apply: orderXpfactor => //.
  apply: nt_prime_order => //; rewrite -expgn_mul mulnC -expnS -eAU. 
  apply: expg_exponent; apply: (subsetP (subBAU _ SK')); exact: a_dec.
move=> {B minB sBAn sBA1 eA1p ntB nBX defA1 disjBU}.
pose K := (coset U) @*^-1 K'.
have KK':= (cosetpreK K').
have {subBAU} sKA : K \subset A.
   move: (subBAU _ SK'); rewrite -{1}(cosetpreK K') quotientSGK //.
   by apply: normal_norm; rewrite normal_cosetpre.
have cKK := (abelianS sKA cAA).
have cK'K' : abelian K' by rewrite -KK'(quotient_abelian _ cKK).
have pK := (pgroupS sKA pA).
have pK' : p.-group K' by rewrite -KK' (quotient_pgroup _ pK).
case: (hS _ SK') => homoK' nXUK' minK'.
have nXKM1 : X / 'Mho^1(K) \subset 'N(K / 'Mho^1(K)).
  apply: quotient_norms; apply: subset_trans (mulG_subr U X) _.
  by rewrite -quotientK //; apply: morphpre_norms; case: (hS _ SK').
have nKX : X \subset 'N(K).
  by apply: subset_trans (morphpre_norm _ _); rewrite -sub_morphim_pre.
pose sP' := \big[dprod/1]_(B \in S :\ K') B. 
pose sP := coset U @*^-1 sP'.
have PP'  := (cosetpreK sP').
have defAU : K / U \x (sP / U) = A / U.
  by rewrite -AUid (big_setD1 K' SK') /= -KK' -/sP' -PP'.
case/dprodP: (defAU)=> [] []  _ P' _ P'def eAUp sPUCKU disjKUPU.
set P := coset U @*^-1 P'.
have sP'P : sP' = P' by rewrite -P'def cosetpreK.
have nXP : X \subset 'N(P).
  apply: subset_trans (morphpre_norm _ _).
  apply: subset_trans (@mulG_subr _ ('ker (coset U)) X) _.
  rewrite -morphimK //  morphpreSK; last by rewrite morphimS.
  move: sP'P; move/bigdprodE<-; apply: bigprod_norm => i Si.
  by case: (hS _ (subsetP (subD1set _ _) _ Si)).
have abelKM1 : p.-abelem (K / 'Mho^1(K)).
  suff -> : 'Mho^1(K) = 'Phi(K) by apply: Phi_quotient_abelem.
  rewrite (Phi_joing pK) derg1 (_ : [~: K, K] = 1); last by apply/commG1P.
  by rewrite joing1G.
have p'XM1 : (p^').-group  (X / 'Mho^1(K)) by exact: quotient_pgroup.
have sUM1KM1 :  U / 'Mho^1(K) \subset K / 'Mho^1(K).
   apply: morphimS; exact: sub_cosetpre.
have nUM1KM1 : X / 'Mho^1(K) \subset 'N(U / 'Mho^1(K)). exact: quotient_norms.
have disjUK1 : U :&:'Mho^1(K) = 1.
  apply/eqP; rewrite set1gE -subG1; apply/subsetP=> x; case/setIP=> Ux M1x.
  move: (M1x); rewrite /= (MhoEabelian _ pK) // expn1; case/imsetP => k Kk exk.
  rewrite exk; case/morphpreP: Kk => /= NUk K'Uk.
  have : coset U k \in 'Mho^n(K').
    move: (homocyclic_Ohm_Mho 1 pK' homoK'); rewrite eK' pfactorK //.
    rewrite subn1 /=; move<-.
    rewrite (OhmEabelian pK'); last by apply: (abelianS (Ohm_sub _ _)).
    by rewrite inE K'Uk expn1 inE -morphX // -exk; apply/eqP; apply: coset_id.
  rewrite (MhoEabelian _ pK' cK'K'); case/imsetP=> z; rewrite -KK'.
  case/morphimP=> y Nuy Ky eyz; rewrite eyz -morphX //=.
  have NUypn : y ^+ (p ^ n)%N \in 'N(U) by rewrite groupX //.
  move/(rcoset_kercosetP NUk NUypn); case/rcosetP=> u Uu ->.
  have uA : u \in A by exact: (subsetP sUA u).
  have yA : y \in A by exact: (subsetP sKA).
  rewrite expMgn; last by apply: commuteX; red; rewrite -(centsP cAA).
  rewrite -expgn_mul mulnC -expnS -eA expg_exponent // mulg1; apply/set1P.
  have : u \in 'Ohm_1 (A) by apply: (subsetP sUA1).
  rewrite (OhmEabelian pA) // ?(abelem_abelian abelA1) // expn1.
  by rewrite !inE; case/andP=> _; move/eqP.
have UKn : U <| K by rewrite normal_cosetpre.
have [D' defKM1 nXD'] := Maschke_abelem abelKM1 p'XM1 sUM1KM1 nXKM1 nUM1KM1.
pose D := coset 'Mho^1(K) @*^-1 D'.
have DD' := (cosetpreK D').
case/dprodP: (defKM1) => _ eKM1p sD'CUM1 disjUM1D'.
have nK1X : X \subset 'N('Mho^1(K)).
  exact: (char_norm_trans (Mho_char 1 [group of K]) nKX).
have nDX : X \subset 'N(D).
  apply: subset_trans (morphpre_norm _ _).
  apply: subset_trans (@mulG_subr _ ('ker (coset 'Mho^1(K))) X) _.
  by rewrite -morphimK //  morphpreSK // morphimS.
move: (eKM1p); move/(f_equal (fun x => coset ('Mho^1(K))%G @*^-1 x)).
rewrite cosetpreM quotientK; last first.
  apply: subset_trans (normal_norm (Mho_normal 1 _)); exact: sub_cosetpre.
have -> : commute 'Mho^1(K)  U.
  apply: centC; apply: (sub_abelian_cent2 cAA) => //.
  by apply: subset_trans (Mho_sub _ _) _; apply: subset_trans sKA _.
rewrite quotientK /=; last exact: (normal_norm (Mho_normal 1 _)).
rewrite -mulgA mulSGid ?sub_cosetpre //= ['Mho^1(_) * _]mulSGid ?Mho_sub //=.
move=> eKp.
move: (eAUp); move/(f_equal (fun x => coset U @*^-1 x)).
rewrite cosetpreM quotientGK //= -/K P'def quotientK; last first. 
  by apply: subset_trans (cent_sub _); apply: sub_abelian_cent.
rewrite mulSGid //= /K -eKp => Adec_tmp; move: (Adec_tmp).
have -> : commute U D.
  apply: centC;  apply: (sub_abelian_cent2 cAA) => //.
  rewrite -Adec_tmp; apply: subset_trans (mulG_subl _ _); exact: mulg_subr.
rewrite -mulgA mulSGid  ?sub_cosetpre //= => {Adec_tmp} Adec.
have sDK : D \subset K by rewrite /K -eKp mulG_subr.
have KPI : K :&: P = U.
  apply/eqP; rewrite eqEsubset subsetI ?sub_cosetpre !andbT.
  apply/subsetP=> x; case/setIP=> Kx Px; rewrite -(ker_coset U).
  have NUx : x \in 'N(U) by apply: (subsetP (normal_norm UKn)).
  apply/kerP => //; apply/set1P; rewrite -set1gE -disjKUPU. 
  rewrite P'def; apply/setIP; split; first by apply/morphimP; exists x => //.
  by move/morphpreP: Px; case.
have sDIUK1 : D :&: U \subset 'Mho^1(K).
  apply/subsetP=> x; case/setIP=> Dx Ux; rewrite -(ker_coset 'Mho^1(K)).
  have NM1x : x \in 'N('Mho^1(K)).
  apply: (subsetP (normal_norm (Mho_normal _ _))).
    exact: (subsetP (normal_sub UKn)).
  apply/kerP => //; apply/set1P; rewrite -set1gE -disjUM1D' /=.
  by rewrite -DD'; apply/setIP; split; by apply/morphimP; exists x.
have UIK1 : U :&:'Mho^1(K) = 1.
  apply/eqP; rewrite set1gE -subG1; apply/subsetP=> x; case/setIP=> Ux M1x.
  move: (M1x); rewrite /= (MhoEabelian _ pK) // expn1; case/imsetP => k Kk exk.
  rewrite exk; case/morphpreP: Kk => /= NUk K'Uk.
  have : coset U k \in 'Mho^n(K').
    move: (homocyclic_Ohm_Mho 1 pK' homoK'); rewrite eK' pfactorK //.
    rewrite subn1 /=; move<-.
    rewrite (OhmEabelian pK'); last by apply: (abelianS (Ohm_sub _ _)).
    by rewrite inE K'Uk expn1 inE -morphX // -exk; apply/eqP; apply: coset_id.
  rewrite (MhoEabelian _ pK' cK'K'); case/imsetP=> z; rewrite -KK'.
  case/morphimP=> y Nuy Ky eyz; rewrite eyz -morphX //=.
  have NUypn : y ^+ (p ^ n)%N \in 'N(U) by rewrite groupX //.
  move/(rcoset_kercosetP NUk NUypn); case/rcosetP=> u Uu ->.
  have uA : u \in A by exact: (subsetP sUA u).
  have yA : y \in A by exact: (subsetP sKA).
  rewrite expMgn; last by apply: commuteX; red; rewrite -(centsP cAA).
  rewrite -expgn_mul mulnC -expnS -eA expg_exponent // mulg1.
  apply/set1P.
  have : u \in 'Ohm_1 (A) by apply: (subsetP sUA1).
  rewrite (OhmEabelian pA) // ?(abelem_abelian abelA1) // expn1.
  by rewrite !inE; case/andP=> _; move/eqP.
have disjDP : D :&: P :=: 1.
  move/setIidPl: sDK <-; rewrite -setIA KPI.
  by move/setIidPl: sDIUK1 <-; rewrite -setIA UIK1 setIg1.
have {Adec} Adec : D \x P = A.
  rewrite -Adec dprodE //=;  apply: (sub_abelian_cent2 cAA); rewrite // -Adec.
    exact: mulG_subr. 
  exact:mulG_subl.
case/dprodP: (Adec) => _ Adef cPD _.
have D_nt : D != 1.
  case abs: (D == 1) => //; move/eqP: abs; rewrite /D => abs.
  move: (eKp); rewrite abs mulg1 => {abs} abs /= ; rewrite -(euclid1 p_pr).
  move: eK'; rewrite -KK' /= -abs trivg_quotient exponent1 expnS; move->.
  by rewrite dvdn_mulr // dvdnn.
have cardP : #|P| < m.
  apply: leq_trans leAm. rewrite -Adef cardMg_divn /= -/D -/P.
  rewrite disjDP cards1 divn1; apply: ltn_Pmull; rewrite ?cardG_gt0 //.
  by move: D_nt; rewrite -cardG_gt1.
have sPA : P \subset A by  rewrite -Adef; exact: mulG_subr.
have cPP : abelian P by exact: (abelianS _ cAA).
have pP : p.-group P by exact: (pgroupS sPA).
case: (IHm _ _ _ cardP cPP pP p'X nXP) => /= SP Pdec hSP.
exists ([group of D] |: SP).
   rewrite -Adec /P -Pdec big_setU1 //.
   case abs: ([group of D] \in SP) => //.
   suff : D \subset P by rewrite -subsetIidl disjDP subG1 (negPf D_nt).
   move: Pdec; rewrite (big_setD1 _ abs) /=. 
   case/dprodP=> [] [] _ B' _ B'def Pdef cP'B' disjDB'.
   by rewrite /P -Pdef B'def; apply: mulG_subl.
move=> H; case/setU1P; last exact: hSP; move->.
have sDA : D \subset A by rewrite -Adef mulG_subl.
have pD : p.-group D := (pgroupS sDA pA).
have cDD : abelian D:= (abelianS sDA cAA).
have disjDX : D :&: X = 1 by apply: coprime_TIg; apply: (pnat_coprime pD).
have defXD : D ><| X = D <*> X by apply: sdprodEY.
have nUD : D \subset 'N(U).
  by apply: subset_trans (cent_sub _); apply: (sub_abelian_cent2 cAA).
have nUDX : D <*> X \subset 'N(U) by rewrite join_subG nUD. 
have nPhiDX :  D <*> X / U \subset 'N('Phi(K')).
  rewrite quotientY // join_subG !(char_norm_trans (Phi_char _)) //.
  by apply: subset_trans (morphimS _ sDK) _; rewrite -KK' normG.
have dom_phi : D <*> X \subset (coset U) @*^-1 'N('Phi(K')).
  by rewrite -sub_morphim_pre /=.
pose phi := [morphism of restrm dom_phi ((coset 'Phi(K')) \o (coset U))].
have PhiK' : 'Phi(K') = 'Mho^1(K').
  rewrite (Phi_joing pK') derg1 (_ : [~: K', K'] = 1); last by apply/commG1P.
  by rewrite joing1G.
have nKU : K \subset 'N(U) by rewrite /K -eKp mul_subG ?normG.
have ker_phi : 'ker phi = 'Mho^1(D).
  rewrite ker_restrm ker_comp ker_coset /= PhiK'.
  apply/eqP; rewrite eqEsubset; apply/andP; split; last first.
    rewrite subsetI (subset_trans (Mho_sub _  _) _) ?joing_subl //=.
    apply: subset_trans (MhoS 1 sDK) _; rewrite -KK' quotientE.
    rewrite -morphim_Mho //= -/K -sub_morphim_pre //; apply: subset_trans nKU.
    exact: Mho_sub.
  rewrite -KK' -morphim_Mho // morphimK; last first. 
    by apply: subset_trans nKU; exact: Mho_sub.
  rewrite ker_coset /= -/K; apply/subsetP=> y; case/setIP.
  case/(mem_sdprod defXD)=> d [x [Dd Xx e dx_u]]; case/mulsgP=> u k1 Uu.
  rewrite (MhoEabelian _ pK cKK); case/imsetP=> k Kk; rewrite expn1 => ekk1.
  rewrite ekk1 => eyuk1; rewrite eyuk1.
  have x1 : x = 1.
    apply/set1P; rewrite -set1gE -disjAX in_setI Xx.
    move: eyuk1; rewrite e; move/eqP; rewrite -(inj_eq (@mulgI _ d^-1)).
    rewrite andbT mulgA mulVg mul1g; move/eqP->; apply: groupM.
      rewrite groupV; exact: (subsetP sDA).
    apply: groupM; first exact: (subsetP sUA).
    apply: groupX; exact: (subsetP sKA).
  move: eyuk1; rewrite e x1 mulg1; move/eqP.
  rewrite -(inj_eq (@mulIg _ (k ^+ p) ^-1)) mulgK; move/eqP=> eu.
  have hu : u \in D :&: U.
    rewrite in_setI Uu -eu andbT; apply: groupM; rewrite ?Dd // groupV.
    apply: (subsetP (sub_cosetpre _)).
    by rewrite /= (MhoEabelian _ pK cKK); apply/imsetP; exists k.
  move/(subsetP sDIUK1): hu.
  rewrite /= (MhoEabelian _ pK cKK); case/imsetP=> k' Kk'->.
  rewrite expn1 -expMgn; last by red; rewrite -(centsP cKK).
  have : k' * k \in K by rewrite groupM.
  rewrite /K -eKp; case/mulsgP=> u1 d1 Ud1 Dd1 ->. 
  rewrite expMgn; last first.
    by red; rewrite -(centsP cAA) ?(subsetP sDA d1) ?(subsetP sUA u1).
  have : u1 \in 'Ohm_1 (A) by apply: (subsetP sUA1).
  rewrite (OhmEabelian pA) // ?(abelem_abelian abelA1) // expn1.
  rewrite !inE; case/andP => _; move/eqP->; rewrite mul1g.
  by rewrite (MhoEabelian _ pD cDD); apply/imsetP; exists d1.
  have skk : 'ker (coset ('ker phi)) \subset 'ker phi by rewrite ker_coset.
  have nkA := ker_norm phi; pose fact_phi := factm skk nkA.
split=> //; last first.
  rewrite acts_irrQ ?Phi_normal //=;last exact: char_norm_trans (Phi_char _) _.
  move: minK'.
  rewrite acts_irrQ ?Phi_normal //=; last exact: char_norm_trans (Phi_char _) _.
  rewrite /= (Phi_joing pD) derg1 (_ : [~: D, D] = 1); last by apply/commG1P.
  rewrite joing1G /= -/D -ker_phi.
  have -> : (X / U / 'Phi(K')) = fact_phi @* (X / 'ker phi).
    rewrite morphim_factm morphim_restrm morphim_comp /=.
    suff -> : D <*> X :&: X = X by [].
    apply/setIidPr; exact: joing_subr.
  have -> : K' / 'Phi(K') =  fact_phi @* (D / 'ker phi).
    rewrite morphim_factm morphim_restrm morphim_comp /=.
    suff -> : coset U @* (D <*> X :&: D) = K'. by done.
    have -> : D <*> X :&: D = D.
      by apply/eqP; rewrite eqEsubset subsetI subxx joing_subl /= subsetIr.
    by rewrite -KK' -eKp quotientMidl.
  rewrite morphpre_minnormal //.
  - by apply/injm_factmP; rewrite ker_coset.
  - apply: morphimS; exact: joing_subl.
  - apply: morphimS; exact: joing_subr.
suff isogDK' : D \isog K'.
  rewrite /homocyclic (isog_abelian isogDK') cK'K' (isog_abelian_type isogDK').
  by case/andP: homoK'.
apply/isogP; exists [morphism of (restrm nUD (coset U))].
  rewrite ker_restrm ker_coset /= -/D.
(* this, as well as the fact that K = D \x U can probably be established and
   used earlier *)
  have -> : D :&: U = (D :&: U) :&: 'Mho^1(K).
    by apply/eqP; rewrite eqEsubset subsetIl subsetIidl andbT.
  by rewrite -setIA UIK1 setIg1.
by rewrite morphim_restrm /= setIid -KK' -eKp quotientMidl.
Qed.

End HuppertBlackburn_5_9.

Section ExtrasForHuppertBlackburn_12_3.

Lemma mx_group_exponent :  forall n m q,
  n > 0 -> m > 0 -> q > 1 -> exponent [set: 'M['Z_q]_(m, n)] = q.
Proof.
move=> n m q pn pm q_gt1.
apply/eqP; rewrite eqn_dvd; apply/andP; split; last first.
  pose cmx1 := const_mx 1%R : 'M['Z_q]_(m, n).
  apply: dvdn_trans (dvdn_exponent (in_setT cmx1)). 
  have := (expg_order cmx1); move/matrixP. 
  move/(_ (Ordinal pm)); move/(_ (Ordinal pn)); rewrite mulmxnE; move/eqP. 
  by rewrite !mxE -order_dvdn order_Zp1 Zp_cast.
apply/exponentP=> x hx; apply/matrixP=> i j; rewrite mulmxnE !mxE.
by rewrite -mulr_natr -Zp_nat_mod // modnn mulr0.
Qed.


Lemma abelem_mx_group : forall n m q,
  n > 0 -> m > 0 -> prime q -> q.-abelem [set: 'M['Z_q]_(m, n)].
Proof.
move=> n m q pn pm primeq.
by rewrite abelemE // mx_group_exponent ?prime_gt1 // zmod_abelian /=.
Qed.


Lemma huppert_blackburn_12_3 : forall (gT : finGroupType),
  forall (V G : {group gT})(p m : nat),
  minnormal V G -> 
  coprime p #|G| ->
  p.-abelem V ->
  m > 0 ->
  let W := [set: 'rV['Z_(p ^ m)](V)]%G in
  exists2 f : {morphism V >-> coset_of 'Mho^1(W)},
      isom V (W / 'Mho^1(W)) f
  & exists toW : groupAction G W,
    {in V & G, morph_act 'J (toW / 'Mho^1(W)) f (idm G)}.
Proof.
move=> gT V G p m minV copG abelV m_gt0 W.
have [ntV nVG] := andP (mingroupp minV).
have [p_pr pVdvdn [n Vpexpn]] := pgroup_pdiv (abelem_pgroup abelV) ntV.
move/(abelem_mx_irrP abelV ntV nVG): (minV) => mx_irrV.
have dim_lt0 : 'dim V > 0 by rewrite (dim_abelemE abelV) // Vpexpn pfactorK.
have pW : p.-group W.
  rewrite -pnat_exponent mx_group_exponent // ?pnat_exp ?pnat_id //.
  by rewrite -(exp1n m) ltn_exp2r // prime_gt1.
have CWW : abelian W by rewrite zmod_abelian.
have PhiMho : 'Phi(W) = 'Mho^1(W).
  by rewrite (Phi_joing pW) derg1 (_ : [~: W, W] = 1) ?joing1G //; apply/commG1P.
Admitted.

End ExtrasForHuppertBlackburn_12_3.

Theorem solvable_Wielandt_fixpoint : forall (I : finType) (gT : finGroupType),
    forall (A : I -> {group gT}) (n m : I -> nat) (G V : {group gT}),
    (forall i, m i + n i > 0 -> A i \subset G) ->
    G \subset 'N(V) -> coprime #|V| #|G| -> solvable V ->
    {in G, forall a, \sum_(i | a \in A i) m i = \sum_(i | a \in A i) n i}%N ->

  (\prod_i #|'C_V(A i)| ^ (m i * #|A i|)
    = \prod_i #|'C_V(A i)| ^ (n i * #|A i|))%N.
Proof.
move=> I gT A n m G V; move: {2}_.+1 (ltnSn #|V|) => k.
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
elim: k  => // k IHk in I gT A G V n m *;
 rewrite ltnS => leVm sAiG nVG copVG solV hGA *.
have [V1 | ntV] := eqsVneq V 1.
  by rewrite V1 !big1 // => i _; rewrite setI1g set1gE cards1 exp1n.
have nVP : V <| V <*> G by rewrite normalYG.
have [B [sBV nBP ntB abelemB]] := (solvable_norm_abelem solV nVP ntV).
case/andP: nBP=> _; move/joing_subP=> /= [nBV nBG]. 
case/is_abelemP: abelemB=> p primep pabelemB.
have solB := (solvableS sBV solV).
have [BV | BVproper] := eqVproper sBV; last first.
  have cardB : #|B| < k by apply: leq_trans leVm; exact: proper_card.
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
    rewrite card_quotient; last first. by rewrite subIset ?nBV.
    by rewrite LaGrangeI.
  have hp : forall mm j, 0 < m j + n j ->  
     (#|'C_V(A j)| ^ (mm j * #|A j|))%N  = 
     ((#|'C_B(A j)| ^ (mm j * #|A j|) * (#|'C_(V / B)(A j / B)|) ^ (mm j * #|A j / B|)))%N.
    move=> mm j; move/sAiG=> sAjG.
    have nBAj : A j \subset 'N(B) by exact: subset_trans nBG.
    have copBAj : coprime #|B| #|A j| by rewrite  (coprimegS sAjG).
    rewrite -(card_isog (quotient_isog _ _)) ?(coprime_TIg copBAj) // -expn_mull.
    by rewrite cardps.
  rewrite !(eq_bigr _ (hp _)) !big_split /=; congr (_ * _)%N.
    exact: (IHk _ _ _ G).
  have cardQ : #|V / B| < k by apply: leq_trans leVm; apply: ltn_quotient.
  have sAQ : forall i : I, 0 < m i + n i -> A i / B \subset G / B.
    move=> i si; apply: quotientS; exact: sAiG.
  have nQ : G / B \subset 'N(V / B) by apply: quotient_norms.
  have copQ : coprime #|V / B| #|G / B| by exact: coprime_morph.
  have solQ : solvable (V / B) by exact: quotient_sol.
  apply: (IHk _ _ _ (G / B)%G) => //.
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
have [Phi1 | ntPhi] := eqsVneq 'Phi(V) 1; last first.
  have hp : forall mm j, 0 < m j + n j ->  
    (#|'C_V(A j)| ^ (mm j * #|A j|))%N  = 
    ((#|'C_('Phi(V))(A j)| ^ (mm j * #|A j|) * (#|'C_(V / 'Phi(V))(A j / 'Phi(V))|) ^ (mm j * #|A j / 'Phi(V)|)))%N.
      move=> mm j hmn; move/sAiG: (hmn) => sAjG; rewrite -BV.
      have nBAj : A j \subset 'N('Phi(B)).
        by apply: (char_norm_trans (Phi_char B)); apply: subset_trans nBG.
      have copPhiAj : coprime #|'Phi(B)| #|A j|.
        by rewrite  BV (coprimegS sAjG) // (coprimeSg (Phi_sub _)).
      have copBAj :  coprime #|B| #|A j| by rewrite BV (coprimegS sAjG).
      rewrite -(card_isog (quotient_isog _ _)) ?(coprime_TIg copBAj) //; last first.
        by apply: coprime_TIg.
      rewrite -expn_mull; congr (_ ^ _)%N.
      rewrite -(coprime_quotient_cent (Phi_sub _) nBAj copBAj solB).
      have -> : 'C_('Phi(B))(A j) = 'C_B(A j) :&: 'Phi(B).
        by rewrite [_ :&: 'Phi(B)]setIC setIA (setIidPl (Phi_sub _)).
      rewrite card_quotient; last by rewrite subIset ?(normal_norm (Phi_normal _)).
      by rewrite LaGrangeI.
    rewrite !(eq_bigr _ (hp _)) {hp} !big_split /=; congr (_ * _)%N.
    have cardPhi : #|'Phi(B)| < k.
      apply: leq_trans leVm; apply: proper_card; rewrite BV; exact: Phi_proper.
    have nPhiG : G \subset 'N('Phi(B)) by apply: (char_norm_trans (Phi_char B)).
    have copPhiG : coprime #|'Phi(B)| #|G| by rewrite (coprimeSg (Phi_sub _)) // BV.
    apply: (IHk _ _ _ G); rewrite /= -?BV //; exact: (solvableS (Phi_sub _)).
  have cardQ : #|V / 'Phi(V)| < k.
   by apply: leq_trans leVm; apply: ltn_quotient; rewrite ?Phi_sub.
  have sAQ : forall i : I, 0 < m i + n i -> A i / 'Phi(V) \subset G / 'Phi(V).
    move=> i si; apply: quotientS; exact: sAiG.
  have nQ : G / 'Phi(V) \subset 'N(V / 'Phi(V)) by apply: quotient_norms.
  have copQ : coprime #|V / 'Phi(V)| #|G / 'Phi(V)| by exact: coprime_morph.
  have solQ : solvable (V / 'Phi(V)) by exact: quotient_sol.
  apply: (IHk _ _ _ (G / 'Phi(V))%G) => //.
  move=> g; case/morphimP=> x /= Nx Gx ->.
  have hindex : forall i,
    (coset 'Phi(V) x \in A i / 'Phi(V)) && (0 < m i + n i)%N  = 
  (x \in A i) && (0 < m i + n i)%N.
    move=> j; case lt0s : (0 < m j + n j); rewrite ?andbF ?andbT //.
    have sAjG := sAiG _ lt0s; move/sAQ: lt0s=> sAjPhiQ.
    have nPhiG : G \subset  'N('Phi(V)) by apply: (char_norm_trans (Phi_char _)).
    have nPhiAj : A j \subset 'N('Phi(V)) by  apply: subset_trans nPhiG.
    apply/idP/idP; last by move/(mem_quotient 'Phi(V)).
    move/(mem_morphpre (subsetP nPhiG _ Gx)); rewrite /= quotientK // => PhiAx.
    have : x \in G :&: ('Phi(V) * A j) by rewrite in_setI Gx.
    have copPhiG : coprime #|'Phi(V)| #|G| by rewrite (coprimeSg (Phi_sub _)).
    rewrite -group_modr //; move: copPhiG; rewrite coprime_sym.
    by move/coprime_TIg->; rewrite mul1g.
  rewrite !(eq_bigl _ _ hindex) /=; exact: hGA.
have hindex : forall mn i, 0 < m i + n i -> 
  (#|'C_V(A i)| ^ (mn i * #|A i|) = p ^ (logn p #|'C_V(A i)| * (mn i) * #|A i|))%N.
  move=> mn i _.
  have : p.-group 'C_V(A i).
    by rewrite -BV; apply: (pgroupS _ (abelem_pgroup pabelemB));apply: subsetIl.
  by move/card_pgroup=> h; rewrite {1}h {h} -expn_mulr mulnA.
rewrite !(eq_bigr _ (hindex _)) {hindex} -!expn_sum; congr (_ ^ _)%N.
Admitted.
