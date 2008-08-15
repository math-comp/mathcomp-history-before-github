(***********************************************************************)
(* (c) Copyright Microsoft Corporation and Inria. All rights reserved. *)
(*                                                                     *)
(***********************************************************************)
(***********************************************************************)
(*                                                                     *)
(*          Definition of sylow group                                  *)
(*                                                                     *)
(***********************************************************************)
(***********************************************************************)

Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq.
Require Import fintype div prime finfun finset ssralg.
Require Import bigops groups morphisms normal action cyclic zp. 
Require Import dirprod pgroups nilpotent center.

(* Require Import paths connect. *)

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.
Import GroupScope.

Section Sylow.

Variable (gT : finGroupType) (K : {group gT}).

Variable p : nat.
Hypothesis prime_p : prime p.

Let n := logn p #|K|.

Hypothesis n_pos: 0 < n. 

Lemma SylowDivpCK : p %| #|K|.
Proof.
apply: (@dvdn_trans (p ^ n)%N); last by rewrite dvdn_exp_max.
by move: n_pos; case: n => // n1 _; rewrite dvdn_exp // dvdnn.
Qed.

Let DivpCK := SylowDivpCK.

Lemma sylow_sconjgr: forall L x, x \in K -> sylow p K L = sylow p K (L :^ x).
Proof.
have F1: forall L x, x \in K -> sylow p K L -> sylow p K (L :^ x).
  move=> L x Kx; case/andP => sLK card_L.
  apply/andP; split; last by rewrite card_conjg card_L.
  apply/subsetP=> yx; case/imsetP=> y Ly ->{yx}.
  by rewrite groupJ // (subsetP sLK).
move=> L x Hx; apply/idP/idP => Hx1; first exact: F1.
by rewrite -[L](conjsgK x) F1 // groupV.
Qed.

Lemma sylow_sconjg: forall (H L: {set gT}) x, sylow p H L = sylow p (H :^ x) (L :^ x).
Proof.
have F1: forall (H L: {set gT}) x, sylow p H L -> sylow p (H :^ x) (L :^ x).
  move=> H L x; rewrite !sylowE; case/andP => sLH card_L.
  rewrite /sylow 2!card_conjg -(eqP card_L) eqxx andbT.
  apply/subsetP=> yx; case/imsetP=> y Ly ->{yx}.
  by rewrite memJ_conjg (subsetP sLH).
move=> H L x; apply/idP/idP => Hx1; first exact: F1.
by rewrite -[H](conjsgK x) -[L](conjsgK x) F1.
Qed.

Lemma sylow1_rec: forall i (L : {group gT}), i < n ->
  L \subset K -> (#|L| == p ^ i)%N ->
  exists H : {group gT}, [&& H \subset K, L <| H & #|H| == p ^ i.+1]%N.
Proof.
move=> i L ltin sLK cardL.
have: p %| #|K / L|.
  have <-: #|'C_(rcosets L K)(L | 'Msr)| = #|K / L|.
    rewrite rtrans_fix_norm -(card_imset (mem (K / L)) val_inj).
    apply: eq_card=> Lk; rewrite val_quotient //.
  have divpLK : p %| #|K : L|.
    rewrite -(@dvdn_pmul2l #|L|) // (LaGrange sLK) (eqP cardL) mulnC -expnS.
    by rewrite dvdn_exp_max.
  have pgL: pgroup p L by apply/pnatP=> //; exists i; exact/eqP.
  apply/eqP; rewrite -{divpLK}(eqnP divpLK) -(pgroup_fix_mod prime_p pgL) //.
  apply/subsetP=> x Lx; rewrite /= inE; apply/subsetP=> A; rewrite /= inE.
  case/imsetP=> y Ky ->{A}; rewrite !rcosetE -rcosetM -rcosetE mem_imset //.
  by rewrite groupMl // (subsetP sLK).
case/Cauchy=> // zbar Kzbar Czbar_p.
pose H := coset_of L @*^-1 <[zbar]> :&: K.
exists [group of H] => /=.
have sLH : L \subset H.
  apply/subsetP => x Lx.
  apply/setIP; split; last exact: (subsetP sLK).
  apply/setIP; split; first by rewrite (subsetP (normG _)).
  by rewrite /= inE coset_of_id // group1.
have nLH: H \subset 'N(L).
  by apply/subsetP=> x; case/setIP; case/morphpreP=> *. 
rewrite /(_ <| _) sLH nLH subsetIr.
rewrite -(@LaGrange _ _ L) // -card_quotient //= -/H (eqP cardL) mulnC.
rewrite -{}Czbar_p; apply/eqP; congr (_ * _)%N; apply: eq_card => xbar.
apply/imsetP/idP=> [[x Hx ->{xbar}]|].
  by rewrite 3!inE andbC -andbA in Hx; case/andP: Hx; case/morphpreP=>[_].
case/cycleP=> m <-{xbar}; rewrite {nLH sLH}/H.
case/morphimP: Kzbar => z [Kz Nz ->{zbar}].
exists (z ^+ m); rewrite ?morphX // inE groupX ?Kz //= inE ?groupX //.
by apply/morphpreP; split=> //; apply: cyclenn.
Qed.

Lemma sylow1: forall i j (L : group gT), i <= j <= n ->
  L \subset K -> #|L| == (p ^ i)%N ->
  exists H: group gT, [&& L \subset H, H \subset K & #|H| == p ^ j]%N.
Proof.
move=> i j L; case/andP=> Hij Hjn Hsl Hcl.
move: Hjn; rewrite -(subnK Hij) addnC.
elim: (j - i) => [| k Hrec].
  by rewrite add0n => Hin; exists L; rewrite subset_refl Hsl.
move=> Hk; case Hrec; first by apply: leq_trans Hk; rewrite addSn.
move=> H; case/and3P => Hlh Hhk Hch.
case (@sylow1_rec (k+i) H) => //.
move=> H1; rewrite -andbA; case/and4P => sH1K sHH1 _ oH1; exists H1.
by rewrite sH1K (subset_trans Hlh).
Qed.

(**********************************************************************)
(*               First Sylow theorem                                  *)
(**********************************************************************)

Theorem sylow1_subset : forall i (L : {group gT}),
  L \subset K -> #|L| == (p ^ i)%N -> 
  exists P : {group gT}, (L \subset P) && sylow p K P.
Proof.
move=> i L Hlk Hcl; case (@sylow1 i n L) => //.
  by rewrite leqnn andbT -dvdn_exp_max // -(eqP Hcl) group_dvdn.
by move=> H; case/and3P => [Hlh Hhk Hc]; exists H; rewrite Hlh // sylowE Hhk.
Qed.

Theorem sylow1_cor : exists P : {group gT}, sylow p K P.
Proof.
case (@sylow1_subset 0 [group of [set 1]]) => //=.
- by apply/subsetP => z; rewrite inE; move/eqP->; exact: group1.
- by rewrite cards1.
by move=> H; case/and3P => [_ Hhk Hc]; exists H; apply/andP.
Qed.

Lemma sylow2 : forall (H L : {group gT}) i, H \subset K ->
 #|H| = (p ^ i)%N -> sylow p K L -> exists2 x, x \in K & H \subset L :^ x.
Proof.
move => H L i Hshk Hch Hsl.
move: Hsl; rewrite sylowE; case/andP => Hsl1 Hsl2.
pose lS0 := 'C_(rcosets L K)(H | 'Msr).
have F1: ~~ (p %| #|K : L|).
  apply/negP => Fd.
  move/dvdnP: Fd => [u Hu].
  have F2: p ^ n.+1 %| #|K|.
    apply/dvdnP; exists u.
    rewrite -(LaGrange Hsl1) Hu (eqP Hsl2) /= (mulnA u).
    exact: mulnC. 
  by move: F2; rewrite /n dvdn_p_p_part // (cardD1 1) group1.
have F2: #|K : L| %% p = #|lS0| %% p.
  have: pgroup p H by apply/pnatP=> //; exists i. 
  move/pgroup_fix_mod=> <- //; apply/subsetP=> x Hx; rewrite inE /=.
  apply/subsetP=> A; rewrite inE /=; case/imsetP=> y Ly ->{A}.
  by rewrite !rcosetE -rcosetM -rcosetE mem_imset ?groupM // (subsetP Hshk).
have{F1 F2}: #|lS0| != 0.
  by move: F1; rewrite /dvdn F2; case: #|lS0|; rewrite ?mod0n.
case/existsP=> X; case/setIP; case/rcosetsP=> x Kx ->{X}.
by rewrite act_fix_sub; exists x.
Qed.

(**********************************************************************)
(*               Second Sylow theorem                                 *)
(**********************************************************************)

Lemma sylow2_cor: forall L1 L2 : {group gT},
  sylow p K L1 -> sylow p K L2 -> exists2 x, x \in K & L2 = (L1 :^ x)%G.
Proof.
move => L1 L2 Hl1; rewrite sylowE; case/andP => Ml2 Nl2.
case: (sylow2 Ml2 (eqP Nl2) Hl1) => x Hx1 Hx2.
exists x => //; apply/eqP; rewrite -val_eqE eqset_sub_card Hx2 /=.
by rewrite card_conjg (eqP Nl2); 
   move: Hl1; rewrite sylowE; case/andP => _; move/eqP ->.
Qed.
 
Theorem sylow2_subset: forall i (L P : {group gT}),
  L \subset K -> #|L| == (p ^ i)%N -> sylow p K P -> P <| K -> L \subset P.
Proof.
move=> i L P Hlk Hcl Hsp Hnp.
case (@sylow1_subset i L) => // P1; case/andP => Hlp1 Hsp1.
case (sylow2_cor Hsp Hsp1) => x Kx [EP1].
by case/normalP: Hnp => _ nPK; rewrite EP1 /= nPK in Hlp1.
Qed.

(**********************************************************************)
(*   First part of the third Sylow theorem                            *)
(**********************************************************************)

Definition gsylow A : pred {group gT} := [eta (sylow p) A].

Theorem sylow3_div : #|gsylow K| %| #|K|.
Proof.
case sylow1_cor => H Hh.
suff ->: #|gsylow K| = #|orbit 'JG%act K H| by exact: dvdn_orbit.
apply: eq_card => L; apply/idP/idP; last first.
  by case/orbitP => y Hy <- /=; rewrite /gsylow -topredE /= -sylow_sconjgr.
case/(sylow2_cor Hh) => y Hy [HH].
by apply/orbitP; exists y.
Qed.

End Sylow.

Section SylowAux.

Open Scope group_scope.

Variable (gT : finGroupType) (H K L : {group gT}).
Hypothesis subset_HL : H \subset L.
Hypothesis subset_LK : L \subset K.

Variable p : nat.
Hypothesis prime_p : prime p.
Let n := logn p #|K|.

Hypothesis n_pos: 0 < n.

Lemma sylow_subset: sylow p K H -> sylow p L H.
Proof.
rewrite !sylowE; move/andP => [H1 H2]; apply/andP; split => //.
rewrite (eqP H2) /p_part; apply/eqP.
suff ->: logn p #|K| = logn p #|L| by [].
apply/eqP; rewrite eqn_leq; apply/andP; split; last first.
  by apply dvdn_leq_log => //; exact: group_dvdn.
by rewrite /p_part in H2; rewrite -dvdn_exp_max // -(eqP H2) group_dvdn.
Qed.

End SylowAux.

Section Sylow3.

Open Scope group_scope.

Variable (gT : finGroupType) (K : {group gT}).

Variable p : nat.
Hypothesis prime_p : prime p.

Let n := logn p #|K|.

Hypothesis n_pos : 0 < n.

(**********************************************************************)
(*   Second part of the third Sylow theorem                           *)
(**********************************************************************)
Lemma sylow3_mod : #|gsylow p K| %% p = 1%N.
Proof.
case (sylow1_cor K prime_p) => H; rewrite sylowE => Hh.
case/andP: (Hh) => F2 F3.
pose Syl := [set P | gsylow p K P].
suff <-: #|Syl| %% p = 1%N by rewrite cardsE.
have: [acts (H | 'JG) on Syl].
  apply: (subset_trans F2); apply/actsP=> x Kx P.
  by rewrite !inE /gsylow !sylowE card_conjg -{1}(conjGid Kx) conjSg.
move/pgroup_fix_mod=> -> //; last first.
  by rewrite /pgroup /pi_group (eqP F3) p_part_pi pi_nat_part.
rewrite -(([set H] =P _ :&: _) _).
  by rewrite cards1 modn_small ?prime_gt1.
rewrite eqset_sub {1}sub1set 2!inE /gsylow sylowE Hh /=; apply/andP; split.
  by apply/afixP=> x Hx; apply: group_inj; exact: conjGid.
apply/subsetP=> L; rewrite 2!{1}inE; case/andP=> sylL; move/afixP=> fixL.
rewrite inE eq_sym -val_eqE eqset_sub_card /= (eqP F3).
move: (sylL); rewrite /gsylow sylowE; case/andP => sLK.
move/eqP->; rewrite leqnn andbT.
have nLN: L <| 'N_K(L) by rewrite /(L <| _) subsetI sLK normG subsetIr.
apply: sylow2_subset F3 _ (nLN) => //.
  by rewrite subsetI F2; apply/normsP=> x Hx; rewrite -{2}(fixL x Hx).
by apply: sylow_subset sylL; rewrite ?subsetIl //; case/andP: nLN.
Qed.

End Sylow3.

Lemma Frattini : forall (gT : finGroupType) (G H P : {group gT}) p,
  H <| G -> prime p -> sylow p H P -> H * 'N_G(P) = G.
Proof.
move=> gT G H P p; case/normalP=> sHG nHG p_prime sylP.
have sPG: P \subset G by apply: subset_trans sHG; case/andP: sylP.
apply/eqP; rewrite eqset_sub setIC group_modl // subsetIr.
apply/subsetP=> x Gx; pose Q := (P :^ x^-1)%G.
have sylQ: sylow p H Q by  by rewrite (sylow_sconjg _ _ _ x) conjsgKV nHG.
have [y Hy [/= QPy]] := sylow2_cor p_prime sylP sylQ.
rewrite inE Gx andbT -(mulKg y x) mem_mulg ?groupV //.
by apply/normP; rewrite conjsgM -QPy conjsgKV.
Qed.

Definition sylows (gT : finGroupType) (G: {group gT}) (A: {set gT}):=
   if primes #|A| is [::p] then group_set A && sylow p G A
   else false.

Lemma sylowsP (gT : finGroupType) (G: {group gT}) P: 
  reflect (exists p, [/\ prime p, p %| #|G|, group_set P & sylow p G P]) 
          (sylows G P).
Proof.
move=> gT G P; apply: (iffP idP).
  rewrite /sylows; case: primes (mem_primes^~ #|P|)=> // p [|p1] //.
  move/(_ p); rewrite inE eqxx /=; move/eqP.
  rewrite eq_sym; move/eqP; move/idP; case/and3P=> H1P H2P H3P.
  case/andP=> H4P H5P; exists p; split=> //.
  rewrite (dvdn_trans H3P) // (@group_dvdn _ _ (Group H4P)) //=.
  by case/andP: H5P.
case=> p [H1p H2p H3p]; rewrite sylowE; case/andP=> H4p H5p.
by rewrite /sylows (eqP H5p) 
          !(primes_exp, primes_prime, H3p, sylowE, H4p) //  
          -dvdn_exp_max // expn1.
Qed.

Lemma normal_sylowP : forall (gT : finGroupType) (G : {group gT}) p,
  prime p -> reflect (exists2 P : {group gT}, sylow p G P & (P <| G)%g)
                     (#|gsylow p G| == 1%N).
Proof.
move=> gT G p p_pr; apply: (iffP idP) => [syl1 | [P sylP nPG]].
  have [P sylP]: exists P, P \in gsylow p G.
    by apply/existsP; rewrite /pred0b (eqP syl1).
  exists P => //; apply/normalP; split=> [|x Gx]; first by case/andP: sylP.
  apply/eqP; apply/idPn=> nPxP.
  rewrite (cardD1 P) sylP eqSS in syl1; case/existsP: syl1.
  exists (P :^ x)%G; rewrite /= nPxP -topredE /gsylow /=.
  by rewrite -(conjGid Gx) -sylow_sconjg.
rewrite (cardD1 P) [P \in _]sylP eqSS; apply/pred0P=> Q /=.
apply/andP=> [[nQP sylQ]]; case/eqP: nQP; apply: val_inj=> /=.
case: (sylow2_cor p_pr sylP sylQ) => x Gx ->{Q sylQ}.
case/normalP: nPG => _; exact.
Qed.

Lemma sylowNLE : forall (gT : finGroupType) (G P Q : {group gT}) p,
  prime p -> (P <| G)%g -> sylow p G P -> sylow p G Q -> P = Q :> set _.
Proof.
move=> gT G P Q p Pp Npg Sp Sq.
have: #|gsylow p G| == 1%N by apply/(normal_sylowP _ Pp); exists P.
  rewrite (cardD1 P) (cardD1 Q) .
rewrite [_ \in _]Sp inE [predD1 _ _ _]/= [_ \in _]Sq.
by case E1: (Q == P) => //; move/eqP: E1->.
Qed.

Section DirProd.

Variable gT: finGroupType.

(* General lemmas to get to sylow_dirprod *) 
Lemma coprime_bigprod: forall p (I: eqType) r (P : pred I) F,
  (forall i : I, P i  && (i \in r) -> coprime p (F i)) ->
  coprime p (\prod_(i <- r | P i) F i).
Proof.
move=> p I r P F HcF.
apply big_prop_seq => [| x y Hx Hy |//]; first by exact: coprimen1.
by rewrite coprime_mulr Hx.
Qed.

Lemma div_primes: forall (n m: nat), 0 < n ->
  (forall p, p \in primes n -> p_part p n %| m) -> n %| m.
Proof.
move=> n m Hn Hpa.
rewrite -(prod_p_parts Hn).
have: forall i, i \in primes n -> prime i.
  by move=> i; rewrite mem_primes; case/andP.
have: uniq (primes n) by exact: uniq_primes.
elim: (primes n) Hpa => [| i r Hrec];
  rewrite !(big_seq0, big_adds) /= ?dvd1n //.
move=> H1; case/andP=> H2 H3 H4.
have Hrec1: \prod_(p <- r) p_part p n %| m.
  by apply: Hrec => // p Hp; rewrite (H1, H4) // inE orbC Hp.
rewrite gauss_inv //; first by rewrite Hrec1 H1 // inE eqxx.
apply: coprime_bigprod => j /= Hj.
rewrite coprime_expl // coprime_expr //.
have Pi: prime i by rewrite H4 // inE eqxx.
have Pj: prime j by rewrite H4 // inE orbC Hj.
rewrite prime_coprime //.
apply/negP => HH; case/negP: H2.
case/primeP: (Pj) => _; move/(_  _ HH); case/orP => // Hi.
  by move: Pi; rewrite (eqP Hi).
by rewrite (eqP Hi).
Qed.

Lemma comm_bigprod: forall (A: {set gT}) (I: eqType) r (P: pred I) F,
  (forall i, P i && (i \in r) -> A \subset 'C(F i)) -> 
  A \subset 'C(\prod_(i <- r | P i) F i).
Proof.
move=> A I r P F Hg.
apply: (@big_prop_seq _ (fun x => A \subset 'C(x))) => 
    [|B C HB HC|//]; rewrite centsC; last first.
  by rewrite mul_subG // centsC.
by apply/subsetP=> x; rewrite inE; move/eqP->; rewrite group1.
Qed.

Lemma subset_bigprod: forall (A: {group gT}) I r (P: pred I) (F: I -> {set gT}),
  (forall i : I, P i -> F i \subset A) -> \prod_(i <- r | P i) F i \subset A.
Proof.
move=> A I r P F Hg.
by apply big_prop => [| B C HB HC|//]; rewrite (sub1G, mul_subG).
Qed.

Lemma group_set_bigprod: forall (I: eqType) (r : seq I) P (F: I -> {set gT}),
   uniq r ->
  (forall i, P i && (i \in r) -> group_set (F i)) ->
  (forall i j, i <> j -> P i && (i \in r) -> P j && (j \in r) ->
           (F i) \subset 'C(F j)) ->
  group_set (\prod_(i <- r | P i) F i).
Proof.
move=> I r P F; elim: r => [| i r Hrec];
  rewrite !(big_seq0, big_adds, group_set_unit) => //=.
case/andP => Hir Hu Hi Ha.
have HGi: group_set (\prod_(j <- r | P j) F j).
  apply: Hrec => [//| i1 | i1 j1 Hi1j1]; case/andP => Hp1 Hip1.
    by rewrite Hi // Hp1 inE orbC Hip1.
  by case/andP => Hpj1 Hjp1; rewrite Ha // inE ?Hip1 ?Hjp1 orbC andbC.
case Ep1: (P i) => //.
have HG1: group_set (F i) by rewrite Hi // Ep1 inE eqxx.
pose Gi := (Group HG1).
pose G1 := (Group HGi).
apply/group_setP; split.
  by apply/imset2P; exists (1:gT) (1:gT); rewrite ?mul1g ?(group1 Gi) ?(group1 G1).
move=> x y; case/imset2P=> x1 x2 Hx1 Hx2 ->; case/imset2P=> y1 y2 Hy1 Hy2 ->.
apply/imset2P; exists (x1 * y1) (x2 * y2); first by rewrite (@groupM _ Gi).
  by rewrite (@groupM _ G1).
rewrite !mulgA; congr mulg; rewrite -!mulgA; congr mulg.
suff: F i \subset 'C(\prod_(j <- r| P j) F j) by  move/centsP; move/(_ _ Hy1 _ Hx2).
apply: comm_bigprod => j; case/andP => H1j H2j.
apply: Ha => [Hij||]; first by case/negP: Hir; rewrite Hij.
  by rewrite Ep1 inE eqxx.
by rewrite H1j inE orbC H2j.
Qed.

Lemma card_bigprod: forall (I: eqType) (r : seq I) P (F: I -> {set gT}),
  uniq r ->
  (forall i, P i && (i \in r) -> group_set (F i)) ->
  (forall i j, i <> j -> P i && (i \in r) -> P j && (j \in r) ->
           (F i) \subset 'C(F j)) ->
  (forall i j, i <> j -> P i && (i \in r) -> P j && (j \in r) ->
           coprime #|F i| #|F j|) ->
  #|(\prod_(i <- r | P i) (F i: set _))| =  (\prod_(i <- r | P i) #|F i|)%N.
Proof.
move=> I r P F; elim: r => [| i r Hrec];
  rewrite !(big_seq0, big_adds, cards1) => //=.
case/andP=> H1u H2u Hg Hs Hc.
have Hr: #|\prod_(i <- r | P i) F i| = (\prod_(i <- r | P i) #|F i|)%N.
  apply: Hrec => [// | i1 | i1 j1 Hij1 | i1 j1 Hij1]; case/andP => H1i1 H2i1.
  - by rewrite Hg // H1i1 inE H2i1 orbC.
  - by case/andP => H1j1 H2j1; rewrite Hs // (H1i1, H1j1) inE (H2i1, H2j1) orbC.
  by case/andP => H1j1 H2j1; rewrite Hc // (H1i1, H1j1) inE (H2i1, H2j1) orbC.
case Ep1: (P i) => //.
have HG1: group_set (F i) by rewrite Hg // Ep1 inE eqxx.
set H := reducebig _ _ _ _ _.
have GH: group_set H.
  apply: group_set_bigprod =>  [// | i1 | i1 j1 Hij1]; case/andP => H1i1 H2i1.
  - by rewrite Hg // H1i1 inE H2i1 orbC.
  by case/andP => H1j1 H2j1; rewrite Hs // (H1i1, H1j1) inE (H2i1, H2j1) orbC.
pose Gi := (Group GH).
pose G1 := (Group HG1).
rewrite (@coprime_card_mulG _ G1 Gi) //= Hr //.
apply: coprime_bigprod => j; case/andP => H1j H2j.
rewrite Hc // ?(Ep1, H1j, inE, eqxx, H2j, orbT) //.
by move=> Hij; case/negP: H1u; rewrite Hij.
Qed.

Lemma sylow_dirprod (G : {group gT}):
  (forall Pi, sylows G Pi -> Pi <| G) ->
 \big[direct_product/1]_(Pi | sylows G Pi) Pi = G.
Proof.
move => G HG.
pose r := index_enum  [finType of {set gT}].
have Hur: uniq r by apply: uniq_enum.
have Hgr: forall i, sylows G i && (i \in r) -> group_set i.
  by move=> i; case/andP; case/sylowsP => p; case.
have Hcr: forall Pi Pj, Pi <> Pj -> 
            sylows G Pi && (Pi \in r) -> sylows G Pj && (Pj \in r) -> 
            coprime #|Pi| #|Pj|.
  move=> Pi Pj Hij.
  case/andP; case/sylowsP => p1 [H1pi H2pi H3pi]; 
     rewrite sylowE; case/andP => H4pi H5pi H6pi.
  case/andP; case/sylowsP => p2 [H1pj H2pj H3pj];
     rewrite sylowE; case/andP => H4pj H5pj H6pj.
  rewrite (eqP H5pi) (eqP H5pj) coprime_expl // coprime_expr //.
  rewrite prime_coprime //.
  apply/negP => Hp1p2; case: Hij; apply: (@sylowNLE _ G (Group H3pi) (Group H3pj) _ H1pi).
  - by apply: HG; apply/sylowsP; exists p1; split => //; rewrite sylowE H4pi.
  - by rewrite sylowE H4pi.
  case/primeP: H1pj => _; move /(_ _ Hp1p2); case/orP.
    by move/eqP => Hp1; move: H1pi; rewrite Hp1.
  by move/eqP->; rewrite sylowE H4pj.
have Hsr: forall Pi Pj, Pi <> Pj -> 
            sylows G Pi && (Pi \in r) -> sylows G Pj && (Pj \in r) -> 
            Pi \subset 'C(Pj).
  move=> Pi Pj Hij Hsi Hsj.
  case/andP: (Hsi); case/sylowsP => p1 [H1pi H2pi H3pi]; case/andP => H4pi H5pi H6pi.
  case/andP: (Hsj); case/sylowsP => p2 [H1pj H2pj H3pj]; case/andP => H4pj H5pj H6pj.
  apply/centsP => x Hx y Hy.
  apply/commgP.
  have Ht: trivg (Pi :&: Pj).
    by rewrite (@coprime_trivg _ (Group H3pi) (Group H3pj)) // Hcr.
  move/subsetP: Ht; move/(_ [~ x, y]); rewrite !inE => -> //.
  rewrite -[Pi]/(Group H3pi: set _) -[Pj]/(Group H3pj: set _)
          {1}commgEl commgEr; apply/andP; split; rewrite groupM // ?groupV //.
    have: Pi <| G by apply: HG; case/andP: Hsi.
    case/normalP => /= _; move/(_ y)<-; last by apply: (subsetP H4pj).
    by apply/imsetP; exists x.
  have: Pj <| G by apply: HG; case/andP: Hsj.
  case/normalP => /= _; move/(_ x)<-; last by apply: (subsetP H4pi). 
  by apply/imsetP; exists (y^-1); rewrite // (@groupV _ (Group H3pj)) //.
have GP: group_set (\prod_(Pi | sylows G Pi) Pi) by apply: group_set_bigprod.
have<-: \prod_(Pi | sylows G Pi) Pi = G.
  apply/eqP; rewrite eqset_sub_card.
  rewrite subset_bigprod; last by move=> i; case/sylowsP => x [_ _ _]; case/andP.
  apply: dvdn_leq => //.
    by rewrite (@ltn_0group _ (Group GP)).
  apply: div_primes; first by apply: ltn_0group.
  move=> p Hp.
  have H1p: prime p.
    by move: Hp; rewrite mem_primes; case/and3P.
  case: (@sylow1_cor _ G _ H1p) => Pj HPj.
  move: (HPj); rewrite sylowE; case/andP => _; rewrite /p_part; move/eqP<-.
  rewrite card_bigprod //-/r.
  have: (Pj: [finType of {set gT}]) \in r by rewrite mem_enum //.
  elim: (r) => [| i r1 Hrec]; rewrite !(big_seq0, big_adds) => //=.
  rewrite inE; case/orP => H1Pj; last first.
    by case: sylows; rewrite ?(dvdn_mull) // Hrec.
  rewrite -(eqP H1Pj); suff->: sylows G Pj by rewrite dvdn_mulr.
  apply/sylowsP; exists p; split; rewrite // ?groupP //.
  by move: Hp; rewrite mem_primes; case/and3P.
have: uniq r by apply: uniq_enum.
rewrite -/r; elim: (r) => [| Pi r1 Hrec]; rewrite !(big_seq0, big_adds) => //=.
case/andP => H1r1 H2r1; move: (Hrec H2r1) => Hrec1; case E1: (sylows _ _) => //.
rewrite {1}/direct_product Hrec1 //.
set H:= \prod_(Pi <- r1 | sylows G Pi)Pi.
have F1: forall i, sylows G i && (i \in r1) -> group_set i.
   by move=> Pi1; case/andP=> HPi1 _; rewrite Hgr // HPi1 mem_enum.
have F2: forall i j, i <> j ->
  sylows G i && (i \in r1) -> sylows G j && (j \in r1) -> coprime #|i| #|j|.
  by move=> Pi1 Pj1 Hij1; case/andP=> HPi1 _; case/andP=> HPj1 _; 
     rewrite Hcr // (HPi1, HPj1) mem_enum.
have F3: forall Pj, sylows G Pj && (Pj \in r1) -> coprime #|Pi| #|Pj|.
  move=> Pi1; case/andP=> H1Pi1 H2Pi1; rewrite Hcr // ?(E1, H1Pi1, mem_enum) //.
  by move=> HH; case/negP: H1r1; rewrite HH.
have F4: forall i j, i <> j ->
  sylows G i && (i \in r1) -> sylows G j && (j \in r1) -> i \subset 'C(j).
  by move=> Pi1 Pj1 Hij1; case/andP=> HPi1 _; case/andP=> HPj1 _; 
     rewrite Hsr // (HPi1, HPj1) mem_enum.
have GPi: group_set Pi by rewrite Hgr // E1 mem_enum.
have GH: group_set H by apply: (group_set_bigprod  H2r1).
have->: trivg (Pi :&: \prod_(Pi <- r1 | sylows G Pi)Pi) by
  rewrite (@coprime_trivg _ (Group GPi) (Group GH)) ?(card_bigprod,coprime_bigprod).
rewrite /central_product GPi GH.
have ->: Pi \subset 'C(H).
  apply: comm_bigprod => Pi1.
  case/andP=> HPi1 H1Pi1; rewrite Hsr // ?(E1, HPi1, mem_enum) //.
  by move=> HH; case/negP: H1r1; rewrite HH.
case: eqP => He1; first by rewrite He1 -{1}(@set_mul1g gT H).
by case: eqP => He2; rewrite // He2 -{1}(mulg1 Pi).
Qed.


End DirProd.

Section Nilpotent.

Variable (gT : finGroupType).
Implicit Type G H : {group gT}.

Lemma nilpotent_pgroup : forall G, is_pgroup G -> nilpotent G.
Proof.
move=> G pgG.
case: (leqP #|G| 1).
  by rewrite -trivg_card; case/trivGP=> ->; exact: nilpotent1.
move/prime_pdiv; set p := pdiv _ => pr_p; have Gpos: #|G| > 0 by [].
move: (part_pi_nat pgG); rewrite -p_part_pi -/p /p_part.
move: (logn _ _) => m oG; apply/ucnP; exists m; apply/eqP.
rewrite eqset_sub_card ucn_subset0 /= -oG.
elim: {-2}m (leqnn m) => [|k IHk] ltkm; first exact: pos_card_group.
case/andP: (ucn_normal G k) => sZ nZ.
  case/andP: (ucn_normal0 G k) => sZG nZG.
have: #|G / 'Z_k(G)| %| #|G|.
  by rewrite card_quotient // -(LaGrange sZG) dvdn_mull.
rewrite -oG; case/dvdn_exp_prime=> // [] [|j] lejk oGbar.
  apply: (@leq_trans #|G|); first by rewrite -oG leq_exp2l // prime_gt1.
  apply: subset_leq_card; apply: subset_trans sZ.
  by rewrite -trivg_quotient // trivg_card oGbar.
rewrite -(LaGrange sZ) -card_quotient //= ucn_center expnSr.
rewrite leq_mul ?(IHk (ltnW _)) // dvdn_leq ?pos_card_group //.
have:= pgroup_ntriv pr_p oGbar; rewrite trivg_card.
have: #|'Z(G / 'Z_k(G))| %| p ^ j.+1 by rewrite -oGbar group_dvdn // subsetIl.
by case/dvdn_exp_prime=> // [] [|i] _ -> // _; rewrite dvdn_mulr.
Qed.


Lemma small_nil_class : forall G, nil_class G <= 5 -> nilpotent G.
Proof.
move=> G; have Hg0: (0 < #|G|) by rewrite (cardD1 1) group1.
move=> leK5.
case: (ltnP 5 #|G|) => [lt5G | leG5 {leK5}].
  by rewrite nilpotent_class (leq_ltn_trans leK5).
apply: nilpotent_pgroup.
move: Hg0 leG5; rewrite /is_pgroup /pgroup /pi_group; move: #|G|.
by do 6!case => //.
Qed.

Lemma nilpotent_sylow: forall G: {group gT}, 
  nilpotent G <-> \big[direct_product/1]_(Pi | sylows G Pi) Pi = G.
Proof.
move=> G; have Hg0: (0 < #|G|) by rewrite (cardD1 1) group1.
split=> Hg; last first.
  apply: (nilpotent_bigdprod Hg) => Pi.
  case/sylowsP=> p [H1p H2p H3p] HS.
  have HS1: is_sylow G (Group H3p) by apply/is_sylowP; exists p.
  move: HS; rewrite sylowE; case/andP=> H4p H5p.
  suff: nilpotent (Group H3p) by done.
  by apply: nilpotent_pgroup; move: HS1; rewrite is_sylowE; case/andP.
apply: sylow_dirprod.
move=> Pi; case/sylowsP=> p [H1p H2p H3p H4p].
pose H := 'N_G(Pi)%G; pose N := 'N_G(H)%G.
have SHG: H \subset G by apply/subsetP=> x; rewrite inE; case/andP.
rewrite (@nilpotent_sub_norm _ G H) //.
  by apply: (@normalSG _ G (Group H3p)); case/andP: H4p.
have normHN: H <| N.
  by apply: normalSG; apply/subsetP=> x; rewrite inE; case/andP.
have SPi: sylow p H Pi.
 apply: (@sylow_subset gT (Group H3p) G)=> //=.
   apply/subsetP=> x; rewrite inE => Hx.
   case/andP: H4p; move/subsetP; move/(_ x Hx)=> -> _.
   by exact: (subsetP (normG (Group H3p)) x Hx).
move: (@Frattini _ _ _ (Group H3p) _ normHN H1p SPi).
suff H1: 'N_N(Pi) \subset H.
  by rewrite (mulGSgid (group1 _)) // => EHN; rewrite {2}EHN.
by apply/subsetP=> x; rewrite !inE; rewrite -andbA; case/and3P=> ->.
Qed.

End Nilpotent.

Section PGroups.


Variable (p: nat) (prime_p: prime p).
Variable (gT : finGroupType).
Implicit Type G H : {group gT}.

(* Bender 1.22 p.9 *)

Lemma normal_pgroup: forall k r (G N : {group gT}), 
  pgroup p G -> N <| G -> #|N| = (p ^ k)%N -> r <= k -> 
   exists L: {group gT}, [/\ L \subset N, L <| G & #|L| = (p ^ r)%N].
Proof.
move=> k; move: {-2}k (leqnn k) gT.
elim: k => [| k Hrec] [| k1//] Hk1 gT1 [|r//] G N PG NNG CG Lrk; try by exists N.
  exists (unit_group gT1); split => //; first by exact: sub1G.
    apply/normalP; split; first exact: sub1G.
    by move=> x Hx; rewrite /= conjs1g.
  by rewrite expn0 cards1.
have PN := pgroupS (normal_sub NNG) PG.
case/(pnatP _ prime_p): (PG) => k2 Hk2.
pose N1 := (N :&: 'Z(G))%G.
have SN1: N1 \subset N by rewrite subsetIl.
have PN1 := pgroupS SN1 PN.
have NTN1: ~~ trivg N1.
  apply: nilpotent_meet_center => //.
    by apply: nilpotent_pgroup; apply: (@pgroup_is_pgroup _ p).
  by rewrite trivg_card CG -ltnNge -(expn0 p) ltn_exp2l // prime_gt1.
have DN1: #|N1| %| (p ^k1.+1)%N. 
  by rewrite -CG -(LaGrangeI N 'Z(G)) dvdn_mulr.
have CN1: p %| #|N1|.
  case/(dvdn_exp_prime _ _ prime_p): DN1 => [[|n]] _ Hn; last by rewrite Hn dvdn_exp.
  by case/negP: NTN1; rewrite trivg_card Hn expn0.
case/(pnatP _ prime_p): (PN1) => [[| k3] Hk3].
  by move: CN1; rewrite Hk3 expn0 dvdn1; case: p prime_p => //; case.
case: (Cauchy prime_p CN1) => a Sa; rewrite {1}/order=> Ca1.
pose G1 := (G / <[a]>)%G; pose N2 := (N / <[a]>)%G.
have [NNG1 _] := andP NNG; have [Sa1 Sa2] := setIP _ _ _ Sa.
have IaG: a \in G by apply: (subsetP NNG1).
have NCa: <[a]> <| G.
  apply/andP; split; first by apply: cycle_h.
  suff<-: 'C_G[a] = G by apply: normal_centraliser.
  apply/setIidPl; apply/subsetP => x Hx; apply/cent1P.
  by case/centerP: Sa2 => _;move/(_ _ Hx).
case/andP: NCa => NCa1 NCa2.
have SaN: <[a]> \subset N by apply: cycle_h.
have Dk: forall k, (p^k.+1%/p = p^k)%N.
  by move=> kk; rewrite divn_mulr // ltn_0prime.
case (Hrec _ Hk1 _ r G1 N2) => //.
- apply/(pnatP _ prime_p); exists k2.-1.
  rewrite card_quotient // -group_divn //.
  move/subset_leq_card: NCa1; rewrite Hk2 Ca1.
  case: {Hk2}k2 => [| k2 _]; last by rewrite Dk.
  by rewrite expn0; case: p prime_p => //; case.
- by apply: morphim_normal.
- rewrite card_quotient; last by rewrite (subset_trans NNG1).
  by rewrite -group_divn // Ca1 CG Dk.
move=> L1 [H1L1 H2L2 H3L3]; pose H := (G :&: coset_of <[a]> @*^-1 L1)%G.
have Iaa := cyclenn a.
have EG: coset_of <[a]> @*^-1 G1 = G by rewrite cosetimK // (mulSgGid Iaa).
have EN: coset_of <[a]> @*^-1 N2 = N.
  have SNa: N \subset 'N(<[a]>) by rewrite (subset_trans NNG1).
  by rewrite cosetimK // (mulSgGid Iaa).
have SaH: <[a]>%G \subset H.
  by rewrite subsetI NCa1 {1}ker_cosetE morphpreS // sub1G.
have NaH: H \subset 'N(<[a]>) by rewrite (subset_trans (subsetIl _ _)).
have QH: H/<[a]> = L1.
  case/andP: H2L2 => H2L2 _.
  rewrite /H quotientE cosetimGI // -quotientE -/G1 
         !(morphpreK, subset_trans H2L2, morphimS) //.
  by apply/setIidPr.
exists  H; split; last first.
- by rewrite -(@LaGrange _ _ <[a]>) // -card_quotient // QH H3L3 Ca1.
- by move: H2L2; rewrite -QH -(@morphpre_normal _ _  _ (coset_of_morphism <[a]>));
   [rewrite EG cosetimGK | apply: morphimS | apply: morphimS].
by rewrite (subset_trans (subsetIr _ _)) // -EN morphpreS.
Qed.

End PGroups.

Unset Implicit Arguments.
