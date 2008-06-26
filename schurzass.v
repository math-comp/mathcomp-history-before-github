Require Import ssreflect ssrbool ssrfun eqtype ssrnat div.
Require Import fintype ssralg bigops finset.
Require Import groups normal automorphism action.
Require Import commutators cyclic center sylow.

(* Require Import seq paths connect finfun group_perm. *)

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Import GroupScope.

Lemma Frattini : forall (gT : finGroupType) (G H P : {group gT}) p,
  H <| G -> prime p -> sylow p H P -> H * 'N_G(P) = G.
Proof.
move=> gT G H P p; case/normalsubP=> sHG nHG p_prime sylP.
have sPG: P \subset G by apply: subset_trans sHG; case/andP: sylP.
apply/eqP; rewrite eqset_sub setIC group_modl // subsetIr.
apply/subsetP=> x Gx; pose Q := (P :^ x^-1)%G.
have sylQ: sylow p H Q by  by rewrite (sylow_sconjg _ _ _ x) conjsgKV nHG.
have [y [Hy QPy]] := (sylow2_cor p_prime sylP sylQ).
rewrite inE Gx andbT -(mulKg y x) mem_mulg ?groupV //.
by apply/normgP; rewrite conjsgM -QPy conjsgKV.
Qed.

Section Split.

Variable gT : finGroupType.

Section Defs.

Variables G H : {set gT}.

Definition complg := [set K : {group gT} | trivg (H :&: K) && (H * K == G)].

Definition splitg := #|complg| != 0.

Definition divgr x := x * (remgr G H x)^-1.

End Defs.

Variables G H : group gT.

Lemma complgP : forall K : {group gT},
  reflect (trivg (H :&: K) /\ H * K = G) (K \in complg G H).
Proof.
by move=> K; rewrite inE; apply: (iffP andP); case; split=> //; apply/eqP.
Qed.

Lemma splitgP :
  reflect (exists2 K : {group gT}, trivg (H :&: K) & H * K = G) (splitg G H).
Proof.
by apply: (iffP pred0Pn); case=> K; first case/complgP;
  exists K; last apply/complgP.
Qed.

Variable K : group gT.

Lemma split_pr : forall x, x = divgr K H x * remgr K H x.
Proof. by move=> *; rewrite mulgKV. Qed.

Lemma divgr_id : forall x y, x \in H -> divgr K H (x * y) = x * divgr K H y.
Proof. by move=> *; rewrite /divgr remGr_id ?mulgA. Qed.

Lemma mem_remgr : forall x, x \in H * K -> remgr K H x \in K.
Proof. by move=> x; rewrite -mem_remGr; case/setIP. Qed.

Lemma mem_divgr : forall x, x \in H * K -> divgr K H x \in H.
Proof.
by move=> x; rewrite -mem_remGr inE rcoset_sym mem_rcoset; case/andP.
Qed.

Section Disjoint.

Hypothesis trHK : trivg (H :&: K).

Lemma remgr_idr : forall x, x \in K -> remgr K H x = x.
Proof.
move=> x Kx; apply/eqP; rewrite eq_mulgV1 -in_set1 -[[set 1]]/(1%G : set gT).
rewrite -(trivGP _ trHK) inE -mem_rcoset groupMr ?groupV // -in_setI.
by rewrite setIC mem_remGr (subsetP (mulG_subr _ _)).
Qed.

Lemma remgr_idl : forall x y, x \in H -> y \in K -> remgr K H (x * y) = y.
Proof. by move=> *; rewrite remGr_id // remgr_idr. Qed.

Lemma divgr_idl : forall x y, x \in H -> y \in K -> divgr K H (x * y) = x.
Proof. by move=> *; rewrite /divgr remgr_idl // mulgK. Qed.

End Disjoint.

Lemma complgC : (H \in complg G K) = (K \in complg G H).
Proof.
rewrite !inE setIC; congr (_ && _).
by apply/eqP/eqP=> defG; rewrite -(comm_group_setP _ _ _) // defG groupP.
Qed.

Hypothesis cK : K \in complg G H.

Lemma sub_compl : K \subset G.
Proof. case/complgP: cK => _ <-; exact: mulG_subr. Qed.

Hypothesis nHG : H <| G.

Lemma remGrM : {in G &, {morph remgr K H : x y / x * y}}.
Proof.
case/normalsubP: nHG => _; case/complgP: cK => trHK <- nHHK x y HKx HKy.
rewrite {1}[y]split_pr mulgA (conjgCV x) {2}[x]split_pr -2!mulgA mulgA.
rewrite remGr_id 1?remgr_idr // groupMl -?mem_conjg ?nHHK //;
  by rewrite (mem_remgr, mem_divgr).
Qed.

End Split.

Prenex Implicits complg splitg divgr.

Theorem Gaschutz_split : forall (gT : finGroupType) (G H P : {group gT}) p,
  prime p -> H <| G -> sylow p G P -> H \subset P -> abelian H ->
  splitg G H = splitg P H.
Proof.
move=> gT G H P p prime_p nsHG sylP sHP abelH.
have sPG: P \subset G by case/andP: sylP.
have [sHG nHG] := andP nsHG.
apply/splitgP/splitgP=> [[K trHK eqHK] | [Q trHQ eqHQ]].
  exists (K :&: P)%G.
    by apply: subset_trans trHK; rewrite setIA subsetIl.
  by rewrite group_modl // eqHK; apply/setIidPr.
have sQP: Q \subset P by rewrite -eqHQ mulG_subr.
pose rP x := repr (P :* x); pose pP x := x * (rP x)^-1.
have PpP: forall x, pP x \in P.
  by move=> x; rewrite -mem_rcoset rcoset_repr rcoset_refl.
have rPmul : forall x y, x \in P -> rP (x * y) = rP y.
  by move=> x y Px; congr repr; apply: rcoset_trans1; rewrite mem_mulg ?set11.
pose pQ x := remgr Q H x; pose rH x := pQ (pP x) * rP x.
have pQhq: forall h q, h \in H -> q \in Q -> pQ (h * q) = q.
  by exact: remgr_idl.
have pQmul: forall x y, x \in P -> y \in P -> pQ (x * y) = pQ x * pQ y.
  apply: remGrM; [exact/complgP | exact: normalsubS nsHG].
have HrH: forall x, rH x \in H :* x.
  by move=> x; rewrite rcoset_sym mem_rcoset invMg mulgA mem_divgr // eqHQ PpP.
have GrH: forall x, x \in G -> rH x \in G.
  by move=> x Gx; rewrite -(groupMr _ (groupVr Gx)) (subsetP sHG) -?mem_rcoset.
have rH_Pmul: forall x y, x \in P -> rH (x * y) = pQ x * rH y.
  by move=> *; rewrite /rH mulgA -pQmul; first by rewrite /pP rPmul ?mulgA.
have rH_Hmul: forall h y, h \in H -> rH (h * y) = rH y.
  by move=> h y Hh; rewrite rH_Pmul ?(subsetP sHP) // -(mulg1 h) pQhq // mul1g.
pose toH x : {x' | x' \in H} := insubd (Sub 1 (group1 H)) x.
have valH: {in H, cancel toH val} by move=> *; exact: insubdK.
pose Hgrp := [is {x | x \in H} <: finGroupType].
have mulHC : commutative (@mulg Hgrp).
  by case=> x Hx [y Hy]; apply: val_inj; rewrite /= abelH.
pose gTH := Ring.AdditiveGroup (@mulgA _) mulHC (@mul1g _) (@mulVg _).
have Hval: forall u : gTH, sval u \in H by exact: valP.
have valM: forall a b : gTH, sval (a + b)%R = sval a * sval b by [].
have valE: forall (a : gTH) n, sval (a*+n)%R = sval a ^+ n.
  by move=> a; elim=> // n IHn; congr (_ * _).
pose mu x y : gTH := toH ((rH x * rH y)^-1 * rH (x * y)).
pose nu y := (\sum_(Px \in rcosets P G) mu (repr Px) y)%R.
have rHmul : forall x y,
  x \in G -> y \in G -> rH (x * y) = rH x * rH y * sval (mu x y).
- move=> x y Gx Gy; rewrite valH ?mulKVg // -mem_lcoset lcoset_sym.
  rewrite -norm_rlcoset; last by rewrite (subsetP nHG) ?GrH ?groupM.
  rewrite (rcoset_trans1 (HrH _)) -rcoset_mul ?(subsetP nHG) ?GrH //.
  by rewrite mem_mulg.
have mu_Pmul: forall x y z, x \in P -> mu (x * y) z = mu y z.
  move=> x y z Px; congr toH; rewrite -mulgA !(rH_Pmul x) ?rPmul //.
  by rewrite -mulgA invMg -mulgA mulKg.
have mu_Hmul: forall x y z, x \in G -> y \in H -> mu x (y * z) = mu x z.
  move=> x y z Gx Hy; congr toH.
  rewrite (mulgA x) (conjgCV x) -mulgA 2?rH_Hmul //.
  by rewrite -mem_conjg (normgP _) ?(subsetP nHG).
have{mu_Hmul} nu_Hmul: forall y z, y \in H -> nu (y * z) = nu z.
  move=> y z Hy; apply: eq_bigr => Px; case/rcosetsP=> x Gx ->{Px}.
  apply: mu_Hmul y z _ Hy.
  by rewrite -(groupMl _ (subsetP sPG _ (PpP x))) mulgKV.
pose actG (a : gTH) y : gTH := toH (sval a ^ rH y).
have valG: forall a y, y \in G -> sval (actG a y) = sval a ^ rH y.
  move=> a y Gy; rewrite valH // -mem_conjgV (normgP _) ?Hval //=.
  by rewrite groupV (subsetP nHG) // GrH.
have actG0: forall y, y \in G -> (actG 0 y = 0)%R.
  by move=> y Gy; apply: val_inj; rewrite /= valG //= conj1g.
have actGM: forall a b y, y \in G -> (actG (a + b) y = actG a y + actG b y)%R.
  by move=> a b y Gy; apply: val_inj; rewrite /= !valG //= conjMg.
have actGE: forall a n y, y \in G -> (actG (a *+ n) y = actG a y *+ n)%R.
  by move=> a n y Gy; apply: val_inj; rewrite /= !(valE, valG) // conjXg.
have cocycle_mu: forall x y z, x \in G -> y \in G -> z \in G ->
  (mu (x * y)%g z + actG (mu x y) z = mu y z + mu x (y * z)%g)%R.
- move=> x y z Gx Gy Gz; apply: val_inj.
  apply: (mulg_injl (rH x * rH y * rH z)).
  rewrite Ring.addrC /= valG -1?mulgA // (mulgA (rH z)).
  rewrite -conjgC 3!mulgA -!rHmul ?groupM //.
  by rewrite -2!(mulgA (rH x)) -mulgA -!rHmul ?groupM //.
move: mu => mu in rHmul mu_Pmul cocycle_mu nu nu_Hmul; pose iP := #|G : P|.
have{actG0 actGM cocycle_mu} cocycle_nu : forall y z, y \in G -> z \in G ->
  (nu z + actG (nu y) z = mu y z *+ iP + nu (y * z)%g)%R.
- move=> y z Gy Gz; pose ap := (@Ring.add gTH); pose am a := actG a z.
  rewrite -/(am (nu y)) (@big_morph _ _ 0 0 _ ap)%R {}/ap {}/am; last first.
    by split=> [|x1 x2] /=; auto.
  have ->: (nu z = \sum_(Px \in rcosets P G) mu (repr Px * y)%g z)%R.
    rewrite /nu (reindex (fun Px => Px :* y)) /=; last first.
      exists (fun Px => Px :* y^-1) => Px _;
      by rewrite -rcosetM (mulgV, mulVg) mulg1.
    symmetry; apply: eq_big => Px.
       apply/rcosetsP/rcosetsP=> [] [x Gx] eq_Px.
         by exists (x * y); rewrite ?groupMl // rcosetM eq_Px.
       exists (x * y^-1); first by rewrite groupMl ?groupV.
       by rewrite rcosetM -eq_Px -rcosetM mulgV mulg1.
    case/rcosetsP=> x Gx ->{Px}; rewrite -rcosetM.
    case: repr_rcosetP=> p1 Pp1; case: repr_rcosetP=> p2 Pp2.
    by rewrite -mulgA [x * y]lock !mu_Pmul.
  rewrite -sumr_const -!big_split /=; apply: eq_bigr => Px.
  case/rcosetsP=> x Gx ->{Px}; rewrite -cocycle_mu //.
  by case: repr_rcosetP=> p1 Pp1; rewrite groupMr // (subsetP sPG).
have [m mK]: exists m, forall a : gTH, (a*+(iP * m) = a)%R.
  pose n := #|P|; have n_p: n = p_part p #|G| by apply/eqP; case/andP: sylP.
  case: (@bezoutl iP n)=> [|m' _].
     rewrite lt0n; apply/pred0Pn.
     by exists (P :* 1); apply/rcosetsP; exists (1 : gT).
  have ->: gcdn iP n = 1%N.
    case: (p_part_coprime prime_p (pos_card_group G)) => n' co_p_n'.
    rewrite -n_p -(LaGrange sPG); move/eqP.
    rewrite mulnC eqn_pmul2r ?pos_card_group //.
    rewrite -/iP n_p /p_part; move/eqP->.
    case: (logn _ _) => [|k]; first exact: gcdn1.
    by apply/eqP; rewrite gcdnC [_ == _]coprime_expl.
  case/dvdnP=> m inv_m; exists m => a.
  rewrite mulnC -inv_m /= mulnC Ring.mulrnA /=.
  suff ->: (a*+n = 0)%R by rewrite Ring.mulr0n Ring.addr0.
  apply: val_inj; rewrite /= !valE /=; apply/eqP; rewrite -orderg_dvd.
  by rewrite orderg_dvd_g // (subsetP sHP) // Hval.
move: nu => nu in nu_Hmul cocycle_nu.
pose f x := rH x * sval ((nu x)*+m)%R.
have{cocycle_nu} fM: {in G &, {morph f : x y / x * y}}.
  move=> x y Gx Gy; rewrite /f ?rHmul // -3!mulgA; congr (_ * _).
  rewrite (mulgA _ (rH y)) (conjgC _ (rH y)) -mulgA -valG ?actGE //.
  congr (_ * _); rewrite -!valM -(mK (mu x y)).
  by rewrite Ring.mulrnA -!Ring.mulrn_addl -cocycle_nu // Ring.addrC.
exists (Morphism fM @* G)%G.
  apply/subsetP=> x; case/setIP=> Hx; case/morphimP=> y _ Gy eq_x; apply/set1P.
  move: Hx; rewrite {x}eq_x /= groupMr // -{1}(mulgKV y (rH y)).
  rewrite groupMl -?mem_rcoset // => Hy.
  rewrite -(mulg1 y) /f nu_Hmul // rH_Hmul //; exact: (morph1 (Morphism fM)).
apply/setP=> x; apply/mulsgP/idP=> [[h y Hh fy ->{x}] | Gx].
  rewrite groupMl; last exact: (subsetP sHG).
  case/morphimP: fy => z _ Gz ->{x Hx y}.
  by rewrite /= /f groupMl ?GrH // (subsetP sHG) ?valP.
exists (x * (f x)^-1) (f x); last first; first by rewrite mulgKV.
  by apply/morphimP; exists x. 
rewrite -groupV invMg invgK -mulgA (conjgC (val _)) mulgA.
rewrite groupMl -(mem_rcoset, mem_conjg) // (normalP nHG) //.
exact: (svalP (nu x *+ m)%R).
Qed.

Definition hall (gT : finGroupType) (G H : {set gT}) :=
  (H \subset G) && coprime #|H| (#|G| %/ #|H|).

Lemma sylow_hall : forall (gT : finGroupType) (G P : {group gT}) p,
  prime p -> sylow p G P -> hall G P.
Proof.
move=> gT G P p prime_p; case/andP=> sPG sylP; rewrite /hall sPG /=.
case: (p_part_coprime prime_p (pos_card_group G)) => n' co_p_n' ->.
rewrite /p_part -(eqP sylP) divn_mull ?pos_card_group // (eqP sylP).
by case: (logn _ _) => [|k]; rewrite ?coprime_expl // /coprime gcdnC.
Qed.

Module AfterGaschutz.
End AfterGaschutz.

Theorem SchurZass_split : forall (gT : finGroupType) (G H : {group gT}),
  hall G H -> H <| G -> splitg G H.
Proof.
move=> gT G; move: {2}_.+1 (ltnSn #|G|) => n.
elim: n gT G => // n IHn gT G; rewrite ltnS => Gn H.
case: (leqP #|H| 1%N) => [trivH _ _ | ntrivH].
  have: trivg H.
    apply/subsetP=> x Hx; rewrite inE; apply/idPn=> nx1.
    by rewrite (cardD1 1) group1 (cardD1 x) inE /= Hx nx1 in trivH.
  move/trivgP->; apply/splitgP; exists G; [exact: subsetIl | exact: mul1g].
have:= (prime_pdiv ntrivH); set p := pdiv _ => prime_p.
case: (sylow1_cor H prime_p) => // P sylP hallH nsHG.
have [sHG nHG] := andP nsHG.
case nPG: (P <| G); last first.
  pose N := ('N_G(P))%G.
  have sNG: N \subset G by rewrite subsetIl.
  have eqHN_G: H * N = G by exact: Frattini sylP.
  pose H' := (H :&: N)%G.
  have nH'N: H' <| N.
    rewrite /(_ <| N) subsetIr; apply/subsetP=> x Nx.
    rewrite inE; apply/subsetP=> y; rewrite conjIg (conjGid Nx) (normgP _) //.
    by apply: (subsetP nHG); case/setIP: Nx.
  have eq_iH: #|G| %/ #|H| = #|N| %/ #|H'|.
    rewrite -(divn_pmul2l (pos_card_group H')) mulnC -eqHN_G card_mulG.
    by rewrite (mulnC #|H'|) divn_pmul2l // pos_card_group.
  have hallH': hall N H'.
    have sH'H: H' \subset H by exact: subsetIl.
    case/andP: hallH => _; rewrite eq_iH -(LaGrange sH'H) coprime_mull.
    by rewrite /hall subsetIr; case/andP.
  have: splitg N H'; last case/splitgP=> K trKN eqH'K.
    apply: IHn hallH' nH'N; apply: {n}leq_trans Gn.
    rewrite ltn_neqAle subset_leq_card // andbT; apply/eqP=> eqNG.
    case/andP: nPG; rewrite (subset_trans _ sHG); last by case/andP: sylP.
    suff <-: (N = G :> set _) by rewrite subsetIr.
    by apply/setP; exact/subset_cardP.
  have sKN: K \subset N by rewrite -(mul1g K) -eqH'K mulSg ?sub1set.
  apply/splitgP; exists K.
    apply/subsetP=> x; case/setIP=> Hx Kx; apply: (subsetP trKN).
    by rewrite 2!inE Hx (subsetP sKN) Kx.
  apply/eqP; rewrite eqset_sub -eqHN_G mulgS // -eqH'K mulgA mulSg //.
  by rewrite -{2}(mulGid H) mulgS // subsetIl.
pose Z := ('Z(P))%G; have iZ: 'Z(P) = Z by [].
have sZP: Z \subset P by exact: subset_center.
have sZH: Z \subset H by case/andP: sylP; move/(subset_trans sZP).
have sZG: Z \subset G by exact: subset_trans sHG.
have nZG: Z <| G by apply: char_norm_trans nPG; exact: characteristic_center.
have nZH: Z <| H by exact: normalsubS nZG.
pose Gbar := (G / Z)%G; have iGbar: G / Z = Gbar by [].
pose Hbar := (H / Z)%G; have iHbar: H / Z = Hbar by [].
have nHGbar: Hbar <| Gbar by exact: morphim_normalsub.
have hallHbar: hall Gbar Hbar.
  rewrite /hall morphimS //=.
  rewrite !card_quotient; try by [case/andP: nZG | case/andP: nZH].
  rewrite -(divn_pmul2l (pos_card_group Z)) !LaGrange //.
  by case/andP: hallH => _; rewrite -{1}(LaGrange sZH) coprime_mull; case/andP.
have: splitg Gbar Hbar; last case/splitgP=> Kbar trHKbar eqHKbar. 
  apply: IHn => //; apply: {n}leq_trans Gn.
  rewrite card_quotient; last by case/andP: nZG.
  rewrite -(group_divn sZG) divn_lt ?pos_card_group //.
  apply: (leq_trans (prime_gt1 prime_p)).
  apply: dvdn_leq; first exact: pos_card_group.
  pose to := Action (@conjg1 gT) (@conjgM _).
  have eqZ: Z =i predI (act_fix to P) (mem P).
    move=> z; rewrite /= inE /= !inE /= -(andbC (z \in P)).
    case: (z \in P) => //=.
    apply/centgP/eqP=> [Cz | <- x].
      apply/setP=> x; rewrite inE; case Px: (x \in P) => //=.
      rewrite (sameP eqP conjg_fixP); apply/commgP; exact: Cz.
    by rewrite inE; case/andP=> _; rewrite (sameP eqP conjg_fixP); move/commgP.
  case/andP: sylP => _; move/eqP=> cPp.
  rewrite {eqZ}(eq_card eqZ) /dvdn -(mpl prime_p cPp) => [|x y].
    rewrite cPp; apply/dvdn_exp_prime=> //; exists 1%N; last by rewrite expn1.
    by rewrite -dvdn_exp_max // expn1 dvdn_pdiv.
  by case/imsetP=> z Pz ->; rewrite /= groupJr.
have [ZK [sZZK sZKG] quoZK]:
  exists2 ZK : group gT, Z \subset ZK /\ ZK \subset G & ZK / Z = Kbar.
- exists [group of G :&: coset_of Z @*^-1 Kbar]; rewrite /=.
    rewrite subsetIl subsetI sZG -sub_morphim_pre ?normG //.
    by rewrite -quotientE trivial_quotient sub1G.
  have sKG: Kbar \subset Gbar by rewrite -eqHKbar mulG_subr.
  rewrite [_ / _]morphimGI ?ker_coset // morphpreK -quotientE.
    exact/setIidPr.
  by rewrite (subset_trans sKG) // morphimS //; case/andP: nZG.
have nZZK: Z <| ZK by exact: normalsubS nZG.
have cardZK: #|ZK| = (#|Z| * #|G : H|)%N.
  rewrite -(LaGrange sZZK); congr (_ * _)%N.
  rewrite -card_quotient ?quoZK; last by case/andP: nZZK.
  rewrite -(group_divn sHG) -(LaGrange sZG) -(LaGrange sZH) divn_pmul2l //.
  rewrite -!card_quotient; try by [case/andP: nZG | case/andP: nZH].
  by rewrite iGbar -eqHKbar (card_mulG_trivP _ _ trHKbar) divn_mulr.
have sylZ: sylow p ZK Z.
  rewrite /sylow sZZK andTb eq_sym cardZK mulnC logn_gauss //.
    have:= group_dvdn sZP; case/andP: sylP => _; move/eqP->.
    by case/dvdn_exp_prime=> // i _ ->; rewrite logn_exp.
  case/andP: hallH => _; rewrite group_divn //.
  have: p %| #|H| by exact: dvdn_pdiv.
  by case/dvdnP=> m ->; rewrite coprime_mull; case/andP.
have: splitg ZK Z; last case/splitgP=> K trZK eqZK.
  rewrite (Gaschutz_split _ nZZK sylZ) ?subset_refl //.
    apply/splitgP.
    exists (1%G : group gT); [exact: subsetIr | exact: mulg1].
  apply: (subin1 (subsetP sZP)); apply: central_sym; apply/centralP.
  exact: subsetIr.
have sKZK: K \subset ZK by rewrite -(mul1g K) -eqZK mulSg ?sub1set.
have trHK: trivg (H :&: K).
  apply/subsetP=> x; case/setIP=> Hx Kx; apply: (subsetP trZK).
  have Nx: x \in 'N(Z) by apply: subsetP (x) Hx; case/andP: nZH.
  rewrite inE Kx andbT coset_of_idr //; apply/set1P.
  rewrite (subsetP trHKbar) // -quoZK inE !mem_imset // inE Nx //.
  exact: (subsetP sKZK).
apply/splitgP; exists K => //; apply/setP; apply/subset_cardP.
  rewrite (card_mulG_trivP H K _) // -(@divn_mulr #|K| #|Z|) //.
  by rewrite -(card_mulG_trivP Z K _) // eqZK cardZK divn_mulr // LaGrange.
by rewrite -(mulGid G) mulgSS // (subset_trans sKZK).
Qed.

Module SchurZassCP1. End SchurZassCP1.

Definition solvable (gT : finGroupType) (G : {set gT}) :=
  forallb H : {group gT}, (H \subset G :&: [~: H, H]) ==> trivg H.

Prenex Implicits solvable.

Section Solvable.

Variable gT : finGroupType.

Lemma solvable_sub : forall G H : {group gT},
  H \subset G -> solvable G -> solvable H.
Proof.
move=> G H sHG solG.
apply/forallP=> K; rewrite subsetI; apply/implyP; case/andP=> sKH sKK'.
by have:= forallP solG K; rewrite subsetI sKK' (subset_trans sKH).
Qed.

Lemma solvable_morphim : forall (rT : finGroupType) (G H : {group gT})
                              (f : {morphism G >-> rT}),
  solvable H -> solvable (f @* H).
Proof.
move=> rT G H f solH; have{solH} [G' [f' ->{f G H}]]:
  exists G' : {group gT}, exists2 f' : {morphism G' >-> rT},
  f @* H = f' @* G' & solvable G'.
- pose G' := (G :&: H)%G; have sG'G: G' \subset G by exact: subsetIl.
  exists G'; exists [morphism of restrm sG'G f] => /=.
    by rewrite /= morphim_restrm setIid morphimIdom.
  apply: solvable_sub solH; exact: subsetIr.
move: G' f' => G f solG.
apply/forallP=> Hb; apply/implyP; rewrite subsetI; case/andP=> sHbG sHbHb'.
have{sHbG} [H]: exists2 H : {group gT}, H \subset G & f @* H = Hb.
  by exists (f @*^-1 Hb)%G; rewrite (subsetIl, morphpreK).
elim: {H}_.+1 {-2}H (ltnSn #|H|) => // n IHn H.
rewrite ltnS => leHn sHG defHb.
case eqH'H: ([~: H, H] == H).
  have:= forallP solG H; rewrite subsetI sHG (eqP eqH'H) subset_refl -defHb. 
  by move/trivGP->; rewrite morphim1.
have sH'H: [~: H, H] \subset H by by rewrite subcomm_normal normG.
apply: IHn (subset_trans sH'H sHG) _.
  rewrite eqset_sub_card sH'H /= in eqH'H.
  by apply: leq_trans leHn; rewrite ltnNge eqH'H.
apply/eqP; rewrite morphimR // defHb.
by rewrite eqset_sub sHbHb' subcomm_normal normG.
Qed.

Lemma solvable_quo : forall G H : {group gT}, solvable G -> solvable (G / H).
Proof. move=> G H; exact: solvable_morphim. Qed.

Definition elementary_abelian (A : {set gT}) :=
  abelian A /\ {in A, forall x, #[x] %| pdiv #|A|}.

Definition Ohm i (A : {set gT}) :=
  <<[set x \in A | #[x] == pdiv #|A| ^ i]%N>>.

Definition Mho i (A : {set gT}) := <<expgn^~ (pdiv #|A| ^ i)%N @: A>>.

Notation "''Ohm_' i ( G )" := (Ohm i G)
  (at level 8, i at level 2, format "''Ohm_' i ( G )") : group_scope.

Notation "''Mho^' i ( G )" := (Ohm i G)
  (at level 8, i at level 2, format "''Mho^' i ( G )") : group_scope.

Canonical Structure Ohm_group i G := Eval hnf in [group of 'Ohm_i(G)].

Canonical Structure Mho_group i G := Eval hnf in [group of 'Mho^i(G)].

Notation "''Ohm_' i ( G )" := (Ohm_group i G) : subgroup_scope.

Notation "''Mho^' i ( G )" := (Mho_group i G) : subgroup_scope.

Lemma char_Ohm : forall i (G : {group gT}), 'Ohm_i(G) \char G.
Proof.
move=> i G; have sOmG: 'Ohm_i(G) \subset G.
  by rewrite gen_subG; apply/subsetP=> x; rewrite inE; case/andP.
apply/charP; split=> // f injf fG; apply/morphim_fixP => //.
rewrite sub_morphim_pre // gen_subG; apply/subsetP=> x; rewrite inE.
case/andP=> Gx oxp; rewrite !inE Gx mem_geng // inE eq_sym -{2}fG.
rewrite mem_imset ?setIid //= -{oxp}(eqP oxp); apply/eqP.
have sxG: cyclic x \subset G by rewrite cyclic_h.
apply: isom_card [morphism of restrm sxG f] _ => /=.
by apply/isomP; rewrite injm_restrm //= morphim_restrm setIid morphim_cyclic.
Qed.

Lemma elementary_eq_Ohm1 : forall G : {group gT},
  abelian G -> (elementary_abelian G <-> 'Ohm_1(G) = G).
Proof.
move=> G abelG; pose p := pdiv #|G|; pose G1 := [set x \in G | #[x] %| p].
have gG1: group_set G1.
  apply/group_setP; split=> [|x y]; rewrite !inE ?(orderg1, dvd1n, group1) //.
  rewrite !orderg_dvd.
  case/andP=> Gx; move/eqP=> xp; case/andP=> Gy; move/eqP=> yp.
  rewrite groupM // expMgn ?(xp, yp, mulg1) //=; exact: abelG.
have ->: 'Ohm_1(G) = G1.
  apply/eqP; rewrite eqset_sub -{1}[G1](genGid (Group gG1)) genSg.
    apply/subsetP=> x; rewrite /= !inE; case/andP=> Gx.
      case: (x =P 1) => [->|]; [by rewrite group1 | move/eqP=> nx1].
      have: prime p.
        by rewrite prime_pdiv // (cardD1 1) (cardD1 x) group1 inE /= Gx nx1.
      case/primeP=> _ prp; move/prp; case/predU1P=> [x1 | xp].
        by case/eqP: nx1; rewrite -[x]expg1 -x1 orderg_expn1.
      by rewrite mem_geng // inE /= Gx expn1.
    apply/subsetP=> x; rewrite !inE; case/andP=> ->; move/eqP->.
    by rewrite expn1 dvdnn.
split=> [[_ elemG] | OmG].
  apply/setP=> x; rewrite inE; case Gx: (x \in G) => //; exact: elemG.
by split=> // x; rewrite -{1}OmG inE; case/andP.
Qed.

Lemma solvable_norm_abel : forall L G : {group gT},
  solvable G -> G <| L -> ~~ trivg G ->
  exists H : {group gT}, [/\ H \subset G, H <| L, ~~ trivg H
                           & elementary_abelian H].
Proof.
move=> L G solG; set H := {1 2}G; have: H \subset G := subset_refl _.
elim: {H}_.+1 {-2}H (ltnSn #|H|) => // n IHn H; rewrite ltnS => leHn.
move=> sHG nHL ntH; case abelH: (trivg [~: H, H]).
  pose H1 := 'Ohm_1(H)%G; have charH1: H1 \char H by exact: char_Ohm.
  have sH1H: H1 \subset H by case/andP: charH1.
  have abelH1: abelian H1.
    move=> x H1x /= y H1y; apply: (commG1P abelH); exact: (subsetP sH1H).
  pose p := pdiv #|H|.
  have prp: prime p by rewrite prime_pdiv // ltnNge -trivg_card.
  have ntH1 : ~~ trivg H1.
    case: (cauchy prp (dvdn_pdiv #|H|)) => x; case/andP=> Hx; move/eqP=> oxp.
    rewrite /trivg gen_subG expn1; apply/subsetPn; exists x.
      by rewrite inE Hx oxp eqxx.
    by apply/set1P=> x1; rewrite -oxp x1 [#[_]]orderg1 in prp.
  exists H1; split=> //; first exact: subset_trans sHG.
    exact: char_norm_trans nHL.
  apply/elementary_eq_Ohm1=> //; apply/eqP.
  rewrite eqset_sub; case/andP: (char_Ohm 1 H1) => -> _.
  rewrite gen_subG; apply/subsetP=> x Hx; have H1x: x \in H1 := mem_geng Hx.
  rewrite mem_geng // !inE H1x; rewrite inE in Hx; case/andP: Hx => Hx oxp.
  rewrite ((pdiv _ =P p) _) // eqn_leq !pdiv_min_dvd ?prime_gt1 //.
  - by rewrite prime_pdiv // ltnNge -trivg_card.
  - apply: dvdn_trans (dvdn_pdiv _) _; exact: group_dvdn.
  by apply: dvdn_trans (orderg_dvd_g H1x); rewrite (eqP oxp) expnS dvdn_mulr.
have chH': [~: H, H] \char H by apply: charR; apply: char_refl.
have [sH'H _] := andP chH'; move/idPn: abelH.
apply: IHn; last 1 [exact: subset_trans sHG | exact: char_norm_trans nHL].
apply: leq_trans leHn; rewrite ltnNge -[_ <= _]andTb -sH'H -eqset_sub_card.
apply/eqP=> eqH'H; have:= forallP solG H.
by rewrite eqH'H subsetI sHG subset_refl -implybN ntH.
Qed.

End Solvable.

Theorem SchurZass_trans_sol : forall (gT : finGroupType) (H K K1 : {group gT}),
    solvable H -> K \subset 'N(H) -> K1 \subset H * K ->
    coprime #|H| #|K| -> #|K1| = #|K| ->
  exists2 x, x \in H & K1 = (K :^ x)%G.
Proof.
move=> gT H; move: {2}_.+1 (ltnSn #|H|) => n; elim: n => // n IHn in gT H *.
rewrite ltnS => leHn K K1 solH nHK; case trH: (trivg H).
  rewrite (trivgP _ trH) mul1g => sK1K _ eqK1K.
  exists (1 : gT); first exact: set11.
  by apply/eqP; rewrite -val_eqE /= conjsg1 eqset_sub_card sK1K eqK1K /=.
pose G := (H <*> K)%G.
have defG: G = H * K :> set gT by rewrite -normC // -norm_mulgenE // mulgenC.
have sHG: H \subset G by rewrite -gen_subG genSg // subsetUl.
have sKG: K \subset G by rewrite -gen_subG genSg // subsetUr.
have nHG: H <| G by rewrite /(H <| G) sHG gen_subG subUset nHK normG.
move/idPn: trH; case/(solvable_norm_abel solH nHG)=> M [sMH nMG ntM [abelM _]].
rewrite -defG => sK1G coHK oK1K.
have nMsG: forall L : {set gT}, L \subset G -> L \subset 'N(M).
  by move=> L; move/subset_trans; apply; case/andP: nMG.
have [coKM coHMK]: coprime #|M| #|K| /\ coprime #|H / M| #|K|.
  by apply/andP; rewrite -coprime_mull card_quotient ?nMsG ?LaGrange.
have oKM: forall K' : {group gT},
  K' \subset G -> #|K'| = #|K| -> #|K' / M| = #|K|.
- move=> K' sK'G oK'.
  rewrite -quotient_mulg -?norm_mulgenE ?card_quotient ?nMsG //; last first.
    by rewrite gen_subG subUset sK'G; case/andP: nMG.
  rewrite -group_divn /=; last by rewrite -gen_subG genSg ?subsetUr.
  rewrite norm_mulgenE ?nMsG // coprime_card_mulG ?divn_mull //.
  by rewrite oK' coprime_sym.
have [xb]: exists2 xb, xb \in H / M & (K1 / M = (K / M) :^ xb)%G.
  apply: IHn; try by rewrite (solvable_quo, morphim_normal, oKM K) ?(oKM K1).
    apply: leq_trans leHn; rewrite card_quotient ?nMsG //.
    rewrite -(ltn_pmul2l (pos_card_group M)) LaGrange // -{1}(mul1n #|H|).
    by rewrite ltnNge leq_pmul2r // -trivg_card.
  by rewrite -morphimMl ?nMsG // -defG morphimS.
case/morphimP=> x nMx Hx ->{xb}; move/(congr1 val)=> /= eqK1Kx.
pose K2 := (K :^ x)%G.
have{eqK1Kx} eqK12: K1 / M = K2 / M by rewrite [K2 / M]morphimJ.
suff [y My ->]: exists2 y, y \in M & K1 = (K2 :^ y)%G.
  exists (x * y); first by rewrite groupMl // (subsetP sMH).
  by apply: val_inj; rewrite /= conjsgM.
pose toM y : {z | z \in M} := insubd (Sub 1 (group1 M)) y.
have valM: {in M, cancel toM val} by move=> *; exact: insubdK.
pose Mgrp := [is {y | y \in M} <: finGroupType].
have mulMC : commutative (@mulg Mgrp).
  by case=> y My [z Mz]; apply: val_inj; rewrite /= abelM.
pose rT := Ring.AdditiveGroup (@mulgA _) mulMC (@mul1g _) (@mulVg _).
have Mval: forall u : rT, sval u \in M by exact: valP.
have rM: forall a b : rT, sval (a + b)%R = sval a * sval b by [].
have rX: forall (a : rT) m, sval (a *+ m)%R = sval a ^+ m.
  by move=> a; elim=> // m IHm; congr (_ * _).
have rV: forall (a : rT), sval (- a)%R = (sval a)^-1 by [].
pose actG (y : rT) z : rT := toM (sval y ^ z).
have valG: forall a y, y \in K1 -> sval (actG a y) = sval a ^ y.
  move=> a y Ky; rewrite valM // -mem_conjgV (normgP _) ?Mval //=.
  by rewrite groupV (subsetP (nMsG _ sK1G)).
have actG0: forall y, y \in K1 -> (actG 0 y = 0)%R.
  by move=> y Ky; apply: val_inj; rewrite /= valG //= conj1g.
have actGM: forall a b y, y \in K1 -> (actG (a + b) y = actG a y + actG b y)%R.
  by move=> a b y Ky; apply: val_inj; rewrite /= !valG //= conjMg.
have actGX: forall a m y, y \in K1 -> (actG (a *+ m) y = actG a y *+ m)%R.
  by move=> a m y Ky; apply: val_inj; rewrite /= !(rX, valG) // conjXg.
have sK2G: K2 \subset G by rewrite -(conjGid (subsetP sHG _ Hx)) conjSg.
pose L := (M <*> K2)%G.
have defL: M * K2 = L by rewrite -normC -?norm_mulgenE 1?mulgenC ?nMsG.
have cKL: K2 \in complg L M.
  by apply/complgP; rewrite coprime_trivg ?card_conjg.
have nML: M <| L.
  apply: normalsubS nMG; first by rewrite -gen_subG genSg // subsetUl.
  by rewrite gen_subG subUset (subset_trans sMH).
have sK1L: K1 \subset L.
  apply/subsetP=> y Ky; rewrite -defL.
  have Ny: y \in 'N(M) by exact: subsetP (nMsG K1 _) _ _.
  have: coset_of M y \in K2 / M by rewrite -eqK12 mem_imset // inE Ny.
  case/morphimP=> z Nz Kz /=; move/(congr1 val)=> /=.
  rewrite !coset_ofN // => eqMyz.
  rewrite -sub1set in Kz; apply: (subsetP (mulgS _ Kz)).
  by rewrite -eqMyz rcoset_refl.
pose mu y : rT := toM (divgr K2 M y).
have val_mu: forall y, y \in K1 -> sval (mu y) = divgr K2 M y.
  move=> y; move/(subsetP sK1L); rewrite -defL => Ly.
  by rewrite valM // mem_divgr.
have mu_cocycle:
  {in K1 &, forall y z, mu (y * z) = (actG (mu z) y^-1 + mu y)%R}.
- move=> y z Ky Kz; apply: val_inj => /=.
  rewrite valG ?(val_mu, groupM, groupV) //.
  rewrite /divgr (remGrM cKL) ?(subsetP sK1L) //.
  by rewrite mulgA -conjgCV -!mulgA -invMg.
have [m mK]: exists m, forall a : rT, (a *+ (#|K| * m) = a)%R.
  case: (bezoutl #|M| (pos_card_group K)) => m' _.
  rewrite gcdnC (eqnP coKM); case/dvdnP=> m def_m; exists m => a.
  apply: val_inj; rewrite mulnC -def_m /= rX (_ : _ ^+ _ = 1) ?mulg1 //.
  by apply/eqP; rewrite -orderg_dvd dvdn_mull // orderg_dvd_g.
exists (sval ((\sum_(y \in K1) mu y) *+ m)%R)^-1; first by rewrite groupV.
apply/eqP; rewrite -val_eqE eqset_sub_card !card_conjg oK1K leqnn andbT.
apply/subsetP=> /= y Ky; rewrite mem_conjgV conjgE (conjgCV y) mulgA.
have K': y^-1 \in K1 by rewrite groupV.
rewrite -valG ?groupV // -rV -rM (_ : _ + _ = - mu y)%R.
  by rewrite /= val_mu // invMg mulgKV invgK mem_remgr // defL (subsetP sK1L).
rewrite Ring.oppr_muln actGX // -Ring.mulrn_addl -sum_opp.
rewrite (@big_morph _ _ 0 0 _ (@Ring.add rT) (actG^~ y^-1))%R; last first.
  split=> [|a b]; [exact: actG0 | exact: actGM].
rewrite (reindex (mulg y)) /=; last first.
  by exists (mulg y^-1) => z _; rewrite (mulKVg, mulKg).
rewrite (eq_bigl (mem K1)) => [|z]; last by rewrite groupMl.
rewrite -big_split /= (eq_bigr (fun _ => - mu y)%R) ?sumr_const => [|z Kz].
  by rewrite -Ring.mulrnA oK1K mK.
by rewrite mu_cocycle // Ring.oppr_add -Ring.addrA -Ring.addrC Ring.addrK.
Qed.

