Require Import ssreflect ssrbool ssrfun eqtype ssrnat.
Require Import div seq fintype paths connect finfun ssralg bigops finset.
Require Import groups normal action group_perm automorphism cyclic center sylow.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Import GroupScope.

Lemma Frattini : forall (gT : finGroupType) (G H P : {group gT}) p,
  H <| G -> prime p -> sylow p H P -> H * N_(G)(P) = G.
Proof.
move=> gT G H P p; case/normalsubP=> sHG nHG p_prime sylP.
have sPG: P \subset G by apply: subset_trans sHG; case/andP: sylP.
apply/eqP; rewrite eqset_sub setIC group_modl // subsetIr.
apply/subsetP=> x Gx; pose Q := (P :^ x^-1)%G.
have sylQ: sylow p H Q by rewrite (sylow_sconjg _ _ _ x) conjsgKV nHG.
have [y [Hy QPy]] := (sylow2_cor p_prime sylP sylQ).
rewrite inE Gx andbT -(mulKg y x) mem_mulg ?groupV //.
by apply/normgP; rewrite conjsgM -QPy conjsgKV.
Qed.

Section Split.

Variable gT : finGroupType.

Section Defs.

Variables G H : set gT.

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
rewrite -(trivgP _ trHK) inE -mem_rcoset groupMr ?groupV // -in_setI.
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
  by rewrite group_modl // eqHK; apply/eqP; rewrite eqsetIr.
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
  apply: remGrM; [exact/complgP | exact: normalsubS sPG].
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
pose Hgrp := {{x | x \in H} as finGroupType}.
have mulHC : commutative (@mulg Hgrp).
  by case=> x Hx [y Hy]; apply: val_inj; rewrite /= abelH.
pose gTH := Ring.AdditiveGroup (@mulgA _) mulHC (@mul1g _) (@mulVg _).
have Hval: forall u : gTH, val u \in H by exact: valP.
have valM: forall a b : gTH, val (a + b)%R = val a * val b by [].
have valE: forall (a : gTH) n, val (a*+n)%R = val a ^+ n.
  by move=> a; elim=> // n IHn; congr (_ * _).
pose mu x y : gTH := toH ((rH x * rH y)^-1 * rH (x * y)).
pose nu y := (\sum_(Px \in rcosets P G) mu (repr Px) y)%R.
have rHmul : forall x y,
  x \in G -> y \in G -> rH (x * y) = rH x * rH y * val (mu x y).
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
pose actG (a : gTH) y : gTH := toH (val a ^ rH y).
have valG: forall a y, y \in G -> val (actG a y) = val a ^ rH y.
  move=> a y Gy; rewrite valH // -mem_conjgV (normgP _) ?Hval //=.
  by rewrite groupV (subsetP nHG) // GrH.
have actG0: forall y, y \in G -> (actG 0 y = 0)%R.
  by move=> y Gy; apply: val_inj; rewrite valG //= conj1g.
have actGM: forall a b y, y \in G -> (actG (a + b) y = actG a y + actG b y)%R.
  by move=> a b y Gy; apply: val_inj; rewrite /= !valG //= conjMg.
have actGE: forall a n y, y \in G -> (actG (a*+n) y = (actG a y)*+n)%R.
  by move=> a n y Gy; apply: val_inj; rewrite !(valE, valG) // conjXg.
have cocycle_mu: forall x y z, x \in G -> y \in G -> z \in G ->
  (mu (x * y)%g z + actG (mu x y) z = mu y z + mu x (y * z)%g)%R.
- move=> x y z Gx Gy Gz; apply: val_inj.
  apply: (mulg_injl (rH x * rH y * rH z)).
  rewrite Ring.addrC !valM valG // -mulgA (mulgA (rH z)).
  rewrite -conjgC 3!mulgA -!rHmul ?groupM //.
  by rewrite -2!(mulgA (rH x)) -mulgA -!rHmul ?groupM //.
move: mu => mu in rHmul mu_Pmul cocycle_mu nu nu_Hmul; pose iP := indexg P G.
have{actG0 actGM cocycle_mu} cocycle_nu : forall y z, y \in G -> z \in G ->
  (nu z + actG (nu y) z = (mu y z)*+iP + nu (y * z)%g)%R.
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
  apply: val_inj; rewrite !valE /=; apply/eqP; rewrite -orderg_dvd.
  by rewrite orderg_dvd_g // (subsetP sHP) // Hval.
move: nu => nu in nu_Hmul cocycle_nu.
pose f x := if x \in G then rH x * val ((nu x)*+m)%R else 1.
have{nu_Hmul} kerf: H \subset ker f.
  apply/subsetP=> h *; apply/kerP=> y.
  by rewrite /f rH_Hmul // groupMl (nu_Hmul, subsetP sHG).
have{cocycle_nu} morf: forall y z, y \in G -> z \in G -> f (y * z) = f y * f z.
  move=> y z Gy Gz; rewrite /f Gy Gz groupM ?rHmul // -3!mulgA; congr (_ * _).
  rewrite (mulgA _ (rH z)) (conjgC _ (rH z)) -mulgA -valG ?actGE //.
  congr (_ * _); rewrite -!valM -(mK (mu y z)).
  by rewrite Ring.mulrnA -!Ring.mulrn_addl -cocycle_nu // Ring.addrC.
have [phi phi_f]: exists phi : morphism _ _, f =1 phi.
  case triv_f: (trivm f).
    by exists (triv_morph gT gT); exact: trivm_is_cst.
  have domf: dom f = G.
    apply/setP=> x; rewrite 2!inE {2}/f orbC.
    case Gx: (x \in G).
      case: eqP => // eq_rHx; apply: (subsetP kerf).
      rewrite -groupV -(mulg1 x^-1) -eq_rHx mulgA groupMr ?Hval //.
      by rewrite -mem_lcoset -norm_rlcoset ?(subsetP nHG).
    rewrite eqxx; apply/kerP=> in_ker.
    case/existsP: triv_f=> y; case/eqP.
    case Gy: (y \in G); last by rewrite /f Gy.
    by rewrite -in_ker /f groupMr // Gx.
  have gdomf: group_set (dom f) by rewrite domf groupP.
  by rewrite -domf in morf; exists (Morphism gdomf morf).
exists {phi @: G as group _}.
  apply/subsetP=> x; case/setIP=> Hx; case/imsetP=> y Gy eq_x; apply/set1P.
  move: Hx; rewrite {x}eq_x -phi_f {1}/f Gy groupMr ?Hval //.
  rewrite -{1}(mulgKV y (rH y)) groupMl -?mem_rcoset // -{2}(mulg1 y).
  by move/(subsetP kerf); move/kerP->; rewrite phi_f morph1.
apply/setP=> x; apply/mulsgP/idP=> [[h y Hh phi_y ->{x}] | Gx].
  rewrite groupMl; last exact: (subsetP sHG).
  case/imsetP: phi_y => z Gz ->{x Hx y}.
  by rewrite -phi_f /f Gz groupMl ?GrH // (subsetP sHG) ?valP.
exists (x * (phi x)^-1) (phi x); last first; first by rewrite mulgKV.
  by apply/imsetP; exists x. 
rewrite -phi_f /f Gx -groupV invMg invgK -mulgA (conjgC (val _)) mulgA.
rewrite groupMl -(mem_conjg, mem_rcoset) //.
by rewrite (normgP _) ?(valP (nu x *+ m)%R, subsetP nHG).
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
  pose N := (N_(G)(P))%G.
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
have nZH: Z <| H by exact: normalsubS sHG.
pose Gbar := (G / Z)%G; have iGbar: G / Z = Gbar by [].
pose Hbar := (H / Z)%G; have iHbar: H / Z = Hbar by [].
have nHGbar: Hbar <| Gbar.
  rewrite /(_ <| _) imsetS //=.
  apply/normalP=> xbar; case/imsetP=> x Gx ->{xbar}.
  have sGdom: G \subset dom (coset_of Z).
    by apply: subset_trans (subset_dom_coset _); case/andP: nZG.
  by rewrite -imset_conj (normalP nHG, subset_trans sHG, subsetP sGdom).
have hallHbar: hall Gbar Hbar.
  rewrite /hall imsetS //= iZ.
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
    by rewrite -dvdn_exp_max //= expn1 dvdn_pdiv.
  by case/imsetP=> z Pz ->; rewrite /= groupJr.
have [ZK [sZZK sZKG] quoZK]:
  exists2 ZK : group gT, Z \subset ZK /\ ZK \subset G & ZK / Z = Kbar.
- exists [group of mpreim (coset_of Z) Kbar :&: G]; rewrite /= mpreimUker //.
    split; last exact: subsetIr.
    apply/subsetP=> x Zz; rewrite 2!inE (subsetP sZG) // andbT.
    apply/orP; right; exact: (subsetP (subset_ker_coset _)).    
  apply/setP=> xbar; apply/imsetP/idP=> [[x ZKx ->{xbar}] | Kxbar].
    case/setIP: ZKx; case/setUP; first by rewrite !inE; case/andP.
    move/mker=> -> _; exact: group1.
  have: xbar \in Gbar by rewrite -eqHKbar (subsetP (mulG_subr _ _)).
  case/quotientP=> x [Gx Nx eq_xbar]; exists x => //=.
  rewrite 4!inE -eq_xbar Gx Kxbar !andbT; case: eqP => //= kx.
  by apply/kerMP; rewrite ?(subsetP (subset_dom_coset _)) //= -eq_xbar.
have nZZK: Z <| ZK by exact: normalsubS sZKG.
have cardZK: #|ZK| = (#|Z| * indexg H G)%N.
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
  have Gx: x \in G by exact: (subsetP sHG).
  suff: x \in ker_(G) (coset_of Z).
    rewrite ker_coset_of_loc //; last by case/andP: nZG.
    by rewrite !inE Kx Gx.
  rewrite inE Gx andbT; apply/kerMP.
    rewrite (subsetP (subset_dom_coset Z)) //.
    by case/andP: nZG => _; move/subsetP; exact.
  apply/set1P; apply: (subsetP trHKbar); rewrite -quoZK.
  by apply/setIP; split; apply/imsetP; exists x; rewrite // (subsetP sKZK).
apply/splitgP; exists K => //; apply/setP; apply/subset_cardP.
  rewrite (card_mulG_trivP H K _) // -(@divn_mulr #|K| #|Z|) //.
  by rewrite -(card_mulG_trivP Z K _) // eqZK cardZK divn_mulr // LaGrange.
by rewrite -(mulGid G) mulgSS // (subset_trans sKZK).
Qed.


