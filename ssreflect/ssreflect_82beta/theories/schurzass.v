Require Import ssreflect ssrbool ssrfun eqtype ssrnat div prime.
Require Import fintype ssralg bigops finset.
Require Import groups morphisms automorphism normal action gprod.
Require Import commutators cyclic center pgroups sylow nilpotent maximal.

(* Require Import seq paths connect finfun group_perm. *)

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Import GroupScope.

Theorem Gaschutz : forall (gT : finGroupType) (G H P : {group gT}),
  H <| G -> H \subset P -> P \subset G -> abelian H -> coprime #|H| #|G : P| ->
    [splits G, over H] = [splits P, over H]
 /\ {in [complements to H in G] &, forall K L : {group gT},
     K :&: P = L :&: P -> exists2 x, x \in H & L :=: K :^ x}.
Proof.
move=> gT G H P nsHG sHP sPG abelH coHiPG.
have [sHG nHG] := andP nsHG.
(* set up H as a ZG-module *)
have mulHC : @commutative (subg_of H) mulg.
  by case=> x Hx [y Hy]; apply: val_inj; rewrite /= (centsP abelH).
pose rT := Ring.AdditiveGroup (@mulgA _) mulHC (@mul1g _) (@mulVg _).
have valM: forall a b : rT, sgval (a + b)%R = sgval a * sgval b by [].
have valV: forall a : rT, sgval (- a)%R = (sgval a)^-1 by [].
have valX: forall (a : rT) n, sgval (a *+ n)%R = sgval a ^+ n.
  by move=> a; elim=> // n IHn; congr (_ * _).
pose to (a : rT) y : rT := subg H (sgval a ^ y).
have valA: forall a y, y \in G -> sgval (to a y) = sgval a ^ y.
  by move=> a y Gy; rewrite subgK // memJ_norm ?subgP ?(subsetP nHG).
have to0: forall y, y \in G -> (to 0 y = 0)%R.
  by move=> y Gy; apply: val_inj; rewrite /= valA //= conj1g.
have toM: forall y, y \in G -> {morph to^~ y : a b / a + b}%R.
  by move=> a b y Gy; apply: val_inj; rewrite /= !valA //= conjMg.
have toX: forall a n y, y \in G -> (to (a *+ n) y = to a y *+ n)%R.
  by move=> a n y Gy; apply: val_inj; rewrite /= !(valX, valA) // conjXg.
pose toB y Gy : Monoid.morphism _ _ _ _ (to^~ y) := conj (to0 y Gy) (toM y Gy).
(* Action on right cosets *)
have act_Cayley: forall K L : {group gT}, [acts (L | 'Msr) on rcosets K L].
  move=> K L; apply/subsetP=> x Lx; rewrite inE; apply/subsetP=> X.
  case/rcosetsP=> y Ly ->{X}; rewrite inE /= rcosetE -rcosetM -rcosetE.
  by rewrite mem_imset ?groupM.
(* Get m == 1 / #|G : P| [mod #|H|] *)
have [m mK]: exists m, forall a : rT, (a *+ (#|G : P| * m) = a)%R.
  case: (bezoutl #|H| (ltn_0indexg G P))=> m' _; rewrite gcdnC (eqnP coHiPG).
  case/dvdnP=> m inv_m; exists m => a.
  rewrite mulnC -inv_m /= mulnC Ring.mulrnA /=.
  suff ->: (a *+ #|H| = 0)%R by rewrite Ring.mulr0n Ring.addr0.
  apply: val_inj; rewrite /= !valX /=; apply/eqP; rewrite -order_dvd.
  by rewrite order_dvd_g ?subgP.
split=> [|K L].
  apply/splitsP/splitsP=> [[K] | [Q]].
    case/complP=> trHK eqHK; exists (K :&: P)%G.
    rewrite inE setICA (setIidPl sHP) setIC trHK eqxx group_modl // eqHK.
    by rewrite (sameP eqP setIidPr).
  case/complP=> trHQ eqHQ.
  have sQP: Q \subset P by rewrite -eqHQ mulG_subr.
  pose rP x := repr (P :* x); pose pP x := x * (rP x)^-1.
  have PpP: pP _ \in P.
    by move=> x; rewrite -mem_rcoset rcoset_repr rcoset_refl.
  have rPmul : forall x y, x \in P -> rP (x * y) = rP y.
    by move=> x y Px; rewrite /rP rcosetM rcoset_id.
  pose pQ x := remgr H Q x; pose rH x := pQ (pP x) * rP x.
  have pQhq: {in H & Q, forall h q, pQ (h * q) = q} by exact: remgrMid.
  have pQmul: {in P &, {morph pQ : x y / x * y}}.
    apply: remgrM; [exact/complP | exact: normalS nsHG].
  have HrH: forall x, rH x \in H :* x.
    move=> x; rewrite rcoset_sym mem_rcoset invMg mulgA mem_divgr //.
    by rewrite eqHQ PpP.
  have GrH: forall x, x \in G -> rH x \in G.
    move=> x Gx; case/rcosetP: (HrH x) => y Hy ->.
    by rewrite groupM // (subsetP sHG).
  have rH_Pmul: forall x y, x \in P -> rH (x * y) = pQ x * rH y.
    by move=> *; rewrite /rH mulgA -pQmul; first by rewrite /pP rPmul ?mulgA.
  have rH_Hmul: forall h y, h \in H -> rH (h * y) = rH y.
    by move=> h y Hh; rewrite rH_Pmul ?(subsetP sHP) // -(mulg1 h) pQhq ?mul1g.
  pose mu x y : rT := subg H ((rH x * rH y)^-1 * rH (x * y)).
  pose nu y := (\sum_(Px \in rcosets P G) mu (repr Px) y)%R.
  have rHmul : {in G &, forall x y, rH (x * y) = rH x * rH y * sgval (mu x y)}.
    move=> x y Gx Gy; rewrite /= subgK ?mulKVg // -mem_lcoset lcoset_sym.
    rewrite -norm_rlcoset; last by rewrite (subsetP nHG) ?GrH ?groupM.
    rewrite (rcoset_transl (HrH _)) -rcoset_mul ?(subsetP nHG) ?GrH //.
    by rewrite mem_mulg.
  have to_rH : forall a x, x \in G -> to a (rH x) = to a x.
    move=> a x Gx; apply: val_inj; rewrite /= !valA ?GrH //.
    case/rcosetP: (HrH x) => b; move/subgK=> <- ->; rewrite conjgM.
    by congr (_ ^ _); rewrite conjgE -valV -!valM (Ring.addrC a) Ring.addKr.
  have mu_Pmul: forall x y z, x \in P -> mu (x * y) z = mu y z.
    move=> x y z Px; apply: (congr1 (subg _)). (* was congr subg *)
    rewrite -mulgA !(rH_Pmul x) ?rPmul; try exact: Px. (* was //. *)
    by rewrite -mulgA invMg -mulgA mulKg.
  have mu_Hmul: forall x y z, x \in G -> y \in H -> mu x (y * z) = mu x z.
    move=> x y z Gx Hy; apply: (congr1 (subg _)). (* was congr subg. *)
    rewrite (mulgA x) (conjgCV x) -mulgA 2?rH_Hmul //.
    by rewrite -mem_conjg (normP _) ?(subsetP nHG).
  have{mu_Hmul} nu_Hmul: forall y z, y \in H -> nu (y * z) = nu z.
    move=> y z Hy; apply: eq_bigr => Px; case/rcosetsP=> x Gx ->{Px}.
    apply: mu_Hmul y z _ Hy.
    by rewrite -(groupMl _ (subsetP sPG _ (PpP x))) mulgKV.
  have cocycle_mu: {in G & &, forall x y z,
    mu (x * y)%g z + to (mu x y) z = mu y z + mu x (y * z)%g}%R.
  - move=> x y z Gx Gy Gz; apply: val_inj.
    apply: (mulg_injl (rH x * rH y * rH z)).
    rewrite -(to_rH _ _ Gz) Ring.addrC /= valA ?GrH //.
    rewrite mulgA -(mulgA _ (rH z)) -conjgC mulgA -!rHmul ?groupM //.
    by rewrite mulgA -mulgA -2!(mulgA (rH x)) -!rHmul ?groupM.
  move: mu => mu in rHmul mu_Pmul cocycle_mu nu nu_Hmul.
  have{cocycle_mu} cocycle_nu : {in G &, forall y z,
     nu z + to (nu y) z = mu y z *+ #|G : P| + nu (y * z)%g}%R.
  - move=> y z Gy Gz; rewrite /= (big_morph _ (toB z Gz)).
    have ->: (nu z = \sum_(Px \in rcosets P G) mu (repr Px * y)%g z)%R.
      rewrite /nu (reindex ('Msr%act^~ y)); last first.
        by exists ('Msr%act^~ y^-1) => Px _; rewrite (actK, actKV).
      symmetry; apply: eq_big => Px; first by rewrite (actsP (act_Cayley P G)).
      case/rcosetsP=> x Gx /= ->{Px}; rewrite rcosetE -rcosetM.
      case: repr_rcosetP=> p1 Pp1; case: repr_rcosetP=> p2 Pp2.
      by rewrite -mulgA [x * y]lock !mu_Pmul.
    rewrite -sumr_const -!big_split /=; apply: eq_bigr => Px.
    case/rcosetsP=> x Gx ->{Px}; rewrite -cocycle_mu //.
    by case: repr_rcosetP=> p1 Pp1; rewrite groupMr // (subsetP sPG).
  move: nu => nu in nu_Hmul cocycle_nu.
  pose f x := rH x * sgval (nu x *+ m)%R.
  have{cocycle_nu} fM: {in G &, {morph f : x y / x * y}}.
    move=> x y Gx Gy; rewrite /f ?rHmul // -3!mulgA; congr (_ * _).
    rewrite (mulgA _ (rH y)) (conjgC _ (rH y)) -mulgA -valA ?GrH ?to_rH //.
    congr (_ * _); rewrite -!valM -(mK (mu x y)) toX //.
    by rewrite Ring.mulrnA -!Ring.mulrn_addl -cocycle_nu // Ring.addrC.
  exists (Morphism fM @* G)%G; apply/complP; split.
    apply/trivgP; apply/subsetP=> x; case/setIP=> Hx.
    case/morphimP=> y _ Gy eq_x.
    apply/set1P; move: Hx; rewrite {x}eq_x /= groupMr ?subgP //.
    rewrite -{1}(mulgKV y (rH y)) groupMl -?mem_rcoset // => Hy.
    rewrite -(mulg1 y) /f nu_Hmul // rH_Hmul //; exact: (morph1 (Morphism fM)).
  apply/setP=> x; apply/mulsgP/idP=> [[h y Hh fy ->{x}] | Gx].
    rewrite groupMl; last exact: (subsetP sHG).
    case/morphimP: fy => z _ Gz ->{x Hx y}.
    by rewrite /= /f groupMl ?GrH // (subsetP sHG) ?subgP.
  exists (x * (f x)^-1) (f x); last first; first by rewrite mulgKV.
    by apply/morphimP; exists x.
  rewrite -groupV invMg invgK -mulgA (conjgC (val _)) mulgA.
  by rewrite groupMl -(mem_rcoset, mem_conjg) // (normsP nHG) // subgP.
case/complP=> trHK eqHK cpHL; case/complP: (cpHL) => trHL eqHL KPeqLP.
pose nu x : rT := subg H (divgr H L x); pose Q := (K :&: P)%G.
have sKG: {subset K <= G} by apply/subsetP; rewrite -eqHK mulG_subr.
have sLG: {subset L <= G} by apply/subsetP; rewrite -eqHL mulG_subr.
have val_nu: forall x, x \in G -> sgval (nu x) = divgr H L x.
  by move=> x Gx; rewrite subgK // mem_divgr // eqHL.
have nu_cocycle: {in G &, forall x y, nu (x * y) = (to (nu y) x^-1 + nu x)%R}.
  move=> x y Gx Gy; apply: val_inj => /=.
  rewrite valA ?groupV // !(val_nu, groupM, groupV) // /divgr (remgrM cpHL) //.
  by rewrite mulgA -conjgCV -!mulgA -invMg.
have nuL: forall x, x \in L -> nu x = 0%R.
  move=> x Lx; apply: val_inj; rewrite /= val_nu ?sLG //.
  by rewrite /divgr remgr_id ?mulgV.
exists (sgval ((\sum_(X \in rcosets Q K) nu (repr X)^-1) *+ m)%R).
  exact: subgP.
apply/eqP; rewrite eq_sym eqEcard; apply/andP.
split; last first.
  by rewrite cardJg -(leq_pmul2l (ltn_0group H)) -!TI_cardMg // eqHL eqHK.
apply/subsetP=> /= x_nu; case/imsetP=> x Kx ->{x_nu}.
rewrite conjgE mulgA (conjgC _ x).
have Gx: x \in G by rewrite sKG.
rewrite conjVg -mulgA -valA // -valV -valM (_ : _ + _ = nu x^-1)%R.
  rewrite /= val_nu ?groupV //.
  by rewrite mulKVg groupV mem_remgr // eqHL groupV.
rewrite toX // Ring.oppr_muln -Ring.mulrn_addl (big_morph _ (toB x Gx)).
rewrite Ring.addrC (reindex ('Msr%act^~ x)) /=; last first.
  by exists ('Msr%act^~ x^-1) => Px _; rewrite (actK, actKV).
rewrite (eq_bigl (mem (rcosets Q K))) => [/=|X]; last first.
  by rewrite (actsP (act_Cayley Q K)).
rewrite -sum_split_sub /= (eq_bigr (fun _ => nu x^-1)) => [|X]; last first.
  case/imsetP=> y Ky ->{X}; rewrite !rcosetE.
  set yx1 := repr _; have: yx1 \in Q :* y :* x.
    by apply: (mem_repr (y * x)); rewrite -rcosetM rcoset_refl.
  case/rcosetP=> y1 Qyy1 ->{yx1}; move: (repr _) (mem_repr _ Qyy1) => y2 Qyy2.
  have Gy2: y2 \in G.
    by case/rcosetP: Qyy2 => z2; case/setIP=> Kz2 _ ->; rewrite sKG ?groupM.
  move: Qyy1; rewrite -(rcoset_transl Qyy2) /= KPeqLP; case/rcosetP=> z1.
  case/setIP=> Lz1 _ ->{y1}.
  rewrite !invMg 2?nu_cocycle ?groupM ?groupV // ?sLG // !invgK.
  rewrite (nuL z1^-1) ?groupV // to0 // Ring.add0r (Ring.addrC (to _ x)).
  by rewrite Ring.addrK.
rewrite sumr_const -Ring.mulrnA (_ : #|_| = #|G : P|) ?mK //.
rewrite -[#|_|]divgS ?subsetIl // -(divn_pmul2l (ltn_0group H)).
rewrite -!TI_cardMg //; last by rewrite setIA setIAC (setIidPl sHP).
by rewrite group_modl // eqHK (setIidPr sPG) divgS.
Qed.

Module AfterGaschutz.
End AfterGaschutz.

Theorem SchurZass_split : forall (gT : finGroupType) (G H : {group gT}),
  Hall G H -> H <| G -> [splits G, over H].
Proof.
move=> gT G; move: {2}_.+1 (ltnSn #|G|) => n.
elim: n gT G => // n IHn gT G; rewrite ltnS => Gn H hallH nsHG.
have [sHG nHG] := andP nsHG.
case: (trivgVpdiv H) => [H1 | [p pr_p pH]].
  by apply/splitsP; exists G; rewrite inE H1 -subG1 subsetIl mul1g eqxx.
have [P sylP] := Sylow_exists p H.
case nPG: (P <| G); last first.
  pose N := ('N_G(P))%G.
  have sNG: N \subset G by rewrite subsetIl.
  have eqHN_G: H * N = G by exact: Frattini_arg sylP.
  pose H' := (H :&: N)%G.
  have nH'N: H' <| N.
    rewrite /(_ <| N) subsetIr; apply/subsetP=> x Nx.
    rewrite inE; apply/subsetP=> y; rewrite conjIg (conjGid Nx) (normP _) //.
    by apply: (subsetP nHG); case/setIP: Nx.
  have eq_iH: #|G : H| = #|N| %/ #|H'|.
    rewrite -divgS // -(divn_pmul2l (ltn_0group H')) mulnC -eqHN_G.
    by rewrite -mul_cardG (mulnC #|H'|) divn_pmul2l // ltn_0group.
    have hallH': Hall N H'.
    have sH'H: H' \subset H by exact: subsetIl.
    case/andP: hallH => _; rewrite eq_iH -(LaGrange sH'H) coprime_mull.
    by rewrite /Hall divgS subsetIr //; case/andP.
  have: [splits N, over H'].
    apply: IHn hallH' nH'N; apply: {n}leq_trans Gn.
    rewrite ltn_neqAle subset_leq_card // andbT; apply/eqP=> eqNG.
    case/andP: nPG; rewrite (subset_trans _ sHG); last by case/andP: sylP.
    suff <-: N :=: G by rewrite subsetIr.
    by apply/setP; exact/subset_cardP.
  case/splitsP=> K; case/complP=> trKN eqH'K.
  have sKN: K \subset N by rewrite -(mul1g K) -eqH'K mulSg ?sub1set.
  apply/splitsP; exists K; rewrite inE -subG1; apply/andP; split.
    apply/subsetP=> x; case/setIP=> Hx Kx.
    by rewrite -trKN 2!inE Hx (subsetP sKN) Kx.
  rewrite eqEsubset -eqHN_G mulgS // -eqH'K mulgA mulSg //.
  by rewrite mul_subG ?subsetIl.
pose Z := ('Z(P))%G; have iZ: 'Z(P) = Z by [].
have sZP: Z \subset P by exact: center_sub.
have sZH: Z \subset H by case/andP: sylP; move/(subset_trans sZP).
have sZG: Z \subset G by exact: subset_trans sHG.
have nZG: Z <| G by apply: char_normal_trans nPG; exact: center_char.
have nZH: Z <| H by exact: normalS nZG.
pose Gbar := (G / Z)%G; have iGbar: G / Z = Gbar by [].
pose Hbar := (H / Z)%G; have iHbar: H / Z = Hbar by [].
have nHGbar: Hbar <| Gbar by exact: morphim_normal.
have hallHbar: Hall Gbar Hbar.
  by apply: morphim_Hall; first case/andP: nZH.
have: [splits Gbar, over Hbar].
  apply: IHn => //; apply: {n}leq_trans Gn.
  rewrite card_quotient; last by case/andP: nZG.
  rewrite -(divgS sZG) ltn_Pdiv ?ltn_0group // ltnNge -trivg_card_le1.
  apply/eqP; move/(trivg_center_pgroup (pHall_pgroup sylP)); move/eqP.
  rewrite trivg_card1 (card_Hall sylP) p_part -(expn0 p).
  by rewrite eqn_exp2l ?prime_gt1 // lognE pH pr_p ltn_0group.
case/splitsP=> Kbar; case/complP=> trHKbar eqHKbar.
have: Kbar \subset Gbar by rewrite -eqHKbar mulG_subr.
case/inv_quotientS=> //= ZK quoZK sZZK sZKG.
have nZZK: Z <| ZK by exact: normalS nZG.
have cardZK: #|ZK| = (#|Z| * #|G : H|)%N.
  rewrite -(LaGrange sZZK); congr (_ * _)%N.
  rewrite -card_quotient -?quoZK; last by case/andP: nZZK.
  rewrite -(divgS sHG) -(LaGrange sZG) -(LaGrange sZH) divn_pmul2l //.
  rewrite -!card_quotient; try by [case/andP: nZG | case/andP: nZH].
  by rewrite iGbar -eqHKbar (TI_cardMg trHKbar) mulKn.
have: [splits ZK, over Z].
  case: (Gaschutz nZZK _ sZZK) => // [||-> _].
  - apply: subset_trans (centS sZP); exact: subsetIr.
  - rewrite -divgS // cardZK mulKn //.
    by case/andP: hallH=> _; rewrite -(LaGrange sZH) coprime_mull; case/andP.
  by apply/splitsP; exists [1 gT]%G; rewrite inE -subG1 subsetIr mulg1 eqxx.
case/splitsP=> K; case/complP=> trZK eqZK.
have sKZK: K \subset ZK by rewrite -(mul1g K) -eqZK mulSg ?sub1set.
have trHK: H :&: K = 1.
  apply/trivgP; apply/subsetP=> x; case/setIP=> Hx Kx; rewrite -trZK.
  have Nx: x \in 'N(Z) by apply: subsetP (x) Hx; case/andP: nZH.
  rewrite inE Kx andbT coset_idr //; apply/set1gP.
  rewrite -trHKbar quoZK inE !mem_imset // inE Nx //; exact: (subsetP sKZK).
apply/splitsP; exists K; rewrite inE trHK ?eqEcard subxx leqnn /=.
rewrite mul_subG ?(subset_trans sKZK) //= TI_cardMg // -(@mulKn #|K| #|Z|) //.
by rewrite -TI_cardMg // eqZK cardZK mulKn // LaGrange.
Qed.

Module SchurZassCP1. End SchurZassCP1.

Theorem SchurZass_trans_sol : forall (gT : finGroupType) (H K K1 : {group gT}),
    solvable H -> K \subset 'N(H) -> K1 \subset H * K ->
    coprime #|H| #|K| -> #|K1| = #|K| ->
  exists2 x, x \in H & K1 :=: K :^ x.
Proof.
move=> gT H; move: {2}_.+1 (ltnSn #|H|) => n; elim: n => // n IHn in gT H *.
rewrite ltnS => leHn K K1 solH nHK; case: (eqsVneq H 1) => [H1 |].
  rewrite H1 mul1g => sK1K _ eqK1K.
  exists (1 : gT); first exact: set11.
  by apply/eqP; rewrite conjsg1 eqEcard sK1K eqK1K /=.
pose G := (H <*> K)%G.
have defG: G :=: H * K by rewrite -normC // -norm_mulgenEl // mulgenC.
have sHG: H \subset G by rewrite -gen_subG genS // subsetUl.
have sKG: K \subset G by rewrite -gen_subG genS // subsetUr.
have nHG: H <| G by rewrite /(H <| G) sHG gen_subG subUset nHK normG.
case/(solvable_norm_abelem solH nHG)=> M [sMH nMG ntM].
case/andP=> abelM _; rewrite -defG => sK1G coHK oK1K.
have nMsG: forall L : {set gT}, L \subset G -> L \subset 'N(M).
  by move=> L; move/subset_trans; apply; case/andP: nMG.
have [coKM coHMK]: coprime #|M| #|K| /\ coprime #|H / M| #|K|.
  by apply/andP; rewrite -coprime_mull card_quotient ?nMsG ?LaGrange.
have oKM: forall K' : {group gT},
  K' \subset G -> #|K'| = #|K| -> #|K' / M| = #|K|.
- move=> K' sK'G oK'.
  rewrite -quotient_mulg -?norm_mulgenEl ?card_quotient ?nMsG //; last first.
    by rewrite gen_subG subUset sK'G; case/andP: nMG.
  rewrite -divgS /=; last by rewrite -gen_subG genS ?subsetUr.
  rewrite norm_mulgenEl ?nMsG // coprime_cardMg ?mulnK //.
  by rewrite oK' coprime_sym.
have [xb]: exists2 xb, xb \in H / M & K1 / M = (K / M) :^ xb.
  apply: IHn; try by rewrite (quotient_sol, morphim_norms, oKM K) ?(oKM K1).
    apply: leq_trans leHn; rewrite card_quotient ?nMsG //.
    rewrite -(ltn_pmul2l (ltn_0group M)) LaGrange // -{1}(mul1n #|H|).
    by rewrite ltnNge leq_pmul2r // -trivg_card_le1.
  by rewrite -morphimMl ?nMsG // -defG morphimS.
case/morphimP=> x nMx Hx ->{xb} eqK1Kx; pose K2 := (K :^ x)%G.
have{eqK1Kx} eqK12: K1 / M = K2 / M by rewrite quotientJ.
suff [y My ->]: exists2 y, y \in M & K1 :=: K2 :^ y.
  exists (x * y); first by rewrite groupMl // (subsetP sMH).
  by rewrite conjsgM.
have nMK1: K1 \subset 'N(M) by case/andP: nMG => _; exact: subset_trans.
have defMK: M * K1 = M <*> K1 by rewrite -normC // -norm_mulgenEl // mulgenC.
have sMKM: M \subset M <*> K1 by rewrite -defMK mulG_subl.
have nMKM: M <| M <*> K1 by rewrite /(_ <| _) sMKM gen_subG subUset normG.
have trMK1: M :&: K1 = 1 by rewrite coprime_TIg ?oK1K.
have trMK2: M :&: K2 = 1 by rewrite coprime_TIg ?cardJg ?oK1K.
case: (Gaschutz nMKM _ sMKM) => //= [|_].
  by rewrite -divgS //= -defMK coprime_cardMg oK1K // mulKn.
apply; first 1 last; first by rewrite inE defMK trMK1 ?eqxx /=.
  by rewrite -!(setIC M) trMK1.
rewrite inE trMK2 eqxx eq_sym eqEcard /= -defMK andbC.
rewrite !coprime_cardMg ?cardJg ?oK1K // leqnn.
rewrite -{2}(mulGid M) -mulgA mulgS //.
by move/eqP: eqK12; rewrite eqEsubset morphimSK // ker_coset; case/andP.
Qed.

