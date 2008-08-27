Require Import ssreflect ssrbool ssrfun eqtype ssrnat div prime.
Require Import fintype ssralg bigops finset.
Require Import groups morphisms automorphism normal action.
Require Import commutators cyclic center pgroups sylow.

(* Require Import seq paths connect finfun group_perm. *)

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Import GroupScope.

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
case/normalP: nHG => _; case/complgP: cK => trHK <- nHHK x y HKx HKy.
rewrite {1}[y]split_pr mulgA (conjgCV x) {2}[x]split_pr -2!mulgA mulgA.
rewrite remGr_id 1?remgr_idr // groupMl -?mem_conjg ?nHHK //;
  by rewrite (mem_remgr, mem_divgr).
Qed.

End Split.

Prenex Implicits complg splitg divgr.

Theorem Gaschutz : forall (gT : finGroupType) (G H P : {group gT}),
  H <| G -> H \subset P -> P \subset G -> abelian H -> coprime #|H| #|G : P| ->
    splitg G H = splitg P H
 /\ {in complg G H &, forall K L : {group gT},
      K :&: P = L :&: P -> exists2 x, x \in H & L = (K :^ x)%G}.
Proof.
move=> gT G H P nsHG sHP sPG abelH coHiPG.
have [sHG nHG] := andP nsHG.
(* set up H as a ZG-module *)
have mulHC : @commutative {x | x \in H} mulg.
  by case=> x Hx [y Hy]; apply: val_inj; rewrite /= (centsP abelH).
pose rT := Ring.AdditiveGroup (@mulgA _) mulHC (@mul1g _) (@mulVg _).
pose inH x : rT := insubd (Sub 1 (group1 H)) x.
have valH: {in H, cancel inH val} by move=> *; exact: insubdK.
have Hval: forall u : rT, sval u \in H by exact: valP.
have valM: forall a b : rT, sval (a + b)%R = sval a * sval b by [].
have valV: forall a : rT, sval (- a)%R = (sval a)^-1 by [].
have valX: forall (a : rT) n, sval (a *+ n)%R = sval a ^+ n.
  by move=> a; elim=> // n IHn; congr (_ * _).
pose to (a : rT) y := inH (sval a ^ y).
have valA: forall a y, y \in G -> sval (to a y) = sval a ^ y.
  by move=> a y Gy; rewrite valH // -{2}(normsP nHG y Gy) memJ_conjg.
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
  by rewrite order_dvd_g // (subsetP sHP) // Hval.
split=> [|K L].
  apply/splitgP/splitgP=> [[K trHK eqHK] | [Q trHQ eqHQ]].
    exists (K :&: P)%G; first by rewrite setICA (setIidPl sHP) setIC.
    by rewrite group_modl // eqHK (setIidPr sPG).
  have sQP: Q \subset P by rewrite -eqHQ mulG_subr.
  pose rP x := repr (P :* x); pose pP x := x * (rP x)^-1.
  have PpP: pP _ \in P.
    by move=> x; rewrite -mem_rcoset rcoset_repr rcoset_refl.
  have rPmul : forall x y, x \in P -> rP (x * y) = rP y.
    by move=> x y Px; rewrite /rP rcosetM rcoset_id.
  pose pQ x := remgr Q H x; pose rH x := pQ (pP x) * rP x.
  have pQhq: {in H & Q, forall h q, pQ (h * q) = q} by exact: remgr_idl.
  have pQmul: {in P &, {morph pQ : x y / x * y}}.
    apply: remGrM; [exact/complgP | exact: normalS nsHG].
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
  pose mu x y : rT := inH ((rH x * rH y)^-1 * rH (x * y)).
  pose nu y := (\sum_(Px \in rcosets P G) mu (repr Px) y)%R.
  have rHmul : {in G &, forall x y, rH (x * y) = rH x * rH y * sval (mu x y)}.
    move=> x y Gx Gy; rewrite /= valH ?mulKVg // -mem_lcoset lcoset_sym.
    rewrite -norm_rlcoset; last by rewrite (subsetP nHG) ?GrH ?groupM.
    rewrite (rcoset_trans1 (HrH _)) -rcoset_mul ?(subsetP nHG) ?GrH //.
    by rewrite mem_mulg.
  have to_rH : forall a x, x \in G -> to a (rH x) = to a x.
    move=> a x Gx; apply: val_inj; rewrite /= !valA ?GrH //.
    case/rcosetP: (HrH x) => b; move/valH=> <- ->; rewrite conjgM.
    by congr (_ ^ _); rewrite conjgE -valV -!valM (Ring.addrC a) Ring.addKr.   
  have mu_Pmul: forall x y z, x \in P -> mu (x * y) z = mu y z.
    move=> x y z Px; congr inH; rewrite -mulgA !(rH_Pmul x) ?rPmul //.
    by rewrite -mulgA invMg -mulgA mulKg.
  have mu_Hmul: forall x y z, x \in G -> y \in H -> mu x (y * z) = mu x z.
    move=> x y z Gx Hy; congr inH.
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
  pose f x := rH x * sval (nu x *+ m)%R.
  have{cocycle_nu} fM: {in G &, {morph f : x y / x * y}}.
    move=> x y Gx Gy; rewrite /f ?rHmul // -3!mulgA; congr (_ * _).
    rewrite (mulgA _ (rH y)) (conjgC _ (rH y)) -mulgA -valA ?GrH ?to_rH //.
    congr (_ * _); rewrite -!valM -(mK (mu x y)) toX //.
    by rewrite Ring.mulrnA -!Ring.mulrn_addl -cocycle_nu // Ring.addrC.
  exists (Morphism fM @* G)%G.
    apply/subsetP=> x; case/setIP=> Hx; case/morphimP=> y _ Gy eq_x.
    apply/set1P; move: Hx; rewrite {x}eq_x /= groupMr // -{1}(mulgKV y (rH y)).
    rewrite groupMl -?mem_rcoset // => Hy.
    rewrite -(mulg1 y) /f nu_Hmul // rH_Hmul //; exact: (morph1 (Morphism fM)).
  apply/setP=> x; apply/mulsgP/idP=> [[h y Hh fy ->{x}] | Gx].
    rewrite groupMl; last exact: (subsetP sHG).
    case/morphimP: fy => z _ Gz ->{x Hx y}.
    by rewrite /= /f groupMl ?GrH // (subsetP sHG) ?valP.
  exists (x * (f x)^-1) (f x); last first; first by rewrite mulgKV.
    by apply/morphimP; exists x. 
  rewrite -groupV invMg invgK -mulgA (conjgC (val _)) mulgA.
  by rewrite groupMl -(mem_rcoset, mem_conjg) // (normsP nHG) // Hval.
case/complgP=> trHK eqHK cpHL; case/complgP: (cpHL) => trHL eqHL KPeqLP.
pose nu x : rT := inH (divgr L H x); pose Q := (K :&: P)%G.
have sKG: {subset K <= G} by apply/subsetP; rewrite -eqHK mulG_subr.
have sLG: {subset L <= G} by apply/subsetP; rewrite -eqHL mulG_subr.
have val_nu: forall x, x \in G -> sval (nu x) = divgr L H x.
  by move=> x Gx; rewrite valH // mem_divgr // eqHL.
have nu_cocycle: {in G &, forall x y, nu (x * y) = (to (nu y) x^-1 + nu x)%R}.
  move=> x y Gx Gy; apply: val_inj => /=.
  rewrite valA ?groupV // !(val_nu, groupM, groupV) // /divgr (remGrM cpHL) //.
  by rewrite mulgA -conjgCV -!mulgA -invMg.
have nuL: forall x, x \in L -> nu x = 0%R.
  move=> x Lx; apply: val_inj; rewrite /= val_nu ?sLG //.
  by rewrite /divgr remgr_idr ?mulgV.
exists (sval ((\sum_(X \in rcosets Q K) nu (repr X)^-1) *+ m)%R) => //.
apply/eqP; rewrite -val_eqE eq_sym eqset_sub_card; apply/andP.
split; last first.
  rewrite card_conjg -(leq_pmul2l (ltn_0group H)) -!(card_mulG_trivP _ _ _) //.
  by rewrite eqHL eqHK.
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
  move: Qyy1; rewrite -(rcoset_trans1 Qyy2) /= KPeqLP; case/rcosetP=> z1.
  case/setIP=> Lz1 _ ->{y1}.
  rewrite !invMg 2?nu_cocycle ?groupM ?groupV // ?sLG // !invgK.
  rewrite (nuL z1^-1) ?groupV // to0 // Ring.add0r (Ring.addrC (to _ x)).
  by rewrite Ring.addrK.
rewrite sumr_const -Ring.mulrnA (_ : #|_| = #|G : P|) ?mK //.
rewrite -[#|_|]group_divn ?subsetIl // -(divn_pmul2l (ltn_0group H)).
rewrite -!(card_mulG_trivP _ _ _) //; last first.
  by rewrite setIA setIAC (setIidPl sHP).
by rewrite group_modl // eqHK (setIidPr sPG) group_divn.
Qed.

Module AfterGaschutz.
End AfterGaschutz.

Theorem SchurZass_split : forall (gT : finGroupType) (G H : {group gT}),
  is_hall G H -> H <| G -> splitg G H.
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
    rewrite inE; apply/subsetP=> y; rewrite conjIg (conjGid Nx) (normP _) //.
    by apply: (subsetP nHG); case/setIP: Nx.
  have eq_iH: #|G : H| = #|N| %/ #|H'|.
    rewrite -group_divn // -(divn_pmul2l (pos_card_group H')) mulnC -eqHN_G.
    by rewrite card_mulG (mulnC #|H'|) divn_pmul2l // pos_card_group.
  have hallH': is_hall N H'.
    have sH'H: H' \subset H by exact: subsetIl.
    case/andP: hallH => _; rewrite eq_iH -(LaGrange sH'H) coprime_mull.
    by rewrite /is_hall group_divn subsetIr //; case/andP.
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
have nZH: Z <| H by exact: normalS nZG.
pose Gbar := (G / Z)%G; have iGbar: G / Z = Gbar by [].
pose Hbar := (H / Z)%G; have iHbar: H / Z = Hbar by [].
have nHGbar: Hbar <| Gbar by exact: morphim_normal.
have hallHbar: is_hall Gbar Hbar.
  by apply: morphim_is_hall; first case/andP: nZH.
have: splitg Gbar Hbar; last case/splitgP=> Kbar trHKbar eqHKbar. 
  apply: IHn => //; apply: {n}leq_trans Gn.
  rewrite card_quotient; last by case/andP: nZG.
  rewrite -(group_divn sZG) divn_lt ?pos_card_group // ltnNge -trivg_card.
  move: sylP; rewrite sylowE; case/andP => _.
  rewrite p1_part lognE prime_p dvdn_pdiv ltn_0group.
  move/eqP; exact: pgroup_ntriv.
have: Kbar \subset Gbar by rewrite -eqHKbar mulG_subr.
case/inv_quotientS=> // ZK; move/(congr1 val)=> /= quoZK sZZK sZKG.
have nZZK: Z <| ZK by exact: normalS nZG.
have cardZK: #|ZK| = (#|Z| * #|G : H|)%N.
  rewrite -(LaGrange sZZK); congr (_ * _)%N.
  rewrite -card_quotient -?quoZK; last by case/andP: nZZK.
  rewrite -(group_divn sHG) -(LaGrange sZG) -(LaGrange sZH) divn_pmul2l //.
  rewrite -!card_quotient; try by [case/andP: nZG | case/andP: nZH].
  by rewrite iGbar -eqHKbar (card_mulG_trivP _ _ trHKbar) divn_mulr.
have: splitg ZK Z; last case/splitgP=> K trZK eqZK.
  case: (Gaschutz nZZK _ sZZK) => // [||-> _].
  - apply: subset_trans (centS sZP); exact: subsetIr.
  - rewrite -group_divn // cardZK divn_mulr //. 
    by case/andP: hallH=> _; rewrite -(LaGrange sZH) coprime_mull; case/andP.
  apply/splitgP; exists (1%G : group gT); [exact: subsetIr | exact: mulg1].
have sKZK: K \subset ZK by rewrite -(mul1g K) -eqZK mulSg ?sub1set.
have trHK: trivg (H :&: K).
  apply/subsetP=> x; case/setIP=> Hx Kx; apply: (subsetP trZK).
  have Nx: x \in 'N(Z) by apply: subsetP (x) Hx; case/andP: nZH.
  rewrite inE Kx andbT coset_of_idr //; apply/set1P.
  rewrite (subsetP trHKbar) // quoZK inE !mem_imset // inE Nx //.
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

Lemma solvable_norm_abelem : forall L G : {group gT},
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
    apply: subset_trans (subset_trans sH1H _) (centS sH1H).
    by rewrite (sameP centsP commG1P).
  pose p := pdiv #|H|.
  have prp: prime p by rewrite prime_pdiv // ltnNge -trivg_card.
  have ntH1 : ~~ trivg H1.
    case: (Cauchy prp (dvdn_pdiv #|H|)) => x Hx oxp.
    rewrite /trivg gen_subG expn1; apply/subsetPn; exists x.
      by rewrite inE Hx -/p -oxp order_expn1 eqxx.
    by apply/set1P=> x1; rewrite -oxp x1 order1 in prp.
  exists H1; split=> //; first exact: subset_trans sHG.
    exact: char_norm_trans nHL.
  apply/abelem_Ohm1P=> //; apply/eqP.
  rewrite eqset_sub; case/andP: (char_Ohm 1 H1) => -> _.
  rewrite gen_subG; apply/subsetP=> x Hx.
  have H1x: x \in H1 by rewrite mem_gen.
  apply: mem_gen; move: Hx; rewrite !inE -!order_dvd -/p !expn1 H1x.
  case/andP=> Hx; case: (primeP prp) => _ dvp; move/dvp=> {dvp}.
  case/orP; move/eqP=> oxp; rewrite oxp ?dvd1n //.
  rewrite ((pdiv _ =P p) _) ?dvdnn // eqn_leq !pdiv_min_dvd ?prime_gt1 //.
  - by rewrite prime_pdiv // ltnNge -trivg_card.
  - apply: dvdn_trans (dvdn_pdiv _) _; exact: group_dvdn.
  by rewrite -oxp order_dvd_g.
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
have sHG: H \subset G by rewrite -gen_subG genS // subsetUl.
have sKG: K \subset G by rewrite -gen_subG genS // subsetUr.
have nHG: H <| G by rewrite /(H <| G) sHG gen_subG subUset nHK normG.
move/idPn: trH; case/(solvable_norm_abelem solH nHG)=> M [sMH nMG ntM].
case/andP=> abelM _; rewrite -defG => sK1G coHK oK1K.
have nMsG: forall L : {set gT}, L \subset G -> L \subset 'N(M).
  by move=> L; move/subset_trans; apply; case/andP: nMG.
have [coKM coHMK]: coprime #|M| #|K| /\ coprime #|H / M| #|K|.
  by apply/andP; rewrite -coprime_mull card_quotient ?nMsG ?LaGrange.
have oKM: forall K' : {group gT},
  K' \subset G -> #|K'| = #|K| -> #|K' / M| = #|K|.
- move=> K' sK'G oK'.
  rewrite -quotient_mulg -?norm_mulgenE ?card_quotient ?nMsG //; last first.
    by rewrite gen_subG subUset sK'G; case/andP: nMG.
  rewrite -group_divn /=; last by rewrite -gen_subG genS ?subsetUr.
  rewrite norm_mulgenE ?nMsG // coprime_card_mulG ?divn_mull //.
  by rewrite oK' coprime_sym.
have [xb]: exists2 xb, xb \in H / M & (K1 / M = (K / M) :^ xb)%G.
  apply: IHn; try by rewrite (solvable_quo, morphim_norms, oKM K) ?(oKM K1).
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
have nMK1: K1 \subset 'N(M) by case/andP: nMG => _; exact: subset_trans.
have defMK: M * K1 = M <*> K1 by rewrite -normC // -norm_mulgenE // mulgenC.
have sMKM: M \subset M <*> K1 by rewrite -defMK mulG_subl.
have nMKM: M <| M <*> K1 by rewrite /(_ <| _) sMKM gen_subG subUset normG.
have trMK1: trivg (M :&: K1) by rewrite coprime_trivg ?oK1K.
have trMK2: trivg (M :&: K2) by rewrite coprime_trivg ?card_conjg ?oK1K.
case: (Gaschutz nMKM _ sMKM) => // [|_].
  by rewrite -group_divn //= -defMK coprime_card_mulG oK1K // divn_mulr.
apply; first 1 last; first by rewrite inE defMK trMK1 /=.
  by rewrite -!(setIC M); case/trivGP: trMK1 => ->; exact/trivgP.
rewrite inE trMK2 eq_sym eqset_sub_card /= -defMK andbC.
rewrite !coprime_card_mulG ?card_conjg ?oK1K // leqnn.
rewrite -{2}(mulGid M) -mulgA mulgS //.
by move/eqP: eqK12; rewrite eqset_sub morphimSK // ker_coset; case/andP.
Qed.

