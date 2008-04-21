Require Import ssreflect ssrbool ssrfun eqtype ssrnat.
Require Import div seq fintype paths connect groups.  
Require Import group_perm finfun action normal ssralg.
Require Import bigops sylow center cyclic finset.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Section More_conjg.

Variable elt : finGroupType.

Lemma conjgC : forall x y : elt, x * y = y * x ^ y.
Proof. by move=> *; rewrite /conjg -!mulgA mulKgv. Qed.

Lemma conjgCv : forall x y : elt, x * y = y ^ x^-1 * x.
Proof. by move=> x y; rewrite (conjgC _ x) conjgKv. Qed.

Lemma norm_conjg : forall (H : {set elt}) x y,
  x \in normaliser H -> (y ^ x \in H) = (y \in H).
Proof. by move=> H x y Nx; rewrite -{1}(norm_sconjg Nx) sconjg_conj. Qed.

End More_conjg.

Notation "'N_' ( G ) H"  := (normaliser H :&: G)
  (at level 10, H at level 8, format "'N_' ( G )  H") : group_scope.

Lemma Frattini : forall (elt : finGroupType) (G H P : {group elt}) p,
  H <| G -> H \subset G -> prime p -> sylow p H P ->
  H :*: N_(G) P = G.
Proof.
move=> elt G H P p nHG sHG p_prime sylP.
have sPG: P \subset G by apply: subset_trans sHG; case/andP: sylP.
apply/setP; apply/subset_eqP; apply/andP; split.
  rewrite -{2}(smulgg G); apply: subset_trans (smulsg _ sHG).
  apply smulgs; exact: subsetIr.
apply/subsetP=> x Gx; pose Q := {P :^ x^-1 as group _}.
have sylQ: sylow p H Q.
  by move/normalP: nHG; move/(_ _ (groupVr Gx))<-; rewrite -sylow_sconjg.
have [y [Hy QPy]]: exists y, y \in H /\ Q = P :^ y :> set _.
  exact: (sylow2_cor _ sylP sylQ).
apply/smulgP; exists y^-1 (y * x); rewrite ?(groupV, mulKg) //.
rewrite 2!setE andbC groupMr // (subsetP sHG) //= sconjgM.
by apply/subsetP=> z; rewrite setE -QPy setE conjgK.
Qed.

Section Split.

Variable elt : finGroupType.

Section Defs.

Variables G H : set elt.

Definition pcomplg K := (H :*: K == G).

Definition complg := [set K : group elt | trivg (H :&: K) && (H :*: K == G)].

Definition splitg := #|complg| != 0.

Definition pr_compl K x := repr (H :* x :&: K).

Definition pr_ker K x := x * (pr_compl K x)^-1.

End Defs.

Variables G H : group elt.

Lemma complgP : forall K : {group elt},
  reflect (disjointg H K /\ H :*: K = G) (K \in complg G H).
Proof.
by move=> K; rewrite setE; apply: (iffP andP); case; split=> //; apply/eqP.
Qed.

Lemma splitgP :
  reflect (exists2 K : {group elt}, disjointg H K & H :*: K = G) (splitg G H).
Proof.
by apply: (iffP pred0Pn); case=> K; first case/complgP;
  exists K; last apply/complgP.
Qed.

Variable K : group elt.

Lemma split_pr : forall x, x = pr_ker H K x * pr_compl H K x.
Proof. by move=> *; rewrite mulgKv. Qed.

Lemma pr_compl_mull : forall x y, x \in H ->
  pr_compl H K (x * y) = pr_compl H K y.
Proof. by move=> x y Hx; rewrite {1}/pr_compl rcoset_morph rcoset_id. Qed.

Lemma pr_ker_mull : forall x y, x \in H ->
  pr_ker H K (x * y) = x * pr_ker H K y.
Proof. by move=> x y Hx; rewrite {1}/pr_ker pr_compl_mull // mulgA. Qed.

Lemma rcoset_compl_pr : forall x, x \in H :*: K ->
  pr_compl H K x \in H :* x :&: K.
Proof.
move=> x; case/smulgP=> h k Hh Kk ->{x}; apply: mem_repr (k) _ _.
by rewrite setE rcoset_sym rcosetE mulgK Hh.
Qed.

Lemma compl_pr : forall x, x \in H :*: K -> pr_compl H K x \in K.
Proof. by move=> x; move/rcoset_compl_pr; case/setIP. Qed.

Lemma ker_pr : forall x, x \in H :*: K -> pr_ker H K x \in H.
Proof.
by move=> x; move/rcoset_compl_pr; case/setIP; rewrite rcoset_sym rcosetE.
Qed.

Section Disjoint.

Hypothesis trHK : disjointg H K.

Lemma pr_compl_id : forall x, x \in K -> pr_compl H K x = x.
Proof.
move=> x Kx; rewrite -[pr_compl H K x]mul1g; apply: canLR (mulgKv _) _.
have HKx: x \in H :*: K by exact: (subsetP (smulg_subr _ _)).
symmetry; apply/set1P; move/disjointgP: trHK => <-.
by rewrite setE ker_pr // groupMl // groupV compl_pr.
Qed.

Lemma pr_compl_idr : forall x y,
  x \in H -> y \in K -> pr_compl H K (x * y) = y.
Proof. by move=> *; rewrite pr_compl_mull // pr_compl_id. Qed.

Lemma pr_ker_idl : forall x y, x \in H -> y \in K -> pr_ker H K (x * y) = x.
Proof. by move=> *; rewrite /pr_ker pr_compl_idr // mulgK. Qed.

End Disjoint.

Lemma complgC : H <| G -> (H \in complg G K) = (K \in complg G H).
Proof.
move=> nHG; rewrite !setE; congr (trivg _ && _); first by apply/setP=> x; rewrite !setE andbC.
apply/eqP/eqP=> eqG; rewrite -eqG in nHG.
  rewrite norm_smulC //; apply: subset_trans nHG; exact: smulg_subl.
rewrite -norm_smulC //; apply: subset_trans nHG; exact: smulg_subr.
Qed.

Hypothesis cK : K \in complg G H.

Lemma sub_compl : K \subset G.
Proof. case/complgP: cK => _ <-; exact: smulg_subr. Qed.

Hypothesis nHG : H <| G.

Lemma pr_compl_morph : forall x y, x \in G -> y \in G ->
  pr_compl H K (x * y) = pr_compl H K x * pr_compl H K y.
Proof.
case/complgP: cK nHG => trHK <- nHHK x y HKx HKy.
rewrite {1}[y]split_pr mulgA (conjgCv x) {2}[x]split_pr -2!mulgA mulgA.
rewrite pr_compl_mull 1?pr_compl_id // groupMl ?(compl_pr, ker_pr, norm_conjg) // groupV.
exact: (subsetP nHHK).
Qed.

End Split.

Prenex Implicits pcomplg complg splitg pr_compl pr_ker.

Theorem Gaschutz_split : forall (elt : finGroupType) (G H P : {group elt}) p,
  prime p -> H <| G -> sylow p G P -> H \subset P -> H \subset center H ->
  splitg G H = splitg P H.
Proof.
move=> elt G H P p prime_p nHG sylP sHP abelH.
have sPG: P \subset G by case/andP: sylP.
have sHG: H \subset G by exact: subset_trans sPG.
apply/splitgP/splitgP=> [[K trHK eqHK] | [Q trHQ eqHQ]].
  exists {K :&: P as group _}.
    by rewrite /disjointg /trivg setIA (disjointgP _ _ trHK) subsetIl.
  rewrite group_modularity // eqHK; apply/setP=> x.
  by rewrite setE andbC; case Px: (x \in P); first exact: (subsetP sPG).
have sQP: Q \subset P by rewrite -eqHQ -{1}(smul1g Q) smulsg ?subset_set1.
pose rP x := repr (P :* x); pose pP x := x * (rP x)^-1.
have PpP: forall x, pP x \in P.
  by move=> x; rewrite -rcosetE rcoset_repr rcoset_refl.
have rPmul : forall x y, x \in P -> rP (x * y) = rP y.
  move=> x y Px; congr repr; apply: rcoset_trans1.
  by rewrite rcoset_sym setE mulgK.
pose pQset x := Q :&: (H :* x); pose pQ x := repr (pQset x).
have pQhq: forall h q, h \in H -> q \in Q -> pQ (h * q) = q.
  move=> h q Hh Qq; set q1 := pQ _; have: q1 \in pQset (h * q).
    by apply: (@mem_repr _ q); rewrite setE Qq rcoset_sym setE mulgK.
  case/setIP=> Qq1; case/rcosetP=> h1 Hh1; rewrite mulgA => eq_qq1.
  suff: h1 * h \in [set 1] by rewrite -[q]mul1g eq_qq1; move/set1P <-.
  by rewrite (subsetP trHQ) // setE groupM // -(groupMr _ Qq) -eq_qq1.
have pQmul: forall x y, x \in P -> y \in P -> pQ (x * y) = pQ x * pQ y.
  move=> x y; rewrite -eqHQ; case/smulgP=> h1 q1 Hh1 Hq1  ->{x}.
  case/smulgP=> h2 q2 Hh2 Hq2 ->{y}.
  rewrite -mulgA (mulgA q1) (conjgCv q1) -mulgA mulgA.
  by rewrite !pQhq // groupMl ?norm_conjg //;
     rewrite groupV !(subsetP nHG, subsetP sPG, subsetP sQP).
pose rH x := pQ (pP x) * rP x.
have HrH: forall x, rH x \in H :* x.
  move=> x; rewrite rcoset_sym setE invg_mul mulgA -/(pP x); have:= PpP x.
  by rewrite -eqHQ; case/smulgP=> h q Hh Hq ->; rewrite pQhq ?mulgK.
have GrH: forall x, x \in G -> rH x \in G.
  by move=> x Gx; rewrite -(groupMr _ (groupVr Gx)) (subsetP sHG) -?rcosetE.
have rH_Pmul: forall x y, x \in P -> rH (x * y) = pQ x * rH y.
  by move=> x y Px; rewrite /rH mulgA -pQmul // /pP rPmul // mulgA.
have rH_Hmul: forall h y, h \in H -> rH (h * y) = rH y.
  by move=> h y Hh; rewrite rH_Pmul ?(subsetP sHP) // -(mulg1 h) pQhq // mul1g.
pose toH x : {x' | x' \in H} := insubd (exist [eta mem H] _ (group1 H)) x.
have valH: {in H, cancel toH val} by move=> *; exact: insubdK.
pose Hgrp := {{x | x \in H} as finGroupType}.
have mulHC : commutative (@mulg Hgrp).
  move=> x y; apply/eqP; have:= subsetP abelH _ (valP x).
  by rewrite setE (valP x); move/subsetP; apply; exact: valP.
pose eltH := Ring.AdditiveGroup (@mulgA _) mulHC (@mul1g _) (@mulVg _).
have Hval: forall u : eltH, val u \in H by exact: valP.
have valM: forall a b : eltH, val (a + b)%R = val a * val b by [].
have valE: forall (a : eltH) n, val (a*+n)%R = val a ** n.
  by move=> a; elim=> //= n <-.
pose mu x y : eltH := toH ((rH x * rH y)^-1 * rH (x * y)).
pose nu y := (\sum_(Px \in rcosets P G) mu (repr Px) y)%R.
have rHmul : forall x y,
  x \in G -> y \in G -> rH (x * y) = rH x * rH y * val (mu x y).
- move=> x y Gx Gy; rewrite valH ?mulKgv // -lcosetE lcoset_sym.
  rewrite -norm_rlcoset; last by rewrite (subsetP nHG) ?GrH ?groupM.
  rewrite -(rcoset_trans1 (HrH _)) -rcoset_mul ?(subsetP nHG) ?GrH //.
  by apply/smulgP; exists (rH x) (rH y).
have mu_Pmul: forall x y z, x \in P -> mu (x * y) z = mu y z.
  move=> x y z Px; congr toH; rewrite -mulgA !(rH_Pmul x) ?rPmul //.
  by rewrite -mulgA invg_mul -mulgA mulKg.
have mu_Hmul: forall x y z, x \in G -> y \in H -> mu x (y * z) = mu x z.
  move=> x y z Gx Hy; congr toH.
  rewrite (mulgA x) (conjgCv x) -mulgA 2?rH_Hmul //.
  by rewrite norm_conjg // groupV (subsetP nHG).
have{mu_Hmul} nu_Hmul: forall y z, y \in H -> nu (y * z) = nu z.
  move=> y z Hy; apply: eq_bigr => Px; case/imsetP=> x Gx ->{Px}.
  apply: mu_Hmul y z _ Hy.
  by rewrite -(groupMl _ (subsetP sPG _ (PpP x))) mulgKv.
pose actG (a : eltH) y : eltH := toH (val a ^ rH y).
have valG: forall a y, y \in G -> val (actG a y) = val a ^ rH y.
  move=> a y Gy; rewrite valH // -sconjgE norm_sconjg ?Hval //=.
  by rewrite groupV (subsetP nHG) // GrH.
have actG0: forall y, y \in G -> (actG 0 y = 0)%R.
  by move=> y Gy; apply: val_inj; rewrite valG //= conj1g.
have actGM: forall a b y, y \in G -> (actG (a + b) y = actG a y + actG b y)%R.
  by move=> a b y Gy; apply: val_inj; rewrite /= !valG //= conjg_mul.
have actGE: forall a n y, y \in G -> (actG (a*+n) y = (actG a y)*+n)%R.
  by move=> a n y Gy; apply: val_inj; rewrite !(valE, valG) // gexpn_conjg.
have cocycle_mu: forall x y z, x \in G -> y \in G -> z \in G ->
  (mu (x * y)%G z + actG (mu x y) z = mu y z + mu x (y * z)%G)%R.
- move=> x y z Gx Gy Gz; apply: val_inj.
  apply: (mulg_injl (rH x * rH y * rH z)).
  rewrite Ring.addrC !valM valG // -mulgA (mulgA (rH z)).
  rewrite -conjgC 3!mulgA -!rHmul ?groupM //.
  by rewrite -2!(mulgA (rH x)) -mulgA -!rHmul ?groupM //.
move: mu => mu in rHmul mu_Pmul cocycle_mu nu nu_Hmul; pose iP := indexg P G.
have{actG0 actGM cocycle_mu} cocycle_nu : forall y z, y \in G -> z \in G ->
  (nu z + actG (nu y) z = (mu y z)*+iP + nu (y * z)%G)%R.
- move=> y z Gy Gz; pose ap := (@Ring.add eltH); pose am a := actG a z.
  rewrite -/(am (nu y)) (@big_morph _ _ 0 0 _ ap)%R {}/ap {}/am; last first.
    by split=> [|x1 x2] /=; auto.
  have ->: (nu z = \sum_(Px \in rcosets P G) mu (repr Px * y)%G z)%R.
    rewrite /nu (reindex (fun Px => Px :* y)) /=; last first.
      exists (fun Px => Px :* y^-1) => Px _;
      by rewrite -rcoset_morph (mulgV, mulVg) rtrans_1.
    symmetry; apply: eq_big => Px.
       apply/imsetP/imsetP=> [] [x Gx] eq_Px.
         by exists (x * y); rewrite ?groupMl // rcoset_morph eq_Px.
       exists (x * y^-1); first by rewrite groupMl ?groupV.
       by rewrite rcoset_morph -eq_Px -rcoset_morph mulgV rtrans_1.
    case/imsetP=> x Gx ->{Px}; rewrite -rcoset_morph.
    case: repr_rcosetP=> p1 Pp1; case: repr_rcosetP=> p2 Pp2.
    by rewrite -mulgA [x * y]lock !mu_Pmul.
  rewrite -sumr_const -!big_split /=; apply: eq_bigr => Px.
  case/imsetP=> x Gx ->{Px}; rewrite -cocycle_mu //.
  by case: repr_rcosetP=> p1 Pp1; rewrite groupMr // (subsetP sPG).
have [m mK]: exists m, forall a : eltH, (a*+(iP * m) = a)%R.
  pose n := #|P|; have n_p: n = p_part p #|G| by apply/eqP; case/andP: sylP.
  case: (@bezoutl iP n)=> [|m' _].
     rewrite lt0n; apply/pred0Pn.
     by exists (P :* 1); apply/imsetP; exists (1 : elt).
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
    by exists (triv_morph elt elt); exact: trivm_is_cst.
  have domf: dom f = G.
    apply/setP=> x; rewrite 2!setE {2}/f orbC.
    case Gx: (x \in G).
      case: eqP => // eq_rHx; apply: (subsetP kerf).
      rewrite -groupV -(mulg1 x^-1) -eq_rHx mulgA groupMr ?Hval //.
      by rewrite -lcosetE -norm_rlcoset ?(subsetP nHG).
    rewrite eqxx; apply/kerP=> in_ker.
    case/existsP: triv_f=> y; case/eqP.
    case Gy: (y \in G); last by rewrite /f Gy.
    by rewrite -in_ker /f groupMr // Gx.
  have gdomf: group_set (dom f) by rewrite domf set_of_groupP.
  by rewrite -domf in morf; exists (Morphism gdomf morf).
exists {phi @: G as group _}.
  apply/subsetP=> x; case/setIP=> Hx; case/imsetP=> y Gy eq_x; apply/set1P.
  move: Hx; rewrite {x}eq_x -phi_f {1}/f Gy groupMr ?Hval //.
  rewrite -{1}(mulgKv y (rH y)) groupMl -?rcosetE // -{2}(mulg1 y).
  by move/(subsetP kerf); move/kerP->; rewrite phi_f morph1.
apply/setP=> x; apply/smulgP/idP=> [[h y Hh phi_y ->{x}] | Gx].
  rewrite groupMl; last exact: (subsetP sHG).
  case/imsetP: phi_y => z Gz ->{x Hx y}.
  by rewrite -phi_f /f Gz groupMl ?GrH // (subsetP sHG) ?valP.
exists (x * (phi x)^-1) (phi x); last first; first by rewrite mulgKv.
  by apply/imsetP; exists x. 
rewrite -phi_f /f Gx -groupV invg_mul invgK -mulgA (conjgC (val _)) mulgA.
by rewrite groupMl ?norm_conjg -?rcosetE // (valP, groupV) ?(subsetP nHG).
Qed.

Definition hall (elt : finGroupType) (G H : {set elt}) :=
  (H \subset G) && coprime #|H| (#|G| %/ #|H|).

Lemma sylow_hall : forall (elt : finGroupType) (G P : {group elt}) p,
  prime p -> sylow p G P -> hall G P.
Proof.
move=> elt G P p prime_p; case/andP=> sPG sylP; rewrite /hall sPG /=.
case: (p_part_coprime prime_p (pos_card_group G)) => n' co_p_n' ->.
rewrite /p_part -(eqP sylP) divn_mull ?pos_card_group // (eqP sylP).
by case: (logn _ _) => [|k]; rewrite ?coprime_expl // /coprime gcdnC.
Qed.

Theorem SchurZass_split : forall (elt : finGroupType) (G H : {group elt}),
  hall G H -> H <| G -> splitg G H.
Proof.
move=> elt G; move: {2}_.+1 (ltnSn #|G|) => n.
elim: n elt G => // n IHn elt G; rewrite ltnS => Gn H.
case: (leqP #|H| 1%N) => [trivH _ _ | ntrivH].
  have: trivg H.
    apply/subsetP=> x Hx; rewrite setE; apply/idPn=> nx1.
    by rewrite (cardD1 1) group1 (cardD1 x) inE /= Hx nx1 in trivH.
  move/trivgP->; apply/splitgP; exists G; [exact: subsetIl | exact: smul1g].
have:= (prime_pdiv ntrivH); set p := pdiv _ => prime_p.
case: (sylow1_cor H prime_p) => // P sylP hallH nHG.
have sHG: H \subset G by case/andP: hallH.
case nPG: (P <| G); last first.
  pose N := {normaliser P :&: G as group _}.
  have sNG: N \subset G by rewrite subsetIr.
  have eqHN_G: H :*: N = G by exact: Frattini sylP.
  pose H' := {H :&: N as group _}.
  have nH'N: H' <| N.
    apply/subsetP=> x Nx; rewrite setE; apply/subsetP=> y.
    rewrite 2!setE -sconjgE invgK /conjg groupMr ?groupMl ?groupV //= -/N.
    by rewrite (normalP _ _ nHG) => [?|]; rewrite 1?setE // (subsetP sNG).
  have eq_iH: #|G| %/ #|H| = #|N| %/ #|H'|.
    rewrite -(divn_pmul2l (pos_card_group H')) mulnC -eqHN_G card_smulg.
    by rewrite (mulnC #|H'|) divn_pmul2l // pos_card_group.
  have hallH': hall N H'.
    have sH'H: H' \subset H by exact: subsetIl.
    case/andP: hallH => _; rewrite eq_iH -(LaGrange sH'H) coprime_mull.
    by rewrite /hall subsetIr; case/andP.
  have: splitg N H'; last case/splitgP=> K trKN eqH'K.
    apply: IHn hallH' nH'N; apply: {n}leq_trans Gn.
    rewrite ltn_neqAle subset_leq_card // andbT; apply/eqP=> eqNG.
    case/negP: nPG; suff <-: (N = G :> set _) by exact: subsetIl.
    by apply/setP; exact/subset_cardP.
  have sKN: K \subset N by rewrite -(smul1g K) -eqH'K smulsg ?subset_set1.
  apply/splitgP; exists K.
    apply/subsetP=> x; case/setIP=> Hx Kx; apply: (subsetP trKN).
    by rewrite 2!setE Hx (subsetP sKN) Kx.
  apply/setP; apply/subset_eqP; apply/andP; split; first by rewrite -eqHN_G smulgs.
  by rewrite -eqHN_G -eqH'K smulgA smulsg // -{2}(smulgg H) smulgs // subsetIl.
pose Z := {center P as group _}; have iZ: center P = Z by [].
have sZP: Z \subset P by exact: subset_center.
have sZH: Z \subset H by case/andP: sylP; move/(subset_trans sZP).
have sZG: Z \subset G by exact: subset_trans sHG.
have nZG: Z <| G.
  apply/subsetP=> x Gx; rewrite setE; apply/subsetP=> z.
  rewrite !setE -sconjgE invgK (normalP _ _ nPG) //.
  case Pz: (z \in P) => //=; move/subsetP=> Cz; apply/subsetP=> y.
  rewrite -{1}(conjgKv x y) -sconjgE (normalP _ _ nPG) ?groupV //.
  by move/Cz; move/eqP; rewrite -!conjg_mul; move/conjg_inj; move/eqP.
have nZH: Z <| H by exact: normal_subset sHG.
pose Gbar := {G / Z as group _}; have iGbar: G / Z = Gbar by [].
pose Hbar := {H / Z as group _}; have iHbar: H / Z = Hbar by [].
have nHGbar: Hbar <| Gbar.
  apply/normalP=> xbar; case/imsetP=> x Gx ->{xbar}.
  have sGdom := subset_trans nZG (subset_dom_coset _).
  by rewrite -imset_conj (normalP _ _ nHG, subset_trans sHG, subsetP sGdom).
have hallHbar: hall Gbar Hbar.
  rewrite /hall subset_imset //= -[center P]/(Z : set _) /center.
  rewrite !card_quotient // -(divn_pmul2l (pos_card_group Z)) !LaGrange //.
  by case/andP: hallH => _; rewrite -{1}(LaGrange sZH) coprime_mull; case/andP.
have: splitg Gbar Hbar; last case/splitgP=> Kbar trHKbar eqHKbar. 
  apply: IHn => //; apply: {n}leq_trans Gn.
  rewrite card_quotient // -(group_divn sZG) divn_lt ?pos_card_group //.
  apply: (leq_trans (prime_gt1 prime_p)).
  apply: dvdn_leq; first exact: pos_card_group.
  have toA: forall x y z: elt, x ^ (y * z) = (x ^ y) ^ z.
     by move=> *; rewrite conjg_conj.
  pose to := @Action _ _ (fun x y => x ^ y) (@conjg1 _) toA.
  have eqZ: Z =i predI (act_fix to P) (mem P).
    move=> z; rewrite /= inE /= !setE -(andbC (z \in P)).
    case: (z \in P) => //=.
    apply/subsetP/eqP=> [Cz | <- x].
      apply/setP=> x; rewrite setE; case Px: (x \in P) => //=.
      apply/conjg_fpP; exact: Cz.
    by rewrite setE; case/andP=> _; move/conjg_fpP.
  case/andP: sylP => _; move/eqP=> cPp.
  rewrite {eqZ}(eq_card eqZ) /dvdn -(mpl prime_p cPp) => [|x y].
    rewrite cPp; apply/dvdn_exp_prime=> //; exists 1%N; last by rewrite expn1.
    by rewrite -dvdn_exp_max //= expn1 dvdn_pdiv.
  by case/imsetP=> z Pz ->; rewrite /= /conjg groupMr ?groupMl ?groupV.
have [ZK [sZZK sZKG] quoZK]:
  exists2 ZK : group elt, Z \subset ZK /\ ZK \subset G & ZK / Z = Kbar.
- exists [group of mpreim (coset_of Z) Kbar :&: G]; rewrite /= mpreimUker //.
    split; last exact: subsetIr.
    apply/subsetP=> x Zz; rewrite 2!setE (subsetP sZG) // andbT.
    apply/orP; right; exact: (subsetP (subset_ker_coset _)).    
  apply/setP=> xbar; apply/imsetP/idP=> [[x ZKx ->{xbar}] | Kxbar].
    case/setIP: ZKx; case/setUP; first by rewrite !setE; case/andP.
    move/mker=> -> _; exact: group1.
  have: xbar \in Gbar by rewrite -eqHKbar (subsetP (smulg_subr _ _)).
  case/quotientP=> x [Gx Nx eq_xbar]; exists x => //=.
  rewrite 4!setE -eq_xbar Gx Kxbar !andbT; case: eqP => //= kx.
  by apply/kerMP; rewrite ?(subsetP (subset_dom_coset _)) //= -eq_xbar.
have nZZK: Z <| ZK by exact: normal_subset sZKG.
have cardZK: #|ZK| = (#|Z| * indexg H G)%N.
  rewrite -(LaGrange sZZK); congr muln; rewrite -card_quotient // quoZK.
  rewrite -(group_divn sHG) -(LaGrange sZG) -(LaGrange sZH) divn_pmul2l //.
  rewrite -!card_quotient // iGbar -eqHKbar disjoint_card_smulg //.
  by rewrite divn_mulr.
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
    exists {[set 1] as group elt}; [exact: subsetIr | exact: smulg1].
  apply/subsetP=> z Zz; rewrite setE Zz; apply: (subset_trans sZP).
  by rewrite setE in Zz; case/andP: Zz.
have sKZK: K \subset ZK by rewrite -(smul1g K) -eqZK smulsg ?subset_set1.
have trHK: disjointg H K.
  apply/subsetP=> x; case/setIP=> Hx Kx; apply: (subsetP trZK).
  have Gx: x \in G by exact: (subsetP sHG).
  suff: x \in ker_(G) (coset_of Z) by rewrite ker_coset_of_loc // !setE Kx Gx.
  rewrite setE Gx andbT; apply/kerMP.
    by rewrite (subsetP (subset_dom_coset Z)) // (subsetP nZG).
  suff: coset_of Z x \in [set 1] by move/set1P.
  apply: (subsetP trHKbar); rewrite -quoZK.
  by apply/setIP; split; apply/imsetP; exists x; rewrite // (subsetP sKZK).
apply/splitgP; exists K => //; apply/setP; apply/subset_cardP.
  rewrite disjoint_card_smulg // -(@divn_mulr #|K| #|Z|) //.
  by rewrite -disjoint_card_smulg // eqZK cardZK divn_mulr // LaGrange.
apply/subsetP=> hk; case/smulgP=> h k Hh Kk ->{zk}.
by rewrite (groupMl _ (subsetP sHG h Hh)) (subsetP sZKG) // (subsetP sKZK).
Qed.


