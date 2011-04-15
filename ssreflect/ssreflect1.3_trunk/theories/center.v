(* (c) Copyright Microsoft Corporation and Inria. All rights reserved. *)
Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq div fintype bigop.
Require Import finset fingroup morphism perm automorphism quotient action.
Require Import gproduct gfunctor cyclic.

(******************************************************************************)
(* Definition of the center of a group and of external central products:      *)
(*           'Z(G) == the center of the group G, i.e., 'C_G(G).               *)
(*   cprod_by isoZ == the finGroupType for the central product of H and K     *)
(*                    with centers identified by the isomorphism gz on 'Z(H); *)
(*                    here isoZ : isom 'Z(H) 'Z(K) gz. Note that the actual   *)
(*                    central product is [set: cprod_by isoZ].                *)
(*    cpairg1 isoZ == the isomorphism from H to cprod_by isoZ, isoZ as above. *)
(*    cpair1g isoZ == the isomorphism from K to cprod_by isoZ, isoZ as above. *)
(*      xcprod H K == the finGroupType for the external central product of H  *)
(*                    and K with identified centers, provided the dynamically *)
(*                    tested condition 'Z(H) \isog 'Z(K) holds.               *)
(*      ncprod H n == the finGroupType for the central product of n copies of *)
(*                    H with their centers identified; [set: ncprod H 0] is   *)
(*                    isomorphic to 'Z(H).                                    *)
(*  xcprodm cf eqf == the morphism induced on cprod_by isoZ, where as above   *)
(*                    isoZ : isom 'Z(H) 'Z(K) gz, by fH : {morphism H >-> rT} *)
(*                    and fK : {morphism K >-> rT}, given both                *)
(*                    cf : fH @* H \subset 'C(fK @* K) and                    *)
(*                    eqf : {in 'Z(H), fH =1 fK \o gz}.                       *)
(*   Following Aschbacher, we only provide external central products with     *)
(* identified centers, as these are well defined provided the local center    *)
(* isomorphism group of one of the subgroups is full. Nevertheless the        *)
(* entire construction could be carried out under the weaker assumption that  *)
(* gz is an isomorphism between subgroups of 'Z(H) and 'Z(K), and even the    *)
(* uniqueness theorem holds under the weaker assumption that gz map 'Z(H) to  *)
(* a characteristic subgroup of 'Z(K) not isomorphic to any other subgroup of *)
(* 'Z(K), a condition that holds for example when K is cyclic, as in the      *)
(* structure theorem for p-groups of symplectic type.                         *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GroupScope.

Section Defs.

Variable gT : finGroupType.

Definition center (A : {set gT}) := 'C_A(A).

Canonical Structure center_group (G : {group gT}) : {group gT} :=
  Eval hnf in [group of center G].

End Defs.

Notation "''Z' ( A )" := (center A) : group_scope.
Notation "''Z' ( H )" := (center_group H) : subgroup_scope.

Lemma morphim_center : GFunctor.pcontinuous center.
Proof. move=> gT rT G D f; exact: morphim_subcent. Qed.

Canonical Structure center_igFun :=
  [igFun by fun _ _ => subsetIl _ _ & morphim_center].
Canonical Structure center_gFun := [gFun by morphim_center].
Canonical Structure center_pgFun := [pgFun by morphim_center].

Section Center.

Variables gT : finGroupType.
Implicit Type rT : finGroupType.
Implicit Types x y : gT.
Implicit Types A B : {set gT}.
Implicit Types G H K D : {group gT}.

Lemma subcentP : forall A B x,
  reflect (x \in A /\ centralises x B) (x \in 'C_A(B)).
Proof.
move=> A B x; rewrite inE. case: (x \in A); last by right; case.
by apply: (iffP centP) => [|[]].
Qed.

Lemma subcent_sub : forall A B, 'C_A(B) \subset 'N_A(B).
Proof. by move=> A B; rewrite setIS ?cent_sub. Qed.

Lemma subcent_norm : forall G B, 'N_G(B) \subset 'N('C_G(B)).
Proof. by move=> G B; rewrite normsI ?subIset ?normG // orbC cent_norm.  Qed.

Lemma subcent_normal : forall G B, 'C_G(B) <| 'N_G(B).
Proof. by move=> G B; rewrite /normal subcent_sub subcent_norm. Qed.

Lemma subcent_char : forall G H K, H \char G -> K \char G -> 'C_H(K) \char G.
Proof.
move=> G H K; case/charP=> sHG chHG; case/charP=> sKG chKG; apply/charP.
split=> [|f injf Gf]; first by rewrite subIset ?sHG.
by rewrite injm_subcent ?chHG ?chKG.
Qed.

Lemma centerP : forall A x,
  reflect (x \in A /\ centralises x A) (x \in 'Z(A)).
Proof. move=> A x; exact: subcentP. Qed.

Lemma center_sub : forall A, 'Z(A) \subset A.
Proof. move=> A; exact: subsetIl. Qed.

Lemma center1 : 'Z(1) = [1 gT].
Proof. by apply/eqP; rewrite eqEsubset center_sub sub1G. Qed.

Lemma centerC : forall A, {in A, centralised 'Z(A)}.
Proof. by move=> A; apply/centsP; rewrite centsC subsetIr. Qed.

Lemma center_normal : forall G, 'Z(G) <| G.
Proof. exact: gFnormal. Qed.

Lemma sub_center_normal : forall H G, H \subset 'Z(G) -> H <| G.
Proof.
by move=> H G; rewrite subsetI centsC /normal; case/andP=> ->; move/cents_norm.
Qed.

Lemma center_abelian : forall G, abelian 'Z(G).
Proof.
by move=> P; rewrite /abelian subIset // centsC subIset // subxx orbT.
Qed.

Lemma center_char : forall G, 'Z(G) \char G.
Proof. exact: gFchar. Qed.

Lemma center_idP : forall A, reflect ('Z(A) = A) (abelian A).
Proof. by move=> A; exact: setIidPl. Qed.

Lemma subcent1P : forall A x y,
  reflect (y \in A /\ commute x y) (y \in 'C_A[x]).
Proof.
move=> A x y; rewrite inE; case: (y \in A); last by right=> [[]].
by apply: (iffP cent1P) => [|[]].
Qed.

Lemma subcent1_id : forall x G, x \in G -> x \in 'C_G[x].
Proof. move=> x G Gx; rewrite inE Gx; exact/cent1P. Qed.

Lemma subcent1_sub : forall x G, 'C_G[x] \subset G.
Proof. move=> x G; exact: subsetIl. Qed.

Lemma subcent1C : forall x y G, x \in G -> y \in 'C_G[x] -> x \in 'C_G[y].
Proof. by move=> x y G Gx; case/subcent1P=> *; apply/subcent1P. Qed.

Lemma subcent1_cycle_sub : forall x G, x \in G -> <[x]> \subset 'C_G[x].
Proof. by move=> x G Gx; rewrite cycle_subG ?subcent1_id. Qed.

Lemma subcent1_cycle_norm : forall x G, 'C_G[x] \subset 'N(<[x]>).
Proof. by move=> x G; rewrite cents_norm // cent_gen cent_set1 subsetIr. Qed.

Lemma subcent1_cycle_normal : forall x G, x \in G -> <[x]> <| 'C_G[x].
Proof.
by move=> x G Gx; rewrite /normal subcent1_cycle_norm subcent1_cycle_sub.
Qed.

(* Gorenstein. 1.3.4 *)
Lemma cyclic_center_factor_abelian : forall G, cyclic (G / 'Z(G)) -> abelian G.
Proof.
move=> G; case/cyclicP=> a Ga; case: (cosetP a) => /= z Nz def_a.
have G_Zz: G :=: 'Z(G) * <[z]>.
  rewrite -quotientK ?cycle_subG ?quotient_cycle //=.
  by rewrite -def_a -Ga quotientGK // center_normal.
rewrite G_Zz abelianM cycle_abelian center_abelian subIset ?centS ?orbT //.
by rewrite G_Zz mulG_subr.
Qed.

Lemma cyclic_factor_abelian : forall H G,
  H \subset 'Z(G) -> cyclic (G / H) -> abelian G.
Proof.
move=> H G sHZ cycGH; apply: cyclic_center_factor_abelian.
have nG : G \subset 'N(_) := normal_norm (sub_center_normal _).
have [f <-]:= homgP (homg_quotientS (nG _ sHZ) (nG _ (subxx _)) sHZ).
exact: morphim_cyclic.
Qed.

Section Injm.

Variables (rT : finGroupType) (D : {group gT}) (f : {morphism D >-> rT}).

Hypothesis injf : 'injm f.

Lemma injm_center : forall G, G \subset D -> f @* 'Z(G) = 'Z(f @* G).
Proof. by move=> G; exact: injm_subcent. Qed.

End Injm.

End Center.

Implicit Arguments center_idP [gT A].

Lemma isog_center : forall (aT rT : finGroupType),
  forall (G : {group aT}) (H : {group rT}), G \isog H -> 'Z(G) \isog 'Z(H).
Proof. exact: gFisog. Qed.

Section Product.

Variable gT : finGroupType.
Implicit Types G H K : {group gT}.
Implicit Types A B C : {set gT}.

Lemma center_prod : forall H K,
  K \subset 'C(H) -> 'Z(H) * 'Z(K) = 'Z(H * K).
Proof.
move=> H K cHK; apply/setP=> z; rewrite {3}/center centM !inE.
have cKH: H \subset 'C(K) by rewrite centsC.
apply/imset2P/and3P=> [[x y]| []].
  case/setIP=> Hx cHx; case/setIP=> Ky cKy -> {z}.
  by rewrite mem_imset2 ?groupM // ?(subsetP cHK) ?(subsetP cKH).
case/imset2P=> x y Hx Ky ->{z}.
rewrite groupMr => [cHx|]; last exact: subsetP Ky.
rewrite groupMl => [cKy|]; last exact: subsetP Hx.
by exists x y; rewrite ?inE ?Hx ?Ky.
Qed.

Lemma center_cprod : forall A B G, A \* B = G -> 'Z(A) \* 'Z(B) = 'Z(G).
Proof.
move=> A B G; case/cprodP => [[H K -> ->] <- cHK].
rewrite cprodE ?center_prod //= subIset ?(subset_trans cHK) //.
by rewrite centS ?center_sub.
Qed.

Lemma center_bigcprod : forall I r P (F : I -> {set gT}) G,
  \big[cprod/1]_(i <- r | P i) F i = G
  -> \big[cprod/1]_(i <- r | P i) 'Z(F i) = 'Z(G).
Proof.
move=> I r P F; pose R A C := forall G, A :=: G -> C = 'Z(G).
apply (big_rel R) => [_ <-|A B C D IHA IHB G dG|_ _ G ->]; rewrite ?center1 //.
case/cprodP: dG IHA IHB (dG) => [[H K -> ->] _ _] IHH IHK dG.
by rewrite (IHH H) // (IHK K) // (center_cprod dG).
Qed.

Lemma cprod_center_id : forall G, G \* 'Z(G) = G.
Proof. by move=> G; rewrite cprodE ?subsetIr // mulGSid ?center_sub. Qed.

Lemma center_dprod : forall A B G, A \x B = G -> 'Z(A) \x 'Z(B) = 'Z(G).
Proof.
move=> A B G; case/dprodP=> [[H1 H2 -> ->] defG cH12 trH12].
move: defG; rewrite -cprodE //; move/center_cprod.
case/cprodP=> _ /= <- cZ12; apply: dprodE => //=.
by rewrite setIAC setIA -setIA trH12 (setIidPl _) ?sub1G.
Qed.

Lemma center_bigdprod : forall I r P (F: I -> {set gT}) G,
  \big[dprod/1]_(i <- r | P i) F i = G
    -> \big[dprod/1]_(i <- r | P i) 'Z(F i) = 'Z(G).
Proof.
move=> I r P F; pose R A C := forall G, A :=: G -> C = 'Z(G).
apply (big_rel R) => [_ <-|A B C D IHA IHB G dG|_ _ G ->]; rewrite ?center1 //.
case/dprodP: dG IHA IHB (dG) => [[H K -> ->] _ _ _] IHH IHK dG.
by rewrite (IHH H) // (IHK K) // (center_dprod dG).
Qed.

Lemma Aut_cprod_full : forall G H K,
    H \* K = G -> 'Z(H) = 'Z(K) ->
    Aut_in (Aut H) 'Z(H) \isog Aut 'Z(H) ->
    Aut_in (Aut K) 'Z(K) \isog Aut 'Z(K) ->
  Aut_in (Aut G) 'Z(G) \isog Aut 'Z(G).
Proof.
move=> G H K defG eqZHK; have [_ defHK cHK] := cprodP defG.
have defZ: 'Z(G) = 'Z(H) by rewrite -defHK -center_prod // eqZHK mulGid.
have ziHK: H :&: K = 'Z(K).
  by apply/eqP; rewrite eqEsubset subsetI -{1 2}eqZHK !center_sub setIS.
have AutZP := Aut_sub_fullP (@center_sub gT _).
move/AutZP=> AutZHfull; move/AutZP=> AutZKfull; apply/AutZP=> g injg gZ.
have [gH [def_gH ker_gH _ im_gH]] := domP g defZ.
have [gK [def_gK ker_gK _ im_gK]] := domP g (etrans defZ eqZHK).
have [injgH injgK]: 'injm gH /\ 'injm gK by rewrite ker_gH ker_gK.
have [gHH gKK]: gH @* 'Z(H) = 'Z(H) /\ gK @* 'Z(K) = 'Z(K).
  by rewrite im_gH im_gK -eqZHK -defZ.
have [|fH [injfH im_fH fHZ]] := AutZHfull gH injgH.
  by rewrite im_gH /= -defZ.
have [|fK [injfK im_fK fKZ]] := AutZKfull gK injgK.
  by rewrite im_gK /= -eqZHK -defZ.
have cfHK: fK @* K \subset 'C(fH @* H) by rewrite im_fH im_fK.
have eq_fHK: {in H :&: K, fH =1 fK}.
  by move=> z; rewrite ziHK => Zz; rewrite fHZ ?fKZ /= ?eqZHK // def_gH def_gK.
exists (cprodm_morphism defG cfHK eq_fHK).
rewrite injm_cprodm injfH injfK im_cprodm im_fH im_fK defHK.
rewrite -morphimIdom ziHK -eqZHK injm_center // im_fH eqxx.
split=> //= z; rewrite {1}defZ => Zz; have [Hz _] := setIP Zz.
by rewrite cprodmEl // fHZ // def_gH.
Qed.

End Product.

Section CprodBy.

Variables gTH gTK : finGroupType.
Variables (H : {group gTH}) (K : {group gTK}) (gz : {morphism 'Z(H) >-> gTK}).

Definition ker_cprod_by of isom 'Z(H) 'Z(K) gz :=
  [set xy | let: (x, y) := xy in (x \in 'Z(H)) && (y == (gz x)^-1)].

Hypothesis isoZ : isom 'Z(H) 'Z(K) gz.
Let kerHK := ker_cprod_by isoZ.

Let injgz : 'injm gz. Proof. by case/isomP: isoZ. Qed.
Let gzZ : gz @* 'Z(H) = 'Z(K). Proof. by case/isomP: isoZ. Qed.
Let gzZchar : gz @* 'Z(H) \char 'Z(K). Proof. by rewrite gzZ char_refl. Qed.
Let sgzZZ : gz @* 'Z(H) \subset 'Z(K) := char_sub gzZchar.
Let sZH := center_sub H.
Let sZK := center_sub K.
Let sgzZG : gz @* 'Z(H) \subset K := subset_trans sgzZZ sZK.

Lemma ker_cprod_by_is_group : group_set kerHK.
Proof.
apply/group_setP; rewrite inE /= group1 morph1 invg1 /=.
split=> // [[x1 y1] [x2 y2]].
rewrite inE /=; case/andP=> Zx1; move/eqP->; have [_ cGx1] := setIP Zx1.
rewrite inE /=; case/andP=> Zx2; move/eqP->; have [Gx2 _] := setIP Zx2.
by rewrite inE /= groupM //= -invMg (centP cGx1) // morphM.
Qed.
Canonical Structure ker_cprod_by_group := Group ker_cprod_by_is_group.

Lemma ker_cprod_by_central : kerHK \subset 'Z(setX H K).
Proof.
rewrite -(center_dprod (setX_dprod H K)) -morphim_pairg1 -morphim_pair1g.
rewrite -!injm_center ?subsetT ?injm_pair1g ?injm_pairg1 //=.
rewrite morphim_pairg1 morphim_pair1g setX_dprod.
apply/subsetP=> [[x y]]; rewrite inE; case/andP=> Zx; move/eqP->.
by rewrite inE /= Zx groupV (subsetP sgzZZ) ?mem_morphim.
Qed.

Definition cprod_by := locked (subFinGroupType [group of setX H K / kerHK]).
Local Notation C := [set: FinGroup.arg_sort (FinGroup.base cprod_by)].

Definition in_cprod : gTH * gTK -> cprod_by.
Proof. unlock cprod_by; exact: (subg _ \o coset kerHK). Defined.

Lemma in_cprodM : {in setX H K &, {morph in_cprod : u v / u * v}}.
Proof.
unlock in_cprod cprod_by => u v Gu Gv /=.
have nkerHKG := normal_norm (sub_center_normal ker_cprod_by_central).
by rewrite -!morphM ?mem_quotient // (subsetP nkerHKG).
Qed.
Canonical Structure in_cprod_morphism := Morphism in_cprodM.

Lemma ker_in_cprod : 'ker in_cprod = kerHK.
Proof.
have: 'ker (subg [group of setX H K / kerHK] \o coset kerHK) = kerHK.
  by rewrite ker_comp ker_subg -kerE ker_coset. 
apply: etrans; rewrite /ker /morphpre /=; unlock in_cprod cprod_by.
by rewrite ['N(kerHK) :&: _]quotientGK ?sub_center_normal ?ker_cprod_by_central.
Qed.

Lemma cpairg1_dom : H \subset 'dom (in_cprod \o @pairg1 gTH gTK).
Proof. by rewrite -sub_morphim_pre ?subsetT // morphim_pairg1 setXS ?sub1G. Qed.

Lemma cpair1g_dom : K \subset 'dom (in_cprod \o @pair1g gTH gTK).
Proof. by rewrite -sub_morphim_pre ?subsetT // morphim_pair1g setXS ?sub1G. Qed.

Definition cpairg1 := tag (restrmP _ cpairg1_dom).
Definition cpair1g := tag (restrmP _ cpair1g_dom).

Local Notation CH := (mfun cpairg1 @* gval H).
Local Notation CK := (mfun cpair1g @* gval K).

Lemma injm_cpairg1 : 'injm cpairg1.
Proof.
rewrite /cpairg1; case: restrmP => _ [_ -> _ _].
rewrite ker_comp ker_in_cprod; apply/subsetP=> x; rewrite 5!inE /=.
by case/and3P=> _ Zx; rewrite inE eq_sym (inv_eq invgK) invg1 morph_injm_eq1.
Qed.
Let injH := injm_cpairg1.

Lemma injm_cpair1g : 'injm cpair1g.
Proof.
rewrite /cpair1g; case: restrmP => _ [_ -> _ _].
rewrite ker_comp ker_in_cprod; apply/subsetP=> y; rewrite !inE /= morph1 invg1.
by case/and3P.
Qed.
Let injK := injm_cpair1g.

Lemma im_cpair_cent : CK \subset 'C(CH).
Proof.
rewrite /cpairg1 /cpair1g; do 2!case: restrmP => _ [_ _ _ -> //].
rewrite !morphim_comp morphim_cents // morphim_pair1g morphim_pairg1.
by case/dprodP: (setX_dprod H K).
Qed.
Hint Resolve im_cpair_cent.

Lemma im_cpair : CH * CK = C.
Proof.
rewrite /cpairg1 /cpair1g; do 2!case: restrmP => _ [_ _ _ -> //].
rewrite !morphim_comp -morphimMl morphim_pairg1 ?setXS ?sub1G //.
rewrite morphim_pair1g setX_prod morphimEdom /=; unlock in_cprod cprod_by.
by rewrite imset_comp imset_coset -morphimEdom im_subg.
Qed.

Lemma im_cpair_cprod : CH \* CK = C. Proof. by rewrite cprodE ?im_cpair. Qed.

Lemma eq_cpairZ : {in 'Z(H), cpairg1 =1 cpair1g \o gz}.
Proof.
rewrite /cpairg1 /cpair1g => z1 Zz1; set z2 := gz z1.
have Zz2: z2 \in 'Z(K) by rewrite (subsetP sgzZZ) ?mem_morphim.
have [[Gz1 _] [/= Gz2 _]]:= (setIP Zz1, setIP Zz2).
do 2![case: restrmP => f /= [df _ _ _]; rewrite {f}df].
apply/rcoset_kerP; rewrite ?inE ?group1 ?andbT //.
by rewrite ker_in_cprod mem_rcoset inE /= invg1 mulg1 mul1g Zz1 /=.
Qed.

Lemma setI_im_cpair : CH :&: CK = 'Z(CH).
Proof.
apply/eqP; rewrite eqEsubset setIS //=.
rewrite subsetI center_sub -injm_center //.
rewrite (eq_in_morphim _ eq_cpairZ); first by rewrite morphim_comp morphimS.
by rewrite !(setIidPr _) // -sub_morphim_pre.
Qed.

Lemma cpair1g_center : cpair1g @* 'Z(K) = 'Z(C).
Proof.
case/cprodP: (center_cprod im_cpair_cprod) => _ <- _.
by rewrite injm_center // -setI_im_cpair mulSGid //= setIC setIS 1?centsC.
Qed.

(* Uses gzZ. *)
Lemma cpair_center_id : 'Z(CH) = 'Z(CK).
Proof.
rewrite -!injm_center // -gzZ -morphim_comp; apply: eq_in_morphim eq_cpairZ.
by rewrite !(setIidPr _) // -sub_morphim_pre.
Qed.

(* Uses gzZ. *)
Lemma cpairg1_center : cpairg1 @* 'Z(H) = 'Z(C).
Proof. by rewrite -cpair1g_center !injm_center // cpair_center_id. Qed.

Section ExtCprodm.

Variable rT : finGroupType.
Variables (fH : {morphism H >-> rT}) (fK : {morphism K >-> rT}).
Hypothesis cfHK : fK @* K \subset 'C(fH @* H).
Hypothesis eq_fHK : {in 'Z(H), fH =1 fK \o gz}.

Let gH := ifactm fH injm_cpairg1.
Let gK := ifactm fK injm_cpair1g.

Lemma xcprodm_cent : gK @* CK \subset 'C(gH @* CH).
Proof. by rewrite !im_ifactm. Qed.

Lemma xcprodmI : {in CH :&: CK, gH =1 gK}.
Proof.
rewrite setI_im_cpair -injm_center // => fHx; case/morphimP=> x Gx Zx ->{fHx}.
by rewrite {2}eq_cpairZ //= ?ifactmE ?eq_fHK //= (subsetP sgzZG) ?mem_morphim.
Qed.

Definition xcprodm := cprodm im_cpair_cprod xcprodm_cent xcprodmI.
Canonical Structure xcprod_morphism := [morphism of xcprodm].

Lemma xcprodmEl : {in H, forall x, xcprodm (cpairg1 x) = fH x}.
Proof. by move=> x Hx; rewrite /xcprodm cprodmEl ?mem_morphim ?ifactmE. Qed.

Lemma xcprodmEr : {in K, forall y, xcprodm (cpair1g y) = fK y}.
Proof. by move=> y Ky; rewrite /xcprodm cprodmEr ?mem_morphim ?ifactmE. Qed.

Lemma xcprodmE :
  {in H & K, forall x y, xcprodm (cpairg1 x * cpair1g y) = fH x * fK y}.
Proof.
by move=> x y Hx Ky; rewrite /xcprodm cprodmE ?mem_morphim ?ifactmE.
Qed.

Lemma im_xcprodm : xcprodm @* C = fH @* H * fK @* K.
Proof. by rewrite -im_cpair morphim_cprodm // !im_ifactm. Qed.

Lemma im_xcprodml : forall A, xcprodm @* (cpairg1 @* A) = fH @* A.
Proof.
move=> A; rewrite -!(morphimIdom _ A) morphim_cprodml ?morphimS ?subsetIl //.
by rewrite morphim_ifactm ?subsetIl.
Qed.

Lemma im_xcprodmr : forall A, xcprodm @* (cpair1g @* A) = fK @* A.
Proof.
move=> A; rewrite -!(morphimIdom _ A) morphim_cprodmr ?morphimS ?subsetIl //.
by rewrite morphim_ifactm ?subsetIl.
Qed.

Lemma injm_xcprodm : 'injm xcprodm = 'injm fH && 'injm fK.
Proof.
rewrite injm_cprodm !ker_ifactm !subG1 !morphim_injm_eq1 ?subsetIl // -!subG1.
apply: andb_id2l => /= injfH; apply: andb_idr => _.
rewrite !im_ifactm // -(morphimIdom gH) setI_im_cpair -injm_center //.
rewrite morphim_ifactm // eqEsubset subsetI morphimS //=.
rewrite {1}injm_center // setIS //=.
rewrite (eq_in_morphim _ eq_fHK); first by rewrite morphim_comp morphimS.
by rewrite !(setIidPr _) // -sub_morphim_pre.
Qed.

End ExtCprodm.

(* Uses gzZchar. *)
Lemma Aut_cprod_by_full :
    Aut_in (Aut H) 'Z(H) \isog Aut 'Z(H) ->
    Aut_in (Aut K) 'Z(K) \isog Aut 'Z(K) ->
  Aut_in (Aut C) 'Z(C) \isog Aut 'Z(C).
Proof.
move=> AutZinH AutZinK.
have Cfull:= Aut_cprod_full im_cpair_cprod cpair_center_id.
by rewrite Cfull // -injm_center // injm_Aut_full ?center_sub.
Qed.

Section Isomorphism.

Let gzZ_lone : forall Y : {group gTK},
  Y \subset 'Z(K) -> gz @* 'Z(H) \isog Y -> gz @* 'Z(H) = Y.
Proof.
move=> Y sYZ isoY; apply/eqP.
by rewrite eq_sym eqEcard (card_isog isoY) gzZ sYZ /=.
Qed.

Variables (rT : finGroupType) (GH GK G : {group rT}).
Hypotheses (defG : GH \* GK = G) (ziGHK : GH :&: GK = 'Z(GH)).
Hypothesis AutZHfull : Aut_in (Aut H) 'Z(H) \isog Aut 'Z(H).
Hypotheses (isoGH : GH \isog H) (isoGK : GK \isog K).

(* Uses gzZ_lone *)
Lemma cprod_by_uniq :
  exists f : {morphism G >-> cprod_by},
    [/\ isom G C f, f @* GH = CH & f @* GK = CK].
Proof.
have [_ defGHK cGKH] := cprodP defG.
have AutZinH := Aut_sub_fullP sZH AutZHfull.
have [fH injfH defGH]:= isogP (isog_symr isoGH).
have [fK injfK defGK]:= isogP (isog_symr isoGK).
have sfHZfK: fH @* 'Z(H) \subset fK @* K.
  by rewrite injm_center //= defGH defGK -ziGHK subsetIr.
have gzZ_id: gz @* 'Z(H) = invm injfK @* (fH @* 'Z(H)).
  apply: gzZ_lone => /=.
    rewrite injm_center // defGH -ziGHK sub_morphim_pre /= ?defGK ?subsetIr //.
    by rewrite setIC morphpre_invm injm_center // defGK setIS 1?centsC.
  rewrite -morphim_comp.
  apply: isog_trans (sub_isog _ _); first by rewrite isog_sym sub_isog.
    by rewrite -sub_morphim_pre.
  by rewrite !injm_comp ?injm_invm.
have: 'dom (invm injfH \o fK \o gz) = 'Z(H).
  rewrite /dom /= -(morphpreIdom gz); apply/setIidPl.
  by rewrite -2?sub_morphim_pre // gzZ_id morphim_invmE morphpreK ?morphimS.
case/domP=> gzH [def_gzH ker_gzH _ im_gzH].
have{ker_gzH} injgzH: 'injm gzH by rewrite ker_gzH !injm_comp ?injm_invm.
have{AutZinH} [|gH [injgH gH_H def_gH]] := AutZinH _ injgzH.
  by rewrite im_gzH !morphim_comp /= gzZ_id !morphim_invmE morphpreK ?injmK.
have: 'dom (fH \o gH) = H by rewrite /dom /= -{3}gH_H injmK.
case/domP=> gfH [def_gfH ker_gfH _ im_gfH].
have{im_gfH} gfH_H: gfH @* H = GH by rewrite im_gfH morphim_comp gH_H.
have cgfHfK: fK @* K \subset 'C(gfH @* H) by rewrite gfH_H defGK.
have eq_gfHK: {in 'Z(H), gfH =1 fK \o gz}.
  move=> z Zz; rewrite def_gfH /= def_gH //= def_gzH /= invmK //.
  have {Zz}: gz z \in gz @* 'Z(H) by rewrite mem_morphim.
  rewrite gzZ_id morphim_invmE; case/morphpreP=> _.
  exact: (subsetP (morphimS _ _)).
pose f := xcprodm cgfHfK eq_gfHK.
have injf: 'injm f by rewrite injm_xcprodm ker_gfH injm_comp.
have fCH: f @* CH = GH by rewrite im_xcprodml gfH_H.
have fCK: f @* CK = GK by rewrite im_xcprodmr defGK.
have fC: f @* C = G by rewrite im_xcprodm gfH_H defGK defGHK.
have [f' [_ ker_f' _ im_f']] := domP (invm_morphism injf) fC.
exists f'; rewrite -fCH -fCK !{1}im_f' !{1}morphim_invm ?subsetT //.
by split=> //; apply/isomP; rewrite ker_f' injm_invm im_f' -fC im_invm.
Qed.

Lemma isog_cprod_by : G \isog C.
Proof. by have [f [isoG _ _]] := cprod_by_uniq; exact: isom_isog isoG. Qed.

End Isomorphism.

End CprodBy.

Section ExtCprod.
Import finfun.

Variables gTH gTK : finGroupType.
Variables (H : {group gTH}) (K : {group gTK}).

Let gt_ b := if b then gTK else gTH.
Local Notation isob := ('Z(H) \isog 'Z(K)) (only parsing).
Let G_ b := if b as b' return {group gt_ b'} then K else H.

Lemma xcprod_subproof :
  {gz : {morphism 'Z(H) >-> gt_ isob} | isom 'Z(H) 'Z(G_ isob) gz}.
Proof.
case: (pickP [pred f : {ffun _} | misom 'Z(H) 'Z(K) f]) => [f isoZ | no_f].
  rewrite (misom_isog isoZ); case/andP: isoZ => fM isoZ.
  by exists [morphism of morphm fM].
move/pred0P: no_f => not_isoZ; rewrite [isob](congr1 negb not_isoZ).
by exists (idm_morphism  _); apply/isomP; rewrite injm_idm im_idm.
Qed.

Definition xcprod := cprod_by (svalP xcprod_subproof).

Inductive xcprod_spec : finGroupType -> Prop :=
  XcprodSpec gz isoZ : xcprod_spec (@cprod_by gTH gTK H K gz isoZ).

Lemma xcprodP : 'Z(H) \isog 'Z(K) -> xcprod_spec xcprod.
Proof. by rewrite /xcprod => isoZ; move: xcprod_subproof; rewrite isoZ. Qed.

Lemma isog_xcprod : forall (rT : finGroupType) (GH GK G : {group rT}),
    Aut_in (Aut H) 'Z(H) \isog Aut 'Z(H) ->
    GH \isog H -> GK \isog K -> GH \* GK = G -> 'Z(GH) = 'Z(GK) ->
  G \isog [set: xcprod].
Proof.
move=> rT GH GK G AutZinH isoGH isoGK defG eqZGHK.
have [_ _ cGHK] := cprodP defG.
have [|gz isoZ] := xcprodP.
  have [[fH injfH <-] [fK injfK <-]] := (isogP isoGH, isogP isoGK).
  rewrite -!injm_center -?(isog_transl _ (sub_isog _ _)) ?center_sub //=.
  by rewrite eqZGHK sub_isog ?center_sub.
rewrite (isog_cprod_by _ defG) //.
by apply/eqP; rewrite eqEsubset setIS // subsetI {2}eqZGHK !center_sub.
Qed.

End ExtCprod.

Section IterCprod.

Variables (gT : finGroupType) (G : {group gT}).

Definition ncprod := locked (fix loop n : finGroupType :=
  if n is n'.+1 then xcprod G [set: loop n']
  else [finGroupType of subg_of 'Z(G)]).

Local Notation G_ n := [set: gsort (ncprod n)].

Lemma ncprod0 : G_ 0 \isog 'Z(G).
Proof. by unlock ncprod; rewrite isog_sym isog_subg. Qed.

Lemma center_ncprod0 : 'Z(G_ 0) = G_ 0.
Proof. by apply: center_idP; rewrite (isog_abelian ncprod0) center_abelian. Qed.

Lemma center_ncprod : forall n, 'Z(G_ n) \isog 'Z(G).
Proof.
elim=> [|n]; first by rewrite center_ncprod0 ncprod0.
unlock ncprod; move/isog_symr; case/xcprodP => gz isoZ.
by rewrite -cpairg1_center isog_sym sub_isog ?center_sub ?injm_cpairg1.
Qed.

Lemma ncprodS : forall n, xcprod_spec G [set: ncprod n] (ncprod n.+1).
Proof.
by move=> n; have:= xcprodP (isog_symr (center_ncprod n)); unlock ncprod.
Qed.

Lemma ncprod1 : G_ 1 \isog G.
Proof.
case: ncprodS => gz isoZ; rewrite isog_sym /= -im_cpair.
rewrite mulGSid /=; first by rewrite sub_isog ?injm_cpairg1.
rewrite -{3}center_ncprod0 injm_center ?injm_cpair1g //.
by rewrite -cpair_center_id center_sub.
Qed.

Lemma Aut_ncprod_full : forall n,
    Aut_in (Aut G) 'Z(G) \isog Aut 'Z(G) ->
  Aut_in (Aut (G_ n)) 'Z(G_ n) \isog Aut 'Z(G_ n).
Proof.
move=> n AutZinG; elim: n => [|n IHn].
  by rewrite center_ncprod0; apply/Aut_sub_fullP=> // g injg gG0; exists g.
by case: ncprodS => gz isoZ; exact: Aut_cprod_by_full.
Qed.

End IterCprod.

