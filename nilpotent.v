Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq div fintype.
Require Import bigops prime finset groups commutators automorphism.
Require Import morphisms normal center gprod gfunc.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Import GroupScope.

Section Defs.

Variables (n : nat) (gT : finGroupType) (A : {set gT}).

Definition lower_central_at_rec := iter n (fun B => [~: B, A]) A.

Definition upper_central_at_rec := iter n (fun B => coset B @*^-1 'Z(A / B)) 1.

Definition derived_at_rec := iter n (fun B => [~: B, B]) A.

Definition nilpotent :=
  forallb G : {group gT}, (G \subset A :&: [~: G, A]) ==> (G :==: 1).

Definition solvable :=
  forallb G : {group gT}, (G \subset A :&: [~: G, G]) ==> (G :==: 1).

End Defs.

(* 'nosimpl' MUST be used outside of a section -- the end of *)
(* section "cooking" destroys it.                            *)

Definition lower_central_at := nosimpl lower_central_at_rec.
Definition upper_central_at := nosimpl upper_central_at_rec.
Definition derived_at := nosimpl derived_at_rec.

Definition nil_class gT A :=
  index 1 (mkseq (fun n => @lower_central_at n gT A) #|A|).

Notation "''L_' n ( G )" := (lower_central_at n G)
  (at level 8, n at level 2, format "''L_' n ( G )") : group_scope.

Notation "''Z_' n ( G )" := (upper_central_at n G)
  (at level 8, n at level 2, format "''Z_' n ( G )") : group_scope.

Notation "G ^` ( n )" := (derived_at n G)
  (at level 8, format "G ^` ( n )") : group_scope.

Prenex Implicits nilpotent solvable nil_class.

Section LowerCentral.

Variable gT : finGroupType.
Notation sT := {set gT}.
Implicit Type A : {set gT}.
Implicit Type G H : {group gT}.

Lemma lcn0 : forall A, 'L_0(A) = A. Proof. by []. Qed.
Lemma lcnSn : forall A n, 'L_n.+1(A) = [~: 'L_n(A), A]. Proof. by []. Qed.
Lemma lcnE : forall A n, 'L_n(A) = lower_central_at_rec n A. Proof. by []. Qed.

Lemma lcn_group_set : forall G n, group_set 'L_n(G).
Proof. move=> G; elim=> *; exact: groupP. Qed.

Canonical Structure lower_central_at_group n G := Group (lcn_group_set G n).

Lemma lcn_char : forall G n, 'L_n(G) \char G.
Proof. by move=> G; elim=> [|n IHn]; rewrite ?lcnSn ?charR ?char_refl. Qed.

Lemma lcn_normal0 : forall G n, 'L_n(G) <|  G.
Proof. move=> G n; apply: char_normal; exact: lcn_char. Qed.

Lemma lcn_sub0 : forall G n, 'L_n(G) \subset G.
Proof. by move=> G n; case/andP: (lcn_normal0 G n). Qed.

Lemma lcn_norm0 : forall G n, G \subset  'N('L_n(G)).
Proof. by move=> G n; case/andP: (lcn_normal0 G n). Qed.

Lemma lcn_sub : forall G n, 'L_n.+1(G) \subset 'L_n(G).
Proof.
move=> G n; rewrite lcnSn commGC commg_subr.
by case/andP: (lcn_normal0 G n).
Qed.

Lemma lcn_normal : forall G n, 'L_n.+1(G) <| 'L_n(G).
Proof.
move=> n G.
by apply: normalS (lcn_normal0 _ _); rewrite (lcn_sub, lcn_sub0).
Qed.

Lemma lcn_central : forall G n,
  'L_n(G) / 'L_n.+1(G) \subset 'Z(G / 'L_n.+1(G)).
Proof.
move=> G n; rewrite subsetI ?lcn_sub0 //=.
by rewrite morphimS ?quotient_cents2r ?lcn_norm0 ?lcn_sub0 ?lcn_sub.
Qed.

Lemma lcn_stable : forall G n m, n <= m ->  'L_n(G) = 1 -> 'L_m(G) = 1.
Proof.
move=> G n m le_mn Gn1; apply/trivgP; rewrite -{}Gn1 -(subnKC le_mn) addnC.
elim: {m le_mn}(m - n) => //= m; apply: subset_trans; exact: lcn_sub.
Qed.

Lemma nilpotent_class : forall G, nilpotent G = (nil_class G < #|G|).
Proof.
move=> G; rewrite -(size_mkseq (fun n => 'L_n(G)) #|G|) index_mem.
apply/forallP/mapP=> /= [nilG | [n _ Ln1] H]; last first.
  apply/implyP; rewrite subsetI; case/andP=> sHG sHR.
  rewrite -subG1 {}Ln1; elim: n => // n IHn.
  apply: subset_trans sHR _; apply: genS; exact: imset2S.
pose n := #|G|; have: n <= #|G| := leqnn _.
have: #|G| < n + #|'L_n(G)| by rewrite -addn1 leq_add2l cardG_gt0.
elim: n => [|n IHn leGn lt_nG]; first by rewrite ltnn.
have:= nilG [group of 'L_n(G)]; rewrite /= -lcnSn subsetI lcn_sub0.
rewrite -(lcn_sub G n) -eqEsubset eqEcard lcn_sub implybE /= -ltnNge orbC.
case/predU1P=> [trLn | lt_Ln1_Ln]; first by exists n; rewrite ?mem_iota.
by apply: IHn (leq_trans leGn _) (ltnW lt_nG); rewrite addSnnS leq_add2l.
Qed.

Lemma lcnP : forall G, reflect (exists n, 'L_n(G) = 1) (nilpotent G).
Proof.
move=> G; apply: (iffP idP) => [| [n Ln1]].
  rewrite nilpotent_class -(size_mkseq (fun n => 'L_n(G)) #|G|) index_mem.
  by case/mapP=> n _ Ln1; exists n.
apply/forallP=> H; apply/implyP; rewrite subsetI; case/andP=> sHG sHR.
rewrite -subG1 -{}Ln1; elim: n => // n IHn.
apply: subset_trans sHR _; apply: genS; exact: imset2S.
Qed.

Lemma lcn1 : forall A, 'L_1(A) = A^`(1). Proof. by []. Qed.

Theorem abelian_nil : forall G, abelian G -> nilpotent G.
Proof. move=> G abG; apply/lcnP; exists 1%N; exact/commG1P. Qed.

End LowerCentral.

Lemma lcn_resp : forall n, resp (lower_central_at n).
Proof.
elim=> [|n IH] g0T h0T H phi; first by rewrite !lcn0.
by rewrite !lcnSn morphimR ?lcn_sub0 // commSg ?IH.
Qed.

Lemma lcn_compatible : forall n, compatible (lower_central_at n).
Proof.
elim=> [|n IH] gT H G sHG; first by rewrite !lcn0.
by rewrite !lcnSn commgSS ?IH.
Qed.

Canonical Structure bgFunc_lcn n :=
  [bgFunc by fun _ G => lcn_sub0 G n & lcn_resp n].

Canonical Structure gFunc_lcn n := GFunc (lcn_resp n).

Canonical Structure cgFunc_lcn n := CGFunc (lcn_compatible n).

Notation "''L_' n ( G )" := (lower_central_at_group n G) : subgroup_scope.

Section UpperCentral.

Variable gT : finGroupType.
Notation sT := {set gT}.
Implicit Type A B : {set gT}.
Implicit Type G H : {group gT}.

Lemma ucn0 : forall A, 'Z_0(A) = 1.
Proof. by []. Qed.

Lemma ucnSn : forall A n, 'Z_n.+1(A) = coset 'Z_n(A) @*^-1 'Z(A / 'Z_n(A)).
Proof. by []. Qed.

Lemma ucnE : forall A n, 'Z_n(A) = upper_central_at_rec n A.
Proof. by []. Qed.

Lemma ucn_group_set : forall G n, group_set ('Z_n(G)).
Proof.
move=> G; elim=> [|n IHn]; first exact: groupP.
by rewrite ucnSn -(gen_set_id IHn) groupP.
Qed.

Canonical Structure upper_central_at_group n G := Group (ucn_group_set G n).

Lemma ucn_sub : forall G n, 'Z_n(G) \subset 'Z_n.+1(G).
Proof. by move=> G n; rewrite -{1}['Z_n(G)]ker_coset morphpreS ?sub1G. Qed.

Lemma ucn_char : forall G n, 'Z_n(G) \char G.
Proof.
move=> G; elim=> [|n chZn]; [exact: trivg_char | rewrite ucnSn].
have nZn: 'Z_n(G) <| G by exact: char_normal.
apply: char_from_quotient chZn _; last by rewrite cosetpreK center_char.
apply: normalS (nZn); rewrite ?ucn_sub // -{8}(quotientGK nZn) morphpreS //.
exact: center_sub.
Qed.

(* Now reprove all the intermediate facts of the last proof. *)
Lemma ucn_normal0 : forall G n, 'Z_n(G) <| G.
Proof. by move=> G n; rewrite char_normal ?ucn_char. Qed.

Lemma ucn_sub0 : forall G n, 'Z_n(G) \subset G.
Proof. by move=> G n; rewrite normal_sub ?ucn_normal0. Qed.

Lemma ucn_normal : forall G n, 'Z_n(G) <| 'Z_n.+1(G).
Proof.
move=> G n; move: (ucn_sub0 G n.+1) (ucn_normal0 G n).
exact: normalS (ucn_sub G n).
Qed.

Lemma ucn_central : forall G n, 'Z_n.+1(G) / 'Z_n(G) = 'Z(G / 'Z_n(G)).
Proof. by move=> G n; rewrite ucnSn cosetpreK. Qed.

Lemma ucn_comm : forall G n, [~: 'Z_n.+1(G), G] \subset 'Z_n(G).
Proof.
move=> G n; rewrite -quotient_cents2 ?normal_norm ?ucn_normal0 ?ucn_normal //.
by rewrite ucn_central subsetIr.
Qed.

Lemma ucn1 : forall G, 'Z_1(G) = 'Z(G).
Proof.
move=> G; apply/eqP; rewrite eqEsubset ucnSn ucn0 -sub_morphim_pre ?norms1 //.
rewrite -{2}(quotientGK (normal1 G)) -!(morphim_invmE (coset1_injm gT)).
by rewrite !morphim_center.
Qed.

Lemma ucnSnR : forall G n,
  'Z_n.+1(G) = [set x \in G | commg x @: G \subset 'Z_n(G)].
Proof.
move=> G n; apply/setP=> x; rewrite inE.
case Gx: (x \in G); last first.
  by apply/idP=> Zx; case/idP: Gx; apply: subsetP Zx; exact: ucn_sub0.
have nZG: G \subset 'N('Z_n(G)) by rewrite normal_norm ?ucn_normal0.
have nZx: [set x] \subset 'N('Z_n(G)) by rewrite sub1set (subsetP nZG).
rewrite -sub1set ucnSn -sub_morphim_pre // subsetI morphimS ?sub1set //.
by rewrite quotient_cents2 // gen_subG /commg_set imset2_set1l.
Qed.

End UpperCentral.

Lemma ucn_gFunc :  forall n,
  [/\ resp (upper_central_at n), hereditary (upper_central_at n)
    & forall (hT : finGroupType) (G : {group hT}), 'Z_n(G) \subset G ].
Proof.
elim=> [|n [Hresp Hhereditary Hsub]].
  by split=> ? ? *; rewrite ?ucn0 ?morphim1 ?sub1G ?subsetIl //.
pose Zn := @HGFunc [gFunc by Hsub & Hresp] Hhereditary.
pose ZSn:= [hgFunc of appmod center Zn].
split=> [gT hT G phi|gT H G sHG| gT G]; rewrite ucnSn.
- exact: (gFunc_resp ZSn).
- exact: (hgFunc_hereditary ZSn sHG).
- exact: (bgFunc_clos ZSn).
Qed.

Lemma ucn_resp : forall n, resp (upper_central_at n).
Proof. by move=> n; case: (ucn_gFunc n). Qed.


Lemma ucn_hereditary : forall n, hereditary (upper_central_at n).
Proof. by move=> n; case: (ucn_gFunc n). Qed.

Lemma ucn_clos : forall n (gT : finGroupType) (H : {group gT}),
  'Z_n(H) \subset H.
Proof. by move=> n; case: (ucn_gFunc n). Qed.

Canonical Structure bgFunc_ucn n := [bgFunc by ucn_clos n & ucn_resp n].
Canonical Structure gFunc_ucn n := GFunc (ucn_resp n).
Canonical Structure hgFunc_ucn n := HGFunc (ucn_hereditary n).

Notation "''Z_' n ( G )" := (upper_central_at_group n G) : subgroup_scope.

Section Properties.

Variable gT : finGroupType.
Implicit Type A B : {set gT}.
Implicit Type G H K : {group gT}.
Implicit Type rT : finGroupType.

Lemma ucn_lcnP : forall G n, ('L_n(G) == 1) = ('Z_n(G) == G).
Proof.
move=> G n; rewrite !eqEsubset sub1G ucn_sub0 /= andbT -(ucn0 G).
elim: {1 3}n 0 (addn0 n) => [j <- //|i IHi j].
rewrite addSnnS; move/IHi=> <- {IHi}; rewrite ucnSn lcnSn.
have nZG := normal_norm (ucn_normal0 G j).
have nZL := subset_trans (lcn_sub0 _ _) nZG.
by rewrite -sub_morphim_pre // subsetI morphimS ?lcn_sub0 // quotient_cents2.
Qed.

Lemma ucnP : forall G, reflect (exists n, 'Z_n(G) = G) (nilpotent G).
Proof.
move=> G; apply: (iffP (lcnP G)) => [] [n]; move/eqP=> clGn;
  by exists n; apply/eqP; rewrite ucn_lcnP in clGn *.
Qed.

Lemma lcnS : forall A B n, A \subset B -> 'L_n(A) \subset 'L_n(B).
Proof.
by move=> A B n sAB; elim: n => // n IHn; rewrite !lcnSn genS ?imset2S.
Qed.

Lemma nilpotentS : forall A B, B \subset A -> nilpotent A -> nilpotent B.
Proof.
move=> A B sBA nilA; apply/forallP=> H; apply/implyP=> sHR.
have:= forallP nilA H; rewrite (subset_trans sHR) //.
by apply: subset_trans (setIS _ _) (setSI _ _); rewrite ?commgS.
Qed.

Lemma morphim_lcn : forall rT G H (f : {morphism G >-> rT}) n,
  H \subset G -> f @* 'L_n(H) = 'L_n(f @* H).
Proof.
move=> rT G H f n sHG; elim: n => // n IHn.
by rewrite !lcnSn -IHn morphimR // (subset_trans _ sHG) // lcn_sub0.
Qed.

Lemma morphim_nil : forall rT G H (f : {morphism G >-> rT}),
  nilpotent H -> nilpotent (f @* H).
Proof.
move=> rT G H f; move/(nilpotentS (subsetIr G H)); case/lcnP=> n LnH1.
rewrite -morphimIdom; apply/lcnP; exists n.
by rewrite -morphim_lcn ?subsetIl // LnH1 morphim1.
Qed.

Lemma quotient_nil : forall G H, nilpotent G -> nilpotent (G / H).
Proof. move=> G H; exact: morphim_nil. Qed.

Lemma lcn_mul : forall G H n,
  G \subset 'C(H) -> 'L_n(G * H) = 'L_n(G) * 'L_n(H).
Proof.
move=> G H n cGH; elim: n => // n; rewrite lcnSn => ->.
have nHG: H \subset 'N(G) by rewrite cents_norm // centsC.
have sLG := lcn_sub0 G n; have [sLH nLH] := andP (lcn_normal0 H n).
have cHL: H \subset 'C('L_n(G)) by rewrite centsC (subset_trans sLG).
have nLGH := cents_norm cHL.
rewrite -(cent_mulgenEl cGH) commMG /=; last first.
  by rewrite normsR ?(subset_trans sLH) // normsG ?mulgen_subr.
rewrite cent_mulgenEl //; congr (_ * _); rewrite commGC commMG ?normsR //.
  by rewrite (commG1P cHL) mulg1 commGC.
by rewrite (commG1P (subset_trans cGH (centS sLH))) mul1g commGC.
Qed.

Lemma mulg_nil : forall G H, G \subset 'C(H) -> 
  nilpotent (G * H) = nilpotent G && nilpotent H.
Proof.
move=> G H cGH; apply/idP/andP=> [nilGH | []].
  by split; apply: nilpotentS nilGH; rewrite (mulG_subr, mulG_subl).
case/lcnP=> n1 Ln1G1; case/lcnP=> n2 Ln2G1.
rewrite -(cent_mulgenEl cGH); apply/lcnP; rewrite /= cent_mulgenEl //.
have trLadd : forall K i j, 'L_i(K) = 1 -> 'L_(j + i)(K) = 1.
  move=> K i j; apply: lcn_stable; exact: leq_addl.
by exists (n1 + n2); rewrite lcn_mul // {1}addnC !trLadd ?mul1g.
Qed.

Lemma nilpotent1 : nilpotent [1 gT].
Proof. by apply/lcnP; exists 0. Qed.

Lemma nilpotent_sub_norm : forall G H,
  nilpotent G -> H \subset G -> 'N_G(H) \subset H -> G :=: H.
Proof.
move=> G H nilG sHG sNH; apply/eqP; rewrite eqEsubset sHG andbT.
apply/negP=> nsGH.
have{nsGH} [i sZH []]: exists2 i, 'Z_i(G) \subset H & ~ 'Z_i.+1(G) \subset H.
  case/ucnP: nilG => n ZnG; rewrite -{}ZnG in nsGH.
  elim: n => [|i IHi] in nsGH *; first by rewrite sub1G in nsGH.
  by case sZH: ('Z_i(G) \subset H); [exists i | apply: IHi; rewrite sZH].
apply: subset_trans sNH; rewrite subsetI ucn_sub0 -commg_subr.
apply: subset_trans sZH; apply: subset_trans (ucn_comm G i); exact: commgS.
Qed.

Lemma nil_TI_Z : forall G H,
  nilpotent G -> H <| G -> H :&: 'Z(G) = 1 -> H :=: 1.
Proof.
move=> G H nilG; case/andP=> sHG nHG trHZ.
rewrite -{1}(setIidPl sHG); case/ucnP: nilG => n <-.
elim: n => [|n IHn]; apply/trivgP; rewrite ?subsetIr // -trHZ.
rewrite [H :&: 'Z(G)]setIA subsetI setIS ?ucn_sub0 //= (sameP commG1P trivgP).
rewrite -commg_subr commGC in nHG.
rewrite -IHn subsetI (subset_trans _ nHG) ?commSg ?subsetIl //=.
by rewrite (subset_trans _ (ucn_comm G n)) ?commSg ?subsetIr.
Qed.

End Properties.

Section DirectProdProperties.

Variable gT: finGroupType.
Implicit Type G : {group gT}.

Lemma dprod_nil : forall A B G,
   A \x B = G -> nilpotent A -> nilpotent B -> nilpotent G.
Proof.
by move=> A B G; case/dprodP=> [[H K -> ->] <- ? _]; rewrite mulg_nil => [->|].
Qed.

Lemma bigdprod_nil : forall I r (P : pred I) F G,
  \big[dprod/1]_(i <- r | P i) F i = G
  -> (forall i, P i -> nilpotent (F i)) -> nilpotent G.
Proof.
move=> I r P F G defG nilF; rewrite -defG; move: G defG.
apply big_prop => [_ _|A B IHA IHB G defG| i Pi _ _]; last exact: nilF.
  exact: nilpotent1.
case: (dprodP defG) => [[H K defH defK] _ _ _].
by rewrite defG (dprod_nil defG) ?(IHA _ defH) ?(IHB _ defK).
Qed. 
 
End DirectProdProperties.

Section Derived.

Variable gT : finGroupType.
Implicit Type A B : {set gT}.
Implicit Type G H : {group gT}.

Lemma derg0 : forall A, A^`(0) = A. Proof. by []. Qed.
Lemma derg1 : forall A, A^`(1) = [~: A, A]. Proof. by []. Qed.
Lemma dergSn : forall A n, A^`(n.+1) = [~: A^`(n), A^`(n)]. Proof. by []. Qed.

Lemma der_group_set : forall G n, group_set G^`(n).
Proof. move=> G [|n]; exact: groupP. Qed.

Canonical Structure derived_at_group n G := Group (der_group_set G n).

Lemma der_char : forall G n, G^`(n) \char G.
Proof. by move=> G; elim=> *; rewrite ?char_refl // dergSn charR. Qed.

Lemma der_sub : forall G n, G^`(n.+1) \subset G^`(n).
Proof. by move=> G n; rewrite comm_subG. Qed.

Lemma der_sub0 : forall G n, G^`(n) \subset G.
Proof. by move=> G n; rewrite normal_sub ?char_normal ?der_char. Qed.

Lemma der_normal : forall G n, G^`(n.+1) <| G^`(n).
Proof. by move=> G n; rewrite sub_der1_normal // der_sub. Qed.

Lemma der_abelian : forall G n, abelian (G^`(n) / G^`(n.+1)).
Proof. by move=> G n; rewrite sub_der1_abelian // der_sub. Qed.

End Derived.

Lemma der_clos : forall n (gT : finGroupType) (G : {group gT}),
  G^`(n) \subset G.
Proof.
elim; first by move=> gT0 G; rewrite derg0.
by move=> n0 IH gT G; rewrite dergSn (comm_subG (IH _ _) (IH _ _)).
Qed.

Lemma der_resp : forall n, resp (derived_at n).
Proof.
elim => [|n IH] gT hT H phi; first by rewrite derg0.
rewrite !dergSn (morphimR _ (der_clos _ _) (der_clos _ _)).
by rewrite commgSS ?IH.
Qed.

Lemma der_compatible : forall n, compatible (derived_at n).
Proof.
elim => [|n IH] gT H G sHG; first by rewrite !derg0.
by rewrite !dergSn commgSS ?IH.
Qed.

Canonical Structure bgFunc_der n := [bgFunc by der_clos n & der_resp n].
Canonical Structure gFunc_der n := GFunc (der_resp n).
Canonical Structure cgFunc_der n := CGFunc (der_compatible n).

Notation "G ^` ( n )" := (derived_at_group n G) : subgroup_scope.

Section Solvable.

Variable gT : finGroupType.
Implicit Type G H : {group gT}.

Lemma nilpotent_sol : forall G, nilpotent G -> solvable G.
Proof.
move=> G nilG; apply/forallP=> H; rewrite subsetI.
apply/implyP; case/andP=> sHG sHH'; apply: (implyP (forallP nilG H)).
by rewrite subsetI sHG (subset_trans sHH') ?commgS.
Qed.

Lemma abelian_sol : forall G, abelian G -> solvable G.
Proof. move=> G; move/abelian_nil; exact: nilpotent_sol. Qed.

Lemma solvableS : forall G H : {group gT},
  H \subset G -> solvable G -> solvable H.
Proof.
move=> G H sHG solG; apply/forallP=> K; rewrite subsetI.
apply/implyP; case/andP=> sKH sKK'; apply: (implyP (forallP solG K)).
by rewrite subsetI (subset_trans sKH).
Qed.

Lemma morphim_sol : forall (rT : finGroupType) G H (f : {morphism G >-> rT}),
  solvable H -> solvable (f @* H).
Proof.
move=> rT G H; wlog: G H / G :=: H => [IH f solH | <- {H} f solG].
  rewrite -morphimIdom -(setIid (G :&: H)) -(morphim_restrm (subsetIl G H)).
  exact: IH (erefl _) _ (solvableS (subsetIr G H) solH).
apply/forallP=> Hb; apply/implyP; rewrite subsetI; case/andP=> sHbG sHbHb'.
have{sHbG}: exists H : {group gT}, [&& H \subset G & f @* H == Hb].
  by exists (f @*^-1 Hb)%G; rewrite subsetIl morphpreK /=.
case/ex_mingroup=> H; case/mingroupP; case/andP=> sHG; move/eqP=> defHb minH.
suff trH: H :==: 1 by rewrite -defHb (eqP trH) morphim1.
have sH'H := der1_subG H.
apply: (implyP (forallP solG H)); rewrite subsetI sHG [[~: H, H]]minH //=.
by rewrite (subset_trans sH'H) // morphimR // defHb eqEsubset der1_subG.
Qed.

Lemma quotient_sol : forall G H, solvable G -> solvable (G / H).
Proof. move=> G H; exact: morphim_sol. Qed.

Lemma series_sol : forall G H,
  H <| G -> solvable G = solvable H && solvable (G / H).
Proof.
move=> G H; case/andP=> sHG nHG; apply/idP/andP=> [solG | [solH solGH]].
  by rewrite quotient_sol // (solvableS sHG).
apply/forallP=> K; rewrite subsetI; apply/implyP; case/andP=> sKG sK'K.
suffices sKH: K \subset H.
  by apply: (implyP (forallP solH K)); rewrite subsetI sKH.
have nHK := subset_trans sKG nHG.
rewrite -quotient_sub1 // subG1 (implyP (forallP solGH _)) //.
by rewrite subsetI -morphimR ?morphimS.
Qed.

Lemma derivedP : forall G, reflect (exists n, G^`(n) = 1) (solvable G).
Proof.
move=> G; apply: (iffP idP) => [solG | [n solGn]]; last first.
  apply/forallP=> H; rewrite subsetI; apply/implyP; case/andP=> sHG sH'H.
  rewrite -subG1 -{}solGn; elim: n => // n IHn.
  exact: subset_trans sH'H (commgSS _ _).
suffices IHn: forall n, #|G^`(n)| - 1 <= #|G| - n.+1.
  exists #|G|.-1; apply/eqP; rewrite trivg_card_le1 -subn_eq0 -leqn0.
  by rewrite (leq_trans (IHn _)) // prednK ?subnn.
elim=> // n IHn; rewrite dergSn; have:= forallP solG (G^`(n))%G.
case: eqP => /= [->|_]; first by rewrite commG1 cards1.
rewrite -dergSn implybF subsetI der_sub0 /= => sGnGn1.
rewrite -(addn1 n.+1) -subn_sub leq_sub2r //; apply: leq_trans IHn.
by rewrite subn1 -ltnS prednK ?cardG_gt0 // proper_card // /proper der_sub.
Qed.

End Solvable.
