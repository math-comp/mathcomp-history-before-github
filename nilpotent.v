Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq div prime.
Require Import ssralg bigops. 
Require Import fintype finset groups commutators automorphism.
Require Import normal center sylow. 
Require Import schurzass cyclic.


(* Require Import paths connect finfun ssralg bigops. *)

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Import GroupScope.

Section Defs.

Variable (gT : finGroupType) (n : nat) (A : {set gT}).

Definition lower_central_at_rec := iter n (fun B => [~: B, A]) A.

Definition upper_central_at_rec :=
  iter n (fun B => A :&: coset_of B @*^-1 'Z(A / B)) 1.

Definition derived_at_rec m := iter m (fun B => [~: B, B]) A.

End Defs.

(* 'nosimpl' MUST be used outside of a section -- the end of *)
(* section "cooking" destroys it.                            *)

Definition lower_central_at := nosimpl lower_central_at_rec.
Definition upper_central_at := nosimpl upper_central_at_rec.
Definition derived_at := nosimpl derived_at_rec.

Notation "''L_' n ( G )" := (lower_central_at n G)
  (at level 8, n at level 2, format "''L_' n ( G )") : group_scope.

Notation "''Z_' n ( G )" := (upper_central_at n G)
  (at level 8, n at level 2, format "''Z_' n ( G )") : group_scope.

Notation "G ^` ( n )" := (derived_at G n)
  (at level 8, format "G ^` ( n )") : group_scope.

Section LowerCentral.

Variable gT : finGroupType.
Notation sT := {set gT}.
Implicit Type A : {set gT}.
Implicit Type G H : {group gT}.

Lemma lcn0 : forall A, 'L_0(A) = A. Proof. by []. Qed.
Lemma lcnSn : forall A n, 'L_n.+1(A) = [~: 'L_n(A), A]. Proof. by []. Qed.
Lemma lcnE : forall A n, 'L_n(A) = lower_central_at_rec n A. Proof. by []. Qed.

Definition nilpotent A :=
  forallb G : {group gT}, (G \subset A :&: [~: G, A]) ==> trivg G.

Definition nil_class A := index 1 (mkseq (fun n => 'L_n(A)) #|A|).

Lemma lcn_group_set : forall G n, group_set ('L_n(G)).
Proof. move=> G; elim=> *; exact: groupP. Qed.

Canonical Structure lower_central_at_group n G := Group (lcn_group_set G n).

Lemma lcn_char : forall G n, 'L_n(G) \char G.
Proof. by move=> G; elim=> [|n IHn]; rewrite ?lcnSn ?charR ?char_refl. Qed.

Lemma lcn_normal0 : forall G n, 'L_n(G) <|  G.
Proof. move=> G n; apply: normal_char; exact: lcn_char. Qed.

Lemma lcn_subset0 : forall G n, 'L_n(G) \subset G.
Proof. by move=> G n; case/andP: (lcn_normal0 G n). Qed.

Lemma lcn_normaliser0 : forall G n, G \subset  'N('L_n(G) ).
Proof. by move=> G n; case/andP: (lcn_normal0 G n). Qed.

Lemma lcn_subset : forall G n, 'L_n.+1(G) \subset 'L_n(G).
Proof.
move=> G n; rewrite lcnSn commsgC subcomm_normal.
by case/andP: (lcn_normal0 G n).
Qed.

Lemma lcn_normal : forall G n, 'L_n.+1(G) <|  'L_n(G).
Proof.
move=> n G.
by apply: normalS (lcn_normal0 _ _); rewrite (lcn_subset, lcn_subset0).
Qed.

Lemma lcn_center : forall G n, 'L_n(G) / 'L_n.+1(G) \subset 'Z(G / 'L_n.+1(G)).
Proof.
move=> G n; rewrite subsetI ?lcn_subset0 //=.
by rewrite morphimS ?center_commgr ?lcn_normaliser0 ?lcn_subset0 ?lcn_subset.
Qed.

Lemma lcn_stable : forall G n m, n <= m ->  trivg 'L_n(G) -> trivg 'L_m(G).
Proof.
move=> G n m le_mn; apply: subset_trans; rewrite -(subnK le_mn) addnC.
elim: {m le_mn}(m - n) => //= m; apply: subset_trans; exact: lcn_subset.
Qed.

Lemma nilpotent_class : forall G, nilpotent G = (nil_class G < #|G|).
Proof.
move=> G; rewrite -(size_mkseq (fun n => 'L_n(G)) #|G|) index_mem.
apply/forallP/mapsP=> /= [nilG | [n _ Ln1] H]; last first.
  apply/implyP; rewrite subsetI; case/andP=> sHG sHR.
  rewrite /trivg /= -{}Ln1; elim: n => // n IHn.
  apply: subset_trans sHR _; apply: genS; exact: imset2S.
pose n := #|G|; have: n <= #|G| := leqnn _.
have: #|G| < n + #|'L_n(G)| by rewrite -addn1 leq_add2l pos_card_group.
elim: n => [|n IHn leGn lt_nG]; first by rewrite ltnn.
have:= nilG [group of 'L_n(G)]; rewrite /= -lcnSn subsetI lcn_subset0.
rewrite -(lcn_subset G n) -eqset_sub eqset_sub_card lcn_subset implybE /=.
rewrite -ltnNge trivg_card; case/orP=> [lt_Ln1_Ln | trLn].
  by apply: IHn (leq_trans leGn _) (ltnW lt_nG); rewrite addSnnS leq_add2l.
by exists n; [rewrite mem_iota | apply/trivgP; rewrite trivg_card].
Qed.

Lemma lcnP : forall G, reflect (exists n, 'L_n(G) = 1) (nilpotent G).
Proof.
move=> G; apply: (iffP idP) => [| [n Ln1]].
  rewrite nilpotent_class -(size_mkseq (fun n => 'L_n(G)) #|G|) index_mem.
  by case/mapsP=> n _ Ln1; exists n.
apply/forallP=> H; apply/implyP; rewrite subsetI; case/andP=> sHG sHR.
rewrite /trivg /= -{}Ln1; elim: n => // n IHn.
apply: subset_trans sHR _; apply: genS; exact: imset2S.
Qed.

Lemma lcn1 : forall A, 'L_1(A) = A^`(1). Proof. by []. Qed.

End LowerCentral.

Notation "''L_' n ( G )" := (lower_central_at_group n G) : subgroup_scope.

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

End Derived.

Section UpperCentral.

Variable gT : finGroupType.
Notation sT := {set gT}.
Implicit Type A B : {set gT}.
Implicit Type G H : {group gT}.

Lemma ucn0 : forall A, 'Z_0(A) = 1.
Proof. by []. Qed.

(* Definition of Aschbacher *)
Lemma ucnSn : forall A n,
 'Z_n.+1(A) = A :&: coset_of 'Z_n(A) @*^-1 'Z(A / 'Z_n(A)).
Proof. by []. Qed.

Lemma ucnE : forall A n, 'Z_n(A) = upper_central_at_rec n A.
Proof. by []. Qed.

Lemma ucn_group_set : forall G n, group_set ('Z_n(G)).
Proof.
move=> G; elim=> [|n IHn]; first exact: groupP.
by rewrite ucnSn -['Z_n(G)]/(Group IHn : set _) groupP.
Qed.

Canonical Structure upper_central_at_group n G := Group (ucn_group_set G n).

Lemma ucn_subset0 : forall G n, 'Z_n(G) \subset G.
Proof. by move=> G [|n]; rewrite ?sub1G // ucnSn subsetIl. Qed.

Lemma ucn_subset : forall G n, 'Z_n(G) \subset 'Z_n.+1(G).
Proof.
move=> G n; rewrite ucnSn subsetI ucn_subset0.
by rewrite -{1}['Z_n(G)]ker_coset morphpreS ?sub1G.
Qed.

Lemma ucn_char : forall G n, 'Z_n(G) \char G.
Proof.
move=> G; elim=> [|n chZn]; first exact: trivg_char.
have nZn: 'Z_n(G) <| G by exact: normal_char.
case: (andP nZn) => sZn nZn'; rewrite ucnSn.
apply: char_from_quotient (chZn) _.
  by apply: normalS nZn; rewrite (subsetIl, ucn_subset).
rewrite /= quotientE morphimGI ?ker_coset // morphpreK -!quotientE.
  by rewrite setIA setIid characteristic_center.
by rewrite subIset // morphimS.
Qed.

(* Now reprove all the intermediate facts of the last proof. *)
Lemma ucn_normal0 : forall G n, 'Z_n(G) <| G.
Proof. move=> G n; apply: normal_char; exact: ucn_char. Qed.

Lemma ucn_normal : forall G n, 'Z_n(G) <| 'Z_n.+1(G).
Proof.
move=> G n; move: (ucn_subset0 G n.+1) (ucn_normal0 G n).
exact: normalS (ucn_subset G n).
Qed.

Lemma ucn_center : forall G n, 'Z_n.+1(G) / 'Z_n(G) = 'Z(G / 'Z_n(G)).
Proof.
move=> G n; rewrite ucnSn quotientE.
rewrite morphimGI ?ker_coset ?ucn_subset0 // morphpreK -!quotientE.
  by rewrite setIA setIid.
by rewrite subIset // morphimS //; case/andP: (ucn_normal0 G n).
Qed.

Lemma ucn_comm : forall G n, [~: 'Z_n.+1(G), G] \subset 'Z_n(G).
Proof.
move=> G n; case/andP: (ucn_normal0 G n) => _ nZG.
case/andP: (ucn_normal G n) => _ nZZ.
rewrite -trivg_quotient ?comm_subG // quotientE morphimR //= -!quotientE.
by rewrite ucn_center (sameP commG1P centsP) subsetIr.
Qed.

Lemma ucn1 : forall G, 'Z_1(G) = 'Z(G).
Proof.
have morphim_center: forall (K H : group _) (f : morphism _ K),
  f @* 'Z(H) \subset 'Z(f @* H).
- move=> T T' K H f; rewrite subsetI morphimS ?subsetIl //=.
  by rewrite (subset_trans _ (morphim_cent _ _)) ?morphimS // subsetIr.
move=> G; apply: congr_group; apply: (quotient_inj (ucn_normal G 0)).
  apply: normal_char; exact: trivg_char. (* GG: sic! *)
apply/eqP; rewrite eqset_sub ucn_center /= ucn0 morphim_center.
have injq1: 'injm (coset_of (1 : sT)) by rewrite ker_coset trivg1.
have allN1: forall A : sT, A \subset 'N(1).
  by move=> A; rewrite normaliser1 subsetT.
rewrite -{2}(morphim_invm injq1 (allN1 G)) -['Z(_) / 1](morphpre_invm injq1).
by rewrite -sub_morphim_pre ?morphim_center // subIset // morphimS.
Qed.

Lemma ucnSnR : forall G n,
  'Z_n.+1(G) = [set x \in G | commg x @: G \subset 'Z_n(G)].
Proof.
move=> G n; apply/setP=> x; rewrite ucnSn 3!inE; case Gx: (x \in G) => //=.
have nZG: G \subset 'N('Z_n(G)) by case/andP: (ucn_normal0 G n).
have nZx: [set x] \subset 'N('Z_n(G)) by rewrite sub1set (subsetP nZG).
rewrite -sub1set nZx 2!inE -{1}coset_of_norm mem_imset //=.
rewrite -?(sub1set, morphim_set1) //= -quotientE (sameP centsP commG1P).
rewrite -morphimR // trivg_quotient; last exact: comm_subG.
by rewrite gen_subG /commg_set imset2_set1l.
Qed.

End UpperCentral.

Notation "''Z_' n ( G )" := (upper_central_at_group n G) : subgroup_scope.

Section Properties.

Variable gT : finGroupType.
Implicit Type A B : {set gT}.
Implicit Type G H : {group gT}.
Implicit Type rT : finGroupType.

Lemma ucn_lcnP : forall G n, ('L_n(G) == 1) = ('Z_n(G) == G).
Proof.
move=> G n; rewrite !eqset_sub sub1G ucn_subset0 /= andbT -(ucn0 G).
elim: {1 3}n 0 (addn0 n) => [j <- //|i IHi j].
rewrite addSnnS; move/IHi=> <- {IHi}.
have [_ nZG] := andP (ucn_normal0 G j).
have nZL := subset_trans (lcn_subset0 _ _) nZG.
rewrite -trivg_quotient //= lcnSn quotientE morphimR //= -!quotientE.
rewrite (sameP commG1P centsP); symmetry.
rewrite ucnSn subsetI lcn_subset0 -sub_morphim_pre //= -quotientE.
by rewrite subsetI morphimS ?lcn_subset0.
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

Lemma nilpotent_sub : forall A B, B \subset A -> nilpotent A -> nilpotent B.
Proof.
move=> A B sBA nilA; apply/forallP=> H; apply/implyP=> sHR.
have:= forallP nilA H; rewrite (subset_trans sHR) //.
by apply: subset_trans (setIS _ _) (setSI _ _); rewrite ?commgS.
Qed.

Lemma morphim_lcn : forall rT G H (f : {morphism G >-> rT}) n,
  H \subset G -> f @* 'L_n(H) = 'L_n(f @* H).
Proof.
move=> rT G H f n sHG; elim: n => // n IHn.
by rewrite !lcnSn -IHn morphimR // (subset_trans _ sHG) // lcn_subset0.
Qed.

Lemma nilpotent_morphim : forall rT G H (f : {morphism G >-> rT}),
  nilpotent H -> nilpotent (f @* H).
Proof.
move=> rT G H f; move/(nilpotent_sub (subsetIr G H)); case/lcnP=> n LnH1.
rewrite -morphimIdom; apply/lcnP; exists n.
by rewrite -morphim_lcn ?subsetIl // LnH1 morphim1.
Qed.

Lemma nilpotent_quo : forall G H, nilpotent G -> nilpotent (G / H).
Proof. move=> G H; exact: nilpotent_morphim. Qed.

Lemma lcn_mul : forall G H n,
  {in G, centralised H} -> 'L_n(G * H) = 'L_n(G) * 'L_n(H).
Proof.
move=> G H n cGH; elim: n => // n; rewrite lcnSn => ->.
apply/eqP; rewrite eqset_sub; apply/andP; split; last first.
  rewrite -gen_subG genM_mulgen gen_subG subUset /= !lcnSn.
  by rewrite !commgSS // (mulG_subr, mulG_subl).
have sL0 := subsetP (lcn_subset0 _ _).
have cLL: {in 'L_n.+1(G), centralised 'L_n.+1(H)}.
  by move=> x; move/sL0=> Gx y; move/sL0; exact: cGH.
rewrite -(centralised_mulgenE cLL) gen_subG /= centralised_mulgenE //=.
apply/subsetP=> xy; case/imset2P=> x y.
case/imset2P=> x1 x2 Lx1 Lx2 ->{x}; move/sL0: (Lx1) => Gx1.
case/imset2P=> y1 y2 Gy1 Hy2 ->{y} ->{xy}; move/sL0: (Lx2) => Hx2.
rewrite commMgJ conjRg conjMg 2!conjgE (cGH _ Gx1) // mulKg.
rewrite (cGH _ Gy1) // mulKg.
rewrite 2!commgEl 2!conjgM conjgE (cGH (x1 ^ y1)) ?groupJ // mulKg -commgEl.
rewrite (conjgE x2) -(cGH y1) // mulKg -commgEl.
by rewrite mem_imset2 ?mem_gen // mem_imset2.
Qed.

Lemma nilpotent_mul : forall G H, {in G, centralised H} -> 
  nilpotent (G * H) = nilpotent G && nilpotent H.
Proof.
move=> G H cGH; apply/idP/andP=> [nilGH | []].
  by split; apply: nilpotent_sub nilGH; rewrite (mulG_subr, mulG_subl).
case/lcnP=> n1 Ln1G1; case/lcnP=> n2 Ln2G1.
rewrite -(centralised_mulgenE cGH); apply/lcnP; rewrite /= centralised_mulgenE //.
have trLadd : forall (K : {group gT}) i j, 'L_i(K) = 1 -> 'L_(j + i)(K) = 1.
  move=> K i j; move/trivgP=> trL; apply/trivgP; apply: subset_trans trL.
  elim: j => // j; apply: subset_trans; exact: lcn_subset.
by exists (n1 + n2); rewrite lcn_mul // {1}addnC !trLadd ?mul1g.
Qed.

Lemma nilpotent1 : nilpotent (1 : {set gT}).
Proof. by apply/lcnP; exists 0. Qed.

Lemma nilpotent_pgroup : forall G, size (primes #|G|) <= 1 -> nilpotent G.
Proof.
move=> G pgG. (* interface to old p-group characterization *)
case: (leqP #|G| 1).
  by rewrite -trivg_card; case/trivGP=> ->; exact: nilpotent1.
move/prime_pdiv; set p := pdiv _ => pr_p; have Gpos: #|G| > 0 by [].
case: (p_part_coprime pr_p Gpos) => m; rewrite prime_coprime //.
case: (ltnP 1 m).
  move/prime_pdiv; set q := pdiv m => pr_q npm oGm; case/negP: npm.
  have: all (mem (primes #|G|)) [:: p; q].
    do 2!rewrite /= mem_filter -dvdn_divisors //.
    by rewrite pr_p pr_q dvdn_pdiv oGm dvdn_mulr // dvdn_pdiv.
  case: primes pgG => [|r []] //= _; rewrite !mem_seq1 andbT.
  by case/andP; move/eqP->; move/eqP <-; rewrite dvdn_pdiv.
case: m => [|[]] //; first by rewrite dvdn0.
rewrite mul1n /p_part => _ _ {Gpos pgG}; move: p => p in pr_p *.
move: (logn _ _) => m oG; apply/ucnP; exists m; apply/eqP.
rewrite eqset_sub_card ucn_subset0 /= oG.
elim: {-2}m (leqnn m) => [|k IHk] ltkm; first exact: pos_card_group.
case/andP: (ucn_normal G k) => sZ nZ.
  case/andP: (ucn_normal0 G k) => sZG nZG.
have: #|G / 'Z_k(G)| %| #|G|.
  by rewrite card_quotient // -(LaGrange sZG) dvdn_mull.
rewrite oG; case/dvdn_exp_prime=> // [] [|j] lejk oGbar.
  apply: (@leq_trans #|G|); first by rewrite oG leq_exp2l // prime_gt1.
  apply: subset_leq_card; apply: subset_trans sZ.
  by rewrite -trivg_quotient // trivg_card oGbar.
rewrite -(LaGrange sZ) -card_quotient //= ucn_center expnSr.
rewrite leq_mul ?(IHk (ltnW _)) // dvdn_leq ?pos_card_group //.
have:= pgroup_ntriv pr_p oGbar; rewrite trivg_card.
have: #|'Z(G / 'Z_k(G))| %| p ^ j.+1 by rewrite -oGbar group_dvdn // subsetIl.
by case/dvdn_exp_prime=> // [] [|i] _ -> // _; rewrite dvdn_mulr.
Qed.


Lemma small_nil_class : forall G n, nil_class G <= n -> n <= 5 -> nilpotent G.
Proof.
move=> G n leKn; move/(leq_trans leKn) => {n leKn} leK5.
case: (ltnP 5 #|G|) => [lt5G | leG5 {leK5}].
  by rewrite nilpotent_class (leq_ltn_trans leK5).
by apply: nilpotent_pgroup; move: #|G| leG5; do 6!case=> //.
Qed.

Lemma nilpotent_sub_norm : forall G H,
  nilpotent G -> H \subset G -> 'N_G(H) \subset H -> G = H.
Proof.
move=> G H nilG sHG sNH; apply/eqP; rewrite -val_eqE /= eqset_sub sHG andbT.
apply/negP=> nsGH.
have{nsGH} [i sZH []]: exists2 i, 'Z_i(G) \subset H & ~ 'Z_i.+1(G) \subset H.
  case/ucnP: nilG => n ZnG; rewrite -{}ZnG in nsGH.
  elim: n => [|i IHi] in nsGH *; first by rewrite sub1G in nsGH.
  by case sZH: ('Z_i(G) \subset H); [exists i | apply: IHi; rewrite sZH].
case/andP: (ucn_normal0 G i) => _ nZG.
apply: subset_trans sNH; rewrite subsetI subsetIl -subcomm_normal.
apply: subset_trans sZH; apply: subset_trans (ucn_comm G i); exact: commgS.
Qed.

Lemma nilpotent_meet_center : forall G H,
  nilpotent G -> H <| G -> ~~ trivg H -> ~~ trivg (H :&: 'Z(G)).
Proof.
move=> G H nilG; case/andP=> sHG nHG ntH.
pose trZH := [pred i | trivg (H :&: 'Z_i(G))].
have{nilG ntH} [i trZHi]: exists2 i, trZH i & ~~ trZH i.+1.
  move: ntH; rewrite -{1}(setIidPl sHG); case/ucnP: nilG => n <-.
  elim: n => [|i IHi ntZHi1]; first by rewrite /trivg subsetIr.
  by case trZHi: (trZH i); [exists i | move/idPn: trZHi].
apply: contra; apply: subset_trans; rewrite [H :&: 'Z(G)]setIA subsetI.
rewrite {1}setIA subsetIl /= (sameP centsP commG1P).
apply: subset_trans trZHi; rewrite -subcomm_normal commsgC in nHG.
rewrite subsetI (subset_trans _ nHG) ?commSg ?subsetIl //=.
by rewrite (subset_trans _ (ucn_comm G i)) ?commSg ?subsetIr.
Qed.

Require Import dirprod.

Lemma lcn_setX (H1 H2: {group gT}) n : 
  'L_n(setX H1 H2) = setX 'L_n(H1) 'L_n(H2).
Proof.
move=> H1 H2; elim=> [| n Hrec]; first by rewrite !lcn0.
rewrite !lcnSn Hrec.
apply/eqP; rewrite eqset_sub; apply/andP; split.
  rewrite gen_subG.
  apply/subsetP => x; case/imset2P => [[x11 x12] [x21 x22]].
  rewrite inE; case/andP => /= Hx11 Hx12.
  rewrite inE; case/andP => /= Hx21 Hx22 ->.  
  apply/setXP; split => /=.
    by apply: mem_gen; apply/imset2P; exists x11 x21.
  by apply: mem_gen; apply/imset2P; exists x12 x22.
rewrite -setX_gen ?group1;
  try by apply/imset2P; exists (1: gT) (1: gT); rewrite ?group1 ?comm1g.
apply: genS; apply/subsetP => [[x1 x2]]; rewrite !inE /=.
case/andP; case/imset2P => xx1 xx2 Hxx1 Hxx2 ->.
case/imset2P => yy1 yy2 Hyy1 Hyy2 ->.
by apply/imset2P; exists (xx1,yy1) (xx2,yy2); rewrite // !inE /= ?Hxx1 ?Hxx2.
Qed.

Lemma nilpotent_setX (H1 H2: {group gT}) :
  nilpotent (setX H1 H2) <-> nilpotent H1 /\ nilpotent H2. 
Proof.
move=> H1 H2; split.
    case/lcnP=> n; rewrite lcn_setX => Hn.
    split; apply/lcnP; exists n; apply/trivgP; apply/subsetP => y Hy;
    move/trivgP: Hn; move/subsetP; [move/(_ (y, 1))|move/(_ (1, y))];
    by rewrite !inE /= Hy group1; move/(_ is_true_true); case/andP.
move=> [Hn1]; case/lcnP=> n2 Hn2; case/lcnP: Hn1 => n1 Hn1.
pose m  := maxn n1 n2.
have T1m: trivg 'L_m(H1).
  by move/trivgP: Hn1; move/lcn_stable; apply; rewrite leq_maxr leqnn.
have T2m: trivg ('L_m (H2)).
  by move/trivgP: Hn2; move/lcn_stable; apply; rewrite leq_maxr leqnn orbT.
apply/lcnP; exists m; rewrite lcn_setX.
apply/trivgP; apply/subsetP =>  [[x y]]; rewrite !inE /=; case/andP => Hx Hy.
by apply/andP; split; [move: (subsetP T1m _ Hx) | move: (subsetP T2m _ Hy)];  
  rewrite !inE.
Qed.

End Properties.

Section DirectProdProperties.

Variable gT: finGroupType.

Infix "\x" := direct_product (at level 40, left associativity).

Lemma nilpotent_dirprod (H1 H2 G: {group gT}) :
   H1 \x H2 = G -> nilpotent H1 -> nilpotent H2 -> nilpotent G.
Proof.
move=> H1 H2 G; case/dprodGP => [[_ _ _ _ <- Hc] Htr].
rewrite nilpotent_mul; first by move=> ->.
by apply/centsP.
Qed.


Lemma filter_all: forall (I: Type) (r : seq I) P, all P (filter P r).
move=> I r P; elim: r => [| a r1 Hrec] //=.
by case Pa: (P a) => //=; rewrite Pa.
Qed.

Lemma nilpotent_bigdprod : forall (I: Type) (r : seq I) P 
      (F: I -> {set gT}) (G: {group gT}),
  \big[(@direct_product gT)/1]_(i <- r | P i) F i = G
  -> (forall i, P i -> nilpotent (F i)) -> nilpotent G.
Proof.
move=> I r P F; rewrite -!(big_filter r).
elim: {r}(filter P r) (filter_all r P) => [| i r Hrec]; 
  rewrite !(big_seq0, big_adds) /=.
  by move=> _ G <- Hfi; rewrite nilpotent1.
case/andP=> Hpi Hpr G Hpd.
case/dprodGP: (Hpd) => [[G1 G2 Hg1 Hg2 _ _] _] HFi.
move: Hpd (HFi _ Hpi) (Hrec Hpr _ Hg2 HFi); rewrite Hg1 Hg2.
exact: nilpotent_dirprod.
Qed. 
 
End DirectProdProperties.
