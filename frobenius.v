(***********************************************************************)
(* (c) Copyright Microsoft Corporation and Inria. All rights reserved. *)
(*                                                                     *)
(***********************************************************************)
(***********************************************************************)
(*                                                                     *)
(*  Frobenius theorem                                                  *)
(*                                                                     *)
(***********************************************************************)
(***********************************************************************)

Require Import ssreflect ssrbool ssrfun ssrnat.
Require Import eqtype fintype div prime finset.
Require Import groups morphisms normal cyclic center pgroups.

(* Require Import seq paths connect zp. *)

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Import GroupScope.

Section Kb.

Variables (gT : finGroupType) (H : {group gT}).
Variable x : gT.
Hypothesis Hx : x \in H.

Lemma KB_image: forall p (Hp : prime p) l s,
  #[x] = (p ^ l.+1)%N -> coprime p s ->
  [set z \in 'C_H[x] | #[z] %| s] / <[x]>
    = [set z \in 'C_H[x] / <[x]> | #[z] %| s].
Proof.
move=> p Hp l s H1 H2; apply/setP=> x1; rewrite inE.
apply/morphimP/andP=> [[z Nz cxzs ->{x1}]|[]].
  move: cxzs; rewrite inE; case/andP=> cxz zs.
  split; first by apply/morphimP; exists z.
  apply: dvdn_trans zs; exact: morph_order.
case/morphimP=> z Nz cxz ->{x1} zs1.
exists z.`_p^'; first exact: groupX.
  rewrite inE groupX //= order_dvd -consttX; apply/eqP; apply/constt1P.
  have: z ^+ s \in <[x]>.
    move: zs1; rewrite order_dvd -morphX //; move/eqP.
    by apply: coset_of_idr; exact: groupX.
  by apply: mem_p_elt; rewrite /pgroup [#|_|]H1 pnatNK pnat_exp pnat_id.
rewrite morph_constt //= constt_p_elt //.
by apply: (pnat_dvd zs1); rewrite p'natE -?prime_coprime.
Qed.

Lemma KB_card_image: forall p (Hp : prime p) l s,
    #[x] = (p ^ l.+1)%N -> coprime p s ->
  #|[set z \in 'C_H[x] | #[z] %| s]|
     = #|[set z \in 'C_H[x] / <[x]> | #[z] %| s]|.
Proof.
move=> p Hp l s Hx1 Hx2; have sCN := subsetP (subcent1_cycle_norm x H).
symmetry; rewrite -(KB_image Hp Hx1 Hx2) /quotient morphimEsub; last first.
  by apply/subsetP=> z; rewrite inE; case/andP; move/sCN.
apply: card_dimset=> y1 y2; rewrite 2!inE.
case/andP=> Cy1 y1s; case/andP=> Cy2 y2s; case/ker_rcoset; auto => z.
rewrite ker_coset => x_z def_y1.
have p's: p^'.-nat s by rewrite p'natE -?prime_coprime.
rewrite -(constt_p_elt (pnat_dvd y1s p's)) def_y1 consttM.
  rewrite (constt1P _ _ _) ?mul1g ?(constt_p_elt (pnat_dvd y2s p's)) //.
  by apply: mem_p_elt x_z; rewrite /pgroup pnatNK [#|_|]Hx1 pnat_exp pnat_id.
apply: commute_sym; apply: commute_cycle_com (cyclenn _) _ x_z.
by case/setIP: Cy2=> _; move/cent1P.
Qed.

End Kb.


Section PConstituent.

Variable p s : nat.
Hypothesis primep : prime p.
Hypothesis coprimeps : coprime p s.
Variable gT : finGroupType.
Variable G : {group gT}.

Definition spconst x := 
  [set y \in G | (y.`_p == x) && (#[y] %| #[x] * s)].
  
Lemma spconst_uniq: forall x1 x2 y,
  y \in spconst x1 -> y \in spconst x2 -> x1 = x2.
Proof.
move=> x1 x2 y; rewrite !inE.
case/and3P => _ H1 _; case/and3P => _ H2 _.
by rewrite -(eqP H1); apply/eqP.
Qed.

Lemma spconst_conjgs: forall a b,
  b \in G -> spconst (a ^ b) = spconst a :^ b.
Proof.
move => a b Hb; apply/setP => x; apply/idP/idP.
  rewrite mem_conjg !inE; case/and3P=> H1 H2 H3; apply/and3P; split.
  - by rewrite groupJr ?groupV.
  - by rewrite consttJ (eqP H2) conjgK.
  by move: H3; rewrite !orderJ.
case/imsetP=> y; rewrite !inE; case/and3P=> H1 H2 H3 ->{x}; apply/and3P; split.
- exact: groupJ.
- by rewrite consttJ (eqP H2).
by move: H3; rewrite !orderJ.
Qed.

Lemma spconst_card: forall a b, b \in G -> #|spconst (a ^ b)| = #|spconst a|.
Proof. by move=> a b Hb; rewrite spconst_conjgs // card_conjg. Qed.

Lemma pconst_subset_centralizer : forall y, spconst y \subset 'C_G[y].
Proof.
move=> y; apply/subsetP=> x; rewrite inE; case/and3P=> Hx1 Hx2 Hx3.
apply/subcent1P; split=> //.
apply: commute_sym; rewrite -(eqP Hx2); exact: commuteX.
Qed.

Lemma pconst_mul_in: forall y z l, 
  y \in G -> z \in G -> commute y z -> #[y] = (p ^ l.+1)%N -> #[z] %| s ->
  y * z \in spconst y.
Proof.
move => y z l Hy Hz H H1 H2; rewrite inE groupM // consttM //.
have npz: ~~ (p %| #[z]).
  move: coprimeps; rewrite prime_coprime //; apply: contra => pz.
  exact: dvdn_trans H2.
have F0: coprime #[y] #[z] by rewrite H1 coprime_expl ?prime_coprime.
rewrite order_mul // dvdn_pmul2l // H2 andbT /= constt_p_elt.
  by rewrite (constt1P _ _ _) ?mulg1 // /p_elt p'natE.
by rewrite /p_elt H1 pnat_exp pnat_id.
Qed.

Lemma pconst_image: forall y l,
   y \in G -> #[y] = (p ^ l.+1)%N ->
  (fun x => x.`_p^') @: spconst y = [set z \in 'C_G[y] | #[z] %| s]. 
Proof.
move=> y l Hy0 Hy; apply/setP=> x1; rewrite inE /=.
apply/imsetP/idP => [[y1 Hy1 ->{x1}] | ].
  rewrite groupX ?(subsetP (pconst_subset_centralizer y)) //=.
  move: Hy1; rewrite inE; case/and3P=> // _; move/eqP=> <-.
  by rewrite -[#[y1]](partnC p) // !order_constt dvdn_pmul2l.
case/andP; case/setIP=> Gx1; move/cent1P=> cx1 H2.
exists (y * x1); first exact: pconst_mul_in Hy _.
rewrite consttM // (constt1P _ _ _) ?mul1g ?constt_p_elt // /p_elt ?pnatNK.
  move: coprimeps; rewrite p'natE ?prime_coprime //; apply: contra => px1.
  exact: dvdn_trans H2.
by rewrite Hy pnat_exp ?pnat_id.
Qed.

Lemma pconst_card : forall y l,
  y \in G -> #[y] = (p ^ l.+1)%N ->
  #|spconst y| = #|[set z \in 'C_G[y] | #[z] %| s]|. 
Proof.
move=> y l Hy H; symmetry; rewrite -(pconst_image Hy H).
apply: card_dimset => y1 y2; rewrite -{3}[y1](consttC p) -{3}[y2](consttC p).
by rewrite !inE; do 2![case/and3P=> _; move/eqP=> -> _] => ->.
Qed.

Lemma pconst_card_KRG : forall y l, y \in G -> 
  #[y] = (p ^ l.+1)%N ->  
  #|spconst y| = #|[set z \in 'C_G[y] / <[y]> | #[z] %| s]|.
Proof.
by move=> y l Hy H; rewrite (pconst_card Hy H) (KB_card_image G primep H).
Qed.

Definition spconstw y := 
  \bigcup_(i \in rcosets 'C_G[y] G) spconst (y ^ repr i).

Lemma spconstwP: forall x y, y \in G ->
  reflect (exists i, (i \in G) && (x \in spconst (y ^ i))) (x \in spconstw y).
Proof.
move => x y Hy; apply: (iffP idP).
 case/bigcupP => i Hi1 Hi2.
 exists (repr i); rewrite Hi2 andbT.
 case/rcosetsP: Hi1 => x1 Hx1 Hx2.
 move: (@repr_rcosetP gT 'C_G[y] x1).
 rewrite -Hx2.
 case => x2; rewrite inE; case/andP => Hx3 _.
 exact: groupM.
case => i; case/andP => Hi1 Hi2.
set r := 'C_G[y] :* i.
apply/bigcupP; exists r; first by apply/rcosetsP; exists i.
case: (repr r) / (repr_rcosetP 'C_G[y] i) => z /=; case/subcent1P=> _.
by move/commgP; move/conjg_fixP; rewrite conjgM => ->.
Qed.

Lemma card_spconstw: forall y l, y \in G -> #[y] = (p ^ l.+1)%N ->  
  #|spconstw y| = 
   (#|G : 'C_G[y]| * #|[set z \in 'C_G[y] / <[y]> | #[z] %| s]|)%N.
Proof.
move=> y l Hy Oy.
rewrite /spconstw (@card_setnU_id _ _ _ _ #|spconst y|).
- by rewrite -(pconst_card_KRG _ Oy).
- move => u v x Hu Hv /= Hsu Hsv.
  case/rcosetsP: Hu Hsu => i1 /= Hi1 ->{u}.
  case: (repr _) / (repr_rcosetP 'C_G[y] i1) => j1 Hj1 Hsu.
  case/rcosetsP: Hv Hsv => i2 /= Hi2 ->{v}.
  case: (repr _) / (repr_rcosetP 'C_G[y] i2) => j2 Hj2 Hsv.
  apply: rcoset_trans1 => /=; rewrite mem_rcoset; apply/subcent1P; split.
    by rewrite !in_group.
  apply/commgP; apply/conjg_fixP.
  have:= spconst_uniq Hsu Hsv; rewrite !conjgM.
  move: Hj1 Hj2; do 2![case/subcent1P=> _; move/commgP; move/conjg_fixP->].
  exact: (canLR (conjgK _)).
move=> x; case/rcosetsP=> i2 /= Hi2 ->; apply: spconst_card.
case: (repr _) / (repr_rcosetP 'C_G[y] i2) => y1; case/setIP=> Gy1 _.
exact: groupM.
Qed.

End PConstituent.

Section Frob.

Theorem frobenius: forall (gT : finGroupType) (G : {group gT}) n,
  n %| #|G| -> n %| #|[pred z \in G | #[z] %| n]|.
Proof.
pose f gT (H : group gT) n := [pred z \in H | #[z] %| n].
change (forall gT (G : group gT) n, n %| #|G| -> n %| #|f gT G n|).
move => gT G.
move: {G}#|G| {-2}G (leqnn #|G|) => n.
elim: n gT.
  by move=> gT H; move: (ltn_0group H); case: #|H|.
move=> k Rec gT G; rewrite leq_eqVlt; case/orP => Hk n Hn;
    last apply Rec => //.
have Hn1: n <= #|G| by apply: dvdn_leq. 
move: Hn; rewrite -(@subKn n #|G|) //.
set e := _ - n; elim: e {-2}e (leqnn e).
  case => // _ _; rewrite subn0.
  apply/dvdnP; exists 1%N; rewrite mul1n.
  apply: eq_card => x.
  rewrite inE /= /order; case E1: (x \in G) => //=.
  by rewrite cardSg // cycle_subG.
move => n1 Hrec e.
rewrite leq_eqVlt; case/orP => H H1; last apply Hrec => //.
move: H1; rewrite (eqP H).
set n2 := _ - n1.+1.
have Hn2: n2 < #|G| by rewrite /n2 (eqP Hk) ltnS subSS leq_subr.
move: (leq0n n2); rewrite leq_eqVlt; case/orP.
  move => HH; rewrite -(eqP HH).
  case/dvdnP; move => x; rewrite muln0 => Hx.
  by move: Hn2; rewrite Hx.
rewrite leq_eqVlt; case/orP;
  first by move => HH; rewrite -(eqP HH) !dvd1n.
move => Hn2b; case/dvdnP => [k1 Hk1].
have Hn2b0: 0 < n2 by case: (n2) Hn2b.
have HHk: 1 < k1.
  case: k1 Hk1 Hk Hn2; first by move => ->.
  case => //.
  by move => ->; rewrite mul1n ltnn.
pose p := pdiv k1.
have Hp := prime_pdiv HHk; rewrite -/p in Hp.
have Hp0: 0 < p by case: p Hp.
have Hp1: n2 * p %| #|G| by rewrite mulnC Hk1 dvdn_pmul2r ?dvdn_pdiv.
have Hp2: n2 * p <= #|G| by apply dvdn_leq => //; rewrite (eqP Hk).
have D1: n2 %| #|f gT G (n2 * p)%N|.
  apply: (@dvdn_trans (n2 * p)) => //.
    by rewrite dvdn_mulr ?dvdnn.
  rewrite -(@subKn (n2 * p) #|G|) //.
  apply Hrec; last by rewrite subKn.
  rewrite leq_sub_add -(@subnK n1.+1 #|G|).
    rewrite -ltnS -/n2 -[(_ + n1).+1]addnS addnC ltn_add2r.
    by rewrite -{1}(mul1n n2) mulnC ltn_pmul2l // prime_gt1.
  apply ltn_trans with (n1.+1); first exact: ltnSn.
  by rewrite -ltn_0sub -/n2; case: (n2) Hn2b.
rewrite -(@dvdn_addr #|predI (f gT G (n2 * p)%N) (predC (f gT G n2))|).
  case/dvdnP: D1 => u Hu; apply/dvdnP; exists u; rewrite -Hu.
  rewrite -(cardID (f gT G n2) (f gT G (n2 * p)%N)) addnC.
  congr (_ + _); last by apply: eq_card => x; rewrite !inE /= andbC.
  apply: eq_card => x; rewrite [f]lock !inE /= !inE /= -lock andbC /=.
  by case: andP => //= [[-> /= HH]]; rewrite (dvdn_trans HH) ?dvdn_mulr.
case (pfactor_coprime Hp Hn2b0) => s.
rewrite mulnC; set l := logn p n2 => Hsl1 Hsl.
have P1: 0 < p ^ (l.+1) by rewrite ltn_0exp Hp0.
set A := (predI _ _).
have F1: forall z, z \in A ->
  exists u, coprime p u &&  (#[z] == u * p ^ l.+1)%N.
- move => z; case/andP => /=; case/andP => H1 Hb1 /=.
  rewrite H1 /=; move/negP => H2. 
  case/dvdnP: Hb1 => u Hu.
  case E1: (p %| u).
    case/dvdnP: (idP E1) => u1 Hu1.
    case H2; apply/dvdnP; exists u1.
    apply/eqP; rewrite -(@eqn_pmul2r p) //.
    by rewrite Hu Hu1 -mulnA (mulnC p) mulnA eq_refl.
  have E2: p ^ l.+1 %| #[z].
    rewrite -(@gauss _ u); first by
      rewrite -Hu Hsl expnS (mulnC _ p) mulnA dvdn_mulr ?dvdnn.
    by rewrite coprime_expl // prime_coprime // E1.  
  case/dvdnP: E2 => u1 Hu1.
  exists u1; rewrite Hu1 eq_refl andbT.
  have E2: (s == u * u1)%N.
    rewrite  -(@eqn_pmul2r (p ^ (l.+1))) //.
    by rewrite -mulnA -Hu1 -Hu (mulnC _ p) Hsl mulnA -expnS mulnC.
  rewrite (eqP E2) coprime_mulr in Hsl1.
  by case/andP: Hsl1.
rewrite {1}Hsl gauss_inv; last first.
  case: (l) => [| u]; last by rewrite coprime_expl.
  by rewrite expn0 /coprime -dvdn1 dvdn_gcdl.
apply/andP;split.
(* First case *)
  apply: (@dvdn_trans  ((p ^ l) * (p - 1))%N);
    first by rewrite dvdn_mulr.
  pose e1 x : pred gT := generator <[x]>.
  have F2: (wpartition [set x | A x] (fun x => set_of (e1 x)) [set x | A x]).
    split.
      move=> u v x; rewrite /= !inE => Hu Hv Hu1 Hu2 y; rewrite /= !inE.
      by congr (_ == _); rewrite ((_ =P <[x]>) Hu1) ((_ =P <[x]>) Hu2).
    apply/eqP; apply/setP=> x; rewrite inE; apply/bigcupP/idP=> [[y]| Ax].
      rewrite !inE /= /f -andbA; case/and3P=> Gy y_p_n2; rewrite Gy /= => y_p_n2' e1_y_x.
      have{e1_y_x} e_x_y: <[x]> = <[y]> by symmetry; apply/eqP.
      have ->: x \in G.
        by rewrite -cycle_subG e_x_y cycle_subG.
      by rewrite /order e_x_y y_p_n2.
    by exists x; rewrite inE // [e1 _ _]eqxx.
  rewrite -cardsE; apply: card_dvdn_partition F2 _ => x; rewrite inE => Ax.
  case: (F1 _ Ax) => z; case/andP => Hz Hz1.
  rewrite cardsE -phi_gen (eqP Hz1) phi_mult.
    rewrite phi_prime_k // dvdn_mull //.
    by rewrite expnS muln_subr muln1 (mulnC p) dvdnn.
  by rewrite coprime_sym coprime_expl.
(* Second case *)
have F2: wpartition [set z \in G | #[z] == p ^ l.+1]%N
                    (spconstw p s G) [set x | A x].
  split.
    move=> u v x /=; rewrite !inE; case/andP => Hu Hu0; case/andP => Hv Hv0.
    case/(spconstwP _ _ _ Hu) => u1; case/andP => Hub1 Hu1.
    case/(spconstwP _ _ _ Hv) => u2; case/andP => Hub2 Hu2.
    have F2:= (spconst_uniq Hu1 Hu2).
    move=> x1; apply/spconstwP/spconstwP=> // [] [i]; case/andP => Hi1 Hi2.
      exists (u2 * (u1^-1 * i)); rewrite !groupM ?groupV //=.
      by rewrite (_ : v ^ _ = u ^ i) // !conjgM -F2 conjgK.
    exists (u1 * (u2^-1 * i)); rewrite !groupM ?groupV //=.
    by rewrite (_ : u ^ _ = v ^ i) // !conjgM F2 conjgK.
  apply/coverP; split.
     move => x; rewrite inE; case/andP => Hpx Hx; apply/subsetP => y.
     case/(spconstwP _ _ _ Hpx) => i; case/andP => Hpi.
     rewrite /spconst inE; case/and3P => Hi0 Hi1 Hi2.
     rewrite inE /= Hi0 -{2}[#[y]](partnC p) //= -order_constt (eqP Hi1).
     rewrite orderJ in Hi2; rewrite Hsl mulnAC -expnSr -(eqP Hx) Hi2 /=.
     rewrite orderJ (eqP Hx) expnSr -mulnA.
     rewrite dvdn_pmul2l ?ltn_0exp ?ltn_0prime //.
     move: Hsl1 ; rewrite prime_coprime //; apply: contra; apply: dvdn_trans.
     exact: dvdn_mulr.
  move=> x; rewrite inE=> Hx.
  case: (F1 x) => // t; case/andP => Ht1 Ht2.
  have F2: #[x.`_p] = (p ^ l.+1)%N.
    by rewrite order_constt (eqP Ht2) p_part // logn_gauss // pfactorK.
  have F3: x \in G by case/andP: Hx; case/andP. 
  exists x.`_p; first by rewrite inE groupX // F2 eqxx.
  apply/spconstwP; first by rewrite groupX.
  exists (1 : gT); rewrite conjg1 group1 /=.
  rewrite inE F3 eqxx /= F2 expnS -mulnA -Hsl mulnC.
  by case/andP: Hx; case/andP.
rewrite -cardsE; apply: (card_dvdn_partition F2) => x.
rewrite inE; case/andP=> Hbx Hx.
rewrite (card_spconstw _ _ _ (eqP Hx)) //.
set KRG := (quotient _ _).
set cKRG := #|KRG|.
have F3: #|KRG| = #|'C_G[x] : <[x]>|.
  apply: card_quotient.
  exact: subcent1_cycle_norm.
have F4: #|'C_G[x]| = (#|KRG| * #[x])%N.
  rewrite F3 /order.
  apply sym_equal; rewrite mulnC; apply: LaGrange => //=.
  exact: subcent1_cycle_sub.
have F5: cKRG <= k.
  rewrite (eqP Hx) in F4.
  have F5: #|'C_G[x]| %| #|G|.
    by apply: cardSg; exact: subcent1_sub.
  rewrite F4 in F5.
  rewrite -ltnS -(eqP Hk).
  have F6: 0 < #|G| by rewrite (eqP Hk).
  move: (dvdn_leq F6 F5) => H1.
  apply: (leq_trans _ H1). 
  rewrite -(muln1 cKRG) /cKRG ltn_pmul2l.
    apply (@leq_trans ((l.+1).+1)) => //.
    apply ltn_expl; exact: prime_gt1.  
  case E1: #|KRG| => //.
  move: (card0_eq E1) => H2.
  move: (H2 1) => //=.
  by rewrite /KRG group1.
have F6b := (dvdn_gcdr cKRG s).
have F6 := (dvdn_gcdl cKRG s).
have ->: [set z \in KRG | #[z] %| s]
           = [set z \in KRG | #[z] %| gcdn cKRG s].
  apply/setP=> z /=; rewrite 2!inE; case Kz: (z \in KRG) => //=.
  apply/idP/idP=> z_s; last exact: dvdn_trans z_s (dvdn_gcdr _ _).
  by rewrite dvdn_gcd // order_dvd_g.
case/dvdnP: (Rec _ (quotient_group _ _) F5 _ F6) => c.
rewrite cardsE => ->; set r := #|_ : _|.
have F8: #|G| = (r * #|'C_G[x]|)%N.
  apply sym_equal; rewrite mulnC; apply: LaGrange => //.
  by exact: subcent1_sub.
rewrite F4 (eqP Hx) in F8. 
apply: (@dvdn_trans (r * gcdn #|KRG| s)); last first.
  by apply/dvdnP; exists c; rewrite mulnA (mulnC r) !mulnA.
case/dvdnP: (dvdn_gcdl #|KRG| s) => u1 Hu1.
case/dvdnP: (dvdn_gcdr #|KRG| s) => u2 Hu2.
have F9: (gcdn #|KRG| s == 0) = false.
  move: (ltn_0gcd #|KRG| s).
  move: Hn2b; rewrite Hsl; case s => [|s1 _]; first by rewrite muln0.
  by rewrite /= orbT; case gcdn.
have Hu3: coprime u1 u2.
  move: (refl_equal (gcdn #|KRG| s)).
  rewrite -{2}(@muln1 (gcdn _ _)).
  rewrite {1}Hu1 {2}Hu2 (mulnC u1) (mulnC u2) gcdn_mul2l.
  by move/eqP; rewrite eqn_mul2l F9.
rewrite {1}Hu2 dvdn_pmul2r //; last by case: gcdn F9.
rewrite coprime_sym in Hu3.
rewrite -(gauss _ Hu3) -(@dvdn_pmul2r (gcdn #|KRG| s));
  last by case: gcdn F9.
rewrite -Hu2 -mulnA (mulnC r) mulnA -Hu1.
have F10: coprime s (p ^ (l.+1)).
  by rewrite coprime_sym coprime_expl.
rewrite mulnC -(gauss _ F10) mulnC -mulnA -F8.
by rewrite Hk1 Hsl mulnA dvdn_mull.
Qed.

End Frob.

Unset Implicit Arguments.
