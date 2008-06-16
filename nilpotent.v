Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq div.
Require Import fintype paths connect finfun ssralg bigops finset.
Require Import groups commutators automorphism normal center.
Require Import dirprod group_perm. 
Import GroupScope.


Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Import GroupScope.

Section LowerCentral.

Variable gT : finGroupType.
Notation sT := {set gT}.

Definition lcn (G: sT) := nosimpl 
  fix iter (n: nat)  {struct n} :=
    if n is n1.+1 then [~: iter n1, G] else G.

Lemma lcnS G n: lcn G n.+1 = [~: lcn G n, G].
Proof. by done. Qed.

Lemma lcn0 G: lcn G 0 = G.
Proof. by done. Qed.

Definition nilpotent (G: sT) := exists n, trivg (lcn G n).

Definition of_class (G: sT) (n: nat) :=
   trivg (lcn G n) /\ forall m, m < n -> ~~ trivg (lcn G m).

Lemma lcnCH (G: {group gT}) n: characteristic G (lcn G n).
Proof.
by move=> G n; elim: n => [| n Hrec]; try apply: char_comm;
  rewrite // setT_group_char.
Qed.

Lemma lcnGS (G: {group gT}) n : group_set (lcn G n).
Proof.
move=> G n; elim: n => [| n Hrec]; first by exact: groupP.
by exact: group_set_bigcap.
Qed.

Canonical Structure lcn_group n (G: {group gT}) := Group (lcnGS G n).

Lemma lcnSSn (G: {group gT}) n : lcn G n.+1 \subset lcn G n.
Proof.
move=> G n; rewrite lcnS sym_sgcomm subcomm_normal.
case: n => [| n]; first by exact: normG.
by rewrite /= lcnS sym_sgcomm normGR.
Qed.

Lemma lcn_stable (G:{group gT}) n m : 
                     n <= m ->  trivg (lcn G n) -> trivg (lcn G m).
Proof.
move=> G n;elim => [| m Hrec]; first by rewrite leqn0; move/eqP => ->.
rewrite leq_eqVlt;case/orP  ;first by move/eqP=> ->.
rewrite (ltnS n m) => Hnm trivgn;move:(Hrec Hnm trivgn).
case/trivgP => Hm ;rewrite /trivg /= -Hm.
by exact: lcnSSn.
Qed.

Lemma lcnSS0 (G: {group gT}) n : lcn G n \subset G.
Proof.
move=> G; elim => [| n Hrec]; first by exact: subset_refl.
apply: subset_trans (lcnSSn _ _) Hrec.
Qed.

Lemma lcnSSnm (G: {group gT}) n m : 
  m <= n  -> lcn G n \subset lcn G m.
Proof.
move=> G n m; elim: n => [| n Hrec]; first by case: m.
rewrite leq_eqVlt; case/orP; first by move/eqP->.
move=> Hn; apply: (subset_trans (lcnSSn G n)).
by apply: Hrec.
Qed.

Lemma lcnNM0 (G: {group gT}) n : lcn G n <|  G.
Proof.
move=> G n; apply: normal_char; exact: lcnCH.
Qed.

Lemma lcnNMn (G: {group gT}) n : lcn G n.+1 <|  lcn G n.
Proof.
move=> G n; rewrite /normal_subset lcnSSn.
apply/subsetP => x Hx; apply/normgP.
apply/eqP;  rewrite eqset_sub_card card_conjg leqnn andbT lcnS -genJg gen_subG.
apply/subsetP=> xy; case/imsetP => x1; case/imset2P => x2 x3 Hx2 Hx3 -> ->.
rewrite conjg_Rmul groupM //.
  apply: mem_geng; apply/imset2P; exists x [~ x2, x3]^-1 => //.
  by rewrite groupV !groupM // ?groupV // (subsetP (lcnSS0 G n)).
by apply: mem_geng; apply/imset2P; exists x2 x3.
Qed.

Lemma lcnCT (G: {group gT}) n :
  lcn G n / lcn G n.+1 \subset 'Z(G / lcn G n.+1).
Proof.
move=> G n; apply/subsetP => H1; case/quotientP => x [Hx1 Hx2 ->].
apply/centerP; split.
  apply/quotientP; exists x; split=> //.
  by apply: (subsetP (lcnSS0 G n)).
move=> H2; case/quotientP => y [Hy1 Hy2 ->]; rewrite /commute.
case Ht: (trivm (coset_of  (lcn G n.+1))).
  by rewrite !(trivm_is_cst Ht).
move/negP: Ht; move/negP => Ht.
rewrite -!coset_of_morphM /= ?dom_coset //.
rewrite commgC coset_of_morphM ?dom_coset //;
 try by rewrite !groupM // ?groupV.
have F1: [~ x, y] \in lcn G n.+1.
  rewrite /= lcnS; apply: mem_geng. 
  by apply /imset2P; exists x y.
by rewrite (coset_of_id F1) // mulg1.
Qed.

End LowerCentral.

Section UpperCentral.

Variable gT : finGroupType.
Notation sT := {set gT}.

Definition ucn (G: sT) := nosimpl 
  fix iter (n: nat)  {struct n}: sT :=
    if n is n1.+1 then 
      [set x \in G |  (fun y => [~ x, y]) @: G \subset iter n1] 
    else 1.

Lemma ucn0 (G: sT): ucn G 0 = 1.
Proof. done. Qed.

Lemma ucn1 (G: {group gT}): ucn G 1 = 'Z(G).
Proof.
move=> G; rewrite /ucn.
apply/eqP; rewrite eqset_sub; apply/andP; split; apply/subsetP => x; last first.
  case/centerP => H1 H2; rewrite inE H1; apply/subsetP => y.
  case/imsetP => z Hz ->; rewrite inE; apply/commgP; exact: H2.
rewrite inE; case/andP => H1x H2x.
apply/centerP; split => // y Hy.
have F1: [~ x, y] \in (fun y : gT => [~ x, y]) @: G by apply/imsetP; exists y.
by apply/commgP; move: (subsetP H2x _ F1); rewrite inE.
Qed.

Lemma ucnS (G: {group gT}) n: 
  ucn G n.+1 = [set x \in G |  (fun y => [~ x, y]) @: G \subset ucn G n].
Proof. done. Qed.

Lemma ucnGS (G: {group gT}) n : group_set (ucn G n).
Proof.
move=> G ; elim=> [| n Hrec]; first exact: group_set_unit.
pose g0 := Group Hrec.
apply/group_setP; split.
  rewrite ucnS inE group1.
  by apply/subsetP => x; case/imsetP => y Hy ->; rewrite comm1g (group1 g0).
move=> x y; rewrite ucnS !inE.
case/andP=> H1x H2x; case/andP=> H1y H2y.
rewrite groupM //; apply/subsetP=> z; case/imsetP=> t Ht ->.
rewrite commg_gmult_left (@groupM  _ g0) //; last first.
  by apply: (subsetP H2y); apply/imsetP; exists t.
have F1: [~ x, y] \in ucn G n.
  by apply: (subsetP H2x); apply/imsetP; exists y.
have ->: [~ x, t] ^ y = [~ x, y]^-1 * [~ x, t * y].
  by rewrite commg_gmult_right mulgA mulVg mul1g.
rewrite groupM //; try rewrite groupV; apply: (subsetP H2x).
  by apply/imsetP; exists y.
by apply/imsetP; exists (t * y); rewrite // groupM.
Qed.

Canonical Structure ucn_group (G: {group gT}) n := Group (ucnGS G n).

Lemma ucnSS0 (G: {group gT}) n : ucn G n \subset G.
Proof.
move=> G [| n]; first by exact: sub1G.
by rewrite ucnS; apply/subsetP=> x; rewrite inE; case/andP.
Qed.

Lemma ucnSSn (G: {group gT}) n : ucn G n \subset ucn G n.+1.
Proof.
move=> G; elim=> [| n Hrec]; first by rewrite ucn0; apply: sub1G.
rewrite (@ucnS _ n.+1).
apply/subsetP => x; rewrite {1}ucnS.
rewrite inE; case/andP => H1x H2x.
by rewrite inE H1x; apply: subset_trans Hrec.
Qed.

Lemma ucnCH (G: {group gT}) n : characteristic G (ucn G n).
Proof.
move=> G; elim=> [| n Hrec].
  by rewrite ucn0 trivg_char.
(* Down to the definition :-( *)
apply/subset_charP; split; first by exact: ucnSS0.
move=> f Hf; case/andP: (Hf) => H1f H2f; apply/subsetP=> x; case/imsetP => y /=.
rewrite ucnS inE; case/andP => Hy H1y ->.
rewrite !inE; apply/andP; split; first by rewrite (group_perm.perm_closed _ H1f).
apply/subsetP => z; case/imsetP => z1 Hz1 ->.
pose z2 := (group_perm.perm_inv f z1).
have Hz2: z2 \in G by rewrite -(group_perm.perm_closed _ H1f) group_perm.permKV.
have ->: z1 = f z2 by rewrite group_perm.permKV.
rewrite -(morphic_comm H2f) //.
case/subset_charP: Hrec => _; move/(_ _ Hf).
move/subsetP=> HH; apply: HH.
apply/imsetP; exists [~ y, z2] => //.
by apply: (subsetP H1y); apply/imsetP; exists z2.
Qed.

Lemma ucnNM0 (G: {group gT}) n : ucn G n <| G.
Proof. move=> n G; apply: normal_char; exact: ucnCH. Qed.

Lemma ucnNMn (G: {group gT}) n : ucn G n <| ucn G n.+1.
Proof.
move=> n G; apply/andP; split; first by exact: ucnSSn.
apply/subsetP => x.
rewrite ucnS inE; case/andP => Hx H1x.
rewrite inE; apply/subsetP => y.
case/imsetP => z Hz ->.
rewrite conjg_mulR groupM // groupVl // invg_comm.
apply: (subsetP H1x); apply/imsetP; exists z => //.
by apply: (subsetP (ucnSS0 n G)).
Qed.

Lemma ucnCT (G: {group gT}) n :
  ucn G n.+1 / ucn G n = 'Z(G / ucn G n).
Proof.
move=> G n.
case Ht: (trivm (coset_of (ucn G n))).
  have F1: ucn G n = G.
    apply/eqP; rewrite eqset_sub; case/andP: (ucnNM0 G n).
    by case/trivm_coset_of: Ht => -> ->.
  apply/eqP; rewrite eqset_sub; apply/andP; split; apply/subsetP => x; last first.
    rewrite !inE; case/andP; case/quotientP => y [H1y H2y -> H3y] /=.
    apply/quotientP; exists y; split => //=.
    rewrite ucnS inE H1y.
    by apply/subsetP => y1; case/imsetP => z Hz ->; rewrite F1; exact: groupR.
  case/quotientP => y[H1y H2y ->].
  rewrite coset_of_id ?group1 //= F1.
  by move: H1y; rewrite /= ucnS inE; case/andP.
move/negP: Ht; move/negP => Ht.
have F0: G \subset 'N(ucn_group G n) by case/andP: (ucnNM0 G n).
apply/eqP; rewrite eqset_sub; apply/andP; split; apply/subsetP => x; last first.
  rewrite !inE; case/andP; case/quotientP => y [H1y H2y ->] H3y.
  apply/quotientP; exists y; split => //.
  rewrite /= ucnS inE H1y.
  apply/subsetP => y1; case/imsetP => z Hz ->.
  have F1: coset_of (ucn G n) z \in G / ucn G n.
    by apply/quotientP; exists z; repeat split => //; exact: (subsetP F0).
  apply: coset_of_idr; first by apply: (subsetP F0); exact: groupR.
  rewrite -(commg_coset F0) //.
  by apply/eqP; apply/commgP; apply: (centgP H3y).
case/quotientP => /= y  [H1y  H2y ->].
move: H1y; rewrite ucnS inE; case/andP => H1y H3y.
rewrite inE; apply/andP; split.
  by apply/quotientP; exists y; repeat split => //; apply: (subsetP F0).
apply/centgP => y1; case/quotientP => z [H1z H2z] ->.
apply/commgP; rewrite (commg_coset F0) //.
apply/eqP; apply: coset_of_id.
by apply: (subsetP H3y); apply/imsetP; exists z.
Qed.

End UpperCentral.

Section Properties.

Variable gT : finGroupType.
Notation sT := {set gT}.

Lemma ucn_lcnP (G: {group gT}) n : lcn G n == 1 <-> ucn G n == G.
Proof.
move=> G n; split => Hn; rewrite eqset_sub.
  rewrite ucnSS0 -(lcn0 G) -{1}(subnn n).
  elim: {1 4 5} n (leqnn n) => [| m]; first by rewrite subn0 (eqP Hn) sub1G.
  case: n Hn => // [n Hn Hrec Hlt].
  have F1: m <= n.+1 by rewrite (leq_trans (leqnSn _) Hlt).
  apply/subsetP => y Hy.
  rewrite ucnS inE (subsetP (lcnSS0 G (n - m))) //.
  apply/subsetP => x; case/imsetP => x1 Hx1 ->.
  apply: (subsetP (Hrec F1)); rewrite leq_subS //.
  by exact: commg_in_commgs.
rewrite sub1G andbT -(ucn0  G)  -(subnn n).
elim: {1 3 5} n (leqnn n) => [| i].
  by rewrite subn0 (eqP Hn) (lcn0 G) => _;exact: subset_refl.
case: n Hn => // [n Hn Hrec Hlt].
have F1: i <= n.+1 by rewrite (leq_trans (leqnSn _) Hlt).
have HH: G\subset G by apply: subset_refl.
have H1: [~: lcn G i, G] \subset [~: ucn G (n.+1 - i), G].
  by apply: (genSg (commg_setSS (Hrec F1) HH)).
apply: (subset_trans H1).
rewrite subSS leq_subS // ucnS gen_subG.
apply/subsetP => x.
case/imset2P => x1 x2; rewrite !inE.
case/andP => H1x1 H2x1 Hx2 ->.
apply: (subsetP H2x1).
by apply/imsetP; exists x2.
Qed.

Lemma lcnSS  (H G: {set gT}) n: H \subset G -> (lcn H n) \subset  (lcn G n).
Proof.
move=> H F n HsG.
elim: n => [| n Hrec]; first by rewrite !lcn0.
by rewrite !lcnS; apply: (genSg (commg_setSS _  _)).
Qed.

Lemma nilpotentSS (H G: {group gT}) : 
  H \subset G -> nilpotent G -> nilpotent H.
Proof.
move=> H G HsG; case=> n; case/trivgP=>  Hn.
by exists n; move:(lcnSS n HsG); rewrite Hn.
Qed.

Section FMorph.

Variable gT1 gT2: finGroupType.

Lemma lcn_morph (G: {group gT1}) (f : gT1 -> gT2) n:  
     morphic  G f  ->  f @: (lcn G n) = (lcn (f @:G ) n).
Proof.
move=> G f n Hf.
elim: n => [| n Hrec]; first by rewrite !lcn0.
by rewrite !lcnS (morphic_comms Hf) // ?Hrec // lcnSS0.
Qed.

Lemma morphNL (G: {group gT1}) (f : gT1 -> gT2) : 
      morphic  G f -> nilpotent G -> nilpotent (f @: G).
Proof.
move=> G f Hf; case=> n; case/trivgP=> Hn.
exists n; move:(lcn_morph n Hf).
rewrite /trivg /= Hn => <- . 
apply/subsetP => x; case/imsetP => x0; rewrite inE ; move/eqP => -> ->.
by  rewrite (morphic1 Hf) group1.
Qed.

End FMorph.

Lemma centgSS (L H : {set gT}): L \subset H -> 'C(H) \subset 'C(L).
Proof.
move => L H LsH;apply/subsetP=> x.
move/centgP => cx;apply/centgP=> z Az; apply:cx.
by apply:(subsetP LsH).
Qed.

Lemma lcn_prod (H1 H2 :{group gT}) n: {in H1, central H2} ->  
   lcn  (H1 * H2) n =  lcn  H1 n * lcn  H2 n.
Proof.
move=> H1 H2 n Hcomm.
elim: n => [| n Hrec]; first by rewrite !lcn0.
rewrite !lcnS Hrec;set L1 := (lcn H1 _);set L2 := (lcn H2 _).
have LcnC: forall m, commute (lcn H1 m) (lcn H2 m).
  move => m; apply: normalC;apply:in_central_normal;  apply/centralP.
  apply: (subset_trans (lcnSS0  H1 m)); move/centralP: Hcomm => Hcomm.
  by apply: (subset_trans Hcomm); apply:centgSS; apply:lcnSS0.
rewrite -(comm_mulgenE  (LcnC n.+1)) /=.
apply/eqP; rewrite eqset_sub;apply/andP;split.
  rewrite gen_subG;apply/subsetP=> x; case/imset2P => x1 x2.
  case/mulsgP=>l1 l2 Ll1 Ll2 ->;  case/mulsgP=>h1 h2 Hh1 Hh2 -> Hx.
  rewrite /= comm_mulgenE; last by apply:(LcnC n.+1).
  apply/mulsgP; exists [~ l1, h1][~ l2, h2].
    -apply: mem_geng;apply/imset2P;by exists l1 h1.
    -apply: mem_geng;apply/imset2P;by exists l2 h2. 
  rewrite Hx /commg /conjg.
  have Hl2: l2 \in H2 by rewrite(subsetP (lcnSS0 H2 n )).
  have Hl1: l1 \in H1 by rewrite(subsetP (lcnSS0 H1 n)).
  have hcom: forall x y, x\in H1 -> y \in H2 -> x * y = y *x.
    by move => y1 y2 Hy1 Hy2; apply: (Hcomm y1 Hy1).   
  rewrite (hcom l1) ?groupV // (hcom h1) ?groupV // !invMg.
  apply:(mulg_injl l1); rewrite !(mulgA l1) !mulgV !mul1g. 
  rewrite -!mulgA  (mulgA l2^-1) -(hcom _ l2^-1) ?groupV //.
  apply : (mulg_injl h1);rewrite !(mulgA h1) !mulgV !mul1g.
  gsimpl;rewrite -(hcom l1) // ?groupM // ?groupV //. 
  rewrite -!(mulgA l1);apply : (mulg_injl l1^-1);rewrite !(mulgA l1^-1) !mulVg !mul1g.
  rewrite -(hcom h1)//;gsimpl;rewrite !groupM // ?groupV //.
rewrite comm_mulgenE; last by apply:(LcnC n.+1).
apply /subsetP => x; case/mulsgP => x1 x2.
move/generatedP=> gen1;move/generatedP=> gen2 ->.
apply:groupM.
  apply: gen1; rewrite -gen_subG; apply: genSg; apply/subsetP=> c.
  case/imset2P=> l1 h1 hl1 hh1 -> ; apply/imset2P;exists l1 h1 =>//.
    by apply/mulsgP;exists l1 (unitg gT);rewrite // ?group1 // mulg1.
  by apply/mulsgP; exists h1 (unitg gT);rewrite // mulg1.
apply: gen2; rewrite -gen_subG; apply: genSg; apply/subsetP=> c.
  case/imset2P=> l2 h2 hl2 hh2 ->; apply/imset2P;exists l2 h2 =>//.
  by apply/mulsgP; exists  (unitg gT) l2;rewrite ?group1 ?mul1g.
by apply/mulsgP; exists (unitg gT) h2; rewrite ?mul1g.
Qed.

Lemma prodNL (H1 H2: {group gT}) : 
  {in H1, central H2} -> nilpotent H1 -> nilpotent H2 -> nilpotent (H1*H2).
Proof.
move=> H1 H2 ?; case=> n1 Hn1; case=> n2 Hn2.
exists (maxn n1 n2); rewrite lcn_prod /maxn //.
case e: (n1< n2)=> /=.
  case/trivgP: Hn2 => ->; rewrite mulg1.
  have Hn1n2: n1<=n2 by apply/leP;apply:Lt.lt_le_weak; move/ltP:e.
  apply: (lcn_stable   Hn1n2) => //.
case/trivgP: Hn1 => ->; rewrite mul1g.
apply: (@lcn_stable  _ _ n2)=> //.
by apply/leP; move/ltP:e ; apply:Compare_dec.not_gt.
Qed.



Lemma lcn_setX (H1 H2: {group gT}) n : 
  lcn (setX H1 H2) n = setX (lcn H1 n) (lcn H2 n).
Proof.
move=> H1 H2; elim=> [| n Hrec]; first by rewrite !lcn0.
rewrite !lcnS Hrec.
apply/eqP; rewrite eqset_sub; apply/andP; split.
  rewrite gen_subG.
  apply/subsetP => x; case/imset2P => [[x11 x12] [x21 x22]].
  rewrite inE; case/andP => /= Hx11 Hx12.
  rewrite inE; case/andP => /= Hx21 Hx22 ->.  
  apply/setXP; split => /=.
    by apply: mem_geng; apply/imset2P; exists x11 x21.
  by apply: mem_geng; apply/imset2P; exists x12 x22.
rewrite -setX_gen ?group1;
  try by apply/imset2P; exists (1: gT) (1: gT); rewrite ?group1 ?comm1g.
apply: genSg; apply/subsetP => [[x1 x2]]; rewrite !inE /=.
case/andP; case/imset2P => xx1 xx2 Hxx1 Hxx2 ->.
case/imset2P => yy1 yy2 Hyy1 Hyy2 ->.
by apply/imset2P; exists (xx1,yy1) (xx2,yy2); rewrite // !inE /= ?Hxx1 ?Hxx2.
Qed.

Lemma setXNL (H1 H2: {group gT}) :
  nilpotent (setX H1 H2) <-> nilpotent H1 /\ nilpotent H2. 
Proof.
move=> H1 H2; split; rewrite /nilpotent; case.
  move=> n; rewrite lcn_setX => Hn; split; exists n.
    apply/subsetP => y Hy; move: (subsetP Hn (y, 1)).
    by rewrite !inE /= Hy group1; move/(_ is_true_true); case/andP.
  apply/subsetP => y Hy; move: (subsetP Hn (1, y)).
  by rewrite !inE /= Hy group1; move/(_ is_true_true); case/andP.
case=> n1 Hn1; case => n2 Hn2.
pose m  := maxn n1 n2.
have T1m: trivg (lcn H1 m).
  by apply: subset_trans Hn1; rewrite lcnSSnm // leq_maxr leqnn.
have T2m: trivg (lcn H2 m).
  by apply: subset_trans Hn2; rewrite lcnSSnm // leq_maxr leqnn orbT.
exists m; rewrite lcn_setX.
apply/subsetP =>  [[x y]]; rewrite !inE /=; case/andP => Hx Hy.
by apply/andP; split; [move: (subsetP T1m _ Hx) | move: (subsetP T2m _ Hy)];  
  rewrite !inE.
Qed.

Lemma dirprodNL (G H1 H2: {group gT}) :
  [/\ H1 <| G, H2 <| G, G = H1 * H2 :> set _ & trivg (H1 :&: H2)] ->
  nilpotent H1 -> nilpotent H2 -> nilpotent G.
Proof.
move=> G H1 H2; move/dirprod_normal_isom.
case/andP=> Hm Hi NL1 NL2.
case/andP: Hi; move/eqP<- => _.
apply: morphNL => //.
case: (setXNL H1 H2) => _ HH.
by apply HH; split.
Qed.


Lemma pgroupNL (G: {group gT}) p n: 
  prime p -> #|G| = (p ^ n.+1)%N -> nilpotent G.
Proof.
move=> G p n Hp HG; exists (#|G|.+1).
suff: lcn G #|G|.+1 == 1 by rewrite eqset_sub; case/andP.
apply/ucn_lcnP.
move: (subset_leq_card (ucnSS0 G (#|G|.+1))).
rewrite leq_eqVlt; case/orP => Hp1.
  by rewrite eqset_sub_card ucnSS0 (eqP Hp1) leqnn.
have := group_dvdn (ucnSS0 G (#|G|.+1)).
rewrite {2}HG; case/(dvdn_exp_prime _ _ Hp) => n1 Hn1 H1n1.
have F1: forall m, ucn G m == ucn G m.+1 \/ m <= #|ucn G m.+1|.
  elim => [| m [Hrec | Hrec]]; first by right.
    by left; rewrite ucnS {1}(eqP Hrec).
  move: (subset_leq_card (ucnSSn G m.+1)).
  rewrite leq_eqVlt; case/orP => Hp2; last by right; apply: (leq_trans _ Hp2).
  by left; rewrite eqset_sub_card (eqP Hp2) ucnSSn leqnn.
case: (F1 (#|G|.+1)); last by rewrite ltnNge subset_leq_card // ucnSS0.
move=> HH.
have F2 : #|G/ucn G #|G|.+1| = (p ^ (n - n1).+1)%N.
  rewrite card_quotient -?group_divn ?ucnSS0 //; last
    by  case/andP: (ucnNM0 G #|G|.+1).
  rewrite {1}HG H1n1 -leq_subS.
    by rewrite -{1}(subnK Hn1) expn_add divn_mulr // ltn_0exp prime_pos_natP.
  by rewrite -ltnS -(ltn_exp2l _ _ (prime_gt1 Hp)) -HG -H1n1.
case/negP: (pgroup_ntriv Hp F2).
by rewrite -ucnCT -(eqP HH) trivial_quotient /trivg subset_refl.
Qed.
(* Should be in ssrbool *)
Notation "A \ssubset B" := ((A \subset B) /\ ~(B \subset A))
  (at level 70, no associativity, format "A  \ssubset  B") : bool_scope.

Lemma nilpotentSSS (H G: {group gT}) :
  nilpotent G -> H \ssubset G -> H \ssubset N_(G)(H).
Proof.
move=> H G GNL; case=> HSSG HDG; split.
  by apply/subsetP => x Hx; rewrite inE (subsetP HSSG) // (subsetP (normG H) _ Hx).
case: GNL => n Hn.
have: lcn G n == 1 by  rewrite eqset_sub sub1G andbT; exact: Hn.
move/ucn_lcnP => Ucn UnG.
have F1: exists i, [/\ i < n, ucn G i \subset H & ~ ucn G i.+1 \subset H].
  move: HDG; rewrite -{1}(eqP Ucn).
  elim: n {Hn Ucn} => [| n Hrec] H1; first by case: H1; rewrite ucn0 sub1G.
  case E1: ((ucn G n) \subset H); move/idP: E1 => E1; first by exists n.
  by case Hrec => // i [Hi] His; exists i; split => //; rewrite (leq_trans Hi).
case: F1 => i [H1i H2i H3i].
case E1: (ucn G i.+1 \subset ucn G i); move/idP: E1 => E1.
  by case H3i; apply: subset_trans H2i.
have F2: [~: ucn G i.+1, H] \subset H.
  apply: subset_trans _ H2i.
  suff F2: [~: ucn G i.+1, G] \subset ucn G i.
    by apply: subset_trans _ F2; apply: sgcommSSr. 
  rewrite gen_subG; apply/subsetP => x.
  case/imset2P => x1 x2; rewrite ucnS inE; case/andP => H1x1 H2x1 H1x2 ->.
  by apply: (subsetP H2x1); apply/imsetP; exists x2.
rewrite subcomm_normal in F2.
case: H3i; apply: subset_trans UnG.
apply/subsetP => x Hx; rewrite inE; apply/andP; split; last by apply: (subsetP F2).
by apply: (subsetP (ucnSS0 G i.+1)).
Qed.

End Properties.
