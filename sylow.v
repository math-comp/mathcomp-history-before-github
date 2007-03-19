(***********************************************************************)
(* (c) Copyright Microsoft Corporation and Inria. All rights reserved. *)
(*                                                                     *)
(***********************************************************************)
(***********************************************************************)
(*                                                                     *)
(*          Definition of sylow group                                  *)
(*                                                                     *)
(***********************************************************************)
(***********************************************************************)

Require Import ssreflect.
Require Import ssrbool.
Require Import funs.
Require Import eqtype.
Require Import ssrnat.
Require Import seq.
Require Import fintype.
Require Import paths.
Require Import connect.
Require Import groups.
Require Import div.
Require Import action.
Require Import cyclic.
Require Import zp.
Require Import normal.
Require Import rightTranslation.
Require Import tuple.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Section Cauchy.

Open Scope group_scope.

Variable (elt : finGroupType) (H : group elt).

Variable p: nat.
Hypothesis prime_p: prime p.
Hypothesis p_divides_H: dvdn p (card H).


(**********************************************************************)
(*               Cauchy theorem                                       *)
(**********************************************************************)

Let lt1p := prime_gt1 prime_p.
Let zp := zp_group (ltnW lt1p).
Definition make_zp : nat -> zp.
move=> i; apply: make_ord (modn i p) _.
abstract by rewrite ltn_mod ltnW ?lt1p.
Defined.

Let zp1 : zp := make_zp 1.

Lemma make_zp_val : forall x : zp, make_zp (val x) = x.
Proof. case=> i ltip; apply: val_inj => /=; exact: modn_small. Qed.

Lemma zp_power_mul : forall (x : zp) m, x ** m = make_zp (m * val x)%N.
Proof.
move=> x; elim=> [|m IHm]; apply: val_inj => /=; first by rewrite mod0n.
by rewrite -{1}[x]make_zp_val IHm /= modn_add.
Qed.

Lemma zp_power_p : forall x : zp, x ** p = 1.
Proof.
by move=> x; apply: val_inj; rewrite zp_power_mul /= mulnC modn_mull.
Qed. 

Lemma zp1_gen : forall x : zp, zp1 ** val x = x.
Proof.
by move=> x; rewrite zp_power_mul /= (modn_small lt1p) muln1 make_zp_val.
Qed.

Let prod_over_zp f :=
  foldr (fun i x => f (zp1 ** i) * x) (1 : elt) (iota 0 p).

Let X := {t, tfunspace H t && (prod_over_zp t == 1)}.

Definition zprot (f : fgraphType zp elt) x :=
  fgraph_of_fun (fun y => f (x * y)).

Lemma rot1_prod_over_zp : forall f,
  (prod_over_zp (zprot f zp1) == 1) = (prod_over_zp f == 1).
Proof.
move=> f; rewrite /prod_over_zp -(ltnSpred lt1p) -{2}add1n -addn1 !iota_add.
rewrite !foldr_cat /= add0n addnC iota_addl foldr_maps.
rewrite /= g2f.
set y := f _ * 1; have->: f 1 = y; last clearbody y.
  by rewrite -(zp_power_p zp1) -(ltnSpred lt1p) /y mulg1.
rewrite -(eqtype.inj_eq (mulg_injr y^-1)).
rewrite -(eqtype.inj_eq (mulg_injl y^-1) _ 1); gsimpl; congr set1.
elim: (iota _ _) y => [|i s IHs] y /=; gsimpl.
by rewrite g2f -mulgA IHs.
Qed.

Lemma zprot_to1 : forall f, zprot f 1 = f.
Proof. by move=> f; apply/fgraphP=> i; rewrite /zprot g2f mul1g. Qed.

Lemma zprot_to_morph : forall x y f, zprot f (x * y) = zprot (zprot f x) y.
Proof. move=> x y f; apply/fgraphP=> i; rewrite /zprot !g2f; gsimpl. Qed.

Canonical Structure zprot_action := Action zprot_to1 zprot_to_morph.

Definition zp_group : group zp.
exists (isetA zp).
abstract by apply/groupP; split=> [|x y]; rewrite !s2f.
Defined.

Lemma zprot_acts_on_X : closed (orbit zprot_action zp_group) X.
Proof.
apply: intro_closed => f1 f2; first exact: orbit_csym.
case/iimageP=> x _ -> {f2}.
rewrite -(zp1_gen x) /=; elim: {x}(val x) f1 => [|i IHi] f /=.
  by rewrite zprot_to1.
rewrite zprot_to_morph s2f; case/andP; move/tfunspaceP=> Hfx prodf1.
apply: IHi; rewrite s2f {i} rot1_prod_over_zp prodf1 andbT.
by apply/tfunspaceP=> i; rewrite g2f Hfx.
Qed.

Lemma card_X : card X = expn (card H) (p - 1).
Proof.
pose Y := pfunspace 1 {~:(1 : zp)} H.
transitivity (card Y); last first.
  by rewrite card_pfunspace subn1 icardC1 card_ordinal.
pose f t x := if x == 1 then (prod_over_zp t)^-1 else t x.
pose F t := fgraph_of_fun (f t).
have injF : dinjective Y F.
  move=> t1 t2; move/pfunspaceP=> [Yt1 _]; move/pfunspaceP=> [Yt2 _].
  move=> Ft12; apply/fgraphP=> u. 
  have:= erefl (F t1 u); rewrite {2}Ft12 !g2f /f.
  case: eqP => //= -> {u} _; transitivity (1 : elt); last symmetry.
    by apply/eqP; apply/idPn; move/Yt1; rewrite isetC11.
  by apply/eqP; apply/idPn; move/Yt2; rewrite isetC11.
have prodF : forall t, prod_over_zp (F t) = (t 1)^-1 ^ (prod_over_zp t).
  move=> t; rewrite /conjg {-2}/prod_over_zp -(ltnSpred lt1p) /=; gsimpl.
  rewrite g2f /f set11; congr mulg. 
  have: forall i, iota 1 (pred p) i -> (zp1 ** i == 1) = false.
    move=> i; rewrite mem_iota add1n (ltnSpred lt1p).
    move/andP=> [ipos ltip]; apply: negbET.
    by rewrite (zp1_gen (make_ord ltip)) -lt0n.
  elim: (iota _ _ ) => //= i s IHs zpsnot1.
  rewrite g2f /f zpsnot1 ?setU11 ?IHs // => j sj.
  apply zpsnot1; exact: setU1r.
rewrite -(card_diimage injF); apply: eq_card => t; rewrite s2f.
apply/andP/iimageP=> [[]|[t1 Yt1 ->{t}]].
  move/tfunspaceP=> Xt; move/eqP=> Yt; exists (F t); last first.
    apply/fgraphP=> u; rewrite !g2f /f prodF Yt conjg1 invgK.
    by rewrite g2f /f; case: eqP => // ->.
  apply/pfunspaceP; split=> u.
    move/eqP=> dFtu; rewrite s2f; apply/eqP=> Du; case: dFtu.
    by rewrite -{u}Du g2f /f set11 Yt invg1.
  move/imageP=> [v vnot1 ->{u}]; rewrite g2f /f.
  by rewrite s2f eq_sym in vnot1; rewrite (negbET vnot1).
move/pfunspaceP: Yt1 => [Yt1 Xt1]. 
case sup1: (support 1 t1 1); first by move/Yt1: sup1; rewrite isetC11.
move/eqP: sup1 => Dt11; have{Xt1} Xt1: forall u, H (t1 u).
  move=> u; case sup_u: (u == 1); first by rewrite (eqP sup_u) Dt11.
  by apply Xt1; apply/imageP; exists u; rewrite // s2f eq_sym sup_u.
split; last by rewrite prodF Dt11 invg1 conj1g set11.
apply/tfunspaceP=> u; rewrite g2f /f; case: set1 => //.
by rewrite groupV /prod_over_zp; elim: (iota _ _) => //= *; rewrite groupM.
Qed.

Theorem cauchy: exists a, H a && (card (cyclic a) == p).
Proof.
have card_zp: card zp_group = (p ^ 1)%N.
  by rewrite icard_card card_ordinal /= muln1.
have:= mpl prime_p card_zp zprot_acts_on_X; set Z := setI _ _.
rewrite card_X -{1}(leq_add_sub lt1p) /= -modn_mul (eqnP p_divides_H) /=.
pose t1 := fgraph_of_fun (fun _ : zp => 1 : elt).
have Zt1: Z t1.
  apply/andP; split; [| rewrite s2f; apply/andP; split].
    by apply/act_fixP=> x _; apply/fgraphP=> i; rewrite /zprot /t1 !g2f.
    by apply/tfunspaceP=> u; rewrite g2f.
  rewrite /prod_over_zp; apply/eqP; elim: (iota _ _) => //= i s -> {s}.
  by rewrite g2f mul1g.
case: (pickP (setD1 Z t1)) => [t | Z0]; last first.
  by rewrite mod0n (cardD1 t1) Zt1 (eq_card0 Z0) modn_small.
case/and3P=> tnot1; move/act_fixP=> fixt. 
rewrite s2f; case/andP; move/tfunspaceP=> Ht prodt _.
pose x := t 1; exists x; rewrite Ht /=.
have Dt: t _ = x by move=> u; rewrite /x -{2}(fixt u (isetAP _)) g2f mulg1.
have: dvdn (orderg x) p.
  rewrite orderg_dvd -(eqP prodt) -(size_iota 0 p) /prod_over_zp.
  by apply/eqP; elim: (iota _ _) => //= i s <-; rewrite Dt.
case/primeP: prime_p => _ divp; move/divp; case/orP; rewrite eq_sym //.
move/eqP=> Dx1; case/eqP: tnot1; apply/fgraphP=> i.
by rewrite Dt -(gexpn1 x) /t1 g2f -Dx1 (eqP (orderg_expn1 _)).
Qed.

End Cauchy.

Section Sylow.

Open Scope group_scope.

Variable (elt : finGroupType) (K : group elt).

Variable p: nat.
Hypothesis prime_p: prime p.

Let n := logn p (card K).

Hypothesis n_pos: 0 < n.


(*Let*) Lemma DivpCK : dvdn p (card K).
Proof.
apply: (@dvdn_trans (p ^ n)%N); last by rewrite dvdn_exp_max.
by move: n_pos; case: n => // n1 _; rewrite dvdn_expS // dvdnn.
Qed.

(**********************************************************************)
(*  Definition of a sylow group:                                      *)
(*  its a subgroup of cardinal p ^n where n is the largest n such     *)
(*  that p^n divides card k                                           *)
(**********************************************************************)

Definition sylow (L : setType  elt) := 
  and3 (group_set L) (subset L K) (card L = p ^ n)%N.

Lemma sylow_conjsg: forall L x, K x -> 
  sylow L -> sylow (L :^ x).
Proof.
move => L x Kx [group_L sLK card_L]; split.
- exact: (group_set_sconjg (Group group_L)).
- apply/subsetP=> y; rewrite /sconjg s2f; gsimpl => Lyx.
  move: (subsetP sLK _ Lyx) => Kxy.
  by rewrite -groupV in Kx; rewrite -(groupJr y Kx).
by rewrite card_sconjg card_L.
Qed.

Lemma iimage_quotientP: 
  forall A B: group elt, forall (t : finType) (f : _ -> t), 
   (f @: (A/B) = f @: ((A :&: normaliser B)/B)).
Proof.
move=> A B t f; apply/isetP=> x; apply/iimageP/iimageP;
case=> By; case/iimageP=> y Ay dBy ->; case Ny: (normaliser B y);
exists By => //; apply/iimageP.
- by exists y => //; apply/isetIP.
- exists (1:elt) => //; first by apply/isetIP.
  rewrite dBy; apply: (can_inj (@sig_of_cosetK elt B)); apply: val_inj=> /=.
  by rewrite cosetD // coset1.
- by exists y => //; case/isetIP: Ay.
by exists (1:elt) => //; case/isetIP: Ay; rewrite Ny.
Qed.
 
Lemma quotientP : forall (A : group elt) (B : setType elt) (C : cosetType B), 
  reflect (exists x, and3 (A x) (normaliser B x) (C = coset_of B x))
          (quotient A B C).
Proof. 
move=> A B Bx; rewrite (_:(A / B) Bx = (((normaliser B) :&: A) / B) Bx).
  apply:(iffP (iimageP _ _ _)); case.
    by move=> x; case/isetIP=> Nx Ax ->; exists x.
  by move=> x [Ax Nx ->]; exists x => //; apply/isetIP.
apply/iimageP/iimageP; case=> x.
  move=> Ax; rewrite /coset_of /coset. 
  case: Bx; case=> Be BeB=> [[C]]; move: C.
  case Nx : (normaliser B x)=> dBe.
    exists x; first by apply/isetIP.
    apply: (can_inj (@sig_of_cosetK elt B)); apply: val_inj=> /=.
    by rewrite Nx.
  exists (1:elt); first by apply/isetIP. 
  apply: (can_inj (@sig_of_cosetK elt B)); apply: val_inj=> /=.
  by rewrite group1 gmulg1.
by case/isetIP=> Nx Ax ->; exists x.
Qed.

Lemma norm_coset : 
  forall (L : group elt) x y, 
     normaliser L x -> L :* x = L :* y -> normaliser L y.
Proof.
move=> L x y Nx Lxy.
have : (L :* x) y by rewrite Lxy rcoset_refl.
case/rcosetP=> l Ll ->.
rewrite groupM //.
by apply: (subsetP (norm_refl L)); auto.
Qed.

Lemma isetIA: forall A B C : setType elt , A :&: B :&: C = A :&: (B :&: C).
Proof. by move=> A B C; apply/isetP=> x; rewrite !s2f andbA. Qed.

Lemma sylow1_rec: forall i (L : group elt), 0 < i -> i < n -> 
  subset L K -> (card L = p ^ i)%N ->
  exists H: group elt, 
    and4 (subset L H) (subset H K) (L <| H) (card H = p ^ (S i))%N.
Proof.
move=> i L lt0i ltin sLK CL.
have F1: dvdn p (indexg L K).
  case/dvdnP: (dvdn_p_part p (card K)); rewrite /p_part -/n => k1 Hk1.
  apply/dvdnP; exists (muln k1 (p ^ (n - (S i))))%N.
  rewrite -{2}(expn1 p) -mulnA -expn_add addn1 -leq_subS //  subSS.
  have F2: card L > 0 by rewrite (cardD1 1) group1 //=.
  apply/eqP; rewrite -(eqn_pmul2l F2); apply/eqP.
  rewrite (LaGrange sLK) Hk1 CL.
  rewrite (mulnC (p ^ i)) -mulnA -expn_add addnC leq_add_sub //.
  exact : (ltnW ltin).
set (lS0 := rtrans_fix L K).
have F2: (modn (indexg L K) p =  modn (card lS0) p).
  rewrite /lS0 /rtrans_fix /indexg.
  rewrite (@mpl _ _ (trans_action elt) _ _ _ prime_p CL _).
    by congr modn; apply:eq_card => Ha; rewrite !s2f /setI andbC.
  apply: intro_closed=> A B; first exact: orbit_csym.
  case/iimageP=> x Lx ->; case/iimageP=> y Ky ->; apply/iimageP.
  exists (y*x); first by rewrite groupM //; exact: (subsetP sLK x).
  by rewrite /= rcoset_morph.
set (ng_q := K / L).
have F3:card lS0 = card ng_q.
  rewrite /lS0 rtrans_fix_norm -(card_iimage (@coset_set_inj _ L)).
  apply: eq_card=> Lk; rewrite iimage_quotientP.
  apply/iimageP/idP; last first.
    case/iimageP=> Lx QLx ->; case/iimageP: QLx=> x. 
    case/isetIP=> Kx NLx ->; exists x; first by apply/isetIP.
    by rewrite /set_of_coset /= cosetN.
  case=> x; case/isetIP=> Nx Kx ->; apply/iimageP. 
  exists (coset_of L x); first by apply/iimageP; exists x=> //; apply/isetIP.
  by rewrite /set_of_coset /= cosetN.
have F4: dvdn p (card ng_q) by rewrite -F3 /dvdn -F2; apply: F1.
have F5: dvdn p (card (group_quotient L K)) by rewrite /set_of_coset /=.
case (cauchy prime_p F5) => {F1 F2 F3 F4 F5}.
move=> sng; case/andP=> Hsng1 Hsng2.
set H := (coset_of L @^-1: cyclic sng) :&: (normaliser L) :&: K.
have T0 := group_cyclicP sng.
have T1 : group_set H.
  have: group_set ((coset_of L @^-1: cyclic sng) :&: (normaliser L)).
    apply/andP; split.
      apply/isetIP; split; last exact: group1.
      rewrite s2f; case/quotientP: Hsng1=> y [Ky Ny ->].
      by apply/cyclicP; exists 0; rewrite -coset_ofE // gexpn0.
    apply/subsetP => x; unlock smulg smulg_def; rewrite s2f; move/set0Pn.
    case=> y; case/andP; rewrite s2f.
    case/rcosetP=> z; case/isetIP; rewrite s2f => CLz Nz ->.
    case/isetIP; rewrite s2f => CLy Ny.
    apply/isetIP; split; last exact: groupM.
    by rewrite s2f morph_coset_of // groupM.
  by move => gL; apply: (group_setI (Group gL) K).
have T2: subset L H.
  apply/subsetP => x Lx. 
  apply/isetIP; split; last by apply: (subsetP sLK x).
  apply/isetIP; split; first by rewrite s2f coset_of_id // group1.
  by move: x Lx; apply/subsetP; exact: norm_refl.
exists (Group T1); split => //.
- exact: subsetIr.
- have sHN: subset H (normaliser L) by apply/subsetP=>x; do 2 case/isetIP.
  exact: (normal_subset (norm_normal L) sHN).
Admitted.
(*
rewrite -(lLaGrange Hh1) // Hh3.
rewrite (quotient_index Hh1 (normaliser_grp Hi (subgrp_K)) 
         (subset_normaliser Hh1 Hh2) (normaliser_normal Hh2)) //.
  rewrite /L (eq_card (@quotient_image_preimage _ _ _
                      Hh1 (normaliser_grp Hi (subgrp_K))
                    (subset_normaliser Hh1 Hh2) (normaliser_normal Hh2)
                    (cyclic sng))).
  rewrite expnS [muln p _]mulnC; congr muln.
  by exact: (eqP Hsng2).
by exact: quotient_preimage_subset_k.
Qed.
*)

Lemma sylow1: forall i, 0 < i -> i <= n -> 
  exists H: group elt, (subset H K) /\ (card H = p ^ i)%N.
Proof.
elim=> //; case=> [_ _ _| i] => /=. 
  case: (@cauchy _ K _ prime_p DivpCK) => a.
  case/andP => Ha1; move/eqP=> Ha2; rewrite muln1.
  by exists (group_cyclic a); split; first exact: cyclic_h.
move => Rec _ H; case: (Rec _ (ltnW H)) => // g [Hg Cg] {Rec}.
by case: (sylow1_rec _ H Hg Cg) => // ngc [] *; exists ngc. 
Qed.

(**********************************************************************)
(*               First Sylow theorem                                  *)
(**********************************************************************)

Theorem sylow1_cor: exists H: group elt, sylow H.
Proof.
case (@sylow1 n) => // g [Sg Cg]; exists g; split=> //.
exact: set_of_groupP.
Qed.

BELOW NOT EVEN PORTED TO setType

Lemma sylow2: forall H L i,0 <i -> i <= n ->
 subgrp H -> subset H K ->  (card H = p ^ i)%N -> sylow L ->
   exists x, (K x) && subset H (conjsg L x).
Proof.
move => H L i H1 H2 Hsh Hshk Hch Hsl.
move/and3P: Hsl => [[Hsl Hsl1] Hsl2].
set ltrans1 := ltrans subgrp_K Hsl Hshk Hsl1.
set (lS0 := S0 H ltrans1).
have F1: ~~(divn p (lindex L K)).
  apply/negP => Fd.
  move/divnP: Fd => [u Hu].
  have F2: (divn (p ^ (S n)) (card K)).
    apply/divnP; exists u.
    rewrite -(lLaGrange Hsl subgrp_K Hsl1) Hu (eqP Hsl2) expnS (mulnA u).
    exact: mulnC.
  move: F2; rewrite /n dlogn_r;
    last by (move: prime_p; case p => //=; case).
  rewrite (cardD1 1) subgrp1 //=.
have F2:  modn (lindex L K) p =  modn (card lS0) p.
  rewrite -card_rootSet /lS0.
  apply: mpl Hch => //.
    move => x Hx; apply: ltrans_bij => //.
  by move => x y z Hx Hy; apply: ltrans_morph.
rewrite /divn {}F2 in F1.
have F3: exists x, lS0 x.
  apply/set0Pn.
  by move: F1; rewrite /set0b; case (card lS0) => //=; rewrite mod0n.
case: F3 => [[x Hx] Hx3].
move: (andP Hx) => [Hx1 Hx2].
exists x; apply/andP; split => //.
apply/subsetP => y Hy; rewrite -(invg_inv y); apply conjsg_inv => //.
rewrite /conjsg conjgE.
replace (x^-1 * y^-1 * x) with ((y * x)^-1 * x); last by gsimpl.
change (is_true (lcoset L (y * x) x)).
move: (root_connect (lcoset_csym Hsl) (y * x) x).
rewrite lcoset_trans //.
move => H0; rewrite -H0.
rewrite (eqP Hx1).
move/andP: {Hx3}(subsetP Hx3 y Hy) => [Hx3 _].
move: Hx3; rewrite /ltrans1 /ltrans.
case: (wb (H y)); case => e.
move/val_eqP; move/val_eqP => //=.
by move: Hy; rewrite e.
Qed.


(**********************************************************************)
(*               Second Sylow theorem                                 *)
(**********************************************************************)

Lemma sylow2_cor: forall L1 L2,
   sylow L1 -> sylow L2 -> exists x, (K x) /\ (L2 =1 conjsg L1 x).
move => L1 L2 Hl1; move/and3P => [[Hl2 Ml2] Nl2].
case: (sylow2 (i := n) (H := L2) (L := L1)) => //.
  by apply/eqP.
move => x; move/andP => [Hx1 Hx2].
exists x; split => //.
apply/subset_cardP => //.
rewrite conjsg_card (eqP Nl2).
by apply sym_equal; apply/eqP; case/and3P: Hl1.
Qed.


(**********************************************************************)
(*   Definition of the set of sylow set                               *)
(**********************************************************************)

Let ps := powerSet G.
Definition syset (p: ps) := sylow (val p).


(**********************************************************************)
(*   Definition of the group action x |-> [ H |-> xHx^-1              *)
(**********************************************************************)

Definition aconj: 
 forall L (Hl1: subgrp L) (Hl2: subset L K),
 G -> sub_finType syset -> sub_finType syset.
move => L Hl1 Hl2 x.
case (wb (L x)); case => Hkx; last done.
move => [[y Hy] Hy1].
have F1: sylow (conjsg y x).
  by apply: sylow_conjsg => //; apply (subsetP Hl2).
exists ((EqSig _ _ (powerSeq_mem (enum G) (conjsg (G:= G) y x))): ps).
by rewrite /syset //= (eq_sylow (filter_enum _)).
Defined.

Lemma aconj_cancel:
  forall L (Hl1: subgrp L) (Hl2: subset L K),
  forall x, L x -> cancel (aconj Hl1 Hl2 x) (aconj Hl1 Hl2 x^-1).
Proof.
move => L Hl1 Hl2 x Hkx [[y Hy] Hy1].
have F1: L x ^-1 by exact: subgrpV.
rewrite /aconj.
case (wb (L x^-1)); case; last (by rewrite F1); move => H1.
case (wb (L x)); case; last (by rewrite Hkx); move => H2.
do 3 apply/val_eqP => //=.
set (e := (conjsg y x)).
replace y with (filter y (enum G)).
  apply/eqP; apply: eq_filter => z.
  rewrite (eq_conjsg _ (filter_enum e)).
  by rewrite /e /conjsg conjg_conj mulVg conjg1.
apply sym_equal; apply: powerSeq_uniq_eq => //=.
exact: uniq_enum.
Qed.

Lemma aconj_bij:
  forall L (Hl1: subgrp L) (Hl2: subset L K),
  forall x : G, L x -> bijective (aconj Hl1 Hl2 x).
Proof.
move => L Hl1 Hl2 x Hkx.
have F1: L x ^-1 by exact: subgrpV.
exists (aconj Hl1 Hl2 x^-1); first by apply aconj_cancel.
rewrite -{2}(invg_inv x).
by apply aconj_cancel.
Qed.

Lemma aconj_morph: 
  forall L (Hl1: subgrp L) (Hl2: subset L K),
  forall x y z, L x -> L y -> 
  aconj Hl1 Hl2 (x * y) z = aconj Hl1 Hl2 x (aconj Hl1 Hl2 y z).
Proof.
move => L Hl1 Hl2 x y [[z Hz] Hz1] H1 H2.
have F1: L (x * y) by exact: subgrpM.
rewrite /aconj.
case (wb (L (x * y))); case; last (by rewrite F1); move => HH1.
case (wb (L x)); case; last (by rewrite H1); move => HH2.
case (wb (L y)); case; last (by rewrite H2); move => HH3.
do 3 apply/val_eqP => //=.
apply/eqP; apply: eq_filter => z1.
by rewrite /conjsg mem_filter /setI mem_enum andbT  conjg_conj.
Qed.

(**********************************************************************)
(*   First part of the third Sylow theorem                            *)
(**********************************************************************)

Theorem sylow3_div: divn (card syset) (card K).
Proof.
case sylow1_cor => H Hh.
have F1:  (syset (EqSig _ _ (powerSeq_mem (enum G) H)))
by rewrite /syset //= (eq_sylow (filter_enum _)).
set (aconj1 := aconj subgrp_K (subset_refl _)).
replace (card syset) with (card (orbit K aconj1 (EqSig _ _ F1))).
apply: card_orbit_div => //.
  by exact: aconj_bij.
  by exact: aconj_morph.
have F2: (card (sub_finType syset) = card syset).
  exact: card_setA_sub.
rewrite -{}F2.
apply eq_card => x; apply eqb_imp => //= H0.
rewrite /orbit.
have F2 : (sylow (val (val x))).
  case x => //=.
case: (sylow2_cor Hh F2) => y [Hy Hy1].
replace x with (aconj1 y (EqSig _ _ F1)).
  by exact: image_f_imp.
rewrite /aconj1 /aconj.
case (wb (K y)); case; last (by rewrite Hy); move => HH.
do 3 apply/val_eqP => //=.
match goal with |- is_true (_ == ?x) => 
  replace x with (filter x (enum G))
end.
  apply/eqP; apply: eq_filter => z.
  rewrite Hy1.
  exact: (eq_conjsg _ (filter_enum H)).
apply sym_equal; apply: powerSeq_uniq_eq => //=.
exact: uniq_enum.
case x => //= [[x1 Hx1] Hx2] //=.
Qed.

End Sylow.

Section SylowAux.

Open Scope group_scope.

Variable (G : finGroup) (H K L: set G).
Hypothesis subgrp_K: subgrp K.
Hypothesis subgrp_L: subgrp L.
Hypothesis subgrp_H: subgrp H.
Hypothesis subset_HL: subset H L.
Hypothesis subset_LK: subset L K.

Variable p: nat.
Hypothesis prime_p: prime p.
Let n := dlogn p (card K).
Hypothesis n_pos: 0 < n.

Lemma sylow_subset: sylow K p H -> sylow L p H.
Proof.
move/and3P => [H1 H2 H3].
apply/and3P; repeat split => //.
rewrite (eqP H3); apply/eqP.
congr expn.
have F1:= prime_leq_2 _ prime_p.
apply: eqn_antisym.
  rewrite -dlogn_leq -?(eqP H3) //.
    by exact: subgrp_divn.
  by rewrite (cardD1 1) subgrp1.
apply divn_dlogn => //.
  by rewrite (cardD1 1) subgrp1.
by exact: subgrp_divn.
Qed.

End SylowAux.

Section Sylow3.

Open Scope group_scope.

Variable (G : finGroup) (K : set G).
Hypothesis subgrp_K: subgrp K.

Variable p: nat.
Hypothesis prime_p: prime p.

Let n := dlogn p (card K).

Hypothesis n_pos: 0 < n.

(**********************************************************************)
(*   Second part of the third Sylow theorem                           *)
(**********************************************************************)
Lemma sylow3_mod: modn (card (syset K p)) p = 1%N.
Proof.
case (sylow1_cor subgrp_K prime_p n_pos)  => H Hh.
have F1: subgrp H by case/and3P: Hh.
have F2: subset H K by case/and3P: Hh.
have F3: (card H = p ^ n)%N by (apply/eqP; case/and3P: Hh).
set S1 := sub_finType (syset K p).
set aconj1 := aconj subgrp_K F1 F2 (p := p).
set S01 := S0 H aconj1.
have F4: (card S1 = card (syset K p)).
  exact: card_setA_sub.
rewrite -{}F4.
have F4: modn (card S1) p = modn (card S01) p.
  apply: mpl F3 => //.
  exact: aconj_bij.
  exact: aconj_morph.
rewrite {}F4.
rewrite -(@modn_small 1%N p); last by case: p prime_p => //=; case.
congr modn.
have F4:  (syset K p (EqSig _ _ (powerSeq_mem (enum G) H))).
  by rewrite /syset //= (eq_sylow _ _ (filter_enum _)).
set h1:= @EqSig _ (syset K p) _ F4.
have F5: S01 h1.
  apply/subsetP => x Hx.
  apply/andP; split => //.
  rewrite /aconj1 /aconj.
  case (wb (H x)); case; last (by rewrite Hx); move => HH.
  do 4 apply/val_eqP => //=.
  apply/eqP; apply: eq_filter => z.
  rewrite (eq_conjsg _ (filter_enum H)).
  rewrite /conjsg conjgE.
  apply/idP/idP => HH1.
    replace z with (x * (x^-1 * z * x) * x^-1); last gsimpl.
    apply subgrpM => //; last by exact: subgrpV.
    by apply subgrpM => //.
  apply subgrpM => //.
  by apply subgrpM => //; first by exact: subgrpV.
have F6: forall x, S01 x -> x = h1.
  move => [[x Hx] Hx1] H1.
  case (and3P Hx1) => //= G1 G2 G3.
  have F7: subset H (normaliser x K). 
    apply/subsetP => y Hy.
    apply/andP; split; last by apply (subsetP F2).
    apply/subsetP => z Hxy.
    rewrite /conjsg conjgE.
    have F8: stabiliser H aconj1 (EqSig _ _ Hx1) y.
      by apply: (subsetP H1).
    move/andP: F8 => [H2 H3].
    move: H2; rewrite /aconj1 /aconj.
    case (wb (H y)); case; last by rewrite Hy.
    move => He; move/eqP; move/val_eqP.
    move/eqP; move/val_eqP => //= H4.
    rewrite -{2}(eqP H4) filter_enum.
    by rewrite /conjsg conjgE eq_refl.
  have N1 := (subset_normaliser G1 G2).
  have N2 := (normaliser_normal G2).
  have N3 := normaliser_grp x subgrp_K.
  have N4 := (normaliser_subset x K).
  have F8 : sylow (normaliser x K) p H.
    apply: (sylow_subset (K := K)) => //.
  have F9 : sylow (normaliser x K) p x.
    apply: (sylow_subset (K := K)) => //.
  case: (sylow2_cor N3 prime_p _ F9 F8).
    apply: (@leq_trans (dlogn p (card x))).
      rewrite (eqP G3).
      rewrite dlogn_expn //.
      exact: prime_leq_2.
    apply: divn_dlogn => //; first by exact: prime_leq_2.
      by rewrite (cardD1 1) subgrp1.
    by exact: subgrp_divn.
  move => u [Hu Hu1].
  have F10:= (conjsg_normal N3 N2 Hu).
  have F11 : x =1 H.
    by move => z; rewrite -F10 -Hu1.
  rewrite /h1; apply/val_eqP => //=.
  apply/eqP; apply/val_eqP => //=.
  rewrite -(eq_filter (F11)).
  apply/eqP; apply: powerSeq_uniq_eq => //.
  by rewrite uniq_enum.
rewrite -(card1 (d := sub_finType (syset K p)) h1).
apply eq_card => x; apply/idP/idP => HH1.
  by rewrite (F6 x).
by rewrite -(eqP HH1).
Qed.

End Sylow3.

Unset Implicit Arguments.
