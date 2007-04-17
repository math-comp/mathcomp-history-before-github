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
  and3b (group_set L) (subset L K) (card L == p ^ n)%N.

Lemma sylow_sconjg: forall L x, K x -> 
  sylow L = sylow (L :^ x).
Proof.
have F1: forall L x, K x -> sylow L -> sylow (L :^ x).
  move => L x Kx; case/and3P => group_L sLK card_L.
  apply/and3P; split.
  - exact: (group_set_sconjg (Group group_L)).
  - apply/subsetP=> y; rewrite /sconjg s2f; gsimpl => Lyx.
    move: (subsetP sLK _ Lyx) => Kxy.
    by rewrite -groupV in Kx; rewrite -(groupJr y Kx).
  by rewrite card_sconjg card_L.
move => L x Hx; apply/idP/idP => Hx1; first exact: F1.
by rewrite -[L]sconj1g -(mulgV x) sconjgM F1 // groupV.
Qed.


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
set (lS0 := rtrans_fix L K L).
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
have sgLH : subset L (Group T1) by exact: T2.
(*have sgLH : subgroup L (Group T1) by exact: T2.*)
rewrite -(LaGrange sgLH).
rewrite (_: indexg L _ = card (coset_of L @: H)); last first.
  rewrite -(card_image (@coset_set_inj _ L)).
  apply: eq_card => Lx.
  apply/iimageP/imageP.
    case=> x Hx ->; exists (coset_of L x).
      by apply/iimageP; exists x.
    by case/isetIP: Hx; case/isetIP=>*; rewrite /coset_of /set_of_coset /= cosetN.
  case=> cLx; case/iimageP=>x Hx -> ->; exists x => //.
  by case/isetIP: Hx; case/isetIP=>*; rewrite /coset_of /set_of_coset /= cosetN.
rewrite mulnC CL (_: card (_ @: _) = p) //.
rewrite -(eqP Hsng2).
apply: eq_card => Lx.
apply/iimageP/cyclicP.
  case=> x; case/isetIP; case/isetIP; rewrite s2f; case/cyclicP=> m  dsngm Nx Kx ->.
  by exists m.
case: Lx;case=> Lx CLx [m dsngm]; rewrite -(eqP dsngm) {dsngm}.
case/quotientP: Hsng1=> x [Kx Nx dsng]; rewrite dsng -coset_ofE //.
exists (x ** m) => //.
have Kxm : K (x ** m) by rewrite groupE.
have Nxm : normaliser L (x ** m) by rewrite groupE.
apply/isetIP; split => //; apply/isetIP; split=> //.
by rewrite s2f; apply/cyclicP; exists m; rewrite coset_ofE // dsng.
Qed.

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
case (@sylow1 n) => // g [Sg Cg]; exists g; apply/and3P; split=> //.
  exact: set_of_groupP.
by rewrite Cg.
Qed.

Lemma sylow2: forall (H : group elt) L i, 0 <i -> i <= n ->
 subset H K ->  (card H = p ^ i)%N -> sylow L ->
   exists x, (K x) && subset H (L :^ x).
Proof.
move => H L i H2 Hsh Hshk Hch Hsl.
case/and3P: Hsl => Hsl Hsl1 Hsl2.
set (lS0 := rtrans_fix (Group Hsl) K H).
have F1: ~~(dvdn p (indexg (Group Hsl) K)).
  apply/negP => Fd.
  move/dvdnP: Fd => [u Hu].
  have F2: (dvdn (p ^ (S n)) (card K)).
    apply/dvdnP; exists u.
    have sgLK : subset (Group Hsl) K by exact: Hsl1.   
    rewrite -(LaGrange sgLK) Hu (eqP Hsl2) /= (mulnA u).
    exact: mulnC. 
  by move: F2; rewrite /n dvdn_p_p_part // (cardD1 1) group1.
have F2:  modn (indexg (Group Hsl) K) p =  modn (card lS0) p.
  rewrite /indexg /= /lS0 /rtrans_fix icard_card. 
  (* THIS IS ALSO IN THE SYLOW1_REC LEMMA *)
  have CL : card (Group Hsl) = (p ^ n)%N by exact: (eqP Hsl2).
  rewrite (@mpl _ _ (trans_action elt) _ _ _ prime_p Hch).
    by congr modn; apply:eq_card => Ha; rewrite !s2f /setI andbC.
  apply: intro_closed=> A B; first exact: orbit_csym.
  case/iimageP=> x Lx ->; case/iimageP=> y Ky ->; apply/iimageP.
  exists (y*x); first by rewrite groupM // (subsetP Hshk x).
  by rewrite /= rcoset_morph.
rewrite /dvdn {}F2 in F1.
have F3: exists x, lS0 x.
  apply/set0Pn.
  by move: F1; rewrite /set0b; case (card lS0) => //=; rewrite mod0n.
case: F3 => Hx; case/isetIP=> Hx2; rewrite s2f => Hx3.
case/iimageP: Hx2=> x Kx /= dHx; subst Hx.
exists x; rewrite Kx /=.
by apply: (@act_fix_sub _ (Group Hsl)).
Qed.


(**********************************************************************)
(*               Second Sylow theorem                                 *)
(**********************************************************************)

Lemma sylow2_cor: forall L1 L2,
   sylow L1 -> sylow L2 -> exists x, (K x) /\ (L2 =1 L1 :^ x).
move => L1 L2 Hl1; case/and3P => Hl2 Ml2 Nl2.
case: (sylow2 (i := n) (H := (Group Hl2)) (L := L1)) => //.
 by exact: (eqP Nl2).
move => x; move/andP => [Hx1 Hx2].
exists x; split => //.
apply/subset_cardP => //.
rewrite card_sconjg (eqP Nl2).
by apply sym_equal; apply/eqP; case/and3P: Hl1.
Qed.

(**********************************************************************)
(*   Definition of the group action x |-> [ H |-> xHx^-1              *)
(**********************************************************************)

Lemma aconj_1: forall s : setType elt, s :^ 1 = s.
Proof. exact: sconj1g. Qed.

Lemma aconj_morph: forall x y (s : setType elt),
  s :^ (x * y) = s :^ x :^ y.
Proof.
move => x y s; exact: sconjgM.
Qed.

Definition conj_action := Action aconj_1 aconj_morph.


(**********************************************************************)
(*   First part of the third Sylow theorem                            *)
(**********************************************************************)

Theorem sylow3_div: dvdn (card sylow) (card K).
Proof.
case sylow1_cor => H Hh.
replace (card sylow) with (card (orbit conj_action K H)).
  by apply: card_orbit_div.
apply eq_card => L.
apply/idP/idP => //.
  by case/orbitP => y Hy <- /=; rewrite -sylow_sconjg.
case/(sylow2_cor Hh) => y; case => Hy HH.
apply/orbitP; exists y => //.
by apply sym_equal; apply/isetP.
Qed.

End Sylow.

Section SylowAux.

Open Scope group_scope.

Variable (elt : finGroupType) (H K L: group elt).
Hypothesis subset_HL: subset H L.
Hypothesis subset_LK: subset L K.

Variable p: nat.
Hypothesis prime_p: prime p.
Let n := logn p (card K).
Hypothesis n_pos: 0 < n.

Lemma sylow_subset: sylow K p H -> sylow L p H.
Proof.
move/and3P => [H1 H2 H3].
apply/and3P; repeat split => //.
rewrite (eqP H3); apply/eqP.
suff ->: logn p (card K) = logn p (card L) =>//.
apply/eqP; rewrite eqn_leq; apply/andP; split.
  rewrite -dvdn_exp_max -?(eqP H3) //.
    by exact: group_dvdn.
apply dvdn_leq_log => //.
by exact: group_dvdn.
Qed.

End SylowAux.

Section Sylow3.

Open Scope group_scope.

Variable (elt : finGroupType) (K : group elt).

Variable p: nat.
Hypothesis prime_p: prime p.

Let n := logn p (card K).

Hypothesis n_pos: 0 < n.

(**********************************************************************)
(*   Second part of the third Sylow theorem                           *)
(**********************************************************************)
Lemma sylow3_mod: modn (card (sylow K p)) p = 1%N.
Proof.
case (sylow1_cor prime_p n_pos)  => H Hh.
case/and3P: (Hh) => F1 F2 F3.
rewrite -(eq_card (s2f (sylow K p))).
rewrite (mpl prime_p (eqP F3) (to := conj_action elt)); last first.
  move => L1 L2 /=.
  rewrite !s2f.
  case/iimageP => x Hx1 ->; apply: sylow_sconjg.
  exact: (subsetP F2).
rewrite -(@modn_small 1%N p); last by case: p prime_p => //=; case.
congr modn.
set S0 := setI _ _.
have F5: S0 H.
  apply/andP; split; last by rewrite s2f.
  apply/act_fixP => x Hx.
  apply: norm_sconjg; exact: (subsetP (norm_refl H)).
have F6: forall x, S0 x -> x = H.
  move => L; case/andP; move/act_fixP.
  rewrite s2f /= => Hl Hl1.
  case/and3P: (Hl1) => Hl2 Hl3 Hl4.
  set nLK := isetI (normaliser L) K.
(*  set nLK := setI_group (normaliser L) K.*)
  have F7: subset H nLK. 
    apply/subsetP => y Hy.
    rewrite s2f; apply/andP; split; last exact: (subsetP F2).    
    by rewrite s2f /= Hl // subset_refl.
  have F8 : sylow {nLK as group _} p H.
    rewrite /=; apply: (@sylow_subset _ _ K)  => //.
    apply/subsetP => y.
    by rewrite s2f; case/andP.
  have F9 : sylow {nLK as group _} p L.
    change (sylow {nLK as group _} p (Group Hl2)).
    apply: (sylow_subset (K := K)) => //;
      last by apply/subsetP => y; rewrite s2f; case/andP.
    apply/subsetP => /= x Hx.
    apply/isetIP; split.
      by apply: (subsetP (norm_refl (Group Hl2))).
    by apply: (subsetP Hl3).
  case: (sylow2_cor prime_p _ F9 F8).
    apply: (@leq_trans (logn p (card L))).
      rewrite (eqP Hl4).
      rewrite logn_exp //.
    apply: dvdn_leq_log => //.
    apply: (@group_dvdn _ (Group Hl2)) => /=.
    apply/subsetP => y.
    rewrite s2f /= => HH; apply/andP; split.
      by apply: (subsetP (norm_refl (Group Hl2))). 
    exact: (subsetP Hl3).
  move => u [Hu Hu1].
  move/isetP: Hu1 => ->.
  apply:sym_equal; apply: norm_sconjg.
  by case/isetIP: Hu.
rewrite (@cardD1 (set_finType _) (Group F1) S0) F5.
rewrite -[1%N]addn0; congr addn.
apply eq_card0 => x.
rewrite /setD1 /=.
case: (S0 x) (F6 x); last by rewrite andbF.
by move => ->; rewrite // eq_refl.
Qed.

End Sylow3.

Unset Implicit Arguments.
