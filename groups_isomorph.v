(***********************************************************************)
(* (c) Copyright Microsoft Corporation and Inria. All rights reserved. *)
(*                                                                     *)
(***********************************************************************)
(***********************************************************************)
(*                                                                     *)
(*  Definitions of the production of two groups                        *)
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
Require Import div.
Require Import  baux.
Require Import  groups.
Require Import normal.
Require Import connect.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.


Section morphism.
Open Scope group_scope.

Definition morphism := fun (G H : finGroup) => fun  f: G ->H => fun K : set G => 
 forall x y,K x -> K y ->  f  (x * y)  = (f x) * (f y).
Variables G H: finGroup.
Variable f: G->H.

Variable K: set G.

Hypothesis f_morph: morphism f K.
Hypothesis K_sbgrp: subgrp K.

Lemma morph_1:  f 1 = 1.
Proof.
move/subgrpP: K_sbgrp => [H1 Hxy].
by apply (mulg_injr (f 1));rewrite  -f_morph //  !mul1g.
Qed.

Lemma morph_inv: forall x, K x ->f (x^-1) = (f  x)^-1.
Proof.
move/subgrpP: K_sbgrp => [H1 Hxy].
move=> x Hx ;apply (mulg_injr (f x)).
rewrite -f_morph =>//;  first by (rewrite !mulVg; exact:morph_1).
by move:(Hxy x 1 ); rewrite /rcoset mul1g =>H1xy; apply H1xy.
Qed.

Lemma im_sbgrp: subgrp (image f K ).
Proof.
apply finstbl_sbgrp with (f 1).
by apply image_f_imp;case/subgrpP: K_sbgrp.
move => x y Hx Hy;rewrite -(f_diinv Hx) -(f_diinv Hy) -f_morph;last apply a_diinv ; last apply a_diinv .
 apply image_f_imp;apply subgrpM=>// ;apply a_diinv .
Qed.

Definition ker := setI K  (preimage f (set1 1)).

Lemma kerP:forall x , reflect  ((K x ) /\ (f x = 1))(ker x ).
move => x; rewrite /ker /setI.
apply: (iffP idP).
by rewrite /preimage; case/andP=> Kx ; case/eqP => Hfx;split.
move => [Kx Hfx];apply  /andP;split =>//.
by  rewrite /preimage Hfx.
Qed.

Lemma ker_sbgrp: subgrp ker.
Proof.
move/subgrpP: K_sbgrp;rewrite /rcoset ;move => [H1 Hxy];apply/subgrpP;split.
by apply/kerP;split =>//;apply morph_1.
move => x y ; rewrite /ker  /setI /preimage/rcoset;
move /andP => [H1x H2x] ; move/andP => [H1y  H2y];apply /andP;split.
by apply subgrpM=>//; apply subgrpV.
apply /eqP;rewrite f_morph //.
by rewrite  -(eqP H2y) morph_inv //  -(eqP H2x) invg1 mulg1.
by apply subgrpV.
Qed.
Lemma ker_subset_K:subset ker K.
by apply/subsetP => x;case/kerP.
Qed.

Lemma ker_normal : normal  ker K.
Proof.
apply/normalP;rewrite /conjg => x y Hx Hy;move/kerP :Hy=> [h1 h2];apply/kerP;split.
by apply subgrpM =>//;apply subgrpM =>//;apply subgrpV.
rewrite !f_morph  //; first rewrite h2 mulg1 morph_inv // mulVg //.
by apply subgrpV.
by apply subgrpM =>//; apply subgrpV.
Qed.

Definition  K_mod_ker:=(@RG G ker K ker_sbgrp K_sbgrp ker_subset_K  ker_normal).
End morphism.

Section comp.
Variables A B C: finType.
Variables (f:A-> B) (g:B->C).
Variable K:set A.

Lemma image_eq: forall L:set A, L=1K -> image f L =1image f K.
move => L Heq x;apply eqb_imp => H1;
case(Hdiinv H1)=> y; case/andP =>  [ Hx  Hy];rewrite (eqP Hx);apply image_f_imp.  
 by rewrite -(Heq y).
by rewrite (Heq y).
Qed.

Lemma image_comp: image (g\o f) K =1 image g (image f K).
move => x; apply eqb_imp=> H1.
case(Hdiinv H1)=> y; case/andP =>  [ Hx  Hy];rewrite (eqP Hx) /comp.
by apply image_f_imp;apply image_f_imp.
case(Hdiinv H1)=> y; case/andP =>  [ Hx  Hy].
case(Hdiinv Hy)=> z;case/andP=> [H2y H3y].
rewrite (eqP Hx) (eqP H2y).
replace (g(f z)) with (comp g f z); last by rewrite /comp.
by apply image_f_imp. 
Qed.

End comp.

Section dcancel.
Definition dcancel:= fun (A B: eqType ) ( f : B->A) (g : A -> B) ( K : set B)=> forall x: B, K x -> g(f x) = x.
Lemma dcan_dinj:  forall (A B: finType ) ( f : B->A) (g : A-> B) ( K : set B), dcancel f  g K -> dinjective K f.
move => A B f g K; rewrite /dcancel => Hdcan x y Hx Hy Hfx.
by rewrite -[x] Hdcan //  Hfx Hdcan.
Qed.

Variables A B: finType.
Variable f:A-> B. 
Variable K:set A.
Variable a:A.

Definition dcan_fun (x:B) : A:=
let (b,Hb):= wb (image f K x) in 
(if b return ((image f K x) = b -> A)
 then 
fun H  =>   (diinv H) else fun H  => a) Hb.

Lemma dcan_fun_can:  dinjective K f -> dcancel f (dcan_fun   ) K.
move=>  Hinj x Kx.
have h1: (image f K (f x)).
by rewrite image_f_imp.
rewrite /dcan_fun /=.
case (wb (image f K (f x))).
case => H1.
by apply diinv_f.
rewrite h1 in H1;discriminate.
Qed.

Lemma dcan_inj: forall L : set B, L=1 image f K -> dinjective L (dcan_fun).
move => L Heq x y Hx Hy.
rewrite /dcan_fun /=.
case (wb (image f K x)); case => H1.
case (wb (image f K y));case => H2.
by rewrite -{2}(f_diinv H1)  -{2}(f_diinv H2) => ->.
move: (Heq y) H2 => <-; rewrite Hy =>*;discriminate.
move: (Heq x) H1 => <-; rewrite Hx =>*;discriminate.
Qed.
End dcancel.

Section isomorphism.

Definition isomorphism:= fun G H : finGroup => fun f : G -> H => fun K: set G => morphism f K /\ dinjective  K f.

Lemma iso_can_iso: forall G H : finGroup, forall f: G -> H, forall  K: set G , isomorphism  f  K -> forall h, cancel f h-> isomorphism  h (image f K).
Proof.
move =>G H  f K ; rewrite /isomorphism; move => [Hmorph Hinj] h Hcan.
have hdinj: dinjective (d':=G) (image f K) h.
 by rewrite /dinjective;move => x y Hx Hy;rewrite -(f_diinv Hx)  -(f_diinv Hy);rewrite !Hcan => -> //.
split => //;move => x y Hx Hy;by rewrite -(f_diinv Hx) -(f_diinv Hy) -Hmorph;try apply a_diinv; rewrite !Hcan.
Qed.

Lemma isomorph_can_morph: forall G H : finGroup, forall f: G -> H, forall  K: set G , forall L : set H, 
       subgrp K ->  isomorphism  f  K -> L =1 (image f K) -> morphism (dcan_fun f K 1%G) L.
move => G H f K L K_sbgrp [H1 H2] HLim x y Hx Hy.
 move:(HLim x) Hx -> => Hx; move:(HLim y) Hy -> => Hy.
rewrite -(f_diinv Hx ) -(f_diinv Hy) -H1; try apply a_diinv.
 rewrite !(dcan_fun_can 1%G H2) //; try apply a_diinv.
apply: subgrpM => //;apply a_diinv.
Qed.

Lemma iso_can: forall G H : finGroup, forall f: G -> H, forall  K: set G , isomorphism  f  K -> exists h , dcancel f h K.
move => G H f K [H1 H2].
exists (@dcan_fun G H f K 1%G ).
by apply dcan_fun_can.
Qed.

Lemma subgrp_eq: forall G:finGroup, forall K L: set G, K=1 L -> subgrp  K -> subgrp  L.
move => G K L Heq.
case /subgrpP => K1; rewrite  /rcoset => HK;apply /subgrpP;split.
 by move:(Heq 1%G)=> <-.
move => x y Lx Ly ;rewrite /rcoset.
 move:(Heq (y * x^-1)%G)=> <-; apply HK; first by  rewrite (Heq x).
by rewrite  (Heq y).
Qed.

Definition isomorphic:=fun G H : finGroup =>  fun K: set G => fun L :set H =>subgrp K /\ (exists g: G->H, (isomorphism g K) /\ L =1 (  image g K )).
Lemma isomorphic_sym: forall G H:finGroup, forall K : set G, forall L:set H, isomorphic K L -> isomorphic L K.
Proof.
move => G H K L  [H1 [g [H2 H3]]];split.
by apply (@subgrp_eq  H (image g K)) =>//; apply im_sbgrp => //;move:H2 => [H4 H5].
case:H2=>  [Hmorph Hdinj];exists (@dcan_fun G H g K 1%G);split.
 split; last by apply dcan_inj.
by apply isomorph_can_morph => //;by split.
set f:=  (dcan_fun (A:=G) (B:=H) g K 1%G).
move => x; rewrite (image_eq f H3 x);rewrite -(image_comp g f K);apply eqb_imp=> H2.
move:(dcan_fun_can 1%G Hdinj);rewrite -/f /dcancel => H4;rewrite -(H4 x H2).
replace (f (g x)) with ((f\o g ) x); last by rewrite /comp.
by apply image_f_imp.

case:(Hdiinv H2)=> y ;case/andP=> [H2y H3y];rewrite (eqP H2y).
move:(dcan_fun_can 1%G Hdinj);rewrite -/f /dcancel => H9.
replace ((f\o g ) y) with  (f (g y));last by rewrite /comp.
by rewrite (H9 y H3y).
Qed.
Lemma isomorphic_refl: forall G:finGroup, forall K L: set G, subgrp K -> K=1L -> isomorphic K L.
move => G K L K_sbgrp HKL;split => //.
exists (fun x : G => x);split.
split.
by move => x y Kx Ky /=.
by move => x y Kx Ky /=.
move => x.
move:(HKL x)=> <-.
set f:= (fun x0 : G => x0).
have :(x = f x).
by rewrite /f.
move => Hfx.
symmetry;apply: image_f.
by move=> a b; rewrite /f.
Qed.

Lemma isomorphic_trans : forall G H I:finGroup, forall K : set G, forall L:set H, forall M : set I, 
      isomorphic K L -> isomorphic L M -> isomorphic K M. 
Proof.
move => G H I K L M  [H1 [g [[gmorph ginj] H3]]] [H4 [h [[hmorph hinj]]]];split=>//.
exists (h \o g);split.
split.
move => x y  Kx Ky.
rewrite /comp.
rewrite (gmorph x y) //  (hmorph (g x) (g y)) //.
by move:(H3 (g x))=> ->; apply image_f_imp.
by move:(H3 (g y))=> ->; apply image_f_imp.
move => a b Ka Kb; rewrite /comp=>hgeq.
apply:ginj =>//.
apply:hinj =>//.
by rewrite (H3 (g a)); apply image_f_imp.
by rewrite (H3 (g b)); apply image_f_imp.
move => x.
rewrite (image_comp  g h K x).
rewrite (H0 x).
by apply:image_eq.
Qed.
End isomorphism.

Section normal.
Variable G: finGroup.
Variables H1 H2 K:set G.
Hypotheses (H1sbgrp: subgrp (G:=G) H1) (H2sbgrp: subgrp (G:=G) H2) 
       (Ksbgrp:subgrp (G:=G) K ) (H1sbsK:subset H1 K) (H2sbsK:subset H2 K)
(H1norm:normal (G:=G) H1 K)  (H2norm: normal (G:=G) H2 K).

Definition RG1:=(RG H1sbgrp Ksbgrp H1sbsK H1norm).
Definition  RG2:=(RG H2sbgrp Ksbgrp H2sbsK H2norm).


Definition g'(x: RG1) : RG2:= quotient H2sbgrp Ksbgrp H2sbsK H2norm (val x).
Hypothesis Heq: H1 =1 H2.



 Lemma j: forall (valx : G)
( H3 : (setI (roots  (lcoset (G:=G) H1) ) K valx)),
setI (roots (lcoset (G:=G) H2)) K valx.
move => valx; case/andP =>H3 H4.
apply/andP;split =>//.
move: H3;rewrite /roots=>H5.
rewrite -{2}(eqP H5).
apply /eqP.
rewrite /root.
set v1:= connect _ _.
set v2:= connect _ _.
rewrite (@eq_pick _  v1 v2) //.
move => x.
rewrite /v1 /v2.
apply: eq_connect.
move => a b.
rewrite /lcoset.
by rewrite Heq.
Qed.

 Lemma k: forall (valx : G)
( H3 : (setI (roots  (lcoset (G:=G) H2) ) K valx)),
setI (roots(lcoset (G:=G) H1)) K valx.
move => valx; case/andP =>H3 H4.
apply/andP;split =>//.
move: H3;rewrite /roots=>H5.
rewrite -{2}(eqP H5).
apply /eqP.
rewrite /root.
set v1:= connect _ _.
set v2:= connect _ _.
rewrite (@eq_pick _  v1 v2) //.
move => x.
rewrite /v1 /v2.
apply: eq_connect.
move => a b.
rewrite /lcoset.
by rewrite Heq.
Qed.

Definition g1 (x:RG1): RG2.
move=>x ; case x => valx H3.
exists valx.
exact: j.
Defined.

Remark g1_morph: morphism g1 RG1.
move => x y _ _.
case x.
case y.
rewrite /g1 /=.
move => val ValP val0 valP0.
apply /val_eqP.
simpl.
rewrite /root.
set v1:= connect _ _.
set v2:= connect _ _.
rewrite (@eq_pick _  v1 v2) //.
move => z.
rewrite /v1 /v2.
apply: eq_connect.
move => a b.
rewrite /lcoset.
by rewrite Heq.
Qed.

Lemma g1_dinj: dinjective  RG1 g1.
move => x y _ _.
case x.
case y.
rewrite /g1 /=.
move => val ValP val0 valP0 H5.
move/val_eqP: H5.
simpl.
move => H6.

by apply /val_eqP.
Qed.




Lemma RG_isom: isomorphic RG1 RG2.
split.
apply subgrp_of_group.
exists g1.
split.
split.
apply g1_morph.

(*g1 dinjective*)
apply g1_dinj.
(*g1 surjective *)
move=> x.
apply eqb_imp =>//.
move => _.
have :(x = g1 (
match x with
| EqSig valx H3 =>
    EqSig (setI (roots (lcoset (G:=G) H1)) K) valx (k (valx:=valx) H3)
end )).
rewrite /g1.
case x.
by move => valx Hx;
apply/val_eqP. 
move => ->.
by apply image_f_imp.
Qed.

End normal.

Section first_theorem.

Variables G H : finGroup.

Variable K: set G.
Variable f : G -> H.
Hypothesis K_sbgrp: subgrp K.
Hypothesis  f_morph: morphism f K.
Definition  Kerf := (ker f).

Definition Q:= (K_mod_ker  f_morph K_sbgrp).

Definition  quo := quotient (ker_sbgrp f_morph K_sbgrp)  K_sbgrp (ker_subset_K f K)  (ker_normal f_morph K_sbgrp).

Definition g (x: H):  ( K_mod_ker f_morph K_sbgrp):=
let Quo := ( K_mod_ker f_morph K_sbgrp) in 
let (b,Hb):= wb (image f K  x) in 
(if b return ((image f  K x) = b -> Quo )
 then 
fun H  =>   (quo (diinv H)) else fun H  => (quo 1%G)) Hb.

Remark g_dinj: dinjective (image f K) g.
Proof.
move => x y imx imy;rewrite /g.
case  (wb (image f K x));case =>Hx1;last by rewrite imx in Hx1;discriminate.
case  (wb (image f K y));case =>Hy1;last by rewrite imy in Hy1;discriminate.
move => Hquo;rewrite -(f_diinv  Hx1) -(f_diinv  Hy1).
set x1:= (diinv (d:=G) (d':=H) (f:=f) (a:=K) (x':=x) Hx1).
set y1:=  (diinv (d:=G) (d':=H) (f:=f) (a:=K) (x':=y) Hy1).
move:(a_diinv Hx1)=>Kx1; move: (a_diinv Hy1)=>Ky1.
apply : (mulg_injl (f  x1)^-1%G);rewrite -(morph_inv f_morph) //.
rewrite  -f_morph //;last by apply:subgrpV.
rewrite mulVg  (morph_1 f_morph) //  -f_morph //;last by apply:subgrpV.
symmetry;rewrite /quo in Hquo;move:(quotient_quotient_inv  (a_diinv Hx1)  (a_diinv Hy1) Hquo).
case/kerP ; by rewrite /x1 /y1 => [H1 H2].
Qed.

Remark g_surj: K_mod_ker f_morph K_sbgrp =1 image g (image f K).
Proof.
move => x;apply: eqb_imp =>//; move=> _.
have:(K (val x)); first by (case : x => /= val Hx;case/andP:(Hx)). move=> Kvalx.
have: (x= g(f (val x))) ; last by move => ->; apply: image_f_imp;apply image_f_imp.
rewrite /g;case:wb;case;last by (rewrite (image_f_imp f Kvalx )).
 move=> Him; move: (quotient_val  (ker_sbgrp f_morph K_sbgrp) K_sbgrp  (ker_subset_K f K)  (ker_normal f_morph K_sbgrp)  x).
set y:= diinv _;move => <-.
have Hy : (K y); first by apply: a_diinv.
rewrite /quo; apply: inv_quotient_quotient =>//.
apply /kerP;split.
apply: subgrpM => //; first apply subgrpV => //.
rewrite f_morph //.
by rewrite (morph_inv f_morph) // /y f_diinv mulVg.
by apply subgrpV.
Qed.

Remark g_morph: morphism g (image f K).
Proof.
move => x y Hx Hy;rewrite /g;case (wb (image f K x));case => Hx1; last by rewrite Hx in Hx1;discriminate.
case (wb (image f K y));case => Hy1 ; last by rewrite Hy in Hy1;discriminate.
case (wb (image f K(x * y)%G));case => Hxy; 
last by rewrite (subgrpM (im_sbgrp f_morph K_sbgrp) Hx Hy) in Hxy;discriminate.
(*set x1 := (diinv (d:=G) (d':=H) (f:=f) (a:=K) (x':=x) Hx1) .
set y1 := (diinv (d:=G) (d':=H) (f:=f) (a:=K) (x':=y) Hy1).
set xy1 := (diinv (d:=G) (d':=H) (f:=f) (a:=K) (x':=(x * y)%G) Hxy).
*)
rewrite /quo  /K_mod_ker.
case (val_quotient  (ker_sbgrp f_morph K_sbgrp) K_sbgrp  (ker_subset_K f K)  (ker_normal f_morph K_sbgrp) (a_diinv Hxy))=>z;
case /andP => Kerz Hval.
case (val_quotient  (ker_sbgrp f_morph K_sbgrp) K_sbgrp  (ker_subset_K f K)  (ker_normal f_morph K_sbgrp) (a_diinv Hx1) )=>z1;
case /andP => Kx1 Hvalx.
move:(a_diinv Hx1) (a_diinv Hy1) (a_diinv Hxy) => Ka1 Kb1 Kxy1;
rewrite -(@quotient_mul _  _ _ (ker_sbgrp f_morph K_sbgrp) K_sbgrp
   (ker_subset_K (G:=G) (H:=H) f K) (ker_normal f_morph K_sbgrp) ) //.
apply: inv_quotient_quotient =>// ; first by apply subgrpM.
apply/kerP;split.
 apply: subgrpM => //;first by apply: subgrpV.
 by apply: subgrpM => //.
rewrite !f_morph =>//.
 rewrite !f_diinv;rewrite (morph_inv f_morph) //.
 by rewrite  f_diinv mulVg //.
 by apply: subgrpV.
by apply : subgrpM.
Qed.

(* first isomorphism theorem *)

Lemma K_mod_ker_isom_imf: isomorphic  (image f K) (K_mod_ker  f_morph K_sbgrp).
Proof.
split; first by apply im_sbgrp.
exists g;split;last by apply g_surj.
split;last by apply g_dinj.
apply g_morph.
Qed.
End first_theorem.

Section second_theorem.

Variables G  : finGroup.

Variable H N: set G.
Hypothesis H_sbgrp: subgrp H.
Hypothesis N_sbgrp: subgrp N.
Hypothesis N_normal: normal N G .

Remark sbset: subset (setI H N) H .
apply/subsetP. move => x. by case/andP => Hx Nx.
Qed.

Remark HiNnormal: normal (G:=G) (setI H N) H.
apply/normalP. move=>x y Hx; case/andP=> Hy Ny; apply/andP.
move/normalP: N_normal.
rewrite/conjg;split.
apply: subgrpM =>//;apply: subgrpM =>//.
by apply subgrpV.
by apply: H0.
Qed.

Definition H_mod_HiN :=(  @RG G (setI H N) H (sbgrpI H_sbgrp N_sbgrp)H_sbgrp sbset HiNnormal).
Require Import groups_prod.


Lemma HN_sbgrp: subgrp (prod H N).
Proof.
apply:subprod_sbgrp =>// x.
apply eqb_imp.
case/prodP => x0 [y H1]; case/andP : (H1); case/andP=> Hx0 Ny;case/eqP=> Heq.
apply/prodP.
exists (x0*y*x0^-1)%G;exists x0.
apply/andP;split.
apply/andP;split => //.
move/normalP:N_normal;rewrite /conjg=> Hnorm.
move:(Hnorm x0^-1%G y). rewrite invg_inv=> H2.
apply H2 => //.
apply/eqP; rewrite Heq;gsimpl.

case/prodP => x0 [y H1]; case/andP : (H1); case/andP=> Hx0 Hy;case/eqP=> Heq.
apply/prodP.
rewrite Heq.

exists y ; exists (y^-1*x0*y)%G.
apply/andP;split.
apply/andP;split => //.
move/normalP:N_normal;rewrite /conjg=> Hnorm.
apply :(Hnorm y x0 ) => //.
gsimpl.
Qed.
Remark NsbsHN: subset N (prod (G:=G) H N).
apply/subsetP => x Nx;apply/prodP.
exists (Group.unit G); exists x;apply/andP;split.
apply/andP;split =>//.
apply subgrp1 =>//.
by rewrite mul1g.
Qed.

Remark NnormHN: normal (G:=G) N (prod (G:=G) H N).
apply:( normal_subset  N_normal HN_sbgrp  NsbsHN).
by apply/subsetP.
Qed.

Lemma HinHN: forall x , H x ->  (prod H N) x.
Proof.
move=>x Hx.
apply /prodP.
exists x; exists (Group.unit G).
apply/andP;split.
apply/andP;split =>//.
by apply: subgrp1.
by gsimpl.
Qed.
Lemma NinHN: forall x, N x -> (prod H N) x.
Proof.
move=>x Nx.
apply /prodP.
 exists (Group.unit G);exists x.
apply/andP;split.
apply/andP;split =>//.
by apply: subgrp1.
by gsimpl.
Qed.

Definition HN_mod_N :=(@RG G N (prod H N) N_sbgrp HN_sbgrp  NsbsHN NnormHN).

Definition f :=(quotient  N_sbgrp   HN_sbgrp NsbsHN NnormHN).

Remark f_morph: morphism f H.
by move => x y Kx Ky;apply : quotient_mul=>//; apply HinHN.
Qed.

Remark kerf_HiN: (setI H N) =1 ker f  H.
move =>x;apply eqb_imp.
case/andP => Hx Nx;apply/kerP;split => //.
by rewrite /f;  apply quotient1.
case/kerP => Hx Hfx;apply/andP;split =>//.
move: Hfx ; rewrite /f  -quotient11=>Hfx.
move:(quotient_quotient_inv   (G:= G) (H:= N)(subgrp_H := N_sbgrp) (subgrp_K := HN_sbgrp ) (HinHN Hx) (subgrp1 HN_sbgrp) Hfx).
rewrite mulg1=> Nx1.
 rewrite -(invg_inv x).
by apply subgrpV.
Qed.

Remark  imf_HN_mod_N: HN_mod_N=1 (image f H).
move =>x;apply eqb_imp=> //.
move => _.
case x.
move => valx Hx.

move/andP :(Hx) => [H1 H2].
case/prodP:H2.
move => h [n H2].
set xx:= EqSig _ _ _.
have -> :(xx= f h).
rewrite /xx.
rewrite /f.
rewrite -(quotient_root N_sbgrp HN_sbgrp NsbsHN NnormHN).
case/andP: H2.
case/andP => H2 H3.
move/ eqP=> ->.
apply: inv_quotient_quotient.
by apply:in_prod.
apply /prodP.
exists h;exists (Group.unit G).
apply/andP;split.
apply/andP ;split => //.
by apply subgrp1.
by rewrite mulg1.
gsimpl; by apply subgrpV.
apply image_f_imp.
case/andP: H2.
by case/andP => H2 H3.
Qed.

Lemma second_th : isomorphic H_mod_HiN HN_mod_N.
apply isomorphic_sym.
have:(isomorphic  HN_mod_N (image f H)).
apply: (isomorphic_refl (subgrp_of_group HN_mod_N)  imf_HN_mod_N).
rewrite -/HN_mod_N=> H1.
apply: (isomorphic_trans H1).
clear H1.

apply: (isomorphic_trans (K_mod_ker_isom_imf  H_sbgrp  f_morph)).
apply: RG_isom.
move => x.
by rewrite (kerf_HiN x).
Qed.
End second_theorem.


