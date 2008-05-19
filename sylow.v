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

Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq.
Require Import fintype paths connect div finfun finset.
Require Import groups normal action cyclic zp.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Section Cauchy.

Open Scope group_scope.

Variable (gT : finGroupType) (H : {group gT}).

Variable p : nat.
Hypothesis prime_p : prime p.
Hypothesis p_divides_H : p %| #|H|.

(**********************************************************************)
(*               Cauchy theorem                                       *)
(**********************************************************************)

Canonical Structure SylowCauchyPosPrime := prime_pos_nat prime_p.
Notation zp := I_(p).
Let lt1p := prime_gt1 prime_p.
Definition make_zp : nat -> zp.
move=> i; exists (i %% p).
abstract by rewrite ltn_mod pos_natP.
Defined.

Let zp1 : zp := make_zp 1.

Lemma make_zp_val : forall x : zp, make_zp x = x.
Proof. case=> i ltip; apply: val_inj => /=; exact: modn_small. Qed.

Lemma zp_power_mul : forall (x : zp) m, x ^+ m = make_zp (m * x)%N.
Proof.
move=> x; elim=> [|m IHm]; apply: val_inj => /=; first by rewrite mod0n.
by rewrite expgS IHm -{1}(make_zp_val x) /= modn_add2m.
Qed.

Lemma zp_power_p : forall x : zp, x ^+ p = 1.
Proof.
by move=> x; apply: val_inj; rewrite zp_power_mul /= mulnC modn_mull.
Qed. 

Lemma zp1_gen : forall x : zp, zp1 ^+ x = x.
Proof.
by move=> x; rewrite zp_power_mul /= (modn_small lt1p) muln1 make_zp_val.
Qed.

Let prod_over_zp f :=
  foldr (fun i x => f (zp1 ^+ i) * x) (1 : gT) (iota 0 p).

Let X := [set t | ffun_on (mem H) t && (prod_over_zp t == 1)].

Definition zprot (f : {ffun zp -> gT}) x := [ffun y => f (x * y)].

Lemma rot1_prod_over_zp : forall f,
  (prod_over_zp (zprot f zp1) == 1) = (prod_over_zp f == 1).
Proof.
move=> f; rewrite /prod_over_zp -{-2}(ltn_predK lt1p) -{2}add1n -addn1.
rewrite !iota_add !foldr_cat /= add0n addnC iota_addl foldr_maps /= ffunE.
set y := f _ * 1; have->: f 1 = y; last clearbody y.
  by rewrite -(zp_power_p zp1) -{-1}(ltn_predK lt1p) /y mulg1.
rewrite -(inj_eq (mulg_injr y^-1)).
rewrite -(inj_eq (mulg_injl y^-1) _ 1); gsimpl; congr (_ == _).
elim: (iota _ _) y => [|i s IHs] y /=; gsimpl.
by rewrite ffunE -mulgA IHs.
Qed.

Lemma zprot_to1 : forall f, zprot f 1 = f.
Proof. by move=> f; apply/ffunP=> i; rewrite /zprot ffunE mul1g. Qed.

Lemma zprot_to_morph : forall f x y, zprot f (x * y) = zprot (zprot f x) y.
Proof. move=> f x y; apply/ffunP=> i; rewrite /zprot !ffunE; gsimpl. Qed.

Canonical Structure zprot_action := Action zprot_to1 zprot_to_morph.

Definition zp_group : {group zp} := setT_group _.

Lemma zprot_acts_on_X : closed [rel of orbit zprot_action zp_group] (mem X).
Proof.
apply: intro_closed => f1 f2; first exact: orbit_csym.
case/imsetP=> x _ -> {f2}.
rewrite -(zp1_gen x) /=; elim: {x}(nat_of_ord x) f1 => [|i IHi] f /=.
  by rewrite zprot_to1.
rewrite zprot_to_morph inE; case/andP; move/ffun_onP=> Hfx prodf1.
apply: IHi; rewrite inE {i} rot1_prod_over_zp prodf1 andbT.
by apply/ffun_onP=> i; rewrite ffunE Hfx.
Qed.

Lemma card_X : #|X| = (#|H| ^ (p - 1))%N.
Proof.
pose Y := pffun_on 1 (mem [set~ 1 : zp]) (mem H).
transitivity #|Y|; last first.
  by rewrite card_pffun_on subn1 cardsC1 card_ord.
pose f t x := if x == 1 then (prod_over_zp t)^-1 else t x.
pose F (t : {ffun _}) := ffun_of (f t).
have injF : {in Y &, injective F}.
  move=> t1 t2; move/pffun_onP=> [Yt1 _]; move/pffun_onP=> [Yt2 _].
  move=> Ft12; apply/ffunP=> u. 
  have:= erefl (F t1 u); rewrite {2}Ft12 !ffunE /f.
  case: eqP => //= -> {u} _; transitivity (1 : gT); last symmetry.
    by apply/eqP; apply/idPn; move/Yt1; rewrite /= setC11.
  by apply/eqP; apply/idPn; move/Yt2; rewrite /= setC11.
have prodF : forall t, prod_over_zp (F t) = (t 1)^-1 ^ (prod_over_zp t).
  move=> t; rewrite /conjg {-2}/prod_over_zp -(ltn_predK lt1p) /=; gsimpl.
  rewrite ffunE /f eqxx; congr mulg. 
  have: forall i, i \in iota 1 p.-1 -> (zp1 ^+ i == 1) = false.
    move=> i; rewrite mem_iota add1n (ltn_predK lt1p).
    move/andP=> [ipos ltip]; apply: negbET.
    by rewrite (zp1_gen (Ordinal ltip)) -lt0n.
  elim: (iota _ _ ) => //= i s IHs zpsnot1.
  rewrite ffunE /f zpsnot1 ?inE ?eqxx ?IHs // => j sj.
  apply zpsnot1; exact: predU1r.
rewrite -(card_dimset injF); apply: eq_card => t; rewrite inE.
apply/andP/imsetP=> [[]|[t1 Yt1 ->{t}]].
  move/ffun_onP=> /= Xt; move/eqP=> Yt; exists (F t); last first.
    apply/ffunP=> u; rewrite !ffunE /f prodF Yt conjg1 invgK.
    by rewrite ffunE /f; case: eqP => // ->.
  apply/pffun_onP; split=> u.
    move/eqP=> dFtu; rewrite /= inE; apply/eqP=> Du; case: dFtu.
    by rewrite {u}Du ffunE /f eqxx Yt invg1.
  move/imageP=> [v /= vnot1 ->{u}]; rewrite ffunE /f /=.
  by rewrite inE in vnot1; rewrite (negbET vnot1).
move/pffun_onP: Yt1 => [Yt1 Xt1]. 
case sup1: (support 1 t1 1); first by move/Yt1: sup1; rewrite /= setC11.
move/eqP: sup1 => Dt11; have{Xt1} Xt1: forall u, t1 u \in H.
  move=> u; case sup_u: (u == 1); first by rewrite (eqP sup_u) Dt11.
  by apply: Xt1; apply/imageP; exists u; rewrite //= inE sup_u.
split; last by rewrite prodF Dt11 invg1 conj1g eqxx.
apply/ffun_onP=> u; rewrite ffunE /f; case: (_ == _) => //=.
by rewrite groupV /prod_over_zp; elim: (iota _ _) => //= *; rewrite !in_group.
Qed.

Theorem cauchy : exists a, (a \in H) && (#|cyclic a| == p).
Proof.
have card_zp: #|zp_group| = (p ^ 1)%N.
  by rewrite cardsE card_ord expn1.
have:= mpl prime_p card_zp zprot_acts_on_X; set Z := predI _ _.
rewrite card_X -{1}(subnK lt1p) /= -modn_mul2m (eqnP p_divides_H) mod0n.
pose t1 : {ffun zp -> gT} := [ffun => 1].
have Zt1: t1 \in Z.
  apply/andP; split; [|rewrite /= inE; apply/andP; split].
  - by apply/act_fixP=> x _; apply/ffunP=> i; rewrite /zprot /t1 !ffunE.
  - by apply/ffun_onP=> u; rewrite ffunE /=.
  rewrite /prod_over_zp; apply/eqP; elim: (iota _ _) => //= i s -> {s}.
  by rewrite ffunE mul1g.
case: (pickP (predD1 Z t1)) => [t | Z0]; last first.
  by rewrite (cardD1 t1) Zt1 (eq_card0 Z0) modn_small.
case/and3P=> tnot1; move/act_fixP=> fixt /=. 
rewrite inE; case/andP; move/ffun_onP=> /= Ht prodt _.
pose x := t 1; exists x; rewrite Ht /=.
have Dt: t _ = x by move=> u; rewrite /x -{2}(fixt u (in_setT _)) ffunE mulg1.
have: #[x] %| p.
  rewrite orderg_dvd -(eqP prodt) -{1}(size_iota 0 p) /prod_over_zp.
  by apply/eqP; elim: (iota _ _) => //= i s <-; rewrite Dt.
case/primeP: prime_p => _ divp; move/divp; case/orP; rewrite eq_sym //.
move/eqP=> Dx1; case/eqP: tnot1; apply/ffunP=> i.
by rewrite Dt -(expg1 x) ffunE Dx1 orderg_expn1.
Qed.

End Cauchy.

Section Sylow.

Open Scope group_scope.

Variable (gT : finGroupType) (K : {group gT}).

Variable p : nat.
Hypothesis prime_p : prime p.

Let n := logn p #|K|.

Hypothesis n_pos: 0 < n. 

Lemma SylowDivpCK : p %| #|K|.
Proof.
apply: (@dvdn_trans (p ^ n)%N); last by rewrite dvdn_exp_max.
by move: n_pos; case: n => // n1 _; rewrite dvdn_exp // dvdnn.
Qed.

Let DivpCK := SylowDivpCK.

(**********************************************************************)
(*  Definition of a sylow group:                                      *)
(*  its a subgroup of cardinal p ^n where n is the largest n such     *)
(*  that p^n divides card k                                           *)
(**********************************************************************)

Definition sylow (A : {set gT}) : pred {set gT} := 
  fun B => (B \subset A) && (#|B| == p ^ logn p #|A|)%N.

Lemma sylow_sconjgr: forall L x, x \in K -> sylow K L = sylow K (L :^ x).
Proof.
have F1: forall L x, x \in K -> sylow K L -> sylow K (L :^ x).
  move=> L x Kx; case/andP => sLK card_L.
  apply/andP; split; last by rewrite card_conjg card_L.
  apply/subsetP=> yx; case/imsetP=> y Ly ->{yx}.
  by rewrite groupJ // (subsetP sLK).
move=> L x Hx; apply/idP/idP => Hx1; first exact: F1.
by rewrite -[L](conjsgK x) F1 // groupV.
Qed.

Lemma sylow_sconjg: forall H L x, sylow H L = sylow (H :^ x) (L :^ x).
Proof.
have F1: forall H L x, sylow H L -> sylow (H :^ x) (L :^ x).
  move=> H L x; case/andP => sLH card_L.
  rewrite /sylow 2!card_conjg -(eqP card_L) eqxx andbT.
  apply/subsetP=> yx; case/imsetP=> y Ly ->{yx}.
  by rewrite memJ_conjg (subsetP sLH).
move=> H L x; apply/idP/idP => Hx1; first exact: F1.
by rewrite -[H](conjsgK x) -[L](conjsgK x) F1.
Qed.


Lemma sylow1_rec: forall i (L : {group gT}), i < n ->
  L \subset K -> (#|L| == p ^ i)%N ->
  exists H : {group gT}, [&& H \subset K, L <| H & #|H| == p ^ i.+1]%N.
Proof.
move=> i L ltin sLK cardL.
have: p %| #|K / L|.
  have <-: #|rtrans_fix L K L| = #|K / L|.
    rewrite rtrans_fix_norm -(card_imset (mem (K / L)) val_inj).
    by apply: eq_card=> Lk; rewrite set_of_coset_quotient.
  have divpLK : p %| indexg L K.
    rewrite -(@dvdn_pmul2l #|L|) // (LaGrange sLK) (eqP cardL) mulnC -expnS.
    by rewrite dvdn_exp_max.
  apply/eqP; rewrite -{divpLK}(eqnP divpLK); symmetry.
  rewrite /indexg (@mpl _ _ (trans_action gT) _ _ _ _ prime_p (eqP cardL)).
    by congr (_ %% _); apply: eq_card=> x; rewrite !inE andbC.
  apply: intro_closed=> A B; first exact: orbit_csym.
  case/imsetP=> x Lx ->{B}; case/imsetP=> y Ky ->{A}; apply/imsetP.
  exists (y * x); first by rewrite groupM //; exact: (subsetP sLK x).
  by rewrite /= !rcosetE rcosetM.
case/cauchy=> // zbar; case/andP=> Kzbar; move/eqP=> Czbar_p.
pose H := mpreim (coset_of L) (cyclic zbar) :&: K.
exists [group of H] => /=.
have Hntriv : ~~ trivm (coset_of L).
  apply/negP=> Hnt; move/prime_gt1: prime_p; rewrite ltnNge; case/negP.
  rewrite -Czbar_p -(coset_of_repr zbar) trivm_is_cst //.
  rewrite -(cards1 (1 : coset L)); apply: subset_leq_card; exact: cyclic_h.
have sLH : L \subset H.
  apply/subsetP => x Lx. 
  apply/setIP; split; last exact: (subsetP sLK x).
  apply/setIP; split; first by rewrite inE coset_of_id // group1.
  rewrite dom_coset //; exact: (subsetP (normG L)).
have nLH: H \subset 'N(L).
  by apply/subsetP=> x; case/setIP; case/mpreimP=> *; rewrite -dom_coset.
rewrite /(_ <| _) sLH nLH subsetIr -(@LaGrange _ L) // -card_quotient //= -/H.
rewrite (eqP cardL) mulnC -{}Czbar_p.
apply/eqP; congr (_ * _)%N; apply: eq_card => xbar.
apply/imsetP/idP=> [[x Hx ->{xbar}]|].
  by rewrite 3!inE -andbA in Hx; case/andP: Hx.
case/cyclicP=> m <-{xbar}; rewrite {nLH sLH}/H.
case/quotientP: Kzbar => z [Kz Nz ->{zbar}].
by exists (z ^+ m); rewrite 3?inE morphX // dom_coset ?groupX ?cyclicnn.
Qed.

Lemma sylow1: forall i j (L : group gT), i <= j -> j <= n ->
  L \subset K -> #|L| == (p ^ i)%N ->
  exists H: group gT, [&& L \subset H, H \subset K & #|H| == p ^ j]%N.
Proof.
move=> i j L Hij Hjn Hsl Hcl; move: Hjn; rewrite -(subnK Hij) addnC.
elim: (j - i) => [| k Hrec].
  by rewrite add0n => Hin; exists L; rewrite subset_refl Hsl.
move=> Hk; case Hrec; first by apply: leq_trans Hk; rewrite addSn.
move=> H; case/and3P => Hlh Hhk Hch.
case (@sylow1_rec (k+i) H) => //.
move=> H1; rewrite -andbA; case/and4P => sH1K sHH1 _ oH1; exists H1.
by rewrite sH1K (subset_trans Hlh).
Qed.

(**********************************************************************)
(*               First Sylow theorem                                  *)
(**********************************************************************)

Theorem sylow1_subset : forall i (L : {group gT}),
  L \subset K -> #|L| == (p ^ i)%N -> 
  exists P : {group gT}, (L \subset P) && sylow K P.
Proof.
move=> i L Hlk Hcl; case (@sylow1 i n L) => //.
  by rewrite -dvdn_exp_max // -(eqP Hcl) group_dvdn.
by move=> H; case/and3P => [Hlh Hhk Hc]; exists H; rewrite Hlh // /sylow Hhk.
Qed.

Theorem sylow1_cor : exists P : {group gT}, sylow K P.
Proof.
case (@sylow1_subset 0 [group of [set 1]]) => //=.
- by apply/subsetP => z; rewrite inE; move/eqP->; exact: group1.
- by rewrite cards1.
by move=> H; case/and3P => [_ Hhk Hc]; exists H; apply/andP.
Qed.

Lemma sylow2 : forall (H L : {group gT}) i, H \subset K ->
 #|H| = (p ^ i)%N -> sylow K L -> exists x, (x \in K) && (H \subset L :^ x).
Proof.
move => H L i Hshk Hch Hsl.
case/andP: Hsl => Hsl1 Hsl2.
pose lS0 := rtrans_fix L K H.
have F1: ~~ (p %| indexg L K).
  apply/negP => Fd.
  move/dvdnP: Fd => [u Hu].
  have F2: p ^ n.+1 %| #|K|.
    apply/dvdnP; exists u.
    rewrite -(LaGrange Hsl1) Hu (eqP Hsl2) /= (mulnA u).
    exact: mulnC. 
  by move: F2; rewrite /n dvdn_p_p_part // (cardD1 1) group1.
have F2:  indexg L K %% p = #|lS0| %% p. 
  (* THIS IS ALSO IN THE SYLOW1_REC LEMMA *)
  have CL : #|L| = (p ^ n)%N by exact: (eqP Hsl2).
  rewrite (@mpl _ _ (trans_action gT) _ _ _ _ prime_p Hch).
    by congr (_ %% _); apply: eq_card => Ha; rewrite inE /= !inE /= andbC.
  apply: intro_closed=> A B; first exact: orbit_csym.
  case/imsetP=> x Lx ->; case/imsetP=> y Ky ->; apply/imsetP.
  exists (y*x); first by rewrite groupM // (subsetP Hshk x).
  by rewrite /= !rcosetE rcosetM.
rewrite /dvdn {}F2 in F1.
have F3: exists x, x \in lS0.
  apply/pred0Pn.
  by move: F1; rewrite /pred0b; case: #|lS0| => //=; rewrite mod0n.
case: F3 => Hx; case/setIP=> Hx2; rewrite inE => Hx3.
do [case/imsetP: Hx2 => x Kx /= ->; rewrite rcosetE] in Hx3.
exists x; rewrite Kx /=; exact: (@act_fix_sub _ L).
Qed.

(**********************************************************************)
(*               Second Sylow theorem                                 *)
(**********************************************************************)

Lemma sylow2_cor: forall (L1 L2 : {group gT}),
   sylow K L1 -> sylow K L2 -> exists x, x \in K /\ L2 = L1 :^ x :> set _.
Proof.
move => L1 L2 Hl1; case/andP => Ml2 Nl2.
case: (sylow2 Ml2 (eqP Nl2) Hl1) => x; move/andP=> [Hx1 Hx2].
exists x; split => //.
apply/setP; apply/subset_cardP => //.
rewrite card_conjg (eqP Nl2).
by apply sym_equal; apply/eqP; case/andP: Hl1.
Qed.
 
Theorem sylow2_subset: forall i (L P : {group gT}),
  L \subset K -> #|L| == (p ^ i)%N -> sylow K P -> P <| K -> L \subset P.
Proof.
move=> i L P Hlk Hcl Hsp Hnp.
case (@sylow1_subset i L) => // P1; case/andP => Hlp1 Hsp1.
case (sylow2_cor Hsp Hsp1) => x [Kx EP1].
by case/normalsubP: Hnp => _ nPK; rewrite EP1 nPK in Hlp1.
Qed.

(**********************************************************************)
(*   First part of the third Sylow theorem                            *)
(**********************************************************************)

Definition gsylow A : pred {group gT} := [eta sylow A].

Theorem sylow3_div : #|gsylow K| %| #|K|.
Proof.
case sylow1_cor => H Hh.
suff ->: #|gsylow K| = #|orbit (gconj_action gT) K H|.
  exact: card_orbit_div.
apply: eq_card => L; apply/idP/idP; last first.
  by case/orbitP => y Hy <- /=; rewrite /gsylow -topredE /= -sylow_sconjgr.
case/(sylow2_cor Hh) => y [Hy HH].
by apply/orbitP; exists y; last exact: val_inj.
Qed.

End Sylow.

Section SylowAux.

Open Scope group_scope.

Variable (gT : finGroupType) (H K L : {group gT}).
Hypothesis subset_HL : H \subset L.
Hypothesis subset_LK : L \subset K.

Variable p : nat.
Hypothesis prime_p : prime p.
Let n := logn p #|K|.

Hypothesis n_pos: 0 < n.

Lemma sylow_subset: sylow p K H -> sylow p L H.
Proof.
move/andP => [H1 H2].
apply/andP; split => //.
rewrite (eqP H2); apply/eqP.
suff ->: logn p #|K| = logn p #|L| by [].
apply/eqP; rewrite eqn_leq; apply/andP; split.
  rewrite -dvdn_exp_max -?(eqP H2) //; exact: group_dvdn.
apply dvdn_leq_log => //; exact: group_dvdn.
Qed.

End SylowAux.

Section Sylow3.

Open Scope group_scope.

Variable (gT : finGroupType) (K : {group gT}).

Variable p : nat.
Hypothesis prime_p : prime p.

Let n := logn p #|K|.

Hypothesis n_pos : 0 < n.

(**********************************************************************)
(*   Second part of the third Sylow theorem                           *)
(**********************************************************************)
Lemma sylow3_mod : #|gsylow p K| %% p = 1%N.
Proof.
case (sylow1_cor K prime_p) => H Hh.
case/andP: (Hh) => F2 F3.
rewrite -(eq_card (in_set (gsylow p K))).
rewrite (mpl prime_p (eqP F3) (to := gconj_action gT)); last first.
  move => L1 L2 /=.
  rewrite !inE.
  case/imsetP => x Hx1 ->; apply: sylow_sconjgr.
  exact: (subsetP F2).
rewrite -(@modn_small 1%N p); last by case: p prime_p => //=; case.
congr (_ %% _).
set S0 := predI _ _.
have F5: H \in S0.
  apply/andP; split; last by rewrite /= inE.
  apply/act_fixP => x Hx; apply: group_inj; exact: conjGid.
have F6: forall x, x \in S0 -> x = H.
  move => L; case/andP; move/act_fixP.
  rewrite /= inE /= => Hl Hl1.
  case/andP: (Hl1) => Hl3 Hl4.
  pose nLK := ('N(L) :&: K)%G.
  have F7: H \subset nLK. 
    apply/subsetP => y Hy.
    rewrite inE; apply/andP; split; last exact: (subsetP F2).    
    by rewrite inE /= -{2}(Hl _ Hy) subset_refl.
  have F8 : sylow p nLK H.
    apply: (@sylow_subset _ _ K)  => //.
    apply/subsetP => y.
    by rewrite inE; case/andP.
  have F9 : sylow p nLK L.
    apply: (sylow_subset (K := K)) => //;
      last by apply/subsetP => y; rewrite inE; case/andP.
    apply/subsetP => /= x Hx.
    apply/setIP; split.
      by apply: (subsetP (normG L)).
    by apply: (subsetP Hl3).
  case: (sylow2_cor prime_p F9 F8) => u [Hu Hu1].
  apply: val_inj; rewrite /= Hu1.
  by rewrite (normgP _) //; case/setIP: Hu.
rewrite (cardD1 H S0) F5.
rewrite -[1%N]addn0; congr addn.
apply: eq_card0 => x /=; rewrite inE /= inE /= andbC.
case S0x: (x \in S0) => //; apply/eqP; exact: F6.
Qed.

End Sylow3.

Unset Implicit Arguments.
