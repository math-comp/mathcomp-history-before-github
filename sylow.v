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
Require Import fintype connect div finfun finset.
Require Import groups normal action cyclic zp.

(* Require Import paths. *)

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
Notation zp := 'I_p.
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

Notation Local "'rot" := zprot_action (at level 0) : action_scope.

Lemma zprot_acts_on_X : [acts (setT | 'rot) on X].
Proof.
apply/subsetP=> /= x _; rewrite inE /=; apply/subsetP=> f.
rewrite !inE -(zp1_gen x) /=; elim: {x}(x : nat) f => /= [|i IHi] f.
  by rewrite zprot_to1.
rewrite expgS zprot_to_morph; case/andP; move/ffun_onP=> Hfx prodf1.
apply: IHi; rewrite {i} rot1_prod_over_zp prodf1 andbT.
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

Theorem cauchy : exists a, (a \in H) && (#[a] == p).
Proof.
have card_zp: #|(setT : {set zp})| = (p ^ 1)%N.
  by rewrite cardsE card_ord expn1.
have:= mpl prime_p card_zp zprot_acts_on_X; set Z := _ :&: _.
rewrite card_X -{1}(subnK lt1p) /= -modn_mul2m (eqnP p_divides_H) mod0n.
pose t1 : {ffun zp -> gT} := [ffun => 1].
have Zt1: t1 \in Z.
  rewrite 2!inE; apply/andP; split; last first.
    by apply/afixP=> x _; apply/ffunP=> i; rewrite !ffunE.
  apply/andP; split; first by apply/ffun_onP=> u; rewrite ffunE /=.
  rewrite /prod_over_zp; apply/eqP; elim: (iota _ _) => //= i s -> {s}.
  by rewrite ffunE mul1g.
case: (pickP [predD1 Z & t1]) => [t | Z0]; last first.
  by rewrite (cardD1 t1) Zt1 (eq_card0 Z0) modn_small.
case/andP=> tnot1; rewrite /= 2!inE; do 2!case/andP.
move/ffun_onP=> /= Ht prodt; move/afixP=> /= fixt _.
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
  have <-: #|'C_(rcosets L K)(L | 'Msr)| = #|K / L|.
    rewrite rtrans_fix_norm -(card_imset (mem (K / L)) val_inj).
    apply: eq_card=> Lk; rewrite val_quotient //.
  have divpLK : p %| #|K : L|.
    rewrite -(@dvdn_pmul2l #|L|) // (LaGrange sLK) (eqP cardL) mulnC -expnS.
    by rewrite dvdn_exp_max.
  apply/eqP; rewrite -{divpLK}(eqnP divpLK) -(mpl prime_p (eqP cardL)) //.
  apply/subsetP=> x Lx; rewrite /= inE; apply/subsetP=> A; rewrite /= inE.
  case/imsetP=> y Ky ->{A}; rewrite !rcosetE -rcosetM -rcosetE mem_imset //.
  by rewrite groupMl // (subsetP sLK).
case/cauchy=> // zbar; case/andP=> Kzbar; move/eqP=> Czbar_p.
pose H := coset_of L @*^-1 cyclic zbar :&: K.
exists [group of H] => /=.
have sLH : L \subset H.
  apply/subsetP => x Lx.
  apply/setIP; split; last exact: (subsetP sLK).
  apply/setIP; split; first by rewrite (subsetP (normG _)).
  by rewrite /= inE coset_of_id // group1.
have nLH: H \subset 'N(L).
  by apply/subsetP=> x; case/setIP; case/morphpreP=> *. 
rewrite /(_ <| _) sLH nLH subsetIr -(@LaGrange _ L) // -card_quotient //= -/H.
rewrite (eqP cardL) mulnC -{}Czbar_p.
apply/eqP; congr (_ * _)%N; apply: eq_card => xbar.
apply/imsetP/idP=> [[x Hx ->{xbar}]|].
  by rewrite 3!inE andbC -andbA in Hx; case/andP: Hx; case/morphpreP=>[_].
case/cyclicP=> m <-{xbar}; rewrite {nLH sLH}/H.
case/morphimP: Kzbar => z [Kz Nz ->{zbar}].
exists (z ^+ m); rewrite ?morphX // inE groupX ?Kz //= inE ?groupX //.
by apply/morphpreP; split=> //; apply:cyclicnn.
Qed.

Lemma sylow1: forall i j (L : group gT), i <= j <= n ->
  L \subset K -> #|L| == (p ^ i)%N ->
  exists H: group gT, [&& L \subset H, H \subset K & #|H| == p ^ j]%N.
Proof.
move=> i j L; case/andP=> Hij Hjn Hsl Hcl.
move: Hjn; rewrite -(subnK Hij) addnC.
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
  by rewrite leqnn andbT -dvdn_exp_max // -(eqP Hcl) group_dvdn.
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
 #|H| = (p ^ i)%N -> sylow K L -> exists2 x, x \in K & H \subset L :^ x.
Proof.
move => H L i Hshk Hch Hsl.
case/andP: Hsl => Hsl1 Hsl2.
pose lS0 := 'C_(rcosets L K)(H | 'Msr).
have F1: ~~ (p %| #|K : L|).
  apply/negP => Fd.
  move/dvdnP: Fd => [u Hu].
  have F2: p ^ n.+1 %| #|K|.
    apply/dvdnP; exists u.
    rewrite -(LaGrange Hsl1) Hu (eqP Hsl2) /= (mulnA u).
    exact: mulnC. 
  by move: F2; rewrite /n dvdn_p_p_part // (cardD1 1) group1.
have F2: #|K : L| %% p = #|lS0| %% p. 
  rewrite -(mpl prime_p Hch) //; apply/subsetP=> x Hx; rewrite inE /=.
  apply/subsetP=> A; rewrite inE /=; case/imsetP=> y Ly ->{A}.
  by rewrite !rcosetE -rcosetM -rcosetE mem_imset ?groupM // (subsetP Hshk).
have{F1 F2}: #|lS0| != 0.
  by move: F1; rewrite /dvdn F2; case: #|lS0|; rewrite ?mod0n.
case/existsP=> X; case/setIP; case/imsetP=> x Kx ->{X}; rewrite rcosetE.
by move/act_fix_sub; exists x.
Qed.

(**********************************************************************)
(*               Second Sylow theorem                                 *)
(**********************************************************************)

Lemma sylow2_cor: forall L1 L2 : {group gT},
  sylow K L1 -> sylow K L2 -> exists2 x, x \in K & L2 = (L1 :^ x)%G.
Proof.
move => L1 L2 Hl1; case/andP => Ml2 Nl2.
case: (sylow2 Ml2 (eqP Nl2) Hl1) => x Hx1 Hx2.
exists x => //; apply/eqP; rewrite -val_eqE eqset_sub_card Hx2 /=.
by rewrite card_conjg (eqP Nl2); case/andP: Hl1 => _; move/eqP ->.
Qed.
 
Theorem sylow2_subset: forall i (L P : {group gT}),
  L \subset K -> #|L| == (p ^ i)%N -> sylow K P -> P <| K -> L \subset P.
Proof.
move=> i L P Hlk Hcl Hsp Hnp.
case (@sylow1_subset i L) => // P1; case/andP => Hlp1 Hsp1.
case (sylow2_cor Hsp Hsp1) => x Kx [EP1].
by case/normalP: Hnp => _ nPK; rewrite EP1 /= nPK in Hlp1.
Qed.

(**********************************************************************)
(*   First part of the third Sylow theorem                            *)
(**********************************************************************)

Definition gsylow A : pred {group gT} := [eta sylow A].

Theorem sylow3_div : #|gsylow K| %| #|K|.
Proof.
case sylow1_cor => H Hh.
suff ->: #|gsylow K| = #|orbit 'JG%act K H| by exact: card_orbit_div.
apply: eq_card => L; apply/idP/idP; last first.
  by case/orbitP => y Hy <- /=; rewrite /gsylow -topredE /= -sylow_sconjgr.
case/(sylow2_cor Hh) => y Hy [HH].
by apply/orbitP; exists y.
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
pose Syl := [set P | gsylow p K P].
suff <-: #|Syl| %% p = 1%N by rewrite cardsE.
have: [acts (H | 'JG) on Syl].
  apply: (subset_trans F2); apply/actsP=> x Kx P.
  by rewrite !inE /gsylow /sylow card_conjg -{1}(conjGid Kx) conjSg.
move/(mpl prime_p (eqP F3))->; rewrite -(([set H] =P _ :&: _) _).
  by rewrite cards1 modn_small ?prime_gt1.
rewrite eqset_sub {1}sub1set 2!inE /gsylow Hh /=; apply/andP; split.
  by apply/afixP=> x Hx; apply: group_inj; exact: conjGid.
apply/subsetP=> L; rewrite 2!{1}inE; case/andP=> sylL; move/afixP=> fixL.
rewrite inE eq_sym -val_eqE eqset_sub_card /= (eqP F3).
case: (andP sylL) => sLK; move/eqP->; rewrite leqnn andbT.
have nLN: L <| 'N_K(L) by rewrite /(L <| _) subsetI sLK normG subsetIr.
apply: sylow2_subset F3 _ (nLN) => //.
  by rewrite subsetI F2; apply/normsP=> x Hx; rewrite -{2}(fixL x Hx).
by apply: sylow_subset sylL; rewrite ?subsetIl //; case/andP: nLN.
Qed.

End Sylow3.

Lemma normal_sylowP : forall (gT : finGroupType) (G : {group gT}) p,
  prime p -> reflect (exists2 P : {group gT}, sylow p G P & (P <| G)%g)
                     (#|gsylow p G| == 1%N).
Proof.
move=> gT G p p_pr; apply: (iffP idP) => [syl1 | [P sylP nPG]].
  have [P sylP]: exists P, P \in gsylow p G.
    by apply/existsP; rewrite /pred0b (eqP syl1).
  exists P => //; apply/normalP; split=> [|x Gx]; first by case/andP: sylP.
  apply/eqP; apply/idPn=> nPxP.
  rewrite (cardD1 P) sylP eqSS in syl1; case/existsP: syl1.
  exists (P :^ x)%G; rewrite /= nPxP -topredE /gsylow /=.
  by rewrite -(conjGid Gx) -sylow_sconjg.
rewrite (cardD1 P) [P \in _]sylP eqSS; apply/pred0P=> Q /=.
apply/andP=> [[nQP sylQ]]; case/eqP: nQP; apply: val_inj=> /=.
case: (sylow2_cor p_pr sylP sylQ) => x Gx ->{Q sylQ}.
case/normalP: nPG => _; exact.
Qed.

Lemma sylowNLE : forall (gT : finGroupType) (G P Q : {group gT}) p,
  prime p -> (P <| G)%g -> sylow p G P -> sylow p G Q -> P = Q :> set _.
Proof.
move=> gT G P Q p Pp Npg Sp Sq.
have: #|gsylow p G| == 1%N by apply/(normal_sylowP _ Pp); exists P.
  rewrite (cardD1 P) (cardD1 Q) .
rewrite [_ \in _]Sp inE [predD1 _ _ _]/= [_ \in _]Sq.
by case E1: (Q == P) => //; move/eqP: E1->.
Qed.

Unset Implicit Arguments.
