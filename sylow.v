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
Require Import fintype div prime finfun finset ssralg.
Require Import bigops groups morphisms normal action cyclic zp. 
Require Import dirprod pgroups nilpotent.

(* Require Import paths connect. *)

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.
Import GroupScope.

Section Cauchy.

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
  rewrite order_dvd -(eqP prodt) -{1}(size_iota 0 p) /prod_over_zp.
  by apply/eqP; elim: (iota _ _) => //= i s <-; rewrite Dt.
case/primeP: prime_p => _ divp; move/divp; case/orP; rewrite eq_sym //.
move/eqP=> Dx1; case/eqP: tnot1; apply/ffunP=> i.
by rewrite Dt -(expg1 x) ffunE Dx1 order_expn1.
Qed.

End Cauchy.

Section Sylow.

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

Lemma sylowE (A B: {set gT}) :
   sylow p A B = (B \subset A) && (#|B| == p_part p #|A|)%N.
Proof.
have filter_pred1: forall (T : eqType) (a: T) s,
       uniq s ->  filter (pred1 a) s = if a \in s then [::a] else [::].
  move=> T a; elim => [| b s IHr] //=; case/andP => N1 U1.  
  rewrite inE eq_sym; case: eqP => //= E1; rewrite IHr //.
  by rewrite -E1 {2}E1; move: N1; case: (_ \in _).
move=> A B; rewrite /sylow /hall /pi_part.
case: (_ \subset _) => //=.
rewrite -big_filter !(filter_pred1, uniq_primes) //= /p_part -ltn_0log.
by case E2: (logn p #|A|) => [| p1]; rewrite /= !(big_seq0, big_adds, E2, expn0, muln1).
Qed.

Lemma sylow_sconjgr: forall L x, x \in K -> sylow p K L = sylow p K (L :^ x).
Proof.
have F1: forall L x, x \in K -> sylow p K L -> sylow p K (L :^ x).
  move=> L x Kx; case/andP => sLK card_L.
  apply/andP; split; last by rewrite card_conjg card_L.
  apply/subsetP=> yx; case/imsetP=> y Ly ->{yx}.
  by rewrite groupJ // (subsetP sLK).
move=> L x Hx; apply/idP/idP => Hx1; first exact: F1.
by rewrite -[L](conjsgK x) F1 // groupV.
Qed.

Lemma sylow_sconjg: forall (H L: {set gT}) x, sylow p H L = sylow p (H :^ x) (L :^ x).
Proof.
have F1: forall (H L: {set gT}) x, sylow p H L -> sylow p (H :^ x) (L :^ x).
  move=> H L x; rewrite !sylowE; case/andP => sLH card_L.
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
pose H := coset_of L @*^-1 <[zbar]> :&: K.
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
case/cycleP=> m <-{xbar}; rewrite {nLH sLH}/H.
case/morphimP: Kzbar => z [Kz Nz ->{zbar}].
exists (z ^+ m); rewrite ?morphX // inE groupX ?Kz //= inE ?groupX //.
by apply/morphpreP; split=> //; apply: cyclenn.
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
  exists P : {group gT}, (L \subset P) && sylow p K P.
Proof.
move=> i L Hlk Hcl; case (@sylow1 i n L) => //.
  by rewrite leqnn andbT -dvdn_exp_max // -(eqP Hcl) group_dvdn.
by move=> H; case/and3P => [Hlh Hhk Hc]; exists H; rewrite Hlh // sylowE Hhk.
Qed.

Theorem sylow1_cor : exists P : {group gT}, sylow p K P.
Proof.
case (@sylow1_subset 0 [group of [set 1]]) => //=.
- by apply/subsetP => z; rewrite inE; move/eqP->; exact: group1.
- by rewrite cards1.
by move=> H; case/and3P => [_ Hhk Hc]; exists H; apply/andP.
Qed.

Lemma sylow2 : forall (H L : {group gT}) i, H \subset K ->
 #|H| = (p ^ i)%N -> sylow p K L -> exists2 x, x \in K & H \subset L :^ x.
Proof.
move => H L i Hshk Hch Hsl.
move: Hsl; rewrite sylowE; case/andP => Hsl1 Hsl2.
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
  sylow p K L1 -> sylow p K L2 -> exists2 x, x \in K & L2 = (L1 :^ x)%G.
Proof.
move => L1 L2 Hl1; rewrite sylowE; case/andP => Ml2 Nl2.
case: (sylow2 Ml2 (eqP Nl2) Hl1) => x Hx1 Hx2.
exists x => //; apply/eqP; rewrite -val_eqE eqset_sub_card Hx2 /=.
by rewrite card_conjg (eqP Nl2); 
   move: Hl1; rewrite sylowE; case/andP => _; move/eqP ->.
Qed.
 
Theorem sylow2_subset: forall i (L P : {group gT}),
  L \subset K -> #|L| == (p ^ i)%N -> sylow p K P -> P <| K -> L \subset P.
Proof.
move=> i L P Hlk Hcl Hsp Hnp.
case (@sylow1_subset i L) => // P1; case/andP => Hlp1 Hsp1.
case (sylow2_cor Hsp Hsp1) => x Kx [EP1].
by case/normalP: Hnp => _ nPK; rewrite EP1 /= nPK in Hlp1.
Qed.

(**********************************************************************)
(*   First part of the third Sylow theorem                            *)
(**********************************************************************)

Definition gsylow A : pred {group gT} := [eta (sylow p) A].

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
rewrite !sylowE; move/andP => [H1 H2]; apply/andP; split => //.
rewrite (eqP H2) /p_part; apply/eqP.
suff ->: logn p #|K| = logn p #|L| by [].
apply/eqP; rewrite eqn_leq; apply/andP; split; last first.
  by apply dvdn_leq_log => //; exact: group_dvdn.
by rewrite /p_part in H2; rewrite -dvdn_exp_max // -(eqP H2) group_dvdn.
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
case (sylow1_cor K prime_p) => H; rewrite sylowE => Hh.
case/andP: (Hh) => F2 F3.
pose Syl := [set P | gsylow p K P].
suff <-: #|Syl| %% p = 1%N by rewrite cardsE.
have: [acts (H | 'JG) on Syl].
  apply: (subset_trans F2); apply/actsP=> x Kx P.
  by rewrite !inE /gsylow !sylowE card_conjg -{1}(conjGid Kx) conjSg.
move/(mpl prime_p (eqP F3))->; rewrite -(([set H] =P _ :&: _) _).
  by rewrite cards1 modn_small ?prime_gt1.
rewrite eqset_sub {1}sub1set 2!inE /gsylow sylowE Hh /=; apply/andP; split.
  by apply/afixP=> x Hx; apply: group_inj; exact: conjGid.
apply/subsetP=> L; rewrite 2!{1}inE; case/andP=> sylL; move/afixP=> fixL.
rewrite inE eq_sym -val_eqE eqset_sub_card /= (eqP F3).
move: (sylL); rewrite /gsylow sylowE; case/andP => sLK.
move/eqP->; rewrite leqnn andbT.
have nLN: L <| 'N_K(L) by rewrite /(L <| _) subsetI sLK normG subsetIr.
apply: sylow2_subset F3 _ (nLN) => //.
  by rewrite subsetI F2; apply/normsP=> x Hx; rewrite -{2}(fixL x Hx).
by apply: sylow_subset sylL; rewrite ?subsetIl //; case/andP: nLN.
Qed.

End Sylow3.

Lemma Frattini : forall (gT : finGroupType) (G H P : {group gT}) p,
  H <| G -> prime p -> sylow p H P -> H * 'N_G(P) = G.
Proof.
move=> gT G H P p; case/normalP=> sHG nHG p_prime sylP.
have sPG: P \subset G by apply: subset_trans sHG; case/andP: sylP.
apply/eqP; rewrite eqset_sub setIC group_modl // subsetIr.
apply/subsetP=> x Gx; pose Q := (P :^ x^-1)%G.
have sylQ: sylow p H Q by  by rewrite (sylow_sconjg _ _ _ x) conjsgKV nHG.
have [y Hy [/= QPy]] := sylow2_cor p_prime sylP sylQ.
rewrite inE Gx andbT -(mulKg y x) mem_mulg ?groupV //.
by apply/normP; rewrite conjsgM -QPy conjsgKV.
Qed.

Definition sylows (gT : finGroupType) (G: {group gT}) (A: {set gT}):=
   if primes #|A| is [::p] then group_set A && sylow p G A
   else false.

Lemma sylowsP (gT : finGroupType) (G: {group gT}) P: 
  reflect (exists p, [/\ prime p, p %| #|G|, group_set P & sylow p G P]) 
          (sylows G P).
Proof.
move=> gT G P; apply: (iffP idP).
  rewrite /sylows; case: primes (mem_primes^~ #|P|)=> // p [|p1] //.
  move/(_ p); rewrite inE eqxx /=; move/eqP.
  rewrite eq_sym; move/eqP; move/idP; case/and3P=> H1P H2P H3P.
  case/andP=> H4P H5P; exists p; split=> //.
  rewrite (dvdn_trans H3P) // (@group_dvdn _ (Group H4P)) //=.
  by case/andP: H5P.
case=> p [H1p H2p H3p]; rewrite sylowE; case/andP=> H4p H5p.
by rewrite /sylows (eqP H5p) 
          !(primes_exp, primes_prime, H3p, sylowE, H4p) //  
          -dvdn_exp_max // expn1.
Qed.

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

Section DirProd.

Variable gT: finGroupType.

(* General lemmas to get to sylow_dirprod *) 
Lemma coprime_bigprod: forall p (I: eqType) r (P : pred I) F,
  (forall i : I, P i  && (i \in r) -> coprime p (F i)) ->
  coprime p (\prod_(i <- r | P i) F i).
Proof.
move=> p I r P F HcF.
apply big_prop_seq => [| x y Hx Hy |//]; first by exact: coprimen1.
by rewrite coprime_mulr Hx.
Qed.

Lemma div_primes: forall (n m: nat), 0 < n ->
  (forall p, p \in primes n -> p_part p n %| m) -> n %| m.
Proof.
move=> n m Hn Hpa.
rewrite -(prod_p_parts Hn).
have: forall i, i \in primes n -> prime i.
  by move=> i; rewrite mem_primes; case/andP.
have: uniq (primes n) by exact: uniq_primes.
elim: (primes n) Hpa => [| i r Hrec];
  rewrite !(big_seq0, big_adds) /= ?dvd1n //.
move=> H1; case/andP=> H2 H3 H4.
have Hrec1: \prod_(p <- r) p_part p n %| m.
  by apply: Hrec => // p Hp; rewrite (H1, H4) // inE orbC Hp.
rewrite gauss_inv //; first by rewrite Hrec1 H1 // inE eqxx.
apply: coprime_bigprod => j /= Hj.
rewrite coprime_expl // coprime_expr //.
have Pi: prime i by rewrite H4 // inE eqxx.
have Pj: prime j by rewrite H4 // inE orbC Hj.
rewrite prime_coprime //.
apply/negP => HH; case/negP: H2.
case/primeP: (Pj) => _; move/(_  _ HH); case/orP => // Hi.
  by move: Pi; rewrite (eqP Hi).
by rewrite (eqP Hi).
Qed.

Lemma comm_bigprod: forall (A: {set gT}) (I: eqType) r (P: pred I) F,
  (forall i, P i && (i \in r) -> A \subset 'C(F i)) -> 
  A \subset 'C(\prod_(i <- r | P i) F i).
Proof.
move=> A I r P F Hg.
apply: (@big_prop_seq _ (fun x => A \subset 'C(x))) => 
    [|B C HB HC|//]; rewrite centsC; last first.
  by rewrite mul_subG // centsC.
by apply/subsetP=> x; rewrite inE; move/eqP->; rewrite group1.
Qed.

Lemma subset_bigprod: forall (A: {group gT}) I r (P: pred I) (F: I -> {set gT}),
  (forall i : I, P i -> F i \subset A) -> \prod_(i <- r | P i) F i \subset A.
Proof.
move=> A I r P F Hg.
by apply big_prop => [| B C HB HC|//]; rewrite (sub1G, mul_subG).
Qed.

Lemma group_set_bigprod: forall (I: eqType) (r : seq I) P (F: I -> {set gT}),
   uniq r ->
  (forall i, P i && (i \in r) -> group_set (F i)) ->
  (forall i j, i <> j -> P i && (i \in r) -> P j && (j \in r) ->
           (F i) \subset 'C(F j)) ->
  group_set (\prod_(i <- r | P i) F i).
Proof.
move=> I r P F; elim: r => [| i r Hrec];
  rewrite !(big_seq0, big_adds, group_set_unit) => //=.
case/andP => Hir Hu Hi Ha.
have HGi: group_set (\prod_(j <- r | P j) F j).
  apply: Hrec => [//| i1 | i1 j1 Hi1j1]; case/andP => Hp1 Hip1.
    by rewrite Hi // Hp1 inE orbC Hip1.
  by case/andP => Hpj1 Hjp1; rewrite Ha // inE ?Hip1 ?Hjp1 orbC andbC.
case Ep1: (P i) => //.
have HG1: group_set (F i) by rewrite Hi // Ep1 inE eqxx.
pose Gi := (Group HG1).
pose G1 := (Group HGi).
apply/group_setP; split.
  by apply/imset2P; exists (1:gT) (1:gT); rewrite ?mul1g ?(group1 Gi) ?(group1 G1).
move=> x y; case/imset2P=> x1 x2 Hx1 Hx2 ->; case/imset2P=> y1 y2 Hy1 Hy2 ->.
apply/imset2P; exists (x1 * y1) (x2 * y2); first by rewrite (@groupM _ Gi).
  by rewrite (@groupM _ G1).
rewrite !mulgA; congr mulg; rewrite -!mulgA; congr mulg.
suff: F i \subset 'C(\prod_(j <- r| P j) F j) by  move/centsP; move/(_ _ Hy1 _ Hx2).
apply: comm_bigprod => j; case/andP => H1j H2j.
apply: Ha => [Hij||]; first by case/negP: Hir; rewrite Hij.
  by rewrite Ep1 inE eqxx.
by rewrite H1j inE orbC H2j.
Qed.

Lemma card_bigprod: forall (I: eqType) (r : seq I) P (F: I -> {set gT}),
  uniq r ->
  (forall i, P i && (i \in r) -> group_set (F i)) ->
  (forall i j, i <> j -> P i && (i \in r) -> P j && (j \in r) ->
           (F i) \subset 'C(F j)) ->
  (forall i j, i <> j -> P i && (i \in r) -> P j && (j \in r) ->
           coprime #|F i| #|F j|) ->
  #|(\prod_(i <- r | P i) (F i: set _))| =  (\prod_(i <- r | P i) #|F i|)%N.
Proof.
move=> I r P F; elim: r => [| i r Hrec];
  rewrite !(big_seq0, big_adds, cards1) => //=.
case/andP=> H1u H2u Hg Hs Hc.
have Hr: #|\prod_(i <- r | P i) F i| = (\prod_(i <- r | P i) #|F i|)%N.
  apply: Hrec => [// | i1 | i1 j1 Hij1 | i1 j1 Hij1]; case/andP => H1i1 H2i1.
  - by rewrite Hg // H1i1 inE H2i1 orbC.
  - by case/andP => H1j1 H2j1; rewrite Hs // (H1i1, H1j1) inE (H2i1, H2j1) orbC.
  by case/andP => H1j1 H2j1; rewrite Hc // (H1i1, H1j1) inE (H2i1, H2j1) orbC.
case Ep1: (P i) => //.
have HG1: group_set (F i) by rewrite Hg // Ep1 inE eqxx.
set H := reducebig _ _ _ _ _.
have GH: group_set H.
  apply: group_set_bigprod =>  [// | i1 | i1 j1 Hij1]; case/andP => H1i1 H2i1.
  - by rewrite Hg // H1i1 inE H2i1 orbC.
  by case/andP => H1j1 H2j1; rewrite Hs // (H1i1, H1j1) inE (H2i1, H2j1) orbC.
pose Gi := (Group GH).
pose G1 := (Group HG1).
rewrite (@coprime_card_mulG _ G1 Gi) //= Hr //.
apply: coprime_bigprod => j; case/andP => H1j H2j.
rewrite Hc // ?(Ep1, H1j, inE, eqxx, H2j, orbT) //.
by move=> Hij; case/negP: H1u; rewrite Hij.
Qed.

Lemma sylow_dirprod (G : {group gT}):
  (forall Pi, sylows G Pi -> Pi <| G) ->
 \big[direct_product/1]_(Pi | sylows G Pi) Pi = G.
Proof.
move => G HG.
pose r := index_enum  [finType of {set gT}].
have Hur: uniq r by apply: uniq_enum.
have Hgr: forall i, sylows G i && (i \in r) -> group_set i.
  by move=> i; case/andP; case/sylowsP => p; case.
have Hcr: forall Pi Pj, Pi <> Pj -> 
            sylows G Pi && (Pi \in r) -> sylows G Pj && (Pj \in r) -> 
            coprime #|Pi| #|Pj|.
  move=> Pi Pj Hij.
  case/andP; case/sylowsP => p1 [H1pi H2pi H3pi]; 
     rewrite sylowE; case/andP => H4pi H5pi H6pi.
  case/andP; case/sylowsP => p2 [H1pj H2pj H3pj];
     rewrite sylowE; case/andP => H4pj H5pj H6pj.
  rewrite (eqP H5pi) (eqP H5pj) coprime_expl // coprime_expr //.
  rewrite prime_coprime //.
  apply/negP => Hp1p2; case: Hij; apply: (@sylowNLE _ G (Group H3pi) (Group H3pj) _ H1pi).
  - by apply: HG; apply/sylowsP; exists p1; split => //; rewrite sylowE H4pi.
  - by rewrite sylowE H4pi.
  case/primeP: H1pj => _; move /(_ _ Hp1p2); case/orP.
    by move/eqP => Hp1; move: H1pi; rewrite Hp1.
  by move/eqP->; rewrite sylowE H4pj.
have Hsr: forall Pi Pj, Pi <> Pj -> 
            sylows G Pi && (Pi \in r) -> sylows G Pj && (Pj \in r) -> 
            Pi \subset 'C(Pj).
  move=> Pi Pj Hij Hsi Hsj.
  case/andP: (Hsi); case/sylowsP => p1 [H1pi H2pi H3pi]; case/andP => H4pi H5pi H6pi.
  case/andP: (Hsj); case/sylowsP => p2 [H1pj H2pj H3pj]; case/andP => H4pj H5pj H6pj.
  apply/centsP => x Hx y Hy.
  apply/commgP.
  have Ht: trivg (Pi :&: Pj).
    by rewrite (@coprime_trivg _ (Group H3pi) (Group H3pj)) // Hcr.
  move/subsetP: Ht; move/(_ [~ x, y]); rewrite !inE => -> //.
  rewrite -[Pi]/(Group H3pi: set _) -[Pj]/(Group H3pj: set _)
          {1}commgEl commgEr; apply/andP; split; rewrite groupM // ?groupV //.
    have: Pi <| G by apply: HG; case/andP: Hsi.
    case/normalP => /= _; move/(_ y)<-; last by apply: (subsetP H4pj).
    by apply/imsetP; exists x.
  have: Pj <| G by apply: HG; case/andP: Hsj.
  case/normalP => /= _; move/(_ x)<-; last by apply: (subsetP H4pi). 
  by apply/imsetP; exists (y^-1); rewrite // (@groupV _ (Group H3pj)) //.
have GP: group_set (\prod_(Pi | sylows G Pi) Pi) by apply: group_set_bigprod.
have<-: \prod_(Pi | sylows G Pi) Pi = G.
  apply/eqP; rewrite eqset_sub_card.
  rewrite subset_bigprod; last by move=> i; case/sylowsP => x [_ _ _]; case/andP.
  apply: dvdn_leq => //.
    by rewrite (@ltn_0group _ (Group GP)).
  apply: div_primes; first by apply: ltn_0group.
  move=> p Hp.
  have H1p: prime p.
    by move: Hp; rewrite mem_primes; case/and3P.
  case: (@sylow1_cor _ G _ H1p) => Pj HPj.
  move: (HPj); rewrite sylowE; case/andP => _; rewrite /p_part; move/eqP<-.
  rewrite card_bigprod //-/r.
  have: (Pj: [finType of {set gT}]) \in r by rewrite mem_enum //.
  elim: (r) => [| i r1 Hrec]; rewrite !(big_seq0, big_adds) => //=.
  rewrite inE; case/orP => H1Pj; last first.
    by case: sylows; rewrite ?(dvdn_mull) // Hrec.
  rewrite -(eqP H1Pj); suff->: sylows G Pj by rewrite dvdn_mulr.
  apply/sylowsP; exists p; split; rewrite // ?groupP //.
  by move: Hp; rewrite mem_primes; case/and3P.
have: uniq r by apply: uniq_enum.
rewrite -/r; elim: (r) => [| Pi r1 Hrec]; rewrite !(big_seq0, big_adds) => //=.
case/andP => H1r1 H2r1; move: (Hrec H2r1) => Hrec1; case E1: (sylows _ _) => //.
rewrite {1}/direct_product Hrec1 //.
set H:= \prod_(Pi <- r1 | sylows G Pi)Pi.
have F1: forall i, sylows G i && (i \in r1) -> group_set i.
   by move=> Pi1; case/andP=> HPi1 _; rewrite Hgr // HPi1 mem_enum.
have F2: forall i j, i <> j ->
  sylows G i && (i \in r1) -> sylows G j && (j \in r1) -> coprime #|i| #|j|.
  by move=> Pi1 Pj1 Hij1; case/andP=> HPi1 _; case/andP=> HPj1 _; 
     rewrite Hcr // (HPi1, HPj1) mem_enum.
have F3: forall Pj, sylows G Pj && (Pj \in r1) -> coprime #|Pi| #|Pj|.
  move=> Pi1; case/andP=> H1Pi1 H2Pi1; rewrite Hcr // ?(E1, H1Pi1, mem_enum) //.
  by move=> HH; case/negP: H1r1; rewrite HH.
have F4: forall i j, i <> j ->
  sylows G i && (i \in r1) -> sylows G j && (j \in r1) -> i \subset 'C(j).
  by move=> Pi1 Pj1 Hij1; case/andP=> HPi1 _; case/andP=> HPj1 _; 
     rewrite Hsr // (HPi1, HPj1) mem_enum.
have GPi: group_set Pi by rewrite Hgr // E1 mem_enum.
have GH: group_set H by apply: (group_set_bigprod  H2r1).
have->: trivg (Pi :&: \prod_(Pi <- r1 | sylows G Pi)Pi) by
  rewrite (@coprime_trivg _ (Group GPi) (Group GH)) ?(card_bigprod,coprime_bigprod).
rewrite /central_product GPi GH.
have ->: Pi \subset 'C(H).
  apply: comm_bigprod => Pi1.
  case/andP=> HPi1 H1Pi1; rewrite Hsr // ?(E1, HPi1, mem_enum) //.
  by move=> HH; case/negP: H1r1; rewrite HH.
case: eqP => He1; first by rewrite He1 -{1}(@set_mul1g gT H).
by case: eqP => He2; rewrite // He2 -{1}(mulg1 Pi).
Qed.


Lemma nilpotent_sylow: forall G: {group gT}, 
  nilpotent G <-> \big[direct_product/1]_(Pi | sylows G Pi) Pi = G.
Proof.
move=> G; have Hg0: (0 < #|G|) by rewrite (cardD1 1) group1.
split=> Hg; last first.
  apply: (nilpotent_bigdprod Hg) => Pi.
  case/sylowsP=> p [H1p H2p H3p]; rewrite sylowE; case/andP=> H4p H5p.
  suff: nilpotent (Group H3p) by done.
  apply: nilpotent_pgroup; rewrite /= (eqP H5p).
  by rewrite primes_exp ?primes_prime // ltn_0log mem_primes H1p Hg0.
apply: sylow_dirprod.
move=> Pi; case/sylowsP=> p [H1p H2p H3p H4p].
pose H := 'N_G(Pi)%G; pose N := 'N_G(H)%G.
have SHG: H \subset G by apply/subsetP=> x; rewrite inE; case/andP.
rewrite (@nilpotent_sub_norm _ G H) //.
  by apply: (@normalSG _ G (Group H3p)); case/andP: H4p.
have normHN: H <| N.
  by apply: normalSG; apply/subsetP=> x; rewrite inE; case/andP.
have SPi: sylow p H Pi.
 apply: (@sylow_subset gT (Group H3p) G)=> //=.
   apply/subsetP=> x; rewrite inE => Hx.
   case/andP: H4p; move/subsetP; move/(_ x Hx)=> -> _.
   by exact: (subsetP (normG (Group H3p)) x Hx).
move: (@Frattini _ _ _ (Group H3p) _ normHN H1p SPi).
suff H1: 'N_N(Pi) \subset H.
  by rewrite (mulGSgid (group1 _)) // => EHN; rewrite {2}EHN.
by apply/subsetP=> x; rewrite !inE; rewrite -andbA; case/and3P=> ->.
Qed.

End DirProd.

Unset Implicit Arguments.
