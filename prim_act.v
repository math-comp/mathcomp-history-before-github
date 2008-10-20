(***********************************************************************)
(* (c) Copyright Microsoft Corporation and Inria. All rights reserved. *)
(*                                                                     *)
(***********************************************************************)
Require Import ssreflect ssrbool ssrfun eqtype ssrnat.
Require Import div seq fintype.
(* Require Import connect. *)
Require Import tuple finfun ssralg bigops finset.
Require Import groups group_perm morphisms action maximal.

(* n-transitive and primitive actions *)

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Import GroupScope.

Section PrimitiveDef.

Variables (aT : finGroupType) (sT : finType).
Variables (A : {set aT}) (to : {action aT &-> sT}) (S : {set sT}).

Definition primitive :=
  (#|S| > 0) &&
  forallb R : {ffun sT -> {ffun sT -> bool}},
   [==> forallb x, (x \in S) ==> R x x,
        forallb x, forallb y, forallb a,
         [==> x \in S, y \in S, a \in A, R x y => R (to x a) == R (to y a)]
    => (forallb x, forallb y, [==> x \in S, y \in S, R x y => x == y])
    || (forallb x, forallb y, [==> x \in S, y \in S => R x y])].

Lemma primitiveP:
  reflect
  ((exists x, x \in S) /\ forall R : rel sT,
      (forall x, x \in S -> R x x)
   -> (forall x y a, x \in S -> y \in S -> a \in A ->
       R x y -> R (to x a) =1 R (to y a))
   -> (forall x y, x \in S -> y \in S -> R x y -> x = y)
   \/ (forall x y, x \in S -> y \in S -> R x y))
   primitive.
Proof.
apply: (iffP andP) => /= [] [nS0 prim].
  split=> [|R Rrefl Rinv]; first by rewrite lt0n in nS0; move/existsP: nS0.
  pose gR := [ffun x => [ffun y => R x y]]; simpl in gR.
  have{nS0 prim} := forallP prim gR; case: forallP => [_ | [x]]; last first.
    by apply/implyP=> Sx; rewrite !ffunE Rrefl.
  case: forallP => [_ /= | [x]]; last first.
    apply/forallP=> y; apply/forallP=> a; apply/implyP=> Sx; apply/implyP=> Sy.
    apply/implyP=> Aa; rewrite !ffunE; apply/implyP=> Rxy; apply/eqP.
    by apply/ffunP=> c; rewrite !ffunE (Rinv _ y).
  case/orP; move/forallP=> prim; [left | right] => x y Sx Sy => [Rxy|];
    move/(_ x): prim; move/forallP; move/(_ y); rewrite Sx Sy !ffunE ?Rxy //=.
  exact: eqP.
split; first by case: nS0 => x Sx; rewrite (cardD1 x) Sx.
apply/forallP=> R; apply/implyP; move/forallP=> Rrefl.
apply/implyP; move/forallP=> Rinv.
apply/orP; move/(_ (fun x y => R x y)): prim.
case=> [x | x y a Sx Sy Aa Rxy | R1 | RS]; first exact/implyP.
- move/forallP: (Rinv x); move/(_ y); move/forallP; move/(_ a).
  by rewrite Sx Sy Aa Rxy; case: eqP => // ->.
- left; apply/forallP=> x; apply/forallP=> y.
  by apply/implyP=> Sx; apply/implyP=> Sy; apply/implyP; move/R1->.
right; apply/forallP => x; apply/forallP => y; apply/implyP=> Sx.
apply/implyP; exact: RS.
Qed.

End PrimitiveDef.

Notation "[ 'primitive' ( A | to ) 'on' S ]" := (primitive A to S)
  (at level 0, format "[ 'primitive'  (  A  |  to  )  'on'  S ]") : form_scope.

Implicit Arguments primitiveP [aT sT A to S].
Prenex Implicits primitiveP.

Section Primitive.

Variables (aT : finGroupType) (sT : finType).
Variables (G : {group aT}) (to : {action aT &-> sT}) (S : {set sT}).

Hypothesis Gtrans : [transitive (G | to) on S].
Let Gact := actsP (trans_acts Gtrans).

Lemma primitivePt:
  reflect
    (forall Y : {set sT},
       Y \subset S -> wdisjointn (mem G) (fun a x => to x a \in Y)
     -> #|Y| <= 1 \/ Y = S)
   [primitive (G | to) on S].
Proof.
apply: (iffP primitiveP) => [[_ prim] Y sYS impY| prim].
  case: leqP => cardY; [by left | right]; apply/eqP; rewrite eqset_sub sYS /=.
  case: (pickP (mem Y)) => [x /= Yx | Y0]; last by rewrite eq_card0 in cardY.
  move/subsetP: sYS => sYS; have Sx := sYS x Yx.
  pose R b c := existsb x, [&& x \in G, to b x \in Y & to c x \in Y].
  case/(_ R): prim => [y Sy | {x Sx Yx} x y a Sx Sy Ga | R1 | RS].
  - move: Sx; rewrite -(atransP Gtrans _ Sy); case/imsetP=> a Ga toya.
    by apply/existsP; exists a; rewrite -toya Ga Yx.
  - case/existsP=> [b]; case/and3P=> Gb Yxb Yyb z.
    wlog Ryaz: x y Sx Sy Yxb Yyb / R (to y a) z.
      by move=> impl; apply/idP/idP => R_az; move/impl: (R_az) ->.
    rewrite Ryaz; case/existsP: Ryaz => c; case/and3P=> Gc Yyac Yzc.
    apply/existsP; exists c; rewrite Gc {z}Yzc /= andbT -actM.
    by rewrite (impY _ b y) //= (actM, groupM).
  - move: cardY; rewrite (cardD1 x) Yx ltnS lt0n; case/existsP=> y /=.
    case/andP=> nyx Yy; case/eqP: nyx; apply: R1; rewrite ?sYS //.
    by apply/existsP; exists (1 : aT); rewrite group1 !act1 Yx Yy.
  apply/subsetP=> y Sy; case/existsP: (RS x y Sx Sy) => a; case/and3P=> Ga Yxa.
  move: Sy; rewrite -(atransP Gtrans x Sx); case/imsetP=> b Gb ->{y} Yxba.
  by rewrite (impY _ (b * a) (to x b^-1)) //= ?(actM, groupM, actKV).
case/imsetP: Gtrans => x Sx S_xA; split=> [|R Rrefl Rinv]; first by exists x.
pose Y := S :&: [set y | R x y].
case/(_ Y (subsetIl _ _)): prim => [a b y /= Ga Gb Yya Yyb z | Y1 | YS].
- wlog Yzb: a b Ga Gb Yya Yyb / to z b \in Y.
    by move=> impl; apply/idP/idP => Yz_; move/impl: (Yz_) ->.
  rewrite Yzb; move: Yya Yyb Yzb; rewrite !inE.
  case/andP=> Sya Rxya; case/andP=> Syb Rxyb; case/andP=> Szb Rxzb.
  have Sza: to z a \in S by rewrite !Gact in Szb *.
  have Gb1a: b^-1 * a \in G by rewrite groupM ?groupV.
  rewrite Sza -(act1 to x) (Rinv _ (to y a)) //= act1 -(actK to b y) -actM.
  by rewrite -(Rinv x) // (Rinv _ (to z b)) // actM actK Rrefl.
- left=> y z Sy; rewrite S_xA; case/imsetP=> a Ga ->{z} Ryxa.
  move: Y1; rewrite (cardD1 x) (cardD1 (to y a^-1)) !inE /= !inE Sx Rrefl //=.
  case: eqP => [<- _|_]; first by rewrite actKV.
  rewrite Gact ?groupV // Sy -{1}(actK to a x).
  by rewrite -(Rinv y) ?(Gact, groupV, Rrefl).
right=> y z; rewrite -YS !inE; case/andP=> Sy Rxy; case/andP=> Sz Rxz.
by rewrite -(act1 to y) -(Rinv x) ?act1.
Qed.

Lemma prim_trans_norm : forall H : {group aT},
  [primitive (G | to) on S] -> H <| G ->
     H \subset 'C_(G | to)(S) \/ [transitive (H | to) on S].
Proof.
move=> H prim; case/normalP=> sHG nHG; pose R x y := y \in orbit to H x.
case: (primitiveP prim) => [] [x Sx].
case/(_ R)=> [{x Sx} x Sx | {x Sx} x y a Sx _ Ga | {x Sx} R1 | RS].
- exact: orbit_refl.
- case/imsetP=> b Hb ->{y}; apply/setP; apply: orbit_transl.
  by rewrite actCJ orbit_sym mem_imset // -(nHG _ Ga) memJ_conjg.
- left; apply/subsetP => a Ha; have Ga: a \in G by apply: (subsetP sHG).
  rewrite inE Ga; apply/astabP=> x Sx; symmetry; apply: R1; rewrite ?Gact //.
  by rewrite [R _ _]mem_imset.
right; apply/imsetP; exists x => //.
apply/setP=> y; apply/idP/idP; first exact: RS.
by case/imsetP=> a Ha ->; rewrite Gact ?(subsetP sHG).
Qed.

End Primitive.

Section NactionDef.

Variables (gT : finGroupType) (sT : finType).

Variable to : {action gT &-> sT}.
Variable n :  nat.

Definition n_act (t : n.-tuple sT) a := [tuple of maps (to^~ a) t].

Lemma n_act_is_action : is_action n_act.
Proof.
by split=> [t|t a b]; apply: eq_from_tsub=> i; rewrite !tsub_maps ?act1 ?actM.
Qed.

Canonical Structure n_act_action := Action n_act_is_action.

End NactionDef.

Notation "to * n" := (n_act_action to n) : action_scope.

Section NTransitive.

Variables (gT : finGroupType) (sT : finType).
Variable n :  nat.
Variable A : {set gT}.
Variable to : {action gT &-> sT}.
Variable S : {set sT}.

Definition dtuple_on := [set t : n.-tuple sT | uniq t && (t \subset S)].
Definition ntransitive := [transitive (A | to * n) on dtuple_on].

Lemma dtuple_onP : forall t,
  reflect (injective (tsub t) /\ forall i, tsub t i \in S) (t \in dtuple_on).
Proof.
move=> t; rewrite inE subset_all -maps_tsub_enum.
case: (uniq _) / (injectiveP (tsub t)) => f_inj; last by right; case.
rewrite -[all _ _]negbK -has_predC has_maps has_predC negbK /=.
by apply: (iffP allP) => [Sf|[]//]; split=> // i; rewrite Sf ?mem_enum.
Qed.

Lemma n_act_dtuple : forall t a,
  a \in 'N_(|to)(S) -> t \in dtuple_on -> n_act to t a \in dtuple_on.
Proof.
move=> t a; move/astabsP=> toSa; case/dtuple_onP=> t_inj St; apply/dtuple_onP.
split=> [i j | i]; rewrite !tsub_maps ?[_ \in S]toSa //.
by move/act_inj; exact: t_inj.
Qed.

End NTransitive.

Implicit Arguments n_act [gT sT n].

Notation "n .-dtuple ( S )" := (dtuple_on n S)
  (at level 8, format "n .-dtuple ( S )") : set_scope.

Notation "[ 'transitive' * n ( A | to ) 'on' S ]" := (ntransitive n A to S)
  (at level 0, n at level 8,
   format "[ 'transitive'  *  n  ( A  |  to )  'on'  S ]") : form_scope.

Section NTransitveProp.

Variable (gT : finGroupType) (sT : finType).
Variable to : {action gT &-> sT}.
Variable G : {group gT}.
Variable S : {set sT}.

Lemma card_uniq_tuple n (t : n.-tuple sT) : uniq t -> #|t| = n.
Proof. move=> n t; move/card_uniqP->; exact: size_tuple. Qed.

Lemma n_act0 (t : 0.-tuple sT) a : n_act to t a = [tuple].
Proof. move=> *; exact: tuple0. Qed.

Lemma dtuple_on_add : forall n x (t : n.-tuple sT),
  ([tuple of x :: t] \in n.+1.-dtuple(S)) =
     [&& x \in S, x \notin t & t \in n.-dtuple(S)].
Proof. move=> *; rewrite !inE memtE !subset_all -!andbA; do !bool_congr. Qed.

Lemma dtuple_on_add_D1 : forall n x (t : n.-tuple sT),
  ([tuple of x :: t] \in n.+1.-dtuple(S))
     = (x \in S) && (t \in n.-dtuple(S :\ x)).
Proof.
move=> n x t; rewrite dtuple_on_add !inE (andbCA (~~ _)); do 2!congr (_ && _).
rewrite -!(eq_subset (in_set (mem t))) setD1E setIC subsetI; congr (_ && _).
by rewrite setC1E -setCS setCK sub1set !inE.
Qed.

Lemma dtuple_on_subset : forall n (S1 S2 : {set sT}) t,
  S1 \subset S2 -> t \in n.-dtuple(S1) -> t \in n.-dtuple(S2).
Proof.
move=> n S1 S2 t sS12; rewrite !inE; case/andP=> ->; move/subset_trans; exact.
Qed.

Lemma n_act_add n x (t : n.-tuple sT) a :
  n_act to [tuple of x :: t] a = [tuple of to x a :: n_act to t a].
Proof. by move=> *; exact: val_inj. Qed.

Lemma ntransitive0 : [transitive * 0 (G | to) on S].
Proof.
have dt0: [tuple] \in 0.-dtuple(S) by rewrite inE memtE subset_all.
apply/imsetP; exists [tuple of Seq0 sT] => //.
by apply/setP=> x; rewrite [x]tuple0 orbit_refl.
Qed.

Lemma ntransitive_weak : forall k m,
  k <= m -> [transitive * m (G | to) on S] -> [transitive * k (G | to) on S].
Proof.
move=> k m; move/subnK <-; rewrite addnC; elim: {m}(m - k) => // m IHm.
rewrite addSn => tr_m1; apply: IHm; move: {m k}(m + k) tr_m1 => m tr_m1.
have ext_t: forall t, t \in dtuple_on m S ->
  exists x, [tuple of x :: t] \in m.+1.-dtuple(S).
- move=> /= t dt; case sSt: (S \subset t); last first.
    case/subsetPn: sSt => x Sx ntx.
    by exists x; rewrite dtuple_on_add andbA /= Sx ntx.
  case/imsetP: tr_m1 dt => t1.
  rewrite !inE; case/andP=> Ut1 St1 _; case/andP=> Ut _.
  have:= subset_trans St1 sSt; move/subset_leq_card.
  by rewrite !card_uniq_tuple // ltnn.
case/imsetP: (tr_m1); case/tupleP=> x t; rewrite dtuple_on_add.
case/and3P=> Sx ntx dt; set xt := [tuple of _] => tr_xt.
apply/imsetP; exists t => //.
apply/setP=> u; apply/idP/imsetP=> [du | [a Ga ->{u}]].
  case: (ext_t u du) => y; rewrite tr_xt.
  by case/imsetP=> a Ga [_ def_u]; exists a => //; exact: val_inj.
have: n_act to xt a \in dtuple_on _ S by rewrite tr_xt mem_imset.
by rewrite n_act_add dtuple_on_add; case/and3P.
Qed.

Lemma ntransitive1 : forall m,
  0 < m -> [transitive * m (G | to) on S] -> [transitive (G | to) on S].
Proof.
have trdom1: forall x, ([tuple x] \in 1.-dtuple(S)) = (x \in S).
  by move=> x; rewrite dtuple_on_add !inE memtE subset_all andbT.
move=> m m_pos; move/(ntransitive_weak m_pos)=> {m m_pos}.
case/imsetP; case/tupleP=> x t0; rewrite {t0}(tuple0 t0) trdom1 => Sx trx.
apply/imsetP; exists x => //; apply/setP=> y; rewrite -trdom1 trx.
apply/imsetP/imsetP; case=> a Ga [->]; exists a => //; exact: val_inj.
Qed.

Lemma ntransitive_primitive : forall m,
  1 < m -> [transitive * m (G | to) on S] -> [primitive (G | to) on S].
Proof.
move=> m lt1m; move/(ntransitive_weak lt1m) => {m lt1m} Ht2.
apply/primitiveP; split=> [|f Hf1 Hf2].
  case/imsetP: Ht2; case/tupleP=> x t.
  by rewrite dtuple_on_add; case/andP; exists x.
case triv1: (forallb x, (x \in S) ==> (#|predI (mem S) (f x)| == 1%N)).
  left => x y Sx Sy Hf; apply/eqP; apply/idPn=> nxy.
  have:= forallP triv1 x; rewrite (cardD1 x) inE /= Sx Hf1 //=.
  by rewrite (cardD1 y) inE /= (eq_sym y) nxy inE /= Sy Hf.
case/existsP: triv1 => x; rewrite negb_imply; case/andP=> Sx.
rewrite (cardD1 x) inE /= Hf1 // Sx; case/pred0Pn => y /=.
case/and3P=> nxy Sy fxy; right=> x1 y1 Sx1 Sy1.
case: (x1 =P y1) => [-> //|]; [exact: Hf1 | move/eqP; rewrite eq_sym => nxy1].
pose t := [tuple y; x]; pose t1 := [tuple y1; x1].
have{Sx1 Sy1 nxy1} [dt dt1]: t \in 2.-dtuple(S) /\ t1 \in 2.-dtuple(S).
  rewrite !inE !memtE !subset_all /= !mem_seq1 !andbT; split; exact/and3P.
case: (atransP2 Ht2 dt dt1) => a Ga [->] ->.
have trGS: [transitive (G | to) on S] by exact: ntransitive1 Ht2.
by move/Hf2: fxy => -> //; rewrite Hf1 // -(atransP trGS _ Sy) mem_imset.
Qed.

Lemma trans_prim_astab : forall x,
  x \in S -> [transitive (G | to) on S] ->
    [primitive (G | to) on S] = maximal_eq 'C_(G | to)[x] G.
Proof.
move=> x Sx Ht; apply/(primitivePt Ht)/maximal_eqP=> [Hp | [Hs Hst Y Hsub Hd]].
  split=> [|H Hk1 Hk2]; first exact: subsetIl.
  pose Y := orbit to H x; have Yx: x \in Y by exact: orbit_refl.
  case/(_ Y): Hp.
  - rewrite -(acts_orbit _ (trans_acts Ht)) in Sx.
    apply: subset_trans Sx; exact: imsetS.
  - move=> g1 g2 y /= Gg1 Gg2 Yyg1 Yyg2 z; apply: orbit_transr.
    rewrite -{1}(actK to g2 z) -actM mem_imset {z}//.
    case/imsetP: Yyg1 => h1 Hh1 yg1_xh1; case/imsetP: Yyg2 => h2 Hh2 yg2_xh2.
    rewrite -(groupMl _ Hh2) -[_ * _](mulgKV h1) groupMr //.
    apply: (subsetP Hk1); apply/setIP; split.
      by rewrite !(groupM, groupV) // (subsetP Hk2).
    by apply/astab1P; rewrite !actM -yg2_xh2 actK yg1_xh1 actK.
  - move=> Y1; left; apply/eqP; rewrite eqset_sub Hk1 subsetI Hk2 /= andbT.
    apply/subsetP=> a Ha; apply/astab1P.
    apply/set1P; rewrite (([set x] =P Y) _) ?mem_imset //.
    by rewrite eqset_sub_card sub1set Yx cards1.
  move=> YS; right; apply/eqP; rewrite eqset_sub Hk2; apply/subsetP => a Ga.
  have: to x a \in Y by rewrite YS -(atransP Ht _ Sx) mem_imset.
  case/imsetP=> b Hb xab; rewrite -(mulgKV b a) groupMr // (subsetP Hk1) //.
  rewrite inE groupMl // groupV (subsetP Hk2) //; apply/astab1P.
  by rewrite actM xab actK.
case: leqP => lt1Y; [by left | right]; apply/eqP; rewrite eqset_sub Hsub /=.
case: (pickP (mem Y)) lt1Y => [y /= Yy | Y0]; last by rewrite eq_card0.
have{Hd} defN: 'N_(G | to)(Y) = G :&: [set a | to y a \in Y].
  apply/setP=> a; rewrite !in_setI inE; case Ga: (a \in G) => //=.
  apply/astabsP/idP=> [-> // | Yya z].
  by rewrite (Hd a 1 y) ?act1 /=.
rewrite (cardD1 y) Yy ltnS lt0n; case/existsP=> z; case/andP=> nny /= Yz.
have:= subsetP Hsub _ Yy; rewrite -(atransP Ht x Sx); case/imsetP=> a Ga y_xa.
case: (Hst ('N_(G | to)(Y) :^ a^-1)%G) => /=.
- apply/subsetP=> b; case/setIP=> Gb; move/astab1P=> xb_x.
  by rewrite mem_conjgV defN !inE groupJ // y_xa -actCJ xb_x -y_xa.
- by rewrite conjIg conjGid (groupV, subsetIl).
- have:= subsetP Hsub z Yz; rewrite -(atransP Ht _  (subsetP Hsub y Yy)).
  case/imsetP=> b Gb z_yb Cx_NY; case/eqP: nny; rewrite z_yb y_xa actCJV.
  have: b \in 'N_(G | to)(Y) by rewrite defN !inE Gb -z_yb /=.
  by rewrite -(memJ_conjg _ a^-1) Cx_NY inE groupJ ?groupV //; move/astab1P->.
move=> NY_G; apply/subsetP=> t; case/imsetP=> b.
rewrite -{1}(mulgKV a b) groupMr // -NY_G defN mem_conjgV conjgE mulgKV.
by rewrite !inE actM y_xa actK; case/andP=> _ ? ->.
Qed.

End NTransitveProp.

Section NTransitveProp1.

Variable (gT : finGroupType) (sT : finType).

Variable to : {action gT &-> sT}.
Variable G : {group gT}.
Variable S : {set sT}.

(* Corresponds to => of 15.12.1 Aschbacher *)
Theorem stab_ntransitive : forall m x,
     0 < m -> x \in S ->  [transitive * m.+1 (G | to) on S]
  -> [transitive * m ('C_(G | to)[x] | to) on S :\ x].
Proof.
move=> m x m_pos Sx Gtr.
have sSxS: S :\ x \subset S by rewrite setD1E subsetIl.
case: (imsetP Gtr); case/tupleP=> x1 t1; rewrite dtuple_on_add.
case/and3P=> Sx1 nt1x1 dt1 trt1; have Gtr1 := ntransitive1 (ltn0Sn _) Gtr.
case: (atransP2 Gtr1 Sx1 Sx) => // a Ga x1ax.
pose t := n_act to t1 a.
have dxt: [tuple of x :: t] \in m.+1.-dtuple(S).
  rewrite trt1 x1ax; apply/imsetP; exists a => //; exact: val_inj.
apply/imsetP; exists t.
  by rewrite dtuple_on_add_D1 Sx in dxt. 
apply/setP=> t2; apply/idP/imsetP => [dt2|[b]].
  have: [tuple of x :: t2] \in dtuple_on _ S by rewrite dtuple_on_add_D1 Sx.
  case/(atransP2 Gtr dxt)=> b Gb [xbx tbt2].
  exists b; [rewrite inE Gb; exact/astab1P | exact: val_inj].
case/setIP=> Gb; move/astab1P=> xbx ->{t2}.
rewrite n_act_dtuple //; last by rewrite dtuple_on_add_D1 Sx in dxt.
apply/astabsP=> y; rewrite !inE -{1}xbx (inj_eq (act_inj _ _)).
by rewrite (actsP (trans_acts Gtr1)).
Qed.

(* Correspond to <= of 15.12.1 Aschbacher *)
Theorem stab_ntransitiveI : forall m x,
     x \in S ->  [transitive (G | to) on S]
  -> [transitive * m ('C_(G | to)[x] | to) on S :\ x]
  -> [transitive * m.+1 (G | to) on S].
Proof.
move=> m x Sx Gtr Gntr.
have t_to_x: forall t, t \in m.+1.-dtuple(S) ->
  exists2 a, a \in G & exists2 t', t' \in m.-dtuple(S :\ x)
                                 & t = n_act to [tuple of x :: t'] a.
- case/tupleP=> y t St.
  have Sy: y \in S by rewrite dtuple_on_add_D1 in St; case/andP: St.
  rewrite -(atransP Gtr _ Sy) in Sx; case/imsetP: Sx => a Ga toya.
  exists a^-1; first exact: groupVr.
  exists (n_act to t a); last by rewrite n_act_add toya !actK.
  move/(n_act_dtuple (subsetP (trans_acts Gtr) a Ga)): St.
  by rewrite n_act_add -toya dtuple_on_add_D1; case/andP.
case: (imsetP Gntr) => t dt S_tG; pose xt := [tuple of x :: t].
have dxt: xt \in m.+1.-dtuple(S) by rewrite dtuple_on_add_D1 Sx.
apply/imsetP; exists xt => //; apply/setP=> t2.
symmetry; apply/imsetP/idP=> [[a Ga ->] | ].
  by apply: n_act_dtuple; rewrite // (subsetP (trans_acts Gtr)).
case/t_to_x=> a2 Ga2 [t2']; rewrite S_tG.
case/imsetP=> a; case/setIP=> Ga; move/astab1P=> toxa -> -> {t2 t2'}.
by exists (a * a2); rewrite (groupM, actM) //= !n_act_add toxa.
Qed.

End NTransitveProp1.
