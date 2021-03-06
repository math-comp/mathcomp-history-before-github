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

Definition imprimitivity_system Q :=
  [&& partition Q S, [acts (A | to^*) on Q] & 1 < #|Q| < #|S|].

Definition primitive :=
  [transitive (A | to) on S] && ~~ existsb Q, imprimitivity_system Q.

End PrimitiveDef.

Notation "[ 'primitive' ( A | to ) 'on' S ]" := (primitive A to S)
  (at level 0, format "[ 'primitive'  (  A  |  to  )  'on'  S ]") : form_scope.

Prenex Implicits imprimitivity_system.

Section Primitive.

Variables (aT : finGroupType) (sT : finType).
Variables (G : {group aT}) (to : {action aT &-> sT}) (S : {set sT}).

Lemma trans_prim_astab : forall x,
  x \in S -> [transitive (G | to) on S] ->
    [primitive (G | to) on S] = maximal_eq 'C_(G | to)[x] G.
Proof.
move=> x Sx trG; rewrite /primitive trG negb_exists.
apply/forallP/maximal_eqP=> /= [primG | [_ maxCx] Q].
  split=> [|H sCH sHG]; first exact: subsetIl.
  pose X := orbit to H x; pose Q := orbit (to^*)%act G X.
  have Xx: x \in X by exact: orbit_refl.
  have defH: 'N_(G | to)(X) = H.
    have trH: [transitive (H | to) on X] by apply/imsetP; exists x.
    have sHN: H \subset 'N_(G | to)(X) by rewrite subsetI sHG trans_acts.
    move/(subgroup_transitiveP Xx sHN): (trH) => /= <-.
      by rewrite mulSGid //= setIAC subIset ?sCH.
    apply/imsetP; exists x => //; apply/eqP.
    by rewrite eqEsubset imsetS // acts_orbit ?subsetIr.
  move: (sCH); rewrite subEproper; case/predU1P; first by left.
  move/proper_card=> oCH; right; apply/eqP; rewrite eqEcard sHG leqNgt.
  apply: contra {primG}(primG Q) => oHG; apply/and3P; split; last first.
  - rewrite card_orbit astab1_set defH -(@ltn_pmul2l #|H|) ?LaGrange // muln1.
    rewrite oHG -(@ltn_pmul2l #|H|) ?LaGrange // -(card_orbit_stab to G x).
    by rewrite -(atransP trG x Sx) mulnC card_orbit ltn_pmul2r.
  - by apply/actsP=> a Ga Y; apply: orbit_transr; exact: orbit_to.
  apply/and3P; split; last 1 first.
  - rewrite orbit_sym; apply/imsetP=> [[a _]] /= defX.
    by rewrite defX /set_act imset0 inE in Xx.
  - apply/eqP; apply/setP=> y; apply/bigcupP/idP=> [[Xa] | Sy].
      case/imsetP=> a Ga ->{Xa}; case/imsetP=> z; case/imsetP=> b Hb -> ->.
      by rewrite !(actsP (trans_acts trG)) //; exact: subsetP Hb.
    case: (atransP2 trG Sx Sy) => a Ga ->.
    by exists ((to^*)%act X a); apply: mem_imset; rewrite // orbit_refl.
  apply/trivIsetP=> Y Z; case/imsetP=> a Ga ->; case/imsetP=> b Gb ->{Y Z}.
  case dab: [disjoint _ & _]; [by right | left].
  apply: (canRL (actKV _ _)); rewrite -actM; apply/astab1P.
  rewrite astab1_set (subsetP (subsetIr G _)) //= defH.
  case/existsP: dab => y; case/andP.
  case/imsetP=> z; case/imsetP=> a1 Ha1 -> ->{y z}.
  case/imsetP=> t; case/imsetP=> b1 Hb1 ->{t}.
  do 2!move/(canLR (actK _ _)); rewrite -!actM; move/astab1P => Cab.
  rewrite -(groupMr _ (groupVr Hb1)) -mulgA -(groupMl _ Ha1).
  by rewrite (subsetP sCH) // inE Cab !groupM ?groupV // (subsetP sHG).
apply/and3P=> [[]]; case/and3P; set sto := (to^*)%act.
move/eqP=> defS tIQ ntQ actQ; rewrite !ltnNge -negb_or; case/orP.
pose X := cover_at x Q; have Xx: x \in X by rewrite mem_cover_at defS.
have QX: X \in Q by rewrite cover_at_mem ?defS.
have toX: forall Y a, Y \in Q -> a \in G -> to x a \in Y -> sto X a = Y.
  move=> Y a QY Ga Yxa; case: (trivIsetP tIQ Y (sto X a)) => //.
    by rewrite (actsP actQ).
  by case/existsP; exists (to x a); rewrite /= Yxa; exact: mem_imset.
have defQ: Q = orbit (to^*)%act G X.
  apply/eqP; rewrite eqEsubset andbC acts_orbit // QX.
  apply/subsetP=> Y QY; have:= sub0set Y; rewrite subEproper.
  case/predU1P=> [Y0|]; first by rewrite Y0 QY in ntQ.
  case/andP=> _; case/subsetPn=> y Yy _.
  have Sy: y \in S by rewrite -defS; apply/bigcupP; exists Y.
  have [a Ga def_y] := atransP2 trG Sx Sy.
  by apply/imsetP; exists a; rewrite // (toX Y) // -def_y.
rewrite defQ card_orbit; case: (maxCx 'C_(G | sto)[X]%G) => /= [||->|->].
- apply/subsetP=> a; case/setIP=> Ga cxa; rewrite inE Ga /=.
  by apply/astab1P; rewrite (toX X) // (astab1P cxa).
- exact: subsetIl.
- by right; rewrite -card_orbit (atransP trG).
by left; rewrite indexgg.
Qed.

Lemma prim_trans_norm : forall H : {group aT},
  [primitive (G | to) on S] -> H <| G ->
     H \subset 'C_(G | to)(S) \/ [transitive (H | to) on S].
Proof.
move=> H primG; case/andP=> sHG nHG; rewrite subsetI sHG.
have [trG _] := andP primG; have [x Sx defS] := imsetP trG.
move: primG; rewrite (trans_prim_astab Sx) //; case/maximal_eqP=> _.
case/(_ ('C_(G | to)[x] <*> H)%G) => /= [||cxH|]; first exact: mulgen_subl.
- by rewrite mulgen_subG subsetIl.
- have{cxH} cxH: H \subset 'C_(G | to)[x] by rewrite -cxH mulgen_subr.
  rewrite subsetI sHG /= in cxH; left; apply/subsetP=> a Ha.
  apply/astabP=> y Sy; have [b Gb ->] := atransP2 trG Sx Sy.
  rewrite actCJV [to x (a ^ _)](astab1P _) ?(subsetP cxH) //.
  by rewrite -mem_conjg (normsP nHG).
rewrite norm_mulgenEl ?subIset ?nHG //.
by move/(subgroup_transitiveP Sx sHG trG); right.
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
rewrite -!(eq_subset (in_set (mem t))) setDE setIC subsetI; congr (_ && _).
by rewrite -setCS setCK sub1set !inE.
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
move=> m lt1m; move/(ntransitive_weak lt1m) => {m lt1m} tr2G.
have trG: [transitive (G | to) on S] by exact: ntransitive1 tr2G.
have [x Sx _]:= imsetP trG; rewrite (trans_prim_astab Sx trG).
apply/maximal_eqP; split=> [|H]; first exact: subsetIl; rewrite subEproper.
case/predU1P; first by [left]; case/andP=> sCH; case/subsetPn=> a Ha nCa sHG.
right; rewrite -(subgroup_transitiveP Sx sHG trG _) ?mulSGid //.
have actH := subset_trans sHG (trans_acts trG).
pose y := to x a; have Sy: y \in S by rewrite (actsP actH).
have{nCa} yx: y != x by rewrite inE (sameP astab1P eqP) (subsetP sHG) in nCa.
apply/imsetP; exists y => //; apply/eqP.
rewrite eqEsubset acts_orbit // Sy andbT; apply/subsetP=> z Sz.
case: (z =P x) => [->|]; last move/eqP=> zx.
  by rewrite orbit_sym orbit_to.
pose ty := [tuple y; x]; pose tz := [tuple z; x].
have [Sty Stz]: ty \in 2.-dtuple(S) /\ tz \in 2.-dtuple(S).
  rewrite !inE !memtE !subset_all /= !mem_seq1 !andbT; split; exact/and3P.
case: (atransP2 tr2G Sty Stz) => b Gb [->]; move/esym; move/astab1P=> cxb.
by rewrite orbit_to // (subsetP sCH) // inE Gb.
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
move=> m x m_pos Sx Gtr; have sSxS: S :\ x \subset S by rewrite subsetDl.
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
