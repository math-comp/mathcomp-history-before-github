(***********************************************************************)
(* (c) Copyright Microsoft Corporation and Inria. All rights reserved. *)
(*                                                                     *)
(***********************************************************************)
Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq paths fintype.
Require Import tuple bigops finset groups perm action prim_act.
Require Import morphisms normal cyclic.

(* Require Import paths finfun connect div zp. *)

Import Prenex Implicits.
Set Implicit Arguments.
Unset Strict Implicit.

Import GroupScope.

Definition bool_groupMixin := FinGroup.Mixin addbA addFb addbb.
Canonical Structure bool_baseGroup :=
  Eval hnf in BaseFinGroupType bool_groupMixin.
Canonical Structure boolGroup := Eval hnf in FinGroupType addbb. 

Section PermutationParity.

Variable T : finType.

Implicit Type s : {perm T}.
Implicit Types x y z : T.

Definition pcycle s := orbit 'P%act <[s]>.
Definition pcycles s := pcycle s @: T.
Definition odd_perm (s : perm_type T) := odd #|T| (+) odd #|pcycles s|.
Definition even_perm s := ~~ odd_perm s.

Lemma pcycleE : forall s, pcycle s = orbit 'P%act <[s]>. Proof. by []. Qed.

Lemma pcycle_traject : forall s x, pcycle s x =i traject s x #[s].
Proof.
move=> s x y; apply/orbitP/trajectP=> [[sn] | [k _ <-]].
  by case/cyclePmin=> k lt_k_s <- <-; exists k; rewrite //= -permX.
by exists (s ^+ k); rewrite ?mem_cycle //= -permX.
Qed.

Definition dpair := [pred t | t.1 != t.2 :> T].

Lemma prod_tpermP : forall s : {perm T},
  {ts : seq (T * T) | s = \prod_(t <- ts) tperm t.1 t.2 & all dpair ts}.
Proof.
move=> s; elim: {s}_.+1 {-2}s (ltnSn #|[pred x | s x != x]|) => // n IHn s.
rewrite ltnS => le_s_n; case: (pickP (fun x => s x != x)) => [x s_x | s_id].
  have [|ts def_s ne_ts] := IHn (tperm x (s^-1 x) * s).
    rewrite (cardD1 x) !inE s_x in le_s_n; apply: leq_ltn_trans le_s_n.
    apply: subset_leq_card; apply/subsetP=> y.
    rewrite !inE permM permE /= -(canF_eq (permK _)).
    case: (y =P x) => [->|]; first by rewrite permKV eqxx.
    by move/eqP=> ne_yx; case: (_ =P x) => // -> _; rewrite eq_sym.
  exists ((x, s^-1 x) :: ts); last by rewrite /= -(canF_eq (permK _)) s_x.
  by rewrite big_cons -def_s mulgA tperm2 mul1g.
exists (Nil (T * T)); rewrite // big_nil; apply/permP=> x.
by apply/eqP; apply/idPn; rewrite perm1 s_id.
Qed.

Lemma ncycles_mul_tperm : forall s x y (t := tperm x y),
  #|pcycles (t * s)| + (x \notin pcycle s y).*2 = #|pcycles s| + (x != y).
Proof.
pose xf s x y := find (pred2 x y) (traject s (s x) #[s]).
have xf_size : forall s x y, xf s x y <= #[s].
  by move=> s x y; rewrite (leq_trans (find_size _ _)) ?size_traject.
have lt_xf: forall s x y n, n < xf s x y -> ~~ pred2 x y ((s ^+ n.+1) x).
  move=> s x y n lt_n; move/negbT: (before_find (s x) lt_n).
  by rewrite permX iterSr nth_traject // (leq_trans lt_n).
pose t x y s := tperm x y * s.
have tC: forall x y s, t x y s = t y x s by move=> x y s; rewrite /t tpermC.
have tK : forall x y, involutive (t x y) by move=> x y s; exact: tpermKg.
have tXC: forall s x y n, n <= xf s x y -> (t x y s ^+ n.+1) y = (s ^+ n.+1) x.
  move=> s x y; elim=> [|n IHn] lt_n_f; first by rewrite permM tpermR.
  rewrite !(expgSr _ n.+1) !permM {}IHn 1?ltnW //; congr (s _).
  by move/lt_xf: lt_n_f; case/norP=> *; rewrite tpermD // eq_sym.
have eq_xf: forall s x y, pred2 x y ((s ^+ (xf s x y).+1) x).
  move=> s x y; simpl in s, x, y.
  have has_f: has (pred2 x y) (traject s (s x) #[s]).
    apply/hasP; exists x; rewrite /= ?eqxx // -pcycle_traject.
    by apply/orbitP; exists s^-1; rewrite ?[_ s^-1]permK // groupV cycle_id.
  have:= nth_find (s x) has_f; rewrite has_find size_traject in has_f.
  by rewrite nth_traject // -iterSr -permX.
have xfC: forall s x y, xf (t x y s) y x = xf s x y.
  move=> s x y; wlog ltx: s x y / xf (t x y s) y x < xf s x y.
    move=> IWxy; set m := xf _ y x; set n := xf s x y.
    by case: (ltngtP m n) => // ltx; [exact: IWxy | rewrite /m -IWxy tC tK].
  by move/lt_xf: (ltx); rewrite -(tXC s x y) 1?ltnW //= orbC [_ || _]eq_xf.
move=> /= s x y; pose ts := t x y s; rewrite -[_ * s]/ts.
pose dp s' := #|pcycles s' :\ pcycle s' y :\ pcycle s' x|.
rewrite !(addnC #|_|) (cardsD1 (pcycle ts y)) mem_imset ?inE //.
rewrite (cardsD1 (pcycle ts x)) inE mem_imset ?inE //= -/(dp ts).
rewrite (cardsD1 (pcycle s y)) (cardsD1 (pcycle s x)) !(mem_imset, inE) //.
rewrite -/(dp s) !addnA !orbit_eq_mem -!pcycleE andbT; congr (_ + _).
  rewrite {dp}/ts; case: eqP => [<- | ne_xy].
    by rewrite /t tperm1 mul1g orbit_refl.
  suff ->: (x \in pcycle (t x y s) y) = (x \notin pcycle s y).
    by case: (x \in _).
  wlog xf_x: s x y ne_xy / (s ^+ (xf s x y).+1) x = x.
    move=> IWs; have:= eq_xf s x y; set n := xf s x y.
    case/pred2P=> [|snx]; first exact: IWs.
    rewrite -[x \in _]negbK ![x \in _]orbit_sym -!pcycleE.
    by rewrite -{}IWs; [rewrite tC tK | move/esym | rewrite xfC tXC].
  rewrite -{1}xf_x -(tXC _ _ _ _ (leqnn _)) (orbit_to 'P) ?mem_cycle //.
  rewrite orbit_sym; symmetry; apply/orbitP=> [[sn]]; case/cycleP=> n <-{sn}.
  rewrite [_ x _]permX => snx.
  have: looping s x (xf s x y).+1.
    by rewrite permX in xf_x; apply/trajectP; exists 0.
  move/loopingP; move/(_ n); rewrite {n}snx.
  case/trajectP=> [[//|i]]; rewrite ltnS -permX => lt_i def_y.
  by move/lt_xf: lt_i; rewrite def_y /= eqxx orbT.
rewrite {}/ts; wlog: s / dp (t x y s) < dp s.
  move=> IWs; case: (ltngtP (dp (t x y s)) (dp s)); [exact: IWs | | by []].
  by move=> lt_s_ts; rewrite -IWs tK.
rewrite ltnNge; case/negP; apply: subset_leq_card; apply/subsetP=> {dp} C.
rewrite !inE andbA andbC !(eq_sym C); case/and3P; case/imsetP=> z _ ->{C}.
rewrite 2!orbit_eq_mem -pcycleE => sxz syz.
suff ts_z: pcycle (t x y s) z = pcycle s z.
  by rewrite -ts_z !orbit_eq_mem -pcycleE {1 2}ts_z sxz syz mem_imset ?inE.
suff exp_id: forall n, ((t x y s) ^+ n) z = (s ^+ n) z.
  apply/setP=> u; apply/idP/idP; case/orbitP=> v; case/cycleP=> n <- <-{u v}.
    by rewrite [_ z _]exp_id (orbit_to 'P) ?mem_cycle.
  by rewrite -[_ z _]exp_id (orbit_to 'P) ?mem_cycle.
elim=> // n IHn; rewrite !expgSr !permM {}IHn.
by rewrite /t tpermD //; apply/eqP=> xy_z; [case/negP: sxz | case/negP: syz];
   rewrite xy_z (orbit_to 'P) ?mem_cycle.
Qed.

Lemma odd_perm1 : odd_perm 1 = false.
Proof.
rewrite /odd_perm card_imset ?addbb // => x y; move/eqP.
by rewrite orbit_eq_mem /= cycle1; case/orbitP=> ?; move/set1P->; rewrite act1.
Qed.

Lemma odd_mul_tperm : forall x y s,
  odd_perm (tperm x y * s) = (x != y) (+) odd_perm s.
Proof.
move=> x y s; rewrite addbC -addbA -[~~ _]oddb -odd_add -ncycles_mul_tperm.
by rewrite odd_add odd_double addbF.
Qed.

Lemma odd_tperm : forall x y, odd_perm (tperm x y) = (x != y).
Proof. by move=> x y; rewrite -[_ y]mulg1 odd_mul_tperm odd_perm1 addbF. Qed.

Lemma odd_perm_prod : forall ts,
  all dpair ts -> odd_perm (\prod_(t <- ts) tperm t.1 t.2) = odd (size ts).
Proof.
elim=> [_|t ts IHts] /=; first by rewrite big_nil odd_perm1.
by case/andP=> dt12 dts; rewrite big_cons odd_mul_tperm dt12 IHts.
Qed.

Lemma odd_permM : {morph odd_perm : s1 s2 / s1 * s2 >-> s1 (+) s2}.
Proof.
move=> s1 s2; case: (prod_tpermP s1) => ts1 ->{s1} dts1.
case: (prod_tpermP s2) => ts2 ->{s2} dts2.
by rewrite -big_cat !odd_perm_prod ?all_cat ?dts1 // size_cat odd_add.
Qed.

Lemma odd_permV : forall s, odd_perm s^-1 = odd_perm s.
Proof. by move=> s; rewrite -{2}(mulgK s s) !odd_permM -addbA addKb. Qed.

Lemma odd_permJ : forall s1 s2, odd_perm (s1 ^ s2) = odd_perm s1.
Proof. by move=> s1 s2; rewrite !odd_permM odd_permV addbC addbK. Qed.

(** Definitions of the alternate groups and some Properties **)
Definition Sym of phant T : {set {perm T}} := setT.

Canonical Structure Sym_group phT := Eval hnf in [group of Sym phT].

Notation Local "'Sym_T" := (Sym (Phant T)) (at level 0).

Canonical Structure sign_morph := @Morphism _ _ 'Sym_T _ (in2W odd_permM).

Definition Alt of phant T := 'ker odd_perm.

Canonical Structure Alt_group phT := Eval hnf in [group of Alt phT].

Notation Local "'Alt_T" := (Alt (Phant T)) (at level 0).

Lemma Alt_even : forall p, (p \in 'Alt_T) = even_perm p.
Proof. by move=> p; rewrite !inE /even_perm /=; case: odd_perm. Qed.

Lemma Alt_subset : 'Alt_T \subset 'Sym_T.
Proof. exact: subsetT. Qed.

Lemma Alt_normal : 'Alt_T <| 'Sym_T.
Proof. exact: ker_normal. Qed.

Lemma Alt_norm : 'Sym_T \subset 'N('Alt_T).
Proof. by case/andP: Alt_normal. Qed.

Let n := #|T|.

Lemma Alt_index : 1 < n -> #|'Sym_T : 'Alt_T| = 2.
Proof.
move=> lt1n; rewrite -card_quotient ?Alt_norm //=.
have : ('Sym_T / 'Alt_T) \isog (odd_perm @* 'Sym_T) by apply: first_isog.
case/isogP=> g; move/injmP; move/card_in_imset <-.
rewrite /morphim setIid=> ->; rewrite -card_bool; apply: eq_card => b.
apply/imsetP; case: b => /=; last first.
 by exists (1 : {perm T}); [rewrite setIid inE | rewrite odd_perm1].
case: (pickP T) lt1n => [x1 _ | d0]; last by rewrite /n eq_card0.
rewrite /n (cardD1 x1) ltnS lt0n; case/existsP=> x2 /=.
by rewrite eq_sym andbT -odd_tperm; exists (tperm x1 x2); rewrite ?inE.
Qed.

Lemma card_Sym : #|'Sym_T| = fact n.
Proof.
rewrite -[n]cardsE -card_perm; apply: eq_card => p.
by apply/idP/subsetP=> [? ?|]; rewrite !inE.
Qed.

Lemma card_Alt : 1 < n -> (2 * #|'Alt_T|)%N = fact n.
Proof.
by move/Alt_index <-; rewrite mulnC (LaGrange Alt_subset) card_Sym.
Qed.

Lemma Sym_trans : [transitive * n ('Sym_T | 'P) on setT].
Proof.
apply/imsetP; pose t1 := [tuple of enum T].
have dt1: t1 \in n.-dtuple(setT) by rewrite inE enum_uniq; apply/subsetP.
exists t1 => //; apply/setP=> t; apply/idP/imsetP=> [|[a _ ->{t}]]; last first.
  by apply: n_act_dtuple => //; apply/astabsP=> x; rewrite !inE.
case/dtuple_onP=> injt _; have injf := inj_comp injt (@enum_rank_inj _).
exists (perm injf); first by rewrite inE.
apply: eq_from_tnth => i; rewrite tnth_map /= [aperm _ _]permE; congr tnth.
by rewrite (tnth_nth (enum_default i)) enum_valK.
Qed.

Lemma Alt_trans : [transitive * n.-2 ('Alt_T | 'P) on setT].
Proof.
case n_m2: n Sym_trans => [|[|m]] /= tr_m2; try exact: ntransitive0.
have tr_m := ntransitive_weak (leqW (leqnSn m)) tr_m2.
case/imsetP: tr_m2; case/tupleP=> x; case/tupleP=> y t.
rewrite !dtuple_on_add 2!inE [x \in _]inE negb_or /= -!andbA.
case/and4P=> nxy ntx nty dt _; apply/imsetP; exists t => //; apply/setP=> u.
apply/idP/imsetP=> [|[a _ ->{u}]]; last first.
  by apply: n_act_dtuple => //; apply/astabsP=> z; rewrite !inE.
case/(atransP2 tr_m dt)=> /= a _ ->{u}.
case odd_a: (odd_perm a); last by exists a => //; rewrite !inE /= odd_a.
exists (tperm x y * a); first by rewrite !inE /= odd_permM odd_tperm nxy odd_a.
apply: val_inj; apply: eq_in_map => z tz; rewrite actM /= /aperm; congr (a _).
by case: tpermP ntx nty => // <-; rewrite tz.
Qed.

Lemma aperm_faithful : forall A : {group {perm T}},
  [faithful (A | 'P) on setT].
Proof.
move=> A; apply/faithfulP=> /= p _ np1; apply/eqP; apply/perm_act1P=> y.
by rewrite np1 ?inE.
Qed.

End PermutationParity.

Notation "''Sym_' T" := (Sym (Phant T))
  (at level 8, T at level 2, format "''Sym_' T") : group_scope.
Notation "''Sym_' T" := (Sym_group (Phant T)) : subgroup_scope.

Notation "''Alt_' T" := (Alt (Phant T))
  (at level 8, T at level 2, format "''Alt_' T") : group_scope.
Notation "''Alt_' T" := (Alt_group (Phant T)) : subgroup_scope.

Coercion odd_perm : perm_type >-> bool.
