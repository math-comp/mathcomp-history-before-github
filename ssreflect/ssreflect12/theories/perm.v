(* (c) Copyright Microsoft Corporation and Inria. You may distribute   *)
(* under the terms of either the CeCILL-B License or the CeCILL        *)
(* version 2 License, as specified in the README file.                 *)
Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq paths choice fintype.
Require Import finfun bigops finset groups.

(**************************************************************************)
(* This file contains the definition and properties  associated to the    *)
(* group of permutations.                                                 *)
(*   {perm T} == the permutation of a finite type T                       *)
(*                        (i.e. an injective function from T to T)        *)
(*   'S_n == the permutations of {0,.., n-1}                              *)
(*   perm_on A u <=> u is a permutation on T where only the elements of a *)
(*                                 a subset A of T are affected           *)
(*   tperm x y == the transposition of x, y                               *)
(*   aperm x s == s(x)                                                    *)
(*   pcycle s x == the set of all elements that are in the same cycle     *) 
(*                 of permutation s as x                                  *)
(*   pcycles s == the set of cycles of permutation s                      *)
(*   odd_perm s <=> s is an odd permutation                               *)
(*   dpair x <=> x is a pair of distinct objects                          *)
(* Permutations are coerced to the underlying function.                   *)
(* Canonical structures are defined allowing permutations to be an eqType,*)
(* choiceType, countType, finType, subType, finGroupType (permutations    *)
(* with the composition form a group, therefore all generic group         *)
(* notations are inherited: 1 == identity permutation, * == composition,  *)
(* ^-1 == inverse permutation).                                           *)
(* Lemmas are given to establish the common properties for permutations.  *)
(**************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Import GroupScope.

Section PermDefSection.

Variable T : finType.

Inductive perm_type : predArgType :=
  Perm (pval : {ffun T -> T}) & injectiveb pval.
Definition pval p := let: Perm f _ := p in f.
Definition perm_of of phant T := perm_type.
Identity Coercion type_of_perm : perm_of >-> perm_type.

Notation pT := (perm_of (Phant T)).

Canonical Structure perm_subType :=
  Eval hnf in [subType for pval by perm_type_rect].
Definition perm_eqMixin := Eval hnf in [eqMixin of perm_type by <:].
Canonical Structure perm_eqType := Eval hnf in EqType perm_eqMixin.
Definition perm_choiceMixin := [choiceMixin of perm_type by <:].
Canonical Structure perm_choiceType := Eval hnf in ChoiceType perm_choiceMixin.
Definition perm_countMixin := [countMixin of perm_type by <:].
Canonical Structure perm_countType := Eval hnf in CountType perm_countMixin.
Canonical Structure perm_subCountType :=
  Eval hnf in [subCountType of perm_type].
Definition perm_finMixin := [finMixin of perm_type by <:].
Canonical Structure perm_finType := Eval hnf in FinType perm_finMixin.
Canonical Structure perm_subFinType := Eval hnf in [subFinType of perm_type].

Canonical Structure perm_for_subType := Eval hnf in [subType of pT].
Canonical Structure perm_for_eqType := Eval hnf in [eqType of pT].
Canonical Structure perm_for_choiceType := Eval hnf in [choiceType of pT].
Canonical Structure perm_for_countType := Eval hnf in [countType of pT].
Canonical Structure perm_for_subCountType := Eval hnf in [subCountType of pT].
Canonical Structure perm_for_finType := Eval hnf in [finType of pT].
Canonical Structure perm_for_subFinType := Eval hnf in [subFinType of pT].

Lemma perm_proof : forall f : T -> T, injective f -> injectiveb (finfun f).
Proof.
by move=> f f_inj; apply/injectiveP; apply: eq_inj f_inj _ => x; rewrite ffunE.
Qed.

End PermDefSection.

Notation "{ 'perm' T }" := (perm_of (Phant T))
  (at level 0, format "{ 'perm'  T }") : type_scope.

Arguments Scope pval [_ group_scope].

Bind Scope group_scope with perm_type.
Bind Scope group_scope with perm_of.

Notation "''S_' n" := {perm 'I_n}
  (at level 8, n at level 2, format "''S_' n").

Notation Local fun_of_perm_def := (fun T (u : perm_type T) => val u : T -> T).
Notation Local perm_def := (fun T f injf => Perm (@perm_proof T f injf)).

Module Type PermDefSig.
Parameter fun_of_perm : forall T, perm_type T -> T -> T.
Coercion fun_of_perm : perm_type >-> Funclass.
Parameter perm : forall (T : finType) (f : T -> T), injective f -> {perm T}.
Axiom fun_of_permE : fun_of_perm = fun_of_perm_def.
Axiom permE : perm = perm_def.
End PermDefSig.
Module PermDef : PermDefSig.
Definition fun_of_perm := fun_of_perm_def.
Definition perm := perm_def.
Lemma fun_of_permE : fun_of_perm = fun_of_perm_def. Proof. by []. Qed.
Lemma permE : perm = perm_def. Proof. by []. Qed.
End PermDef.

Notation fun_of_perm := PermDef.fun_of_perm.
Notation "@ 'perm'" := (@PermDef.perm) (at level 10, format "@ 'perm'").
Notation perm := (@PermDef.perm _ _).
Canonical Structure fun_of_perm_unlock := Unlockable PermDef.fun_of_permE.
Canonical Structure perm_unlock := Unlockable PermDef.permE.

Section Theory.

Variable T : finType.

Notation pT := {perm T}.

Lemma permP : forall u v : pT, u =1 v <-> u = v.
Proof.
move=> u v; split=> [| -> //]; rewrite unlock => eq_uv.
by apply: val_inj; apply/ffunP.
Qed.

Lemma pvalE : forall u : pT, pval u = u :> (T -> T).
Proof. by rewrite [@fun_of_perm _]unlock. Qed.

Lemma permE : forall f f_inj, @perm T f f_inj =1 f.
Proof. by move=> f f_inj x; rewrite -pvalE [@perm _]unlock ffunE. Qed.

Lemma perm_inj : forall u : pT, injective u.
Proof. move=> u; rewrite -!pvalE; exact: (injectiveP _ (valP u)). Qed.

Implicit Arguments perm_inj [].

Hint Resolve perm_inj.

Lemma perm_onto : forall u : pT, codom u =i predT.
Proof. by move=> u; apply/subset_cardP; rewrite ?card_codom ?subset_predT. Qed.

Definition perm_one := perm (@inj_id T).

Lemma perm_invK : forall u : pT, cancel (fun x => iinv (perm_onto u x)) u.
Proof. by move=> u x /=; rewrite f_iinv. Qed.

Definition perm_inv u := perm (can_inj (perm_invK u)).

Definition perm_mul u v := perm (inj_comp (perm_inj v) (perm_inj u)).

Lemma perm_oneP : left_id perm_one perm_mul.
Proof. by move=> u; apply/permP => x; rewrite permE /= permE. Qed.

Lemma perm_invP : left_inverse perm_one perm_inv perm_mul.
Proof. by move=> u; apply/permP => x; rewrite !permE /= permE f_iinv. Qed.

Lemma perm_mulP : associative perm_mul.
Proof. by move=> u v w; apply/permP => x; do !rewrite permE /=. Qed.

Definition perm_of_baseFinGroupMixin : FinGroup.mixin_of (perm_type T) :=
  FinGroup.Mixin perm_mulP perm_oneP perm_invP.
Canonical Structure perm_baseFinGroupType :=
  Eval hnf in BaseFinGroupType perm_of_baseFinGroupMixin.
Canonical Structure perm_finGroupType :=
  @FinGroupType perm_baseFinGroupType perm_invP.

Canonical Structure perm_of_baseFinGroupType :=
  Eval hnf in [baseFinGroupType of pT].
Canonical Structure perm_of_finGroupType :=
  Eval hnf in [finGroupType of pT].

Lemma perm1 : forall x, (1 : pT) x = x.
Proof. by move=> x; rewrite permE. Qed.

Lemma permM : forall (s1 s2 : pT) x, (s1 * s2) x = s2 (s1 x).
Proof. by move=> *; rewrite permE. Qed.

Lemma permK : forall s : pT, cancel s s^-1.
Proof. by move=> s x; rewrite -permM mulgV perm1. Qed.

Lemma permKV : forall s : pT, cancel s^-1 s.
Proof. by move=> s; have:= permK s^-1; rewrite invgK. Qed.

Lemma permJ : forall (s t : pT) x, (s ^ t) (t x) = t (s x).
Proof. by move=> *; rewrite !permM permK. Qed.

Lemma permX : forall (s : pT) x n, (s ^+ n) x = iter n s x.
Proof. by move=> s x; elim=> [|n /= <-]; rewrite ?perm1 // -permM expgSr. Qed.

Definition perm_on (A : {set T}) : pred pT :=
  fun u => [pred x | u x != x] \subset A.

Lemma perm_closed : forall A u x, perm_on A u -> (u x \in A) = (x \in A).
Proof.
move=> a u x; move/subsetP=> u_on_a.
case: (u x =P x) => [-> //|]; move/eqP=> nfix_u_x.
by rewrite !u_on_a // inE /= ?(inj_eq (perm_inj u)).
Qed.

Lemma perm_on1 :  forall H, perm_on H 1.
Proof. by move=> H; apply/subsetP=> x; rewrite inE /= perm1 eqxx. Qed.

Lemma perm_onM :  forall H f g,
  perm_on H f -> perm_on H g -> perm_on H (f * g).
Proof.
move=> H f g; move/subsetP => fH; move/subsetP => gH.
apply/subsetP => x; rewrite inE /= permM.
by case: (f x =P x) => [->|]; [move/gH | move/eqP; move/fH].
Qed.

Lemma out_perm : forall H f x, perm_on H f -> x \notin H -> f x = x.
Proof.
move=> H f x fH nHx; apply/eqP; apply: negbNE; apply: contra nHx.
exact: (subsetP fH).
Qed.

Lemma tperm_proof : forall x y : T,
  involutive [fun z => z with x |-> y, y |-> x].
Proof.
move=> x y z /=.
case: (z =P x) => [-> | ne_zx]; first by rewrite eqxx; case: eqP.
by case: (z =P y) => [->| ne_zy]; [rewrite eqxx | do 2?case: eqP].
Qed.

Definition tperm x y := perm (can_inj (tperm_proof x y)).

CoInductive tperm_spec (x y z : T) : T -> Type :=
  | TpermFirst of z = x          : tperm_spec x y z y
  | TpermSecond of z = y         : tperm_spec x y z x
  | TpermNone of z <> x & z <> y : tperm_spec x y z z.

Lemma tpermP : forall x y z, tperm_spec x y z (tperm x y z).
Proof.
by move=> x y z; rewrite permE /=; do 2?[case: eqP => /=]; constructor; auto.
Qed.

Lemma tpermL : forall x y : T, tperm x y x = y.
Proof. by move=> x y; case tpermP. Qed.

Lemma tpermR : forall x y : T, tperm x y y = x.
Proof. by move=> x y; case tpermP. Qed.

Lemma tpermD : forall x y z : T,  x != z -> y != z -> tperm x y z = z.
Proof. by move => x y z; case tpermP => // ->; rewrite eqxx. Qed.

Lemma tpermC : forall x y : T, tperm x y = tperm y x.
Proof. by move=> *; apply/permP => ?; do 2![case: tpermP => //] => ->. Qed.

Lemma tperm1 : forall x : T, tperm x x = 1.
Proof. by move=> *; apply/permP => ?; rewrite perm1; case: tpermP. Qed.

Lemma tpermK : forall x y : T, involutive (tperm x y).
Proof. by move=> x y z; rewrite !permE tperm_proof. Qed.

Lemma tpermKg : forall x y : T, involutive (mulg (tperm x y)).
Proof. by move=> x s y; apply/permP=> z; rewrite !permM tpermK. Qed.

Lemma tpermV : forall x y : T, (tperm x y)^-1 = tperm x y.
Proof.
by move=> x y; set t := tperm x y; rewrite -{2}(mulgK t t) -mulgA tpermKg.
Qed.

Lemma tperm2 : forall x y : T, tperm x y * tperm x y = 1.
Proof. by move=> x y; rewrite -{1}tpermV mulVg. Qed.

Lemma card_perm : forall A : {set T}, #|perm_on A| = fact #|A|.
Proof.
move=> A; elim: {A}#|A| {1 3}A (eqxx #|A|) => [|n IHn] A /=.
  move/pred0P=> A0; rewrite -(card1 (1 : pT)); apply: eq_card => u.
  apply/idP/eqP => /= [uA | -> {u}]; last exact: perm_on1.
  by apply/permP => x; rewrite perm1 (out_perm uA) // -topredE /= A0.
case: (pickP (mem A)) => [x /= Ax An1|]; last by move/eq_card0->.
have:= An1; rewrite (cardsD1 x) Ax eqSS; move/IHn=> {IHn} <-.
move/eqP: An1 => <- {n}; rewrite -cardX.
pose h (u : pT) := (u x, u * tperm x (u x)).
have h_inj: injective h.
  move=> u1 u2; rewrite /h [mulg]lock; case=> ->; unlock; exact: mulIg.
rewrite -(card_imset _ h_inj); apply: eq_card=> [[/= y v]].
apply/imsetP/andP=> /= [[u uA [-> -> {y v}]]|[Ay vA']].
  split; first by rewrite perm_closed.
  apply/subsetP=> z; rewrite !inE permM permE /=.
  rewrite (inj_eq (perm_inj u)) /=.
  case: (z =P x) => [->|nxz nhuz /=]; first by case/eqP; case: eqP.
  by apply: (subsetP uA); apply: contra nhuz; move/eqP->; case: (z =P x).
pose u : pT := v * tperm x y.
have def_y: y = u x by rewrite permM permE /= (out_perm vA') ?inE eqxx.
exists u; last by rewrite /h -def_y -mulgA tperm2 mulg1.
apply/subsetP=> z; rewrite inE /= permM (inv_eq (tpermK x y)) permE /=.
do 2!case: (z =P _) => [-> //| _].
by move/(subsetP vA'); rewrite inE; case/andP.
Qed.

End Theory.

Prenex Implicits tperm.

Lemma inj_tperm : forall (T T' : finType) (f : T -> T') x y z,
  injective f -> f (tperm x y z) = tperm (f x) (f y) (f z).
Proof.
by move=> T T' f x y z injf; rewrite !permE /= !(inj_eq injf) !(fun_if f).
Qed.

Lemma tpermJ : forall (T : finType) x y (s : {perm T}),
  (tperm x y) ^ s = tperm (s x) (s y).
Proof.
move=> T x y s; apply/permP => z; rewrite -(permKV s z) permJ.
apply: inj_tperm; exact: perm_inj.
Qed.

Section PermutationParity.

Variable T : finType.

Implicit Type s : {perm T}.
Implicit Types x y z : T.

(* Note that pcycle s x is the orbit of x by <[s]> under the action aperm. *)
(* Hence, the pcycle lemmas below are special cases of more general lemmas *)
(* on orbits that will be stated in action.v.                              *)
(*   Defining pcycle directly here avoids a dependency of matrix.v on      *)
(* action.v and hence morphism.v.                                          *)

Definition aperm x s := s x.
Definition pcycle s x := aperm x @: <[s]>.
Definition pcycles s := pcycle s @: T.
Definition odd_perm (s : perm_type T) := odd #|T| (+) odd #|pcycles s|.

Lemma apermE : forall x a, aperm x a = a x. Proof. by []. Qed.

Lemma mem_pcycle : forall s i x, (s ^+ i) x \in pcycle s x.
Proof. by move=> s i x; rewrite (mem_imset (aperm x)) ?mem_cycle. Qed.

Lemma pcycle_id : forall s x, x \in pcycle s x.
Proof. by move=> s x; rewrite -{1}[x]perm1 (mem_pcycle s 0). Qed.

Lemma pcycle_traject : forall s x, pcycle s x =i traject s x #[s].
Proof.
move=> s x y; apply/idP/trajectP=> [| [i _ ->]].
  by case/imsetP=> si; case/cyclePmin=> i ? -> ->; exists i; rewrite // -permX.
by rewrite -permX mem_pcycle.
Qed.

Lemma eq_pcycle_mem : forall s x y,
  (pcycle s x == pcycle s y) = (x \in pcycle s y).
Proof.
move=> s x y; apply/eqP/idP=> [<-|]; first exact: pcycle_id.
case/imsetP=> si s_si ->; apply/setP => z; apply/imsetP/imsetP.
  by case=> sj s_sj ->; exists (si * sj); rewrite ?groupM /aperm ?permM.
case=> sj s_sj ->; exists (si^-1 * sj); first by rewrite groupM ?groupV.
by rewrite /aperm permM permK.
Qed.

Lemma pcycle_sym : forall s x y, (x \in pcycle s y) = (y \in pcycle s x).
Proof. by move=> s x y; rewrite -!eq_pcycle_mem eq_sym. Qed.

Lemma pcycle_perm : forall s i x y, pcycle s ((s ^+ i) x) = pcycle s x.
Proof. by move=> s i x y; apply/eqP; rewrite eq_pcycle_mem mem_pcycle. Qed.

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
    by rewrite pcycle_sym (mem_pcycle _ 1).
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
rewrite (cardsD1 (pcycle ts x)) inE mem_imset ?inE //= -/(dp ts) {}/ts.
rewrite (cardsD1 (pcycle s y)) (cardsD1 (pcycle s x)) !(mem_imset, inE) //.
rewrite -/(dp s) !addnA !eq_pcycle_mem andbT; congr (_ + _); last first.
  wlog: s / dp (t x y s) < dp s.
    move=> IWs; case: (ltngtP (dp (t x y s)) (dp s)); [exact: IWs | | by []].
    by move=> lt_s_ts; rewrite -IWs tK.
  rewrite ltnNge; case/negP; apply: subset_leq_card; apply/subsetP=> {dp} C.
  rewrite !inE andbA andbC !(eq_sym C); case/and3P; case/imsetP=> z _ ->{C}.
  rewrite 2!eq_pcycle_mem => sxz syz.
  suff ts_z: pcycle (t x y s) z = pcycle s z.
    by rewrite -ts_z !eq_pcycle_mem {1 2}ts_z sxz syz mem_imset ?inE.
  suff exp_id: forall n, ((t x y s) ^+ n) z = (s ^+ n) z.
    apply/setP=> u; apply/idP/idP; case/imsetP=> si; case/cycleP=> i -> ->.
      by rewrite /aperm exp_id mem_pcycle.
    by rewrite /aperm -exp_id mem_pcycle.
  elim=> // n IHn; rewrite !expgSr !permM {}IHn tpermD //.
    apply: contra sxz; move/eqP->; exact: mem_pcycle.
  apply: contra syz; move/eqP->; exact: mem_pcycle.
case: eqP {dp} => [<- | ne_xy]; first by rewrite /t tperm1 mul1g pcycle_id.
suff ->: (x \in pcycle (t x y s) y) = (x \notin pcycle s y) by case: (x \in _).
wlog xf_x: s x y ne_xy / (s ^+ (xf s x y).+1) x = x.
  move=> IWs; have ne_yx := nesym ne_xy; have:= eq_xf s x y; set n := xf s x y.
  case/pred2P=> [|snx]; first exact: IWs.
  by rewrite -[x \in _]negbK ![x \in _]pcycle_sym -{}IWs ?xfC ?tXC // tC tK.
rewrite -{1}xf_x -(tXC _ _ _ _ (leqnn _)) mem_pcycle; symmetry.
rewrite -eq_pcycle_mem eq_sym eq_pcycle_mem pcycle_traject.
apply/trajectP=> [[n _ snx]].
have: looping s x (xf s x y).+1 by rewrite /looping -permX xf_x inE eqxx.
move/loopingP; move/(_ n); rewrite -{n}snx.
case/trajectP=> [[_|i]]; first exact: nesym; rewrite ltnS -permX => lt_i def_y.
by move/lt_xf: lt_i; rewrite def_y /= eqxx orbT.
Qed.

Lemma odd_perm1 : odd_perm 1 = false.
Proof.
rewrite /odd_perm card_imset ?addbb // => x y; move/eqP.
by rewrite eq_pcycle_mem /pcycle cycle1 imset_set1 /aperm perm1; move/set1P.
Qed.

Lemma odd_mul_tperm : forall x y s,
  odd_perm (tperm x y * s) = (x != y) (+) odd_perm s.
Proof.
move=> x y s; rewrite addbC -addbA -[~~ _]oddb -odd_add -ncycles_mul_tperm.
by rewrite odd_add odd_double addbF.
Qed.

Lemma odd_tperm : forall x y, odd_perm (tperm x y) = (x != y).
Proof. by move=> x y; rewrite -[_ y]mulg1 odd_mul_tperm odd_perm1 addbF. Qed.

Definition dpair (eT : eqType) := [pred t | t.1 != t.2 :> eT].
Implicit Arguments dpair [eT].

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

End PermutationParity.

Coercion odd_perm : perm_type >-> bool.
Implicit Arguments dpair [eT].
Prenex Implicits pcycle dpair pcycles aperm.

Unset Implicit Arguments.
