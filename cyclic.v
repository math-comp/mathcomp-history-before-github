
(***********************************************************************)
(* (c) Copyright Microsoft Corporation and Inria. All rights reserved. *)
(*                                                                     *)
(***********************************************************************)
(***********************************************************************)
(*                                                                     *)
(*  Definition of cyclic group                                         *)
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
Require Import normal.
Require Import div.
Require Import zp.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Section Phi.

Open Scope dnat_scope.

(***********************************************************************)
(*                                                                     *)
(*  Euler phi function                                                 *)
(*                                                                     *)
(***********************************************************************)

Definition phi n := 
    card (fun x: fzp n => coprime n x).

Lemma phi_mult: forall m n, 
  coprime m n -> phi (m * n) = phi m * phi n.
Proof.
move => m n H0; rewrite /phi.
rewrite -card_sub [card]lock -card_sub.
rewrite (mulnC (card _)) -card_sub -lock.
apply: etrans (card_prod _ _).
pose cops u := sub_finType (fun x: fzp u => coprime u x).
change (card (setA (cops (m * n))) = card (setA (prod_finType (cops n) (cops m)))).
apply: bij_eq_card_setA.
have Hf1: forall x: cops (m * n), modn (val x) n < n.
  move => [[x Hx] Hx1] /=.
  by rewrite ltn_mod; move: (Hx); case n => //; rewrite mulnC.
have Hf2: forall x : cops (m * n), 
  coprime n (Ordinal (Hf1 x)). 
  move => [[x Hx] Hx1] /=; rewrite /= in Hx1.
  rewrite /coprime -gcdn_modr.
  rewrite coprime_mull in Hx1.
  by case/andP: Hx1.
have Hf3: forall x: cops (m * n), modn (val x) m < m.
  move => [[x Hx] Hx1] /=.
  by rewrite ltn_mod; move: (Hx); case m => //; rewrite mulnC.
have Hf4: forall x : cops (m * n), 
  coprime m (Ordinal (Hf3 x)).
  move => [[x Hx] Hx1] /=; rewrite /= coprime_mull in Hx1.
  case/andP: Hx1 => Hx1 Hx2.
  by rewrite /coprime -gcdn_modr. 
pose f (x : cops (m*n)): (prod_finType (cops n) (cops m)) :=
  pair (EqSig (fun x: fzp n => coprime n x) _ (Hf2 x)) 
         (EqSig (fun x: fzp m => coprime m x) _ (Hf4 x)).
have Hf5: forall x: prod_finType (cops n) (cops m), 
   modn (chinese (val (snd x)) 
                 (val (fst x)) m n) (m * n) < (m * n).
  move => [[[x Hx] Hx1] [[y Hy] Hy1]] /=; rewrite ltn_mod.
  by move: (Hx) (Hy); case n; case m.
have Hf6: forall x : prod_finType (cops n) (cops m), 
  coprime (m * n) (Ordinal (Hf5 x)).
(*    (val (EqSig  (fun p : nat_eqType => p < m * n) _ (Hf5 x))).*)
  move => [[[x Hx] Hx1] [[y Hy] Hy1]] /=.
  have F1: 0 < n; first by move: (Hx); case n.
  have F2: 0 < m; first by move: (Hy); case m.
  rewrite /coprime /= -gcdn_modr.
  move: (coprime_mull (chinese y x m n) m n).
  rewrite {1}/coprime => ->.
  rewrite /= /coprime in Hx1; rewrite /= /coprime in Hy1.
  rewrite gcdnC gcdn_modl (@chinese_remainder2 y _ m) // 
          -gcdn_modl in Hx1.
  rewrite (coprime_sym n) /coprime Hx1 andbT.
  rewrite gcdnC.
  by rewrite gcdnC gcdn_modl (@chinese_remainder1 _ x _ n) // 
         -gcdn_modl in Hy1.
pose g x : cops (m * n) := 
  (EqSig (fun x: fzp (m * n) => coprime (m * n) x) _
         (Hf6 x)).
exists f; exists g. 
  move => [[x Hx] Hx1].
  have F1: 0 < n; first by move: (Hx); rewrite mulnC; case n.
  have F2: 0 < m; first by move: (Hx); case m.
  rewrite /f /g /=; (do !apply:  val_inj ) => /=.
  (do !apply: ordinal_inj) => /=.
  by rewrite -chinese_remainderf // modn_small.
move => [[[x Hx] Hx1] [[y Hy] Hy1]].
have F1: 0 < n; first by move: (Hx); case n.
have F2: 0 < m; first by move: (Hy); case m.
congr pair; (do !apply: val_inj) => /=; (do !apply: ordinal_inj) => /=;
  set e := chinese _ _ _ _.
- rewrite -(modn_addl_mul (divn e (m * n) * m)) -mulnA
          -divn_eq /e.
  rewrite -chinese_remainder2 // modn_small // eqd_refl.
rewrite -(modn_addl_mul (divn e (m * n) * n))
       -mulnA (mulnC n) -divn_eq /e.
by rewrite -chinese_remainder1 // modn_small // eqd_refl.
Qed.

Lemma phi_prime_k: forall p k, prime p ->
  phi (p ^ (S k)) = (p ^ (S k)) - (p ^ k).
Proof.
move => p k Hp; have Hp0: (0 < p) by case: p Hp.
have F1: forall a b c, a + b = c -> a = c - b.
  by move => a b c H; rewrite -H subn_addl.
apply: F1; rewrite /phi /=.
set n := p ^ k.
have Hf: forall x : fzp n, p * x < p * n.
  by move => [n1 Hn1]; rewrite /= ltn_pmul2l.
pose f x : fzp (p * n) := Ordinal (Hf x).
have injF: injective f.
  move=> [x Hx] [y Hy] [Hxy]; apply: ordinal_inj => /=.
  by apply/eqP; rewrite -(@eqn_pmul2l p) // Hxy.
rewrite -{5}(card_ordinal n) -(card_image injF).
rewrite -{7}(card_ordinal (p * n)) addnC.
set a := image _ _; apply: etrans (cardC a); congr addn.
apply: eq_card => [[x Hx]] /=.
rewrite /n -{1}(expnS p k) -prime_coprime_expn //.
rewrite prime_coprime //. 
suff : dvdn p x = ~~ setC a (Ordinal Hx)
  by move=>->; apply/negPn/idP.
apply/idP/idP.
  move/dvdnP=> [y Dx]; have Hy := Hx.
  rewrite Dx mulnC ltn_pmul2l /= in Hy => //.
  apply/negPn; apply/imageP.
  exists (Ordinal Hy) => //.
  by rewrite /f /=; apply:ordinal_inj=>/=; rewrite mulnC.
move/negPn; move/imageP=>[y Hy]; rewrite/f; move/ord_eqP=> /= HH. 
by apply/dvdnP; exists (nat_of_ord y); rewrite mulnC; apply/eqP.
Qed.

End Phi.


Section Comp.

Variable A: Type.
Variable f: A -> A.

(***********************************************************************)
(*                                                                     *)
(*  Definition of composition f o g                                    *)
(*                                                                     *)
(***********************************************************************)

Definition comp (f g: A->A) := fun x => f (g x).

(***********************************************************************)
(*                                                                     *)
(*  Definition of iterative composition f^n                            *)
(*                                                                     *)
(***********************************************************************)

Fixpoint compn (n: nat) : A -> A :=
  if n is S n1 then  comp f (compn n1) else (@id A).

Lemma compn_add: forall n m x,
  compn (n+m) x = comp (compn n) (compn m) x.
Proof.
elim => [|n Rec] m x //=.
by rewrite /comp Rec.
Qed.

Lemma compn0: forall x, compn 0 x = x.
Proof. by done. Qed.

Lemma compn1: forall x, compn 1%N x = f x.
Proof. by done. Qed.

Lemma compnS: forall n x, compn (S n) x = f (compn n x).
Proof. by done. Qed.

End Comp.

Section Cyclic.

Open Scope group_scope.

Variable G : finGroupType.

Lemma gexpn_compn: forall (a: G) n, a ** n = compn (fun x => a * x) n 1.
Proof. by move=> a; elim=> /= [|n Rec]; [rewrite /id|rewrite /comp Rec]. Qed.

(***********************************************************************)
(*                                                                     *)
(*  Definition of the sequence cat l [a, f a, f(f a), ...] till        *)
(*    either we reach a repetition or the size of the sequence is n    *)
(*                                                                     *)
(***********************************************************************)

Fixpoint seq_fn (f: G -> G) (n: nat) (a: G) (l: seq G) {struct n}: 
   seq G :=
  if n is S n1 then
     if ~~(l a) then seq_fn f n1 (f a) (Adds a l) else l else l.

Lemma card_seq_fn: forall f n a l, card (seq_fn f n a l) <= card l + n.
Proof.
move => f; elim => [| n Rec] a l => /=.
  by rewrite addn0 leqnn.
case Eq1: (~~(l a)) => //=; last by rewrite leq_addr.
apply: (leq_trans (Rec (f a) (Adds a l))) => /=.
by rewrite cardU1 Eq1 //= add1n addSnnS leqnn.
Qed.

Lemma  seq_fn_card: forall f n a (l: seq G) m, 
 l a -> card l <= m -> compn f m a == a -> 
 card (seq_fn f n (compn f (card l) a) l) <= m.
Proof.
move => f; elim => [| n Rec] //= a l m H H1 H2.
case Eq1: (l (compn f (card l) a)) => //.
move: (Rec a (Adds (compn f (card l) a) l)) => /=.
rewrite /= cardU1 Eq1 // /comp => H3; apply H3 => //=.
  by rewrite /setU1 H orbT.
move: H1; rewrite leq_eqVlt; move/orP => [H4 | H4] //.
by move: Eq1; rewrite (eqP H4) (eqP H2) H.
Qed.

(***********************************************************************)
(*                                                                     *)
(*  Definition of the sequence [a, f a, f(f a), ...] till              *)
(*    either we reach a repetition or the size of the sequence is      *)
(*    card g                                                           *)
(*                                                                     *)
(***********************************************************************)
 
Definition seq_f f a := seq_fn f (card (setA G)) a (Seq0 _).

Lemma  seq_f_card: forall f a m, 
 compn f (S m) a == a -> card (seq_f f a) <= S m.
Proof.
move => f a m H; rewrite /seq_f. 
move: (cardD1 1 (setA G)).
case: (card (setA G)) => //=.
move => n _; move: (@seq_fn_card f n a (Seq a) (S m)).
rewrite /= cardU1 /= card0 /comp compn0 => H1; apply H1 => //.
by rewrite /setU1 eq_refl orTb.
Qed. 

Lemma  seq_fn_in: forall f n a (l: seq G), 
 (forall m, m < card l -> l (compn f m a)) ->
 forall m, m < card (seq_fn f n (compn f (card l) a) l)  -> 
   seq_fn f n (compn f (card l) a) l  (compn f m a).
Proof.
move => f; elim => [| n Rec] //= a l H m.
case Eq1: (l (compn f (card l) a)) => /=.
  by move => *; apply H.
move => H1; rewrite -compnS.
pattern (S (card l)) at 1.
replace (S (card l)) with (card (Adds (compn f (card l) a) l)).
apply Rec.
  move => m1 //=; rewrite cardU1 /comp Eq1 /=.
  rewrite add1n ltnS leq_eqVlt; move/orP => [H2 | H2].
  by rewrite (eqP H2) /setU1 eq_refl orTb.
  by rewrite /setU1 H; first by rewrite orbT.
  by rewrite //= cardU1 Eq1.
by rewrite //= cardU1 Eq1.
Qed.  

Lemma seq_f_in: forall f a m, 
  m < card (seq_f f a) -> seq_f f a (compn f m a).
Proof.
move => f a m H; rewrite /seq_f.
pattern a at 1; replace a with (compn f (card (@Seq0 G)) a).
apply: seq_fn_in => //.
  by move => m1; rewrite /= card0.
  by rewrite /= card0 compn0; exact H. 
by rewrite /= card0 compn0. 
Qed.
 
Lemma  seq_fn_in_rev: forall f n a (l: seq G), 
 (forall b, l b -> {m: nat | (m < card l) && (compn f m a == b)}) ->
 forall b,
   seq_fn f n (compn f (card l) a) l b ->
   {m: nat | 
    (m < card (seq_fn f n (compn f (card l) a) l)) &&
    (compn f m a == b)}.
Proof.
move => f; elim => [| n Rec] //= a l H m.
case Eq1: (l (compn f (card l) a)) => //=.
  by move => *; apply H.
rewrite -compnS.
pattern (S (card l)) at 1.
replace (S (card l)) with (card (Adds (compn f (card l) a) l)).
  move => H1; case: (Rec _ _ _ _ H1) => //=.
    move => b; rewrite {1}/setU1; case Eq2: (compn f (card l) a == b). 
      by exists (card l); rewrite Eq2 andbT cardU1 Eq1 add1n leqnn.
    case/H => m1 => Hm1. 
    exists m1; case/andP: Hm1 => H3 H4; rewrite H4 andbT cardU1 Eq1 //.
    by rewrite (leq_trans H3) // add1n leqnSn.
  move => m1; move/andP => [H2 H3].
  exists m1; rewrite H3 andbT.
  by move: H2; rewrite cardU1 Eq1.
by rewrite /= cardU1 Eq1.
Qed.  

Lemma seq_f_in_rev: forall f a b, 
  seq_f f a b -> {m: nat | (m < card (seq_f f a)) && (compn f m a == b)}.
Proof.
move => f a m H; rewrite /seq_f.
pattern a at 1; replace a with (compn f (card  (@Seq0 G)) a).
apply: seq_fn_in_rev => //.
  by rewrite /= card0.
by rewrite /= card0 compn0. 
Qed.

Lemma seq_fn_uniq: forall f n a (l: seq G),
 uniq l -> uniq (seq_fn f n (compn f (card l) a) l).
Proof.
move => f; elim => [| n Rec] //= a l H.
case Eq1: (l (compn f (card l) a)) => //.
move: (Rec a (Adds (compn f (card l) a) l));
  rewrite /= cardU1 Eq1 // /comp => H1; exact: H1.
Qed.

Lemma seq_f_uniq: forall f a, uniq (seq_f f a).
Proof.
move => f a; rewrite /seq_f -{1}(compn0 f a).
replace 0 with (card (@Seq0 G)).
  by apply: seq_fn_uniq.
by rewrite //= card0.
Qed.

Lemma seq_fn_loop: forall f n a (l: seq G), 
   seq_fn f n (compn f (card l) a) l  
              (compn f (card (seq_fn f n (compn f (card l) a) l)) a) 
|| (card (seq_fn f n (compn f (card l) a) l) == n + card l).
Proof.
move => f; elim => [| n Rec] /=.
  by move => a l; rewrite add0n eq_refl orbT.
move => a l; case Eq1: (l (compn f (card l) a)) => /=.
  by rewrite Eq1 orTb.
move: (Rec a (Adds (compn f (card l) a) l)) => /=.
rewrite cardU1 Eq1 //= /comp addnA addn1.
by move => H1; exact H1.
Qed.
  
Lemma seq_f_loop_base: forall f a,
  seq_f f a (compn f (card (seq_f f a)) a).
Proof.
move => f a; rewrite /seq_f.
move/orP: (seq_fn_loop f (card (setA G)) a seq0) => //= [H1 | H1] //.
  by rewrite card0 compn0 in H1; rewrite H1.
rewrite card0 addn0 compn0 in H1.
have F1: (seq_fn f (card (setA G)) a seq0 =1 (setA G)).
  apply: subset_cardP => //=; first by apply/eqP.
  by apply/subsetP => x y.
by rewrite F1.
Qed.

Lemma seq_fn_sub_set: forall f n a (l: seq G), 
  sub_set l (seq_fn f n a l).
Proof.
move => f; elim => [| n Rec] /=; first by move => *.
move => a l; case (l a) => //=.
by move => x Hx; apply Rec => /=; rewrite /setU1 Hx orbT.
Qed.

Lemma seq_f_id: forall f a, seq_f f a a.
Proof.
move => f a;rewrite /seq_f.
move: (cardD1 1 (setA G)) => //=.
case: (card (setA G)) => //=.
by move => *; apply seq_fn_sub_set => //=; rewrite /setU1 eq_refl.
Qed.

Lemma seq_f_loop: forall f a n, seq_f f a (compn f n a).
Proof.
move => f a n.
elim: n {1 3}n (leqnn n) => [| n Rec] /=.
  by case => //= _; rewrite /id seq_f_id.
move => n1 Hn1.
case Lt1: (n1 < card (seq_f f a)).
  by apply seq_f_in; rewrite Lt1.
move/negP: Lt1; move/idP; rewrite -leqNgt => Lt1.
rewrite -(leq_add_sub Lt1).
rewrite addnC compn_add.
case: (seq_f_in_rev (seq_f_loop_base f a)) => k.
move/andP => [Hk1 Hk2].
rewrite /comp -(eqP Hk2).
change (is_true (seq_f f a (comp (compn f (n1 - card (seq_f f a))) 
                           (compn f k) a))).
rewrite -compn_add; apply Rec.
rewrite -ltnS -addnS.
rewrite (leq_trans _ Hn1) //.
by rewrite -{2}(leq_add_sub Lt1) [card _ + _]addnC leq_add2l Hk1.
Qed.

(***********************************************************************)
(*                                                                     *)
(*  Cyclic group                                                       *)
(*                                                                     *)
(***********************************************************************)

Definition cyclic a := {x, seq_f (fun x => a * x) 1 x}.

Definition orderg (x: G) := card (cyclic x).

Lemma cyclic1: forall a, cyclic a 1.
Proof.
by move => a; rewrite s2f; apply: seq_f_id.
Qed.

Lemma cyclicP: forall a b, 
  reflect (exists n, a ** n == b) (cyclic a b). 
Proof.
move => a b; apply introP; rewrite s2f.
  move => H; case (seq_f_in_rev H).
  move => n; move/andP => [Hn1 Hn2]; exists n.
  by rewrite (gexpn_compn).
move/negP => H1 [k H2]; case: H1.
rewrite -(eqP H2) gexpn_compn.
by apply seq_f_loop.
Qed.

Lemma cyclic_h: forall a (h:group G), h a -> subset (cyclic a) h.
Proof.
move => a h Ha; apply/subsetP => x; move/cyclicP => [k Hk].
rewrite -(eqP Hk); exact: groupE.
Qed.

Lemma cyclic_decomp: forall a b, 
  cyclic a b -> {m: nat | (m < orderg a) && (a ** m == b)}.
Proof.
move=> a b; rewrite s2f => H.
case: (@seq_f_in_rev (fun x => a * x) 1 b) => //.
move=> m; move/andP=> [H1 H2]; exists m.
by rewrite /orderg /cyclic icard_card H1 gexpn_compn H2.
Qed.

Lemma cyclicPmin: forall a b, 
  reflect (exists m, (m < orderg a) && (a ** m == b))
          (cyclic a b). 
Proof.
move => a b; apply: (iffP idP).
  by move=> H; case: (cyclic_decomp H) => m Hm; exists m.
by case=> m; case/andP=> H1 H2; apply/cyclicP; exists m.
Qed.

Lemma cyclic_in: forall a m, cyclic a (a ** m).
Proof. by move=> a m; apply/cyclicP; exists m; rewrite eq_refl. Qed.

Lemma cyclic_gexpn: forall a b n,
  cyclic a b -> cyclic a (b ** n).
Proof.
move => a b n; move/cyclicP => [x Hx].
by rewrite -(eqP Hx) gexpn_mul cyclic_in.
Qed.

Lemma cyclicnn: forall a, cyclic a a.
Proof. move => a; rewrite -{2}(gexpn1 a); exact: cyclic_in. Qed.

Lemma orderg1: orderg 1 = 1%N.
Proof.
rewrite /orderg (cardD1 1) cyclicnn -(addn0 1%N); congr addn.
apply eq_card0 => x; rewrite /setD1; apply/negP.
case/andP => H1; case/cyclicP => n; rewrite gexp1n => H2.
by case/negP: H1.
Qed.

Lemma orderg_pos: forall a, 0 < orderg a.
Proof. by move => a; rewrite /orderg (cardD1 a) cyclicnn. Qed.

Hint Resolve orderg_pos.

Lemma cyclic_conjgs: forall a b,
   cyclic (a ^ b) =1 (cyclic a) :^ b. 
Proof.
move=> a b x; rewrite [(_:^ b)_]s2f; apply/cyclicP/idP=> [[n]|].
  by move/eqP=> <-; rewrite /sconjg gexpn_conjg conjgK cyclic_in.
by move/cyclicP => [n Hn]; exists n; rewrite gexpn_conjg (eqP Hn) conjgKv.
Qed.

Lemma orderg_conjg: forall a b, orderg (a ^ b) = orderg a.
Proof.
move=> a b; rewrite /orderg -(card_iimage (conjg_inj b) (cyclic a)).
by apply eq_card => x; rewrite cyclic_conjgs sconjg_iimage.
Qed.

Lemma group_cyclicP: forall a, group_set (cyclic a).
Proof.
move => a; apply/groupP; split; first by apply cyclic1.
move => x y; move/cyclicP => [n Hn]; move/cyclicP => [m Hm].
by apply/cyclicP; exists (n + m); rewrite -gexpn_add (eqP Hn) (eqP Hm).
Qed.

Canonical Structure group_cyclic a := Group (group_cyclicP a). 

Lemma orderg_expn1: forall a, a ** (orderg a) == 1.
Proof.
move => a; case/cyclicPmin: (cyclic_in a (orderg a)).
case => /= [|n]; move/andP => [H1 H2]; first by rewrite -(eqP H2).
have F1: a ** (orderg a - (S n)) == 1.
  apply/eqP; apply: (mulg_injl (a ** (S n))).
  by rewrite gexpn_add mulg1 leq_add_sub -?(eqP H2) ?(leq_trans _ H1) ?leqnSn.
rewrite -subSS leq_subS // gexpn_compn in F1.
move: (seq_f_card F1).
rewrite -leq_subS // subSS leqNgt -ltn_0sub -icard_card leq_sub_sub //=.
by rewrite (leq_trans _ H1) // leqnSn.
Qed.

Lemma orderg_dvd: forall a n, 
  dvdn (orderg a) n = (a ** n == 1).
Proof.
move => a n; apply/idP/idP.
  move/dvdnP => [k Hk]; rewrite Hk.
  rewrite mulnC -gexpn_mul (eqP (orderg_expn1 a)).
  by rewrite gexp1n; apply eq_refl.
rewrite (divn_eq n (orderg a)).
rewrite -gexpn_add mulnC -gexpn_mul (eqP (orderg_expn1 a)) gexp1n.
rewrite mul1g dvdn_addr //; last by rewrite dvdn_mulr.
move: (ltn_mod n (orderg a)); case: (modn n (orderg a)).
  by rewrite dvdn0.
move => n1 H1 H2.
rewrite gexpn_compn in H2; move: (seq_f_card H2).
rewrite /orderg /cyclic icard_card in H1; rewrite leqNgt H1.
move: (cardD1 1 (seq_f (fun x => a *x) 1)).
case: (card (seq_f (fun x => a * x) 1)) => //.
by rewrite seq_f_id.
Qed.

Lemma orderg_dvd_g:
  forall (H : group G) a, H a -> dvdn (orderg a) (card H).
Proof.
move => H a Ha. 
(*have sCaH: subgroup (group_cyclic a) H. *)
have sCaH: subset (group_cyclic a) H. 
  by apply/subsetP=> x; move/cyclicP=> [n Dx]; rewrite -(eqP Dx) groupE. 
by rewrite -(LaGrange sCaH) dvdn_mulr. 
Qed.

Lemma orderg_gcd: forall a n, 0 < n ->
  orderg (a ** n) = divn (orderg a) (gcdn (orderg a) n).
Proof.
move => a n H.
set (u := orderg a).
set (v := orderg (a ** n)).
have Pu := orderg_pos a; rewrite -/u in Pu. 
have Pv := orderg_pos (a ** n); rewrite -/v in Pv.
apply/eqP; rewrite eqn_leq. 
rewrite dvdn_leq ;[ rewrite dvdn_leq //|rewrite dvdn_leq //|]. 
- have F1: dvdn v u.
    apply: group_dvdn; try apply: group_cyclic.
      by apply/subsetP => b; move/cyclicP => [n1 Hn1];  
         rewrite -(eqP Hn1) gexpn_mul cyclic_in.
  case/dvdnP: F1 => k Hk.
  have F1: dvdn k (gcdn u n).
    apply dvdn_gcd; first by rewrite Hk dvdn_mulr.
    have F2: (0 < v); first by case: (v) Pv.
    by rewrite -(@dvdn_pmul2r v k) // -Hk /u orderg_dvd
             -gexpn_mul /v orderg_expn1.
  case/dvdnP: F1 => k1 Hk1.
  case/dvdnP: (dvdn_gcdl u n) => k2 Hk2.
  rewrite {1}Hk2 divn_mull; 
    last by move: Pu; rewrite {1}Hk2; case: (gcdn _ _); rewrite ?muln0.
  apply/dvdnP; exists k1.
  apply/eqP; rewrite -(@eqn_pmul2l k); last
    by move: Pu; rewrite Hk; case: (k).
  by rewrite // -Hk Hk2 Hk1 (mulnC k) (mulnC k1 k2) !mulnA.
- case/dvdnP: (dvdn_gcdl u n) => x Hx;
    rewrite {1}Hx divn_mull; move: Pu; 
      first by rewrite Hx; case x.
    by rewrite {1}Hx; case: (gcdn u n); rewrite ?muln0.
by rewrite /v orderg_dvd gexpn_mul // -gcdn_divnC //
          -gexpn_mul /u (eqP (orderg_expn1 a)) gexp1n.
Qed.

Lemma orderg_gexp_dvd: forall a n,
  dvdn (orderg (a ** n)) (orderg a).
Proof.
move => a [| n].
  by rewrite gexpn0 orderg1 dvd1n.
rewrite orderg_gcd //.
apply/dvdnP; exists (gcdn (orderg a) (S n)).
rewrite mulnC; apply sym_equal; apply/eqP.
rewrite -dvdn_eq; exact: dvdn_gcdl.
Qed.

Lemma orderg_mul: forall (a b: G), 
  commute a b -> coprime (orderg a) (orderg b) ->
  orderg (a * b) = (orderg a * orderg b)%N.
Proof.
move => a b H H1.
have F1: dvdn (orderg (a * b)) (orderg a * orderg b).
  rewrite orderg_dvd; apply/eqP; rewrite gexpnC //.
  by rewrite -gexpn_mul mulnC -gexpn_mul
             !(eqP (orderg_expn1 _)) !gexp1n mul1g.
apply/eqP; rewrite eqn_dvd //.
set oab := orderg (_ * _); set oa := orderg _; 
 set ob := orderg _.
have F2: oab <= oa * ob.
 by apply: dvdn_leq => //; rewrite ltn_0mul /oa /ob !orderg_pos.
have F3: (a ** oab = b ** (oa * ob - oab)). 
  apply: (mulg_injr (b ** oab)).
  rewrite gexpn_add -gexpnC //.
  rewrite addnC leq_add_sub // /oab (eqP (orderg_expn1 _)).
  by rewrite  mulnC -gexpn_mul /ob (eqP (orderg_expn1 _))
              gexp1n.
have F4: orderg (a ** oab) == 1%N.
  rewrite /coprime in H1.  
  rewrite -dvdn1 -(eqP H1).
  apply dvdn_gcd; last rewrite F3;
  by exact: orderg_gexp_dvd.
rewrite gauss_inv //; apply/and3P; split => //.
  rewrite /oa /ob orderg_dvd.
  by move: (eqP (orderg_expn1 (a ** oab)));
     rewrite (eqP F4) gexpn1 => ->.
rewrite F3 in F4.
move: (eqP (orderg_expn1 (b ** (oa * ob - oab)))).
  rewrite (eqP F4) gexpn1 => F5.
have F6: (b ** (oa * ob) = 1).
  by rewrite mulnC -gexpn_mul /ob 
             (eqP (orderg_expn1 _)) gexp1n.
rewrite /oa /ob orderg_dvd.
by rewrite -F6 -(leq_add_sub F2) -gexpn_add F5; gsimpl.
Qed.

(***********************************************************************)
(*                                                                     *)
(*        Generator                                                    *)
(*                                                                     *)
(***********************************************************************)

Definition generator H a := subset (cyclic a) H && subset H (cyclic a).

Lemma generator_cyclic: forall a, generator (cyclic a) a.
Proof.
by move => a; apply/subset_eqP.
Qed.

Lemma generator_orderg: forall a b, 
  generator (cyclic a) b -> orderg a = orderg b.
Proof.
move => a b; case/andP => H1 H2.
apply: eq_card => x; apply/idP/idP => H3.
  by apply: (subsetP H2).
by apply: (subsetP H1).
Qed.

Lemma cyclic_subset: forall a n,
   subset (cyclic (a ** n)) (cyclic a).
Proof.
move => a n; apply/subsetP => x.
move/cyclicP => [n1 Hn1].
apply/cyclicP; exists (muln n n1).
by rewrite -(eqP Hn1) gexpn_mul eq_refl.
Qed.

Lemma cyclicV: forall a, cyclic a =1 cyclic a^-1.
Proof.
move => a x; apply/idP/idP; move/cyclicP => [n1 Hn1].
  apply: groupVl; apply/cyclicP; exists n1; apply/eqP; apply: invg_inj.
  by rewrite gexpnV; gsimpl; apply/eqP.
apply: groupVl; apply/cyclicP; exists n1; apply/eqP; apply: invg_inj.
by gsimpl; rewrite -gexpnV (eqP Hn1).
Qed.

Lemma generator_coprime: forall a m, 
  coprime m (orderg a) -> generator (cyclic a) (a ** m).
Proof.
move => a m Ham.
set n := orderg a.
rewrite /generator cyclic_subset /=.
rewrite /= coprime_sym /coprime in Ham.
case (@bezoutl n m); first exact: orderg_pos.
move => x Hx1 Hx2; rewrite /n (eqP Ham) in Hx2.
rewrite (eq_subset (cyclicV a)).
replace (a^-1) with ((a ** m) ** x).
  by exact: cyclic_subset.
case/dvdnP: Hx2 => k Hk.
apply: (mulg_injl a); gsimpl.
by rewrite -{1}(gexpn1 a) gexpn_mul mulnC gexpn_add Hk
           mulnC /n -gexpn_mul (eqP (orderg_expn1 _)) gexp1n.
Qed.

Definition f_phi_gen: forall a,
  sub_eqType (fun x: fzp (orderg a) => coprime (orderg a) x) ->
  sub_eqType (generator (cyclic a)).
move => a; set n :=  (orderg a).
move => [[m Hm1] Hm2]; exists (a ** m).
by apply: generator_coprime; rewrite coprime_sym.
Defined.

Definition f_phi_gen_inv: forall a,
  sub_eqType (generator (cyclic a)) ->
  sub_eqType (fun x: fzp (orderg a) => coprime (orderg a) x).
move => a [b Hb].
case: (@cyclic_decomp a b).
  case/andP: Hb; move/subsetP => HH _; apply: HH; apply: cyclicnn.
move => m Hm.
have Hm1: (m < orderg a) by case/andP: Hm.
exists (Ordinal Hm1) => /=.
case/andP: Hm => _ Hm2.
pose (k := (gcdn m (orderg a))).
pose (k1 := (divn m k)).
pose (k2 := (divn (orderg a) k)).
have Hk1: (k * k1)%N == m.
   by rewrite /k /k1 mulnC -dvdn_eq dvdn_gcdl.
have Hk2: (k * k2)%N == orderg a.
   by rewrite /k /k2 mulnC -dvdn_eq dvdn_gcdr.
have F0: orderg a = orderg b by
  apply/eqP; rewrite eqn_leq; apply/andP; split;
  apply: subset_leq_card; case/andP: Hb.
have F1: dvdn (orderg a) k2; first
  rewrite F0 orderg_dvd -(eqP Hm2) gexpn_mul -(eqP Hk1).
  rewrite -mulnA (mulnC k1) mulnA -gexpn_mul (eqP Hk2).
  by rewrite (eqP (orderg_expn1 _)) gexp1n.
move: F1; rewrite -{1}(eqP Hk2) -{2}(mul1n k2) dvdn_pmul2r; last
  by  move: (orderg_pos a); rewrite -(eqP Hk2) mulnC; case k2.
by rewrite dvdn1 /k coprime_sym.
Defined.

Lemma phi_gen: forall a, 
  phi (orderg a) = card (generator (cyclic a)).
Proof.
move => a; apply: bij_eq_card.
exists (@f_phi_gen a); exists (@f_phi_gen_inv a).
rewrite /cancel.
  move => [[x Hx1] Hx2]; apply: val_inj => /=.
  case (@cyclic_decomp a (a ** x)) => /= x1.
  move/andP => [Hx3 Hx4]; apply ordinal_inj => /=.
  wlog: x1 x Hx1 Hx3 {Hx2}Hx4/ x1 <= x => H1; first by 
    (case: (ltnP x x1) => H2; first symmetry;
      apply: H1 => //;  
      rewrite ?(eqP Hx4) //leq_eqVlt H2 orbT).
  have F1: dvdn (orderg a) (x - x1); first
    by rewrite orderg_dvd; apply/eqP;
       apply: (mulg_injl (a ** x1)); 
       rewrite mulg1 gexpn_add leq_add_sub // (eqP Hx4).
  rewrite -(leq_add_sub H1).
  case Eq1: (x - x1) => [| n1] //; rewrite Eq1 in F1.
  move: (dvdn_leq (is_true_true: 0 < S n1) F1).
  rewrite -Eq1 => H4.
  have: orderg a <= x.
    by apply: (leq_trans H4); apply leq_subr. 
  by rewrite leqNgt Hx1.
move => [x Hx]; apply: val_inj => /=.
by case (@cyclic_decomp a x) => /= x1; case/andP => _;move/eqP. 
Qed.

End Cyclic.


Unset Implicit Arguments.
