(* (c) Copyright Microsoft Corporation and Inria. All rights reserved. *)
Require Import ssreflect.
Require Import ssrbool.
Require Import funs.
Require Import eqtype.
Require Import ssrnat.
Require Import seq.
Require Import fintype.
Require Import paths.
Require Import connect.
Require Import div.
Require Import groups.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

(* group of permutations *)
Section PermGroup.

Variable d:finType.

CoInductive permType : Type := 
  Perm : eq_sig (fun g : fgraphType d d => uniq (fval g)) -> permType.

Definition pval p := match p with Perm g => g end.

Lemma can_pval : cancel pval Perm.
Proof. by rewrite /cancel; case => /=. Qed.

Lemma pval_inj : injective pval. 
Proof. exact: can_inj can_pval. Qed.

Canonical Structure perm_eqType := EqType (can_eq can_pval).

Canonical Structure perm_finType := FinType (can_uniq can_pval).

Definition fun_of_perm := fun u : permType => (val (pval u) : fgraphType _ _) : d -> d.

Coercion fun_of_perm : permType >-> Funclass.

Lemma perm_uniqP : forall g : fgraphType d d, reflect (injective g) (uniq (@fval d d g)).
Proof.
move=> g; apply: (iffP idP) => Hg.
  apply: can_inj (fun x => sub x (enum d) (index x (fval g))) _ => x.
  by rewrite {2}/fun_of_fgraph; unlock; rewrite index_uniq ?sub_index ?fproof ?mem_enum /card // count_setA index_mem mem_enum.
by rewrite -[g]can_fun_of_fgraph; unlock fgraph_of_fun; rewrite /= uniq_maps // uniq_enum.
Qed.

Lemma eq_fun_of_perm: forall u v : permType, u =1 v -> u = v.
Proof.
move => u v Huv; apply: pval_inj; apply: val_inj. 
rewrite -(can_fun_of_fgraph (val (pval u))) -(can_fun_of_fgraph (val (pval v))).
apply: fval_inj; unlock fgraph_of_fun; exact: (eq_maps Huv).
Qed.

Lemma perm_of_injP : forall f : d -> d, injective f -> uniq (fval (fgraph_of_fun f)).
Proof.
move=> f Hf; apply/perm_uniqP.
by apply: eq_inj Hf _ => x; rewrite g2f.
Qed.

Definition perm_of_inj f (Hf : injective f) : permType :=
  Perm (EqSig (fun g : fgraphType d d => uniq (fval g)) _ (perm_of_injP Hf)).

Lemma p2f : forall f (Hf : injective f), perm_of_inj Hf =1 f.
Proof. move=> *; exact: g2f. Qed.

Lemma perm_inj : forall u : permType, injective u.
Proof. by case=> H; apply/perm_uniqP; case: H => *. Qed.

Definition perm_elem := perm_finType.

Lemma inj_id : @injective d _ id.
Proof. done. Qed. 
Definition perm_unit := perm_of_inj inj_id.

Definition perm_inv u := perm_of_inj (finv_inj (@perm_inj u)).

Definition perm_mul u v := perm_of_inj (inj_comp (@perm_inj v) (@perm_inj u)).

Lemma perm_unitP : forall x, perm_mul perm_unit x = x.
Proof.
move=> u; apply eq_fun_of_perm => x.
by do 2!rewrite /fun_of_perm /= /comp g2f.
Qed.

Lemma perm_invP : forall x, perm_mul (perm_inv x) x = perm_unit.
Proof.
move=> u; apply: eq_fun_of_perm => x.
do 3!rewrite /fun_of_perm /= /comp g2f. 
by rewrite f_finv; last exact: perm_inj.
Qed.

Lemma perm_mulP : 
  forall x y z, perm_mul x (perm_mul y z) = perm_mul (perm_mul x y) z.
Proof.
move=> u v w; apply: eq_fun_of_perm => x.
by do 4!rewrite /fun_of_perm /= /comp g2f. 
Qed.

Canonical Structure perm_finGroupType := 
  FinGroupType perm_unitP perm_invP perm_mulP.

Lemma perm1 : forall x, perm_unit x = id x.
Proof. by move=> x; rewrite p2f. Qed.

Definition perm a (u : permType) := subset (fun x => u x != x) a.

Lemma perm_closed : forall a u x, perm a u -> a (u x) = a x.
Proof.
move=> a u x Hu; case Hx: (u x != x); last by move/eqP: Hx => ->.
by rewrite !(subsetP Hu) ?(inj_eq (@perm_inj u)).
Qed.  

Definition transpose (x y z : d) := if x == z then y else if y == z then x else z.

Lemma transposeK : forall x y, involutive (transpose x y).
Proof.
move=> x y z; rewrite /transpose.
case Hx: (x == z); first by rewrite (eqP Hx) set11; case: eqP.
by case Hy: (y == z); [rewrite set11 (eqP Hy) | rewrite Hx Hy].
Qed.

Definition transperm x y := perm_of_inj (can_inj (transposeK x y)).

Open Scope group_scope.

Lemma square_transperm : forall x y, let t := transperm x y in t * t = 1.
Proof.
move=> x y; apply: eq_fun_of_perm => z; rewrite /mulg /=.
do 4!rewrite /fun_of_perm /= /comp g2f.
exact: transposeK.
Qed.

Lemma card_perm: forall a : set d, card (perm a) = fact (card a).
Proof.
move=> a; move Dn: (card a) => n; move/eqP: Dn; elim: n a => [|n IHn] a.
  move/set0P=> Da; rewrite /= -(card1 perm_unit); apply: eq_card=> u.
  apply/subsetP/eqP => [Hu | <- {u} x].
    apply: eq_fun_of_perm => x; apply: eqP. 
    rewrite {1}/fun_of_perm /= g2f eq_sym.
    by apply/idPn; move/Hu; rewrite Da.
  by rewrite {1}/fun_of_perm /= g2f set11.
case: (pickP a) => [x Hx Ha|]; last by move/eq_card0->.
move: (Ha); rewrite (cardD1 x) Hx; set a' := setD1 a x; move/(IHn a')=> {IHn} Ha'.
pose h (u : permType) := EqPair (u x) (u * transperm x (u x)) : prod_finType _ _.
have Hh: injective h.
  move=> u1 u2 H; case: H (congr1 (@eq_pi2 _ _) H) => /= -> _; exact: mulg_injr.
rewrite /fact -/fact -(eqP Ha) -Ha' mulnI -card_prod_set -(card_image Hh).
apply: eq_card=> [[y v]]; apply/set0Pn/andP; rewrite /preimage /setI /=.
  case=> u; do 2!case/andP; do 2!move/eqP->; move=> Hu {y v}.
  split; first by rewrite perm_closed.
  apply/subsetP=> z.
  do 2!rewrite /mulg /= /fun_of_perm /= g2f /comp.
  rewrite /transpose -/(u x) -/(u z) (inj_eq (@perm_inj u)) /a' /setD1.
  case: (x =P z) => [<-|_]; first by case/eqP; case: eqP.
  case: (x =P u z) => [Dx | _]; first by rewrite -(perm_closed _ Hu) -Dx.
  exact: subsetP Hu z.
rewrite /= in v *; move=> [Hy Hv]; pose u : permType := v * transperm x y.
have Dy: y = u x.
  do 2!rewrite /u /= /fun_of_perm /= g2f /comp.
  rewrite -/(v x) (_ : v x = x) /transpose ?set11 //.
  by apply/eqP; apply/idPn; move/(subsetP Hv); rewrite /a'/ setD1 set11.
exists u; rewrite /h -Dy /u -mulgA square_transperm mulg1 set11.
apply/subsetP=> z; do 2!rewrite /fun_of_perm /= g2f /comp.
rewrite (inv_eq (transposeK x y)) /transpose -/(v z).
by do 2!case: (_ =P z) => [<- //| _]; move/(subsetP Hv); case/andP.
Qed.

End PermGroup.

Unset Implicit Arguments.
