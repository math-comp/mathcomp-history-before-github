Require Import ssreflect.
Require Import ssrbool.
Require Import funs.
Require Import eqtype.
Require Import ssrnat.
Require Import seq.
Require Import fintype.
Require Import connect.
Require Import groups.
Require Import action.
Require Import frobenius_cauchy.
Require Import group_perm.
Require Import tuple.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits. 

Section perm.

Variable d: finType.
Variable x: d ->d.
Hypothesis h: injective x.

Lemma perm_eqfun: forall z, (perm_of_inj h) z = x z.
Proof. apply:can_fgraph_of_fun. Qed.
End perm.

Section square_colouring.

Variable n: nat.
Definition colors:=ordinal n.
Hypothesis Hn:0<n.
Definition col0:colors:= (make_ord Hn).

Definition square := ordinal 4.

Definition perm_square:= perm_finType square.
Definition mk4 x Hx: square := EqSig (fun m : nat_eqType => m < 4) x Hx.
Definition c0:= @mk4 0 is_true_true.
Definition c1:= @mk4 1%N is_true_true.
Definition c2:=@mk4 2 is_true_true.
Definition c3:=@mk4 3 is_true_true.

(*rotations*)
Definition R1 (sc : square):square :=
match sc with EqSig 0 _ => c1| EqSig 1 _ => c2| EqSig 2 _ => c3| EqSig (S (S (S _))) _ => c0 end.

Definition R2 (sc : square):square :=
match sc with EqSig 0 _ => c2 | EqSig 1 _ => c3 | EqSig 2 _ =>c0| EqSig (S (S (S _))) _ => c1 end.

Definition R3 (sc : square):square :=
match sc with EqSig 0 _ => c3| EqSig 1 _ => c0| EqSig 2 _ => c1| EqSig (S (S (S _))) _ => c2 end.

Ltac get_inv elt l :=
  match l with 
         (_, (elt, ?x))  => x
 |    (elt, ?x)  => x
 |        (?x, _) => get_inv elt x
 end.


Definition op_inv := ( (R1,R3) ,(R2,R2) ,(R3,R1)).

Ltac inj_tac :=
move: (refl_equal op_inv); unfold op_inv;
match goal with |- ?X = _ -> injective ?Y =>
  move => _;  let x := get_inv Y X in
  apply : (can_inj (g:=x)); move => [val H1] 
end.

Lemma R1_inj:  injective R1.
Proof.
inj_tac;repeat (destruct val => //=;first by apply /eqP).
Qed.

Lemma R2_inj:  injective R2.
Proof.
inj_tac;repeat (destruct val => //=;first by apply /eqP).
Qed.

Lemma R3_inj: injective R3.
Proof. inj_tac;repeat (destruct val => //=;first by apply /eqP). Qed.

Definition r1 := (perm_of_inj R1_inj).
Definition r2 := (perm_of_inj R2_inj).
Definition r3 := (perm_of_inj R3_inj).
Definition id1:= (perm_unit square).

Definition is_rot r:=  (r * r1 == r1 * r).
Definition rot := {r, is_rot r}.

Lemma group_set_rot: group_set  rot.
apply /groupP;split.
 by rewrite /rot  s2f /is_rot mulg1 mul1g.
move => x y; rewrite /rot !s2f /= /is_rot ;move/eqP => hx ; move/eqP => hy.
by rewrite -mulgA hy !mulgA hx.
Qed.

Canonical Structure rot_group:= Group group_set_rot.

Definition rotations:setType (perm_finType square):= iset4 id1 r1 r2 r3.

Theorem ff: forall (d1 d2: finType) x1 x2,
(fun_of_fgraph (x:= d1) (x0 := d2) x1) =1 (fun_of_fgraph x2)  -> x1 = x2.
Proof.
move => d1 d2 x1 x2 H;rewrite -(can_fun_of_fgraph x1) -(can_fun_of_fgraph x2).
by apply: fval_inj;unlock fgraph_of_fun;exact: (eq_maps H).
Qed.

Lemma rot_eq_rot: forall r s, is_rot r -> is_rot s ->
(fun_of_perm r) c0 = (fun_of_perm s) c0 -> r = s.
rewrite /is_rot; move => r s  hr hs  hrs;apply :eq_fun_of_perm;move => z;
destruct z;destruct val.
 by have<-:(c0 = EqSig(fun m:nat_eqType => m < 4)0 valP);first by apply/val_eqP.
(*1*)
destruct val.
 have ht : forall t,is_rot t ->  fun_of_perm t  (EqSig (fun m : nat_eqType => m < 4) 1%N valP)= fun_of_perm (r1 * t) c0;last first.
rewrite (ht r hr) (ht s hs) -(eqP hr) -(eqP hs).
rewrite /fun_of_perm/=/comp!(can_fgraph_of_fun (d1:= square)(d2:= square)).
by congr fun_of_fgraph.
move => t ht; rewrite {2}/fun_of_perm/= /comp!(can_fgraph_of_fun (d1:= square)(d2:= square)).
 by congr fun_of_fgraph;rewrite /r1 perm_eqfun/=/c1;apply /val_eqP.
(*2*)
destruct val.
have ht: forall t,is_rot t->fun_of_perm t  (EqSig (fun m : nat_eqType => m < 4) 2%N valP)= fun_of_perm (t * (r1 * r1)) c0.
move=> t ;rewrite /is_rot => ht;rewrite mulgA (eqP ht)-mulgA(eqP ht).
rewrite {2}/fun_of_perm/=/comp{2}/fun_of_perm/=/comp/=.
rewrite !(can_fgraph_of_fun (d1:= square)(d2:= square)).
congr fun_of_fgraph.
by rewrite !perm_eqfun;apply /val_eqP.
rewrite (ht r hr) (ht s hs).
rewrite /fun_of_perm/=/comp. 
 rewrite !(can_fgraph_of_fun (d1:= square)(d2:= square))/comp.
rewrite hrs !perm_eqfun/R1/=;apply/val_eqP;auto.
(*3*)
destruct val=>//.
have ht : forall t, is_rot t -> fun_of_perm t  (EqSig (fun m : nat_eqType => m < 4) 3 valP)= fun_of_perm (t*( r1 * r1 * r1)) c0.
move=> t ;rewrite /is_rot => ht.
replace (t*(r1*r1*r1)) with ((r1*r1*r1)*t).
rewrite {2}/fun_of_perm/=/comp  !(can_fgraph_of_fun (d1:= square)(d2:= square)).
congr fun_of_fgraph.
by rewrite /r1;repeat rewrite !perm_eqfun/comp;apply/val_eqP.
by rewrite -!mulgA- (eqP ht) (mulgA r1 t r1) -(eqP ht) -(mulgA t r1 r1)  mulgA -(eqP ht)!mulgA.
rewrite (ht r hr) (ht s hs) /fun_of_perm/=/comp !(can_fgraph_of_fun (d1:= square)(d2:= square)).
by rewrite hrs.
Qed.

Lemma rotations_is_rot: forall r, rotations  r -> is_rot r.
move => r ;rewrite /rotations/is_rot s2f.
case /or4P;move/eqP => <-//; first (by rewrite mulg1 mul1g);
 apply/eqP;apply: eq_fun_of_perm;move =>z;rewrite !perm_eqfun /comp !perm_eqfun/R2/R1/R3;
 destruct z;repeat (destruct val => //=).
Qed.

Lemma rot_is_rot: rot =1 rotations.
Proof.
move => r;apply/idP/idP; last by rewrite /rot s2f;apply  rotations_is_rot.
rewrite /rot  s2f /rotations s2f;move/eqP=> h;apply/or4P.
case e: ((fun_of_perm r )c0)=> [val0 val0P].
case e0: val0=>[|val].
 rewrite (rot_eq_rot (r:=r) (s:= id1));first by rewrite eq_refl; apply/or4P.
   by rewrite (eqP h).
  by rewrite /is_rot/id1 mulg1 mul1g.
 by rewrite e perm_eqfun;apply /val_eqP; apply /eqP=>/=;rewrite e0.
destruct val.
 rewrite (rot_eq_rot (r:=r) (s:= r1));first by rewrite eq_refl; apply/or4P;rewrite orbT.
   by rewrite (eqP h).
  apply  rotations_is_rot.
  by rewrite /rotations s2f; rewrite eq_refl/=;apply/orP;right.
 by rewrite e /c0/mk4/r1 perm_eqfun/=;apply/val_eqP;apply/eqP=>/=;rewrite e0.
destruct val.
 rewrite (rot_eq_rot (r:=r) (s:= r2));first by rewrite eq_refl; apply/or4P;rewrite !orbT.
   by rewrite (eqP h).
  by apply  rotations_is_rot ;rewrite /rotations s2f; rewrite eq_refl/= !orbT.
 by rewrite e /c0/mk4/r2 perm_eqfun/=;apply/val_eqP;apply/eqP=>/=; by rewrite e0.
destruct val;last by  clear e;rewrite e0 in val0P;discriminate.
rewrite (rot_eq_rot (r:=r) (s:= r3));first by rewrite eq_refl; apply/or4P;rewrite !orbT.
  by rewrite (eqP h).
 by apply  rotations_is_rot ;rewrite /rotations s2f; rewrite eq_refl/= !orbT.
by rewrite e /c0/mk4/r3 perm_eqfun/=;apply/val_eqP;apply/eqP=>/=;rewrite e0.
Qed.


(*symmetries*)
Definition Sh (sc : square) : square:=
match sc with  EqSig 0 _ => c1| EqSig 1 _ => c0| EqSig 2 _ => c3| EqSig (S (S (S _))) _ =>c2 end.

Lemma Sh_inj: injective Sh.
Proof.
apply : (can_inj (g:= Sh));move => [val H1];
repeat (destruct val => //=;first by apply /eqP).
Qed.

Definition sh := (perm_of_inj Sh_inj).

Lemma sh_inv: perm_inv sh = sh.
Proof.
apply:(mulg_injr sh);rewrite mulVg ;apply:eq_fun_of_perm;move => [ val H1];
rewrite !perm_eqfun /= /comp/= !perm_eqfun;
repeat (destruct val => //=;first by apply /eqP).
Qed.

Definition Sv (sc : square) : square:=
match sc with  EqSig 0 _ => c3| EqSig 1 _ => c2| EqSig 2 _ => c1| EqSig (S (S (S _))) _ =>c0 end.

Lemma Sv_inj: injective Sv.
Proof. apply : (can_inj (g:= Sv));move => [val H1];
repeat (destruct val => //=;first by apply /eqP).
Qed.

Definition sv := (perm_of_inj Sv_inj).

Lemma sv_inv: perm_inv sv = sv.
Proof.
apply:(mulg_injr sv);rewrite mulVg ;apply:eq_fun_of_perm;move => [ val H1];
rewrite !perm_eqfun /= /comp/= !perm_eqfun;
repeat (destruct val => //=;first by apply /eqP).
Qed.

Definition S1 (sc : square) : square:=
match sc with  EqSig 0 _ => c0| EqSig 1 _ => c3| EqSig 2 _ => c2| EqSig (S (S (S _))) _ =>c1 end.

Lemma S1_inj: injective S1.
Proof.
apply : (can_inj (g:= S1));move => [val H1];
repeat (destruct val => //=;first by apply /eqP).
Qed.

Definition s1 := (perm_of_inj S1_inj).

Lemma s1_inv: perm_inv s1 = s1.
Proof.
apply:(mulg_injr s1);rewrite mulVg ;apply:eq_fun_of_perm;move => [ val H1];
rewrite !perm_eqfun /= /comp/= !perm_eqfun;
repeat (destruct val => //=;first by apply /eqP).
Qed.

Definition S2 (sc : square) : square:=
match sc with  EqSig 0 _ => c2| EqSig 1 _ => c1| EqSig 2 _ => c0| EqSig (S (S (S _))) _ =>c3 end.

Lemma S2_inj: injective S2.
Proof.
apply : (can_inj (g:= S2));move => [val H1];
repeat (destruct val => //=;first by apply /eqP).
Qed.

Definition s2 := (perm_of_inj S2_inj).

Lemma s2_inv: perm_inv s2 = s2.
Proof.
apply:(mulg_injr s2);rewrite mulVg ;apply:eq_fun_of_perm;move => [ val H1];
rewrite !perm_eqfun /= /comp/= !perm_eqfun;
repeat (destruct val => //=;first by apply /eqP).
Qed.

Lemma ord_enum4: ord_enum 4 = Seq (make_ord (is_true_true:0 < 4))
                                  (make_ord (is_true_true:1 < 4))
                                  (make_ord (is_true_true:2 < 4))
                                  (make_ord (is_true_true:3 < 4)).
rewrite /ord_enum /subfilter /=.
rewrite /insub.
do 4 (case: idP; last by move => *; done).
by move => i1 i2 i3 i4; repeat congr Adds; apply/val_eqP => //.
Qed.

Lemma diff_id_sh: unitg (perm_finGroupType square) != sh.
Proof.
rewrite /set1/= /fgraph_of_fun; unlock;apply/negP; move/eqP;move/fgraph_eqP=>/=.
by rewrite ord_enum4.
Qed.

Definition isometries2 :setType (perm_finType square):=  iset2 1 (perm_of_inj Sh_inj).

Lemma card_iso2: card isometries2 = 2.
Proof. 
rewrite icard2-/sh;congr S.
have ->: (1 != sh) =>//.
rewrite/set1/=/fgraph_of_fun; unlock;apply/negP; move/eqP;move/fgraph_eqP => /=;
by rewrite ord_enum4.
 Qed.

Lemma group_set_iso2: group_set  isometries2.
Proof.
apply/groupP;split;first by rewrite s2f eq_refl.
move => x y; rewrite !s2f;case /orP=> H1;case/orP=> H2; rewrite -(eqP H2) -(eqP H1);apply/orP;
 [left|right|right|left];gsimpl.
by rewrite -/sh -{1}sh_inv mulVg.
Qed.
Canonical Structure iso2_group:= Group group_set_iso2.

Definition cPair:= prod_finType (ordinal 4) (ordinal 4).
Definition e01:cPair:= (EqPair c0 c1).
Definition e12:cPair:= (EqPair c1 c2).
Definition e23:cPair:= (EqPair c2 c3).
Definition e30:cPair:= (EqPair c3 c0).
Definition e10:cPair:= (EqPair c1 c0).
Definition e21:cPair:= (EqPair c2 c1).
Definition e32:cPair:= (EqPair c3 c2).
Definition e03:cPair:= (EqPair c0 c3).

Definition next (sc:square):=
match sc with EqSig 0 _ => iset2 c3 c1
                      | EqSig 1 _ =>  iset2 c0 c2
                      | EqSig 2 _ =>  iset2 c1 c3
                      | EqSig (S (S (S _))) _  =>  iset2 c2 c0 end.

Lemma card_next: forall sc, card (next sc) = 2.
move =>sc ; destruct sc;
repeat (destruct val  =>//;first by rewrite icard2;congr S).
Qed.



Lemma next_nref: forall ci cj, ci==cj -> (next ci cj)=false.
move => ci cj Hcij.
destruct ci as [vali valiP];destruct cj as [valj valjP];rewrite (eqP Hcij).
do 4!(destruct valj =>//; first  by rewrite s2f).
 Qed.

Lemma next_sym: forall ci cj, next ci cj = next cj ci.
move => ci cj; destruct ci ;destruct cj.
destruct val;destruct val0.
rewrite  !next_nref //.
repeat (destruct val0=>//; first by rewrite !s2f ).
repeat (destruct val=>//; first by rewrite !s2f ).
destruct val;destruct val0; first by rewrite  !next_nref //.
repeat (destruct val0=>//; first by rewrite !s2f ).
repeat (destruct val=>//; first by rewrite !s2f ).
destruct val;destruct val0; first by rewrite  !next_nref //.
repeat (destruct val0=>//; first by rewrite !s2f ).
repeat (destruct val=>//; first by rewrite !s2f ).
destruct val =>//;destruct val0=>//; first by rewrite  !next_nref //.
Qed.

Definition edges1:={e:cPair,(e== e01)||(e==e12)||(e==e23)||(e==e30)
                         ||(e== e10)||(e==e21)||(e==e32)||(e==e03)}.
Definition edges: setType cPair:= iset4 e01 e12 e23 e30.

Definition isometries := {p, (p==id1)|| ((p==r1)||((p==r2)||((p==r3)||((p==sh)||((p==sv)||((p==s1)||(p==s2)))))))}.

Definition fop:= fun_of_perm.

Definition is_iso p:= forall ci cj, next ci cj -> next (fop p ci) (fop p cj).

Lemma is_iso_id: is_iso id1.
by move => ci cj ;rewrite /fop !perm_eqfun/= => ->.
Qed.

Lemma iso_r1:is_iso r1.
move => ci cj ;rewrite /fop !perm_eqfun/=.
destruct ci as[vali valiP]; destruct cj as [valj valjP].
repeat (destruct vali=>//;destruct valj=>//; first (rewrite next_nref//);
first (by repeat (destruct valj=>//; first by rewrite !s2f));
repeat (destruct vali=>//; first by rewrite !s2f)).
Qed.

Lemma isometries_iso: forall p, isometries p -> is_iso p.
move  => p; rewrite s2f.
case/or4P=> H; try rewrite (eqP H);
first (by move => ci cj ;rewrite /fop !perm_eqfun/= => ->);
try (move => ci cj ;rewrite /fop !perm_eqfun/=;
destruct ci as[vali valiP]; destruct cj as [valj valjP];
repeat (destruct vali=>//;destruct valj=>//; first (rewrite next_nref//);
first (by repeat (destruct valj=>//; first by rewrite !s2f));
repeat (destruct vali=>//; first by rewrite !s2f))).
move/or4P:H ;case =>H;try rewrite (eqP H);
try (move => ci cj ;rewrite /fop !perm_eqfun/=;
destruct ci as[vali valiP]; destruct cj as [valj valjP];
repeat (destruct vali=>//;destruct valj=>//; first (rewrite next_nref//);
first (by repeat (destruct valj=>//; first by rewrite !s2f));
repeat (destruct vali=>//; first by rewrite !s2f))).
move/orP: H=>[H|H]; rewrite (eqP H);
move => ci cj ;rewrite /fop !perm_eqfun/=;
destruct ci as[vali valiP]; destruct cj as [valj valjP];
repeat (destruct vali=>//;destruct valj=>//; first (rewrite next_nref//);
first (by repeat (destruct valj=>//; first by rewrite !s2f));
repeat (destruct vali=>//; first by rewrite !s2f)).
Qed.


Lemma  is_isoP:forall  p,reflect (is_iso p)
            (isometries p).
move => p;
apply :(iffP idP).
apply:isometries_iso.

case e0: ((fun_of_perm p )c0)=> [val0 val0P].
case e1: ((fun_of_perm p )c1)=> [val1 val1P].
destruct val0;destruct val1.
absurd (p c0 = p c1);first (red; move=>h;by move:(perm_inj h)).
by rewrite e0 e1;apply/eqP;done.
destruct val1.
(*id1*)
move => hpiso.
have :next (p c1) (p c2).
apply (hpiso c1 c2);rewrite s2f.
by apply/orP;right.
rewrite e1 s2f.
case/orP.
move => h.
have : (p c0 = p c2).
rewrite e0.
rewrite /set1/=.
rewrite -(eqP h);simpl.
by apply/val_eqP.
move => h1.
have : c0 = c2;  first by apply: (perm_inj h1).
move =>*;discriminate.
move => h2.

have :next (p c2) (p c3).
apply (hpiso c2 c3);rewrite s2f.
by apply/orP;right.
rewrite - (eqP h2) s2f.
case/orP.
move => h.
absurd (p c1 = p c3);first (red; move=>h1;by move:(perm_inj h1)).
by rewrite e1 -(eqP h);apply/eqP.
move => e3.
have : p = id1.
apply eq_fun_of_perm.
move => z;destruct z.
destruct val;rewrite perm_eqfun/=.
rewrite /id/set1/=.
apply: (etrans (y:= p c0)).

congr fun_of_fgraph.
 by apply/eqP.
rewrite e0;apply/eqP;done.
destruct val.
apply: (etrans (y:= p c1)).

congr fun_of_fgraph.
 by apply/eqP.
rewrite e1;apply/eqP;done.
destruct val; first apply: (etrans (y:= p c2)).
congr fun_of_fgraph;by apply/eqP.
rewrite -(eqP h2);apply/eqP;done.
destruct val=>//;apply : (etrans (y:= p c3)).
congr fun_of_fgraph;by apply/eqP.
rewrite -(eqP e3);apply/eqP;done.
move => ->.
rewrite s2f eq_refl;done.
move => Hpiso;have: next (p c0)(p c1).
apply: Hpiso.
rewrite s2f;done.
rewrite e0.
simpl.
rewrite s2f.
case/orP ; last by rewrite e1.
move => e3;have hs1: isometries s1; first by rewrite s2f eq_refl ?orbT.
have: next (p c1)(p c2).
apply: Hpiso.
rewrite s2f;done.
rewrite -(eqP e3).
simpl.
rewrite s2f.
case/orP ; first last.
move => h2;absurd (p c2 = p c0);first (red; move=>h1;by move:(perm_inj h1)).
by rewrite e0 -(eqP h2);apply/eqP.
move => e2.
have: next (p c2)(p c3).
apply: Hpiso.
rewrite s2f;done.
rewrite -(eqP e2).
simpl.
rewrite s2f.
case/orP.
have : p = s1.
apply eq_fun_of_perm.
move => z;destruct z.
destruct val;rewrite perm_eqfun/=.
rewrite /id/set1/=.
apply: (etrans (y:= p c0)).

congr fun_of_fgraph.
 by apply/eqP.
rewrite e0;apply/eqP;done.
destruct val.
apply: (etrans (y:= p c1)).

congr fun_of_fgraph.
 by apply/eqP.
rewrite -(eqP e3);apply/eqP;done.
destruct val; first apply: (etrans (y:= p c2)).
congr fun_of_fgraph;by apply/eqP.
rewrite -(eqP e2);apply/eqP;done.
destruct val=>//;apply : (etrans (y:= p c3)).
congr fun_of_fgraph;by apply/eqP.
have: next (p c2)(p c3).
apply: Hpiso.
rewrite s2f;done.
rewrite -(eqP e2).
simpl.
rewrite s2f.
case/orP.
move/eqP=>h3;by rewrite -h3.
move => h3; absurd (p c1 = p c3);first (red; move=>h1;by move:(perm_inj h1)).
by rewrite -(eqP e3)  -(eqP h3);apply/eqP.
move => -> _.
by rewrite s2f eq_refl !orbT.
move =>h3; absurd (p c1 = p c3);first (red; move=>h1;by move:(perm_inj h1)).
by rewrite -(eqP e3)  -(eqP h3);apply/eqP.

move => Hpiso;have: next (p c1)(p c0).
apply: Hpiso.
rewrite s2f;done.
rewrite e1.
simpl.
rewrite s2f.
case/orP.
move => e3;have hr3: isometries r3; first by rewrite s2f eq_refl ?orbT.
have ->: p = r3;last by apply : hr3.
rename e3 into f0.
have: next (p c1)(p c2).
apply: Hpiso.
rewrite s2f;done.
rewrite e1.
simpl.
rewrite s2f.
case/orP.
move => e2.
 absurd (p c2 = p c0);first (red; move=>h1;by move:(perm_inj h1)).
by rewrite -(eqP e2)  -(eqP f0);apply/eqP.
move => e2.

have: next (p c2)(p c3).
apply: Hpiso.
rewrite s2f;done.
rewrite -(eqP e2).
simpl.
rewrite s2f.
case/orP.
move => e3.
 absurd (p c3 = p c1);first (red; move=>h1;by move:(perm_inj h1)).
by rewrite -(eqP e3)  e1;apply/eqP.
move => e3.
apply eq_fun_of_perm.
move => z;destruct z.
destruct val;rewrite perm_eqfun/=.
rewrite /id/set1/=.
apply: (etrans (y:= p c0)).

congr fun_of_fgraph.
 by apply/eqP.
rewrite (eqP f0);apply/eqP;done.
destruct val.
apply: (etrans (y:= p c1)).

congr fun_of_fgraph.
 by apply/eqP.
rewrite e1;apply/eqP;done.
destruct val; first apply: (etrans (y:= p c2)).
congr fun_of_fgraph;by apply/eqP.
rewrite -(eqP e2);apply/eqP;done.
destruct val=>//;apply : (etrans (y:= p c3)).
congr fun_of_fgraph;by apply/eqP.
rewrite -(eqP e3);apply/eqP;done.
move => e3;have hr3: isometries sh; first by rewrite s2f eq_refl ?orbT.
have ->: p = sh;last by apply : hr3.
rename e3 into f0.
have: next (p c1)(p c2).
apply: Hpiso.
rewrite s2f;done.
rewrite e1.
simpl.
rewrite s2f.
case/orP;first last.
move => e2.
 absurd (p c2 = p c0);first (red; move=>h1;by move:(perm_inj h1)).
by rewrite -(eqP e2)  -(eqP f0);apply/eqP.
move => e2.

have: next (p c2)(p c3).
apply: Hpiso.
rewrite s2f;done.
rewrite -(eqP e2).
simpl.
rewrite s2f.
case/orP;first last.
move => e3.
 absurd (p c3 = p c1);first (red; move=>h1;by move:(perm_inj h1)).
by rewrite -(eqP e3)  e1;apply/eqP.
move => e3.
apply eq_fun_of_perm.
move => z;destruct z.
destruct val;rewrite perm_eqfun/=.
rewrite /id/set1/=.
apply: (etrans (y:= p c0)).

congr fun_of_fgraph.
 by apply/eqP.
rewrite (eqP f0);apply/eqP;done.
destruct val.
apply: (etrans (y:= p c1)).

congr fun_of_fgraph.
 by apply/eqP.
rewrite e1;apply/eqP;done.
destruct val; first apply: (etrans (y:= p c2)).
congr fun_of_fgraph;by apply/eqP.
rewrite -(eqP e2);apply/eqP;done.
destruct val=>//;apply : (etrans (y:= p c3)).
congr fun_of_fgraph;by apply/eqP.
rewrite -(eqP e3);apply/eqP;done.

(*next*)
move => hpiso.
destruct val0;destruct val1.
have : (p c0 = p c1).
rewrite e0.
rewrite /set1/=.
rewrite e1;simpl.
by apply/val_eqP.
move => h1.
have : c0 = c1;  first by apply: (perm_inj h1).
move =>*;discriminate.
destruct val1.
have :next (p c1) (p c2).
apply (hpiso c1 c2);rewrite s2f.
by apply/orP;right.
rewrite e1 s2f.
case/orP;move => h.
 absurd (p c0 = p c2);first (red; move=>h1;by move:(perm_inj h1)).
by rewrite -(eqP h)  e0;apply/eqP.
have :next (p c2) (p c3).
apply (hpiso c2 c3);rewrite s2f.
by apply/orP;right.
rewrite - (eqP h) s2f.
case/orP;move => e3.
absurd (p c1 = p c3);first (red; move=>h1;by move:(perm_inj h1)).
by rewrite e1 -(eqP e3);apply/eqP.
have : p = r1.
apply eq_fun_of_perm.
move => z;destruct z.
destruct val;rewrite perm_eqfun/=.
rewrite /id/set1/=.
apply: (etrans (y:= p c0)).

congr fun_of_fgraph.
 by apply/eqP.
rewrite e0;apply/eqP;done.
destruct val.
apply: (etrans (y:= p c1)).

congr fun_of_fgraph.
 by apply/eqP.
rewrite e1;apply/eqP;done.
destruct val; first apply: (etrans (y:= p c2)).
congr fun_of_fgraph;by apply/eqP.
rewrite -(eqP h);apply/eqP;done.
destruct val=>//;apply : (etrans (y:= p c3)).
congr fun_of_fgraph;by apply/eqP.
rewrite -(eqP e3);apply/eqP;done.
move => ->.
by rewrite s2f eq_refl ?orbT.
destruct val1 =>//.
have: next (p c0)(p c1).
apply: hpiso.
rewrite s2f;done.
rewrite e0 e1.
simpl.
rewrite s2f.
case/orP;move/eqP=>*;discriminate.
destruct val0.
have: next (p c1)(p c2).
apply: hpiso.
rewrite s2f;done.
rewrite  e1.
simpl.
rewrite s2f.
case/orP ; first last.
move => h2;absurd (p c2 = p c0);first (red; move=>h1;by move:(perm_inj h1)).
by rewrite e0 -(eqP h2);apply/eqP.
move => e2.
have: next (p c2)(p c3).
apply: hpiso.
rewrite s2f;done.
rewrite -(eqP e2).
simpl.
rewrite s2f.
case/orP => e3.

have : p = s2.
apply eq_fun_of_perm.
move => z;destruct z.
destruct val;rewrite perm_eqfun/=.
rewrite /id/set1/=.
apply: (etrans (y:= p c0)).

congr fun_of_fgraph.
 by apply/eqP.
rewrite e0;apply/eqP;done.
destruct val.
apply: (etrans (y:= p c1)).

congr fun_of_fgraph.
 by apply/eqP.
rewrite e1;apply/eqP;done.
destruct val; first apply: (etrans (y:= p c2)).
congr fun_of_fgraph;by apply/eqP.
rewrite -(eqP e2);apply/eqP;done.
destruct val=>//;apply : (etrans (y:= p c3)).
congr fun_of_fgraph;by apply/eqP.
by rewrite -(eqP e3).
move => ->.
by rewrite s2f eq_refl ?orbT.
absurd (p c1 = p c3);first (red; move=>h1;by move:(perm_inj h1)).
by rewrite e1 -(eqP e3)  ;apply/eqP.
destruct val0 =>//.
have: next (p c1)(p c0).
apply: hpiso.
rewrite s2f;done.
rewrite e1 e0.
simpl.
rewrite s2f.
case/orP;move/eqP=>*;discriminate.
destruct val0.
destruct val1.
absurd (p c1 = p c0);first (red; move=>h1;by move:(perm_inj h1)).
by rewrite e1 e0;apply/eqP.
destruct val1 =>//.
have hr2: isometries r2; first by rewrite s2f eq_refl ?orbT.
have ->: p = r2;last by apply : hr2.
have: next (p c1)(p c2).
apply: hpiso.
rewrite s2f;done.
rewrite e1.
simpl.
rewrite s2f.
case/orP;move => e2.
 absurd (p c2 = p c0);first (red; move=>h1;by move:(perm_inj h1)).
by rewrite -(eqP e2)  e0;apply/eqP.
have: next (p c2)(p c3).
apply: hpiso.
rewrite s2f;done.
rewrite -(eqP e2).
simpl.
rewrite s2f.
case/orP;move => e3.
 absurd (p c3 = p c1);first (red; move=>h1;by move:(perm_inj h1)).
by rewrite -(eqP e3)  e1;apply/eqP.
apply eq_fun_of_perm.
move => z;destruct z.
destruct val;rewrite perm_eqfun/=.
rewrite /set1/=.
apply: (etrans (y:= p c0)).
congr fun_of_fgraph.
 by apply/eqP.
rewrite e0;apply/eqP;done.
destruct val.
apply: (etrans (y:= p c1)).
congr fun_of_fgraph.
 by apply/eqP.
rewrite e1;apply/eqP;done.
destruct val; first apply: (etrans (y:= p c2)).
congr fun_of_fgraph;by apply/eqP.
rewrite -(eqP e2);apply/eqP;done.
destruct val=>//;apply : (etrans (y:= p c3)).
congr fun_of_fgraph;by apply/eqP.
rewrite -(eqP e3);apply/eqP;done.
destruct val0=>//;destruct val1.
have: next (p c1)(p c2).
apply: hpiso.
rewrite s2f;done.
rewrite e1.
simpl.
rewrite s2f.
case/orP;move => e2;first last.
 absurd (p c2 = p c0);first (red; move=>h1;by move:(perm_inj h1)).
by rewrite -(eqP e2)  e0;apply/eqP.
have: next (p c2)(p c3).
apply: hpiso.
rewrite s2f;done.
rewrite -(eqP e2).
simpl.
rewrite s2f.
case/orP;move => e3;first last.
 absurd (p c3 = p c1);first (red; move=>h1;by move:(perm_inj h1)).
by rewrite -(eqP e3)  e1;apply/eqP.
have -> : p = sv.
apply eq_fun_of_perm.
move => z;destruct z.
destruct val;rewrite perm_eqfun/=.
rewrite /set1/=.
apply: (etrans (y:= p c0)).
congr fun_of_fgraph; by apply/eqP.
rewrite e0;apply/eqP;done.
destruct val.
apply: (etrans (y:= p c1)).
congr fun_of_fgraph; by apply/eqP.
rewrite e1;apply/eqP;done.
destruct val; first apply: (etrans (y:= p c2)).
congr fun_of_fgraph;by apply/eqP.
rewrite -(eqP e2);apply/eqP;done.
destruct val=>//;apply : (etrans (y:= p c3)).
congr fun_of_fgraph;by apply/eqP.
rewrite -(eqP e3);apply/eqP;done.
by rewrite s2f eq_refl ?orbT.
destruct val1=>//.
absurd (p c0 = p c1);first (red; move=>h1;by move:(perm_inj h1)).
by rewrite  e0  e1;apply/eqP.
Qed.

Lemma group_set_iso: group_set  isometries.
Proof.
apply/groupP;split.
by  rewrite s2f eq_refl/=.

move => x y hx hy ; apply /is_isoP.
move => ci cj.
simpl.
rewrite /fop.
simpl.
rewrite /fun_of_perm !(can_fgraph_of_fun (d1:= square)(d2:= square))/comp.
move => hij;move : ((isometries_iso hx) _ _ hij).
exact:  ((isometries_iso hy) (fop x ci) (fop x cj)).
Qed.
Canonical Structure iso_group:= Group group_set_iso.

Lemma card_rot: card rot = 4.
Proof.
rewrite (eq_card rot_is_rot).
rewrite (icardD1 id1)  (icardD1 r1) (icardD1 r2) (icardD1 r3)  /rotations/= !s2f  eq_refl !orTb;congr addn.
repeat 
 match goal with |- context [?x != ?y] => have ->: (x != y);
first by rewrite/set1/= /fgraph_of_fun; unlock;apply/negP; move/eqP;
   move/fgraph_eqP => /=;rewrite ord_enum4  end.
repeat (rewrite eq_refl  ?orbT;congr addn).
rewrite -(@eq_card _ set0 );first by apply card0.
by move =>x ;rewrite !s2f;do 4! case: (_ ==x).
Qed.


Lemma group_set_rotations: group_set  rotations.
Proof.
move/groupP: group_set_rot=> [h1 hs].
apply/groupP;split.
by rewrite -(rot_is_rot 1).
move => x y; rewrite -!rot_is_rot.
by apply hs.
Qed.

(*Canonical Structure rotations_group:= Group group_set_rotations.*)
Definition col_squares: finType :=fgraph_finType  square  colors.

Definition  act_f(sc: col_squares ) (perm:perm_square) :col_squares:= 
let cs:= fun_of_fgraph sc in let : permf := fun_of_perm (perm_inv perm) in 
fgraph_of_fun ( fun z => cs (permf z)).

Lemma act_f_1:  forall x , act_f x 1 = x.
Proof.
move => x;rewrite /act_f;apply:ff;move => y.
have -> : (@perm_inv  square 1) = 1;first by exact :invg1.
by rewrite can_fgraph_of_fun perm_eqfun.
Qed.

Lemma act_f_morph:  forall x y z, act_f z (x * y) = act_f (act_f z x) y.
move => x y z;rewrite /act_f/=;apply :(ff (d1:= square) (d2:= colors)).
have ->: (@perm_inv square (x*y))= (perm_inv y)*(perm_inv x);first by exact:invg_mul.
by move => t;rewrite !(can_fgraph_of_fun (d1:= square) (d2:= colors))  perm_eqfun.
Qed.

Definition to := Action  act_f_1 act_f_morph.

Definition square_coloring_number2 := t to iso2_group.
Definition square_coloring_number4 := t to rot_group.
Definition square_coloring_number8 := t to iso_group.

Infix "^":= expn : dnat_scope.


Lemma Fid:forall a:group (perm_finGroupType square), a 1-> (F to a 1)=1 (setA col_squares).
move => a Ha x.
rewrite /F;apply/idP;apply/idP.
apply/andP;split =>//=;last by rewrite act_f_1.
Qed.

Lemma card_Fid :forall a :group (perm_finGroupType square), a 1 -> card (F to a id1) = (n ^ 4)%N.
move => a Ha;rewrite (eq_card (Fid Ha)) /col_squares.
have <- : card (setA square) = 4;first by rewrite cardA /=ord_enum4.
have <-: card (setA colors)=n;first by rewrite card_ordinal.
rewrite -card_tfunspace; apply: eq_card=> f; symmetry.
by move: (@fgraph_prodP square colors  (fun _  => setA colors)f ) => h; apply/h.
Qed.

Definition coin0(sc : col_squares) : colors:=(fun_of_fgraph sc) c0.
Definition coin1(sc : col_squares) : colors:=(fun_of_fgraph sc) c1.
Definition coin2(sc : col_squares) : colors:=(fun_of_fgraph sc) c2.
Definition coin3(sc : col_squares) : colors:=(fun_of_fgraph sc) c3.


Lemma F_Sh: forall a:group (perm_finGroupType square), a sh -> (F to a (perm_of_inj Sh_inj))=1 
{x:col_squares, (coin0 x == coin1 x) &&(coin2 x == coin3 x)}.
Proof.
rewrite /sh => a Ha x. rewrite  /F   !s2f  Ha /=    /to/=/act_f/=.

rewrite /coin0/c0/coin1/c1/coin2/c2/coin3/c3/=sh_inv.
have: (card (setA square)=4);first by rewrite cardA /=ord_enum4.
destruct x; do 4! (destruct val=>//=; first by rewrite -e=> *; discriminate).
destruct val=>//=; last by rewrite -e=> *; discriminate.
move => _.
apply/idP/idP=>/=.
 move/eqP=> H;rewrite /fun_of_fgraph/=; unlock=>/=.
 move:H;set f:= fgraph_of_fun _;set g:= Fgraph _ =>H.
 have:((fun_of_fgraph f c0) = (fun_of_fgraph g c0));first by rewrite H.
 have:((fun_of_fgraph f c2) = (fun_of_fgraph g c2));first by rewrite H.
 rewrite !can_fgraph_of_fun !perm_eqfun/= /fun_of_fgraph;unlock=>/=.
 by move=> -> ->;apply/andP;split;done.
rewrite {1 2 3 4}/fun_of_fgraph;unlock=>/=.
rewrite ord_enum4.
simpl.
case/andP=> h0 h1;rewrite (eqP h0)(eqP h1);
apply/eqP;apply :(ff (d1:= square) (d2:= colors))=> z.
rewrite can_fgraph_of_fun/= perm_eqfun.
destruct z;  
repeat (destruct val=>//=;first by rewrite /fun_of_fgraph;unlock=>/=;unlock=>/=;rewrite ord_enum4).
Qed.

Lemma F_Sv: forall a:group (perm_finGroupType square), a sv -> (F to a (perm_of_inj Sv_inj))=1 
{x:col_squares, (coin0 x == coin3 x) &&(coin2 x == coin1 x)}.
Proof.
rewrite /sv => a Ha x. rewrite  /F   !s2f  Ha /=    /to/=/act_f/=.

rewrite /coin0/c0/coin1/c1/coin2/c2/coin3/c3/=sv_inv.
have: (card (setA square)=4);first by rewrite cardA /=ord_enum4.
destruct x; do 4! (destruct val=>//=; first by rewrite -e=> *; discriminate).
destruct val=>//=; last by rewrite -e=> *; discriminate.
move => _.
apply/idP/idP=>/=.
 move/eqP=> H;rewrite /fun_of_fgraph/=; unlock=>/=.
 move:H;set f:= fgraph_of_fun _;set g:= Fgraph _ =>H.
 have:((fun_of_fgraph f c0) = (fun_of_fgraph g c0));first by rewrite H.
 have:((fun_of_fgraph f c1) = (fun_of_fgraph g c1));first by rewrite H.
 rewrite !can_fgraph_of_fun !perm_eqfun/= /fun_of_fgraph;unlock=>/=.
 by move=> -> ->;apply/andP;split;done.
rewrite {1 2 3 4}/fun_of_fgraph;unlock=>/=.
rewrite ord_enum4.
simpl.
case/andP=> h0 h1;rewrite (eqP h0)(eqP h1);
apply/eqP;apply :(ff (d1:= square) (d2:= colors))=> z.
rewrite can_fgraph_of_fun/= perm_eqfun.
destruct z;  
repeat (destruct val=>//=;first by rewrite /fun_of_fgraph;unlock=>/=;unlock=>/=;rewrite ord_enum4).
Qed.

Ltac inv_tac :=
match goal with |- perm_inv  ?x = _  =>
apply:(mulg_injr x);rewrite mulVg ;apply:eq_fun_of_perm ;move => [ val H1];
rewrite !perm_eqfun /= /comp/= !perm_eqfun
end.

Lemma r1_inv: perm_inv r1 = r3.
Proof. inv_tac;repeat (destruct val => //=;rewrite /mk4 /=  //;first by apply /
eqP). Qed.

Lemma r2_inv: perm_inv r2 = r2.
Proof. inv_tac;repeat (destruct val => //=;rewrite /mk4 /=  //;first by apply /
eqP). Qed.

Lemma r3_inv: perm_inv r3 = r1.
Proof. inv_tac;repeat (destruct val => //=;rewrite /mk4 /=  //;first by apply /
eqP). Qed.


Lemma F_R2: forall a:group (perm_finGroupType square), a  r2 ->(F to a (perm_of_inj R2_inj))=1 
{x:col_squares, (coin0 x == coin2 x) &&(coin1 x == coin3 x)}.
Proof.
rewrite /r2  => a Ha x;rewrite /F  !s2f  Ha /=   /to/=/act_f/=.
destruct x;rewrite /coin0/c0/coin1/c1/coin2/c2/coin3/c3/=.
have: (card (setA square)=4);first by rewrite cardA /=ord_enum4.
do 4! (destruct val=>//=; first by rewrite -e=> *; discriminate).
destruct val=>//=; last by rewrite -e=> *; discriminate.

move =>_;rewrite r2_inv;apply /idP/idP =>/=.
 move/eqP=> H;rewrite /fun_of_fgraph/=; unlock=>/=.
 move:H;set f:= fgraph_of_fun _;set g:= Fgraph _ => H. 
 have:((fun_of_fgraph f c0) = (fun_of_fgraph g c0));first by rewrite H.
 have:((fun_of_fgraph f c1) = (fun_of_fgraph g c1));first by rewrite H.
 rewrite /f /g/r2 !can_fgraph_of_fun !perm_eqfun/= /fun_of_fgraph;unlock=>/=.
 by move=> -> ->;apply/andP;split.
rewrite {1 2 3 4}/fun_of_fgraph;unlock=>/=.
rewrite ord_enum4 =>/=.
case/andP=> h0 h1;rewrite (eqP h0 ) (eqP h1);
apply/eqP;apply : (ff (d1:= square) (d2:= colors)) => z.
rewrite can_fgraph_of_fun/= perm_eqfun;destruct z.
repeat (destruct val=>//=;first by rewrite /fun_of_fgraph;unlock=>/=;unlock=>/=;rewrite ord_enum4).
Qed.

Lemma F_r1: forall a:group (perm_finGroupType square), a  r1 ->(F to a (perm_of_inj R1_inj))=1 
{x:col_squares,(coin0 x == coin1 x)&&(coin1 x == coin2 x)&&(coin2 x == coin3 x)}.
rewrite /r1  => a Ha x;rewrite /F  !s2f  Ha /=   /to/=/act_f/=.
destruct x;rewrite /coin0/c0/coin1/c1/coin2/c2/coin3/c3/=.
have: (card (setA square)=4);first by rewrite cardA /=ord_enum4.
do 4! (destruct val=>//=; first by rewrite -e=> *; discriminate).
destruct val=>//=; last by rewrite -e=> *; discriminate.
move =>_;rewrite r1_inv;apply /idP/idP =>/=.
 move/eqP=> H;rewrite /fun_of_fgraph/=; unlock=>/=.
 move:H;set f:= fgraph_of_fun _;set g:= Fgraph _ => H.
 have:((fun_of_fgraph f c0) = (fun_of_fgraph g c0));first by rewrite H.
 have:((fun_of_fgraph f c1) = (fun_of_fgraph g c1));first by rewrite H.
 have:((fun_of_fgraph f c2) = (fun_of_fgraph g c2));first by rewrite H.
 rewrite /f /g!can_fgraph_of_fun !perm_eqfun/= /fun_of_fgraph;unlock=>/=.
 by move=> -> -> -> ;apply/andP;split =>//;apply/andP;split.
rewrite {1 2 3 4 5 6}/fun_of_fgraph;unlock=>/=.
rewrite ord_enum4 =>/=.
case/andP=> h0 h1; move/andP: h0=> [h0 h2];rewrite (eqP h0 ) (eqP h2) (eqP h1).
apply/eqP;apply : (ff (d1:= square) (d2:= colors))=> z.
rewrite can_fgraph_of_fun/r3/= perm_eqfun;destruct z.
repeat (destruct val=>//=;first by rewrite /fun_of_fgraph;unlock=>/=;rewrite ord_enum4).
Qed.

Lemma F_r3: forall a:group (perm_finGroupType square), a  r3 ->(F to a (perm_of_inj R3_inj))=1 
{x:col_squares,(coin0 x == coin1 x)&&(coin1 x == coin2 x)&&(coin2 x == coin3 x)}.
rewrite /r3  => a Ha x;rewrite /F  !s2f  Ha /=   /to/=/act_f/=.
destruct x;rewrite /coin0/c0/coin1/c1/coin2/c2/coin3/c3/=.
have: (card (setA square)=4);first by rewrite cardA /=ord_enum4.
do 4! (destruct val=>//=; first by rewrite -e=> *; discriminate).
destruct val=>//=; last by rewrite -e=> *; discriminate.
move =>_;rewrite r3_inv;apply/idP/idP=>/=.
 move/eqP=> H;rewrite /fun_of_fgraph/=; unlock=>/=.
 move:H;set f:= fgraph_of_fun _;set g:= Fgraph _ => H.
 have:((fun_of_fgraph f c0) = (fun_of_fgraph g c0));first by rewrite H.
 have:((fun_of_fgraph f c1) = (fun_of_fgraph g c1));first by rewrite H.
 have:((fun_of_fgraph f c2) = (fun_of_fgraph g c2));first by rewrite H.
 rewrite /f /g !can_fgraph_of_fun !perm_eqfun/= /fun_of_fgraph;unlock=>/=.
 by move=> -> -> -> ;apply/andP;split =>//;apply/andP;split.
rewrite {1 2 3 4 5 6}/fun_of_fgraph;unlock=>/=;rewrite ord_enum4 =>/=.
case/andP=> h0 h1; move/andP: h0=> [h0 h2];rewrite (eqP h0 ) (eqP h2) (eqP h1).
apply/eqP;apply : (ff (d1:= square) (d2:= colors))=> z.
rewrite can_fgraph_of_fun/r3/= perm_eqfun;destruct z.
repeat (destruct val=>//=;first by rewrite /fun_of_fgraph;unlock=>/= ;rewrite ord_enum4).
Qed.
 Lemma size4:  forall x y z t:colors ,  size (Seq x y z t ) = card (setA (ordinal 4)).
by rewrite cardA/= ord_enum4.
Qed.

Definition f(col_pair:prod_finType colors colors) :col_squares:=
match col_pair  with EqPair c1 c2 => 
    Fgraph (d1:=ordinal 4) (val:=Seq c1 c1 c2 c2)
      (size4 c1 c1 c2 c2)
end.

Lemma f_inj: injective f.
move => x y;destruct x; destruct y;rewrite /f.
move/fgraph_eqP=> H;case/and5P :H=>*.
by apply /eqP;apply /andP;split.
Qed.
Definition g(col_pair:prod_finType colors colors) :col_squares:=
match col_pair  with EqPair c1 c2 => 
    Fgraph (d1:=ordinal 4) (val:=Seq c1 c2 c2 c1)
      (size4 c1 c2 c2 c1)
end.

Lemma g_inj: injective g.
move => x y;destruct x; destruct y;rewrite /g.
move/fgraph_eqP=> H;case/and5P :H=>*.
by apply /eqP;apply /andP;split.
Qed.

Definition c(col:colors) :col_squares:=
    Fgraph (d1:=ordinal 4) (val:=Seq col col col col)
      (size4 col col col col).

Lemma c_inj: injective c.
Proof.
move => x y;destruct x; destruct y;rewrite /f.
move/fgraph_eqP=> H;case/and5P :H=>*.
by apply /eqP.
Qed.


Lemma fbicolor: card {x : col_squares, (coin0 x == coin1 x) && (coin2 x == coin3 x)} =(n * n)%N.
have <-: card (setA colors) = n;first by rewrite card_ordinal.
move: (card_image f_inj (setA (prod_finType colors colors))).
have <-: card(setA(prod_finType colors colors)) =
        (card (setA colors) * card (setA colors))%N;first by rewrite -card_prod.
have : image f (setA (prod_finType colors colors)) =1 {x : col_squares, (coin0 x == coin1 x) && (coin2 x == coin3 x)}.
 move => z;rewrite s2f;destruct z.
have: (card (setA square)=4);first by rewrite cardA /=ord_enum4.
do 4! (destruct val=>//=; first by rewrite -e=> *; discriminate).
destruct val=>//=; last by rewrite -e=> *; discriminate.
move => _;apply /idP/idP.
  case/imageP => x3  Hx3;case x3 => col1 col2;rewrite /f/=.
  case/fgraph_eqP;case/and5P=> h1 h2 h3 h4 _.
  rewrite (eqP h1)(eqP h2) (eqP h3)(eqP h4) /coin0/coin1/coin2/coin3/=.
  by apply/andP;split; rewrite /fun_of_fgraph;unlock=> /= ; rewrite ord_enum4.
 rewrite /coin1/coin0/coin2/coin3/=/fun_of_fgraph;unlock=>/=;
  rewrite ord_enum4/=.
 case/andP=> h1 h2;apply/imageP;exists (EqPair x x1) =>//=.
 by rewrite (eqP h1) (eqP h2) =>//=;apply/fgraph_eqP=>//=.
by move => h1 <-;symmetry;apply:eq_card.
Qed.



Lemma gbicolor: card {x : col_squares, (coin0 x == coin3 x) && (coin2 x == coin1 x)} =(n * n)%N.
have <-: card (setA colors) = n;first by rewrite card_ordinal.
move: (card_image g_inj (setA (prod_finType colors colors))).
have <-: card(setA(prod_finType colors colors)) =
        (card (setA colors) * card (setA colors))%N;first by rewrite -card_prod.
have : image g (setA (prod_finType colors colors)) =1 {x : col_squares, (coin0 x == coin3 x) && (coin2 x == coin1 x)}.
 move => z;rewrite s2f;destruct z.
have: (card (setA square)=4);first by rewrite cardA /=ord_enum4.
do 4! (destruct val=>//=; first by rewrite -e=> *; discriminate).
destruct val=>//=; last by rewrite -e=> *; discriminate.
move => _;apply /idP/idP.
  case/imageP => x3  Hx3;case x3 => col1 col2;rewrite /g/=.
  case/fgraph_eqP;case/and5P=> h1 h2 h3 h4 _.
  rewrite (eqP h1)(eqP h2) (eqP h3)(eqP h4) /coin0/coin1/coin2/coin3/=.
  by apply/andP;split; rewrite /fun_of_fgraph;unlock=> /= ; rewrite ord_enum4.
 rewrite /coin1/coin0/coin2/coin3/=/fun_of_fgraph;unlock=>/=;
  rewrite ord_enum4/=.
 case/andP=> h1 h2;apply/imageP;exists (EqPair x x1) =>//=.
 by rewrite (eqP h1) (eqP h2) =>//=;apply/fgraph_eqP=>//=.
by move => h1 <-;symmetry;apply:eq_card.
Qed.

Lemma card_FSh: forall a:group (perm_finGroupType square), a  sh ->card (F to a (perm_of_inj Sh_inj))= (n*n)%N.
move => a Ha;rewrite (eq_card (F_Sh Ha)).
exact:fbicolor.
Qed.
Lemma card_FSv: forall a:group (perm_finGroupType square), a  sv ->card (F to a (perm_of_inj Sv_inj))= (n*n)%N.
move => a Ha;rewrite (eq_card (F_Sv Ha)).
exact:gbicolor.
Qed.

Definition h (sc: col_squares): col_squares:=
match sc with
| Fgraph val e => 
      match val as s return (size s = card (setA square) -> col_squares) with
        (Seq  x0 x1 x2 x3) =>fun e4 : size (Seq x0 x2 x1 x3) = card(setA square) =>
                        Fgraph (d1:=square) (val:=Seq x0 x2 x1 x3) e4
   | _=> fun _  => sc
    end e
end.

Lemma h_inj: injective h.
Proof.
move => x;destruct x.
have: (card (setA square)=4);first by rewrite cardA /=ord_enum4.
do 4! (destruct val=>//=; first by rewrite -e=> *; discriminate).
destruct val=>//=; first move =>_;last by rewrite -e=> *; discriminate.
move => y;destruct y.
have: (card (setA square)=4);first by rewrite cardA /=ord_enum4.
do 4! (destruct val; first by rewrite -e0=> *; discriminate).
destruct val; first move =>_;last by rewrite -e0=> *; discriminate.
move/fgraph_eqP=> H;case/and5P :H=>h1 h2 h3 h4 _;rewrite (eqP h1)(eqP h2 )(eqP h3) (eqP h4).
by apply/fgraph_eqP.
Qed.
Definition F1:= {x : col_squares, (coin0 x == coin2 x) && (coin1 x == coin3 x)}.
Definition F2:= {x : col_squares, (coin0 x == coin1 x) && (coin2 x == coin3 x)}.

Lemma im_h_12: image h F1 =1 F2.
Proof.
move => z;destruct z;rewrite !s2f.
 have: (card (setA square)=4);first by rewrite cardA /=ord_enum4.
do 4! (destruct val; first by rewrite -e=> *; discriminate).
destruct val; first move =>_;last by rewrite -e=> *; discriminate.
apply/idP/idP.
case/imageP=> x3;rewrite s2f;destruct x3.
 have: (card (setA square)=4);first by rewrite cardA /=ord_enum4.
do 4! (destruct val; first by rewrite -e0=> *; try discriminate).
destruct val; first move =>_;last by rewrite -e=> *; discriminate.
 rewrite /coin0/coin1/coin2/coin3/=;case/andP;rewrite/fun_of_fgraph;
  unlock=>/=;rewrite ord_enum4/=.
 do 2! (move/eqP => ->).  
 by case/fgraph_eqP;case/and5P; do 4! (move/eqP => ->); move=>_;apply/andP.
case/andP;rewrite/coin0/coin1/coin2/coin3 {1 2 3 4}/fun_of_fgraph;unlock=>/=;rewrite ord_enum4/=.
do 2! (move/eqP => ->);apply/imageP.
have h1:  size (Seq col0 col0 col0 col0) = card (setA square)=>//.
exists (Fgraph (d1:=square) (val:=Seq x0 x2 x0 x2) h1);last by apply/fgraph_eqP.
by rewrite s2f;apply/andP;rewrite /coin0/coin1/coin2/coin3;split=>//;
 rewrite /fun_of_fgraph;unlock=>/=;rewrite ord_enum4.
Qed.


Lemma card_FR2: forall a:group (perm_finGroupType square), a  r2 ->card (F to a (perm_of_inj R2_inj))= (n*n)%N.
by move => a Ha;rewrite (eq_card (F_R2 Ha)) -fbicolor
 -(card_image h_inj {x : col_squares, (coin0 x == coin2 x) && (coin1 x == coin3 x)}) (eq_card im_h_12).
Qed.

Lemma unicolor: card {x : col_squares,
           (coin0 x == coin1 x)&&(coin1 x == coin2 x)&&(coin2 x == coin3 x)}= n.
have<-: card (setA colors) = n;first by rewrite card_ordinal.
rewrite -(card_image c_inj (setA  colors));apply:eq_card.
 rewrite /coin1/coin0/coin3/coin2/=.
 move => z;rewrite s2f;destruct z.
 have: (card (setA square)=4);first by rewrite cardA /=ord_enum4.
do 4! (destruct val; first by rewrite -e=> *; try discriminate).
destruct val; first move =>_;last by rewrite -e=> *; discriminate.
 rewrite/fun_of_fgraph;unlock=>/=;rewrite ord_enum4/=.
 apply/idP/idP.
case/andP=> h1 h2;first move/andP:h1 =>[h1 h3].
 apply/imageP; exists x2 =>//.
 by rewrite (eqP h1) (eqP h3) (eqP h2)/c/=;apply/fgraph_eqP=>//=.
case/imageP =>x3 Hx3;rewrite /c/=;case/fgraph_eqP;
   case/and5P;do 4! case/eqP=> ->; move =>_/=.
apply/andP;split;last by rewrite/fun_of_fgraph;unlock.
by apply/andP;split;by rewrite /fun_of_fgraph;unlock.
Qed.

Lemma card_FR1: forall a:group (perm_finGroupType square), 
     a r1 ->card (F to a (perm_of_inj R1_inj))= n.
Proof. by move => a Ha;rewrite (eq_card (F_r1 Ha));exact:unicolor. Qed.

Lemma card_FR3: forall a:group (perm_finGroupType square), 
     a r3 ->card (F to a (perm_of_inj R3_inj))= n.
Proof. by move => a Ha;rewrite (eq_card (F_r3 Ha)); exact:unicolor. Qed.

Lemma burnside_app2: (square_coloring_number2 *2= ( n^4) + n^2)%N.
Proof.
rewrite -{1}card_iso2 -(Frobenius_Cauchy to iso2_group)(@sumD1 _ id1 )//= 
  (@sumD1 _ sh ).
 rewrite (@sum_id _ _ _ 0).
  rewrite muln0 addn0;congr addn.
   apply card_Fid; first by move/groupP:group_set_iso2;case.
 rewrite /sh card_FSh/=; first by rewrite muln1.
 by rewrite /isometries2 !s2f -/sh eq_refl  orbT.
 move => x;rewrite /F/eqtype.setD1; case/and3P=> Hx1 Hx2 Hx.
 rewrite -(card0 col_squares);apply eq_card.
 move => z. 
 apply /idP;apply/negP; apply/nandP.
left.

rewrite /isometries2 s2f.
apply/norP;split;auto.
by rewrite /setD1;apply/andP;split=>//; apply: diff_id_sh.
Qed.

Lemma burnside_app_rot: (square_coloring_number4 *4= ( n^4) + n^2 +2*n)%N.
Proof.
rewrite -{1}card_rot.
rewrite -(Frobenius_Cauchy to rot_group).
rewrite (@sumD1 _ id1 )//=(@sumD1 _ r1 )//=.
 rewrite (@sumD1 _ r2 )//=.
  rewrite (@sumD1 _ r3 )//=.
   rewrite (@sum_id _ _ _ 0).
    rewrite muln0 addn0 -!addnA ;congr addn.
     by rewrite card_Fid;last by move/groupP:group_set_rot;case.
    rewrite addnC addnA; congr addn; first congr addn.
      rewrite  card_FR2/=; first by rewrite muln1.
      by rewrite rot_is_rot /rot !s2f  eq_refl  !orbT.
     by rewrite  card_FR3//=;rewrite rot_is_rot /rot !s2f  eq_refl  !orbT.
    rewrite card_FR1/=; first by rewrite addn0.
    by rewrite rot_is_rot /rotations !s2f  eq_refl  !orbT.
   move => x;rewrite /F/eqtype.setD1.
   case/and5P=> Hx3 Hx2 Hx1 Hxid _;rewrite -(card0 col_squares).
   apply eq_card;move => z;apply /idP.
apply/negP; apply/nandP.
left.
rewrite s2f.
apply /negP.
 move => h0;have: rotations x.
by rewrite -rot_is_rot /rot s2f.
rewrite /rotations s2f.
by case /or4P=> h1 ;move:Hxid Hx1 Hx2 Hx3;rewrite -(eqP h1);
[|move =>_|move =>_ _|move=>_ _ _];case/eqP.
 rewrite /setD1;apply/and4P;repeat split;
repeat  (match goal with |- context [?x != ?y] =>apply/eqP =>heq;absurd (x c0 = y c0);
last( by rewrite heq); red; rewrite !perm_eqfun/= =>*;discriminate end).
apply/and3P;repeat split;
repeat  (match goal with |- context [?x != ?y] =>apply/eqP =>heq;absurd (x c0 = y c0);
last( by rewrite heq); red; rewrite !perm_eqfun/= =>*;discriminate end).
apply/andP;split=>//.
apply/eqP =>heq;absurd (id1 c0 = r1 c0);
last( by rewrite heq); red; rewrite !perm_eqfun/= =>*;discriminate.
 Qed.


Lemma F_S1: forall a:group (perm_finGroupType square), a  s1 ->(F to a (perm_of_inj S1_inj))=1 
{x:col_squares,(coin1 x == coin3 x)}.
rewrite /s1  => a Ha x;rewrite /F  !s2f  Ha /=   /to/=/act_f/=.
destruct x;rewrite /coin0/c0/coin1/c1/coin2/c2/coin3/c3/=.
have: (card (setA square)=4);first by rewrite cardA /=ord_enum4.
do 4! (destruct val=>//=; first by rewrite -e=> *; discriminate).
destruct val=>//=; last by rewrite -e=> *; discriminate.
move =>_;rewrite s1_inv;apply/idP/idP=>/=.
 move/eqP=>H;rewrite /s1/fun_of_fgraph/=; unlock=>/=.
rewrite ord_enum4.
simpl.


 move:H;set fff:= fgraph_of_fun _;set ggg:= Fgraph _ => H.
 have:((fun_of_fgraph fff c3) = (fun_of_fgraph ggg c3));first by rewrite H.
 rewrite /fff /ggg !can_fgraph_of_fun !perm_eqfun/= /fun_of_fgraph;unlock=>/=.
simpl.
rewrite ord_enum4;by case/eqP.
rewrite /fun_of_fgraph;unlock=>/=;rewrite ord_enum4 =>/=.
move/eqP => ->.
simpl.
apply/eqP;apply : (ff (d1:= square) (d2:= colors))=> z.
rewrite can_fgraph_of_fun/s1/= perm_eqfun;destruct z.
repeat (destruct val=>//=;first by rewrite /fun_of_fgraph;unlock=>/= ;rewrite ord_enum4).
Qed.
Definition i(col_triplet:prod_finType colors (prod_finType colors colors)) :col_squares:=
match col_triplet  with EqPair c1 c2c3 => 
  match c2c3 with EqPair c2 c3 =>
    Fgraph (d1:=ordinal 4) (val:=Seq c1 c2 c3 c2)
      (size4 c1 c2 c3 c2)
end end.

Lemma i_inj: injective i.
move => x y;destruct x as [x1 [x2 x3]]; destruct y as [y1 [y2 y3]];rewrite /i.
move/fgraph_eqP=> H;case/and5P :H=>*.
apply /eqP;repeat (apply /andP;split=>//).
Qed.



Lemma tricolor: card {x : col_squares, (coin1 x == coin3 x)}  =(n ^3)%N.
have <-: card (setA colors) = n;first by rewrite card_ordinal.
move: (card_image i_inj (setA (prod_finType colors (prod_finType colors colors)))).
have <-: card(setA(prod_finType colors(prod_finType colors colors))) = (card (setA colors) ^ 3)%N;first by  rewrite !card_prod/= muln1.

have : image i (setA (prod_finType colors (prod_finType colors colors))) =1 {x : col_squares, (coin1 x == coin3 x)}.
 move => z;rewrite s2f;destruct z.
have: (card (setA square)=4);first by rewrite cardA /=ord_enum4.
do 4! (destruct val=>//=; first by rewrite -e=> *; discriminate).
destruct val=>//=; last by rewrite -e=> *; discriminate.
move => _;apply /idP/idP.
  case/imageP => x3  Hx3;case x3 => col1 col23; case col23 => col2 col3;
rewrite /i/=.
  case/fgraph_eqP;case/and5P=> h1 h2 h3 h4 _.
  rewrite (eqP h1)(eqP h2) (eqP h3)(eqP h4) /coin0/coin1/coin2/coin3/=.
  by rewrite /fun_of_fgraph;unlock=> /= ; rewrite ord_enum4.
 rewrite /coin1/coin0/coin2/coin3/=/fun_of_fgraph;unlock=>/=;
  rewrite ord_enum4/=.
 move => h1 ;apply/imageP;exists (EqPair x (EqPair x0 x1)) =>//=.
 by rewrite (eqP h1) =>//=;apply/fgraph_eqP=>//=.
by move => h1 <-;symmetry;apply:eq_card.
Qed.

Lemma card_FS1: (card (F to iso_group s1)= n^3)%N.
have Hs1: iso_group s1;first by rewrite s2f eq_refl //= !orbT.
rewrite (eq_card (F_S1 Hs1));exact:tricolor.
Qed.

Lemma F_S2: forall a:group (perm_finGroupType square), a  s2 ->(F to a (perm_of_inj S2_inj))=1 
{x:col_squares,(coin0 x == coin2 x)}.
rewrite /s2  => a Ha x;rewrite /F  !s2f  Ha /=   /to/=/act_f/=.
destruct x;rewrite /coin0/c0/coin1/c1/coin2/c2/coin3/c3/=.
have: (card (setA square)=4);first by rewrite cardA /=ord_enum4.
do 4! (destruct val=>//=; first by rewrite -e=> *; discriminate).
destruct val=>//=; last by rewrite -e=> *; discriminate.
move =>_;rewrite s2_inv;apply/idP/idP=>/=.
 move/eqP=>H;rewrite /s2/fun_of_fgraph/=; unlock=>/=.
rewrite ord_enum4.
simpl.
 move:H;set fff:= fgraph_of_fun _;set ggg:= Fgraph _ => H.
 have:((fun_of_fgraph fff c2) = (fun_of_fgraph ggg c2));first by rewrite H.
 rewrite /fff /ggg !can_fgraph_of_fun !perm_eqfun/= /fun_of_fgraph;unlock=>/=.
simpl.
by rewrite ord_enum4;case/eqP.
rewrite /fun_of_fgraph;unlock=>/=;rewrite ord_enum4 =>/=.
move/eqP => ->.
simpl.
apply/eqP;apply : (ff (d1:= square) (d2:= colors))=> z.
rewrite can_fgraph_of_fun/s2/= perm_eqfun;destruct z.
repeat (destruct val=>//=;first by rewrite /fun_of_fgraph;unlock=>/= ;rewrite ord_enum4).
Qed.

Definition j(col_triplet:prod_finType colors (prod_finType colors colors)) :col_squares:=
match col_triplet  with EqPair c1 c2c3 => 
  match c2c3 with EqPair c2 c3 =>
    Fgraph (d1:=ordinal 4) (val:=Seq c1 c2 c1 c3)
      (size4 c1 c2 c1 c3)
end end.

Lemma j_inj: injective j.
move => x y;destruct x as [x1 [x2 x3]]; destruct y as [y1 [y2 y3]];rewrite /j.
move/fgraph_eqP=> H;case/and5P :H=>*.
apply /eqP;repeat (apply /andP;split=>//).
Qed.



Lemma jtricolor: card {x : col_squares, (coin0 x == coin2 x)}  =(n ^3)%N.
have <-: card (setA colors) = n;first by rewrite card_ordinal.
move: (card_image j_inj (setA (prod_finType colors (prod_finType colors colors)))).
have <-: card(setA(prod_finType colors(prod_finType colors colors))) = (card (setA colors) ^ 3)%N;first by  rewrite !card_prod/= muln1.

have : image j (setA (prod_finType colors (prod_finType colors colors))) =1 {x : col_squares, (coin0 x == coin2 x)}.
 move => z;rewrite s2f;destruct z.
have: (card (setA square)=4);first by rewrite cardA /=ord_enum4.
do 4! (destruct val=>//=; first by rewrite -e=> *; discriminate).
destruct val=>//=; last by rewrite -e=> *; discriminate.
move => _;apply /idP/idP.
  case/imageP => x3  Hx3;case x3 => col1 col23; case col23 => col2 col3;
rewrite /j/=.
  case/fgraph_eqP;case/and5P=> h1 h2 h3 h4 _.
  rewrite (eqP h1)(eqP h2) (eqP h3)(eqP h4) /coin0/coin1/coin2/coin3/=.
  by rewrite /fun_of_fgraph;unlock=> /= ; rewrite ord_enum4.
 rewrite /coin1/coin0/coin2/coin3/=/fun_of_fgraph;unlock=>/=;
  rewrite ord_enum4/=.
 move => h1 ;apply/imageP;exists (EqPair x (EqPair x0 x2)) =>//=.
 by rewrite (eqP h1) =>//=;apply/fgraph_eqP=>//=.
by move => h1 <-;symmetry;apply:eq_card.
Qed.

Lemma card_FS2: (card (F to iso_group s2)= n^3)%N.
have Hs2: iso_group s2;first by rewrite s2f eq_refl //= !orbT.
rewrite (eq_card (F_S2 Hs2));exact:jtricolor.
Qed.


Lemma burnside_app_iso: (square_coloring_number8 *8= ( n^4) + 2*n^3+ 3* n^2 +2*n)%N.
Proof.
have card_iso: card iso_group = 8.
rewrite  (eq_card (a:= iso_group) (b:= isometries)).
rewrite (icardD1 id1)  (icardD1 r1) (icardD1 r2) (icardD1 r3) (icardD1 sh )( icardD1 sv) (icardD1 s1) (icardD1 s2)
 /isometries/= !s2f  eq_refl !orTb;congr addn.
repeat 
 match goal with |- context [?x != ?y] => have ->: (x != y);
first by rewrite/set1/= /fgraph_of_fun; unlock;apply/negP; move/eqP;
   move/fgraph_eqP => /=;rewrite ord_enum4  end.
repeat (rewrite eq_refl  ?orbT;congr addn).
rewrite -(@eq_card _ set0 );first by apply card0.
move =>x ;rewrite !s2f.
do 8! rewrite (eq_sym x).
do 8!(case: ( _ ==x );simpl;auto).
by move => z; apply/is_isoP/is_isoP.
rewrite - card_iso -(Frobenius_Cauchy to iso_group).
rewrite (@sumD1 _ id1 )//=(@sumD1 _ r1 )//=.
 rewrite (@sumD1 _ r2 )//=.
  rewrite (@sumD1 _ r3 )//=.
   rewrite (@sumD1 _ sh )//=.
   rewrite (@sumD1 _ sv )//=.
   rewrite (@sumD1 _ s1 )//=.
   rewrite (@sumD1 _ s2 )//=.
   rewrite (@sum_id _ _ _ 0).
    rewrite muln0 addn0 -!addnA ;congr addn.
     by rewrite card_Fid;last by move/groupP:group_set_iso;case.
rewrite card_FR1;last by rewrite /isometries !s2f  eq_refl  !orbT.
rewrite card_FR2;last by rewrite /isometries !s2f  eq_refl  !orbT.
rewrite card_FR3;last by rewrite /isometries !s2f  eq_refl  !orbT.
rewrite card_FSh;last by rewrite /isometries !s2f  eq_refl  !orbT.
rewrite card_FSv;last by rewrite /isometries !s2f  eq_refl  !orbT.
rewrite card_FS1 card_FS2.
simpl.
rewrite !muln1 !add0n !addn0.
do 11!(try rewrite -!addnA; (congr addn;[idtac])||rewrite addnC =>//).
   move => x;rewrite /F/eqtype.setD1.
   case/and5P=> Hx3 Hx2 Hx1 Hxid.
 case/and5P=> Hx4 Hx5 Hx6 Hx7 _.
rewrite -(card0 col_squares).
   apply eq_card;move => z;apply /idP.
apply/negP; apply/nandP.
left.
rewrite s2f.
apply /negP.
case /or4P=> h0.
move/eqP :Hx7.
by rewrite (eqP h0).
move/eqP :Hx6;by rewrite (eqP h0).
move/eqP :Hx5;by rewrite (eqP h0).
move /orP:h0.
case => h0.
move/eqP :Hx4;by rewrite (eqP h0).
move /orP:h0;case => h0.
move/eqP :Hxid;by rewrite (eqP h0).
move /orP:h0;case => h0.
move/eqP :Hx1;by rewrite (eqP h0).
move /orP:h0;case => h0.
move/eqP :Hx2;by rewrite (eqP h0).
move/eqP :Hx3;by rewrite (eqP h0).
 rewrite /setD1;apply/and4P;repeat split;
repeat  (match goal with |- context [?x != ?y] =>apply/eqP =>heq;absurd (x c0 = y c0);
last( by rewrite heq); red; rewrite !perm_eqfun/= =>*;discriminate end).
apply/and5P;repeat split;
repeat  (match goal with |- context [?x != ?y] =>apply/eqP =>heq;absurd (x c0 = y c0);
last( by rewrite heq); red; rewrite !perm_eqfun/= =>*;discriminate end).
apply/eqP.
red=>heq.
absurd (r2 c1 = s2 c1); last( by rewrite heq); red; rewrite !perm_eqfun/= =>*;discriminate.
rewrite /setD1;apply/and4P;repeat split;
repeat  (match goal with |- context [?x != ?y] =>apply/eqP =>heq;absurd (x c0 = y c0);
last( by rewrite heq); red; rewrite !perm_eqfun/= =>*;discriminate end).
apply/and4P;repeat split;
repeat  (match goal with |- context [?x != ?y] =>apply/eqP =>heq;absurd (x c0 = y c0);
last( by rewrite heq); red; rewrite !perm_eqfun/= =>*;discriminate end).
apply/eqP =>heq;absurd (id1 c1 = s1 c1);
last( by rewrite heq); red; rewrite !perm_eqfun/= =>*;discriminate.
rewrite /setD1;apply/and5P;repeat split;
repeat  (match goal with |- context [?x != ?y] =>apply/eqP =>heq;absurd (x c0 = y c0);
last( by rewrite heq); red; rewrite !perm_eqfun/= =>*;discriminate end).
apply/eqP;red=>heq.
absurd (r3 c1 = sv c1); last( by rewrite heq); red; rewrite !perm_eqfun/= =>*;discriminate.
apply/andP;split =>//.
repeat  (match goal with |- context [?x != ?y] =>apply/eqP =>heq;absurd (x c0 = y c0);
last( by rewrite heq); red; rewrite !perm_eqfun/= =>*;discriminate end).
rewrite /setD1;apply/and4P;repeat split;
repeat  (match goal with |- context [?x != ?y] =>apply/eqP =>heq;absurd (x c0 = y c0);
last( by rewrite heq); red; rewrite !perm_eqfun/= =>*;discriminate end).
apply/eqP =>heq;absurd (r1 c1 =sh c1);
last( by rewrite heq); red; rewrite !perm_eqfun/= =>*;discriminate .
apply/andP;split =>//.
repeat  (match goal with |- context [?x != ?y] =>apply/eqP =>heq;absurd (x c0 = y c0);
last( by rewrite heq); red; rewrite !perm_eqfun/= =>*;discriminate end).
rewrite /setD1;apply/and3P;repeat split;
repeat  (match goal with |- context [?x != ?y] =>apply/eqP =>heq;absurd (x c0 = y c0);
last( by rewrite heq); red; rewrite !perm_eqfun/= =>*;discriminate end).
apply/andP;repeat split;repeat  (match goal with |- context [?x != ?y] =>apply/eqP =>heq;absurd (x c0 = y c0);
last( by rewrite heq); red; rewrite !perm_eqfun/= =>*;discriminate end).
rewrite /setD1;apply/andP;repeat split;
repeat  (match goal with |- context [?x != ?y] =>apply/eqP =>heq;absurd (x c0 = y c0);
last( by rewrite heq); red; rewrite !perm_eqfun/= =>*;discriminate end).
apply/andP;repeat split;
repeat  (match goal with |- context [?x != ?y] =>apply/eqP =>heq;absurd (x c0 = y c0);
last( by rewrite heq); red; rewrite !perm_eqfun/= =>*;discriminate end).
rewrite /setD1;apply/andP;repeat split;
repeat  (match goal with |- context [?x != ?y] =>apply/eqP =>heq;absurd (x c0 = y c0);
last( by rewrite heq); red; rewrite !perm_eqfun/= =>*;discriminate end).
 Qed.
End square_colouring.
