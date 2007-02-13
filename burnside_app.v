
Require Import ssreflect.
Require Import ssrbool.
Require Import funs.
Require Import eqtype.
Require Import ssrnat.
Require Import seq.
Require Import fintype.
Require Import connect.
Require Import groups.
Require Import baux.
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
rewrite /fun_of_perm => /=.
apply:can_fgraph_of_fun.
Qed.
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
Definition c1:= @mk4 (S O) is_true_true.
Definition c2:=@mk4 2 is_true_true.
Definition c3:=@mk4 3 is_true_true.

Definition R1 (sc : square):square :=
match sc with
| EqSig 0 _ => @mk4 (S O) is_true_true
| EqSig 1 _ => @mk4 2 is_true_true
| EqSig 2 _ => @mk4 3 is_true_true
| EqSig (S (S (S _))) _ => @mk4 0 is_true_true
end.

Definition Sh (sc : square) : square:=
match sc with
| EqSig 0 _ => @mk4 1%N is_true_true
| EqSig 1 _ => @mk4 0 is_true_true
| EqSig 2 _ => @mk4 3 is_true_true
| EqSig (S (S (S _))) _ => @mk4 2 is_true_true
end.

Lemma Sh_inj: injective Sh.
apply : (can_inj (g:= Sh)).
move => [val H1].
repeat (destruct val => //=;rewrite /mk4 /=  //;first by apply /eqP).
Qed.

Definition sh1 := (perm_of_inj Sh_inj).
Lemma sh_inv: perm_inv sh1 = sh1.
apply:(mulg_injr sh1).
rewrite mulVg /sh1.
apply:eq_fun_of_perm.
move => [ val H1].
rewrite !perm_eqfun /= /comp/= !perm_eqfun.
repeat (destruct val => //=;rewrite /mk4 /=  //;first by apply /eqP).
Qed.

Definition id1:= (perm_unit square).

(*Axiom ok: forall P,P.*)

Lemma diff_id_sh: unitg (perm_finGroupType square) != sh1.
rewrite /set1/= /fgraph_of_fun.
by unlock.
Qed.

Definition isometries :setType (perm_finType square):=  iset2 1 (perm_of_inj Sh_inj).

Lemma card_iso: card isometries = 2.
rewrite icard2.
rewrite/set1/= /fgraph_of_fun.
by unlock.
Qed.


Lemma Giso: group  isometries.
apply/groupP.
split.
by rewrite s2f eq_refl.
move => x y; rewrite !s2f.
case /orP=> H1;case/orP=> H2.
   by apply/orP;left;apply /eqP;rewrite -(eqP H2) -(eqP H1);gsimpl.
  by rewrite -(eqP H1) (eqP H2);apply/orP;right;apply /eqP;gsimpl.
 by rewrite -(eqP H2) (eqP H1);apply/orP;right;apply /eqP;gsimpl.
apply/orP;left;apply/eqP;rewrite -(eqP H2) -(eqP H1).
rewrite -/sh1 -{1}sh_inv.
by rewrite mulVg.
Qed.


Definition col_squares: finType :=fgraph_finType  square  colors.
Definition  act_f4(sc: col_squares ) (perm:perm_square) :col_squares:= 
let cs:= fun_of_fgraph sc in let : permf := fun_of_perm (perm_inv perm) in 
fgraph_of_fun ( fun z => cs (permf z)).

Theorem ff: forall (d1 d2: finType) x1 x2,
(fun_of_fgraph (x:= d1) (x0 := d2) x1) =1 (fun_of_fgraph x2)  -> x1 = x2.
Proof.
move => d1 d2 x1 x2 H.
rewrite -(can_fun_of_fgraph x1) -(can_fun_of_fgraph x2).
apply: fval_inj.
unlock fgraph_of_fun.
exact: (eq_maps H).
Qed.

Lemma act_f_1:  forall x , act_f4 x 1 = x.
move => x.
rewrite /act_f4.
apply:ff.
move => y.
rewrite can_fgraph_of_fun.
have -> : (@perm_inv  square 1) = 1.
exact :invg1.
by rewrite perm_eqfun.
Qed.

 Lemma act_f_morph:          forall x y z, act_f4 z (x * y) = act_f4 (act_f4 z x) y.
move => x y z;rewrite /act_f4/=.
apply :(ff (d1:= square) (d2:= colors)).
move => t.
rewrite !(can_fgraph_of_fun (d1:= square) (d2:= colors)).
have ->: (@perm_inv square (x*y))= (perm_inv y)*(perm_inv x).
exact:invg_mul.
by rewrite perm_eqfun /comp.
Qed.

Definition to := Action  act_f_1 act_f_morph.

Definition square_coloring_number := t to isometries.

Infix "^":= expn : dnat_scope.

Lemma Fid: (F to isometries 1)=1 (setA col_squares).
move => x;apply eqb_imp;rewrite /F//.
move => _.
apply/andP;split =>/=.
by rewrite s2f eq_refl.
by rewrite act_f_1.
Qed.

Lemma card_Fid :card (F to isometries id1) = (n ^ 4)%N.
rewrite (eq_card Fid) /col_squares.
have <- : card (setA square) = 4; first by rewrite cardA.
have <-: card (setA colors)=n;first by rewrite card_ordinal.
rewrite -card_tfunspace; apply: eq_card=> f; symmetry.
move: (@fgraph_prodP square colors col0  (fun _ : nat => setA colors)f ) => h.
apply/h =>//=.
Qed.

(*
Lemma card_Fsh : card (F to isometries sh1) = (n ^ 2)%N.*)
Definition coin0(sc : col_squares) : colors:=(fun_of_fgraph sc) c0.
Definition coin1' (sc : col_squares) : colors:=
match sc with
| Fgraph val proof =>
    match val
    with
   | Adds x1 (Adds x2 (Adds x3 (Seq x4))) => x1
   |_=>  col0 end end.
Definition coin1(sc : col_squares) : colors:=(fun_of_fgraph sc) c1.
Definition coin2(sc : col_squares) : colors:=(fun_of_fgraph sc) c2.
Definition coin3(sc : col_squares) : colors:=(fun_of_fgraph sc) c3.

Definition coin2' (sc : col_squares) : colors:=
match sc with
| Fgraph val proof =>
    match val
    with
   | Adds x1 (Adds x2 (Adds x3 (Seq x4))) => x2
   |_=>  col0 end end.
Definition coin3'(sc : col_squares) : colors:=
match sc with
| Fgraph val proof =>
    match val
    with
   | Adds x1 (Adds x2 (Adds x3 (Seq x4))) => x3
   |_=>  col0 end end.

Definition coin4' (sc : col_squares) : colors:=
match sc with
| Fgraph val proof =>
    match val
    with
   | Adds x1 (Adds x2 (Adds x3 (Seq x4))) => x4
   |_=>  col0 end end.

Lemma F_Sh: (F to isometries (perm_of_inj Sh_inj))=1 
{x:col_squares, (coin0 x == coin1 x) &&(coin2 x == coin3 x)}.
move => x;rewrite /F.
rewrite /isometries.
rewrite !s2f eq_refl orbT andTb  /to/=/act_f4/=.
destruct x.
rewrite /coin0/c0/coin1/c1/coin2/c2/coin3/c3/=.
do 4! destruct val=>//.
rewrite sh_inv.
apply/idP/idP.
simpl.
move/eqP=> H.
rewrite /fun_of_fgraph/=; unlock=>/=.
move:H.
set f:= fgraph_of_fun _.
set g:= Fgraph _.
move => H.
have:((fun_of_fgraph f( @mk4 0 is_true_true)) = (fun_of_fgraph g  ( @mk4 0 is_true_true))).
by rewrite H.
have:((fun_of_fgraph f( @mk4 2 is_true_true)) = (fun_of_fgraph g  ( @mk4 2 is_true_true))).
by rewrite H.
rewrite /f /g/sh1.
rewrite !can_fgraph_of_fun !perm_eqfun/= /fun_of_fgraph;unlock=>/=.
by move=> -> ->;apply/andP;split;done.
rewrite {1 2 3 4}/fun_of_fgraph;unlock=>/=.
case/andP=> h0 h1.
rewrite (eqP h0 ) (eqP h1).
apply/eqP;apply : (ff (d1:= square) (d2:= colors)).
move=>z.
rewrite can_fgraph_of_fun/sh1/= perm_eqfun.
destruct z.
repeat (destruct val0=>//=;
first by rewrite /fun_of_fgraph;unlock=>/=).
Qed.


Definition f(col_pair:prod_finType colors colors) :col_squares:=
match col_pair  with EqPair c1 c2 => 
    Fgraph (d1:=ordinal 4) (val:=Seq c1 c1 c2 c2)
      (refl_equal (card (setA (ordinal 4))))
end.

Lemma f_inj: injective f.
move => x y.
destruct x; destruct y.
rewrite /f.
move/fgraph_eqP=> H.
case/and5P :H.
move=>*.
by apply /eqP;apply /andP;split.
Qed.


Lemma card_FSh: card (F to isometries (perm_of_inj Sh_inj))= (n*n)%N.
rewrite (eq_card F_Sh).

Print bij_eq_card.
Print card_image.
have: card (setA colors) = n.
by rewrite card_ordinal.
move => <-.
move: (card_image f_inj (setA (prod_finType colors colors))).
Print card_prod.
have : card (setA (prod_finType colors colors)) = 
(card (setA colors) * card (setA colors))%N.
by rewrite -card_prod.
move => <-.
have : image f (setA (prod_finType colors colors)) =1 {x : col_squares, (coin0 x == coin1 x) && (coin2 x == coin3 x)}.

move => z.
rewrite s2f.
(*apply eqb_imp.
case/imageP.
destruct x.

move => _.*)
destruct z.
destruct val;try discriminate.
destruct val;try discriminate.
destruct val;try discriminate.
destruct val;try discriminate.
destruct val;try discriminate.
apply eqb_imp.
case/imageP.
move => x3 Hx3.
case x3 => col1 col2.


rewrite /f.
simpl.
move => H;inversion H.

auto.
simpl.
 apply/andP;split.
rewrite /coin1/coin0.
simpl.
rewrite /fun_of_fgraph.
by unlock.
rewrite /coin2/coin3/=.
by rewrite /fun_of_fgraph;unlock.
simpl.
rewrite /coin1/coin0/coin2/coin3/=.
rewrite /fun_of_fgraph;unlock=>/=.
case/andP=> h1 h2.
apply/imageP.

exists (EqPair x x1).
auto.
rewrite (eqP h1) (eqP h2);auto.

rewrite /f.
apply/fgraph_eqP.
simpl.
auto.

move => h1 <-.
symmetry.

by apply:eq_card.
Qed.


Lemma burnside_app1: (square_coloring_number *2= ( n^4) + n^2)%N.

rewrite -{1}card_iso.
rewrite -(Frobenius_Cauchy to Giso).
rewrite (@sumD1 _ id1 )//= (@sumD1 _ sh1 ).
rewrite (@sum_id _ _ _ 0).
rewrite muln0 addn0;congr addn.
apply card_Fid.
by rewrite /sh1 card_FSh/= muln1.

move => x;rewrite /F/eqtype.setD1.
case/and3P=> Hx1 Hx2 Hx.
 rewrite -(card0 col_squares).
apply eq_card.
move => z.
apply eqb_imp.
case/andP.
rewrite /isometries s2f.
case/orP=> h1 h2.
move : Hx2.
by rewrite -(eqP h1)  /set1/= /fgraph_of_fun; unlock.
by move : Hx1;rewrite -(eqP h1) /set1/= /fgraph_of_fun;by unlock.
move=> hh;discriminate.
rewrite /setD1.
apply/andP;split=>//.
by apply: diff_id_sh.
Qed.
