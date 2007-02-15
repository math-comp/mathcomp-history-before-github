
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

Definition R2 (sc : square):square :=
match sc with
| EqSig 0 _ => @mk4 2 is_true_true
| EqSig 1 _ => @mk4 3 is_true_true
| EqSig 2 _ => @mk4 0 is_true_true
| EqSig (S (S (S _))) _ => @mk4 1%N is_true_true
end.
Definition R3 (sc : square):square :=
match sc with
| EqSig 0 _ => @mk4 3 is_true_true
| EqSig 1 _ => @mk4 0 is_true_true
| EqSig 2 _ => @mk4 1%N is_true_true
| EqSig (S (S (S _))) _ => @mk4 2 is_true_true
end.
Lemma R1_inj: injective R1.
apply : (can_inj (g:= R3)).
move => [val H1].
repeat (destruct val => //=;rewrite /mk4 /=  //;first by apply /eqP).
Qed.

Lemma R2_inj: injective R2.
apply : (can_inj (g:= R2)).
move => [val H1].
repeat (destruct val => //=;rewrite /mk4 /=  //;first by apply /eqP).
Qed.
Lemma R3_inj: injective R3.
apply : (can_inj (g:= R1)).
move => [val H1].
repeat (destruct val => //=;rewrite /mk4 /=  //;first by apply /eqP).
Qed.

Definition r1 := (perm_of_inj R1_inj).
Definition r2 := (perm_of_inj R2_inj).
Definition r3 := (perm_of_inj R3_inj).
Lemma r1_inv: perm_inv r1 = r3.
apply:(mulg_injr r1).
rewrite mulVg /r3/r1.
apply:eq_fun_of_perm.
move => [ val H1].
rewrite !perm_eqfun /= /comp/= !perm_eqfun.
repeat (destruct val => //=;rewrite /mk4 /=  //;first by apply /eqP).
Qed.
Lemma r2_inv: perm_inv r2 = r2.
apply:(mulg_injr r2).
rewrite mulVg /r2.
apply:eq_fun_of_perm.
move => [ val H1].
rewrite !perm_eqfun /= /comp/= !perm_eqfun.
repeat (destruct val => //=;rewrite /mk4 /=  //;first by apply /eqP).
Qed.
Lemma r3_inv: perm_inv r3 = r1.
apply:(mulg_injr r3).
rewrite mulVg /r1.
apply:eq_fun_of_perm.
move => [ val H1].
rewrite !perm_eqfun /= /comp/= !perm_eqfun.
repeat (destruct val => //=;rewrite /mk4 /=  //;first by apply /eqP).
Qed.

Lemma r1_r1 : r2= r1*r1.
apply:eq_fun_of_perm.
move => [ val H1].
rewrite  !perm_eqfun /= /comp/= !perm_eqfun/R1/=.
repeat (destruct val => //=;rewrite /mk4 /=  //).
Qed.

Lemma r1_r2 : r3= r1*r2.
apply:eq_fun_of_perm.
move => [ val H1].
rewrite  !perm_eqfun /= /comp/= !perm_eqfun/R1/=.
repeat (destruct val => //=;rewrite /mk4 /=  //).
Qed.
Lemma r2_r1 : r3= r2*r1.
apply:eq_fun_of_perm.
move => [ val H1].
rewrite  !perm_eqfun /= /comp/= !perm_eqfun/R1/=.
repeat (destruct val => //=;rewrite /mk4 /=  //).
Qed.
Lemma r2_r3 : r1= r2*r3.
apply:eq_fun_of_perm.
move => [ val H1].
rewrite  !perm_eqfun /= /comp/= !perm_eqfun/R1/=.
repeat (destruct val => //=;rewrite /mk4 /=  //).
Qed.
Lemma r3_r2 : r1= r3*r2.
apply:eq_fun_of_perm.
move => [ val H1].
rewrite  !perm_eqfun /= /comp/= !perm_eqfun/R1/=.
repeat (destruct val => //=;rewrite /mk4 /=  //).
Qed.
Lemma r3_r3 : r2= r3*r3.
apply:eq_fun_of_perm.
move => [ val H1].
rewrite  !perm_eqfun /= /comp/= !perm_eqfun/R1/=.
repeat (destruct val => //=;rewrite /mk4 /=  //).
Qed.
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

Definition isometries2 :setType (perm_finType square):=  iset2 1 (perm_of_inj Sh_inj).

Lemma card_iso2: card isometries2 = 2.
rewrite icard2.
rewrite/set1/= /fgraph_of_fun.
by unlock.
Qed.


Lemma Giso: group  isometries2.
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

Definition rotations:setType (perm_finType square):= iset4 id1 r1 r2 r3.
Ltac magic := 
   match goal with h:?x==_=true|- _ => move:h ; 
        match goal with h1:?y==_=true|- _ => move=> h ;
      let hh := fresh " hh" in
      (have hh: (x==y)=false ; first (by rewrite /set1/= /fgraph_of_fun;unlock) ; 
       rewrite (eqP h1) h  in hh) end end.

Lemma card_rot0: card rotations = 4.
rewrite -(@eq_card _ (set4 id1 r1 r2 r3));last by move=>y; rewrite s2f.
rewrite (cardD1 id1).
change 4 with (1+3);congr addn.
rewrite /set4;by rewrite eq_refl.
rewrite -(@eq_card _ (set3  r1 r2 r3)).
rewrite (cardD1 r1).
change 3 with (1+2);congr addn.
by rewrite /set3  eq_refl.
rewrite -(@eq_card _ (set2   r2 r3)).
rewrite (cardD1 r2).
change 2 with (1+1);congr addn.
rewrite /set2;by rewrite eq_refl.
rewrite -(@eq_card _ (set1   r3)).
apply:card1.
move => x;rewrite /setD1 /set2.
case e1: (r3 == x);case e2:(r2 == x)=> //; by magic.
move => x;rewrite /setD1 /set2/set3.
case e2: (r2 == x);case e3:(r3 == x) ; case e1:(r1 == x) => //; by magic.
move => x;rewrite /setD1 /set3/set4.
case e2: (r2 == x);case e3:(r3 == x) ; case e1:(r1 == x) ;case e0: (id1==x)=> //; by magic.
Qed.

Lemma card_rot: card rotations = 4.
Proof.
rewrite (icardD1 id1)  (icardD1 r1) (icardD1 r2) (icardD1 r3)  /rotations/= !s2f  eq_refl !orTb;congr addn.
have ->: (id1 != r1);first by rewrite /set1/= /fgraph_of_fun;unlock.
rewrite andTb  eq_refl orTb orbT;congr addn.
have ->: (r1 != r2); first by rewrite /set1/= /fgraph_of_fun;unlock.
rewrite andTb.
have ->: (id1 != r2); first by rewrite /set1/= /fgraph_of_fun;unlock.
rewrite andTb eq_refl  !orTb !orbT;congr addn.
have ->: (r2 != r3); first by rewrite /set1/= /fgraph_of_fun;unlock.
rewrite andTb.
have ->: (r1 != r3); first by rewrite /set1/= /fgraph_of_fun;unlock.
rewrite andTb.
have ->: (id1 != r3); first by rewrite /set1/= /fgraph_of_fun;unlock.
rewrite andTb eq_refl  !orbT;congr addn.
rewrite -(@eq_card _ set0 );first by apply card0.
move => x;rewrite !s2f;case e3: (r3 == x)=>//.
case e2: (r2 == x)=>//.
case e1: (r1 == x)=>//.
case e0: (id1 == x)=>//.
Qed.

Lemma Grot: group  rotations.
apply/groupP.
split.
by rewrite s2f eq_refl.
move => x y; rewrite !s2f.
case /or4P=>H1;case/or4P=> H2;  rewrite -(eqP H1) -(eqP H2);
try ( rewrite mul1g eq_refl   ?orbT ?orTb;done); try ( rewrite mulg1 eq_refl ?orbT ?orTb;done).
by rewrite  r1_r1 eq_refl   ?orbT.
by rewrite  r1_r2 eq_refl   ?orbT.
by rewrite -r1_inv mulgV eq_refl   ?orbT ?orTb.
by rewrite  r2_r1 eq_refl   ?orbT.
by rewrite -{1}r2_inv  mulVg eq_refl   ?orbT ?orTb.
by rewrite r2_r3 eq_refl ?orbT ?orTb.
by rewrite -r3_inv mulgV   eq_refl ?orbT ?orTb.
by rewrite r3_r2  eq_refl ?orbT ?orTb.
by rewrite r3_r3  eq_refl ?orbT ?orTb.
Qed.

Theorem ff: forall (d1 d2: finType) x1 x2,
(fun_of_fgraph (x:= d1) (x0 := d2) x1) =1 (fun_of_fgraph x2)  -> x1 = x2.
Proof.
move => d1 d2 x1 x2 H.
rewrite -(can_fun_of_fgraph x1) -(can_fun_of_fgraph x2).
apply: fval_inj.
unlock fgraph_of_fun.
exact: (eq_maps H).
Qed.

Definition col_squares: finType :=fgraph_finType  square  colors.
Definition  act_f(sc: col_squares ) (perm:perm_square) :col_squares:= 
let cs:= fun_of_fgraph sc in let : permf := fun_of_perm (perm_inv perm) in 
fgraph_of_fun ( fun z => cs (permf z)).


Lemma act_f_1:  forall x , act_f x 1 = x.
move => x.
rewrite /act_f.
apply:ff.
move => y.
rewrite can_fgraph_of_fun.
have -> : (@perm_inv  square 1) = 1.
exact :invg1.
by rewrite perm_eqfun.
Qed.

 Lemma act_f_morph:          forall x y z, act_f z (x * y) = act_f (act_f z x) y.
move => x y z;rewrite /act_f/=.
apply :(ff (d1:= square) (d2:= colors)).
move => t.
rewrite !(can_fgraph_of_fun (d1:= square) (d2:= colors)).
have ->: (@perm_inv square (x*y))= (perm_inv y)*(perm_inv x).
exact:invg_mul.
by rewrite perm_eqfun /comp.
Qed.

Definition to := Action  act_f_1 act_f_morph.

Definition square_coloring_number2 := t to isometries2.
Definition square_coloring_number4 := t to rotations.

Infix "^":= expn : dnat_scope.

Lemma Fid0: (F to isometries2 1)=1 (setA col_squares).
move => x;apply eqb_imp;rewrite /F//.
move => _.
apply/andP;split =>/=.
by rewrite s2f eq_refl.
by rewrite act_f_1.
Qed.

Lemma Fid:forall a:setType(perm_finType square), group a -> (F to a 1)=1 (setA col_squares).
move => a Ha x;apply eqb_imp;rewrite/F//.
move => _.
apply/andP;split =>//=.
by move/groupP: Ha => [H1 H2].
by rewrite act_f_1.
Qed.

Lemma card_Fid0 :card (F to isometries2 id1) = (n ^ 4)%N.
rewrite (eq_card Fid0) /col_squares.
have <- : card (setA square) = 4; first by rewrite cardA.
have <-: card (setA colors)=n;first by rewrite card_ordinal.
rewrite -card_tfunspace; apply: eq_card=> f; symmetry.
move: (@fgraph_prodP square colors col0  (fun _ : nat => setA colors)f ) => h.
apply/h =>//=.
Qed.

Lemma card_Fid :forall a, group a -> card (F to a id1) = (n ^ 4)%N.
move => a Ha;rewrite (eq_card (Fid Ha)) /col_squares.
have <- : card (setA square) = 4; first by rewrite cardA.
have <-: card (setA colors)=n;first by rewrite card_ordinal.
rewrite -card_tfunspace; apply: eq_card=> f; symmetry.
move: (@fgraph_prodP square colors col0  (fun _ : nat => setA colors)f ) => h.
apply/h =>//=.
Qed.

Definition coin0(sc : col_squares) : colors:=(fun_of_fgraph sc) c0.
Definition coin1(sc : col_squares) : colors:=(fun_of_fgraph sc) c1.
Definition coin2(sc : col_squares) : colors:=(fun_of_fgraph sc) c2.
Definition coin3(sc : col_squares) : colors:=(fun_of_fgraph sc) c3.

Lemma F_Sh2: (F to isometries2 (perm_of_inj Sh_inj))=1 
{x:col_squares, (coin0 x == coin1 x) &&(coin2 x == coin3 x)}.
move => x;rewrite /F  /isometries2  !s2f eq_refl orbT andTb  /to/=/act_f/=.
destruct x;rewrite /coin0/c0/coin1/c1/coin2/c2/coin3/c3/=.
do 4! destruct val=>//.
rewrite sh_inv;apply/idP/idP=>/=.
 move/eqP=> H;rewrite /fun_of_fgraph/=; unlock=>/=.
 move:H;set f:= fgraph_of_fun _;set g:= Fgraph _ =>H.
 have:((fun_of_fgraph f c0) = (fun_of_fgraph g c0));first by rewrite H.
 have:((fun_of_fgraph f c2) = (fun_of_fgraph g c2));first by rewrite H.
 rewrite /f /g/sh1 !can_fgraph_of_fun !perm_eqfun/= /fun_of_fgraph;unlock=>/=.
 by move=> -> ->;apply/andP;split;done.
rewrite {1 2 3 4}/fun_of_fgraph;unlock=>/=.
case/andP=> h0 h1;rewrite (eqP h0)(eqP h1);
apply/eqP;apply :(ff (d1:= square) (d2:= colors))=> z.
rewrite can_fgraph_of_fun/sh1/= perm_eqfun;
destruct z;repeat (destruct val0=>//=;first by rewrite /fun_of_fgraph;unlock=>/=).
Qed.

Lemma F_r2: (F to rotations (perm_of_inj R2_inj))=1 
{x:col_squares, (coin0 x == coin2 x) &&(coin1 x == coin3 x)}.
move => x;rewrite /F /rotations !s2f eq_refl !orbT andTb  /to/=/act_f/=.
destruct x;rewrite /coin0/c0/coin1/c1/coin2/c2/coin3/c3/=.
do 4! destruct val=>//.
rewrite r2_inv;apply/idP/idP=>/=.
 move/eqP=> H;rewrite /fun_of_fgraph/=; unlock=>/=.
 move:H;set f:= fgraph_of_fun _;set g:= Fgraph _ => H. 
 have:((fun_of_fgraph f c0) = (fun_of_fgraph g c0));first by rewrite H.
 have:((fun_of_fgraph f c1) = (fun_of_fgraph g c1));first by rewrite H.
 rewrite /f /g/r2 !can_fgraph_of_fun !perm_eqfun/= /fun_of_fgraph;unlock=>/=.
 by move=> -> ->;apply/andP;split.
rewrite {1 2 3 4}/fun_of_fgraph;unlock=>/=.
case/andP=> h0 h1;rewrite (eqP h0 ) (eqP h1);
apply/eqP;apply : (ff (d1:= square) (d2:= colors)) => z.
rewrite can_fgraph_of_fun/sh1/= perm_eqfun;destruct z.
repeat (destruct val0=>//=;first by rewrite /fun_of_fgraph;unlock=>/=).
Qed.

Lemma F_r1: (F to rotations (perm_of_inj R1_inj))=1 
{x:col_squares,(coin0 x == coin1 x)&&(coin1 x == coin2 x)&&(coin2 x == coin3 x)}.
move => x;rewrite /F /rotations !s2f eq_refl orbT andTb  /to/=/act_f/=.
destruct x;rewrite /coin0/c0/coin1/c1/coin2/c2/coin3/c3/=.
do 4! destruct val=>//.
rewrite r1_inv;apply/idP/idP=>/=.
 move/eqP=> H;rewrite /fun_of_fgraph/=; unlock=>/=.
 move:H;set f:= fgraph_of_fun _;set g:= Fgraph _ => H.
 have:((fun_of_fgraph f c0) = (fun_of_fgraph g c0));first by rewrite H.
 have:((fun_of_fgraph f c1) = (fun_of_fgraph g c1));first by rewrite H.
 have:((fun_of_fgraph f c2) = (fun_of_fgraph g c2));first by rewrite H.
 rewrite /f /g/r1 !can_fgraph_of_fun !perm_eqfun/= /fun_of_fgraph;unlock=>/=.
 by move=> -> -> -> ;apply/andP;split =>//;apply/andP;split.
rewrite {1 2 3 4 5 6}/fun_of_fgraph;unlock=>/=.
case/andP=> h0 h1; move/andP: h0=> [h0 h2];rewrite (eqP h0 ) (eqP h2) (eqP h1).
apply/eqP;apply : (ff (d1:= square) (d2:= colors))=> z.
rewrite can_fgraph_of_fun/r3/= perm_eqfun;destruct z.
repeat (destruct val0=>//=;first by rewrite /fun_of_fgraph;unlock=>/=).
Qed.

Lemma F_r3: (F to rotations (perm_of_inj R3_inj))=1 
{x:col_squares,(coin0 x == coin1 x)&&(coin1 x == coin2 x)&&(coin2 x == coin3 x)}.
move => x;rewrite /F /rotations !s2f eq_refl !orbT andTb  /to/=/act_f/=.
destruct x;rewrite /coin0/c0/coin1/c1/coin2/c2/coin3/c3/=.
do 4! destruct val=>//.
rewrite r3_inv;apply/idP/idP=>/=.
 move/eqP=> H;rewrite /fun_of_fgraph/=; unlock=>/=.
 move:H;set f:= fgraph_of_fun _;set g:= Fgraph _ => H.
 have:((fun_of_fgraph f c0) = (fun_of_fgraph g c0));first by rewrite H.
 have:((fun_of_fgraph f c1) = (fun_of_fgraph g c1));first by rewrite H.
 have:((fun_of_fgraph f c2) = (fun_of_fgraph g c2));first by rewrite H.
 rewrite /f /g/r3 !can_fgraph_of_fun !perm_eqfun/= /fun_of_fgraph;unlock=>/=.
 by move=> -> -> -> ;apply/andP;split =>//;apply/andP;split.
rewrite {1 2 3 4 5 6}/fun_of_fgraph;unlock=>/=.
case/andP=> h0 h1; move/andP: h0=> [h0 h2];rewrite (eqP h0 ) (eqP h2) (eqP h1).
apply/eqP;apply : (ff (d1:= square) (d2:= colors))=> z.
rewrite can_fgraph_of_fun/r3/= perm_eqfun;destruct z.
repeat (destruct val0=>//=;first by rewrite /fun_of_fgraph;unlock=>/=).
Qed.

Definition f(col_pair:prod_finType colors colors) :col_squares:=
match col_pair  with EqPair c1 c2 => 
    Fgraph (d1:=ordinal 4) (val:=Seq c1 c1 c2 c2)
      (refl_equal (card (setA (ordinal 4))))
end.

Lemma f_inj: injective f.
move => x y;destruct x; destruct y;rewrite /f.
move/fgraph_eqP=> H;case/and5P :H=>*.
by apply /eqP;apply /andP;split.
Qed.

Definition g(col_pair:prod_finType colors colors) :col_squares:=
match col_pair  with EqPair c1 c2 => 
    Fgraph (d1:=ordinal 4) (val:=Seq c1 c2 c1 c2)
      (refl_equal (card (setA (ordinal 4))))
end.

Lemma g_inj: injective g.
move => x y;destruct x; destruct y;rewrite /f.
move/fgraph_eqP=> H;case/and5P :H=>*.
by apply /eqP;apply /andP;split.
Qed.

Definition c(col:colors) :col_squares:=
    Fgraph (d1:=ordinal 4) (val:=Seq col col col col)
      (refl_equal (card (setA (ordinal 4)))).

Lemma c_inj: injective c.
Proof.
move => x y.;destruct x; destruct y;rewrite /f.
move/fgraph_eqP=> H;case/and5P :H=>*.
by apply /eqP.
Qed.

Lemma card_FSh2: card (F to isometries2 (perm_of_inj Sh_inj))= (n*n)%N.
rewrite (eq_card F_Sh2).
have <-: card (setA colors) = n;first by rewrite card_ordinal.
move: (card_image f_inj (setA (prod_finType colors colors))).
have <-: card(setA(prod_finType colors colors)) =
        (card (setA colors) * card (setA colors))%N;first by rewrite -card_prod.
have : image f (setA (prod_finType colors colors)) =1 {x : col_squares, (coin0 x == coin1 x) && (coin2 x == coin3 x)}.
 move => z;rewrite s2f;destruct z.
 do 5! (destruct val;try discriminate);apply eqb_imp.
  case/imageP => x3  Hx3;case x3 => col1 col2;rewrite /f/=.
  case/fgraph_eqP;case/and5P=> h1 h2 h3 h4 _.
  rewrite (eqP h1)(eqP h2) (eqP h3)(eqP h4) /coin0/coin1/coin2/coin3/=.
  by apply/andP;split;by rewrite /fun_of_fgraph;unlock.
 rewrite /coin1/coin0/coin2/coin3/=/fun_of_fgraph;unlock=>/=.
 case/andP=> h1 h2;apply/imageP;exists (EqPair x x1) =>//=.
 by rewrite (eqP h1) (eqP h2) =>//=;apply/fgraph_eqP=>//=.
by move => h1 <-;symmetry;apply:eq_card.
Qed.

Lemma card_Fr2: card (F to rotations (perm_of_inj R2_inj))= (n*n)%N.
rewrite (eq_card F_r2).
have <-: card (setA colors) = n;first by rewrite card_ordinal.
move: (card_image g_inj (setA (prod_finType colors colors))).
have <-: card(setA(prod_finType colors colors)) =
        (card (setA colors) * card (setA colors))%N;first by rewrite -card_prod.
have : image g (setA (prod_finType colors colors)) =1 {x : col_squares, (coin0 x == coin2 x) && (coin1 x == coin3 x)}.
 move => z;rewrite s2f;destruct z.
 do 5! (destruct val;try discriminate);apply eqb_imp.
  case/imageP => x3  Hx3;case x3 => col1 col2;rewrite /g/=.
  case/fgraph_eqP;case/and5P=> h1 h2 h3 h4 _.
  rewrite (eqP h1)(eqP h2) (eqP h3)(eqP h4) /coin0/coin1/coin2/coin3/=.
  by apply/andP;split; rewrite /fun_of_fgraph;unlock=>/=.
 rewrite /coin1/coin0/coin2/coin3/=/fun_of_fgraph;unlock=>/=.
 case/andP=> h1 h2;apply/imageP;exists (EqPair x x2) =>//=.
 rewrite (eqP h1) (eqP h2) =>//=;apply/fgraph_eqP=>//=.
by move => h1 <-;symmetry;apply:eq_card.
Qed.

Lemma card_FR1: card (F to rotations (perm_of_inj R1_inj))= n.
Proof.
rewrite (eq_card F_r1).
have<-: card (setA colors) = n;first by rewrite card_ordinal.
rewrite -(card_image c_inj (setA  colors)).
have : image c (setA colors) =1 {x : col_squares, (coin0 x == coin1 x) && (coin1 x == coin2 x)&& (coin2 x == coin3 x)}.
 move => z;rewrite s2f;destruct z;do 5!(destruct val;try discriminate).
 apply/idP/idP. 
  case/imageP =>x3 Hx3;rewrite /c/=.
  case/fgraph_eqP;case/and5P.
  do 4! case/eqP=> ->.
  move =>_/=.
  rewrite /coin1/coin0/coin3/coin2/=.
  apply/andP;split;last by rewrite/fun_of_fgraph;unlock.
  apply/andP;split;  by rewrite /fun_of_fgraph;unlock.
   rewrite /coin1/coin0/coin3/coin2/fun_of_fgraph;unlock=>/=.
 case/andP=> h1 h2;first move/andP:h1 =>[h1 h3].
 apply/imageP.
 exists x2;first by done.
 rewrite (eqP h1) (eqP h3) (eqP h2)/c/=.
 by apply/fgraph_eqP=>//=.
by move => h1;symmetry; apply:eq_card.
Qed.

Lemma card_FR3: card (F to rotations (perm_of_inj R3_inj))= n.
Proof.
rewrite (eq_card F_r3).
have<-: card (setA colors) = n;first by rewrite card_ordinal.
rewrite -(card_image c_inj (setA  colors)).
have : image c (setA colors) =1 {x : col_squares, (coin0 x == coin1 x) && (coin1 x == coin2 x)&& (coin2 x == coin3 x)}.
 move => z;rewrite s2f;destruct z;do 5!(destruct val;try discriminate).
 apply/idP/idP. 
  case/imageP =>x3 Hx3;rewrite /c/=.
  case/fgraph_eqP;case/and5P.
  do 4! case/eqP=> ->.
  move =>_/=.
  rewrite /coin1/coin0/coin3/coin2/=.
  apply/andP;split;last by rewrite/fun_of_fgraph;unlock.
  apply/andP;split;  by rewrite /fun_of_fgraph;unlock.
   rewrite /coin1/coin0/coin3/coin2/fun_of_fgraph;unlock=>/=.
 case/andP=> h1 h2;first move/andP:h1 =>[h1 h3].
 apply/imageP.
 exists x2;first by done.
 rewrite (eqP h1) (eqP h3) (eqP h2)/c/=.
 by apply/fgraph_eqP=>//=.
by move => h1;symmetry; apply:eq_card.
Qed.

Lemma burnside_app2: (square_coloring_number2 *2= ( n^4) + n^2)%N.
Proof.
rewrite -{1}card_iso2.
rewrite -(Frobenius_Cauchy to Giso).
rewrite (@sumD1 _ id1 )//= (@sumD1 _ sh1 ).
 rewrite (@sum_id _ _ _ 0).
  rewrite muln0 addn0;congr addn.
   by apply (card_Fid Giso).
  by rewrite /sh1 card_FSh2/= muln1.
 move => x;rewrite /F/eqtype.setD1.
 case/and3P=> Hx1 Hx2 Hx.
 rewrite -(card0 col_squares);apply eq_card.
 move => z;apply eqb_imp.
  case/andP;rewrite /isometries2 s2f.
  case/orP=> h1 h2.
   by move : Hx2; rewrite -(eqP h1)  /set1/= /fgraph_of_fun; unlock.
  move : Hx1;rewrite -(eqP h1)-/sh1/fgraph_of_fun; unlock.
by case/eqP;rewrite /fun_of_fgraph;unlock.
by move=>*;discriminate.
rewrite /setD1.
apply/andP;split=>//.
by apply: diff_id_sh.
Qed.

Lemma burnside_app_rot: (square_coloring_number4 *4= ( n^4) + n^2 +2*n)%N.
Proof.
rewrite -{1}card_rot.
rewrite -(Frobenius_Cauchy to Grot).
rewrite (@sumD1 _ id1 )//=(@sumD1 _ r1 )//=.
 rewrite (@sumD1 _ r2 )//=.
rewrite (@sumD1 _ r3 )//=.
rewrite (@sum_id _ _ _ 0).
rewrite muln0 addn0 -!addnA ;congr addn.
by rewrite (card_Fid Grot).
rewrite addnC addnA.
congr addn; first congr addn.
rewrite /r2.
by rewrite  card_Fr2/= muln1.
by rewrite  card_FR3/=.
by rewrite card_FR1/= addn0.
move => x;rewrite /F/eqtype.setD1.
case/and5P=> Hx3 Hx2 Hx1 Hxid _.
 rewrite -(card0 col_squares).
apply eq_card.
move => z.
apply eqb_imp.
case/andP.
rewrite /rotations s2f.
case/or4P=> h1 h2.
move : Hxid.
 by rewrite -(eqP h1) /set1/= /fgraph_of_fun; unlock =>/=.
by move : Hx1;rewrite -(eqP h1) /set1/= /fgraph_of_fun;by unlock.
by move : Hx2;rewrite -(eqP h1) /set1/= /fgraph_of_fun;by unlock.
by move : Hx3;rewrite -(eqP h1) /set1/= /fgraph_of_fun;by unlock.
move=> hh;discriminate.
rewrite /setD1.
apply/and4P;repeat split;
 by rewrite /set1/= /fgraph_of_fun; unlock.
apply/and3P;repeat split;
 by rewrite /set1/= /fgraph_of_fun; unlock.
apply/andP;split=>//.
by rewrite  /set1/= /fgraph_of_fun;unlock.

Qed.
