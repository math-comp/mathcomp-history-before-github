
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
Proof.
rewrite /fun_of_perm => /=;apply:can_fgraph_of_fun.
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


Definition op_inv := ( (R1,R3) ,(R2,R2) ,(R3,R1)).

Ltac get_inv elt l :=
  match l with 
         (_, (elt, ?x))  => x
 |    (elt, ?x)  => x
 |        (?x, _) => get_inv elt x
 end.

Ltac inj_tac :=
move: (refl_equal op_inv); unfold op_inv;
match goal with |- ?X = _ -> injective ?Y =>
  move => _;  let x := get_inv Y X in
  apply : (can_inj (g:=x)); move => [val H1] 
end.

Lemma R1_inj:  injective R1.
Proof.
inj_tac;repeat (destruct val => //=;rewrite /mk4 /=  //;first by apply /eqP).
Qed.

Lemma R2_inj: injective R2.
Proof.
inj_tac;repeat (destruct val => //=;rewrite /mk4 /=  //;first by apply /eqP).
Qed.

Lemma R3_inj: injective R3.
Proof. inj_tac;repeat (destruct val => //=;rewrite /mk4 /=  //;first by apply /eqP). Qed.

Definition r1 := (perm_of_inj R1_inj).
Definition r2 := (perm_of_inj R2_inj).
Definition r3 := (perm_of_inj R3_inj).

Ltac rinj_tac :=
match goal with |- perm_inv  ?x = _  =>
apply:(mulg_injr x);rewrite mulVg ;apply:eq_fun_of_perm ;move => [ val H1];
rewrite !perm_eqfun /= /comp/= !perm_eqfun
end.

Lemma r1_inv: perm_inv r1 = r3.
Proof. rinj_tac;repeat (destruct val => //=;rewrite /mk4 /=  //;first by apply /eqP). Qed.

Lemma r2_inv: perm_inv r2 = r2.
Proof. rinj_tac;repeat (destruct val => //=;rewrite /mk4 /=  //;first by apply /eqP). Qed.

Lemma r3_inv: perm_inv r3 = r1.
Proof. rinj_tac;repeat (destruct val => //=;rewrite /mk4 /=  //;first by apply /eqP). Qed.

Lemma r1_r1 : r2= r1*r1.
Proof.
apply:eq_fun_of_perm;move => [ val H1];rewrite  !perm_eqfun /= /comp/= !perm_eqfun/=;
repeat (destruct val => //=;rewrite /mk4 /=  //).
Qed.

Lemma r1_r2 : r3= r1*r2.
Proof.
apply:eq_fun_of_perm;move => [ val H1];rewrite  !perm_eqfun /= /comp/= !perm_eqfun/=;
repeat (destruct val => //=;rewrite /mk4 /=  //).
Qed.

Lemma r2_r1 : r3= r2*r1.
Proof.
apply:eq_fun_of_perm;move => [ val H1];rewrite  !perm_eqfun /= /comp/= !perm_eqfun/=;
repeat (destruct val => //=;rewrite /mk4 /=  //).
Qed.

Lemma r2_r3 : r1= r2*r3.
Proof.
apply:eq_fun_of_perm;move => [ val H1];rewrite  !perm_eqfun /= /comp/= !perm_eqfun/=;
repeat (destruct val => //=;rewrite /mk4 /=  //).
Qed.

Lemma r3_r2 : r1= r3*r2.
Proof.
apply:eq_fun_of_perm;move => [ val H1];
rewrite  !perm_eqfun /= /comp/= !perm_eqfun/=.
repeat (destruct val => //=;rewrite /mk4 /=  //).
Qed.

Lemma r3_r3 : r2= r3*r3.
Proof.
apply:eq_fun_of_perm;move => [ val H1];rewrite  !perm_eqfun /= /comp/= !perm_eqfun/=;
repeat (destruct val => //=;rewrite /mk4 /=  //).
Qed.

(*symmetries*)
Definition Sh (sc : square) : square:=
match sc with  EqSig 0 _ => c1| EqSig 1 _ => c0| EqSig 2 _ => c3| EqSig (S (S (S _))) _ =>c2 end.

Lemma Sh_inj: injective Sh.
Proof.
apply : (can_inj (g:= Sh));move => [val H1];
repeat (destruct val => //=;rewrite /mk4 /=  //;first by apply /eqP).
Qed.

Definition sh := (perm_of_inj Sh_inj).

Lemma sh_inv: perm_inv sh = sh.
Proof.
apply:(mulg_injr sh);rewrite mulVg ;apply:eq_fun_of_perm;move => [ val H1];
rewrite !perm_eqfun /= /comp/= !perm_eqfun;
repeat (destruct val => //=;rewrite /mk4 /=  //;first by apply /eqP).
Qed.

Definition id1:= (perm_unit square).

Lemma diff_id_sh: unitg (perm_finGroupType square) != sh.
Proof. by rewrite /set1/= /fgraph_of_fun; unlock. Qed.

Definition isometries2 :=  iset2 1 (perm_of_inj Sh_inj).

Lemma card_iso2: card isometries2 = 2.
Proof. by rewrite icard2;rewrite/set1/= /fgraph_of_fun; unlock. Qed.

Lemma group_set_iso: group_set  isometries2.
Proof.
apply/groupP;split;first by rewrite s2f eq_refl.
move => x y; rewrite !s2f;case /orP=> H1;case/orP=> H2; rewrite -(eqP H2) -(eqP H1);apply/orP;
 [left|right|right|left];gsimpl.
by rewrite -/sh -{1}sh_inv mulVg.
Qed.
Canonical Structure iso_group:= Group group_set_iso.


Definition rotations:setType (perm_finType square):= iset4 id1 r1 r2 r3.

Ltac magic := 
   match goal with h:?x==_=true|- _ => move:h ; 
        match goal with h1:?y==_=true|- _ => move=> h ;
      let hh := fresh " hh" in
      (have hh: (x==y)=false ; first (by rewrite /set1/= /fgraph_of_fun;unlock) ; 
       rewrite (eqP h1) h  in hh) end end.

Lemma card_rot: card rotations = 4.
Proof.
rewrite (icardD1 id1)  (icardD1 r1) (icardD1 r2) (icardD1 r3)  /rotations/= !s2f  eq_refl !orTb;congr addn.
repeat 
 match goal with |- context [?x != ?y] => have ->: (x != y);first by rewrite /set1/= /fgraph_of_fun;unlock end.
repeat (rewrite eq_refl  ?orbT;congr addn).
rewrite -(@eq_card _ set0 );first by apply card0.
by move =>x ;rewrite !s2f;do 4! case: (_ ==x).
Qed.


Lemma group_set_rot: group_set  rotations.
Proof.
apply/groupP;split;first by rewrite s2f eq_refl.
move => x y; rewrite !s2f;case /or4P=>H1;case/or4P=> H2;  rewrite -(eqP H1) -(eqP H2);
[rewrite mul1g|rewrite mul1g|rewrite mul1g|rewrite mul1g|rewrite mulg1|rewrite  r1_r1
 |rewrite  r1_r2|rewrite -r1_inv mulgV|rewrite mulg1|rewrite  r2_r1| rewrite -{1}r2_inv  mulVg|rewrite r2_r3
 |rewrite mulg1|rewrite -r3_inv mulgV|rewrite r3_r2|rewrite r3_r3];rewrite eq_refl ?orbT ?orTb;done.
Qed.
Canonical Structure rot_group:= Group group_set_rot.

Theorem ff: forall (d1 d2: finType) x1 x2,
(fun_of_fgraph (x:= d1) (x0 := d2) x1) =1 (fun_of_fgraph x2)  -> x1 = x2.
Proof.
move => d1 d2 x1 x2 H;rewrite -(can_fun_of_fgraph x1) -(can_fun_of_fgraph x2).
by apply: fval_inj;unlock fgraph_of_fun;exact: (eq_maps H).
Qed.

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


Definition square_coloring_number2 := t to iso_group.
Definition square_coloring_number4 := t to rot_group.

Infix "^":= expn : dnat_scope.

Lemma Fid:forall a: group (perm_finGroupType square), a 1-> (F to a 1)=1 (setA col_squares).
move => a Ha x;apply eqb_imp;rewrite/F//.
by move => _;apply/andP;split =>//=;last by rewrite act_f_1.
Qed.

Lemma card_Fid :forall a :group (perm_finGroupType square), a 1 -> card (F to a id1) = (n ^ 4)%N.
move => a Ha;rewrite (eq_card (Fid Ha)) /col_squares.
have <- : card (setA square) = 4; first by rewrite cardA.
have <-: card (setA colors)=n;first by rewrite card_ordinal.
rewrite -card_tfunspace; apply: eq_card=> f; symmetry.
by move: (@fgraph_prodP square colors col0  (fun _ : nat => setA colors)f ) => h; apply/h.
Qed.

Definition coin0(sc : col_squares) : colors:=(fun_of_fgraph sc) c0.
Definition coin1(sc : col_squares) : colors:=(fun_of_fgraph sc) c1.
Definition coin2(sc : col_squares) : colors:=(fun_of_fgraph sc) c2.
Definition coin3(sc : col_squares) : colors:=(fun_of_fgraph sc) c3.


Lemma F_Sh: forall a:group (perm_finGroupType square), a sh -> (F to a (perm_of_inj Sh_inj))=1 
{x:col_squares, (coin0 x == coin1 x) &&(coin2 x == coin3 x)}.
Proof.
rewrite /sh => a Ha x. rewrite  /F   !s2f  Ha /=    /to/=/act_f/=.
destruct x;do 4! destruct val=>//.
rewrite /coin0/c0/coin1/c1/coin2/c2/coin3/c3/=sh_inv;apply/idP/idP=>/=.
 move/eqP=> H;rewrite /fun_of_fgraph/=; unlock=>/=.
 move:H;set f:= fgraph_of_fun _;set g:= Fgraph _ =>H.
 have:((fun_of_fgraph f c0) = (fun_of_fgraph g c0));first by rewrite H.
 have:((fun_of_fgraph f c2) = (fun_of_fgraph g c2));first by rewrite H.
 rewrite !can_fgraph_of_fun !perm_eqfun/= /fun_of_fgraph;unlock=>/=.
 by move=> -> ->;apply/andP;split;done.
rewrite {1 2 3 4}/fun_of_fgraph;unlock=>/=.
case/andP=> h0 h1;rewrite (eqP h0)(eqP h1);
apply/eqP;apply :(ff (d1:= square) (d2:= colors))=> z.
rewrite can_fgraph_of_fun/= perm_eqfun;
destruct z;repeat (destruct val0=>//=;first by rewrite /fun_of_fgraph;unlock=>/=).
Qed.

Lemma F_R2: forall a:group (perm_finGroupType square), a  r2 ->(F to a (perm_of_inj R2_inj))=1 
{x:col_squares, (coin0 x == coin2 x) &&(coin1 x == coin3 x)}.
Proof.
rewrite /r2  => a Ha x;rewrite /F  !s2f  Ha /=   /to/=/act_f/=.
destruct x;rewrite /coin0/c0/coin1/c1/coin2/c2/coin3/c3/=;do 4! destruct val=>//.
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
rewrite can_fgraph_of_fun/= perm_eqfun;destruct z.
repeat (destruct val0=>//=;first by rewrite /fun_of_fgraph;unlock=>/=).
Qed.

Lemma F_r1: forall a:group (perm_finGroupType square), a  r1 ->(F to a (perm_of_inj R1_inj))=1 
{x:col_squares,(coin0 x == coin1 x)&&(coin1 x == coin2 x)&&(coin2 x == coin3 x)}.
rewrite /r1  => a Ha x;rewrite /F  !s2f  Ha /=   /to/=/act_f/=.
destruct x;rewrite /coin0/c0/coin1/c1/coin2/c2/coin3/c3/=.
do 4! destruct val=>//.
rewrite r1_inv;apply/idP/idP=>/=.
 move/eqP=> H;rewrite /fun_of_fgraph/=; unlock=>/=.
 move:H;set f:= fgraph_of_fun _;set g:= Fgraph _ => H.
 have:((fun_of_fgraph f c0) = (fun_of_fgraph g c0));first by rewrite H.
 have:((fun_of_fgraph f c1) = (fun_of_fgraph g c1));first by rewrite H.
 have:((fun_of_fgraph f c2) = (fun_of_fgraph g c2));first by rewrite H.
 rewrite /f /g!can_fgraph_of_fun !perm_eqfun/= /fun_of_fgraph;unlock=>/=.
 by move=> -> -> -> ;apply/andP;split =>//;apply/andP;split.
rewrite {1 2 3 4 5 6}/fun_of_fgraph;unlock=>/=.
case/andP=> h0 h1; move/andP: h0=> [h0 h2];rewrite (eqP h0 ) (eqP h2) (eqP h1).
apply/eqP;apply : (ff (d1:= square) (d2:= colors))=> z.
rewrite can_fgraph_of_fun/r3/= perm_eqfun;destruct z.
repeat (destruct val0=>//=;first by rewrite /fun_of_fgraph;unlock=>/=).
Qed.

Lemma F_r3: forall a:group (perm_finGroupType square), a  r3 ->(F to a (perm_of_inj R3_inj))=1 
{x:col_squares,(coin0 x == coin1 x)&&(coin1 x == coin2 x)&&(coin2 x == coin3 x)}.
rewrite /r3  => a Ha x;rewrite /F  !s2f  Ha /=   /to/=/act_f/=.
destruct x;rewrite /coin0/c0/coin1/c1/coin2/c2/coin3/c3/=.
do 4! destruct val=>//.
rewrite r3_inv;apply/idP/idP=>/=.
 move/eqP=> H;rewrite /fun_of_fgraph/=; unlock=>/=.
 move:H;set f:= fgraph_of_fun _;set g:= Fgraph _ => H.
 have:((fun_of_fgraph f c0) = (fun_of_fgraph g c0));first by rewrite H.
 have:((fun_of_fgraph f c1) = (fun_of_fgraph g c1));first by rewrite H.
 have:((fun_of_fgraph f c2) = (fun_of_fgraph g c2));first by rewrite H.
 rewrite /f /g !can_fgraph_of_fun !perm_eqfun/= /fun_of_fgraph;unlock=>/=.
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

Definition c(col:colors) :col_squares:=
    Fgraph (d1:=ordinal 4) (val:=Seq col col col col)
      (refl_equal (card (setA (ordinal 4)))).

Lemma c_inj: injective c.
Proof.
move => x y;destruct x; destruct y;rewrite /f.
move/fgraph_eqP=> H;case/and5P :H=>*.
by apply /eqP.
Qed.


Lemma bicolor: card {x : col_squares, (coin0 x == coin1 x) && (coin2 x == coin3 x)} =(n * n)%N.
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

Lemma card_FSh: forall a:group (perm_finGroupType square), a  sh ->card (F to a (perm_of_inj Sh_inj))= (n*n)%N.
move => a Ha;rewrite (eq_card (F_Sh Ha)).
exact:bicolor.
Qed.

Definition g (sc: col_squares): col_squares:=
match sc with
| Fgraph val e => 
      match val as s return (size s = card (setA square) -> col_squares) with
        (Seq  x0 x1 x2 x3) =>fun e4 : size (Seq x0 x2 x1 x3) = 4 =>
                        Fgraph (d1:=square) (val:=Seq x0 x2 x1 x3) e4
   | _=> fun _  => sc
    end e
end.

Lemma g_inj: injective g.
Proof.
move => x y;destruct x; destruct y;rewrite /g/=.
do 5! destruct val=>//;do 5! destruct val0=>//;
move/fgraph_eqP=> H;case/and5P :H=>h1 h2 h3 h4 _;rewrite (eqP h1)(eqP h2 )(eqP h3) (eqP h4).
by apply/fgraph_eqP.
Qed.
Definition S1:= {x : col_squares, (coin0 x == coin2 x) && (coin1 x == coin3 x)}.
Definition S2:= {x : col_squares, (coin0 x == coin1 x) && (coin2 x == coin3 x)}.

Lemma im_g_12: image g S1 =1 S2.
Proof.
move => z;destruct z;rewrite !s2f; do 5!(destruct val=>//);apply eqb_imp.
 case/imageP=> x3;rewrite s2f;destruct x3;do 5! (destruct val=>//).
 rewrite /coin0/coin1/coin2/coin3/=;case/andP;rewrite/fun_of_fgraph;unlock=>/=.
 do 2! (move/eqP => ->).  
 by case/fgraph_eqP;case/and5P; do 4! (move/eqP => ->); move=>_;apply/andP.
case/andP;rewrite/coin0/coin1/coin2/coin3 {1 2 3 4}/fun_of_fgraph;unlock=>/=.
do 2! (move/eqP => ->);apply/imageP.
have h:  size (Seq col0 col0 col0 col0) = card (setA square)=>//.
exists (Fgraph (d1:=square) (val:=Seq x0 x2 x0 x2) h);last by apply/fgraph_eqP.
by rewrite s2f;apply/andP;rewrite /coin0/coin1/coin2/coin3;split=>//;
 rewrite /fun_of_fgraph;unlock=>/=.
Qed.


Lemma card_FR2: forall a:group (perm_finGroupType square), a  r2 ->card (F to a (perm_of_inj R2_inj))= (n*n)%N.
by move => a Ha;rewrite (eq_card (F_R2 Ha)) -bicolor
 -(card_image g_inj {x : col_squares, (coin0 x == coin2 x) && (coin1 x == coin3 x)}) (eq_card im_g_12).
Qed.

Lemma unicolor: card {x : col_squares,
           (coin0 x == coin1 x)&&(coin1 x == coin2 x)&&(coin2 x == coin3 x)}= n.
have<-: card (setA colors) = n;first by rewrite card_ordinal.
rewrite -(card_image c_inj (setA  colors));apply:eq_card.
 rewrite /coin1/coin0/coin3/coin2/=.
 move => z;rewrite s2f;destruct z;do 5!(destruct val=>//); apply/idP/idP. 
 rewrite/fun_of_fgraph;unlock=>/=.
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
rewrite -{1}card_iso2 -(Frobenius_Cauchy to iso_group)(@sumD1 _ id1 )//= 
  (@sumD1 _ sh ).
 rewrite (@sum_id _ _ _ 0).
  rewrite muln0 addn0;congr addn.
   apply card_Fid; first by move/groupP:group_set_iso;case.
 rewrite /sh card_FSh/=; first by rewrite muln1.
 by rewrite /isometries2 !s2f -/sh eq_refl  orbT.
 move => x;rewrite /F/eqtype.setD1; case/and3P=> Hx1 Hx2 Hx.
 rewrite -(card0 col_squares);apply eq_card.
 move => z;apply eqb_imp=>//.
 case/andP;rewrite /isometries2 s2f.
 case/orP=> h1 h2.
  by move : Hx2; rewrite -(eqP h1)  /set1/= /fgraph_of_fun; unlock.
 move : Hx1;rewrite -(eqP h1)/fgraph_of_fun; unlock.
 by case/eqP;rewrite /fun_of_fgraph;unlock.
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
      by rewrite /rotations !s2f  eq_refl  !orbT.
     by rewrite  card_FR3//=;rewrite /rotations !s2f  eq_refl  !orbT.
    rewrite card_FR1/=; first by rewrite addn0.
    by rewrite /rotations !s2f  eq_refl  !orbT.
   move => x;rewrite /F/eqtype.setD1.
   case/and5P=> Hx3 Hx2 Hx1 Hxid _;rewrite -(card0 col_squares).
   apply eq_card;move => z;apply eqb_imp => //.
    by case/andP;rewrite /rotations s2f;case/or4P=> h1 h2; move : Hxid Hx1 Hx2 Hx3;
           rewrite -(eqP h1) /set1/= /fgraph_of_fun;unlock.
by rewrite /setD1;apply/and4P;repeat split; rewrite /set1/= /fgraph_of_fun; unlock.
by apply/and3P;repeat split; by rewrite /set1/= /fgraph_of_fun; unlock.
by apply/andP;split=>//;rewrite  /set1/= /fgraph_of_fun;unlock.
Qed.
End square_colouring.