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

Variables (d : finType) (x :d -> d) (h : injective x).

Lemma perm_eqfun: 
  forall z, (perm_of_inj h) z = x z.
Proof. by rewrite /fun_of_perm => /=;apply:g2f. Qed.

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


Definition rot_inv := ( (R1,R3) ,(R2,R2) ,(R3,R1)).

Ltac inj_tac :=
move: (refl_equal rot_inv); unfold rot_inv;
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
move => x1 y; rewrite /rot !s2f /= /is_rot ;move/eqP => hx1 ; move/eqP => hy.
by rewrite -mulgA hy !mulgA hx1.
Qed.

Canonical Structure rot_group:= Group group_set_rot.

Definition rotations:setType (perm_finType square):= iset4 id1 r1 r2 r3.

Theorem fog_inj: forall (d1 d2: finType) x1 x2,
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
rewrite /fun_of_perm/=/comp !(g2f (d1:= square)(d2:= square)).
by congr fun_of_fgraph.
move => t ht; rewrite {2}/fun_of_perm/= /comp!(g2f (d1:= square)(d2:= square)).
 congr fun_of_fgraph; rewrite /r1; apply /val_eqP => /=; unlock perm_of_inj fun_of_perm.
 by rewrite g2f /=. 
(*2*)
destruct val.
have ht: forall t,is_rot t->fun_of_perm t  (EqSig (fun m : nat_eqType => m < 4) 2%N valP)= fun_of_perm (t * (r1 * r1)) c0.
move=> t ;rewrite /is_rot => ht;rewrite mulgA (eqP ht)-mulgA(eqP ht).
rewrite {2}/fun_of_perm/=/comp{2}/fun_of_perm/=/comp/=.
rewrite !(g2f (d1:= square)(d2:= square)).
congr fun_of_fgraph. 
 by rewrite /r1 /perm_of_inj /fun_of_perm !g2f; apply /val_eqP.
rewrite (ht r hr) (ht s hs).
rewrite /fun_of_perm/=/comp. 
 rewrite !(g2f (d1:= square)(d2:= square))/comp.
rewrite hrs /perm_of_inj /fun_of_perm g2f  /R1/=;apply/val_eqP;auto.
(*3*)
destruct val=>//.
have ht : forall t, is_rot t -> fun_of_perm t  (EqSig (fun m : nat_eqType => m < 4) 3 valP)= fun_of_perm (t*( r1 * r1 * r1)) c0.
move=> t ;rewrite /is_rot => ht.
replace (t*(r1*r1*r1)) with ((r1*r1*r1)*t).
rewrite {2}/fun_of_perm/=/comp  !(g2f (d1:= square)(d2:= square)).
congr fun_of_fgraph. 
 by apply:val_inj => /=; do 3 rewrite /r1 !perm_eqfun /comp.
by rewrite -!mulgA- (eqP ht) (mulgA r1 t r1) -(eqP ht) -(mulgA t r1 r1)  mulgA -(eqP ht)!mulgA.
rewrite (ht r hr) (ht s hs) /fun_of_perm/=/comp !(g2f (d1:= square)(d2:= square)).
by rewrite hrs.
Qed.

Lemma rotations_is_rot: forall r, rotations  r -> is_rot r.
move => r ;rewrite /rotations/is_rot s2f.
case /or4P;move/eqP => <-//; first (by rewrite mulg1 mul1g);
 apply/eqP;apply: eq_fun_of_perm;move =>z; rewrite !perm_eqfun /comp !perm_eqfun/R2/R1/R3;
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
apply/negP; rewrite /set1 /= /fgraph_of_fun; move/eqP; injection.  
by unlock; injection; rewrite ord_enum4.
Qed.

Definition isometries2 :setType (perm_finType square):=  iset2 1 (perm_of_inj Sh_inj).

Lemma card_iso2: card isometries2 = 2.
Proof. 
rewrite icard2-/sh;congr S.
have ->: (1 != sh) =>//. 
exact: diff_id_sh.
Qed.

Lemma group_set_iso2: group_set  isometries2.
Proof.
apply/groupP;split;first by rewrite s2f eq_refl.
move => x y; rewrite !s2f;case /orP=> H1;case/orP=> H2; rewrite -(eqP H2) -(eqP H1);apply/orP;
 [left|right|right|left];gsimpl.
by rewrite -/sh -{1}sh_inv mulVg.
Qed.
Canonical Structure iso2_group:= Group group_set_iso2.
Definition isometries := {p, (p==id1)|| ((p==r1)||((p==r2)||((p==r3)||((p==sh)||((p==sv)||((p==s1)||(p==s2)))))))}.

Definition fop:= fun_of_perm.

Definition opp (sc:square):=
match sc with EqSig 0 _ => c2
                      | EqSig 1 _ =>  c3
                      | EqSig 2 _ =>  c0
                      | EqSig (S (S (S _))) _  =>  c1 end.

Definition is_iso p:= forall ci, (fop p (opp ci))=opp(fop p ci).

Lemma isometries_iso: forall p, isometries p -> is_iso p.
Proof.
move  => p; rewrite s2f.
case/or4P =>[H|H|H|];last case/or4P =>[H|H|H|];last (case/orP => H);
move => ci;rewrite (eqP H)/fop !perm_eqfun/=;
destruct ci as[vali valiP]; repeat (destruct vali=>//=).
Qed.

Ltac non_inj p a1 a2 heq1 heq2:= 
let h1:= fresh "h1" in 
(absurd (p a1 = p a2);first (by red; move=> h1;move:(perm_inj h1));
by rewrite heq1 heq2;apply/eqP).

Ltac is_isoPtac p f e0 e1 e2 e3:= 
have ->: p = f; last (by rewrite s2f eq_refl ?orbT); apply eq_fun_of_perm;move => [[|[|[|[|val]]]] valP]//;
[apply: (etrans (y:= p c0))|apply: (etrans (y:= p c1))|apply: (etrans (y:= p c2))|apply: (etrans (y:= p c3))];
try (by congr fun_of_fgraph; apply /eqP); rewrite  perm_eqfun/set1 ?e0/id1 ?e1?e2?e3;by apply /eqP.

Lemma  is_isoP:forall  p,reflect (is_iso p) (isometries p).
Proof.
move => p;apply :(iffP idP);first by apply:isometries_iso.
move => Hpiso;case e0: ((fun_of_perm p )c0)=> [val0 val0P];
repeat (destruct val0 =>//;first (move:(Hpiso c0);rewrite/fop e0/= =>e2));
case e1: ((fun_of_perm p )c1)=> [val1 val1P];
repeat (destruct val1=>//;first (move:(Hpiso c1);rewrite/fop e1/= =>e3)); try ( non_inj p c0 c1 e0 e1);
try ( non_inj p c0 c3 e0 e3).
(*id1*)
is_isoPtac p id1 e0 e1 e2 e3.
is_isoPtac p s1 e0 e1 e2 e3.
is_isoPtac p sh e0 e1 e2 e3.
is_isoPtac p r1 e0 e1 e2 e3.
is_isoPtac p s2 e0 e1 e2 e3.
is_isoPtac p r2 e0 e1 e2 e3.
is_isoPtac p r3 e0 e1 e2 e3.
is_isoPtac p sv e0 e1 e2 e3.
Qed.


Lemma group_set_iso: group_set  isometries.
Proof.
apply/groupP;split; first by   rewrite s2f eq_refl/=.
move => x y hx hy ; apply /is_isoP => ci;rewrite /fop/fun_of_perm !g2f /comp.
move:((isometries_iso hx) ci);rewrite /fop => ->;exact:  (isometries_iso hy).
Qed.

Canonical Structure iso_group:= Group group_set_iso.

Lemma card_rot: card rot = 4.
Proof.
rewrite (eq_card rot_is_rot);rewrite (icardD1 id1)  (icardD1 r1) (icardD1 r2) (icardD1 r3)  /rotations/= !s2f  eq_refl !orTb;congr addn.
repeat
 match goal with |- context [?x != ?y] => have ->: (x != y);
first by rewrite/set1/= /fgraph_of_fun; apply/negP; injection; move/eqP; injection; unlock;
   move/fgraph_eqP => /=;rewrite ord_enum4  end.
repeat (rewrite eq_refl  ?orbT;congr addn).
rewrite -(@eq_card _ set0 );first by apply card0.
by move =>x ;rewrite !s2f;do 4! case: (_ ==x).
Qed.

Lemma group_set_rotations: group_set  rotations.
Proof.
move/groupP: group_set_rot=> [h1 hs].
apply/groupP;split; first by rewrite -(rot_is_rot 1).
move => x y; rewrite -!rot_is_rot;by apply hs.
Qed.

Canonical Structure rotations_group:= Group group_set_rotations.
Definition col_squares: finType :=fgraph_finType  square  colors.

Definition  act_f(sc: col_squares ) (perm:perm_square) :col_squares:= 
let cs:= fun_of_fgraph sc in let : permf := fun_of_perm (perm_inv perm) in 
fgraph_of_fun ( fun z => cs (permf z)).

Lemma act_f_1:  forall x , act_f x 1 = x.
Proof.
move => x;rewrite /act_f;apply:fog_inj;move => y.
have -> : (@perm_inv  square 1) = 1;first by exact :invg1.
by rewrite g2f perm_eqfun.
Qed.

Lemma act_f_morph:  forall x y z, act_f z (x * y) = act_f (act_f z x) y.
Proof.
move => x y z;rewrite /act_f/=;apply :(fog_inj (d1:= square) (d2:= colors)).
have ->: (@perm_inv square (x*y))= (perm_inv y)*(perm_inv x);first by exact:invg_mul.
by move => t;rewrite !(g2f (d1:= square) (d2:= colors))  perm_eqfun.
Qed.

Definition to := Action  act_f_1 act_f_morph.

Definition square_coloring_number2 := t to iso2_group.
Definition square_coloring_number4 := t to rot_group.
Definition square_coloring_number8 := t to iso_group.

Infix "^":= expn : dnat_scope.

Lemma Fid:forall a:group (perm_finGroupType square), a 1-> (F to a 1)=1 (setA col_squares).
Proof.
move => a Ha x;rewrite /F;apply/idP;apply/idP.
apply/andP;split =>//=; by rewrite act_f_1.
Qed.

Lemma card_Fid :forall a :group (perm_finGroupType square), a 1 -> card (F to a id1) = (n ^ 4)%N.
Proof.
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
rewrite /sh => a Ha x; rewrite  /F   !s2f  Ha /=    /to/=/act_f/= /coin0/c0/coin1/c1/coin2/c2/coin3/c3/=sh_inv.
have: (card (setA square)=4);first by rewrite cardA /=ord_enum4.
destruct x; do 4! (destruct val=>//=; first by rewrite -e=> *; discriminate).
destruct val=>//=; last by rewrite -e=> *; discriminate.
move => _.
apply/idP/idP=>/=.
 move/eqP=> H;rewrite /fun_of_fgraph/=; unlock=>/=.
 move:H;set f:= fgraph_of_fun _;set g:= Fgraph _ =>H.
 have:((fun_of_fgraph f c0) = (fun_of_fgraph g c0));first by rewrite H.
 have:((fun_of_fgraph f c2) = (fun_of_fgraph g c2));first by rewrite H.
 rewrite !g2f !perm_eqfun/= /fun_of_fgraph;unlock=>/=.
 by move=> -> ->;apply/andP;split;done.
rewrite {1 2 3 4}/fun_of_fgraph;unlock=>/=.
rewrite ord_enum4/=. 
case/andP=> h0 h1;rewrite (eqP h0)(eqP h1).
apply/eqP;apply :(fog_inj (d1:= square) (d2:= colors))=> z.
rewrite g2f /= perm_eqfun; destruct z;
repeat (destruct val=>//=;first by rewrite /fun_of_fgraph;unlock=>/=;unlock=>/=;rewrite ord_enum4).
Qed.

Lemma F_Sv: forall a:group (perm_finGroupType square), a sv -> (F to a (perm_of_inj Sv_inj))=1 
{x:col_squares, (coin0 x == coin3 x) &&(coin2 x == coin1 x)}.
Proof.
rewrite /sv => a Ha x; rewrite  /F   !s2f  Ha /=    /to/=/act_f/= /coin0/c0/coin1/c1/coin2/c2/coin3/c3/=sv_inv.
have: (card (setA square)=4);first by rewrite cardA /=ord_enum4.
destruct x; do 4! (destruct val=>//=; first by rewrite -e=> *; discriminate).
destruct val=>//=; last by rewrite -e=> *; discriminate.
move => _;apply/idP/idP=>/=.
 move/eqP=> H;rewrite /fun_of_fgraph/=; unlock=>/=.
 move:H;set f:= fgraph_of_fun _;set g:= Fgraph _ =>H.
 have:((fun_of_fgraph f c0) = (fun_of_fgraph g c0));first by rewrite H.
 have:((fun_of_fgraph f c1) = (fun_of_fgraph g c1));first by rewrite H.
 rewrite !g2f !perm_eqfun/= /fun_of_fgraph;unlock=>/=.
 by move=> -> ->;apply/andP;split;done.
rewrite {1 2 3 4}/fun_of_fgraph;unlock=>/=.
rewrite ord_enum4/=;case/andP=> h0 h1;rewrite (eqP h0)(eqP h1);
apply/eqP;apply :(fog_inj (d1:= square) (d2:= colors))=> z.
rewrite g2f /= perm_eqfun;destruct z;  
repeat (destruct val=>//=;first by rewrite /fun_of_fgraph;unlock=>/=;unlock=>/=;rewrite ord_enum4).
Qed.

Ltac inv_tac :=
match goal with |- perm_inv  ?x = _  =>
apply:(mulg_injr x);rewrite mulVg ;apply:eq_fun_of_perm ;move => [ val H1];
rewrite !perm_eqfun /= /comp/= !perm_eqfun
end.

Lemma r1_inv: perm_inv r1 = r3.
Proof. inv_tac;repeat (destruct val => //=;rewrite /mk4 /=  //;first by apply /eqP). Qed.

Lemma r2_inv: perm_inv r2 = r2.
Proof. inv_tac;repeat (destruct val => //=;rewrite /mk4 /=  //;first by apply /eqP). Qed.

Lemma r3_inv: perm_inv r3 = r1.
Proof. inv_tac;repeat (destruct val => //=;rewrite /mk4 /=  //;first by apply /eqP). Qed.

Lemma F_R2: forall a:group (perm_finGroupType square), a  r2 ->(F to a (perm_of_inj R2_inj))=1 
{x:col_squares, (coin0 x == coin2 x) &&(coin1 x == coin3 x)}.
Proof.
rewrite /r2  => a Ha x;rewrite /F  !s2f  Ha /=   /to/=/act_f/=;
destruct x;rewrite /coin0/c0/coin1/c1/coin2/c2/coin3/c3/=.
have: (card (setA square)=4);first by rewrite cardA /=ord_enum4.
do 4! (destruct val=>//=; first by rewrite -e=> *; discriminate).
destruct val=>//=; last by rewrite -e=> *; discriminate.
move =>_;rewrite r2_inv;apply /idP/idP =>/=.
 move/eqP=> H;rewrite /fun_of_fgraph/=; unlock=>/=.
 move:H;set f:= fgraph_of_fun _;set g:= Fgraph _ => H. 
 have:((fun_of_fgraph f c0) = (fun_of_fgraph g c0));first by rewrite H.
 have:((fun_of_fgraph f c1) = (fun_of_fgraph g c1));first by rewrite H.
 rewrite /f /g/r2 !g2f !perm_eqfun/= /fun_of_fgraph;unlock=>/=.
 by move=> -> ->;apply/andP;split.
rewrite {1 2 3 4}/fun_of_fgraph;unlock=>/=.
rewrite ord_enum4 =>/=.
case/andP=> h0 h1;rewrite (eqP h0 ) (eqP h1);
apply/eqP;apply : (fog_inj (d1:= square) (d2:= colors)) => z.
rewrite g2f/= perm_eqfun;destruct z.
repeat (destruct val=>//=;first by rewrite /fun_of_fgraph;unlock=>/=;unlock=>/=;rewrite ord_enum4).
Qed.

Lemma F_r1: forall a:group (perm_finGroupType square), a  r1 ->(F to a (perm_of_inj R1_inj))=1 
{x:col_squares,(coin0 x == coin1 x)&&(coin1 x == coin2 x)&&(coin2 x == coin3 x)}.
Proof.
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
 rewrite /f /g!g2f !perm_eqfun/= /fun_of_fgraph;unlock=>/=.
 by move=> -> -> -> ;apply/andP;split =>//;apply/andP;split.
rewrite {1 2 3 4 5 6}/fun_of_fgraph;unlock=>/=;rewrite ord_enum4 =>/=.
case/andP=> h0 h1; move/andP: h0=> [h0 h2];rewrite (eqP h0 ) (eqP h2) (eqP h1).
apply/eqP;apply : (fog_inj (d1:= square) (d2:= colors))=> z.
rewrite g2f/r3/= perm_eqfun;destruct z.
repeat (destruct val=>//=;first by rewrite /fun_of_fgraph;unlock=>/=;rewrite ord_enum4).
Qed.

Lemma F_r3: forall a:group (perm_finGroupType square), a  r3 ->(F to a (perm_of_inj R3_inj))=1 
{x:col_squares,(coin0 x == coin1 x)&&(coin1 x == coin2 x)&&(coin2 x == coin3 x)}.
Proof.
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
 rewrite /f /g !g2f !perm_eqfun/= /fun_of_fgraph;unlock=>/=.
 by move=> -> -> -> ;apply/andP;split =>//;apply/andP;split.
rewrite {1 2 3 4 5 6}/fun_of_fgraph;unlock=>/=;rewrite ord_enum4 =>/=.
case/andP=> h0 h1; move/andP: h0=> [h0 h2];rewrite (eqP h0 ) (eqP h2) (eqP h1).
apply/eqP;apply : (fog_inj (d1:= square) (d2:= colors))=> z.
rewrite g2f/r3/= perm_eqfun;destruct z.
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
Proof.
move => x y;destruct x; destruct y;rewrite /f.
move/fgraph_eqP=> H;case/and5P :H=>*;by apply /eqP;apply /andP;split.
Qed.

Definition g(col_pair:prod_finType colors colors) :col_squares:=
match col_pair  with EqPair c1 c2 => 
    Fgraph (d1:=ordinal 4) (val:=Seq c1 c2 c2 c1)  (size4 c1 c2 c2 c1)
end.

Lemma g_inj: injective g.
Proof.
move => x y;destruct x; destruct y;rewrite /g.
move/fgraph_eqP=> H;case/and5P :H=>*;by apply /eqP;apply /andP;split.
Qed.

Definition c(col:colors) :col_squares:=
    Fgraph (d1:=ordinal 4) (val:=Seq col col col col)(size4 col col col col).

Lemma c_inj: injective c.
Proof.
move => x y;destruct x; destruct y;rewrite /f.
move/fgraph_eqP=> H;case/and5P :H=>*;by apply /eqP.
Qed.


Lemma fbicolor: card {x : col_squares, (coin0 x == coin1 x) && (coin2 x == coin3 x)} =(n * n)%N.
Proof.
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
Proof.
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
Proof.
move => a Ha;rewrite (eq_card (F_Sh Ha));exact:fbicolor.
Qed.

Lemma card_FSv: forall a:group (perm_finGroupType square), a  sv ->card (F to a (perm_of_inj Sv_inj))= (n*n)%N.
Proof.
move => a Ha;rewrite (eq_card (F_Sv Ha));exact:gbicolor.
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
Proof.
by move => a Ha;rewrite (eq_card (F_R2 Ha)) -fbicolor
 -(card_image h_inj {x : col_squares, (coin0 x == coin2 x) && (coin1 x == coin3 x)}) (eq_card im_h_12).
Qed.

Lemma unicolor: card {x : col_squares,
           (coin0 x == coin1 x)&&(coin1 x == coin2 x)&&(coin2 x == coin3 x)}= n.
Proof.
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
left;rewrite /isometries2 s2f.
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
apply/negP; apply/nandP;left;rewrite s2f;apply /negP.
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
Proof.
rewrite /s1  => a Ha x;rewrite /F  !s2f  Ha /=   /to/=/act_f/=.
destruct x;rewrite /coin0/c0/coin1/c1/coin2/c2/coin3/c3/=.
have: (card (setA square)=4);first by rewrite cardA /=ord_enum4.
do 4! (destruct val=>//=; first by rewrite -e=> *; discriminate).
destruct val=>//=; last by rewrite -e=> *; discriminate.
move =>_;rewrite s1_inv;apply/idP/idP=>/=.
 move/eqP=>H;rewrite /s1/fun_of_fgraph/=; unlock=>/=.
rewrite ord_enum4/=; move:H;set fff:= fgraph_of_fun _;set ggg:= Fgraph _ => H.
 have:((fun_of_fgraph fff c3) = (fun_of_fgraph ggg c3));first by rewrite H.
 rewrite /fff /ggg !g2f !perm_eqfun/= /fun_of_fgraph;unlock=>/=.
rewrite ord_enum4;by case/eqP.
rewrite /fun_of_fgraph;unlock=>/=;rewrite ord_enum4 =>/=.
move/eqP => ->/=;apply/eqP;apply : (fog_inj(d1:= square) (d2:= colors))=> z.
rewrite g2f/s1/= perm_eqfun;destruct z.
repeat (destruct val=>//=;first by rewrite /fun_of_fgraph;unlock=>/= ;rewrite ord_enum4).
Qed.

Definition i(col_triplet:prod_finType colors (prod_finType colors colors)) :col_squares:=
match col_triplet  with EqPair c1 c2c3 => 
  match c2c3 with EqPair c2 c3 =>
    Fgraph (d1:=ordinal 4) (val:=Seq c1 c2 c3 c2)
      (size4 c1 c2 c3 c2)
end end.

Lemma i_inj: injective i.
Proof.
move => x y;destruct x as [x1 [x2 x3]]; destruct y as [y1 [y2 y3]];rewrite /i.
move/fgraph_eqP=> H;case/and5P :H=>*.
apply /eqP;repeat (apply /andP;split=>//).
Qed.

Lemma tricolor: card {x : col_squares, (coin1 x == coin3 x)}  =(n ^3)%N.
Proof.
have <-: card (setA colors) = n;first by rewrite card_ordinal.
move: (card_image i_inj (setA (prod_finType colors (prod_finType colors colors)))).
have <-: card(setA(prod_finType colors(prod_finType colors colors))) = (card (setA colors) ^ 3)%N;first by  rewrite !card_prod/= muln1.
have : image i (setA (prod_finType colors (prod_finType colors colors))) =1 {x : col_squares, (coin1 x == coin3 x)}.
 move => z;rewrite s2f;destruct z.
 have: (card (setA square)=4);first by rewrite cardA /=ord_enum4.
 do 4! (destruct val=>//=; first by rewrite -e=> *; discriminate).
 destruct val=>//=; last by rewrite -e=> *; discriminate.
 move => _;apply /idP/idP.
  case/imageP => x3  Hx3;case x3 => col1 col23; case col23 => col2 col3;   rewrite /i/=.
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
Proof.
have Hs1: iso_group s1;first by rewrite s2f eq_refl //= !orbT.
rewrite (eq_card (F_S1 Hs1));exact:tricolor.
Qed.

Lemma F_S2: forall a:group (perm_finGroupType square), a  s2 ->(F to a (perm_of_inj S2_inj))=1 
{x:col_squares,(coin0 x == coin2 x)}.
Proof.
rewrite /s2  => a Ha x;rewrite /F  !s2f  Ha /=   /to/=/act_f/=.
destruct x;rewrite /coin0/c0/coin1/c1/coin2/c2/coin3/c3/=.
have: (card (setA square)=4);first by rewrite cardA /=ord_enum4.
do 4! (destruct val=>//=; first by rewrite -e=> *; discriminate);destruct val=>//=; last by rewrite -e=> *; discriminate.
move =>_;rewrite s2_inv;apply/idP/idP=>/=.
 move/eqP=>H;rewrite /s2/fun_of_fgraph/=; unlock=>/=;rewrite ord_enum4/=.
 move:H;set fff:= fgraph_of_fun _;set ggg:= Fgraph _ => H.
 have:((fun_of_fgraph fff c2) = (fun_of_fgraph ggg c2));first by rewrite H.
 rewrite /fff /ggg !g2f !perm_eqfun/= /fun_of_fgraph;unlock=>/=.
 by rewrite ord_enum4;case/eqP.
rewrite /fun_of_fgraph;unlock=>/=;rewrite ord_enum4 =>/=.
move/eqP => ->/=;apply/eqP;apply : (fog_inj (d1:= square) (d2:= colors))=> z.
rewrite g2f/s2/= perm_eqfun;destruct z.
repeat (destruct val=>//=;first by rewrite /fun_of_fgraph;unlock=>/= ;rewrite ord_enum4).
Qed.

Definition j(col_triplet:prod_finType colors (prod_finType colors colors)) :col_squares:=
match col_triplet  with EqPair c1 c2c3 => 
  match c2c3 with EqPair c2 c3 =>
    Fgraph (d1:=ordinal 4) (val:=Seq c1 c2 c1 c3)
      (size4 c1 c2 c1 c3)
end end.

Lemma j_inj: injective j.
Proof.
move => x y;destruct x as [x1 [x2 x3]]; destruct y as [y1 [y2 y3]];rewrite /j.
move/fgraph_eqP=> H;case/and5P :H=>*.
apply /eqP;repeat (apply /andP;split=>//).
Qed.

Lemma jtricolor: card {x : col_squares, (coin0 x == coin2 x)}  =(n ^3)%N.
Proof.
have <-: card (setA colors) = n;first by rewrite card_ordinal.
move: (card_image j_inj (setA (prod_finType colors (prod_finType colors colors)))).
have <-: card(setA(prod_finType colors(prod_finType colors colors))) = (card (setA colors) ^ 3)%N;first by  rewrite !card_prod/= muln1.
have : image j (setA (prod_finType colors (prod_finType colors colors))) =1 {x : col_squares, (coin0 x == coin2 x)}.
 move => z;rewrite s2f;destruct z.
 have: (card (setA square)=4);first by rewrite cardA /=ord_enum4.
 do 4! (destruct val=>//=; first by rewrite -e=> *; discriminate);destruct val=>//=; last by rewrite -e=> *; discriminate.
 move => _;apply /idP/idP.
  case/imageP => x3  Hx3;case x3 => col1 col23; case col23 => col2 col3;rewrite /j/=.
  case/fgraph_eqP;case/and5P=> h1 h2 h3 h4 _.
  rewrite (eqP h1)(eqP h2) (eqP h3)(eqP h4) /coin0/coin1/coin2/coin3/=.
  by rewrite /fun_of_fgraph;unlock=> /= ; rewrite ord_enum4.
 rewrite /coin1/coin0/coin2/coin3/=/fun_of_fgraph;unlock=>/=;  rewrite ord_enum4/=.
 move => h1 ;apply/imageP;exists (EqPair x (EqPair x0 x2)) =>//=.
 by rewrite (eqP h1) =>//=;apply/fgraph_eqP=>//=.
by move => h1 <-;symmetry;apply:eq_card.
Qed.

Lemma card_FS2: (card (F to iso_group s2)= n^3)%N.
Proof.
have Hs2: iso_group s2;first by rewrite s2f eq_refl //= !orbT.
rewrite (eq_card (F_S2 Hs2));exact:jtricolor.
Qed.

Ltac disc0:= let heq := fresh "heq" in repeat  (match goal with |- context [?x != ?y] =>apply/eqP =>heq;absurd (x c0 = y c0);
     last( by rewrite heq); red; rewrite !perm_eqfun/= =>*;discriminate end).

Ltac disc1:= let heq := fresh "heq" in repeat  (match goal with |- context [?x != ?y] =>apply/eqP =>heq;absurd (x c1 = y c1);
     last( by rewrite heq); red; rewrite !perm_eqfun/= =>*;discriminate end).

Lemma burnside_app_iso: (square_coloring_number8 *8= ( n^4) + 2*n^3+ 3* n^2 +2*n)%N.
Proof.
have card_iso: card iso_group = 8.
 rewrite  (eq_card (a:= iso_group) (b:= isometries)).
  rewrite (icardD1 id1)  (icardD1 r1) (icardD1 r2) (icardD1 r3) (icardD1 sh )( icardD1 sv) (icardD1 s1) (icardD1 s2)
 /isometries/= !s2f  eq_refl !orTb;congr addn.
  repeat 
   match goal with |- context [?x != ?y] => have ->: (x != y);
   first by rewrite/set1/= /fgraph_of_fun; apply/negP; injection; move/eqP; injection; unlock;
   move/fgraph_eqP => /=;rewrite ord_enum4  end.
  repeat (rewrite eq_refl  ?orbT;congr addn).
  rewrite -(@eq_card _ set0 );first by apply card0.
  move =>x ;rewrite !s2f.
  do 8! rewrite (eq_sym x).
  do 8!(case: ( _ ==x );simpl;auto).
 by move => z; apply/is_isoP/is_isoP.
rewrite - card_iso -(Frobenius_Cauchy to iso_group).
rewrite (@sumD1 _ id1 ) 1?(@sumD1 _ r1 ) 1?(@sumD1 _ r2 ) 1? (@sumD1 _ r3 )
 1?(@sumD1 _ sh ) 1? (@sumD1 _ sv ) 1? (@sumD1 _ s1 )1? (@sumD1 _ s2 )1? (@sum_id _ _ _ 0)//=;
try do 3!(rewrite /setD1;try apply/and4P; try apply/and5P; try apply/and3P; try apply/andP; repeat split;disc0;disc1).
        rewrite muln0 addn0 -!addnA ;congr addn.
         by rewrite card_Fid;last by move/groupP:group_set_iso;case.
        rewrite card_FR1 1?card_FR2 1?card_FR3 ?card_FSh ?card_FSv ?card_FS1 ?card_FS2;try by rewrite /isometries !s2f  eq_refl  !orbT.
        rewrite /=!muln1 !add0n !addn0; do 11!(try rewrite -!addnA; (congr addn;[idtac])||rewrite addnC =>//).
       move => x;rewrite /F/eqtype.setD1; case/and5P=> Hs2 Hs1 Hsv Hsh; case/and5P=> Hr1 Hr2 Hr3 Hid _.
       rewrite -(card0 col_squares);   apply eq_card;move => z;apply /idP.
       apply/negP; apply/nandP;left;rewrite s2f;apply /negP.
case /or4P; last case/or4P;last case/orP; by rewrite eq_sym; apply/negP.
Qed.

End square_colouring.

Corollary burnside_app_iso_4col: square_coloring_number8 4 = 55.

apply/eqP;rewrite - (@eqn_pmul2r 8)// burnside_app_iso;done.
Qed.

