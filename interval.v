Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq div choice fintype.
Require Import bigop ssralg finset fingroup zmodp zint orderedalg.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope ring_scope.
Import GRing.Theory ORing.Theory.

Section IntervalPo.

CoInductive int_bound (T : Type) : Type := BClose of bool & T | BInfty.

CoInductive interval (T : Type) := Interval of int_bound T & int_bound T.

Variable (R : poIdomainType).

Definition pred_of_int (i : interval R) : pred R := nosimpl
  [pred x | let: Interval l u := i in
      match l with
        | BClose false a => a < x
        | BClose _ a => a <= x
        | BInfty => true
      end &&
      match u with
        | BClose false b => x < b
        | BClose _ b => x <= b
        | BInfty => true
      end].
Canonical Structure intPredType := Eval hnf in mkPredType pred_of_int.

Notation "`[ a , b ]" := (Interval (BClose true a) (BClose true b))
  (at level 0, a, b at level 9 , format "`[ a ,  b ]") : ring_scope.
Notation "`] a , b ]" := (Interval (BClose false a) (BClose true b))
  (at level 0, a, b at level 9 , format "`] a ,  b ]") : ring_scope.
Notation "`[ a , b [" := (Interval (BClose true a) (BClose false b))
  (at level 0, a, b at level 9 , format "`[ a ,  b [") : ring_scope.
Notation "`] a , b [" := (Interval (BClose false a) (BClose false b))
  (at level 0, a, b at level 9 , format "`] a ,  b [") : ring_scope.
Notation "`] '-oo' , b ]" := (Interval (BInfty _) (BClose true b))
  (at level 0, b at level 9 , format "`] '-oo' ,  b ]") : ring_scope.
Notation "`] '-oo' , b [" := (Interval (BInfty _) (BClose false b))
  (at level 0, b at level 9 , format "`] '-oo' ,  b [") : ring_scope.
Notation "`[ a , '+oo' [" := (Interval (BClose true a) (BInfty _))
  (at level 0, a at level 9 , format "`[ a ,  '+oo' [") : ring_scope.
Notation "`] a , '+oo' [" := (Interval (BClose false a) (BInfty _))
  (at level 0, a at level 9 , format "`] a ,  '+oo' [") : ring_scope.
Notation "`] -oo , '+oo' [" := (Interval (BInfty _) (BInfty _))
  (at level 0, format "`] -oo ,  '+oo' [") : ring_scope.


Definition int_rewrite (i : interval R) x : Prop :=
  let: Interval l u := i in
    (match l, u with
       | BClose true a, BClose true b =>
         (a <= x) * (x < a = false) * (x <= b) * (b < x = false)
         * (a <= b) * (b < a = false)
         * (a \in `[a, b]) * (b \in `[a, b])
       | BClose true a, BClose false b =>
         (a <= x) * (x < a = false) * (x <= b) * (x < b) * (b <= x = false)
         * (a <= b) * (a < b) * (b <= a = false)
         * (a \in `[a, b]) * (a \in `[a, b[)* (b \in `[a, b]) * (b \in `]a, b])
       | BClose false a, BClose true b =>
         (a <= x) * (a < x) * (x <= a = false) * (x <= b) * (b < x = false)
         * (a <= b) * (a < b) * (b <= a = false)
         * (a \in `[a, b]) * (a \in `[a, b[)* (b \in `[a, b]) * (b \in `]a, b])
       | BClose false a, BClose false b =>
         (a <= x) * (a < x) * (x <= a = false) * (x <= b) * (x < b) * (b <= x = false)
         * (a <= b) * (a < b) * (b <= a = false)
         * (a \in `[a, b]) * (a \in `[a, b[)* (b \in `[a, b]) * (b \in `]a, b])
       | BInfty, BClose true b => (x <= b) * (b < x = false)
       | BInfty, BClose false b => (x <= b) * (x < b) * (b <= x = false)
       | BClose true a, BInfty => (a <= x) * (x < a = false)
       | BClose false a, BInfty => (a <= x) * (a < x) * (x <= a = false)
       | BInfty, BInfty => forall x : R, x == x
    end)%type.

Definition int_decompose (i : interval R) x : Prop :=
  let: Interval l u := i in
  ((match l with
    | BClose true a => (a <= x) : Prop
    | BClose _ a => (a < x) : Prop
    | BInfty => True
  end : Prop) *
  (match u with
    | BClose true b => (x <= b) : Prop
    | BClose _ b => (x < b) : Prop
    | BInfty => True
  end : Prop))%type.

Lemma int_dec : forall (x : R) (i : interval R),
  reflect (int_decompose i x) (x \in i).
Proof. move=> x [[[] a|] [[] b|]]; apply: (iffP andP); case=> //. Qed.

Implicit Arguments int_dec [x i].

Definition ltreif (x y : R) b := if b then x <= y else x < y.

Local Notation "x < y ?<= 'if' b" := (ltreif x y b)
  (at level 70, y at next level,
  format "x '[hv'  <  y '/'  ?<=  'if'  b ']'") : ring_scope.

Lemma ltreifxx : forall x b, x < x ?<= if b = b.
Proof. by move=> x [] /=; rewrite lterr. Qed.

Lemma ltreif_trans : forall x y z b1 b2,
  x < y ?<= if b1 -> y < z ?<= if b2 ->  x < z ?<= if b1 && b2.
Proof.
by move=> x y z [] [] /=;
[exact: ler_trans|exact: ler_lt_trans|exact: ltr_le_trans|exact: ltr_trans].
Qed.

Lemma ltreifW : forall b x y, x < y ?<= if b -> x <= y.
Proof. by case=> x y //; move/ltrW. Qed.

Definition le_boundl b1 b2 :=
  match b1, b2 with
    | BClose b1 x1, BClose b2 x2 => x1 < x2 ?<= if (b2 ==> b1)
    | BClose _ _, BInfty => false
    | _, _ => true
  end.

Definition le_boundr b1 b2 :=
  match b1, b2 with
    | BClose b1 x1, BClose b2 x2 => x1 < x2 ?<= if (b1 ==> b2)
    | BInfty, BClose _ _ => false
    | _, _ => true
  end.

Lemma int_boundlr : forall bl br, forall x,
  x \in Interval bl br = le_boundl bl (BClose true x) && le_boundr (BClose true x) br.
Proof. by move=> [[] a|] [[] b|] x. Qed.

Lemma le_boundr_refl : reflexive le_boundr.
Proof. by move=> [[] b|]; rewrite /le_boundr /= ?lerr. Qed.

Hint Resolve le_boundr_refl.

Lemma le_boundl_refl : reflexive le_boundl.
Proof. by move=> [[] b|]; rewrite /le_boundl /= ?lerr. Qed.

Hint Resolve le_boundl_refl.

Lemma le_boundl_bb : forall x b1 b2, le_boundl (BClose b1 x) (BClose b2 x) = (b2 ==> b1).
Proof. by move=> x b1 b2; rewrite /le_boundl //= ltreifxx. Qed.

Lemma le_boundr_bb : forall x b1 b2, le_boundr (BClose b1 x) (BClose b2 x) = (b1 ==> b2).
Proof. by move=> x b1 b2; rewrite /le_boundr /= ltreifxx. Qed.

Lemma int_xx : forall x bl br,
  Interval (BClose bl x) (BClose br x) =i if bl && br then pred1 x else pred0.
Proof. by move=> x [] [] y /=; rewrite !inE 1?eq_sym (eqr_le, lter_anti). Qed.

Lemma int_gte : forall ba xa bb xb, (if ba && bb then xb < xa else xb <= xa)
  -> Interval (BClose ba xa) (BClose bb xb) =i pred0.
Proof.
move=> ba xa bb xb hx y; rewrite int_boundlr inE /=.
apply/negP; case/andP; move/ltreif_trans=> hy; move/hy.
by case: (_ && _) hx=> /=; [move/ltr_geF->|move/ler_gtF->].
Qed.

Lemma boundl_in_int : forall ba xa b,
  xa \in Interval (BClose ba xa) b = if ba then le_boundr (BClose true xa) b else false.
Proof. by move=> [] xa [bb xb|] //=; do ?by rewrite inE /= lterr. Qed.

Lemma boundr_in_int : forall bb xb a,
  xb \in Interval a (BClose bb xb) = if bb then le_boundl a (BClose true xb) else false.
Proof. move=> [] xb [ba xa|] //=; do ?by rewrite inE /= lterr ?(andbT, andbF). Qed.

Definition bound_in_int := (boundl_in_int, boundr_in_int).

Lemma intP : forall (x : R) (i : interval R), (x \in i) -> int_rewrite i x.
Proof.
move=> x [[[] a|] [[] b|]]; move/int_dec=> //= [hl hu];do ?[split=> //;
  do ?[by rewrite ltrW | by rewrite ltrWN | by rewrite ltrNW |
    by rewrite (ltr_geF, ler_gtF)]];
  rewrite ?(bound_in_int) /le_boundl /le_boundr //=; do ?
    [ by rewrite (@ler_trans _ x)
    | by rewrite 1?ltrW // (@ltr_le_trans _ x)
    | by rewrite 1?ltrW // (@ler_lt_trans _ x) // 1?ltrW
    | by apply: negbTE; rewrite ler_gtF // (@ler_trans _ x)
    | by apply: negbTE; rewrite ltr_geF // (@ltr_le_trans _ x) // 1?ltrW
    | by apply: negbTE; rewrite ltr_geF // (@ler_lt_trans _ x)].
Qed.

Hint Rewrite intP.
Implicit Arguments intP [x i].

Definition subint (i1 i2 : interval R) :=
  match i1, i2 with
    | Interval a1 b1, Interval a2 b2 => le_boundl a2 a1 && le_boundr b1 b2
  end.

Lemma subintP : forall (i2 i1 : interval R), 
  (subint i1 i2) -> {subset i1 <= i2}.
Proof.
by move=> [[[] a2|] [[] b2|]] [[[] a1|] [[] b1|]];
  rewrite /subint //; case/andP=> /= ha hb; move=> x hx; rewrite ?inE;
    rewrite ?(ler_trans ha) ?(ler_lt_trans ha) ?(ltr_le_trans ha) //;
      rewrite ?(ler_trans _ hb) ?(ltr_le_trans _ hb) ?(ler_lt_trans _ hb) //;
        rewrite ?(intP hx) //.
Qed.

Lemma subintPr : forall (a b1 b2 : int_bound R),
  le_boundr b1 b2 -> {subset (Interval a b1) <= (Interval a b2)}.
Proof. by move=> a b1 b2 hb; apply: subintP=> /=; rewrite hb andbT. Qed.

Lemma subintPl : forall (a1 a2 b : int_bound R),
  le_boundl a2 a1 -> {subset (Interval a1 b) <= (Interval a2 b)}.
Proof. by move=> a1 a2 b ha; apply: subintP=> /=; rewrite ha /=. Qed.

Lemma ltreif_in_int : forall ba bb xa xb x,
  x \in Interval (BClose ba xa) (BClose bb xb) -> xa < xb ?<= if ba && bb.
Proof.
by move=> ba bb xa xb y; rewrite int_boundlr; case/andP; apply: ltreif_trans.
Qed.

Lemma ltr_in_int : forall ba bb xa xb x, ~~ (ba && bb) ->
  x \in Interval (BClose ba xa) (BClose bb xb) -> xa < xb.
Proof.
move=> ba bb xa xb x; case bab: (_ && _)=> // _.
by move/ltreif_in_int; rewrite bab.
Qed.

Lemma ler_in_int : forall ba bb xa xb x,
  x \in Interval (BClose ba xa) (BClose bb xb) -> xa <= xb.
Proof. by move=> ba bb xa xb x; move/ltreif_in_int; move/ltreifW. Qed.

(* Lemma subinP' : forall (i2 i1 : interval), reflect {subset i1 <= i2}  (subint i1 i2). *)
(* Proof. *)
(* move=> i2 i1; apply: (iffP idP); first exact: subintP. *)
(* move: i1 i2=> [[[] a1|] [[] b1|]] [[[] a2|] [[] b2|]] //=.  *)


Lemma mem0_intcc_xNx : forall x, (0 \in `[-x, x]) = (0 <= x).
Proof.
by move=> x; rewrite !inE; case hx: (0 <= _); rewrite (andbT, andbF) ?ge0_cp.
Qed.

Lemma mem0_intoo_xNx : forall x, 0 \in `](-x), x[ = (0 < x).
Proof.
by move=> x; rewrite !inE; case hx: (0 < _); rewrite (andbT, andbF) ?gt0_cp.
Qed.

Lemma int_splitI : forall a b, forall x,
  x \in Interval a b = (x \in Interval a (BInfty _)) && (x \in Interval (BInfty _) b).
Proof. by move=> [[] a|] [[] b|] x; rewrite ?inE ?andbT. Qed.

Lemma ltreifN_po : forall x y b, y < x ?<= if ~~ b ->  x < y ?<= if b = false.
Proof. by move=> x y [] /=; [apply: ltr_geF|apply: ler_gtF]. Qed.

Lemma ltreifS : forall b x y, x < y -> x < y ?<= if b.
Proof. by case=> x y //; move/ltrW. Qed.

Lemma ltreifT : forall x y, x < y ?<= if true = (x <= y). Proof. by []. Qed.

Lemma ltreifF : forall x y, x < y ?<= if false = (x < y). Proof. by []. Qed.

Lemma ltreif_neg : forall x y b, ORing.cpable x y ->
  x < y ?<= if ~~b = ~~ (y < x ?<= if b).
Proof. by move=> x y [] cxy /=; rewrite (cpable_ltrNge, cpable_lerNgt). Qed.

Lemma int_splitU_po : forall xc bc a b, xc \in Interval a b ->
  forall y, ORing.cpable y xc -> y \in Interval a b =
    (y \in Interval a (BClose bc xc)) || (y \in Interval (BClose (~~bc) xc) b).
Proof.
move=> xc bc [ba xa|] [bb xb|] cab y cyc; move: cab;
 rewrite !int_boundlr /le_boundl /le_boundr /=.
* case/andP=> hac hcb; case hay: ltreif=> /=; case hyb: ltreif=> //=.
  + by case: bc=> /=; case: cpable3P cyc.
  + rewrite ltreifN_po ?andbF // ltreifS // cpable_ltrNge 1?cpable_sym //.
    move/negP:hyb; move/negP; apply: contra.
    case: bb hcb=> /= hcb hyc; first exact: ler_trans hcb.
    exact: ler_lt_trans hcb.
  move/ltreifW:hyb=> hyb; suff: false by [].
  by rewrite -hay -[ba]andbT (ltreif_trans hac).
* rewrite !andbT; move=> hac; case hay: ltreif=> /=; symmetry.
    by case: bc=> /=; case: cpable3P cyc.
  apply: negbTE; move/negP: hay; move/negP; apply: contra.
  by move/ltreifW; rewrite -[ba]andbT -ltreifT; move/(ltreif_trans _); apply.
* move=> hcb; case hyb: ltreif=> /=; symmetry; rewrite ?(andbF, orbF).
    by case: bc=> /=; case: cpable3P cyc.
  apply: negbTE; move/negP: hyb; move/negP; apply: contra.
  by move/ltreifW; rewrite -ltreifT; move/ltreif_trans; apply.
by case: bc=> /=; case: cpable3P cyc.
Qed.

Lemma int_splitU2_po : forall x a b, x \in Interval a b ->
  forall y, ORing.cpable y x -> y \in Interval a b =
    [|| (y \in Interval a (BClose false x)), (y == x)
      | (y \in Interval (BClose false x) b)].
Proof.
move=> x a b hx y cxy; rewrite (@int_splitU_po x false) //.
case hyx: (_ \in _); rewrite //= (@int_splitU_po x true) ?int_xx //=.
by rewrite bound_in_int; move: hx; rewrite int_boundlr; case/andP.
Qed.

Lemma intUff : forall x y b1 b2 a b,
  x \in Interval (BClose b2 y) b -> y \in Interval a (BClose b1 x) ->
  forall z, ORing.cpable z x -> ORing.cpable z y ->
    (z \in Interval a (BClose b1 x)) || (z \in Interval (BClose b2 y) b)
      = (z \in Interval a b).
Proof.
move=> x y b1 b2 a b /= hx hy z czx czy.
rewrite (int_splitU_po (~~b2) hy) //; rewrite (int_splitU_po b1 hx) //.
rewrite negbK orbA orbC -!orbA orbb orbC; symmetry.
rewrite (@int_splitU_po y (~~b2)) //.
  by rewrite -orbA; congr orb; rewrite (@int_splitU_po x b1) ?negbK.
apply: subintP hy=> /=; rewrite le_boundl_refl /=.
move: hx; rewrite int_boundlr; case/andP=> _.
rewrite /le_boundr; case: b=> [[] b|] //=.
  by rewrite implybT.
exact: ltreifS.
Qed.

Lemma oppr_int : forall ba bb (xa xb x : R),
  (-x \in Interval (BClose ba xa) (BClose bb xb))
= (x \in Interval (BClose bb (-xb)) (BClose ba (-xa))).
Proof. by move=> [] [] xa xb x; rewrite ?inE lter_oppr andbC lter_oppl. Qed.

Lemma oppr_intoo : forall (a b x : R), (-x \in `]a, b[) = (x \in `](-b), (-a)[).
Proof. by move=> a b x; apply: oppr_int. Qed.

Lemma oppr_intco : forall (a b x : R), (-x \in `[a, b[) = (x \in `](-b), (-a)]).
Proof. by move=> a b x; apply: oppr_int. Qed.

Lemma oppr_intoc : forall (a b x : R), (-x \in `]a, b]) = (x \in `[(-b), (-a)[).
Proof. by move=> a b x; apply: oppr_int. Qed.

Lemma oppr_intcc : forall (a b x : R), (-x \in `[a, b]) = (x \in `[(-b), (-a)]).
Proof. by move=> a b x; apply: oppr_int. Qed.

End IntervalPo.

Notation "`[ a , b ]" := (Interval (BClose true a) (BClose true b))
  (at level 0, a, b at level 9 , format "`[ a ,  b ]") : ring_scope.
Notation "`] a , b ]" := (Interval (BClose false a) (BClose true b))
  (at level 0, a, b at level 9 , format "`] a ,  b ]") : ring_scope.
Notation "`[ a , b [" := (Interval (BClose true a) (BClose false b))
  (at level 0, a, b at level 9 , format "`[ a ,  b [") : ring_scope.
Notation "`] a , b [" := (Interval (BClose false a) (BClose false b))
  (at level 0, a, b at level 9 , format "`] a ,  b [") : ring_scope.
Notation "`] '-oo' , b ]" := (Interval (BInfty _) (BClose true b))
  (at level 0, b at level 9 , format "`] '-oo' ,  b ]") : ring_scope.
Notation "`] '-oo' , b [" := (Interval (BInfty _) (BClose false b))
  (at level 0, b at level 9 , format "`] '-oo' ,  b [") : ring_scope.
Notation "`[ a , '+oo' [" := (Interval (BClose true a) (BInfty _))
  (at level 0, a at level 9 , format "`[ a ,  '+oo' [") : ring_scope.
Notation "`] a , '+oo' [" := (Interval (BClose false a) (BInfty _))
  (at level 0, a at level 9 , format "`] a ,  '+oo' [") : ring_scope.
Notation "`] -oo , '+oo' [" := (Interval (BInfty _) (BInfty _))
  (at level 0, format "`] -oo ,  '+oo' [") : ring_scope.

Notation "x < y ?<= 'if' b" := (ltreif x y b)
  (at level 70, y at next level,
  format "x '[hv'  <  y '/'  ?<=  'if'  b ']'") : ring_scope.

Section IntervalOrdered.

Variable R : oIdomainType.

Lemma int_splitU : forall (xc : R) bc a b, xc \in Interval a b ->
  forall y, y \in Interval a b
    = (y \in Interval a (BClose bc xc)) || (y \in Interval (BClose (~~bc) xc) b).
Proof. by move=> xc bc a b hxc y; apply: int_splitU_po. Qed.

Lemma int_splitU2 : forall (x : R) a b, x \in Interval a b ->
  forall y, y \in Interval a b =
    [|| (y \in Interval a (BClose false x)), (y == x)
      | (y \in Interval (BClose false x) b)].
Proof. by move=> x a b hx y; apply: int_splitU2_po. Qed.

End IntervalOrdered.

Section IntervalField.

Variable R : oFieldType.

Lemma mid_in_int : forall ba bb (xa xb : R), xa < xb ?<= if (ba && bb)
  -> mid xa xb \in Interval (BClose ba xa) (BClose bb xb).
Proof.
by move=> [] [] xa xb /= hx; apply/int_dec=> /=; rewrite ?midf_lte // ?ltrW.
Qed.

Lemma mid_in_intoo : forall (xa xb : R), xa < xb -> mid xa xb \in `]xa, xb[.
Proof. by move=> xa xb hx; apply: mid_in_int. Qed.

Lemma mid_in_intcc : forall (xa xb : R), xa <= xb -> mid xa xb \in `[xa, xb].
Proof. by move=> xa xb hx; apply: mid_in_int. Qed.

End IntervalField.
