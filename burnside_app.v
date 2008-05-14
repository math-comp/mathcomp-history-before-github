Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq fintype div ssralg.
Require Import connect groups action frobenius_cauchy group_perm signperm.
Require Import tuple finfun bigops finset.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits. 

Import GroupScope.

Section colouring.

Variable n : nat.
Definition  colors := I_(n).
Canonical Structure colors_eqType := Eval hnf in [eqType of colors].
Canonical Structure colors_finType := Eval hnf in [finType of colors].

Section square_colouring.

Definition square := I_(4).
Canonical Structure square_eqType := Eval hnf in [eqType of square].
Canonical Structure square_subType := Eval hnf in [subType of square].
Canonical Structure square_finType := Eval hnf in [finType of square].
Canonical Structure square_subFinType := Eval hnf in [subFinType of square].

Definition mksquare i : square := Sub (i %% _) (ltn_mod i 4).
Definition c0 := mksquare 0.
Definition c1 := mksquare 1.
Definition c2 := mksquare 2.
Definition c3 := mksquare 3.

(*rotations*)
Definition R1 (sc : square) : square := tsub [tuple c1; c2; c3; c0] sc.

Definition R2 (sc : square) : square := tsub [tuple c2; c3; c0; c1] sc.

Definition R3 (sc : square) : square := tsub [tuple c3; c0; c1; c2] sc.

Ltac get_inv elt l :=
  match l with 
  | (_, (elt, ?x))  => x
  | (elt, ?x)  => x
  | (?x, _) => get_inv elt x
  end.

Definition rot_inv := ((R1, R3), (R2, R2), (R3, R1)).

Ltac inj_tac :=
  move: (erefl rot_inv); unfold rot_inv;
  match goal with |- ?X = _ -> injective ?Y =>
    move=> _; let x := get_inv Y X in
    apply: (can_inj (g:=x)); move => [val H1] 
  end.

Lemma R1_inj :  injective R1.
Proof. by inj_tac; repeat (destruct val => //=; first by apply /eqP). Qed.

Lemma R2_inj :  injective R2.
Proof. by inj_tac; repeat (destruct val => //=; first by apply /eqP). Qed.

Lemma R3_inj: injective R3.
Proof. by inj_tac; repeat (destruct val => //=; first by apply /eqP). Qed.

Definition r1 := (perm_of R1_inj).
Definition r2 := (perm_of R2_inj).
Definition r3 := (perm_of R3_inj).
Definition id1:= (1 : {perm square}).

Definition is_rot (r : {perm _}) :=  (r * r1 == r1 * r).
Definition rot := [set r | is_rot r].

Lemma group_set_rot: group_set rot.
Proof.
apply /group_setP;split; first  by rewrite /rot  inE /is_rot mulg1 mul1g.
move => x1 y; rewrite /rot !inE /= /is_rot; move/eqP => hx1; move/eqP => hy.
by rewrite -mulgA hy !mulgA hx1.
Qed.

Canonical Structure rot_group:= Group group_set_rot.

Definition rotations := [set id1; r1; r2; r3].

Lemma rot_eq_c0: forall r s : {perm square},
  is_rot r -> is_rot s -> r c0 = s c0 -> r = s.
Proof.
rewrite /is_rot => r s; move/eqP => hr; move/eqP=> hs hrs; apply/permP => a.
have ->: a = (r1 ^+ a) c0 
   by apply/eqP; case: a; do 4?case => //=; rewrite ?permM !permE.
by rewrite -!permM -!commuteX   //  !permM hrs.
Qed.

Lemma rot_r1: forall r, is_rot r -> r = r1 ^+ (r c0).
Proof.
move=> r hr;apply: rot_eq_c0 => //;apply/eqP.
   by symmetry; exact: commuteX.
by case: (r c0); do 4?case => //=; rewrite ?permM !permE  /=.
Qed.

Lemma rotations_is_rot: forall r, r \in rotations -> is_rot r.
Proof.
move=> r Dr; apply/eqP; apply/permP => a; rewrite inE !permM in Dr *.
by case/or4P: Dr; move/eqP->; rewrite !permE //; case: a; do 4?case.
Qed.

Lemma rot_is_rot: rot = rotations.
Proof.
apply/setP=> r; apply/idP/idP; last by move/rotations_is_rot; rewrite inE.
rewrite !inE => h.
have -> : r = r1 ^+ (r c0) by apply: rot_eq_c0; rewrite // -rot_r1.
have e2: 2 = r2 c0 by rewrite permE /=.
have e3: 3 = r3 c0 by rewrite permE /=.
case (r c0); do 4?[case] => // ?; rewrite ?(expg1, eqxx, orbT) //.
  by rewrite [nat_of_ord _]/= e2 -rot_r1 ?(eqxx, orbT, rotations_is_rot, inE).
by rewrite [nat_of_ord _]/= e3 -rot_r1 ?(eqxx, orbT, rotations_is_rot, inE).
Qed.

(*symmetries*)
Definition Sh (sc : square) : square := tsub [tuple c1; c0; c3; c2] sc.

Lemma Sh_inj: injective Sh.
Proof.
by apply:(can_inj (g:= Sh));  case; do 4?case  => //=;move=> H;apply /eqP.
Qed.

Definition sh := (perm_of Sh_inj).

Lemma sh_inv : sh^-1 = sh.
Proof.
apply:(mulg_injr sh);rewrite mulVg ;apply/permP.
by case; do 4?case  => //=; move=> H;rewrite !permE /= !permE; apply /eqP.
Qed.

Definition Sv (sc : square) : square := tsub [tuple c3; c2; c1; c0] sc.

Lemma Sv_inj: injective Sv.
Proof.
by apply : (can_inj (g:= Sv));case; do 4?case  => //=;move => H;apply /eqP.
Qed.

Definition sv := (perm_of Sv_inj).

Lemma sv_inv: sv^-1 = sv.
Proof.
apply:(mulg_injr sv);rewrite mulVg ;apply/permP.
by case; do 4?case  => //=; move=> H; rewrite !permE /= !permE; apply /eqP.
Qed.

Definition Sd1 (sc : square) : square := tsub [tuple c0; c3; c2; c1] sc.

Lemma Sd1_inj : injective Sd1.
Proof.
by apply: can_inj Sd1 _; case; do 4?case=> //=; move=> H; apply /eqP.
Qed.

Definition sd1 := (perm_of Sd1_inj).

Lemma sd1_inv : sd1^-1 = sd1.
Proof.
apply: (mulg_injr sd1); rewrite mulVg; apply/permP.
by case; do 4?case=> //=; move=> H; rewrite !permE /= !permE; apply /eqP.
Qed.

Definition Sd2 (sc : square) : square := tsub [tuple c2; c1; c0; c3] sc.

Lemma Sd2_inj : injective Sd2.
Proof.
by apply: can_inj Sd2 _; case; do 4?case=> //=; move=> H; apply /eqP.
Qed.

Definition sd2 := (perm_of Sd2_inj).

Lemma sd2_inv : sd2^-1 = sd2.
Proof.
apply: (mulg_injr sd2); rewrite mulVg; apply/permP.
by case; do 4?case=> //=; move=> H; rewrite !permE /= !permE; apply/eqP.
Qed.

Lemma ord_enum4: sval (ord_enum 4) = [:: c0; c1; c2; c3].
Proof. by apply: (inj_maps (@val_inj _ _ _)); exact: (svalP (ord_enum 4)). Qed.

Lemma diff_id_sh: 1 != sh.
Proof.
by apply/eqP; move/(congr1 (fun p : {perm square} => p c0)); rewrite !permE.
Qed.

Definition isometries2 := [set 1; sh].

Lemma card_iso2: #|isometries2| = 2.
Proof. by rewrite cards2 diff_id_sh. Qed.

Lemma group_set_iso2 : group_set isometries2.
Proof.
apply/group_setP; split => [|x y]; rewrite !inE ?eqxx //.
do 2![case/orP; move/eqP->]; gsimpl; rewrite ?(eqxx, orbT) //.
by rewrite -/sh -{1}sh_inv mulVg eqxx.
Qed.
Canonical Structure iso2_group:= Group group_set_iso2.

Definition isometries :=
  [set p | [|| p == 1, p == r1, p == r2, p == r3,
            p == sh, p == sv, p == sd1 | p == sd2 ]].

Definition opp (sc : square) := tsub [tuple c2; c3; c0; c1] sc.

Definition is_iso (p : {perm square}) := forall ci, p (opp ci) = opp (p ci).

Lemma isometries_iso : forall p, p \in isometries -> is_iso p.
Proof.
move=> p; rewrite inE.
by do ?case/orP; move/eqP=> -> a; rewrite !permE; case: a; do 4?case.
Qed.

Ltac non_inj p a1 a2 heq1 heq2 := 
let h1:= fresh "h1" in 
(absurd (p a1 = p a2);first (by red; move=> h1;move:(perm_inj h1));
by rewrite heq1 heq2;apply/eqP).

Ltac is_isoPtac p f e0 e1 e2 e3 := 
  suff ->: p = f by [rewrite inE eqxx ?orbT];
  let e := fresh "e" in apply/permP;
  do 5?[case] => // ?; [move: e0 | move: e1 | move: e2 | move: e3] => e;
  apply: etrans (congr1 p _) (etrans e _); apply/eqP; rewrite // permE.

Lemma is_isoP : forall p, reflect (is_iso p) (p \in isometries).
Proof.
move=> p; apply: (iffP idP) => [|iso_p]; first exact: isometries_iso.
move e1: (p c1) (iso_p c1) => k1; move e0: (p c0) (iso_p c0) k1 e1 => k0.
case: k0 e0; do 4?[case] => //= ? e0 e2; do 5?[case] => //= ? e1 e3;
 try by [non_inj p c0 c1 e0 e1 | non_inj p c0 c3 e0 e3].
by is_isoPtac p id1 e0 e1 e2 e3.
by is_isoPtac p sd1 e0 e1 e2 e3.
by is_isoPtac p sh e0 e1 e2 e3.
by is_isoPtac p r1 e0 e1 e2 e3.
by is_isoPtac p sd2 e0 e1 e2 e3.
by is_isoPtac p r2 e0 e1 e2 e3.
by is_isoPtac p r3 e0 e1 e2 e3.
by is_isoPtac p sv e0 e1 e2 e3.
Qed.


Lemma group_set_iso: group_set isometries.
Proof.
apply/group_setP; split; first by rewrite inE eqxx /=.
by move=> x y hx hy; apply/is_isoP => ci; rewrite !permM !isometries_iso.
Qed.

Canonical Structure iso_group := Group group_set_iso.

Lemma card_rot: #|rot| = 4.
Proof.
rewrite -[4]/(size [:: id1; r1; r2; r3]) -(card_uniqP _).
  by apply: eq_card => x; rewrite rot_is_rot  !inE orbF.
by apply: maps_uniq (fun p : {perm square} => p c0) _ _; rewrite /= !permE.
Qed.

Lemma group_set_rotations : group_set rotations.
Proof. by rewrite -rot_is_rot group_set_rot. Qed.

Canonical Structure rotations_group := Group group_set_rotations.

Definition col_squares := {{ffun square -> colors} : as finType}.

Definition act_f (sc : col_squares) (p : {perm square}) : col_squares := 
  [ffun z => sc (p^-1 z)].

Lemma act_f_1:  forall k, act_f k 1 = k.
Proof. by move=> k; apply/ffunP=> a; rewrite ffunE invg1 permE. Qed.

Lemma act_f_morph:  forall k x y, act_f k (x * y) = act_f (act_f k x) y.
Proof. by move=> k x y; apply/ffunP=> a; rewrite !ffunE invMg permE. Qed.

Definition to := Action act_f_1 act_f_morph.

Definition square_coloring_number2 := act_nbcomp to iso2_group.
Definition square_coloring_number4 := act_nbcomp to rot_group.
Definition square_coloring_number8 := act_nbcomp to iso_group.


Lemma Fid : act_fix1 to 1 = setT.
Proof. by apply/setP=> x /=; rewrite !inE act1 eqxx. Qed.

Lemma card_Fid: #|act_fix1 to 1| = (n ^ 4)%N.
Proof.
rewrite -[4]card_ord -[n]card_ord -card_ffun_on Fid cardsE.
by symmetry; apply: eq_card => f; exact/ffun_onP.
Qed.

Definition coin0 (sc : col_squares) : colors := sc c0.
Definition coin1 (sc : col_squares) : colors := sc c1.
Definition coin2 (sc : col_squares) : colors := sc c2.
Definition coin3 (sc : col_squares) : colors := sc c3.

Lemma eqperm_map : forall p1 p2 : col_squares,
  (p1 == p2) = all (fun s => p1 s == p2 s) [:: c0; c1; c2; c3].
Proof.
move=> p1 p2; apply/eqP/allP=> [-> // | Ep12]; apply/ffunP=> x.
by apply/eqP; apply Ep12; case: x; do 4!case=> //.
Qed.

Lemma F_Sh :
  act_fix1 to sh = [set x | (coin0 x == coin1 x) && (coin2 x == coin3 x)].
Proof.
apply/setP=> x; rewrite !inE eqperm_map /= /act_f sh_inv !ffunE !permE /=.
by rewrite eq_sym (eq_sym (x c3)) andbT andbA !andbb.
Qed.

Lemma F_Sv :
   act_fix1 to sv = [set x | (coin0 x == coin3 x) && (coin2 x == coin1 x)].
Proof.
apply/setP => x; rewrite !inE eqperm_map /= /act_f sv_inv !ffunE !permE /=.
by rewrite eq_sym andbT andbC (eq_sym (x c1)) andbA -andbA !andbb andbC.
Qed.

Ltac inv_tac :=
  apply: esym (etrans _ (mul1g _)); apply: canRL (mulgK _) _;
  let a := fresh "a" in apply/permP => a;
  apply/eqP; rewrite permM !permE; case: a; do 4?case.

Lemma r1_inv: r1^-1 = r3.
Proof. by inv_tac. Qed.

Lemma r2_inv: r2^-1 = r2.
Proof. by inv_tac. Qed.

Lemma r3_inv: r3^-1 = r1.
Proof. by inv_tac. Qed.

Lemma F_r2 :
  act_fix1 to r2 = [set x | (coin0 x == coin2 x) && (coin1 x == coin3 x)].
Proof.
apply/setP => x; rewrite !inE eqperm_map /= /act_f r2_inv !ffunE !permE /=.
by rewrite eq_sym andbT andbCA andbC (eq_sym (x c3)) andbA -andbA !andbb andbC.
Qed.

Lemma F_r1 : act_fix1 to r1 = 
  [set x | (coin0 x == coin1 x)&&(coin1 x == coin2 x)&&(coin2 x == coin3 x)].
Proof.
apply/setP => x; rewrite !inE eqperm_map /= /act_f r1_inv !ffunE !permE andbC.
by do 3![case E: {+}(_ == _); rewrite // {E}(eqP E)]; rewrite eqxx.
Qed.

Lemma F_r3 : act_fix1 to r3 =
  [set x | (coin0 x == coin1 x)&&(coin1 x == coin2 x)&&(coin2 x == coin3 x)].
Proof.
apply/setP => x; rewrite !inE eqperm_map /= /act_f r3_inv !ffunE !permE /=.
by do 3![rewrite eq_sym; case E: {+}(_ == _); rewrite // {E}(eqP E)].
Qed.

Lemma card_n2 : forall x y z t : square, uniq [:: x; y; z; t] ->
  #|[set p : col_squares | (p x == p y) && (p z == p t)]| = (n ^ 2)%N.
Proof.
move=> x y z t Uxt; rewrite -[n]card_ord.
pose f (p : col_squares) := (p x, p z); rewrite -(@card_dimage _ _ f).
  rewrite -mulnn -card_prod; apply: eq_card => [] [c d] /=; apply/imageP.
  rewrite (uniq_cat [::x; y]) in Uxt; case/and3P: Uxt => _.
  rewrite /= !orbF !andbT; case/norP; rewrite !inE !orbF => nxzt nyzt _.
  exists [ffun i => if pred2 x y i then c else d].
    by rewrite !inE /= !ffunE !eqxx orbT (negbET nxzt) (negbET nyzt) !eqxx.
  by rewrite {}/f !ffunE /= eqxx (negbET nxzt).
move=> p1 p2; rewrite !inE.
case/andP=> p1y p1t; case/andP=> p2y p2t [px pz].
have eqp12: all (fun i => p1 i == p2 i) [:: x; y; z; t].
  by rewrite /= -(eqP p1y) -(eqP p1t) -(eqP p2y) -(eqP p2t) px pz !eqxx.
apply/ffunP=> i; apply/eqP; apply: (allP eqp12). 
by rewrite (subset_cardP _ (subset_predT _)) // (card_uniqP Uxt) card_ord.
Qed.

Lemma card_n :
 #|[set x | (coin0 x == coin1 x)&&(coin1 x == coin2 x)&& (coin2 x == coin3 x)]|
   = n.
Proof.
rewrite -[n]card_ord /coin0 /coin1 /coin2 /coin3.
pose f (p : col_squares) := p c3; rewrite -(@card_dimage _ _ f).
  apply: eq_card => c /=; apply/imageP.
  exists ([ffun => c] : col_squares); last by rewrite /f ffunE.
  by rewrite /= inE !ffunE !eqxx.
move=> p1 p2; rewrite /= !inE /f -!andbA => eqp1 eqp2 eqp12.
apply/eqP; rewrite eqperm_map /= andbT.
case/and3P: eqp1; do 3!move/eqP->; case/and3P: eqp2; do 3!move/eqP->.
by rewrite !andbb eqp12.
Qed.

Lemma burnside_app2: (square_coloring_number2 * 2 = n ^ 4 + n ^ 2)%N.
Proof.
rewrite -{1}card_iso2 -(Frobenius_Cauchy to iso2_group) /=.
rewrite (eq_bigl (mem [:: id1; sh])) => [|p] /=; last first.
  by rewrite  !inE orbF.
rewrite -big_uniq /=; last by rewrite !inE orbF diff_id_sh.
by rewrite /reducebig unlock  /= addn0 card_Fid F_Sh card_n2 //= !muln1.
Qed.

Lemma burnside_app_rot:
  (square_coloring_number4 * 4 = n ^ 4 + n ^ 2 + 2 * n)%N.
Proof.
rewrite -{1}card_rot -(Frobenius_Cauchy to rot_group).
rewrite (eq_bigl (mem [:: id1; r1; r2; r3])) => [|p] /=; last first.
  by rewrite rot_is_rot !inE orbF.
rewrite -big_uniq; last first.
  by apply: maps_uniq (fun p : {perm square} => p c0) _ _; rewrite /= !permE.
rewrite /reducebig unlock /= !addn0 card_Fid F_r1 F_r2 F_r3 card_n card_n2 //=.
ring.
Qed.

Lemma F_Sd1 : act_fix1 to sd1 = [set x | coin1 x == coin3 x].
Proof.
apply/setP => x; rewrite !inE eqperm_map /= /act_f sd1_inv !ffunE !permE /=.
by rewrite !eqxx !andbT eq_sym /= andbb.
Qed.

Lemma card_n3 : forall x y : square, x != y ->
  #|[set k : col_squares | k x == k y]| = (n ^ 3)%N.
Proof.
move=> x y nxy; apply/eqP; case: (ltngtP n 0) => // [|n0]; last first.
  by rewrite n0; apply/existsP=> [] [p _]; case: (p c0) => i; rewrite n0.
move/eqn_pmul2l <-; rewrite -expnS -card_Fid Fid cardsT.
rewrite -{1}[n]card_ord -cardX.
pose pk k := [ffun i => k (if i == y then x else i) : colors].
rewrite -(@card_image _ _ (fun k : col_squares => (k y, pk k))).
  apply/eqP; apply: eq_card => ck /=;  rewrite inE /= inE.
  apply/eqP/imageP; last first.
    by case=> k _ -> /=; rewrite !ffunE if_same eqxx.
  case: ck => c k /= kxy.
  exists [ffun i => if i == y then c else k i]; first by rewrite inE.
  rewrite !ffunE eqxx; congr (_, _); apply/ffunP=> i; rewrite !ffunE.
  case Eiy: (i == y); last by rewrite Eiy.
  by rewrite (negbET nxy) (eqP Eiy).
move=> k1 k2 [Eky Epk]; apply/ffunP=> i.
have{Epk}: pk k1 i = pk k2 i by rewrite Epk.
by rewrite !ffunE; case: eqP => // ->.
Qed.

Lemma F_Sd2 : act_fix1 to sd2 = [set x | coin0 x == coin2 x].
Proof.
apply/setP => x; rewrite !inE eqperm_map /= /act_f sd2_inv !ffunE !permE /=.
by rewrite !eqxx !andbT eq_sym /= andbb.
Qed.

Lemma burnside_app_iso :
  (square_coloring_number8 * 8 = n ^ 4 + 2 * n ^ 3 + 3 * n ^ 2 + 2 * n)%N.
Proof.
pose iso_list := [:: id1; r1; r2; r3; sh; sv; sd1; sd2].
have Uiso: uniq iso_list.
  apply: maps_uniq (fun p : {perm square} => (p c0, p c1)) _ _.
  by rewrite /= !permE.
have Eiso: iso_group =i iso_list by move=> p; rewrite /= !inE orbF.
have <-: #|iso_group| = 8 by rewrite (eq_card Eiso) (card_uniqP Uiso).
rewrite -(Frobenius_Cauchy to) (eq_bigl _ _ Eiso) -big_uniq //.
rewrite /reducebig unlock /= card_Fid F_r1 F_r2 F_r3 F_Sh F_Sv F_Sd1 F_Sd2.
by rewrite card_n !card_n3 // !card_n2 //=; ring.
Qed.

End square_colouring.

Section cube_colouring.

Definition cube := I_(6).
Canonical Structure cube_eqType := Eval hnf in [eqType of cube].
Canonical Structure cube_subType := Eval hnf in [subType of cube].
Canonical Structure cube_finType := Eval hnf in [finType of cube].
Canonical Structure cube_subFinType := Eval hnf in [subFinType of cube].

Definition mkFcube i : cube := Sub (i %% 6) (ltn_mod i 6).
Definition F0:= mkFcube 0.
Definition F1:= mkFcube 1.
Definition F2:= mkFcube 2.
Definition F3:= mkFcube 3.
Definition F4:= mkFcube 4.
Definition F5:= mkFcube 5.

(* axial symetries*) 
Definition S05 :=[:: F0;F4; F3; F2; F1; F5].
Definition S05f (sc : cube):cube := tsub [tuple of S05] sc.


Definition S14 :=[:: F5;F1; F3; F2; F4; F0].
Definition S14f (sc : cube):cube := tsub [tuple of S14] sc.

Definition S23 :=[:: F5;F4; F2; F3; F1; F0].
Definition S23f (sc : cube):cube := tsub [tuple of S23] sc.

(* rotations 90 *)
Definition R05 := [:: F0; F2; F4; F1; F3; F5].
Definition R05f (sc : cube):cube := tsub [tuple of R05] sc.
Definition R50:= [:: F0; F3; F1; F4; F2; F5].
Definition R50f (sc : cube):cube := tsub  [tuple of R50] sc.
Definition R14 := [:: F3; F1; F0; F5; F4; F2].
Definition R14f (sc : cube):cube := tsub [tuple of R14] sc.
Definition R41 := [:: F2; F1; F5; F0; F4; F3].
Definition R41f (sc : cube):cube := tsub [tuple of R41] sc.
Definition R23 := [:: F1; F5; F2; F3; F0; F4].
Definition R23f (sc : cube):cube := tsub [tuple of R23] sc.
Definition R32 := [:: F4; F0; F2; F3; F5; F1].
Definition R32f (sc : cube):cube := tsub [tuple of R32] sc.
(* rotations 120 *)
Definition R024 := [:: F2; F5; F4; F1; F0; F3].
Definition R024f (sc : cube):cube := tsub [tuple of R024] sc.
Definition R135 := [:: F4; F3; F0; F5; F2; F1].
Definition R135f (sc : cube):cube := tsub [tuple of  R135] sc.
Definition R012 :=[:: F1; F2; F0; F5; F3; F4]. 
Definition R012f (sc : cube):cube := tsub [tuple of  R012] sc. 
Definition R345 :=[:: F2; F0; F1; F4; F5; F3]. 
Definition R345f (sc : cube):cube := tsub [tuple of  R345] sc. 
Definition R031 := [::  F3; F0; F4; F1; F5; F2].
Definition R031f (sc : cube):cube := tsub [tuple of  R031] sc. 
Definition R425:=[:: F1; F3; F5; F0; F2; F4].
Definition R425f (sc : cube):cube := tsub [tuple of  R425]  sc. 
Definition R043 :=[:: F4; F2; F5; F0; F3; F1].
Definition R043f (sc : cube):cube := tsub [tuple of  R043]  sc. 
Definition R215 :=[:: F3; F5; F1; F4; F0; F2].
Definition R215f (sc : cube):cube := tsub  [tuple of  R215] sc. 

(* last symmetries*)
Definition S1 :=[:: F5; F2; F1; F4; F3; F0].
Definition S1f (sc : cube):cube := tsub  [tuple of  S1] sc. 
Definition S2 :=[::  F5; F3; F4; F1; F2; F0].
Definition S2f (sc : cube):cube := tsub  [tuple of  S2]sc. 
Definition S3 :=[::  F1; F0; F3; F2; F5; F4].
Definition S3f  (sc : cube):cube := tsub  [tuple of  S3]sc. 
Definition S4:=[:: F4; F5; F3; F2; F0; F1].
Definition S4f  (sc : cube):cube := tsub  [tuple of  S4]sc. 
Definition S5 :=[::  F2; F4; F0; F5; F1; F3].
Definition S5f  (sc : cube):cube := tsub [tuple of  S5] sc.
Definition S6 :=[::F3; F4; F5; F0; F1; F2].
Definition S6f  (sc : cube):cube := tsub [tuple of  S6]  sc. 

Lemma S1_inv: involutive S1f.
Proof. move => z;apply /eqP;case : z ; do 6!case =>//=. Qed.
Lemma S2_inv: involutive S2f.
Proof. move => z;apply /eqP;case : z ; do 6!case =>//=. Qed.
Lemma S3_inv: involutive S3f.
Proof. move => z;apply /eqP;case : z ; do 6!case =>//=. Qed.
Lemma S4_inv: involutive S4f.
Proof. move => z;apply /eqP;case : z ; do 6!case =>//=. Qed.
Lemma S5_inv: involutive S5f.
Proof. move => z;apply /eqP;case : z ; do 6!case =>//=. Qed.
Lemma S6_inv: involutive S6f.
Proof. move => z;apply /eqP;case : z ; do 6!case =>//=. Qed.

Lemma S05_inj:injective S05f.
Proof.
by apply:(can_inj (g:= S05f)) => z; apply /eqP;case : z ; do 6!case =>//=. 
Qed.
 
Lemma S14_inj:injective S14f.
Proof. 
by apply:(can_inj (g:= S14f)) => z; apply /eqP;case : z ; do 6!case =>//=.
Qed.

Lemma S23_inv: involutive S23f.
Proof. by move => z;apply /eqP;case : z ; do 6!case =>//=. Qed.

Lemma R05_inj:injective R05f.
Proof.
by apply:(can_inj (g:= R50f)) => z; apply /eqP;case : z ; do 6!case =>//=. 
Qed.
 
Lemma R14_inj:injective R14f.
Proof. 
by apply:(can_inj (g:= R41f)) => z; apply /eqP;case : z ; do 6!case =>//=.  
Qed.

Lemma R23_inj:injective R23f.
Proof. 
by apply:(can_inj (g:= R32f)) => z; apply /eqP;case : z ; do 6!case =>//=.  
Qed.

Lemma R50_inj:injective R50f.
Proof. 
by apply:(can_inj (g := R05f)) => z; apply /eqP;case : z ; do 6!case =>//=.  
Qed.
Lemma R41_inj:injective R41f.
Proof. 
by apply:(can_inj (g := R14f)) => z; apply /eqP;case : z ; do 6!case =>//=.  
Qed.
Lemma R32_inj:injective R32f.
Proof. 
by apply:(can_inj (g:= R23f)) => z; apply /eqP;case : z ; do 6!case =>//=.  
Qed.
Lemma R024_inj:injective R024f.
Proof. 
by apply:(can_inj (g:= R135f)) => z; apply /eqP;case : z ; do 6!case =>//=.  
Qed.
Lemma R135_inj:injective R135f.
Proof. 
by apply:(can_inj (g:= R024f)) => z; apply/eqP;case : z; do 6!case =>//=.
Qed.
Lemma R012_inj:injective R012f.
Proof. 
by apply:(can_inj (g:= R345f)) => z; apply /eqP;case : z ; do 6!case =>//=.  
Qed.
Lemma R345_inj:injective R345f.
Proof. 
by apply:(can_inj (g:= R012f)) => z; apply/eqP;case : z; do 6!case =>//=.
Qed.
Lemma R031_inj:injective R031f.
Proof. 
by apply:(can_inj (g:= R425f)) => z; apply /eqP;case : z ; do 6!case =>//=.  
Qed.
Lemma R425_inj:injective R425f. 
Proof. 
by apply:(can_inj (g:= R031f)) => z; apply /eqP;case : z ; do 6!case =>//=.  
Qed.
Lemma R043_inj:injective R043f.
Proof. 
by apply:(can_inj (g:= R215f)) => z; apply /eqP;case : z ; do 6!case =>//=.  
Qed.
Lemma R215_inj:injective R215f.
Proof. 
by apply:(can_inj (g:= R043f)) => z; apply /eqP;case : z ; do 6!case =>//=.  
Qed.

Definition id3:= (1 : {perm cube}).
Definition s05 := (perm_of S05_inj).
Definition s14 :{perm cube_finType}.
Proof.
apply: (@perm_of _ S14f); apply:(@can_inj _ _ _ S14f)=> z.
by apply /eqP;case : z ; do 6!case =>//=. 
Defined.

Definition s23 := (perm_of (inv_inj S23_inv)).
Definition r05 := (perm_of R05_inj).
Definition r14 := (perm_of R14_inj).
Definition r23 := (perm_of R23_inj).
Definition r50 := (perm_of R50_inj).
Definition r41 := (perm_of R41_inj).
Definition r32 := (perm_of R32_inj).
Definition r024 := (perm_of R024_inj).
Definition r135 := (perm_of R135_inj).
Definition r012 := (perm_of R012_inj).
Definition r345 := (perm_of R345_inj).
Definition r031 := (perm_of R031_inj).
Definition r425 := (perm_of R425_inj).
Definition r043 := (perm_of R043_inj).
Definition r215 := (perm_of R215_inj).

Definition s1 := (perm_of (inv_inj S1_inv)).
Definition s2 := (perm_of (inv_inj S2_inv)).
Definition s3 := (perm_of (inv_inj S3_inv)).
Definition s4 := (perm_of (inv_inj S4_inv)).
Definition s5 := (perm_of (inv_inj S5_inv)).
Definition s6 := (perm_of (inv_inj S6_inv)).

Definition dir_iso3 := [set p | 
[|| id3 == p, s05 == p, s14 == p, s23 == p, r05 == p, r14 == p, r23 == p,
 r50 == p, r41 == p, r32 == p, r024 == p, r135 == p, r012 == p, r345 == p, 
 r031 == p, r425 == p, r043 == p, r215 == p,
 s1 == p, s2 == p, s3 == p, s4 == p, s5 == p | s6 == p]].

Definition dir_iso3l := [:: id3; s05; s14; s23; r05; r14; r23; r50; r41; 
  r32; r024; r135; r012; r345; r031; r425; r043 ; r215;
  s1 ; s2; s3; s4; s5; s6].

Definition S0 :=[::F5; F4; F3; F2; F1; F0].
Definition S0f  (sc : cube):cube := tsub [tuple of  S0]  sc. 

Lemma S0_inv: involutive S0f.
Proof. move => z;apply /eqP;case : z ; do 6!case =>//=. Qed.

Definition s0 := (perm_of (inv_inj S0_inv)).

Definition is_iso3 (p : {perm cube}) := forall fi, p (s0 fi) = s0 (p fi).


Lemma dir_iso_iso3: forall p, p \in dir_iso3  -> is_iso3 p.
Proof.
move  => p; rewrite inE.
do ?case/orP; move/eqP=> <- a;  rewrite !permE; case: a;
 do 6![case => // ].
Qed.

Lemma iso3_ndir:forall p, p \in dir_iso3  -> is_iso3 (s0 * p).
Proof.
move  => p; rewrite inE.
by do ?case/orP; move/eqP=> <- a;  rewrite !permE /comp /= !permE;
  case: a;do 6![case => // ].
Qed.

(* Lemma ndir_iso3: forall p, p \in dir_iso3  -> (s0 * p) \notin dir_iso3.
Proof.
move  => p; rewrite !setE. 
do ?case/orP; move/eqP=> <-;
do ! [apply/norP;split; first
by apply/eqP; 
   move/(congr1 (fun p : {perm cube} => (p F0, p F1, p F2))); rewrite !permE /comp /= !permE];
by apply/eqP; 
   move/(congr1 (fun p : {perm cube} => (p F0, p F1, p F2))); rewrite !permE /comp /= !permE.
Qed.*)


Definition sop (p : {perm cube}) : seq  cube_finType.
Proof.
by (do 3! case) =>  t  _ _; exact: t.
Defined.

Lemma sop_inj:  injective sop.
Proof.
(do 3! case) =>  t1 ? ?;(do 3! case) =>  t2  ? ? /= H.
by do 5 apply/val_eqP => /=; rewrite H.
Qed.

Let tt := seq cube_finType.
Definition  prod_tuple (t1  t2:tt) := maps  (fun n:I_(6) => sub F0 t2 n  ) t1 .

Lemma sop_spec: forall x (n0:I_(6)), sub F0 (sop x) n0 = x n0.
Proof.
(do 3! case) => t1 i1 j1 /=;rewrite /fun_of_perm /= /fun_of_ffun /proj1_sig /=.
move => n0 /=; case:ffun_fun_def;rewrite /=.
move => x1;case;rewrite //=.
by apply :esym;rewrite enum_rank_ord /=;exact: tsub_sub .
Qed.

Lemma prod_t_correct: forall x y i , 
               (perm_mul x y) i = sub F0 (prod_tuple (sop x) (sop y)) i.
Proof.
move=> x y i /=;rewrite !permE /comp.  rewrite /prod_tuple /=  -!sop_spec.
apply: esym ; apply: (sub_maps F0);case:x;(do 2! case) => t2 i2 j2 /=.
by rewrite (eqP i2);case: i => //= m;rewrite -(card_ord 6).
Qed.

Lemma sop_morph: 
     Monoid.morphism id3  (sop id3) (@perm_mul  cube_finType)   prod_tuple sop.
Proof.
split; first by done.
move => x y; apply:(@eq_from_sub _ F0); last first.
  move => i H.
  have hi: i < 6.
    case: perm_mul H.
    (do 2! case) => t1 i1 j1 /=.
    by rewrite (eqP i1); by rewrite -(card_ord 6).
  have -> : i = (Sub _ : _ -> I_(6)) hi by apply /eqP.
  by rewrite sop_spec prod_t_correct.
rewrite /prod_tuple size_maps.
case:perm_mul;  (do 2! case) => t1 i1 j1 /=; rewrite (eqP i1).
by case:(x); (do 2! case) => t2 i2 j2 /=; rewrite (eqP i2).
Qed.
 
Definition sop1 (p : {perm cube}) := [:: p F0;p F1; p F2; p F3; p F4;p F5].

Definition seq_iso_L:= [:: [:: F0; F1; F2; F3; F4; F5]; S05; S14; S23; R05; 
  R14; R23; R50; R41; R32; R024; R135; R012; R345; R031; R425; R043; R215;
  S1; S2; S3; S4; S5; S6].


Lemma seqs1 : forall x, sop x == sop1 x.
Proof.
do 3! case => //;case.
  by move => H ; apply: False_ind;rewrite card_ord in H.
do 5 (move => x s /= H; move : s H x;
 case; first by move => H ; apply: False_ind;rewrite card_ord in H).
move => x6 ; case; first last.
 by move => s l H;  apply: False_ind;rewrite card_ord in H.
move => H x5 x4 x3 x2 x1 i; rewrite   /sop1 /fun_of_perm /=.
by do 6 case: app_ffunP;rewrite /= !enum_rank_ord /= !(tsub_sub  F0) //=.
Qed.

Lemma Lcorrect: seq_iso_L == maps sop  [::  id3; s05; s14; s23; r05; r14; r23;
  r50;  r41;  r32; r024;  r135;  r012;  r345;  r031;  r425;  r043 ;  r215;
  s1 ;  s2;  s3;  s4;  s5; s6].
Proof.
by rewrite !maps_adds !(eqP ( seqs1 _ )) /sop1  !permE //=.
Qed.

Lemma iso0_1: dir_iso3 =i dir_iso3l.
Proof.
by move=> p; rewrite /= !inE orbF /= !(eq_sym _ p).
Qed.

Lemma L_iso: forall p, p \in dir_iso3  <-> (sop p) \in seq_iso_L.
Proof.
move=> p; rewrite  (eqP Lcorrect) mem_maps ; last by  exact : sop_inj.
by rewrite ?setE ?inE ?orbF /= !(eq_sym _ p).
Qed.

Lemma stable: forall x y, x \in dir_iso3 -> y \in dir_iso3 -> 
                          (x * y) \in dir_iso3.
Proof.
move => x y; rewrite !L_iso => H1 H2.
case: sop_morph => _ ->.
have: (all  ( fun x => 
   (all (fun y => (mem seq_iso_L )(prod_tuple x y)) seq_iso_L))seq_iso_L). 
  by vm_compute.
move/(@allP [eqType of tt]);move  /(_ _ H1).
by move/(@allP [eqType of tt]);move  /(_ _ H2).
Qed.

Lemma iso_eq_F0_F1: forall r s : {perm cube}, r \in dir_iso3 -> 
   s \in dir_iso3 -> r F0 = s F0 -> r F1 = s F1 -> r = s.
Proof.
move=> r s hr hs hrs0 hrs1;apply:sop_inj.
move: hrs0 hrs1; rewrite -!sop_spec =>  h1 h2. 
have Hlr:   (sop r) \in seq_iso_L by case: (L_iso r); move /(_ hr).
have Hls: (sop s) \in seq_iso_L by case: (L_iso s); move /(_ hs).
have :(all  ( fun x => 
       (all (fun y => implb ((sub F0 x F0 == sub F0 y F0)&& 
       (sub F0 x F1 == sub F0 y F1)) ( x==y)) seq_iso_L)) seq_iso_L).
  by vm_compute.
move/allP;  move  /(_ _ Hlr); move/allP; move  /(_ _ Hls).
by rewrite h1 h2 !eqxx /=;move/eqP.
(* do !case/orP => // ;move/eqP=> <- //;
 do !case/orP => // ;move/eqP=> <- //=. : 78sec*)
Qed.

Lemma ndir_s0p: forall p, p \in dir_iso3  -> (s0 * p) \notin dir_iso3.
Proof.
move => p; rewrite !L_iso => H1.
have: (all (fun p  => ~~(mem seq_iso_L ) (prod_tuple S0 p)) seq_iso_L)by vm_compute.
move/(@allP [eqType of tt]);move  /(_ _ H1).
have <- : (sop s0)= S0 by  rewrite  !(eqP ( seqs1 _ )) /sop1 !permE .
by apply:contra; rewrite  L_iso => Hn1; case : sop_morph => _ <-; exact:Hn1.
(*do ?case/orP; move/eqP=> <-;
do ! [apply/norP;split; first
by apply/eqP; 
   move/(congr1 (fun p : {perm cube} => (p F0, p F1, p F2))); rewrite !permE /comp /= !permE];
by apply/eqP; 
   move/(congr1 (fun p : {perm cube} => (p F0, p F1, p F2))); rewrite !permE /comp /= !permE.*)
Qed.


Definition indir_iso3l := maps (perm_mul s0) dir_iso3l.


Definition iso3l:= dir_iso3l ++ indir_iso3l.

Definition seq_iso3_L := maps sop  iso3l.

Lemma eqperm : forall p1 p2 : {perm cube},
  (p1 == p2) = all (fun s => p1 s == p2 s) [:: F0; F1; F2; F3; F4; F5].
Proof.
move=> p1 p2; apply/eqP/allP=> [-> // | Ep12]; apply/permP=> x.
by apply/eqP; apply Ep12; case: x; do 6!case=> //.
Qed.


Lemma iso_eq_F0_F1_F2: forall r s : {perm cube}, is_iso3 r -> 
   is_iso3 s -> r F0 = s F0 -> r F1 = s F1 ->  r F2 = s F2 -> r = s.
Proof.
move=> r s hr hs hrs0 hrs1 hrs2.
move :(hrs0);move:  (hrs1);move: (hrs2).
have e23 : F2 = s0 F3 by apply/eqP;rewrite permE /S0f (tsub_sub F0).
have e14 : F1 = s0 F4 by apply/eqP;rewrite permE /S0f (tsub_sub F0).
have e05: F0 = s0 F5 by apply/eqP;rewrite permE /S0f (tsub_sub F0).
rewrite e23 e14 e05;rewrite !hr !hs.
move/perm_inj=> hrs3; move/perm_inj=> hrs4; move/perm_inj=> hrs5.
apply/eqP; rewrite eqperm.
apply/allP.
move => x.
case/orP; first by move/eqP =>a; rewrite ?a; apply/eqP =>//.
case/orP; first by move/eqP =>a; rewrite ?a; apply/eqP =>//.
by do ![case/orP; first by move/eqP =>a; rewrite ?a; apply/eqP =>//].
Qed.

Ltac iso_tac := 
  let a := fresh "a" in apply/permP => a;
  apply/eqP; rewrite !permM !permE; case: a; do 6?case.

Ltac inv_tac :=
  apply: esym (etrans _ (mul1g _)); apply: canRL (mulgK _) _; iso_tac.

Lemma dir_s0p: forall p,  (s0 * p) \in dir_iso3 -> p \notin dir_iso3.
Proof.
move => p Hs0p; move: (ndir_s0p Hs0p); rewrite mulgA.
have e:  (s0^-1=s0) by inv_tac.
by rewrite -{1}e mulVg mul1g.
Qed.

Definition is_iso3b p :=  (p * s0 == s0 * p).
Definition iso3 := [set p | is_iso3b p].

Lemma is_iso3P : forall p, reflect (is_iso3 p) (p \in iso3).
Proof.
move => p; apply: (iffP idP); rewrite inE /iso3  /is_iso3b /is_iso3 =>e.
  by move => fi; rewrite -!permM (eqP e).
by apply/eqP;apply/permP=> z; rewrite !permM (e z).
Qed.

Lemma group_set_iso3: group_set iso3.
Proof.
apply /group_setP;split.
  by apply/is_iso3P => fi; rewrite -!permM mulg1 mul1g.
move => x1 y; rewrite /iso3 !inE /= /is_iso3.
rewrite /is_iso3b.
rewrite -mulgA. 
move/eqP => hx1; move/eqP => hy.
rewrite hy !mulgA. by  rewrite -hx1.
Qed.

Canonical Structure iso_group3:= Group group_set_iso3.

Lemma group_set_diso3: group_set  dir_iso3.
Proof.
apply/group_setP;split;first by   rewrite inE eqxx /=.
by exact:stable.
Qed.
Canonical Structure diso_group3:= Group group_set_diso3.

Lemma gen_diso3:  dir_iso3 = <<[set r05; r14]>>.
Proof.
apply/setP; apply/subset_eqP;apply/andP; split;first last.
  by rewrite gen_subG;apply/subsetP => x;   rewrite !inE; 
    case/orP; move/eqP =>->; rewrite  eqxx !orbT.
apply/subsetP => x; rewrite !inE.
have -> : s05 = r05 * r05  by iso_tac.
have -> : s14 = r14 * r14  by iso_tac.
have -> : s23 = r14 * r14 * r05 * r05 by iso_tac.
have -> : r23 = r05 * r14 * r05 * r14 * r14 by iso_tac.
have -> : r50 = r05  * r05 * r05 by iso_tac.
have -> : r41 = r14 * r14 * r14 by iso_tac.
have -> : r32 = r14 * r14 * r14 * r05* r14 by iso_tac.
have -> : r024 = r05 * r14 * r14 * r14 by iso_tac.
have -> : r135 = r14 * r05 * r05 * r05 by iso_tac.
have -> : r012 = r14 * r05 by iso_tac.
have -> : r345 = r05 * r14 * r05 * r05 by iso_tac.
have -> : r031 = r05 * r14 by iso_tac.
have -> : r425 = r05 * r05 * r14 * r05 by iso_tac.
have -> : r043 = r14 * r14 * r14 * r05 by iso_tac.
have -> : r215 = r05 * r05 * r05 * r14 by iso_tac.
have -> : s1 = r14 * r14 * r05 by iso_tac.
have -> : s2 = r05 * r14 * r14 by iso_tac.
have -> : s3 = r05 * r14 * r05 by iso_tac.
have -> : s4 = r05 * r14  * r14 * r14 * r05 by iso_tac.
have -> : s5 = r14  * r05 * r05 by iso_tac.
have -> : s6 = r05 * r05 * r14 by iso_tac.
by do ?(case/orP; first move/eqP => <- );
     first (by exact:group1); last (move/eqP => <-);
     do ?apply:groupM; apply:mem_geng; rewrite inE eqxx ?orbT //=.
Qed.


Definition col_cubes := {{ffun cube -> colors} : as finType}.

Definition act_g (sc : col_cubes) (p : {perm cube}) : col_cubes := 
  [ffun z => sc (p^-1 z)].

Lemma act_g_1:  forall k, act_g k 1 = k.
Proof. by move=> k; apply/ffunP=> a; rewrite ffunE invg1 permE. Qed.

Lemma act_g_morph:  forall k x y, act_g k (x * y) = act_g (act_g k x) y.
Proof. by move=> k x y; apply/ffunP=> a; rewrite !ffunE invMg permE. Qed.

Definition to_g := Action act_g_1 act_g_morph.


Definition cube_coloring_number24 := act_nbcomp to_g diso_group3.


Lemma Fid3 : act_fix1 to_g 1 = setT.
Proof. by apply/setP=> x /=; rewrite !inE act1 eqxx. Qed.

Lemma card_Fid3: #|act_fix1 to_g 1| = (n ^ 6)%N.
Proof.
rewrite -[6]card_ord -[n]card_ord -card_ffun_on Fid3 cardsT.
by symmetry; apply: eq_card => ff; exact/ffun_onP.
Qed.

Definition col0 (sc : col_cubes) : colors := sc F0.
Definition col1 (sc : col_cubes) : colors := sc F1.
Definition col2 (sc : col_cubes) : colors := sc F2.
Definition col3 (sc : col_cubes) : colors := sc F3.
Definition col4 (sc : col_cubes) : colors := sc F4.
Definition col5 (sc : col_cubes) : colors := sc F5.

Lemma eqperm_map2 : forall p1 p2 : col_cubes,
  (p1 == p2) = all (fun s => p1 s == p2 s) [:: F0; F1; F2; F3; F4; F5].
Proof.
move=> p1 p2; apply/eqP/allP=> [-> // | Ep12]; apply/ffunP=> x.
by apply/eqP; apply Ep12; case: x; do 6!case=> //.
Qed.


Lemma F_s05 :
  act_fix1 to_g s05 = [set x | (col1 x == col4 x) && (col2 x == col3 x)].
Proof.
have s05_inv: s05^-1=s05 by inv_tac.
apply/setP => x; rewrite !inE eqperm_map2 /= /act_g s05_inv !ffunE !permE /=.
apply sym_equal; rewrite !eqxx /= andbT/col1/col2/col3/col4/col5/col0.
by do 2![rewrite eq_sym; case : {+}(_ == _)=>  //= ].
Qed.

Lemma F_s14 :
   act_fix1 to_g s14= [set x | (col0 x == col5 x) && (col2 x == col3 x)].
Proof.
have s14_inv: s14^-1=s14  by inv_tac.
apply/setP => x; rewrite !inE eqperm_map2 /= /act_g s14_inv !ffunE !permE /=.
apply sym_equal; rewrite !eqxx /= andbT/col1/col2/col3/col4/col5/col0.
by do 2![rewrite eq_sym; case : {+}(_ == _)=>  //= ].
Qed.

Lemma r05_inv: r05^-1 = r50.
Proof. by inv_tac. Qed.

Lemma r50_inv: r50^-1 = r05.
Proof. by inv_tac. Qed.

Lemma r14_inv: r14^-1 = r41.
Proof. by inv_tac. Qed.

Lemma r41_inv: r41^-1 = r14.
Proof. by inv_tac. Qed.

Lemma s23_inv: s23^-1 = s23.
Proof. by inv_tac. Qed.

Lemma F_s23 :
  act_fix1 to_g s23 = [set x | (col0 x == col5 x) && (col1 x == col4 x)].
Proof.
apply/setP => x; rewrite !inE eqperm_map2 /= /act_g s23_inv !ffunE !permE /=.
apply sym_equal; rewrite !eqxx /= andbT/col1/col2/col3/col4/col5/col0.
by do 2![rewrite eq_sym; case : {+}(_ == _)=>  //=].
Qed.

Lemma F_r05: act_fix1 to_g r05=
  [set x | (col1 x == col2 x) && (col2 x == col3 x)
                                && (col3 x == col4 x)].
Proof.
apply sym_equal.
apply/setP => x; rewrite !inE eqperm_map2 /= /act_g r05_inv !ffunE !permE /=.
rewrite !eqxx /= !andbT /col1/col2/col3/col4/col5/col0.
by do 3! [rewrite eq_sym;case E: {+}(_ == _); rewrite  ?andbF // {E}(eqP E)  ].
Qed.

Lemma F_r50: act_fix1 to_g r50=
  [set x | (col1 x == col2 x) && (col2 x == col3 x)
                                && (col3 x == col4 x)].
Proof.
apply/setP => x; rewrite !inE eqperm_map2 /= /act_g r50_inv !ffunE !permE /=.
apply sym_equal;rewrite !eqxx /= !andbT /col1/col2/col3/col4.
by do 3![rewrite eq_sym;case E: {+}(_ == _); rewrite  ?andbF // {E}(eqP E) ].
Qed.

Lemma F_r23 : act_fix1 to_g r23 =
  [set x | (col0 x == col1 x) && (col1 x == col4 x)
                                && (col4 x == col5 x)].
Proof.
have r23_inv: r23^-1 = r32 by inv_tac.
apply/setP => x; rewrite !inE eqperm_map2 /= /act_g r23_inv !ffunE !permE /=.
apply sym_equal; rewrite !eqxx /= !andbT /col1/col0/col5/col4.
by do 3![rewrite eq_sym; case E: {+}(_ == _); rewrite ?andbF  // {E}(eqP E)].
Qed.

Lemma F_r32 : act_fix1 to_g r32 =
  [set x | (col0 x == col1 x) && (col1 x == col4 x)
                                && (col4 x == col5 x)].
Proof.
have r32_inv: r32^-1 = r23 by inv_tac.
apply/setP => x; rewrite !inE eqperm_map2 /= /act_g r32_inv !ffunE !permE /=.
apply sym_equal; rewrite !eqxx /= !andbT /col1/col0/col5/col4.
by do 3![rewrite eq_sym; case E: {+}(_ == _); rewrite ?andbF  // {E}(eqP E)].
Qed.

Lemma F_r14 : act_fix1 to_g r14 =
  [set x | (col0 x == col2 x) && (col2 x == col3 x) && (col3 x == col5 x)].
Proof.
apply/setP => x; rewrite !inE eqperm_map2 /= /act_g r14_inv !ffunE !permE /=.
apply sym_equal; rewrite !eqxx /= !andbT /col2/col0/col5/col3.
by do 3![rewrite eq_sym; case E: {+}(_ == _); rewrite ?andbF  // {E}(eqP E)].
Qed.

Lemma F_r41 : act_fix1 to_g r41 =
  [set x | (col0 x == col2 x) && (col2 x == col3 x) && (col3 x == col5 x)].
Proof.
apply/setP => x; rewrite !inE eqperm_map2 /= /act_g r41_inv !ffunE !permE /=.
apply sym_equal; rewrite !eqxx /= !andbT /col2/col0/col5/col3.
by do 3![rewrite eq_sym; case E: {+}(_ == _); rewrite ?andbF  // {E}(eqP E)].
Qed.

Lemma F_r024 : act_fix1 to_g r024 =
  [set x | (col0 x == col4 x) && (col4 x == col2  x) && (col1 x == col3 x) 
       && (col3 x == col5 x) ].
Proof.
have r024_inv: r024^-1 = r135 by inv_tac.
apply/setP => x; rewrite !inE eqperm_map2 /= /act_g r024_inv !ffunE !permE /=.
apply sym_equal; rewrite ?eqxx /= !andbT /col0/col1/col2/col3/col4/col5.
by do 4![rewrite eq_sym; case E: {+}(_ == _); rewrite ?andbF  // ?{E}(eqP E)].
Qed.

Lemma F_r135 : act_fix1 to_g r135 =
  [set x | (col0 x == col4 x) && (col4 x == col2  x) && (col1 x == col3 x) 
       && (col3 x == col5 x)].
Proof.
have r135_inv: r135^-1 = r024 by inv_tac.
apply/setP => x; rewrite !inE eqperm_map2 /= /act_g r135_inv !ffunE !permE /=.
apply sym_equal; rewrite ?eqxx /= !andbT /col0/col1/col2/col3/col4/col5.
by do 4![rewrite eq_sym; case E: {+}(_ == _); rewrite ?andbF  // ?{E}(eqP E)].
Qed.

Lemma F_r012 : act_fix1 to_g r012 =
  [set x | (col0 x == col2 x) && (col2 x == col1  x) && (col3 x == col4 x) 
       && (col4 x == col5 x)].
Proof.
have r012_inv: r012^-1 = r345 by inv_tac.
apply/setP => x; rewrite !inE eqperm_map2 /= /act_g r012_inv !ffunE !permE /=.
apply sym_equal; rewrite ?eqxx /= !andbT /col0/col1/col2/col3/col4/col5.
by do 4![rewrite eq_sym; case E: {+}(_ == _); rewrite ?andbF  // ?{E}(eqP E)].
Qed.

Lemma F_r345 : act_fix1 to_g r345 =
  [set x | (col0 x == col2 x) && (col2 x == col1  x) && (col3 x == col4 x) 
       && (col4 x == col5 x)].
Proof.
have r345_inv: r345^-1 = r012 by inv_tac.
apply/setP => x; rewrite !inE eqperm_map2 /= /act_g r345_inv !ffunE !permE /=.
apply sym_equal; rewrite ?eqxx /= !andbT /col0/col1/col2/col3/col4/col5.
do 4![rewrite eq_sym; case E: {+}(_ == _); rewrite ?andbF  // ?{E}(eqP E)].
Qed.

Lemma F_r031 : act_fix1 to_g r031 =
  [set x | (col0 x == col3 x) && (col3 x == col1  x) && (col2 x == col4 x) 
       && (col4 x == col5 x)].
Proof.
have r031_inv: r031^-1 = r425 by inv_tac.
apply/setP => x; rewrite !inE eqperm_map2 /= /act_g r031_inv !ffunE !permE /=.
apply sym_equal; rewrite ?eqxx /= !andbT /col0/col1/col2/col3/col4/col5.
by do 4![rewrite eq_sym; case E: {+}(_ == _); rewrite ?andbF  // ?{E}(eqP E)].
Qed.

Lemma F_r425 : act_fix1 to_g r425 =
  [set x | (col0 x == col3 x) && (col3 x == col1  x) && (col2 x == col4 x) 
       && (col4 x == col5 x)].
Proof.
have r425_inv: r425^-1 = r031 by inv_tac.
apply/setP => x; rewrite !inE eqperm_map2 /= /act_g r425_inv !ffunE !permE /=.
apply sym_equal; rewrite ?eqxx /= !andbT /col0/col1/col2/col3/col4/col5.
by do 4![rewrite eq_sym; case E: {+}(_ == _); rewrite ?andbF  // ?{E}(eqP E)].
Qed.

Lemma F_r043 : act_fix1 to_g r043 =
  [set x | (col0 x == col4 x) && (col4 x == col3  x) && (col1 x == col2 x) 
       && (col2 x == col5 x)].
Proof.
have r043_inv: r043^-1 = r215 by inv_tac.
apply/setP => x; rewrite !inE eqperm_map2 /= /act_g r043_inv !ffunE !permE /=.
apply sym_equal; rewrite ?eqxx /= !andbT /col0/col1/col2/col3/col4/col5.
by do 4![rewrite eq_sym; case E: {+}(_ == _); rewrite ?andbF  // ?{E}(eqP E)].
Qed.

Lemma F_r215 : act_fix1 to_g r215 =
  [set x | (col0 x == col4 x) && (col4 x == col3  x) && (col1 x == col2 x) 
       && (col2 x == col5 x)].
Proof.
have r215_inv: r215^-1 = r043 by inv_tac.
apply/setP => x; rewrite !inE eqperm_map2 /= /act_g r215_inv !ffunE !permE /=.
apply sym_equal; rewrite ?eqxx /= !andbT /col0/col1/col2/col3/col4/col5.
by do 4![rewrite eq_sym; case E: {+}(_ == _); rewrite ?andbF  // ?{E}(eqP E)].
Qed.

Lemma F_s1 : act_fix1 to_g s1 =
  [set x | (col0 x == col5 x) && (col1 x == col2  x) && (col3 x == col4 x)].
Proof.
have s1_inv: s1^-1 = s1 by inv_tac.
apply/setP => x; rewrite !inE eqperm_map2 /= /act_g s1_inv !ffunE !permE /=.
apply sym_equal; rewrite ?eqxx /= !andbT /col0/col1/col2/col3/col4/col5.
by do 3![rewrite eq_sym; case E: {+}(_ == _); rewrite ?andbF  // ?{E}(eqP E)].
Qed.

Lemma F_s2: act_fix1 to_g s2 =
  [set x | (col0 x == col5 x) && (col1 x == col3  x) && (col2 x == col4 x)].
Proof.
have s2_inv: s2^-1 = s2 by inv_tac.
apply/setP => x; rewrite !inE eqperm_map2 /= /act_g s2_inv !ffunE !permE /=.
apply sym_equal; rewrite ?eqxx /= !andbT /col0/col1/col2/col3/col4/col5.
by do 3![rewrite eq_sym; case E: {+}(_ == _); rewrite ?andbF  // ?{E}(eqP E)].
Qed.

Lemma F_s3: act_fix1 to_g s3 =
  [set x | (col0 x == col1 x) && (col2 x == col3  x) && (col4 x == col5 x)].
Proof.
have s3_inv: s3^-1 = s3 by inv_tac.
apply/setP => x; rewrite !inE eqperm_map2 /= /act_g s3_inv !ffunE !permE /=.
apply sym_equal; rewrite ?eqxx /= !andbT /col0/col1/col2/col3/col4/col5.
by do 3![rewrite eq_sym; case E: {+}(_ == _); rewrite ?andbF  // ?{E}(eqP E)].
Qed.

Lemma F_s4: act_fix1 to_g s4 =
  [set x | (col0 x == col4 x) && (col1 x == col5  x) && (col2 x == col3 x)].
Proof.
have s4_inv: s4^-1 = s4 by inv_tac.
apply/setP => x; rewrite !inE eqperm_map2 /= /act_g s4_inv !ffunE !permE /=.
apply sym_equal; rewrite ?eqxx /= !andbT /col0/col1/col2/col3/col4/col5.
by do 3![rewrite eq_sym; case E: {+}(_ == _); rewrite ?andbF  // ?{E}(eqP E)].
Qed.

Lemma F_s5: act_fix1 to_g s5 =
  [set x | (col0 x == col2 x) && (col1 x == col4  x) && (col3 x == col5 x)].
Proof.
have s5_inv: s5^-1 = s5 by inv_tac.
apply/setP => x; rewrite !inE eqperm_map2 /= /act_g s5_inv !ffunE !permE /=.
apply sym_equal; rewrite ?eqxx /= !andbT /col0/col1/col2/col3/col4/col5.
by do 3![rewrite eq_sym; case E: {+}(_ == _); rewrite ?andbF  // ?{E}(eqP E)].
Qed.

Lemma F_s6: act_fix1 to_g s6 =
  [set x | (col0 x == col3 x) && (col1 x == col4  x) && (col2 x == col5 x)].
Proof.
have s6_inv: s6^-1 = s6 by inv_tac.
apply/setP => x; rewrite !inE eqperm_map2 /= /act_g s6_inv !ffunE !permE /=.
apply sym_equal; rewrite ?eqxx /= !andbT /col0/col1/col2/col3/col4/col5.
by do 3![rewrite eq_sym; case E: {+}(_ == _); rewrite ?andbF  // ?{E}(eqP E)].
Qed.

Lemma uniq4_uniq6: forall x y z t: cube, uniq [:: x; y; z;t] -> 
                               exists u , exists v,  uniq [:: x; y; z;t; u ; v].
Proof.
move => x y z t Uxt; move:( cardC  (mem [:: x; y; z; t])).
rewrite card_ord  (card_uniq_tuple Uxt) => hcard.
have hcard2: #|predC (mem [:: x; y; z; t])| = 2.
  by apply:( @addn_injl 4); rewrite /injective  hcard.
have:  #|predC (mem [:: x; y; z; t])| != 0 by rewrite hcard2.
case/existsP=> u Hu; exists u.
move:( cardC  (mem [:: x; y; z; t;u]));rewrite card_ord => hcard5.
have:  #|predC (mem [:: x; y; z; t;u])| !=0.
  rewrite -lt0n  -(ltn_add2l #|mem [:: x; y; z; t; u]|) hcard5 addn0.
 by apply: (leq_ltn_trans (card_size [:: x; y; z; t; u])).
case/existsP => v Hv; exists v.
rewrite (uniq_cat [::x; y;z;t]) Uxt andTb.
apply/andP;split.
  apply/hasPn => x0; rewrite !inE orbF.
  case/orP; move/eqP => ->; first by move:Hu.
  by move:Hv; rewrite /= !inE !orbF  !orbA;case/norP.
rewrite /= andbT !inE orbF /= eq_sym;case/norP:Hv =>//= _.
by rewrite orbF;do 3![case/norP => //= ; move/negbET => _].
Qed.

Lemma card_n4 : forall x y z t : cube, uniq [:: x; y; z; t] ->
   #|[set p : col_cubes | (p x == p y) && (p z == p t)]| = (n ^ 4)%N.
Proof.
move=> x y z t  Uxt. rewrite -[n]card_ord .
case:(uniq4_uniq6 Uxt) => u; case => v Uxv.
pose ff (p : col_cubes) := (p x, p z, p u , p v).
rewrite -(@card_dimage _ _ ff); first last.
  move=> p1 p2; rewrite !inE.
  case/andP=> p1y p1t; case/andP=> p2y p2t  [px pz] pu pv.
  have eqp12: all (fun i => p1 i == p2 i) [:: x; y; z; t; u ; v].
   by rewrite /= -(eqP p1y) -(eqP p1t) -(eqP p2y) -(eqP p2t) px pz pu pv !eqxx.
  apply/ffunP=> i; apply/eqP; apply: (allP eqp12). 
  by rewrite (subset_cardP _ (subset_predT _)) // (card_uniqP Uxv) card_ord.
have ->:forall n, (n ^ 4)%N= (n*n*n*n)%N.
  by move => n0;rewrite (expn_add n0 2 2) -mulnn mulnA.
rewrite -!card_prod; apply: eq_card => [] [[[c d]e ]g] /=; apply/imageP.
rewrite (uniq_cat [::x; y;z;t]) in Uxv; case/and3P: Uxv => _ hasxt.
rewrite /= !inE orbF andbT.
move/negbET=> nuv .
rewrite (uniq_cat [::x; y]) in Uxt; case/and3P: Uxt => _.
rewrite /=. rewrite  !orbF !andbT; case/norP; rewrite !inE !orbF=> nxyz nxyt _.
move:hasxt;rewrite /= !orbF; case/norP; rewrite !inE orbA  !orbF.
case/norP  => nxyu nztu.
rewrite orbA;case/norP=> nxyv nztv.
exists [ffun i => if pred2 x y i then c else if pred2 z t i then d  
                    else if u==i then e else g].
  rewrite !inE /= !ffunE //= !eqxx orbT //= !eqxx /= orbT.
  by rewrite (negbET nxyz) (negbET nxyt).
rewrite {}/ff !ffunE /= !eqxx /=.
rewrite (negbET nxyz) (negbET nxyu) (negbET nztu) (negbET nxyv) (negbET nztv).
by rewrite  nuv.
Qed.

Lemma card_n3_3 : forall x y z t: cube, uniq [:: x; y; z;t] ->
  #|[set p : col_cubes | (p x == p y) && (p y == p z)&& (p z == p t)]|  
      = (n ^ 3)%N.
Proof.
move=> x y z t Uxt; rewrite -[n]card_ord .
case:(uniq4_uniq6 Uxt) => u; case => v Uxv.
pose ff (p : col_cubes) := (p x, p u , p v); 
   rewrite -(@card_dimage _ _ ff); first last.
  move=> p1 p2; rewrite !inE.
  case/andP ;case/andP => p1xy p1yz p1zt.
  case/andP ;case/andP => p2xy p2yz p2zt [px pu] pv.
  have eqp12: all (fun i => p1 i == p2 i) [:: x; y; z; t; u ; v].
    by rewrite /= -(eqP p1zt) -(eqP p2zt) -(eqP p1yz) -(eqP p2yz) -(eqP p1xy)
     -(eqP p2xy) px pu pv !eqxx.
  apply/ffunP=> i; apply/eqP; apply: (allP eqp12). 
  by rewrite (subset_cardP _ (subset_predT _)) // (card_uniqP Uxv) card_ord.
have ->:forall n, (n ^ 3)%N= (n*n*n)%N.
  by move => n0 ; rewrite (expn_add n0 2 1) -mulnn expn1.
rewrite -!card_prod; apply: eq_card => [] [[c d]e ] /=; apply/imageP.
rewrite (uniq_cat [::x; y;z;t]) in Uxv; case/and3P: Uxv => _ hasxt.
rewrite /uniq  !inE orbF !andbT; move/negbET=> nuv.
exists 
   [ffun i => if (i \in [:: x; y; z; t]) then c else if u == i then d else e].
  by rewrite /= !inE   !ffunE !inE  !orbF !eqxx !orbT !eqxx.
rewrite {}/ff !ffunE !inE /= !eqxx /= !orbF.
move: hasxt; rewrite nuv.
by do 8![case E: ( _ ==  _ ); rewrite ?(eqP E)/= ?inE ?orbF  ?eqxx //= ?E {E}].
Qed.

Lemma card_n2_3 : forall x y z t u v: cube, uniq [:: x; y; z;t; u ; v] ->
  #|[set p : col_cubes | (p x == p y) && (p y == p z)&& (p t == p u )
                            && (p u== p v)]|  = (n ^ 2)%N.
Proof.
move=> x y z t u v  Uxv; rewrite -[n]card_ord .
pose ff (p : col_cubes) := (p x, p t); rewrite -(@card_dimage _ _ ff); first last.
  move=> p1 p2; rewrite !inE.
  case/andP ;case/andP ; case/andP => p1xy p1yz p1tu p1uv.
  case/andP ;case/andP; case/andP => p2xy p2yz p2tu p2uv [px pu].  
  have eqp12: all (fun i => p1 i == p2 i) [:: x; y; z; t; u ; v].
    by rewrite /= -(eqP p1yz) -(eqP p2yz) -(eqP p1xy) -(eqP p2xy) -(eqP p1uv) 
      -(eqP p2uv) -(eqP p1tu) -(eqP p2tu) px  pu !eqxx.
  apply/ffunP=> i; apply/eqP; apply: (allP eqp12). 
  by rewrite (subset_cardP _ (subset_predT _)) // (card_uniqP Uxv) card_ord.
have ->:forall n, (n ^ 2)%N= (n*n)%N by move => n0 ; rewrite  -mulnn .
   rewrite -!card_prod; apply: eq_card => [] [c d]/=; apply/imageP.
rewrite (uniq_cat [::x; y;z]) in Uxv; case/and3P: Uxv => Uxt hasxt nuv .
move:hasxt;rewrite /= !orbF. case/norP; rewrite !inE !orbF => nxyzt.
case/norP => nxyzu nxyzv.
exists [ffun i =>  if (i \in [:: x; y; z] ) then c else  d].
  rewrite !inE /= !ffunE !inE //= !orbF !eqxx !orbT !eqxx //=.
  by rewrite (negbET nxyzt) (negbET nxyzu)(negbET nxyzv) !eqxx.
rewrite {}/ff !ffunE  !inE /= !eqxx /=.
by rewrite !orbF; rewrite (negbET nxyzt) .
Qed.

Lemma card_n3s : forall x y z t u v: cube, uniq [:: x; y; z;t; u ; v] ->
  #|[set p : col_cubes | (p x == p y) && (p z == p t)&& (p u == p v )]|  
    = (n ^ 3)%N.
Proof.
move=> x y z t u v  Uxv; rewrite -[n]card_ord .
pose ff (p : col_cubes) := (p x, p z, p u).
rewrite -(@card_dimage _ _ ff); first last.
  move=> p1 p2; rewrite !inE.
  case/andP ;case/andP =>  p1xy p1zt p1uv.
  case/andP ;case/andP => p2xy p2zt p2uv  [px pz] pu.
  have eqp12: all (fun i => p1 i == p2 i) [:: x; y; z; t; u ; v].
    by rewrite /= -(eqP p1xy) -(eqP p2xy) -(eqP p1zt) -(eqP p2zt) -(eqP p1uv)
      -(eqP p2uv)  px  pz pu !eqxx.
  apply/ffunP=> i; apply/eqP; apply: (allP eqp12). 
  by rewrite (subset_cardP _ (subset_predT _)) // (card_uniqP Uxv) card_ord.
have ->:forall n, (n ^ 3)%N= (n*n*n)%N.
  by move => n0 ; rewrite (expn_add n0 2 1) -mulnn expn1.
rewrite -!card_prod. apply: eq_card => [] [[c d]e ] /=; apply/imageP.
rewrite (uniq_cat [::x; y;z;t]) in Uxv; case/and3P: Uxv => Uxt hasxt nuv .
rewrite (uniq_cat [::x; y]) in Uxt; case/and3P: Uxt => _.
rewrite /= !orbF !andbT; case/norP ; rewrite !inE !orbF => nxyz nxyt _.
move:hasxt;rewrite /= !orbF; case/norP; rewrite !inE orbA !orbF.
case/norP => nxyu nztu.
rewrite orbA;case/norP=> nxyv nztv.
exists [ffun i =>  if (i \in [:: x; y] ) then c else  if (i \in [:: z; t] )
                         then d else e].
  rewrite !inE /= !ffunE !inE // !orbF !eqxx !orbT !eqxx //=.
  by rewrite (negbET nxyz) (negbET nxyt)(negbET nxyu) (negbET nztu)
           (negbET nxyv) (negbET nztv) !eqxx.
rewrite {}/ff !ffunE !inE  /= !eqxx /=.
by rewrite !orbF; rewrite (negbET nxyz) (negbET nxyu) (negbET nztu).
Qed.

Lemma burnside_app_iso3 :
  (cube_coloring_number24 * 24 = 
                   n ^ 6 + 6 * n ^ 3 + 3 * n ^ 4 + 8 * (n ^ 2)  + 6 * n ^ 3)%N.
Proof.
pose iso_list :=[::id3;  s05;  s14;  s23;  r05;  r14;  r23;  r50;  r41;  r32;
  r024;  r135;  r012;  r345;  r031;  r425;  r043 ;  r215;
  s1 ;  s2;  s3;  s4;  s5;  s6].
have Uiso: uniq iso_list.
  apply: maps_uniq (fun p : {perm cube} => (p F0, p F1)) _ _.
  have bsr:(fun p : {perm cube} => (p F0, p F1)) =1  
    (fun p  => (sub F0 p F0, sub F0 p F1)) \o sop.
    by move => x; rewrite /= -2!sop_spec.
  by rewrite (eq_maps bsr) maps_comp  -(eqP Lcorrect); vm_compute.
have Eiso: diso_group3 =i iso_list.
by move=> p; rewrite  !inE /= orbF !(eq_sym _ p).
have <-: #|diso_group3| = 24 by rewrite (eq_card Eiso) (card_uniqP Uiso).
rewrite -(Frobenius_Cauchy to_g) (eq_bigl _ _ Eiso) -big_uniq //.
rewrite /reducebig unlock /= card_Fid3 F_s05 F_s14 F_s23 F_r05 F_r14 F_r23
  F_r50 F_r41 F_r32 F_r024 F_r135 F_r012 F_r345 F_r031 F_r425 F_r043  F_r215 
  F_s1  F_s2 F_s3 F_s4 F_s5 F_s6.
by rewrite !card_n4 // !card_n3_3 // !card_n2_3 // !card_n3s //; ring.
Qed.

End cube_colouring.

End colouring.

Corollary burnside_app_iso_3_3col: cube_coloring_number24 3 = 57.
Proof.
by apply/eqP; rewrite -(@eqn_pmul2r 24) // burnside_app_iso3.
Qed.


Corollary burnside_app_iso_2_4col: square_coloring_number8 4 = 55.
Proof. by apply/eqP; rewrite -(@eqn_pmul2r 8) // burnside_app_iso. Qed.

