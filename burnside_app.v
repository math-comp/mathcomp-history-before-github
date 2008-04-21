Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq fintype div ssralg.
Require Import connect.
Require Import groups.
Require Import action.
Require Import frobenius_cauchy.
Require Import group_perm.
Require Import signperm.
Require Import tuple.
Require Import finfun.
Require Import bigops.
Require Import finset.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits. 

Section square_colouring.

Variable n : nat.
Definition colors := I_(n).
Canonical Structure colors_eqType := Eval hnf in [eqType of colors].
Canonical Structure colors_finType := Eval hnf in [finType of colors_eqType].

Definition square := I_(4).
Canonical Structure square_eqType := Eval hnf in [eqType of square].
Canonical Structure square_finType := Eval hnf in [finType of square_eqType].
(*
Definition perm_square := {perm square}.
Canonical Structure perm_square_eqType := Eval hnf in [eqType of perm_square].
Canonical Structure perm_square_finType :=
  Eval hnf in [finType of perm_square_eqType].
Canonical Structure perm_square_groupType :=
  Eval hnf in [finGroupType of perm_square_finType].
*)

Definition mksquare i : square := (Sub _ : _ -> I_(4)) (ltn_mod i _).
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
Proof. inj_tac; repeat (destruct val => //=; first by apply /eqP). Qed.

Lemma R2_inj :  injective R2.
Proof. inj_tac; repeat (destruct val => //=; first by apply /eqP). Qed.

Lemma R3_inj: injective R3.
Proof. inj_tac; repeat (destruct val => //=; first by apply /eqP). Qed.

Definition r1 := (perm_of R1_inj).
Definition r2 := (perm_of R2_inj).
Definition r3 := (perm_of R3_inj).
Definition id1:= (1 : {perm square}).

Definition is_rot r :=  (r * r1 == r1 * r).
Definition rot := [set r | is_rot r].

Lemma group_set_rot: group_set rot.
Proof.
apply /groupP;split; first  by rewrite /rot  setE /is_rot mulg1 mul1g.
move => x1 y; rewrite /rot !setE /= /is_rot ;move/eqP => hx1 ; move/eqP => hy.
by rewrite -mulgA hy !mulgA hx1.
Qed.

Canonical Structure rot_group:= Group group_set_rot.

Definition rotations := [set id1; r1; r2; r3].

Lemma rot_eq_c0: forall r s : {perm square},
  is_rot r -> is_rot s -> r c0 = s c0 -> r = s.
Proof.
move=> r s hr hs hrs; apply/permP => a.
have ->: a = (r1 ** a) c0 
   by apply/eqP; case: a; do 4?case => //=; rewrite ?permM !permE.
by rewrite -!permM -!(eqP (commute_expn _ _))  // !permM hrs.
Qed.

Lemma rot_r1: forall r, is_rot r -> r = r1 ** (r c0).
Proof.
move=> r hr;apply: rot_eq_c0 => //;apply/eqP.
  by rewrite -!(eqP (commute_expn _ _)) // /commute.
by case  :(r c0); do 4?case => //=; rewrite ?permM !permE  /=.
Qed.

Lemma rotations_is_rot: forall r, r \in rotations -> is_rot r.
Proof.
move=> r Dr; apply/eqP; apply/permP => a; rewrite setE !permM in Dr *.
by case/or4P: Dr; move/eqP->; rewrite !permE //; case: a; do 4?case.
Qed.

Lemma rot_is_rot: rot = rotations.
Proof.
apply/setP=> r; apply/idP/idP; last by move/rotations_is_rot; rewrite setE.
rewrite !setE => h.
have -> : r = r1 ** r c0 by apply: rot_eq_c0; rewrite // -rot_r1.
have e2: 2 = r2 c0 by rewrite permE /=.
have e3: 3 = r3 c0 by rewrite permE /=.
case (r c0); do 4?[case] => // ?; rewrite ?(gexpn1, eqxx, orbT) //.
  by rewrite [nat_of_ord _]/= e2 -rot_r1 ?(eqxx, orbT, rotations_is_rot, setE).
by rewrite [nat_of_ord _]/= e3 -rot_r1 ?(eqxx, orbT, rotations_is_rot, setE).
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
by apply:(mulg_injr sh);rewrite mulVg ;apply/permP;
case; do 4?case  => //=; move=> H;rewrite !permE /= !permE; apply /eqP.
Qed.

Definition Sv (sc : square) : square := tsub [tuple c3; c2; c1; c0] sc.

Lemma Sv_inj: injective Sv.
Proof.
by apply : (can_inj (g:= Sv));case; do 4?case  => //=;move => H;apply /eqP.
Qed.

Definition sv := (perm_of Sv_inj).

Lemma sv_inv: sv^-1 = sv.
Proof.
by apply:(mulg_injr sv);rewrite mulVg ;apply/permP;
case; do 4?case  => //=; move=> H; rewrite !permE /= !permE; apply /eqP.
Qed.

Definition S1 (sc : square) : square := tsub [tuple c0; c3; c2; c1] sc.

Lemma S1_inj : injective S1.
Proof.
by apply: can_inj S1 _; case; do 4?case=> //=; move=> H; apply /eqP.
Qed.

Definition s1 := (perm_of S1_inj).

Lemma s1_inv : s1^-1 = s1.
Proof.
by apply: (mulg_injr s1); rewrite mulVg; apply/permP;
 case; do 4?case=> //=; move=> H; rewrite !permE /= !permE; apply /eqP.
Qed.

Definition S2 (sc : square) : square := tsub [tuple c2; c1; c0; c3] sc.

Lemma S2_inj : injective S2.
Proof.
by apply: can_inj S2 _; case; do 4?case=> //=; move=> H; apply /eqP.
Qed.

Definition s2 := (perm_of S2_inj).

Lemma s2_inv : s2^-1 = s2.
Proof.
by apply: (mulg_injr s2); rewrite mulVg; apply/permP;
  case; do 4?case=> //=; move=> H; rewrite !permE /= !permE; apply/eqP.
Qed.

Lemma ord_enum4: sval (ord_enum 4) = [:: c0; c1; c2; c3].
Proof. apply: (inj_maps (@val_inj _ _ _)); exact: (svalP (ord_enum 4)). Qed.

Lemma diff_id_sh: 1 != sh.
Proof.
by apply/eqP; move/(congr1 (fun p : {perm square} => p c0)); rewrite !permE.
Qed.

Definition isometries2 := [set 1; sh].

Lemma card_iso2: #|isometries2| = 2.
Proof. by rewrite cards2 diff_id_sh. Qed.

Lemma group_set_iso2 : group_set isometries2.
Proof.
apply/groupP; split => [|x y]; rewrite !setE ?eqxx //.
do 2![case/orP; move/eqP->]; gsimpl; rewrite ?(eqxx, orbT) //.
by rewrite -/sh -{1}sh_inv mulVg eqxx.
Qed.
Canonical Structure iso2_group:= Group group_set_iso2.

Definition isometries :=
  [set p | [|| p == 1, p == r1, p == r2, p == r3,
            p == sh, p == sv, p == s1 | p == s2 ]].

Definition opp (sc : square) := tsub [tuple c2; c3; c0; c1] sc.

Definition is_iso (p : {perm square}) := forall ci, p (opp ci) = opp (p ci).

Lemma isometries_iso : forall p, p \in isometries -> is_iso p.
Proof.
move=> p; rewrite setE.
by do ?case/orP; move/eqP=> -> a; rewrite !permE; case: a; do 4?case.
Qed.

Ltac non_inj p a1 a2 heq1 heq2 := 
let h1:= fresh "h1" in 
(absurd (p a1 = p a2);first (by red; move=> h1;move:(perm_inj h1));
by rewrite heq1 heq2;apply/eqP).

Ltac is_isoPtac p f e0 e1 e2 e3 := 
  suff ->: p = f by [rewrite setE eqxx ?orbT];
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
by is_isoPtac p s1 e0 e1 e2 e3.
by is_isoPtac p sh e0 e1 e2 e3.
by is_isoPtac p r1 e0 e1 e2 e3.
by is_isoPtac p s2 e0 e1 e2 e3.
by is_isoPtac p r2 e0 e1 e2 e3.
by is_isoPtac p r3 e0 e1 e2 e3.
by is_isoPtac p sv e0 e1 e2 e3.
Qed.


Lemma group_set_iso: group_set isometries.
Proof.
apply/groupP; split; first by rewrite setE eqxx /=.
by move=> x y hx hy; apply/is_isoP => ci; rewrite !permM !isometries_iso.
Qed.

Canonical Structure iso_group := Group group_set_iso.

Lemma card_rot: #|rot| = 4.
Proof.
rewrite -[4]/(size [:: id1; r1; r2; r3]) -(card_uniqP _).
  by apply: eq_card => x; rewrite rot_is_rot setE !inE orbF.
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
Proof. by move=> k x y; apply/ffunP=> a; rewrite !ffunE invg_mul permE. Qed.

Definition to := Action act_f_1 act_f_morph.

Definition square_coloring_number2 := act_nbcomp to iso2_group.
Definition square_coloring_number4 := act_nbcomp to rot_group.
Definition square_coloring_number8 := act_nbcomp to iso_group.

(* Infix "^":= expn : dnat_scope. *)

Lemma Fid : act_fix1 to 1 = setA.
Proof. by apply/setP=> x /=; rewrite !setE act1 eqxx. Qed.

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
apply/eqP; apply Ep12; case: x; do 4!case=> //.
Qed.

Lemma F_Sh :
  act_fix1 to sh = [set x | (coin0 x == coin1 x) && (coin2 x == coin3 x)].
Proof.
apply/setP=> x; rewrite !setE eqperm_map /= /act_f sh_inv !ffunE !permE /=.
by rewrite eq_sym (eq_sym (x c3)) andbT andbA !andbb.
Qed.

Lemma F_Sv :
   act_fix1 to sv = [set x | (coin0 x == coin3 x) && (coin2 x == coin1 x)].
Proof.
apply/setP => x; rewrite !setE eqperm_map /= /act_f sv_inv !ffunE !permE /=.
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
apply/setP => x; rewrite !setE eqperm_map /= /act_f r2_inv !ffunE !permE /=.
by rewrite eq_sym andbT andbCA andbC (eq_sym (x c3)) andbA -andbA !andbb andbC.
Qed.

Lemma F_r1 : act_fix1 to r1 =
  [set x | (coin0 x == coin1 x) && (coin1 x == coin2 x)
                                && (coin2 x == coin3 x)].
Proof.
apply/setP => x; rewrite !setE eqperm_map /= /act_f r1_inv !ffunE !permE /= andbC.
by do 3![case E: {+}(_ == _); rewrite // {E}(eqP E)]; rewrite eqxx.
Qed.

Lemma F_r3 : act_fix1 to r3 =
  [set x | (coin0 x == coin1 x) && (coin1 x == coin2 x)
                                && (coin2 x == coin3 x)].
Proof.
apply/setP => x; rewrite !setE eqperm_map /= /act_f r3_inv !ffunE !permE /=.
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
    by rewrite !setE /= !ffunE !eqxx orbT (negbET nxzt) (negbET nyzt) !eqxx.
  by rewrite {}/f !ffunE /= eqxx (negbET nxzt).
move=> p1 p2; rewrite !setE.
case/andP=> p1y p1t; case/andP=> p2y p2t [px pz].
have eqp12: all (fun i => p1 i == p2 i) [:: x; y; z; t].
  by rewrite /= -(eqP p1y) -(eqP p1t) -(eqP p2y) -(eqP p2t) px pz !eqxx.
apply/ffunP=> i; apply/eqP; apply: (allP eqp12). 
by rewrite (subset_cardP _ (subset_setA _)) // (card_uniqP Uxt) card_ord.
Qed.

Lemma card_n :
 #|[set x | (coin0 x == coin1 x) && (coin1 x == coin2 x)
                                && (coin2 x == coin3 x)]|
   = n.
Proof.
rewrite -[n]card_ord /coin0 /coin1 /coin2 /coin3.
pose f (p : col_squares) := p c3; rewrite -(@card_dimage _ _ f).
  apply: eq_card => c /=; apply/imageP.
  exists ([ffun => c] : col_squares); last by rewrite /f ffunE.
  by rewrite /= setE !ffunE !eqxx.
move=> p1 p2; rewrite /= !setE /f -!andbA => eqp1 eqp2 eqp12.
apply/eqP; rewrite eqperm_map /= andbT.
case/and3P: eqp1; do 3!move/eqP->; case/and3P: eqp2; do 3!move/eqP->.
by rewrite !andbb eqp12.
Qed.

Lemma burnside_app2: (square_coloring_number2 * 2 = n ^ 4 + n ^ 2)%N.
Proof.
rewrite -{1}card_iso2 -(Frobenius_Cauchy to iso2_group) /=.
rewrite (eq_bigl (mem [:: id1; sh])) => [|p] /=; last first.
  by rewrite setE !inE orbF.
rewrite -big_uniq /=; last by rewrite !inE orbF diff_id_sh.
by unlock reducebig => /=; rewrite addn0 card_Fid F_Sh card_n2 //= !muln1.
Qed.

Lemma burnside_app_rot:
  (square_coloring_number4 * 4 = n ^ 4 + n ^ 2 + 2 * n)%N.
Proof.
rewrite -{1}card_rot -(Frobenius_Cauchy to rot_group).
rewrite (eq_bigl (mem [:: id1; r1; r2; r3])) => [|p] /=; last first.
  by rewrite rot_is_rot setE !inE orbF.
rewrite -big_uniq; last first.
  by apply: maps_uniq (fun p : {perm square} => p c0) _ _; rewrite /= !permE.
unlock reducebig; rewrite /= !addn0 card_Fid F_r1 F_r2 F_r3 card_n card_n2 //=.
ring.
Qed.

Lemma F_S1 : act_fix1 to s1 = [set x | coin1 x == coin3 x].
Proof.
apply/setP => x; rewrite !setE eqperm_map /= /act_f s1_inv !ffunE !permE /=.
by rewrite !eqxx !andbT eq_sym /= andbb.
Qed.

Lemma card_n3 : forall x y : square, x != y ->
  #|[set k : col_squares | k x == k y]| = (n ^ 3)%N.
Proof.
move=> x y nxy; apply/eqP; case: (ltngtP n 0) => // [|n0]; last first.
  by rewrite n0; apply/existsP=> [] [p _]; case: (p c0) => i; rewrite n0.
move/eqn_pmul2l <-; rewrite -expnS -card_Fid Fid cardsE.
rewrite -{1}[n]card_ord -cardX.
pose pk k := [ffun i => k (if i == y then x else i) : colors].
rewrite -(@card_image _ _ (fun k : col_squares => (k y, pk k))).
  apply/eqP; apply: eq_card => ck /=; apply/eqP/imageP; last first.
    by case=> k _ -> {cK}/=; rewrite !ffunE if_same eqxx.
  case: ck => c k /= kxy.
  exists [ffun i => if i == y then c else k i]; first by rewrite setE.
  rewrite !ffunE eqxx; congr (_, _); apply/ffunP=> i; rewrite !ffunE.
  case Eiy: (i == y); last by rewrite Eiy.
  by rewrite (negbET nxy) (eqP Eiy).
move=> k1 k2 [Eky Epk]; apply/ffunP=> i.
have{Epk}: pk k1 i = pk k2 i by rewrite Epk.
by rewrite !ffunE; case: eqP => // ->.
Qed.

Lemma F_S2 : act_fix1 to s2 = [set x | coin0 x == coin2 x].
Proof.
apply/setP => x; rewrite !setE eqperm_map /= /act_f s2_inv !ffunE !permE /=.
by rewrite !eqxx !andbT eq_sym /= andbb.
Qed.

Lemma burnside_app_iso :
  (square_coloring_number8 * 8 = n ^ 4 + 2 * n ^ 3 + 3 * n ^ 2 + 2 * n)%N.
Proof.
pose iso_list := [:: id1; r1; r2; r3; sh; sv; s1; s2].
have Uiso: uniq iso_list.
  apply: maps_uniq (fun p : {perm square} => (p c0, p c1)) _ _.
  by rewrite /= !permE.
have Eiso: iso_group =i iso_list by move=> p; rewrite /= setE !inE orbF.
have <-: #|iso_group| = 8 by rewrite (eq_card Eiso) (card_uniqP Uiso).
rewrite -(Frobenius_Cauchy to) (eq_bigl _ _ Eiso) -big_uniq //.
unlock reducebig; rewrite /= card_Fid F_r1 F_r2 F_r3 F_Sh F_Sv F_S1 F_S2.
rewrite card_n !card_n3 // !card_n2 //=; ring.
Qed.

End square_colouring.

Corollary burnside_app_iso_4col: square_coloring_number8 4 = 55.
Proof. by apply/eqP; rewrite -(@eqn_pmul2r 8) // burnside_app_iso. Qed.

