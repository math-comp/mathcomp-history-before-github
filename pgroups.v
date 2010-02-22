Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq div.
Require Import fintype paths finfun bigops finset prime groups.
Require Import morphisms perm action automorphism normal cyclic.
Require Import gfunc gprod.

(*****************************************************************************)
(* Standard group notions and constructions based on the prime decomposition *)
(* of the order of the group or its elements.                                *)
(*   pi.-group G      <=> G is a pi-group                                    *)
(*                    <-> pi.-nat #|G|                                       *)
(*     + Recall that here and in the sequel pi can be a prime p              *)
(*   pi.-subgroup(H) G   <=> H is a pi-subgroup of G                         *)
(*                    <-> (H \subset G) && pi.-group H                       *)
(*     + This is provided mostly as a shorhand, with few associated lemmas.  *)
(*     + However, we do establish some results on maximal pi-subgroups.      *)
(*   pi.-elt x        <=> x is a pi-element                                  *)
(*                    <-> pi.-nat #[x] (<-> pi.-group <[x]>)                 *)
(*   x.`_pi           == the pi-constituent of x: the only pi-element        *)
(*                       y \in <[x]> s.t. x * y^-1 is a pi'-element          *)
(*   pi.-Hall(G) H    <=> H is a Hall pi-subgroup of G                       *)
(*                    <-> [&& H \subset G, pi.-group H & pi^'.-nat #|G : H|] *)
(*                     -> #|H| = #|G|`_pi                                    *)
(*   p.-Sylow(G) P    <=> P is a Sylow p-subgroup of G                       *)
(*                    <-> p.-Hall(G) P                                       *)
(*     + This is only a display notation; note that due to an ugly display   *)
(*       engine bug, Coq will fail to use the notation under a coercion such *)
(*       as is_true, and will display p.-Hall(G) P instead.                  *)
(*   'Syl_p(G)        == the set of the p-Sylow subgroups of G               *)
(*                    := [set P : {group _} | p.-Sylow(G) P]                 *)
(*   p_group P        <=> P is a p-group for some prime p                    *)
(*                    <-> (pdiv #|P|).-group P                               *)
(*   Hall G H         <=> H is a Hall pi-subgroup of G for some pi           *)
(*                    <-> coprime #|H| #|G : H| && (H \subset G)             *)
(*   Sylow G P        <=> P is a Sylow p-subgroup of G for some p            *)
(*                    <-> p_group P && Hall G P                              *)
(*   'O_pi(G)         == the pi-core of G                                    *)
(*                    := the largest normal pi-subgroup of G                 *)
(*   pcore_mod pi G H == the pi-core of G mod H                              *)
(*                    := G :&: (coset H @*^-1 'O_pi(G / H))                  *)
(*   'O_{pi2, pi1}(G) == the pi1,pi2-core of G                               *)
(*                    := the pi1-core of G mod 'O_pi2(G)                     *)
(*     + We have 'O_{pi2, pi1}(G) / 'O_pi2(G) = 'O_pi1(G / 'O_pi2(G))        *)
(*          with 'O_pi2(G) <| 'O_{pi2, pi1}(G) <| G                          *)
(*   'O_{pn, ..., p1}(G) == the p1, ..., pn-core of G, more generally        *)
(*                    := the p1-core of G mod 'O_{pn, ..., p2}(G)            *)
(* Note that notions are always defined on sets even though their name       *)
(* indicates "group" properties; the actual definition of the notion never   *)
(* tests for the group property, since this property will always be          *)
(* provided by a (canonical) group structure. Similarly, p-group properties  *)
(* assume without test that p is a prime.                                    *)
(*****************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Import GroupScope.

Section PgroupDefs.

(* We defer the definition of the functors ('0_p(G), etc) because they need *)
(* to quantify over the finGroupType explicitly.                            *)

Variable gT : finGroupType.
Implicit Type x : gT.
Implicit Types A B : {set gT}.
Implicit Type pi : nat_pred.
Implicit Types p n : nat.

Definition pgroup pi A := pi.-nat #|A|.

Definition psubgroup pi A B := (B \subset A) && pgroup pi B.

Definition p_group A := pgroup (pdiv #|A|) A.

Definition p_elt pi x := pi.-nat #[x].

Definition constt x pi := x ^+ (chinese #[x]`_pi #[x]`_pi^' 1 0).

Definition Hall A B := (B \subset A) && coprime #|B| #|A : B|.

Definition pHall pi A B := [&& B \subset A, pgroup pi B & pi^'.-nat #|A : B|].

Definition Syl p A := [set P : {group gT} | pHall p A P].

Definition Sylow A B := p_group B && Hall A B.

End PgroupDefs.

Prenex Implicits p_group Hall Sylow.

Notation "pi .-group" := (pgroup pi)
  (at level 2, format "pi .-group") : group_scope.

Notation "pi .-subgroup ( A )" := (psubgroup pi A)
  (at level 8, format "pi .-subgroup ( A )") : group_scope.

Notation "pi .-elt" := (p_elt pi)
  (at level 2, format "pi .-elt") : group_scope.

Notation "x .`_ pi" := (constt x pi)
  (at level 3, format "x .`_ pi") : group_scope.

Notation "pi .-Hall ( G )" := (pHall pi G)
  (at level 8, format "pi .-Hall ( G )") : group_scope.

Notation "p .-Sylow ( G )" := (nat_pred_of_nat p).-Hall(G)
  (at level 8, format "p .-Sylow ( G )") : group_scope.

Notation "''Syl_' p ( G )" := (Syl p G)
  (at level 8, p at level 2, format "''Syl_' p ( G )") : group_scope.

Section PgroupProps.

Variable gT : finGroupType.
Implicit Type pi : nat_pred.
Implicit Type p : nat.
Implicit Types x y z : gT.
Implicit Types A B C D : {set gT}.
Implicit Types G H K P Q : {group gT}.

Lemma trivgVpdiv : forall G, G :=: 1 \/ (exists2 p, prime p & p %| #|G|).
Proof.
move=> G; case: (leqP #|G| 1) => [leG1|lt1G]; [left | right].
  exact: card_le1_trivg.
by exists (pdiv #|G|); rewrite ?pdiv_dvd ?pdiv_prime.
Qed.

Lemma prime_subgroupVti : forall G H, prime #|G| -> G \subset H \/ H :&: G = 1.
Proof.
move=> G H prG; case: (trivgVpdiv (H :&: G)) => [|[p p_pr pG]]; first by right.
left; rewrite (sameP setIidPr eqP) eqEcard subsetIr.
suffices <-: p = #|G| by rewrite dvdn_leq ?cardG_gt0.
by apply/eqP; rewrite -dvdn_prime2 // -(LaGrangeI G H) setIC dvdn_mulr.
Qed.

Lemma pgroupP : forall pi G,
  reflect (forall p, prime p -> p %| #|G| -> p \in pi) (pi.-group G).
Proof. move=> pi G; exact: pnatP. Qed.
Implicit Arguments pgroupP [pi G].

Lemma eq_pgroup : forall pi1 pi2 A, pi1 =i pi2 -> pi1.-group A = pi2.-group A.
Proof. move=> pi1 pi2 A; exact: eq_pnat. Qed.

Lemma pgroup1 : forall pi, pi.-group (1 : {set gT}).
Proof. by move=> pi; rewrite /pgroup cards1. Qed.

Lemma pgroupS : forall pi G H, H \subset G -> pi.-group G -> pi.-group H.
Proof. move=> pi G H sHG; exact: pnat_dvd (cardSg sHG). Qed.

Lemma oddSg : forall G H, H \subset G -> odd #|G| -> odd #|H|.
Proof. move=> G H; rewrite !odd_2'nat; exact: pgroupS. Qed.

Lemma odd_pgroup_odd : forall p G, odd p -> p.-group G -> odd #|G|.
Proof.
move=> p G p_odd pG; rewrite odd_2'nat (pi_pnat pG) // !inE.
by case: eqP p_odd => // ->.
Qed.

Lemma properG_ltn_log : forall p G H,
  p.-group G -> H \proper G -> logn p #|H| < logn p #|G|.
Proof. 
move=> p G H pG; rewrite properEneq eqEcard andbC ltnNge; case/andP=> sHG.
rewrite sHG /= -{1}(part_pnat_id pG) -{1}(part_pnat_id (pgroupS sHG pG)) !p_part {pG}.
by apply: contra; case: p => [|p] leGH; rewrite ?logn0 // leq_pexp2l.
Qed.

Lemma pgroupM : forall pi G H, pi.-group (G * H) = pi.-group G && pi.-group H.
Proof.
move=> pi G H; have GH_gt0: 0 < #|G :&: H| := cardG_gt0 _.
rewrite /pgroup -(mulnK #|_| GH_gt0) -mul_cardG -(LaGrangeI G H) -mulnA.
by rewrite mulKn // -(LaGrangeI H G) setIC !pnat_mul andbCA; case: (pnat _).
Qed.

Lemma pgroupJ : forall pi G x, pi.-group (G :^ x) = pi.-group G.
Proof. by move=> pi G x; rewrite /pgroup cardJg. Qed.

Lemma pgroup_p : forall p P, p.-group P -> p_group P.
Proof.
move=> p P pgP; case: (leqP #|P| 1).
  by move/card_le1_trivg->; exact: pgroup1.
move/pdiv_prime=> pr_q; have:= pgroupP pgP _ pr_q (pdiv_dvd _).
by rewrite /p_group; move/eqnP->.
Qed.

Lemma p_groupP : forall P, p_group P -> exists2 p, prime p & p.-group P.
Proof.
move=> P; case: (ltnP 1 #|P|); first by move/pdiv_prime; exists (pdiv #|P|).
move/card_le1_trivg=> -> _; exists 2 => //; exact: pgroup1.
Qed.

Lemma pgroup_pdiv : forall p G,
    p.-group G -> G :!=: 1 ->
  [/\ prime p, p %| #|G| & exists m, #|G| = p ^ m.+1]%N.
Proof.
move=> p G pG; rewrite trivg_card1; case/p_groupP: (pgroup_p pG) => q q_pr qG.
move/implyP: (pgroupP pG q q_pr); case/p_natP: qG => // [[|m] ->] //.
by rewrite dvdn_exp //; move/eqnP=> <- _; split; rewrite ?dvdn_exp //; exists m.
Qed.

Lemma card_Hall : forall pi G H, pi.-Hall(G) H -> #|H| = #|G|`_pi.
Proof.
move=> pi G H; case/and3P=> sHG piH pi'H.
by rewrite -(LaGrange sHG) partn_mul ?LaGrange // part_pnat_id ?part_p'nat ?muln1.
Qed.

Lemma pHall_sub : forall pi A B, pi.-Hall(A) B -> B \subset A.
Proof. by move=> pi A B; case/andP. Qed.

Lemma pHall_pgroup : forall pi A B, pi.-Hall(A) B -> pi.-group B.
Proof. by move=> pi A B; case/and3P. Qed.

Lemma pHallP : forall pi G H,
  reflect (H \subset G /\ #|H| = #|G|`_pi) (pi.-Hall(G) H).
Proof.
move=> pi G H; apply: (iffP idP) => [piH | [sHG oH]].
  split; [exact: pHall_sub piH | exact: card_Hall].
rewrite /pHall sHG -divgS // /pgroup oH.
by rewrite -{2}(@partnC pi #|G|) ?mulKn ?part_pnat.
Qed.

Lemma pHallE : forall pi G H,
  pi.-Hall(G) H = (H \subset G) && (#|H| == #|G|`_pi).
Proof. by move=> pi G H; apply/pHallP/andP=> [] [->]; move/eqP. Qed.

Lemma pHall_Hall : forall pi A B, pi.-Hall(A) B -> Hall A B.
Proof.
move=> pi A B; case/and3P=> sBA piB pi'B.
by rewrite /Hall sBA (pnat_coprime piB).
Qed.

Lemma Hall_pi : forall G H, Hall G H -> \pi(#|H|).-Hall(G) H.
Proof.
move=> G H; case/andP=> sHG coHG.
by rewrite /pHall sHG /pgroup pnat_pi -?coprime_pi'.
Qed.

Lemma HallP : forall G H, Hall G H -> exists pi, pi.-Hall(G) H.
Proof. move=> G H HallH; exists \pi(#|H|); exact: Hall_pi. Qed.

Lemma pHallJ2 : forall pi G H x,
   pi.-Hall(G :^ x) (H :^ x) = pi.-Hall(G) H.
Proof. by move=> pi G H x; rewrite !pHallE conjSg !cardJg. Qed.

Lemma pHallJ : forall pi G H x,
  x \in G -> pi.-Hall(G) (H :^ x) = pi.-Hall(G) H.
Proof. by move=> pi G H x Gx; rewrite -{1}(conjGid Gx) pHallJ2. Qed.

Lemma HallJ : forall G H x, x \in G -> Hall G (H :^ x) = Hall G H.
Proof.
move=> G H x Gx; rewrite /Hall -!divgI.
by rewrite -{1 3}(conjGid Gx) conjSg -conjIg !cardJg.
Qed.

Lemma psubgroupJ : forall pi G H x,
  x \in G -> pi.-subgroup(G) (H :^ x) = pi.-subgroup(G) H.
Proof.
by move=> pi G H x Gx; rewrite /psubgroup pgroupJ -{1}(conjGid Gx) conjSg.
Qed.

Lemma p_groupJ : forall P x, p_group (P :^ x) = p_group P.
Proof. by move=> P x; rewrite /p_group cardJg pgroupJ. Qed.

Lemma SylowJ : forall G P x, x \in G -> Sylow G (P :^ x) = Sylow G P.
Proof. by move=> G P x Gx; rewrite /Sylow p_groupJ HallJ. Qed.

Lemma p_Sylow : forall p G P, p.-Sylow(G) P -> Sylow G P.
Proof.
move=> p G P pP.
by rewrite /Sylow (pgroup_p (pHall_pgroup pP)) (pHall_Hall pP).
Qed.

Lemma pHall_subl : forall pi G K H,
  H \subset K -> K \subset G -> pi.-Hall(G) H -> pi.-Hall(K) H.
Proof.
move=> pi G K H sHK sKG; rewrite /pHall sHK; case/and3P=> _ ->.
apply: pnat_dvd; exact: indexSg.
Qed.

Lemma Hall1 : forall G, Hall G 1.
Proof. by move=> G; rewrite /Hall sub1G cards1 coprime1n. Qed.

Lemma p_group1 : @p_group gT 1.
Proof. by rewrite (@pgroup_p 2) ?pgroup1. Qed.

Lemma Sylow1 : forall G, Sylow G 1.
Proof. by move=> G; rewrite /Sylow p_group1 Hall1. Qed.

Lemma eq_pHall : forall pi1 pi2 A B,
  pi1 =i pi2 -> pi1.-Hall(A) B = pi2.-Hall(A) B.
Proof.
move=> pi1 pi2 A B eq_pi; congr [&& _, _ & _]; apply: eq_pnat => // q.
congr (~~ _); exact: eq_pi.
Qed.

Lemma SylowP : forall G P,
  reflect (exists2 p, prime p & p.-Sylow(G) P) (Sylow G P).
Proof.
move=> G P; apply: (iffP idP) => [| [p _]]; last exact: p_Sylow.
case/andP; case/p_groupP=> p p_pr; case/p_natP=> // [[P1 _ | n oP]].
  have{p p_pr P1} ->: P :=: 1 by apply: card1_trivg; rewrite P1.
  pose p := pdiv #|G|.+1; have pr_p: prime p by rewrite pdiv_prime ?ltnS.
  exists p; rewrite // pHallE sub1G cards1 part_p'nat //.
  apply/pgroupP=> q pr_q qG; apply/eqnP=> def_q.
  have: p %| #|G| + 1 by rewrite addn1 pdiv_dvd.
  by rewrite dvdn_addr -def_q // euclid1.
move/Hall_pi; rewrite oP pi_of_exp // (eq_pHall _ _ (pi_of_prime _)) //.
by exists p.
Qed.

Lemma p_elt_exp : forall pi x m, pi.-elt (x ^+ m) = (#[x]`_pi^' %| m).
Proof.
move=> pi x m; apply/idP/idP=> [pi_xm|].
  rewrite -(@gauss _ #[x ^+ m]); last first.
    by rewrite coprime_sym (pnat_coprime pi_xm) ?part_pnat.
  apply: (@dvdn_trans #[x]); first by rewrite -{2}[#[x]](partnC pi) ?dvdn_mull.
  by rewrite order_dvdn mulnC expgn_mul expg_order.
case/dvdnP=> q ->{m}; rewrite mulnC; apply: pnat_dvd (part_pnat pi #[x]).
by rewrite order_dvdn -expgn_mul mulnC mulnA partnC // -order_dvdn dvdn_mulr.
Qed.

Lemma mem_p_elt : forall pi x G, pi.-group G -> x \in G -> pi.-elt x.
Proof. by move=>pi x G piG Gx; apply: pgroupS piG; rewrite cycle_subG. Qed.

Lemma p_eltM_norm : forall pi x y, x \in 'N(<[y]>) ->
  pi.-elt x -> pi.-elt y -> pi.-elt (x * y).
Proof.
move=> pi x y nyx pi_x pi_y; apply: (@mem_p_elt pi _ (<[x]> <*> <[y]>)%G).
  rewrite /= norm_mulgenEl ?cycle_subG // pgroupM; exact/andP.
by rewrite groupM // mem_gen // inE cycle_id ?orbT.
Qed.

Lemma p_eltM :  forall pi x y, commute x y ->
  pi.-elt x -> pi.-elt y -> pi.-elt (x * y).
Proof.
move=> pi x y cxy; apply: p_eltM_norm; apply: (subsetP (cent_sub _)).
rewrite cent_gen cent_set1; exact/cent1P.
Qed.

Lemma p_elt1 : forall pi, pi.-elt (1 : gT).
Proof. by move=> pi; rewrite /p_elt order1. Qed.

Lemma p_eltV : forall pi x, pi.-elt x^-1 = pi.-elt x.
Proof. by move=> pi x; rewrite /p_elt orderV. Qed.

Lemma p_eltX : forall pi x n, pi.-elt x -> pi.-elt (x ^+ n).
Proof.
by move=> pi x n; rewrite -{1}[x]expg1 !p_elt_exp dvdn1; move/eqnP->.
Qed.

Lemma p_eltJ : forall pi x y, pi.-elt (x ^ y) = pi.-elt x.
Proof. by move=> pi x y; congr pnat; rewrite orderJ. Qed.

Lemma sub_p_elt : forall pi1 pi2 x,
  {subset pi1 <= pi2} -> pi1.-elt x -> pi2.-elt x.
Proof. move=> pi1 pi2 x pi12; apply: sub_in_pnat => q _; exact: pi12. Qed.

Lemma eq_p_elt : forall pi1 pi2 x, pi1 =i pi2 -> pi1.-elt x = pi2.-elt x.
Proof. move=> pi1 pi2 x pi12; exact: eq_pnat. Qed.

Lemma p_eltNK : forall pi x, pi^'^'.-elt x = pi.-elt x.
Proof. move=> pi x; exact: pnatNK. Qed.

Lemma eq_constt : forall pi1 pi2 x, pi1 =i pi2 -> x.`_pi1 = x.`_pi2.
Proof.
move=> pi1 pi2 x pi12; congr (x ^+ (chinese _ _ 1 0)); apply: eq_partn => //.
move=> q; congr (~~ _); exact: pi12.
Qed.

Lemma consttNK : forall pi x, x.`_pi^'^' = x.`_pi.
Proof. by move=> pi x; rewrite /constt !partnNK. Qed.

Lemma cycle_constt : forall pi (x : gT), x.`_pi \in <[x]>.
Proof. move=> pi x; exact: mem_cycle. Qed.

Lemma consttV : forall pi x, (x^-1).`_pi = (x.`_pi)^-1.
Proof. by move=> pi x; rewrite /constt expVgn orderV. Qed.

Lemma constt1 : forall pi, 1.`_pi = 1 :> gT.
Proof. move=> pi; exact: exp1gn. Qed.

Lemma consttJ : forall pi x y, (x ^ y).`_pi = x.`_pi ^ y.
Proof. by move=> pi x y; rewrite /constt orderJ conjXg. Qed.

Lemma p_elt_constt : forall pi x, pi.-elt x.`_pi.
Proof. by move=> pi x; rewrite p_elt_exp /chinese addn0 mul1n dvdn_mulr. Qed.

Lemma consttC : forall pi x, x.`_pi * x.`_pi^' = x.
Proof.
move=> pi x; apply/eqP; rewrite -{3}[x]expg1 -expgn_add eq_expg_mod_order.
rewrite partnNK -{5 6}(@partnC pi #[x]) // /chinese !addn0.
by rewrite chinese_remainder ?chinese_modl ?chinese_modr ?coprime_partC ?eqxx.
Qed.

Lemma p'_elt_constt : forall pi x, pi^'.-elt (x * (x.`_pi)^-1).
Proof.
by move=> pi x; rewrite -{1}(consttC pi^' x) consttNK mulgK p_elt_constt.
Qed.

Lemma order_constt : forall pi (x : gT), #[x.`_pi] = #[x]`_pi.
Proof.
move=> pi x; rewrite -{2}(consttC pi x) orderM; [|exact: commuteX2|].
  rewrite partn_mul // part_pnat_id ?part_p'nat ?muln1 //; exact: p_elt_constt.
apply: (@pnat_coprime pi); exact: p_elt_constt.
Qed.

Lemma consttM : forall pi x y, commute x y -> (x * y).`_pi = x.`_pi * y.`_pi.
Proof.
move=> pi x y cxy; pose m := #|<<[set x; y]>>|.
pose k := chinese m`_pi m`_pi^' 1 0; have m_gt0: 0 < m := cardG_gt0 _.
suffices kXpi: forall z, z \in <<[set x; y]>> -> z.`_pi = z ^+ k.
  by rewrite !kXpi ?expMgn // ?groupM ?mem_gen // !inE eqxx ?orbT.
move=> z xyz; have{xyz} zm: #[z] %| m by rewrite cardSg ?cycle_subG.
apply/eqP; rewrite eq_expg_mod_order -{3 4}[#[z]](partnC pi) //.
rewrite chinese_remainder ?chinese_modl ?chinese_modr ?coprime_partC //.
rewrite -!(modn_dvdm k (partn_dvd _ m_gt0 zm)).
rewrite chinese_modl ?chinese_modr ?coprime_partC //.
by rewrite !modn_dvdm ?partn_dvd ?eqxx.
Qed.

Lemma consttX : forall pi x n, (x ^+ n).`_pi = x.`_pi ^+ n.
Proof.
move=> pi x; elim=> [|n IHn]; first exact: constt1.
rewrite !expgS consttM ?IHn //; exact: commuteX.
Qed.

Lemma constt1P : forall pi x, reflect (x.`_pi = 1) (pi^'.-elt x).
Proof.
move=> pi x; rewrite -{2}[x]expg1 p_elt_exp -order_constt consttNK.
rewrite order_dvdn expg1; exact: eqP.
Qed.

Lemma constt_p_elt : forall pi x, pi.-elt x -> x.`_pi = x.
Proof.
move=> pi x; rewrite -p_eltNK -{3}(consttC pi x); move/constt1P->.
by rewrite mulg1.
Qed.

Lemma sub_in_constt : forall pi1 pi2 x,
  {in \pi(#[x]), {subset pi1 <= pi2}} -> x.`_pi2.`_pi1 = x.`_pi1.
Proof.
move=> pi1 pi2 x pi12; rewrite -{2}(consttC pi2 x).
rewrite consttM; last exact: commuteX2.
rewrite (constt1P _ x.`_pi2^' _) ?mulg1 //.
apply: sub_in_pnat (p_elt_constt _ x) => p; rewrite order_constt => pi_p.
apply: contra; apply: pi12.
by rewrite -[#[x]](partnC pi2^') // primes_mul // pi_p.
Qed.

Lemma prod_constt : forall x, \prod_(0 <= p < #[x].+1) x.`_p = x.
Proof.
move=> x; pose lp n := [pred p | p < n].
have: (lp #[x].+1).-elt x by apply/pnatP=> // p _; exact: dvdn_leq.
move/constt_p_elt=> def_x; symmetry; rewrite -{1}def_x {def_x}.
elim: _.+1 => [|p IHp].
  by rewrite big_nil; apply/constt1P; exact/pgroupP.
rewrite big_nat_recr /= -{}IHp -(consttC (lp p) x.`__); congr (_ * _).
  rewrite sub_in_constt // => q _; exact: leqW.
set y := _.`__; rewrite -(consttC p y) (constt1P p^' _ _) ?mulg1.
  by rewrite 2?sub_in_constt // => q _; move/eqnP->; rewrite !inE ?ltnn.
rewrite /p_elt pnatNK !order_constt -partnI.
apply: sub_in_pnat (part_pnat _ _) => q _.
by rewrite !inE ltnS -leqNgt -eqn_leq.
Qed.

Lemma max_pgroupJ : forall pi M G x,
  x \in G -> [max M | pi.-subgroup(G) M] ->
   [max M :^ x of M | pi.-subgroup(G) M].
Proof.
move=> pi M G x Gx; case/maxgroupP=> piM maxM; apply/maxgroupP.
split=> [|H piH]; first by rewrite psubgroupJ.
rewrite -(conjsgKV x H) conjSg; move/maxM=> /= -> //.
by rewrite psubgroupJ ?groupV.
Qed.

Lemma comm_sub_max_pgroup : forall pi H M G,
  [max M | pi.-subgroup(G) M] -> pi.-group H -> H \subset G ->
  commute H M -> H \subset M.
Proof.
move=> pi H M G; case/maxgroupP; case/andP=> sMG piM maxM piH sHG cHM.
rewrite -(maxM (H <*> M)%G) /= comm_mulgenE ?(mulG_subl, mulG_subr) //.
by rewrite /psubgroup pgroupM piM piH mul_subG.
Qed.

Lemma normal_sub_max_pgroup : forall pi H M G,
  [max M | pi.-subgroup(G) M] -> pi.-group H -> H <| G -> H \subset M.
Proof.
move=> pi H M G maxM piH; case/andP=> sHG nHG.
apply: comm_sub_max_pgroup piH sHG _ => //; apply: commute_sym; apply: normC.
by apply: subset_trans nHG; case/andP: (maxgroupp maxM).
Qed.

Lemma norm_sub_max_pgroup : forall pi H M G,
  [max M | pi.-subgroup(G) M] -> pi.-group H -> H \subset G ->
  H \subset 'N(M) -> H \subset M.
Proof.
move=> pi H M G maxM piH sHG; move/normC; exact: comm_sub_max_pgroup piH sHG.
Qed.

Lemma sub_pHall : forall pi H G K,
  pi.-Hall(G) H -> pi.-group K -> H \subset K -> K \subset G -> K :=: H.
Proof.
move=> pi H G K hallH piK sHK sKG; apply/eqP; rewrite eq_sym eqEcard sHK.
by rewrite (card_Hall hallH) -(part_pnat_id piK) dvdn_leq ?partn_dvd ?cardSg.
Qed.

Lemma Hall_max : forall pi H G, pi.-Hall(G) H -> [max H | pi.-subgroup(G) H].
Proof.
move=> pi H G hallH; apply/maxgroupP; split=> [|K].
  by rewrite /psubgroup; case/and3P: hallH => ->.
case/andP=> sKG piK sHK; exact: (sub_pHall hallH).
Qed.

Lemma pHall_id : forall pi H G, pi.-Hall(G) H -> pi.-group G -> H :=: G.
Proof.
by move=> pi H G hallH piG; rewrite (sub_pHall hallH piG) ?(pHall_sub hallH).
Qed.

Lemma psubgroup1 : forall pi G, pi.-subgroup(G) 1.
Proof. by move=> pi G; rewrite /psubgroup sub1G pgroup1. Qed.

Lemma Cauchy : forall p G, prime p -> p %| #|G| -> {x | x \in G & #[x] = p}.
Proof.
move=> p G pr_p; elim: {G}_.+1 {-2}G (ltnSn #|G|) => // n IHn G.
rewrite ltnS => leGn pG; pose xpG := [pred x \in G | #[x] == p].
case: (pickP xpG) => [x|no_x]; first by case/andP=> Gx; move/eqP; exists x.
have{pG n leGn IHn} pZ: p %| #|'C_G(G)|.
  have:= pG; rewrite -(cardsID 'C(G)) dvdn_addl //.
  have: [acts G, on G :\: 'C(G) | 'J]; last move/acts_sum_card_orbit <-.
    by apply/actsP=> x Gx y; rewrite !inE -!mem_conjgV -centJ conjGid ?groupV.
  apply big_prop => // [|C]; first exact: dvdn_add.
  case/imsetP=> x; case/setDP=> Gx nCx ->{C}; rewrite card_orbit astab1J.
  move: pG; rewrite -(LaGrange (subsetIl G 'C[x]%G)) euclid //; case/orP => //.
  case/IHn=> [|y]; last first.
    by case/setIP=> Gy _; move/eqP=> oyp; case/andP: (no_x y).
  apply: leq_trans leGn; apply: proper_card; rewrite properE subsetIl.
  by rewrite subsetI subxx /= -cent_set1 centsC sub1set.
have [Q maxQ _]: {Q | [max Q | p^'.-subgroup('C_G(G)) Q] & 1%G \subset Q}.
  apply: maxgroup_exists; exact: psubgroup1.
case/andP: (maxgroupp maxQ) => sQC; rewrite /pgroup p'natE //; case/negP.
apply: dvdn_trans pZ (cardSg _); apply/subsetP=> x; case/setIP=> Gx Cx.
rewrite -sub1set -gen_subG (normal_sub_max_pgroup maxQ) //; last first.
  rewrite /normal subsetI !cycle_subG ?Gx ?cents_norm ?subIset ?andbT //=.
  by rewrite centsC cycle_subG Cx.
rewrite /pgroup p'natE //= -[#|_|]/#[x]; apply/dvdnP=> [[m oxm]].
have m_gt0: 0 < m by apply: dvdn_gt0 (order_gt0 x) _; rewrite oxm dvdn_mulr.
case/idP: (no_x (x ^+ m)); rewrite /= groupX //= orderXgcd //= oxm.
by rewrite gcdnC gcdn_mulr mulKn.
Qed.

(* These lemmas actually hold for maximal pi-groups, but below we'll *)
(* derive from the Cauchy lemma that a normal max pi-group is Hall.  *)

Lemma subset_normal_Hall : forall pi H G K,
  pi.-Hall(G) H -> H <| G -> (K \subset H) = pi.-subgroup(G) K.
Proof.
move=> pi H G K hallH nHG; apply/idP/andP=> [sKH | [sKG piK]].
  by case/and3P: hallH => sHG piH _; rewrite (pgroupS sKH) ?(subset_trans sKH).
apply: norm_sub_max_pgroup (Hall_max hallH) piK _ _ => //.
case/andP: nHG => _; exact: subset_trans.
Qed.

Lemma mem_normal_Hall : forall pi H G x,
  pi.-Hall(G) H -> H <| G -> x \in G -> (x \in H) = pi.-elt x.
Proof.
move=> pi H G x hallH nHG Gx; have:= subset_normal_Hall <[x]> hallH nHG.
by rewrite /psubgroup !gen_subG !sub1set Gx.
Qed.

Lemma uniq_normal_Hall : forall pi H G K,
  pi.-Hall(G) H -> H <| G -> [max K | pi.-subgroup(G) K] -> K :=: H.
Proof.
move=> pi H G K hallH nHG; case/maxgroupP.
rewrite -(subset_normal_Hall _ hallH) /psubgroup // => sKH maxK.
rewrite (maxK H) //; exact: maxgroupp (Hall_max hallH).
Qed.

End PgroupProps.

Implicit Arguments pgroupP [gT pi G].
Implicit Arguments constt1P [gT pi x].
Prenex Implicits pgroupP constt1P.

Lemma normal_max_pgroup_Hall :
  forall pi (gT : finGroupType) (G H : {group gT}),
  [max H | pi.-subgroup(G) H] -> H <| G -> pi.-Hall(G) H.
Proof.
move=> pi gT G H; case/maxgroupP; case/andP=> sHG piH maxH nHG.
have [_ nnHG] := andP nHG; rewrite /pHall sHG piH; apply/pnatP=> // p pr_p.
rewrite inE /= -pnatE // -card_quotient //.
case/Cauchy=> //= Hx; rewrite -sub1set -gen_subG -/<[Hx]> /order.
case/inv_quotientS=> //= K -> sHK sKG {Hx}.
rewrite card_quotient ?(subset_trans sKG) // => iKH; apply/negP=> pi_p.
rewrite -iKH -divgS // (maxH K) ?divnn ?cardG_gt0 // in pr_p.
by rewrite /psubgroup sKG /pgroup -(LaGrange sHK) mulnC pnat_mul iKH pi_p.
Qed.

Section Morphim.

Variables (aT rT : finGroupType) (D : {group aT}) (f : {morphism D >-> rT}).
Implicit Type pi : nat_pred.
Implicit Types G H P : {group aT}.

Lemma morphim_pgroup : forall pi G, pi.-group G -> pi.-group (f @* G).
Proof. move=> pi G; apply: pnat_dvd; exact: dvdn_morphim. Qed.

Lemma morphim_odd : forall G, odd #|G| -> odd #|f @* G|.
Proof. move=> G; rewrite !odd_2'nat; exact: morphim_pgroup. Qed.

Lemma pmorphim_pgroup : forall pi G,
   pi.-group ('ker f) -> G \subset D -> pi.-group (f @* G) = pi.-group G.
Proof.
move=> pi G piker sGD; apply/idP/idP=> [pifG|]; last exact: morphim_pgroup.
apply: (@pgroupS _ _ (f @*^-1 (f @* G))); first by rewrite -sub_morphim_pre.
by rewrite /pgroup card_morphpre ?morphimS // pnat_mul; exact/andP.
Qed.

Lemma morphim_p_index : forall pi G H,
  H \subset D -> pi.-nat #|G : H| -> pi.-nat #|f @* G : f @* H|.
Proof.
move=> pi G H dH; apply: pnat_dvd; apply: index_morphim.
by rewrite subIset // orbC dH.
Qed.

Lemma morphim_pHall : forall pi G H,
  H \subset D -> pi.-Hall(G) H -> pi.-Hall(f @* G) (f @* H).
Proof.
move=> pi G H dH; case/and3P=> sHG piH pi'GH.
by rewrite /pHall morphimS // morphim_pgroup // morphim_p_index.
Qed.

Lemma pmorphim_pHall : forall pi G H,
    G \subset D -> H \subset D -> pi.-subgroup(H :&: G) ('ker f) ->
  pi.-Hall(f @* G) (f @* H) = pi.-Hall(G) H.
Proof.
move=> pi G H sGD sHD; case/andP; rewrite subsetI; case/andP=> sKH sKG piK.
rewrite !pHallE morphimSGK //; case sHG: (H \subset G) => //=.
rewrite -(LaGrange sKH) -(LaGrange sKG) partn_mul // (part_pnat_id piK).
by rewrite !card_morphim !(setIidPr _) // eqn_pmul2l.
Qed.

Lemma morphim_Hall : forall G H,
   H \subset D -> Hall G H -> Hall (f @* G) (f @* H).
Proof.
move=> G H dH; case/HallP=> pi piH; apply: (@pHall_Hall _ pi).
exact: morphim_pHall.
Qed.

Lemma morphim_pSylow : forall p G P,
  P \subset D -> p.-Sylow(G) P -> p.-Sylow(f @* G) (f @* P).
Proof. move=> p; exact: morphim_pHall. Qed.

Lemma morphim_p_group : forall P, p_group P -> p_group (f @* P).
Proof. move=> P; move/morphim_pgroup; exact: pgroup_p. Qed.

Lemma morphim_Sylow : forall G P,
  P \subset D -> Sylow G P -> Sylow (f @* G) (f @* P).
Proof.
move=> G P dP; case/andP=> pP hallP.
by rewrite /Sylow morphim_p_group // morphim_Hall.
Qed.

Lemma morph_p_elt : forall pi x, x \in D -> pi.-elt x -> pi.-elt (f x).
Proof. move=> pi x Dx; apply: pnat_dvd; exact: morph_order. Qed.

Lemma morph_constt : forall pi x, x \in D -> f x.`_pi = (f x).`_pi.
Proof.
move=> pi x Dx; rewrite -{2}(consttC pi x) morphM ?groupX //.
rewrite consttM; last by rewrite !morphX //; exact: commuteX2.
have: pi.-elt (f x.`_pi) by rewrite morph_p_elt ?groupX ?p_elt_constt //.
have: pi^'.-elt (f x.`_pi^') by rewrite morph_p_elt ?groupX ?p_elt_constt //.
by move/constt1P->; move/constt_p_elt->; rewrite mulg1.
Qed.

End Morphim.

Section Pquotient.

Variables (pi : nat_pred) (gT : finGroupType) (p : nat) (G H K : {group gT}).
Hypothesis piK : pi.-group K.

Lemma quotient_pgroup : pi.-group (K / H). Proof. exact: morphim_pgroup. Qed.

Lemma quotient_pHall :
  K \subset 'N(H) -> pi.-Hall(G) K -> pi.-Hall(G / H) (K / H).
Proof. exact: morphim_pHall. Qed.

Lemma quotient_odd : odd #|K| -> odd #|K / H|. Proof. exact: morphim_odd. Qed.

Lemma pquotient_pgroup : G \subset 'N(K) -> pi.-group (G / K) = pi.-group G.
Proof. by move=> nKG; rewrite pmorphim_pgroup ?ker_coset. Qed.

Lemma pquotient_pHall :
  K <| G -> K <| H -> pi.-Hall(G / K) (H / K) = pi.-Hall(G) H.
Proof.
case/andP=> sKG nKG; case/andP=> sKH nKH.
by rewrite pmorphim_pHall // ker_coset /psubgroup subsetI sKH sKG.
Qed.

Lemma ltn_log_quotient :
  p.-group G -> H :!=: 1 -> H \subset G -> logn p #|G / H| < logn p #|G|.
Proof.
move=> pG ntH sHG; apply: contraLR (ltn_quotient ntH sHG); rewrite -!leqNgt.
rewrite -{2}(part_pnat_id pG) -{2}(part_pnat_id (morphim_pgroup _ pG)) !p_part.
by case: (posnP p) => [-> //|]; exact: leq_pexp2l.
Qed.

End Pquotient.

(* Application of card_Aut_cyclic to internal faithful action on cyclic *)
(* p-subgroups.                                                         *)
Section InnerAutCyclicPgroup.

Variables (gT : finGroupType) (p : nat) (G C : {group gT}).
Hypothesis nCG : G \subset 'N(C).

Lemma logn_quotient_cent_cyclic_pgroup : 
  p.-group C -> cyclic C -> logn p #|G / 'C_G(C)| <= (logn p #|C|).-1.
Proof.
move=> pC cycC; case: (eqsVneq C 1) => [-> | ntC].
  by rewrite cent1T setIT trivg_quotient cards1 logn1.
have [p_pr _ [e oC]] := pgroup_pdiv pC ntC.
rewrite -ker_conj_aut (isog_card (first_isog_loc _ _)) //.
apply: leq_trans (dvdn_leq_log _ _ (cardSg (Aut_conj_aut _ _))) _ => //.
rewrite card_Aut_cyclic // oC phi_pfactor //= logn_gauss ?pfactorK //.
by rewrite prime_coprime // gtnNdvd // -(subnKC (prime_gt1 p_pr)).
Qed.

Lemma p'group_quotient_cent_prime :
  prime p -> #|C| %| p -> p^'.-group (G / 'C_G(C)).
Proof.
move=> p_pr pC; have pgC: p.-group C := pnat_dvd pC (pnat_id p_pr).
have [_ dv_p] := primeP p_pr; case/pred2P: {dv_p pC}(dv_p _ pC) => [|pC].
  by move/card1_trivg->; rewrite cent1T setIT trivg_quotient pgroup1.
have le_oGC := logn_quotient_cent_cyclic_pgroup pgC.
rewrite /pgroup -partn_eq1 ?cardG_gt0 // -dvdn1 p_part pfactor_dvdn // logn1.
by rewrite (leq_trans (le_oGC _)) ?prime_cyclic // pC ?(pfactorK 1).
Qed.

End InnerAutCyclicPgroup.

Section PcoreDef.

(* A functor needs to quantify over the finGroupType just beore the set. *)

Variables (pi : nat_pred) (gT : finGroupType) (A : {set gT}).

Definition pcore := \bigcap_(G | [max G | pi.-subgroup(A) G]) G.

Canonical Structure pcore_group : {group gT} := Eval hnf in [group of pcore].

End PcoreDef.

Notation "''O_' pi ( G )" := (pcore pi G)
  (at level 8, pi at level 2, format "''O_' pi ( G )") : group_scope.
Notation "''O_' pi ( G )" := (pcore_group pi G) : subgroup_scope.

Section PseriesDefs.

Variables (pis : seq nat_pred) (gT : finGroupType) (A : {set gT}).

Definition pcore_mod pi B := coset B @*^-1 'O_pi(A / B).
Canonical Structure pcore_mod_group pi B : {group gT} :=
  Eval hnf in [group of pcore_mod pi B].

Definition pseries := foldr pcore_mod 1 (rev pis).

Lemma pseries_group_set : group_set pseries.
Proof. rewrite /pseries; case: rev => [|pi1 pi1']; exact: groupP. Qed.

Canonical Structure pseries_group : {group gT} := group pseries_group_set.

End PseriesDefs.

Notation Local ConsPred := (@Cons nat_pred) (only parsing).
Notation "''O_{' p1 , .. , pn } ( A )" :=
  (pseries (ConsPred p1 .. (ConsPred pn [::]) ..) A)
  (at level 8, format "''O_{' p1 , .. , pn } ( A )") : group_scope.
Notation "''O_{' p1 , .. , pn } ( A )" :=
  (pseries_group (ConsPred p1 .. (ConsPred pn [::]) ..) A) : subgroup_scope.

Section PCoreProps.

Variables (pi : nat_pred) (gT : finGroupType).
Implicit Type A : {set gT}.
Implicit Types G H M K : {group gT}.

Lemma pcore_psubgroup : forall G, pi.-subgroup(G) 'O_pi(G).
Proof.
move=> G; have [M maxM _]: {M | [max M | pi.-subgroup(G) M] & 1%G \subset M}.
  by apply: maxgroup_exists; rewrite /psubgroup sub1G pgroup1.
have sOM: 'O_pi(G) \subset M by exact: bigcap_inf.
case/andP: (maxgroupp maxM) => piM sMG.
by rewrite /psubgroup (pgroupS sOM) // (subset_trans sOM).
Qed.

Lemma pcore_pgroup : forall G, pi.-group 'O_pi(G).
Proof. by move=> G; case/andP: (pcore_psubgroup G). Qed.

Lemma pcore_sub : forall G, 'O_pi(G) \subset G.
Proof. by move=> G; case/andP: (pcore_psubgroup G). Qed.

Lemma pcore_sub_Hall : forall G H, pi.-Hall(G) H -> 'O_pi(G) \subset H.
Proof. move=> G H; move/Hall_max=> maxH; exact: bigcap_inf. Qed.

Lemma pcore_max : forall G H, pi.-group H -> H <| G -> H \subset 'O_pi(G).
Proof.
move=> G H piH nHG; apply/bigcapsP=> M maxM.
exact: normal_sub_max_pgroup piH nHG.
Qed.

Lemma pcore_pgroup_id : forall G, pi.-group G -> 'O_pi(G) = G.
Proof. by move=> G piG; apply/eqP; rewrite eqEsubset pcore_sub pcore_max. Qed.

Lemma pcore_normal : forall G, 'O_pi(G) <| G.
Proof.
move=> G; rewrite /(_ <| G) pcore_sub; apply/subsetP=> x Gx.
rewrite inE; apply/bigcapsP=> M maxM; rewrite sub_conjg.
by apply: bigcap_inf; apply: max_pgroupJ; rewrite ?groupV.
Qed.

Lemma normal_Hall_pcore : forall H G, pi.-Hall(G) H -> H <| G -> 'O_pi(G) = H.
Proof.
move=> H G hallH nHG; apply/eqP.
rewrite eqEsubset (subset_normal_Hall _ hallH) //= pcore_psubgroup.
by rewrite pcore_max //= (pHall_pgroup hallH).
Qed.

End PCoreProps.

Section MorphPcore.

Implicit Type pi : nat_pred.
Implicit Types gT rT : finGroupType.

Lemma morphim_pcore : forall pi gT rT (D G : {group gT})
                                      (f : {morphism D >-> rT}),
  f @* 'O_pi(G) \subset 'O_pi(f @* G).
Proof.
move=> pi gT rT D G f; apply/bigcapsP=> M; move/normal_sub_max_pgroup; apply.
  by rewrite morphim_pgroup ?pcore_pgroup.
apply: morphim_normal; exact: pcore_normal.
Qed.

Lemma pcoreS : forall pi gT (G H : {group gT}),
  H \subset G -> H :&: 'O_pi(G) \subset 'O_pi(H).
Proof.
move=> pi gT G H sHG; rewrite -{2}(setIidPl sHG).
do 2!rewrite -(morphim_idm (subsetIl H _)) morphimIdom; exact: morphim_pcore.
Qed.

Lemma pcore_resp : forall pi gT rT (D : {group gT}) (f : {morphism D >-> rT}),
  f @* 'O_pi(D) \subset 'O_pi(f @* D).
Proof. move=> pi gT rT D; exact: morphim_pcore. Qed.

Lemma pcore_hereditary : forall pi, hereditary (pcore pi).
Proof. by move=> pi gT H G; move/pcoreS; rewrite setIC. Qed.

Canonical Structure bgFunc_pcore pi :=
  [bgFunc by pcore_sub pi & pcore_resp pi].

Canonical Structure gFunc_pcore pi := GFunc (pcore_resp pi).

Canonical Structure hgFunc_pcore pi := HGFunc (pcore_hereditary pi).

Lemma pcore_char : forall pi gT (G : {group gT}), 'O_pi(G) \char G.
Proof. move=> pi; exact: bgFunc_char. Qed.

Section PcoreMod.

Variable F : hgFunc.

Lemma pcore_mod_sub : forall pi gT (G : {group gT}),
  pcore_mod G pi (F _ G) \subset G.
Proof.
move=> pi gT G; have nFD := bgFunc_norm F G.
rewrite sub_morphpre_im ?pcore_sub //=.
  by rewrite ker_coset_prim subIset // gen_subG bgFunc_clos.
by apply: subset_trans (pcore_sub _ _) _; apply: morphimS.
Qed.

Lemma quotient_pcore_mod : forall pi gT (G : {group gT}) (B : {set gT}),
  pcore_mod G pi B / B = 'O_pi(G / B).
Proof.
move=> pi gT A B; apply: morphpreK; apply: subset_trans (pcore_sub _ _) _.
by rewrite /= /quotient -morphimIdom  morphimS ?subsetIl.
Qed.

Lemma morphim_pcore_mod : forall pi gT rT (D G : {group gT}),
  forall f : {morphism D >-> rT},
  f @* pcore_mod G pi (F _ G) \subset pcore_mod (f @* G) pi (F _ (f @* G)).
Proof.
move=> pi gT rT D G f.
have sDF: D :&: G \subset 'dom (coset (F _ G)).
  by rewrite setIC subIset ?bgFunc_norm.
have sDFf: D :&: G \subset 'dom (coset (F _ (f @* G)) \o f).
  by rewrite -sub_morphim_pre ?subsetIl // morphimIdom bgFunc_norm.
pose K := 'ker (restrm sDFf (coset (F _ (f @* G)) \o f)).
have sFK: 'ker (restrm sDF (coset (F _ G))) \subset K.
  rewrite /K !ker_restrm ker_comp /= subsetI subsetIl /= -setIA.
  rewrite -sub_morphim_pre ?subsetIl //.
  by rewrite morphimIdom !ker_coset (setIidPr _) ?hgFunc_morphim ?bgFunc_clos.
have sOF := pcore_sub pi (G / F _ G); have sDD: D :&: G \subset D :&: G by [].
rewrite -sub_morphim_pre -?quotientE; last first.
  by apply: subset_trans (bgFunc_norm F _); rewrite morphimS ?pcore_mod_sub.
suffices im_fact: forall H : {group gT}, F _ G \subset H -> H \subset G ->
  factm sFK sDD @* (H / F _ G) = f @* H / F _ (f @* G).
- rewrite -2?im_fact ?pcore_mod_sub ?bgFunc_clos //;
    try by rewrite -{1}[F _ G]ker_coset morphpreS ?sub1G.
  by rewrite quotient_pcore_mod morphim_pcore.
move=> H sFH sHG; rewrite -(morphimIdom _ (H / _)) /= {2}morphim_restrm setIid.
rewrite -morphimIG ?ker_coset //.
rewrite -(morphim_restrm sDF) morphim_factm morphim_restrm.
by rewrite morphim_comp -quotientE -setIA morphimIdom (setIidPr _).
Qed.

Lemma pcore_mod_res : forall pi gT rT (D : {group gT}),
  forall f : {morphism D >-> rT},
  f @* pcore_mod D pi (F _ D) \subset pcore_mod (f @* D) pi (F _ (f @* D)).
Proof. move=> pi gT rT D; exact: morphim_pcore_mod. Qed.

Lemma pcore_mod1 : forall pi gT (G : {group gT}), pcore_mod G pi 1 = 'O_pi(G).
Proof.
rewrite /pcore_mod => pi gT G; have inj1 := coset1_injm gT.
rewrite -bgFunc_asresp ?norms1 //.
by rewrite -(morphim_invmE inj1) morphim_invm ?norms1.
Qed.

End PcoreMod.

Lemma pseries_rcons : forall pi pis gT (A : {set gT}),
  pseries (rcons pis pi) A = pcore_mod A pi (pseries pis A).
Proof. by move=> pi pis gT A; rewrite /pseries rev_rcons. Qed.

Lemma pseries_subfun : forall pis,
   [/\ forall gT (G : {group gT}), pseries pis G \subset G
    & forall gT rT (G D : {group gT}) (f : {morphism D >-> rT}),
      f @* (pseries pis G) \subset pseries pis (f @* G)].
Proof.
elim/last_ind=> [|pis pi [sFpi fFpi]].
  by split=> [gT G | gT rT D G f]; rewrite (sub1G, morphim1).
have [rF hF] := (resp_of_dresp fFpi, hereditary_of_dresp fFpi).
pose F := @HGFunc [gFunc by sFpi & rF] hF.
split=> [gT G | gT rT D G f]; rewrite !pseries_rcons ?(pcore_mod_sub F) //.
exact: (morphim_pcore_mod F).
Qed.

Lemma pseries_sub : forall pis gT (G : {group gT}), pseries pis G \subset G.
Proof. by move=> pis; case: (pseries_subfun pis). Qed.

Lemma morphim_pseries : forall pis gT rT (D G : {group gT}),
  forall f : {morphism D >-> rT},
  f @* (pseries pis G) \subset pseries pis (f @* G).
Proof. by move=> pis; case: (pseries_subfun pis). Qed.

Lemma pseries_resp : forall pis gT rT (G : {group gT}),
  forall f : {morphism G >-> rT},
  f @* (pseries pis G) \subset pseries pis (f @* G).
Proof. by move=> pis gT rT G; exact: morphim_pseries. Qed.

Lemma pseriesS : forall pis, hereditary (pseries pis).
Proof.
move=> pis gT H G sHG; rewrite -{2}(setIidPl sHG) {1}setIC.
do 2!rewrite -(morphim_idm (subsetIl H _)) morphimIdom; exact: morphim_pseries.
Qed.

Canonical Structure bgFunc_pseries pis :=
  [bgFunc by pseries_sub pis & pseries_resp pis].

Canonical Structure gFunc_pseries pis := GFunc (pseries_resp pis).

Canonical Structure hgFunc_pseries pis := HGFunc (pseriesS pis).

Lemma pseries_char : forall pis gT (G : {group gT}), pseries pis G \char G.
Proof. move=> pis; exact: bgFunc_char. Qed.

Lemma pseries_normal : forall pis gT (G : {group gT}), pseries pis G <| G.
Proof. move=> pis; exact: bgFunc_normal. Qed.

Lemma pseries1 : forall pi gT (G : {group gT}), 'O_{pi}(G) = 'O_pi(G).
Proof. exact: pcore_mod1. Qed.

Lemma pseries_pop : forall pi pis gT (G : {group gT}),
  'O_pi(G) = 1 -> pseries (pi :: pis) G = pseries pis G.
Proof.
move=> pi pis gT G OG1.
by rewrite /pseries rev_cons -cats1 foldr_cat /= pcore_mod1 OG1.
Qed.

Lemma pseries_pop2 : forall pi1 pi2 gT (G : {group gT}),
  'O_pi1(G) = 1 -> 'O_{pi1, pi2}(G) = 'O_pi2(G).
Proof. move=> pi1 pi2 gT G; move/pseries_pop->; exact: pseries1. Qed.

Lemma pseries_sub_catl : forall pi1s pi2s gT (G : {group gT}),
  pseries pi1s G \subset pseries (pi1s ++ pi2s) G.
Proof.
move=> pi1s pis gT G; elim/last_ind: pis => [|pi pis IHpi]; rewrite ?cats0 //.
rewrite -rcons_cat pseries_rcons; apply: subset_trans IHpi _.
by rewrite sub_cosetpre.
Qed.

Lemma quotient_pseries : forall pis pi gT (G : {group gT}),
  pseries (rcons pis pi) G / pseries pis G = 'O_pi(G / pseries pis G).
Proof. by move=> pis pi gT G; rewrite pseries_rcons quotient_pcore_mod. Qed.

Lemma pseries_norm2 : forall pi1s pi2s gT (G : {group gT}),
  pseries pi2s G \subset 'N(pseries pi1s G).
Proof.
move=> pi1s pi2s gt G.
apply: subset_trans (normal_norm (pseries_normal pi1s G)); exact: pseries_sub.
Qed.

Lemma pseries_sub_catr : forall pi1s pi2s gT (G : {group gT}),
  pseries pi2s G \subset pseries (pi1s ++ pi2s) G.
Proof.
elim=> //= pi1 pi1s IH pi2s gT G; apply: subset_trans (IH _ _ _) _ => {IH}.
elim/last_ind: {pi1s pi2s}(_ ++ _) => [|pis pi IHpi]; first exact: sub1G.
rewrite -rcons_cons (pseries_rcons _ (pi1 :: pis)).
rewrite -sub_morphim_pre ?pseries_norm2 //.
apply: pcore_max; last by rewrite morphim_normal ?pseries_normal.
have: pi.-group (pseries (rcons pis pi) G / pseries pis G).
  by rewrite quotient_pseries pcore_pgroup.
by apply: pnat_dvd; rewrite !card_quotient ?pseries_norm2 // indexgS.
Qed.

Lemma quotient_pseries2 : forall pi1 pi2 gT (G : {group gT}),
  'O_{pi1, pi2}(G) / 'O_pi1(G) = 'O_pi2(G / 'O_pi1(G)).
Proof. by move=> pi1 pi2 gT G; rewrite -pseries1 -quotient_pseries. Qed.

Lemma quotient_pseries_cat : forall pi1s pi2s gT (G : {group gT}),
  pseries (pi1s ++ pi2s) G / pseries pi1s G
    = pseries pi2s (G / pseries pi1s G).
Proof.
move=> pi1s pis gT G; elim/last_ind: pis => [|pis pi IHpi].
  by rewrite cats0 trivg_quotient.
have psN := pseries_normal _ G; set K := pseries _ G.
case: (third_isom (pseries_sub_catl pi1s pis G) (psN _)) => //= f inj_f im_f.
have nH2H: pseries pis (G / K) <| pseries (pi1s ++ rcons pis pi) G / K.
  rewrite -IHpi morphim_normal // -cats1 catA.
  by apply/andP; rewrite pseries_sub_catl pseries_norm2.
apply: (quotient_inj nH2H).
  by apply/andP; rewrite /= -cats1 pseries_sub_catl pseries_norm2.
rewrite /= quotient_pseries /= -IHpi -rcons_cat.
rewrite -[G / _ / _](morphim_invm inj_f) //= {2}im_f //.
have:= @bgFunc_asresp (bgFunc_pcore pi).
move <-; rewrite /= ?injm_invm ?im_f // -quotient_pseries.
by rewrite -im_f ?morphim_invm ?morphimS ?normal_sub.
Qed.

Lemma pseries_catl_id : forall pi1s pi2s gT (G : {group gT}),
  pseries pi1s (pseries (pi1s ++ pi2s) G) = pseries pi1s G.
Proof.
elim/last_ind=> [|pis pi IHpi] pi2s gT G; first by [].
apply: (@quotient_inj _ (pseries_group pis G)).
- rewrite /= -(IHpi (pi :: pi2s)) cat_rcons /(_ <| _) pseries_norm2.
  by rewrite -cats1 pseries_sub_catl.
- by rewrite /= /(_ <| _) pseries_norm2 -cats1 pseries_sub_catl.
rewrite /= cat_rcons -(IHpi (pi :: pi2s)) {1}quotient_pseries IHpi.
apply/eqP; rewrite quotient_pseries eqEsubset !pcore_max ?pcore_pgroup //=.
  rewrite -quotient_pseries morphim_normal // /(_ <| _) pseries_norm2.
  by rewrite -cat_rcons pseries_sub_catl.
apply: char_normal_trans (pcore_char pi _) (morphim_normal _ _).
exact: pseries_normal.
Qed.

Lemma pseries_char_catl : forall pi1s pi2s gT (G : {group gT}),
  pseries pi1s G \char pseries (pi1s ++ pi2s) G.
Proof.
by move=> pi1s pi2s gT G; rewrite -(pseries_catl_id pi1s pi2s G) pseries_char.
Qed.

Lemma pseries_catr_id : forall pi1s pi2s gT (G : {group gT}),
  pseries pi2s (pseries (pi1s ++ pi2s) G) = pseries pi2s G.
Proof.
move=> pi1s pis gT; elim/last_ind: pis => [|pis pi IHpi] G; first by [].
have Epis: pseries pis (pseries (pi1s ++ rcons pis pi) G) = pseries pis G.
  by rewrite -cats1 catA -2!IHpi pseries_catl_id.
apply: (@quotient_inj _ (pseries_group pis G)).
- by rewrite /= -Epis /(_ <| _) pseries_norm2 -cats1 pseries_sub_catl.
- by rewrite /= /(_ <| _) pseries_norm2 -cats1 pseries_sub_catl.
rewrite /= -Epis {1}quotient_pseries Epis quotient_pseries.
apply/eqP; rewrite eqEsubset !pcore_max ?pcore_pgroup //=.
  rewrite -quotient_pseries morphim_normal // /(_ <| _) pseries_norm2.
  by rewrite pseries_sub_catr.
apply: char_normal_trans (pcore_char pi _) (morphim_normal _ _).
exact: pseries_normal.
Qed.

Lemma pseries_char_catr : forall pi1s pi2s gT (G : {group gT}),
  pseries pi2s G \char pseries (pi1s ++ pi2s) G.
Proof.
by move=> pi1s pi2s gT G; rewrite -(pseries_catr_id pi1s pi2s G) pseries_char.
Qed.

Lemma pcore_modp : forall pi gT (G H : {group gT}),
  H <| G -> pi.-group H -> pcore_mod G pi H = 'O_pi(G).
Proof.
move=> pi gT G H nHG piH; apply/eqP; rewrite eqEsubset andbC.
have nnHG := normal_norm nHG; have sOG := subset_trans (pcore_sub pi _).
rewrite -sub_morphim_pre ?(sOG, morphim_pcore) // pcore_max //.
  rewrite -(pquotient_pgroup piH) ?subsetIl //.
  by rewrite quotient_pcore_mod pcore_pgroup.
by rewrite -{2}(quotientGK nHG) morphpre_normal ?pcore_normal ?sOG ?morphimS.
Qed.

Lemma pquotient_pcore : forall pi gT (G H : {group gT}),
  H <| G -> pi.-group H -> 'O_pi(G / H) = 'O_pi(G) / H.
Proof. by move=> *; rewrite -quotient_pcore_mod pcore_modp. Qed.

Lemma trivg_pcore_quotient : forall pi gT (G : {group gT}),
  'O_pi(G / 'O_pi(G)) = 1.
Proof.
move=> pi gT G; rewrite pquotient_pcore ?pcore_normal ?pcore_pgroup //.
exact: trivg_quotient.
Qed.

Lemma pseries_rcons_id : forall pis pi gT (G : {group gT}),
  pseries (rcons (rcons pis pi) pi) G = pseries (rcons pis pi) G.
Proof.
move=> pis pi gT G; apply/eqP; rewrite -!cats1 eqEsubset pseries_sub_catl andbT.
rewrite -catA -(quotientSGK _ (pseries_sub_catl _ _ _)) ?pseries_norm2 //.
rewrite !quotient_pseries_cat -quotient_sub1 ?pseries_norm2 //.
by rewrite quotient_pseries_cat /= !pseries1 trivg_pcore_quotient.
Qed.

End MorphPcore.

Section SubPcore.

Variable gT : finGroupType.
Implicit Types pi : nat_pred.
Implicit Type G : {group gT}.

Lemma sub_pcore : forall pi1 pi2 G,
  {subset pi1 <= pi2} -> 'O_pi1(G) \subset 'O_pi2(G).
Proof.
move=> pi1 pi2 G sub_pi; rewrite pcore_max ?pcore_normal //.
apply: sub_in_pnat (pcore_pgroup _ _) => p _; exact: sub_pi.
Qed.

Lemma eq_pcore : forall pi1 pi2 G, pi1 =i pi2 -> 'O_pi1(G) = 'O_pi2(G).
Proof.
move=> pi1 pi2 G eq_pi; apply/eqP; rewrite eqEsubset.
by rewrite !sub_pcore // => p; rewrite eq_pi.
Qed.

Lemma pcoreI : forall pi1 pi2 G, 'O_[predI pi1 & pi2](G) = 'O_pi1('O_pi2(G)).
Proof.
move=> pi1 pi2 G; apply/eqP; rewrite eqEsubset !pcore_max //.
- rewrite /pgroup pnatI [pnat _ _]pcore_pgroup.
  exact: pgroupS (pcore_sub _ _) (pcore_pgroup _ _).
- exact: char_normal_trans (pcore_char _ _) (pcore_normal _ _).
- by apply: sub_in_pnat (pcore_pgroup _ _) => p _; case/andP.
apply/andP; split; first by apply: sub_pcore => p; case/andP.
apply: subset_trans (pcore_sub _ _) (normal_norm _); exact: pcore_normal.
Qed.

Lemma bigcap_p'core : forall pi G,
  G :&: \bigcap_(p < #|G|.+1 | (p : nat) \in pi) 'O_p^'(G) = 'O_pi^'(G).
Proof.
move=> pi G; apply/eqP; rewrite eqEsubset subsetI pcore_sub pcore_max /=.
- by apply/bigcapsP=> p pi_p; apply: sub_pcore => r; apply: contra; move/eqnP->.
- apply/pgroupP=> q q_pr qGpi'; apply: contraL (eqxx q) => /= pi_q.
  apply: (pgroupP (pcore_pgroup q^' G)) => //.
  have qG: q %| #|G| by rewrite (dvdn_trans qGpi') // cardSg ?subsetIl.
  have ltqG: q < #|G|.+1 by rewrite ltnS dvdn_leq.
  rewrite (dvdn_trans qGpi') ?cardSg ?subIset //= orbC.
  by rewrite (bigcap_inf (Ordinal ltqG)).
rewrite /normal subsetIl normsI ?normG //.
apply big_prop => [|H K nHG nKG|p _]; rewrite ?normsI ?bgFunc_norm //.
by rewrite normsG // subsetT.
Qed.

Lemma coprime_pcoreC : forall (xT : finGroupType) pi G (H : {group xT}),
  coprime #|'O_pi(G)| #|'O_pi^'(H)|.
Proof. move=> *; exact: pnat_coprime (pcore_pgroup _ _) (pcore_pgroup _ _). Qed.

Lemma TI_pcoreC : forall pi (G H : {group gT}), 'O_pi(G) :&: 'O_pi^'(H) = 1.
Proof. by move=> pi G H; rewrite coprime_TIg ?coprime_pcoreC. Qed.

End SubPcore.

