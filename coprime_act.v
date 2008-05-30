Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq div.
Require Import fintype paths connect finfun ssralg bigops finset.
Require Import groups normal group_perm automorphism action.
Require Import cyclic center sylow schurzass hall.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Import GroupScope.

Section InternalAction.

Variable pi : pred nat.
Variable gT : finGroupType.
Implicit Types G H K A X : {group gT}.

Lemma coprime_norm_cent : forall A G,
  A \subset 'N(G) -> coprime #|G| #|A| ->
  N_(G)(A) = C_(G)(A).
Proof.
move=> A G nGA coGA; apply/eqP; rewrite eqset_sub andbC setIS ?sub_centg //=.
rewrite subsetI subsetIl /=; apply/centralP; apply/commG1P.
apply: subset_trans (coprime_trivg coGA); rewrite gen_subG.
apply/subsetP=> xy; case/imset2P=> x y; case/setIP=> Gx nAx Ay ->{xy}.
rewrite inE {1}commgEl commgEr (groupMr _ Ay) groupMl  ?groupV //.
by rewrite !memJ_normg ?groupV // ?(subsetP nGA, Gx).
Qed.

Lemma coprime_hall_exists : forall A G,
  A \subset 'N(G) -> coprime #|G| #|A| -> solvable G ->
  exists2 H : {group gT}, hall_for pi G H & A \subset 'N(H).
Proof.
move=> A G nGA coGA solG; case: (HallExist pi solG) => H hallH.
have sG_AG: G \subset A <*> G by rewrite -{1}genGid genSg ?subsetUr.
have nG_AG: A <*> G \subset 'N(G) by rewrite gen_subG subUset nGA normG.
pose N := N_(A <*> G)(H)%G.
have nGN: N \subset 'N(G) by rewrite subIset ?nG_AG.
have nGN_N: G :&: N <| N.
  apply/normalsubP; rewrite subsetIr; split=> // x Nx.
  by rewrite conjIg (normgP _) // (subsetP nGN, conjGid).
have NG_AG : G * N = A <*> G by apply: HallFrattini hallH => //; exact/andP.
have iGN_A: #|N| %/ #|G :&: N| = #|A|.
  rewrite group_divn ?subsetIr // -card_quotient; last by case/andP: nGN_N.
  rewrite (isog_card (second_isom nGN)) /= -(quotient_mulg nGN) (normC nGN).
  rewrite NG_AG card_quotient // -group_divn //= norm_mulgenE //.
  by rewrite coprime_card_mulG 1?coprime_sym // divn_mull.
have hallGN: hall N (G :&: N).
  move: coGA; rewrite -(LaGrange (subsetIl G N)) coprime_mull.
  by rewrite /hall subsetIr iGN_A; case/andP.
case/splitgP: {hallGN nGN_N}(SchurZass_split hallGN nGN_N) => B trBGN defN.
have{trBGN iGN_A} oBA: #|B| = #|A|.
  by rewrite -iGN_A -{1}defN (card_mulG_trivP _ _ trBGN) divn_mulr.
have sBN: B \subset N by rewrite -defN mulG_subr.
case: (SchurZass_trans_sol solG nGA _ coGA oBA) => [|x Gx defB].
  by rewrite -(normC nGA) -norm_mulgenE // -NG_AG -(mul1g B) mulgSS ?sub1G.
exists (H :^ x^-1)%G; first by rewrite hall_for_conj ?groupV.
apply/subsetP=> y Ay; have: y ^ x \in B by rewrite defB memJ_conjg.
move/(subsetP sBN); case/setIP=> _; move/normgP=> nHyx.
by apply/normgP; rewrite -conjsgM conjgCV invgK conjsgM nHyx.
Qed.

Lemma coprime_hall_trans : forall A G H1 H2,
  A \subset 'N(G) -> coprime #|G| #|A| -> solvable G ->
  hall_for pi G H1 -> A \subset 'N(H1) ->
  hall_for pi G H2 -> A \subset 'N(H2) ->
  exists2 x, x \in C_(G)(A) & H1 = (H2 :^ x)%G.
Proof.
move=> A G H H' nGA coGA solG hallH nHA hallH'.
case: {hallH'}(HallConj solG hallH' hallH) => x Gx ->{H'} nHxA.
have sG_AG: G \subset A <*> G by rewrite -{1}genGid genSg ?subsetUr.
have nG_AG: A <*> G \subset 'N(G) by rewrite gen_subG subUset nGA normG.
pose N := N_(A <*> G)(H)%G.
have nGN: N \subset 'N(G) by rewrite subIset ?nG_AG.
have nGN_N: G :&: N <| N.
  apply/normalsubP; rewrite subsetIr; split=> // y Ny.
  by rewrite conjIg (normgP _) // (subsetP nGN, conjGid).
have NG_AG : G * N = A <*> G by apply: HallFrattini hallH => //; exact/andP.
have iGN_A: indexg (G :&: N) N = #|A|.
  rewrite -card_quotient //; last by case/andP: nGN_N.
  rewrite (isog_card (second_isom nGN)) /= -(quotient_mulg nGN) (normC nGN).
  rewrite NG_AG card_quotient // -group_divn //= norm_mulgenE //.
  by rewrite coprime_card_mulG 1?coprime_sym // divn_mull.
have solGN: solvable (G :&: N) by apply: solvable_sub solG; exact: subsetIl.
have oAxA: #|A :^ x^-1| = #|A| by exact: card_conjg.
have sAN: A \subset N by rewrite subsetI -{1}genGid genSg // subsetUl.
have nGNA: A \subset 'N(G :&: N).
  by apply/normalP=> y ?; rewrite conjIg (normalP nGA) ?(conjGid, subsetP sAN).
have coGNA: coprime #|G :&: N| #|A|.
  by move: coGA; rewrite -(LaGrange (subsetIl G N)) coprime_mull; case/andP.
case: (SchurZass_trans_sol solGN nGNA _ coGNA oAxA) => [|y GNy [defAx]].
  have ->: (G :&: N) * A = N.
    apply/eqP; rewrite eqset_sub_card -{2}(mulGid N) mulgSS ?subsetIr //=.
    by rewrite coprime_card_mulG // -iGN_A LaGrange ?subsetIr.
  apply/subsetP=> yx; case/imsetP=> y Ay ->{yx}.
  rewrite inE groupJ ?groupV ?mem_geng //=; try by [apply/setUP; auto].
  by apply/normgP; rewrite !conjsgM invgK (normalP nHxA) // conjsgK.
case/setIP: GNy => Gy; case/setIP=> _; move/normgP=> nHy.
exists (y * x)^-1.
  rewrite -coprime_norm_cent // groupV inE groupM //=; apply/normgP.
  by rewrite conjsgM -defAx conjsgKV.
by apply: val_inj; rewrite /= -{2}nHy -(conjsgM _ y) conjsgK.
Qed.


Lemma norm_conj_cent : forall A G x, x \in 'C(A) ->
  (A \subset 'N(G :^ x)) = (A \subset 'N(G)).
Proof.
move=> A G x; move/centgP=> cAx; apply/normalP/normalP=> nGA y Ay.
  by rewrite -[G :^ y](conjsgK x) -(conjsgM _ y) -cAx // conjsgM nGA ?conjsgK.
by rewrite -conjsgM cAx // conjsgM nGA.
Qed.

Lemma coprime_quotient_cent : forall A G H,
    H <| G -> A \subset 'N(H) -> coprime #|H| #|A| -> solvable H ->
  C_(G)(A) / H = C_(G / H)(A / H).
Proof.
move=> A G H; case/normalsubP=> sHG nHG nHA coHA solH.
apply/eqP; rewrite eqset_sub subsetI imsetS ?subsetIl //=.
rewrite (subset_trans _ (imset_cent _ _)) ?imsetS ?subsetIr //=.
apply/subsetP=> xb; case/setIP; case/quotientP=> x [Gx Nx def_x] cAxb.
have{cAxb} cAx: forall y, y \in A -> [~ x, y] \in H.
  move=> y Ay; have Ny: y \in 'N(H) by exact: subsetP Ay.
  have dH := subsetP (subset_dom_coset H).
  rewrite coset_of_idr ?groupR // morphR ?dH //= -def_x.
  by apply/eqP; apply/commgP; apply: (centgP cAxb); exact: imset_f_imp.
have AxAH : A :^ x \subset H * A.
  apply/subsetP=> yx; case/imsetP=> y Ay ->{yx}.
  rewrite -normC // -(mulKVg y (y ^ x)) -commgEl mem_mulg //.
  by rewrite -groupV invg_comm cAx.
case: (SchurZass_trans_sol _ nHA AxAH) => // [|y Hy]; first exact: card_conjg.
case=> def_Ax; apply/imsetP; exists (x * y^-1); last first.
  apply: val_inj; rewrite def_x /= coset_ofN //.
  rewrite coset_ofN ?(groupMl, groupV) // ?(subsetP (normG H)) //.
  by rewrite conjgCV rcosetM [H :* _ ^ _]rcoset_id // memJ_normg groupV.
rewrite inE groupMl // ?(groupV, subsetP sHG) //=.
apply/centgP=> z Az; apply/commgP; apply/eqP; apply/set1P.
apply: (subsetP (coprime_trivg coHA)); rewrite inE {1}commgEl commgEr.
rewrite invMg -mulgA invgK groupMl // conjMg mulgA -commgEl.
rewrite groupMl ?cAx // memJ_normg ?(groupV, subsetP nHA) // Hy /=.
by rewrite groupMr // conjVg groupV conjgM -mem_conjg -def_Ax memJ_conjg.
Qed.

End InternalAction.

Lemma coprime_has_primes : forall m n, m > 0 -> n > 0 ->
  coprime m n = ~~ has (mem (primes m)) (primes n).
Proof.
move=> m n m_pos n_pos; apply/eqnP/hasPn=> [mn1 p | no_p_mn].
  rewrite /= !mem_primes m_pos n_pos /=; case/andP=> pr_p p_n.
  have:= prime_gt1 pr_p; rewrite pr_p ltnNge -mn1 /=; apply: contra => p_m.
  by rewrite dvdn_leq ?ltn_0gcd ?m_pos // dvdn_gcd ?p_m.
case: (ltngtP (gcdn m n) 1) => //; first by rewrite ltnNge ltn_0gcd ?m_pos.
move/prime_pdiv; set p := pdiv _ => pr_p.
move/implyP: (no_p_mn p); rewrite /= !mem_primes m_pos n_pos pr_p /=.
by rewrite !(dvdn_trans (dvdn_pdiv _)) // (dvdn_gcdl, dvdn_gcdr).
Qed.

Lemma coprime_hall_subset : forall pi (gT : finGroupType) (A G X : {group gT}),
  A \subset 'N(G) -> coprime #|G| #|A| -> solvable G ->
  pi_subgroup pi G X -> A \subset 'N(X) ->
  exists H : {group gT}, [/\ hall_for pi G H, A \subset 'N(H) & X \subset H].
Proof.
move=> pi gT A G; move: {2}_.+1 (ltnSn #|G|) => n.
elim: n => // n IHn in gT A G *; rewrite ltnS => leGn X nGA coGA solG piX nXA.
case trG: (trivg G); last move/idPn: trG => trG.
  case: (coprime_hall_exists pi nGA) => // H hallH nHA; exists H; split=> //.
  by apply: subset_trans (subset_trans trG (sub1G _)); case/andP: piX.
have sG_AG: G \subset A <*> G by rewrite -{1}genGid genSg ?subsetUr.
have sA_AG: A \subset A <*> G by rewrite -{1}genGid genSg ?subsetUl.
have nG_AG: A <*> G \subset 'N(G) by rewrite gen_subG subUset nGA normG.
have nsG_AG: G <| A <*> G by exact/andP.
case: (solvable_norm_abel solG nsG_AG) => // M [sMG nMAG ntM [abelM]].
have{nMAG} [nMA nMG]: A \subset 'N(M) /\ G \subset 'N(M).
  by apply/andP; rewrite -subUset -gen_subG; case/andP: nMAG.
have nMX: X \subset 'N(M) by case/andP: piX; move/subset_trans->.
set p := pdiv #|M| => elemM.
have pr_p: prime p by rewrite prime_pdiv // ltnNge -trivg_card.
have{elemM} pM: primes #|M| = [:: p].
  apply: (eq_sorted_irr ltn_trans ltnn); rewrite ?sorted_primes // => q.
  rewrite mem_primes mem_seq1 pos_card_group /=.
  apply/andP/eqP=> [[pr_q q_M] | ->]; last by rewrite dvdn_pdiv.
  case: (cauchy pr_q q_M) => x; case/andP=> Mx; move/eqP=> oxp.
  have:= elemM _ Mx; rewrite [#[x]]oxp; case/primeP: pr_p => _ pr_p.
  by move/pr_p; case/orP; move/eqP=> // q1; rewrite q1 in pr_q.
pose Gb := (G / M)%G; pose Ab := (A / M)%G; pose Xb := (X / M)%G.
have oAb: #|Ab| = #|A|.
  rewrite /= -quotient_mulg // -norm_mulgenE // card_quotient; last first.
    by rewrite gen_subG subUset nMA normG.
  rewrite -group_divn /= norm_mulgenE ?mulG_subr //.
  rewrite coprime_card_mulG ?divn_mull // coprime_sym.
  by move: coGA; rewrite -(LaGrange sMG) coprime_mull; case/andP.
have dM := subset_dom_coset M.
case: (IHn _ Ab Gb _ Xb); do 1?[exact: solvable_quo | exact: imset_normal].
- rewrite -[#|_|]mul1n card_quotient //.
  apply: leq_trans leGn; have:= pos_card_group G.
  rewrite -(LaGrange sMG) ltn_0mul; case/andP=> _ M'pos.
  by rewrite ltn_pmul2r // ltnNge -trivg_card.
- rewrite card_quotient // oAb.
  by move: coGA; rewrite -(LaGrange sMG) coprime_mull; case/andP.
- case/andP: piX => sXG piX; rewrite /pi_subgroup imsetS //=.
  rewrite -(isog_card (second_isom nMX)) /= card_quotient //; last first.
    by apply/normalP=> x Xx; rewrite conjIg (normalP nMX) ?conjGid.
  apply/allP=> q Xq; apply: (allP piX).
  by rewrite -(LaGrange (subsetIr M X)) primes_mul ?Xq ?orbT.
move=> Hb []; case/and3P=> sHGb piHb pi'Hb' nHbA sXHb.
case/inv_quoS: (sHGb) => [|HM [defHM sMHM sHMG]]; first exact/andP.
have{Xb sXHb} sXHM: X \subset HM.
  apply/subsetP=> x Xx; have:= rcoset_refl M x.
  have: coset_of M x \in Hb by apply: (subsetP sXHb); exact: imset_f_imp.
  rewrite defHM; case/quotientP=> y [Hy Ny]; move/(congr1 val).
  rewrite /= !coset_ofN // ?(subsetP nMX) // => ->.
  by case/rcosetP=> z Mz ->; rewrite groupMl // (subsetP sMHM).
have{pi'Hb' sHGb} pi'HM': all (predC pi) (primes (indexg HM G)).
  move: pi'Hb'; rewrite -!group_divn // defHM !card_quotient //; last first.
  - exact: subset_trans nMG.
  by rewrite -(divn_pmul2l (pos_card_group M)) !LaGrange.
have{Ab oAb nHbA} nHMA: A \subset 'N(HM).
  apply/subsetP=> x Ax; rewrite inE.
  apply/subsetP=> yx; case/imsetP=> y HMy ->{yx}.
  have nMy: y \in 'N(M) by rewrite (subsetP nMG) // (subsetP sHMG).
  have:= rcoset_refl M (y ^ x); have: coset_of M (y ^ x) \in Hb.
    rewrite morphJ ?(subsetP dM, subsetP nMA x Ax) //.
    rewrite memJ_normg; first by rewrite defHM imset_f_imp.
    by rewrite (subsetP nHbA) ?imset_f_imp.
  rewrite defHM; case/quotientP=> z [Hz Nz]; move/(congr1 val).
  rewrite /= !coset_ofN // => [->|]; last by rewrite groupJ // (subsetP nMA).
  by case/rcosetP=> t Mt ->; rewrite groupMl // (subsetP sMHM).
case pi_p: (pi p).
  exists HM; split=> //; apply/and3P; split=> //.
  rewrite -(LaGrange sMHM) -card_quotient //; last exact: subset_trans nMG.
  rewrite -[HM / M]/(val (HM / M)%G) -defHM /=.
  apply/allP=> q; rewrite primes_mul ?pos_card_group // pM mem_seq1.
  by case/predU1P => [-> //|]; move/(allP piHb).
case: (ltnP #|HM| #|G|) => [ltHG | leGHM {n IHn leGn}].
  case: (IHn _ A HM (leq_trans ltHG leGn) X) => // [|||H [hallH nHA sXH]].
  - by move: coGA; rewrite -(LaGrange sHMG) coprime_mull; case/andP.
  - exact: solvable_sub solG.
  - by apply/andP; case/andP: piX.
  case/and3P: hallH => sHHM piH pi'H'.
  have sHG: H \subset G by exact: subset_trans sHMG.
  exists H; split=> //; apply/and3P; split=> //; apply/allP=> x.
  rewrite -group_divn // -(LaGrange sHMG) -(LaGrange sHHM) -mulnA divn_mulr //.
  rewrite primes_mul //.
  case/orP; [exact: (allP pi'H') | exact: (allP pi'HM')].
have{leGHM nHMA sHMG sMHM sXHM pi'HM'} eqHMG: HM = G.
  by apply/eqP; rewrite -val_eqE eqset_sub_card sHMG.
have{HM Hb defHM eqHMG piHb} hallM: hall_for (predC pi) G M.
  rewrite /hall_for sMG pM /= pi_p -card_quotient //.
  by apply/allP=> q GMq; rewrite /= negbK (allP piHb) // defHM eqHMG.
case: (coprime_hall_exists pi nGA) => // H hallH nHA.
pose XM := (X <*> M)%G; pose Y := (H :&: XM)%G.
case/andP: piX => sXG piX; case: (and3P hallH) => sHG piH _.
have sXXM: X \subset XM by rewrite  -{1}genGid genSg ?subsetUl.
have co_pi_M: forall B : {group gT}, all pi (primes #|B|) -> coprime #|B| #|M|.
  move=> B; move/allP=> piB; rewrite coprime_sym coprime_has_primes //.
  rewrite (hall_for_part hallM); apply/hasPn=> q Bq.
  by rewrite primes_pi_part /= mem_filter /= piB.
have hallX: hall_for pi XM X.
  rewrite /hall_for piX sXXM -group_divn //= norm_mulgenE //.
  by rewrite coprime_card_mulG ?co_pi_M // divn_mulr; case/and3P: hallM.
have hallY: hall_for pi XM Y.
  have sYXM: Y \subset XM by rewrite subsetIr.
  have piY: all pi (primes #|Y|).
    apply/allP=> q Yq; apply: (allP piH).
    by rewrite -(LaGrange (subsetIl H XM)) primes_mul ?Yq.
  apply/and3P; split; rewrite // -group_divn // -((Y * M =P XM) _).
    by rewrite coprime_card_mulG ?co_pi_M // divn_mulr; case/and3P: hallM.
  rewrite /= setIC group_modr /= norm_mulgenE ?mulG_subr // eqsetIl.
  rewrite ((H * M =P G) _) ?eqset_sub_card -(mulGid G) mulgSS //= mulGid.
  rewrite coprime_card_mulG ?co_pi_M //.
  by rewrite (hall_for_part hallM) (hall_for_part hallH) pi_partC.
have nXMA: A \subset 'N(XM).
  apply/normalP=> x Ax; rewrite /= norm_mulgenE // conjsMg.
  by rewrite (normalP nMA) ?(normalP nXA).
have sXMG: XM \subset G by rewrite gen_subG subUset sXG.
case: (coprime_hall_trans nXMA _ _ hallX nXA hallY) => [|||x].
- by have:= coGA; rewrite -(LaGrange sXMG) coprime_mull; case/andP.
- exact: solvable_sub solG.
- by apply/normalP=> x Ax; rewrite conjIg (normalP nHA) ?(normalP nXMA).
case/setIP=> XMx cAx ->; exists (H :^ x)%G; split.
- by rewrite hall_for_conj ?(subsetP sXMG).
- by rewrite norm_conj_cent.
by rewrite conjSg subsetIl.
Qed.

Module AfterInner. End AfterInner.

(* Should be in action.v. *)
Definition fix_act (sT aT : finType) (A : {set aT}) to :=
  [set x : sT | forallb a, (a \in A) ==> (to x a == x)].

Definition stab_act (sT aT : finType) to (S : {set aT}) :=
  [set a : aT | forallb x, (x \in S) ==> (to x a == x)].

Notation "''C' ( A | to )" := (fix_act A to)
 (at level 9, format "''C' ( A  |  to )") : group_scope.

Notation "'C_' ( S ) ( A | to )" := (S :&: 'C(A | to))
 (at level 9, format "'C_' ( S ) ( A  |  to )") : group_scope.

Notation "'C_' ( | to ) ( S )" := (stab_act to S)
 (at level 9, format "'C_' ( |  to ) ( S )") : group_scope.

Notation "'C_' ( A | to ) ( S )" := (A :&: C_(|to)(S))
 (at level 9, format "'C_' ( A  |  to ) ( S )") : group_scope.

Definition stabs_act (aT sT : finType) to (S : {set sT}) :=
  [ set a : aT | to^~ a @: S \subset S ].

Notation "'N_' ( | to ) ( S )" := (stabs_act to S)
  (at level 9, format "'N_' ( | to ) ( S )") : group_scope.

Notation "'N_' ( A | to ) ( S )" := (A :&: N_(|to)(S))
  (at level 9, format "'N_' ( A  |  to ) ( S )") : group_scope.

Notation "'C_' ( | to ) [ x ]" := C_(|to)([set x])
  (at level 9, format "'C_' ( | to ) [ x ]") : group_scope.

Notation "'C_' ( A | to ) [ x ]" := C_(A | to)([set x])
  (at level 9, format "'C_' ( A  |  to ) [ x ]") : group_scope.

Notation "''C' [ a | to ]" := 'C([set a] | to)
  (at level 9, format "''C' [ a  |  to ]") : group_scope.

Notation "'C_' ( S ) [ a | to ] " := C_(S)([set a] | to)
  (at level 9, format "'C_' ( S ) [ a  |  to ]") : group_scope.

(* For some obscure reason, the Coq pretty-printer doesn't recognize *)
(* this notation. *)
Notation "[ 'acts' ( A | to ) 'on' S ]" := (A \subset N_(|to)(S))
  (at level 0, format "[ 'acts'  ( A  |  to )  'on'  S ]") : form_scope.

Definition act_stable (aT sT : finType) to (S : {set sT}) :=
  forall (a : aT) (x : sT), (to x a \in S) = (x \in S).

Notation "{ 'acts' ( A | to ) 'on' S }" := {in A, act_stable to S}
  (at level 0, format "{ 'acts'  ( A  |  to )  'on'  S }") : form_scope.

Definition quo_act (gT aT : finGroupType) (H : {set gT}) to :=
  fun (Hx : coset H) (a : aT) => insubd Hx (to^~ a @: Hx).

Prenex Implicits quo_act.

Section ExternalAction.

Variables (pi : pred nat) (aT gT : finGroupType) (to : action aT gT).
Variables (A : {group aT}) (G : {group gT}).

Hypothesis morphA : {in A & G &, forall a, {morph to^~ a : x y / x * y}}.

Hypothesis nGA : [acts (A | to) on G].

Hypothesis coGA : coprime #|A| #|G|.

Hypothesis solG : solvable G.

Lemma ext_coprime_hall_exists : 
  exists2 H : {group gT}, hall_for pi G H & [acts (A | to) on H].
Proof.
Admitted.

Lemma ext_coprime_hall_trans : forall H1 H2 : {group gT},
  hall_for pi G H1 -> [acts (A | to) on H1] ->
  hall_for pi G H2 -> [acts (A | to) on H2] ->
  exists2 x, x \in C_(G)(A | to) & H1 = (H2 :^ x)%G.
Proof.
Admitted.

Lemma ext_norm_conj_cent : forall (H : {group gT}) x,
   x \in 'C(A | to) -> [acts (A | to) on H :^ x] = [acts (A | to) on H].
Proof.
Admitted.

Lemma ext_coprime_quotient_cent : forall L : {group gT},
  G <| L -> C_(L)(A | to) / G = C_(L / G)(A | quo_act to).
Proof.
Admitted.

Lemma ext_coprime_hall_subset : forall X : {group gT},
    pi_subgroup pi G X -> A \subset N_(|to)(X) ->
  exists H : {group gT},
    [/\ hall_for pi G H, [acts (A | to) on H] & X \subset H].
Proof.
Admitted.

End ExternalAction.