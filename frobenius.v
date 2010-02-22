(***********************************************************************)
(* (c) Copyright Microsoft Corporation and Inria. All rights reserved. *)
(*                                                                     *)
(***********************************************************************)
(***********************************************************************)
(*                                                                     *)
(*  Frobenius theorem                                                  *)
(*                                                                     *)
(***********************************************************************)
(***********************************************************************)

Require Import ssreflect ssrbool ssrfun ssrnat.
Require Import eqtype fintype div bigops prime finset.
Require Import groups morphisms action normal cyclic center pgroups.

(* Require Import seq paths connect zp. *)

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Import GroupScope.

Definition Ldiv (gT : finGroupType) n := [set z : gT | z ^+ n == 1].

Notation "''Ldiv_' n ()" := (Ldiv _ n)
  (at level 8, n at level 2, format "''Ldiv_' n ()") : group_scope.

Notation "''Ldiv_' n ( G )" := (G :&: 'Ldiv_n())
  (at level 8, n at level 2, format "''Ldiv_' n ( G )") : group_scope.

Theorem Frobenius_Ldiv : forall (gT : finGroupType) (G : {group gT}) n,
  n %| #|G| -> n %| #|'Ldiv_n(G)|.
Proof.
move=> gT G n nG; move: {2}_.+1 (ltnSn (#|G| %/ n)) => mq.
elim: mq => // mq IHm in gT G n nG *; case/dvdnP: nG => q oG.
have [q_gt0 n_gt0] : 0 < q /\ 0 < n by apply/andP; rewrite -muln_gt0 -oG.
rewrite ltnS oG mulnK // => leqm.
have:= q_gt0; rewrite leq_eqVlt; case/predU1P=> [q1 | lt1q].
  rewrite -(mul1n n) q1 -oG (setIidPl _) //.
  by apply/subsetP=> x Gx; rewrite inE -order_dvdn order_dvdG.
pose p := pdiv q; have pr_p: prime p by exact: pdiv_prime.
have lt1p: 1 < p := prime_gt1 pr_p; have p_gt0 := ltnW lt1p.
have{leqm} lt_qp_mq: q %/ p < mq by apply: leq_trans leqm; rewrite ltn_Pdiv.
have: n %| #|'Ldiv_(p * n)(G)|.
  have: p * n %| #|G| by rewrite oG dvdn_pmul2r ?pdiv_dvd.
  move/IHm=> IH; apply: dvdn_trans (IH _); first exact: dvdn_mull.
  by rewrite oG divn_pmul2r.
rewrite -(cardsID 'Ldiv_n()) dvdn_addl.
  rewrite -setIA ['Ldiv_n(_)](setIidPr _) //.
  apply/subsetP=> x; rewrite !inE -!order_dvdn; exact: dvdn_mull.
rewrite setDE -setIA -setDE; set A := _ :\: _.
have pA: forall x, x \in A -> #[x]`_p = (n`_p * p)%N.
  move=> x; rewrite !inE -!order_dvdn; case/andP=> xn xnp.
  rewrite !p_part // -expnSr; congr (p ^ _)%N; apply/eqP.
  rewrite eqn_leq -{1}addn1 -(pfactorK 1 pr_p) -logn_mul ?expn1 // mulnC.
  rewrite dvdn_leq_log ?muln_gt0 ?p_gt0 //= ltnNge; apply: contra xn => xn.
  move: xnp; rewrite -[#[x]](partnC p) //.
  rewrite !gauss_inv ?coprime_partC //; case/andP=> _.
  rewrite p_part ?pfactor_dvdn // xn gauss // coprime_sym.
  exact: pnat_coprime (pnat_id _) (part_pnat _ _).
rewrite -(partnC p n_gt0) gauss_inv ?coprime_partC //; apply/andP; split.
  rewrite -sum1_card (partition_big_imset (@cycle _)) /=.
  apply: dvdn_sum => X; case/imsetP=> x; case/setIP=> Gx Ax ->{X}.
  rewrite (eq_bigl (generator <[x]>)) => [|y].
    rewrite sum1dep_card -phi_gen -[#[x]](partnC p) //.
    rewrite phi_coprime ?coprime_partC // dvdn_mulr // .
    by rewrite (pA x Ax) p_part // -expnSr phi_pfactor // dvdn_mull.
  rewrite /generator eq_sym andbC; case xy: {+}(_ == _) => //.
  rewrite !inE -!order_dvdn in Ax *.
  by rewrite -cycle_subG /order -(eqP xy) cycle_subG Gx.
rewrite -sum1_card (partition_big_imset (fun x => x.`_p ^: G)) /=.
apply: dvdn_sum => X; case/imsetP=> x; case/setIP=> Gx Ax ->{X}.
set y := x.`_p; have oy: #[y] = (n`_p * p)%N by rewrite order_constt pA.
rewrite (partition_big (fun x => x.`_p) (mem (y ^: G))) /= => [|z]; last first.
  by case/andP=> _; move/eqP <-; rewrite /= class_refl.
pose G' := ('C_G[y] / <[y]>)%G; pose n' := gcdn #|G'| n`_p^'.
have n'_gt0: 0 < n' by rewrite gcdn_gt0 cardG_gt0.
rewrite (eq_bigr (fun _ => #|'Ldiv_n'(G')|)) => [|ya].
  rewrite sum_nat_const -index_cent1 indexgI.
  rewrite -(dvdn_pmul2l (cardG_gt0 'C_G[y])) mulnA LaGrangeI.
  have oCy: #|'C_G[y]| = (#[y] * #|G'|)%N.
    rewrite card_quotient ?subcent1_cycle_norm // LaGrange //.
    by rewrite subcent1_cycle_sub ?groupX.
  rewrite oCy -mulnA -(muln_lcm_gcd #|G'|) -/n' mulnA dvdn_mul //.
    rewrite muln_lcmr -oCy order_constt pA // mulnAC partnC // dvdn_lcm.
    by rewrite cardSg ?subsetIl // mulnC oG dvdn_pmul2r ?pdiv_dvd.
  apply: IHm; [exact: dvdn_gcdl | apply: leq_ltn_trans lt_qp_mq].
  rewrite -(@divn_pmul2r n`_p^') // -muln_lcm_gcd mulnC divn_pmul2l //.
  rewrite leq_divr // divn_mulAC ?leq_divl ?dvdn_mulr ?dvdn_lcmr //.
  rewrite dvdn_leq ?muln_gt0 ?q_gt0 //= mulnC muln_lcmr dvdn_lcm.
  rewrite -(@dvdn_pmul2l n`_p) // mulnA -oy -oCy mulnCA partnC // -oG.
  by rewrite cardSg ?subsetIl // dvdn_mul ?pdiv_dvd.
case/imsetP=> a Ga ->{ya}.
pose h := [fun z => coset <[y]> (z ^ a^-1)].
pose h' := [fun Z : coset_of <[y]> => (y * (repr Z).`_p^') ^ a].
rewrite -sum1_card (reindex_onto h h') /= => [|Z]; last first.
  rewrite conjgK coset_kerl ?cycle_id ?morph_constt ?repr_coset_norm //.
  rewrite /= coset_reprK 2!inE -order_dvdn dvdn_gcd; case/and3P=> _ _ p'Z.
  apply: constt_p_elt (pnat_dvd p'Z _); exact: part_pnat.
apply: eq_bigl => z; apply/andP/andP=> [[]|[]].
  rewrite inE -andbA; case/and3P=> Gz Az _; move/eqP=> zp_ya.
  have czy: z ^ a^-1 \in 'C[y].
    rewrite -mem_conjg -normJ conjg_set1 -zp_ya.
    by apply/cent1P; exact: commuteX.
  have Nz:  z ^ a^-1 \in 'N(<[y]>) by apply: subsetP czy; exact: norm_gen.
  have G'z: h z \in G' by rewrite mem_morphim //= inE groupJ // groupV.
  rewrite inE G'z inE -order_dvdn dvdn_gcd order_dvdG //=.
  rewrite /order -morphim_cycle // -quotientE card_quotient ?cycle_subG //.
  rewrite -(@dvdn_pmul2l #[y]) // LaGrange; last first.
    by rewrite /= cycleJ cycle_subG mem_conjgV -zp_ya mem_cycle.
  rewrite oy mulnAC partnC // [#|_|]orderJ; split.
    by rewrite !inE -!order_dvdn mulnC in Az; case/andP: Az.
  set Z := coset _ _; have NZ := repr_coset_norm Z; have:= coset_reprK Z.
  case/kercoset_rcoset=> {NZ}// yi; case/cycleP=> i -> -> {yi Z}.
  rewrite consttM; last by apply commute_sym; apply: commuteX; apply/cent1P.
  rewrite (constt1P _) ?p_eltNK 1?p_eltX ?p_elt_constt // mul1g.
  by rewrite conjMg consttJ conjgKV -zp_ya consttC.
rewrite 2!inE -order_dvdn; set Z := coset _ _.
case/andP=> Cz n'Z; move/eqP=> def_z.
have Nz: z ^ a^-1 \in 'N(<[y]>).
  rewrite -def_z conjgK groupMr; first by rewrite -(cycle_subG y) normG.
  by rewrite groupX ?repr_coset_norm.
have{Cz}: z ^ a^-1 \in 'C_G[y]; last case/setIP=> Gz Cz.
  case/morphimP: Cz => u Nu Cu.
  case/kercoset_rcoset=> // yi; case/cycleP=> i ->{yi} ->.
  by rewrite groupMr // groupX // inE groupX //; exact/cent1P.
have{def_z} zp_ya: z.`_p = y ^ a.
  rewrite -def_z consttJ consttM.
    rewrite constt_p_elt ?p_elt_constt //.
    by rewrite (constt1P _) ?p_eltNK ?p_elt_constt ?mulg1.
  apply: commute_sym; apply/cent1P.
  rewrite -def_z conjgK groupMl // in Cz; exact/cent1P.
have ozp: #[z ^ a^-1]`_p = #[y].
  by rewrite -order_constt consttJ zp_ya conjgK.
split; rewrite zp_ya // -class_lcoset lcoset_id // eqxx andbT.
rewrite -(conjgKV a z) !inE groupJ //= -!order_dvdn orderJ; apply/andP; split.
  apply/negP; move/(partn_dvd p n_gt0); apply/negP.
  by rewrite ozp -(muln1 n`_p) oy dvdn_pmul2l // dvdn1 neq_ltn lt1p orbT.
rewrite -(partnC p n_gt0) mulnCA mulnA -oy -(@partnC p #[_]) // ozp.
apply dvdn_mul => //; apply: dvdn_trans (dvdn_trans n'Z (dvdn_gcdr _ _)).
rewrite {2}/order -morphim_cycle // -quotientE card_quotient ?cycle_subG //.
rewrite -(@dvdn_pmul2l #|<[z ^ a^-1]> :&: <[y]>|) ?cardG_gt0 // LaGrangeI.
rewrite -[#|<[_]>|](partnC p) ?order_gt0 // dvdn_pmul2r // ozp.
by rewrite cardSg ?subsetIr.
Qed.
