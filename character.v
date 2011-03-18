(* (c) Copyright Microsoft Corporation and Inria. All rights reserved. *)
Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq path div choice.
Require Import fintype tuple finfun bigop prime ssralg poly finset.
Require Import fingroup morphism perm automorphism quotient finalg action.
Require Import zmodp commutator cyclic center pgroup sylow matrix mxalgebra.
Require Import mxpoly mxrepresentation vector algC.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GroupScope GRing.Theory.
Local Open Scope ring_scope.

(**************************************************************************)
(*                                                                        *)
(* This file contains the basic notions of character theory               *)
(*                                                                        *)
(*  cfun gT R : the type of functions from gT to R                        *)
(*                                                                        *)
(*  (f ^* )%CH  : the conjugate function                                  *)
(*                                                                        *)
(*  'CF[R](G,A) : the vector space of class functions of G with support   *)
(*                in A                                                    *)
(*  'CF(G,A)    : the vector space of class functions of G with support   *)
(*                in A over algC                                          *)
(*  'CF(R)      : the vector space of class functions of G over R         *)
(*  'CF(G)      : the vector space of class functions of G over algC      *)
(*                                                                        *)
(*  irr G : irreducible character of G                                    *)
(*                                                                        *)
(*  is_irr G f :  predicates that tells if the function f is a character  *)
(*                                                                        *)
(*  get_irr G f : if is_irr G f is true returns the corresponding         *)
(*                 irreducible character                                  *)
(*                                                                        *)
(*  char_of_repr G rG : turn the representation rG into a character       *)
(*                                                                        *)
(*  is_char G f : predicates that tells if the function f is a character  *)
(*                                                                        *)
(*  get_char G f : if is_irr G f is true returns the corresponding        *)
(*                 character                                              *)
(*                                                                        *)
(*  '[f,g]_G : the inner product of f g such that irr G is                *)
(*                     an orthonormal basis of 'CF(G)                     *)
(*                                                                        *)
(*  cker G f : the kernel of G i.e g \in G such that f g = f 1            *)
(*                                                                        *)
(*   (f/N)%CH  :        if f is a character G, it returns the isomorphic  *)
(*                      character in G/N                                  *)
(*  (f^())%CH  : if f is a character G/N, returns the isomorphic          *)
(*                      character in G                                    *)
(*                                                                        *)
(* is_comp i f : the irreducible character i is a constituent of f        *)
(*                                                                        *)
(* 'Res[H] f: restrict the function to H, i.e f x = 0 for x \notin H      *)
(*                                                                        *)
(* 'Ind[G,H] f: the induced function from H to G                          *)
(*                                                                        *)
(* ccenter G f: the center i.e g \in G such that |f g| = f 1              *)
(*                                                                        *)
(* cfaithful G f: the class function f is faithfull, i.e its center       *)
(*                 is trivial                                             *)
(*                                                                        *)
(**************************************************************************)

(**
 This should be moved to matrix.v
**)

Lemma cofactor_mxZ : forall (R : comRingType) (n : nat) (A : 'M[R]_n) a i j, 
 cofactor (a *: A) i j = a^+n.-1 * cofactor A i j.
Proof.
move=> R n A a i j; rewrite !expand_cofactor.
rewrite -mulr_sumr; apply: eq_bigr=> k Hk.
rewrite [a^+_ * _]mulrC -mulrA; congr (_ * _).
suff->: a ^+ n.-1 = \prod_(k0 | i != k0) a.
  by rewrite -big_split; apply: eq_bigr=> i1 _; rewrite !mxE mulrC.
rewrite prodr_const; congr (_ ^+ _).
rewrite -{1}[n]card_ord -(cardsC1 i); apply: eq_card=> m.
by rewrite !inE /in_mem /= eq_sym; case: (i == m).
Qed.

Lemma adj1 : forall (R : comRingType) (n : nat), \adj (1%:M) = 1%:M :> 'M[R]_n.
Proof.
by move=> R n; rewrite -{2}(det1 R n) -mul_adj_mx mulmx1.
Qed.

Lemma adj_mxZ : forall (R : comRingType) (n : nat) (A : 'M[R]_n) a, 
 \adj (a *: A) = a^+n.-1 *: \adj A.
Proof.
by move=> R n A a; apply/matrixP=> i j; rewrite !mxE cofactor_mxZ.
Qed.

Lemma unitmxZ : forall (R : comUnitRingType) n (A : 'M[R]_n) a,
  GRing.unit a -> (a *: A) \in unitmx = (A \in unitmx).
Proof.
move=> R n A a Ha.
rewrite !unitmxE det_scalemx commr_unit_mul ?unitr_exp //.
exact: mulrC.
Qed.

Lemma invmxZ : forall (R : fieldType) (n : nat) (A : 'M[R]_n) a, 
 A \in unitmx -> invmx (a *: A) = a^-1 *: invmx A.
Proof.
move=> R [|n] A a HA; first by rewrite !(flatmx0 (_ *: _)); exact: flatmx0.
case: (a =P 0)=> [->|].
  by rewrite invr0 !scale0r /invmx det0 invr0 scale0r if_same.
move/eqP=> Ha.
have Ua: GRing.unit a by by rewrite unitfE.
have Uan: GRing.unit (a^+n) by rewrite unitr_exp.
have Uan1: GRing.unit (a^+n.+1) by rewrite unitr_exp.
rewrite /invmx det_scalemx adj_mxZ unitmxZ // HA !scalerA invr_mul //.
congr (_ *: _); rewrite -mulrA mulrC; congr (_ / _).
by rewrite mulrC exprS invr_mul // mulrA divrr // mul1r.
Qed.

Lemma invmx1 : forall (R : fieldType) (n : nat), invmx 1%:M = 1%:M :> 'M[R]_n.
Proof.
by move=> R n; rewrite /invmx det1 invr1 scale1r adj1 if_same.
Qed.

Lemma invmx_scalar :
 forall (R : fieldType) (n : nat) (a: R), invmx (a%:M) = a^-1%:M :> 'M[R]_n.
Proof.
by move=> R n a; rewrite -scalemx1 invmxZ ?unitmx1 // invmx1 scalemx1.
Qed.

Lemma scalar_exp :
 forall (R : ringType) (m n : nat) (a: R), 
 (a^+m)%:M = a%:M^+ m :> 'M_n.+1.
Proof.
move=> R m n a; elim: m=> [|m IH]; first by rewrite !expr0.
by rewrite !exprS scalar_mxM IH.
Qed.

Lemma row_is_linear : 
  forall (R: ringType) m n (i : 'I_m), linear (@row R m n i).
Proof.
by move=> R m n i k A B; apply/matrixP=> x y; rewrite !mxE.
Qed.

Canonical Structure row_linear R m n i := Linear (@row_is_linear R m n i).

Lemma gring_row_is_linear : 
  forall (R: comUnitRingType) gT G, linear (@gring_row R gT G).
Proof. move=> *; exact: row_is_linear. Qed.

Canonical Structure gring_row_linear R gT G := 
  Linear (@gring_row_is_linear R gT G).

(* This should be put in mxrepresentation *)

Section MxR.

Variables (R : fieldType) (gT : finGroupType) (G : {group gT}).

Lemma mx_rsim_scalar : 
  forall m n 
   (rG1 : mx_representation R G m) (rG2 : mx_representation R G n) g c,
   g \in G -> mx_rsim rG1 rG2 -> rG1 g = c%:M -> rG2 g = c%:M.
Proof.
move=> m n rG1 rG2 g c InG HR.
move/mx_rsim_sym: (HR); case/mx_rsim_def=> B1 [B2 HH].
move/(_ _ InG)=> -> ->; rewrite scalar_mxC -mulmxA.
suff->: B1 *m B2 = 1%:M by rewrite mulmx1.
by move: B1 B2 HH; rewrite (mxrank_rsim HR); move=> *; exact: mulmx1C.
Qed.

Record representation :=
  Representation {rdegree; mx_repr_of_repr :> mx_representation R G rdegree}.

Lemma mx_repr0 : mx_repr G (fun _ : gT => 1%:M : 'M[R]_0).
Proof. by split=> // g h Hg Hx; rewrite mulmx1. Qed.

Definition grepr0 := Representation (MxRepresentation mx_repr0).

Lemma add_mx_repr : forall rG1 rG2 : representation,
  mx_repr G (fun g => block_mx (rG1 g) 0 0 (rG2 g)).
Proof.
move=> rG1 rG2; split=> [|x y Hx Hy].
  by rewrite !repr_mx1 -scalar_mx_block.
by rewrite mulmx_block !(mulmx0, mul0mx, addr0, add0r, repr_mxM).
Qed.

Definition dadd_grepr rG1 rG2 :=
  Representation (MxRepresentation (add_mx_repr rG1 rG2)).

Section DsumRepr.

Variables (n : nat) (rG : mx_representation R G n).

Lemma mx_rsim_dadd : forall (U V W : 'M_n) (rU rV : representation),
  forall (modU : mxmodule rG U) (modV : mxmodule rG V) (modW : mxmodule rG W),
    (U + V :=: W)%MS -> mxdirect (U + V) ->
    mx_rsim (submod_repr modU) rU -> mx_rsim (submod_repr modV) rV ->
  mx_rsim (submod_repr modW) (dadd_grepr rU rV).
Proof.
move=> U V W [nU rU] [nV rV] modU modV modW defW dxUV /=.
have tiUV := mxdirect_addsP dxUV.
move=> [fU def_nU]; rewrite -{nU}def_nU in rU fU * => inv_fU hom_fU.
move=> [fV def_nV]; rewrite -{nV}def_nV in rV fV * => inv_fV hom_fV.
pose pU := in_submod U (proj_mx U V) *m fU.
pose pV := in_submod V (proj_mx V U) *m fV.
exists (val_submod 1%:M *m row_mx pU pV) => [||g Gg].
- by rewrite -defW (mxdirectP dxUV).
- apply/row_freeP.
  pose pU' := invmx fU *m val_submod 1%:M.
  pose pV' := invmx fV *m val_submod 1%:M.
  exists (in_submod _ (col_mx pU' pV')).
  rewrite in_submodE mulmxA -in_submodE -mulmxA mul_row_col mulmx_addr.
  rewrite -[pU *m _]mulmxA -[pV *m _]mulmxA !mulKVmx -?row_free_unit //.
  rewrite addrC (in_submodE V) 2![val_submod 1%:M *m _]mulmxA -in_submodE.
  rewrite addrC (in_submodE U) 2![val_submod 1%:M *m _]mulmxA -in_submodE.
  rewrite -!val_submodE !in_submodK ?proj_mx_sub //.
  by rewrite add_proj_mx ?val_submodK // val_submod1 defW.
rewrite mulmxA -val_submodE -[submod_repr _ g]mul1mx val_submodJ //.
rewrite -(mulmxA _ (rG g)) mul_mx_row -mulmxA mul_row_block !mulmx0 addr0 add0r.
rewrite !mul_mx_row; set W' := val_submod 1%:M; congr (row_mx _ _).
  rewrite 3!mulmxA in_submodE mulmxA.
  have hom_pU: (W' <= dom_hom_mx rG (proj_mx U V))%MS.
    by rewrite val_submod1 -defW proj_mx_hom.
  rewrite (hom_mxP hom_pU) // -in_submodE (in_submodJ modU) ?proj_mx_sub //.
  rewrite -(mulmxA _ _ fU) hom_fU // in_submodE -2!(mulmxA W') -in_submodE.
  by rewrite -mulmxA (mulmxA _ fU).
rewrite 3!mulmxA in_submodE mulmxA.
have hom_pV: (W' <= dom_hom_mx rG (proj_mx V U))%MS.
  by rewrite val_submod1 -defW addsmxC proj_mx_hom // capmxC.
rewrite (hom_mxP hom_pV) // -in_submodE (in_submodJ modV) ?proj_mx_sub //.
rewrite -(mulmxA _ _ fV) hom_fV // in_submodE -2!(mulmxA W') -in_submodE.
by rewrite -mulmxA (mulmxA _ fV).
Qed.

Lemma mx_rsim_dsum : forall (I : finType) (P : pred I) U rU (W : 'M_n),
  forall (modU : forall i, mxmodule rG (U i)) (modW : mxmodule rG W),
    let S := (\sum_(i | P i) U i)%MS in (S :=: W)%MS -> mxdirect S -> 
    (forall i, mx_rsim (submod_repr (modU i)) (rU i : representation)) ->
  mx_rsim (submod_repr modW) (\big[dadd_grepr/grepr0]_(i | P i) rU i).
Proof.
move=> I P U rU W modU modW /= defW dxW rsimU.
rewrite mxdirectE /= -!(big_filter _ P) in dxW defW *.
elim: {P}(filter P _) => [|i e IHe] in W modW dxW defW *.
  rewrite !big_nil /= in defW *.
  by exists 0 => [||? _]; rewrite ?mul0mx ?mulmx0 // /row_free -defW !mxrank0.
rewrite !big_cons /= in dxW defW *.
rewrite 2!(big_nth i) !big_mkord /= in IHe dxW defW.
set Wi := (\sum_i _)%MS in defW dxW IHe.
rewrite -mxdirectE mxdirect_addsE !mxdirectE eqxx /= -/Wi in dxW.
have modWi: mxmodule rG Wi by exact: sumsmx_module.
case/andP: dxW; move/(IHe Wi modWi) {IHe}; move/(_ (eqmx_refl _))=> rsimWi.
by move/eqP; move/mxdirect_addsP=> dxUiWi; exact: mx_rsim_dadd (rsimU i) rsimWi.
Qed.

Definition n_grepr rW k := \big[dadd_grepr/grepr0]_(i < k) rW.

Lemma mx_rsim_socle : forall (sG : socleType rG) (W : sG) (rW : representation),
    let modW : mxmodule rG W := component_mx_module rG (socle_base W) in
    mx_rsim (socle_repr W) rW ->
  mx_rsim (submod_repr modW) (n_grepr rW (socle_mult W)).
Proof.
move=> sG W rW; set M := socle_base W => modW rsimM.
have simM: mxsimple rG M := socle_simple W.
have rankM_gt0: \rank M > 0 by rewrite lt0n mxrank_eq0; case: simM.
have [I /= U_I simU]: mxsemisimple rG W by exact: component_mx_semisimple.
pose U (i : 'I_#|I|) := U_I (enum_val i).
have reindexI := reindex _ (onW_bij I (enum_val_bij I)).
rewrite mxdirectE /= !reindexI -mxdirectE /= => defW dxW.
have isoU: forall i, mx_iso rG M (U i).
  move=> i; have sUiW: (U i <= W)%MS  by rewrite -defW (sumsmx_sup i).
  exact: component_mx_iso (simU _) sUiW.
have ->: socle_mult W = #|I|.
  rewrite -(mulnK #|I| rankM_gt0); congr (_ %/ _)%N.
  rewrite -defW (mxdirectP dxW) /= -sum_nat_const reindexI /=.
  by apply: eq_bigr => i _; rewrite -(mxrank_iso (isoU i)).
have modU: mxmodule rG (U _) := mxsimple_module (simU _).
suff: mx_rsim (submod_repr (modU _)) rW by exact: mx_rsim_dsum defW dxW.
by move=> i; apply: mx_rsim_trans (mx_rsim_sym _) rsimM; exact/mx_rsim_iso.
Qed.

End DsumRepr.

Section CosetRepr.

Variable (N : {group gT}) (n : nat) (rG : mx_representation R (G / N)%g n).
Hypothesis nsNG: N <| G.
Let nNG : G \subset 'N(N) := normal_norm nsNG.

Definition coset_mx := morphim_mx rG nNG.
Canonical Structure coset_repr :=
  MxRepresentation (morphim_mx_repr rG nNG : mx_repr G coset_mx).

Local Notation rGH := coset_repr.

Lemma coset_repr_coset : forall x, x \in G -> rG (coset N x) = rGH x.
Proof. by []. Qed.

Lemma coset_repr_rker : N \subset rker rGH.
Proof. by rewrite rker_morphim subsetI sub_cosetpre normal_sub. Qed.

Lemma rsim_quo_coset : mx_rsim (quo_repr coset_repr_rker nNG) rG.
Proof.
exists 1%:M => // [|Nx]; first by rewrite row_free_unit unitmx1.
by case/morphimP=> x nNx Gx ->{Nx}; rewrite mul1mx mulmx1 quo_repr_coset.
Qed.

End CosetRepr.

End MxR.

Implicit Arguments grepr0 [R gT G].
Prenex Implicits grepr0 dadd_grepr.

(* Move to fingroup and should replace card_classes_abelian in action *)
(* GG: can't move to fingroup, because sum_card_class is in action. *)
Lemma card_classes_abelian : forall (gT : finGroupType) (G : {group gT}), 
  abelian G = (#|classes G| == #|G|).
Proof.
move=> gT G.
have F : reflect (forall i, i \in classes G -> #|i| = 1%N) (abelian G).
  apply(iffP idP)=> [HH i| HH].
    case/imsetP=> g InG ->; apply/eqP; apply/cards1P; exists g.
    by apply/cent_classP; move/subsetP: HH->.
  apply/subsetP=> g InG; apply/centP=> h InH.
  move/eqP: (HH _ (mem_classes InG)); case/cards1P=> l H.
  have: g \in g ^: G by exact: class_refl.
  have: g ^ h \in g ^: G by exact: memJ_class.
  rewrite H !inE; move/eqP=> H1; move/eqP=> H2.
  by rewrite /commute {2}H2 -H1 mulgA mulgV mul1g.
rewrite -sum_card_class; apply/idP/idP=>[|HH].
  by move/F=> HH; rewrite (eq_bigr (fun _ => 1%N)) // sum_nat_const muln1.
have F1: forall g, g \in G -> (0 < #|g ^: G|)%N.
  by move=> g InG; rewrite (cardD1 g) class_refl.
apply/F=> i; case/imsetP=> g InG ->; move: HH.
rewrite (eq_bigr (fun  C : {set gT}  => #|C|.-1 + 1))%N; last first.
  by move=> C; case/imsetP=> h InH->; rewrite addn1 prednK // F1.
rewrite big_split sum_nat_const //= muln1 -{1}[#|_|]add0n eqn_addr.
rewrite eq_sym sum_nat_eq0.
move/forallP; move/(_ (g ^: G)); move/implyP; move/(_ (mem_classes InG)).
by case: #|_| (F1 _ InG)=> // [] [].
Qed.

Lemma class_inv: forall (gT : finGroupType) (G : {group gT}) g,
  (g ^: G)^-1%g = g^-1 ^: G.
Proof.
move=> gT G g; apply/setP=> h; rewrite inE.
apply/imsetP/imsetP; case=> l LiG H.
  by exists l=> //; rewrite conjVg -H invgK.
by exists l=> //; rewrite H conjVg invgK.
Qed.

Section AlgC.

Variable (gT : finGroupType).

Lemma groupC : group_closure_field algC gT.
Proof. exact: group_closure_closed_field. Qed.

Lemma neq0GC : forall  (G : {group gT}), (#|G|)%:R != 0 :> algC.
Proof. by move=> G; rewrite -neq0N_neqC (cardD1 1%g) group1. Qed.

Lemma sposGC : forall (G : {group gT}), 0 < #|G|%:R.
Proof. by move=> G; rewrite /ltC neq0GC // posC_nat. Qed.

Implicit Type G : {group gT}.
Import GroupScope GRing.Theory.

Lemma pGroupG : forall G, [char algC]^'.-group G.
Proof.
by move=> G; apply: sub_pgroup (pgroup_pi G)=> i _; rewrite inE /= Cchar.
Qed.

End AlgC.

(****************************************************************************)
(*  trying to do something about characters                                 *)
(****************************************************************************)

Delimit Scope character_scope with CH.

(* function of a fintype into a ring form a vectype *)
Section Vectype.

Variable (R : fieldType) (aT : finType).

Definition ffun2rv (f : {ffun aT -> R^o}) :=  \row_(i < #|aT|) f (enum_val i).

Lemma ffun2rv_is_linear : linear ffun2rv.
Proof. by move=> k /= x y; apply/rowP=> i; rewrite !mxE !ffunE. Qed.

Canonical Structure ffun2rv_linear := Linear ffun2rv_is_linear.

Lemma ffun2rv_bij : bijective ffun2rv.
Proof.
exists (fun r : 'rV_#|aT| => [ffun x => r 0 (enum_rank x)]) => [g | r].
  by apply/ffunP=> x; rewrite ffunE mxE enum_rankK.
by apply/rowP=> i; rewrite mxE ffunE enum_valK.
Qed.

Definition ffunVectMixin := VectMixin ffun2rv_is_linear ffun2rv_bij.
Canonical Structure ffunVectType := VectType R ffunVectMixin.

End Vectype.

Local Notation "{ 'vffun' x '->' y }" := (ffunVectType y x)
  (at level 0, format "{ 'vffun'  '[hv' x  '->'  y ']' }") : type_scope.

Section ClassFun.

Variable (gT : finGroupType) (R : fieldType) (G : {group gT}).

Inductive cfun : predArgType := ClassFun of {ffun gT -> R}.

Definition finfun_of_cfun A := let: ClassFun f := A in f.
Definition fun_of_cfun f x := finfun_of_cfun f x.
Coercion fun_of_cfun : cfun >-> Funclass.

Lemma finfun_of_cfunE: forall f x, finfun_of_cfun f x  = f x.
Proof. by []. Qed.

Definition cfun_of_fun f := locked ClassFun [ffun x => f x].

Lemma cfunE : forall f, cfun_of_fun f =1 f.
Proof. by unlock cfun_of_fun fun_of_cfun => f x; rewrite /= ffunE. Qed.

Lemma cfunP : forall (f1 f2 : cfun), f1 =1 f2 <-> f1 = f2.
Proof.
move=> [f1] [f2]; split=> [/= eqf1f2 | -> //].
congr ClassFun; apply/ffunP=> i; exact: eqf1f2.
Qed.

Canonical Structure cfun_subType :=
  Eval hnf in [newType for finfun_of_cfun by cfun_rect].
Definition cfun_eqMixin := Eval hnf in [eqMixin of cfun by <:].
Canonical Structure cfun_eqType := 
  Eval hnf in EqType cfun cfun_eqMixin.
Definition cfun_choiceMixin := [choiceMixin of cfun by <:].
Canonical Structure cfun_choiceType :=
  Eval hnf in ChoiceType cfun cfun_choiceMixin.

Definition cfun_zero := cfun_of_fun (fun _ => 0).
Definition cfun_one := cfun_of_fun (fun _ => 1).
Definition cfun_opp (f : cfun) := cfun_of_fun (fun x => - f x).
Definition cfun_add (f g : cfun) := cfun_of_fun (fun x => f x + g x). 
Definition cfun_mul (f g : cfun) := cfun_of_fun (fun x => f x * g x). 

Fact cfun_addA : associative cfun_add.
Proof. by move=> f1 f2 f3; apply/cfunP=> i; rewrite !cfunE addrA. Qed.
Fact cfun_addC : commutative cfun_add.
Proof. by move=> f1 f2; apply/cfunP=> i; rewrite !cfunE addrC. Qed.
Fact cfun_add0 : left_id cfun_zero cfun_add.
Proof. by move=> f; apply/cfunP=> i; rewrite !cfunE add0r. Qed.
Fact cfun_addN : left_inverse cfun_zero cfun_opp cfun_add.
Proof. by move=> f; apply/cfunP=> i; rewrite !cfunE addNr. Qed.

Definition cfun_zmodMixin :=
  GRing.Zmodule.Mixin cfun_addA cfun_addC cfun_add0 cfun_addN.
Canonical Structure cfun_zmodType :=
  Eval hnf in ZmodType _ cfun_zmodMixin.

Fact cfun_mulA : associative cfun_mul.
Proof. by move=> f1 f2 f3; apply/cfunP=> i; rewrite !cfunE mulrA. Qed.
Fact cfun_mulC : commutative cfun_mul.
Proof. by move=> f1 f2; apply/cfunP=> i; rewrite !cfunE mulrC. Qed.
Fact cfun_1l : left_id cfun_one cfun_mul.
Proof. by move=> f; apply/cfunP=> i; rewrite !cfunE mul1r. Qed.
Fact cfun_mul_addl :  left_distributive cfun_mul cfun_add.
Proof. by move=> f1 f2 f3; apply/cfunP=> i; rewrite !cfunE mulr_addl. Qed.
Fact cfun1_nonzero :  cfun_one != 0.
Proof. 
apply/eqP; move/cfunP; move/(_ 1%g); rewrite !cfunE.
by move/eqP; rewrite oner_eq0.
Qed.

Definition cfun_ringMixin := 
  ComRingMixin cfun_mulA cfun_mulC cfun_1l cfun_mul_addl cfun1_nonzero.
Canonical Structure cfun_ringType := Eval hnf in RingType cfun cfun_ringMixin.
Canonical Structure cfun_comRingType := Eval hnf in ComRingType cfun cfun_mulC.

Definition cfun_scale k (f : cfun) :=  cfun_of_fun (fun x => k * f x).

Fact cfun_scaleA : forall k1 k2 f, 
  cfun_scale k1 (cfun_scale k2 f) = cfun_scale (k1 * k2) f.
Proof. by move=> k1 k2 f; apply/cfunP=> i; rewrite !cfunE mulrA. Qed.
Fact cfun_scale1 : left_id 1 cfun_scale.
Proof. by move=> f; apply/cfunP=> i; rewrite !cfunE mul1r. Qed.
Fact cfun_scale_addr : forall k, {morph (cfun_scale k) : x y / x + y}.
Proof. by move=> k f g; apply/cfunP=> i; rewrite !cfunE mulr_addr. Qed.
Fact cfun_scale_addl : forall u, {morph (cfun_scale)^~ u : k1 k2 / k1 + k2}.
Proof. by move=> k f g; apply/cfunP=> i; rewrite !cfunE mulr_addl. Qed.

Definition cfun_lmodMixin := 
  LmodMixin cfun_scaleA cfun_scale1 cfun_scale_addr cfun_scale_addl.
Canonical Structure cfun_lmodType :=
  Eval hnf in LmodType R cfun cfun_lmodMixin.

Lemma sum_cfunE:  
  forall I (r : seq I) (P : pred I) (F : I -> cfun),
  \big[+%R/0]_(i <- r | P i) F i = 
     cfun_of_fun (fun x => \big[+%R/0]_(i <- r | P i) (F i x)).
Proof.
move=> i r P F1; elim: r=> [|y r Hrec].
  by rewrite !big_nil; apply/cfunP=> j; rewrite !cfunE big_nil.
by rewrite big_cons Hrec; case F2: (P _); apply/cfunP=> x;
   rewrite !cfunE big_cons F2.
Qed.

Lemma cfunMn : forall (f : cfun) n x, (f *+ n) x = f x *+ n.
Proof.
by move=> f n x; elim: n => [|n IHn]; rewrite ?mulrS !cfunE -?IHn //. 
Qed.

(* GG: this should either go in finfun, or be replaced with *)
(* pffun_on 0 A predT (val f) *)
Definition has_support (f : cfun) (A : {set gT}) :=
  forallb x: gT, (f x != 0) ==> (x \in A).

Definition base_cfun (G A : {set gT}) : seq cfun :=
  filter
    (has_support^~ A)
    (map (fun i : 'I_#|classes G|  => 
        cfun_of_fun (fun x => (x \in (enum_val i))%:R))
      (enum 'I_#|classes G|)).

Lemma base_cfun_subset : forall (A : {set gT}),
 G \subset A -> 
 base_cfun G A = (map (fun i : 'I_#|classes G|  => 
                   cfun_of_fun (fun x => (x \in (enum_val i))%:R))
                   (enum 'I_#|classes G|)).
Proof.
move=> A GsA; apply/all_filterP.
apply/allP=> /= f; case/mapP=> i Hi ->.
apply/forall_inP=> x; rewrite cfunE.
case: (boolP (_ \in _))=> Hxi HH; last by case/eqP: HH.
apply: (subsetP GsA).
suff: (enum_val i) \subset G by move/subsetP; apply.
case/imsetP: (enum_valP i)=> g GiG ->.
by apply: class_subG.
Qed.
 
Definition cfun2rv f := ffun2rv (finfun_of_cfun f).

Lemma cfun2rv_is_linear : linear cfun2rv.
Proof. 
move=> k x y; rewrite -linearP; congr ffun2rv.
by apply/ffunP=> i; rewrite !ffunE !finfun_of_cfunE !cfunE.
Qed.

Canonical Structure cfun2rv_linear := Linear cfun2rv_is_linear.

Lemma cfun2rv_bij : bijective cfun2rv.
Proof.
have [f H1f H2f] := ffun2rv_bij R gT.
exists (fun x  => ClassFun (f x))=> [[g]|x]; last exact: (H2f x).
by congr ClassFun; exact: (H1f g).
Qed.

Definition cfunVectMixin := VectMixin cfun2rv_is_linear cfun2rv_bij.
Canonical Structure cfunVectType := VectType R cfunVectMixin.

Definition class_fun G  A := span (base_cfun G A).

Local Notation "'CF( G , A )" := (class_fun G A).
Local Notation "'CF( G )" := (class_fun G G).

Lemma cfun_memfP : forall (A : {set gT}) (f : cfun),
  reflect 
    (   (forall x, x \notin (A :&: G) -> f x = 0) 
     /\ 
        (forall x y, x \in G -> y \in G -> f (x ^ y) = f x)
    )
    (f \in 'CF(G, A)).
Proof.
move=> A f; pose bGA := base_cfun G A.
apply: (iffP idP)=> [|[Hg Hc]].
  move/coord_span->; split=> [x XniAG|x y XiG YiG].
    rewrite sum_cfunE cfunE; apply: big1=> i _; rewrite !cfunE.
    have: bGA`_i \in bGA by apply: mem_nth.
    rewrite mem_filter; case/andP=> Hs.
    move: XniAG; rewrite inE negb_andb; case/orP=> [XniA|XniG].
      move/forallP: Hs; move/(_ x).
      by rewrite (negPf XniA) implybF negbK; move/eqP->; rewrite mulr0.
    case/mapP=> j Hj ->; rewrite !cfunE.
    have [y Gy ->] := imsetP (enum_valP j).
    move/subsetP: (class_subG Gy (subxx _)); move/(_ x); move/contra.
    by move/(_ XniG); case: (_ \in _)=> //; rewrite mulr0.
  apply/eqP; rewrite -subr_eq0; apply/eqP.
  rewrite !sum_cfunE !cfunE -sumr_sub; apply: big1=> i _.
  set u := coord _ _ _; rewrite !cfunE.
  have: bGA`_i \in bGA by apply: mem_nth.
  rewrite mem_filter; case/andP=> Hs.
  case/mapP=> j Hj ->; rewrite !cfunE.
  have [z Gz ->] := imsetP (enum_valP j).
  by rewrite (class_transl _ (memJ_class _ _)) // subrr.
suff<-: \sum_(C \in (classes G)) 
           (f (repr C)) *: cfun_of_fun (fun x => (x \in C)%:R) = f.
  apply: memv_suml=> i Hi.
  case: (boolP (f (repr i) == 0))=> [|Hr].
    by move/eqP->; rewrite scale0r mem0v.
  apply: memvZl; apply: memv_span.
  rewrite mem_filter; apply/andP; split.
    apply/forall_inP=> x; rewrite cfunE.
    case: (boolP (x \in i))=> //= XiI HH //; last by case/eqP: HH.
    case: (boolP (x \in A))=> // XniA; case/eqP: Hr.
    case/imsetP: Hi XiI => g GiG ->; case/imsetP=> h HiG Hx.
    case: (repr_class G g)=> h1 H1iG ->.
    by rewrite Hc // -(Hc _ _ _ HiG) // -Hx Hg // inE (negPf XniA).
  by apply/mapP; exists (enum_rank_in (classes1 G) i);  
      [rewrite mem_enum | rewrite enum_rankK_in].
apply/cfunP=> g; rewrite sum_cfunE cfunE.
case GiG: (g \in G); last first.
  rewrite Hg ?(inE,GiG,andbF) //; apply: big1=> i Hi; rewrite !cfunE.
  have [x Gx ->] := imsetP Hi.
  case Hgx: (_ \in _); last by rewrite mulr0.
  move/subsetP: (class_subG Gx (subxx G)) GiG.
  by move/(_ g (idP Hgx))=> ->.
rewrite (bigD1 (g ^: G : set_of_finType _)) /=; last by apply/imsetP; exists g.
rewrite !cfunE big1.
  rewrite class_refl.
  case: (repr_class G g)=> x Hx ->; rewrite Hc // addr0; exact: mulr1.
move=> i; case/andP; case/imsetP=> y Hy -> Hz.
rewrite !cfunE; case E1: (_ \in _); last by rewrite mulr0.
by case/negP: Hz; rewrite eq_sym; apply/eqP; apply: class_transr.
Qed.

Lemma cfun_memP : forall (f : cfun),
  reflect 
    ((forall x, x \notin G -> f x = 0) /\
        (forall x y, x \in G -> y \in G -> f (x ^ y) = f x))
    (f \in 'CF(G)).
Proof. by move=> f; apply: (iffP (cfun_memfP G f)); rewrite setIid. Qed.

Lemma cfunS0 : forall A (f : cfun) x, f \in 'CF(G,A) -> x \notin A -> f x = 0.
Proof. 
move=> A f x; case/cfun_memfP=> HH _ XniA; apply: HH.
by rewrite inE (negPf XniA).
Qed.

Lemma cfun0 : forall (f : cfun) x, f \in 'CF(G) -> x \notin G -> f x = 0.
Proof. exact: cfunS0. Qed.

Lemma cfunJ : forall A (f : cfun) x y, 
   f \in 'CF(G,A) -> x \in G -> y \in G -> f (x ^ y) = f x.
Proof. by move=> A f x y; case/cfun_memfP=> _ HH; exact: HH. Qed.

Lemma cfun_sum : forall (F : gT -> R),
  (forall g h, g \in G -> h \in G -> F (g^h) = F g) ->
  \sum_(g \in G) F g = \sum_(C \in classes G) #|C|%:R * (F (repr C)).
Proof.
move=> F HF.
rewrite {1}(partition_big _  _ ((@mem_classes gT)^~ G)) /=.
apply: eq_bigr=> cl Hcl.
rewrite (eq_bigr (fun _ => F (repr cl))); last first.
  move=> i1; case/andP=> Hi1; move/eqP=> <-.
  by case: (repr_class G i1)=> z Hz ->; rewrite HF.
rewrite -sum1_card natr_sum -!mulr_suml.
apply: eq_big=> [i1|i1]; last by rewrite mul1r.
case/imsetP: Hcl=> z Hz ->; apply/idP/idP=>[|Hi].
  by case/andP=> Hi; move/eqP<-; exact: class_refl.
move/subsetP: (class_subG Hz (subxx _)); move/(_ _ Hi)->.
by apply/eqP; apply: class_transr.
Qed.

Lemma cfun_free : forall A, free (base_cfun G A).
Proof.
move=> A; apply: free_filter.
apply/freeP=> s S0 i.
have Hi: (i < #|classes G|)%N 
  by case: i=> /= m; rewrite size_map -cardE card_ord.
move/cfunP: S0; move/(_ (repr (enum_val (Ordinal Hi)))).
rewrite sum_cfunE !cfunE (bigD1 i) //= big1.
 rewrite !cfunE (nth_map (Ordinal Hi)) // ?cfunE; last first.
   by rewrite -cardE card_ord.
 rewrite (nth_ord_enum  _ (Ordinal Hi)).
 have [y Gy ->] := imsetP (enum_valP (Ordinal Hi)).
 case: (repr_class G y)=> x Hx ->.
 by rewrite memJ_class // addr0 => <-; apply: sym_equal; exact: mulr1.
move=> j Dij.
rewrite (nth_map (Ordinal Hi)) ?cfunE ?ffunE; last first.
  by case: {Dij}j=> /= m; rewrite size_map.
have Hj: (j < #|classes G|)%N.
  by case: {Dij}j=> /= m; rewrite size_map -cardE card_ord.
rewrite (nth_ord_enum  _ (Ordinal Hj))=> /=.
move: (@enum_val_inj _  _ (Ordinal Hj) (Ordinal Hi)).
have [y Gy ->] := imsetP (enum_valP (Ordinal Hi)).
have [z Gz ->] := imsetP (enum_valP (Ordinal Hj)).
case: (repr_class G y)=> t Ht -> Heq.
case Et: (_ \in _); last by  exact: mulr0.
suff: z ^: G = y ^: G by move/Heq; move/val_eqP=> HH; case/negP: Dij.
apply: class_transr.
by rewrite class_sym (class_trans _ Et) // -{1}[y]conjg1 
           classGidl // conjg1 class_refl .
Qed.

Lemma dim_cfun : \dim ('CF(G)) = #|classes G|.
Proof.
move: (cfun_free G); rewrite /free; move/eqP->.
by rewrite base_cfun_subset ?subxx // size_map -cardE card_ord.
Qed.

End ClassFun.

Notation "''CF[' R ] ( G , A ) " := (class_fun R G A).
Notation "''CF[' R ] ( G ) " := (class_fun R G G).
Notation "''CF(' G , A ) " := 
  (class_fun (GRing.ClosedField.fieldType algC) G A).
Notation "''CF(' G ) " := 
  (class_fun (GRing.ClosedField.fieldType algC) G G).

Definition cfun_conjC (gT: finGroupType) (f : cfun gT algC) :=
  cfun_of_fun (fun h => (f h)^*).

Notation "f ^*" := (cfun_conjC f) : character_scope.

Lemma cfun_conjCE : forall gT (f : cfun gT algC) g, (f^*)%CH g = (f g)^*.
Proof. by move=> gT f g; rewrite cfunE. Qed.

Lemma cfun_conjCK: forall gT (f : cfun gT algC), (f^*^*)%CH = f.
Proof. by move=> gT f; apply/cfunP=> g; rewrite !cfunE conjCK. Qed.

Section Char.

Variables (gT : finGroupType) (G : {group gT}).

Definition char_of_repr n (G : {set gT}) (f: gT -> 'M[algC]_n) := 
 cfun_of_fun (fun g : gT => ((g \in G)%:R * \tr (f g))).

Lemma char_of_repr1 : 
  forall n (rG : mx_representation algC G n), char_of_repr G rG 1%g = n%:R.
Proof. by move=> n rG; rewrite !cfunE group1 repr_mx1 mxtrace1 mul1r. Qed.

Lemma char_of_repr_sim : 
  forall n1 n2 (rG1: mx_representation algC G n1) 
               (rG2: mx_representation algC G n2),
  mx_rsim rG1 rG2 -> char_of_repr G rG1 = char_of_repr G rG2.
Proof.
move=> n1 n2 rG1 rG2; case/mx_rsim_def=> M1 [M2] HM1M2 Hx.
apply/cfunP=> x; rewrite !cfunE; case H: (_ \in _); last by rewrite !mul0r.
by rewrite Hx // mxtrace_mulC mulmxA HM1M2 mul1mx.
Qed.

Lemma char_of_repr_in_cfun : forall n (rG :  mx_representation algC G n), 
  char_of_repr G rG \in 'CF(G).
Proof.
move=> n rG; apply/cfun_memP.
split=> [x|x y Hx Hy]; rewrite !cfunE.
  by case: (x \in G)=> //; rewrite mul0r.
by rewrite groupJ // Hx !mul1r !(repr_mxM,repr_mxV,groupM,groupV) //
           mxtrace_mulC mulmxK // repr_mx_unit.
Qed.

Lemma char_of_grepr0 : char_of_repr G (@grepr0 algC _ G) = 0.
Proof. by apply/cfunP=> g; rewrite !cfunE mxtrace1 mulr0. Qed.

Lemma char_of_dadd_grepr : forall rG1 rG2 : representation algC G,
  char_of_repr G (dadd_grepr rG1 rG2) = 
    char_of_repr G rG1 + char_of_repr G rG2.
Proof.
by move=> rG1 rG2; apply/cfunP=> g; rewrite !cfunE -mulr_addr mxtrace_block.
Qed.

Lemma char_of_dsum_grepr : forall (I : finType) (P : pred I),
                           forall rG : I -> representation algC G,
  char_of_repr G (\big[dadd_grepr/grepr0]_(i | P i) rG i) =
    \sum_(i | P i) char_of_repr G (rG i).
Proof.
pose gchar (rG : representation algC G) := char_of_repr G rG.
by move=> I; exact: (big_morph gchar char_of_dadd_grepr char_of_grepr0).
Qed.

Lemma char_of_n_grepr : forall (rG : representation algC G) k, 
  char_of_repr G (n_grepr rG k) = char_of_repr G rG *+ k.
Proof. by move=> rG k; rewrite char_of_dsum_grepr /= sumr_const card_ord. Qed.

Section StandardRepr.

Variables (n : nat) (rG : mx_representation algC G n).
Let sG := DecSocleType rG.
Let iG : irrType algC G := DecSocleType _.

Definition standard_irr (W : sG) := irr_comp iG (socle_repr W).

Definition standard_socle i := pick [pred W | standard_irr W == i].
Local Notation soc := standard_socle.

Definition standard_irr_coef i := oapp (fun W => socle_mult W) 0%N (soc i).

Definition standard_grepr :=
  \big[dadd_grepr/grepr0]_i
    n_grepr (Representation (socle_repr i)) (standard_irr_coef i).

Lemma mx_rsim_standard : mx_rsim rG standard_grepr.
Proof.
pose W i := oapp val 0 (soc i); pose S := (\sum_i W i)%MS.
have C'G: [char algC]^'.-group G := pGroupG G.
have [defS dxS]: (S :=: 1%:M)%MS /\ mxdirect S.
  rewrite /S mxdirectE /= !(bigID soc xpredT) /=.
  rewrite addsmxC big1 => [|i]; last by rewrite /W; case (soc i).
  rewrite adds0mx_id addnC (@big1 nat) ?add0n => [|i]; last first.
    by rewrite /W; case: (soc i); rewrite ?mxrank0.
  have <-: Socle sG = 1%:M := reducible_Socle1 sG (mx_Maschke rG C'G).
  have [W0 _ | noW] := pickP sG; last first.
    suff no_i: (soc : pred iG) =1 xpred0 by rewrite /Socle !big_pred0 ?mxrank0.
    by move=> i; rewrite /soc; case: pickP => // W0; have:= noW W0.
  have irrK: forall Wi, soc (standard_irr Wi) = Some Wi.
    move=> Wi; rewrite /soc.
    case: pickP => [W' /= | ]; last by move/(_ Wi); rewrite /= eqxx.
    move/eqP=> eqWi; apply/eqP; apply/socle_rsimP.
    apply: mx_rsim_trans (rsim_irr_comp iG C'G (socle_irr _)) (mx_rsim_sym _).
    by rewrite [irr_comp _ _]eqWi; exact: rsim_irr_comp (socle_irr _).
  have bij_irr: {on [pred i | soc i], bijective standard_irr}.
    exists (odflt W0 \o soc) => [Wi _ | i]; first by rewrite /= irrK.
    by rewrite inE /soc /=; case: pickP => //= Wi; move/eqP.
  rewrite !(reindex standard_irr) {bij_irr}//=.
  have all_soc: forall Wi, soc (standard_irr Wi) by move=> Wi; rewrite irrK.
  rewrite (eq_bigr val) => [|Wi _]; last by rewrite /W irrK.
  rewrite !(eq_bigl _ _ all_soc); split=> //.
  rewrite (eq_bigr (mxrank \o val)) => [|Wi _]; last by rewrite /W irrK.
  by rewrite -mxdirectE /= Socle_direct.
pose modW i : mxmodule rG (W i) :=
  if soc i is Some Wi as oWi return mxmodule rG (oapp val 0 oWi) then
    component_mx_module rG (socle_base Wi)
  else mxmodule0 rG n.
apply: mx_rsim_trans (mx_rsim_sym (rsim_submod1 (mxmodule1 rG) _)) _ => //.
apply: mx_rsim_dsum (modW) _ defS dxS _ => i.
rewrite /W /standard_irr_coef /modW /soc; case: pickP => [Wi|_] /=; last first.
  rewrite /n_grepr big_ord0.
  by exists 0 => [||x _]; rewrite ?mxrank0 ?mulmx0 ?mul0mx.
by move/eqP=> <-; apply: mx_rsim_socle; exact: rsim_irr_comp (socle_irr Wi).
Qed.

End StandardRepr.

(* This proof needs to be later, because it requires the linear independence
   of the irreducible characters *)
(* !!!!!!!!!!! FOR THE MOMENT AN AXIOM !!!!!!!!!!!!!!!!!!! *)
Lemma char_of_repr_rsimP : forall m n (rG1 : mx_representation algC G m)
                                      (rG2 : mx_representation algC G n),
   reflect (mx_rsim rG1 rG2) (char_of_repr G rG1 == char_of_repr G rG2).
Proof.
move=> m n rG1 rG2; apply: (iffP eqP)=> HH; last first.
  apply/cfunP=> g; rewrite !cfunE.
  case E1: (g \in G); last by rewrite !mul0r.
  by rewrite !mul1r; apply: mxtrace_rsim.
admit.
Qed.

Definition reg_cfun := char_of_repr G (regular_repr algC G).

Lemma reg_cfunE : forall (g : gT),
  reg_cfun g = if (g == 1%g) then #|G|%:R else 0.
Proof.
move=> g; rewrite cfunE.
case: (boolP (g \in G))=> [Hg|]; last first.
  by rewrite !mul0r; case: eqP=> // ->; case/negP; exact: group1.
rewrite mul1r /mxtrace.
case: eqP=> [->| Hd]; last first.
  apply: big1=> i _; rewrite !mxE andTb.
  case: eqP=> // He; case: Hd; apply: sym_equal.
  apply: (mulgI (enum_val i)); rewrite mulg1.
  by apply: (can_in_inj (@gring_indexK _ G));
   [exact: enum_valP | exact: (groupM (enum_valP _) Hg) | rewrite gring_valK].
rewrite (eq_bigr (fun x => 1%:R)); last first.
  by move=> i; rewrite !mxE mulg1 gring_valK !eqxx.
by rewrite sumr_const cardT -cardE card_ord.
Qed.

Definition xchar (chi: cfun gT algC) (u: 'rV[algC]_#|G|) : algC^o := 
  \sum_(i < #|G|) u 0 i * chi (enum_val i).

(* In order to add a second canonical structure on xchar *)
Definition xcharb x := (@xchar)^~ x.

Lemma xcharbE : forall u (x : 'rV_#|G|), xchar u x = xcharb x u.
Proof. by []. Qed.

Lemma xcharb_is_linear : forall x, linear (xcharb x).
Proof.
move=> i k m n.
rewrite /xchar scaler_sumr -big_split /=; apply: eq_bigr=> l _.
by rewrite !cfunE mulr_addr scaler_mulr.
Qed.

Canonical Structure xcharb_linear x := Linear (xcharb_is_linear x).

Lemma xchar_trace : forall u n (rG: mx_representation algC G n),
  xchar (char_of_repr G rG) u = 
  \tr (gring_op rG (gring_mx (regular_repr algC G) u)).
Proof.
move=> u n rG.
rewrite /xchar /gring_op /= gring_mxK.
apply: (@etrans _ _
   (\sum_(i0 < #|G|) \tr(u 0 i0 *: rG (enum_val i0)))).
  by apply: eq_bigr=> j _; rewrite cfunE enum_valP mul1r mxtraceZ.
rewrite -raddf_sum; congr (\tr _).
apply/matrixP=> i1 j1; rewrite !mxE summxE; apply eq_bigr=> k1 _.
by rewrite !(mxvecE,mxE).
Qed.

End Char.

Section IrrClass.

Variable (gT : finGroupType).

Section IrrClassDef.

Variable (G : {set gT}).

Let sG := DecSocleType (regular_repr algC <<G>>).

Inductive irr : predArgType := IrrClass of sG.
Definition socle_of_irr (theta : irr) := let: IrrClass s := theta in s.
Definition irr_of_socle := IrrClass.

Canonical Structure irr_subType :=
  Eval hnf in [newType for socle_of_irr by irr_rect].
Definition irr_eqMixin := Eval hnf in [eqMixin of irr by <:].
Canonical Structure irr_eqType := 
  Eval hnf in EqType irr irr_eqMixin.
Definition irr_choiceMixin := [choiceMixin of irr by <:].
Canonical Structure irr_choiceType :=
  Eval hnf in ChoiceType irr irr_choiceMixin.
Definition irr_countMixin := [countMixin of irr by <:].
Canonical Structure irr_countType :=
  Eval hnf in CountType irr irr_countMixin.
Canonical Structure irr_subCountType :=
  Eval hnf in [subCountType of irr].
Definition irr_finMixin := [finMixin of irr by <:].
Canonical Structure irr_finType :=
  Eval hnf in FinType irr irr_finMixin.
Canonical Structure irr_subFinType :=
  Eval hnf in [subFinType of irr].

Coercion cfun_of_irr theta := 
  char_of_repr <<G>> (irr_repr (@socle_of_irr theta)).

Definition irr1 := IrrClass (principal_comp sG).
  
Definition get_irr f :=
  odflt irr1 [pick theta | (theta : irr) == f :> cfun _ _].

End IrrClassDef.

Variable (G : {group gT}).

Let sG := DecSocleType (regular_repr algC <<G>>).

Lemma irr_reprE : forall (theta : irr G),
   exists i : DecSocleType (regular_repr algC G),
   theta = char_of_repr G (irr_repr i) :> cfun _ _. 
Proof.
move=> theta.
have: exists i : DecSocleType (regular_repr algC <<G>>),
          theta = char_of_repr <<G>> (irr_repr i) :> cfun _ _.
  by exists (socle_of_irr theta).
by rewrite !(genGidG,genGid).
Qed.

(* GG: THIS IS WRONG!!! injectivity FOLLOWS from linear independance *)
Lemma cfun_of_irr_inj : injective (@cfun_of_irr G).
Proof.
move=> theta1 theta2.
move/eqP; move/char_of_repr_rsimP.
move/(irr_comp_rsim sG (pGroupG <<G>>)).
rewrite !irr_reprK //; try exact: pGroupG.
by case: theta1; case: theta2=>  u v /= ->.
Qed.

Lemma irr1E : forall g, irr1 G g = (g \in G)%:R.
Proof.
move=> g; case: (boolP (_ \in _))=> GiG; last first.
  by rewrite (cfun0 (char_of_repr_in_cfun _)) ?genGidG.
rewrite cfunE {1}genGid GiG mul1r irr1_repr ?genGidG //.
by rewrite mxtrace1 degree_irr1.
Qed.

Lemma card_irr : #|irr G| = #|classes G|.
Proof.
rewrite -{6}[G]genGidG.
rewrite -(card_irr sG) ?pGroupG //; last exact: groupC.
by rewrite card_sub; apply: eq_card=> i; rewrite !inE.
Qed.

Lemma irr_val1 : forall theta : irr G, 
  theta 1%g = (irr_degree (socle_of_irr theta))%:R.
Proof.
by move=> theta; rewrite cfunE group1 mul1r repr_mx1 mxtrace1.
Qed.

Lemma irr1_neq0 : forall theta : irr G, theta 1%g != 0.
Proof.
move=> theta; rewrite irr_val1 -neq0N_neqC.
by case: irr_degree (irr_degree_gt0 (socle_of_irr theta)).
Qed.

Lemma irr_sum_square : \sum_(theta : irr G) (theta 1%g) ^+ 2 = #|G|%:R.
Proof.
rewrite -{6}[G]genGidG.
rewrite -(sum_irr_degree sG) ?pGroupG //; last exact: groupC.
rewrite (big_morph _ (@natr_add _) (erefl _)).
rewrite (reindex (@socle_of_irr G)); last by exists (@irr_of_socle G)=> [] [].
by apply: eq_bigr=> theta _; rewrite irr_val1 natr_exp.
Qed.

Lemma irr_in_cfun : forall theta : irr G, (theta : cfun _ _) \in 'CF(G).
Proof.
move=> theta; case: (irr_reprE theta)=> rG ->.
by apply: char_of_repr_in_cfun.
Qed.

Definition is_irr (G : {set gT}) (f : cfun _ _) := 
  existsb theta : irr G, f == theta.

Lemma is_irr_irr: forall theta : irr G, is_irr G theta.
Proof. by move=> theta; apply/existsP; exists theta. Qed.

Lemma is_irrP : forall f, 
  reflect (exists theta : irr G, f = theta :> cfun _ _) (is_irr G f).
Proof.
by move=> f; apply: (iffP (@existsP _ _))=>[[theta Ht]|[theta ->]];
   exists theta=> //; apply/eqP.
Qed.

Lemma is_irr_reprP : forall f, 
  reflect (exists i : DecSocleType (regular_repr algC G),
             f = char_of_repr G (irr_repr i))
          (is_irr G f).
Proof.
move=> f; apply: (iffP idP)=>[|[i->]].
  case/is_irrP=> chi.
  by case: (irr_reprE chi)=> i -> ->; exists i.
move: i.
suff: forall i : DecSocleType (regular_repr algC <<G>>),
         is_irr G (char_of_repr <<G>> (irr_repr i)).
  by rewrite !(genGid,genGidG).
by move=> i; apply/is_irrP; exists (irr_of_socle i).
Qed.

Lemma get_irrE : forall f, is_irr G f -> get_irr G f = f :> cfun _ _ .
Proof.
move=> f; case/is_irrP=> theta Ht; rewrite /get_irr; case: pickP=> /=.
  by move=> theta'; move/eqP.
by move/(_ theta); rewrite Ht eqxx.
Qed.
 
Lemma reg_cfun_sum : 
  reg_cfun G = \sum_(theta : irr G) theta (1%g) *: (theta : cfun _ _).
Proof.
rewrite -{1}[G]genGidG.
apply/cfunP=> g; rewrite !cfunE.
case Ig: (_ \in _); last first.
  rewrite mul0r sum_cfunE cfunE big1 // => theta _.
  by rewrite cfunE [_ g](cfun0 (char_of_repr_in_cfun _)) (mulr0,Ig).
rewrite mul1r (mxtrace_regular sG (pGroupG _)) //; last by exact: groupC.
rewrite sum_cfunE cfunE.
  (* Too slow 
rewrite {1}(reindex (@socle_of_irr G)).
*)
pose reindex := (@reindex _ _ (GRing.add_comoid algC)).
rewrite (reindex _  _ (@socle_of_irr G)) //=; last first.
  by exists (@irr_of_socle G)=> [] [].
by apply eq_bigr=> i _; rewrite irr_val1 !cfunE Ig mul1r // mulr_natl.
Qed.

Lemma xchar_is_linear : forall theta : irr G, linear (@xchar _ G theta).
Proof.
move=> theta k m n.
rewrite scaler_sumr -big_split /=; apply: eq_bigr=> l _.
by rewrite scaler_mull -mulr_addl !mxE.
Qed.

Canonical Structure xchar_linear (theta : irr G) := 
  Linear (xchar_is_linear theta).

Local Notation "'E_" := 
  ((@Wedderburn_id _ _ _ _) \o (@socle_of_irr _)) (at level 0).
Local Notation "'R_":= 
  ((@Wedderburn_subring _ _ _ _) \o (@socle_of_irr _)) (at level 0).

Lemma xchar_subring : forall (theta1 theta2 : irr G) A, 
  theta1 != theta2 -> (A \in 'R_theta2)%MS -> xchar theta1 (gring_row A) = 0.
Proof.
move=> theta1 theta2 A Ht HA.
pose s := @socle_of_irr G.
rewrite xchar_trace -(mxtrace0 _ (irr_degree (s theta1))); congr (\tr _).
have F1: s theta2 != irr_comp sG (irr_repr (s theta1)).
  rewrite irr_reprK ?pGroupG //.
  apply/eqP=> HH; case/eqP: Ht; apply/val_eqP.
  by rewrite eq_sym; apply/eqP.
apply: irr_comp'_op0 F1 _; first by exact: pGroupG.
  by apply: socle_irr.
rewrite gring_rowK // -(Wedderburn_sum sG (pGroupG _)).
apply/memmx_sumsP; exists (fun ss => (ss == s theta2)%:R *: A).
  rewrite (bigD1 (s theta2)) //= eqxx scale1r big1 ?addr0 // => k.
  by case: (k == s theta2); rewrite // scale0r.
by move=> k; case E1: (k == s theta2); 
  [move/eqP: E1->; rewrite scale1r | rewrite scale0r mem0mx].
Qed.

Lemma xchar_id : forall theta1 theta2 : irr G,
  xchar theta1 (gring_row ('E_ theta2)) = 
   if theta1 == theta2 then theta1 1%g else 0.
Proof.
move=> theta1 theta2; case: eqP=> [->|Ht]; last first.
  by apply: xchar_subring (Wedderburn_id_mem _); apply/eqP.
rewrite cfunE group1 mul1r -gring_opG //.
have R1 := (envelop_mx_id (regular_repr algC <<G>>) (group1 <<G>>)).
rewrite -[regular_repr algC _ 1%g]gring_rowK // -xchar_trace.
rewrite -[regular_repr _ _ _]mul1mx -(Wedderburn_sum_id sG (pGroupG _)).
have->: regular_repr algC <<G>> 1%g = 1%:M.
  by apply/matrixP=> i1 j1; rewrite !mxE !eqxx mulg1 gring_valK eq_sym.
pose s := @socle_of_irr G.
rewrite mulmx1 linear_sum.
have HL: forall theta : irr G, linear (@xchar _ <<G>> theta).
  by rewrite genGidG; exact: xchar_is_linear.
pose f theta := Linear (HL theta).
rewrite (@linear_sum _ _ _ (f _)) /= (bigD1 (s theta2)) //= big1=> [|k].
  by rewrite addr0.
rewrite eq_sym => Hij.
have F1: theta2 != irr_of_socle k by apply/eqP; move/val_eqP=> HH; case/negP: Hij.
exact: (xchar_subring F1 (Wedderburn_id_mem k)).
Qed.

Lemma irr_e_mul : forall (theta : irr G) A, (A \in group_ring algC <<G>>)%MS ->
 xchar theta (gring_row ('E_ theta *m A)) = xchar theta (gring_row A).
Proof.
move=> theta A HA.
rewrite -{2}[A]mul1mx -(Wedderburn_sum_id sG); last exact: pGroupG.
rewrite mulmx_suml linear_sum.
have HL: forall theta : irr G, linear (@xchar _ <<G>> theta).
  by rewrite genGidG; exact: xchar_is_linear.
pose f theta := Linear (HL theta).
rewrite (@linear_sum _ _ _ (f _)) /= (bigD1 (socle_of_irr theta)) //=.
rewrite big1 ?addr0 // => ss; rewrite eq_sym => Hss.
have F1: theta != irr_of_socle ss by apply/eqP; move/val_eqP=> HH; case/negP: Hss.
apply: (xchar_subring F1).
case/andP: (Wedderburn_ideal ss)=> _ Hj.
apply: submx_trans Hj=> //.
apply: mem_mulsmx=> //.
exact: Wedderburn_id_mem.
Qed.

Lemma xchar_singleton : forall n g (rG : mx_representation algC G n),  
  g \in G -> 
    xchar (char_of_repr G rG) (gring_row (regular_repr algC G g)) = 
    char_of_repr G rG g.
Proof.
move=> n g rG Hg.
  rewrite /xchar (bigD1 (enum_rank_in (group1 G) g)) // big1 ?addr0.
  by rewrite enum_rankK_in // !mxE gring_indexK // mul1g !eqxx mul1r //= addr0.
move=> i; rewrite !mxE enum_rankK_in // mul1g /gring_index.
by case: (i == _)=> //; rewrite mul0r.
Qed.

(* This corresponds to Isaacs' Th. 2.12 *)
Lemma gring_row_e : forall theta : irr G, 
  gring_row ('E_ theta) = \row_i (#|G|%:R^-1 * theta 1%g * theta ((enum_val i)^-1)%g).
Proof.
move=> theta; apply/rowP=> i.
set g:= ((enum_val i)^-1)%g.
have GiG: (g \in <<G>>)%g by rewrite groupV enum_valP.
pose rG := regular_repr algC <<G>> g.
have: xchar (reg_cfun G) (gring_row ('E_ theta *m rG)) = 
        #|G|%:R * gring_row ('E_ theta) 0 i.
  rewrite /xchar (bigD1 (gring_index <<G>> 1%g)) //= big1; last first.
    move=> k Hk; rewrite reg_cfunE.
    case: eqP; last by rewrite mulr0.
    by move=> Hk'; case/negP: Hk; rewrite -Hk' gring_valK.
  rewrite addr0 enum_rankK_in ?genGid // gring_row_mul.
  rewrite reg_cfunE // eqxx mulrC; congr (_ * _).
  (* This takes ages 
  rewrite {1}mxE {1}(bigD1 j) //= {1}big1.
  *)
  rewrite {1}mxE {1}(@bigD1 _ _ (GRing.add_comoid algC) _ i) //= big1.
    by rewrite !mxE mulgV !eqxx mulr1 addr0.
  move=> k Hk.
  rewrite !mxE eqxx; case: eqP; last by rewrite mulr0.
  move=> Hi; case/negP: Hk.
  apply/eqP; apply: enum_val_inj; apply/eqP; rewrite eq_mulgV1.
  rewrite eq_sym; apply/eqP.
  apply: (can_in_inj (@gring_indexK _ <<G>>))=> //.
  by rewrite !(groupM,enum_valP).
rewrite reg_cfun_sum xcharbE linear_sum /=.
rewrite (bigD1 theta) //= big1 ?addr0; last first.
  move=> k Hki.
  rewrite linearZ /= -xcharbE.
  rewrite (xchar_subring Hki) //; first by rewrite scaler0.
  case/andP: (Wedderburn_ideal (socle_of_irr theta))=> _ Hi.
  apply: submx_trans Hi; apply: mem_mulsmx; first by exact: Wedderburn_id_mem.
  by apply: envelop_mx_id; rewrite groupV enum_valP.
rewrite linearZ /= -xcharbE.
rewrite irr_e_mul; last first.
  by apply: envelop_mx_id; rewrite groupV enum_valP.
have->: forall n g (rG : mx_representation algC <<G>> n),  
    g \in <<G>> -> 
    xchar (char_of_repr <<G>> rG) (gring_row (regular_repr algC <<G>> g)) = 
    char_of_repr <<G>> rG g; last by [].
  rewrite !genGid genGidG.
  by exact: xchar_singleton.
rewrite !mxE // /GRing.scale /= -mulrA => ->.
by rewrite !mulrA mulVf ?mul1r // neq0GC.
Qed.

Definition to_socle n (rG : mx_representation algC <<G>> n) (j: DecSocleType rG) := 
  irr_comp sG (socle_repr j).

Lemma to_socle_inj : forall n (rG : mx_representation algC <<G>> n),
  injective (@to_socle n rG).
Proof.
move=> n rG x y Hxy; apply/eqP; apply/socle_rsimP.
apply: (mx_rsim_trans (rsim_irr_comp sG _ (socle_irr _))).
  by exact: pGroupG.
apply: mx_rsim_sym; move: Hxy; rewrite /to_socle=>->.
by apply: (rsim_irr_comp sG _ (socle_irr _)); exact: pGroupG.
Qed.

Definition irr_coef n (rG : mx_representation algC <<G>> n) theta :=
let s :=  socle_of_irr theta in
oapp (fun x => socle_mult x) 0%N [pick j | s == to_socle (j: DecSocleType rG)].

Lemma char_of_standard_grepr : forall n (rG : mx_representation algC <<G>> n),
  char_of_repr <<G>> (standard_grepr rG)
    = \sum_(theta : irr G)
         (standard_irr_coef rG (val theta))%:R *: (theta : cfun _ _).
Proof.
move=> n rG; rewrite char_of_dsum_grepr.
rewrite (reindex (@IrrClass _)) /=; last by exists val => // [[]].
by apply: eq_bigr => i _; rewrite scaler_nat char_of_n_grepr.
Qed.

End IrrClass.

Section VectorSpace.

Variable (gT : finGroupType).

Section VectorSpaceDef.

Variable (G : {set gT}).

Definition base_irr := map (@cfun_of_irr gT G) (enum (irr G)).

Lemma sg2bi_ord : forall (theta : irr G), 
  (enum_rank theta < size base_irr)%N.
Proof. by move=> i; rewrite size_map -cardE. Qed.

Lemma bi2sg_ord : 
  forall (i : 'I_(size base_irr)), (i < #|irr G|)%N.
Proof. by case=> i; rewrite size_map -cardE. Qed.

Definition bi2sg (i : 'I_(size base_irr)) :=
  enum_val (Ordinal (bi2sg_ord i)).

Definition sg2bi (theta : irr G) := Ordinal (sg2bi_ord theta).

Lemma bi2sgK : cancel bi2sg sg2bi.
Proof. by case=> i Hi; apply/val_eqP; rewrite /= enum_valK. Qed.

Lemma sg2biK : cancel sg2bi bi2sg.
Proof. 
by move=> i; rewrite -{2}(enum_rankK i); congr enum_val; apply/val_eqP.
Qed.

Definition ncoord (i: irr G) c : algC^o := coord base_irr c (sg2bi i).

End VectorSpaceDef.

Variable (G : {group gT}).

Local Notation "'E_" := 
  ((@Wedderburn_id _ _ _ _) \o (@socle_of_irr _ _)) (at level 0).
Local Notation "'R_":= 
  ((@Wedderburn_subring _ _ _ _) \o (@socle_of_irr _ _)) (at level 0).
  
Lemma free_base_irr : free (base_irr G).
Proof.
apply/freeP=> s; set ss := \sum_(i<_) _ => Hs j.
have Hj: (j <  #|irr G|)%nat by case: j; rewrite size_map -cardE.
pose j' := enum_val (Ordinal Hj).
suff: xchar ss (gring_row ('E_ j')) = s j * j' 1%g.
  rewrite /xchar big1 //.
    move/eqP; rewrite eq_sym mulf_eq0; case/orP; first by move/eqP.
    rewrite irr_val1 -(eqN_eqC _ 0)=> He.
    by move: (irr_degree_gt0 (socle_of_irr j')); rewrite (eqP He).
  by move=> i _; rewrite Hs cfunE mulr0.
rewrite xcharbE linear_sum; rewrite (bigD1 j) //= big1.
  rewrite  addr0 (nth_map (irr1 G)) //; last by rewrite -cardE.
  rewrite linearZ /= -xcharbE.
  suff->: (nth (irr1 G) (enum (irr G)) j) = j'
    by rewrite  xchar_id eqxx.
  by move: (nth_enum_rank (irr1 G) j'); rewrite enum_valK.
move=> i Hij.
have Hi: (i <  #|irr G|)%nat.
  by case: {Hij}i; rewrite size_map -cardE.
pose i' := enum_val (Ordinal Hi).
rewrite  (nth_map (irr1 G)) //; last by rewrite -cardE.
rewrite linearZ /= -xcharbE.
have->: (nth (irr1 G) (enum (irr G)) i) = i'.
  by move: (nth_enum_rank (irr1 G) i'); rewrite enum_valK.
rewrite  xchar_id; case: eqP; last by rewrite scaler0.
move/eqP=> HH; case/negP: Hij.
by move: HH; rewrite (bij_eq (enum_val_bij (irr_finType G))).
Qed.

Lemma char_of_repr_inj : forall n1 n2,
  forall rG1 : mx_representation algC G n1,
  forall rG2 : mx_representation algC G n2,
  char_of_repr G rG1 = char_of_repr G rG2 -> mx_rsim rG1 rG2.
Proof.
rewrite -(genGidG G) => n1 n2 rG1 rG2 /= eq_char12.
have [rsim1 rsim2] := (mx_rsim_standard rG1, mx_rsim_standard rG2).
pose c rG (xi : irr G) : algC := (standard_irr_coef rG (val xi))%:R.
suff eq_c21: (fun i => c n1 rG1 (bi2sg i) - c n2 rG2 (bi2sg i)) =1 (fun _ => 0).
  apply: mx_rsim_trans rsim1 (mx_rsim_sym _).
  suffices ->: standard_grepr rG1 = standard_grepr rG2 by [].
  apply: eq_bigr => theta _; congr (n_grepr _ _).
  apply/eqP; rewrite eqN_eqC -subr_eq0 -[theta]/(val (IrrClass theta)).
  by rewrite -(sg2biK (IrrClass theta)) eq_c21.
apply: (freeP _ free_base_irr); apply/eqP.
rewrite (eq_bigr _ (fun i _ => scaler_subl _ _ _)) sumr_sub subr_eq0.
have sg2bi_bij: {on predT, bijective (@sg2bi G)}.
  by apply: onW_bij; exists (@bi2sg G); [exact: sg2biK | exact: bi2sgK].
rewrite !(reindex (@sg2bi G)) {sg2bi_bij}//=.
have id_irr: forall n rG xi (i := sg2bi xi),
  true -> c n rG (bi2sg i) *: (base_irr G)`_i = c n rG xi *: (xi : cfun _ _).
- move=> n rG xi i _; rewrite sg2biK; congr (_ *: _).
  by rewrite (nth_map (bi2sg i)) -?cardE ?bi2sg_ord ?nth_enum_rank.
rewrite !{id_irr}(eq_bigr _ (id_irr _ _)) -!char_of_standard_grepr.
by rewrite -(char_of_repr_sim rsim1) -(char_of_repr_sim rsim2) eq_char12.
Qed.

Lemma base_irr_basis : is_basis 'CF(G) (base_irr G).
Proof.
rewrite /is_basis free_base_irr andbT /is_span -dimv_leqif_eq.
  rewrite dim_cfun.
  move: free_base_irr; rewrite /free; move/eqP->.
  by rewrite size_map -cardE card_irr.
rewrite -span_subsetl; apply/allP=> i; case/mapP=> j _ ->.
by rewrite -{2 3}genGid char_of_repr_in_cfun.
Qed.

Lemma ncoord_sum : forall x : cfun gT algC, x \in 'CF(G) -> 
  x = \sum_(theta : irr G) ncoord theta x *: (theta : cfun _ _).
Proof.
move=> x Hx.
have F1:  {on [pred i | xpredT i], bijective (@bi2sg G)}.
  by apply: onW_bij; exists (@sg2bi G); [apply: bi2sgK | apply: sg2biK].
rewrite (reindex _ F1) /=.
have F2: x \in span (base_irr G).
  move: (is_basis_span base_irr_basis).
  by rewrite /is_span; move/eqP->.
rewrite {1}(coord_span F2); apply: eq_bigr=> i _; congr (_ *: _).
  by rewrite /ncoord bi2sgK.
rewrite  (nth_map (irr1 G)).
  by rewrite /bi2sg (enum_val_nth (irr1 G)).
rewrite -cardE; apply: bi2sg_ord.
Qed.

Lemma ncoord_is_linear : forall theta : irr G, linear (ncoord theta).
Proof. by move=> i k c1 c2; rewrite /ncoord linearD linearZ !ffunE. Qed.

Canonical Structure ncoord_linear (theta : irr G) :=
  Linear (ncoord_is_linear theta).

Lemma ncoordE : forall  (f : cfun _ _) (coord : irr G -> algC), 
  f \in 'CF(G) -> f = \sum_theta (coord theta) *: (theta: cfun _ _) -> 
  forall theta, coord theta = ncoord theta f.
Proof.
move=> f coord Hin Hf theta.
suff: (fun j => ncoord (bi2sg j) f -  coord (bi2sg j)) =1 (fun _ => 0).
  move/(_ (sg2bi theta)); rewrite sg2biK; move/eqP.
  by rewrite subr_eq0; move/eqP.
move/freeP: free_base_irr; apply.
have F1:  {on [pred i | xpredT i], bijective (@sg2bi G)}.
  by apply: onW_bij; exists (@bi2sg G); [apply: sg2biK | apply: bi2sgK ].
rewrite (reindex _ F1) /=.
rewrite (eq_bigr (fun theta => ncoord theta f *: (theta : cfun _ _) - 
                             coord theta *: (theta : cfun _ _))).
  by rewrite sumr_sub -Hf -ncoord_sum // subrr.
by move=> theta' _; rewrite sg2biK scaler_subl // (nth_map (irr1 G)) -?cardE
                       // nth_enum_rank.
Qed.

Lemma ncoord0 : forall theta : irr G, ncoord theta 0 = 0.
Proof.
move=> theta; apply: sym_equal.
apply: (@ncoordE 0 (fun i => 0:algC)); first exact: mem0v.
by rewrite big1 // => j _; exact: scale0r.
Qed.

Lemma ncoord_irr : forall theta1 theta2 : irr G, 
  ncoord theta1 theta2 = (theta1 == theta2)%:R.
Proof.
move=> theta1 theta2.
apply: sym_equal; apply: (@ncoordE _ (fun j => (j == theta2)%:R)).
  by rewrite -{2 3}genGid; exact: char_of_repr_in_cfun.
rewrite (bigD1 theta2) // big1 /= ?(addr0,eqxx,scale1r) // => theta.
by rewrite eq_sym; case: (_ == _)=> //; rewrite scale0r.
Qed.

Lemma isNatC_ncoord_repr :
  forall n (rG : mx_representation algC G n) (theta : irr G),
    isNatC(ncoord theta (char_of_repr G rG)).
Proof.
suff: forall n (rG : mx_representation algC <<G>> n) (theta : irr G),
  isNatC(ncoord theta (char_of_repr <<G>> rG)) by rewrite genGid.
move=> n rG theta.
pose sG':= DecSocleType rG.
rewrite -(@ncoordE _ (fun theta => (irr_coef rG theta)%:R)).
- by rewrite isNatC_nat.
- by rewrite -{3 4}genGid char_of_repr_in_cfun.
pose ts (i: sG') := (to_socle i).
have->: char_of_repr <<G>> rG = 
  \sum_i (irr_of_socle (ts i) : cfun _ _) *+ socle_mult i.
  apply/cfunP=> g; rewrite !(sum_cfunE,cfunE).
  case: (boolP (_ \in _))=> Hin; last first.
    rewrite mul0r big1 ?ffunE // => j _.
    by rewrite (cfun0 _ Hin) // memvMn // char_of_repr_in_cfun.
  have F1: (Socle sG' :=: 1%:M)%MS.
    by rewrite reducible_Socle1 //; apply: mx_Maschke; exact: pGroupG.
  rewrite mul1r -(mxtrace_submod1 (Socle_module sG') F1) // mxtrace_Socle=> //.
  apply: eq_bigr=> i1 _ /=.
  rewrite  cfunMn !cfunE Hin mul1r; congr (_ *+ _).
  apply: mxtrace_rsim=> //; apply: rsim_irr_comp=> //; first by exact: pGroupG. 
  by apply/submod_mx_irr; apply: socle_simple.
case  E1: (enum sG') => [| x s].
  have F1: forall (i: sG'), false.
    by move=> x; have: x \in enum sG'; [rewrite mem_enum | rewrite E1].
  rewrite !big1 //; last by move=> x; have:= F1 x.
  move=> j; rewrite /irr_coef; case: pickP; last by rewrite scale0r.
  by move=> x; have:= F1 x.
rewrite (reindex (@irr_of_socle _ G)) /=; last first.
  by exists (@socle_of_irr _ G)=> // [] [].
have->: 
  \sum_i
    (irr_coef rG (irr_of_socle i))%:R *: (irr_of_socle i : cfun _ _) = 
   \sum_ (i |  codom ts i) 
    (irr_coef rG (irr_of_socle i))%:R *: (irr_of_socle i : cfun _ _).
  apply: sym_equal; rewrite big_mkcond; apply: eq_bigr=> k _.
  rewrite /irr_coef; case: pickP; last by rewrite scale0r if_same.
  by move=> i1 /=; move/eqP->; rewrite codom_f.
have F1:  {on [pred i | codom ts i],  bijective ts}.
  pose f i := odflt x [pick j | i == ts j].
  exists f=> [i1 _|i1].
    rewrite /f; case: pickP=> [i2|]; last by move/(_ i1); rewrite eqxx.
    by move/eqP; move/to_socle_inj->.
  case/imageP=> i2 Hi2.
  rewrite /f; case: pickP; first by move=>i3; move/eqP.
  by move/(_ i2); move/eqP.
rewrite (reindex _ F1) /=.
apply: eq_big=>[i1 /=|i1 _]; first by rewrite /= codom_f.
rewrite scaler_nat /irr_coef; congr (_ *+ _).
case: pickP; last by move/(_ i1); rewrite eqxx.
by move=> i2; move/eqP; move/to_socle_inj<-.
Qed.

End VectorSpace.

Section Restrict.

Variable (gT : finGroupType).

Definition crestrict (G : {set gT}) (f : cfun gT algC) :=
    cfun_of_fun (fun g : gT => (g \in G)%:R * (f g)).

Local Notation "''Res[' G ]  f " := (crestrict G f) (at level 24).

Lemma crestrictE : forall (G : {set gT}) f, {in G, 'Res[G] f =1 f}.
Proof. by move=> G f g H; rewrite cfunE H mul1r. Qed.
 
Lemma crestrict_in_cfun : forall f (G H : {group gT}), 
  H \subset G -> f \in 'CF(G) -> 'Res[H] f \in 'CF(H).
Proof.
move=> f G H Hsub fC; apply/cfun_memP; split.
  by move=> g; rewrite cfunE; case: (_ \in _)=> //; rewrite mul0r.
move=> g h gIn hIn; rewrite !cfunE groupJ //.
by rewrite gIn (cfunJ fC) // (subsetP Hsub).
Qed.

Lemma crestrict_is_linear : forall (G : {group gT}), linear (crestrict G).
Proof.
move=> G c f1 f2; apply/cfunP=> g.
by rewrite !cfunE mulr_addr mulrCA.
Qed.

Canonical Structure crestrit_linear G :=
  Linear (crestrict_is_linear G).

Lemma crestrict_subset : 
  forall (G  H : {set gT}) (f : cfun gT algC),
  H \subset G -> 'Res[H] ('Res[G] f) = 'Res[H] f.
Proof.
move=> G H f HsG; apply/cfunP=> g.
by rewrite !cfunE; case: (boolP (_ \in _))=> [HH|]; 
   rewrite ?mul0r // (subsetP HsG) // !mul1r.
Qed.

Lemma crestrict_subg : 
  forall (G H : {group gT}) n (rG : mx_representation algC G n)
                              (HsG: H \subset G),
  'Res[H] (char_of_repr G rG) = char_of_repr H (subg_repr rG HsG).
Proof.
move=> G H n rG HsG; apply/cfunP=> g; rewrite !cfunE /=.
by case InH: (g \in H); rewrite ?mul0r // (subsetP HsG _ (idP InH)) !mul1r.
Qed.

End Restrict.

Notation "''Res[' G ]  f " := (crestrict G f) (at level 24).

Section IsChar.

Variable (gT : finGroupType).

Section IsCharDef.

Variable G : {set gT}.

Definition is_char  (f : cfun gT algC) :=
  all (fun theta : irr G => isNatC (ncoord theta f)) (enum (irr G)) &&
  (f \in 'CF[algC](<<G>>)).

End IsCharDef.

Variable G : {group gT}.

Lemma is_charP : forall f,
  reflect (exists n, exists rG : mx_representation algC G n, 
            char_of_repr G rG = f)
          (is_char G f).
Proof.
move=> f.
suff: reflect (exists n, exists rG : mx_representation algC <<G>> n, 
               char_of_repr <<G>> rG = f)
              (is_char G f) by rewrite genGid.
apply: (iffP andP); last first.
  case=> n [rG <-]; split; last exact: char_of_repr_in_cfun.
  apply/allP=> chi _.
  move: rG; rewrite genGid=> rG.
  by exact: isNatC_ncoord_repr.
case; move/allP=> Ha Hf.
pose n' (j : irr G) := getNatC (ncoord j f).
have->: f = \sum_(j : irr G) (n' j)%:R *: (j : cfun _ _).
  move: (Hf); rewrite genGid=> Hf'.
  rewrite {1}(ncoord_sum Hf'); apply: eq_bigr=> i _.
  congr (_ *: _); apply/eqP; rewrite -getNatCP; apply: Ha.
  by exact: mem_enum.
elim: {n'}(\sum_j (n' j))%N {-2}n' (leqnn (\sum_j (n' j)))=> [| N IH] n' HS.
  exists 0%N; exists grepr0.
  apply/cfunP=> i; rewrite sum_cfunE !cfunE mxtrace1 mulr0 big1 // => j Hj.
  by move: HS; rewrite (bigD1 j) //=; case: (n' j)=> //; rewrite scale0r cfunE.
case: (boolP (all (fun i => n' i == 0%N) (enum (irr G)))).
  move/allP=> HH.
  exists 0%N; exists grepr0.
  apply/cfunP=> i; rewrite sum_cfunE !cfunE mxtrace1 mulr0 big1 // => j Hj.
  by rewrite (eqP (HH _ (mem_enum _ j))) scale0r cfunE.
case/allPn=> k kIn Hk.
pose n'' j := if (j == k) then (n' j).-1 else n' j.
have F1: (\sum_j (n' j) = 1 + \sum_j n'' j)%N.
  rewrite (bigD1 k) //[(\sum_j n'' j)%N](bigD1 k) //.
  rewrite addnA /n'' eqxx add1n prednK; last by case: (n' k) Hk.
  by congr (_ + _)%N; apply: eq_bigr=> i; case: (i == k).
have F2: \sum_j (n' j)%:R *: (j : cfun _ _)  = 
             (k : cfun _ _) + \sum_j (n'' j)%:R *: (j : cfun _ _).
  rewrite (bigD1 k) //[(\sum_j (n'' j)%:R *: _)](bigD1 k) // addrA; congr (_ + _).
    rewrite /n'' eqxx -{2}[(k: cfun _ _)]scale1r -scaler_addl -(natr_add _ 1%N).
    by rewrite add1n prednK //; case: (n' k) Hk.
  by apply: eq_bigr=> i; rewrite /n''; case: (i == k).
case: (IH n''); first by  rewrite -ltnS -add1n -F1.
intros n [rG HrG]; pose i := socle_of_irr k; exists ((irr_degree i) + n)%N.
exists (dadd_grepr (Representation (irr_repr i)) (Representation rG)).
by rewrite (char_of_dadd_grepr (Representation _) (Representation _)) HrG F2.
Qed.

Lemma is_char_char_of_repr : forall n (rG : mx_representation algC G n),
  is_char G (char_of_repr G rG).
Proof. by move=> n rG; apply/is_charP; exists n; exists rG. Qed.

Lemma is_char_reg : is_char G (reg_cfun G).
Proof. exact: is_char_char_of_repr. Qed.

Lemma is_char_irr : forall theta : irr G, is_char G theta.
Proof. 
move=> theta; apply/is_charP; pose i := socle_of_irr theta.
suff: exists n : nat,
  exists rG : mx_representation algC <<G>> n, char_of_repr <<G>> rG = theta.
    by rewrite genGid.
by exists (irr_degree i); exists (irr_repr i).
Qed.

Lemma isNatC_ncoord_char : forall (theta : irr G) (f : cfun _ _),
 is_char G f -> isNatC (ncoord theta f).
Proof.
move=> i f; case/is_charP=> n [rG <-].
by exact: isNatC_ncoord_repr.
Qed.

Lemma is_char0 : is_char G 0.
Proof. by rewrite -(char_of_grepr0 G) is_char_char_of_repr. Qed.

Lemma character0_eq0 : forall chi,
  is_char G chi -> (chi == 0) = (chi 1%g == 0).
Proof.
move=> chi IC; apply/eqP/eqP=> [->|HH]; first by rewrite cfunE.
move: HH; case/is_charP: IC=> n [rG <-].
rewrite !cfunE group1 repr_mx1 mxtrace1 mul1r; move/eqP; rewrite -(eqN_eqC _ 0).
move=>HH; move: rG; rewrite (eqP HH)=> rG.
by apply/cfunP=> g; rewrite !cfunE [rG _]flatmx0 mxtrace0 mulr0.
Qed.

Lemma is_char_in_cfun : forall f,  is_char G f -> f \in 'CF(G).
Proof. 
by move=> f; case/is_charP=> n [rG <-]; apply: char_of_repr_in_cfun.
Qed.

Lemma is_char_add : forall f1 f2, 
  is_char G f1 -> is_char G f2 -> is_char G (f1 + f2).
Proof.
move=> f1 f2; case/is_charP=> m [rG1 HrG1]; case/is_charP=> n [rG2 HrG2].
apply/is_charP; exists (m + n)%N.
exists (dadd_grepr (Representation rG1) (Representation rG2)).
by rewrite (char_of_dadd_grepr (Representation _) (Representation _)) HrG1 HrG2.
Qed.

Lemma is_char_scal : forall f n, is_char G f -> is_char G (f *+ n).
Proof.
move=> f n Hf; elim: n=> [|n Hn]; first by rewrite mulr0n is_char0.
by rewrite mulrS is_char_add.
Qed.

Lemma is_char_sum : forall (I : eqType) r (P : I -> bool) (F : I -> cfun _ _),
  (forall i, ((P i) && (i \in r)) -> is_char G (F i)) -> 
    is_char G (\sum_(i <- r | P i)  F i).
Proof.
move=> I r P F; elim: r=> [| a r IH HH].
  by rewrite big_nil is_char0.
have HF : is_char G (\sum_(i <- r | P i) F i).
  by apply: IH=> i; case/andP=> HH1 HH2; apply: HH; rewrite HH1 inE HH2 orbT.
rewrite big_cons; case: (boolP (P a))=> HP //; rewrite is_char_add //.
by rewrite HH // inE eqxx andbT.
Qed.

Lemma is_char_cbP : forall f,
  reflect 
    (exists n, f = \sum_(theta : irr G) (n theta)%:R *: (theta : cfun _ _))
    (is_char G f).
Proof.
move=> f; apply: (iffP idP)=> [HH|[n ->]]; last first.
  apply: is_char_sum=> i _.
  by rewrite scaler_nat is_char_scal // is_char_irr.
exists (fun theta => getNatC (ncoord theta f)).
rewrite {1}(ncoord_sum (is_char_in_cfun HH)).
apply: eq_bigr=> theta _.
by move/(@isNatC_ncoord_char theta): HH; rewrite getNatCP; move/eqP<-.
Qed.

Lemma is_char_indu : forall (P: cfun gT algC -> Prop), P 0 -> 
  (forall (theta : irr G) chi, 
      is_char G chi -> P chi -> P ((theta : cfun _ _) + chi)) ->
  forall chi, is_char G chi -> P chi.
Proof.
move=> P P0 IH chi; case/is_char_cbP=> n ->.
elim: {n}(\sum_t (n t))%N {-2}n (leqnn (\sum_t (n t)))=>[n HH|N IH1 n].
  rewrite big1 // => i _.
  by move: HH; rewrite (bigD1 i) //=; case: (n i)=> //; rewrite scale0r.
case: (boolP (all (fun t => n t == 0%N) (enum (irr G)))).
  move/allP=> Ht _; rewrite big1 // => theta _.
  move: (Ht theta); rewrite mem_enum.
  by move/(_ is_true_true); move/eqP->; rewrite scale0r.
case/allPn=> theta; rewrite mem_enum=> Ht Nt0 HH.
pose n' (t : irr G) := if (t == theta) then (n t).-1 else n t.
have F1: (\sum_t (n t) = (\sum_t (n' t)).+1)%N.
  rewrite (bigD1 theta) // [(\sum_t n' t)%N](bigD1 theta) //= -add1n addnA.
  congr (_ + _)%N; first by rewrite /n' eqxx; case: (n theta) Nt0.
  by apply: eq_bigr=> j Hj; rewrite /n' (negPf Hj).
have F2: \sum_t (n t)%:R *: (t : cfun _ _)  = 
           (theta : cfun _ _) + \sum_t (n' t)%:R *: (t : cfun _ _).
  rewrite (bigD1 theta) //= [\sum_t (n' t)%:R *: _](bigD1 theta) //=.
  rewrite addrA; congr (_ + _).
    rewrite /n' eqxx; case: (n theta) Nt0=> // m' _.
    by rewrite -{1}add1n natr_add scaler_addl scale1r.
  by apply: eq_bigr=> j Hj; rewrite /n' (negPf Hj).
rewrite F2; apply: IH.
  by apply: is_char_sum=> i _; rewrite scaler_nat is_char_scal // is_char_irr.
by apply: IH1; rewrite -ltnS -F1.
Qed.

Lemma isNatC_char1 : forall chi, is_char G chi -> isNatC (chi 1%g).
Proof.
apply is_char_indu=> {chi}[|theta chi IH HH].
  by rewrite cfunE (isNatC_nat 0).
by rewrite cfunE isNatC_add // irr_val1 isNatC_nat.
Qed.

Lemma posC_char1 : forall chi, is_char G chi -> 0 <= chi 1%g.
Proof. by move=> chi HH; apply: posC_isNatC; apply: (isNatC_char1 _). Qed.

Lemma ltC_irr1: forall (theta : irr G), 0 < theta 1%g.
Proof.
move=> theta.
case/isNatCP: (isNatC_char1 (is_char_irr theta)) (irr1_neq0 theta).
by move=> n /= ->; rewrite /ltC => ->; exact: posC_nat.
Qed.


Lemma is_irr_crestrict : forall (H : {group gT}) chi,
 is_char G chi -> H \subset G -> is_irr H ('Res[H] chi) -> is_irr G chi.
Proof.
move=> H chi; case/is_charP.
suff: forall n : nat,
  (exists rG : mx_representation algC <<G>> n, char_of_repr <<G>> rG = chi) ->
   <<H>> \subset <<G>> -> is_irr H ('Res[<<H>>] chi) -> is_irr G chi.
  by rewrite !genGid.
move=> n [rG <-] HsG.
rewrite (crestrict_subg _ HsG).
case/is_irrP=> i Hi; apply/is_irrP.
pose sG := DecSocleType (regular_repr algC <<G>>).
exists (irr_of_socle (irr_comp sG rG)).
apply/eqP;apply/char_of_repr_rsimP=> /=.
apply: rsim_irr_comp; first by exact: pGroupG.
apply: (@subg_mx_irr _ _ _ _ _ _ HsG).
move/eqP: Hi.
move/char_of_repr_rsimP.
move/mx_rsim_sym; move/mx_rsim_irr; apply.
by apply: socle_irr.
Qed.

End IsChar.

Section Linear.

Variables (gT : finGroupType) (G : {group gT}) (f: cfun gT algC).

Definition clinear (G : {set gT}) f := is_char <<G>> f && (f 1%g == 1).

Hypothesis CFf : clinear G f.

Lemma clinear1: f 1%g = 1.
Proof. by apply/eqP; case/andP: CFf. Qed.

Lemma is_char_linear : is_char G f.
Proof. by case/andP: CFf; rewrite genGid. Qed.

Lemma clinearM: forall g h,
  g \in G -> h \in G -> f (g * h)%g = f g * f h.
Proof.
move=> g h InG InH.
case/andP: (CFf); rewrite genGid.
case/is_charP=> // n [rG <-] HH.
move/eqP: (char_of_repr1 rG); rewrite (eqP HH) -(eqN_eqC 1%N) => Hn.
rewrite !cfunE groupM // InG InH // !mul1r repr_mxM //.
move: {HH}rG; rewrite -(eqP Hn)=> rG.
rewrite (mx11_scalar (rG g)) (mx11_scalar (rG h)) -scalar_mxM.
by rewrite !mxtrace_scalar !mulr1n.
Qed.

Lemma clinear_neq0: forall g, g \in G -> f g != 0.
Proof.
move=> g InG; apply/eqP=> fg.
case/eqP: (nonzero1r algC); case/andP: (CFf)=> _; move/eqP<-.
by rewrite -(mulgV g) clinearM ?groupV // fg mul0r.
Qed.

Lemma clinearV: forall g, g \in G -> f (g^-1)%g = (f g)^-1.
Proof.
move=> g InG.
have F1: f g * f (g^-1%g) = 1 by rewrite -clinearM ?groupV // mulgV clinear1.
have F2 := clinear_neq0 InG.
by apply: (mulfI F2); rewrite F1 divff.
Qed.

Lemma clinearX : forall g n, g \in G -> (f g)^+n = f (g^+n)%g.
Proof.
move=> g n Hin; elim: n=> [|n IH]; first by rewrite expr0 expg0 clinear1.
by rewrite exprS expgS clinearM ?groupX // IH.
Qed.

Lemma clinear_unit : forall g, g \in G -> f g ^+ #[g] = 1.
Proof. by move=> g InG; rewrite clinearX // expg_order clinear1. Qed.

Lemma clinear_norm : forall g, g \in G -> normC (f g) = 1%:R.
Proof.
move=> g InG; have Hs := clinear_unit InG.
apply/eqP; rewrite -(@posC_unit_exp _ (#[g].-1)) //; last by exact: posC_norm.
by rewrite prednK // -normC_exp Hs normC1.
Qed.

Lemma clinearV_norm : forall g, g \in G ->  f (g^-1%g) = (f g)^*.
Proof.
move=> g InG; rewrite invg_expg -clinearX //.
apply: (mulfI (clinear_neq0 InG)).
rewrite -exprS prednK // clinear_unit // -[_ * _]sqrtCK.
move: (clinear_norm InG); rewrite /normC => -> //.
by rewrite exprS mulr1.
Qed.

Lemma char_abelianP : 
  reflect (forall (theta : irr G), clinear G theta) (abelian G).
Proof.
apply: (iffP idP)=> [HH theta|HH].
  rewrite /clinear genGid irr_val1 irr_degree_abelian ?genGidG //; last first.
    by exact: groupC.
  by rewrite is_char_irr // eqxx.
rewrite card_classes_abelian.
rewrite eqN_eqC -irr_sum_square // (eq_bigr (fun i => 1)) //=.
  by rewrite sumr_const // -card_irr.
by move=> i _; case/andP: (HH i)=> _ HH'; rewrite (eqP HH') exprS mulr1.
Qed.

Lemma irr_repr_linear : forall (theta : irr G) g, g \in G -> 
  clinear G theta -> irr_repr (socle_of_irr theta) g = (theta g)%:M.
Proof.
move=> theta g GiG AbG.
rewrite cfunE genGid GiG mul1r.
move: (irr_repr (socle_of_irr theta)).
case/andP: AbG=> _; rewrite irr_val1.
rewrite -(eqN_eqC _ 1);move/eqP->.
move=> irr_repr; rewrite trace_mx11.
apply/matrixP=> [] [[|] Hi1] // [[|] Hj1] //.
by rewrite !mxE /= mulr1n; congr fun_of_matrix; apply/eqP.
Qed.

Lemma clinear_is_irr : is_irr G f.
Proof.
case/andP: (CFf); rewrite genGid => Hc Hf.
case/is_charP: Hc => n [].
suff: forall rG : mx_representation algC <<G>> n, 
          char_of_repr <<G>> rG = f -> is_irr G f.
  by rewrite genGid.
move=> rG HrG.
move: Hf; rewrite -HrG char_of_repr1 -(eqN_eqC _ 1%N).
move/eqP=> Hn; move: rG HrG; rewrite Hn.
move=> rG HrG; apply/is_irrP.
pose sG := DecSocleType (regular_repr algC <<G>>).
exists (irr_of_socle (irr_comp sG rG)).
apply/eqP; apply/char_of_repr_rsimP=> /=.
apply: rsim_irr_comp; first by exact: pGroupG.
apply/mx_irrP; split=> // U HU HU1.
move: HU1 (rank_leq_row U); rewrite -mxrank_eq0 /row_full.
by case: (\rank _)=> // [] [|].
Qed.

End Linear.

Section MoreIsChar.

Variable (gT : finGroupType) (G H : {group gT}).

Lemma is_char_restrict : forall f, 
  H \subset G -> is_char G f -> is_char H ('Res[H] f).
Proof.
move=> f Hsub; case/is_charP=> n [rG <-].
apply/is_charP; exists n; exists (subg_repr rG Hsub).
apply/cfunP=> g; rewrite !cfunE; case E1: (_ \in _); last by rewrite !mul0r.
by rewrite (subsetP Hsub) // !mul1r.
Qed.

Lemma char_norm : forall chi (g : gT),
  is_char G chi -> normC (chi g) <= chi 1%g.
Proof.
move=> chi g; case/is_charP=> n [rG <-].
case: (boolP (g \in G))=> Hin; last first.
  by rewrite (cfun0 (char_of_repr_in_cfun _)) // normC0 char_of_repr1 posC_nat.
have F1: (<[g]> \subset G) by rewrite cycle_subG.
pose rG' := subg_repr rG F1.
have Hf: forall g1, g1 \in <[g]> -> 
    char_of_repr G rG g1 = char_of_repr <[g]> rG' g1.
  by move=> g1 Hg1; rewrite !cfunE Hg1; move/subsetP: (F1)->.
rewrite !Hf ?(cycle_id,group1) // (ncoord_sum (char_of_repr_in_cfun _)).
rewrite !sum_cfunE 2!cfunE.
pose nc (i: irr <[g]>) := ncoord i (char_of_repr <[g]> rG').
suff->: \sum_i (nc i *: (i: cfun _ _)) 1%g = 
        \sum_i normC ((nc i *: (i: cfun _ _)) g%g).
  by apply: normC_sum.
have F2 := cycle_abelian g.
apply: eq_bigr=> i _.
rewrite cfunE irr_val1 irr_degree_abelian ?genGidG //; last first.
  by exact: groupC.
have CFf: clinear <[g]> i by move/char_abelianP: F2; apply.
rewrite cfunE normC_mul (clinear_norm  CFf) ?cycle_id //.
by rewrite normC_pos // /nc posC_isNatC // isNatC_ncoord_repr.
Qed.

 (* This could surely be proved more nicely in mx_representation *)
Lemma clinear_norm_scalar : 
  forall n (rG : mx_representation algC G n) g,
   g \in G -> 
   (forall (theta : irr G), clinear G theta) ->
   normC (char_of_repr G rG g) = char_of_repr G rG 1%g ->
   exists2 c, normC c = (n != 0%N)%:R & rG g = c%:M.
Proof.
suff Hf: forall f, is_char G f ->
  forall (n : nat) (rG : mx_representation algC G n) (g : gT),
    g \in G -> f = char_of_repr G rG -> 
    (forall theta : irr G, clinear G theta) -> normC (f g) = f 1%g ->
    exists2 c : algC, normC c = (n != 0%N)%:R & rG g = c%:M.
  move=> n rG g GiG HP HN.
  suff: is_char G (char_of_repr G rG) by move/Hf; apply.
  by apply: is_char_char_of_repr.
apply: is_char_indu=> [|theta chi IC IH] n.
   move=> rG g GiG H0.
   have: mx_rsim rG (@grepr0 algC _ G).
     by apply/char_of_repr_rsimP; rewrite -H0 char_of_grepr0.
   move/mxrank_rsim=> HH; move: {H0}rG; rewrite HH=> rG.
   exists 0; first by rewrite eqxx normC0.
   by rewrite (flatmx0 (rG g)) (flatmx0 _%:M) .
suff: forall (rG : mx_representation algC <<G>> n) (g : gT),
       g \in G -> (theta : cfun _ _) + chi = char_of_repr <<G>> rG ->
       (forall theta : irr G, clinear G theta) ->
       normC (((theta : cfun _ _) + chi) g) = ((theta : cfun _ _) + chi) 1%g ->
       exists2 c : algC, normC c = (n != 0%N)%:R & rG g = c%:M.
  by rewrite genGid.
move=> rG g GiG H0 CL; rewrite cfunE [_ 1%g]cfunE=> NN.
have GiG': g \in <<G>> by rewrite genGid.
have F1: normC (theta g + chi g) = normC (theta g) + normC (chi g).
  apply: (leC_anti (normC_add _ _)); rewrite NN.
  apply: leC_add; [apply: char_norm | apply: char_norm] => //.
  by apply: is_char_irr.
have F2 : normC (chi g) = chi 1%g.
  apply: (leC_anti (char_norm _ _))=> //.
  rewrite -(leC_add2l (theta 1%g)) -NN F1 leC_add2r char_norm //.
  by apply: is_char_irr.
have F3: normC(theta g) = theta 1%g.
  by apply: (@addIr _ (normC (chi g))); rewrite -F1 NN F2.
have F4 := (irr_repr_linear GiG (CL theta)).
have F5: theta 1%g = 1 by case: (CL theta); case/andP=> _;move/eqP.
case/is_charP: IC=> m [].
suff: forall rG1 : mx_representation algC <<G>> m,
          char_of_repr <<G>> rG1 = chi ->
          exists2 c : algC, normC c = (n != 0%N)%:R & rG g = c%:M.
  by move: {H0}rG; rewrite genGid.
move=> rG1 Hc.
have IH': forall (n : nat) (rG : mx_representation algC <<G>> n) (g : gT),
     g \in G ->
     chi = char_of_repr <<G>> rG ->
     (forall theta : irr G, clinear G theta) ->
     normC (chi g) = chi 1%g ->
     exists2 c : algC, normC c = (n != 0%N)%:R & rG g = c%:M.
  by rewrite genGid.
case: (IH' _ _ _ GiG (sym_equal Hc) CL F2)=> c H1c H2c.
move: H1c; case: eqP=> Hm H1c.
  have F6: mx_rsim rG (irr_repr (socle_of_irr theta)).
    apply/char_of_repr_rsimP; rewrite -H0.
    suff->: chi = 0 :> cfun _ _ by rewrite addr0.
    rewrite -Hc; move: {Hc H2c}rG1; rewrite Hm=> rG1.
    by apply/cfunP=> h; rewrite !cfunE (flatmx0 (rG1 _)) mxtrace0 mulr0.
  exists (theta g); last by apply: (mx_rsim_scalar GiG' (mx_rsim_sym F6)).
  rewrite F3; case/andP: (CL theta)=> _; move/eqP->.
  case: eqP=> //; move/eqP; rewrite eqN_eqC.
  move/mxrank_rsim: F6->; rewrite -(irr_val1 theta) F5.
  by rewrite -(eqN_eqC 1 0).
have F6 : theta g = c.
  case/normC_add_eq: F1=> k Hk.
  case/andP; move/eqP=> H1k; move/eqP=> H2k.
  rewrite H1k F3 F5 mul1r.
  move/eqP: Hm; rewrite neq0N_neqC;move/mulfI; apply.
  move: H2k; rewrite -Hc cfunE GiG' mul1r H2c.
  rewrite mxtrace_scalar -mulr_natr normC_mul H1c mul1r.
  by rewrite normC_pos ?posC_nat // mulrC.
pose rG' := dadd_grepr (Representation (irr_repr (socle_of_irr theta)))
                       (Representation rG1).
have F7: mx_rsim rG rG'.
  apply/char_of_repr_rsimP; rewrite -H0.
  by rewrite (char_of_dadd_grepr (Representation _) (Representation _)) Hc.
have F8 : rG' g = c%:M.
  have->: rG' g= block_mx (irr_repr (socle_of_irr theta) g) 0 0 (rG1 g).
   by [].
  by rewrite H2c F4 F6 -scalar_mx_block.
exists c; last by by apply: (mx_rsim_scalar GiG' (mx_rsim_sym F7)).
rewrite H1c; case/mxrank_rsim: F7; move/eqP.
rewrite eqN_eqC natr_add -(irr_val1 theta) F5 -(natr_add _ 1%N m) -eqN_eqC.
by case: {rG H0}n.
Qed.

Lemma clinear_cker_mx1 : 
  forall n (rG : mx_representation algC G n) g,
   g \in G -> 
   (forall (theta : irr G), clinear G theta) ->
   char_of_repr G rG g = char_of_repr G rG 1%g ->  rG g = 1%:M.
Proof.
move=> n rG g GiG Ht HC.
case/isNatCP: (isNatC_char1 (is_char_char_of_repr rG))=> k Hk.
have: normC (char_of_repr G rG g) = char_of_repr G rG 1%g.
  by rewrite HC Hk normC_nat.
case/(clinear_norm_scalar GiG Ht)=> c Hc Hx.
move: Hk; rewrite -HC cfunE GiG Hx mxtrace_scalar.
move: Hc; case: eqP=> [HH _ _|Hn HN]; first by rewrite HH !(flatmx0 _%:M).
rewrite mul1r=> HH.
suff->: c = 1 by [].
have F1: n%:R != 0 :> algC by rewrite -neq0N_neqC; move/eqP: Hn.
have F2: c = k%:R * n%:R^-1.
  by apply: (mulIf F1); rewrite mulr_natr HH mulfVK.
move: HN; rewrite F2.
by rewrite normC_mul normC_inv normC_pos ?posC_nat // normC_nat.
Qed.

Definition is_comp (G : {set gT}) (theta : irr G) (f : cfun gT algC) := 
  ncoord theta f != 0.

Lemma is_compE : forall (i : irr G) f, is_comp i f = (ncoord i f != 0).
Proof. by []. Qed.

Lemma is_comp_charP : forall (theta : irr G) chi,
  is_char G chi ->
  reflect (exists2 chi', is_char G chi' &
             chi = (theta : cfun _ _) + chi' :> cfun _ _) 
          (is_comp theta chi).
Proof.
move=> theta chi IC; apply: (iffP idP)=>[HH|[chi' IC' ->]]; last first.
  rewrite /is_comp linearD /= ncoord_irr eqxx.
  case/isNatCP: (isNatC_ncoord_char theta IC')=> n ->.
  by rewrite -natr_add -neq0N_neqC.
exists (chi - (theta : cfun _ _)); last by rewrite addrC subrK.
apply/andP; split; last first.
  by rewrite memv_sub // genGid ?(is_char_in_cfun, is_char_irr).
apply/allP=> /= t _.
rewrite linearD linearN /= ncoord_irr.
case: (_ =P _)=> [->|_]; last first.
  by rewrite subr0 isNatC_ncoord_char.
move: HH; rewrite /is_comp.
case/isNatCP: (isNatC_ncoord_char theta IC)=>  [] [|n] ->.
  by case/negP.
by rewrite -addn1 natr_add addrK isNatC_nat.
Qed.

Lemma is_comp_neq0 : forall f : cfun _ _, 
  f \in 'CF(G) -> f != 0 :> cfun _ _ -> exists i : irr G, is_comp i f.
Proof.
move=> f FCF Nf0; case: (pickP ((@is_comp G)^~ f)) => [i Hi | HH].
  by exists i.
case/eqP: Nf0; apply/val_eqP=> /=.
move: (ncoord_sum FCF); rewrite big1=> [|i Hi]; first by move=> ->.
by move/eqP: (HH i)->; rewrite scale0r.
Qed.

Lemma is_comp_irr1_char1 : forall (theta : irr G) chi, 
  is_char G chi ->  is_comp theta chi -> theta 1%g <= chi 1%g.
Proof.
move=> theta chi IC; rewrite is_compE => Hn.
rewrite (ncoord_sum (is_char_in_cfun IC)) (bigD1 theta) //=.
set n := theta 1%g; rewrite 2!cfunE {}/n -leC_sub addrC addrA.
apply: posC_add.
  rewrite -mulN1r -mulr_addl posC_mul //; last first.
    by rewrite posC_isNatC // (isNatC_char1 (is_char_irr _)).
  case/isNatCP: (isNatC_ncoord_char theta IC) Hn=> [] [|n] -> //.
    by rewrite /is_comp; case/negP.
  by move=> _; rewrite -add1n natr_add addrA addNr add0r posC_nat.
rewrite sum_cfunE cfunE posC_sum // => t Ht.
rewrite cfunE posC_mul //; last first.
  by rewrite posC_isNatC // (isNatC_char1 (is_char_irr _)).
by rewrite posC_isNatC // (isNatC_ncoord_char t IC).
Qed.

Lemma is_char_conjC : forall chi, is_char G chi -> is_char G (chi^*)%CH.
Proof.
move=> chi; case/is_charP=> n [rG <-].
apply/is_charP; exists n; exists (map_repr conjC rG).
by apply/cfunP=> h; rewrite !cfunE map_reprE trace_map_mx rmorphM conjC_nat.
Qed.

End MoreIsChar.

Section OrthogonalRelations.

Variable (aT gT : finGroupType) (A : {group aT}) (G : {group gT}).

Lemma char_inv : forall n (rG: mx_representation algC G n) g,
  char_of_repr G rG g^-1%g = (char_of_repr G rG g)^*.
Proof.
move=> n rG g.
case: (boolP (g \in G))=> Hin; last first.
  by rewrite (cfun0 (char_of_repr_in_cfun _) Hin); rewrite -groupV // in Hin;
     rewrite (cfun0 (char_of_repr_in_cfun _)) // conjC0.
have F1: (<[g]> \subset G) by rewrite cycle_subG.
pose rG' := subg_repr rG F1.
have F2: forall g1, g1 \in <[g]> -> 
    char_of_repr G rG g1 = char_of_repr <[g]> rG' g1.
  by move=> g1 Hg1; rewrite !cfunE Hg1; move/subsetP: (F1)->.
rewrite !F2 ?(groupVr,cycle_id) //. 
rewrite (ncoord_sum (char_of_repr_in_cfun _)).
rewrite sum_cfunE 2!cfunE rmorph_sum; apply: eq_bigr=> i _.
have Cf: clinear <[g]> i by move/char_abelianP: (cycle_abelian g); move/(_ i).
rewrite cfunE (clinearV_norm Cf) ?cycle_id //.
have F3: isNatC (ncoord i (char_of_repr <[g]> rG'))
  by apply: isNatC_ncoord_repr.
by rewrite -{1}(isNatC_conj F3) {1}/GRing.scale /= -rmorphM ?cfunE.
Qed.

Lemma invg_is_char : forall chi g, is_char G chi -> chi g^-1%g = (chi g)^*.
Proof.
move=> chi g; case/is_charP=> n [rG <-]; exact: char_inv.
Qed.

Let card_neq0 : #|G|%:R^-1 != 0 :> algC.
Proof. by rewrite invr_eq0 neq0GC. Qed.

(* Painfully following Isaacs' proof 2.14 *)
Lemma irr_first_orthogonal_relation : forall theta1 theta2 : irr G,
 #|G|%:R^-1 * (\sum_(g \in G) theta1 g * (theta2 g)^*) = (theta1 == theta2)%:R.
Proof.
move=> theta1 theta2.
rewrite (reindex invg) /=; last by apply: onW_bij; apply: inv_bij; exact invgK.
pose e (theta : irr G) :=  Wedderburn_id (socle_of_irr theta).
have F1 : e theta1 *m e theta2 = (theta1 == theta2)%:R *: e theta1.
  case: eqP=> [<-|Hij]; [rewrite scale1r | rewrite scale0r].
    case: (Wedderburn_is_id (pGroupG _) (socle_of_irr theta1))=> _ Hi Hj _.
    by exact: Hj.
  move/eqP: Hij=> HH; apply: (Wedderburn_mulmx0 HH); exact: Wedderburn_id_mem.
have F2: #|G|%:R^-1 * theta1 1%g * theta2 1%g != 0.
  by do 2 (apply: mulf_neq0; last by exact: irr1_neq0).
apply: (mulIf F2).
pose r1 (u: 'M[algC]_#|<<G>>|) := gring_row u 0 (gring_index <<G>> 1%g).
apply: (@etrans _ _ (r1 (e theta1 *m e theta2))); last first.
  rewrite F1 /=; case: eqP=> [->|_].
    by rewrite scale1r mul1r /r1 gring_row_e !mxE gring_indexK // invg1.
  rewrite scale0r mul0r /r1.
  suff->: @gring_row algC _ <<G>> 0 = 0 by rewrite mxE.
  by apply/rowP=> k; rewrite !mxE.
pose gr i g := gring_row (e i) 0 (gring_index <<G>> g). 
suff->:
    r1 (e theta1 *m e theta2) = \sum_(g \in G) gr theta1 g * gr theta2 (g^-1)%g.
  rewrite -mulr_sumr -mulr_suml.
  apply: eq_big=> [g|i1]; first by rewrite /= groupV.
  have HH: forall (n : nat) (rG : mx_representation algC <<G>> n) (g : gT),
       char_of_repr <<G>> rG (g^-1)%g = (char_of_repr <<G>> rG g)^*.
    by rewrite genGid; exact: char_inv.
  move=> Hi1.
  rewrite  /gr {1}gring_row_e {1}gring_row_e !mxE !gring_indexK 
           // ?genGidG // -1?groupV //.
  (* mimicking ring *)
  rewrite invgK; rewrite -!mulrA; congr (_ * _).
  apply: sym_equal; rewrite mulrC -!mulrA; congr (_ * _).
  have->: (theta2 (i1^-1)%g)^* = theta2 i1.
    by rewrite HH conjCK.
  apply: sym_equal; rewrite [theta2 _ * _]mulrC -!mulrA; congr (_ * _).
  by rewrite mulrC -!mulrA; congr (_ * _).
rewrite (eq_bigl (fun g => g \in <<G>>)); last first.
  by rewrite genGid.
rewrite /r1 gring_row_mul.
have F3: (e theta2 \in group_ring algC <<G>>)%MS.
  apply (submx_trans (Wedderburn_id_mem _)).
  by rewrite /Wedderburn_subring genmxE submxMl.
rewrite -{1}(gring_rowK F3) mxE.
  (* This takes ages
rewrite {1}(reindex (@enum_val _ (fun x=> x \in G))) /=; last first.
  *)
rewrite {1}(@reindex _ _ (GRing.add_comoid algC) _ _
     (@enum_val _ (fun x=> x \in <<G>>))) /=; last first.
  by exists (gring_index <<G>>)=> g Hg;
        [exact: gring_valK | apply: gring_indexK].
apply: eq_big=> [g|i1 _]; first by rewrite enum_valP.
rewrite  /gr !gring_valK; congr (_ * _).
rewrite 2!mxE.
  (* This takes ages
rewrite {1}(@bigD1 (gring_index G (enum_val i1)^-1)) //=.
  *)
rewrite {1}(@bigD1 _ _  (GRing.add_comoid algC) _ 
                        (gring_index <<G>> (enum_val i1)^-1)) //=.
set u := gring_row _ _ _ .
rewrite {1}big1 ?addr0.
  rewrite !(mxE,mxvecE) gring_indexK; last by rewrite groupV enum_valP.
  by rewrite mulgV !eqxx mulr1.
move=> i2 Hi2.
rewrite !(mxE,mxvecE).
case: (gring_index <<G>> 1 =P _); last by rewrite andbF mulr0.
move=> HH; case/negP: Hi2.
have F5: (enum_val i1 * enum_val i2)%g \in <<G>>.
  by apply: groupM; exact: enum_valP.
rewrite -[_^-1%g]mulg1.
rewrite (can_in_inj (@gring_indexK _ <<G>>) (group1 <<G>>) F5 HH).
by rewrite mulgA mulVg mul1g gring_valK.
Qed.

Lemma irr_second_orthogonal_relation : forall (g h: gT), 
 g \in G -> h \in G ->
 \sum_(theta : irr G) theta g * (theta h)^* =
   if g \in (h ^: G) then #|'C_G[h]|%:R else 0.
Proof.
move=> g h GiG HiG.
have F0: forall j, (j < #|irr G| -> j < #|classes G|)%N 
  by move=> j; rewrite card_irr.
pose x i := Ordinal (F0 _ (ltn_ord i)).
have G0: forall j, (j < #|classes G| -> j < #|irr G|)%N 
  by move=> j1; rewrite card_irr.
pose y i := Ordinal (G0 _ (ltn_ord i)).
have XY: forall i, x (y i) = i by move=> i; apply/val_eqP.
have YX: forall i, y (x i) = i by move=> i; apply/val_eqP.
pose X := \matrix_(i < #|irr G|, j < #|irr G|) 
  ((enum_val i) (repr (enum_val (x j)))).
pose Y := \matrix_(i < #|irr G|, j < #|irr G|) 
  let C := enum_val (x i) in #|C|%:R * (#|G|%:R^-1 * (enum_val j) (repr C))^*.
have HH: forall (n : nat) (rG : mx_representation algC <<G>> n) (g : gT),
     char_of_repr <<G>> rG (g^-1)%g = (char_of_repr <<G>> rG g)^*.
  by rewrite genGid; exact: char_inv.
have F2: X *m Y = 1%:M.
  apply/matrixP=> i j; rewrite !mxE.
  have->: (i == j) = (enum_val i == enum_val j).
    by apply/eqP/eqP; [move-> | exact: enum_val_inj].
  rewrite -irr_first_orthogonal_relation -mulr_sumr cfun_sum; last first.
    move=> g1 g2 Hg1 Hg2.
    by rewrite -!HH  -conjVg  !(cfunJ (char_of_repr_in_cfun _)) 
                ?(groupV,genGidG).
  rewrite (reindex y) /=; last by apply: onW_bij; exists x=> i1; apply/val_eqP.
  rewrite (reindex (@enum_val _ (fun x => x \in classes G))) /=; last first.
    by apply: (enum_val_bij_in (mem_classes (group1 G))).
  apply: eq_big=> [i1|i1 _]; first by rewrite enum_valP.
  rewrite !mxE /= XY.
  (* mimicking ring *)
  rewrite mulrC -!mulrA; congr (_ * _).
  rewrite rmorphM fmorphV ?conjC_nat //.
  by rewrite -mulrA [enum_val i _ * _]mulrC.
have Hi1: #|h ^: G|%:R != 0 :> algC.
  by rewrite -neq0N_neqC (cardsD1 h) class_refl.
apply: (mulfI (mulf_neq0 Hi1 card_neq0)); rewrite -mulr_sumr.
apply: (@etrans _ _ (g \in h ^: G)%:R); last first.
  case: (boolP (_ \in _))=> [Hin|]; last by rewrite mulr0.
  rewrite -(LaGrange (subcent1_sub h G)) index_cent1.
  rewrite mulrC mulrA natr_mul divff //.
  apply: mulf_neq0=> //.
  by rewrite -neq0N_neqC (cardsD1 h) (subcent1_id HiG).
move/mulmx1C: F2.
pose toC x := enum_rank_in (classes1 G) (x ^: G).
move/matrixP; move/(_ (y (toC h)) (y (toC g))).
rewrite !mxE.
have<-:  (y (toC h) == y (toC g)) = (g \in h ^: G)=> [|<-].
  apply/eqP/idP=> [|Hin]; last by rewrite /toC (class_transr Hin).
  move/(can_inj XY).
  move/(can_in_inj (enum_rankK_in (classes1 G)) 
         (mem_classes HiG) (mem_classes GiG))->.
  exact: class_refl.
rewrite (reindex (fun i: irr G => enum_rank i)); last first.
  by apply: onW_bij; apply: enum_rank_bij.
apply: eq_bigr=> t _.
rewrite !mxE /= !XY  /toC !enum_rankK !enum_rankK_in ?mem_classes //.
case: (repr_class G g)=> g1 Hg1->.
case: (repr_class G h)=> h1 Hh1->.
rewrite !(cfunJ (char_of_repr_in_cfun _)) ?genGidG //.
rewrite -!mulrA; congr (_ * _).
by rewrite rmorphM fmorphV ?conjC_nat // -mulrA [t _ * _]mulrC.
Qed.

Lemma irr_conjugate : forall (g h: gT), g \in G -> h \in G ->
  reflect (forall theta : irr G, theta g = theta h) (g \in (h ^: G)).
Proof.
move=> g h GiG HiG; apply: (iffP idP)=> [HH chi|HH].
  case/imsetP: HH=> x Hx ->.
  by rewrite (cfunJ (irr_in_cfun _)).
move: (irr_second_orthogonal_relation GiG HiG); case: (_ \in _)=> // HH1.
move: (fun I=> posC_sum_eq0 I HH1).
have F1:  forall chi : irr G, 
  (chi \in index_enum (irr_finType G)) && xpredT chi -> 
     0 <= chi g * (chi h)^*.
  by move=> chi _; rewrite HH /leC subr0 repC_pconj.
case/eqP: (nonzero1r algC).
move: (posC_sum_eq0 F1 HH1); move/(_ (irr1 G)).
rewrite !irr1E GiG HiG conjC1 mul1r; apply=> //.
by rewrite  /index_enum -enumT mem_enum.
Qed.

(* This corresponds to Isaacs' 6.32 *)
Lemma action_irr_class_card : 
  forall (ito : action A (irr G))  (cto : action A {set gT}) a,
    a \in A -> [acts A, on (classes G) | cto] -> 
   (forall c (theta : irr G),
       c \in classes G -> theta (repr c) = ito theta a (repr (cto c a))) ->
     #|'Fix_ito[a]| = #|'Fix_(classes G| cto)[a]|.
Proof.
move=> ito cto a AiA Acto H.
 (* borrowed to the second orthogonality proof *)
have F0: forall j, (j < #|irr G| -> j < #|classes G|)%N 
  by move=> j; rewrite card_irr.
pose f i := Ordinal (F0 _ (ltn_ord i)).
have G0: forall j, (j < #|classes G| -> j < #|irr G|)%N 
  by move=> j1; rewrite card_irr.
pose g i := Ordinal (G0 _ (ltn_ord i)).
have FG: forall i, f (g i) = i by move=> i; apply/val_eqP.
have GF: forall i, g (f i) = i by move=> i; apply/val_eqP.
pose X := \matrix_(i < #|irr G|, j < #|irr G|) 
  ((enum_val i) (repr (enum_val (f j)))).
pose Y := \matrix_(i < #|irr G|, j < #|irr G|) 
  (let C := enum_val (f i) in #|C|%:R * (#|G|%:R^-1 * (enum_val j) (repr C))^*).
have Hc: forall (n : nat) (rG : mx_representation algC <<G>> n) (g : gT),
     char_of_repr <<G>> rG (g^-1)%g = (char_of_repr <<G>> rG g)^*.
  by rewrite genGid; exact: char_inv.
have F2: X *m Y = 1%:M.
  apply/matrixP=> i j; rewrite !mxE.
  have->: (i == j) = (enum_val i == enum_val j).
    by apply/eqP/eqP; [move-> | exact: enum_val_inj].
  rewrite -irr_first_orthogonal_relation -mulr_sumr cfun_sum; last first.
    move=> g1 g2 Hg1 Hg2.
    by rewrite -!Hc -conjVg !(cfunJ (irr_in_cfun _)) ?groupV.
  rewrite (reindex g) /=; last by apply: onW_bij; exists f=> i1; apply/val_eqP.
  rewrite (reindex (@enum_val _ (fun x => x \in classes G))) /=; last first.
    by apply: (enum_val_bij_in (mem_classes (group1 G))).
  apply: eq_big=> [i1|i1 _]; first by rewrite enum_valP.
  rewrite !mxE /= FG mulrC -!mulrA; congr (_ * _).
  by rewrite rmorphM fmorphV ?conjC_nat // -mulrA [enum_val i _ * _]mulrC.
 (****************************************)
pose Pa : 'M[algC]_ _ := 
  \matrix_(i < #|irr G|, j < #|irr G|) (ito (enum_val i) a == (enum_val j))%:R.
apply/eqP; rewrite eqN_eqC.
have <-: \tr Pa = #|'Fix_ito[a]|%:R.
  rewrite /mxtrace (bigID (fun u => (enum_val u) \in 'Fix_ito[a])) /=.
  rewrite (eq_bigr (fun u => 1%:R)); last first.
    move=> i; rewrite inE mxE; move/subsetP=> Hi.
    case: eqP=> // Hv; case: Hv; apply/eqP.
    by move: (Hi a); rewrite !inE; apply.
  rewrite sumr_const big1 ?addr0; last first.
    move=> i; rewrite inE mxE; move/subsetP=> Hi.
    by case: eqP=> // Hv; case: Hi=> b; rewrite !inE; move/eqP->; rewrite Hv.
  rewrite -mulr_natl mulr1 /= -(card_imset  (pred_of_set 'Fix_ito[a]) (@enum_rank_inj _)).
  apply/eqP; rewrite -eqN_eqC; apply/eqP; apply: eq_card=> i.
  apply/idP/imsetP; first by move=> j; exists (enum_val i)=> //; rewrite enum_valK.
  by case=> j Hj ->; rewrite /in_mem /= enum_rankK.
pose Qa : 'M[algC]_ _ := 
  \matrix_(i < #|irr G|, j < #|irr G|) (cto (enum_val (f i)) a == (enum_val (f j)))%:R.
have <-: \tr Qa = #|'Fix_(classes G | cto)[a]|%:R.
  rewrite /mxtrace (bigID (fun u => (enum_val (f u)) \in 'Fix_(classes G | cto)[a])) /=.
  rewrite (eq_bigr (fun u => 1%:R)); last first.
    move=> i; rewrite !inE !mxE; case/andP=> H1i; move/subsetP=> H2i.
    case: eqP=> // Hv; case: Hv; apply/eqP.
    by move: (H2i a); rewrite !inE; apply.
  rewrite sumr_const big1 ?addr0; last first.
    move=> i; rewrite !inE !mxE => Hi.
    case: eqP=> //; move/eqP=> Hv; case/negP: Hi; rewrite enum_valP.
    by apply/subsetP=> b; rewrite !inE; move/eqP->.
  rewrite -mulr_natl mulr1 /=.
  have F1: injective (enum_val \o f).
    by move=> i j; move/enum_val_inj; move/val_eqP=> HH; apply/eqP.
  rewrite -(card_imset _ F1).
  apply/eqP; rewrite -eqN_eqC; apply/eqP; apply: eq_card=> i.
  apply/imsetP/idP; first by case=> j Hj ->.
  move=> Hi; move: (Hi); rewrite inE; case/andP=> H1i _.
  by exists (g (enum_rank_in (classes1 _) i));  rewrite /in_mem /= FG enum_rankK_in.
have F3: X \in unitmx by case/mulmx1_unit: F2.
suff->: Qa = invmx X *m Pa *m X.
  rewrite mxtrace_mulC mulmxA mulmxV ?mul1mx //.
rewrite -[Qa]mul1mx -(mulVmx F3) -!mulmxA; congr (_ *m _).
apply/matrixP=> u v; rewrite !mxE.
have [oti H1o H2o]: bijective (ito ^~a).
  apply: injF_bij; apply: act_inj.
have [otc H1co H2co]: bijective (cto ^~a).
  apply: injF_bij; apply: act_inj.
have Hv : otc (enum_val (f v)) \in classes G.
  by rewrite -(acts_act Acto AiA) H2co enum_valP.
pose i1 := enum_rank (ito (enum_val u) a). 
have Hi1: ito (enum_val u) a = enum_val i1 by rewrite enum_rankK.
pose j1 := g (enum_rank_in (classes1 G) (otc (enum_val (f v)))).
have Hj1: cto (enum_val (f j1)) a = enum_val (f v).
  by rewrite FG enum_rankK_in ?H2co.
rewrite (bigD1 j1) // big1 /= ?addr0 => [|i Dii1]; last first.
  rewrite !mxE; case: eqP; rewrite ?mulr0 // -Hj1.
  by move/(can_inj H1co); move/enum_val_inj; move/val_eqP=> /==> HH; case/negP: Dii1.
 (* too slow ! 
rewrite (bigD1 i1) // big1 /= ?addr0=> [|i Dii1]; last first.
 *)
 have->: \sum_(j < #|irr G|) Pa u j * X j v = Pa u i1 * X i1 v.
  rewrite {1}(bigD1 i1) // big1 /= ?addr0=> [|i Dii1] //.
  rewrite !mxE; case: eqP; rewrite ?mul0r // Hi1.
  by move/enum_val_inj=> HH; case/eqP: Dii1.
rewrite !mxE Hi1 Hj1 !(eqxx, mulr1, mul1r).
by rewrite H FG enum_rankK_in // H2co  enum_rankK.
Qed.

End OrthogonalRelations.

Section InnerProduct.

Variable (gT : finGroupType) (G : {group gT}).

Let card_neq0 : #|G|%:R^-1 != 0 :> algC.
Proof. by rewrite invr_eq0 neq0GC. Qed.

Definition inner_prod (G : {set gT}) (f g : cfun _ _) :=
  #|G|%:R^-1 * \sum_(i \in G) f i * (g i)^*.

Local Notation "'[ u , v  ]_ G":=  (inner_prod G u v) (at level 10).

Lemma inner_prodE: forall (f g : cfun _ _),
  '[f,g]_G = #|G|%:R^-1 * \sum_(i \in G) f i * (g i)^*.
Proof. by []. Qed.

Let card_conj : (#|G|%:R^-1)^* = #|G|%:R^-1.
Proof. by rewrite posC_conjK // posC_inv posC_nat. Qed.

Lemma inner_conj : forall f g, '[f,g]_G = ('[g,f]_G)^*.
Proof.
move=> f g; rewrite /inner_prod rmorphM card_conj.
congr (_ * _); rewrite rmorph_sum; apply: eq_bigr=> i _.
by rewrite rmorphM conjCK mulrC.
Qed.
 
Lemma posC_inner_prod : forall f, 0 <= '[f, f]_G.
Proof. 
move=> f; apply: posC_mul; first by rewrite posC_inv posC_nat.
by rewrite posC_sum // => i _; rewrite /leC subr0 repC_pconj.
Qed.

Lemma inner_prod0l : forall f, '[0,f]_G = 0.
Proof.
move=> f.
rewrite inner_prodE big1 ?mulr0 // => i.
by rewrite cfunE mul0r.
Qed.

Lemma inner_prod0r : forall f, '[f,0]_G = 0.
Proof.
move=> f.
rewrite inner_prodE big1 ?mulr0 // => i.
by rewrite cfunE conjC0 mulr0.
Qed.

Lemma inner_prod0 : forall f : cfun _ _, 
  f \in 'CF(G) -> ('[f, f]_G == 0) = (f == 0).
Proof.
rewrite /=.
move=> f Hf; apply/eqP/eqP=> Hp; last first.
  by rewrite Hp /inner_prod big1 ?mulr0 // => i _; rewrite !cfunE mul0r.
apply/cfunP=> g; rewrite cfunE.
case: (boolP (g \in G))=> Hin; last by rewrite (cfun0 Hf).
suff: f g * (f g)^* == 0.
  by rewrite mulf_eq0; case/orP; [move/eqP|rewrite conjC_eq0;move/eqP].
move: Hp; move/eqP; rewrite /inner_prod mulf_eq0; case/orP=> [|Hp].
  by rewrite (negPf card_neq0).
apply/eqP; apply: (posC_sum_eq0 _ (eqP Hp))=> //.
 by move=>*; rewrite -sqrtC_pos; exact: posC_norm.
by rewrite /index_enum -enumT mem_enum.
Qed.

Definition inner_prodb f := (@inner_prod G)^~ f.

Lemma inner_prodbE : forall f g, inner_prodb f g = inner_prod G g f.
Proof. by []. Qed.

Lemma inner_prodb_is_linear : forall f, linear (inner_prodb f : _ -> algC^o).
Proof.
move=> f k g1 g2.
rewrite /inner_prodb /inner_prod.
rewrite {1}scaler_mulr -{1}scaler_addr; congr (_ * _).
rewrite {1}scaler_sumr /= -{1}big_split /=; apply: eq_bigr=> i _.
by rewrite scaler_mull -mulr_addl !cfunE.
Qed.

Canonical Structure inner_prodb_linear f :=
  Linear (inner_prodb_is_linear f).

Lemma inner_prod_is_additive : forall f, additive (inner_prod G f).
Proof.
move=> f g1 g2.
rewrite /inner_prod /inner_prod.
rewrite -mulr_subr; congr (_ * _).
rewrite -sumr_sub; apply: eq_bigr=> i _.
by rewrite !cfunE rmorph_sub // mulr_subr.
Qed.

Canonical Structure inner_prod_additive f := 
  Additive (inner_prod_is_additive f).

Lemma inner_prodZ : forall k f g, '[f, k *: g]_G = k^* * '[f,g]_G.
Proof.
move=> k f g; rewrite /inner_prod.
rewrite mulrCA; congr (_ * _).
rewrite -mulr_sumr; apply: eq_bigr=> i _.
by rewrite !cfunE rmorphM mulrCA.
Qed.

Lemma irr_orthonormal : forall (theta1 theta2: irr G),
   '[theta1,theta2]_G = (theta1 == theta2)%:R.
Proof. by move=> *; rewrite -irr_first_orthogonal_relation. Qed.

Lemma ncoord_inner_prod : forall (f : cfun _ _) (theta : irr G),
   f \in 'CF(G) -> ncoord theta f = '[f,theta]_G.
Proof.
move=> f theta FiC.
rewrite {2}(ncoord_sum FiC) -inner_prodbE linear_sum.
by rewrite (bigD1 theta) // big1=> [|j Hj]; 
   rewrite /= ?addr0 linearZ /= inner_prodbE irr_orthonormal;
    [rewrite eqxx /GRing.scale /= mulr1|rewrite (negPf Hj) scaler0].
Qed.

Lemma inner_prod_char : forall chi1 chi2,  
  is_char G chi1 -> is_char G chi2 ->
   '[chi1,chi2]_G = 
       \sum_(theta : irr G) (ncoord theta chi1) * (ncoord theta chi2).
Proof.
move=> chi1 chi2 IC1 IC2.
move/is_char_in_cfun: (IC1); case/(ncoord_sum)=> HH1; rewrite {1}HH1.
move/is_char_in_cfun: (IC2); case/(ncoord_sum)=> HH2; rewrite {1}HH2.
rewrite -inner_prodbE {1}linear_sum /=.
apply: eq_bigr=> t _; rewrite linearZ /= inner_prodbE.
rewrite raddf_sum  {1}(bigD1 t) // big1 //= ?addr0 => [|j Hj]; last first.
  by rewrite inner_prodZ irr_orthonormal eq_sym (negPf Hj) mulr0.
congr (_ * _); rewrite inner_prodZ irr_orthonormal eqxx mulr1.
case/isNatCP: (isNatC_ncoord_char t IC2)=> n ->.
by rewrite conjC_nat.
Qed.

Lemma inner_prod_char_nat : forall ch1 ch2,
  is_char G ch1 -> is_char G ch2 -> isNatC ('[ch1,ch2]_G).
Proof.
move=> ch1 ch2 IC1 IC2; rewrite inner_prod_char //.
by apply: isNatC_sum=> i _; apply: isNatC_mul; apply: isNatC_ncoord_char.
Qed.
 
Lemma inner_prod_charC : forall chi1 chi2,
    is_char G chi1 -> is_char G chi2 -> '[chi1,chi2]_G = '[chi2,chi1]_G.
Proof.
move=> chi1 chi2 IC1 IC2.
by rewrite !inner_prod_char //; apply: eq_bigr=> i _; rewrite mulrC.
Qed.

Lemma is_irr_inner_prod_charE : forall chi,
  is_char G chi -> is_irr G chi = ('[chi, chi]_G == 1).
Proof.
move=> chi IC; apply/is_irrP/eqP=> [[theta ->]|].
  by rewrite irr_orthonormal eqxx.
rewrite inner_prod_char //.
case/is_char_cbP: (IC)=> n Hchi HH.
case: (isNatC_sum_eq1 _ _ HH).
- move=> theta _; apply: isNatC_mul;
     rewrite Hchi linear_sum isNatC_sum //= => j _; rewrite linearZ /= ?ncoord_irr;
       apply: isNatC_mul; apply: isNatC_nat.
- by rewrite /index_enum -enumT; exact: enum_uniq.
move=> t [Htn _ HF HG]; exists t.
apply/val_eqP=> /=; apply/eqP.
rewrite (ncoord_sum (is_char_in_cfun IC)).
rewrite (bigD1 t) //= big1 ?addr0=> [|t' Ht']; last first.
  have F1: t' \in index_enum (irr_finType G).
    rewrite /index_enum -enumT.
    apply/(nthP (irr1 G)); exists (enum_rank t')=> //.
      case: enum_rank=> /= m; first by rewrite cardT /=.
    by apply/val_eqP; rewrite nth_enum_rank.
  move: (HG _ Ht' F1 is_true_true); move/eqP; rewrite mulf_eq0.
  by case/orP; rewrite Hchi; move/eqP->; rewrite scale0r.
case/isNatCP: (isNatC_ncoord_char t IC) HF=> m ->; move/eqP=> HH1; apply/eqP.
move: HH1; rewrite -natr_mul -(eqN_eqC _ 1); case: m=> //; case => //.
by rewrite scale1r.
Qed.

Lemma cfun_conjC_inner : forall f1 f2 : cfun gT algC,
 ('[f1^*,f2^*]_G)%CH = ('[f1,f2]_G)^*.
Proof.
move=> f1 f2; rewrite !inner_prodE rmorphM conjC_inv conjC_nat.
congr (_ * _); rewrite (big_morph _ (rmorphD conjC) conjC0); apply: eq_bigr.
by move=> g GiG; rewrite !cfunE rmorphM.
Qed.

Lemma is_irr_conjC : forall (theta : irr G),  is_irr G (theta^*)%CH.
Proof.
move=> theta; rewrite is_irr_inner_prod_charE; last first.
  by apply: is_char_conjC; exact: is_char_irr.
rewrite cfun_conjC_inner.
rewrite -conjC1; apply/eqP; congr (_^*); apply/eqP.
by rewrite -is_irr_inner_prod_charE ?(is_irr_irr, is_char_irr).
Qed.
 
Definition irr_conjC (G : {group gT}) (theta : irr G) := 
  get_irr G (theta^*)%CH.

Lemma irr_conjCE : forall theta : irr G,
  irr_conjC theta = (theta^*)%CH :> cfun _ _.
Proof. by move=> i; rewrite get_irrE // is_irr_conjC. Qed.

Lemma irr_conjCK : involutive (@irr_conjC G).
Proof.
by move=> i; apply: cfun_of_irr_inj; rewrite !irr_conjCE cfun_conjCK.
Qed.


End InnerProduct.

Notation "'[ u , v  ]_ G":=  (inner_prod G u v) (at level 10).

Section MoreInnerProd.

Variable gT : finGroupType.

Lemma is_comp_inner_prod_le : 
  forall (G  H : {group gT}) (theta : irr H) (chi : irr G) psi,
  is_char G psi -> H \subset G -> is_comp chi psi -> 
    '['Res[H] chi, theta]_H <= '['Res[H] psi, theta]_H.
Proof.
move=> G H theta chi psi IC HsG.
case/(is_comp_charP _ IC)=> chi' IC' ->.
rewrite linearD -!inner_prodbE linearD /= !inner_prodbE.
rewrite addrC -leC_sub addrK.
apply: posC_isNatC.
rewrite -ncoord_inner_prod.
  apply: isNatC_ncoord_char.
  by apply: (is_char_restrict HsG).
apply: (crestrict_in_cfun HsG).
by apply: is_char_in_cfun.
Qed.

Lemma is_comp_restrict :
  forall (G H : {group gT}) (theta : irr H) (chi : irr G) psi,
    is_char G psi -> H \subset G -> is_comp chi psi -> 
    is_comp theta ('Res[H] chi) -> is_comp theta ('Res[H] psi).
Proof.
move=> G H theta chi psi IC HsG Cchi Ctheta.
have CC := is_comp_inner_prod_le theta IC HsG Cchi.
rewrite is_compE ncoord_inner_prod; last first.
  by apply: (crestrict_in_cfun HsG); exact: is_char_in_cfun.
have CF1 : 'Res[H] chi \in 'CF(H).
  by apply: (crestrict_in_cfun HsG); exact: irr_in_cfun.
apply/negP=> HH.
move: Ctheta.
rewrite is_compE ncoord_inner_prod //.
case/eqP; apply: leC_anti; first by rewrite -(eqP HH) //.
rewrite -ncoord_inner_prod // posC_isNatC // isNatC_ncoord_char //.
by apply: is_char_restrict (is_char_irr _).
Qed.

End MoreInnerProd.

Section Kernel.

Variable (gT : finGroupType) (G : {group gT}).

Definition cker (G : {set gT}) (f : cfun gT algC) := 
  if is_char <<G>> f then [set g \in G | f g == f 1%g] else 1%G.

Lemma cker_charE : forall f,
   is_char G f -> cker G f = [set g \in G | f g == f 1%g].
Proof. by move=> f Hf; rewrite /cker genGid Hf. Qed.

Lemma cker_char1: forall chi g,
  g \in cker G chi -> chi g = chi 1%g.
Proof.
move=> chi g.
rewrite /cker genGid; case: (boolP (is_char G chi))=> [IC|_]; last first.
  by move/set1gP->.
by rewrite inE; case/andP=> _; move/eqP.
Qed.

Lemma cker_irrE : forall (theta : irr G),
  cker G theta = [set g \in G | theta g == theta 1%g].
Proof.  by move=> t; rewrite /cker genGid is_char_irr. Qed.

Lemma cker_NcharE : forall f, ~is_char G f -> cker G f = 1%G.
Proof. by move=> f Hf; rewrite /cker genGid; move/eqP: Hf; case: is_char. Qed.

Definition cfaithful (G : {set gT}) f := cker G f \subset 1%G.

Lemma cfaithful_reg : cfaithful G (reg_cfun G).
Proof.
apply/subsetP=> g.
rewrite cker_charE ?is_char_reg //.
rewrite !inE !reg_cfunE eqxx.
case E1: (g == 1%g); first by move/eqP: E1->; rewrite group1 eqxx.
by rewrite eq_sym (negPf (neq0GC G)) andbF.
Qed.

Lemma ckerE : forall chi,
  is_char G chi -> 
  cker G chi = if chi == 0 then (G : {set _}) else
               \bigcap_(theta : irr G | is_comp theta chi) cker G theta.
Proof.
move=> chi IC; rewrite cker_charE //.
case: eqP=> [->|].
  by apply/setP=> g; rewrite !inE !cfunE eqxx andbT.
have NS := ncoord_sum (is_char_in_cfun IC).
move/eqP=> Hdc; apply/setP=> g; apply/idP/bigcapP=> [|Hi]; last first.
  have InG: g \in G.
    case/(is_comp_neq0 (is_char_in_cfun IC)): Hdc=> j; move/(Hi _).
    by rewrite cker_irrE // inE; case/andP.
  rewrite inE /= NS.
  rewrite !sum_cfunE !cfunE InG.
  apply/eqP; apply: eq_bigr=> i _; rewrite cfunE [_ 1%g]cfunE.
  case: (boolP (is_comp i chi))=> [Hc|].
    by move: (Hi _ Hc); rewrite cker_irrE // inE InG /=; move/eqP->.
  by rewrite negbK; move/eqP->; rewrite !mul0r.
rewrite inE; case/andP=> InG.
rewrite NS !sum_cfunE !cfunE.
move/eqP=> Hs t; rewrite cker_irrE // !inE InG.
have->:
   cfun_of_fun (fun x : gT => 
                  \sum_(t:irr G) (ncoord t chi *: (t : cfun _ _)) x) = chi.
  by apply/cfunP=> x; rewrite cfunE {2}NS sum_cfunE cfunE.
move=> Hd.
have F: (ncoord t chi *: (t : cfun _ _)) g = 
            (ncoord t chi *: (t : cfun _ _)) 1%g.
  have F1: 0 <= ncoord t chi by apply: posC_isNatC; rewrite isNatC_ncoord_char.
  apply: (normC_sum_upper _ Hs)=> [t' Ht'|]; last first.
    by rewrite /index_enum -enumT mem_enum.
  have F2: 0 <= ncoord t' chi
    by apply: posC_isNatC; rewrite isNatC_ncoord_char.
  rewrite cfunE [(ncoord t' chi *: (t' : cfun _ _)) 1%g]cfunE !normC_mul //.
  rewrite normC_pos // leC_mul2l //.
  by apply: char_norm (is_char_irr _).
apply/eqP; apply: (mulfI Hd).
by move: F; rewrite cfunE => ->; rewrite !cfunE.
Qed. 

Lemma cker_all1 : \bigcap_(theta : irr G) cker G theta = 1%G.
Proof.
apply/setP=> g; apply/idP/idP; rewrite inE; last first.
  move/eqP->; apply/bigcapP=> i _.
  by rewrite cker_irrE // inE group1 eqxx.
have F1: (\bigcap_(theta : irr G) cker G theta) \subset cker G (reg_cfun G).
  rewrite ckerE ?is_char_reg //.
  case: eqP=> Heq.
    have: reg_cfun G 1%g = 0 by rewrite Heq cfunE.
    rewrite cfunE group1 repr_mx1 mxtrace1 mul1r.
    by move/eqP; rewrite (negPf (neq0GC G)).
  by apply/subsetP=> h; move/bigcapP=> Hi; apply/bigcapP=> j _; exact: Hi.
move/(subsetP F1); rewrite cker_charE ?is_char_reg //.
rewrite inE !reg_cfunE //.
case/andP=> InG; rewrite eqxx; case: (g == 1%g)=> //.
by rewrite eq_sym (negPf (neq0GC G)).
Qed.

Lemma is_comp_cker : forall (theta : irr G) chi,
  is_char G chi -> is_comp theta chi -> cker G chi \subset cker G theta.
Proof.
move=> theta chi IC HC.
rewrite ckerE //; case: eqP=> HH; last by apply: (bigcap_min theta).
by case/eqP: HC; rewrite HH ncoord0.
Qed.

End Kernel.

Section MoreKernel.

Variable (gT : finGroupType) (G : {group gT}).

Lemma char_rkerP : forall n (rG : mx_representation algC G n), 
  cker G (char_of_repr G rG) = rker rG.
Proof.
move=> n rG; rewrite /cker genGid ?is_char_char_of_repr //.
apply/setP=> g; apply/idP/rkerP=>[Hg |[H1 H2]]; last first.
  by rewrite inE !cfunE H1 H2 repr_mx1 !group1 mul1r mxtrace1 eqxx.
have InG: g \in G by move: Hg; rewrite inE; case/andP.
split=> //.
have F1: (<[g]> \subset G) by rewrite cycle_subG.
pose rG' := subg_repr rG F1.
have H'g: g \in cker <[g]> (char_of_repr <[g]> rG').
  move: Hg; rewrite /cker genGid ?is_char_char_of_repr //.
  by rewrite /rG' !inE !cfunE !group1 !InG cycle_id !mul1r.
suff: g \in rker rG' by rewrite inE mul1mx; case/andP=> _; move/eqP.
have Ing := cycle_id g.
apply/rkerP; split => //.
apply: (@clinear_cker_mx1 _ <[g]> _ rG')=> //.
  by apply/char_abelianP; exact: cycle_abelian.
by move: H'g; rewrite /cker genGid is_char_char_of_repr !inE Ing; move/eqP.
Qed.

Lemma cker_group_set : forall f, group_set (cker G f).
Proof.
move=> f; case: (boolP (is_char G f))=> Hf.
  case/is_charP: Hf=> n [rG <-].
  rewrite char_rkerP //.
  by exact: rstab_group_set.
rewrite cker_NcharE; last by move/negP: Hf.
by exact: group_set_one.
Qed.

Canonical Structure cker_group f := Group (cker_group_set f).

Lemma cker_normal : forall f, cker G f <| G.
Proof.
move=> f; case: (boolP (is_char G f))=> Hf.
  by case/is_charP: Hf=> n [rG <-]; rewrite char_rkerP // rker_normal.
rewrite cker_NcharE; last by move/negP: Hf.
by exact: normal1.
Qed.

Lemma cker_sub : forall f, cker G f \subset G.
Proof. by move=> f; apply: (normal_sub (cker_normal _)). Qed.

Lemma char_ckerMr : forall chi g h,
  is_char G chi -> g \in cker G chi -> h \in G -> chi (g * h)%g = chi h.
Proof.
move=> chi g h.
case/is_charP=> // n [rG <-] GiC HiG.
have GiG: g \in G.
  by apply: (subsetP (cker_sub (char_of_repr G rG))).
rewrite !cfunE groupM ?YiG // repr_mxM //.
move: GiC; rewrite char_rkerP // inE GiG mul1mx andTb; move/eqP->.
by rewrite HiG mul1mx.
Qed.

Lemma char_ckerMl : forall chi g h,
  is_char G chi -> g \in cker G chi -> h \in G -> chi (h * g)%g = chi h.
Proof.
move=> chi g h.
case/is_charP=> // n [rG <-] GiC HiG.
have GiG: g \in G by apply: (subsetP (cker_sub (char_of_repr G rG))).
rewrite !cfunE groupM ?YiG // repr_mxM //.
move: GiC; rewrite char_rkerP // inE GiG mul1mx andTb; move/eqP->.
by rewrite HiG mulmx1.
Qed.

Lemma clinear_commutator : forall f,
  clinear G f -> (G^`(1) \subset cker G f)%g.
Proof.
move=> f Cf; case/andP: (Cf); rewrite genGid=> F1 F2.
have->: cker G f = (cker_group f) by [].
rewrite gen_subG; apply/subsetP=> gh; case/imset2P=> g h InG InH ->.
rewrite /= /cker genGid F1 inE groupR ?(InG,InH) // commgEl.
rewrite !(clinearM Cf) ?(groupM, groupV) // !(clinearV Cf) //.
rewrite mulrCA mulrC mulrA mulVf ?(clinear_neq0 Cf) //.
by rewrite mul1r divff ?(clinear_neq0 Cf) // (eqP F2) eqxx.
Qed.

End MoreKernel.

Section Coset.

Variable (gT : finGroupType).

Implicit Type G : {group gT}.

Definition qfun_of_cfun (N: {set gT}) (f : cfun gT algC) :=
  cfun_of_fun (fun x : coset_of N => f (repr x)).

Local Notation "f '/' N" := (qfun_of_cfun N f) : character_scope.

Definition cfun_of_qfun (N: {set gT}) (f : cfun (coset_groupType N) algC) :=
  cfun_of_fun (fun x : gT => (x \in 'N(N))%:R * f (coset N x)).

Local Notation " f '^()'" := (cfun_of_qfun f) (at level 2) : character_scope.

Let repr_quo_fact1 : forall (G N: {group gT}) (M : coset_of N),
 N <| G -> (repr M \in G) = (M \in (G / N)%g).
Proof.
move=> G N M NN; rewrite -imset_coset; apply/idP/imsetP.
  by move=> InG; exists (repr M)=> //; rewrite coset_reprK.
case=> g Hg ->.
rewrite  val_coset ?(subsetP (normal_norm NN)) //.
suff: N :* g \subset G by move/subsetP=>-> //; apply: mem_repr_rcoset.
apply/subsetP=> x; case/rcosetP=> y Hy ->; apply: groupM=> //.
by apply: (subsetP (normal_sub NN)).
Qed.

Let repr_quo_fact2 : forall (G N: {group gT}) g,
 N <| G -> (g \in 'N(N)) && (coset N g \in (G/N)%g) = (g \in G).
Proof.
move=> G N g NN.
rewrite -imset_coset; apply/andP/idP=>[[HN]|HH]; last first.
  split; first by apply: (subsetP (normal_norm NN)).
  by apply/imsetP; exists g.
case/imsetP=> h InH.
have HH: h \in 'N(N) by apply: (subsetP (normal_norm NN)).
move/(rcoset_kercosetP HN HH); rewrite mem_rcoset=> InNM.
suff->: g = ((g * h^-1)*h)%g.
  by rewrite groupM // (subsetP (normal_sub NN)).
by rewrite -mulgA mulVg mulg1.
Qed.

Lemma is_char_qfunc : forall (G N : {group gT}) f,
  is_char G f -> N <| G -> N \subset cker G f -> is_char (G/N)%G (f / N)%CH.
Proof.
move=> G N f; case/is_charP=> // n [rG <-] HN HC.
move: (HC); rewrite char_rkerP=> HC' //.
pose rG' := quo_repr HC' (normal_norm HN).
suff->: (char_of_repr G rG / N)%CH = char_of_repr (G/N)%g rG'.
  by apply: is_char_char_of_repr; exact: coset_splitting_field.
by apply/cfunP=> M; rewrite !cfunE repr_quo_fact1.
Qed.

Lemma qfuncE : forall (G N : {group gT}) f x,
 is_char G f -> N <| G -> N \subset cker G f -> x \in G -> 
  (f / N)%CH (coset N x) = f x.
Proof.
move=> G N f x Cf NN  Ncker InG; rewrite !cfunE.
rewrite val_coset //; last by apply: (subsetP (normal_norm NN)).
case: repr_rcosetP=> y Hy.
by apply: (char_ckerMr Cf)=> //; apply: (subsetP Ncker).
Qed.

Lemma cfunqE : forall (N : {group gT}) f x,
 x \in 'N(N) -> (f ^())%CH x = f (coset N x).
Proof. by move=> N f x InG; rewrite !cfunE InG // mul1r. Qed.

Lemma is_char_cfunq : forall (G N : {group gT}) f,
  N <| G -> is_char (G/N)%G f -> is_char G (f^())%CH.
Proof.
move=> G N f NN; case/is_charP=> n [rG <-].
pose rG' := coset_repr rG NN.
suff->: ((char_of_repr (G/N)%g rG)^())%CH = char_of_repr G rG' 
  by apply: is_char_char_of_repr.
apply/cfunP=> M; rewrite !cfunE mulrA -natr_mul mulnb.
rewrite repr_quo_fact2 //.
Qed.

(* We could do better *)
Lemma cker_cfunq : forall (G N : {group gT}) f,
 is_char (G/N)%G f -> N <| G -> N \subset cker G (f^())%CH.
Proof.
move=> G N f Cf HN.
have F1: is_char G (f^())%CH by apply: is_char_cfunq.
apply/subsetP=> g Hg.
have GiG: g \in G by apply: (subsetP (normal_sub HN)).
rewrite /cker genGid F1 inE GiG !cfunqE ?group1 //.
- by rewrite !coset_id // eqxx.
by apply: (subsetP (normal_norm HN)).
Qed.

Lemma cfunq_id : forall (G N : {group gT}) f,
 is_char (G/N)%G f -> N <| G -> (f^()/ N)%CH = f.
Proof.
move=> G N f Cf HN.
have F1: is_char G (f^())%CH by apply: is_char_cfunq.
have F2:= cker_cfunq Cf HN.
have F3: is_char (G/N)%G (f^() / N)%CH by apply: is_char_qfunc.
apply/cfunP=> x.
case: (boolP (x \in (G/N)%g))=> [|InG]; last first.
  rewrite (cfun0 (is_char_in_cfun Cf)) //.
  by apply: (cfun0 (is_char_in_cfun F3)).
rewrite -imset_coset; case/imsetP=> y InG ->.
rewrite (@qfuncE G) //  cfunqE //.
by apply: (subsetP (normal_norm HN)).
Qed.

Lemma qfunc_id : forall (G N : {group gT}) f,
 is_char G f -> N <| G -> N \subset cker G f -> ((f/N)^())%CH = f.
Proof.
move=> G N f Cf HN Hc.
have F1: is_char (G/N)%G (f/N)%CH by apply: is_char_qfunc.
have F2: is_char G ((f/N)^())%CH by apply: is_char_cfunq.
apply/cfunP=> x.
case: (boolP (x \in G))=> InG; last first.
  rewrite (cfun0 (is_char_in_cfun Cf)) //.
  apply: (cfun0 (is_char_in_cfun F2))=> //.
rewrite cfunqE ?(@qfuncE G) //.
by apply: (subsetP (normal_norm HN)).
Qed.

Lemma qfunc_irr : forall (G N : {group gT}) (theta : irr G),
 N <| G -> N \subset cker G theta -> is_irr (G/N)%G (theta/N)%CH.
Proof.
move=> G N theta.
case: (irr_reprE theta)=> i -> NnG.
rewrite char_rkerP=> Cf.
pose rG := quo_repr Cf (normal_norm NnG).
apply/is_irr_reprP.
pose sG := DecSocleType (regular_repr algC (G/N)%G).
exists (irr_comp sG rG).
apply/cfunP=> x.
have F1: mx_irreducible rG.
  by apply/quo_mx_irr=> //; apply: socle_irr.
have F2: ([char algC]^').-group (G / N)%G.
  by apply: sub_pgroup (pgroup_pi _)=> i' _; rewrite inE /= Cchar.
move/(rsim_irr_comp sG F2): F1.
move/char_of_repr_rsimP; move/eqP<-.
by rewrite /rG !cfunE repr_quo_fact1.
Qed.

Lemma cfunq_irr : forall (G N : {group gT}) (theta : irr (G/N)%G),
 N <| G ->  is_irr G (theta^())%CH.
Proof.
move=> G N theta; case: (irr_reprE theta)=> i -> NnG.
pose rG := coset_repr (irr_repr i) NnG.
pose sG := DecSocleType (regular_repr algC G).
apply/is_irr_reprP; exists (irr_comp sG rG).
apply/cfunP=> x.
have F1: mx_irreducible rG.
  apply/(quo_mx_irr (coset_repr_rker (irr_repr i) NnG) (normal_norm NnG)).
  apply: (mx_rsim_irr (mx_rsim_sym (rsim_quo_coset (irr_repr i) NnG))).
  by apply: socle_irr.
move/(rsim_irr_comp sG (pGroupG G)): F1.
move/char_of_repr_rsimP; move/eqP<-.
rewrite /rG !cfunE.
by rewrite  mulrA -natr_mul mulnb repr_quo_fact2.
Qed.

Definition cirrq (G H : {group gT}) (theta : irr (G/H)%G) := 
  get_irr G (theta^())%CH.

Lemma cirrqE : forall (G H : {group gT}) (theta : irr (G/H)%G), 
  H <| G -> cirrq theta = (theta^())%CH :> cfun _ _.
Proof. by move=> *; rewrite /cirrq get_irrE // cfunq_irr. Qed.

Definition qirrc (G H : {group gT}) (theta : irr G) := 
  get_irr (G/H)%G (theta/H)%CH.

Lemma qirrcE : forall (G H : {group gT}) (theta : irr G), 
 H <| G  -> H \subset cker G theta -> qirrc H theta = (theta/H)%CH :> cfun _ _.
Proof. by move=> *; rewrite /qirrc get_irrE // qfunc_irr. Qed.

Lemma cirrqK : forall (G H : {group gT}),
  H <| G -> cancel (@cirrq G H) (@qirrc G H).
Proof.
move=> G H HnG theta; apply cfun_of_irr_inj.
have F1 := is_char_irr theta.
by rewrite qirrcE // cirrqE ?cker_cfunq // (cfunq_id F1).
Qed.

Lemma qirrcK : forall (G H : {group gT}) (theta : irr G),
  H <| G ->  H \subset cker G theta -> cirrq (qirrc H theta) = theta.
Proof.
move=> G H theta HnG Hi; apply cfun_of_irr_inj.
have F1 := is_char_irr theta.
by rewrite cirrqE // qirrcE // (qfunc_id F1).
Qed.

Lemma norm_cap_cker : forall (G N : {group gT}), N <| G ->  
   N = \bigcap_(t : irr G | N \subset cker G t) (cker G t) :> {set _}.
Proof.
move=> G N NnG; apply/eqP; rewrite eqEsubset; apply/andP; split.
  by  apply/bigcapsP.
apply/subsetP=> g; move/bigcapP=> Hg.
have InG : g \in G.
  case/is_irrP: (cfunq_irr (irr1 _) NnG)=> j Hj.
  apply: (subsetP (cker_sub G j)). 
  by apply: Hg; rewrite -Hj; apply: cker_cfunq=>//; exact: is_char_irr.
have InN: g \in 'N(N) by apply: (subsetP (normal_norm NnG)).
suff: coset N g \in \bigcap_(t : irr (G/N)%G) cker (G/N)%G t.
  by rewrite cker_all1; move/set1P; move/coset_idr; apply.
apply/bigcapP=> i _.
case/is_irrP: (cfunq_irr i NnG)=> j Hj.
have: g \in cker G j by apply: Hg; rewrite -Hj cker_cfunq // is_char_irr.
rewrite /cker !genGid !(is_char_irr) !inE -(repr_quo_fact2 _ NnG) InN.
rewrite -Hj !cfunqE ?group1 //.
suff->: coset N 1%g  = 1%g by [].
by apply: coset_id; exact: group1.
Qed.

Lemma sum_norm_quo : forall (H G : {group gT}) g,
   g \in G -> H <| G ->
    \sum_(t : irr (G/H)%G) (t (coset H g)) * (t (coset H g))^* =
    \sum_(t : irr G | H \subset cker G t) (t g) * (t g)^*.
Proof.
move=> H G g GiG HnG.
rewrite (reindex (@cirrq G H)) //=.
apply: eq_big=> i'; first by rewrite cirrqE // cker_cfunq // is_char_irr.
  by move=> _; rewrite cirrqE // cfunqE // (subsetP (normal_norm HnG)).
exists (qirrc H)=> i' HH; first by apply: cirrqK.
by apply: qirrcK.
Qed.

Lemma norm_cker : forall (G N : {group gT}), N <| G ->  
   N = cker G ((reg_cfun (G/N)%G) ^())%CH :> {set _}.
Proof.
move=> G N NnG; apply/setP=> g.
rewrite /cker genGid is_char_cfunq ?is_char_char_of_repr // !inE.
case: (boolP (g \in G))=> InG /=; last first.
  by apply/idP=> HH; case/negP: InG; apply: (subsetP (normal_sub NnG)).
rewrite !cfunqE ?(group1, (subsetP (normal_norm NnG)) ) //.
rewrite !reg_cfunE (coset_id (group1 _)) eqxx.
case E1: (g \in N); first by rewrite coset_id // !eqxx.
case: (_ =P 1%g)=> [HH|__].
  by case/idP: E1; apply: coset_idr=> //; apply: (subsetP (normal_norm NnG)).
by rewrite eq_sym (negPf (neq0GC _)).
Qed.

End Coset.

Notation "f '/' N" := (qfun_of_cfun N f) : character_scope.
Notation " f '^()'" := (cfun_of_qfun f) (at level 2) : character_scope.

Section Derive.

Variable gT : finGroupType.

Lemma clinear_commutator_irr : forall (G : {group gT}) (theta : irr G),
  clinear G theta = (G^`(1) \subset cker G theta)%g.
Proof.
move=> G theta; apply/idP/idP=> [|NN]; first by apply: clinear_commutator.
case/is_irrP: (qfunc_irr (der_normal 1 G) NN)=> j Hj.
have F1 : abelian (G/G^`(1)) := der_abelian 0 G.
move/char_abelianP: F1; move/(_ j)=> HH.
rewrite /clinear genGid is_char_irr.
rewrite -(qfunc_id (is_char_irr _) (der_normal 1 G) NN).
rewrite cfunqE ?group1 //  Hj.
suff->: coset (G^`(1))%G 1%g = 1%g by case/andP: HH.
by apply: coset_id; exact: group1.
Qed.

(* This corresponds to Isaacs' 2.23(a) *) 
Lemma derive_at_cap : forall (G : {group gT}),
   (G^`(1) = \bigcap_(t : irr G | clinear G t) cker G t)%g.
Proof.
move=> G; rewrite (norm_cap_cker (der_normal 1 G)).
by apply: eq_bigl=> t; rewrite clinear_commutator_irr.
Qed.

(* Isaacs' 2.23(b) *)
Lemma card_linear : forall (G : {group gT}),
  #|[pred theta : irr G | clinear G theta]| = #|G : G^`(1)%g|.
Proof.
move=> G.
have F1 := der_normal 1 G.
rewrite -card_quotient ?normal_norm //.
move: (der_abelian 0 G); rewrite card_classes_abelian; move/eqP<-. 
rewrite -card_irr.
have->: (G^`(0) = G)%G by apply/val_eqP=> //.
rewrite -(card_imset _ (can_inj (cirrqK F1))) //.
apply: eq_card=> i.
rewrite !inE clinear_commutator_irr.
apply/idP/imsetP=> [HH|[j H1 ->]]; last first.
  by rewrite cirrqE // cker_cfunq // is_char_irr.
by exists (qirrc _ i)=> //; rewrite qirrcK.
Qed.

(* This is 2.24 *)
Lemma quotient_subcent_card : forall (G N : {group gT}) g,
 g \in G -> N <| G -> (#|'C_(G / N)[coset N g]| <= #|'C_G[g]|)%N.
Proof.
move=> G N g InG NN; rewrite leq_leC.
move: (irr_second_orthogonal_relation InG InG); rewrite class_refl => <-.
have InN : coset N g \in (G/N)%g by apply: mem_quotient.
move: (irr_second_orthogonal_relation InN InN); rewrite class_refl => <-.
rewrite sum_norm_quo //.
rewrite [\sum_i(_)](bigID (fun theta : irr G => N \subset cker G theta)) //=.
rewrite -{1}[\sum_(i|_)(_)]addr0 leC_add2l.
apply: posC_sum=> i _.
by rewrite /leC subr0; exact: repC_pconj.
Qed.

End Derive.

Section Center.

Variable (gT : finGroupType) (G : {group gT}).

Definition ccenter (G : {set gT}) (f : cfun gT algC) := 
  if is_char <<G>> f then [set g \in G | normC(f g) == f 1%g] else 1%G.

Definition rcenter (n : nat) (rG : mx_representation algC G n) :=
  [set g \in G | is_scalar_mx (rG g)].

Lemma rcenter_norm: forall (n : nat) (rG : mx_representation algC G n) g c,
  n != 0%N -> g \in G -> rG g = c%:M -> normC(c) = 1.
Proof.
move=> [|n] // rG g c _ InG HrG.
have F1: forall m, rG (g ^+ m)%g = (c ^+ m)%:M.
  by move=> m; rewrite repr_mxX // HrG scalar_exp.
have F2: c ^+ #[g] = 1.
  move: (F1 #[g]); rewrite expg_order repr_mx1.
  by move/matrixP; move/(_ 0 0); rewrite !mxE eqxx mulr1n.
apply/eqP; rewrite -(@posC_unit_exp _ #[g].-1) ?posC_norm //.
by rewrite -normC_exp prednK ?order_gt0 // F2 normC1.
Qed.

Lemma rcenter_group_set : forall  (n : nat) (rG : mx_representation algC G n),
 group_set (rcenter rG).
Proof.
move=> n rG.
rewrite /group_set !inE group1 repr_mx1 scalar_mx_is_scalar.
apply/subsetP=> i; rewrite !inE; case/imset2P=> g1 g2; rewrite !inE.
case/andP=> InG1; case/is_scalar_mxP=> k1 Hk1.
case/andP=> InG2; case/is_scalar_mxP=> k2 Hk2 HH.
by rewrite HH groupM // repr_mxM // Hk1 Hk2 -scalar_mxM scalar_mx_is_scalar.
Qed.

(* Isaacs' 2.27a *)
Lemma char_rcenterP : forall n (rG : mx_representation algC G n), 
  ccenter G (char_of_repr G rG) = rcenter rG.
Proof.
move=> n rG; rewrite /ccenter /rcenter genGid.
rewrite ?is_char_char_of_repr //.
apply/setP=> g; apply/idP/idP; rewrite !inE; case/andP=> InG; last first.
  rewrite InG; case/is_scalar_mxP=> c.
  case: (boolP (n == 0%N))=> Hn.
    move: rG; rewrite (eqP Hn)=> rG.
    by rewrite !cfunE !(flatmx0 (rG _)) !mxtrace0 !mulr0 normC0 eqxx.
  move=> Hc; rewrite cfunE InG mul1r Hc mxtrace_scalar char_of_repr1.
  by rewrite -mulr_natr normC_mul (rcenter_norm Hn InG Hc) 
              mul1r normC_nat eqxx.
rewrite InG; move/eqP=> HH.
have F1: (<[g]> \subset G) by rewrite cycle_subG.
pose rG' := subg_repr rG F1.
have HH': normC (char_of_repr <[g]> rG' g) = char_of_repr <[g]> rG' 1%g.
  by move: HH; rewrite /rG' !cfunE !group1 !InG cycle_id.
suff: exists2 c, normC c = (n != 0%N)%:R & rG' g = c%:M.
  by case=> c _ HH1; apply/is_scalar_mxP; exists c; rewrite -HH1.
apply: (@clinear_norm_scalar  _ <[g]> _ rG')=> //.
  exact: cycle_id.
by apply/char_abelianP; exact: cycle_abelian.
Qed.

Lemma ccenter_group_set : forall f, group_set (ccenter G f).
Proof.
move=> f; case: (boolP (is_char G f))=> Hf; last first.
  by rewrite /ccenter genGid (negPf Hf) group_set_one.
case/is_charP: Hf=> n [rG <-]; rewrite char_rcenterP //.
by exact: rcenter_group_set.
Qed.

Lemma irr_ccenterE : forall (theta : irr G) g,
  g \in G -> g \in ccenter G theta = (normC (theta g) == theta 1%g).
Proof.
by move=> t g GiG; rewrite /ccenter genGid (is_char_irr t) inE GiG.
Qed.

Lemma char_ccenterE : forall chi g,
  is_char G chi -> g \in G -> g \in ccenter G chi = (normC (chi g) == chi 1%g).
Proof.
by move=> chi g IC GiG; rewrite /ccenter genGid IC inE GiG.
Qed.

Lemma ccenter_mulC : forall chi g h,
  g \in ccenter G chi -> h \in G -> chi (g * h)%g = chi (h * g)%g.
Proof.
move=> chi; case: (boolP (is_char G chi))=> Hf g h; last first.
  by rewrite /ccenter genGid (negPf Hf); move/set1gP->; rewrite mul1g mulg1.
case/is_charP: Hf=> n [rG <-]; rewrite char_rcenterP //.
rewrite inE !cfunE; case/andP=> GiG; case/is_scalar_mxP=> k rGK HiG.
by rewrite !(groupM,GiG,HiG,mul1r) // !repr_mxM // rGK scalar_mxC.
Qed.

(* Isaacs' 2.27b *)
Canonical Structure ccenter_group f := Group (ccenter_group_set f).

(* Isaacs' 2.27b *)
Lemma ccenter_sub : forall f, ccenter G f \subset G.
Proof.
move=> f; case: (boolP (is_char G f))=> Hf; last first.
  rewrite /ccenter genGid (negPf Hf).
  by apply/subsetP=> g; rewrite inE; move/eqP->; exact: group1.
by rewrite /ccenter genGid Hf; apply/subsetP=> g; rewrite inE; case/andP.
Qed.

Lemma cker_center_normal : forall f, cker G f <| ccenter G f.
Proof.
move=> f; apply: normalS (cker_normal _ _); last by exact: ccenter_sub.
apply/subsetP=> g; rewrite /= /cker /ccenter genGid.
case E1: (is_char _ _)=> //; rewrite !inE.
case/andP=> HH; move/eqP->; rewrite HH normC_pos ?eqxx //.
apply: posC_isNatC; exact: (isNatC_char1 (idP E1)).
Qed.

Lemma ccenter_normal : forall f, ccenter G f <| G.
Proof.
move=> f; apply/normalP; split; first exact: ccenter_sub.
move=> g InG; apply/setP=> h.
rewrite /ccenter genGid.
case E1: (is_char G f); last by rewrite conjs1g.
have F1 := is_char_in_cfun (idP E1).
rewrite !inE; apply/imsetP/idP.
  case=> l; rewrite inE; case/andP=> LiG Hn ->.
  by rewrite groupJ // (cfunJ F1) ?Hn.
case/andP=> HiG NcH; exists (h ^(g^-1))%g; last first.
  by rewrite -conjgM mulVg conjg1.
by rewrite inE groupJ ?groupV // (cfunJ F1) ?groupV.
Qed.

(* Isaacs' 2.27c *)
Lemma ccenter_restrict : forall chi,
  exists2 chi1,
     clinear  (ccenter G chi) chi1 & 
     'Res[ccenter G chi] chi =  (chi 1%g) *: (chi1 : cfun _ _).
Proof.
move=> chi.
case: (boolP (is_char G chi))=> IC; last first.
  rewrite /ccenter genGid (negPf IC).
  exists (irr1 1%G).
    by rewrite /clinear genGid is_char_irr irr1E group1 eqxx.
   apply/cfunP=> g; case: (boolP (g \in 1%G)); last first.
     rewrite 3!cfunE genGid.
     by move/negPf->; rewrite !mul0r mulr0.
   by move/set1gP->; rewrite 2!cfunE irr1E group1 mul1r mulr1.
case/is_charP: IC=> [] [|n] [rG Hc].
  exists (irr1 [group of ccenter G chi]).
    by rewrite /clinear genGid is_char_irr irr1E group1 eqxx.
  by apply/cfunP=> g; rewrite -Hc !cfunE !(flatmx0 (rG _)) mxtrace0 !mulr0 mul0r.
pose repr g := ((rG g 0 0)%:M : 'M_(1,1)).
have Mx: mx_repr  [group of ccenter G chi] repr.
  split=> [| g h]; first by rewrite /repr repr_mx1 mxE eqxx.
  rewrite /= -Hc  char_rcenterP /rcenter !inE.
  case/andP=> InG; case/is_scalar_mxP=> k1 Hk1.
  case/andP=> InH; case/is_scalar_mxP=> k2 Hk2.
  by rewrite /repr repr_mxM // Hk1 Hk2 -!scalar_mxM !mxE !mulr1n.
exists (char_of_repr (ccenter G chi) (MxRepresentation Mx)).
  rewrite /clinear genGid is_char_char_of_repr.
  by rewrite cfunE group1 mul1r repr_mx1 mxtrace1 eqxx.
apply/cfunP=> g; rewrite !cfunE /=.
case: (boolP (g \in _))=> InG; last by rewrite !mul0r mulr0.
rewrite !mul1r.
move: InG; rewrite -Hc char_rcenterP /rcenter !inE.
case/andP=> InG; case/is_scalar_mxP=> k1 Hk1.
rewrite /repr !cfunE InG group1 Hk1 repr_mx1 !mul1r !mxE.
by rewrite  !mxtrace_scalar !mulr1n mulr_natl.
Qed.

(* Isaacs' 2.27d *)
Lemma ccenter_cyclic: forall chi, 
  is_char G chi -> chi != 0 -> cyclic (ccenter G chi/cker G chi)%g.
Proof.
move=> chi IC Hc; set CG := ccenter G chi.
have F1 : chi 1%g != 0 by rewrite -(character0_eq0 IC).
case: (ccenter_restrict chi)=> l H1l H2l.
have F2: cker G chi = cker CG ('Res[CG] chi)%CH .
   rewrite /cker !genGid IC (is_char_restrict (ccenter_sub _)) //. 
   apply/setP=> g; rewrite !inE.
   rewrite /CG /ccenter genGid IC !cfunE !inE.
   rewrite group1 /=; case E1: (g \in G)=> //=.
   rewrite [normC (chi 1%g)]normC_pos; last first.
     by apply: posC_isNatC; apply: isNatC_char1 IC.
   case: (normC _ =P _); first by rewrite eqxx !mul1r.
   case: (_ =P _)=> // HH HH1; case: HH1; rewrite HH.
   by rewrite normC_pos // posC_isNatC // (isNatC_char1 IC).
have F3 : cker CG ('Res[CG] chi)%CH = cker CG l.
   rewrite /cker /CG genGid  (is_char_restrict (ccenter_sub _)) //.
   rewrite (is_char_linear H1l).
   apply/setP=> g; rewrite !inE H2l !cfunE.
   by congr (_ && _); apply/eqP/eqP=>[|-> //]; move/(mulfI F1).
rewrite F2 F3; pose m (u : coset_of (cker CG l)) := l (repr u).
have Fm : forall C,  C  \in (ccenter G chi / cker CG l)%g ->
         exists c, [/\ c \in 'N(cker CG l), c \in  ccenter G chi, 
                       (C =  coset (cker CG l) c)%g & m C = l c].
  move=> C; case/imsetP=> /= c; rewrite inE; case/andP=> H1c H2c ->.
  exists c; rewrite H1c H2c; split=> //.
  rewrite /m /= !val_coset //.
  case: repr_rcosetP=> g /= GiK.
  rewrite !(clinearM H1l) //.
    by rewrite (cker_char1 GiK) (clinear1 H1l) mul1r.
  by rewrite (subsetP (normal_sub (cker_center_normal _))) // F2 F3.
apply: (@field_mul_group_cyclic _ _ _ m).
  move=> /= C1 C2; case/Fm=> c1 [H1c1 H2c1 -> ->]; case/Fm=> c2 [H1c2 H2c2 -> ->].
  rewrite /m /= !val_coset // rcoset_mul //.
  case: repr_rcosetP=> k InK.
  rewrite !(clinearM H1l) ?groupM // ?(cker_char1 InK, clinear1 H1l, mul1r) //.
  by rewrite (subsetP (normal_sub (cker_center_normal _))) // F2 F3.
move=> C; case/Fm=> c [H1c H2c -> ->].
split.
  move=> HH; rewrite coset_id // cker_charE ?is_char_linear //.
  by rewrite inE HH (clinear1 H1l) eqxx andbT.
move/(coset_idr H1c).
rewrite /= cker_charE  ?is_char_linear // inE (clinear1 H1l)  //.
by case/andP=> _ HH1; apply/eqP.
Qed.

(* Isaacs' 2.27e *)
Lemma ccenter_subset_center : forall chi, 
  is_char G chi -> (ccenter G chi/cker G chi)%g \subset 'Z(G/cker G chi)%g.
Proof.
move=> chi IC; apply/subsetP.
move=> C1; case/imsetP=> g; rewrite inE; case/andP=> H1g H2g -> /=.
apply/centerP; split.
  by apply: mem_quotient; apply: (subsetP (ccenter_sub chi)).
move=> C2; case/imsetP=> h; rewrite inE; case/andP=> H1h H2h -> /=.
apply/val_eqP; apply/eqP=> /=.
rewrite !val_coset //= !rcoset_mul //.
apply: rcoset_transl; apply/rcosetP; exists [~ g^-1, h^-1]; last first.
  exact: commgCV.
have InG: g \in G by apply: (subsetP (ccenter_sub chi)).
case/is_charP: IC=> n [rG HrG].
rewrite -HrG /= char_rkerP inE ?(groupR,groupV) //.
rewrite mul1mx !repr_mxM ?(invgK,groupR,groupJ,groupM,groupV)//.
move: H2g; rewrite -HrG char_rcenterP inE; case/andP=> _.
case/is_scalar_mxP=> k Hk.
rewrite !mulmxA Hk -scalar_mxC -Hk repr_mxK // -repr_mxM ?groupV//.
by rewrite mulgV repr_mx1 eqxx.
Qed.

(* Isaacs' 2.27f*)
Lemma ccenter_eq_center : forall theta : irr G, 
  (ccenter G theta/cker G theta)%g ='Z(G/cker G theta)%g.
Proof.
move=> t; case: (irr_reprE t)=> i-> {t}.
set t := char_of_repr _ _.
apply/eqP; rewrite eqEsubset.
rewrite ccenter_subset_center ?is_char_char_of_repr //.
apply/subsetP=> C1; case: (@cosetP _ _ C1)=> g Hg -> HH.
have GiG: g \in G.
  move: HH; rewrite inE; case/andP.
  case/imsetP=> h; rewrite inE; case/andP=> H1h H2h.
  move/(rcoset_kercosetP Hg H1h)=> //.
  case/rcosetP=> l H1l -> _; rewrite groupM //.
  by move: l H1l; apply/subsetP; exact: cker_sub.
apply: mem_quotient.
suff: g \in ccenter G t by [].
rewrite char_rcenterP /rcenter inE GiG.
have F1:  mx_absolutely_irreducible (irr_repr i).
  by apply: groupC; apply: socle_irr.
apply: (mx_abs_irr_cent_scalar F1).
apply/subsetP=> h HiG.
have HiN: h \in 'N(cker G t).
  by apply: (subsetP (normal_norm (cker_normal G t))).
set rGi := irr_repr _.
rewrite inE HiG -{1}repr_mxM //.
have F2 : (g * h)%g  \in (coset (cker G t) g * coset (cker G t) h)%g.
  apply/imset2P=> /=.
  by exists (g : gT) (h : gT)=> //;
     rewrite val_coset //; apply/rcosetP; exists 1%g; rewrite // mul1g.
move: F2; case/centerP: HH=> _; move/(_ (coset (cker G t) h))->; last first.
  by apply: mem_quotient.
case/imset2P=> g1 h1.
rewrite val_coset //; case/rcosetP=> g2 Hg2 ->.
rewrite val_coset //; case/rcosetP=> h2 Hh2 -> ->.
rewrite !repr_mxM ?groupM // ?(subsetP (cker_sub G t)) //.
have: g2 \in rker rGi. 
  by rewrite -char_rkerP /=.
rewrite inE; case/andP=> _; rewrite {1}mul1mx; move/eqP->; rewrite {1}mul1mx.
have: h2 \in rker rGi by rewrite -char_rkerP.
rewrite inE; case/andP=> _; rewrite {1}mul1mx; move/eqP->; rewrite {1}mul1mx.
by rewrite eqxx.
Qed.

Lemma center_sub_quo : forall (M N : {group gT}),
  N <| M -> ('Z(M)/N \subset 'Z(M/N))%g.
Proof.
move=> M N NM; apply/subsetP=> C.
case/imsetP=> g; rewrite inE; case/andP=> H1g H2g -> /=.
apply/centerP; split.
  by apply: mem_quotient; apply: (subsetP (center_sub M)).
move=> C1; case/imsetP=> h; rewrite inE; case/andP=> H1h H2h -> /=.
apply/val_eqP=> /=; apply/eqP.
rewrite !val_coset // !rcoset_mul //.
by case/centerP: H2g=> InG; move/(_ _ H2h); rewrite /commute => ->.
Qed.
  
(* This is 2.28 *)
Lemma center_bigcap : 'Z(G) = \bigcap_(theta : irr G) ccenter G theta.
Proof.
apply/setP=> g; apply/idP/idP=> [GiZ|].
  have GiG: g \in G by apply: (subsetP (center_sub G)).
  apply/bigcapP=> t _.
  case: (irr_reprE t) (ccenter_eq_center t)=> i -> {t}.
  set t := char_of_repr _ _ => Ct.
  have: coset (cker G t) g \in (ccenter G t/(cker G t))%g.
    rewrite Ct.
    apply: (subsetP ( center_sub_quo (cker_normal _ _))).
    by apply: mem_quotient.
  case/imsetP=> h; rewrite inE; case/andP=> H1h H2h /=.
  move/val_eqP; rewrite /= !val_coset //; last first.
    by apply: (subsetP (normal_norm (cker_normal G t))).
  move=> HH; move: GiG.
  have: g \in  cker_group G t :* g.
    by apply/rcosetP; exists (1%g); rewrite ?(group1,mul1g).
  rewrite (eqP HH); case/rcosetP=> l /= LiC -> LHiG.
  have LiG: l \in G by apply: (subsetP (cker_sub G t)).
  have HiG: h \in G by apply: (subsetP (ccenter_sub t)).
  rewrite char_rcenterP inE LHiG.
  move: LiC; rewrite char_rkerP inE mul1mx {1}repr_mxM //.
  case/andP=> InL; move/eqP->; rewrite mul1mx.
  by move: H2h; rewrite char_rcenterP inE; case/andP.
move/bigcapP=> HH.
have GiG: g \in G.
  by apply: (subsetP (ccenter_sub (irr1 G))); apply: HH.
apply/centerP; split=> //.
move=> h HiG; apply/commgP.
suff: [~ g, h] \in 1%G by rewrite inE.
rewrite -(cker_all1 G); apply/bigcapP=> t _.
case: (irr_reprE t) (HH t is_true_true) => i -> {t}.
set t := char_of_repr _ _ => Ct.
rewrite char_rkerP inE groupR // mul1mx.
set rGi := irr_repr _.
rewrite !repr_mxM ?(groupV,groupJ,groupM) //.
have: is_scalar_mx (rGi g).
  by move: Ct; rewrite char_rcenterP inE GiG.
case/is_scalar_mxP=> k Hk; rewrite Hk -scalar_mxC {1}mulmxA {1}mulmxA.
rewrite -Hk andTb; apply/eqP.
  (* Too slow
rewrite  {1}(repr_mxKV rGi InH).
*)
have->: rGi (g^-1)%g *m rGi (h^-1)%g *m rGi h *m rGi g = rGi (g^-1)%g *m rGi g.
   by congr (_ *m _); apply: (repr_mxKV rGi HiG).
by rewrite -repr_mxM ?groupV // mulVg repr_mx1.
Qed.
 
Lemma inner_subl: forall (H : {group gT}) (f1 f2 : cfun _ _), 
  H \subset G ->  (forall g, g \in G :\: H -> f1 g = 0) -> 
  '[f1,f2]_H = #|G : H|%:R * '[f1,f2]_G.
Proof.
move=> H f1 f2 HsG Hi; apply: sym_equal.
rewrite !inner_prodE {1}(bigID (fun x => x \in H)) /= addrC.
rewrite {1}big1=> [|j Hj]; last by rewrite Hi ?mul0r // inE andbC.
have CG := neq0GC G; have CH := neq0GC H.
apply: (mulfI CH).
rewrite add0r !mulrA -natr_mul LaGrange // !divff // !mul1r.
apply: eq_bigl=> g; rewrite andbC; case E1: (g \in H)=> //.
by rewrite (subsetP HsG).
Qed.

(* This is 2.29 *)
Lemma crestrict_sub_inner_bound : forall (H : {group gT}) f,
  H \subset G ->  '['Res[H] f,'Res[H] f]_H <= #|G : H|%:R * '[f,f]_G ?= iff
      (forallb g : gT, (g \in G:\:H) ==> (f g == 0)).
Proof.
move=> H f HsG; rewrite inner_subl // => [|i]; last first.
  by rewrite cfunE inE; case/andP; move/negPf->; rewrite mul0r.
apply/leCifP; case: (boolP (forallb b:_, _)).
  move/forall_inP=> Hi; apply/eqP.
  congr(_ * _); rewrite !inner_prodE; congr (_ * _); apply: eq_bigr=> g InG.
  rewrite cfunE; case E1: (g \in H); rewrite (mul0r,mul1r) //.
  have: g \in G:\:H by rewrite inE E1.
  by move/Hi; move/eqP->; rewrite !mul0r.
rewrite negb_forall_in; case/existsP=> g; case/andP=> H1g H2g.
rewrite ltC_sub -mulr_subr sposC_mul //.
  by rewrite -(ltn_ltC 0) indexg_gt0.
have InG: g \in G by apply: (subsetP (subsetDl G H)).
rewrite ['['Res[_] _,_]_G]inner_prodE (bigD1 g) //=.
rewrite inner_prodE (bigD1 g) //=.
rewrite -mulr_subr sposC_mul //.
  by rewrite sposC_inv -(ltn_ltC 0) cardG_gt0.
rewrite -addrA sposC_addr //.
  by rewrite ltCE posC_pconj andbT mulf_neq0 // conjC_eq0.
have: g \notin H by move: H1g; rewrite inE; case/andP.
rewrite cfunE; move/negPf->; rewrite !mul0r add0r.
rewrite -sumr_sub posC_sum // => i; case/andP=> _;case/andP=> HH _.
by rewrite !cfunE; case: (_ \in _); 
   rewrite !(mul0r,mul1r,subrr,subr0, (posC_nat 0),posC_pconj).
Qed.

(* This is 2.30 *)
Lemma irr1_bound : forall (theta : irr G),
  (theta 1%g)^+2 <= #|G:ccenter G theta|%:R ?= iff
      (forallb g : gT, (g \in G:\:ccenter G theta) ==> (theta g == 0)).
Proof.
move=> theta.
pose CG := (ccenter G theta).
have F1 : CG \subset G by apply: (ccenter_sub _).
rewrite -[_%:R]mulr1.
have: is_irr G theta by apply: is_irr_irr.
rewrite is_irr_inner_prod_charE ?is_char_irr //.
move/eqP=>HH; rewrite -{2}HH.
suff{HH}->: (theta 1%g)^+2 = '['Res[CG] theta,'Res[CG] theta]_CG.
  by apply: crestrict_sub_inner_bound.
case (@ccenter_restrict theta)=> l Hl ->.
rewrite inner_prodZ -inner_prodbE linearZ /= inner_prodbE.
move: (clinear_is_irr Hl).
rewrite is_irr_inner_prod_charE ?is_char_linear //.
move/eqP->.
rewrite ?expr2 isNatC_conj /GRing.scale /= ?mulr1 //.
by apply: (isNatC_char1 (is_char_irr _)).
Qed.
  
(* This is 2.31 *)
Lemma irr1_abelian_bound : forall (theta : irr G),
  abelian (G/ccenter G theta) -> (theta 1%g)^+2 = #|G:ccenter G theta|%:R.
Proof.
move=> theta AbGc; apply/eqP; rewrite irr1_bound.
apply/forall_inP=> g; rewrite inE; case/andP=> NInC GiG.
have GiN := subsetP (normal_norm (cker_normal G theta)) _ GiG.
pose CC := ccenter G theta.
have: coset (cker G theta) g \notin ([group of CC]/cker G theta)%G.
  apply/negP; case/imsetP=> /= h; rewrite inE; case/andP=> HiN HiC.
  have HiG: h \in G by apply: (subsetP (ccenter_sub theta)).
  move/rcoset_kercosetP; move/(_ GiN HiN); case/rcosetP=> u Hu Hg.
  have UiG: u \in G by apply: (subsetP (cker_sub G theta)).
  case/negP: NInC; rewrite Hg.
  rewrite irr_ccenterE ?groupM // (char_ckerMr (is_char_irr _)) //.
  by rewrite -irr_ccenterE.
rewrite  /= (ccenter_eq_center theta) => H.
case: (boolP (existsb h: gT, 
               (h \in G) && ([ ~ g, h] \notin cker G theta))); last first.
  rewrite negb_exists_in; move/forall_inP=> HH.
  case/negP: H; apply/centerP; split=> /=.
    by apply: mem_quotient.
  move=> N; case: (@cosetP _ _ N)=> h H1h -> H2h.
  apply/commgP.
  suff<-: coset (cker G theta) [~ g,h] = 1%g.
    by rewrite /commg /conjg !morphM ?(groupM,groupV) // !morphV.
  have HiG: h \in G.
    case/imsetP: H2h=> l; rewrite inE; case/andP=> H1l H2l.
    move/(rcoset_kercosetP H1h H1l).
    case/rcosetP=> k Hk ->; rewrite groupM //.
    by apply: (subsetP (normal_sub (cker_normal _ theta))).
  by apply: coset_id; move: (HH _ HiG); rewrite negbK.
case/existsP=> h; case/andP=> HiG CNiK.
have HiN: h \in 'N(ccenter G theta).
  by apply: (subsetP (normal_norm (ccenter_normal _))).
have GiNc: g \in 'N(ccenter G theta).
  by apply: (subsetP (normal_norm (ccenter_normal _))).
have CiC :  [~ g, h] \in ccenter G theta.
  apply: coset_idr; first by rewrite groupR.
  rewrite /commg /conjg !morphM ?(groupM,groupV,morphV) //=.
  suff->: commute (coset (ccenter G theta) g) (coset (ccenter G theta) h).
    by rewrite !mulgA mulgKV mulVg.
  move: AbGc; rewrite abelianE; move/subsetP.
  move/(_ _ (mem_quotient [group of CC] GiG)); move/centP.     
  by move/(_ _ (mem_quotient [group of CC] HiG)).
have: theta (g * [~ g, h])%g = theta (g).
  by rewrite -conjg_mulR (cfunJ (irr_in_cfun theta)).
case/is_charP: (is_char_irr theta)=> //= n [rG HrG].
move: CiC CNiK; rewrite -!HrG char_rkerP inE mul1mx=> CiC.
have RiG: [~ g, h] \in G by rewrite groupR.
rewrite !cfunE ?RiG groupM ?(GiG,RiG,group1,mul1r) // repr_mxM //.
move: CiC; rewrite char_rcenterP // inE RiG; case/is_scalar_mxP=> k ->.
rewrite scalar_mxC mul_scalar_mx mxtraceZ andTb.
case: (boolP (\tr(rG g) == 0))=> // HH HH1 HH2.
case/eqP: HH1.
apply/matrixP=> i1 j1; rewrite !mxE; case: eqP=> // _.
by apply: (mulIf HH); rewrite mul1r.
Qed.

Lemma cfaithfulE : forall f, cfaithful G f = (cker G f \subset 1%G).
Proof. by []. Qed.

(* 2.32a *)
Lemma irr_faithful_center: forall theta : irr G,
  cfaithful G theta -> cyclic ('Z(G)).
Proof.
move=> theta; move/trivgP=> HH.
rewrite (isog_cyclic (isog_center (quotient1_isog G))) -HH.
rewrite /= -ccenter_eq_center.
apply: ccenter_cyclic; first by apply: is_char_irr.
apply/negP; move/eqP; move/cfunP; move/(_ 1%g)=> HH1.
by case/negP: (irr1_neq0 theta); rewrite HH1 cfunE.
Qed.

(* 2.32b *)
Lemma pgroup_cyclic_faithful: forall p : nat, 
  p.-group G -> cyclic 'Z(G) -> exists theta : irr G, cfaithful G theta.
Proof.
 (* Lengthly Proof!! *)
move=> p PG CZG.
case: (boolP (G == 1%g :> {set _}))=> [HG1|DG].
  exists (irr1 G); rewrite /cfaithful /=.
  by move/eqP: HG1<-; exact: cker_sub.
case/(pgroup_pdiv PG): (DG) => Pp Dp [m Hm].
case: (boolP (forallb theta : irr G, cker G theta != 1%g)); last first.
  rewrite negb_forall; case/existsP=> i; rewrite negbK=> Hi.
  by exists i; apply/trivGP; apply/eqP.
move/forallP=> Hi.
case/cyclicP: CZG=> b Zb.
have: 'Z(G) != 1%g.
  by apply/eqP=> HH; case/eqP: DG; apply: (trivg_center_pgroup PG).
case/(pgroup_pdiv (pgroupS (center_sub _) PG))=> _ Zp1 [m1 Hm1].
pose Z := <[(b^+(p^m1)%N)%g]>.
have CZ: #|Z| = p.
  have ->: p = (p ^ (m1.+1 - m1))%N by rewrite subSnn expn1.
  by rewrite -orderE; apply: orderXexp; rewrite -Hm1 /= Zb orderE.
suff: Z \subset 1%G.
  move/subset_leq_card; rewrite CZ cards1.
  by move: Pp; case: (p)=> // [[|]].
rewrite -(cker_all1 G); apply/bigcapsP=> i _.
suff: forall N : {group gT}, N <| G -> N != 1%G -> Z \subset N.
  by apply; [apply: cker_normal | apply: Hi].
move=> {i Hi}N NnG DN.
have NsG:  N :&: 'Z(G) \subset G by apply: subIset; rewrite (normal_sub NnG).
have: N :&: 'Z(G) != 1%g.
  apply/eqP=> DNZ.
  case: (pgroup_pdiv (pgroupS (normal_sub NnG) PG) DN)=> _ Dp' [m' Hm'].
  move: (Pp).
  have Act : [acts G, on N | 'J] by rewrite astabsJ normal_norm.
  have DOr : forall x,  x \in N ->
       #|orbit 'J G x| != 1%N -> (p %| #|(orbit 'J G x)|)%N.  
    move=> g GiN; rewrite orbitJ -index_cent1; move: (dvdn_indexg G 'C_G[g]).
    rewrite Hm; case/dvdn_pfactor=> // [] [|m2] Hm2-> //.
    by rewrite expnS dvdn_mulr.
  move: Dp'; rewrite -(acts_sum_card_orbit Act).
  rewrite (bigID (fun S : {set _} => #|S| != 1%N)) dvdn_addr; last first.
    apply big_prop=> [|x y Hx Hy|]; rewrite ?(dvdn0,dvdn_addr) //=.
    by move=> i; case/andP; case/imsetP=> g GiG -> HH; exact: DOr.
  rewrite (bigD1 1%g) ?(cards1,andbT) //=; last first.
    by apply/imsetP; exists 1%g; rewrite ?group1 // orbitJ (class1g (group1 _)).
  rewrite big1 /=; first by rewrite dvdn1; move/eqP->.
  move=> i; do 2 case/andP; case/imsetP=> g GiN ->.
  rewrite negbK orbitJ -index_cent1 indexg_eq1 classG_eq1=> H1g H2g.
  move/eqP: DNZ; rewrite -[_==_]negbK; case/negP.
  apply/trivgPn; exists g=> //.
  have GiG : g \in G by apply: (subsetP (normal_sub NnG)).
  rewrite inE GiN; apply/centerP; split=> // y YiG.
  by case/subcent1P: (subsetP H1g _ YiG).
case/(pgroup_pdiv (pgroupS NsG PG))=> _ HH [m2 Hm2].
case: (Cauchy Pp HH)=> u Hu Hv.
have: u \in <[b]> by rewrite -Zb; move: Hu; rewrite inE; case/andP.
case/cyclePmin=> m3 Hm3 H1u.
move: (expg_order  u); rewrite Hv H1u -expgn_mul.
move/eqP; rewrite -order_dvdn.
move: Hm1; rewrite /= Zb /= -orderE => ->.
rewrite expnSr dvdn_pmul2r ?prime_gt0 //.
case/dvdnP=> k Hk.
have <-: <[u]> = Z.
  apply/eqP; rewrite eqEcard -orderE Hv CZ leqnn cycle_subG.
  by rewrite H1u Hk mulnC expgn_mul mem_cycle.
by rewrite cycle_subG (subsetP (subsetIl _ 'Z(G))).
Qed.

End Center.

Section Induced.

Variable (gT : finGroupType).

Definition cinduced  (G H : {set gT}) (f : cfun gT algC) := cfun_of_fun
 (fun g =>  #|H|%:R^-1 * \sum_(c | c \in G) f (g ^ c)).

Local Notation "'Ind[ G , H ] f" := (cinduced G H f) (at level 24).
Variable (G H : {group gT}).

Lemma cinduced_in_cfun : forall (f : cfun gT algC),
  H \subset G -> f \in 'CF(H) -> 'Ind[G,H] f \in 'CF(G).
Proof.
move=> f HsG Hf; apply/cfun_memP; split=> [g Hg|g h GiG HiG].
  rewrite !cfunE big1 ?mulr0 // => h HiG.
  rewrite (cfun0 Hf) //.
  apply/negP; move/(subsetP HsG)=> GHiH; case/negP: Hg.
  by rewrite -[g]conjg1 -[1%g](mulgV h) conjgM groupJ // groupV.
rewrite !cfunE; congr (_ * _).
rewrite (reindex (fun x => h^-1 * x)%g) //=; last first.
  by exists (mulg h)=> l; rewrite mulgA (mulgV,mulVg) mul1g.
apply: eq_big=> [l|l _]; first by rewrite groupMl // groupV.
by rewrite -conjgM mulgA mulgV mul1g.
Qed.

Lemma cinduced1 : forall f, 
  H \subset G -> ('Ind[G,H] f) 1%g = #|G:H|%:R * f 1%g.
Proof.
move=> f HsG; rewrite cfunE (eq_bigr (fun _ => f 1%g)).
  rewrite sumr_const -[(f _) *+ _]mulr_natl mulrA -(LaGrange HsG).
  by rewrite natr_mul mulrA mulVf ?mul1r // neq0GC.
by move=> i; rewrite conj1g.
Qed.

Lemma induced0: forall chi,
  is_char H chi -> H \subset G -> ('Ind[G,H] chi == 0) = (chi == 0%CH).
Proof.
move=> chi IC HsG; apply/eqP/eqP=>[|->]; last first.
  by apply/cfunP=> g; rewrite !cfunE big1 ?mulr0 // => h _; rewrite cfunE.
move/cfunP; move/(_ 1%g); rewrite cinduced1 // cfunE.
move/eqP; rewrite mulf_eq0; case/orP.
  rewrite -(eqN_eqC _ 0).
  by case: #|_:_| (indexg_gt0 G H).
by rewrite -(character0_eq0 IC); move/eqP.
Qed.

(* Isaacs' 5.2 *)
Lemma frobenius_reciprocity : 
  forall f1 f2, H \subset G -> f1 \in 'CF(H) -> f2 \in 'CF(G)->
   '[f1,'Res[H] f2]_H = '['Ind[G,H] f1,f2]_G.
Proof.
move=> f1 f2 HsG F1iC F2iC.
apply: sym_equal; rewrite !inner_prodE.
pose f3 i :=  #|H|%:R^-1 * \sum_(g \in G) f1 (i ^g) * (f2 i)^*.
rewrite (eq_bigr f3) =>[/=|g GiG]; rewrite {}/f3; last first.
  by rewrite cfunE -mulrA -mulr_suml.
rewrite mulr_sumr exchange_big /=.
pose f3 i :=  \sum_(g \in G) f1 (g ^ i) * (f2 (g ^ i))^*.
rewrite (eq_bigr f3) =>[/=|g GiG]; rewrite {}/f3; last first.
  by apply: eq_bigr=> h HiG; rewrite (cfunJ F2iC).
rewrite  pair_big /= .
rewrite (reindex (fun p => (p.1,p.2^(p.1^-1))%g)) /=; last first.
  by exists (fun p => (p.1,p.2^(p.1))%g)=> [] [g h];
     rewrite -conjgM ?(mulgV, mulVg,conjg1) //=.
rewrite (eq_bigl (fun j => (j.1 \in G) && (j.2 \in G))); last first.
  move=> [g h]; case E1: (g \in G)=> //; move/idP: E1 => E1.
  by rewrite groupMl !(groupMr,groupV).
rewrite (eq_bigr (fun i =>  f1 i.2 * (f2 i.2)^*)); last first.
  by move=> [g h]; rewrite -conjgM ?(mulgV, mulVg,conjg1).
rewrite -(pair_big (fun g => g \in G) (fun g => g \in G)
                 (fun i j =>  f1 j * (f2 j)^*)) /=.
rewrite sumr_const (bigID (fun g => g \notin H)) big1 //= ?add0r; last first.
  by move=> g; case/andP=> GiG GniH; rewrite (cfun0 F1iC) ?mul0r.
set u := _%:R; set v := _%:R; rewrite -mulr_natl -/u.
rewrite !mulrA [_/_]mulrC mulfVK ?neq0GC //; congr (_ * _).
apply: eq_big=> [g|g]; rewrite negbK.
  by case E1: (g \in H); rewrite ?andbF // (subsetP HsG _ (idP E1)).
by case/andP=> _ GiH; rewrite crestrictE.
Qed.

Lemma cinduced_conjC : forall f, ('Ind[G,H] f)^*%CH = 'Ind[G,H] (f^*)%CH.
Proof.
move=> f; apply/cfunP=> g.
rewrite !cfunE rmorphM conjC_inv conjC_nat; congr (_ * _).
rewrite rmorph_sum; apply: eq_bigr=> h HiG.
by rewrite cfunE.
Qed.

Lemma is_char_induced : forall chi,
   is_char H chi -> H \subset G -> is_char G ('Ind[G,H] chi).
Proof.
move=> chi IC HsG; have IiC := cinduced_in_cfun HsG (is_char_in_cfun IC).
apply/andP; split; rewrite ?genGid //; apply/allP=> t _.
rewrite ncoord_inner_prod // -frobenius_reciprocity //
        ?(is_char_in_cfun, is_char_irr, irr_in_cfun) //.
rewrite (inner_prod_char IC (is_char_restrict HsG (is_char_irr _))).
apply: isNatC_sum => j _; rewrite isNatC_mul // isNatC_ncoord_char //.
by apply: (is_char_restrict HsG (is_char_irr _)).
Qed.

Lemma is_comp_irr_restrict : forall theta : irr H,
  H \subset G -> exists j : irr G, is_comp theta ('Res[H] j).
Proof.
move=> t HsG.
case: (boolP ('Ind[G, H] t == 0))=> [HH|].
  have: ('Ind[G, H] t) 1%g == 0 by rewrite (eqP HH) cfunE.
  rewrite /= cinduced1 //.
  rewrite mulf_eq0 (negPf (irr1_neq0 _)) orbF -(eqN_eqC _ 0).
  by case: indexg (indexg_gt0 G H).
have ICI: is_char G ('Ind[G, H]t).
  by apply: is_char_induced=> //; exact: is_char_irr.
case/(is_comp_neq0 (is_char_in_cfun ICI))=> j Hj; exists j.
rewrite is_compE  ncoord_inner_prod ?(is_char_in_cfun) //; last first.
  by apply: (is_char_restrict HsG); exact: is_char_irr.
rewrite inner_prod_charC  // ?(is_char_restrict HsG, is_char_irr) //.
rewrite frobenius_reciprocity ?irr_in_cfun //.
by rewrite -ncoord_inner_prod // ?cinduced_in_cfun // irr_in_cfun.
Qed.

End Induced.

Notation "''Ind[' G , H ]  f " := (cinduced G H f) (at level 24).
