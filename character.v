(* (c) Copyright Microsoft Corporation and Inria. All rights reserved. *)
Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq path div choice.
Require Import fintype tuple finfun bigop prime ssralg poly finset.
Require Import fingroup morphism perm automorphism quotient finalg action.
Require Import zmodp commutator cyclic center pgroup sylow matrix mxalgebra.
Require Import mxpoly mxrepresentation vector algC classfun.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GroupScope GRing.Theory.
Local Open Scope ring_scope.

(**************************************************************************)
(*                                                                        *)
(* This file contains the basic notions of character theory               *)
(*                                                                        *)
(*         irr G : Tuple of {cfun gT} that contains all the irreducible   *)
(*               characters                                               *)
(*                                                                        *)
(*        Nirr G : Number of irreducible character                        *)
(*                                                                        *)
(*        Iirr G : Ordinal 'I_(Nirr G). Nirr and Iirr are defined in such *)
(*                 a way that 0 \in Iirr G                                *)
(*                                                                        *)
(*        'xi_i  : the ith character with i : Iirr G                      *)
(*                                                                        *)
(*      'xi[G]_i : the ith character with an explicite reference to the   *)
(*                unlying group G                                         *)
(*                                                                        *)
(*   is_char G f : predicates that tells if the function f is a character *)
(*                                                                        *)
(*      cker G f : the kernel of G i.e g \in G such that f g = f 1        *)
(*                                                                        *)
(*   is_comp i f : the irreducible character 'xi_i is a constituent of f  *)
(*                                                                        *)
(*   ccenter G f : the center i.e g \in G such that |f g| = f 1           *)
(*                                                                        *)
(* cfaithful G f : the class function f is faithfull, i.e its center      *)
(*                 is trivial                                             *)
(*                                                                        *)
(**************************************************************************)

Section AlgC.

Variable (gT : finGroupType).

Lemma groupC : group_closure_field algC gT.
Proof. exact: group_closure_closed_field. Qed.

End AlgC.

Lemma class_inv: forall (gT : finGroupType) (G : {group gT}) g,
  (g ^: G)^-1%g = g^-1 ^: G.
Proof.
move=> gT G g; apply/setP=> h; rewrite inE.
apply/imsetP/imsetP; case=> l LiG H.
  by exists l=> //; rewrite conjVg -H invgK.
by exists l=> //; rewrite H conjVg invgK.
Qed.

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

Section Tensor.

Variable (F : fieldType).

Fixpoint trow  (n1 : nat) : forall (A : 'rV[F]_n1) m2 n2 (B : 'M[F]_(m2,n2)), 'M[F]_(m2,n1 * n2) :=
  if n1 is n'1.+1 
  then
    fun (A : 'M[F]_(1,(1 + n'1))) m2 n2 (B : 'M[F]_(m2,n2)) =>
       (row_mx (lsubmx A 0 0 *: B) (trow (rsubmx A) B))
   else (fun _ _ _ _ => 0).

Lemma trow0 : forall n1 m2 n2 B, @trow n1 0 m2 n2 B = 0.
Proof.
elim=> //= n1 IH m2 n2 B.
rewrite !mxE scale0r linear0.
rewrite IH //; apply/matrixP=> i j; rewrite !mxE.
by case: split=> *; rewrite mxE.
Qed.

Definition trowb n1 m2 n2 B A :=  @trow n1 A m2 n2 B.

Lemma trowbE : forall n1 m2 n2 A B, trowb B A = @trow n1 A m2 n2 B.
Proof. by []. Qed.

Lemma trowb_is_linear : 
  forall n1 m2 n2 (B : 'M_(m2,n2)), linear (@trowb n1 m2 n2 B).
Proof.
elim=> [|n1 IH] //= m2 n2 B k A1 A2 /=.
  by rewrite scaler0 add0r.
rewrite linearD /= linearZ.
apply/matrixP=> i j.
rewrite !mxE.
case: split=> a.
  by rewrite !mxE mulr_addl mulrA.
by rewrite linearD /= linearZ IH !mxE.
Qed.

Canonical Structure trowb_linear n1 m2 n2 B := 
  Linear (@trowb_is_linear n1 m2 n2 B).
  
Lemma trow_is_linear : 
  forall n1 m2 n2 (A : 'rV_n1), linear (@trow n1 A m2 n2).
Proof.
elim=> [|n1 IH] //= m2 n2 B k A1 A2 /=.
  by rewrite scaler0 add0r.
rewrite linearD /= linearZ /=.
apply/matrixP=> i j.
rewrite !mxE.
case: split=> a; first by rewrite !mxE.
by rewrite IH !mxE.
Qed.

Canonical Structure trow_linear n1 m2 n2 A := 
  Linear (@trow_is_linear n1 m2 n2 A).

Fixpoint tprod  (m1 : nat) : 
  forall n1 (A : 'M[F]_(m1,n1)) m2 n2 (B : 'M[F]_(m2,n2)), 'M[F]_(m1 * m2,n1 * n2) :=
  if m1 is m'1.+1 
    return forall n1 (A : 'M[F]_(m1,n1)) m2 n2 (B : 'M[F]_(m2,n2)), 'M[F]_(m1 * m2,n1 * n2)
  then
    fun n1 (A : 'M[F]_(1 + m'1,n1)) m2 n2 B =>
        (col_mx (trow (usubmx A) B) (tprod (dsubmx A) B))
   else (fun _ _ _ _ _ => 0).

Lemma dsumx_mul : forall m1 m2 n p A B,
  dsubmx ((A *m B) : 'M[F]_(m1 + m2, n)) = dsubmx (A : 'M_(m1 + m2, p)) *m B.
Proof.
move=> m1 m2 n p A1 S2.
apply/matrixP=> i j; rewrite !mxE; apply: eq_bigr=> k _.
by rewrite !mxE.
Qed.

Lemma usumx_mul : forall m1 m2 n p A B,
  usubmx ((A *m B) : 'M[F]_(m1 + m2, n)) = usubmx (A : 'M_(m1 + m2, p)) *m B.
Proof.
move=> m1 m2 n p A1 S2.
apply/matrixP=> i j; rewrite !mxE; apply: eq_bigr=> k _.
by rewrite !mxE.
Qed.

Let trow_mul :
  forall (m1 m2 n2 p2 : nat) 
         (A : 'rV_m1) (B1: 'M[F]_(m2,n2)) (B2 :'M[F]_(n2,p2)), 
  trow A (B1 *m B2) = B1 *m trow A B2.
Proof.
move=> m1 m2 n2 p2 A B1 B2.
elim: m1 A => [|m1 IH] A /=; first by rewrite mulmx0.
by rewrite IH mul_mx_row -scalemxAr.
Qed.

Lemma tprodE : forall m1 n1 p1 (A1 :'M[F]_(m1,n1)) (A2 :'M[F]_(n1,p1))
                      m2 n2 p2 (B1 :'M[F]_(m2,n2)) (B2 :'M[F]_(n2,p2)),
  tprod (A1 *m A2) (B1 *m B2) = (tprod A1 B1) *m (tprod A2 B2).
Proof.
elim=> /= [|m1 IH]; first by move=> *; rewrite mul0mx.
move=> n1 p1 A1 S2 m2 n2 p2 B1 B2.
rewrite mul_col_mx -IH.
congr col_mx; last by rewrite dsumx_mul.
rewrite usumx_mul.
elim: n1 {A1}(usubmx (A1: 'M_(1 + m1, n1))) p1 S2=> //= [u p1 S2|].
  by rewrite [S2](flatmx0) !mulmx0 -trowbE linear0.
move=> n1 IH1 A p1 S2 //=.
set Al := lsubmx _; set Ar := rsubmx _.
set Su := usubmx _; set Sd := dsubmx _.
rewrite mul_row_col -IH1.
rewrite -{1}(@hsubmxK F 1 1 n1 A).
rewrite -{1}(@vsubmxK F 1 n1 p1 S2).
rewrite (@mul_row_col F 1 1 n1 p1).
rewrite -trowbE linearD /= trowbE -/Al.
congr (_ + _).
rewrite {1}[Al]mx11_scalar mul_scalar_mx.
by rewrite -trowbE linearZ /= trowbE -/Su trow_mul scalemxAl.
Qed.

Let tprod_tr : forall m1 n1 (A :'M[F]_(m1, 1 + n1)) m2 n2 (B :'M[F]_(m2, n2)),
  tprod A B =  row_mx (trow (lsubmx A)^T B^T)^T (tprod (rsubmx A) B).
Proof.
rewrite /=.
elim=> [|m1 IH] n1 A m2 n2 B //=.
  by rewrite trmx0 row_mx0.
rewrite !IH.
pose A1 := A :  'M_(1 + m1, 1 + n1).
have F1: dsubmx (rsubmx A1) = rsubmx (dsubmx A1).
  by apply/matrixP=> i j; rewrite !mxE.
have F2: rsubmx (usubmx A1) = usubmx (rsubmx A1).
  by apply/matrixP=> i j; rewrite !mxE.
have F3: lsubmx (dsubmx A1) = dsubmx (lsubmx A1).
  by apply/matrixP=> i j; rewrite !mxE.
rewrite tr_row_mx -block_mxEv -block_mxEh !(F1,F2,F3); congr block_mx.
- by rewrite !mxE linearZ /= trmxK.
by rewrite -trmx_dsub.
Qed.

Lemma tprod1 : forall m n, 
  tprod (1%:M : 'M[F]_(m,m)) (1%:M : 'M[F]_(n,n)) = 1%:M.
Proof.
elim=> [|m IH] n //=; first by rewrite [1%:M]flatmx0.
rewrite tprod_tr.
set u := rsubmx _; have->: u = 0.
  apply/matrixP=> i j; rewrite !mxE.
  by case: i; case: j=> /= j Hj; case.
set v := lsubmx (dsubmx _); have->: v = 0.
  apply/matrixP=> i j; rewrite !mxE.
  by case: i; case: j; case.
set w := rsubmx _; have->: w = 1%:M.
  apply/matrixP=> i j; rewrite !mxE.
  by case: i; case: j; case.
rewrite IH -!trowbE !linear0.
rewrite -block_mxEv.
set z := (lsubmx _) 0 0; have->: z = 1.
  by rewrite /z !mxE eqxx.
by rewrite scale1r scalar_mx_block.
Qed.

Lemma mxtrace_prod : forall m n (A :'M[F]_(m)) (B :'M[F]_(n)),
  \tr (tprod A B) =  \tr A * \tr B.
Proof.
elim=> [|m IH] n A B //=.
  by rewrite [A]flatmx0 mxtrace0 mul0r.
rewrite tprod_tr -block_mxEv mxtrace_block IH.
rewrite linearZ /= -mulr_addl; congr (_ * _).
rewrite -trace_mx11 .
pose A1 := A : 'M_(1 + m).
rewrite -{3}[A](@submxK _ 1 m 1 m A1).
by rewrite (@mxtrace_block _ _ _ (ulsubmx A1)).
Qed.

End Tensor.

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

Section ProdRepr.

Variable (m n : nat) (rG1 : mx_representation R G m)
                     (rG2 : mx_representation R G n).

Lemma prod_mx_repr : mx_repr G (fun g => tprod (rG1 g) (rG2 g)).
Proof.
split=>[|i j InG JnG]; first by rewrite !repr_mx1 tprod1.
by rewrite !repr_mxM // tprodE.
Qed.

Definition prod_repr := MxRepresentation prod_mx_repr.

End ProdRepr.

End MxR.

Implicit Arguments grepr0 [R gT G].
Prenex Implicits grepr0 dadd_grepr.

Section Char.

Variables (gT : finGroupType) (G : {group gT}).

Definition char_of_repr n (G : {set gT}) (f: gT -> 'M[algC]_n) : {cfun gT} := 
 [ffun g : gT => ((g \in G)%:R * \tr (f g))].

Lemma char_of_repr1 : 
  forall n (rG : mx_representation algC G n), char_of_repr G rG 1%g = n%:R.
Proof. by move=> n rG; rewrite !ffunE group1 repr_mx1 mxtrace1 mul1r. Qed.

Lemma char_of_repr_sim : 
  forall n1 n2 (rG1: mx_representation algC G n1) 
               (rG2: mx_representation algC G n2),
  mx_rsim rG1 rG2 -> char_of_repr G rG1 = char_of_repr G rG2.
Proof.
move=> n1 n2 rG1 rG2; case/mx_rsim_def=> M1 [M2] HM1M2 Hx.
apply/ffunP=> x; rewrite !ffunE; case H: (_ \in _); last by rewrite !mul0r.
by rewrite Hx // mxtrace_mulC mulmxA HM1M2 mul1mx.
Qed.

Lemma memc_char_of_repr : forall n (rG :  mx_representation algC G n), 
  char_of_repr G rG \in 'CF(G).
Proof.
move=> n rG; apply/cfun_memP.
split=> [x|x y YiG]; rewrite !ffunE.
  by case: (x \in G)=> //; rewrite mul0r.
rewrite (groupJr _ YiG) ; case: (boolP (_ \in _))=> xiG; last first.
   by rewrite !mul0r.
by rewrite !(repr_mxM,repr_mxV,groupM,groupV) //
           mxtrace_mulC mulmxK // repr_mx_unit.
Qed.

Lemma char_of_grepr0 : char_of_repr G (@grepr0 algC _ G) = 0.
Proof. by apply/ffunP=> g; rewrite !ffunE mxtrace1 mulr0. Qed.

Lemma char_of_dadd_grepr : forall rG1 rG2 : representation algC G,
  char_of_repr G (dadd_grepr rG1 rG2) = 
    char_of_repr G rG1 + char_of_repr G rG2.
Proof.
by move=> rG1 rG2; apply/ffunP=> g; rewrite !ffunE -mulr_addr mxtrace_block.
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

Definition reg_cfun (G : {set gT}) := char_of_repr G (regular_repr algC <<G>>).

Lemma reg_cfunE : forall (g : gT),
  reg_cfun G g = if (g == 1%g) then #|G|%:R else 0.
Proof.
move=> g; rewrite ffunE genGidG.
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

Definition xchar (G: {set gT}) (chi: {cfun gT}) (u: 'rV[algC]_#|G|) : algC^o := 
  \sum_(i < #|G|) u 0 i * chi (enum_val i).

(* In order to add a second canonical structure on xchar *)
Definition xcharb (G : {set gT}) x := (@xchar G)^~ x.

Lemma xcharbE : forall u (x : 'rV_#|G|), xchar u x = xcharb x u.
Proof. by []. Qed.

Lemma xcharb_is_linear : forall x, linear (@xcharb G x).
Proof.
move=> i k m n.
rewrite /xchar scaler_sumr -big_split /=; apply: eq_bigr=> l _.
by rewrite !ffunE mulr_addr scaler_mulr.
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
  by apply: eq_bigr=> j _; rewrite ffunE enum_valP mul1r mxtraceZ.
rewrite -raddf_sum; congr (\tr _).
apply/matrixP=> i1 j1; rewrite !mxE summxE; apply: eq_bigr=> k1 _.
by rewrite !(mxvecE,mxE).
Qed.

End Char.

Section IrrClassDef.

Variable (gT : finGroupType) (G : {set gT}).

Let sG := DecSocleType (regular_repr algC <<G>>).

Definition pred_Nirr := #|classes G|.-1.

Definition base_irr :=
   (map (fun x => char_of_repr <<G>> (irr_repr x)) (enum sG)).

Lemma cfuni_in_base_irr : '1_<<G>> \in base_irr.
Proof.
suff->: '1_<<G>> = char_of_repr <<G>> (irr_repr (principal_comp sG)).
  by apply: map_f=> //; rewrite mem_enum.
apply/ffunP=> g; rewrite !ffunE.
case: (boolP (_ \in _))=> GiG; last by rewrite mul0r.
by rewrite irr1_repr // mxtrace1 degree_irr1 mul1r.
Qed.

Definition nonprincipal_irr := 
  let (i,s,_) := rot_to cfuni_in_base_irr in
  let v := [tuple of nseq (pred_Nirr) (0 : {cfun _})] in 
  odflt v (insub s). 

Definition irr : pred_Nirr.+1.-tuple {cfun gT} :=
  [tuple of '1_<<G>> :: nonprincipal_irr].

Definition irr_representation (i : 'I_pred_Nirr.+1)  := 
  oapp (fun x => Representation (irr_repr x))
     grepr0
     (pick (fun j : sG => 
                 (tnth irr i%R) == char_of_repr <<G>> (irr_repr j))).

End IrrClassDef.

Notation Nirr G := (pred_Nirr G).+1.
Notation Iirr G := 'I_(Nirr G).
Notation "''xi_' i" := 
  (tnth (irr _) i%R) (at level 8, i at level 2, format "''xi_' i") : ring_scope.
Notation "''xi[' G ]_ i" := 
  (tnth (irr G) i%R) (at level 8, i at level 2, only parsing) : ring_scope.
Notation "''Xi_' i" := 
  (irr_representation i%R) (at level 8, i at level 2, format "''Xi_' i").

Section IrrClass.

Variable (gT : finGroupType) (G : {group gT}).

Lemma cfuni_xi0 : '1_G = 'xi[G]_0.
Proof.  by rewrite (tnth_nth 0) /= genGid. Qed.

Lemma irr_cfuni : '1_G \in irr G.
Proof. by rewrite inE genGid eqxx. Qed.

Lemma NirrE : Nirr G = #|classes G|.
Proof. by rewrite /pred_Nirr (cardD1 [1]) classes1. Qed.

Let sG := DecSocleType (regular_repr algC G).
Let sG' := DecSocleType (regular_repr algC <<G>>).

Let base_irr :=
   (map (fun x => char_of_repr <<G>> (irr_repr x)) (enum sG')).

Lemma perm_eq_irr : perm_eq (irr G) base_irr.
Proof.
rewrite /irr /nonprincipal_irr; case: rot_to=> n s' HH.
rewrite perm_eq_sym -(perm_rot n base_irr) HH /=.
case: (insubP _)=> /= [u _ -> // |].
rewrite -eqSS (_: (size s').+1 = size('1_<<G>>::s')) // -{1}HH.
rewrite size_rot size_map -cardE NirrE.
by rewrite card_irr genGidG ?(pGroupG, eqxx) //; last exact: groupC.
Qed.

Lemma irrP: forall f : {cfun gT},
   reflect (exists i : sG, char_of_repr G (irr_repr i) = f)
           (f \in irr G).
Proof.
move=> i; move: (perm_eq_mem perm_eq_irr).
rewrite /base_irr /sG' !genGid !genGidG=> ->.
(apply: (iffP mapP)=> [] [] j)=> [Jh->|<-]; exists j=> //.
by rewrite mem_enum.
Qed.
 
Lemma irr_xi : forall i : Iirr G, 'xi_i \in irr G.
Proof. by move=> i; apply: mem_nth; rewrite size_tuple. Qed.

Lemma irrIP: forall f : {cfun gT},
   reflect (exists i : Iirr G, 'xi_i = f)
           (f \in irr G).
Proof.
move=> f; apply: (iffP idP)=> [|[i <-]]; last exact: irr_xi.
case/(nthP 0)=> j; rewrite size_tuple => Hj <-.
by exists (Ordinal Hj); rewrite (tnth_nth 0).
Qed.


Definition socle_of_Iirr (i : Iirr G) : sG :=
  odflt  [1 sG]%irr (pick (fun j => 'xi_i == char_of_repr G (irr_repr j))).

Lemma socle_of_IirrE :  forall (i : Iirr G),
   char_of_repr G (irr_repr (socle_of_Iirr i)) = 'xi_i.
Proof.
move=> i; rewrite /socle_of_Iirr; case: pickP=> [x |]; first by move/eqP.
by case/irrP: (irr_xi i)=> j <-; move/(_ j); rewrite eqxx.
Qed.

Definition irr_of_socle (i : sG) : Iirr G :=
  odflt 0 (pick (fun j : Iirr G => 'xi_j == char_of_repr G (irr_repr i))).

Lemma irr_of_socleE :  forall (i : sG),
   'xi_(irr_of_socle i) = char_of_repr G (irr_repr i).
Proof.
move=> i; rewrite /irr_of_socle; case: pickP=> [x |]; first by move/eqP.
have: char_of_repr G (irr_repr i) \in irr G.
  rewrite (perm_eq_mem perm_eq_irr).
  rewrite /base_irr /sG' genGid genGidG; apply: map_f; apply: mem_enum.
case/(nthP 0)=> j; rewrite size_tuple => Hj <-.
by move/(_ (Ordinal Hj)); rewrite (tnth_nth 0) eqxx.
Qed.

Lemma irr_sumE : 
  forall (R : Type) (idx : R) (op : Monoid.com_law idx) (F : _ -> R),
       \big[op/idx]_(i < Nirr G) F 'xi_i = 
       \big[op/idx]_(i : sG) F (char_of_repr G (irr_repr i)).
Proof.
move=> R idx op F.
apply: (@trans_equal _ _ (\big[op/idx]_(i <- irr G) F i)).
  apply: sym_equal; rewrite (big_nth 0) big_mkord size_tuple.
  by apply: eq_bigr=> i _; rewrite  (tnth_nth 0).
by rewrite (eq_big_perm _ perm_eq_irr) big_map /sG' !(genGid,genGidG) enumT.
Qed.

Lemma irr_sum_square : \sum_(i < Nirr G) ('xi_i 1%g) ^+ 2 = #|G|%:R.
Proof.
rewrite (irr_sumE _ (fun f => (f 1%g) ^+ 2)) /=.
rewrite -[X in X%:R](sum_irr_degree sG) ?pGroupG //; last exact: groupC.
rewrite natr_sum; apply: eq_bigr=> i _.
by rewrite ffunE group1 mul1r repr_mx1 mxtrace1 natr_exp.
Qed.

Lemma irr1_degree : forall i : Iirr G, 
  'xi_i 1%g = (irr_degree (socle_of_Iirr i))%:R.
Proof.
move=> i; case/irrP: (irr_xi i)=> j Hj.
rewrite /socle_of_Iirr; case: pickP=> [k|].
  move/eqP-> => /=.
  by rewrite ffunE group1 mul1r repr_mx1 mxtrace1.
by move/(_ j); rewrite Hj eqxx.
Qed.

Lemma isNatC_irr1 : forall i : Iirr G, isNatC ('xi_i 1%g).
Proof. by move=> i; rewrite irr1_degree isNatC_nat. Qed.

Lemma irr1_neq0 : forall i : Iirr G, 'xi_i 1%g != 0.
Proof.
move=> i; rewrite irr1_degree.
case: irr_degree (irr_degree_gt0 (socle_of_Iirr i))=> // n _. 
by rewrite -(eqN_eqC _ 0).
Qed.

Lemma ltC_irr1: forall i : Iirr G, 0 < 'xi_i 1%g.
Proof.
move=> i.
case/isNatCP: (isNatC_irr1 i) (irr1_neq0 i).
by move=> n /= ->; rewrite /ltC => ->; exact: posC_nat.
Qed.

Lemma memc_irr : forall i : Iirr G, 'xi_i \in 'CF(G).
Proof.
by move=> i; case/irrP: (irr_xi i)=> j <-; apply: memc_char_of_repr.
Qed.

Lemma reg_cfun_sum : 
  reg_cfun G = \sum_(i < Nirr G) 'xi_i (1%g) *: 'xi_i.
Proof.
rewrite (irr_sumE _ (fun f => (f 1%g) *: f)) /=.
apply/ffunP=> g; rewrite !ffunE genGidG.
case (boolP (_ \in _))=> GiG; last first.
  rewrite mul0r; rewrite (cfun0 _ GiG) // memv_suml // => i _.
  by apply: memvZl; apply: memc_char_of_repr.
rewrite mul1r (mxtrace_regular sG (pGroupG _)) //; last by exact: groupC.
rewrite sum_ffunE ffunE.
apply: eq_bigr => i _.
by rewrite !ffunE repr_mx1 mxtrace1 {1}group1 {1}GiG !mul1r -mulr_natl.
Qed.

Lemma xchar_is_linear : forall i : sG,
  linear (@xchar _ G (char_of_repr G (irr_repr i))).
Proof.
move=> i k m n.
rewrite scaler_sumr -big_split /=; apply: eq_bigr=> l _.
by rewrite scaler_mull -mulr_addl !mxE.
Qed.

Canonical Structure xchar_linear i := Linear (xchar_is_linear i).

Local Notation "'E_" := Wedderburn_id.
Local Notation "'R_":= Wedderburn_subring.
 
Lemma xchar_subring : forall (i1 i2 : sG) A, 
  i1 != i2 -> (A \in 'R_i2)%MS ->
   xchar (char_of_repr G (irr_repr i1)) (gring_row A) = 0.
Proof.
move=> i1 i2 A Ht HA.
rewrite xchar_trace -(mxtrace0 _ (irr_degree i1)); congr (\tr _).
have F1: i2 != irr_comp sG (irr_repr i1).
  rewrite irr_reprK ?pGroupG //.
  by apply/eqP=> HH; case/eqP: Ht.
apply: irr_comp'_op0 F1 _; first by exact: pGroupG.
  by apply: socle_irr.
rewrite gring_rowK // -(Wedderburn_sum sG (pGroupG _)).
apply/memmx_sumsP; exists (fun i => (i == i2)%:R *: A).
  rewrite (bigD1 i2) //= eqxx scale1r big1 ?addr0 // => k.
  by case: (k == i2); rewrite // scale0r.
by move=> k; case E1: (k == i2); 
  [move/eqP: E1->; rewrite scale1r | rewrite scale0r mem0mx].
Qed.

Lemma xchar_id : forall (i1 i2 : sG) (f1 := char_of_repr G (irr_repr i1)),
  xchar f1 (gring_row ('E_ i2)) = if i1 == i2 then f1 1%g else 0.
Proof.
move=> i1 i2 f1; rewrite /f1; case: eqP=> [->|Ht]; last first.
  by apply: xchar_subring (Wedderburn_id_mem _); apply/eqP.
rewrite ffunE group1 mul1r -gring_opG //.
have R1 := (envelop_mx_id (regular_repr algC G) (group1 G)).
rewrite -[regular_repr algC _ 1%g]gring_rowK // -xchar_trace.
rewrite -[regular_repr _ _ _]mul1mx -(Wedderburn_sum_id sG (pGroupG _)).
have->: regular_repr algC G 1%g = 1%:M.
  by apply/matrixP=> x y; rewrite !mxE !eqxx mulg1 gring_valK eq_sym.
rewrite mulmx1 !linear_sum /= (bigD1 i2) //= big1 ?addr0 // => k.
rewrite eq_sym => Hij.
exact: (xchar_subring Hij (Wedderburn_id_mem k)).
Qed.

Lemma irr_e_mul : forall (i : sG) A (f := char_of_repr G (irr_repr i)), 
 (A \in group_ring algC G)%MS ->
   xchar f (gring_row ('E_i *m A)) = xchar f (gring_row A).
Proof.
move=> i A f HA.
rewrite -{2}[A]mul1mx -(Wedderburn_sum_id sG); last exact: pGroupG.
rewrite mulmx_suml !linear_sum /= (bigD1 i) //= big1 ?addr0 // => j.
rewrite eq_sym => Hj.
apply: (xchar_subring Hj).
case/andP: (Wedderburn_ideal j)=> _ Ij.
by apply: submx_trans Ij=> //; apply: (mem_mulsmx (Wedderburn_id_mem _)).
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
Lemma gring_row_e : forall (i : sG) (f := char_of_repr G (irr_repr i)), 
  gring_row ('E_i) = \row_j (#|G|%:R^-1 * f 1%g * f ((enum_val j)^-1)%g).
Proof.
move=> i f; apply/rowP=> j.
set g:= ((enum_val j)^-1)%g.
have GiG: (g \in G)%g by rewrite groupV enum_valP.
pose rG := regular_repr algC G g.
have: xchar (reg_cfun G) (gring_row ('E_i *m rG)) = 
        #|G|%:R * gring_row ('E_i) 0 j.
  rewrite /xchar (bigD1 (gring_index G 1%g)) //= big1; last first.
    move=> k Hk; rewrite reg_cfunE.
    case: eqP; last by rewrite mulr0.
    by move=> Hk'; case/negP: Hk; rewrite -Hk' gring_valK.
  rewrite addr0 enum_rankK_in ?genGid // gring_row_mul.
  rewrite reg_cfunE // eqxx mulrC; congr (_ * _).
  (* This takes ages 
  rewrite {1}mxE {1}(bigD1 j) //= {1}big1.
  *)
  rewrite {1}mxE {1}(@bigD1 _ _ (GRing.add_comoid algC) _ j) //= big1.
    by rewrite !mxE mulgV !eqxx mulr1 addr0.
  move=> k Hk.
  rewrite !mxE eqxx; case: eqP; last by rewrite mulr0.
  move=> Hi; case/negP: Hk.
  apply/eqP; apply: enum_val_inj; apply/eqP; rewrite eq_mulgV1.
  rewrite eq_sym; apply/eqP.
  apply: (can_in_inj (@gring_indexK _ G))=> //.
  by rewrite !(groupM,enum_valP).
rewrite reg_cfun_sum xcharbE linear_sum /=.
rewrite (irr_sumE _ (fun f => xcharb (gring_row ('E_ i *m rG)) (f 1%g *: f))) /=.
rewrite (bigD1 i) //= big1 ?addr0; last first.
  move=> k Hki.
  rewrite linearZ /= -xcharbE.
  rewrite (xchar_subring Hki) //; first by rewrite scaler0.
  case/andP: (Wedderburn_ideal i)=> _ Hi.
  apply: submx_trans Hi; apply: mem_mulsmx; first by exact: Wedderburn_id_mem.
  by apply: envelop_mx_id; rewrite groupV enum_valP.
rewrite linearZ /= -xcharbE.
rewrite irr_e_mul; last first.
  by apply: envelop_mx_id; rewrite groupV enum_valP.
rewrite xchar_singleton // !mxE //= -mulrA=> HH.
by rewrite[f 1%g * _]HH !mulrA mulVf ?mul1r // neq0GC.
Qed.

End IrrClass.

Section VectorSpace.

Variable (gT : finGroupType).

Section VectorSpaceDef.

Variable (G : {set gT}).

Definition ncoord x i := coord (irr G) i x.

End VectorSpaceDef.


Variable (G : {group gT}).

Local Notation "'E_" :=  Wedderburn_id.
Local Notation "'R_":=  Wedderburn_subring.
Let sG := DecSocleType (regular_repr algC G).
  
Lemma free_irr : free (irr G).
Proof.
rewrite (free_perm_eq (perm_eq_irr G)).
rewrite !(genGid,genGidG).
apply/freeP=> s; set ss := \sum_(i<_) _ => Hs j.
pose j' := enum_val j.
suff: xchar ss (gring_row ('E_ j')) = s j *  char_of_repr G (irr_repr j') 1%g.
  rewrite /xchar big1 //.
    move/eqP; rewrite eq_sym mulf_eq0; case/orP; first by move/eqP.
    rewrite ffunE group1 mul1r repr_mx1 mxtrace1.
    by case: irr_degree (irr_degree_gt0 j')=> // n _; rewrite -(eqN_eqC _ 0).
  by move=> i _; rewrite Hs ffunE mulr0.
rewrite xcharbE linear_sum; rewrite (bigD1 j) //= big1 ?addr0.
  rewrite (nth_map ([1 sG]%irr)) //; last by rewrite -cardE.
  rewrite linearZ /= -xcharbE.
  suff->: (nth [1 sG]%irr (enum sG) j) = j'
    by rewrite  xchar_id eqxx.
  by move: (nth_enum_rank [1 sG]%irr j'); rewrite enum_valK.
move=> i Hij.
pose i' := enum_val i.
rewrite  (nth_map [1 sG]%irr) //; last by rewrite -cardE.
rewrite linearZ /= -xcharbE.
have->: (nth [1 sG]%irr (enum sG) i) = i'.
  by move: (nth_enum_rank [1 sG]%irr i'); rewrite enum_valK.
rewrite  xchar_id; case: eqP; last by rewrite scaler0.
move/eqP=> HH; case/negP: Hij.
by move: HH; rewrite (bij_eq (enum_val_bij (socle_finType sG))).
Qed.

Lemma xi_inj : forall i j : Iirr G, 'xi_i = 'xi_j -> i = j.
Proof.
move=> i j HH; apply/val_eqP; move/eqP: HH.
by rewrite !(tnth_nth 0) (nth_uniq 0 _ _ (uniq_free free_irr)) ?size_tuple.
Qed.

Definition socle_of_cfun (f : {cfun gT}) : sG :=
  odflt  [1 sG]%irr (pick (fun i : sG => f == char_of_repr G (irr_repr i))).

Lemma socle_of_cfunE :  forall (i : sG),
   socle_of_cfun (char_of_repr G (irr_repr i)) = i.
Proof.
move=> i; rewrite /socle_of_cfun; case: pickP=> [x |]; last first.
  by move/(_ i); rewrite eqxx.
rewrite eq_sym; move/eqP; move: free_irr.
rewrite (free_perm_eq (perm_eq_irr G)) genGid genGidG.
move/uniq_free; move/injectiveP; apply.
Qed.

Lemma char_of_standard_grepr : forall n (rG : mx_representation algC G n),
  char_of_repr G (standard_grepr rG)
    = \sum_(i < Nirr G)
         (standard_irr_coef rG (socle_of_cfun 'xi_i))%:R *: 'xi_i.
Proof.
move=> n rG; rewrite char_of_dsum_grepr.
rewrite (irr_sumE _ _ (fun f => (standard_irr_coef rG (socle_of_cfun f))%:R *: f)).
by apply: eq_bigr => i _; rewrite scaler_nat char_of_n_grepr socle_of_cfunE.
Qed.

Lemma char_of_repr_inj : forall n1 n2,
  forall rG1 : mx_representation algC G n1,
  forall rG2 : mx_representation algC G n2,
  char_of_repr G rG1 = char_of_repr G rG2 -> mx_rsim rG1 rG2.
Proof.
move=> n1 n2 rG1 rG2 /= eq_char12.
have [rsim1 rsim2] := (mx_rsim_standard rG1, mx_rsim_standard rG2).
pose c n (rG : mx_representation algC G n) (i : Iirr G) : algC := 
  (standard_irr_coef rG (socle_of_cfun 'xi_i))%:R.
apply: mx_rsim_trans (rsim1) (mx_rsim_sym _).
suffices ->: standard_grepr rG1 = standard_grepr rG2 by [].
apply: eq_bigr => i _; congr (n_grepr _ _).
apply/eqP; rewrite eqN_eqC.
rewrite -[i]socle_of_cfunE -irr_of_socleE.
suff: c n1 rG1 (irr_of_socle i) == c n2 rG2 (irr_of_socle i) by [].
pose FF1 := @free_coords  _ _  _ (irr G).
have FF2 := free_irr.
pose f n (rG : mx_representation algC G n) i :=  c n rG i *: 'xi_i.
pose g n (rG : mx_representation algC G n) i :=  c n rG i *: (irr G)`_i.
have FF3: forall n rG i, f n rG i = g n rG i.
  by move=> n rG j; rewrite /f /g (tnth_nth 0).
rewrite -FF1 //.
rewrite (eq_bigr (f n1 rG1))=> [|j _]; last by rewrite FF3.
rewrite -(char_of_standard_grepr rG1) -(char_of_repr_sim rsim1).
rewrite eq_char12.
rewrite (char_of_repr_sim rsim2) (char_of_standard_grepr rG2).
rewrite (eq_bigr (g n2 rG2))=> [|j _]; last by rewrite -FF3.
by rewrite FF1.
Qed.

Lemma char_of_repr_rsimP : forall m n (rG1 : mx_representation algC G m)
                                      (rG2 : mx_representation algC G n),
   reflect (mx_rsim rG1 rG2) (char_of_repr G rG1 == char_of_repr G rG2).
Proof.
move=> m n rG1 rG2; apply: (iffP eqP)=> HH; first by apply: char_of_repr_inj.
apply/ffunP=> g; rewrite !ffunE.
case E1: (g \in G); last by rewrite !mul0r.
by rewrite !mul1r; apply: mxtrace_rsim.
Qed.

Lemma is_basis_irr : is_basis 'CF(G) (irr G).
Proof.
rewrite /is_basis free_irr andbT /is_span -dimv_leqif_eq.
  rewrite dim_cfun.
  move: free_irr; rewrite /free; move/eqP->.
  by rewrite size_tuple NirrE.
rewrite -span_subsetl; apply/allP=> i.
by case/irrIP=> k <-; apply: memc_irr.
Qed.

Lemma ncoord_sum : forall A (x : {cfun gT}), x \in 'CF(G,A) -> 
  x = \sum_(i < Nirr G) ncoord i x *: 'xi_i.
Proof.
move=> A x Hx.
have F2: x \in span (irr G).
  move: (is_span_is_basis is_basis_irr).
  by rewrite /is_span; move/eqP->; exact: (memcW Hx).
rewrite {1}(coord_span F2).
by apply: eq_bigr=> i _; rewrite (tnth_nth 0).
Qed.

Lemma ncoord_is_linear : forall i : Iirr G, linear (ncoord i).
Proof. by move=> i k c1 c2; rewrite /ncoord linearD linearZ !ffunE. Qed.

Canonical Structure ncoord_linear i := Linear (ncoord_is_linear i).

Lemma ncoordE : forall  (c : Iirr G -> algC) (i : Iirr G), 
  ncoord i (\sum_(j < Nirr G) (c j) *: 'xi_j) = c i.
Proof.
move=> c i.
rewrite (eq_bigr (fun j => c j *: (irr G)`_j))=> [|j _].
  by apply: free_coords free_irr.
by rewrite (tnth_nth 0).
Qed.

Lemma ncoord0 : forall i: Iirr G, ncoord i 0 = 0.
Proof.
move=> i.
by move: (ncoordE (fun i => 0) i); rewrite big1 // => j _; rewrite scale0r.
Qed.

Lemma ncoord_irr : forall i j : Iirr G, ncoord i 'xi_j = (i == j)%:R.
Proof.
move=> i j.
move: (ncoordE (fun k => (k == j)%:R) i).
rewrite (bigD1 j) //= big1 ?(eqxx, scale1r, addr0) // => k /negPf->.
by rewrite scale0r. 
Qed.

Lemma isNatC_ncoord_repr :
  forall n (rG : mx_representation algC G n) (i : Iirr G),
    isNatC (ncoord i (char_of_repr G rG)).
Proof.
move=> n rG theta.
rewrite (char_of_repr_sim (mx_rsim_standard rG)).
rewrite char_of_standard_grepr ncoordE.
by apply: isNatC_nat.
Qed.

End VectorSpace.

Section Restrict.

Variable (gT : finGroupType).

Lemma crestrict_subg : 
  forall (G H : {group gT}) n (rG : mx_representation algC G n)
                              (HsG: H \subset G),
  'Res[H] (char_of_repr G rG) = char_of_repr H (subg_repr rG HsG).
Proof.
move=> G H n rG HsG; apply/ffunP=> g; rewrite !ffunE /=.
by case InH: (g \in H); rewrite ?mul0r // (subsetP HsG _ (idP InH)) !mul1r.
Qed.

End Restrict.

Section IsChar.

Variable (gT : finGroupType).

Definition is_char (G : {set gT}) (f : {cfun gT}) :=
  (forallb i : Iirr G, isNatC (ncoord i f)) && (f \in 'CF(G)).

Variable G : {group gT}.

Lemma is_charP : forall f,
  reflect (exists n, exists rG : mx_representation algC G n, 
            char_of_repr G rG = f)
          (is_char G f).
Proof.
move=> f.
apply: (iffP andP); last first.
  case=> n [rG <-]; split; last exact: memc_char_of_repr.
  apply/forallP=> chi.
  by exact: isNatC_ncoord_repr.
case; move/forallP=> Ha Hf.
pose n' (j : Iirr G) := getNatC (ncoord j f).
have->: f = \sum_(j < Nirr G) (n' j)%:R *: 'xi_j.
  rewrite {1}(ncoord_sum Hf) //.
  apply: eq_bigr=> i _.
  by congr (_ *: _); apply/eqP; apply: Ha.
elim: {n'}(\sum_j (n' j))%N {-2}n' (leqnn (\sum_j (n' j)))=> [| N IH] n' HS.
  exists 0%N; exists grepr0.
  apply/ffunP=> i; rewrite sum_ffunE !ffunE mxtrace1 mulr0 big1 // => j Hj.
  by move: HS; rewrite (bigD1 j) //=; case: (n' j)=> //; rewrite scale0r ffunE.
case: (boolP (all (fun i => n' i == 0%N) (enum (Iirr G)))).
  move/allP=> HH.
  exists 0%N; exists grepr0.
  apply/ffunP=> i; rewrite sum_ffunE !ffunE mxtrace1 mulr0 big1 // => j Hj.
  by rewrite (eqP (HH _ (mem_enum _ j))) scale0r ffunE.
case/allPn=> k kIn Hk.
pose n'' j := if (j == k) then (n' j).-1 else n' j.
have F1: (\sum_j (n' j) = 1 + \sum_j n'' j)%N.
  rewrite (bigD1 k) //[(\sum_j n'' j)%N](bigD1 k) //.
  rewrite addnA /n'' eqxx add1n prednK; last by case: (n' k) Hk.
  by congr (_ + _)%N; apply: eq_bigr=> i; case: (i == k).
have F2: \sum_j (n' j)%:R *: 'xi_j  = 'xi_k + \sum_j (n'' j)%:R *: 'xi_j.
  rewrite (bigD1 k) //[(\sum_j (n'' j)%:R *: _)](bigD1 k) // addrA; congr (_ + _).
    rewrite /n'' eqxx; case: (n' _) Hk=> //= n _.
    by rewrite -add1n natr_add scaler_addl scale1r.
  by apply: eq_bigr=> i; rewrite /n''; case: (i == k).
case: (IH n''); first by  rewrite -ltnS -add1n -F1.
intros n [rG HrG]; pose i := socle_of_cfun G ('xi_k); exists ((irr_degree i) + n)%N.
exists (dadd_grepr (Representation (irr_repr i)) (Representation rG)).
rewrite (char_of_dadd_grepr (Representation _) (Representation _)) HrG F2.
suff ->: char_of_repr G (irr_repr (socle_of_cfun G 'xi_k)) = 'xi_k by [].
rewrite /socle_of_cfun; case: pickP=> [k1|] /=; first by move/eqP.
have: 'xi_k \in irr G by rewrite (tnth_nth 0) mem_nth // size_tuple.
rewrite (perm_eq_mem (perm_eq_irr G)); case/mapP.
rewrite genGid genGidG /= => i1 _ ->.
by  move/(_ i1); rewrite eqxx.
Qed.

Lemma is_char_char_of_repr : forall n (rG : mx_representation algC G n),
  is_char G (char_of_repr G rG).
Proof. by move=> n rG; apply/is_charP; exists n; exists rG. Qed.

Lemma is_char_reg : is_char G (reg_cfun G).
Proof.  rewrite /reg_cfun genGidG; exact: is_char_char_of_repr. Qed.

Lemma is_char_irr : forall i : Iirr G, is_char G 'xi_i.
Proof. 
move=> i; apply/is_charP.
case/irrP: (irr_xi i)=> j <-.
by exists (irr_degree j); exists (irr_repr j).
Qed.

Lemma isNatC_ncoord_char : forall (i : Iirr G) (f : {cfun _}),
 is_char G f -> isNatC (ncoord i f).
Proof.
move=> i f; case/is_charP=> n [rG <-].
by exact: isNatC_ncoord_repr.
Qed.

Lemma is_char0 : is_char G 0.
Proof. by rewrite -(char_of_grepr0 G) is_char_char_of_repr. Qed.

Lemma is_char1 : is_char G '1_G.
Proof.  case/irrP: (irr_cfuni G)=> i <-; exact: is_char_char_of_repr. Qed.

Lemma character0_eq0 : forall chi,
  is_char G chi -> (chi == 0) = (chi 1%g == 0).
Proof.
move=> chi IC; apply/eqP/eqP=> [->|HH]; first by rewrite ffunE.
move: HH; case/is_charP: IC=> n [rG <-].
rewrite !ffunE group1 repr_mx1 mxtrace1 mul1r; move/eqP; rewrite -(eqN_eqC _ 0).
move=>HH; move: rG; rewrite (eqP HH)=> rG.
by apply/ffunP=> g; rewrite !ffunE [rG _]flatmx0 mxtrace0 mulr0.
Qed.

Lemma memc_is_char : forall f,  is_char G f -> f \in 'CF(G).
Proof. 
by move=> f; case/is_charP=> n [rG <-]; apply: memc_char_of_repr.
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

Lemma is_char_sum : forall (I : eqType) r (P : I -> bool) (F : I -> {cfun _}),
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

Lemma is_char_mul : forall f1 f2, 
  is_char G f1 -> is_char G f2 -> is_char G (f1 * f2).
Proof.
move=> f1 f2; case/is_charP=> m [rG1 HrG1]; case/is_charP=> n [rG2 HrG2].
apply/is_charP; exists (m * n)%N.
exists (prod_repr rG1 rG2).
apply/ffunP=> g; rewrite -HrG1 -HrG2 !ffunE /=.
by rewrite mxtrace_prod; case: (_ \in _); rewrite !(mul1r,mul0r).
Qed.

Lemma is_char_exp : forall (n : nat) f,
  is_char G f -> n != 0%N -> is_char G (f ^+ n).
Proof.
move=> n f ICf; elim: n=> [|[|n] IH] // _.
by rewrite exprS is_char_mul // IH.
Qed.

Lemma is_char_cbP : forall f,
  reflect 
    (exists n, f = \sum_(i < Nirr G) (n i)%:R *: 'xi_i)
    (is_char G f).
Proof.
move=> f; apply: (iffP idP)=> [HH|[n ->]]; last first.
  apply: is_char_sum=> i _.
  by rewrite scaler_nat is_char_scal // is_char_irr.
exists (fun theta => getNatC (ncoord theta f)).
rewrite {1}(ncoord_sum (memc_is_char HH)).
apply: eq_bigr=> theta _.
by congr (_ *: _); apply/eqP; apply: isNatC_ncoord_char.
Qed.

Lemma is_char_indu : forall (P: {cfun gT} -> Prop), P 0 -> 
  (forall (i : Iirr G) chi, 
      is_char G chi -> P chi -> P ('xi_i + chi)) ->
  forall chi, is_char G chi -> P chi.
Proof.
move=> P P0 IH chi; case/is_char_cbP=> n ->.
elim: {n}(\sum_t (n t))%N {-2}n (leqnn (\sum_t (n t)))=>[n HH|N IH1 n].
  rewrite big1 // => i _.
  by move: HH; rewrite (bigD1 i) //=; case: (n i)=> //; rewrite scale0r.
case: (boolP (all (fun t => n t == 0%N) (enum (Iirr G)))).
  move/allP=> Ht _; rewrite big1 // => theta _.
  move: (Ht theta); rewrite mem_enum.
  by move/(_ is_true_true); move/eqP->; rewrite scale0r.
case/allPn=> i; rewrite mem_enum=> Ht Nt0 HH.
pose n' (t : Iirr G) := if (t == i) then (n t).-1 else n t.
have F1: (\sum_t (n t) = (\sum_t (n' t)).+1)%N.
  rewrite (bigD1 i) // [(\sum_t n' t)%N](bigD1 i) //= -[X in _ = X]add1n addnA.
  congr (_ + _)%N; first by rewrite /n' eqxx; case: (n i) Nt0.
  by apply: eq_bigr=> j Hj; rewrite /n' (negPf Hj).
have F2: \sum_(t < Nirr G) (n t)%:R *: 'xi_t = 
            'xi_i + \sum_(t < Nirr G) (n' t)%:R *: 'xi_t.
  rewrite  [X in _ + X](bigD1 i) //= (bigD1 i) //=.
  rewrite addrA; congr (_ + _).
    rewrite /n' eqxx; case: (n i) Nt0=> // m' _.
    by rewrite -{1}add1n natr_add scaler_addl scale1r.
  by apply: eq_bigr=> j Hj; rewrite /n' (negPf Hj).
rewrite F2; apply: IH.
  by apply: is_char_sum=> j _; rewrite scaler_nat is_char_scal // is_char_irr.
by apply: IH1; rewrite -ltnS -F1.
Qed.

Lemma isNatC_char1 : forall chi, is_char G chi -> isNatC (chi 1%g).
Proof.
apply: is_char_indu=> [|i chi IH HH].
  by rewrite ffunE (isNatC_nat 0).
rewrite ffunE isNatC_add //.
by apply: isNatC_irr1.
Qed.

Lemma posC_char1 : forall chi, is_char G chi -> 0 <= chi 1%g.
Proof. by move=> chi HH; apply: posC_isNatC; apply: (isNatC_char1 _). Qed.

Lemma irr_crestrict : forall (H : {group gT}) chi,
 is_char G chi -> H \subset G -> 'Res[H] chi \in irr H -> chi \in irr G.
Proof.
move=> H chi; case/is_charP.
move=> n [rG <-] HsG.
rewrite (crestrict_subg _ HsG).
case/irrP=> i Hi; apply/irrP.
pose sG := DecSocleType (regular_repr algC G).
exists (irr_comp sG rG).
apply/eqP;apply/char_of_repr_rsimP=> /=.
apply: mx_rsim_sym.
apply: rsim_irr_comp; first by exact: pGroupG.
apply: (@subg_mx_irr _ _ _ _ _ _ HsG).
move/eqP: Hi.
move/(char_of_repr_rsimP).
move/mx_rsim_irr; apply.
by apply: socle_irr.
Qed.

End IsChar.


Section Linear.

Variables (gT : finGroupType) (G : {group gT}) (f: {cfun gT}).

Definition clinear (G : {set gT}) f := is_char <<G>> f && (f 1%g == 1).

Hypothesis CFf : clinear G f.

Lemma clinear_val1: f 1%g = 1.
Proof. by apply/eqP; case/andP: CFf. Qed.

Lemma is_char_linear : is_char G f.
Proof. by case/andP: CFf; rewrite genGid. Qed.

Lemma clinear1 : clinear G '1_G.
Proof. by rewrite /clinear genGid is_char1 /= ffunE group1. Qed.

Lemma clinearM: forall g h,
  g \in G -> h \in G -> f (g * h)%g = f g * f h.
Proof.
move=> g h InG InH.
case/andP: (CFf); rewrite genGid.
case/is_charP=> // n [rG <-] HH.
move/eqP: (char_of_repr1 rG); rewrite (eqP HH) -(eqN_eqC 1%N) => Hn.
rewrite !ffunE groupM // InG InH // !mul1r repr_mxM //.
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
have F1: f g * f (g^-1%g) = 1 
  by rewrite -clinearM ?groupV // mulgV clinear_val1.
have F2 := clinear_neq0 InG.
by apply: (mulfI F2); rewrite F1 divff.
Qed.

Lemma clinearX : forall g n, g \in G -> (f g)^+n = f (g^+n)%g.
Proof.
move=> g n Hin; elim: n=> [|n IH].
  by rewrite expr0 expg0 clinear_val1.
by rewrite exprS expgS clinearM ?groupX // IH.
Qed.

Lemma clinear_unit : forall g, g \in G -> f g ^+ #[g] = 1.
Proof. by move=> g InG; rewrite clinearX // expg_order clinear_val1. Qed.

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
  reflect (forall (i : Iirr G), clinear G 'xi_i) (abelian G).
Proof.
apply: (iffP idP)=> [HH i|HH].
  rewrite /clinear genGid is_char_irr /=.
  case/irrP: (irr_xi i)=> j <-.
  rewrite ffunE group1 mul1r repr_mx1 mxtrace1 irr_degree_abelian //.
  by exact: groupC.
rewrite card_classes_abelian.
rewrite eqN_eqC -irr_sum_square // (eq_bigr (fun i : Iirr G => 1)) //=.
  rewrite sumr_const // -NirrE.
by rewrite cardT -cardE card_ord.
by move=> i _; case/andP: (HH i)=> _ HH'; rewrite (eqP HH') exprS mulr1.
Qed.

Lemma irr_repr_linear : forall (i : Iirr G) g, g \in G -> 
  clinear G 'xi_i -> irr_repr (socle_of_Iirr i) g = ('xi_i g)%:M.
Proof.
move=> i g GiG; move: (irr1_degree i).
rewrite /socle_of_Iirr; case: pickP=> [j|]; last first.
  by case/irrP: (irr_xi i)=> k <-; move/(_ k); rewrite eqxx.
rewrite [odflt _ _]/= => HH1 HH2 AbG.
rewrite (eqP HH1) ffunE GiG mul1r.
move: (irr_repr _).
case/andP: AbG=> _; rewrite irr1_degree.
have->: j = (socle_of_Iirr i).
  move: (sym_equal (socle_of_IirrE i)); rewrite (eqP HH1).
  move: (free_irr G); rewrite (free_perm_eq (perm_eq_irr G)).
  rewrite genGid genGidG; move/uniq_free.
  by move/injectiveP; apply.
rewrite -(eqN_eqC _ 1); move/eqP->.
move=> irr_repr; rewrite trace_mx11.
apply/matrixP=> [] [[|] Hi1] // [[|] Hj1] //.
by rewrite !mxE /= mulr1n; congr fun_of_matrix; apply/eqP.
Qed.

Lemma clinear_irr : f \in irr G.
Proof.
case/andP: (CFf); rewrite genGid => Hc Hf.
case/is_charP: Hc => n [].
move=> rG HrG.
move: Hf; rewrite -HrG char_of_repr1 -(eqN_eqC _ 1%N).
move/eqP=> Hn; move: rG HrG; rewrite Hn.
move=> rG HrG; apply/irrP.
pose sG := DecSocleType (regular_repr algC G).
exists (irr_comp sG rG).
apply/eqP; apply/char_of_repr_rsimP=> /=.
apply: mx_rsim_sym; apply: rsim_irr_comp; first by exact: pGroupG.
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
apply/ffunP=> g; rewrite !ffunE; case E1: (_ \in _); last by rewrite !mul0r.
by rewrite (subsetP Hsub) // !mul1r.
Qed.

Lemma is_char_norm : forall chi (g : gT),
  is_char G chi -> normC (chi g) <= chi 1%g.
Proof.
move=> chi g; case/is_charP=> n [rG <-].
case: (boolP (g \in G))=> Hin; last first.
  by rewrite (cfun0 (memc_char_of_repr _)) // normC0 char_of_repr1 posC_nat.
have F1: (<[g]> \subset G) by rewrite cycle_subG.
pose rG' := subg_repr rG F1.
have Hf: forall g1, g1 \in <[g]> -> 
    char_of_repr G rG g1 = char_of_repr <[g]> rG' g1.
  by move=> g1 Hg1; rewrite !ffunE Hg1; move/subsetP: (F1)->.
rewrite !Hf ?(cycle_id,group1) // (ncoord_sum (memc_char_of_repr _)).
rewrite !sum_ffunE 2!ffunE.
pose nc (i: Iirr <[g]>) := ncoord i (char_of_repr <[g]> rG').
suff->: \sum_i (nc i *: 'xi_i) 1%g = \sum_i normC ((nc i *: 'xi_i) g%g).
  by apply: normC_sum.
have F2 := cycle_abelian g.
apply: eq_bigr=> i _.
have CFf: clinear <[g]> 'xi_i by move/char_abelianP: F2; apply.
rewrite ffunE (clinear_val1 CFf).
rewrite ffunE normC_mul (clinear_norm  CFf) ?cycle_id //.
by rewrite normC_pos // /nc posC_isNatC // isNatC_ncoord_repr.
Qed.

 (* This could surely be proved more nicely in mx_representation *)
Lemma clinear_norm_scalar : 
  forall n (rG : mx_representation algC G n) g,
   g \in G -> 
   (forall (i : Iirr G), clinear G 'xi_i) ->
   normC (char_of_repr G rG g) = char_of_repr G rG 1%g ->
   exists2 c, normC c = (n != 0%N)%:R & rG g = c%:M.
Proof.
suff Hf: forall f, is_char G f ->
  forall (n : nat) (rG : mx_representation algC G n) (g : gT),
    g \in G -> f = char_of_repr G rG -> 
    (forall i : Iirr G, clinear G 'xi_i) -> normC (f g) = f 1%g ->
    exists2 c : algC, normC c = (n != 0%N)%:R & rG g = c%:M.
  move=> n rG g GiG HP HN.
  suff: is_char G (char_of_repr G rG) by move/Hf; apply.
  by apply: is_char_char_of_repr.
apply: is_char_indu=> [|i chi IC IH] n.
   move=> rG g GiG H0.
   have: mx_rsim rG (@grepr0 algC _ G).
     by apply/char_of_repr_rsimP; rewrite -H0 char_of_grepr0.
   move/mxrank_rsim=> HH; move: {H0}rG; rewrite HH=> rG.
   exists 0; first by rewrite eqxx normC0.
   by rewrite (flatmx0 (rG g)) (flatmx0 _%:M) .
move=> rG g GiG H0 CL; rewrite ffunE [_ 1%g]ffunE=> NN.
have F1: normC ('xi_i g + chi g) = normC ('xi_i g) + normC (chi g).
  apply: (leC_anti (normC_add _ _)); rewrite NN.
  apply: leC_add; [apply: is_char_norm | apply: is_char_norm] => //.
  by apply: is_char_irr.
have F2 : normC (chi g) = chi 1%g.
  apply: (leC_anti (is_char_norm _ _))=> //.
  rewrite -(leC_add2l ('xi_i 1%g)) -NN F1 leC_add2r is_char_norm //.
  by apply: is_char_irr.
have F3: normC('xi_i g) = 'xi_i 1%g.
  by apply: (@addIr _ (normC (chi g))); rewrite -F1 NN F2.
have F4 := (irr_repr_linear GiG (CL i)).
have F5: 'xi_i 1%g = 1 by case: (CL i); case/andP=> _;move/eqP.
case/is_charP: IC=> m [].
move=> rG1 Hc.
case: (IH _ _ _ GiG (sym_equal Hc) CL F2)=> c H1c H2c.
move: H1c; case: eqP=> Hm H1c.
  have F6: mx_rsim rG (irr_repr (socle_of_Iirr i)).
    apply/char_of_repr_rsimP; rewrite -H0.
    rewrite socle_of_IirrE.
    suff->: chi = 0 by rewrite addr0.
    rewrite -Hc; move: {Hc H2c}rG1; rewrite Hm=> rG1.
    by apply/ffunP=> h; rewrite !ffunE (flatmx0 (rG1 _)) mxtrace0 mulr0.
  exists ('xi_i g); last first.
    by apply: (mx_rsim_scalar GiG (mx_rsim_sym F6)).
  rewrite F3; case/andP: (CL i)=> _; move/eqP->.
  case: eqP=> //; move/eqP; rewrite eqN_eqC.
  move/mxrank_rsim: F6->; rewrite -irr1_degree F5.
  by rewrite -(eqN_eqC 1 0).
have F6 : 'xi_i g = c.
  case/normC_add_eq: F1=> k Hk.
  case/andP; move/eqP=> H1k; move/eqP=> H2k.
  rewrite H1k F3 F5 mul1r.
  move/eqP: Hm; rewrite neq0N_neqC;move/mulfI; apply.
  move: H2k; rewrite -Hc ffunE GiG mul1r H2c.
  rewrite mxtrace_scalar -mulr_natr normC_mul H1c mul1r.
  by rewrite normC_pos ?posC_nat // mulrC.
pose rG' := dadd_grepr (Representation (irr_repr (socle_of_Iirr i)))
                       (Representation rG1).
have F7: mx_rsim rG rG'.
  apply/char_of_repr_rsimP; rewrite -H0.
  rewrite (char_of_dadd_grepr (Representation _) (Representation _)) Hc.
  by rewrite socle_of_IirrE.
have F8 : rG' g = c%:M.
  have->: rG' g= block_mx (irr_repr (socle_of_Iirr i) g) 0 0 (rG1 g).
   by [].
  by rewrite H2c F4 F6 -scalar_mx_block.
exists c; last by by apply: (mx_rsim_scalar GiG (mx_rsim_sym F7)).
rewrite H1c; case/mxrank_rsim: F7; move/eqP.
rewrite eqN_eqC natr_add -(irr1_degree i) F5 -(natr_add _ 1%N m) -eqN_eqC.
by case: {rG H0}n.
Qed.

Lemma clinear_cker_mx1 : 
  forall n (rG : mx_representation algC G n) g,
   g \in G -> 
   (forall i : Iirr G, clinear G 'xi_i) ->
   char_of_repr G rG g = char_of_repr G rG 1%g -> rG g = 1%:M.
Proof.
move=> n rG g GiG Ht HC.
case/isNatCP: (isNatC_char1 (is_char_char_of_repr rG))=> k Hk.
have: normC (char_of_repr G rG g) = char_of_repr G rG 1%g.
  by rewrite HC Hk normC_nat.
case/(clinear_norm_scalar GiG Ht)=> c Hc Hx.
move: Hk; rewrite -HC ffunE GiG Hx mxtrace_scalar.
move: Hc; case: eqP=> [HH _ _|Hn HN]; first by rewrite HH !(flatmx0 _%:M).
rewrite mul1r=> HH.
suff->: c = 1 by [].
have F1: n%:R != 0 :> algC by rewrite -neq0N_neqC; move/eqP: Hn.
have F2: c = k%:R * n%:R^-1.
  by apply: (mulIf F1); rewrite mulr_natr HH mulfVK.
move: HN; rewrite F2.
by rewrite normC_mul normC_inv normC_pos ?posC_nat // normC_nat.
Qed.

(* we could extend it to is_comp f g := is_char G (g - f) *)
Definition is_comp (G : {set gT}) (i : Iirr G) (f : {cfun gT}) := 
  ncoord i f != 0.

Lemma is_compE : forall (i : Iirr G) f, is_comp i f = (ncoord i f != 0).
Proof. by []. Qed.

Lemma is_comp_charP : forall (i : Iirr G) chi,
  is_char G chi ->
  reflect (exists2 chi', is_char G chi' & chi = 'xi_i + chi') 
          (is_comp i chi).
Proof.
move=> i chi IC; apply: (iffP idP)=>[HH|[chi' IC' ->]]; last first.
  rewrite /is_comp linearD /= ncoord_irr eqxx.
  case/isNatCP: (isNatC_ncoord_char i IC')=> n ->.
  by rewrite -natr_add -neq0N_neqC.
exists (chi - 'xi_i); last by rewrite addrC subrK.
apply/andP; split; last first.
  by apply: memv_sub; rewrite ?(memc_is_char, is_char_irr).
apply/forallP=> t.
rewrite linearD linearN /= ncoord_irr.
case: (_ =P _)=> [->|_]; last first.
  by rewrite subr0 isNatC_ncoord_char.
move: HH; rewrite /is_comp.
case/isNatCP: (isNatC_ncoord_char i IC)=>  [] [|n] ->.
  by case/negP.
by rewrite -addn1 natr_add addrK isNatC_nat.
Qed.

Lemma is_comp_neq0 : forall (A : {set gT}) (f : {cfun _}), 
  f \in 'CF(G,A) -> f != 0  -> exists i : Iirr G, is_comp i f.
Proof.
move=> A f FCF Nf0; case: (pickP ((@is_comp G)^~ f)) => [i Hi | HH].
  by exists i.
case/eqP: Nf0; apply/val_eqP=> /=.
move: (ncoord_sum FCF); rewrite big1=> [|i Hi]; first by move=> ->.
by move/eqP: (HH i)->; rewrite scale0r.
Qed.

Lemma is_comp_irr1_char1 : forall (i : Iirr G) chi, 
  is_char G chi ->  is_comp i chi -> 'xi_i 1%g <= chi 1%g.
Proof.
move=> i chi IC; rewrite is_compE => Hn.
rewrite (ncoord_sum (memc_is_char IC)) (bigD1 i) //=.
set n := 'xi_i 1%g; rewrite 2!ffunE {}/n -leC_sub addrC addrA.
apply: posC_add.
  rewrite -mulN1r -mulr_addl posC_mul //; last first.
    by rewrite posC_isNatC // (isNatC_char1 (is_char_irr _)).
  case/isNatCP: (isNatC_ncoord_char i IC) Hn=> [] [|n] -> //.
    by rewrite /is_comp; case/negP.
  by move=> _; rewrite -add1n natr_add addrA addNr add0r posC_nat.
rewrite sum_ffunE ffunE posC_sum // => t Ht.
rewrite ffunE posC_mul //; last first.
  by rewrite posC_isNatC // (isNatC_char1 (is_char_irr _)).
by rewrite posC_isNatC // (isNatC_ncoord_char t IC).
Qed.

Lemma is_char_conjC : forall chi, is_char G chi -> is_char G (chi^*)%CH.
Proof.
move=> chi; case/is_charP=> n [rG <-].
apply/is_charP; exists n; exists (map_repr conjC rG).
by apply/ffunP=> h; rewrite !ffunE map_reprE trace_map_mx rmorphM conjC_nat.
Qed.

End MoreIsChar.

Section OrthogonalRelations.

Variable (aT gT : finGroupType) (A : {group aT}) (G : {group gT}).

Lemma char_inv : forall n (rG: mx_representation algC G n) g,
  char_of_repr G rG g^-1%g = (char_of_repr G rG g)^*.
Proof.
move=> n rG g.
case: (boolP (g \in G))=> Hin; last first.
  by rewrite (cfun0 (memc_char_of_repr _) Hin); rewrite -groupV // in Hin;
     rewrite (cfun0 (memc_char_of_repr _)) // conjC0.
have F1: (<[g]> \subset G) by rewrite cycle_subG.
pose rG' := subg_repr rG F1.
have F2: forall g1, g1 \in <[g]> -> 
    char_of_repr G rG g1 = char_of_repr <[g]> rG' g1.
  by move=> g1 Hg1; rewrite !ffunE Hg1; move/subsetP: (F1)->.
rewrite !F2 ?(groupVr,cycle_id) //. 
rewrite (ncoord_sum (memc_char_of_repr _)).
rewrite sum_ffunE 2!ffunE rmorph_sum; apply: eq_bigr=> i _.
have Cf: clinear <[g]> 'xi_i by move/char_abelianP: (cycle_abelian g); move/(_ i).
rewrite ffunE (clinearV_norm Cf) ?cycle_id //.
have F3: isNatC (ncoord i (char_of_repr <[g]> rG'))
  by apply: isNatC_ncoord_repr.
by rewrite -{1}(isNatC_conj F3) {1}/GRing.scale /= -rmorphM ?ffunE.
Qed.

Lemma invg_is_char : forall chi g, is_char G chi -> chi g^-1%g = (chi g)^*.
Proof.
move=> chi g; case/is_charP=> n [rG <-]; exact: char_inv.
Qed.

Let card_neq0 : #|G|%:R^-1 != 0 :> algC.
Proof. by rewrite invr_eq0 neq0GC. Qed.

(* Painfully following Isaacs' proof 2.14 *)
Lemma irr_first_orthogonal_relation : forall i j : Iirr G,
 #|G|%:R^-1 * (\sum_(g \in G) 'xi_i g * ('xi_j g)^*) = (i == j)%:R.
Proof.
move=> i j.
rewrite (reindex invg) /=; last by apply: onW_bij; apply: inv_bij; exact invgK.
pose e (j : Iirr G) :=  Wedderburn_id (socle_of_Iirr j).
have F1 : e i *m e j = (i == j)%:R *: e i.
  case: eqP=> [<-|Hij]; [rewrite scale1r | rewrite scale0r].
    case: (Wedderburn_is_id (pGroupG _) (socle_of_Iirr i))=> _ Hi Hj _.
    by exact: Hj.
  have Hsij: socle_of_Iirr i != socle_of_Iirr j.
    apply/eqP=> HH; case: Hij; apply/val_eqP.
    rewrite -(nth_uniq 0 _ _ (uniq_free (free_irr G))) ?size_tuple //=.
    by rewrite -!tnth_nth -socle_of_IirrE HH socle_of_IirrE.
  apply: (Wedderburn_mulmx0 Hsij); exact: Wedderburn_id_mem.
have F2: #|G|%:R^-1 * 'xi_i 1%g * 'xi_j 1%g != 0.
  by do 2 (apply: mulf_neq0; last by exact: irr1_neq0).
apply: (mulIf F2).
pose r1 (u: 'M[algC]_#|G|) := gring_row u 0 (gring_index G 1%g).
apply: (@etrans _ _ (r1 (e i *m e j))); last first.
  rewrite F1 /=; case: eqP=> [->|_].
    rewrite scale1r mul1r /r1 gring_row_e !mxE gring_indexK // invg1.
    by rewrite socle_of_IirrE.
  rewrite scale0r mul0r /r1.
  suff->: @gring_row algC _ G 0 = 0 by rewrite mxE.
  by apply/rowP=> k; rewrite !mxE.
pose gr k g := gring_row (e k) 0 (gring_index G g). 
suff->:
    r1 (e i *m e j) = \sum_(g \in G) gr i g * gr j (g^-1)%g.
  rewrite -mulr_sumr -mulr_suml.
  apply: eq_big=> [g|i1]; first by rewrite /= groupV.
(*
  have Hi1: forall (n : nat) (rG : mx_representation algC <<G>> n) (g : gT),
       char_of_repr <<G>> rG (g^-1)%g = (char_of_repr <<G>> rG g)^*.
    by rewrite genGid; exact: char_inv.
*)
  move=> Hi1.
  rewrite  /gr {1}gring_row_e {1}gring_row_e !mxE !gring_indexK 
           // -1?groupV //.
  rewrite !socle_of_IirrE.
  (* mimicking ring *)
  rewrite invgK; rewrite -!mulrA; congr (_ * _).
  apply: sym_equal; rewrite mulrC -!mulrA; congr (_ * _).
  have->: ('xi_j (i1^-1)%g)^* = 'xi_j i1.
    by rewrite -socle_of_IirrE char_inv conjCK.
  apply: sym_equal; rewrite ['xi_j _ * _]mulrC -!mulrA; congr (_ * _).
  by rewrite mulrC -!mulrA; congr (_ * _).
rewrite /r1 gring_row_mul.
have F3: (e j \in group_ring algC G)%MS.
  apply: (submx_trans (Wedderburn_id_mem _)).
  by rewrite /Wedderburn_subring genmxE submxMl.
rewrite -{1}(gring_rowK F3) mxE.
  (* This takes ages
rewrite {1}(reindex (@enum_val _ (fun x=> x \in G))) /=; last first.
  *)
rewrite {1}(@reindex _ _ (GRing.add_comoid algC) _ _
     (@enum_val _ (fun x=> x \in G))) /=; last first.
  by exists (gring_index G)=> g Hg;
        [exact: gring_valK | apply: gring_indexK].
apply: eq_big=> [g|i1 _]; first by rewrite enum_valP.
rewrite  /gr !gring_valK; congr (_ * _).
rewrite 2!mxE.
  (* This takes ages
rewrite {1}(@bigD1 (gring_index G (enum_val i1)^-1)) //=.
  *)
rewrite {1}(@bigD1 _ _  (GRing.add_comoid algC) _ 
                        (gring_index G (enum_val i1)^-1)) //=.
set u := gring_row _ _ _ .
rewrite {1}big1 ?addr0.
  rewrite !(mxE,mxvecE) gring_indexK; last by rewrite groupV enum_valP.
  by rewrite mulgV !eqxx mulr1.
move=> i2 Hi2.
rewrite !(mxE,mxvecE).
case: (gring_index G 1 =P _); last by rewrite andbF mulr0.
move=> HH; case/negP: Hi2.
have F5: (enum_val i1 * enum_val i2)%g \in G.
  by apply: groupM; exact: enum_valP.
rewrite -[_^-1%g]mulg1.
rewrite (can_in_inj (@gring_indexK _ G) (group1 G) F5 HH).
by rewrite mulgA mulVg mul1g gring_valK.
Qed.

Lemma irr_second_orthogonal_relation : forall (g h: gT), 
 g \in G -> h \in G ->
 \sum_(i < Nirr G) 'xi_i g * ('xi_i h)^* =
   if g \in (h ^: G) then #|'C_G[h]|%:R else 0.
Proof.
move=> g h GiG HiG.
have F0: forall j, (j < Nirr G -> j < #|classes G|)%N 
  by move=> j; rewrite NirrE.
pose x i := Ordinal (F0 _ (ltn_ord i)).
have G0: forall j, (j < #|classes G| -> j < Nirr G)%N 
  by move=> j1; rewrite NirrE.
pose y i := Ordinal (G0 _ (ltn_ord i)).
have XY: forall i, x (y i) = i by move=> i; apply/val_eqP.
have YX: forall i, y (x i) = i by move=> i; apply/val_eqP.
pose X := \matrix_(i < Nirr G, j < Nirr G) 
  ('xi_i (repr (enum_val (x j)))).
pose Y := \matrix_(i < Nirr G, j < Nirr G) 
  let C := enum_val (x i) in #|C|%:R * (#|G|%:R^-1 * 'xi_j (repr C))^*.
have F2: X *m Y = 1%:M.
  apply/matrixP=> i j; rewrite !mxE.
  rewrite -irr_first_orthogonal_relation -mulr_sumr cfun_sum; last first.
    by move=> g1 g2 Hg1 Hg2; rewrite !(cfunJ _ (memc_irr _)). 
  rewrite (reindex y) /=; last by apply: onW_bij; exists x=> i1; apply/val_eqP.
  rewrite (reindex (@enum_val _ (fun x => x \in classes G))) /=; last first.
    by apply: (enum_val_bij_in (mem_classes (group1 G))).
  apply: eq_big=> [i1|i1 _]; first by rewrite enum_valP.
  rewrite !mxE /= XY.
  (* mimicking ring *)
  rewrite mulrC -!mulrA; congr (_ * _).
  rewrite rmorphM fmorphV ?conjC_nat //.
  by rewrite -mulrA ['xi_i _ * _]mulrC.
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
apply: eq_bigr=> t _.
rewrite !mxE /= !XY  /toC !enum_rankK_in ?mem_classes //.
case: (repr_class G g)=> g1 Hg1->.
case: (repr_class G h)=> h1 Hh1->.
rewrite !(cfunJ _ (memc_irr _)) // -!mulrA; congr (_ * _).
by rewrite rmorphM fmorphV ?conjC_nat // -mulrA ['xi_t _ * _]mulrC.
Qed.

Lemma irr_conjugate : forall (g h: gT), g \in G -> h \in G ->
  reflect (forall i : Iirr G, 'xi_i g = 'xi_i h) (g \in (h ^: G)).
Proof.
move=> g h GiG HiG; apply: (iffP idP)=> [HH chi|HH].
  case/imsetP: HH=> x Hx ->.
  by rewrite (cfunJ _ (memc_irr _)).
move: (irr_second_orthogonal_relation GiG HiG); case: (_ \in _)=> // HH1.
move: (fun I=> posC_sum_eq0 I HH1) => /=.
rewrite -[index_enum _]enumT.
have F1:  forall i : Iirr G, 
  (i \in enum (ordinal_finType (Nirr G))) && (xpredT i) -> 
     0 <= 'xi_i g * ('xi_i h)^*.
  by move=> i _; rewrite HH /leC subr0 repC_pconj.
case/eqP: (nonzero1r algC).
move: (posC_sum_eq0 F1)=> /=.
move: HH1; rewrite -[index_enum _]enumT => HH1.
move/(_ HH1); move/(_ 0)=> /=.
rewrite !cfuniE genGid GiG HiG conjC1 mul1r; apply=> //.
by rewrite  mem_enum.
Qed.

(* This corresponds to Isaacs' 6.32 *)
Lemma action_irr_class_card : 
  forall (ito : action A (Iirr G))  (cto : action A {set gT}) a,
    a \in A -> [acts A, on (classes G) | cto] -> 
   (forall c (i : Iirr G),
       c \in classes G -> 'xi_i (repr c) = 'xi_(ito i a) (repr (cto c a))) ->
     #|'Fix_ito[a]| = #|'Fix_(classes G| cto)[a]|.
Proof.
move=> ito cto a AiA Acto H.
 (* borrowed to the second orthogonality proof *)
have F0: forall j, (j < Nirr G -> j < #|classes G|)%N 
  by move=> j; rewrite NirrE.
pose f i := Ordinal (F0 _ (ltn_ord i)).
have G0: forall j, (j < #|classes G| -> j < Nirr G)%N 
  by move=> j1; rewrite NirrE.
pose g i := Ordinal (G0 _ (ltn_ord i)).
have FG: forall i, f (g i) = i by move=> i; apply/val_eqP.
have GF: forall i, g (f i) = i by move=> i; apply/val_eqP.
pose X := \matrix_(i < Nirr G, j < Nirr G) 
  (('xi_i) (repr (enum_val (f j)))).
pose Y := \matrix_(i < Nirr G, j < Nirr G) 
  (let C := enum_val (f i) in #|C|%:R * (#|G|%:R^-1 * ('xi_j) (repr C))^*).
have F2: X *m Y = 1%:M.
  apply/matrixP=> i j; rewrite !mxE.
  rewrite -irr_first_orthogonal_relation -mulr_sumr cfun_sum; last first.
    move=> g1 g2 Hg1 Hg2.
    by rewrite !(cfunJ _ (memc_irr _)) ?groupV.
  rewrite (reindex g) /=; last by apply: onW_bij; exists f=> i1; apply/val_eqP.
  rewrite (reindex (@enum_val _ (fun x => x \in classes G))) /=; last first.
    by apply: (enum_val_bij_in (mem_classes (group1 G))).
  apply: eq_big=> [i1|i1 _]; first by rewrite enum_valP.
  rewrite !mxE /= FG mulrC -!mulrA; congr (_ * _).
  by rewrite rmorphM fmorphV ?conjC_nat // -mulrA ['xi_i _ * _]mulrC.
 (****************************************)
pose Pa : 'M[algC]_ _ := 
  \matrix_(i < Nirr G, j < Nirr G) (ito i a == j)%:R.
apply/eqP; rewrite eqN_eqC.
have <-: \tr Pa = #|'Fix_ito[a]|%:R.
  rewrite /mxtrace (bigID (fun u => u \in 'Fix_ito[a])) /=.
  rewrite (eq_bigr (fun u => 1%:R)); last first.
    move=> i; rewrite inE mxE; move/subsetP=> Hi.
    case: eqP=> // Hv; case: Hv; apply/eqP.
    by move: (Hi a); rewrite !inE; apply.
  rewrite sumr_const big1 ?addr0; last first.
    move=> i; rewrite inE mxE; move/subsetP=> Hi.
    by case: eqP=> // Hv; case: Hi=> b; rewrite !inE; move/eqP->; rewrite Hv.
  rewrite -mulr_natl mulr1 /= -(card_imset  (pred_of_set 'Fix_ito[a]) (@enum_rank_inj _)).
  by apply/eqP; rewrite -eqN_eqC; apply/eqP; apply: eq_card=> i.
pose Qa : 'M[algC]_ _ := 
  \matrix_(i < Nirr G, j < Nirr G) (cto (enum_val (f i)) a == (enum_val (f j)))%:R.
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
pose i1 := ito u a. 
(*
have Hi1: ito u a = enum_val i1 by rewrite enum_rankK.
*)
pose j1 := g (enum_rank_in (classes1 G) (otc (enum_val (f v)))).
have Hj1: cto (enum_val (f j1)) a = enum_val (f v).
  by rewrite FG enum_rankK_in ?H2co.
rewrite (bigD1 j1) // big1 /= ?addr0 => [|i Dii1]; last first.
  rewrite !mxE; case: eqP; rewrite ?mulr0 // -Hj1.
  by move/(can_inj H1co); move/enum_val_inj; move/val_eqP=> /==> HH; case/negP: Dii1.
 (* too slow ! 
rewrite (bigD1 i1) // big1 /= ?addr0=> [|i Dii1]; last first.
 *)
have->: \sum_(j < Nirr G) Pa u j * X j v = Pa u i1 * X i1 v.
  rewrite {1}(bigD1 i1) // big1 /= ?addr0=> [|i Dii1] //.
  rewrite !mxE; case: eqP; rewrite ?mul0r // => HH.
  by case/negP: Dii1; rewrite -HH.
rewrite !mxE Hj1 !(eqxx, mulr1, mul1r).
by rewrite H FG enum_rankK_in // H2co.
Qed.

End OrthogonalRelations.

Section InnerProduct.

Variable (gT : finGroupType) (G : {group gT}).

Let card_neq0 : #|G|%:R^-1 != 0 :> algC.
Proof. by rewrite invr_eq0 neq0GC. Qed.

Lemma irr_orthonormal : forall (i j: Iirr G),
   '['xi_i,'xi_j]_G = (i == j)%:R.
Proof. by move=> *; rewrite -irr_first_orthogonal_relation. Qed.

Lemma ncoord_inner_prod : forall A (f : {cfun _}) (i : Iirr G),
   f \in 'CF(G,A) -> ncoord i f = '[f,'xi_i]_G.
Proof.
move=> A f i FiC.
rewrite {2}(ncoord_sum FiC) -inner_prodbE linear_sum.
by rewrite (bigD1 i) // big1=> [|j Hj]; 
   rewrite /= ?addr0 linearZ /= inner_prodbE irr_orthonormal;
    [rewrite eqxx /GRing.scale /= mulr1|rewrite (negPf Hj) scaler0].
Qed.

Lemma inner_prod_cf : forall A (f1 f2 : {cfun gT}),
   f1 \in 'CF(G,A)-> f2 \in  'CF(G,A)->
   '[f1, f2]_G = \sum_(i < Nirr G) ncoord i f1 * (ncoord i f2)^* .
Proof.
move=> A f1 f2; case/(ncoord_sum)=>{1}->;case/(ncoord_sum)=>{1}->.
rewrite -inner_prodbE {1}linear_sum /=.
apply: eq_bigr=> t _; rewrite linearZ /= inner_prodbE.
rewrite raddf_sum  {1}(bigD1 t) // big1 //= ?addr0 => [|j Hj]; last first.
  by rewrite inner_prodZ irr_orthonormal eq_sym (negPf Hj) mulr0.
by rewrite inner_prodZ irr_orthonormal eqxx mulr1; congr (_ * _).
Qed.

Lemma inner_prod_char : forall chi1 chi2,  
  is_char G chi1 -> is_char G chi2 ->
   '[chi1,chi2]_G = 
       \sum_(i < Nirr G) (ncoord i chi1) * (ncoord i chi2).
Proof.
move=> ch1 ch2 IC1 IC2.
rewrite (inner_prod_cf (memc_is_char IC1) (memc_is_char IC2)).
apply: eq_bigr=> t _.
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

Lemma irr_inner_prod_charE : forall chi,
  is_char G chi -> chi \in irr G = ('[chi, chi]_G == 1).
Proof.
move=> chi IC; apply/irrIP/eqP=> [[i <-]|].
  by rewrite irr_orthonormal eqxx.
rewrite inner_prod_char //.
case/is_char_cbP: (IC)=> n Hchi HH.
case: (isNatC_sum_eq1 _ _ HH).
- move=> i _; apply: isNatC_mul;
     rewrite Hchi linear_sum isNatC_sum //= => j _; rewrite linearZ /= ?ncoord_irr;
       apply: isNatC_mul; apply: isNatC_nat.
- by rewrite /index_enum -enumT; exact: enum_uniq.
move=> t [Htn _ HF HG]; exists t.
apply/val_eqP=> /=; apply/eqP.
rewrite (ncoord_sum (memc_is_char IC)).
rewrite (bigD1 t) //= big1 ?addr0=> [|t' Ht']; last first.
  have F1: t' \in index_enum (ordinal_finType (Nirr G)).
    rewrite -[index_enum _]enumT.
    apply/(nthP 0); exists (enum_rank t')=> //.
      case: enum_rank=> /= m; first by rewrite cardT /=.
    by apply/val_eqP; rewrite nth_enum_rank.
  move: (HG _ Ht' F1 is_true_true); move/eqP; rewrite mulf_eq0.
  by case/orP; rewrite Hchi; move/eqP->; rewrite scale0r.
case/isNatCP: (isNatC_ncoord_char t IC) HF=> m ->; move/eqP=> HH1; apply/eqP.
move: HH1; rewrite -natr_mul -(eqN_eqC _ 1); case: m=> //; case => //.
by rewrite scale1r.
Qed.

Lemma irr_conjC : forall (i: Iirr G),  (('xi_i)^*)%CH \in irr G.
Proof.
move=> i; rewrite irr_inner_prod_charE; last first.
  by apply: is_char_conjC; exact: is_char_irr.
rewrite cfun_conjC_inner.
rewrite -conjC1; apply/eqP; congr (_^*); apply/eqP.
by rewrite -irr_inner_prod_charE ?(irr_xi,is_char_irr).
Qed.

Definition irrC (G : {set gT}) (i : Iirr G) :=
  odflt 0 (pick (fun j : Iirr G =>  'xi_j == ('xi_i)^*)%CH).

Lemma irrCE : forall (i : Iirr G), 'xi_(irrC i) = ('xi_i)^*%CH.
Proof.
move=> i; rewrite /irrC; case: pickP=> [j|]; first by move/eqP.
by case/irrIP: (irr_conjC i)=> j <-; move/(_ j); rewrite eqxx.
Qed.

Lemma irrCK : involutive (@irrC G).
Proof. by move=> i; apply: xi_inj; rewrite !irrCE cfun_conjCK. Qed.

End InnerProduct.

Section MoreInnerProd.

Variable gT : finGroupType.

Lemma is_comp_inner_prod_le : 
  forall (G  H : {group gT}) (i : Iirr H) (j : Iirr G) psi,
  is_char G psi -> H \subset G -> is_comp j psi -> 
    '['Res[H]  'xi_j, 'xi_i]_H <= '['Res[H] psi, 'xi_i]_H.
Proof.
move=> G H i j psi IC HsG.
case/(is_comp_charP _ IC)=> chi' IC' ->.
rewrite linearD -!inner_prodbE linearD /= !inner_prodbE.
rewrite addrC -leC_sub addrK.
apply: posC_isNatC.
have FF := memc_restrict HsG (memc_is_char IC').
rewrite -(ncoord_inner_prod _  FF) isNatC_ncoord_char //.
by apply: (is_char_restrict HsG).
Qed.

Lemma is_comp_restrict :
  forall (G H : {group gT}) (i : Iirr H) (j : Iirr G) psi,
    is_char G psi -> H \subset G -> is_comp j psi -> 
    is_comp i ('Res[H] 'xi_j) -> is_comp i ('Res[H] psi).
Proof.
move=> G H i j psi IC HsG Cj Ci.
have CC := is_comp_inner_prod_le i IC HsG Cj.
have FF := (memc_restrict HsG (memc_is_char IC)).
rewrite is_compE (ncoord_inner_prod _ FF).
have CF1 : 'Res[H] 'xi_j \in 'CF(H).
  by apply: (memc_restrict HsG (memc_irr _)).
apply/negP=> HH.
move: Ci.
rewrite is_compE (ncoord_inner_prod _ CF1) //.
case/eqP; apply: leC_anti; first by rewrite -(eqP HH) //.
rewrite -(ncoord_inner_prod _ CF1) // posC_isNatC // isNatC_ncoord_char //.
by apply: is_char_restrict (is_char_irr _).
Qed.

End MoreInnerProd.

Section Kernel.

Variable (gT : finGroupType) (G : {group gT}).

Definition cker (G : {set gT}) (f : {cfun gT}) := 
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

Lemma cker_irrE : forall (i : Iirr G),
  cker G 'xi_i = [set g \in G | 'xi_i g == 'xi_i 1%g].
Proof.  by move=> i; rewrite /cker genGid is_char_irr. Qed.

Lemma cker_NcharE : forall f, ~is_char G f -> cker G f = 1%G.
Proof. by move=> f Hf; rewrite /cker genGid; move/eqP: Hf; case: is_char. Qed.

Lemma cker1 : cker G '1_G = G.
Proof.
rewrite cfuni_xi0 cker_irrE -cfuni_xi0.
apply/setP=> g; rewrite inE !ffunE group1.
by case: (_ \in _)=> //; rewrite eqxx.
Qed.

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
               \bigcap_(i < Nirr G | is_comp i chi) cker G 'xi_i.
Proof.
move=> chi IC; rewrite cker_charE //.
case: eqP=> [->|].
  by apply/setP=> g; rewrite !inE !ffunE eqxx andbT.
have NS := ncoord_sum (memc_is_char IC).
move/eqP=> Hdc; apply/setP=> g; apply/idP/bigcapP=> [|Hi]; last first.
  have InG: g \in G.
    case/(is_comp_neq0 (memc_is_char IC)): Hdc=> j; move/(Hi _).
    by rewrite cker_irrE // inE; case/andP.
  rewrite inE /= NS.
  rewrite !sum_ffunE !ffunE InG.
  apply/eqP; apply: eq_bigr=> i _; rewrite ffunE [_ 1%g]ffunE.
  case: (boolP (is_comp i chi))=> [Hc|].
    by move: (Hi _ Hc); rewrite cker_irrE // inE InG /=; move/eqP->.
  by rewrite negbK; move/eqP->; rewrite !scale0r.
rewrite inE; case/andP=> InG.
rewrite NS !sum_ffunE !ffunE.
move/eqP=> Hs t; rewrite cker_irrE // !inE InG.
have->:
   [ffun x : gT => 
                  \sum_(i < Nirr G) (ncoord i chi *: 'xi_i) x] = chi.
  by apply/ffunP=> x; rewrite ffunE {2}NS sum_ffunE ffunE.
move=> Hd.
pose c := ncoord t chi *: 'xi_t. 
have F: c g =  c 1%g.
  have F1: 0 <= ncoord t chi by apply: posC_isNatC; rewrite isNatC_ncoord_char.
  apply: (normC_sum_upper _ Hs)=> [t' Ht'|]; last first.
    by rewrite -[index_enum _]enumT mem_enum.
  have F2: 0 <= ncoord t' chi
    by apply: posC_isNatC; rewrite isNatC_ncoord_char.
  rewrite ffunE [_ 1%g]ffunE !normC_mul //.
  rewrite normC_pos // leC_mul2l //.
  by apply: is_char_norm (is_char_irr _).
apply/eqP; apply: (mulfI Hd).
by move: F; rewrite /c ffunE [_ 1%g]ffunE.
Qed. 

Lemma cker_all1 : \bigcap_(i < Nirr G) cker G 'xi_i = 1%G.
Proof.
apply/setP=> g; apply/idP/idP; rewrite inE; last first.
  move/eqP->; apply/bigcapP=> i _.
  by rewrite cker_irrE // inE group1 eqxx.
have F1: (\bigcap_(i < Nirr G) cker G 'xi_i) \subset cker G (reg_cfun G).
  rewrite ckerE ?is_char_reg //.
  case: eqP=> Heq.
    have: reg_cfun G 1%g = 0 by rewrite Heq ffunE.
    rewrite ffunE group1 repr_mx1 mxtrace1 mul1r.
    by move/eqP; rewrite genGidG (negPf (neq0GC G)).
  by apply/subsetP=> h; move/bigcapP=> Hi; apply/bigcapP=> j _; exact: Hi.
move/(subsetP F1); rewrite cker_charE ?is_char_reg //.
rewrite inE !reg_cfunE //.
case/andP=> InG; rewrite eqxx; case: (g == 1%g)=> //.
by rewrite eq_sym (negPf (neq0GC G)).
Qed.

Lemma is_comp_cker : forall (i : Iirr G) chi,
  is_char G chi -> is_comp i chi -> cker G chi \subset cker G 'xi_i.
Proof.
move=> i chi IC HC.
rewrite ckerE //; case: eqP=> HH; last by apply: (bigcap_min i).
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
  by rewrite inE !ffunE H1 H2 repr_mx1 !group1 mul1r mxtrace1 eqxx.
have InG: g \in G by move: Hg; rewrite inE; case/andP.
split=> //.
have F1: (<[g]> \subset G) by rewrite cycle_subG.
pose rG' := subg_repr rG F1.
have H'g: g \in cker <[g]> (char_of_repr <[g]> rG').
  move: Hg; rewrite /cker genGid ?is_char_char_of_repr //.
  by rewrite /rG' !inE !ffunE !group1 !InG cycle_id !mul1r.
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
rewrite !ffunE groupM ?YiG // repr_mxM //.
move: GiC; rewrite char_rkerP // inE GiG mul1mx andTb; move/eqP->.
by rewrite HiG mul1mx.
Qed.

Lemma char_ckerMl : forall chi g h,
  is_char G chi -> g \in cker G chi -> h \in G -> chi (h * g)%g = chi h.
Proof.
move=> chi g h.
case/is_charP=> // n [rG <-] GiC HiG.
have GiG: g \in G by apply: (subsetP (cker_sub (char_of_repr G rG))).
rewrite !ffunE groupM ?YiG // repr_mxM //.
move: GiC; rewrite char_rkerP // inE GiG mul1mx andTb; move/eqP->.
by rewrite HiG mulmx1.
Qed.

Lemma char_ckerJ : forall chi g h,
  is_char G chi -> g \in cker G chi -> h \in G -> chi (h ^ g)%g = chi h.
Proof.
move=> chi g h Cc GiG HiG.
rewrite (char_ckerMr Cc) ?(groupV,groupM) ?(char_ckerMl Cc) //.
by apply: (subsetP (cker_sub chi)).
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
by apply/ffunP=> M; rewrite !ffunE repr_quo_fact1.
Qed.

Lemma qfuncE : forall (G N : {group gT}) f x,
 is_char G f -> N <| G -> N \subset cker G f -> x \in G -> 
  (f / N)%CH (coset N x) = f x.
Proof.
move=> G N f x Cf NN  Ncker InG; rewrite !ffunE.
rewrite val_coset //; last by apply: (subsetP (normal_norm NN)).
case: repr_rcosetP=> y Hy.
by apply: (char_ckerMr Cf)=> //; apply: (subsetP Ncker).
Qed.

Lemma is_char_cfunq : forall (G N : {group gT}) f,
  N <| G -> is_char (G/N)%G f -> is_char G (f^())%CH.
Proof.
move=> G N f NN; case/is_charP=> n [rG <-].
pose rG' := coset_repr rG NN.
suff->: ((char_of_repr (G/N)%g rG)^())%CH = char_of_repr G rG' 
  by apply: is_char_char_of_repr.
apply/ffunP=> M; rewrite !ffunE mulrA -natr_mul mulnb.
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

Lemma cfunqK : forall (G N : {group gT}) f,
 is_char (G/N)%G f -> N <| G -> (f^()/ N)%CH = f.
Proof.
move=> G N f Cf HN.
have F1: is_char G (f^())%CH by apply: is_char_cfunq.
have F2:= cker_cfunq Cf HN.
have F3: is_char (G/N)%G (f^() / N)%CH by apply: is_char_qfunc.
apply/ffunP=> x.
case: (boolP (x \in (G/N)%g))=> [|InG]; last first.
  rewrite (cfun0 (memc_is_char Cf)) //.
  by apply: (cfun0 (memc_is_char F3)).
rewrite -imset_coset; case/imsetP=> y InG ->.
rewrite (@qfuncE G) //  cfunqE //.
by apply: (subsetP (normal_norm HN)).
Qed.

Lemma qfuncK : forall (G N : {group gT}) f,
 is_char G f -> N <| G -> N \subset cker G f -> ((f/N)^())%CH = f.
Proof.
move=> G N f Cf HN Hc.
have F1: is_char (G/N)%G (f/N)%CH by apply: is_char_qfunc.
have F2: is_char G ((f/N)^())%CH by apply: is_char_cfunq.
apply/ffunP=> x.
case: (boolP (x \in G))=> InG; last first.
  rewrite (cfun0 (memc_is_char Cf)) //.
  apply: (cfun0 (memc_is_char F2))=> //.
rewrite cfunqE ?(@qfuncE G) //.
by apply: (subsetP (normal_norm HN)).
Qed.

Lemma irr_qfunc : forall (G N : {group gT}) (i : Iirr G),
 N <| G -> N \subset cker G 'xi_i -> ('xi_i/N)%CH \in irr (G/N)%G.
Proof.
move=> G N i.
case/irrP: (irr_xi i)=> j <- NnG.
rewrite char_rkerP=> Cf.
pose rG := quo_repr Cf (normal_norm NnG).
apply/irrIP.
pose sG := DecSocleType (regular_repr algC (G/N)%G).
exists (irr_of_socle (irr_comp sG rG)).
apply/ffunP=> x;rewrite irr_of_socleE.
have F1: mx_irreducible rG.
  by apply/quo_mx_irr=> //; apply: socle_irr.
have F2: ([char algC]^').-group (G / N)%G.
  by apply: sub_pgroup (pgroup_pi _)=> i' _; rewrite inE /= Cchar.
move/(rsim_irr_comp sG F2): F1.
move/char_of_repr_rsimP; move/eqP<-.
by rewrite /rG !ffunE repr_quo_fact1.
Qed.

Lemma irr_cfunq : forall (G N : {group gT}) (i : Iirr (G/N)%G),
 N <| G ->  (('xi_i)^())%CH \in irr G.
Proof.
move=> G N i; case/irrP: (irr_xi i)=> j <- NnG.
pose rG := coset_repr (irr_repr j) NnG.
pose sG := DecSocleType (regular_repr algC G).
apply/irrIP; exists (irr_of_socle (irr_comp sG rG)).
rewrite irr_of_socleE.
apply/ffunP=> x.
have F1: mx_irreducible rG.
  apply/(quo_mx_irr (coset_repr_rker (irr_repr j) NnG) (normal_norm NnG)).
  apply: (mx_rsim_irr (mx_rsim_sym (rsim_quo_coset (irr_repr j) NnG))).
  by apply: socle_irr.
move/(rsim_irr_comp sG (pGroupG G)): F1.
move/char_of_repr_rsimP; move/eqP<-.
rewrite /rG !ffunE.
by rewrite  mulrA -natr_mul mulnb repr_quo_fact2.
Qed.

Lemma norm_cap_cker : forall (G N : {group gT}), N <| G ->  
   N = \bigcap_(i < Nirr G | N \subset cker G 'xi_i) (cker G 'xi_i) :> {set _}.
Proof.
move=> G N NnG; apply/eqP; rewrite eqEsubset; apply/andP; split.
  by  apply/bigcapsP.
apply/subsetP=> g; move/bigcapP=> Hg.
have InG : g \in G.
  case/irrIP: (irr_cfunq 0 NnG)=> j Hj.
  apply: (subsetP (cker_sub G 'xi_j)). 
  apply: Hg; rewrite Hj; apply: cker_cfunq=>//; exact: is_char_irr.
have InN: g \in 'N(N) by apply: (subsetP (normal_norm NnG)).
suff: coset N g \in \bigcap_(i < Nirr (G/N)%G) cker (G/N)%G 'xi_i.
  by rewrite cker_all1; move/set1P; move/coset_idr; apply.
apply/bigcapP=> i _.
case/irrIP: (irr_cfunq i NnG)=> j Hj.
have: g \in cker G 'xi_j by apply: Hg; rewrite Hj cker_cfunq // is_char_irr.
rewrite /cker !genGid !(is_char_irr) !inE -(repr_quo_fact2 _ NnG) InN.
rewrite Hj !cfunqE ?group1 //.
suff->: coset N 1%g  = 1%g by [].
by apply: coset_id; exact: group1.
Qed.

Definition cirrq (G H : {group gT}) (i : Iirr (G/H)%G) := 
  irr_of_socle (socle_of_cfun G (('xi_i) ^())%CH).

Lemma cirrqE : forall (G H : {group gT}) (i : Iirr (G/H)%G), 
  H <| G -> 'xi_(cirrq i) = ('xi_i)^()%CH.
Proof. 
move=> G H i HnG; case/irrP: (irr_cfunq i HnG)=> j Hj.
by rewrite /cirrq -Hj socle_of_cfunE irr_of_socleE Hj.
Qed.

Definition qirrc (G H : {group gT}) (i : Iirr G) := 
  irr_of_socle (socle_of_cfun (G/H)%G (('xi_i) / H)%CH).

Lemma qirrcE : forall (G H : {group gT}) (i : Iirr G), 
  H <| G -> H \subset cker G 'xi_i -> 'xi_(qirrc H i) = (('xi_i)/H)%CH.
Proof.
move=> G H i HnG HsC; case/irrP: (irr_qfunc HnG HsC)=> j Hj.
by rewrite /qirrc -Hj socle_of_cfunE irr_of_socleE Hj.
Qed.

Lemma cirrqK : forall (G H : {group gT}),
  H <| G -> cancel (@cirrq G H) (@qirrc G H).
Proof.
move=> G H HnG i.
apply: xi_inj; rewrite qirrcE // cirrqE ?cker_cfunq //.
  rewrite (cfunqK (is_char_irr _)) //.
by exact: is_char_irr.
Qed.

Lemma qirrcK : forall (G H : {group gT}) (i : Iirr G),
  H <| G ->  H \subset cker G 'xi_i -> cirrq (qirrc H i) = i.
Proof.
move=> G H i HnG HsC; apply: xi_inj.
have Ii := is_char_irr i.
by rewrite cirrqE // qirrcE // (qfuncK Ii).
Qed.

Lemma sum_norm_quo : forall (H G : {group gT}) g,
   g \in G -> H <| G ->
    \sum_(i < Nirr (G/H)%G) ('xi_i (coset H g)) * ('xi_i (coset H g))^* =
    \sum_(i < Nirr G | H \subset cker G 'xi_i) ('xi_i g) * ('xi_i g)^*.
Proof.
move=> H G g GiG HnG.
rewrite (reindex (@cirrq G H)) //=.
  apply: eq_big=> i.
    by rewrite cirrqE // cker_cfunq // is_char_irr.
  by move=> _; rewrite cirrqE // cfunqE // (subsetP (normal_norm HnG)).
exists (@qirrc G H)=> i; rewrite !inE => HH; first by rewrite cirrqK //.
by rewrite qirrcK.
Qed.

Lemma norm_cker : forall (G N : {group gT}), N <| G ->  
   N = cker G ((reg_cfun (G/N)%g) ^())%CH :> {set _}.
Proof.
move=> G N NnG; apply/setP=> g.
rewrite /cker genGid is_char_cfunq ?inE //; last first.
  rewrite /reg_cfun -[(_/_)%G]genGidG -{2}[(_/_)%g]genGid.
  apply: is_char_char_of_repr.
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

Section Derive.

Variable gT : finGroupType.

Lemma clinear_commutator_irr : forall (G : {group gT}) (i : Iirr G),
  clinear G 'xi_i = (G^`(1) \subset cker G 'xi_i)%g.
Proof.
move=> G i; apply/idP/idP=> [|GsC]; first by apply: clinear_commutator.
have F1 : abelian (G/G^`(1)) := der_abelian 0 G.
move/char_abelianP: F1; move/(_ (qirrc (G^`(1))%G i))=> HH.
rewrite /clinear genGid is_char_irr.
rewrite -(qfuncK (is_char_irr _) (der_normal 1 G) GsC).
rewrite cfunqE ?group1 //.
have->: coset (G^`(1))%G 1%g = 1%g.
  by apply: coset_id; exact: group1.
by case/andP: HH; rewrite qirrcE // der_normal.
Qed.

(* This corresponds to Isaacs' 2.23(a) *) 
Lemma derive_at_cap : forall (G : {group gT}),
   (G^`(1) = \bigcap_(i < Nirr G | clinear G 'xi_i) cker G 'xi_i)%g.
Proof.
move=> G; rewrite (norm_cap_cker (der_normal 1 G)).
by apply: eq_bigl=> i; rewrite clinear_commutator_irr.
Qed.

(* Isaacs' 2.23(b) *)
Lemma card_linear : forall (G : {group gT}),
  #|[pred i : Iirr G | clinear G 'xi_i]| = #|G : G^`(1)%g|.
Proof.
move=> G.
have F1 := der_normal 1 G.
rewrite -card_quotient ?normal_norm //.
move: (der_abelian 0 G); rewrite card_classes_abelian; move/eqP<-. 
rewrite -NirrE.
have->: (G^`(0) = G)%G by apply/val_eqP=> //.
rewrite -[X in _ = X]card_ord.
rewrite -(card_imset _ (can_inj (cirrqK F1))).
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
rewrite [\sum_i(_)](bigID (fun i : Iirr G => N \subset cker G 'xi_i)) //=.
rewrite -{1}[\sum_(i|_)(_)]addr0 leC_add2l.
apply: posC_sum=> i _.
by rewrite /leC subr0; exact: repC_pconj.
Qed.

End Derive.

Section Center.

Variable (gT : finGroupType) (G : {group gT}).

Definition ccenter (G : {set gT}) (f : {cfun gT}) := 
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
    by rewrite !ffunE !(flatmx0 (rG _)) !mxtrace0 !mulr0 normC0 eqxx.
  move=> Hc; rewrite ffunE InG mul1r Hc mxtrace_scalar char_of_repr1.
  by rewrite -mulr_natr normC_mul (rcenter_norm Hn InG Hc) 
              mul1r normC_nat eqxx.
rewrite InG; move/eqP=> HH.
have F1: (<[g]> \subset G) by rewrite cycle_subG.
pose rG' := subg_repr rG F1.
have HH': normC (char_of_repr <[g]> rG' g) = char_of_repr <[g]> rG' 1%g.
  by move: HH; rewrite /rG' !ffunE !group1 !InG cycle_id.
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

Lemma irr_ccenterE : forall (i : Iirr G) g,
  g \in G -> g \in ccenter G 'xi_i = (normC ('xi_i g) == 'xi_i 1%g).
Proof.
by move=> i g GiG; rewrite /ccenter genGid (is_char_irr i) inE GiG.
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
rewrite inE !ffunE; case/andP=> GiG; case/is_scalar_mxP=> k rGK HiG.
by rewrite !(groupM,GiG,HiG,mul1r) // !repr_mxM // rGK scalar_mxC.
Qed.

(* Isaacs' 2.27b *)
Canonical Structure ccenter_group f := Group (ccenter_group_set f).

(* Isaacs' 2.27b *)
Lemma ccenter_sub : forall f, ccenter G f \subset G.
Proof.
move=> f; case: (boolP (is_char G f))=> Hf.
  by rewrite /ccenter genGid Hf; apply/subsetP=> g; rewrite inE; case/andP.
rewrite /ccenter genGid (negPf Hf).
by apply/subsetP=> g; rewrite inE; move/eqP->; exact: group1.
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
have F1 := memc_is_char (idP E1).
rewrite !inE; apply/imsetP/idP.
  case=> l; rewrite inE; case/andP=> LiG Hn ->.
  by rewrite groupJ // (cfunJ _ F1) ?Hn.
case/andP=> HiG NcH; exists (h ^(g^-1))%g; last first.
  by rewrite -conjgM mulVg conjg1.
by rewrite inE groupJ ?groupV // (cfunJ _ F1) ?groupV.
Qed.

(* Isaacs' 2.27c *)
Lemma ccenter_restrict : forall chi,
  exists2 chi1,
     clinear  (ccenter G chi) chi1 & 
     'Res[ccenter G chi] chi =  (chi 1%g) *: chi1.
Proof.
move=> chi.
case: (boolP (is_char G chi))=> IC; last first.
  rewrite /ccenter genGid (negPf IC) //.
  exists ('1_1%G); first exact: clinear1.
  apply/ffunP=> g; rewrite !ffunE.
  case: (boolP (g \in 1%G)); last first.
    by rewrite mul0r [_ *: _]mulr0.
  by move/set1gP->; rewrite mulrC.
case/is_charP: IC=> [] [|n] [rG Hc].
  exists ('1_[group of ccenter G chi]); first exact: clinear1.
  apply/ffunP=> g.
  by rewrite -Hc !ffunE !(flatmx0 (rG _)) mxtrace0 !mulr0 scale0r.
pose repr g := ((rG g 0 0)%:M : 'M_(1,1)).
have Mx: mx_repr  [group of ccenter G chi] repr.
  split=> [| g h]; first by rewrite /repr repr_mx1 mxE eqxx.
  rewrite /= -Hc  char_rcenterP /rcenter !inE.
  case/andP=> InG; case/is_scalar_mxP=> k1 Hk1.
  case/andP=> InH; case/is_scalar_mxP=> k2 Hk2.
  by rewrite /repr repr_mxM // Hk1 Hk2 -!scalar_mxM !mxE !mulr1n.
exists (char_of_repr (ccenter G chi) (MxRepresentation Mx)).
  rewrite /clinear genGid is_char_char_of_repr.
  by rewrite ffunE group1 mul1r repr_mx1 mxtrace1 eqxx.
apply/ffunP=> g; rewrite !ffunE /=.
case: (boolP (g \in _))=> InG; last by rewrite !mul0r scaler0.
rewrite !mul1r.
move: InG; rewrite -Hc char_rcenterP /rcenter !inE.
case/andP=> InG; case/is_scalar_mxP=> k1 Hk1.
rewrite /repr !ffunE InG group1 Hk1 repr_mx1 !mul1r !mxE.
by rewrite  !mxtrace_scalar !mulr1n [_ *: _]mulr_natl.
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
   rewrite /CG /ccenter genGid IC !ffunE !inE.
   rewrite group1 /=; case E1: (g \in G)=> //=.
   rewrite [normC (chi 1%g)]normC_pos; last first.
     by apply: posC_isNatC; apply: isNatC_char1 IC.
   case: (normC _ =P _); first by rewrite eqxx !mul1r.
   case: (_ =P _)=> // HH HH1; case: HH1; rewrite HH.
   by rewrite normC_pos // posC_isNatC // (isNatC_char1 IC).
have F3 : cker CG ('Res[CG] chi)%CH = cker CG l.
   rewrite /cker /CG genGid  (is_char_restrict (ccenter_sub _)) //.
   rewrite (is_char_linear H1l).
   apply/setP=> g; rewrite !inE H2l !ffunE.
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
    by rewrite (cker_char1 GiK) (clinear_val1 H1l) mul1r.
  by rewrite (subsetP (normal_sub (cker_center_normal _))) // F2 F3.
apply: (@field_mul_group_cyclic _ _ _ m).
  move=> /= C1 C2; case/Fm=> c1 [H1c1 H2c1 -> ->]; case/Fm=> c2 [H1c2 H2c2 -> ->].
  rewrite /m /= !val_coset // rcoset_mul //.
  case: repr_rcosetP=> k InK.
  by rewrite !(clinearM H1l) ?groupM // 
             ?(cker_char1 InK, clinear_val1 H1l, mul1r) //
             (subsetP (normal_sub (cker_center_normal _))) // F2 F3.
move=> C; case/Fm=> c [H1c H2c -> ->].
split=> [HH|/(coset_idr H1c)].
  rewrite coset_id // cker_charE ?is_char_linear //.
  by rewrite inE HH (clinear_val1 H1l) eqxx andbT.
rewrite /= cker_charE  ?is_char_linear // inE (clinear_val1 H1l)  //.
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
Lemma ccenter_eq_center : forall i : Iirr G, 
  (ccenter G 'xi_i / cker G 'xi_i)%g ='Z(G / cker G 'xi_i)%g.
Proof.
move=> i.
apply/eqP; rewrite eqEsubset.
rewrite ccenter_subset_center ?is_char_irr //.
apply/subsetP=> C1; case: (@cosetP _ _ C1)=> g Hg -> HH.
have GiG: g \in G.
  move: HH; rewrite inE; case/andP.
  case/imsetP=> h; rewrite inE; case/andP=> H1h H2h.
  move/(rcoset_kercosetP Hg H1h)=> //.
  case/rcosetP=> l H1l -> _; rewrite groupM //.
  by move: l H1l; apply/subsetP; exact: cker_sub.
apply: mem_quotient.
suff: g \in ccenter G 'xi_i by [].
case/irrP: (irr_xi i)=> j Hj.
rewrite -Hj char_rcenterP /rcenter inE GiG.
have F1:  mx_absolutely_irreducible (irr_repr j).
  by apply: groupC; apply: socle_irr.
apply: (mx_abs_irr_cent_scalar F1).
apply/subsetP=> h HiG.
have HiN: h \in 'N(cker G 'xi_i).
  by apply: (subsetP (normal_norm (cker_normal G 'xi_i))).
set rGj := irr_repr _.
rewrite inE HiG -{1}repr_mxM //.
have F2 : (g * h)%g  \in (coset (cker G 'xi_i) g * coset (cker G 'xi_i) h)%g.
  apply/imset2P=> /=.
  by exists (g : gT) (h : gT)=> //;
     rewrite val_coset //; apply/rcosetP; exists 1%g; rewrite // mul1g.
move: F2; case/centerP: HH=> _; move/(_ (coset (cker G 'xi_i) h))->; last first.
  by apply: mem_quotient.
case/imset2P=> g1 h1.
rewrite val_coset //; case/rcosetP=> g2 Hg2 ->.
rewrite val_coset //; case/rcosetP=> h2 Hh2 -> ->.
rewrite !repr_mxM ?groupM // ?(subsetP (cker_sub G 'xi_i)) //.
have: g2 \in rker rGj by rewrite -char_rkerP Hj.
rewrite inE; case/andP=> _; rewrite {1}mul1mx; move/eqP->; rewrite {1}mul1mx.
have: h2 \in rker rGj by rewrite -char_rkerP Hj.
rewrite inE; case/andP=> _; rewrite {1}mul1mx; move/eqP->; rewrite {1}mul1mx.
by rewrite eqxx.
Qed.

Lemma center_sub_quo : forall (M N : {group gT}),
  N <| M -> ('Z(M) / N \subset 'Z(M / N))%g.
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
Lemma center_bigcap : 'Z(G) = \bigcap_(i < Nirr G) ccenter G 'xi_i.
Proof.
apply/setP=> g; apply/idP/idP=> [GiZ|].
  have GiG: g \in G by apply: (subsetP (center_sub G)).
  apply/bigcapP=> i _.
  have: coset (cker G 'xi_i) g \in (ccenter G 'xi_i/(cker G 'xi_i))%g.
    rewrite ccenter_eq_center.
    apply: (subsetP (center_sub_quo (cker_normal _ _))).
    by apply: mem_quotient.
  case/imsetP=> h; rewrite inE; case/andP=> H1h H2h /=.
  move/val_eqP; rewrite /= !val_coset //; last first.
    by apply: (subsetP (normal_norm (cker_normal G 'xi_i))).
  move=> HH; move: GiG.
  have: g \in  cker_group G 'xi_i :* g.
    by apply/rcosetP; exists (1%g); rewrite ?(group1,mul1g).
  rewrite (eqP HH); case/rcosetP=> l /= LiC -> LHiG.
  have LiG: l \in G by apply: (subsetP (cker_sub G 'xi_i)).
  have HiG: h \in G by apply: (subsetP (ccenter_sub 'xi_i)).
  case/irrP: (irr_xi i)=> j Hj.
  rewrite -Hj char_rcenterP inE LHiG.
  move: LiC; rewrite -Hj char_rkerP inE mul1mx {1}repr_mxM //.
  case/andP=> InL; move/eqP->; rewrite mul1mx.
  by move: H2h; rewrite -Hj char_rcenterP inE; case/andP.
move/bigcapP=> HH.
have GiG: g \in G.
  apply: (subsetP (ccenter_sub ('1_G))).
  by case/irrIP: (irr_cfuni G)=> i <-; apply: HH.
apply/centerP; split=> //.
move=> h HiG; apply/commgP.
suff: [~ g, h] \in 1%G by rewrite inE.
rewrite -(cker_all1 G); apply/bigcapP=> i _.
case/irrP: (irr_xi i)=> j Hj.
rewrite -Hj char_rkerP inE groupR // mul1mx.
set rGj := irr_repr _.
rewrite !repr_mxM ?(groupV,groupJ,groupM) //.
have: is_scalar_mx (rGj g).
  by move: (HH i is_true_true); rewrite -Hj char_rcenterP inE GiG.
case/is_scalar_mxP=> k Hk; rewrite Hk -scalar_mxC {1}mulmxA {1}mulmxA.
rewrite -Hk andTb; apply/eqP.
  (* Too slow
rewrite  {1}(repr_mxKV rGi InH).
*)
have->: rGj (g^-1)%g *m rGj (h^-1)%g *m rGj h *m rGj g = rGj (g^-1)%g *m rGj g.
   by congr (_ *m _); apply: (repr_mxKV rGj HiG).
by rewrite -repr_mxM ?groupV // mulVg repr_mx1.
Qed.
 
Lemma inner_subl: forall (H : {group gT}) (f1 f2 : {cfun _}), 
  H \subset G ->  (forall g, g \in G :\: H -> f1 g = 0) -> 
  '[f1, f2]_H = #|G : H|%:R * '[f1, f2]_G.
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
  H \subset G ->  '['Res[H] f,'Res[H] f]_H <= #|G : H|%:R * '[f, f]_G ?= iff
      (forallb g : gT, (g \in G:\:H) ==> (f g == 0)).
Proof.
move=> H f HsG; rewrite inner_subl // => [|i]; last first.
  by rewrite !ffunE inE; case/andP; move/negPf->; rewrite mul0r.
apply/leCifP; case: (boolP (forallb b:_, _)).
  move/forall_inP=> Hi; apply/eqP.
  congr(_ * _); rewrite !inner_prodE; congr (_ * _); apply: eq_bigr=> g InG.
  rewrite !ffunE; case E1: (g \in H); rewrite (mul0r,mul1r) //.
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
rewrite !ffunE; move/negPf->; rewrite !mul0r add0r.
rewrite -sumr_sub posC_sum // => i; case/andP=> _;case/andP=> HH _.
by rewrite !ffunE; case: (_ \in _); 
   rewrite !(mul0r,mul1r,subrr,subr0, (posC_nat 0),posC_pconj).
Qed.

(* This is 2.30 *)
Lemma irr1_bound : forall (i : Iirr G),
  ('xi_i 1%g) ^+ 2 <= #|G : ccenter G 'xi_i|%:R ?= iff
      (forallb g : gT, (g \in G:\:ccenter G 'xi_i) ==> ('xi_i g == 0)).
Proof.
move=> i.
pose CG := (ccenter G 'xi_i).
have F1 : CG \subset G by apply: (ccenter_sub _).
rewrite -[_%:R]mulr1.
have:= (irr_xi i).
rewrite irr_inner_prod_charE ?is_char_irr //.
move/eqP=>HH; rewrite -{2}HH.
suff{HH}->: ('xi_i 1%g)^+2 = '['Res[CG] 'xi_i, 'Res[CG] 'xi_i]_CG.
  by apply: crestrict_sub_inner_bound.
case (@ccenter_restrict 'xi_i)=> l Hl ->.
rewrite inner_prodZ -inner_prodbE linearZ /= inner_prodbE.
move: (clinear_irr Hl).
rewrite irr_inner_prod_charE ?is_char_linear //.
move/eqP->.
rewrite ?expr2 isNatC_conj /GRing.scale /= ?mulr1 //.
by apply: (isNatC_char1 (is_char_irr _)).
Qed.
  
(* This is 2.31 *)
Lemma irr1_abelian_bound : forall (i : Iirr G),
   abelian (G / ccenter G 'xi_i) -> 
     ('xi_i 1%g) ^+ 2 = #|G : ccenter G 'xi_i|%:R.
Proof.
move=> i AbGc; apply/eqP; rewrite irr1_bound.
apply/forall_inP=> g; rewrite inE; case/andP=> NInC GiG.
have GiN := subsetP (normal_norm (cker_normal G 'xi_i)) _ GiG.
pose CC := ccenter G 'xi_i.
have: coset (cker G 'xi_i) g \notin ([group of CC]/cker G 'xi_i)%G.
  apply/negP; case/imsetP=> /= h; rewrite inE; case/andP=> HiN HiC.
  have HiG: h \in G by apply: (subsetP (ccenter_sub 'xi_i)).
  move/rcoset_kercosetP; move/(_ GiN HiN); case/rcosetP=> u Hu Hg.
  have UiG: u \in G by apply: (subsetP (cker_sub G 'xi_i)).
  case/negP: NInC; rewrite Hg.
  rewrite irr_ccenterE ?groupM // (char_ckerMr (is_char_irr _)) //.
  by rewrite -irr_ccenterE.
rewrite  /= (ccenter_eq_center i) => H.
case: (boolP (existsb h: gT, 
               (h \in G) && ([ ~ g, h] \notin cker G 'xi_i))); last first.
  rewrite negb_exists_in; move/forall_inP=> HH.
  case/negP: H; apply/centerP; split=> /=.
    by apply: mem_quotient.
  move=> N; case: (@cosetP _ _ N)=> h H1h -> H2h.
  apply/commgP.
  suff<-: coset (cker G 'xi_i) [~ g,h] = 1%g.
    by rewrite /commg /conjg !morphM ?(groupM,groupV) // !morphV.
  have HiG: h \in G.
    case/imsetP: H2h=> l; rewrite inE; case/andP=> H1l H2l.
    move/(rcoset_kercosetP H1h H1l).
    case/rcosetP=> k Hk ->; rewrite groupM //.
    by apply: (subsetP (normal_sub (cker_normal _ 'xi_i))).
  by apply: coset_id; move: (HH _ HiG); rewrite negbK.
case/existsP=> h; case/andP=> HiG CNiK.
have HiN: h \in 'N(ccenter G 'xi_i).
  by apply: (subsetP (normal_norm (ccenter_normal _))).
have GiNc: g \in 'N(ccenter G 'xi_i).
  by apply: (subsetP (normal_norm (ccenter_normal _))).
have CiC :  [~ g, h] \in ccenter G 'xi_i.
  apply: coset_idr; first by rewrite groupR.
  rewrite /commg /conjg !morphM ?(groupM,groupV,morphV) //=.
  suff->: commute (coset (ccenter G 'xi_i) g) (coset (ccenter G 'xi_i) h).
    by rewrite !mulgA mulgKV mulVg.
  move: AbGc; rewrite abelianE; move/subsetP.
  move/(_ _ (mem_quotient [group of CC] GiG)); move/centP.     
  by move/(_ _ (mem_quotient [group of CC] HiG)).
have: 'xi_i (g * [~ g, h])%g = 'xi_i (g).
  by rewrite -conjg_mulR (cfunJ _ (memc_irr i)).
case/is_charP: (is_char_irr i)=> //= n [rG HrG].
move: CiC CNiK; rewrite -!HrG char_rkerP inE mul1mx=> CiC.
have RiG: [~ g, h] \in G by rewrite groupR.
rewrite !ffunE ?RiG groupM ?(GiG,RiG,group1,mul1r) // repr_mxM //.
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
Lemma irr_faithful_center: forall i : Iirr G, cfaithful G 'xi_i -> cyclic ('Z(G)).
Proof.
move=> i; move/trivgP=> HH.
rewrite (isog_cyclic (isog_center (quotient1_isog G))) -HH.
rewrite /= -ccenter_eq_center.
apply: ccenter_cyclic; first by apply: is_char_irr.
apply/negP; move/eqP; move/ffunP; move/(_ 1%g)=> HH1.
by case/negP: (irr1_neq0 i); rewrite HH1 ffunE.
Qed.

(* 2.32b *)
Lemma pgroup_cyclic_faithful: forall p : nat, 
  p.-group G -> cyclic 'Z(G) -> exists i : Iirr G, cfaithful G 'xi_i.
Proof.
 (* Lengthly Proof!! *)
move=> p PG CZG.
case: (boolP (G == 1%g :> {set _}))=> [HG1|DG].
  exists 0; rewrite /cfaithful /=.
  by move/eqP: HG1<-; exact: cker_sub.
case/(pgroup_pdiv PG): (DG) => Pp Dp [m Hm].
case: (boolP (forallb i : Iirr G, cker G 'xi_i != 1%g)); last first.
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
    elim/big_prop: _ => [|x y Hx Hy|]; rewrite ?(dvdn0,dvdn_addr) //=.
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

Variable (G H : {group gT}).

Lemma cinduced_eq0: forall chi,
  H \subset G -> is_char H chi -> ('Ind[G,H] chi == 0) = (chi == 0%CH).
Proof.
move=> chi HsG IC; apply/eqP/eqP=>[|->]; last first.
  by apply/ffunP=> g; rewrite !ffunE big1 ?mulr0 // => h _; rewrite ffunE.
move/ffunP; move/(_ 1%g); rewrite cinduced1 // ffunE.
move/eqP; rewrite mulf_eq0; case/orP.
  rewrite -(eqN_eqC _ 0).
  by case: #|_:_| (indexg_gt0 G H).
by rewrite -(character0_eq0 IC); move/eqP.
Qed.

Lemma is_char_induced : forall chi,
   is_char H chi -> H \subset G -> is_char G ('Ind[G,H] chi).
Proof.
move=> chi IC HsG; have IiC := memc_induced HsG (memc_is_char IC).
apply/andP; split; rewrite ?genGid //; apply/forallP=> t.
rewrite (ncoord_inner_prod _ IiC) // -frobenius_reciprocity //
        ?(memc_is_char, is_char_irr, memc_irr) //.
rewrite (inner_prod_char IC (is_char_restrict HsG (is_char_irr _))).
apply: isNatC_sum => j _; rewrite isNatC_mul // isNatC_ncoord_char //.
by apply: (is_char_restrict HsG (is_char_irr _)).
Qed.

Lemma is_comp_irr_restrict : forall i : Iirr H,
  H \subset G -> exists j : Iirr G, is_comp i ('Res[H] 'xi_j).
Proof.
move=> i HsG.
case: (boolP ('Ind[G, H] 'xi_i == 0))=> [HH|].
  have: ('Ind[G, H] 'xi_i) 1%g == 0 by rewrite (eqP HH) ffunE.
  rewrite /= cinduced1 //.
  rewrite mulf_eq0 (negPf (irr1_neq0 _)) orbF -(eqN_eqC _ 0).
  by case: indexg (indexg_gt0 G H).
have ICI: is_char G ('Ind[G, H] 'xi_i).
  by apply: is_char_induced=> //; exact: is_char_irr.
case/(is_comp_neq0 (memc_is_char ICI))=> j Hj; exists j.
have FF := memc_is_char (is_char_restrict HsG (is_char_irr j)).
rewrite is_compE  (ncoord_inner_prod _ FF).
rewrite inner_prod_charC  // ?(is_char_restrict HsG, is_char_irr) //.
rewrite (frobenius_reciprocity HsG) ?memc_irr //.
have FF1 := memc_induced HsG (memc_irr i).
by rewrite -(ncoord_inner_prod _ FF1).
Qed.

End Induced.
