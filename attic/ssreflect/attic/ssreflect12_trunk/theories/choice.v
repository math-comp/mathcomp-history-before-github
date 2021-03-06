(* (c) Copyright Microsoft Corporation and Inria. All rights reserved. *)
Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.

(*****************************************************************************)
(* This file contains the definitions of:                                    *)
(*  - choiceType : interface for type with choice operator                   *)
(*  - countType : interface for countable type                               *)
(* In addition to the lemmas relevant to these definitions, this file also   *)
(* contains definitions of Canonical Structure of choiceType for nat and     *)
(* subtype / option type / seq type / sigma type of a choice type. It also   *)
(* contains definitions of Canonical Structure of countType for nat, bool    *)
(* and subtype / option type / seq type / sigma type of a countable type and *)
(* sum and prod types of two countable types.                                *)
(*****************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

(* Technical definitions about coding and decoding of  list. This results are*)
(* useful for the definition of Canonical Structure of choice and countable  *)
(* types. *)

Module CodeSeq.

(* Goedel-style one-to-one encoding of seq T into T, for T := nat    *)
(* and T := seq (seq T0). Note that there is no such encoding in     *)
(* general for T := seq T0, since seq void ~ unit while              *)
(* seq (seq void) ~ nat.                                             *)

Module Nat.

(* The code for [:: n1; ...; nk] has binary representation           *)
(*     1 0 ... 0 1 ... 1 0 ... 0 1 0 ... 0                           *)
(*       <----->         <----->   <----->                           *)
(*        nk 0s           n2 0s     n1 0s                            *)

Definition code := foldr (fun n m => 2 ^ n * m.*2.+1) 0.

Fixpoint decode_rec (v q r : nat) {struct q} :=
  match q, r with
  | 0, _         => [:: v]
  | q'.+1, 0     => v :: [rec 0, q', q']
  | q'.+1, 1     => [rec v.+1, q', q']
  | q'.+1, r'.+2 => [rec v, q', r']
  end where "[ 'rec' v , q , r ]" := (decode_rec v q r).

Definition decode n := if n is 0 then [::] else [rec 0, n.-1, n.-1].

Lemma decodeK : cancel decode code.
Proof.
have m2s: forall n, n.*2 - n = n by move=> n; rewrite -addnn addnK.
case=> //= n; rewrite -[n.+1]mul1n -(expn0 2) -{3}[n]m2s.
elim: n {2 4}n {1 3}0 => [|q IHq] [|[|r]] v //=; rewrite {}IHq ?mul1n ?m2s //.
by rewrite expnSr -mulnA mul2n.
Qed.

Lemma codeK : cancel code decode.
Proof.
elim=> //= v s IHs; rewrite -[_ * _]prednK ?muln_gt0 ?expn_gt0 //=.
rewrite -{3}[v]addn0; elim: v {1 4}0 => [|v IHv {IHs}] q.
  rewrite mul1n /= -{1}addnn -{4}IHs; move: (_ s) {IHs} => n.
  by elim: {1 3}n => //=; case: n.
rewrite expnS -mulnA mul2n -{1}addnn -[_ * _]prednK ?muln_gt0 ?expn_gt0 //.
by rewrite doubleS addSn /= addSnnS; elim: {-2}_.-1 => //=.
Qed.

End Nat.

Module Seq2.
Section Seq2.

Variable T : Type.

(* Auxiliary functions that pad s2 : seq (seq T) with leading [::], *)
(* compute the padding, and strip it.                               *)
(* To encode a sequence we flatten its contents and prepend padding *)
(* whose length encodes (via Nat.code) the shape of the sequence.   *)
(* More precisely code for a sequence s3 with shape sh == shape s3  *)
(* and contents sc == flatten s3 is:                                *)
(*  - pad (Nat.code sh) [::]        if sc = [::]                    *)
(*  - pad (Nat.code sh) (strip sc)  if sc has padding               *)
(*  - pad (Nat.code (behead sh)) sc if sc != [::] has no padding    *)
(* The omitted padding/shape can be readily reconstructed; it is    *)
(* obviously necessary to delete the padding to avoid confusion     *)
(* with the shape encoding; beheading the shape makes the encoding  *)
(* one-to-one (otherwise, the contents following the padding could  *)
(* never exceed the capacity of the shape encoded by the padding.   *)

Definition pad n s2 : seq (seq T) := ncons n [::] s2.

Definition padding := find [pred s : seq T | size s > 0].

Definition strip s2 := drop (padding s2) s2.

Lemma stripK : forall s2, pad (padding s2) (strip s2) = s2.
Proof. by elim=> [|[]] //= s2 ->. Qed.

Lemma padKl : forall n s2, padding (pad n (strip s2)) = n.
Proof. by move=> n s2; elim: n => /= [|n -> //]; elim: s2 => [|[]]. Qed.

Lemma padKr : forall n s2, strip (pad n (strip s2)) = strip s2.
Proof. by move=> n s2; rewrite /strip padKl nconsK. Qed.

Definition code s3 :=
  let sh := shape s3 in let s2' := strip (flatten s3) in
  pad (Nat.code (drop (maxn (sumn sh) 1 <= size s2') sh)) s2'.

Definition decode s2 :=
  let: (sh', s2') := let n := padding s2 in (Nat.decode n, drop n s2) in
  let m := sumn sh' in let m' := size s2' in
  reshape (ncons (maxn m 1 <= m') (m' - m) sh') (pad (m - m') s2').

Lemma codeK : cancel code decode.
Proof.
rewrite /code => s3; set sh := shape s3; set s2' := strip _.
rewrite /decode padKl nconsK Nat.codeK.
case le_s2': (maxn (sumn sh) 1 <= size s2'); last first.
  rewrite drop0 le_s2' /= -size_flatten size_drop subKn ?find_size // stripK.
  exact: flattenK.
move: le_s2'; rewrite !leq_maxl size_drop size_flatten -/sh andbC subn_gt0.
case/andP=> lt_sh; rewrite lt_sh -subn_eq0 subKn /s2' /strip; last exact: ltnW.
move/eqP->; rewrite subn0 drop1 drop0; case def_sh: sh lt_sh => //= [n sh'] _.
by rewrite leq_addl addnK addnC -subn_sub subnn -[ncons _ _ _]def_sh flattenK.
Qed.

Lemma decodeK : cancel decode code.
Proof.
rewrite /decode => s2; set sh' := Nat.decode _; set s2' := drop _ _.
set sh := ncons _ _ _; set s3' := pad _ _; have sz_s3': sumn sh = size s3'.
  rewrite size_ncons {s3'}/sh addnC add_sub_maxn leq_maxl andbC.
  case: posnP => [->|_]; first by rewrite max0n.
  case: leqP => [_|lt_m_m'] /=; first by rewrite addnC add_sub_maxn maxnC.
  by apply/eqP; rewrite eq_sym eqn_maxr ltnW.
rewrite /code reshapeKl ?reshapeKr ?{}sz_s3' // padKr size_ncons addnC.
by rewrite add_sub_maxn -maxnA leq_maxl leqnn {sh}nconsK Nat.decodeK stripK.
Qed.

End Seq2.
End Seq2.

End CodeSeq.

Section OtherEncodings.
(* Miscellaneous encodings: option T -c-> seq T, T -c-> seq (seq T),          *)
(* T1 * T2 -c-> {i : T2 & T1}, and T1 + T2 -c-> option T1 * option T2.        *)
(*   We use these encodings to propagate canonical structures through these   *)
(* type constructors so that ultimately all Choice and Countable derive from  *)
(* the (trivial) Countable structure on nat. The peculiar order of the        *)
(* encoding of the product type T1 * T2 is due to the fact that we want it to *)
(* compose with  {i : T & T_ i} -c-> seq I, which is the only encoding we     *)
(* have for sigT, and is only defined when T_ i : countType (hence, it will   *)
(* only appear later in this file). This limitation means we have to assume   *)
(* that one of T1 or T2 in T1 * T2 / T1 + T2 is a countType, even if we only  *)
(* need a choiceType; it seemed somewhat more natural to take T1 : countType. *)

Variables T T1 T2 : Type.

Definition seq_of_opt := @oapp T _ (nseq 1) [::].
Lemma seq_of_optK : cancel seq_of_opt ohead. Proof. by case. Qed.

Definition seq2_of (x : T) := [::[::x]].
Lemma seq2_ofK : pcancel seq2_of (ohead \o head [::]). Proof. by []. Qed.

Definition tag_of_pair (p : T1 * T2) :=  @Tagged T2 p.2 (fun _ => T1) p.1.
Definition pair_of_tag (u : {i : T2 & T1}) := (tagged u, tag u).
Lemma tag_of_pairK : cancel tag_of_pair pair_of_tag. Proof. by case. Qed.
Lemma pair_of_tagK : cancel pair_of_tag tag_of_pair. Proof. by case. Qed.

Definition opair_of_inj (s : T1 + T2) :=
  match s with inl x => (Some x, None) | inr y => (None, Some y) end.
Definition inj_of_opair p := oapp (some \o @inr T1 T2) (omap (inl T2) p.1) p.2.
Lemma opair_of_injK : pcancel opair_of_inj inj_of_opair. Proof. by case. Qed.

End OtherEncodings.

(* Structures for Types with a choice function, and for Types with   *)
(* countably many elements. The two concepts are closely linked: we  *)
(* indeed make Countable a subclass of Choice, as countable choice   *)
(* is valid in CiC. This apparent redundancy is needed to ensure the *)
(* consistency of the Canonical Structure inference, as the          *)
(* canonical Choice for a given type may differ from the countable   *)
(* choice for its canonical Countable structure, e.g., for options.  *)
(* Nevertheless for most standard datatype constructors, including   *)
(* sums and pairs, Choice can only be satisfied constructively via   *)
(* countability, so in practice we build most Choice and Countable   *)
(* structures simultaneously.                                        *)
(*   For T : choiceType and P : pred T, we have actually two choice  *)
(* functions:                                                        *)
(*    xchoose : (exists x, P x) -> T                                 *)
(*    choose : pred T -> T -> T                                      *)
(*   We always have P (xchoose exP), while P (choose P x0) only if   *)
(* P x0 holds. Both xchoose and choose are extensional in P and do   *)
(* not depend on the witness exP or x0 (provided P x0). Note that    *)
(* xchoose is slightly more powerful, but less convenient to use.    *)
(* The Choice structure actually contains an xchoose function for    *)
(* seq (seq T), as this allows us to derive a Choice structure for   *)
(* seq T (and thus for iter n seq T for any n).                      *)
(*   For T : countType we have two functions:                        *)
(*    pickle : T -> nat, and unpickle : nat -> option T              *)
(* The two functions provide an effective embedding of T in nat: we  *)
(* have pcancel pickle unpickle, i.e., unpickle \o pickle =1 some.   *)
(* The names of the generic functions underline the correspondence   *)
(* with the notion of "Serializable" types in programming languages. *)
(* Note that unpickle needs to be a partial function to account for  *)
(* a possibly empty T (e.g., T = {x | P x}). We derive a pickle_inv  *)
(* function that is an exact inverse to pickle, i.e., we have both   *)
(* pcancel pickle pickle_inv, and ocancel pickle_inv pickle.         *)
(*   Finally, we need to provide a join class to let type inference  *)
(* unify subType and countType class constraints, as we can have     *)
(* a countable subType of an uncountable choiceType (the problem     *)
(* did not arise earlier with eqType or choiceType because in        *)
(* in practice the base type of an Equality/Choice subType is always *)
(* an Equality/Choice Type).                                         *)

Module Choice.

Section Mixin.

Variable T : Type.
Implicit Types P Q : pred T.

Definition xfun := forall P, (exists x, P x) -> T.
Implicit Type f : xfun.

Definition correct f := forall P xP, P (f P xP).
Definition extensional f := forall P Q xP xQ, P =1 Q -> f P xP = f Q xQ.

Record mixin_of : Type := Mixin {
  xchoose : xfun;
  xchooseP : correct xchoose;
  eq_xchoose : extensional xchoose
}.

End Mixin.

Record class_of (T : Type) : Type :=
  Class { base :> Equality.class_of T; ext2 : mixin_of (seq (seq T)) }.

Structure type : Type := Pack {sort :> Type; _ : class_of sort; _ : Type}.
Definition class cT := let: Pack _ c _ := cT return class_of cT in c.
Definition clone T cT c of phant_id (class cT) c := @Pack T c T.

Definition pack T m :=
  fun b bT & phant_id (Equality.class bT) b => Pack (@Class T b m) T.

Section PcanMixin.

Variables (T sT : Type) (m : mixin_of T) (f : sT -> T) (f' : T -> option sT).
Hypothesis fK : pcancel f f'.

Section Xfun.

Variables (sP : pred sT) (xsP : exists x, sP x).

Lemma pcan_xchoose_proof : exists x, oapp sP false (f' x).
Proof. by case: xsP => x sPx; exists (f x); rewrite fK. Qed.

Lemma pcan_xchoose_sig :
  {x | Some x = f' (xchoose m pcan_xchoose_proof) & sP x}.
Proof.
by case def_x: (f' _) (xchooseP m pcan_xchoose_proof) => //= [x]; exists x.
Qed.

Definition pcan_xchoose := s2val pcan_xchoose_sig.

Lemma pcan_xchooseP : sP pcan_xchoose.
Proof. exact: (s2valP' pcan_xchoose_sig). Qed.

End Xfun.

Lemma eq_pcan_xchoose : extensional pcan_xchoose.
Proof.
move=> sP sQ exsP exsQ eqsPQ; apply: (_ : injective some) => [? ? [] //|].
rewrite !(s2valP (pcan_xchoose_sig _)); congr f'; apply: eq_xchoose.
by case/f'=> //=.
Qed.

Definition PcanMixin := Mixin pcan_xchooseP eq_pcan_xchoose.

End PcanMixin.

Coercion ext0 T m := PcanMixin (ext2 m) (@seq2_ofK T).

Definition CanMixin2 T sT f f' (fK : @cancel _ (seq (seq sT)) f f') :=
  PcanMixin (ext2 (class T)) (can_pcan fK).

(* Construct class_of T directly from an encoding seq (seq T) c-> nat.  *)
(* This is used to build a Choice base class for Countable types.       *)

Lemma nat_xchooseP : correct ex_minn.
Proof. by move=> P xP; case: ex_minnP. Qed.

Lemma eq_nat_xchoose : extensional ex_minn.
Proof.
move=> P Q xP xQ eqPQ; do 2![case: ex_minnP] => m Pm min_m n Qn min_n {xP xQ}.
by apply/eqP; rewrite eqn_leq min_m ?min_n ?eqPQ // -eqPQ.
Qed.

Definition natMixin T := @PcanMixin nat T (Mixin nat_xchooseP eq_nat_xchoose).

Coercion eqType cT := Equality.Pack (class cT) cT.

End Choice.

Notation choiceType := Choice.type.
Notation ChoiceMixin := Choice.Mixin.
Notation ChoiceType T m := (@Choice.pack T m _ _ id).
Canonical Structure Choice.eqType.

Notation "[ 'choiceType' 'of' T 'for' cT ]" :=  (@Choice.clone T cT _ idfun)
  (at level 0, format "[ 'choiceType'  'of'  T  'for'  cT ]") : form_scope.
Notation "[ 'choiceType' 'of' T ]" := (@Choice.clone T _ _ id)
  (at level 0, format "[ 'choiceType'  'of'  T ]") : form_scope.

Section ChoiceTheory.

Variable T : choiceType.
Implicit Types P Q : pred T.

Definition xchoose := Choice.xchoose (Choice.class T).

Lemma xchooseP : Choice.correct xchoose.
Proof. exact: Choice.xchooseP. Qed.

Lemma eq_xchoose : Choice.extensional xchoose.
Proof. exact: Choice.eq_xchoose. Qed.

Definition choose P x0 :=
  if insub x0 : {? x | P x} is Some (exist x Px) then
    xchoose (ex_intro [eta P] x Px)
  else x0.

Lemma chooseP : forall P x0, P x0 -> P (choose P x0).
Proof. by move=> P x0 Px0; rewrite /choose (insubT [eta P] Px0) xchooseP. Qed.

Lemma choose_id : forall P x0 y0, P x0 -> P y0 -> choose P x0 = choose P y0.
Proof.
rewrite /choose => P x0 y0 Px0 Py0.
rewrite (insubT [eta P] Px0) (insubT [eta P] Py0) /=; exact: eq_xchoose.
Qed.

Lemma eq_choose : forall P Q, P =1 Q -> choose P =1 choose Q.
Proof.
rewrite /choose => P Q eqPQ x0.
do [case: insubP; rewrite eqPQ] => [[x Px] Qx0 _| ?]; last by rewrite insubN.
rewrite (insubT [eta Q] Qx0); exact: eq_xchoose.
Qed.

Definition PcanChoiceMixin sT f f' (fK : @pcancel T sT f f') :=
  Choice.CanMixin2 (mapK (map_pK fK)).

Definition CanChoiceMixin sT f f' (fK : @cancel T sT f f') :=
  PcanChoiceMixin (can_pcan fK).

Section SubChoice.

Variables (P : pred T) (sT : subType P).

Definition sub_choiceMixin := PcanChoiceMixin (@valK T P sT).
Definition sub_choiceClass := @Choice.Class sT (sub_eqMixin sT) sub_choiceMixin.
Canonical Structure sub_choiceType := Choice.Pack sub_choiceClass sT.

End SubChoice.

End ChoiceTheory.

Prenex Implicits xchoose choose.

Notation "[ 'choiceMixin' 'of' T 'by' <: ]" :=
    (sub_choiceMixin _ : Choice.mixin_of (seq (seq T)))
  (at level 0, format "[ 'choiceMixin'  'of'  T  'by'  <: ]") : form_scope.

(* Canonical Structure of choiceType *)
Section SomeChoiceTypes.

Variables (T : choiceType) (P : pred T).

Definition seq_choiceMixin := Choice.CanMixin2 (@CodeSeq.Seq2.codeK T).
Canonical Structure seq_choiceType :=
  Eval hnf in ChoiceType (seq T) seq_choiceMixin.

Definition option_choiceMixin := CanChoiceMixin (@seq_of_optK T).
Canonical Structure option_choiceType :=
  Eval hnf in ChoiceType (option T) option_choiceMixin.

Definition sig_choiceMixin := [choiceMixin of {x | P x} by <:].
Canonical Structure sig_choiceType :=
  Eval hnf in ChoiceType {x | P x} sig_choiceMixin.

End SomeChoiceTypes.

Module Countable.

Record mixin_of (T : Type) : Type := Mixin {
  pickle : T -> nat;
  unpickle : nat -> option T;
  pickleK : pcancel pickle unpickle
}.

Section PickleSeq.

Variables (T : Type) (p : T -> nat) (u : nat -> option T).
Hypothesis pK : pcancel p u.

Definition pickle_seq s := CodeSeq.Nat.code (map p s).

Definition unpickle_seq n := Some (pmap u (CodeSeq.Nat.decode n)).

Lemma pickle_seqK : pcancel pickle_seq unpickle_seq.
Proof. by move=> s; rewrite /unpickle_seq CodeSeq.Nat.codeK map_pK. Qed.

End PickleSeq.

Definition ChoiceMixin T m :=
  Choice.natMixin (pickle_seqK (pickle_seqK (@pickleK T m))).

Definition EqMixin T m := PcanEqMixin (@pickleK T m).

Record class_of (T : Type) : Type :=
  Class { base :> Choice.class_of T; ext :> mixin_of T }.

Structure type : Type := Pack {sort :> Type; _ : class_of sort; _ : Type}.
Definition class cT := let: Pack _ c _ := cT return class_of cT in c.
Definition clone T cT c of phant_id (class cT) c := @Pack T c T.

Definition pack T m :=
  fun bT b & phant_id (Choice.class bT) b => Pack (@Class T b m) T.

Coercion eqType cT := Equality.Pack (class cT) cT.
Coercion choiceType cT := Choice.Pack (class cT) cT.

End Countable.

Notation countType := Countable.type.
Notation CountType T m := (@Countable.pack T m _ _ id).
Notation CountMixin := Countable.Mixin.
Notation CountChoiceMixin := Countable.ChoiceMixin.
Canonical Structure Countable.eqType.
Canonical Structure Countable.choiceType.

Definition unpickle T := Countable.unpickle (Countable.class T).
Definition pickle T := Countable.pickle (Countable.class T).
Implicit Arguments unpickle [T].
Prenex Implicits pickle unpickle.

Notation "[ 'countType' 'of' T 'for' cT ]" := (@Countable.clone T cT _ idfun)
 (at level 0, format "[ 'countType'  'of'  T  'for'  cT ]") : form_scope.
Notation "[ 'countType' 'of' T ]" := (@Countable.clone T _ _ id)
  (at level 0, format "[ 'countType'  'of'  T ]") : form_scope.

Section CountableTheory.

Variable T : countType.

Lemma pickleK : @pcancel nat T pickle unpickle.
Proof. exact: Countable.pickleK. Qed.

Definition pickle_inv n :=
  obind (fun x : T => if pickle x == n then Some x else None) (unpickle n).

Lemma pickle_invK : ocancel pickle_inv pickle.
Proof.
by rewrite /pickle_inv => n; case def_x: (unpickle n) => //= [x]; case: eqP.
Qed.

Lemma pickleK_inv : pcancel pickle pickle_inv.
Proof. by rewrite /pickle_inv => x; rewrite pickleK /= eqxx. Qed.

Lemma pcan_pickleK : forall sT f f',
  @pcancel T sT f f' -> pcancel (pickle \o f) (pcomp f' unpickle).
Proof. by move=> sT f f' fK x; rewrite /pcomp pickleK /= fK. Qed.

Definition PcanCountMixin sT f f' (fK : pcancel f f') :=
  @CountMixin sT _ _ (pcan_pickleK fK).

Definition CanCountMixin sT f f' (fK : cancel f f') :=
  @PcanCountMixin sT _ _ (can_pcan fK).

Definition sub_countMixin P sT := PcanCountMixin (@valK T P sT).

Definition seq_countMixin := CountMixin (Countable.pickle_seqK pickleK).
Canonical Structure seq_countType :=
  Eval hnf in CountType (seq T) seq_countMixin.

End CountableTheory.

Notation "[ 'countMixin' 'of' T 'by' <: ]" :=
    (sub_countMixin _ : Countable.mixin_of T)
  (at level 0, format "[ 'countMixin'  'of'  T  'by'  <: ]") : form_scope.

Section SubCountType.

Variables (T : choiceType) (P : pred T).
Import Countable.

Structure subCountType : Type :=
  SubCountType {subCount_sort :> subType P; _ : mixin_of subCount_sort}.

Coercion sub_countType (sT : subCountType) :=
  Eval hnf in pack (let: SubCountType _ m := sT return mixin_of sT in m) id.
Canonical Structure sub_countType.

Definition pack_subCountType U :=
  fun sT cT & sub_sort sT * sort cT -> U * U =>
  fun b m   & phant_id (Class b m) (class cT) => @SubCountType sT m.

End SubCountType.

(* This assumes that T has both countType and subType structures. *)
Notation "[ 'subCountType' 'of' T ]" :=
    (@pack_subCountType _ _ T _ _ id _ _ id)
  (at level 0, format "[ 'subCountType'  'of'  T ]") : form_scope.

(* The remaining Canonical Structures for standard datatypes. *)

Lemma unit_pickleK : pcancel (fun _ => 0) (fun _ => Some tt).
Proof. by case. Qed.
Definition unit_countMixin := CountMixin unit_pickleK.
Definition unit_choiceMixin := CountChoiceMixin unit_countMixin.
Canonical Structure unit_choiceType :=
  Eval hnf in ChoiceType unit unit_choiceMixin.
Canonical Structure unit_countType :=
  Eval hnf in CountType unit unit_countMixin.

Lemma bool_pickleK : pcancel nat_of_bool (some \o leq 1). Proof. by case. Qed.
Definition bool_countMixin := CountMixin bool_pickleK.
Definition bool_choiceMixin := CountChoiceMixin bool_countMixin.
Canonical Structure bool_choiceType :=
  Eval hnf in ChoiceType bool bool_choiceMixin.
Canonical Structure bool_countType :=
  Eval hnf in CountType bool bool_countMixin.

Lemma nat_pickleK : pcancel id (@Some nat). Proof. by []. Qed.
Definition nat_countMixin := CountMixin nat_pickleK.
Definition nat_choiceMixin := CountChoiceMixin nat_countMixin.
Canonical Structure nat_choiceType :=
  Eval hnf in ChoiceType nat nat_choiceMixin.
Canonical Structure nat_countType :=
  Eval hnf in CountType nat nat_countMixin.

Canonical Structure bitseq_choiceType := Eval hnf in [choiceType of bitseq].
Canonical Structure bitseq_countType :=  Eval hnf in [countType of bitseq].

Definition option_countMixin (T : countType) := CanCountMixin (@seq_of_optK T).
Canonical Structure option_countType (T : countType) :=
  Eval hnf in CountType (option T) (option_countMixin T).

Definition sig_countMixin (T : countType) (P : pred T) :=
  [countMixin of {x | P x} by <:].
Canonical Structure sig_countType (T : countType) (P : pred T) :=
  Eval hnf in CountType {x | P x} (sig_countMixin P).
Canonical Structure sig_subCountType (T : countType) (P : pred T) :=
  Eval hnf in [subCountType of {x | P x}].

Section TagSeq.
(* To encode {i : I | T_ i} into a type that inherits the Choice or    *)
(* Countable structure of I, we need T_ i to be a countType, in which  *)
(* case we get an encoding {i : I | T_ i} c-> seq I.                   *)
Variables (I : Type) (T_ : I -> countType).
Definition seq_of_tag_count (u : {i : I & T_ i}) :=
  nseq (pickle (tagged u)).+1 (tag u).
Definition tag_count_of_seq s :=
  if s is i :: s' then omap (@Tagged I i T_) (unpickle (size s')) else None.
Lemma seq_of_tag_countK : pcancel seq_of_tag_count tag_count_of_seq.
Proof. by case=> i x /=; rewrite size_nseq pickleK. Qed.
End TagSeq.

Definition tag_choiceMixin (I : choiceType) (T_ : I -> countType) :=
  PcanChoiceMixin (@seq_of_tag_countK I T_).
Canonical Structure tag_choiceType (I : choiceType) (T_ : I -> countType) :=
  Eval hnf in ChoiceType {i : I & T_ i} (tag_choiceMixin T_).
Definition tag_countMixin (I : countType) (T_ : I -> countType) :=
  PcanCountMixin (@seq_of_tag_countK I T_).
Canonical Structure tag_countType (I : countType) (T_ : I -> countType) :=
  Eval hnf in CountType {i : I & T_ i} (tag_countMixin T_).

Definition prod_choiceMixin (T1 : countType) (T2 : choiceType) :=
  CanChoiceMixin (@tag_of_pairK T1 T2).
Canonical Structure prod_choiceType (T1 : countType) (T2 : choiceType) :=
  Eval hnf in ChoiceType (T1 * T2) (prod_choiceMixin T1 T2).
Definition prod_countMixin (T1 : countType) (T2 : countType) :=
  CanCountMixin (@tag_of_pairK T1 T2).
Canonical Structure prod_countType (T1 : countType) (T2 : countType) :=
  Eval hnf in CountType (T1 * T2) (prod_countMixin T1 T2).

Definition sum_choiceMixin (T1 : countType) (T2 : choiceType) :=
  PcanChoiceMixin (@opair_of_injK T1 T2).
Canonical Structure sum_choiceType (T1 : countType) (T2 : choiceType) :=
  Eval hnf in ChoiceType (T1 + T2) (sum_choiceMixin T1 T2).
Definition sum_countMixin (T1 : countType) (T2 : countType) :=
  PcanCountMixin (@opair_of_injK T1 T2).
Canonical Structure sum_countType (T1 : countType) (T2 : countType) :=
  Eval hnf in CountType (T1 + T2) (sum_countMixin T1 T2).

