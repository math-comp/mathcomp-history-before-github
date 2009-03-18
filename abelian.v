(***********************************************************************)
(* (c) Copyright Microsoft Corporation and Inria. All rights reserved. *)
(*                                                                     *)
(***********************************************************************)
(***********************************************************************)
(*                                                                     *)
(*                     Abelian group structure                         *)
(*                                                                     *)
(***********************************************************************)
(***********************************************************************)

Require Import ssreflect ssrbool ssrfun ssrnat.
Require Import eqtype seq fintype finset.
Require Import groups div cyclic bigops.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Import GroupScope.

(*
Structure theorem for abelian finite groups. The development involves:
- definition of "base" (may be replaced by the one in pgroups).
- a functional (from finGroupType to nat) representation for combination of elements in an abelian setting.
- a reflection lemma relating generated groups to the above functional representation. 
- the main result: every abelian finite group has a base.
- a few lemmas that are presumably useful to working with abelian finite groups.

Note: there is room for cleaning and improvment. 
*)


(* Definitions about functions *)

Section Function_Misc_Def.

Variables (gT : finGroupType) (f g : gT -> nat).
Variables (x : gT) (n : nat) (A : {set gT}).

Definition addf f g := fun y : gT => f y + g y. 

Definition peak y := if y == x then n else 0.

Definition force y := if y == x then n else f y.

Definition support := forallb y, (0 < f y) ==> (y \in A).

End Function_Misc_Def.

(* Lemmas involving the above definitions, predU1, predD1 and foldr *)

Section Function_Pred_Misc_Prop. 

Variables (gT : finGroupType) (f h : gT -> nat) (x : gT).
Variables (n m : nat) (A B : {set gT}).

Lemma eq_force : force f x (f x) =1 f.
Proof.
by move=> y; rewrite/force; case yx: (y == x) => //; move/eqP: yx ->. 
Qed.

Lemma force_peak : addf (force f x n) (peak x m) =1 force f x (n + m).
Proof.
by move=> y; rewrite/addf/peak/force; case: (y == x).
Qed.  

Lemma neq_force : forall y, y <> x -> force f x n y = f y.
Proof.
by move=> y xy; rewrite/force; case yx: (y == x) => //; move/eqP: yx xy.
Qed. 

Lemma supP : forall g (C : {set gT}),
  reflect (forall y, 0 < g y -> y \in C) (support g C).
Proof.
by move=> g C; apply: (iffP forallP); move=> H y; move/implyP: (H y).
Qed.

Lemma sup0P : forall g (C : {set gT}),
  reflect (forall y, y \notin C -> g y = 0) (support g C).
Proof.
move=> g C; apply: (iffP (supP _ _)) => insupp y => [nCy | gy_gt0].
  by apply/eqP; apply/idPn; rewrite -lt0n => gy_gt0; rewrite insupp in nCy.
by apply/idPn=> nCy; rewrite insupp in gy_gt0.
Qed.

Lemma sup_sub : A \subset B -> support f A -> support f B.
Proof.
move/subsetP=> AB; move/supP => supA.
by apply/supP => y fy; apply: AB; apply: supA.
Qed.

Lemma eq_sup : A =i B -> support f A = support f B.
Proof.
by move=> AB; apply/supP/supP=> insupp y; move/(_ y): insupp; rewrite AB.
Qed.

Lemma sup_addf : support f A && support h A = support (addf f h) A. 
Proof.
apply/andP/supP=> [[inf inh y]|infh].
  rewrite addn_gt0; case/orP; [exact: (supP _ _ inf) | exact: (supP _ _ inh)].
by split; apply/supP=> y fy_gt0; rewrite infh // addn_gt0 fy_gt0 ?orbT.
Qed.

Lemma sup_peak : (x \in A) || (n == 0) = support (peak x n) A.
Proof.
apply: eq_true_iff_eq; rewrite/peak; split.
  move=> Axn; apply/supP => /= y; case: (y =P x) Axn => // -> Axn n_gt0.
  by rewrite eqn0Ngt n_gt0 orbF in Axn.
by move/supP; move/(_ x); rewrite eqxx orbC; case: n => // ? ->.
Qed.

Lemma sup_force : x \in A -> support f A = support (force f x n) A.
Proof.
by rewrite/force; move=> Ax; apply: eq_true_iff_eq; split; 
move/supP => H; apply/supP => y; [| move: (H y)];
case yx: (y == x); try done; try exact: H; move/eqP: yx ->. 
Qed.

Lemma sup_predU1_force : support f (x |: A) = support (force f x 0) A.
Proof.
rewrite/force; apply/idP/idP; move/supP => H; apply/supP => y;
  by move/(_ y): H; rewrite !inE; case: (y == x).
Qed.

Lemma predU1_sub : (x |: B) \subset A -> B \subset A /\ x \in A. 
Proof. by rewrite subUset sub1set andbC; move/andP. Qed.

Lemma predU1_super : A \subset (x |: A).
Proof. by apply/subsetP => y Ay; rewrite inE Ay orbT. Qed.

Lemma predD1E : x \in A -> A = x |: A :\ x.
Proof.
by move=> Ax; apply/setP=> y; rewrite !inE; case: (y =P x) => //= ->.
Qed.

Lemma eq_foldr : forall (f1 f2 : gT -> gT -> gT)(s : seq gT),
  (forall y z, y \in s -> f1 y z = f2 y z) -> foldr f1 1 s = foldr f2 1 s.  
Proof. 
move=> f1 f2; elim => //= y s Hind H.
rewrite Hind; first by apply: H; rewrite inE eqxx.
by move=> z p sz; apply: H; rewrite inE sz orbT. 
Qed.

End Function_Pred_Misc_Prop.



(* Definition of and lemmas on combinations of elements by exponentiation
   according to a function and multiplication along a sequence.
   "esums" stands for sum of exponents along the sequence.   
   "ems" stands for exponentiation and multiplication along the sequence *)

Section Combo_Sequence.

Variable (gT : finGroupType).

Definition esums (f : gT -> nat) (s : seq gT) :=
  foldr (fun x n => (f x) + n) 0 s.

Definition ems (f : gT -> nat) (s : seq gT) :=
  foldr (fun x y => x ^+ (f x) * y) 1 s.

Lemma eq_esums : forall (f g : gT -> nat), f =1 g ->
forall s, esums f s = esums g s.
Proof.
by move=> f g fg; elim => //= x s ->; rewrite (fg x). 
Qed.

Lemma esums_addf : forall (f g : gT -> nat),
forall s, esums (addf f g) s =  esums f s + esums g s.
Proof.
by move=> f g; elim => //= x s Hind; rewrite/addf Hind /=
!addnA -(addnA _ (g x)) (addnC (g x)) addnA.
Qed.

Lemma esums_peak : forall (y : gT) n s,
  esums (peak y n) s = (n * count (pred1 y) s)%N.
Proof.
move=> y n; elim => //= x s ->; rewrite/peak eq_sym muln_addr. 
by case yx: (y == x) => //=; [rewrite muln1 | rewrite muln0].
Qed.

Lemma eq_ems : forall (f g : gT -> nat), f =1 g -> ems f =1 ems g.
Proof.
by move => f g fg; elim => //= x s ->; rewrite fg.
Qed.

Lemma ems1: forall s, ems (fun _ => 0) s = 1.
Proof. 
elim => //= x s ->; gsimpl.   
Qed.

Lemma ems_peak : forall (y : gT) n s,
  ems (peak y n) s = y ^+ (n * count (pred1 y) s).
Proof.
rewrite/peak; move=> y n; elim => //=; first by rewrite muln0 /=; gsimpl.  
move=> x s ->; rewrite eq_sym muln_addr expgn_add.
by case yx: (y == x) => //=; [rewrite (eqP yx) muln1 | rewrite muln0].
Qed. 

Lemma ems_not1 : forall (f : gT -> nat) s,
  ems f s <> 1 -> exists2 x, x \in s & 0 < f x.
Proof.
move => f; elim => //= x s Hind.
case xfx: (x ^+ (f x) == 1).
  move/eqP: xfx ->; gsimpl => emsf.
  by case: (Hind emsf) => y sy fy; exists y => //; rewrite inE sy orbT.
move=> _; exists x; first by rewrite inE eqxx.
by case fx: (f x) xfx => //; rewrite eqxx.
Qed.

Lemma ems1_not1 : forall (f : gT -> nat) s x,
  uniq s -> ems f s = 1 -> x \in s -> x ^+ (f x) <> 1 ->
  exists2 y, y <> x & 0 < f y.
Proof.
move=> f; elim => //= y s Hind x.
case/andP; move/negP=> notsy us yemsf; case/predU1P=> [-> yfy|sx xfx].
  case: (@ems_not1 f s) => [emsf | z sz fz].
    by rewrite -yemsf emsf mulg1 in yfy.
  by exists z => // zy; rewrite zy in sz.
case: (y ^+ (f y) =P 1) => [yfy | nyfy].
  by rewrite yfy mul1g in yemsf; exact: Hind.
by exists y => [yx|]; [rewrite -yx in sx | case: (f y) nyfy].
Qed.

End Combo_Sequence.



(* Definition of and lemmas on combinations of elements by exponentiation
   according to a function and multiplication along the enum sequence
   (the carrier of the underlying finGroupType). "esum" stands for
    sum of exponents. "em" stands for exponentiation and multiplication *)

Section Combo_Enum.

Variable (gT : finGroupType).

Definition esum (f : gT -> nat) := esums f (enum gT).

Definition em (f : gT -> nat) := ems f (enum gT).

Lemma eq_esum : forall (f g : gT -> nat), f =1 g -> esum f = esum g.
Proof.
move=> f g fg; exact: eq_esums.
Qed.

Lemma esum_addf : forall (f g : gT -> nat),
esum (addf f g) =  esum f + esum g.
Proof.
move=> f g; exact: esums_addf.
Qed.

Lemma esum_peak : forall (y : gT) n, esum (peak y n) = n.
Proof.
move=> y n; have:= esums_peak y n (enum gT).
rewrite /esum count_uniq_mem; last exact: enum_uniq.
by rewrite mem_enum /= muln1. 
Qed.

Lemma esum_leq : forall (f : gT -> nat) x, f x <= esum f.
Proof.
by move=> f x; rewrite -(eq_esum (eq_force f x)) -(add0n (f x))  
-(eq_esum (force_peak _ _ _ _)) esum_addf esum_peak leq_add2r. 
Qed.

Lemma esum_force : forall (f : gT -> nat) x n ,
esum (force f x n) = esum f + n - f x.
Proof.
move=> f x n; apply: (@addIn (f x)); rewrite subnK; last first.
  by apply: (leq_trans (esum_leq _ _)); apply: leq_addr.
rewrite -(eq_esum (eq_force f x)) -{1}(esum_peak x (f x)).
rewrite -{2}(esum_peak x n) -!esum_addf !(eq_esum (force_peak _ _ _ _)).
by rewrite addnC.
Qed.

Lemma eq_em : forall (f g : gT -> nat), f =1 g -> em f = em g.
Proof.
move => f g fg; exact: eq_ems.
Qed.

Lemma em1: em (fun _ => 0) = 1.
Proof. 
exact: ems1.
Qed.

Lemma em_peak : forall (y : gT) n, em (peak y n) = y ^+ n.
Proof.
move=> y n; rewrite/em ems_peak count_uniq_mem;
last exact (enum_uniq gT). by rewrite mem_enum /= muln1. 
Qed.

Lemma em_not1 : forall (f : gT -> nat), em f <> 1 -> exists x, 0 < f x.
Proof.
by rewrite/em; move=> f emsf; case: (ems_not1 emsf) => x; exists x.
Qed.

Lemma em1_not1 : forall (f : gT -> nat) x, em f = 1 -> x ^+ (f x) <> 1 ->
exists2 y, y <> x & 0 < f y.
Proof.
rewrite/em; move=> f x emsf xfx; apply: (@ems1_not1 gT f (enum gT)) => //;
[exact: enum_uniq | exact: mem_enum].
Qed.

End Combo_Enum.

(* Definition of and lemmas on 
   abelian sets and combinations in abelian sets *)

Section Abelian.

Variable (gT : finGroupType).
Variable (A : {set gT}) (abelA : abelian A).

Lemma asub : forall B : {set gT}, B \subset A -> abelian B.
Proof.
by move=> B BA; apply/centsP => x Bx y By;
move/subsetP: BA => BA; move/centsP: abelA; apply; apply: BA.
Qed.

Lemma aems_com : forall (f : gT -> nat) x n,
   x \in A -> support f A ->
   forall s, (x ^+ n) * ems f s = ems f s * (x ^+ n). 
Proof.
move=> f x n Ax fA; elim => /=; first by gsimpl. move=> y s Hind;
rewrite -mulgA -{}Hind !mulgA -commuteX //; apply: commute_sym.
case fy: (f y); first exact: commute1.
apply: commuteX; apply: (centsP abelA) => //.
by apply: (supP _ _ fA); rewrite fy. 
Qed.

Lemma aems_addf : forall f g : gT -> nat,
  support f A -> support g A ->
  forall s, ems (addf f g) s = ems f s * ems g s.
Proof.
move=> f g fA gA; rewrite/ems/addf; elim => /=; try move=> x s ->; gsimpl.
congr (_ * _); rewrite expgn_add -!mulgA; congr (_ * _).
case gx: (g x); first by rewrite mulg1 mul1g.
by apply: aems_com => //; apply: (supP _ _ gA); rewrite gx.
Qed.

Lemma aem_addf : forall f g : gT -> nat,
  support f A -> support g A -> em (addf f g) = em f * em g.
Proof. move=> f g fA gA; exact: aems_addf. Qed.

Lemma aem_force : forall f x n,
  x \in A -> support f A ->
  em (force f x n) = em f * (x ^+ n) * (x ^+ (f x))^-1.
Proof. 
move=> f x n Ax fA; apply: (mulIg (x ^+ (f x))); gsimpl.
by rewrite -(eq_em (eq_force f x)) -!(em_peak) -!aem_addf;
first rewrite !(eq_em (force_peak _ _ _ _)) addnC;
try rewrite -sup_peak Ax; try rewrite -sup_force .
Qed.

Lemma aem_force0 :  forall f x, x \in A -> support f A ->
  em f = em (force f x 0) * x ^+ (f x).
Proof. by move=> f x Ax fA; rewrite aem_force; rewrite // mulg1 mulgKV. Qed.

End Abelian.

(* Definition of and lemmas on sets that are generated
   by multiplication of cyclic groups along the enum sequence
   The "m" in "mgen" stands for "multiplication" *)

Section Generated_Sequence.

Variable (gT : finGroupType).

(*
Definition mgens s : set gT :=
foldr (fun x Y => (<[x]>) :*: Y) [set 1] s.
*)

Definition mgen (A : {set gT}) : {set gT} := \prod_(x \in A) <[x]>.

Lemma mgenP : forall A x,
  reflect (exists2 f, support f A & em f = x) (x \in mgen A).
Proof.
move=> A x; rewrite /mgen /em /index_enum -enumT.
elim: {+}(enum _) x (enum_uniq gT) => /= [x _ | y s IHs x].
  rewrite big_nil inE; apply: (iffP eqP) => [->|[]//].
  exists (fun _ : gT => 0) => //=; exact/supP.
case/andP=> nsy; move/IHs=> {IHs}IHs; rewrite big_cons.
case Ay: (y \in A); last first.
  apply: (iffP (IHs x)); case=> f Af <-; exists f => //;
    by rewrite (sup0P _ _ Af) (Ay, mul1g).
apply: (iffP mulsgP) => [[x1 x2] | [f Af <-{x}]].
  case/cycleP=> i <-{x1}; case/IHs=> f Af <- -> {x x2}.
  exists (force f y i); first by rewrite -sup_force.
  rewrite /force eqxx; congr (_ * _).
  by apply: eq_foldr => x z sx; case: eqP => // eqxy; rewrite -eqxy sx in nsy.
exists (y ^+ (f y)) (ems f s) => //; first by apply/cycleP; exists (f y).
apply/IHs; exists (force f y 0); first by rewrite -sup_force.
apply: eq_foldr => x z sx.
by rewrite /force; case: eqP => // eqxy; rewrite -eqxy sx in nsy.
Qed.

Lemma mgen_super : forall A : {set gT}, A \subset mgen A.
Proof.
move=> A; apply/subsetP => x Ax.
apply/mgenP; exists (peak x 1); first by rewrite -sup_peak Ax.
by rewrite em_peak expg1.
Qed.

Lemma mgen_sub : forall (A : {set gT}) (G : {group gT}),
  A \subset G -> mgen A \subset G.
Proof.
move=> A G sAG; rewrite /mgen; elim: index_enum  => /= [| x s IHs].
  by rewrite big_nil sub1set.
rewrite big_cons; case Ax: (x \in A) => //=.
apply/subsetP=> y; case/mulsgP=> y1 y2.
case/cycleP => i <-; move/(subsetP IHs)=> sy2 ->.
by rewrite groupMr // groupX // (subsetP sAG).
Qed.

(* This result -- abelian sets generate abelian groups -- is not *)
(* used in the main theorem. *)

Lemma amgen : forall A : {set gT}, abelian A -> abelian (mgen A).
Proof.
move=> A abelA.
suff comgen: forall B C : {set gT}, B \subset 'C(C) -> B \subset 'C(mgen C).
  apply: (comgen); rewrite centsC; exact: comgen.
move=> B C; rewrite !(centsC B); exact: mgen_sub.
Qed.

End Generated_Sequence.



(* Coincidence of the combinations of elements of a given set and
   the group that is generated by the given set, and a reflection lemma *)

Section Generated_Abelian.

Variable (gT : finGroupType) (A : {set gT}) (abelA : abelian A).

Lemma amgen_group_set : group_set (mgen A).
Proof.
apply/andP; split.
  apply/mgenP; exists (fun _ : gT => 0); first by apply/supP.
  by rewrite/em; elim: enum => //= x s ->; rewrite mulg1.
apply/subsetP=> xy; case/mulsgP=> x y.
case/mgenP => f Af <-; case/mgenP => g Ag <- -> {x y xy}. 
apply/mgenP; exists (addf f g); first by rewrite -sup_addf Af.
by apply: (aem_addf abelA).
Qed.

Canonical Structure amgen_group := Group amgen_group_set.

Lemma amgen_gen : <<A>> = mgen A.
Proof.
by apply/eqP; rewrite eqEsubset gen_subG mgen_super mgen_sub // subset_gen.
Qed.

Lemma agen : abelian <<A>>.
Proof. rewrite amgen_gen; exact: amgen. Qed.

Lemma agenP : forall x,
  reflect (exists2 f, support f A & em f = x) (x \in <<A>>).
Proof. rewrite amgen_gen; exact: mgenP. Qed.

End Generated_Abelian.

(* Definition of and lemmas on freeness *)

Section Free.

Variable (gT : finGroupType).

Definition Free (B : {set gT}) :=
    1 \notin B
 /\ forall f g, support f B -> support g B -> em f = em g ->
    forall x, x ^+ (f x) = x ^+ (g x).

Definition free (B : {set gT}) :=
  1 \notin B /\ forall f, support f B -> em f = 1 -> forall x, x ^+ (f x) = 1.

Lemma Free_set0 : Free set0.
Proof.
by split=> [|f g f0 g0 _ x]; rewrite ?(sup0P  _ _ f0, sup0P  _ _ g0) ?inE.
Qed.

Lemma Free_free : forall B, Free B -> free B.
Proof.
move=> B [nB1 frB]; split=> // f fB emf x.
rewrite (frB f (fun _ => 0)) => //; first by apply/supP.
by rewrite em1 emf. 
Qed.

Lemma afree_Free : forall B, abelian B -> free B -> Free B.
Proof.
move=> B abelB; case=> nB1 frB; split=> // f g Bf Bg emfg.
have: (em g)^-1 \in << B >> by rewrite groupV; apply/agenP=> //; exists g.
case/agenP=> // h Bh; move/(congr1 (mulg^~ (em g))); rewrite mulVg => hg.
have hf: em h * em f = 1 by rewrite emfg.
move: hg; rewrite -(aem_addf abelB Bh Bg) => emhg.
move: hf; rewrite -(aem_addf abelB Bh Bf) => emhf.
have Bhg: support (addf h g) B by rewrite -sup_addf Bh Bg.
have Bhf: support (addf h f) B by rewrite -sup_addf Bh Bf.
have Hf := frB _ Bhf emhf; have Hg := frB _ Bhg emhg.
move=> x; apply: (mulgI (x ^+ (h x))).
by rewrite -!expgn_add; rewrite Hf Hg. 
Qed.

Lemma free_predU1 : forall B x, x != 1 -> abelian (x |: B) ->
  <[x]> :&: << B >> = 1 -> free B -> free (x |: B).
Proof.
move=> B x nx1 abelxB xB1 [nB1 frB].
split=> [|f xBf]; first by rewrite !inE negb_or eq_sym nx1.
rewrite (@aem_force0 _ _ abelxB f x _ xBf); last by rewrite setU11.
move/(canRL (mulgK _)); rewrite mul1g; set z := _^-1 => def_z.
have xz: z \in <[x]> by rewrite groupV; apply: groupX; exact: cycle_id.    
have genBz: z \in << B >>.
  rewrite -def_z; apply/agenP; first by rewrite (asub abelxB) ?predU1_super. 
  by exists (force f x 0) => //; rewrite -sup_predU1_force.
have{xz genBz} z1: z = 1 by apply/set1P; rewrite -[[set 1]]xB1 inE xz.
move=> y; case: (y =P x) => [->|nyx]; first by apply: invg_inj; rewrite invg1.
by rewrite -(neq_force f 0 nyx) frB ?{}def_z // -sup_predU1_force. 
Qed.

(*
Fixpoint sfreeb (s : seq gT) : bool :=
if s is x::s'
then (x != 1) && sfreeb s' && subset (<[x]> :&: << s' >>) [set 1]
else true.

Definition freeb (B : pred gT) := sfreeb (enum B).

Lemma freeb1 : forall B, freeb B -> ~B 1.
Proof.
move=> B. rewrite/freeb -(filter_enum B).
elim: (enum gT) => //= x s Hind. 
case Bx: (B x) => //=. case/andP; case/andP; move/negP => notx1 Hfree _. 
case/orP => //=; exact: Hind. exact: Hind.
Qed.

Lemma freeb_free : forall B, freeb B -> free B.
Proof.
rewrite/free/freeb/em; move=> B sfB; split; first exact: freeb1.
move=> f; rewrite -(eq_sup f (filter_enum B));
elim: (enum gT) (enum_uniq gT) f sfB => /= [_ f _ f0 _ x | x s Hind];
first by case fx: (f x) => //; move/forallP: f0; move/(_ x); rewrite fx.
case/andP => notsx us; case Bx: (B x) => /=; last first.
- move=> f freeB fB; case fx: (f x) => /=; gsimpl; first exact: Hind.
  by move: (supP _ _ fB x); rewrite mem_filter Bx fx; move/implyP.
- move=> f; case/andP; case/andP => _ sfB Inter fB. 
  rewrite -{2}(mulgV (x ^+ f x)); move/mulgI => xfx.
  have xfx1:  x ^+ f x = 1. apply: sym_eq; apply/set1P;
  apply: (subsetP Inter); apply/setIP; split; first by apply/cycleP;
  exists (f x). rewrite -groupV -xfx; clear Hind sfB Inter xfx. 
  elim: s f x Bx notsx fB us => /= [* | y s Hind f x Bx]; first exact: group1. 
    rewrite negb_or; case/andP; move/negP => ynotx notsx; case By: (B y);
    last first.
  + move=> fB; case/andP => notsy us; case fy: (f y) => /=; first by gsimpl;
    apply: (Hind _ x). by move/implyP: (supP _ _ fB y);
    rewrite /= fy eq_sym (mem_filter B s y) By /= orbF.  
  + move=> fB; case/andP => sy us; apply: groupM; first by apply: groupX; 
    apply: (subsetP (subset_generated _)); rewrite /= eq_refl.
    have: subset << filter B s >> << y :: filter B s >>. by apply: sub_gen; 
    apply/subsetP => z /= ->; rewrite orbT. move/subsetP; apply.
    rewrite (@eq_foldr gT (fun a b => (a ^+ f a) * b)
    (fun a b => (a ^+ force f x 0 a) * b) s);
    first by apply: (Hind _ y) => //; rewrite -sup_predU1_force.
    by move=> a b sa; rewrite neq_force => // ax; rewrite ax in sa;
    apply: (negP notsx).
  move=> y; case xy: (x == y); first by move/eqP: xy <-.
  rewrite -!(@neq_force gT f x 0); last by move=> yx;
  rewrite yx eq_refl in xy. apply: Hind => //=;
  first by rewrite -sup_predU1_force. 
  rewrite -(@eq_foldr gT (fun a b => (a ^+ f a) * b)
  (fun a b => (a ^+ (force f x 0 a)) * b)); first by rewrite xfx xfx1;
  gsimpl. by move=> a b sa; rewrite neq_force => // ax; rewrite ax in sa;
  apply: (negP notsx).
Qed. 
*)

(*
Lemma free_freeb : forall B, abelian B -> free B -> freeb B.
Proof.
move=> B abelB; case => notB1 H; rewrite/free/freeb/em. 
elim: (enum gT) (enum_uniq gT) => //= x s Hind. case/andP => notsx us.
case Bx: (B x) => /=; last exact: Hind. apply/andP. split. 
- apply/andP. split; last by exact: Hind.
  by  apply/negP; move/eqP=> x1; rewrite x1 in Bx. 
- apply/subsetP => y. case/setIP. case/cycleP => n. move/eqP <-.  
  case/agenP; first by apply: (@asub _ B _) => //; apply/subsetP => z;
  rewrite mem_filter; case/andP. move=> f fB. emxn. apply



rewrite/free/freeb/em; move=> B; case => notB1. 
elim: (enum gT) (enum_uniq gT) => //= x s Hind. case/andP => notsx us H.
case Bx: (B x) => /=; last by apply: Hind => // f fB H2; 
apply: H => //; rewrite (sup0P _ _ fB x) /=; gsimpl; rewrite Bx. 
apply/andP. split. 
- apply/andP. split; last first. apply: Hind => //.

by exact: Hind.
  by  apply/negP; move/eqP=> x1; rewrite x1 in Bx. 
- apply/subsetP => y. case/setIP. case/cycleP => n. move/eqP <-. 
*)

End Free.


(* Definition of and lemmas on bases *)

Section Base.

Variable (gT : finGroupType).

Definition base (E B : {set gT}) := free B /\ <<B>> = E.

Lemma base1 : base 1 set0.
Proof. split; [apply: Free_free; exact: Free_set0 | exact: gen0]. Qed.

End Base.


Section StructureTheorems.

(* Every abelian finite group has a base. Lemma + theorem *)

Variable (gT : finGroupType).

Lemma abelian_base_aux : forall E : {set gT}, abelian E ->
  exists2 B : seq gT, #|B| < #|E|.+1 & base <<E>> [set x \in B].
Proof.
move=> E; elim: {E}_.+1 {-2 4}E (ltnSn #|E|) => // n IHn E cardE abelE.
case: (pickP (mem E)) => /= [z Ez | E0]; last first.
  exists ([::] : seq gT); first by rewrite card0.
  rewrite (_ : E = set0) ?gen0; first exact: base1.
  apply/setP=> x; rewrite inE; exact: E0.
case E1: (1 \in E); last move/idPn: E1 => notE1.
  rewrite -(@genD1 gT E 1 _) ?group1 //.
  case: (IHn (E :\ 1)); first by rewrite (cardsD1 1 E) E1 /= in cardE.
    by apply: (asub abelE); apply/subsetP => x; rewrite inE; case/andP.
  by move=> B; move/(ltn_addl 1) => cardB baseB; exists B.
have{Ez} [f []]: exists f, [/\ support f E, em f = 1 & 0 < f z].
  exists (peak z #[z]); split; first by rewrite -sup_peak Ez.
    by rewrite em_peak expg_order. 
  by rewrite /peak eqxx order_gt0.
move: {-4 6}E cardE notE1 (erefl << E >>).
elim: {f z}_.+1 {-2}f {-2}z (ltnSn (f z)) => // m mind f.
elim: {f}_.+1 {-2}f (ltnSn (esum f)) => // M Mind f esumf.
move=> x fxm1 X cardX notX1 XE fX emf fx0.
have abelX: abelian <<X>> by rewrite XE; apply: agen.
have Xx: x \in X by exact: (supP _ _ fX).
have genXx: x \in <<X>> by apply: mem_gen.
have fgenX: support f <<X>> by apply: (sup_sub (subset_gen X)).
have sXxX: X :\ _ \subset X.
  by move=> y; apply/subsetP=> z; rewrite inE; case/andP.
have sxX: [set x] \subset X by rewrite sub1set.
case: (x ^+ (f x) =P 1) => [xfx1 | xfx].
  case: (<[x]> :&: << X :\ x >> =P 1) => [X1x|]. 
    case: (IHn (X :\ x)) => [|| B cardB [FreeB BXx]].
    - by rewrite (cardsD1 x X) (supP _ _ fX x fx0) in cardX.  
    - apply: (asub abelX); exact: subset_trans (subset_gen X).
    exists (x :: B).
      rewrite -cardsE set_cons cardsU1 ltnS inE cardsE.
      by rewrite (leq_trans _ cardB) // -add1n leq_add2r leq_b1.
    split; last first; rewrite set_cons.
      by rewrite -XE; apply: genDU; rewrite ?sub1set.
    apply: free_predU1 => //=; last by rewrite BXx.
      by apply/eqP=> x1; rewrite -x1 Xx in notX1. 
    by apply: (asub abelX); rewrite -gen_subG (@genDU _ _ _ X).
  move/eqP; case/trivgPn=> y; case/setIP; case/cycleP => k <-{y}.
  rewrite (divn_eq k (f x)) expgn_add mulnC expgn_mul xfx1 exp1gn.
  rewrite mul1g -groupV; case/agenP=> [|g gX emg xknot1].
    by apply: (asub abelX); rewrite -gen_subG genS // subsetDr.
  apply: (mind (force g x (k %% f x)) x _ X) => //.
  - by rewrite /force eqxx (leq_trans _ (fxm1 : f x <= m)) // ltn_mod.
  - rewrite -sup_force => //; exact: sup_sub gX.
  - rewrite (aem_force abelX) //; last first.
      by apply: (sup_sub _ gX); rewrite -gen_subG genS // subsetDr.
    rewrite (sup0P _ _ gX x) /=; last by rewrite !inE eqxx Xx.
    by rewrite emg; gsimpl; apply: invg1.
  rewrite /force eqxx lt0n; apply: contra xknot1.
  by move/eqP=> ->; rewrite eqxx.
case: (em1_not1 emf xfx) => y ynotx fy0.
have Xy: y \in X by exact: supP fX _ _.
have genXy: y \in <<X>> by rewrite mem_gen.
have xyyx: commute x y by exact: (centsP abelX).
have notxyx: x * y != x.
  apply/eqP; move/(canRL (mulKg _)); rewrite mulVg => y1.
  by rewrite -y1 Xy in notX1.
have notxyy: x * y != y.
  apply/eqP; move/(canRL (mulgK _)); rewrite mulgV => x1.
  by rewrite -x1 Xx in notX1.
case Xxy: (x * y \in X).
  case: (IHn (X :\ x * y)) => [||B cardB [FreeB genB]].
  - by rewrite -(ltn_add2l (x * y \in X)) -cardsD1 Xxy.
  - apply: (asub abelX); exact: subset_trans (subset_gen X).
  exists B; first exact: (ltn_trans cardB).
  split=> //; rewrite genB -XE; apply: genD1.
  by rewrite groupMl mem_gen // !inE eq_sym; exact/andP.
case: (ltnP (f y) (f x)) => fxfy.
  apply: (mind f y _ X) => //; exact: leq_trans fxfy _.
case: (x * y =P 1) => [xy1 | xynot1].
  case: (IHn (X :\ y)) => [||B cardB [FreeB genB]]. 
  - by rewrite (cardsD1 y) (supP _ _ fX) in cardX. 
  - by apply: (asub abelX); apply: subset_trans (subset_gen X).
  exists B; [exact: ltnW | split => //].
  rewrite genB -XE; apply: genD1; rewrite -{1}(mulKg x y) xy1 mulg1 groupV.
  apply: mem_gen; rewrite !inE Xx andbT eq_sym; exact/eqP.
pose f' := force (force (force f x 0) (x * y) (f x)) y (f y - f x).
pose X' := x * y |: (X :\ x).
apply: (Mind f' _ (x * y) _ X') => //; last 1 first.
- by rewrite /f' /force (negPf notxyx) (negPf notxyy) eqxx.
- rewrite !esum_force /force (negPf notxyx) eq_sym (negPf notxyy).
  rewrite (introF eqP ynotx) (sup0P _ _ fX (x * y)) ?Xxy //.
  rewrite addn0 subn0 -addnA (subnKC fxfy) addnK.
  by rewrite -[M](subn1 M.+1) -leq_subS (esum_leq, leq_sub2) //.
- by rewrite /f' /force eqxx (negPf notxyy).
- by rewrite cardsU1 inE Xxy andbF -[~~ _]Xx -cardsD1.
- by rewrite !inE eq_sym (introF eqP xynot1) (negPf notX1) andbF.
- rewrite -XE; apply/setP; apply/subset_eqP; apply/andP.
  split; rewrite gen_subG; apply/subsetP => t.
    rewrite 3!inE; case/predU1P=> [->|].
      by apply: groupM; apply: mem_gen.
    case/andP=> _; exact: mem_gen.
  case tx: (t == x) => Xt; last first.
    by apply: mem_gen; rewrite !inE Xt tx orbT.
  rewrite {t tx Xt}(eqP tx) -(mulgK y x).
  by rewrite groupMl ?groupV mem_gen // !inE ?eqxx // Xy orbC; case: eqP.
- rewrite -sup_force; last by rewrite !inE Xy orbC; case: eqP.
  rewrite -sup_force; last by rewrite setU11.
  rewrite -sup_predU1_force; apply/supP => t ft /=.
  by rewrite !inE (supP _ _ fX t ft); case (t == x); rewrite ?orbT.
rewrite !(aem_force abelX) /force => //; first 1 last; first exact: groupM.  
- by apply/supP => t; case tx: (t == x) => // ft; exact: (supP _ _ fgenX).
- apply/supP => t; case: eqP => [-> _ | _]; first exact: groupM.
  by case: eqP => // _; apply: (supP _ _ fgenX).
rewrite emf !mul1g expMgn // mulKg (negPf notxyx) eq_sym (negPf notxyy).
rewrite (introF eqP ynotx) (sup0P _ _ fX (x * y)) ?Xxy // invg1 mulg1.
by rewrite -expgn_add subnKC ?mulgV.
Qed.

Theorem abelian_base : forall G : {group gT},
  abelian G -> exists B, base G B.
Proof.
by move=> G; case/abelian_base_aux=> B _; rewrite genGid; exists [set x \in B].
Qed.


End StructureTheorems.
