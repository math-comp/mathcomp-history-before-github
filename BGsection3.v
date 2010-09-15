Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq paths div.
Require Import fintype bigops prime binomial finset ssralg.
Require Import groups morphisms normal perm automorphism action commutators.
Require Import finalg zmodp gprod cyclic center pgroups gseries nilpotent sylow.
Require Import abelian maximal hall matrix mxrepresentation.
Require Import BGsection1 BGsection2.

(******************************************************************************)
(*   This file covers the material in B & G, Section 3, with the exception of *)
(* Theorem 3.6, whose long proof is in a sepearate file.                      *)
(*   Basic definitions relative to Frobenius groups are, temporarily, given   *)
(* here. All of this should move to the frobenius file once the relevant      *)
(* background material is available.                                          *)
(*   Note that in spite of the use of Gorenstein 2.7.6, the material in all   *)
(* of Section 3, and in all likelyhood the whole of B & G, does NOT depend on *)
(* the general proof of existence of Frobenius kernels, because results on    *)
(* Frobenius groups are only used when the semidirect product decomposition   *)
(* is already known, and (as we show below) in this case the kernel is always *)
(* equal to the normal complement of the Frobenius complement.                *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Local Open Scope ring_scope.
Import GroupScope GRing.Theory.

(* This should go in ssreflect.v *)
(* Allow overloading of the cast (x : T) syntax, put whitespace around the    *)
(* ":" symbol to avoid lexical clashes (and for consistency with the parsing  *)
(* precedence of the notation, which binds less tightly then application),    *)
(* and put printing boxes the print type of a long definition on a separate   *)
(* line rather than force-fit it at the right margin.                         *)
Notation "x : T" := (x : T)
  (at level 100, right associativity, format "'[hv' x '/ '  :  T ']'").
Notation "T : 'Type'" := (T%type : Type) (at level 100, only parsing).

(* Add to ssrnat *)
Lemma subn2 : forall n, (n - 2)%N = n.-2. Proof. by do 3?case. Qed.

(* Add to seq *)
Lemma perm_filterC : forall (T : eqType) (a : pred T) s,
  perm_eql (filter a s ++ filter (predC a) s) s.
Proof.
move=> T a s; apply/perm_eqlP; elim: s => //= x s IHs.
by case: (a x); last rewrite /= -cat1s perm_catCA; rewrite perm_cons.
Qed.

Section MoreDiv.

Lemma expn_sub : forall p m n,
   p > 0 -> m >= n -> (p ^ (m - n))%N = p ^ m %/ p ^ n.
Proof.
move=> p m n p_gt0 n_le_m.
by rewrite -{2}(subnK n_le_m) expn_add mulnK // expn_gt0 p_gt0.
Qed.

Lemma coprimeSn : forall n, coprime n.+1 n.
Proof.
by move=> n; rewrite -coprime_modl (modn_addr 1) coprime_modl coprime1n.
Qed.

Lemma coprimenS : forall n, coprime n n.+1.
Proof. by move=> n; rewrite coprime_sym coprimeSn. Qed.

Lemma coprimePn : forall n, n > 0 -> coprime n.-1 n.
Proof. by case=> // n _; rewrite coprimenS. Qed.

Lemma coprimenP : forall n, n > 0 -> coprime n n.-1.
Proof. by case=> // n _; rewrite coprimeSn. Qed.

End MoreDiv.

(* Two pigeon-hole lemmas for fintype.v and finset.v, respectively. *)
Lemma image_injP : forall (aT rT : finType) (f : aT -> rT) (A : pred aT),
  reflect {in A &, injective f} (#|[image f of A]| == #|A|).
Proof.
move=> aT rT f A; apply: (iffP eqP) => [eqfA |]; last exact: card_in_image.
by apply/dinjectiveP; apply/card_uniqP; rewrite size_map -cardE.
Qed.
Implicit Arguments image_injP [aT rT f A].

Lemma imset_injP : forall (aT rT : finType) (f : aT -> rT) (A : {set aT}),
  reflect {in A &, injective f} (#|f @: A| == #|A|).
Proof.
by move=> aT rT f A; rewrite [@imset _]unlock cardsE; exact: image_injP.
Qed.
Implicit Arguments imset_injP [aT rT f A].

Lemma setID : forall (T : finType) (A B : {set T}), A :&: B :|: A :\: B = A.
Proof. by move=> T A B; rewrite setDE -setIUr setUCr setIT. Qed.

Section MorePrime.

Open Scope nat_scope.

Lemma prime_nt_dvdP : forall d p, d != 1 -> prime p -> reflect (d = p) (d %| p).
Proof.
move=> d p d_neq1; case/primeP=> _ min_p; apply: (iffP idP) => [|-> //].
by move/min_p; rewrite (negPf d_neq1) /=; move/eqP.
Qed.

Lemma prime_oddPn : forall p, prime p -> reflect (p = 2) (~~ odd p).
Proof.
by move=> p p_pr; apply: (iffP idP) => [|-> //]; case/even_prime: p_pr => ->.
Qed.

Lemma pfactorKpdiv : forall p n,
  prime p -> logn (pdiv (p ^ n)) (p ^ n) = n.
Proof. by move=> p [//|n] p_pr; rewrite pdiv_pfactor ?pfactorK. Qed.

End MorePrime.

Section MoreSsralg.

Variable R : unitRingType.
Open Scope ring_scope.

Lemma div1r : forall x : R, 1 / x = x^-1. Proof. by move=> x; exact: mul1r. Qed.

End MoreSsralg.

(* Some properties of G^#, and a new construction:                            *)
(*  gcore H G == the largest subgroup of H normalised by G (if H \subset G,   *)
(*               this is the largest normal subgroup of G contained in H).    *)
(* Helper notation for defining new groups *)
Notation gsort gT := (FinGroup.arg_sort (FinGroup.base gT%type)) (only parsing).

Section MoreGroups.

Variable gT : finGroupType.
Implicit Types x y : gT.
Implicit Types A B : {set gT}.
Implicit Types G H : {group gT}.

Lemma expgnC : forall x m n, x ^+ m ^+ n = x ^+ n ^+ m.
Proof. by move=> x m n; rewrite -!expgn_mul mulnC. Qed.

(* Should update the proof of conjSg to use this lemma*)
Lemma rcosetSg : forall x A B, (A :* x \subset B :* x) = (A \subset B).
Proof.
move=> x A B; apply/idP/idP=> sAB; last exact: mulSg.
by rewrite -(rcosetK x A) -(rcosetK x B) mulSg.
Qed.

Lemma sub_rcoset : forall x A B, (A \subset B :* x) = (A :* x ^-1 \subset B).
Proof. by move=> x A B; rewrite -(rcosetSg x^-1) rcosetK. Qed.

Lemma sub_rcosetV : forall x A B, (A \subset B :* x^-1) = (A :* x \subset B).
Proof. by move=> x A B; rewrite sub_rcoset invgK. Qed.

Lemma conjCg : forall A x, (~: A) :^ x = ~: A :^ x.
Proof. by move=> A x; apply/setP=> y; rewrite inE !mem_conjg inE. Qed.

Lemma conjDg : forall A B x, (A :\: B) :^ x = A :^ x :\: B :^ x.
Proof. by move=> A B x; rewrite !setDE !(conjCg, conjIg). Qed.

Lemma conjD1g : forall A x, A^# :^ x = (A :^ x)^#.
Proof. by move=> A x; rewrite conjDg conjs1g. Qed.

Lemma group1_contra : forall G x, x \notin G -> x != 1.
Proof. by move=> G x; apply: contra; move/eqP->. Qed.

Lemma cardMg_divn : forall G H, #|G * H| = (#|G| * #|H|) %/ #|G :&: H|.
Proof. by move=> G H; rewrite mul_cardG mulnK ?cardG_gt0. Qed.

Lemma cardIg_divn : forall G H, #|G :&: H| = (#|G| * #|H|) %/ #|G * H|.
Proof. by move=> G H; rewrite mul_cardG mulKn // (cardD1 (1 * 1)) mem_mulg. Qed.

Lemma normD1 : forall A, 'N(A^#) = 'N(A).
Proof.
move=> A; apply/setP=> x; rewrite !inE conjD1g.
apply/idP/idP=> nAx; last exact: setSD.
apply/subsetP=> y Axy;  move/implyP: (subsetP nAx y); rewrite !inE Axy andbT.
by case: eqP Axy => // ->; rewrite mem_conjg conj1g.
Qed.

Lemma groupD1_inj : forall G H, G^# = H^# -> G :=: H.
Proof. by move=> G H; move/(congr1 (setU 1)); rewrite !setD1K. Qed.

Lemma nt_prime_order : forall p x, prime p -> x ^+ p = 1 -> x != 1 -> #[x] = p.
Proof.
move=> p x p_pr xp ntx; apply/prime_nt_dvdP; rewrite ?order_eq1 //.
by rewrite order_dvdn xp.
Qed.

Lemma expg_mod : forall p k x, x ^+ p = 1 -> x ^+ (k %% p) = x ^+ k.
Proof.
move=> p k x xp.
by rewrite {2}(divn_eq k p) expgn_add mulnC expgn_mul xp exp1gn mul1g.
Qed.

Lemma invg2id : forall x, #[x] = 2 -> x^-1 = x.
Proof. by move=> x ox; rewrite invg_expg ox. Qed.

Lemma cycle2g : forall x, #[x] = 2 -> <[x]> = [set 1; x].
Proof. by move=> x ox; apply/setP=> y; rewrite cycle_traject ox !inE mulg1. Qed.

Lemma class_sub_norm : forall G A x,
  G \subset 'N(A) -> (x ^: G \subset A) = (x \in A).
Proof. by move=> G A x nAG; rewrite acts_sub_orbit // astabsJ. Qed.

Lemma class_supportD1 : forall G H, (class_support H G)^# =  cover (H^# :^: G).
Proof.
move=> G H; apply/setP=> x; apply/idP/idP.
  case/setD1P=> nt_x; case/imset2P=> y z Hy Gz def_x.
  apply/bigcupP; exists (H^# :^ z); first by rewrite mem_imset.
  by rewrite conjD1g !inE nt_x def_x memJ_conjg.
case/bigcupP=> Hz; case/imsetP=> z Gz ->{Hz}; rewrite conjD1g 4!inE.
by case/andP=> ->; case/imsetP=> y Hy ->; rewrite mem_imset2.
Qed.

Lemma normsC : forall A, 'N(~: A) = 'N(A).
Proof.
by move=> A; apply/setP => x; rewrite -groupV !inE conjCg setCS sub_conjg.
Qed.

Lemma normsD : forall A B C,
  A \subset 'N(B) -> A \subset 'N(C) -> A \subset 'N(B :\: C).
Proof. by move=> A B C nBA nCA; rewrite setDE normsI ?normsC. Qed.

Lemma cycle_norm_cycle : forall x y,
  (<[y]> \subset 'N(<[x]>)) = (x ^ y \in <[x]>).
Proof. by move=> x y; rewrite cycle_subG inE -cycleJ cycle_subG. Qed.

Lemma mulgen_idPl : forall G A, reflect (G <*> A = G) (A \subset G).
Proof.
move=> G A; apply: (iffP idP) => [sHG | <-]; last by rewrite mulgen_subr.
by rewrite mulgenE (setUidPl sHG) genGid.
Qed.

Lemma mulgen_idPr : forall A G, reflect (A <*> G = G) (A \subset G).
Proof. by move=> A G; rewrite mulgenC; exact: mulgen_idPl. Qed.

Lemma mulGidPl : forall G H, reflect (G * H = G) (H \subset G).
Proof.
by move=> G H; apply: (iffP idP) => [|<-]; [exact: mulGSid | exact: mulG_subr].
Qed.

Lemma mulGidPr : forall G H, reflect (G * H = H) (G \subset H).
Proof.
by move=> G H; apply: (iffP idP) => [|<-]; [exact: mulSGid | exact: mulG_subl].
Qed.

Section Gcore.

Definition gcore A B := \bigcap_(x \in B) A :^ x.

Canonical Structure gcore_group H B := [group of gcore H B].

Lemma gcore_sub : forall A G, gcore A G \subset A.
Proof. by move=> A G; rewrite (bigcap_min 1) ?conjsg1. Qed.

Lemma gcore_norm : forall A G, G \subset 'N(gcore A G).
Proof.
move=> A G; apply/subsetP=> x Gx; rewrite inE; apply/bigcapsP=> y Gy.
by rewrite sub_conjg -conjsgM bigcap_inf ?groupM ?groupV.
Qed.

Lemma gcore_max : forall A B G,
  B \subset A -> G \subset 'N(B) -> B \subset gcore A G.
Proof.
move=> A B G sBA nBG; apply/bigcapsP=> y Gy.
by rewrite -sub_conjgV (normsP nBG) ?groupV.
Qed.

End Gcore.

(* An elementary proof; it is almost as short as the "advanced" proof using   *)
(* group actions, and besides the value of the coset is used in extremal.v.   *)
Lemma rcoset_index2 : forall G H x,
  H \subset G -> #|G : H| = 2 -> x \in G :\: H -> H :* x = G :\: H.
Proof.
move=> G H x sHG indexHG; case/setDP=> Gx notHx; apply/eqP.
rewrite eqEcard -(leq_add2l #|G :&: H|) cardsID -(LaGrangeI G H) indexHG muln2.
rewrite (setIidPr sHG) card_rcoset addnn leqnn andbT.
apply/subsetP=> yx; case/rcosetP=> y Hy ->{yx}; apply/setDP.
by rewrite !groupMl // (subsetP sHG).
Qed.

Lemma index2_normal : forall G H, H \subset G -> #|G : H| = 2 -> H <| G.
Proof.
move=> G H sHG indexHG; rewrite /normal sHG; apply/subsetP=> x Gx.
case Hx: (x \in H); first by rewrite inE conjGid.
rewrite inE conjsgE mulgA -sub_rcosetV -invg_rcoset.
by rewrite !(rcoset_index2 sHG) ?inE ?groupV ?Hx // invDg !invGid.
Qed.

End MoreGroups.

Implicit Arguments mulgen_idPl [gT G A].
Implicit Arguments mulgen_idPr [gT G A].
Implicit Arguments mulGidPl [gT G H].
Implicit Arguments mulGidPr [gT G H].

(* Complements in the morphic image, and a new property.                      *)
(*  ifactm injf g == the factor morphism of g wrt f, when f is injective      *)
(*                   (injf : 'injm f); the domain of ifactm injf g is f @* G, *)
(*                   where G = 'dom(G).                                       *)
(*      H \homg G <=> H is a homomorphic image of G                           *)
Section MoreMorphism.

Section MoreMorphim.

Variables (aT rT : finGroupType) (D : {group aT}) (f : {morphism D >-> rT}).
Implicit Type A B : {set aT}.
Implicit Type R : {set rT}.

Lemma leq_morphim : forall A, #|f @* A| <= #|A|.
Proof.
move=> A; apply: (leq_trans (leq_imset_card _ _)).
by rewrite subset_leq_card ?subsetIr.
Qed.

Lemma morphim_mulgen : forall A B,
  A \subset D -> B \subset D -> f @* (A <*> B) = f @* A <*> f @* B.
Proof. by move=> A B sAD sBD; rewrite morphim_gen ?morphimU // subUset sAD. Qed.

Lemma morphim_setIpre : forall A R, f @* (A :&: f @*^-1 R) = f @* A :&: R.
Proof.
move=> A R; apply/setP=> fa; apply/morphimP/setIP=> [[a Ba] | []].
  by rewrite !inE Ba /=; case/andP=> Aa Dfa ->; rewrite mem_morphim.
by case/morphimP=> a Ba Aa -> Dfa; exists a; rewrite // !inE Aa Ba.
Qed.

Lemma morph_injm_eq1 : forall x, 'injm f -> x \in D -> (f x == 1) = (x == 1).
Proof.
by move=> x injf Dx; rewrite -(morph1 f) (inj_in_eq (injmP _ injf)) ?group1.
Qed.

Lemma morphim_injm_eq1 : forall A,
  'injm f -> A \subset D -> (f @* A == 1) = (A == 1).
Proof.
move=> A injf sAD; rewrite -(morphim1 f).
by apply/eqP/eqP=> [|-> //]; apply: injm_morphim_inj; last exact: sub1G.
Qed.

Lemma order_injm : forall x, 'injm f -> x \in D -> #[f x] = #[x].
Proof.
by move=> x injf Dx; rewrite orderE -morphim_cycle // card_injm ?cycle_subG.
Qed.

Lemma card_im_injm : (#|f @* D| == #|D|) = 'injm f.
Proof. by rewrite morphimEdom (sameP imset_injP (injmP _)). Qed.

Lemma eq_in_morphim : forall (D2 A : {set aT}) (f2 : {morphism D2 >-> rT}),
  D :&: A = D2 :&: A -> {in A, f =1 f2} -> f @* A = f2 @* A.
Proof.
move=> D2 A f2 eqD12A eqAf12; rewrite /morphim /= eqD12A.
by apply: eq_in_imset => x; case/setIP=> _; exact: eqAf12.
Qed.

(* Common case of morphim_restrm; should fold all instances of it. *)
Lemma im_restrm : forall A (sAD : A \subset D), restrm sAD f @* A = f @* A.
Proof. by move=> A sAD; rewrite morphim_restrm setIid. Qed.
  
End MoreMorphim.

Section InjFactm.

Variables (gT aT rT : finGroupType) (D G : {group gT}).
Variables (g : {morphism G >-> rT}) (f : {morphism D >-> aT}) (injf : 'injm f).

Definition ifactm :=
  tag (domP [morphism of g \o invm injf] (morphpre_invm injf G)).

Lemma ifactmE : {in D, forall x, ifactm (f x) = g x}.
Proof.
rewrite /ifactm => x Dx; case: domP => f' /= [def_f' _ _ _].
by rewrite {f'}def_f' //= invmE.
Qed.

Lemma morphim_ifactm : forall A : {set gT},
  A \subset D -> ifactm @* (f @* A) = g @* A.
Proof.
rewrite /ifactm => A sAD; case: domP => _ /= [_ _ _ <-].
by rewrite morphim_comp morphim_invm.
Qed.

Lemma im_ifactm : G \subset D -> ifactm @* (f @* G) = g @* G.
Proof. exact: morphim_ifactm. Qed.

Lemma morphpre_ifactm : forall C, ifactm @*^-1 C = f @* (g @*^-1 C).
Proof.
rewrite /ifactm => C; case: domP => _ /= [_ _ -> _].
by rewrite morphpre_comp morphpre_invm.
Qed.

Lemma ker_ifactm : 'ker ifactm = f @* 'ker g.
Proof. exact: morphpre_ifactm. Qed.

Lemma injm_ifactm : 'injm g -> 'injm ifactm.
Proof. by rewrite ker_ifactm; move/trivgP->; rewrite morphim1. Qed.

End InjFactm.

Section Homg.

Import finfun.

Implicit Types rT gT aT : finGroupType.

Definition homg rT aT (C : {set rT}) (D : {set aT}) :=
  existsb f : {ffun aT -> rT}, (morphic D f && (f @: D == C)).

Lemma homgP : forall rT aT (C : {set rT}) (D : {set aT}), 
  reflect (exists f : {morphism D >-> rT}, f @* D = C) (homg C D).
Proof.
move=> rT aT H G; apply: (iffP existsP) => [[f] | [f <-]].
  case/andP=> fM; move/eqP=> <-; exists (morphm_morphism fM).
  by rewrite /morphim /= setIid.
exists (finfun f); apply/andP; split.
  by apply/morphicP=> x y Dx Dy; rewrite !ffunE morphM.
by apply/eqP; rewrite /morphim setIid; apply: eq_imset => x; rewrite ffunE.
Qed.

Lemma morphim_homg : forall aT rT (A D : {set aT}) (f : {morphism D >-> rT}),
  A \subset D -> homg (f @* A) A.
Proof.
move=> aT rT A D f sAD; apply/homgP; exists (restrm_morphism sAD f).
by rewrite morphim_restrm setIid.
Qed.

Lemma leq_homg : forall rT aT (C : {set rT}) (G : {group aT}),
  homg C G -> #|C| <= #|G|.
Proof. move=> rT aT C G; case/homgP=> f <-; exact: leq_morphim. Qed.

Lemma homg_refl : forall aT (A : {set aT}), homg A A.
Proof.
by move=> aT A; apply/homgP; exists (idm_morphism A); rewrite im_idm.
Qed.

Lemma homg_trans : forall aT (B : {set aT}),
                   forall rT (C : {set rT}) gT (G : {group gT}),
  homg C B -> homg B G -> homg C G.
Proof.
move=> aT B rT C gT G homCB homBG.
case/homgP: homBG homCB => fG <-; case/homgP=> fK <-.
by rewrite -morphim_comp morphim_homg // -sub_morphim_pre.
Qed.

Lemma isogEcard : forall rT aT (G : {group rT}) (H : {group aT}),
  (G \isog H) = (homg G H) && (#|H| <= #|G|).
Proof.
move=> rT aT G H; rewrite isog_sym; apply/isogP/andP=> [[f injf <-] | []].
  by rewrite leq_eqVlt eq_sym card_im_injm injf morphim_homg.
case/homgP=> f <-; rewrite leq_eqVlt eq_sym card_im_injm.
by rewrite ltnNge leq_morphim orbF; exists f.
Qed.

Lemma isog_hom : forall rT aT (G : {group rT}) (H : {group aT}),
  G \isog H -> homg G H.
Proof. by move=> rT aT G H; rewrite isogEcard; case/andP. Qed.

Lemma isogEhom : forall rT aT (G : {group rT}) (H : {group aT}),
  (G \isog H) = homg G H && homg H G.
Proof.
move=> rT aT G H; apply/idP/andP=> [isoGH | [homGH homHG]].
  by rewrite !isog_hom // isog_sym.
by rewrite isogEcard homGH leq_homg.
Qed.

Lemma eq_homgl : forall gT aT rT,
                 forall (G : {group gT}) (H : {group aT}) (K : {group rT}),
  G \isog H -> homg G K = homg H K.
Proof.
move=> gT aT rT G H K; rewrite isogEhom; case/andP=> homGH homHG.
apply/idP/idP; exact: homg_trans.
Qed.

Lemma eq_homgr : forall gT rT aT,
                 forall (G : {group gT}) (H : {group rT}) (K : {group aT}),
  G \isog H -> homg K G = homg K H.
Proof.
move=> gT rT aT G H K; rewrite isogEhom; case/andP=> homGH homHG.
apply/idP/idP=> homK; exact: homg_trans homK _.
Qed.

End Homg.

End MoreMorphism.

Notation "G \homg H" := (homg G H)
  (at level 70, no associativity) : group_scope.

Implicit Arguments homgP [rT aT C D].

Section MoreNormal.

Variables (gT : finGroupType) (H : {group gT}).

(* Consider renaming the current quotient_mulgen to quotient_mulgenr *)
Lemma quotient_mulgen2 : forall A B : {set gT},
  A \subset 'N(H) -> B \subset 'N(H) -> (A <*> B) / H = (A / H) <*> (B / H).
Proof. exact: morphim_mulgen. Qed.

Lemma leq_quotient : forall A : {set gT}, #|A / H| <= #|A|.
Proof. exact: leq_morphim. Qed.

Lemma quotient_homg : forall A : {set gT}, A \subset 'N(H) -> homg (A / H) A.
Proof. move=> A; exact: morphim_homg. Qed.

Lemma card_homg : forall (aT rT : finGroupType),
                  forall (G : {group aT}) (R : {group rT}),
  G \homg R -> #|G| %| #|R|.
Proof.
by move=> aT rT G R; case/homgP=> f <-; rewrite card_morphim setIid dvdn_indexg.
Qed.

(* We could have a stronger version of third_isog, along the same lines. *)
Lemma homg_quotientS : forall (K : {group gT}) (A : {set gT}),
  A \subset 'N(H) -> A \subset 'N(K) -> H \subset K -> A / K \homg A / H.
Proof.
move=> K A; rewrite -!(gen_subG A) /=; set G := <<A>> => nHG nKG sKH.
have sub_ker: 'ker (restrm nHG (coset H)) \subset 'ker (restrm nKG (coset K)).
  by rewrite !ker_restrm !ker_coset setIS.
have sAG: A \subset G := subset_gen A; rewrite -(setIidPr sAG).
rewrite -[_ / H](morphim_restrm nHG) -[_ / K](morphim_restrm nKG) /=.
by rewrite -(morphim_factm sub_ker (subxx G)) morphim_homg ?morphimS.
Qed.

End MoreNormal.

(* Injective morphisms map characteristic subgroups. *)
Section MoreAutomorphisms.

Section MoreInjm.

Variables (aT rT : finGroupType) (D : {group aT}) (f : {morphism D >-> rT}).

Hypothesis injf : 'injm f.

Lemma injm_char : forall G H : {group aT},
  G \subset D -> H \char G -> f @* H \char f @* G.
Proof.
move=> G H sGD; case/charP=> sHG charH.
apply/charP; split=> [|g injg gfG]; first exact: morphimS.
have: 'dom (invm injf \o g \o f) = G.
  by rewrite /dom /= -(morphpreIim g) (setIidPl _) ?injmK // gfG morphimS.
case/domP=> h [_ ker_h _ im_h].
have hH: h @* H = H.
  apply: charH; first by rewrite ker_h !injm_comp ?injm_invm.
  by rewrite -im_h !morphim_comp gfG morphim_invm.
rewrite /= -{2}hH -im_h !morphim_comp morphim_invmE morphpreK //.
by rewrite (subset_trans _ (morphimS f sGD)) //= -{3}gfG !morphimS.
Qed.

End MoreInjm.

Section StillMoreInjm.

Variables (aT rT : finGroupType) (D : {group aT}) (f : {morphism D >-> rT}).
Hypothesis injf : 'injm f.

Lemma char_injm : forall G H : {group aT},
  G \subset D -> H \subset D -> (f @* H \char f @* G) = (H \char G).
Proof.
move=> G H sGD sHD; apply/idP/idP; last exact: injm_char.
by move/(injm_char (injm_invm injf)); rewrite !morphim_invm ?morphimS // => ->.
Qed.

End StillMoreInjm.

End MoreAutomorphisms.

(* This should go in a new file "presentation.v". *)
(* Support for generator-and-relation presentations of groups. We provide the *)
(* syntax:                                                                    *)
(*  G \homg Grp (x_1 : ... x_n : (s_1 = t_1, ..., s_m = t_m))                 *)
(*    <=> G is generated by elements x_1, ..., x_m satisfying the relations   *)
(*        s_1 = t_1, ..., s_m = t_m, i.e., G is a homomorphic image of the    *)
(*        group generated by the x_i, subject to the relations s_j = t_j.     *)
(*  G \isog Grp (x_1 : ... x_n : (s_1 = t_1, ..., s_m = t_m))                 *)
(*    <=> G is isomorphic to the group generated by the x_i, subject to the   *)
(*        relations s_j = t_j. This is an intensional predicate (in Prop), as *)
(*        even the non-triviality of a generated group is undecidable.        *)
(* Syntax details:                                                            *)
(*  - Grp is a litteral constant.                                             *)
(*  - There must be at one generator and one relation.                        *)
(*  - A relation s_j = 1 can be abbreviated as simply s_j (a.k.a. a relator). *)
(*  - Two consecutive relations s_j = t, s_j+1 = t can be abbreviated         *)
(*    s_j = s_j+1 = t.                                                        *)
(*  - The s_j and t_j are terms built from the x_i and the standard group     *)
(*    operators *, 1, ^-1, ^+, ^-, ^, [~ u_1, ..., u_k]; no other operator or *)
(*    abbreviation may be used, as the notation is implemented using static   *)
(*    overloading.                                                            *)
(*  - This is the closest we could get to the notation used in Aschbacher,    *)
(*       Grp (x_1, ... x_n : t_1,1 = ... = t_1,k1, ..., t_m,1 = ... = t_m,km) *)
(*    under the current limitations of the Coq Notation facility.             *)
(* Semantics details:                                                         *)
(* - G \isog Grp (...) : Prop expands to the statement                        *)
(*      forall rT (H : {group rT}), (H \homg G) = (H \homg Grp (...))         *)
(*   (with rT : finGroupType).                                                *)
(* - G \homg Grp (x_1 : ... x_n : (s_1 = t_1, ..., s_m = t_m)) : bool, with   *)
(*   G : {set gT}, is convertible to the boolean expression                   *)
(*     existsb t : gT * ... gT, let: (x_1, ..., x_n) := t in                  *)
(*       (<[x_1]> <*> ... <*> <[x_n]>, (s_1, ... (s_m-1, s_m) ...))           *)
(*          == (G, (t_1, ... (t_m-1, t_m) ...))                               *)
(*   where the tuple comparison above is convertible to the conjunction       *)
(*       [&& <[x_1]> <*> ... <*> <[x_n]> == G, s_1 == t_1, ... & s_m == t_m]  *)
(*   Thus G \homg Grp (...) can be easily exploited by destructing the tuple  *)
(*   created case/existsP, then destructing the tuple equality with case/eqP. *)
(*   Conversely it can be proved by using apply/existsP, providing the tuple  *)
(*   with a single exists (u_1, ..., u_n), then using rewrite !xpair_eqE /=   *)
(*   to expose the conjunction, and optionally using an apply/and{m+1}P view  *)
(*   to split it into subgoals (in that case, the rewrite is in principle     *)
(*   redundant, but necessary in practice because of the poor performance of  *)
(*   conversion in the Coq unifier).                                          *)

Module Presentation.

Section Presentation.

Implicit Types gT rT : finGroupType.
Implicit Type vT : finType. (* tuple value type *)

Inductive term :=
  | Cst of nat
  | Idx
  | Inv of term
  | Exp of term & nat
  | Mul of term & term
  | Conj of term & term
  | Comm of term & term.

Fixpoint eval {gT} e t : gT :=
  match t with
  | Cst i => nth 1 e i
  | Idx => 1
  | Inv t1 => (eval e t1)^-1
  | Exp t1 n => eval e t1 ^+ n
  | Mul t1 t2 => eval e t1 * eval e t2
  | Conj t1 t2 => eval e t1 ^ eval e t2
  | Comm t1 t2 => [~ eval e t1, eval e t2]
  end.

Inductive formula := Eq2 of term & term | And of formula & formula.
Coercion Eq1 s := Eq2 s Idx.
Definition Eq3 s1 s2 t := And (Eq2 s1 t) (Eq2 s2 t).

Inductive rel_type := NoRel | Rel vT of vT & vT.

Coercion bool_of_rel r := if r is Rel vT v1 v2 then v1 == v2 else true.

Definition and_rel vT (v1 v2 : vT) r :=
  if r is Rel wT w1 w2 then Rel (v1, w1) (v2, w2) else Rel v1 v2.
 
Fixpoint rel {gT} (e : seq gT) f r :=
  match f with
  | Eq2 s t => and_rel (eval e s) (eval e t) r
  | And f1 f2 => rel e f1 (rel e f2 r)
  end.

Inductive type := Generator of term -> type | Formula of formula.
Definition Cast p : type := p. (* syntactic scope cast *)
Coercion Formula : formula >-> type.

Inductive env gT := Env of {set gT} & seq gT.
Definition env1 {gT} (x : gT : finType) := Env <[x]> [:: x].

Fixpoint sat gT vT B n (s : vT -> env gT) p :=
  match p with
  | Formula f =>
    existsb v, let: Env A e := s v in and_rel A B (rel (rev e) f NoRel)
  | Generator p' =>
    let s' v := let: Env A e := s v.1 in Env (A <*> <[v.2]>) (v.2 :: e) in
    sat B n.+1 s' (p' (Cst n))
  end.

Definition hom gT (B : {set gT}) p := sat B 1 env1 (p (Cst 0)).
Definition iso gT (B : {set gT}) p :=
  forall rT (H : {group rT}), (H \homg B) = hom H p.

End Presentation.

End Presentation.

(* In a separate file, we could Import Presentation at this point. *)

(* Declare (implicitly) the argument scope tags. *)
Notation "1" := Presentation.Idx : group_presentation.
Arguments Scope Presentation.Inv [group_presentation].
Arguments Scope Presentation.Exp [group_presentation nat_scope].
Arguments Scope Presentation.Mul [group_presentation group_presentation].
Arguments Scope Presentation.Conj [group_presentation group_presentation].
Arguments Scope Presentation.Comm [group_presentation group_presentation].
Arguments Scope Presentation.Eq1 [group_presentation].
Arguments Scope Presentation.Eq2 [group_presentation group_presentation].
Arguments Scope Presentation.Eq3
  [group_presentation group_presentation group_presentation].
Arguments Scope Presentation.And [group_presentation group_presentation].
Arguments Scope Presentation.Formula [group_presentation].
Arguments Scope Presentation.Cast [group_presentation].

Infix "*" := Presentation.Mul : group_presentation.
Infix "^+" := Presentation.Exp : group_presentation.
Infix "^" := Presentation.Conj : group_presentation.
Notation "x ^-1" := (Presentation.Inv x) : group_presentation.
Notation "x ^- n" := (Presentation.Inv (x ^+ n)) : group_presentation.
Notation "[ ~ x1 , x2 , .. , xn ]" :=
  (Presentation.Comm .. (Presentation.Comm x1 x2) .. xn) : group_presentation.
Notation "x = y" := (Presentation.Eq2 x y) : group_presentation.
Notation "x = y = z" := (Presentation.Eq3 x y z) : group_presentation.
Notation "( r1 , r2 , .. , rn )" := 
  (Presentation.And .. (Presentation.And r1 r2) .. rn) : group_presentation.

(* Declare (implicitly) the argument scope tags. *)
Notation "x : p" := (fun x => Presentation.Cast p) : nt_group_presentation.
Arguments Scope Presentation.Generator [nt_group_presentation].
Arguments Scope Presentation.hom [_ group_scope nt_group_presentation].
Arguments Scope Presentation.iso [_ group_scope nt_group_presentation].

Notation "x : p" := (Presentation.Generator (x : p)) : group_presentation.

Notation "H \homg 'Grp' p" := (Presentation.hom H p)
  (at level 70, p at level 0, format "H  \homg  'Grp'  p") : group_scope.

Notation "H \isog 'Grp' p" := (Presentation.iso H p)
  (at level 70, p at level 0, format "H  \isog  'Grp'  p") : group_scope.

Notation "H \homg 'Grp' ( x : p )" := (Presentation.hom H (x : p))
  (at level 70, x at level 0,
   format "'[hv' H  '/ '  \homg  'Grp'  ( x  :  p ) ']'") : group_scope.

Notation "H \isog 'Grp' ( x : p )" := (Presentation.iso H (x : p))
  (at level 70, x at level 0,
   format "'[hv' H '/ '  \isog  'Grp'  ( x  :  p ) ']'") : group_scope.

Section PresentationTheory.

Implicit Types gT rT : finGroupType.

Import Presentation.

Lemma isoGrp_hom : forall gT (G : {group gT}) p, G \isog Grp p -> G \homg Grp p.
Proof. move=> gT G p <-; exact: homg_refl. Qed.

Lemma isoGrpP : forall gT (G : {group gT}) p rT (H : {group rT}),
  G \isog Grp p -> reflect (#|H| = #|G| /\ H \homg Grp p) (H \isog G).
Proof.
move=> gT G p rT H isoGp; apply: (iffP idP) => [isoGH | [oH homHp]].
  by rewrite (isog_card isoGH) -isoGp isog_hom.
by rewrite isogEcard isoGp homHp /= oH.
Qed.

Lemma homGrp_trans : forall rT gT (H : {set rT}) (G : {group gT}) p,
  H \homg G -> G \homg Grp p -> H \homg Grp p.
Proof.
move=> rT gT H G p; case/homgP=> h <-{H}; rewrite /hom; move: {p}(p _) => p.
have evalG: forall e t, all (mem G) e -> eval (map h e) t = h (eval e t).
  move=> e t Ge; apply: (@proj2 (eval e t \in G)); elim: t => /=.
  - move=> i; case: (leqP (size e) i) => [le_e_i | lt_i_e].
      by rewrite !nth_default ?size_map ?morph1.
    by rewrite (nth_map 1) // [_ \in G](allP Ge) ?mem_nth.
  - by rewrite morph1.
  - by move=> t [Gt ->]; rewrite groupV morphV.
  - by move=> t [Gt ->] n; rewrite groupX ?morphX.
  - by move=> t1 [Gt1 ->] t2 [Gt2 ->]; rewrite groupM ?morphM.
  - by move=> t1 [Gt1 ->] t2 [Gt2 ->]; rewrite groupJ ?morphJ.
  by move=> t1 [Gt1 ->] t2 [Gt2 ->]; rewrite groupR ?morphR.
have and_relE: forall x1 x2 r, and_rel x1 x2 r = (x1 == x2) && r :> bool.
  by move=> xT x1 x2 [|[yT y1 y2]] //=; rewrite andbT.
have rsatG: forall e f, all (mem G) e -> rel e f NoRel -> rel (map h e) f NoRel.
  move=> e f Ge; have: NoRel -> NoRel by []; move: NoRel {2 4}NoRel.
  elim: f => [x1 x2 | f1 IH1 f2 IH2] r hr IHr; last by apply: IH1; exact: IH2.
  by rewrite !and_relE !evalG //; case/andP; move/eqP->; rewrite eqxx.
set s := env1; set vT := gT : finType in s *.
set s' := env1; set vT' := rT : finType in s' *.
have: forall v, let: Env A e := s v in
  A \subset G -> all (mem G) e /\ exists v', s' v' = Env (h @* A) (map h e).
- move=> x; rewrite /= cycle_subG andbT => Gx; rewrite morphim_cycle //.
  by split; last exists (h x).
elim: p 1%N vT vT' s s' => /= [p IHp | f] n vT vT' s s' Gs.
  apply: IHp => [[v x]] /=; case: (s v) {Gs}(Gs v) => A e /= Gs.
  rewrite mulgen_subG cycle_subG; case/andP=> sAG Gx; rewrite Gx.
  have [//|-> [v' def_v']] := Gs; split=> //; exists (v', h x); rewrite def_v'.
  by congr (Env _ _); rewrite morphim_mulgen ?cycle_subG // morphim_cycle.
case/existsP=> v; case: (s v) {Gs}(Gs v) => /= A e Gs.
rewrite and_relE; case/andP; move/eqP=> defA rel_f.
have{Gs} [|Ge [v' def_v']] := Gs; first by rewrite defA.
apply/existsP; exists v'; rewrite def_v' and_relE defA eqxx /=.
by rewrite -map_rev rsatG ?(eq_all_r (mem_rev e)).
Qed.

Lemma eq_homGrp : forall gT rT (G : {group gT}) (H : {group rT}) p,
  G \isog H -> (G \homg Grp p) = (H \homg Grp p).
Proof.
move=> gT rT G H p; rewrite isogEhom; case/andP=> homGH homHG.
by apply/idP/idP; exact: homGrp_trans.
Qed.

Lemma isoGrp_trans : forall gT rT (G : {group gT}) (H : {group rT}) p,
  G \isog H -> H \isog Grp p -> G \isog Grp p.
Proof.
by move=> gT rT G H p isoGH isoHp kT K; rewrite -isoHp; exact: eq_homgr.
Qed.

Lemma intro_isoGrp : forall gT (G : {group gT}) p,
    G \homg Grp p -> (forall rT (H : {group rT}), H \homg Grp p -> H \homg G) ->
  G \isog Grp p.
Proof.
move=> gT G p homGp freeG rT H.
by apply/idP/idP=> [homHp|]; [exact: homGrp_trans homGp | exact: freeG].
Qed.

End PresentationTheory.

(* A somewhat lighter weight alternative to the formalization above, which
   encodes presentations directly as polymorphic predicates, thus avoiding
   the duplication of the group term syntax, and being extensible
   (e.g., if we added integer exponentiation it would be supported).
     Unfortunately this approach does not work all that well, for several
   reasons:
     - We had to introduce an artificial canonical structure to coerce
       relators to relations, because the natural class of relators,
       FinGroup.sort, should NEVER be a coercion class.
     - We had to introduce an artificial sigma type regrouping the generic
       finGroupType with the first generator of the presentation, to get
       around a limitation of the Notation unparser (it will not recognize
       a Notation that introduces a bound variable when that variable
       appears in the arguments of the notation, unless its name is also
       an argument of the notation; the problem is that the check is done
       on the internal term, which means that the offending occurrences
       could very well be hidden by say implicit arguments; it would be
       better to recognize the notation and simply display any residual
       occurrences of the hidden variable as "_").
     - We would have to introduce a canonical structure that recognizes the
       functoriality of relators and relation in order to prove the homGrp_trans
       lemma above, and this would actually be more work than above.
    Note that we've actually solved the first two issues, and the second one
    could go away if Notation handled bound variables a bit more gracefully;
    but we did give up on the third. A functoriality interface could be
    amortized by using it to infer the continuity of group functors, and more
    generally supporting "proof by isomorphism", but this goes goes beyond
    the scope of this construction.

Module Presentation.

Section Presentation.

Variable gT : finGroupType.
Implicit Type tT : finType.

Inductive type : nat -> Type :=
| Generator n of gT -> type n : type n.+1
| Relation tT of tT & tT      : type 0.

Structure cast n := Cast {sort :> Type; _ : sort -> type n}.

Definition get n (cT : cast n) :=
  let: Wrap c := let: Cast _ c := cT return wrapped (cT -> type n) in Wrap c
  in c.

Definition IdCast n := @Cast n (type n) id.
Definition Rel2 (x y : gT) := Relation x y.
Definition Rel3 (x y z : gT) := Relation (x, y) (z, z).
Definition RelCast := @Cast 0 (FinGroup.sort gT) (Rel2^~ 1).

Definition And cT1 cT2 p1 p2 :=
  match @get 0 cT1 p1, @get 0 cT2 p2 with
  | Relation _ ls1 rs1, Relation _ ls2 rs2 => Relation (ls1, ls2) (rs1, rs2)
  | p1, _ => p1
  end.

Fixpoint rel_type n := if n is n'.+1 then gT -> rel_type n' else (bool : Type).

Fixpoint rel {n} A B p :=
  match p in type n return rel_type n with
  | Generator _ p' => fun x => rel (A <*> <[x]>) B (p' x) 
  | Relation _ ls rs => (A, ls) == (B, rs)
  end.

Fixpoint sat n (tT : finType) : (tT -> rel_type n) -> bool :=
  if n is n'.+1 then
    fun s => sat (fun t => let: (t', x) := t in s t' x)
  else fun s => existsb t, s t.

End Presentation.

Section Hom.

Record pack := Pack {pack_sort :> finGroupType; pack_val :> pack_sort}.
Coercion pack_cast (xT : pack) := pack_val xT : sort (RelCast xT). 

Implicit Type gT : finGroupType.
Variable n : nat.
Implicit Type p : forall xT : pack, type xT n.

Definition hom gT B p := sat (fun x : gT => rel <[x]> B (p (Pack x))).

Definition iso gT (B : {set gT}) p :=
  forall gT' (H : {group gT'}), (H \homg B) = hom H p.

End Hom.

End Presentation.

Canonical Structure Presentation.IdCast.
Canonical Structure Presentation.RelCast.

Notation "x = y" := (Presentation.Rel2 x y) : group_presentation.
Notation "x = y = z" := (Presentation.Rel3 x y z) : group_presentation.
Arguments Scope Presentation.And [_ _ _ group_presentation group_presentation].
Arguments Scope Presentation.get [_ nat_scope _ group_presentation].

Notation "( r1 , r2 , .. , rn )" := 
  (Presentation.And .. (Presentation.And r1 r2) .. rn) : group_presentation.

Notation "x : p" :=
  (Presentation.Generator (fun x => Presentation.get p)) : group_presentation.

Notation "H \homg 'Grp' ( x : p )" :=
  (Presentation.hom H (fun x => Presentation.get p))
  (at level 70, no associativity, x at level 0, p at level 100,
   format "H  \homg  'Grp'  ( x  :  p )") : group_scope.

Notation "H \isog 'Grp' ( x : p )" :=
  (Presentation.iso H (fun x => Presentation.get p))
  (at level 70, no associativity, x at level 0, p at level 100,
   format "H  \isog  'Grp'  ( x  :  p )").

Section PresentationTheory.

Import Presentation.

Implicit Type gT : finGroupType.
Variables (n : nat) (p : forall xT : pack, type xT n).

Lemma isoGrp_hom : forall gT (G : {group gT}), iso G p -> hom G p.
Proof. move=> gT G <-; exact: homg_refl. Qed.

Lemma isoGrpP : forall gT (G : {group gT}) gT' (H : {group gT'}),
  iso G p -> reflect (iso H p) (H \isog G).
Proof.
move=> gT G gT' H isoGp; apply: (iffP idP) => [isoGH kT K | isoHp].
  by rewrite -isoGp (eq_homgr _ isoGH).
by rewrite isogEhom isoGp isoHp !isoGrp_hom.
Qed.

Lemma isoGrp_trans : forall gT rT (G : {group rT}) (H : {group rT}) p,
  G \isog H -> iso H p -> iso G p.
Proof.
by move=> gT rT G H p isoGH isoHp kT K; rewrite -isoHp; exact: eq_homgr.
Qed.

End PresentationTheory.
*)

(* Test presentation syntax
Section TestPresentation.
Variables (rT : finGroupType) (G H : {group rT}) (n : nat) (u v : rT).

Goal G \isog Grp (x : y : (x ^+ n, y ^+ 2, x ^ y = x^-1)).
apply: intro_isoGrp.
  apply/existsP; exists (u, v) => /=.
  rewrite !xpair_eqE /=; apply/and4P=> /=.
  admit.
move=> gT K; case/existsP=> [[x y]] /=; case/eqP.
Abort.

End TestPresentation.
*)

(* Filling (many) gaps in the set of lemmas on partial actions, and on the    *)
(* properties of action constructions.                                        *)
(* Added two properties and a new action construction:                        *)
(*  morph_act to to' f fA <=> the action of to' on the images of f and fA is  *)
(*                   the image of the action of to, i.e., for all x and a we  *)
(*                   have f (to x a) = to' (f x) (fA a). Note that there is   *)
(*                   no mention of the domains of to and to'; if needed, this *)
(*                   predicate should be restricted via the {in ...} notation *)
(*                   and domain conditions should be added.                   *)
(* *** This property should subsume the morph_actJ property defined in gprod. *)
(*  acts_irreducibly to A G <=> A acts irreducibly via the groupAction to on  *)
(*                   the (non-trivial) group G.                               *)
(*  (to \o f)%act == the composite action (with domain f @*^-1 G) of the      *)
(*                   action to : action G rT with f : {morphism D >-> gT},    *)
(*                   via comp_act to f. Here f must be the actual morphism    *)
(*                   object (e.g., coset_morphism H), not the underlying      *)
(*                   function (e.g., coset H). This is also a groupAction     *)
(*                   (denoted (to \o f)%gact) when to is a groupAction.       *)
(* Also added a definition of the restriction operation on permutations (this *)
(* can't go in perm because the domain is a stabiliser), and the relative     *)
(* automorphpism group:                                                       *)
(*  restr_perm S p == if p acts on S, the permutation with support in S that  *)
(*                    coincides with p on S; else the identity. Note that     *)
(*                    restr_perm is a permutation group morphism that maps    *)
(*                    Aut G to Aut S when S is a subgroup of G.               *)
(*      Aut_in A G == the local permutation group 'N_A(G | 'P) / 'C_A(G | 'P) *)
(*                    Usually A is an automorphism group, and then Aut_in A G *)
(*                    is isomorphic to a subgroup of Aut G, specifically      *)
(*                    restr_perm @* A.                                        *)
Section MoreActions.

Definition morph_act (aT aT' : finGroupType) (D : {set aT}) (D' : {set aT'})
                     T T' (to : action D T) (to' : action D' T') f fA :=
  forall x a, f (to x a) = to' (f x) (fA a).

Section RawActions.

Variables (aT : finGroupType) (rT : finType) (D : {set aT}) (to : action D rT).

Lemma astabS : forall S1 S2 : {set rT},
  S1 \subset S2 -> 'C(S2 | to) \subset 'C(S1 | to).
Proof.
move=> S1 S2 sS12; apply/subsetP=> x; rewrite !inE; case/andP=> ->.

exact: subset_trans.
Qed.

Lemma afixS : forall A1 A2 : {set aT},
  A1 \subset A2 -> 'Fix_to(A2) \subset 'Fix_to(A1).
Proof.
move=> A1 A2 sA12; apply/subsetP=> u; rewrite !inE; exact: subset_trans.
Qed.

Lemma astabsC : forall S, 'N(~: S | to) = 'N(S | to). 
Proof.
move=> S; apply/setP=> a; apply/idP/idP=> nSa; rewrite !inE (astabs_dom nSa).
  by rewrite -setCS -preimsetC; apply/subsetP=> x; rewrite inE astabs_act.
by rewrite preimsetC setCS; apply/subsetP=> x; rewrite inE astabs_act.
Qed.

Lemma astabsI : forall S1 S2,
  'N(S1 | to) :&: 'N(S2 | to) \subset 'N(S1 :&: S2 | to). 
Proof.
move=> S1 S2; apply/subsetP=> a; rewrite !inE -!andbA preimsetI.
by case/and4P=> -> nS1a _ nS2a; rewrite setISS.
Qed.

Section ActsSetop.

Variables (A : {set aT}) (S1 S2 : {set rT}).
Hypotheses (act1 : [acts A, on S1 | to]) (act2 : [acts A, on S2 | to]).

Lemma astabU : 'C(S1 :|: S2 | to) = 'C(S1 | to) :&: 'C(S2 | to).
Proof. by apply/setP=> a; rewrite !inE subUset; case: (a \in D). Qed.

Lemma astabsU : 'N(S1 | to) :&: 'N(S2 | to) \subset 'N(S1 :|: S2 | to). 
Proof.
by rewrite -(astabsC S1) -(astabsC S2) -(astabsC (S1 :|: S2)) setCU astabsI.
Qed.

Lemma astabsD : 'N(S1 | to) :&: 'N(S2 | to) \subset 'N(S1 :\: S2 | to). 
Proof. by rewrite setDE -(astabsC S2) astabsI. Qed.

Lemma actsI : [acts A, on S1 :&: S2 | to].
Proof. by apply: subset_trans (astabsI S1 S2); rewrite subsetI act1. Qed.

Lemma actsU : [acts A, on S1 :|: S2 | to].
Proof. by apply: subset_trans astabsU; rewrite subsetI act1. Qed.

Lemma actsD : [acts A, on S1 :\: S2 | to].
Proof. by apply: subset_trans astabsD; rewrite subsetI act1. Qed.

End ActsSetop.

Lemma afixU : forall A B, 'Fix_to(A :|: B) = 'Fix_to(A) :&: 'Fix_to(B).
Proof. by move=> A B; apply/setP=> x; rewrite !inE subUset. Qed.

End RawActions.

Section PartialActions.

Variables (aT : finGroupType) (rT : finType).
Variables (D : {group aT}) (to : action D rT).
Implicit Types A B : {group aT}.
Implicit Type S : {set rT}.

Lemma actXin : forall x a i, a \in D -> to x (a ^+ i) = iter i (to^~ a) x.
Proof.
move=> x a i Da; elim: i => /= [|i <-]; first by rewrite act1.
by rewrite expgSr actMin ?groupX.
Qed.
 
Lemma afix1 : 'Fix_to(1) = setT.
Proof. by apply/setP=> x; rewrite !inE sub1set inE act1 eqxx. Qed.

Lemma afixD1 : forall A, 'Fix_to(A^#) = 'Fix_to(A).
Proof. by move=> A; rewrite -{2}(setD1K (group1 A)) afixU afix1 setTI. Qed.

Lemma afix_gen_in : forall A : {set aT},
  A \subset D -> 'Fix_to(<<A>>) = 'Fix_to(A).
Proof.
move=> A sAD; apply/eqP; rewrite eqEsubset afixS ?sub_gen //=.
by rewrite -astabCin gen_subG ?astabCin.
Qed.

Lemma afix_cycle_in : forall a, a \in D -> 'Fix_to(<[a]>) = 'Fix_to[a].
Proof. by move=> a Da; rewrite afix_gen_in ?sub1set. Qed.

Lemma afixMin : forall A B,
  A \subset D -> B \subset D -> 'Fix_to(A * B) = 'Fix_to(A) :&: 'Fix_to(B).
Proof.
move=> A B sAB sBD; rewrite -afix_gen_in ?mul_subG // genM_mulgen -afixU.
by rewrite afix_gen_in // subUset sAB.
Qed. 

Lemma sub_astab1_in : forall (A : {set aT}) x,
  A \subset D -> (A \subset 'C[x | to]) = (x \in 'Fix_to(A)).
Proof. by move=> A x sAD; rewrite astabCin ?sub1set. Qed.

Lemma orbit_in_transl : forall A x y,
  A \subset D -> y \in orbit to A x -> orbit to A y = orbit to A x.
Proof.
move=> A x y sAD Axy; apply/setP=> z.
by apply/idP/idP; apply: sub_orbit_trans; rewrite // sub_orbit_sym.
Qed.

Lemma card_orbit_in : forall A x,
  A \subset D -> #|orbit to A x| = #|A : 'C_A[x | to]|.
Proof.
move=> A x sAD; rewrite orbit_stabilizer 1?card_in_imset //.
exact: can_in_inj (act_reprK _).
Qed.

Lemma atrans_dvd_index_in : forall A S,
  A \subset D -> [transitive A, on S | to] -> #|S| %| #|A : 'C_A(S | to)|.
Proof.
move=> A S sAD; case/imsetP=> x Sx defS; rewrite {1}defS card_orbit_in //.
by rewrite indexgS // setIS // astabS // sub1set.
Qed.

Lemma atrans_dvd_in : forall A S,
  A \subset D -> [transitive A, on S | to] -> #|S| %| #|A|.
Proof.
move=> A S sAD transA; apply: dvdn_trans (atrans_dvd_index_in sAD transA) _.
exact: dvdn_indexg.
Qed.

Lemma atransPin : forall A S,
     A \subset D -> [transitive A, on S | to] ->
  forall x, x \in S -> orbit to A x = S.
Proof. move=> A S sAD; case/imsetP=> x _ -> y; exact: orbit_in_transl. Qed.

Lemma atransP2in : forall A S,
    A \subset D -> [transitive A, on S | to] ->
  {in S &, forall x y, exists2 a, a \in A & y = to x a}.
Proof.
by move=> A S sAD transA x y; move/(atransPin sAD transA) <-; move/imsetP.
Qed.

Lemma atrans_acts_in : forall A S,
  A \subset D -> [transitive A, on S | to] -> [acts A, on S | to].
Proof.
move=> A S sAD transA; apply/subsetP=> a Aa; rewrite !inE (subsetP sAD) //.
by apply/subsetP=> x; move/(atransPin sAD transA) <-; rewrite inE mem_imset.
Qed.

Lemma subgroup_transitivePin : forall A B S x,
     x \in S -> B \subset A -> A \subset D -> [transitive A, on S | to] ->
  reflect ('C_A[x | to] * B = A) [transitive B, on S | to].
Proof.
move=> A B S x Sx sBA sAD trA; have sBD := subset_trans sBA sAD.
apply: (iffP idP) => [trB | defA].
  rewrite group_modr //; apply/setIidPl; apply/subsetP=> a Aa.
  have Sxa: to x a \in S by rewrite (acts_act (atrans_acts_in sAD trA)).
  have [b Bb xab]:= atransP2in sBD trB Sxa Sx.
  have Da := subsetP sAD a Aa; have Db := subsetP sBD b Bb.
  rewrite -(mulgK b a) mem_mulg ?groupV // !inE groupM //= sub1set inE.
  by rewrite actMin -?xab.
apply/imsetP; exists x => //; apply/setP=> y; rewrite -(atransPin sAD trA Sx).
apply/imsetP/imsetP=> [] [a]; last by exists a; first exact: (subsetP sBA).
rewrite -defA; case/imset2P=> c b; case/setIP=> _ cxc Bb -> ->.
exists b; rewrite ?actMin ?(astab_dom cxc) ?(subsetP sBD) //.
by rewrite (astab_act cxc) ?inE.
Qed.

End PartialActions.

Section TotalActions.

Variables (aT : finGroupType) (rT : finType) (to : {action aT &-> rT}).

(* These lemmas need to work with arbitrary G-sets *)
Lemma sub_astab1 : forall (A : {set aT}) x,
  (A \subset 'C[x | to]) = (x \in 'Fix_to(A)).
Proof. by move=> A x; rewrite sub_astab1_in ?subsetT. Qed.

Lemma astabC : forall (A : {set aT}) S,
  (A \subset 'C(S | to)) = (S \subset 'Fix_to(A)).
Proof. by move=> A S; rewrite astabCin ?subsetT. Qed.

Lemma afix_cycle : forall a, 'Fix_to(<[a]>) = 'Fix_to[a].
Proof. by move=> a; rewrite afix_cycle_in ?inE. Qed.

Lemma afix_gen : forall A : {set aT}, 'Fix_to(<<A>>) = 'Fix_to(A).
Proof. by move=> a; rewrite afix_gen_in ?subsetT. Qed.

Lemma afixM : forall A B : {group aT},
  'Fix_to(A * B) = 'Fix_to(A) :&: 'Fix_to(B).
Proof. by move=> A B; rewrite afixMin ?subsetT. Qed.

(* This is the first part of Aschbacher (5.7) *)
Lemma astab_trans_gcore : forall (G : {group aT}) S u,
  [transitive G, on S | to] -> u \in S -> 'C(S | to) = gcore 'C[u | to] G.
Proof.
move=> G S u transG Su; apply/eqP; rewrite eqEsubset.
rewrite gcore_max ?astabS ?sub1set //=; last first.
  exact: subset_trans (atrans_acts transG) (astab_norm _ _).
apply/subsetP=> x cSx; apply/astabP=> uy.
case/(atransP2 transG Su) => y Gy ->{uy}.
by apply/astab1P; rewrite astab1_act (bigcapP cSx).
Qed.

End TotalActions.

Section SubAction.

Variables (aT : finGroupType) (D : {group aT}).
Variables (rT : finType) (sP : pred rT) (sT : subFinType sP) (to : action D rT).

Lemma astab_subact : forall S : {set sT},
  'C(S | to^?) = subact_dom sP to :&: 'C(val @: S | to).
Proof.
move=> S; apply/setP=> a; rewrite inE in_setI; apply: andb_id2l => sDa.
have [Da _] := setIP sDa; rewrite !inE Da.
apply/subsetP/subsetP=> [cSa u | cSa x Sx]; rewrite !inE.
  case/imsetP=> x Sx -> {u}.
  by have:= cSa x Sx; rewrite inE -val_eqE val_subact sDa.
by have:= cSa _ (mem_imset val Sx); rewrite inE -val_eqE val_subact sDa.
Qed.

Lemma astabs_subact : forall S : {set sT},
  'N(S | to^?) = subact_dom sP to :&: 'N(val @: S | to).
Proof.
move=> S; apply/setP=> a; rewrite inE in_setI; apply: andb_id2l => sDa.
have [Da _] := setIP sDa; rewrite !inE Da.
apply/subsetP/subsetP=> [nSa u | nSa x Sx]; rewrite !inE.
  case/imsetP=> x Sx -> {u}; have:= nSa x Sx; rewrite inE; move/(mem_imset val).
  by rewrite val_subact sDa.
have:= nSa _ (mem_imset val Sx); rewrite inE; case/imsetP=> y Sy def_y.
by rewrite ((_ a =P y) _) // -val_eqE val_subact sDa def_y.
Qed.

Lemma afix_subact : forall A : {set aT},
    A \subset subact_dom sP to ->
  'Fix_(to^?)(A) = val @^-1: 'Fix_to(A) :> {set sT}.
Proof.
move=> A; move/subsetP=> sAD; apply/setP=> u.
rewrite !inE !(sameP setIidPl eqP); congr (_ == A).
apply/setP=> a; rewrite !inE; apply: andb_id2l => Aa.
by rewrite -val_eqE val_subact sAD.
Qed.

End SubAction.

Section ModAction.

Variables (aT : finGroupType) (D : {group aT}) (rT : finType).
Variable to : action D rT.

Section GenMod.

Variables (A : {group aT}) (S : {set rT}).
Hypothesis cSA :  A \subset 'C(S | to).

Let fixSA : S \subset 'Fix_to(D :&: A).
Proof. by rewrite -astabCin ?subsetIl // subIset ?cSA ?orbT. Qed.

Lemma astabs_mod : 'N(S | to %% A) = 'N(S | to) / A.
Proof.
apply/setP=> Aa; apply/idP/morphimP=> [nSa | [a nAa nSa ->]].
  case/morphimP: (astabs_dom nSa) => a nAa Da defAa; exists a => //.
  rewrite !inE Da; apply/subsetP=> x Sx; rewrite !inE.
  by have:= Sx; rewrite -(astabs_act x nSa) defAa /= modactE ?(subsetP fixSA).
have Da := astabs_dom nSa; rewrite !inE mem_quotient //; apply/subsetP=> x Sx.
by rewrite !inE /= modactE ?(astabs_act x nSa) ?(subsetP fixSA).
Qed.

Lemma astab_mod : 'C(S | to %% A) = 'C(S | to) / A.
Proof.
apply/setP=> Aa; apply/idP/morphimP=> [cSa | [a nAa cSa ->]].
  case/morphimP: (astab_dom cSa) => a nAa Da defAa; exists a => //.
  rewrite !inE Da; apply/subsetP=> x Sx; rewrite !inE.
  by rewrite -{2}[x](astab_act cSa) // defAa /= modactE ?(subsetP fixSA).
have Da := astab_dom cSa; rewrite !inE mem_quotient //; apply/subsetP=> x Sx.
by rewrite !inE /= modactE ?(astab_act cSa) ?(subsetP fixSA).
Qed.

End GenMod.

Lemma afix_mod : forall (G A : {group aT}) (S : {set rT}),
    A \subset 'C(S | to) -> G \subset 'N_D(A) ->
  'Fix_(S | to %% A)(G / A) = 'Fix_(S | to)(G).
Proof.
move=> G A S cSA; rewrite subsetI; case/andP=> sGD nAG.
apply/eqP; rewrite eqEsubset !subsetI !subsetIl /= -!astabCin ?quotientS //.
have cfixA: forall F, A \subset 'C(S :&: F | to).
  by move=> F; rewrite (subset_trans cSA) // astabS ?subsetIl.
rewrite andbC astab_mod ?quotientS //=; last by rewrite astabCin ?subsetIr.
by rewrite -(quotientSGK nAG) //= -astab_mod // astabCin ?quotientS ?subsetIr.
Qed.

Lemma modact_faithful : forall (G : {group aT}) (S : {set rT}),
  [faithful G / 'C_G(S | to), on S | to %% 'C_G(S | to)].
Proof.
move=> G S; rewrite /faithful astab_mod ?subsetIr //=.
by rewrite -quotientIG ?subsetIr ?trivg_quotient.
Qed.

End ModAction.

Section GroupActions.

Variables (aT rT : finGroupType) (D : {group aT}) (R : {group rT}).
Variable to : groupAction D R.

Lemma gacentS : forall A1 A2 : {set aT},
  A1 \subset A2 -> 'C_(|to)(A2) \subset 'C_(|to)(A1).
Proof. by move=> A1 A2 sA12; rewrite !(setIS, afixS). Qed.  

Lemma gacentU : forall A B : {set aT},
  'C_(|to)(A :|: B) = 'C_(|to)(A) :&: 'C_(|to)(B).
Proof. by move=> A B; rewrite -setIIr -afixU -setIUr. Qed.

Lemma gacent1 : 'C_(|to)(1) = R.
Proof. by rewrite /gacent (setIidPr (sub1G _)) afix1 setIT. Qed.

Lemma gacentD1 : forall A : {group aT}, 'C_(|to)(A^#) = 'C_(|to)(A).
Proof.
by move=> A; rewrite -{2}(setD1K (group1 A)) gacentU gacent1 gacentIim.
Qed.

Lemma gacent_gen : forall A : {set aT},
  A \subset D -> 'C_(|to)(<<A>>) = 'C_(|to)(A).
Proof.
by move=> A sAD; rewrite /gacent ![D :&: _](setIidPr _) ?gen_subG ?afix_gen_in.
Qed.

Lemma gacent_cycle : forall a, a \in D -> 'C_(|to)(<[a]>) = 'C_(|to)[a].
Proof. by move=> a Da; rewrite gacent_gen ?sub1set. Qed.

Lemma gacentM : forall A B : {group aT},
  A \subset D -> B \subset D -> 'C_(|to)(A * B) = 'C_(|to)(A) :&: 'C_(|to)(B).
Proof.
move=> A B sAD sAB; rewrite -gacentU -gacent_gen ?mul_subG // genM_mulgen.
by rewrite gacent_gen // subUset sAD.
Qed.

Lemma astab1 : 'C(1 | to) = D.
Proof.
by apply/setP=> a; rewrite !(inE, sub1set); apply: andb_idr; move/gact1->.
Qed.

Lemma astabD1 : forall S : {group rT}, 'C(S^# | to) = 'C(S | to).
Proof.
by move=> S; rewrite -{2}(setD1K (group1 S)) astabU astab1 astabIdom.
Qed.

Lemma astabs1 : 'N(1 | to) = D.
Proof. by rewrite astabs_set1 astab1. Qed.

Lemma astabsD1 : forall S : {group rT}, 'N(S^# | to) = 'N(S | to).
Proof.
move=> S; apply/eqP; rewrite eqEsubset andbC -{1}astabsIdom -{1}astabs1 setIC.
by rewrite astabsD -{2}(setD1K (group1 S)) -astabsIdom -{1}astabs1 astabsU.
Qed.

Lemma gacentC : forall (A : {set aT}) (S : {set rT}),
     A \subset D -> S \subset R ->
  (S \subset 'C_(|to)(A)) = (A \subset 'C(S | to)).
Proof.
by move=> A S sAD sSR; rewrite subsetI sSR astabCin // (setIidPr sAD).
Qed.

Lemma astab_gen : forall S : {set rT},
  S \subset R -> 'C(<<S>> | to) = 'C(S | to).
Proof.
move=> S sSR; apply/setP=> a; case Da: (a \in D); last by rewrite !inE Da.
by rewrite -!sub1set -!gacentC ?sub1set ?gen_subG.
Qed.

Lemma astabM : forall S1 S2 : {group rT},
    S1 \subset R -> S2 \subset R ->
  'C(S1 * S2 | to) = 'C(S1 | to) :&: 'C(S2 | to).
Proof.
move=> S1 S2 sS1R sS2R; rewrite -astabU -astab_gen ?mul_subG // genM_mulgen.
by rewrite astab_gen // subUset sS1R.
Qed.

Lemma acts_gen : forall (A : {set aT}) (S : {set rT}),
  S \subset R -> [acts A, on S | to] -> [acts A, on <<S>> | to].
Proof.
move=> A S sSR actsA; apply: {A}subset_trans actsA _.
apply/subsetP=> a nSa; have Da := astabs_dom nSa; rewrite !inE Da.
apply: subset_trans (_ : <<S>> \subset actm to a @*^-1 <<S>>) _.
  rewrite gen_subG subsetI sSR; apply/subsetP=> x Sx.
  by rewrite inE /= actmE ?mem_gen // astabs_act.
by apply/subsetP=> x; rewrite !inE; case/andP=> Rx; rewrite /= actmE.
Qed.

Lemma acts_mulgen : forall (A : {set aT}) (S1 S2 : {set rT}),
  S1 \subset R -> S2 \subset R ->
    [acts A, on S1 | to] -> [acts A, on S2 | to] ->
  [acts A, on S1 <*> S2 | to].
Proof.
by move=> A S1 S2 sS1R sS2R nS1A nS2A; rewrite acts_gen ?actsU // subUset sS1R.
Qed.

Lemma gacent_mod : forall (A G : {group aT}) (S : {group rT}),
    A \subset 'C(S | to) -> G \subset 'N(A) ->
  'C_(S | to %% A)(G / A) = 'C_(S | to)(G).
Proof.
move=> A G S cSA nAG; rewrite -gacentIdom gacentE ?subsetIl // setICA.
have sAD: A \subset D by rewrite (subset_trans cSA) ?subsetIl.
rewrite -quotientGI // afix_mod ?setIS // setICA -gacentIim (setIC R) -setIA.
rewrite -gacentE ?subsetIl // gacentIdom setICA (setIidPr _) //.
by rewrite gacentC // ?(subset_trans cSA) ?astabS ?subsetIl // setICA subsetIl.
Qed.

Definition acts_irreducibly (A : {set aT}) (S : {set rT}) :=
  [min S of G | (G :!=: 1) && [acts A, on G | to]].

End GroupActions.

Section CompAct.

Variables (gT aT : finGroupType) (rT : finType).
Variables (D : {set aT}) (to : action D rT).
Variables (B : {set gT}) (f : {morphism B >-> aT}).

Definition comp_act x e := to x (f e).
Lemma comp_is_action : is_action (f @*^-1 D) comp_act.
Proof.
split=> [e | x e1 e2]; first exact: act_inj.
case/morphpreP=> Be1 Dfe1; case/morphpreP=> Be2 Dfe2.
by rewrite /comp_act morphM ?actMin.
Qed.
Canonical Structure comp_action := Action comp_is_action.

Lemma comp_actE : forall x e, comp_action x e = to x (f e). Proof. by []. Qed.

Lemma afix_comp : forall A : {set gT},
  A \subset B -> 'Fix_comp_action(A) = 'Fix_to(f @* A).
Proof.
move=> A sAB; apply/setP=> x; rewrite !inE /morphim (setIidPr sAB).
apply/subsetP/subsetP=> [cAx fa | cfAx a Aa].
  by case/imsetP=> a Aa ->; move/cAx: Aa; rewrite !inE.
by rewrite inE; move/(_ (f a)): cfAx; rewrite inE mem_imset // => ->.
Qed.

Lemma astab_comp : forall S, 'C(S | comp_action) = f @*^-1 'C(S | to).
Proof. by move=> S; apply/setP=> x; rewrite !inE -andbA. Qed.

Lemma astabs_comp : forall S, 'N(S | comp_action) = f @*^-1 'N(S | to).
Proof. by move=> S; apply/setP=> x; rewrite !inE -andbA. Qed.

End CompAct.

Section GCompAct.

Variables (gT aT rT : finGroupType).
Variables (D : {group aT}) (R : {group rT}) (to : groupAction D R).
Variables (B : {group gT}) (f : {morphism B >-> aT}).

Lemma comp_is_groupAction : is_groupAction R (comp_action to f).
Proof.
move=> a; case/morphpreP=> Ba Dfa; apply: etrans (actperm_Aut to Dfa).
by congr (_ \in Aut R); apply/permP=> x; rewrite !actpermE.
Qed.
Canonical Structure comp_groupAction := GroupAction comp_is_groupAction.

Lemma gacent_comp : forall A, 'C_(|comp_groupAction)(A) = 'C_(|to)(f @* A).
Proof.
move=> A; rewrite /gacent afix_comp ?subIset ?subxx //.
by rewrite -(setIC A) (setIC D) morphim_setIpre.
Qed.

End GCompAct.

Section InternalGroupActions.

Variable gT : finGroupType.
Implicit Type A : {set gT}.
Implicit Types G H U V : {group gT}.

(* This is the second part of Aschbacher (5.7) *)
Lemma astabRs_rcosets : forall H G, 'C(rcosets H G | 'Rs) = gcore H G.
Proof.
move=> H G; have transGH := transRs_rcosets H G.
by rewrite (astab_trans_gcore transGH (orbit_refl _ G _)) astab1Rs.
Qed.

Lemma card_conjugates : forall A G, #|A :^: G| = #|G : 'N_G(A)|.
Proof. by move=> A G; rewrite card_orbit astab1Js. Qed.

Lemma gacentQ : forall A G, 'C_(|'Q)(A) = 'C(A / G).
Proof.
move=> A G; apply/setP=> Gx; case: (cosetP Gx) => x Nx ->{Gx}.
rewrite -sub_cent1 -astab1J astabC sub1set -(quotientInorm G A).
have defD: qact_dom 'J G = 'N(G) by rewrite qact_domE ?subsetT ?astabsJ.
rewrite !(inE, mem_quotient) //= defD setIC.
apply/subsetP/subsetP=> [cAx Ga | cAx a Aa].
  case/morphimP=> a Na Aa ->{Ga}.
  by move/cAx: Aa; rewrite !inE qactE ?defD ?morphJ.
have [_ Na] := setIP Aa; move/implyP: (cAx (coset G a)); rewrite mem_morphim //.
by rewrite !inE qactE ?defD ?morphJ.
Qed.

Lemma acts_irrQ : forall G U V : {group gT},
    G \subset 'N(V) -> V <| U ->
  acts_irreducibly 'Q G (U / V) = minnormal (U / V) (G / V).
Proof.
move=> G U V nVG nsVU; apply/mingroupP/mingroupP; case; case/andP=> ->.
  rewrite astabsQ // subsetI nVG /= => nUG minUV.
  rewrite quotient_norms //; split=> // H; case/andP=> ntH nHG sHU.
  apply: minUV (sHU); rewrite ntH -(cosetpreK H) actsQ //.
  by apply: subset_trans (morphpre_norms _ nHG); rewrite -sub_quotient_pre.
rewrite sub_quotient_pre // => nUG minU; rewrite astabsQ //.
rewrite (subset_trans nUG); last first.
  by rewrite subsetI subsetIl /= -{2}(quotientGK nsVU) morphpre_norm.
split=> // H; case/andP=> ntH nHG sHU.
rewrite -{1}(cosetpreK H) astabsQ ?normal_cosetpre ?subsetI ?nVG //= in nHG.
apply: minU sHU; rewrite ntH; apply: subset_trans (quotientS _ nHG) _.
by rewrite -{2}(cosetpreK H) quotient_norm.
Qed.

End InternalGroupActions.

Section RestrictPerm.

Variables (T : finType) (S : {set T}).

Definition restr_perm := actperm (<[subxx 'N(S | 'P)]>).
Canonical Structure restr_perm_morphism := [morphism of restr_perm].

Lemma restr_perm_on : forall p, perm_on S (restr_perm p).
Proof.
move=> ?; apply/subsetP=> x; apply: contraR => notSx.
by rewrite permE /= /actby (negPf notSx).
Qed.

Lemma restr_permE : {in 'N(S | 'P) & S, forall p, restr_perm p =1 p}.
Proof. by move=> ? x nSp Sx; rewrite /= actpermE actbyE. Qed.

Lemma ker_restr_perm : 'ker restr_perm = 'C(S | 'P).
Proof. by rewrite ker_actperm astab_actby setIT (setIidPr (astab_sub _ _)). Qed.

Lemma im_restr_perm : {in 'N(S | 'P), forall p, restr_perm p @: S = S}.
Proof.
move=> ? nSp /=; rewrite (eq_in_imset (fun _ => restr_permE nSp)).
by rewrite -{2}(astabs_setact nSp); exact: eq_imset.
Qed.

End RestrictPerm.

Section RestrictAut.

Variable gT : finGroupType.

Definition Aut_in A (B : {set gT}) := 'N_A(B | 'P) / 'C_A(B | 'P).

Variables G H : {group gT}.
Hypothesis sHG: H \subset G.

Lemma restr_perm_Aut : restr_perm H @* Aut G \subset Aut H.
Proof.
apply/subsetP=> rp; case/morphimP=> p nHp AutGp ->{rp}.
rewrite inE restr_perm_on; apply/morphicP=> x y Hx Hy /=.
by rewrite !restr_permE ?groupM // -(autmE AutGp) morphM ?(subsetP sHG).
Qed.

Lemma Aut_in_isog : Aut_in (Aut G) H \isog restr_perm H @* Aut G.
Proof.
rewrite /Aut_in -ker_restr_perm kerE -morphpreIdom -morphimIdom -kerE /=.
by rewrite setIA (setIC _ (Aut G)) first_isog_loc ?subsetIr.
Qed.

Lemma Aut_in_fullP :
  reflect (forall h : {morphism H >-> gT}, 'injm h -> h @* H = H ->
             exists g : {morphism G >-> gT},
             [/\ 'injm g, g @* G = G & {in H, g =1 h}])
          (Aut_in (Aut G) H \isog Aut H).
Proof.
rewrite (isog_transl _ Aut_in_isog) /=; set rG := _ @* _.
apply: (iffP idP) => [iso_rG h injh hH| AutHinG].
  have: aut injh hH \in rG; last case/morphimP=> g nHg AutGg def_g.
    suffices ->: rG = Aut H by exact: Aut_aut.
    by apply/eqP; rewrite eqEcard restr_perm_Aut /= (isog_card iso_rG).
  exists (autm_morphism AutGg); rewrite injm_autm im_autm; split=> // x Hx.
  by rewrite -(autE injh hH Hx) def_g actpermE actbyE.
suffices ->: rG = Aut H by exact: isog_refl.
apply/eqP; rewrite eqEsubset restr_perm_Aut /=.
apply/subsetP=> h AutHh; have hH := im_autm AutHh.
have [g [injg gG eq_gh]] := AutHinG _ (injm_autm AutHh) hH.
have [Ng AutGg]: aut injg gG \in 'N(H | 'P) /\ aut injg gG \in Aut G.
  rewrite Aut_aut !inE; split=> //; apply/subsetP=> x Hx.
  by rewrite inE /= /aperm autE ?(subsetP sHG) // -hH eq_gh ?mem_morphim.
apply/morphimP; exists (aut injg gG) => //; apply: (eq_Aut AutHh) => [|x Hx].
  by rewrite (subsetP restr_perm_Aut) // mem_morphim.
by rewrite restr_permE //= /aperm autE ?eq_gh ?(subsetP sHG).
Qed.

End RestrictAut.

(* This is proved by more elementary means in groups.v
Lemma index2_normal : forall gT (G H : {group gT}),
  H \subset G -> #|G : H| = 2 -> H <| G.
Proof.
move=> gT G H sHG indexHG; rewrite /normal sHG; apply/subsetP=> x Gx.
case Hx: (x \in H); first by rewrite inE conjGid.
have defHx: [set H :* x] = rcosets H G :\ gval H.
  apply/eqP; rewrite eqEcard sub1set !inE cards1 -rcosetE mem_orbit //=.
  rewrite (sameP eqP afix1P) -sub_astab1 astab1Rs sub1set Hx /=.
  by rewrite -ltnS -indexHG [#|G : H|](cardsD1 (gval H)) orbit_refl.
rewrite -sub_afixRs_norm -sub_astab1 -astabs_set1 defHx.
by rewrite actsD ?astabs_set1 ?astab1Rs // (subset_trans sHG) ?actsRs_rcosets.
Qed.
*)

End MoreActions.

Notation "to \o f" := (comp_action to f) : action_scope.
Notation "to \o f" := (comp_groupAction to f) : groupAction_scope.

Section MoreZmodp.

Lemma order_Zp1 : forall p', #[Zp1 : 'I_p'.+1] = p'.+1.
Proof. by move=> p'; rewrite orderE -Zp_cycle cardsT card_ord. Qed.

Lemma natr_negZp : forall p' (p := p'.+2) (x : 'I_p), (- x)%:R = - x.
Proof. by move=> p' p x; apply: val_inj; rewrite /= Zp_nat /= modn_mod. Qed.

Lemma unitZpE : forall p x, p > 1 -> GRing.unit (x%:R : 'Z_p) = coprime p x.
Proof.
by move=> p x p_gt1; rewrite /GRing.unit /= val_Zp_nat ?Zp_cast ?coprime_modr.
Qed.

Lemma unitFpE : forall p x, prime p -> GRing.unit (x%:R : 'F_p) = coprime p x.
Proof. by move=> p x p_pr; rewrite pdiv_id // unitZpE // prime_gt1. Qed.

End MoreZmodp.

(* A few tidbits on modular powers, and a new construction: *)
(*   eltm dvd_y_x == the small morphism (with domain <[x]>) mapping x to y,  *)
(*                    given a proof dvd_y_x : #[y] %| #[x].                  *)
Section MoreCyclic.

Section OneGroup.

Variable (gT : finGroupType) (G : {group gT}).
Implicit Type x : gT.

Lemma expgn_znat : forall x k, x \in G -> x ^+ (k%:R : 'Z_(#|G|)) = x ^+ k.
Proof.
move=> x k; case: (eqsVneq G 1) => [-> | ntG Gx].
  by move/set1P->; rewrite !exp1gn.
apply/eqP; rewrite val_Zp_nat ?cardG_gt1 // eq_expg_mod_order.
by rewrite modn_dvdm ?order_dvdG.
Qed.

Lemma expgn_zneg : forall x (k : 'Z_(#|G|)), x \in G -> x ^+ (- k) = x ^- k.
Proof.
move=> x k Gx; apply/eqP; rewrite eq_sym eq_invg_mul -expgn_add.
by rewrite -(expgn_znat _ Gx) natr_add natr_Zp natr_negZp subrr.
Qed.

Lemma nt_gen_prime : forall x, prime #|G| -> x \in G^# -> G :=: <[x]>.
Proof.
move=> x Gpr; case/setD1P; rewrite -cycle_subG -cycle_eq1 => ntX sXG.
apply/eqP; rewrite eqEsubset sXG andbT; apply: contraR ntX.
by move/(prime_TIg Gpr); rewrite (setIidPr sXG) => ->.
Qed.

Lemma dvdn_prime_cyclic : forall p, prime p -> #|G| %| p -> cyclic G.
Proof.
move=> p p_pr pG; case: (eqsVneq G 1) => [-> | ntG]; first exact: cyclic1.
by rewrite prime_cyclic // (prime_nt_dvdP _ p_pr pG) -?trivg_card1.
Qed.

Lemma orderXexp : forall p m n x,
  #[x] = (p ^ n)%N -> #[x ^+ (p ^ m)] = (p ^ (n - m))%N.
Proof.
move=> p m n x ox; case: (leqP n m) => [n_le_m | m_lt_n].
  rewrite -(subnKC n_le_m) -subn_sub subnn expn_add expgn_mul -ox.
  by rewrite expg_order exp1gn order1.
rewrite orderXdiv ox ?dvdn_exp2l ?expn_sub ?(ltnW m_lt_n) //.
by have:= order_gt0 x; rewrite ox expn_gt0 orbC -(ltn_predK m_lt_n).
Qed.

Lemma orderXpfactor : forall p k n x,
  #[x ^+ (p ^ k)] = n -> prime p -> p %| n -> #[x] = (p ^ k * n)%N.
Proof.
move=> p k n x oxp p_pr dv_p_n.
suffices pk_x: p ^ k %| #[x] by rewrite -oxp orderXdiv // mulnC divnK.
rewrite pfactor_dvdn // leqNgt; apply: contraL dv_p_n => lt_x_k.
rewrite -oxp -p'natE // -(subnKC (ltnW lt_x_k)) expn_add expgn_mul.
rewrite (pnat_dvd (orderXdvd _ _)) // -p_part // orderXdiv ?dvdn_part //.
by rewrite -{1}[#[x]](partnC p) // mulKn // part_pnat.
Qed.

Lemma orderXprime : forall p n x,
  #[x ^+ p] = n -> prime p -> p %| n -> #[x] = (p * n)%N.
Proof. by move=> p; exact: (@orderXpfactor p 1). Qed.

Lemma orderXpnat : forall m n x,
  #[x ^+ m] = n -> \pi(n).-nat m -> #[x] = (m * n)%N.
Proof.
move=> m n x oxm n_m; have [m_gt0 _] := andP n_m.
suffices m_x: m %| #[x] by rewrite -oxm orderXdiv // mulnC divnK.
apply/dvdn_partP=> // p; rewrite mem_primes; case/and3P=> p_pr _ p_m.
have n_p: p \in \pi(n) by apply: (pnatP _ _ n_m).
have p_oxm: p %| #[x ^+ (p ^ logn p m)].
  apply: dvdn_trans (orderXdvd _ m`_p^'); rewrite -expgn_mul -p_part ?partnC //.
  by rewrite oxm; rewrite mem_primes in n_p; case/and3P: n_p.
by rewrite (orderXpfactor (erefl _) p_pr p_oxm) p_part // dvdn_mulr.
Qed.

(* A more usable form of cycle_sub_group; will probably cover most uses.  *)
Lemma eq_subG_cyclic : forall H K : {group gT},
  cyclic G -> H \subset G -> K \subset G -> (H :==: K) = (#|H| == #|K|).
Proof.
move=> H K; case/cyclicP=> x -> sHx sKx; apply/eqP/eqP=> [-> //| eqHK].
have def_GHx := cycle_sub_group (cardSg sHx); set GHx := [set _] in def_GHx.
have []: H \in GHx /\ K \in GHx by rewrite -def_GHx !inE sHx sKx eqHK /=.
by do 2!move/set1P->.
Qed.

Lemma cardSg_cyclic : forall H K : {group gT},
  cyclic G -> H \subset G -> K \subset G -> (#|H| %| #|K|) = (H \subset K).
Proof.
move=> H K cycG sHG sKG; apply/idP/idP; last exact: cardSg.
case/cyclicP: (cyclicS sKG cycG) => x defK; rewrite {K}defK in sKG *.
case/dvdnP=> k ox; suffices ->: H :=: <[x ^+ k]> by exact: cycleX.
apply/eqP; rewrite (eq_subG_cyclic cycG) ?(subset_trans (cycleX _ _)) //.
rewrite -orderE orderXdiv orderE ox ?dvdn_mulr ?mulKn //.
by have:= order_gt0 x; rewrite orderE ox; case k.
Qed.

Lemma sub_cyclic_char : forall H : {group gT},
  cyclic G -> (H \char G) = (H \subset G).
Proof.
move=> H; case/cyclicP=> x ->; apply/idP/idP; first by case/andP.
exact: cycle_subgroup_char.
Qed.

End OneGroup.

Section Eltm.

Variables (aT rT : finGroupType) (x : aT) (y : rT).

Definition eltm of #[y] %| #[x] := fun x_i => y ^+ invm (injm_Zpm x) x_i.

Hypothesis dvd_y_x : #[y] %| #[x].

Lemma eltmE : forall i, eltm dvd_y_x (x ^+ i) = y ^+ i.
Proof.
move=> i; apply/eqP; rewrite eq_expg_mod_order.
case: (leqP #[x] 1) => [x_le1 | x_gt1].
  suffices: #[y] %| 1 by rewrite dvdn1; move/eqP->; rewrite !modn1.
  by rewrite (dvdn_trans dvd_y_x) // dvdn1 order_eq1 -cycle_eq1 trivg_card_le1.
rewrite -(expgn_znat i (cycle_id x)) invmE /=; last by rewrite /Zp x_gt1 inE.
by rewrite val_Zp_nat // modn_dvdm.
Qed.

Lemma eltm_id : eltm dvd_y_x x = y. Proof. exact: (eltmE 1). Qed.

Lemma eltmM : {in <[x]> &, {morph eltm dvd_y_x : x_i x_j / x_i * x_j}}.
Proof.
move=> x_i x_j; case/cycleP=> i ->; case/cycleP=> j ->{x_i x_j}.
by apply/eqP; rewrite -expgn_add !eltmE expgn_add.
Qed.
Canonical Structure eltm_morphism := Morphism eltmM.

Lemma im_eltm : eltm dvd_y_x @* <[x]> = <[y]>.
Proof. by rewrite morphim_cycle ?cycle_id //= eltm_id. Qed.

Lemma ker_eltm : 'ker (eltm dvd_y_x) = <[x ^+ #[y] ]>.
Proof.
apply/eqP; rewrite eq_sym eqEcard cycle_subG 3!inE mem_cycle /= eltmE.
rewrite expg_order eqxx (orderE y) -im_eltm card_morphim setIid -orderE.
by rewrite orderXdiv ?dvdn_indexg //= leq_divr ?indexg_gt0 ?LaGrange ?subsetIl.
Qed.

Lemma injm_eltm : 'injm (eltm dvd_y_x) = (#[x] %| #[y]).
Proof. by rewrite ker_eltm subG1 cycle_eq1 -order_dvdn. Qed.

End Eltm.

End MoreCyclic.

(* Complements on semi-direct products, including a new construction:         *)
(*  xsdprodm fHKact == the total morphism on sdprod_of to induced by          *)
(*                     fH : {morphism H >-> rT} and fK : {morphism K >-> rT}, *)
(*                     with to : groupAction K H,                             *)
(*                     given fHKact : morph_act to 'J fH fK.                  *)
Section MoreGprod.

Section MoreSDprod.

Variable gT : finGroupType.
Implicit Types G K H Q : {group gT}.

Lemma sdprod_context : forall G K H, K ><| H = G ->
  [/\ K <| G, H \subset G, K * H = G, H \subset 'N(K) & K :&: H = 1].
Proof.
move=> G K H; case/sdprodP=> _ <- nKH tiKH.
by rewrite /normal mulG_subl mulG_subr mulG_subG normG.
Qed.

Lemma sdprod_Hall : forall G K H, K ><| H = G -> Hall G K = Hall G H.
Proof.
move=> G K H; case/sdprod_context; case/andP=> sKG _ sHG defG _ tiKH.
by rewrite /Hall sKG sHG -!divgS // -defG TI_cardMg // coprime_sym mulKn ?mulnK.
Qed.

Lemma coprime_sdprod_Hall : forall G K H,
  K ><| H = G -> coprime #|K| #|H| = Hall G K.
Proof.
move=> G K H; case/sdprod_context; case/andP=> sKG _ _ defG _ tiKH.
by rewrite /Hall sKG -divgS // -defG TI_cardMg ?mulKn.
Qed.

Lemma sdprod_recl : forall n G K H K1,
  #|G| <= n -> K ><| H = G -> K1 \proper K -> H \subset 'N(K1) ->
  exists G1 : {group gT}, [/\ #|G1| < n, G1 \subset G & K1 ><| H = G1].
Proof.
move=> n G K H K1 leGn; case/sdprodP=> _ defG nKH tiKH ltK1K nK1H.
have tiK1H: K1 :&: H = 1 by apply/trivgP; rewrite -tiKH setSI ?proper_sub.
exists (K1 <*> H)%G; rewrite /= -defG sdprodE // norm_mulgenEr //.
rewrite ?mulSg ?proper_sub ?(leq_trans _ leGn) //=.
by rewrite -defG ?TI_cardMg // ltn_pmul2r ?proper_card.
Qed.

Lemma sdprod_recr : forall n G K H H1,
  #|G| <= n -> K ><| H = G -> H1 \proper H ->
  exists G1 : {group gT}, [/\ #|G1| < n, G1 \subset G & K ><| H1 = G1].
Proof.
move=> n G K H H1 leGn; case/sdprodP=> _ defG nKH tiKH ltH1H.
have [sH1H _] := andP ltH1H; have nKH1 := subset_trans sH1H nKH.
have tiKH1: K :&: H1 = 1 by apply/trivgP; rewrite -tiKH setIS.
exists (K <*> H1)%G; rewrite /= -defG sdprodE // norm_mulgenEr //.
rewrite ?mulgS // ?(leq_trans _ leGn) //=.
by rewrite -defG ?TI_cardMg // ltn_pmul2l ?proper_card.
Qed.

Implicit Type rT : finGroupType.
Implicit Type D : {group gT}.
Lemma injm_sdprod : forall rT D G K H (f : {morphism D >-> rT}),
  'injm f -> G \subset D -> K ><| H = G -> f @* K ><| f @* H = f @* G.
Proof.
move=> rT D G K H f inj_f sGD; case/sdprodP=> _ defG nKH tiKH.
rewrite sdprodE ?morphim_norms //; last by rewrite -injmI // tiKH morphim1.
by rewrite -morphimMl ?(subset_trans _ sGD) -?defG // mulG_subl.
Qed.

Lemma injm_dprod : forall rT D G K H (f : {morphism D >-> rT}),
  'injm f -> G \subset D -> K \x H = G -> f @* K \x f @* H = f @* G.
Proof.
move=> rT D G K H f inj_f sGD; case/dprodP=> _ defG cKH tiKH.
rewrite dprodE ?morphim_cents //; last by rewrite -injmI // tiKH morphim1.
by rewrite -morphimMl ?(subset_trans _ sGD) -?defG // mulG_subl.
Qed.

Lemma morphim_cprod : forall rT D G K H (f : {morphism D >-> rT}),
  G \subset D -> K \* H = G -> f @* K \* f @* H = f @* G.
Proof.
move=> rT D G K H f sGD; case/cprodP=> _ defG cKH.
rewrite cprodE ?morphim_cents //.
by rewrite -morphimMl ?(subset_trans _ sGD) -?defG // mulG_subl.
Qed.

End MoreSDprod.

Lemma im_cprodm : forall (aT rT : finGroupType) (H K G : {group aT}),
            forall (fH : {morphism H >-> rT}) (fK : {morphism K >-> rT}),
            forall (defG : H \* K = G) cfHK (eqfHK : {in H :&: K, fH =1 fK}),
  cprodm defG cfHK eqfHK @* G = fH @* H * fK @* K.
Proof.
move=> aT rT H K G fH fK defG cfHK eqfHK.
by have [_ defHK _] := cprodP defG; rewrite -{2}defHK morphim_cprodm.
Qed.

Section ExtSdprodm.

Variables gT aT rT : finGroupType.
Variables (H : {group gT}) (K : {group aT}) (to : groupAction K H).
Variables (fH : {morphism H >-> rT}) (fK : {morphism K >-> rT}).

Hypothesis actf : {in H & K, morph_act to 'J fH fK}.

Local Notation fsH := (fH \o invm (injm_sdpair1 to)).
Local Notation fsK := (fK \o invm (injm_sdpair2 to)).
Let DgH := sdpair1 to @* H.
Let DgK := sdpair2 to @* K.

Lemma xsdprodm_dom1 : DgH \subset 'dom fsH.
Proof. by rewrite ['dom _]morphpre_invm. Qed.
Local Notation gH := (restrm xsdprodm_dom1 fsH).

Lemma xsdprodm_dom2 : DgK \subset 'dom fsK.
Proof. by rewrite ['dom _]morphpre_invm. Qed.
Local Notation gK := (restrm xsdprodm_dom2 fsK).

Lemma im_sdprodm1 : gH @* DgH = fH @* H.
Proof. by rewrite morphim_restrm setIid morphim_comp im_invm. Qed.

Lemma im_sdprodm2 : gK @* DgK = fK @* K.
Proof. by rewrite morphim_restrm setIid morphim_comp im_invm. Qed.

Lemma xsdprodm_act : {in DgH & DgK, morph_act 'J 'J gH gK}.
Proof.
move=> fh fk; case/morphimP=> h _ Hh ->{fh}; case/morphimP=> k _ Kk ->{fk}.
by rewrite /= -sdpair_act // /restrm /= !invmE ?actf ?gact_stable.
Qed.

Definition xsdprodm := sdprodm (sdprod_sdpair to) xsdprodm_act.
Canonical Structure xsdprod_morphism := [morphism of xsdprodm].

Lemma im_xsdprodm : xsdprodm @* setT = fH @* H * fK @* K.
Proof. by rewrite -im_sdpair morphim_sdprodm // im_sdprodm1 im_sdprodm2. Qed.

Lemma injm_xsdprodm :
  'injm xsdprodm = [&& 'injm fH, 'injm fK & fH @* H :&: fK @* K == 1].
Proof.
rewrite injm_sdprodm im_sdprodm1 im_sdprodm2 morphim_restrm im_sdpair_TI.
rewrite morphim1 !ker_restrm !ker_comp !morphpre_invm !morphimIim.
rewrite !sub_morphim_pre ?subsetIl //.
by rewrite (trivgP (injm_sdpair1 to)) (trivgP (injm_sdpair2 to)).
Qed.

End ExtSdprodm.

End MoreGprod.

(* External center products are defined here.                                 *)
(*   cprod_by isoZ == the finGroupType for the central product of H and K     *)
(*                    with centers identified by the isomorphism gz on 'Z(H); *)
(*                    here isoZ : isom 'Z(H) 'Z(K) gz. Note that the actual   *)
(*                    central product is [set: cprod_by isoZ].                *)
(*    cpairg1 isoZ == the isomorphism from H to cprod_by isoZ, isoZ as above. *)
(*    cpair1g isoZ == the isomorphism from K to cprod_by isoZ, isoZ as above. *)
(*      xcprod H K == the finGroupType for the external central product of H  *)
(*                    and K with identified centers, provided the dynamically *)
(*                    tested condition 'Z(H) \isog 'Z(K) holds.               *)
(*      ncprod H n == the finGroupType for the central product of n copies of *)
(*                    H with their centers identified; [set: ncprod H 0] is   *)
(*                    isomorphic to 'Z(H).                                    *)
(*   Following Aschbacher, we only provide external central products with     *)
(* identified centers, as these are well defined provided the local center    *)
(* isomorphism group of one of the subgroups is full. Nevertheless the        *)
(* entire construction could be carried out under the weaker assumption that  *)
(* gz is an isomorphism between subgroups of 'Z(H) and 'Z(K), and even the    *)
(* uniqueness theorem holds under the weaker assumption that gz map 'Z(H) to  *)
(* a characteristic subgroup of 'Z(K) not isomorphic to any other subgroup of *)
(* 'Z(K), a condition that holds for example when K is cyclic, as in the      *)
(* structure theorem for p-groups of symplectic type.                         *)
Section MoreCenter.

Section CenterFactor.

Variables (gT : finGroupType) (G : {group gT}).
(* A more usable form of center_cyclic_abelian *)
Lemma cyclic_center_factor : cyclic (G / 'Z(G)) -> abelian G.
Proof. move/center_cyclic_abelian->; exact: center_abelian. Qed.

End CenterFactor.

Section MoreInjm.

Variables (aT rT : finGroupType) (D : {group aT}) (f : {morphism D >-> rT}).

Hypothesis injf : 'injm f.

Lemma injm_center : forall G : {group aT},
  G \subset D -> f @* 'Z(G) = 'Z(f @* G).
Proof. by move=> G; exact: injm_subcent. Qed.

End MoreInjm.

Section CprodBy.

Variables gTH gTK : finGroupType.
Variables (H : {group gTH}) (K : {group gTK}) (gz : {morphism 'Z(H) >-> gTK}).

Definition ker_cprod_by of isom 'Z(H) 'Z(K) gz :=
  [set xy | let: (x, y) := xy in (x \in 'Z(H)) && (y == (gz x)^-1)].

Hypothesis isoZ : isom 'Z(H) 'Z(K) gz.
Let kerHK := ker_cprod_by isoZ.

Let injgz : 'injm gz. Proof. by case/isomP: isoZ. Qed.
Let gzZ : gz @* 'Z(H) = 'Z(K). Proof. by case/isomP: isoZ. Qed.
Let gzZchar : gz @* 'Z(H) \char 'Z(K). Proof. by rewrite gzZ char_refl. Qed.
Let sgzZZ : gz @* 'Z(H) \subset 'Z(K) := char_sub gzZchar.
Let sZH := center_sub H.
Let sZK := center_sub K.
Let sgzZG : gz @* 'Z(H) \subset K := subset_trans sgzZZ sZK.

Lemma ker_cprod_by_is_group : group_set kerHK.
Proof.
apply/group_setP; rewrite inE /= group1 morph1 invg1 /=.
split=> // [[x1 y1] [x2 y2]].
rewrite inE /=; case/andP=> Zx1; move/eqP->; have [_ cGx1] := setIP Zx1.
rewrite inE /=; case/andP=> Zx2; move/eqP->; have [Gx2 _] := setIP Zx2.
by rewrite inE /= groupM //= -invMg (centP cGx1) // morphM.
Qed.
Canonical Structure ker_cprod_by_group := Group ker_cprod_by_is_group.

Lemma ker_cprod_by_central : kerHK \subset 'Z(setX H K).
Proof.
rewrite -(center_dprod (setX_dprod H K)) -morphim_pairg1 -morphim_pair1g.
rewrite -!injm_center ?subsetT ?injm_pair1g ?injm_pairg1 //=.
rewrite morphim_pairg1 morphim_pair1g setX_dprod.
apply/subsetP=> [[x y]]; rewrite inE; case/andP=> Zx; move/eqP->.
by rewrite inE /= Zx groupV (subsetP sgzZZ) ?mem_morphim.
Qed.

Definition cprod_by := locked (subFinGroupType [group of setX H K / kerHK]).
Local Notation C := [set: FinGroup.arg_sort (FinGroup.base cprod_by)].

Definition in_cprod : gTH * gTK -> cprod_by.
Proof. unlock cprod_by; exact: (subg _ \o coset kerHK). Defined.

Lemma in_cprodM : {in setX H K &, {morph in_cprod : u v / u * v}}.
Proof.
unlock in_cprod cprod_by => u v Gu Gv /=.
have nkerHKG := normal_norm (sub_center_normal ker_cprod_by_central).
by rewrite -!morphM ?mem_quotient // (subsetP nkerHKG).
Qed.
Canonical Structure in_cprod_morphism := Morphism in_cprodM.

Lemma ker_in_cprod : 'ker in_cprod = kerHK.
Proof.
have: 'ker (subg [group of setX H K / kerHK] \o coset kerHK) = kerHK.
  by rewrite ker_comp ker_subg -kerE ker_coset. 
apply: etrans; rewrite /ker /morphpre /=; unlock in_cprod cprod_by.
by rewrite ['N(kerHK) :&: _]quotientGK ?sub_center_normal ?ker_cprod_by_central.
Qed.

Lemma cpairg1_dom : H \subset 'dom (in_cprod \o @pairg1 gTH gTK).
Proof. by rewrite -sub_morphim_pre ?subsetT // morphim_pairg1 setXS ?sub1G. Qed.

Lemma cpair1g_dom : K \subset 'dom (in_cprod \o @pair1g gTH gTK).
Proof. by rewrite -sub_morphim_pre ?subsetT // morphim_pair1g setXS ?sub1G. Qed.

Definition cpairg1 := tag (restrmP _ cpairg1_dom).
Definition cpair1g := tag (restrmP _ cpair1g_dom).

Local Notation CH := (mfun cpairg1 @* gval H).
Local Notation CK := (mfun cpair1g @* gval K).

Lemma injm_cpairg1 : 'injm cpairg1.
Proof.
rewrite /cpairg1; case: restrmP => _ [_ -> _ _].
rewrite ker_comp ker_in_cprod; apply/subsetP=> x; rewrite 5!inE /=.
by case/and3P=> _ Zx; rewrite inE eq_sym (inv_eq invgK) invg1 morph_injm_eq1.
Qed.
Let injH := injm_cpairg1.

Lemma injm_cpair1g : 'injm cpair1g.
Proof.
rewrite /cpair1g; case: restrmP => _ [_ -> _ _].
rewrite ker_comp ker_in_cprod; apply/subsetP=> y; rewrite !inE /= morph1 invg1.
by case/and3P.
Qed.
Let injK := injm_cpair1g.

Lemma im_cpair_cent : CH \subset 'C(CK).
Proof.
rewrite /cpairg1 /cpair1g; do 2!case: restrmP => _ [_ _ _ -> //].
rewrite !morphim_comp morphim_cents // morphim_pair1g morphim_pairg1.
by case/dprodP: (setX_dprod H K).
Qed.
Hint Resolve im_cpair_cent.

Lemma im_cpair : CH * CK = C.
Proof.
rewrite /cpairg1 /cpair1g; do 2!case: restrmP => _ [_ _ _ -> //].
rewrite !morphim_comp -morphimMl morphim_pairg1 ?setXS ?sub1G //.
rewrite morphim_pair1g setX_prod morphimEdom /=; unlock in_cprod cprod_by.
by rewrite imset_comp imset_coset -morphimEdom subgEdom.
Qed.

Lemma im_cpair_cprod : CH \* CK = C. Proof. by rewrite cprodE ?im_cpair. Qed.

Lemma eq_cpairZ : {in 'Z(H), cpairg1 =1 cpair1g \o gz}.
Proof.
rewrite /cpairg1 /cpair1g => z1 Zz1; set z2 := gz z1.
have Zz2: z2 \in 'Z(K) by rewrite (subsetP sgzZZ) ?mem_morphim.
have [[Gz1 _] [/= Gz2 _]]:= (setIP Zz1, setIP Zz2).
do 2![case: restrmP => f /= [df _ _ _]; rewrite {f}df].
apply/rcoset_kerP; rewrite ?inE ?group1 ?andbT //.
by rewrite ker_in_cprod mem_rcoset inE /= invg1 mulg1 mul1g Zz1 /=.
Qed.

Lemma setI_im_cpair : CH :&: CK = 'Z(CH).
Proof.
apply/eqP; rewrite eqEsubset setIS 1?centsC //=.
rewrite subsetI center_sub -injm_center //.
rewrite (eq_in_morphim _ eq_cpairZ); first by rewrite morphim_comp morphimS.
by rewrite !(setIidPr _) // -sub_morphim_pre.
Qed.

Lemma cpair1g_center : cpair1g @* 'Z(K) = 'Z(C).
Proof.
case/cprodP: (center_cprod im_cpair_cprod) => _ <- _.
by rewrite injm_center // -setI_im_cpair mulSGid //= setIC setIS.
Qed.

(* Uses gzZ. *)
Lemma cpair_center_id : 'Z(CH) = 'Z(CK).
Proof.
rewrite -!injm_center // -gzZ -morphim_comp; apply: eq_in_morphim eq_cpairZ.
by rewrite !(setIidPr _) // -sub_morphim_pre.
Qed.

(* Uses gzZ. *)
Lemma cpairg1_center : cpairg1 @* 'Z(H) = 'Z(C).
Proof. by rewrite -cpair1g_center !injm_center // cpair_center_id. Qed.

Section ExtCprodm.

Variable rT : finGroupType.
Variables (fH : {morphism H >-> rT}) (fK : {morphism K >-> rT}).
Hypothesis cfH2 : fH @* H \subset 'C(fK @* K).
Hypothesis eq_fHK : {in 'Z(H), fH =1 fK \o gz}.

Let gH := ifactm fH injm_cpairg1.
Let gK := ifactm fK injm_cpair1g.

Lemma xcprodm_cent : gH @* CH \subset 'C(gK @* CK).
Proof. by rewrite !im_ifactm. Qed.

Lemma xcprodmI : {in CH :&: CK, gH =1 gK}.
Proof.
rewrite setI_im_cpair -injm_center // => fHx; case/morphimP=> x Gx Zx ->{fHx}.
by rewrite {2}eq_cpairZ //= ?ifactmE ?eq_fHK //= (subsetP sgzZG) ?mem_morphim.
Qed.

Definition xcprodm := cprodm im_cpair_cprod xcprodm_cent xcprodmI.
Canonical Structure ext_cprod_morphism := [morphism of xcprodm].

Lemma xcprodmEl : {in H, forall x, xcprodm (cpairg1 x) = fH x}.
Proof. by move=> x Hx; rewrite /xcprodm cprodmEl ?mem_morphim ?ifactmE. Qed.

Lemma xcprodmEr : {in K, forall y, xcprodm (cpair1g y) = fK y}.
Proof. by move=> y Ky; rewrite /xcprodm cprodmEr ?mem_morphim ?ifactmE. Qed.

Lemma xcprodmE :
  {in H & K, forall x y, xcprodm (cpairg1 x * cpair1g y) = fH x * fK y}.
Proof.
by move=> x y Hx Ky; rewrite /xcprodm cprodmE ?mem_morphim ?ifactmE.
Qed.

Lemma im_xcprodm : xcprodm @* C = fH @* H * fK @* K.
Proof. by rewrite -im_cpair morphim_cprodm // !im_ifactm. Qed.

Lemma im_xcprodml : forall A, xcprodm @* (cpairg1 @* A) = fH @* A.
Proof.
move=> A; rewrite -!(morphimIdom _ A) morphim_cprodml ?morphimS ?subsetIl //.
by rewrite morphim_ifactm ?subsetIl.
Qed.

Lemma im_xcprodmr : forall A, xcprodm @* (cpair1g @* A) = fK @* A.
Proof.
move=> A; rewrite -!(morphimIdom _ A) morphim_cprodmr ?morphimS ?subsetIl //.
by rewrite morphim_ifactm ?subsetIl.
Qed.

Lemma injm_xcprodm : 'injm xcprodm = 'injm fH && 'injm fK.
Proof.
rewrite injm_cprodm !ker_ifactm !subG1 !morphim_injm_eq1 ?subsetIl // -!subG1.
apply: andb_id2l => /= injfH; apply: andb_idr => _.
rewrite !im_ifactm // -(morphimIdom gH) setI_im_cpair -injm_center //.
rewrite morphim_ifactm // eqEsubset subsetI morphimS //=.
rewrite {1}injm_center // setIS 1?centsC //.
rewrite (eq_in_morphim _ eq_fHK); first by rewrite morphim_comp morphimS.
by rewrite !(setIidPr _) // -sub_morphim_pre.
Qed.

End ExtCprodm.

(* Uses gzZchar. *)
Lemma Aut_cprod_full :
    Aut_in (Aut H) 'Z(H) \isog Aut 'Z(H) ->
    Aut_in (Aut K) 'Z(K) \isog Aut 'Z(K) ->
  Aut_in (Aut C) 'Z(C) \isog Aut 'Z(C).
Proof.
move/(Aut_in_fullP sZH)=> AutZinH; move/(Aut_in_fullP sZK)=> AutZinK.
apply/(Aut_in_fullP (center_sub _))=> fz injfz fzZ.
have: 'dom (invm injK \o fz \o cpair1g) = 'Z(K).
  rewrite /dom /= -(morphpreIim fz) (setIidPl _).
    by rewrite injmK //= -cpair1g_center injmK.
  by rewrite fzZ /= -cpair1g_center morphimS.
case/domP=> gzK [def_gzK ker_gzK _ im_gzK].
have{ker_gzK} injgzK: 'injm gzK by rewrite ker_gzK !injm_comp ?injm_invm.
have gzKZ: gzK @* 'Z(K) = 'Z(K).
  rewrite -im_gzK !morphim_comp cpair1g_center fzZ /=.
  by rewrite -cpair1g_center morphim_invm.
have{AutZinK} [gK [injgK gK_K def_gK]] := AutZinK _ injgzK gzKZ.
have: 'dom (cpair1g \o gK) = K by rewrite /dom /= -{3}gK_K injmK.
case/domP=> fK [def_fK ker_fK _ im_fK].
have gKgzZ: gK @* (gz @* 'Z(H)) = gz @* 'Z(H).
  by case/charP: (char_trans gzZchar (center_char K)) => _ ->.
have: 'dom (invm injgz \o gK \o gz) = 'Z(H) by rewrite /dom /= -gKgzZ !injmK.
case/domP=> gzH [def_gzH ker_gzH _ im_gzH].
have{ker_gzH} injgzH: 'injm gzH by rewrite ker_gzH 2?injm_comp // injm_invm.
have{im_gzH} gzHZ: gzH @* 'Z(H) = 'Z(H).
  by rewrite -im_gzH !morphim_comp gKgzZ morphim_invm.
have{AutZinH} [gH [injgH gH_H def_gH]] := AutZinH _ injgzH gzHZ.
have: 'dom (cpairg1 \o gH) = H by rewrite /dom /= -{3}gH_H injmK.
case/domP=> fH [def_fH ker_fH _ im_fH].
have cfH2: fH @* H \subset 'C(fK @* K).
  by rewrite -im_fH -im_fK !morphim_comp gH_H gK_K.
have eq_fHK: {in 'Z(H), fH =1 fK \o gz}.
  move=> z Zz; have ZgHz: gH z \in 'Z(H).
    case/charP: (center_char H)=> _ charZ.
    by rewrite -(charZ gH) ?mem_morphim ?(subsetP sZH).
  rewrite def_fH /= eq_cpairZ // def_fK /= def_gH // def_gzH /= invmK //=.
  by rewrite -gKgzZ !(mem_morphim, subsetP sgzZG).
pose f := xcprodm cfH2 eq_fHK; exists [morphism of f].
rewrite injm_xcprodm ker_fH ker_fK !{1}injm_comp //=.
rewrite im_xcprodm -im_fH -im_fK !{1}morphim_comp gH_H gK_K im_cpair.
split=> // z Zz; rewrite -cpair1g_center in Zz.
have [y Ky Zy -> {z Zz}] := morphimP Zz.
rewrite /f xcprodmEr // def_fK /= def_gK // def_gzK /= invmK //.
rewrite (subsetP (morphimS _ sZK)) // cpair1g_center -{2}fzZ.
by rewrite mem_morphim //= -cpair1g_center mem_morphim.
Qed.

Section Isomorphism.

Let gzZ_lone : forall Y : {group gTK},
  Y \subset 'Z(K) -> gz @* 'Z(H) \isog Y -> gz @* 'Z(H) = Y.
Proof.
move=> Y sYZ isoY; apply/eqP.
by rewrite eq_sym eqEcard (isog_card isoY) gzZ sYZ /=.
Qed.

Variables (rT : finGroupType) (GH GK G : {group rT}).
Hypotheses (defG : GH \* GK = G) (ziGHK : GH :&: GK = 'Z(GH)).
Hypothesis AutZHfull : Aut_in (Aut H) 'Z(H) \isog Aut 'Z(H).
Hypotheses (isoGH : GH \isog H) (isoGK : GK \isog K).

(* Uses gzZ_lone *)
Lemma cprod_by_uniq :
  exists f : {morphism G >-> cprod_by},
    [/\ isom G C f, f @* GH = CH & f @* GK = CK].
Proof.
have [_ defGHK cGKH] := cprodP defG.
have AutZinH := Aut_in_fullP sZH AutZHfull.
have [fH injfH defGH]:= isogP (isog_symr isoGH).
have [fK injfK defGK]:= isogP (isog_symr isoGK).
have sfHZfK: fH @* 'Z(H) \subset fK @* K.
  by rewrite injm_center //= defGH defGK -ziGHK subsetIr.
have gzZ_id: gz @* 'Z(H) = invm injfK @* (fH @* 'Z(H)).
  apply: gzZ_lone => /=.
    rewrite injm_center // defGH -ziGHK sub_morphim_pre /= ?defGK ?subsetIr //.
    by rewrite setIC morphpre_invm injm_center // defGK setIS.
  rewrite -morphim_comp.
  apply: isog_trans (sub_isog _ _); first by rewrite isog_sym sub_isog.
    by rewrite -sub_morphim_pre.
  by rewrite !injm_comp ?injm_invm.
have: 'dom (invm injfH \o fK \o gz) = 'Z(H).
  rewrite /dom /= -(morphpreIdom gz); apply/setIidPl.
  by rewrite -2?sub_morphim_pre // gzZ_id morphim_invmE morphpreK ?morphimS.
case/domP=> gzH [def_gzH ker_gzH _ im_gzH].
have{ker_gzH} injgzH: 'injm gzH by rewrite ker_gzH !injm_comp ?injm_invm.
have{AutZinH} [|gH [injgH gH_H def_gH]] := AutZinH _ injgzH.
  by rewrite -im_gzH !morphim_comp /= gzZ_id !morphim_invmE morphpreK ?injmK.
have: 'dom (fH \o gH) = H by rewrite /dom /= -{3}gH_H injmK.
case/domP=> gfH [def_gfH ker_gfH _ im_gfH].
have{im_gfH} gfH_H: gfH @* H = GH by rewrite -im_gfH morphim_comp gH_H.
have cgfHfK: gfH @* H \subset 'C(fK @* K) by rewrite gfH_H defGK.
have eq_gfHK: {in 'Z(H), gfH =1 fK \o gz}.
  move=> z Zz; rewrite def_gfH /= def_gH //= def_gzH /= invmK //.
  have {Zz}: gz z \in gz @* 'Z(H) by rewrite mem_morphim.
  rewrite gzZ_id morphim_invmE; case/morphpreP=> _.
  exact: (subsetP (morphimS _ _)).
pose f := xcprodm cgfHfK eq_gfHK.
have injf: 'injm f by rewrite injm_xcprodm ker_gfH injm_comp.
have fCH: f @* CH = GH by rewrite im_xcprodml gfH_H.
have fCK: f @* CK = GK by rewrite im_xcprodmr defGK.
have fC: f @* C = G by rewrite im_xcprodm gfH_H defGK defGHK.
have [f' [_ ker_f' _ im_f']] := domP (invm_morphism injf) fC.
exists f'; rewrite -fCH -fCK -!{1}im_f' !{1}morphim_invm ?subsetT //.
by split=> //; apply/isomP; rewrite ker_f' injm_invm -im_f' -fC im_invm.
Qed.

Lemma isog_cprod_by : G \isog C.
Proof. by have [f [isoG _ _]] := cprod_by_uniq; exact: isom_isog isoG. Qed.

End Isomorphism.

End CprodBy.

Section ExtCprod.
Import finfun.

Variables gTH gTK : finGroupType.
Variables (H : {group gTH}) (K : {group gTK}).

Let gt_ b := if b then gTK else gTH.
Local Notation isob := ('Z(H) \isog 'Z(K)) (only parsing).
Let G_ b := if b as b' return {group gt_ b'} then K else H.

Lemma xcprod_subproof :
  {gz : {morphism 'Z(H) >-> gt_ isob} | isom 'Z(H) 'Z(G_ isob) gz}.
Proof.
case: (pickP [pred f : {ffun _} | misom 'Z(H) 'Z(K) f]) => [f isoZ | no_f].
  rewrite (misom_isog isoZ); case/andP: isoZ => fM isoZ.
  by exists [morphism of morphm fM].
move/pred0P: no_f => not_isoZ; rewrite [isob](congr1 negb not_isoZ).
by exists (idm_morphism  _); apply/isomP; rewrite injm_idm im_idm.
Qed.

Definition xcprod := cprod_by (svalP xcprod_subproof).

Inductive xcprod_spec : finGroupType -> Prop :=
  XcprodSpec gz isoZ : xcprod_spec (@cprod_by gTH gTK H K gz isoZ).

Lemma xcprodP : 'Z(H) \isog 'Z(K) -> xcprod_spec xcprod.
Proof. by rewrite /xcprod => isoZ; move: xcprod_subproof; rewrite isoZ. Qed.

Lemma isog_xcprod : forall (rT : finGroupType) (GH GK G : {group rT}),
    Aut_in (Aut H) 'Z(H) \isog Aut 'Z(H) ->
    GH \isog H -> GK \isog K -> GH \* GK = G -> 'Z(GH) = 'Z(GK) ->
  G \isog [set: xcprod].
Proof.
move=> rT GH GK G AutZinH isoGH isoGK defG eqZGHK.
have [_ _ cGKH] := cprodP defG.
have [|gz isoZ] := xcprodP.
  have [[fH injfH <-] [fK injfK <-]] := (isogP isoGH, isogP isoGK).
  rewrite -!injm_center -?(isog_transl _ (sub_isog _ _)) ?center_sub //=.
  by rewrite eqZGHK sub_isog ?center_sub.
rewrite (isog_cprod_by _ defG) //.
by apply/eqP; rewrite eqEsubset setIS 1?centsC // subsetI {2}eqZGHK !center_sub.
Qed.

End ExtCprod.

Section IterCprod.

Variables (gT : finGroupType) (G : {group gT}).

Definition ncprod := locked (fix loop n : finGroupType :=
  if n is n'.+1 then xcprod G [set: loop n']
  else [finGroupType of subg_of 'Z(G)]).

Local Notation G_ n := [set: gsort (ncprod n)].

Lemma ncprod0 : G_ 0 \isog 'Z(G).
Proof. by unlock ncprod; rewrite isog_sym isog_subg. Qed.

Lemma center_ncprod0 : 'Z(G_ 0) = G_ 0.
Proof.
by rewrite center_abelian_id // (isog_abelian ncprod0) center_abelian.
Qed.

Lemma center_ncprod : forall n, 'Z(G_ n) \isog 'Z(G).
Proof.
elim=> [|n]; first by rewrite center_ncprod0 ncprod0.
unlock ncprod; move/isog_symr; case/xcprodP => gz isoZ.
by rewrite -cpairg1_center isog_sym sub_isog ?center_sub ?injm_cpairg1.
Qed.

Lemma ncprodS : forall n, xcprod_spec G [set: ncprod n] (ncprod n.+1).
Proof.
by move=> n; have:= xcprodP (isog_symr (center_ncprod n)); unlock ncprod.
Qed.

Lemma ncprod1 : G_ 1 \isog G.
Proof.
case: ncprodS => gz isoZ; rewrite isog_sym /= -im_cpair.
rewrite mulGSid /=; first by rewrite sub_isog ?injm_cpairg1.
rewrite -{3}center_ncprod0 injm_center ?injm_cpair1g //.
by rewrite -cpair_center_id center_sub.
Qed.

Lemma Aut_ncprod_full : forall n,
    Aut_in (Aut G) 'Z(G) \isog Aut 'Z(G) ->
  Aut_in (Aut (G_ n)) 'Z(G_ n) \isog Aut 'Z(G_ n).
Proof.
move=> n AutZinG; elim: n => [|n IHn].
  by rewrite center_ncprod0; apply/Aut_in_fullP=> // g injg gG0; exists g.
by case: ncprodS => gz isoZ; apply: Aut_cprod_full.
Qed.

End IterCprod.

End MoreCenter.

Section MorePgroups.

Variables (gT : finGroupType) (pi : nat_pred) (p : nat).

Lemma coprime_mulpG_Hall : forall G K R : {group gT},
    K * R = G -> pi.-group K -> pi^'.-group R ->
  pi.-Hall(G) K /\ pi^'.-Hall(G) R.
Proof.
move=> G K R defG piK pi'R; apply/andP.
rewrite /pHall piK -!divgS /= -defG ?mulG_subl ?mulg_subr //= pnatNK.
by rewrite coprime_cardMg ?(pnat_coprime piK) // mulKn ?mulnK //; exact/and3P.
Qed.

Lemma coprime_mulGp_Hall : forall G K R : {group gT},
    K * R = G -> pi^'.-group K -> pi.-group R ->
  pi^'.-Hall(G) K /\ pi.-Hall(G) R.
Proof.
move=> G K R defG pi'K piR; apply/andP; rewrite andbC; apply/andP.
by apply: coprime_mulpG_Hall => //; rewrite -(comm_group_setP _) defG ?groupP.
Qed.

Lemma coprime_p'group : forall K R : {group gT},
  coprime #|K| #|R| -> p.-group R -> R :!=: 1 -> p^'.-group K.
Proof.
move=> K R coKR pR ntR; have [p_pr _ [e oK]] := pgroup_pdiv pR ntR.
by rewrite oK coprime_sym coprime_pexpl // prime_coprime // -p'natE in coKR.
Qed.

Lemma pSylow_Hall_Sylow : forall G H P : {group gT},
  pi.-Hall(G) H -> p \in pi -> p.-Sylow(H) P -> p.-Sylow(G) P.
Proof.
move=> G H P hallH pi_p sylP; have [sHG piH _] := and3P hallH.
rewrite pHallE (subset_trans (pHall_sub sylP) sHG) /=.
by rewrite (card_Hall sylP) (card_Hall hallH) partn_part // => q; move/eqnP->.
Qed.

End MorePgroups.

Section MoreSylow.

Variable gT : finGroupType.

(* !! Hall lemma in the std library are too weak: subnormal does not require *)
(* solvability!.                                                             *)
Lemma Hall_subnormal : forall pi (G K H : {group gT}),
  K <| G -> pi.-Hall(G) H -> pi.-Hall(K) (H :&: K).
Proof.
move=> pi G K H nsKG hallH; have [sHG piH _] := and3P hallH.
have [sHK_H sHK_K] := (subsetIl H K, subsetIr H K).
rewrite pHallE sHK_K /= -(part_pnat_id (pgroupS sHK_H piH)); apply/eqP.
rewrite (widen_partn _ (subset_leq_card sHK_K)); apply: eq_bigr => p pi_p.
have [P sylP] := Sylow_exists p H.
have sylPK := pSylow_normalI nsKG (pSylow_Hall_Sylow hallH pi_p sylP).
rewrite -!p_part -(card_Hall sylPK); symmetry; apply: card_Hall.
by rewrite (pHall_subl _ sHK_K) //= setIC setSI ?(pHall_sub sylP).
Qed.

(* This should subsume the mulg_center_coprime_cent lemma recently added to *)
(* center.v.                                                                *)
Lemma coprime_mulG_setI_norm : forall H G K R : {group gT},
    K * R = G -> G \subset 'N(H) -> coprime #|K| #|R| ->
  (K :&: H) * (R :&: H) = G :&: H.
Proof.
move=> H G K R defG nHG coKR; apply/eqP; rewrite eqEcard mulG_subG /= -defG.
rewrite !setSI ?mulG_subl ?mulG_subr //=.
rewrite coprime_cardMg ?(coKR, coprimeSg (subsetIl _ _), coprime_sym) //=.
pose pi := \pi(#|K|); have piK: pi.-group K by exact: pnat_pi.
have pi'R: pi^'.-group R by rewrite /pgroup -coprime_pi'.
have [hallK hallR] := coprime_mulpG_Hall defG piK pi'R.
have nsHG: H :&: G <| G by rewrite /normal subsetIr normsI ?normG.
rewrite -!(setIC H) defG -(partnC pi (cardG_gt0 _)).
rewrite -(card_Hall (Hall_subnormal nsHG hallR)) /= setICA.
rewrite -(card_Hall (Hall_subnormal nsHG hallK)) /= setICA.
by rewrite -defG (setIidPl (mulG_subl _ _)) (setIidPl (mulG_subr _ _)).  
Qed.

End MoreSylow.

Section MoreAbelian.

Implicit Type gT : finGroupType.

Lemma rank_cycle : forall gT (x : gT), 'r(<[x]>) = (x != 1).
Proof.
move=> gT x; case: eqP => [->|]; first by rewrite cycle1 rank1.
move/eqP=> ntx; apply/eqP; rewrite eqn_leq rank_gt0 cycle_eq1 ntx andbT.
by rewrite -grank_abelian ?cycle_abelian //= -(cards1 x) grank_min.
Qed.

Lemma abelian_rank1_cyclic :  forall gT (G : {group gT}),
  abelian G -> cyclic G = ('r(G) <= 1).
Proof.
move=> gT G cGG; have [b defG atypG] := abelian_structure cGG.
apply/idP/idP; first by case/cyclicP=> x ->; rewrite rank_cycle leq_b1.
rewrite -size_abelian_type // -{}atypG -{}defG unlock.
by case: b => [|x []] //= _; rewrite ?cyclic1 // dprodg1 cycle_cyclic.
Qed.

Lemma exponent2_abelem : forall gT (G : {group gT}),
  exponent G %| 2 -> 2.-abelem G.
Proof.
move=> gT G; move/exponentP=> expG; apply/abelemP=> //; split=> //.
apply/centsP=> x Gx y Gy; apply: (mulIg x); apply: (mulgI y).
by rewrite -!mulgA !(mulgA y) -!(expgS _ 1) !expG ?mulg1 ?groupM.
Qed.

Lemma prime_abelem : forall gT p (X : {group gT}),
  prime p -> #|X| = p -> p.-abelem X.
Proof.
move=> gT p X p_pr oX; rewrite /abelem -oX exponent_dvdn.
by rewrite /pgroup cyclic_abelian ?prime_cyclic ?oX ?pnat_id.
Qed.

Lemma p_rankElem_max : forall gT p (G : {group gT}),
  'E_p^('r_p(G))(G) \subset 'E*_p(G).
Proof.
move=> gT p G; apply/subsetP=> E; case/setIdP=> EpE dimE.
apply/pmaxElemP; split=> // F EpF sEF; apply/eqP.
have pF: p.-group F by case/pElemP: EpF => _; case/and3P.
have pE: p.-group E by case/pElemP: EpE => _; case/and3P.
rewrite eq_sym eqEcard sEF dvdn_leq //.
rewrite -(part_pnat_id pE) -(part_pnat_id pF) !p_part dvdn_exp2l //.
by rewrite (eqP dimE) logn_le_p_rank.
Qed.

Lemma extend_cyclic_Mho : forall gT (G : {group gT}) (p : nat) x,
    p.-group G -> x \in G -> 'Mho^1(G) = <[x ^+ p]> -> 
  forall k, k > 0 -> 'Mho^k(G) = <[x ^+ (p ^ k)]>.
Proof.
move=> gT G p x pG Gx defG1 [//|k _]; have pX := mem_p_elt pG Gx.
apply/eqP; rewrite eqEsubset cycle_subG (Mho_p_elt _ Gx pX) andbT.
rewrite (MhoE _ pG) gen_subG; apply/subsetP=> ypk; case/imsetP=> y Gy ->{ypk}.
have: y ^+ p \in <[x ^+ p]> by rewrite -defG1 (Mho_p_elt 1 _ (mem_p_elt pG Gy)).
rewrite !expnS /= !expgn_mul; case/cycleP=> j ->.
by rewrite -!expgn_mul mulnCA mulnC expgn_mul mem_cycle.
Qed.

Lemma Ohm_normal : forall n gT (G : {group gT}), 'Ohm_n(G) <| G.
Proof. by move=> n; exact: gfunc.bgFunc_normal. Qed.

Lemma Mho_normal : forall n gT (G : {group gT}), 'Mho^n(G) <| G.
Proof. by move=> n; exact: gfunc.bgFunc_normal. Qed.

End MoreAbelian.

(* A few more elementary properties of extraspecial groups. *)
Section MoreMaximal.

Variables gT rT : finGroupType.
Implicit Type p : nat.
Implicit Types E D F G H K U V W : {group gT}.

(* This is Aschbacher (23.2) *)
Lemma Phi_min : forall p G H,
  p.-group G -> G \subset 'N(H) -> p.-abelem (G / H) -> 'Phi(G) \subset H.
Proof.
move=> p G H pG nHG; rewrite -trivg_Phi ?quotient_pgroup // -subG1 /=.
by rewrite -(quotient_Phi pG) ?quotient_sub1 // (subset_trans (Phi_sub _)).
Qed.

Lemma PhiS : forall p G H, p.-group H -> G \subset H -> 'Phi(G) \subset 'Phi(H).
Proof.
move=> p G H pH sGH; rewrite (Phi_mulgen pH) (Phi_mulgen (pgroupS sGH pH)).
by rewrite genS // setUSS ?dergS ?MhoS.
Qed.

(* This should replace Phi_mulg *)
Lemma Phi_cprod :  forall p G H K,
  p.-group G -> H \* K = G -> 'Phi(H) \* 'Phi(K) = 'Phi(G).
Proof.
move=> p G H K pG; case/cprodP=> _ defG cHK.
rewrite cprodE; last by do 2!rewrite (subset_trans (Phi_sub _)) // centsC.
have [sHG sKG]: H \subset G /\ K \subset G.
  by apply/andP; rewrite -mulG_subG defG.
by rewrite -(Phi_mulg (pgroupS sHG pG) (pgroupS sKG pG)) ?defG.
Qed.

Lemma exponent_special : forall p G,
  p.-group G -> special G -> exponent G %| p ^ 2.
Proof.
move=> p G pG spG; have [defPhi _] := spG.
have [_ _ expZ] := and3P (center_special_abelem pG spG).
apply/exponentP=> x Gx; rewrite expgn_mul (exponentP expZ) // -defPhi.
by rewrite (Phi_mulgen pG) mem_gen // inE orbC (Mho_p_elt 1) ?(mem_p_elt pG).
Qed.

Lemma p3group_extraspecial : forall p G,
  p.-group G -> ~~ abelian G -> logn p #|G| <= 3 -> extraspecial G.
Proof.
move=> p G pG not_cGG; have [sZG nZG] := andP (center_normal G).
have ntG: G :!=: 1 by apply: contra not_cGG; move/eqP->; exact: abelian1.
have ntZ: 'Z(G) != 1 by rewrite -(setIidPr sZG) nil_meet_Z ?(pgroup_nil pG).
have [p_pr _ [n oG]] := pgroup_pdiv pG ntG; rewrite oG pfactorK //.
have [_ _ [m oZ]] := pgroup_pdiv (pgroupS sZG pG) ntZ.
have lt_m1_n: m.+1 < n.
  suffices: 1 < logn p #|(G / 'Z(G))|.
    rewrite card_quotient // -divgS // logn_div ?cardSg //.
    by rewrite oG oZ !pfactorK // -ltn_add_sub addn1. 
  rewrite ltnNge; apply: contra not_cGG => cycGs; apply: cyclic_center_factor.
  rewrite (dvdn_prime_cyclic p_pr) // -(part_pnat_id (quotient_pgroup _ pG)).
  by rewrite p_part (dvdn_exp2l _ cycGs).
rewrite -{lt_m1_n}(subnKC lt_m1_n) !addSn !ltnS leqn0 in oG *.
case: m => // in oZ oG *; move/eqP=> n2; rewrite {n}n2 in oG.
exact: card_p3group_extraspecial oZ.
Qed.

Lemma cprod_extraspecial : forall p G H K,
    p.-group G -> H \* K = G -> H :&: K = 'Z(H) ->
  extraspecial H -> extraspecial K -> extraspecial G.
Proof.
move=> p G H K pG defG tiHK [[PhiH defH'] ZH_pr] [[PhiK defK'] ZK_pr].
have [_ defHK cHK]:= cprodP defG.
have sZH_K: 'Z(H) \subset 'Z(K).
  by rewrite subsetI -{1}tiHK subsetIr subIset ?cHK.
have{sZH_K} defZH: 'Z(H) = 'Z(K).
  by apply/eqP; rewrite eqEcard sZH_K leq_eqVlt eq_sym -dvdn_prime2 ?cardSg.
have defZ: 'Z(G) = 'Z(K).
  by case/cprodP: (center_cprod defG) => /= _ <- _; rewrite defZH mulGid.
split; first split; rewrite defZ //.
  by case/cprodP: (Phi_cprod pG defG) => _ <- _; rewrite PhiH PhiK defZH mulGid.
by case/cprodP: (der_cprod 1 defG) => _ <- _; rewrite defH' defK' defZH mulGid.
Qed.

(* This is derived from center_aut_extraspecial, which may be the wrong way   *)
(* around -- perhaps we should be using the fine structure theorems instead.  *)
(* However this would force us to defer this result to extremal.v.            *)
Lemma Aut_extraspecial_full : forall p G,
  p.-group G -> extraspecial G -> Aut_in (Aut G) 'Z(G) \isog Aut 'Z(G).
Proof.
move=> p G pG esG; have p_pr := extraspecial_prime pG esG.
apply/(Aut_in_fullP (center_sub _)) => /= g injg gZ.
have oZ := card_center_extraspecial pG esG.
have [z defZ]: exists z, 'Z(G) = <[z]>.
  by apply/cyclicP; rewrite prime_cyclic ?oZ.
have Zz: z \in 'Z(G) by rewrite defZ cycle_id.
have genZgz: generator <[z]> (g z).
  by rewrite /generator -morphim_cycle // -defZ gZ.
have [i def_gz]: exists i, g z = z ^+ i.
  by apply/cycleP; rewrite ((<[z]> =P _) genZgz) ?cycle_id.
rewrite def_gz generator_coprime orderE -defZ oZ coprime_sym in genZgz.
have [f AutGf eq_fi]:= center_aut_extraspecial pG esG genZgz.
exists (autm_morphism AutGf); rewrite injm_autm im_autm.
split=> // y Zy; rewrite /= autmE eq_fi //.
have [j ->]: exists j, y = z^+ j by apply/cycleP; rewrite -defZ.
by rewrite expgnC -def_gz morphX.
Qed.

Lemma extraspecial_non_abelian : forall G, extraspecial G -> ~~ abelian G.
Proof.
move=> G [[_ defG'] oZ]; rewrite /abelian (sameP commG1P eqP).
by rewrite -derg1 defG' -cardG_gt1 prime_gt1.
Qed.

Lemma exponent_2extraspecial : forall G,
  2.-group G -> extraspecial G -> exponent G = 4.
Proof.
move=> G p2G esG; have [spG _] := esG.
case/dvdn_pfactor: (exponent_special p2G spG) => // k.
rewrite leq_eqVlt ltnS; case/predU1P=> [-> // | lek1] expG.
case/negP: (extraspecial_non_abelian esG).
by rewrite (@abelem_abelian _ 2) ?exponent2_abelem // expG pfactor_dvdn.
Qed.

(* Lemmas bundling Aschbacher (23.10) with (19.1), (19.2), (19.12) and (20.8) *)
Section ExtraspecialFormspace.

Variables (p : nat) (G : {group gT}).
Hypotheses (pG : p.-group G) (esG : extraspecial G).

Let p_pr := extraspecial_prime pG esG.
Let oZ := card_center_extraspecial pG esG.
Let p_gt1 := prime_gt1 p_pr.
Let p_gt0 := prime_gt0 p_pr.

(* This is the tranposition of the hyperplane dimension theorem (Aschbacher   *)
(* (19.1)) to subgroups of an extraspecial group.                             *)
(* This should supercede cent1_extraspecial_maximal.                          *)
Lemma subcent1_extraspecial_maximal : forall U x,
  U \subset G -> x \in G :\: 'C(U) -> maximal 'C_U[x] U.
Proof.
move=> U x sUG; case/setDP=> Gx not_cUx.
apply/maxgroupP; split=> [|H ltHU sCxH].
  by rewrite /proper subsetIl subsetI subxx sub_cent1.
case/andP: ltHU => sHU not_sHU; have sHG := subset_trans sHU sUG.
apply/eqP; rewrite eqEsubset sCxH subsetI sHU /= andbT.
apply: contraR not_sHU => not_sHCx.
have maxCx: maximal 'C_G[x] G.
  rewrite cent1_extraspecial_maximal //; apply: contra not_cUx.
  by rewrite inE Gx; exact: subsetP (centS sUG) _.
have nsCx := p_maximal_normal pG maxCx.
rewrite -(setIidPl sUG) -(mulg_normal_maximal nsCx maxCx sHG) ?subsetI ?sHG //.
by rewrite -group_modr //= setIA (setIidPl sUG) mul_subG.
Qed.

(* This is the tranposition of the orthogonal subspace dimension theorem      *)
(* (Aschbacher (19.2)) to subgroups of an extraspecial group.                 *)
Lemma card_subcent_extraspecial : forall U,
  U \subset G -> #|'C_G(U)| = (#|'Z(G) :&: U| * #|G : U|)%N.
Proof.
move=> U sUG; rewrite setIAC (setIidPr sUG).
elim: {U}_.+1 {-2}U (ltnSn #|U|) sUG => // m IHm U leUm sUG.
have [cUG | not_cUG]:= orP (orbN (G \subset 'C(U))).
  by rewrite !(setIidPl _) ?LaGrange // centsC.
have{not_cUG} [x Gx not_cUx] := subsetPn not_cUG.
pose W := 'C_U[x]; have sCW_G: 'C_G(W) \subset G := subsetIl G _.
have maxW: maximal W U by rewrite subcent1_extraspecial_maximal // inE not_cUx.
have nsWU: W <| U := p_maximal_normal (pgroupS sUG pG) maxW.
have ltWU: W \proper U by exact: maxgroupp maxW.
have [sWU [u Uu notWu]] := properP _ _ ltWU; have sWG := subset_trans sWU sUG.
have defU: W * <[u]> = U by rewrite (mulg_normal_maximal nsWU) ?cycle_subG.
have iCW_CU: #|'C_G(W) : 'C_G(U)| = p.
  rewrite -defU centM cent_cycle setIA /=; rewrite inE Uu cent1C in notWu.
  apply: p_maximal_index (pgroupS sCW_G pG) _.
  apply: subcent1_extraspecial_maximal sCW_G _.
  rewrite inE andbC (subsetP sUG) //= -sub_cent1.
  by apply/subsetPn; exists x; rewrite // inE Gx -sub_cent1 subsetIr.
apply/eqP; rewrite -(eqn_pmul2r p_gt0) -{1}iCW_CU LaGrange ?setIS ?centS //.
rewrite IHm ?(leq_trans (proper_card ltWU)) // -setIA -mulnA.
rewrite -(LaGrange_index sUG sWU) (p_maximal_index (pgroupS sUG pG)) //=.
by rewrite -cent_set1 (setIidPr (centS _)) ?sub1set.
Qed.

(* This is the tranposition of the proof that a singular vector is contained  *)
(* in a hyperbolic plane (Aschbacher (19.12)) to subgroups of an extraspecial *)
(* group.                                                                     *)
(*   The general strucuture theorem for extraspecial groups should be derived *)
(* from this.                                                                 *)
Lemma split1_extraspecial : forall x,
    x \in G :\: 'Z(G) ->
  {E : {group gT} & {R : {group gT} |
    [/\ #|E| = (p ^ 3)%N /\ #|R| = #|G| %/ p ^ 2,
        E \* R = G /\ E :&: R = 'Z(E),
        'Z(E) = 'Z(G) /\ 'Z(R) = 'Z(G),
        extraspecial E /\ x \in E
      & R :=: 'Z(G) \/ extraspecial R]}}.
Proof.
move=> x; case/setDP=> Gx notZx; rewrite inE Gx /= in notZx.
have [[defPhiG defG'] prZ] := esG.
have maxCx: maximal 'C_G[x] G.
  by rewrite subcent1_extraspecial_maximal // inE notZx.
pose y := repr (G :\: 'C[x]).
have [Gy not_cxy]: y \in G /\ y \notin 'C[x].
  move/maxgroupp: maxCx; case/properP=> _ [t Gt not_cyt].
  by apply/setDP; apply: (mem_repr t); rewrite !inE Gt andbT in not_cyt *.
pose E := <[x]> <*> <[y]>; pose R := 'C_G(E).
exists [group of E]; exists [group of R] => /=.
have sEG: E \subset G by rewrite mulgen_subG !cycle_subG Gx.
have [Ex Ey]: x \in E /\ y \in E by rewrite !mem_gen // inE cycle_id ?orbT.
have sZE: 'Z(G) \subset E.
  rewrite (('Z(G) =P E^`(1)) _) ?der_sub // eqEsubset -{2}defG' dergS // andbT. 
  apply: contraR not_cxy => /= not_sZE'.
  rewrite (sameP cent1P commgP) -in_set1 -[[set 1]](prime_TIg prZ not_sZE').
  by rewrite /= -defG' inE !mem_commg.
have ziER: E :&: R = 'Z(E) by rewrite setIA (setIidPl sEG).
have cRE: E \subset 'C(R) by rewrite centsC subsetIr.
have iCxG: #|G : 'C_G[x]| = p by exact: p_maximal_index.
have maxR: maximal R 'C_G[x].
  rewrite /R cent_mulgen !cent_cycle setIA.
  rewrite subcent1_extraspecial_maximal ?subsetIl // inE Gy andbT -sub_cent1.
  by apply/subsetPn; exists x; rewrite 1?cent1C // inE Gx cent1id.
have sRCx: R \subset 'C_G[x] by rewrite -cent_cycle setIS ?centS ?mulgen_subl.
have sCxG: 'C_G[x] \subset G by rewrite subsetIl.
have sRG: R \subset G by rewrite subsetIl.
have iRCx: #|'C_G[x] : R| = p by rewrite (p_maximal_index (pgroupS sCxG pG)).
have defG: E * R = G.
  rewrite -cent_mulgenEl //= -/R mulgenC mulgenA.
  have cGx_x: <[x]> \subset 'C_G[x] by rewrite cycle_subG inE Gx cent1id.
  have nsRcx := p_maximal_normal (pgroupS sCxG pG) maxR.
  rewrite (norm_mulgenEr (subset_trans cGx_x (normal_norm nsRcx))).
  rewrite (mulg_normal_maximal nsRcx) //=; last first.
    by rewrite cent_mulgen !cent_cycle cycle_subG !in_setI Gx cent1id cent1C.
  have nsCxG := p_maximal_normal pG maxCx.
  have syG: <[y]> \subset G by rewrite cycle_subG.
  rewrite (norm_mulgenEr (subset_trans syG (normal_norm nsCxG))).
  by rewrite (mulg_normal_maximal nsCxG) //= cycle_subG inE Gy.
have defZR: 'Z(R) = 'Z(G) by rewrite -['Z(R)]setIA -centM defG.
have defZE: 'Z(E) = 'Z(G).
  by rewrite -defG -center_prod ?mulGSid //= -ziER subsetI center_sub defZR sZE.
have [[//|n] _ oG] := card_extraspecial pG esG.
have oR: #|R| = (p ^ n.*2.+1)%N.
  apply/eqP; rewrite -(setIidPr sRCx) -divg_index iRCx /=.
  by rewrite -(setIidPr sCxG) -divg_index iCxG /= oG !mulKn.
have oE: #|E| = (p ^ 3)%N.
  apply/eqP; rewrite -(@eqn_pmul2r #|R|) ?cardG_gt0 // mul_cardG defG ziER.
  by rewrite defZE oZ oG oR -expnSr -expn_add.
rewrite cprodE // oR oG -expn_sub //; split=> //.
  by split=> //; apply: card_p3group_extraspecial _ oE _; rewrite // defZE.
have [n0 | n_gt0] := posnP n; [left | right; split; last by rewrite defZR].
  by apply/eqP; rewrite eq_sym eqEcard oZ oR -defZR center_sub n0 leqnn.
have pR: p.-group R := pgroupS sRG pG.
have defR': R^`(1) = 'Z(R).
  have [R'1 | ntR'] := eqVneq R^`(1) 1.
    move/eqP: oZ; rewrite -defZR center_abelian_id ?oR; last exact/commG1P.
    by rewrite (eqn_exp2l _ 1) // -(prednK n_gt0). 
  apply/eqP; rewrite defZR eqEcard -{1}defG' dergS //= oZ.
  have pR': p.-group R^`(1) := pgroupS (der_sub 1 _) pR.
  by have [_ _ [k ->]]:= pgroup_pdiv pR' ntR'; rewrite (leq_exp2l 1).
split=> //; apply/eqP; rewrite eqEsubset {1}defZR -defPhiG -defR' (PhiS pG) //.
by rewrite (Phi_mulgen pR) mulgen_subl.
Qed.

(* This is the tranposition of the proof that the dimension of any maximal    *)
(* totally singular subspace is equal to the Witt index (Aschbacher (20.8)),  *)
(* to subgroups of an extraspecial group (in a slightly more general form,    *)
(* since we allow for p != 2).                                                *)
(*   Note that Aschbacher derives this from the Witt lemma, which we avoid.   *)
Lemma pmaxElem_extraspecial : 'E*_p(G) = 'E_p^('r_p(G))(G).
Proof.
have sZmax: {in 'E*_p(G), forall E, 'Z(G) \subset E}.
  move=> E maxE; have [EpE _]:= pmaxElemP maxE; have [sEG _]:= pElemP EpE.
  rewrite in_pmaxElemE // in maxE.
  rewrite -(@Ohm1_id _ p 'Z(G)) ?prime_abelem ?oZ //.
  rewrite (OhmE 1 (pgroupS (center_sub G) pG)).
  by rewrite gen_subG -(eqP maxE) !setIdE setSI // setIS // centS.
suffices card_max: {in 'E*_p(G) &, forall E F, #|E| <= #|F| }.
  have EprGmax: 'E_p^('r_p(G))(G) \subset 'E*_p(G) := p_rankElem_max p G.
  have [E EprE]:= p_rank_witness p G; have maxE := subsetP EprGmax E EprE.
  apply/eqP; rewrite eqEsubset EprGmax andbT; apply/subsetP=> F maxF.
  rewrite inE; have [-> _]:= pmaxElemP maxF; have [_ _ <-]:= pnElemP EprE.
  by apply/eqP; congr (logn p _); apply/eqP; rewrite eqn_leq !card_max.
move=> E F maxE maxF; set U := E :&: F.
have [sUE sUF]: U \subset E /\ U \subset F by apply/andP; rewrite -subsetI.
have sZU: 'Z(G) \subset U by rewrite subsetI !sZmax.
have [EpE _]:= pmaxElemP maxE; have{EpE} [sEG abelE] := pElemP EpE.
have [EpF _]:= pmaxElemP maxF; have{EpF} [sFG abelF] := pElemP EpF.
have [V] := abelem_split_dprod abelE sUE; case/dprodP=> _ defE cVU tiUV.
have [W] := abelem_split_dprod abelF sUF; case/dprodP=> _ defF _ tiUW.
have [sVE sWF]: V \subset E /\ W \subset F by rewrite -defE -defF !mulG_subr.
have [sVG sWG] := (subset_trans sVE sEG, subset_trans sWF sFG).
rewrite -defE -defF !TI_cardMg // leq_pmul2l ?cardG_gt0 //.
rewrite -(leq_pmul2r (cardG_gt0 'C_G(W))) mul_cardG.
rewrite card_subcent_extraspecial // mulnCA LaGrange // mulnC.
rewrite leq_mul ?subset_leq_card //; last by rewrite mul_subG ?subsetIl.
apply: subset_trans (sub1G _); rewrite -tiUV !subsetI subsetIl subIset ?sVE //=.
rewrite in_pmaxElemE // in maxF; rewrite -(eqP maxF) setIdE -defF centM.
rewrite -!setIA -(setICA 'C(W)) setIC setIA setIS // subsetI centsC cVU.
have [_ _ eVp]:= and3P (abelemS sVE abelE).
by apply/subsetP=> x Vx; rewrite inE (exponentP eVp).
Qed.

End ExtraspecialFormspace.

Lemma injm_extraspecial : forall D G (f : {morphism D >-> rT}),
  'injm f -> G \subset D -> extraspecial G -> extraspecial (f @* G).
Proof.
move=> D G f injf sGD [[PhiGid G'id] ZG_pr].
split; last by rewrite -injm_center // card_injm // subIset ?sGD.
by split; rewrite -!gfunc.bgFunc_ascont //= ?PhiGid ?G'id.
Qed.

Lemma isog_extraspecial : forall G (R : {group rT}),
  G \isog R -> extraspecial G -> extraspecial R.
Proof. by move=> G R; case/isogP=> f injf <-; exact: injm_extraspecial. Qed.

End MoreMaximal.

(* New file for definition and properties of extremal p-groups. *)
(* We define canonical representatives for the group classes that cover the   *)
(* extremal p-groups (non-abelian p-groups with a cyclic maximal subgroup):   *)
(* 'Mod_m == the modular group of order m, for m = p ^ n, p prime and n >= 3. *)
(*   'D_m == the dihedral group of order m, for m = 2n >= 4.                  *)
(*   'Q_m == the generalized quaternion group of order m, for q = 2 ^ n >= 8. *)
(*  'SD_m == the semi-dihedral group of order m, for m = 2 ^ n >= 16.         *)
(* In each case the notation is defined in the %type, %g and %G scopes, where *)
(* it denotes a finGroupType, a full gset and the full group for that type.   *)
(* However each notation is only meaningful under the given conditions, in    *)
(* 'D_m is only an extremal group for m = 2 ^ n >= 8, and 'D_8 = 'Mod_8 (they *)
(* are, in fact, beta-convertible).                                           *)
(*   We also define                                                           *)
(*  extremal_generators G p n (x, y) <=> G has order p ^ n, x in G has order  *)
(*            p ^ n.-1, and y is in G \ <[x]>: thus <[x]> has index p in G,   *)
(*            so if p is prime, <[x]> is maximal in G, G is generated by x    *)
(*            and y, and G is extremal or abelian.                            *)
(*  extremal_class G == the class of extremal groups G belongs to: one of     *)
(*           ModularGroup, Dihedral, Quaternion, SemiDihedral or NotExtremal. *)
(*  extremal2 G <=> extremal_class G is one of Dihedral, Quaternion, or       *)
(*           SemiDihedral; this allows 'D_4 and 'D_8, but excludes 'Mod_(2^n) *)
(*           for n > 3.                                                       *)
(*  modular_group_generators p n (x, y) <=> y has order p and acts on x via   *)
(*           x ^ y = x ^+ (p ^ n.-2).+1. This is the complement to            *)
(*          extremal_generators G p n (x, y) for modular groups.              *)
(* We provide cardinality, presentation, generator and structure theorems for *)
(* each class of extremal group. The extremal_generators predicate is used to *)
(* supply structure theorems with all the required data about G; this is      *)
(* completed by an isomorphism assumption (e.g., G \isog 'D_(2 ^ n)), and     *)
(* sometimes other properties (e.g., #[y] == 2 in the semidihedral case). The *)
(* generators assumption can be deduced generically from the isomorphism      *)
(* assumption, or it can be proved manually for a specific choice of x and y. *)
(*  The extremal_class function is used to formulate synthetic theorems that  *)
(* cover several classes of extremal groups (e.g., Aschbacher ex. 8.3).       *)
(*   We develop the fine structure theorems for extraspecial groups; these    *)
(* make use of the following notation:                                        *)
(*    p^{1+2} == if p is prime, an extraspecial group of order p^3 that has   *)
(*               exponent p or 4, and p-rank 2: thus p^{1+2} is isomorphic to *)
(*               'D_8 if p - 2, and NOT isomorphic to 'Mod_(p^3) if p is odd. *)
(*  p^{1+2*n} == the central product of n copies of p^{1+2}, thus of order    *)
(*               p^(1+2*n) if p is a prime, and, when n > 0, a representative *)
(*               of the (unique) isomorphism class of extraspecial groups of  *)
(*               order p^(1+2*n), of exponent p or 4, and p-rank n+1.         *)
(*       'D^n == an alternative (and preferred) notation for 2^{1+2*n}, which *)
(*               is isomorphic to the central product of n copies od 'D_8.    *)
(*     'D^n*Q == the central product of 'D^n with 'Q_8, thus isomorphic to    *)
(*               all extraspecial groups of order 2 ^ (2 * n + 3) that are    *)
(*               not isomorphic to 'D^n.+1 (or, equivalently, have 2-rank n). *)
(* As above, these notations are defined in the %type, %g and %G scopes.      *)

Reserved Notation "''Mod_' m" (at level 8, m at level 2, format "''Mod_' m").
Reserved Notation "''D_' m" (at level 8, m at level 2, format "''D_' m").
Reserved Notation "''SD_' m" (at level 8, m at level 2, format "''SD_' m").
Reserved Notation "''Q_' m" (at level 8, m at level 2, format "''Q_' m").

Reserved Notation "p ^{1+2}" (at level 2, format "p ^{1+2}").
Reserved Notation "p ^{1+2* n }"
  (at level 2, n at level 2, format "p ^{1+2* n }").
Reserved Notation "''D^' n" (at level 8, n at level 2, format "''D^' n").
Reserved Notation "''D^' n * 'Q'"
  (at level 8, n at level 2, format "''D^' n * 'Q'").

Module Extremal.

Section Construction.

Variables q p e : nat.
(* Construct the semi-direct product of 'Z_q by 'Z_p with 1%R ^ 1%R = e%R,    *)
(* if possible, i.e., if p, q > 1 and there is s \in Aut 'Z_p such that       *)
(* #[s] %| p  and s 1%R = 1%R ^+ e.                                           *)

Let a : 'Z_p := Zp1.
Let b : 'Z_q := Zp1.
Local Notation B := <[b]>.

Definition aut_of :=
  odflt 1 [pick s \in Aut B | [&& p > 1, #[s] %| p & s b == b ^+ e]].

Lemma aut_dvdn : #[aut_of] %| #[a].
Proof.
rewrite order_Zp1 /aut_of; case: pickP => [s | _]; last by rewrite order1.
by case/and4P=> _ p_gt1 p_s _; rewrite Zp_cast.
Qed.

Definition act_morphism := eltm_morphism aut_dvdn.

Definition base_act := ('A_B \o act_morphism)%gact.

Lemma act_dom : <[a]> \subset act_dom base_act.
Proof.
rewrite cycle_subG 2!inE cycle_id /= eltm_id /aut_of.
by case: pickP => [op | _] /=; [case/andP | rewrite group1].
Qed.

Definition gact := (base_act \ act_dom)%gact.
Definition gtype := locked (sdprod_groupType gact).

Hypotheses (p_gt1 : p > 1) (q_gt1 : q > 1).

Lemma card : #|[set: gtype]| = (p * q)%N.
Proof.
unlock gtype; rewrite -(sdprod_card (sdprod_sdpair _)).
rewrite !card_injm ?injm_sdpair1 ?injm_sdpair2 //.
by rewrite mulnC -!orderE !order_Zp1 !Zp_cast.
Qed.

Lemma Grp : (exists s, [/\ s \in Aut B, #[s] %| p & s b = b ^+ e]) ->
  [set: gtype] \isog Grp (x : y : (x ^+ q, y ^+ p, x ^ y = x ^+ e)).
Proof.
unlock gtype; case=> s [AutBs dvd_s_p sb].
have memB: _ \in B by move=> c; rewrite -Zp_cycle inE.
have Aa: a \in <[a]> by rewrite !cycle_id.
have [oa ob]: #[a] = p /\ #[b] = q by rewrite !order_Zp1 !Zp_cast.
have def_s: aut_of = s.
  rewrite /aut_of; case: pickP => /= [t | ]; last first.
    by move/(_ s); case/and4P; rewrite sb.
  case/and4P=> AutBt _ _ tb; apply: (eq_Aut AutBt) => // b_i.
  case/cycleP=> i ->; rewrite -(autmE AutBt) -(autmE AutBs) !morphX //=.
  by rewrite !autmE // sb (eqP tb).
apply: intro_isoGrp => [|gT G].
  apply/existsP; exists (sdpair1 _ b, sdpair2 _ a); rewrite /= !xpair_eqE.
  rewrite -!morphim_cycle ?norm_mulgenEr ?im_sdpair ?im_sdpair_norm ?eqxx //=.
  rewrite -!order_dvdn !order_injm ?injm_sdpair1 ?injm_sdpair2 // oa ob !dvdnn.
  by rewrite -sdpair_act // [act _ _ _]apermE /= eltm_id -morphX // -sb -def_s.
case/existsP=> [[x y]] /=; case/eqP=> defG xq1 yp1 xy.
have fxP: #[x] %| #[b] by rewrite order_dvdn ob xq1.
have fyP: #[y] %| #[a] by rewrite order_dvdn oa yp1.
have fP: {in <[b]> & <[a]>, morph_act gact 'J (eltm fxP) (eltm fyP)}.
  move=> bj ai; case/cycleP=> j ->{bj}; case/cycleP=> i ->{ai}.
  rewrite /= !eltmE def_s gactX ?groupX // conjXg morphX //=; congr (_ ^+ j).
  rewrite /autact /= apermE; elim: i {j} => /= [|i IHi].
    by rewrite perm1 eltm_id conjg1.
  rewrite !expgS permM sb -(autmE (groupX i AutBs)) !morphX //= {}IHi.
  by rewrite -conjXg -xy -conjgM.
apply/homgP; exists (xsdprod_morphism fP).
rewrite im_xsdprodm !morphim_cycle //= !eltm_id -norm_mulgenEr //.
by rewrite cycle_norm_cycle xy mem_cycle.
Qed.

End Construction.

End Extremal.

Section SpecializeExtremals.

Import Extremal.

Variable m : nat.
Let p := pdiv m.
Let q := m %/ p.

Definition modular_gtype := gtype q p (q %/ p).+1.
Definition dihedral_gtype := gtype q 2 q.-1.
Definition semidihedral_gtype := gtype q 2 (q %/ p).-1.
Definition quaternion_kernel :=
  <<[set u | u ^+ 2 == 1] :\: [set u ^+ 2 | u <- [set: gtype q 4 q.-1]]>>.
Definition quaternion_gtype := locked (coset_groupType quaternion_kernel).

End SpecializeExtremals.

Notation "''Mod_' m" := (modular_gtype m) : type_scope.
Notation "''Mod_' m" := [set: gsort 'Mod_m] : group_scope.
Notation "''Mod_' m" := [set: gsort 'Mod_m]%G : subgroup_scope.

Notation "''D_' m" := (dihedral_gtype m) : type_scope.
Notation "''D_' m" := [set: gsort 'D_m] : group_scope.
Notation "''D_' m" := [set: gsort 'D_m]%G : subgroup_scope.

Notation "''SD_' m" := (semidihedral_gtype m) : type_scope.
Notation "''SD_' m" := [set: gsort 'SD_m] : group_scope.
Notation "''SD_' m" := [set: gsort 'SD_m]%G : subgroup_scope.

Notation "''Q_' m" := (quaternion_gtype m) : type_scope.
Notation "''Q_' m" := [set: gsort 'Q_m] : group_scope.
Notation "''Q_' m" := [set: gsort 'Q_m]%G : subgroup_scope.

Module Pextraspecial.

Section Construction.

Variable p : nat.

Definition act ij (k : 'Z_p) := let: (i, j) := ij in (i + k * j, j).
Lemma actP : is_action [set: 'Z_p] act.
Proof.
apply: is_total_action=> [] [i j] => [|k1 k2] /=; first by rewrite mul0r addr0.
by rewrite mulr_addl addrA.
Qed.
Canonical Structure action := Action actP.

Lemma gactP : is_groupAction [set: 'Z_p * 'Z_p] action.
Proof.
move=> k _ /=; rewrite inE.
apply/andP; split; first by apply/subsetP=> ij _; rewrite inE.
apply/morphicP=> /= [[i1 j1] [i2 j2] _ _].
by rewrite !permE /= mulr_addr -addrA (addrCA i2) (addrA i1).
Qed.
Canonical Structure groupAction := GroupAction gactP.

Definition gtype := locked (sdprod_groupType groupAction).

Definition ngtype := ncprod [set: gtype].

End Construction.

Definition ngtypeQ n := xcprod [set: ngtype 2 n] 'Q_8.

End Pextraspecial.

Notation "p ^{1+2}" := (Pextraspecial.gtype p) : type_scope.
Notation "p ^{1+2}" := [set: gsort p^{1+2}] : group_scope.
Notation "p ^{1+2}" := [set: gsort p^{1+2}]%G : subgroup_scope.

Notation "p ^{1+2* n }" := (Pextraspecial.ngtype p n) : type_scope.
Notation "p ^{1+2* n }" := [set: gsort p^{1+2*n}] : group_scope.
Notation "p ^{1+2* n }" := [set: gsort p^{1+2*n}]%G : subgroup_scope.

Notation "''D^' n" := (Pextraspecial.ngtype 2 n) : type_scope.
Notation "''D^' n" := [set: gsort 'D^n] : group_scope.
Notation "''D^' n" := [set: gsort 'D^n]%G : subgroup_scope.

Notation "''D^' n * 'Q'" := (Pextraspecial.ngtypeQ n) : type_scope.
Notation "''D^' n * 'Q'" := [set: gsort 'D^n*Q] : group_scope.
Notation "''D^' n * 'Q'" := [set: gsort 'D^n*Q]%G : subgroup_scope.

Section ExtremalTheory.

Implicit Type gT : finGroupType.
Implicit Types p q m n : nat.

(* This is Aschbacher (23.3), with the isomorphism made explicit, and a       *)
(* slightly reworked case analysis on the prime and exponent; in particular   *)
(* the inverting involution is available for all non-trivial p-cycles.        *)
Lemma cyclic_pgroup_Aut_structure : forall gT p (G : {group gT}),
    p.-group G -> cyclic G -> G :!=: 1 ->
  let q := #|G| in let n := (logn p q).-1 in
  let A := Aut G in let P := 'O_p(A) in let F := 'O_p^'(A) in
  exists m : {perm gT} -> 'Z_q,
  [/\ [/\ {in A & G, forall a x, x ^+ m a = a x},
          m 1 = 1%R /\ {in A &, {morph m : a b / a * b >-> (a * b)%R}},
          {in A &, injective m} /\ [image m of A] =i GRing.unit,
          forall k, {in A, {morph m : a / a ^+ k >-> (a ^+ k)%R}}
        & {in A, {morph m : a / a^-1 >-> (a^-1)%R}}],
      [/\ abelian A, cyclic F, #|F| = p.-1 & [faithful F, on 'Ohm_1(G) | 'A_G]]
    & if n == 0%N then A = F else
      exists t, [/\ t \in A, #[t] = 2, m t = - 1%R
      & if odd p then
        [/\ cyclic A /\ cyclic P,
           exists s, [/\ s \in A, #[s] = (p ^ n)%N, m s = p.+1%:R & P = <[s]>]
         & exists s0, [/\ s0 \in A, #[s0] = p, m s0 = (p ^ n).+1%:R
                        & 'Ohm_1(P) = <[s0]>]]
   else if n == 1%N then A = <[t]>
   else exists s,
        [/\ s \in A, #[s] = (2 ^ n.-1)%N, m s = 5%:R, <[s]> \x <[t]> = A
      & exists s0, [/\ s0 \in A, #[s0] = 2, m s0 = (2 ^ n).+1%:R,
                       m (s0 * t) = (2 ^ n).-1%:R & 'Ohm_1(<[s]>) = <[s0]>]]]].
Proof.
move=> gT p G pG cycG ntG q n0 A P F.
have [x0 defG] := cyclicP _ cycG; have Gx0: x0 \in G by rewrite defG cycle_id.
have [p_pr p_dvd_G [n oG]] := pgroup_pdiv pG ntG.
rewrite {1}/q oG pfactorK //= in n0 *; rewrite {}/n0.
have [p_gt1 min_p] := primeP p_pr; have p_gt0 := ltnW p_gt1.
have q_gt1: q > 1 by rewrite cardG_gt1.
have cAA: abelian A := Aut_cyclic_abelian cycG; have nilA := abelian_nil cAA.
have oA: #|A| = (p.-1 * p ^ n)%N by rewrite card_Aut_cyclic // oG phi_pfactor.
have [sylP hallF]: p.-Sylow(A) P /\ p^'.-Hall(A) F.
  by rewrite !nilpotent_pcore_Hall.
have [defPF tiPF]: P * F = A /\ P :&: F = 1.
  by case/dprodP: (nilpotent_pcoreC p nilA).
have oP: #|P| = (p ^ n)%N.
  by rewrite (card_Hall sylP) oA p_part logn_gauss ?coprimenP ?pfactorK.
have oF: #|F| = p.-1.
  apply/eqP; rewrite -(@eqn_pmul2l #|P|) ?cardG_gt0 // -TI_cardMg // defPF.
  by rewrite oA oP mulnC.
have [m' [inj_m' defA def_m']]: exists m' : {morphism units_Zp q >-> {perm gT}},
  [/\ 'injm m', m' @* setT = A & {in G, forall x u, m' u x = x ^+ val u}].
- rewrite /A /q defG; exists (Zp_unit_morphism x0).
  by have [->]:= isomP (Zp_unit_isom x0); split=> // y Gy u; rewrite permE Gy.
pose m (a : {perm gT}) : 'Z_q := val (invm inj_m' a).
have{def_m'} def_m: {in A & G, forall a x, x ^+ m a = a x}.
  by move=> a x Aa Gx /=; rewrite -{2}[a](invmK inj_m') ?defA ?def_m'.
have m1: m 1 = 1%R by rewrite /m morph1.
have mM: {in A &, {morph m : a b / a * b >-> (a * b)%R}}.
  by move=> a b Aa Ab; rewrite /m morphM ?defA.
have mX: forall k, {in A, {morph m : a / a ^+ k >-> (a ^+ k)%R}}.
  by elim=> // k IHk a Aa; rewrite expgS exprS mM ?groupX ?IHk.
have inj_m: {in A &, injective m}.
  apply: can_in_inj (fun u => m' (insubd (1 : {unit 'Z_q}) u)) _ => a Aa.
  by rewrite valKd invmK ?defA.
have{defA} im_m: [image m of A] =i GRing.unit.
  move=> u; apply/imageP/idP=> [[a Aa ->]| Uu]; first exact: valP.
  exists (m' (Sub u Uu)) => /=; first by rewrite -defA mem_morphim ?inE.
  by rewrite /m invmE ?inE.
have mV: {in A, {morph m : a / a^-1 >-> (a^-1)%R}}.
  move=> a Aa /=; rewrite -div1r; apply: canRL (mulrK (valP _)) _.
  by rewrite -mM ?groupV ?mulVg.
have inv_m: forall u : 'Z_q, coprime q u -> {a | a \in A & m a = u}.
  move=> u; rewrite -?unitZpE // natr_Zp -[_ u]im_m => m_u.
  by exists (iinv m_u); [exact: mem_iinv | rewrite f_iinv].
have [cycF ffulF]: cyclic F /\ [faithful F, on 'Ohm_1(G) | 'A_G].
  have Um0: forall a, GRing.unit ((m a)%:R : 'F_p).
    move=> a; have: GRing.unit (m a) by exact: valP.
    by rewrite -{1}[m a]natr_Zp unitFpE ?unitZpE // {1}/q oG coprime_pexpl.
  pose fm0 a : {unit 'F_p} := Sub _ (Um0 a).
  have natZqp: forall u, (u%:R : 'Z_q)%:R = u %:R :> 'F_p.
    by move=> u; rewrite val_Zp_nat // -Fp_nat_mod // modn_dvdm ?Fp_nat_mod.
  have m0M: {in A &, {morph fm0 : a b / a * b}}.
    move=> a b Aa Ab; apply: val_inj; rewrite /= -natr_mul mM //.
    by rewrite -[(_ * _)%R]Zp_nat natZqp.
  pose m0 : {morphism A >-> {unit 'F_p}} := Morphism m0M.
  have im_m0: m0 @* A = [set: {unit 'F_p}].
    apply/setP=> [[/= u Uu]]; rewrite in_setT morphimEdom; apply/imsetP.
    have [|a Aa m_a] := inv_m u%:R.
      by rewrite {1}[q]oG coprime_pexpl // -unitFpE // natZqp natr_Zp.
    by exists a => //; apply: val_inj; rewrite /= m_a natZqp natr_Zp.
  have [x1 defG1]: exists x1, 'Ohm_1(G) = <[x1]>.
    by apply/cyclicP; exact: cyclicS (Ohm_sub _ _) cycG.
  have ox1: #[x1] = p by rewrite orderE -defG1 (Ohm1_cyclic_pgroup_prime _ pG).
  have Gx1: x1 \in G by rewrite -cycle_subG -defG1 Ohm_sub.
  have ker_m0: 'ker m0 = 'C('Ohm_1(G) | 'A_G).
    apply/setP=> a; rewrite inE in_setI; apply: andb_id2l => Aa.
    rewrite 3!inE /= -2!val_eqE /= val_Fp_nat // [1 %% _]modn_small // defG1.
    apply/idP/subsetP=> [ma1 x1i | ma1].
      case/cycleP=> i ->{x1i}; rewrite inE gactX // -[_ a]def_m //.
      by rewrite -(expg_mod_order x1) ox1 (eqP ma1).
    have:= ma1 x1 (cycle_id x1); rewrite inE -[_ a]def_m //.
    by rewrite (eq_expg_mod_order x1 _ 1) ox1 (modn_small p_gt1).
  have card_units_Fp: #|[set: {unit 'F_p}]| = p.-1.
    by rewrite card_units_Zp // pdiv_id // (@phi_pfactor p 1) ?muln1.
  have ker_m0_P: 'ker m0 = P.
    apply: nilpotent_Hall_pcore nilA _.
    rewrite pHallE -(card_Hall sylP) oP subsetIl /=.
    rewrite -(@eqn_pmul2r #|m0 @* A|) ?cardG_gt0 //; apply/eqP.
    rewrite -{1}(isog_card (first_isog _)) card_quotient ?ker_norm //.
    by rewrite LaGrange ?subsetIl // oA im_m0 mulnC card_units_Fp.
  have inj_m0: 'ker_F m0 \subset [1] by rewrite setIC ker_m0_P tiPF.
  split; last by rewrite /faithful -ker_m0.
  have isogF: F \isog [set: {unit 'F_p}].
    have sFA: F \subset A by exact: pcore_sub.
    apply/isogP; exists (restrm_morphism sFA m0); first by rewrite ker_restrm.
    apply/eqP; rewrite eqEcard subsetT card_injm ?ker_restrm //= oF.
    by rewrite card_units_Fp.
  rewrite (isog_cyclic isogF) pdiv_id // -ox1 (isog_cyclic (Zp_unit_isog x1)).
  by rewrite Aut_prime_cyclic // -orderE ox1.
exists m; split=> {im_m mV}//.
case: posnP => [n0 | n_gt0].
  by apply/eqP; rewrite eq_sym eqEcard pcore_sub oF oA n0 muln1 /=.
have [t At mt]: {t | t \in A & m t = -1}.
  apply: inv_m; rewrite /= Zp_cast // coprime_modr modn_small // subn1.
  by rewrite coprimenP // ltnW.
have ot: #[t] = 2.
  apply/eqP; rewrite eqn_leq order_gt1 dvdn_leq ?order_dvdn //=.
    apply/eqP; move/(congr1 m); apply/eqP; rewrite mt m1 eq_sym -subr_eq0.
    rewrite opprK -val_eqE /= Zp_cast ?modn_small // /q oG ltnW //.
    by rewrite (leq_trans (_ : 2 ^ 2 <= p ^ 2)) ?leq_sqr ?leq_exp2l.
  by apply/eqP; apply: inj_m; rewrite ?groupX ?group1 ?mX // mt -signr_odd.
exists t; split=> //.
case G4: (~~ odd p && (n == 1%N)).
  case: (even_prime p_pr) G4 => [p2 | -> //]; rewrite p2 /=; move/eqP=> n1.
  rewrite n1 /=; apply/eqP; rewrite eq_sym eqEcard cycle_subG At /=.
  by rewrite -orderE oA ot p2 n1.
pose e0 : nat := ~~ odd p.
have{inv_m} [s As ms]: {s | s \in A & m s = (p ^ e0.+1).+1%:R}.
  apply: inv_m; rewrite val_Zp_nat // coprime_modr /q oG coprime_pexpl //.
  by rewrite -(@coprime_pexpl e0.+1) // coprimenS.
have lt_e0_n: e0 < n.
  by rewrite /e0; case: (~~ _) G4 => //=; rewrite ltn_neqAle eq_sym => ->.
pose s0 := s ^+ (p ^ (n - e0.+1)).
have [ms0 os0]: m s0 = (p ^ n).+1%:R /\ #[s0] = p.
  have m_se: forall e,
    exists2 k, k = 1 %[mod p] & m (s ^+ (p ^ e)) = (k * p ^ (e + e0.+1)).+1%:R.
  - elim=> [|e [k k1 IHe]]; first by exists 1%N; rewrite ?mul1n.
    rewrite expnSr expgn_mul mX ?groupX // {}IHe -natr_exp -(add1n (k * _)).
    rewrite expn_addl -(prednK p_gt0) 2!big_ord_recl /= prednK // !exp1n bin1.
    rewrite bin0 muln1 mul1n mulnCA -expnS (addSn e).
    set f := (e + _)%N; set sum := (\sum_i _)%N.
    exists (sum %/ p ^ f.+2 * p + k)%N; first by rewrite modn_addl_mul.
    rewrite -(addnC k) muln_addl -mulnA -expnS divnK // {}/sum.
    apply big_prop => [||[i _] /= _]; [exact: dvdn0 | exact: dvdn_add |].
    rewrite exp1n mul1n /bump !add1n expn_mull mulnCA dvdn_mull // -expn_mulr.
    case: (ltnP f.+1 (f * i.+2)) => [le_f_fi|].
      by rewrite dvdn_mull ?dvdn_exp2l.
    rewrite {1}mulnS -(addn1 f) leq_add2l {}/f addnS /e0.
    case: i e => [] // [] //; case odd_p: (odd p) => //= _.
    by rewrite bin2odd // mulnAC dvdn_mulr.
  have [[|d]] := m_se (n - e0.+1)%N; first by rewrite mod0n modn_small.
  move/eqP; rewrite -/s0 eqn_mod_dvd ?subn1 //=; case/dvdnP=> f -> {d}.
  rewrite subnK // mulSn -mulnA -expnS -addSn natr_add natr_mul -oG char_Zp //.
  rewrite mulr0 addr0 => m_s0; split => //.
  have [d _] := m_se (n - e0)%N; rewrite ltn_subS // expnSr expgn_mul -/s0.
  rewrite addSn subnK // -oG  mulrS natr_mul char_Zp // {d}mulr0 addr0. 
  move/eqP; rewrite -m1 (inj_in_eq inj_m) ?group1 ?groupX // -order_dvdn.
  move/min_p; rewrite order_eq1; case/predU1P=> [s0_1 | ]; last by move/eqP.
  move/eqP: m_s0; rewrite eq_sym s0_1 m1 -subr_eq0 mulrSr addrK -val_eqE /=.
  have pf_gt0: p ^ _ > 0 by move=> e; rewrite expn_gt0 p_gt0.
  by rewrite val_Zp_nat // /q oG [_ == _]pfactor_dvdn // pfactorK ?ltnn.
have os: #[s] = (p ^ (n - e0))%N.
  have: #[s] %| p ^ (n - e0).
    by rewrite order_dvdn ltn_subS // expnSr expgn_mul -order_dvdn os0.
  case/dvdn_pfactor=> // d; rewrite leq_eqVlt.
  case/predU1P=> [-> // | lt_d os]; case/idPn: (p_gt1); rewrite -os0.
  by rewrite order_gt1 negbK -order_dvdn os dvdn_exp2l // -ltnS -leq_subS.
have p_s: p.-elt s by rewrite /p_elt os pnat_exp ?pnat_id.
have defS1: 'Ohm_1(<[s]>) = <[s0]>.
  apply/eqP; rewrite eq_sym eqEcard cycle_subG -orderE os0.
  rewrite (Ohm1_cyclic_pgroup_prime _ p_s) ?cycle_cyclic ?leqnn ?cycle_eq1 //=.
    rewrite (OhmE _ p_s) mem_gen ?groupX //= inE mem_cycle //.
    by rewrite -order_dvdn os0 ?dvdnn.
  by apply/eqP=> s1; rewrite -os0 /s0 s1 exp1gn order1 in p_gt1.  
case: (even_prime p_pr) => [p2 | oddp]; last first.
  rewrite {+}/e0 oddp subn0 in s0 os0 ms0 os ms defS1 *.
  have [f defF] := cyclicP _ cycF; have defP: P = <[s]>.
    apply/eqP; rewrite eq_sym eqEcard -orderE oP os leqnn andbT.
    by rewrite cycle_subG (mem_normal_Hall sylP) ?pcore_normal.
  rewrite defP; split; last 1 [by exists s | by exists s0; rewrite ?groupX].
  rewrite -defPF defP defF -cycleM ?cycle_cyclic // /order.
    by red; rewrite (centsP cAA) // -cycle_subG -defF pcore_sub.
  by rewrite -defF -defP (pnat_coprime (pcore_pgroup _ _) (pcore_pgroup _ _)).
rewrite {+}/e0 p2 subn1 /= in s0 os0 ms0 os ms G4 defS1 lt_e0_n *.
rewrite G4; exists s; split=> //; last first.
  exists s0; split; rewrite ?groupX //; apply/eqP; rewrite mM ?groupX //.
  rewrite ms0 mt eq_sym mulrN1 -subr_eq0 opprK -natr_add -addSnnS.
  by rewrite prednK ?expn_gt0 // addnn -mul2n -expnS -p2 -oG char_Zp.
suffices TIst: <[s]> :&: <[t]> = 1.
  rewrite dprodE //; last by rewrite (sub_abelian_cent2 cAA) ?cycle_subG.
  apply/eqP; rewrite eqEcard mulG_subG !cycle_subG As At oA.
  by rewrite TI_cardMg // -!orderE os ot p2 mul1n /= -expnSr prednK.
rewrite setIC; apply: prime_TIg; first by rewrite -orderE ot.
rewrite cycle_subG; apply/negP=> St.
have: t \in <[s0]>.
  by rewrite -defS1 (OhmE _ p_s) mem_gen // inE St -order_dvdn ot p2.
have ->: <[s0]> = [set 1; s0].
  apply/eqP; rewrite eq_sym eqEcard subUset !sub1set group1 cycle_id /=.
  by rewrite -orderE cards2 eq_sym -order_gt1 os0.
rewrite !inE -order_eq1 ot /=; move/eqP; move/(congr1 m); move/eqP.
rewrite mt ms0 eq_sym -subr_eq0 opprK -mulrSr.
rewrite -val_eqE [val _]val_Zp_nat //= /q oG p2 modn_small //.
by rewrite -addn3 expnS mul2n -addnn leq_add2l (ltn_exp2l 1).
Qed.

Definition extremal_generators gT (A : {set gT}) p n xy :=
  let: (x, y) := xy in
  [/\ #|A| = (p ^ n)%N, x \in A, #[x] = (p ^ n.-1)%N & y \in A :\: <[x]>].

Lemma extremal_generators_facts : forall gT (G : {group gT}) p n x y,
    prime p -> extremal_generators G p n (x, y) ->
  [/\ p.-group G, maximal <[x]> G, <[x]> <| G,
      <[x]> * <[y]> = G & <[y]> \subset 'N(<[x]>)].
Proof.
move=> gT G p n x y p_pr [oG Gx ox]; case/setDP=> Gy notXy.
have pG: p.-group G by rewrite /pgroup oG pnat_exp pnat_id.
have maxX: maximal <[x]> G.
  rewrite p_index_maximal -?divgS ?cycle_subG // -orderE oG ox.
  case: (n) oG => [|n' _]; last by rewrite -expn_sub ?subSnn ?leqnSn ?prime_gt0.
  move/eqP; rewrite -trivg_card1; case/trivgPn.
  by exists y; rewrite // (group1_contra notXy).
have nsXG := p_maximal_normal pG maxX; split=> //.
  by apply: mulg_normal_maximal; rewrite ?cycle_subG.
by rewrite cycle_subG (subsetP (normal_norm nsXG)).
Qed.

Section ModularGroup.

Variables p n : nat.
Let m := (p ^ n)%N.
Let q := (p ^ n.-1)%N.
Let r := (p ^ n.-2)%N.

Hypotheses (p_pr : prime p) (n_gt2 : n > 2).
Let p_gt1 := prime_gt1 p_pr.
Let p_gt0 := ltnW p_gt1.
Let def_n := esym (subnKC n_gt2).
Let def_p : pdiv m = p. Proof. by rewrite /m def_n pdiv_pfactor. Qed.
Let def_q : m %/ p = q. Proof. by rewrite /m /q def_n expnS mulKn. Qed.
Let def_r : q %/ p = r. Proof. by rewrite /r /q def_n expnS mulKn. Qed.
Let ltqm : q < m. Proof. by rewrite ltn_exp2l // def_n. Qed.
Let ltrq : r < q. Proof. by rewrite ltn_exp2l // def_n. Qed.
Let r_gt0 : 0 < r. Proof. by rewrite expn_gt0 ?p_gt0. Qed.
Let q_gt1 : q > 1. Proof. exact: leq_ltn_trans r_gt0 ltrq. Qed.

Lemma card_modular_group : #|'Mod_(p ^ n)| = (p ^ n)%N.
Proof. by rewrite Extremal.card def_p ?def_q // -expnS def_n. Qed.

Lemma Grp_modular_group :
  'Mod_(p ^ n) \isog Grp (x : y : (x ^+ q, y ^+ p, x ^ y = x ^+ r.+1)).
Proof.
rewrite /modular_gtype def_p def_q def_r; apply: Extremal.Grp => //.
set B := <[_]>; have Bb: Zp1 \in B by exact: cycle_id.
have oB: #|B| = q by rewrite -orderE order_Zp1 Zp_cast.
have cycB: cyclic B by rewrite cycle_cyclic.
have pB: p.-group B by rewrite /pgroup oB pnat_exp ?pnat_id.
have ntB: B != 1 by rewrite -cardG_gt1 oB.
have [] := cyclic_pgroup_Aut_structure pB cycB ntB.

rewrite oB pfactorK //= -/B -(expgn_znat r.+1 Bb) oB => mB [[def_mB _ _ _ _] _].

rewrite {1}def_n /= => [[t [At ot mBt]]].
have [p2 | ->] := even_prime p_pr; last first.
  by case=> _ _ [s [As os mBs _]]; exists s; rewrite os -mBs def_mB.
rewrite {1}p2 /= -2!eqSS -addn2 -2!{1}subn1 subn_sub subnK 1?ltnW //.
case: eqP => [n3 _ | _ [_ [_ _ _ _ [s [As os mBs _ _]{t At ot mBt}]]]].
  by exists t; rewrite At ot -def_mB // mBt /q /r p2 n3.
by exists s; rewrite As os -def_mB // mBs /r p2.
Qed.

Definition modular_group_generators gT (xy : gT * gT) :=
  let: (x, y) := xy in #[y] = p /\ x ^ y = x ^+ r.+1.

Lemma generators_modular_group : forall gT (G : {group gT}),
    G \isog 'Mod_m ->
  exists2 xy, extremal_generators G p n xy & modular_group_generators xy.
Proof.
move=> gT G; case/(isoGrpP _ Grp_modular_group)=> oG.
rewrite card_modular_group // -/m in oG.
case/existsP=> [[x y]] /=; case/eqP=> defG xq yp xy.
rewrite norm_mulgenEr ?cycle_norm_cycle ?xy ?mem_cycle // in defG.
have [Gx Gy]: x \in G /\ y \in G.
  by apply/andP; rewrite -!cycle_subG -mulG_subG defG.
have notXy: y \notin <[x]>.
  apply: contraL ltqm; rewrite -cycle_subG -oG -defG; move/mulGidPl->.
  by rewrite -leqNgt dvdn_leq ?(ltnW q_gt1) // order_dvdn xq.
have oy: #[y] = p by exact: nt_prime_order (group1_contra notXy).
exists (x, y) => //=; split; rewrite ?inE ?notXy //.
apply/eqP; rewrite -(eqn_pmul2r p_gt0) -expnSr -{1}oy (ltn_predK n_gt2) -/m.
by rewrite -TI_cardMg ?defG ?oG // setIC prime_TIg ?cycle_subG // -orderE oy.
Qed.

(* This is an adaptation of Aschbacher, exercise 8.2: *)
(*  - We allow an alternative to the #[x] = p ^ n.-1 condition that meshes    *)
(*    better with the modular_Grp lemma above.                                *)
(*  - We state explicitly some "obvious" properties of G, namely that G is    *)
(*    the non-abelian semi-direct product <[x]> ><| <[y]> and that y ^+ j     *)
(*    acts on <[x]> via z |-> z ^+ (j * p ^ n.-2).+1                          *)
(*  - We also give the values of the 'Mho^k(G).                               *)
(*  - We corrected a pair of typos.                                           *)
Lemma modular_group_structure : forall gT (G : {group gT}) x y,
    extremal_generators G p n (x, y) ->
    G \isog 'Mod_m -> modular_group_generators (x, y) ->
  let X := <[x]> in
  [/\ [/\ X ><| <[y]> = G, ~~ abelian G
        & {in X, forall z j, z ^ (y ^+ j) = z ^+ (j * r).+1}],
      [/\ 'Z(G) = <[x ^+ p]>, 'Phi(G) = 'Z(G) & #|'Z(G)| = r],
      [/\ G^`(1) = <[x ^+ r]>, #|G^`(1)| = p & nil_class G = 2],
      forall k, k > 0 -> 'Mho^k(G) = <[x ^+ (p ^ k)]>
    & if (p, n) == (2, 3) then 'Ohm_1(G) = G else
      forall k, 0 < k < n.-1 ->
         <[x ^+ (p ^ (n - k.+1))]> \x <[y]> = 'Ohm_k(G)
      /\ #|'Ohm_k(G)| = (p ^ k.+1)%N].
Proof.
move=> gT G x y genG isoG [oy xy] X.
have [oG Gx ox] := genG; case/setDP=> Gy notXy; rewrite -/m -/q in ox oG.
have [pG _ nsXG defXY nXY] := extremal_generators_facts p_pr genG.
have [sXG nXG] := andP nsXG; have sYG: <[y]> \subset G by rewrite cycle_subG.
have n1_gt1: n.-1 > 1 by [rewrite def_n]; have n1_gt0 := ltnW n1_gt1.
have def_n1 := prednK n1_gt0.
have def_m: (q * p)%N = m by rewrite -expnSr /m def_n.
have notcxy: y \notin 'C[x].
  apply: contraL (introT eqP xy); move/cent1P=> cxy.
  rewrite /conjg -cxy // eq_mulVg1 expgS !mulKg -order_dvdn ox.
  by rewrite pfactor_dvdn ?expn_gt0 ?p_gt0 // pfactorK // -ltnNge prednK.
have tiXY: <[x]> :&: <[y]> = 1.
  rewrite setIC prime_TIg -?orderE ?oy //; apply: contra notcxy.
  by rewrite cycle_subG; apply: subsetP; rewrite cycle_subG cent1id.
have notcGG: ~~ abelian G.
  by rewrite -defXY abelianM !cycle_abelian !(cent_cycle, sub_cent1).
have cYXp: <[x ^+ p]> \subset 'C(<[y]>).
  rewrite cent_cycle cycle_subG (sameP cent1P commgP) /commg conjXg xy.
  by rewrite -expgn_mul mulSn expgn_add mulKg -expnSr def_n1 -/q -ox expg_order.
have oxp: #[x ^+ p] = r by rewrite orderXdiv ox ?dvdn_exp //.
have [sZG nZG] := andP (center_normal G).
have defZ: 'Z(G) = <[x ^+ p]>.
  apply/eqP; rewrite eq_sym eqEcard subsetI -{2}defXY centM subsetI cYXp.
  rewrite cent_cycle !cycle_subG !groupX ?cent1id //= -orderE oxp leqNgt.
  apply: contra notcGG => gtZr; apply: cyclic_center_factor.
  rewrite (dvdn_prime_cyclic p_pr) // card_quotient //.
  rewrite -(dvdn_pmul2l (cardG_gt0 'Z(G))) LaGrange // oG -def_m dvdn_pmul2r //.
  case/p_natP: (pgroupS sZG pG) gtZr => k ->.
  by rewrite ltn_exp2l // def_n1; exact: dvdn_exp2l.
have Zxr: x ^+ r \in 'Z(G) by rewrite /r def_n expnS expgn_mul defZ mem_cycle.
have rxy: [~ x, y] = x ^+ r by rewrite /commg xy expgS mulKg.
have defG': G^`(1) = <[x ^+ r]>.
  case/setIP: Zxr => _; rewrite -rxy -defXY -(norm_mulgenEr nXY).
  exact: der1_mulgen_cycles.
have oG': #|G^`(1)| = p.
  by rewrite defG' -orderE orderXdiv ox /q -def_n1 ?dvdn_exp2l // expnS mulnK.
have sG'Z: G^`(1) \subset 'Z(G) by rewrite defG' cycle_subG.
have nil2_G: nil_class G = 2.
  by apply/eqP; rewrite eqn_leq andbC ltnNge nil_class1 notcGG nil_class2.
have XYp: {in X & <[y]>, forall z t,
   (z * t) ^+ p \in z ^+ p *: <[x ^+ r ^+ 'C(p, 2)]>}.
- move=> z t Xz Yt; have Gz := subsetP sXG z Xz; have Gt := subsetP sYG t Yt.
  have Rtz: [~ t, z] \in G^`(1) by exact: mem_commg.
  have cGtz: [~ t, z] \in 'C(G) by case/setIP: (subsetP sG'Z _ Rtz).
  rewrite expMg_Rmul /commute ?(centP cGtz) //.
  have ->: t ^+ p = 1 by apply/eqP; rewrite -order_dvdn -oy order_dvdG.
  rewrite defG' in Rtz; case/cycleP: Rtz => i ->.
  by rewrite mem_lcoset mulg1 mulKg expgnC mem_cycle.
have defMho: 'Mho^1(G) = <[x ^+ p]>.
  apply/eqP; rewrite eqEsubset cycle_subG (Mho_p_elt 1) ?(mem_p_elt pG) //.
  rewrite andbT (MhoE 1 pG) gen_subG -defXY; apply/subsetP=> ztp.
  case/imsetP=> zt; case/imset2P=> z t Xz Yt -> -> {zt ztp}.
  apply: subsetP (XYp z t Xz Yt); case/cycleP: Xz => i ->.
  by rewrite expgnC mul_subG ?sub1set ?mem_cycle //= -defZ cycle_subG groupX.
split=> //; try exact: extend_cyclic_Mho.
- rewrite sdprodE //; split=> // z; case/cycleP=> i ->{z} j.
  rewrite conjXg -expgn_mul mulnC expgn_mul actX; congr (_ ^+ i).
  elim: j {i} => //= j ->; rewrite conjXg xy -!expgn_mul mulnS mulSn addSn.
  rewrite addnA -mulSn -addSn expgn_add mulnCA (mulnC j).
  rewrite {3}/r def_n expnS mulnA -expnSr def_n1 -/q -ox -mulnA expgn_mul.
  by rewrite expg_order exp1gn mulg1.
- by rewrite (Phi_mulgen pG) defMho -defZ (mulgen_idPr _) ?defZ.
have G1y: y \in 'Ohm_1(G).
  by rewrite (OhmE _ pG) mem_gen // inE Gy -order_dvdn oy /=.
case: eqP => [[p2 n3] | notG8 k]; last case/andP=> k_gt0 lt_k_n1.
  apply/eqP; rewrite eqEsubset Ohm_sub -{1}defXY mulG_subG !cycle_subG.
  rewrite G1y -(groupMr _ G1y) /= (OhmE _ pG) mem_gen // inE groupM //.
  rewrite /q /r p2 n3 in oy ox xy *.
  by rewrite expgS -mulgA -{1}(invg2id oy) -conjgE xy -expgS -order_dvdn ox.
have le_k_n2: k <= n.-2 by rewrite -def_n1 in lt_k_n1.
suffices{lt_k_n1} defGk: <[x ^+ (p ^ (n - k.+1))]> \x <[y]> = 'Ohm_k(G).
  split=> //; case/dprodP: defGk => _ <- _ tiXkY; rewrite expnSr TI_cardMg //.
  rewrite -!orderE oy -(subn_sub 1) subn1 orderXdiv ox ?dvdn_exp2l ?leq_subr //.
  by rewrite /q -{1}(subnK (ltnW lt_k_n1)) expn_add mulKn // expn_gt0 p_gt0.
suffices{k k_gt0 le_k_n2} defGn2: <[x ^+ p]> \x <[y]> = 'Ohm_(n.-2)(G).
  have:= Ohm_dprod k defGn2; have p_xp := mem_p_elt pG (groupX p Gx).
  rewrite (Ohm_p_cycle _ p_xp) (Ohm_p_cycle _ (mem_p_elt pG Gy)) oxp oy.
  rewrite pfactorK ?(pfactorK 1) // (eqnP k_gt0) expg1 -expgn_mul -expnS.
  rewrite -leq_subS // -subSS def_n1 def_n => -> /=; rewrite -ltn_subS // subn2.
  by apply/eqP; rewrite eqEsubset OhmS ?Ohm_sub //= -{1}Ohm_id OhmS ?Ohm_leq.
rewrite dprodEgen //=; last by apply/trivgP; rewrite -tiXY setSI ?cycleX.
apply/eqP; rewrite eqEsubset mulgen_subG !cycle_subG /= {-2}(OhmE _ pG) -/r.
rewrite def_n (subsetP (Ohm_leq G (ltn0Sn _))) // mem_gen /=; last first.
  by rewrite inE -order_dvdn oxp groupX /=.
rewrite gen_subG /= cent_mulgenEl // -defXY; apply/subsetP=> uv; case/setIdP.
case/imset2P=> u v Xu Yv ->{uv}; rewrite /r def_n expnS expgn_mul.
case/lcosetP: (XYp u v Xu Yv) => z; case/cycleP=> j ->{z} ->.
case/cycleP: Xu => i ->{u}; rewrite -!(expgn_mul, expgn_add) -order_dvdn ox.
rewrite (mulnC r) /r {1}def_n expnSr mulnA -muln_addl -mulnA -expnS.
rewrite -ltn_subS  // subn2 /q -def_n1 expnS dvdn_pmul2r // dvdn_addl.
  by case/dvdnP=> k ->; rewrite mulnC expgn_mul mem_mulg ?mem_cycle.
case: (ltngtP n 3) => [|n_gt3|n3]; first by rewrite ltnNge n_gt2.
  by rewrite ltn_subS // expnSr mulnA dvdn_mull. 
case: (even_prime p_pr) notG8 => [-> | oddp _]; first by rewrite n3.
by rewrite bin2odd // -!mulnA dvdn_mulr.
Qed.

End ModularGroup.

(* Basic properties of dihedral groups; these will be refined for dihedral    *)
(* 2-groups in the section on extremal 2-groups.                              *)
Section DihedralGroup.

Variable q : nat.
Hypothesis q_gt1 : q > 1.
Let m := q.*2.

Let def2 : pdiv m = 2.
Proof.
apply/eqP; rewrite /m -mul2n eqn_leq pdiv_min_dvd ?dvdn_mulr //.
by rewrite prime_gt1 // pdiv_prime // (@leq_pmul2l 2 1) ltnW.
Qed.

Let def_q : m %/ pdiv m = q. Proof. by rewrite def2 divn2 half_double. Qed.

Section Dihedral_extension.

Variable p : nat.
Hypotheses (p_gt1 : p > 1) (even_p : 2 %| p).
Local Notation ED := [set: gsort (Extremal.gtype q p q.-1)].

Lemma card_ext_dihedral : #|ED| = (p./2 * m)%N.
Proof. by rewrite Extremal.card // /m -mul2n -divn2 mulnA divnK. Qed.

Lemma Grp_ext_dihedral : ED \isog Grp (x : y : (x ^+ q, y ^+ p, x ^ y = x^-1)).
Proof.
suffices isoED: ED \isog Grp (x : y : (x ^+ q, y ^+ p, x ^ y = x ^+ q.-1)).
  move=> gT G; rewrite isoED.
  apply: eq_existsb => [[x y]] /=; rewrite !xpair_eqE.
  congr (_ && _); apply: andb_id2l; move/eqP=> xq1; congr (_ && (_ == _)).
  by apply/eqP; rewrite eq_sym eq_invg_mul -expgS (ltn_predK q_gt1) xq1.
have unitrN1 : GRing.unit (- 1) by move=> ?; rewrite unitr_opp unitr1.
pose uN1 : {unit 'Z_#[Zp1 : 'Z_q]} := Sub _ (unitrN1 _).
apply: Extremal.Grp=> //; exists (Zp_unitm uN1).
rewrite Aut_aut order_injm ?injm_Zp_unitm ?in_setT //; split=> //.
  by rewrite (dvdn_trans _ even_p) // order_dvdn -val_eqE /= mulrNN.
apply/eqP; rewrite autE ?cycle_id // eq_expg_mod_order /=.
by rewrite order_Zp1 !Zp_cast // !modn_mod (modn_small q_gt1) subn1.
Qed.

End Dihedral_extension.

Lemma card_dihedral : #|'D_m| = m.
Proof. by rewrite /('D_m)%type def_q card_ext_dihedral ?mul1n. Qed.

Lemma Grp_dihedral : 'D_m \isog Grp (x : y : (x ^+ q, y ^+ 2, x ^ y = x^-1)).
Proof. by rewrite /('D_m)%type def_q; exact: Grp_ext_dihedral. Qed.

Lemma Grp'_dihedral : 'D_m \isog Grp (x : y : (x ^+ 2, y ^+ 2, (x * y) ^+ q)).
Proof.
move=> gT G; rewrite Grp_dihedral; apply/existsP/existsP=> [] [[x y]] /=.
  case/eqP=> <- xq1 y2 xy; exists (x * y, y); rewrite !xpair_eqE /= eqEsubset.
  rewrite !mulgen_subG !mulgen_subr !cycle_subG -{3}(mulgK y x) /=.
  rewrite 2?groupM ?groupV ?mem_gen ?inE ?cycle_id ?orbT //= -mulgA expgS.
  by rewrite {1}(conjgC x) xy -mulgA mulKg -(expgS y 1) y2 mulg1 xq1 !eqxx.
case/eqP=> <- x2 y2 xyq; exists (x * y, y); rewrite !xpair_eqE /= eqEsubset.
rewrite !mulgen_subG !mulgen_subr !cycle_subG -{3}(mulgK y x) /=.
rewrite 2?groupM ?groupV ?mem_gen ?inE ?cycle_id ?orbT //= xyq y2 !eqxx /=.
by rewrite eq_sym eq_invg_mul !mulgA mulgK -mulgA -!(expgS _ 1) x2 y2 mulg1.
Qed.

End DihedralGroup.

Lemma involutions_gen_dihedral : forall gT (x y : gT),
  let G := <<[set x; y]>> in
  #[x] = 2 -> #[y] = 2 -> x != y -> G \isog 'D_#|G|.
Proof.
move=> gT x y G ox oy ne_x_y; pose q := #[x * y].
have q_gt1: q > 1 by rewrite order_gt1 -eq_invg_mul invg_expg ox.
have homG: G \homg 'D_q.*2.
  rewrite Grp'_dihedral //; apply/existsP; exists (x, y); rewrite /= !xpair_eqE.
  by rewrite mulgen_idl mulgen_idr -{1}ox -oy !expg_order !eqxx.
suff oG: #|G| = q.*2 by rewrite oG isogEcard oG card_dihedral ?leqnn ?andbT.
have: #|G| %| q.*2  by rewrite -card_dihedral ?card_homg.
have Gxy: <[x * y]> \subset G.
  by rewrite cycle_subG groupM ?mem_gen ?set21 ?set22.
have[k oG]: exists k, #|G| = (k * q)%N by apply/dvdnP; rewrite cardSg.
rewrite oG -mul2n dvdn_pmul2r ?order_gt0 ?dvdn_divisors // !inE /=.
case/pred2P=> [k1 | -> //]; case/negP: ne_x_y.
have cycG: cyclic G.
  apply/cyclicP; exists (x * y); apply/eqP.
  by rewrite eq_sym eqEcard Gxy oG k1 mul1n leqnn.
have: <[x]> == <[y]>.
  by rewrite (eq_subG_cyclic cycG) ?genS ?subsetUl ?subsetUr -?orderE ?ox ?oy.
by rewrite eqEcard cycle_subG /= cycle2g // !inE -order_eq1 ox; case/andP.
Qed.

Lemma Grp_2dihedral : forall n, n > 1 ->
 'D_(2 ^ n) \isog Grp (x : y : (x ^+ (2 ^ n.-1), y ^+ 2, x ^ y = x^-1)).
Proof.
move=> n n_gt1; rewrite -(ltn_predK n_gt1) expnS mul2n /=.
by apply: Grp_dihedral; rewrite (ltn_exp2l 0) // -(subnKC n_gt1).
Qed.

Lemma card_2dihedral : forall n, n > 1 -> #|'D_(2 ^ n)| = (2 ^ n)%N.
Proof.
move=> n n_gt1; rewrite -(ltn_predK n_gt1) expnS mul2n /= card_dihedral //.
by rewrite (ltn_exp2l 0) // -(subnKC n_gt1).
Qed.

Lemma card_semidihedral : forall n, n > 3 -> #|'SD_(2 ^ n)| = (2 ^ n)%N.
Proof.
move=> n n_gt3.
rewrite /('SD__)%type -(subnKC (ltnW (ltnW n_gt3))) pdiv_pfactor //.
by rewrite // !expnS !mulKn -?expnS ?Extremal.card //= (ltn_exp2l 0).
Qed.

Lemma Grp_semidihedral : forall n, n > 3 ->
 'SD_(2 ^ n) \isog
     Grp (x : y : (x ^+ (2 ^ n.-1), y ^+ 2, x ^ y = x ^+ (2 ^ n.-2).-1)).
Proof.
move=> n n_gt3.
rewrite /('SD__)%type -(subnKC (ltnW (ltnW n_gt3))) pdiv_pfactor //.
rewrite !expnS !mulKn // -!expnS /=; set q := (2 ^ _)%N.
have q_gt1: q > 1 by rewrite (ltn_exp2l 0).
apply: Extremal.Grp => //; set B := <[_]>.
have oB: #|B| = q by rewrite -orderE order_Zp1 Zp_cast.
have pB: 2.-group B by rewrite /pgroup oB pnat_exp.
have ntB: B != 1 by rewrite -cardG_gt1 oB.
have [] := cyclic_pgroup_Aut_structure pB (cycle_cyclic _) ntB.
rewrite oB /= pfactorK //= -/B => m [[def_m _ _ _ _] _].
rewrite -{1 2}(subnKC n_gt3) => [[t [At ot _ [s [_ _ _ defA]]]]].
case/dprodP: defA => _ defA cst _.
have{cst defA} cAt: t \in 'C(Aut B).
  by rewrite -defA centM inE -sub_cent1 -cent_cycle cst cent_cycle cent1id.
case=> s0 [As0 os0 _ def_s0t _]; exists (s0 * t).
rewrite -def_m ?groupM ?cycle_id // def_s0t !Zp_expgn !mul1n valZpK Zp_nat.
rewrite order_dvdn expMgn /commute 1?(centP cAt) // -{1}os0 -{1}ot.
by rewrite !expg_order mul1g.
Qed.

Section Quaternion.

Variable n : nat.
Hypothesis n_gt2 : n > 2.
Let m := (2 ^ n)%N.
Let q := (2 ^ n.-1)%N.
Let r := (2 ^ n.-2)%N.
Let GrpQ := 'Q_m \isog Grp (x : y : (x ^+ q, y ^+ 2 = x ^+ r, x ^ y = x^-1)).
Let defQ :  #|'Q_m| = m /\ GrpQ.
Proof.
have q_gt1 : q > 1 by rewrite (ltn_exp2l 0) // -(subnKC n_gt2).
have def_m : (2 * q)%N = m by rewrite -expnS (ltn_predK n_gt2).
have def_q : m %/ pdiv m = q
  by rewrite /m -(ltn_predK n_gt2) pdiv_pfactor // expnS mulKn.
have r_gt1 : r > 1 by rewrite (ltn_exp2l 0) // -(subnKC n_gt2).
have def2r : (2 * r)%N = q by rewrite -expnS /q -(subnKC n_gt2).
unlock GrpQ quaternion_gtype quaternion_kernel; rewrite {}def_q.
set B := [set: _]; have: B \homg Grp (u : v : (u ^+ q, v ^+ 4, u ^ v = u^-1)).
  by rewrite -Grp_ext_dihedral ?homg_refl.
have: #|B| = (q * 4)%N by rewrite card_ext_dihedral // mulnC -muln2 -mulnA.
rewrite {}/B; move: (Extremal.gtype q 4 _) => gT.
set B := [set: gT] => oB; set K := _ :\: _.
case/existsP=> [[u v]] /=; case/eqP=> defB uq v4 uv.
have nUV: <[v]> \subset 'N(<[u]>).
  by rewrite cycle_norm_cycle uv groupV cycle_id.
rewrite norm_mulgenEr // in defB.
have le_ou: #[u] <= q by rewrite dvdn_leq ?expn_gt0 // order_dvdn uq. 
have le_ov: #[v] <= 4 by rewrite dvdn_leq // order_dvdn v4.
have tiUV: <[u]> :&: <[v]> = 1 by rewrite cardMg_TI // defB oB leq_mul.
have{le_ou le_ov} [ou ov]: #[u] = q /\ #[v] = 4.
  have:= esym (leqif_mul (leqif_eq le_ou) (leqif_eq le_ov)).2.
  by rewrite -TI_cardMg // defB -oB eqxx eqn0Ngt cardG_gt0; do 2!case: eqP=> //.
have sdB: <[u]> ><| <[v]> = B by rewrite sdprodE.
have uvj: forall j, u ^ (v ^+ j) = (if odd j then u^-1 else u).
  elim=> [|j IHj]; first by rewrite conjg1.
  by rewrite expgS conjgM uv conjVg IHj (fun_if invg) invgK if_neg.
have sqrB : forall i j,
  (u ^+ i * v ^+ j) ^+ 2 = (if odd j then v ^+ 2 else u ^+ i.*2).
- move=> i j; rewrite expgS; case: ifP => odd_j.
    rewrite {1}(conjgC (u ^+ i)) conjXg uvj odd_j expVgn -mulgA mulKg.
    rewrite -expgn_add addnn -(odd_double_half j) odd_j double_add addnC /=.
    by rewrite -(expg_mod _ v4) -!muln2 -mulnA modn_addl_mul.
  rewrite {2}(conjgC (u ^+ i)) conjXg uvj odd_j mulgA -(mulgA (u ^+ i)).
  rewrite -expgn_add addnn -(odd_double_half j) odd_j -2!mul2n mulnA.
  by rewrite expgn_mul v4 exp1gn mulg1 -expgn_add addnn.
pose w := u ^+ r * v ^+ 2.
have Kw: w \in K.
  rewrite !inE sqrB /= -mul2n def2r uq eqxx andbT -defB.
  apply/imsetP=> [[uivj]]; case/imset2P=> ui vj.
  case/cycleP=> i ->; case/cycleP=> j -> ->{ui vj uivj}; apply/eqP.
  rewrite sqrB; case: ifP => _.
    rewrite eq_mulgV1 mulgK -order_dvdn ou pfactor_dvdn ?expn_gt0 ?pfactorK //.
    by rewrite -ltnNge -(subnKC n_gt2).
  rewrite (canF_eq (mulKg _)); apply/eqP=> def_v2.
  suffices: v ^+ 2 \in <[u]> :&: <[v]> by rewrite tiUV inE -order_dvdn ov.
  by rewrite inE {1}def_v2 groupM ?groupV !mem_cycle.
have ow: #[w] = 2.
  case/setDP: Kw; rewrite inE -order_dvdn dvdn_divisors // !inE /= order_eq1.
  by case/orP; move/eqP=> -> //; case/imsetP; exists 1; rewrite ?inE ?exp1gn.
have defK: K = [set w].
  apply/eqP; rewrite eqEsubset sub1set Kw andbT subDset setUC.
  apply/subsetP=> uivj; have: uivj \in B by rewrite inE.
  rewrite -{1}defB; case/imset2P=> ui vj.
  case/cycleP=> i ->; case/cycleP=> j -> ->{ui vj uivj}.
  rewrite !inE sqrB -{-1}[j]odd_double_half.
  case: (odd j); rewrite -order_dvdn ?ov // ou -def2r -mul2n dvdn_pmul2l //.
  case/dvdnP=> k ->{i}; apply/orP.
  rewrite add0n -[j./2]odd_double_half addnC double_add -!muln2 -mulnA.
  rewrite -(expg_mod_order v) ov modn_addl_mul; case: (odd _); last first.
    right; rewrite mulg1 /r -(subnKC n_gt2) expnSr mulnA expgn_mul.
    by apply: mem_imset; rewrite inE.
  rewrite (inj_eq (mulIg _)) -expg_mod_order ou -[k]odd_double_half.
  rewrite addnC -muln2 muln_addl -mulnA def2r modn_addl_mul -ou expg_mod_order.
  case: (odd k); [left | right]; rewrite ?mul1n ?mul1g //.
  by apply/imsetP; exists v; rewrite ?inE.
have nKB: 'N(<<K>>) = B.
  apply/setP=> b; rewrite !inE -genJ genS // {1}defK conjg_set1 sub1set.
  have:= Kw; rewrite !inE -!order_dvdn orderJ ow !andbT; apply: contra.
  case/imsetP=> z _ def_wb; apply/imsetP; exists (z ^ b^-1); rewrite ?inE //.
  by rewrite -conjXg -def_wb conjgK.
rewrite -quotientT card_quotient // nKB -divgS ?subsetT //.
split; first by rewrite oB defK -orderE ow (mulnA q 2 2) mulnK // mulnC.
apply: intro_isoGrp => [|rT H].
  apply/existsP; exists (coset _ u, coset _ v); rewrite /= !xpair_eqE.
  rewrite -!morphX -?morphJ -?morphV /= ?nKB ?in_setT // uq uv morph1 !eqxx.
  rewrite -/B -defB -norm_mulgenEr // quotient_mulgen2 ?nKB ?subsetT //= andbT.
  rewrite !quotient_cycle /= ?nKB ?in_setT ?eqxx //=.
  by rewrite -(coset_kerl _ (mem_gen Kw)) -mulgA -expgn_add v4 mulg1.
case/existsP=> [[x y]] /=; case/eqP=> defH xq y2 xy.
have ox: #[x] %| #[u] by rewrite ou order_dvdn xq.
have oy: #[y] %| #[v].
  by rewrite ov order_dvdn (expgn_mul y 2 2) y2 -expgn_mul mulnC def2r xq.
have actB: {in <[u]> & <[v]>, morph_act 'J 'J (eltm ox) (eltm oy)}.
  move=> ui vj; case/cycleP=> i ->; case/cycleP=> j -> {ui vj} /=.
  rewrite conjXg uvj fun_if if_arg fun_if expVgn morphV ?mem_cycle //= !eltmE.
  rewrite -expVgn -if_arg -fun_if conjXg; congr (_ ^+ i).
  rewrite -{2}[j]odd_double_half addnC expgn_add -mul2n expgn_mul y2.
  rewrite -expgn_mul conjgM (conjgE x) commuteX // mulKg.
  by case: (odd j); rewrite ?conjg1.
pose f := sdprodm sdB actB.
have Kf: 'ker (coset <<K>>) \subset 'ker f.
  rewrite ker_coset defK cycle_subG /= ker_sdprodm.
  apply/imset2P; exists (u ^+ r) (v ^+ 2); first exact: mem_cycle.
    by rewrite inE mem_cycle /= !eltmE y2.
  by apply: canRL (mulgK _) _; rewrite -mulgA -expgn_add v4 mulg1.
have Df: 'dom f \subset 'dom (coset <<K>>) by rewrite /dom nKB subsetT.
apply/homgP; exists (factm_morphism Kf Df); rewrite morphim_factm /= -/B.
rewrite -{2}defB morphim_sdprodm // !morphim_cycle ?cycle_id //= !eltm_id.
by rewrite -norm_mulgenEr // cycle_norm_cycle xy groupV cycle_id.
Qed.

Lemma card_quaternion : #|'Q_m| = m. Proof. by case defQ. Qed.
Lemma Grp_quaternion : GrpQ. Proof. by case defQ. Qed.

End Quaternion.

Lemma eq_Mod8_D8 : 'Mod_8 = 'D_8. Proof. by []. Qed.

Section ExtremalStructure.

Variables (gT : finGroupType) (G : {group gT}) (n : nat).

Implicit Type H : {group gT}.

Let m := (2 ^ n)%N.
Let q := (2 ^ n.-1)%N.
Let q_gt0: q > 0. Proof. by rewrite expn_gt0. Qed.
Let r := (2 ^ n.-2)%N.
Let r_gt0: r > 0. Proof. by rewrite expn_gt0. Qed.

Let def2qr : n > 1 -> [/\ 2 * q = m, 2 * r = q, q < m & r < q]%N.
Proof. by rewrite /q /m /r; move/subnKC=> <-; rewrite !ltn_exp2l ?expnS. Qed.

Lemma generators_2dihedral :
    n > 1 -> G \isog 'D_m ->
  exists2 xy, extremal_generators G 2 n xy
           & let: (x, y) := xy in #[y] = 2 /\ x ^ y = x^-1.
Proof.
move=> n_gt1; have [def2q _ ltqm _] := def2qr n_gt1.
case/(isoGrpP _ (Grp_2dihedral n_gt1)); rewrite card_2dihedral // -/ m => oG.
case/existsP=> [[x y]] /=; rewrite -/q; case/eqP=> defG xq y2 xy.
have{defG} defG: <[x]> * <[y]> = G.
  by rewrite -norm_mulgenEr // cycle_norm_cycle xy groupV cycle_id.
have notXy: y \notin <[x]>.
  apply: contraL ltqm => Xy; rewrite -leqNgt -oG -defG mulGSid ?cycle_subG //.
  by rewrite dvdn_leq // order_dvdn xq.
have oy: #[y] = 2 by exact: nt_prime_order (group1_contra notXy).
have ox: #[x] = q.
  apply: double_inj; rewrite -muln2 -oy -mul2n def2q -oG -defG TI_cardMg //.
  by rewrite setIC prime_TIg ?cycle_subG // -orderE oy.
exists (x, y) => //=.
by rewrite oG ox !inE notXy -!cycle_subG /= -defG  mulG_subl mulG_subr.
Qed.

Lemma generators_semidihedral :
    n > 3 -> G \isog 'SD_m ->
  exists2 xy, extremal_generators G 2 n xy
           & let: (x, y) := xy in #[y] = 2 /\ x ^ y = x ^+ r.-1.
Proof.
move=> n_gt3; have [def2q _ ltqm _] := def2qr (ltnW (ltnW n_gt3)).
case/(isoGrpP _ (Grp_semidihedral n_gt3)).
rewrite card_semidihedral // -/m => oG.
case/existsP=> [[x y]] /=; rewrite -/q -/r; case/eqP=> defG xq y2 xy.
have{defG} defG: <[x]> * <[y]> = G.
  by rewrite -norm_mulgenEr // cycle_norm_cycle xy mem_cycle.
have notXy: y \notin <[x]>.
  apply: contraL ltqm => Xy; rewrite -leqNgt -oG -defG mulGSid ?cycle_subG //.
  by rewrite dvdn_leq // order_dvdn xq.
have oy: #[y] = 2 by exact: nt_prime_order (group1_contra notXy).
have ox: #[x] = q.
  apply: double_inj; rewrite -muln2 -oy -mul2n def2q -oG -defG TI_cardMg //.
  by rewrite setIC prime_TIg ?cycle_subG // -orderE oy.
exists (x, y) => //=.
by rewrite oG ox !inE notXy -!cycle_subG /= -defG  mulG_subl mulG_subr.
Qed.

Lemma generators_quaternion :
    n > 2 -> G \isog 'Q_m ->
  exists2 xy, extremal_generators G 2 n xy
           & let: (x, y) := xy in [/\ #[y] = 4, y ^+ 2 = x ^+ r & x ^ y = x^-1].
Proof.
move=> n_gt2; have [def2q def2r ltqm _] := def2qr (ltnW n_gt2).
case/(isoGrpP _ (Grp_quaternion n_gt2)); rewrite card_quaternion // -/m => oG.
case/existsP=> [[x y]] /=; rewrite -/q -/r; case/eqP=> defG xq y2 xy.
have{defG} defG: <[x]> * <[y]> = G.
  by rewrite -norm_mulgenEr // cycle_norm_cycle xy groupV cycle_id.
have notXy: y \notin <[x]>.
  apply: contraL ltqm => Xy; rewrite -leqNgt -oG -defG mulGSid ?cycle_subG //.
  by rewrite dvdn_leq // order_dvdn xq.
have ox: #[x] = q.
  apply/eqP; rewrite eqn_leq dvdn_leq ?order_dvdn ?xq //=.
  rewrite -(leq_pmul2r (order_gt0 y)) mul_cardG defG oG -def2q mulnAC mulnC.
  rewrite leq_pmul2r // dvdn_leq ?muln_gt0 ?cardG_gt0 // order_dvdn expgn_mul.
  by rewrite -order_dvdn order_dvdG //= inE {1}y2 !mem_cycle.
have oy2: #[y ^+ 2] = 2 by rewrite y2 orderXdiv ox -def2r ?dvdn_mull ?mulnK.
exists (x, y) => /=; last by rewrite (orderXprime oy2).
by rewrite oG !inE notXy -!cycle_subG /= -defG  mulG_subl mulG_subr.
Qed.

Variables x y : gT.
Let X := <[x]>.
Let Y := <[y]>.
Let yG := y ^: G.
Let xyG := (x * y) ^: G.
Let My := <<yG>>.
Let Mxy := <<xyG>>.

Implicit Types M : {group gT}.

Theorem dihedral2_structure :
    n > 1 -> extremal_generators G 2 n (x, y) -> G \isog 'D_m -> 
  [/\ [/\ X ><| Y = G, {in G :\: X, forall t, #[t] = 2}
        & {in X & G :\: X, forall z t, z ^ t = z^-1}],
      [/\ G ^`(1) = <[x ^+ 2]>, 'Phi(G) = G ^`(1), #|G^`(1)| = r
        & nil_class G = n.-1],
      'Ohm_1(G) = G /\ (forall k, k > 0 -> 'Mho^k(G) = <[x ^+ (2 ^ k)]>),
      [/\ yG :|: xyG = G :\: X, [disjoint yG & xyG]
        & forall M, maximal M G = pred3 X My Mxy M]
    & if n == 2 then (2.-abelem G : Prop) else
  [/\ 'Z(G) = <[x ^+ r]>, #|'Z(G)| = 2,
       My \isog 'D_q, Mxy \isog 'D_q
     & forall U, cyclic U -> U \subset G -> #|G : U| = 2 -> U = X]].
Proof.
move=> n_gt1 genG isoG; have [def2q def2r ltqm ltrq] := def2qr n_gt1.
have [oG Gx ox X'y] := genG; rewrite -/m -/q -/X in oG ox X'y.
case/extremal_generators_facts: genG; rewrite -/X // => pG maxX nsXG defXY nXY.
have [sXG nXG]:= andP nsXG; have [Gy notXy]:= setDP X'y.
have ox2: #[x ^+ 2] = r by rewrite orderXdiv ox -def2r ?dvdn_mulr ?mulKn.
have oxr: #[x ^+ r] = 2 by rewrite orderXdiv ox -def2r ?dvdn_mull ?mulnK.
have [[u v] [_ Gu ou U'v] [ov uv]] := generators_2dihedral n_gt1 isoG.
have defUv: <[u]> :* v = G :\: <[u]>.
  apply: rcoset_index2; rewrite -?divgS ?cycle_subG //.
  by rewrite oG -orderE ou -def2q mulnK.
have invUV: {in <[u]> & <[u]> :* v, forall z t, z ^ t = z^-1}.
  move=> z t; case/cycleP=> i ->; case/rcosetP=> z'; case/cycleP=> j -> ->{z t}.
  by rewrite conjgM {2}/conjg commuteX2 // mulKg conjXg uv expVgn.
have oU': {in <[u]> :* v, forall t, #[t] = 2}.
  move=> t Uvt; apply: nt_prime_order => //; last first.
    by case: eqP Uvt => // ->; rewrite defUv !inE group1.
  case/rcosetP: Uvt => z Uz ->{t}; rewrite expgS {1}(conjgC z) -mulgA.
  by rewrite invUV ?rcoset_refl // mulKg -(expgS v 1) -ov expg_order.
have defU: n > 2 -> {in G, forall z, #[z] = q -> <[z]> = <[u]>}.
  move=> n_gt2 z Gz oz; apply/eqP; rewrite eqEcard -!orderE oz cycle_subG.
  apply: contraLR n_gt2; rewrite ou leqnn andbT -(ltn_predK n_gt1) => notUz.
  by rewrite ltnS -(@ltn_exp2l 2) // -/q -oz oU' // defUv inE notUz.
have n2_abelG: (n > 2) || 2.-abelem G.
  rewrite ltn_neqAle eq_sym n_gt1; case: eqP => //= n2.
  apply/abelemP=> //; split=> [|z Gz].
    by apply: (p2group_abelian pG); rewrite oG pfactorK ?n2.
  case Uz: (z \in <[u]>); last by rewrite -expg_mod_order oU' // defUv inE Uz.
  apply/eqP; rewrite -order_dvdn (dvdn_trans (order_dvdG Uz)) // -orderE.
  by rewrite ou /q n2.
have{oU'} oX': {in G :\: X, forall t, #[t] = 2}.
  have [n_gt2 | abelG] := orP n2_abelG; first by rewrite [X]defU // -defUv.
  move=> t; case/setDP=> Gt notXt.
  apply: nt_prime_order (group1_contra notXt) => //.
  by case/abelemP: abelG => // _ ->.
have{invUV} invXX': {in X & G :\: X, forall z t, z ^ t = z^-1}.
  have [n_gt2 | abelG] := orP n2_abelG; first by rewrite [X]defU // -defUv.
  have [//|cGG oG2] := abelemP _ abelG.
  move=> t z Xt; case/setDP=> Gz _; apply/eqP; rewrite eq_sym eq_invg_mul.
  by rewrite /conjg -(centsP cGG z) // ?mulKg ?[t * t]oG2 ?(subsetP sXG).
have nXiG: forall k, G \subset 'N(<[x ^+ k]>).
  move=> k; apply: char_norm_trans nXG.
  by rewrite cycle_subgroup_char // cycle_subG mem_cycle.
have memL: forall i, x ^+ (2 ^ i) \in 'L_i.+1(G).
  elim=> // i IHi; rewrite -groupV expnSr expgn_mul invMg.
  by rewrite -{2}(invXX' _ y) ?mem_cycle ?cycle_id ?mem_commg.
have defG': G^`(1) = <[x ^+ 2]>.
  apply/eqP; rewrite eqEsubset cycle_subG (memL 1%N) ?der1_min //=.
  rewrite (p2group_abelian (quotient_pgroup _ pG)) ?card_quotient //=.
  rewrite -divgS ?cycle_subG ?groupX // oG -orderE ox2.
  by rewrite -def2q -def2r mulnA mulnK.
have defG1: 'Mho^1(G) = <[x ^+ 2]>.
  apply/eqP; rewrite (MhoE _ pG) eqEsubset !gen_subG sub1set andbC.
  rewrite mem_gen; last exact: mem_imset.
  apply/subsetP=> z2; case/imsetP=> z Gz ->{z2}.
  case Xz: (z \in X); last by rewrite -{1}(oX' z) ?expg_order ?group1 // inE Xz.
  by case/cycleP: Xz => i ->; rewrite expgnC mem_cycle.
have defPhi: 'Phi(G) = <[x ^+ 2]>.
  by rewrite (Phi_mulgen pG) defG' defG1 (mulgen_idPl _).
have def_tG: {in G :\: X, forall t, t ^: G = <[x ^+ 2]> :* t}.
  move=> t X't; have [Gt notXt] := setDP X't.
  have defJt: {in X, forall z, t ^ z = z ^- 2 * t}.
    move=> z Xz; rewrite /= invMg -mulgA (conjgC _ t).
    by rewrite  (invXX' _ t) ?groupV ?invgK.
  have defGt: X * <[t]> = G by rewrite (mulg_normal_maximal nsXG) ?cycle_subG.
  apply/setP=> tz; apply/imsetP/rcosetP=> [[t'z] | [z]].
    rewrite -defGt -normC ?cycle_subG ?(subsetP nXG) //.
    case/imset2P=> t' z; case/cycleP=> j -> Xz -> -> {tz t'z t'}.
    exists (z ^- 2); last by rewrite conjgM {2}/conjg commuteX // mulKg defJt.
    case/cycleP: Xz => i ->{z}.
    by rewrite groupV -expgn_mul mulnC expgn_mul mem_cycle.
  case/cycleP=> i -> -> {z tz}; exists (x ^- i); first by rewrite groupV groupX.
  by rewrite defJt ?groupV ?mem_cycle // expVgn invgK expgnC.
have defMt: {in G :\: X, forall t, <[x ^+ 2]> ><| <[t]> = <<t ^: G>>}.
  move=> t X't; have [Gt notXt] := setDP X't.
  rewrite sdprodEgen ?cycle_subG ?(subsetP (nXiG 2)) //; first 1 last.
    rewrite setIC prime_TIg -?orderE ?oX' // cycle_subG.
    by apply: contra notXt; apply: subsetP; rewrite cycleX.
  apply/eqP; have: t \in <<t ^: G>> by rewrite mem_gen ?class_refl.
  rewrite def_tG // eqEsubset mulgen_subG !cycle_subG !gen_subG => tGt.
  rewrite tGt -(groupMr _ tGt) mem_gen ?mem_mulg ?cycle_id ?set11 //=.
  by rewrite mul_subG ?mulgen_subl // -gen_subG mulgen_subr.
have oMt: {in G :\: X, forall t, #|<<t ^: G>>| = q}.
  move=> t X't /=; rewrite -(sdprod_card (defMt t X't)) -!orderE ox2 oX' //.
  by rewrite mulnC.
have sMtG: {in G :\: X, forall t, <<t ^: G>> \subset G}.
  by move=> t; case/setDP=> Gt _; rewrite gen_subG class_subG.
have maxMt: {in G :\: X, forall t, maximal <<t ^: G>> G}.
  move=> t X't /=; rewrite p_index_maximal -?divgS ?sMtG ?oMt //.
  by rewrite oG -def2q mulnK.
have X'xy: x * y \in G :\: X by rewrite !inE !groupMl ?cycle_id ?notXy.
have ti_yG_xyG: [disjoint yG & xyG].
  apply/pred0P=> t; rewrite /= /yG /xyG !def_tG //; apply/andP=> [[yGt]].
  rewrite rcoset_sym (rcoset_transl yGt) mem_rcoset mulgK; move/order_dvdG.
  by rewrite -orderE ox2 ox gtnNdvd.
have s_tG_X': {in G :\: X, forall t, t ^: G \subset G :\: X}.
  by move=> t X't /=; rewrite class_sub_norm // normsD ?normG.
have defX': yG :|: xyG = G :\: X.
  apply/eqP; rewrite eqEcard subUset !s_tG_X' //= -(leq_add2l q) -{1}ox orderE.
  rewrite -/X -{1}(setIidPr sXG) cardsID oG -def2q mul2n -addnn leq_add2l.
  rewrite -(leq_add2r #|yG :&: xyG|) cardsUI disjoint_setI0 // cards0 addn0.
  by rewrite /yG /xyG !def_tG // !card_rcoset addnn -mul2n -orderE ox2 def2r.
split.
- by rewrite ?sdprodE // setIC // prime_TIg ?cycle_subG // -orderE ?oX'.
- rewrite defG'; split=> //.
  apply/eqP; rewrite eqn_leq (leq_trans (nil_class_pgroup pG)); last first.
    by rewrite oG pfactorK // leq_maxl leqnn -(subnKC n_gt1).
  rewrite -(subnKC n_gt1) subn2 ltnNge.
  rewrite (sameP (lcn_nil_classP _ (pgroup_nil pG)) eqP).
  by apply/trivgPn; exists (x ^+ r); rewrite ?memL // -order_gt1 oxr.
- split; last exact: extend_cyclic_Mho.
  have sX'G1: {subset G :\: X <= 'Ohm_1(G)}.
    move=> t X't; have [Gt _] := setDP X't.
    by rewrite (OhmE 1 pG) mem_gen // inE Gt -(oX' t) //= expg_order.
  apply/eqP; rewrite eqEsubset Ohm_sub -{1}defXY mulG_subG !cycle_subG.
  by rewrite -(groupMr _ (sX'G1 y X'y)) !sX'G1.
- split=> //= H; apply/idP/idP=> [maxH |]; last first.
    by case/or3P; move/eqP->; rewrite ?maxMt.
  have [sHG nHG]:= andP (p_maximal_normal pG maxH).
  have oH: #|H| = q. 
    apply: double_inj; rewrite -muln2 -(p_maximal_index pG maxH) LaGrange //.
    by rewrite oG -mul2n.
  rewrite !(eq_sym (gval H)) -eq_sym !eqEcard oH -orderE ox !oMt // !leqnn.
  case sHX: (H \subset X) => //=; case/subsetPn: sHX => t Ht notXt.
  have: t \in yG :|: xyG by rewrite defX' inE notXt (subsetP sHG).
  rewrite !andbT !gen_subG /yG /xyG.
  by case/setUP; move/class_transr <-; rewrite !class_sub_norm ?Ht ?orbT.
rewrite eqn_leq n_gt1; case: leqP n2_abelG => //= n_gt2 _.
have ->: 'Z(G) = <[x ^+ r]>.
  apply/eqP; rewrite eqEcard andbC -orderE oxr -{1}(setIidPr (center_sub G)).
  rewrite cardG_gt1 /= nil_meet_Z ?(pgroup_nil pG) //; last first.
    by rewrite -cardG_gt1 oG (leq_trans _ ltqm).
  apply/subsetP=> t; case/setIP=> Gt cGt.
  case X't: (t \in G :\: X).
    move/eqP: (invXX' _ _ (cycle_id x) X't).
    rewrite /conjg -(centP cGt) // mulKg eq_sym eq_invg_mul -order_eq1 ox2.
    by rewrite (eqn_exp2l _ 0) // -(subnKC n_gt2).
  move/idPn: X't; rewrite inE Gt andbT negbK => Xt.
  have:= Ohm_p_cycle 1 (mem_p_elt pG Gx); rewrite ox pfactorK // subn1 => <-.
  rewrite (OhmE _ (pgroupS sXG pG)) mem_gen // inE Xt /=.
  by rewrite -eq_invg_mul -(invXX' _ y) // /conjg (centP cGt) // mulKg.
have isoMt: {in G :\: X, forall t, <<t ^: G>> \isog 'D_q}.
  have n1_gt1: n.-1 > 1 by rewrite -(subnKC n_gt2).
  move=> t X't /=; rewrite isogEcard card_2dihedral ?oMt // leqnn andbT.
  rewrite Grp_2dihedral //; apply/existsP; exists (x ^+ 2, t) => /=.
  have [_ <- nX2T _] := sdprodP (defMt t X't); rewrite norm_mulgenEr //.
  rewrite -/q -/r !xpair_eqE eqxx -expgn_mul def2r -ox -{1}(oX' t X't).
  by rewrite !expg_order !eqxx /= invXX' ?mem_cycle.
rewrite !isoMt //; split=> // C; case/cyclicP=> z ->{C} sCG iCG.
rewrite [X]defU // defU -?cycle_subG //.
by apply: double_inj; rewrite -muln2 -iCG LaGrange // oG -mul2n.
Qed.

Theorem quaternion_structure :
    n > 2 -> extremal_generators G 2 n (x, y) -> G \isog 'Q_m ->
  [/\ [/\ pprod X Y = G, {in G :\: X, forall t, #[t] = 4}
        & {in X & G :\: X, forall z t, z ^ t = z^-1}],
      [/\ G ^`(1) = <[x ^+ 2]>, 'Phi(G) = G ^`(1), #|G^`(1)| = r
        & nil_class G = n.-1],
      [/\ 'Z(G) = <[x ^+ r]>, #|'Z(G)| = 2,
          forall u, u \in G -> #[u] = 2 -> u = x ^+ r,
          'Ohm_1(G) = <[x ^+ r]> /\ 'Ohm_2(G) = G
         & forall k, k > 0 -> 'Mho^k(G) = <[x ^+ (2 ^ k)]>],
      [/\ yG :|: xyG = G :\: X /\ [disjoint yG & xyG]
        & forall M, maximal M G = pred3 X My Mxy M]
    & n > 3 ->
     [/\ My \isog 'Q_q, Mxy \isog 'Q_q
       & forall U, cyclic U -> U \subset G -> #|G : U| = 2 -> U = X]].
Proof.
move=> n_gt2 genG isoG; have [def2q def2r ltqm ltrq] := def2qr (ltnW n_gt2).
have [oG Gx ox X'y] := genG; rewrite -/m -/q -/X in oG ox X'y.
case/extremal_generators_facts: genG; rewrite -/X // => pG maxX nsXG defXY nXY.
have [sXG nXG]:= andP nsXG; have [Gy notXy]:= setDP X'y.
have oxr: #[x ^+ r] = 2 by rewrite orderXdiv ox -def2r ?dvdn_mull ?mulnK.
have ox2: #[x ^+ 2] = r by rewrite orderXdiv ox -def2r ?dvdn_mulr ?mulKn.
have [[u v] [_ Gu ou U'v] [ov v2 uv]] := generators_quaternion n_gt2 isoG.
have defUv: <[u]> :* v = G :\: <[u]>.
  apply: rcoset_index2; rewrite -?divgS ?cycle_subG //.
  by rewrite oG -orderE ou -def2q mulnK.
have invUV: {in <[u]> & <[u]> :* v, forall z t, z ^ t = z^-1}.
  move=> z t; case/cycleP=> i ->; case/rcosetP=> ?; case/cycleP=> j -> ->{z t}.
  by rewrite conjgM {2}/conjg commuteX2 // mulKg conjXg uv expVgn.
have U'2: {in <[u]> :* v, forall t, t ^+ 2 = u ^+ r}.
  move=> t; case/rcosetP=> z Uz ->; rewrite expgS {1}(conjgC z) -mulgA.
  by rewrite invUV ?rcoset_refl // mulKg -(expgS v 1) v2.
have our: #[u ^+ r] = 2 by rewrite orderXdiv ou -/q -def2r ?dvdn_mull ?mulnK.
have def_ur: {in G, forall t, #[t] = 2 -> t = u ^+ r}.
  move=> t Gt /= ot; case Ut: (t \in <[u]>); last first.
    move/eqP: ot; rewrite eqn_dvd order_dvdn -order_eq1 U'2 ?our //.
    by rewrite defUv inE Ut.
  have p2u: 2.-elt u by rewrite /p_elt ou pnat_exp.
  have: t \in 'Ohm_1(<[u]>).
    by rewrite (OhmE _ p2u) mem_gen // inE Ut -order_dvdn ot.
  rewrite (Ohm_p_cycle _ p2u) ou pfactorK // subn1 -/r cycle_traject our !inE.
  by rewrite -order_eq1 ot /= mulg1; move/eqP.
have defU: n > 3 -> {in G, forall z, #[z] = q -> <[z]> = <[u]>}.
  move=> n_gt3 z Gz oz; apply/eqP; rewrite eqEcard -!orderE oz cycle_subG.
  rewrite ou leqnn andbT; apply: contraLR n_gt3 => notUz.
  rewrite -(ltn_predK n_gt2) ltnS -(@ltn_exp2l 2) // -/q -oz.
  by rewrite (@orderXprime _ 2 2) // U'2 // defUv inE notUz.
have def_xr: x ^+ r = u ^+ r by apply: def_ur; rewrite ?groupX.
have X'2: {in G :\: X, forall t, t ^+ 2 = u ^+ r}.
  case: (ltngtP n 3) => [|n_gt3|n3 t]; first by rewrite ltnNge n_gt2.
    by rewrite /X defU // -defUv.
  case/setDP=> Gt notXt.
  case Ut: (t \in <[u]>); last by rewrite U'2 // defUv inE Ut.
  rewrite [t ^+ 2]def_ur ?groupX //.
  have:= order_dvdG Ut; rewrite -orderE ou /q n3 dvdn_divisors ?inE //=.
  rewrite order_eq1 (negbTE (group1_contra notXt)) /=.
  case/pred2P=> oz; last by rewrite orderXdiv oz.
  by rewrite [t]def_ur // -def_xr mem_cycle in notXt.
have oX': {in G :\: X, forall z, #[z] = 4}.
  by move=> t X't /=; rewrite (@orderXprime _ 2 2) // X'2.
have defZ: 'Z(G) = <[x ^+ r]>.
  apply/eqP; rewrite eqEcard andbC -orderE oxr -{1}(setIidPr (center_sub G)).
  rewrite cardG_gt1 /= nil_meet_Z ?(pgroup_nil pG) //; last first.
    by rewrite -cardG_gt1 oG (leq_trans _ ltqm).
  apply/subsetP=> z; case/setIP=> Gz cGz; have [Gv _]:= setDP U'v.
  case Uvz: (z \in <[u]> :* v).
    move/eqP: (invUV _ _ (cycle_id u) Uvz).
    rewrite /conjg -(centP cGz) // mulKg eq_sym eq_invg_mul -(order_dvdn _ 2).
    by rewrite ou pfactor_dvdn // -(subnKC n_gt2).
  move/idPn: Uvz; rewrite defUv inE Gz andbT negbK def_xr => Uz.
  have p_u: 2.-elt u := mem_p_elt pG Gu.
  suff: z \in 'Ohm_1(<[u]>) by rewrite (Ohm_p_cycle 1 p_u) ou pfactorK // subn1.
  rewrite (OhmE _ p_u) mem_gen // inE Uz /= -eq_invg_mul.
  by rewrite -(invUV _ v) ?rcoset_refl // /conjg (centP cGz) ?mulKg.
have{invUV} invXX': {in X & G :\: X, forall z t, z ^ t = z^-1}.
  case: (ltngtP n 3) => [|n_gt3|n3 t z Xt]; first by rewrite ltnNge n_gt2.
    by rewrite /X defU // -defUv.
  case/setDP=> Gz notXz; rewrite /q /r n3 /= in oxr ox.
  suff xz: x ^ z = x^-1 by case/cycleP: Xt => i ->; rewrite conjXg xz expVgn.
  have: x ^ z \in X by rewrite memJ_norm ?cycle_id ?(subsetP nXG).
  rewrite invg_expg /X cycle_traject ox !inE /= !mulg1 -order_eq1 orderJ ox /=.
  case/or3P; move/eqP=> //; last by move/(congr1 order); rewrite orderJ ox oxr.
  move/conjg_fixP; rewrite (sameP commgP cent1P) cent1C -cent_cycle -/X => cXz.
  have defXz: X * <[z]> = G by rewrite (mulg_normal_maximal nsXG) ?cycle_subG.
  have: z \in 'Z(G) by rewrite inE Gz -defXz centM inE cXz cent_cycle cent1id.
  by rewrite defZ => Xr_z; rewrite (subsetP (cycleX x r)) in notXz.
have nXiG: forall k, G \subset 'N(<[x ^+ k]>).
  move=> k; apply: char_norm_trans nXG.
  by rewrite cycle_subgroup_char // cycle_subG mem_cycle.
have memL: forall i, x ^+ (2 ^ i) \in 'L_i.+1(G).
  elim=> // i IHi; rewrite -groupV expnSr expgn_mul invMg.
  by rewrite -{2}(invXX' _ y) ?mem_cycle ?cycle_id ?mem_commg.
have defG': G^`(1) = <[x ^+ 2]>.
  apply/eqP; rewrite eqEsubset cycle_subG (memL 1%N) ?der1_min //=.
  rewrite (p2group_abelian (quotient_pgroup _ pG)) ?card_quotient //=.
  rewrite -divgS ?cycle_subG ?groupX // oG -orderE ox2.
  by rewrite -def2q -def2r mulnA mulnK.
have defG1: 'Mho^1(G) = <[x ^+ 2]>.
  apply/eqP; rewrite (MhoE _ pG) eqEsubset !gen_subG sub1set andbC.
  rewrite mem_gen; last exact: mem_imset.
  apply/subsetP=> z2; case/imsetP=> z Gz ->{z2}.
  case Xz: (z \in X).
    by case/cycleP: Xz => i ->; rewrite -expgn_mul mulnC expgn_mul mem_cycle.
  rewrite (X'2 z) ?inE ?Xz // -def_xr.
  by rewrite /r -(subnKC n_gt2) expnS expgn_mul mem_cycle.
have defPhi: 'Phi(G) = <[x ^+ 2]>.
  by rewrite (Phi_mulgen pG) defG' defG1 (mulgen_idPl _).
have def_tG: {in G :\: X, forall t, t ^: G = <[x ^+ 2]> :* t}.
  move=> t X't; have [Gt notXt] := setDP X't.
  have defJt: {in X, forall z, t ^ z = z ^- 2 * t}.
    move=> z Xz; rewrite /= invMg -mulgA (conjgC _ t).
    by rewrite  (invXX' _ t) ?groupV ?invgK.
  have defGt: X * <[t]> = G by rewrite (mulg_normal_maximal nsXG) ?cycle_subG.
  apply/setP=> tz; apply/imsetP/rcosetP=> [[t'z] | [z]].
    rewrite -defGt -normC ?cycle_subG ?(subsetP nXG) //.
    case/imset2P=> t' z; case/cycleP=> j -> Xz -> -> {tz t'z t'}.
    exists (z ^- 2); last by rewrite conjgM {2}/conjg commuteX // mulKg defJt.
    case/cycleP: Xz => i ->{z}.
    by rewrite groupV -expgn_mul mulnC expgn_mul mem_cycle.
  case/cycleP=> i -> -> {z tz}; exists (x ^- i); first by rewrite groupV groupX.
  by rewrite defJt ?groupV ?mem_cycle // expVgn invgK -!expgn_mul mulnC.
have defMt: {in G :\: X, forall t, <[x ^+ 2]> <*> <[t]> = <<t ^: G>>}.
  move=> t X't; have [Gt notXt] := setDP X't.
  apply/eqP; have: t \in <<t ^: G>> by rewrite mem_gen ?class_refl.
  rewrite def_tG // eqEsubset mulgen_subG !cycle_subG !gen_subG => tGt.
  rewrite tGt -(groupMr _ tGt) mem_gen ?mem_mulg ?cycle_id ?set11 //=.
  by rewrite mul_subG ?mulgen_subl // -gen_subG mulgen_subr.
have sMtG: {in G :\: X, forall t, <<t ^: G>> \subset G}.
  by move=> t; case/setDP=> Gt _; rewrite gen_subG class_subG.
have oMt: {in G :\: X, forall t, #|<<t ^: G>>| = q}.
  move=> t X't; have [Gt notXt] := setDP X't.
  rewrite -defMt // -(LaGrange (mulgen_subl _ _)) -orderE ox2 -def2r mulnC.
  congr (_ * r)%N; rewrite -card_quotient /=; last first.
    by rewrite defMt // (subset_trans _ (nXiG 2)) ?sMtG.
  rewrite mulgenC quotient_mulgen ?(subset_trans _ (nXiG 2)) ?cycle_subG //.
  rewrite quotient_cycle ?(subsetP (nXiG 2)) //= -defPhi.
  have: coset 'Phi(G) t != 1.
    apply/eqP; move/coset_idr; apply/implyP; apply: contra notXt.
    by rewrite /= defPhi ?(subsetP (nXiG 2)) //; apply: subsetP; exact: cycleX.
  by case/(abelem_order_p (Phi_quotient_abelem pG)); rewrite ?mem_quotient.
have maxMt: {in G :\: X, forall t, maximal <<t ^: G>> G}.
  move=> t X't; rewrite /= p_index_maximal -?divgS ?sMtG ?oMt //.
  by rewrite oG -def2q mulnK.
have X'xy: x * y \in G :\: X by rewrite !inE !groupMl ?cycle_id ?notXy.
have ti_yG_xyG: [disjoint yG & xyG].
  apply/pred0P=> t; rewrite /= /yG /xyG !def_tG //; apply/andP=> [[yGt]].
  rewrite rcoset_sym (rcoset_transl yGt) mem_rcoset mulgK; move/order_dvdG.
  by rewrite -orderE ox2 ox gtnNdvd.
have s_tG_X': {in G :\: X, forall t, t ^: G \subset G :\: X}.
  by move=> t X't /=; rewrite class_sub_norm // normsD ?normG.
have defX': yG :|: xyG = G :\: X.
  apply/eqP; rewrite eqEcard subUset !s_tG_X' //= -(leq_add2l q) -{1}ox orderE.
  rewrite -/X -{1}(setIidPr sXG) cardsID oG -def2q mul2n -addnn leq_add2l.
  rewrite -(leq_add2r #|yG :&: xyG|) cardsUI disjoint_setI0 // cards0 addn0.
  by rewrite /yG /xyG !def_tG // !card_rcoset addnn -mul2n -orderE ox2 def2r.
rewrite pprodE //; split=> // [|||n_gt3].
- rewrite defG'; split=> //; apply/eqP; rewrite eqn_leq.
  rewrite (leq_trans (nil_class_pgroup pG)); last first.
    by rewrite oG pfactorK // -(subnKC n_gt2).
  rewrite -(subnKC (ltnW n_gt2)) subn2 ltnNge.
  rewrite (sameP (lcn_nil_classP _ (pgroup_nil pG)) eqP).
  by apply/trivgPn; exists (x ^+ r); rewrite ?memL // -order_gt1 oxr.
- rewrite {2}def_xr defZ; split=> //; last exact: extend_cyclic_Mho.
  split; apply/eqP; last first.
    have sX'G2: {subset G :\: X <= 'Ohm_2(G)}.
      move=> z X'z; have [Gz _] := setDP X'z.
      by rewrite (OhmE 2 pG) mem_gen // inE Gz -order_dvdn oX'.
    rewrite eqEsubset Ohm_sub -{1}defXY mulG_subG !cycle_subG.
    by rewrite -(groupMr _ (sX'G2 y X'y)) !sX'G2.
  rewrite eqEsubset (OhmE 1 pG) cycle_subG gen_subG andbC.
  rewrite mem_gen ?inE ?groupX -?order_dvdn ?oxr //=.
  apply/subsetP=> t; case/setIdP=> Gt; rewrite -order_dvdn /=.
  rewrite dvdn_divisors ?inE //= order_eq1.
  case/orP; move/eqP; first by move->; exact: group1.
  by move/def_ur=> -> //; rewrite def_xr cycle_id.
- split=> //= H; apply/idP/idP=> [maxH |]; last first.
    by case/or3P; move/eqP->; rewrite ?maxMt.
  have [sHG nHG]:= andP (p_maximal_normal pG maxH).
  have oH: #|H| = q.
    apply: double_inj; rewrite -muln2 -(p_maximal_index pG maxH) LaGrange //.
    by rewrite oG -mul2n.
  rewrite !(eq_sym (gval H)) -eq_sym !eqEcard oH -orderE ox !oMt // !leqnn.
  case sHX: (H \subset X) => //=; case/subsetPn: sHX => z Hz notXz.
  have: z \in yG :|: xyG by rewrite defX' inE notXz (subsetP sHG).
  rewrite !andbT !gen_subG /yG /xyG.
  by case/setUP; move/class_transr <-; rewrite !class_sub_norm ?Hz ?orbT.
have isoMt: {in G :\: X, forall z, <<z ^: G>> \isog 'Q_q}.
  have n1_gt2: n.-1 > 2 by rewrite -(subnKC n_gt3).
  move=> z X'z /=; rewrite isogEcard card_quaternion ?oMt // leqnn andbT.
  rewrite Grp_quaternion //; apply/existsP; exists (x ^+ 2, z) => /=.
  rewrite defMt // -/q -/r !xpair_eqE -!expgn_mul def2r -order_dvdn ox dvdnn.
  rewrite -expnS prednK; last by rewrite -subn2 subn_gt0.
  by rewrite X'2 // def_xr !eqxx /= invXX' ?mem_cycle.
rewrite !isoMt //; split=> // C; case/cyclicP=> z ->{C} sCG iCG.
rewrite [X]defU // defU -?cycle_subG //.
by apply: double_inj; rewrite -muln2 -iCG LaGrange // oG -mul2n.
Qed.

Theorem semidihedral_structure :
    n > 3 -> extremal_generators G 2 n (x, y) -> G \isog 'SD_m -> #[y] = 2 ->
  [/\ [/\ X ><| Y = G, #[x * y] = 4
        & {in X & G :\: X, forall z t, z ^ t = z ^+ r.-1}],
      [/\ G ^`(1) = <[x ^+ 2]>, 'Phi(G) = G ^`(1), #|G^`(1)| = r
        & nil_class G = n.-1],
      [/\ 'Z(G) = <[x ^+ r]>, #|'Z(G)| = 2,
          'Ohm_1(G) = My /\ 'Ohm_2(G) = G
         & forall k, k > 0 -> 'Mho^k(G) = <[x ^+ (2 ^ k)]>],
      [/\ yG :|: xyG = G :\: X /\ [disjoint yG & xyG]
        & forall H, maximal H G = pred3 X My Mxy H]
    & [/\ My \isog 'D_q, Mxy \isog 'Q_q
       & forall U, cyclic U -> U \subset G -> #|G : U| = 2 -> U = X]].
Proof.
move=> n_gt3 genG isoG oy.
have [def2q def2r ltqm ltrq] := def2qr (ltnW (ltnW n_gt3)).
have [oG Gx ox X'y] := genG; rewrite -/m -/q -/X in oG ox X'y.
case/extremal_generators_facts: genG; rewrite -/X // => pG maxX nsXG defXY nXY.
have [sXG nXG]:= andP nsXG; have [Gy notXy]:= setDP X'y.
have ox2: #[x ^+ 2] = r by rewrite orderXdiv ox -def2r ?dvdn_mulr ?mulKn.
have oxr: #[x ^+ r] = 2 by rewrite orderXdiv ox -def2r ?dvdn_mull ?mulnK.
have [[u v] [_ Gu ou U'v] [ov uv]] := generators_semidihedral n_gt3 isoG.
have defUv: <[u]> :* v = G :\: <[u]>.
  apply: rcoset_index2; rewrite -?divgS ?cycle_subG //.
  by rewrite oG -orderE ou -def2q mulnK.
have invUV: {in <[u]> & <[u]> :* v, forall z t, z ^ t = z ^+ r.-1}.
  move=> z t; case/cycleP=> i ->; case/rcosetP=> ?; case/cycleP=> j -> ->{z t}.
  by rewrite conjgM {2}/conjg commuteX2 // mulKg conjXg uv -!expgn_mul mulnC.
have [vV yV]: v^-1 = v /\ y^-1 = y by rewrite !invg_expg ov oy.
have defU: {in G, forall z, #[z] = q -> <[z]> = <[u]>}.
  move=> z Gz /= oz; apply/eqP; rewrite eqEcard -!orderE oz ou leqnn andbT.
  apply: contraLR (n_gt3) => notUz; rewrite -leqNgt -(ltn_predK n_gt3) ltnS.
  rewrite -(@dvdn_Pexp2l 2) // -/q -{}oz order_dvdn expgn_mul (expgS z).
  have{Gz notUz} [z' Uz' ->{z}]: exists2 z', z' \in <[u]> & z = z' * v.
    by apply/rcosetP; rewrite defUv inE -cycle_subG notUz Gz.
  rewrite {2}(conjgC z') invUV ?rcoset_refl // mulgA -{2}vV mulgK -expgS.
  by rewrite prednK // -expgn_mul mulnC def2r -order_dvdn /q -ou order_dvdG.
have{invUV} invXX': {in X & G :\: X, forall z t, z ^ t = z ^+ r.-1}.
  by rewrite /X defU -?defUv.
have xy2: (x * y) ^+ 2 = x ^+ r.
  rewrite expgS {2}(conjgC x) invXX' ?cycle_id // mulgA -{2}yV mulgK -expgS.
  by rewrite prednK.
have oxy: #[x * y] = 4 by rewrite (@orderXprime _ 2 2) ?xy2.
have r_gt2: r > 2 by rewrite (ltn_exp2l 1) // -(subnKC n_gt3).
have coXr1: coprime #[x] (2 ^ (n - 3)).-1.
  rewrite ox coprime_expl // -(@coprime_pexpl (n - 3)) ?coprimenP ?subn_gt0 //.
  by rewrite expn_gt0.
have def2r1: (2 * (2 ^ (n - 3)).-1).+1 = r.-1.
  rewrite -!subn1 muln_subr -expnS -[_.+1]ltn_subS ?(ltn_exp2l 0) //.
  by rewrite /r -(subnKC n_gt3).
have defZ: 'Z(G) = <[x ^+ r]>.
  apply/eqP; rewrite eqEcard andbC -orderE oxr -{1}(setIidPr (center_sub G)).
  rewrite cardG_gt1 /= nil_meet_Z ?(pgroup_nil pG) //; last first.
    by rewrite -cardG_gt1 oG (leq_trans _ ltqm).
  apply/subsetP=> z; case/setIP=> Gz cGz.
  case X'z: (z \in G :\: X).
    move/eqP: (invXX' _ _ (cycle_id x) X'z).
    rewrite /conjg -(centP cGz) // mulKg -def2r1 eq_mulVg1 expgS mulKg mulnC.
    by rewrite -order_dvdn gauss // order_dvdn -order_eq1 ox2 -(subnKC r_gt2).
  move/idPn: X'z; rewrite inE Gz andbT negbK => Xz.
  have:= Ohm_p_cycle 1 (mem_p_elt pG Gx); rewrite ox pfactorK // subn1 => <-.
  rewrite (OhmE _ (mem_p_elt pG Gx)) mem_gen // inE Xz /=.
  rewrite -(expgnK coXr1 Xz) -!expgn_mul mulnCA -order_dvdn dvdn_mull //.
  rewrite mulnC order_dvdn -(inj_eq (mulgI z)) -expgS mulg1 def2r1.
  by rewrite -(invXX' z y) // /conjg (centP cGz) ?mulKg.
have nXiG: forall k, G \subset 'N(<[x ^+ k]>).
  move=> k; apply: char_norm_trans nXG.
  by rewrite cycle_subgroup_char // cycle_subG mem_cycle.
have memL: forall i, x ^+ (2 ^ i) \in 'L_i.+1(G).
  elim=> // i IHi; rewrite -(expgnK coXr1 (mem_cycle _ _)) groupX //.
  rewrite -expgn_mul expnSr -mulnA expgn_mul -(mulKg (x ^+ (2 ^ i)) (_ ^+ _)).
  by rewrite -expgS def2r1 -(invXX' _ y) ?mem_cycle ?mem_commg.
have defG': G^`(1) = <[x ^+ 2]>.
  apply/eqP; rewrite eqEsubset cycle_subG (memL 1%N) ?der1_min //=.
  rewrite (p2group_abelian (quotient_pgroup _ pG)) ?card_quotient //=.
  rewrite -divgS ?cycle_subG ?groupX // oG -orderE ox2.
  by rewrite -def2q -def2r mulnA mulnK.
have defG1: 'Mho^1(G) = <[x ^+ 2]>.
  apply/eqP; rewrite (MhoE _ pG) eqEsubset !gen_subG sub1set andbC.
  rewrite mem_gen; last exact: mem_imset.
  apply/subsetP=> z2; case/imsetP=> z Gz ->{z2}.
  case Xz: (z \in X).
    by case/cycleP: Xz => i ->; rewrite -expgn_mul mulnC expgn_mul mem_cycle.
  have{Xz Gz} [xi Xxi ->{z}]: exists2 xi, xi \in X & z = xi * y.
    have Uvy: y \in <[u]> :* v by rewrite defUv -(defU x).
    apply/rcosetP; rewrite /X defU // (rcoset_transl Uvy) defUv.
    by rewrite inE -(defU x) ?Xz.
  rewrite expn1 expgS {2}(conjgC xi) -{2}[y]/(y ^+ 2.-1) -{1}oy -invg_expg.
  rewrite mulgA mulgK invXX' // -expgS prednK // /r -(subnKC n_gt3) expnS.
  by case/cycleP: Xxi => i ->; rewrite -expgn_mul mulnCA expgn_mul mem_cycle.
have defPhi: 'Phi(G) = <[x ^+ 2]>.
  by rewrite (Phi_mulgen pG) defG' defG1 (mulgen_idPl _).
have def_tG: {in G :\: X, forall t, t ^: G = <[x ^+ 2]> :* t}.
  move=> t X't; have [Gt notXt] := setDP X't.
  have defJt: {in X, forall z, t ^ z = z ^+ r.-2 * t}.
    move=> z Xz /=; rewrite -(mulKg z (z ^+ _)) -expgS -subn2.
    have X'tV: t^-1 \in G :\: X by rewrite inE !groupV notXt.
    by rewrite -ltn_subS 1?ltnW // subn1 -(invXX' _ t^-1) // -mulgA -conjgCV.
  have defGt: X * <[t]> = G by rewrite (mulg_normal_maximal nsXG) ?cycle_subG.
  apply/setP=> tz; apply/imsetP/rcosetP=> [[t'z] | [z]].
    rewrite -defGt -normC ?cycle_subG ?(subsetP nXG) //.
    case/imset2P=> t' z; case/cycleP=> j -> Xz -> -> {t' t'z tz}.
    exists (z ^+ r.-2); last first.
      by rewrite conjgM {2}/conjg commuteX // mulKg defJt.
    case/cycleP: Xz => i ->{z}.
    by rewrite -def2r1 -expgn_mul mulnCA expgn_mul mem_cycle.
  case/cycleP=> i -> -> {z tz}.
  exists (x ^+ (i * expgn_inv X (2 ^ (n - 3)).-1)); first by rewrite groupX.
  rewrite defJt ?mem_cycle // -def2r1 -!expgn_mul.
  by rewrite mulnAC mulnA mulnC muln2 !expgn_mul expgnK ?mem_cycle.
have defMt: {in G :\: X, forall t, <[x ^+ 2]> <*> <[t]> = <<t ^: G>>}.
  move=> t X't; have [Gt notXt] := setDP X't.
  apply/eqP; have: t \in <<t ^: G>> by rewrite mem_gen ?class_refl.
  rewrite def_tG // eqEsubset mulgen_subG !cycle_subG !gen_subG => tGt.
  rewrite tGt -(groupMr _ tGt) mem_gen ?mem_mulg ?cycle_id ?set11 //=.
  by rewrite mul_subG ?mulgen_subl // -gen_subG mulgen_subr.
have sMtG: {in G :\: X, forall t, <<t ^: G>> \subset G}.
  by move=> t; case/setDP=> Gt _; rewrite gen_subG class_subG.
have oMt: {in G :\: X, forall t, #|<<t ^: G>>| = q}.
  move=> t X't; have [Gt notXt] := setDP X't.
  rewrite -defMt // -(LaGrange (mulgen_subl _ _)) -orderE ox2 -def2r mulnC.
  congr (_ * r)%N; rewrite -card_quotient /=; last first.
    by rewrite defMt // (subset_trans _ (nXiG 2)) ?sMtG.
  rewrite mulgenC quotient_mulgen ?(subset_trans _ (nXiG 2)) ?cycle_subG //.
  rewrite quotient_cycle ?(subsetP (nXiG 2)) //= -defPhi.
  have: coset 'Phi(G) t != 1.
    apply/eqP; move/coset_idr; apply/implyP; apply: contra notXt.
    by rewrite /= defPhi ?(subsetP (nXiG 2)) //; apply: subsetP; exact: cycleX.
  by case/(abelem_order_p (Phi_quotient_abelem pG)); rewrite ?mem_quotient.
have maxMt: {in G :\: X, forall t, maximal <<t ^: G>> G}.
  move=> t X't /=; rewrite p_index_maximal -?divgS ?sMtG ?oMt //.
  by rewrite oG -def2q mulnK.
have X'xy: x * y \in G :\: X by rewrite !inE !groupMl ?cycle_id ?notXy.
have ti_yG_xyG: [disjoint yG & xyG].
  apply/pred0P=> t; rewrite /= /yG /xyG !def_tG //; apply/andP=> [[yGt]].
  rewrite rcoset_sym (rcoset_transl yGt) mem_rcoset mulgK; move/order_dvdG.
  by rewrite -orderE ox2 ox gtnNdvd.
have s_tG_X': {in G :\: X, forall t, t ^: G \subset G :\: X}.
  by move=> t X't /=; rewrite class_sub_norm // normsD ?normG.
have defX': yG :|: xyG = G :\: X.
  apply/eqP; rewrite eqEcard subUset !s_tG_X' //= -(leq_add2l q) -{1}ox orderE.
  rewrite -/X -{1}(setIidPr sXG) cardsID oG -def2q mul2n -addnn leq_add2l.
  rewrite -(leq_add2r #|yG :&: xyG|) cardsUI disjoint_setI0 // cards0 addn0.
  by rewrite /yG /xyG !def_tG // !card_rcoset addnn -mul2n -orderE ox2 def2r.
split.
- by rewrite sdprodE // setIC prime_TIg ?cycle_subG // -orderE oy.
- rewrite defG'; split=> //.
  apply/eqP; rewrite eqn_leq (leq_trans (nil_class_pgroup pG)); last first.
    by rewrite oG pfactorK // -(subnKC n_gt3).
  rewrite -(subnKC (ltnW (ltnW n_gt3))) subn2 ltnNge.
  rewrite (sameP (lcn_nil_classP _ (pgroup_nil pG)) eqP).
  by apply/trivgPn; exists (x ^+ r); rewrite ?memL // -order_gt1 oxr.
- rewrite defZ; split=> //; last exact: extend_cyclic_Mho.
  split; apply/eqP; last first.
    have sX'G2: {subset G :\: X <= 'Ohm_2(G)}.
      move=> t X't; have [Gt _] := setDP X't; rewrite -defX' in X't.
      rewrite (OhmE 2 pG) mem_gen // inE Gt -order_dvdn.
      by case/setUP: X't; case/imsetP=> z _ ->; rewrite orderJ ?oy ?oxy.
    rewrite eqEsubset Ohm_sub -{1}defXY mulG_subG !cycle_subG.
    by rewrite -(groupMr _ (sX'G2 y X'y)) !sX'G2.
  rewrite eqEsubset andbC gen_subG class_sub_norm ?gfunc.bgFunc_norm //.
  rewrite (OhmE 1 pG) mem_gen ?inE ?Gy -?order_dvdn ?oy // gen_subG /= -/My.
  apply/subsetP=> t; case/setIdP=> Gt t2; have p_x := pgroupS sXG pG.
  case Xt: (t \in X).
    have: t \in 'Ohm_1(X) by rewrite (OhmE 1 p_x) mem_gen ?inE ?Xt.
    apply: subsetP; rewrite (Ohm_p_cycle 1 p_x) ox pfactorK //.
    rewrite -(subnKC n_gt3) expgn_mul (subset_trans (cycleX _ _)) //.
    by rewrite /My -defMt ?mulgen_subl.
  have{Xt}: t \in yG :|: xyG by rewrite defX' inE Xt.
  case/setUP; first exact: mem_gen.
  by case/imsetP=> z _ def_t; rewrite -order_dvdn def_t orderJ oxy in t2.
- split=> //= H; apply/idP/idP=> [maxH |]; last first.
    by case/or3P; move/eqP->; rewrite ?maxMt.
  have [sHG nHG]:= andP (p_maximal_normal pG maxH).
  have oH: #|H| = q.
    apply: double_inj; rewrite -muln2 -(p_maximal_index pG maxH) LaGrange //.
    by rewrite oG -mul2n.
  rewrite !(eq_sym (gval H)) -eq_sym !eqEcard oH -orderE ox !oMt // !leqnn.
  case sHX: (H \subset X) => //=; case/subsetPn: sHX => t Ht notXt.
  have: t \in yG :|: xyG by rewrite defX' inE notXt (subsetP sHG).
  rewrite !andbT !gen_subG /yG /xyG.
  by case/setUP; move/class_transr <-; rewrite !class_sub_norm ?Ht ?orbT.
have n1_gt2: n.-1 > 2 by [rewrite -(subnKC n_gt3)]; have n1_gt1 := ltnW n1_gt2.
rewrite !isogEcard card_2dihedral ?card_quaternion ?oMt // leqnn !andbT.
have invX2X': {in G :\: X, forall t, x ^+ 2 ^ t == x ^- 2}.
  move=> t X't; rewrite /= invXX' ?mem_cycle // eq_sym eq_invg_mul -expgS.
  by rewrite prednK // -order_dvdn ox2.
rewrite Grp_2dihedral ?Grp_quaternion //; split=> [||C].
- apply/existsP; exists (x ^+ 2, y); rewrite /= defMt // !xpair_eqE.
  by rewrite -!expgn_mul def2r -!order_dvdn ox oy dvdnn eqxx /= invX2X'.
- apply/existsP; exists (x ^+ 2, x * y); rewrite /= defMt // !xpair_eqE.
  rewrite -!expgn_mul def2r -order_dvdn ox xy2 dvdnn eqxx invX2X' //=.
  by rewrite andbT /r -(subnKC n_gt3).
case/cyclicP=> z ->{C} sCG iCG; rewrite [X]defU // defU -?cycle_subG //.
by apply: double_inj; rewrite -muln2 -iCG LaGrange // oG -mul2n.
Qed.

End ExtremalStructure.

Section ExtremalClass.

Variables (gT : finGroupType) (G : {group gT}).

Inductive extremal_group_type :=
  ModularGroup | Dihedral | SemiDihedral | Quaternion | NotExtremal.

Definition index_extremal_group_type c :=
  match c with
  | ModularGroup => 0
  | Dihedral => 1
  | SemiDihedral => 2
  | Quaternion => 3
  | NotExtremal => 4
  end%N.

Definition enum_extremal_groups :=
  [:: ModularGroup; Dihedral; SemiDihedral; Quaternion].

Lemma cancel_index_extremal_groups :
  cancel index_extremal_group_type (nth NotExtremal enum_extremal_groups).
Proof. by case. Qed.
Local Notation extgK := cancel_index_extremal_groups.

Import choice.

Definition extremal_group_eqMixin := CanEqMixin extgK.
Canonical Structure extremal_group_eqType := EqType _ extremal_group_eqMixin.
Definition extremal_group_choiceMixin := CanChoiceMixin extgK.
Canonical Structure extremal_group_choiceType :=
  ChoiceType _ extremal_group_choiceMixin.
Definition extremal_group_countMixin := CanCountMixin extgK.
Canonical Structure extremal_group_countType :=
  CountType _ extremal_group_countMixin.
Lemma bound_extremal_groups : forall c : extremal_group_type, pickle c < 6.
Proof. by case. Qed.
Definition extremal_group_finMixin := Finite.CountMixin bound_extremal_groups.
Canonical Structure extremal_group_finType := FinType _ extremal_group_finMixin.

Definition extremal_class (A : {set gT}) :=
  let m := #|A| in let p := pdiv m in let n := logn p m in
  if (n > 1) && (A \isog 'D_(2 ^ n)) then Dihedral else
  if (n > 2) && (A \isog 'Q_(2 ^ n)) then Quaternion else
  if (n > 3) && (A \isog 'SD_(2 ^ n)) then SemiDihedral else
  if (n > 2) && (A \isog 'Mod_(p ^ n)) then ModularGroup else
  NotExtremal.

Definition extremal2 A := extremal_class A \in behead enum_extremal_groups.

Lemma dihedral_classP :
  extremal_class G = Dihedral <-> (exists2 n, n > 1 & G \isog 'D_(2 ^ n)).
Proof.
rewrite /extremal_class; split=> [ | [n n_gt1 isoG]].
  by move: (logn _ _) => n; do 4?case: ifP => //; case/andP; exists n.
rewrite (isog_card isoG) card_2dihedral // -(ltn_predK n_gt1) pdiv_pfactor //.
by rewrite pfactorK // (ltn_predK n_gt1) n_gt1 isoG.
Qed.

Lemma quaternion_classP :
  extremal_class G = Quaternion <-> (exists2 n, n > 2 & G \isog 'Q_(2 ^ n)).
Proof.
rewrite /extremal_class; split=> [ | [n n_gt2 isoG]].
  by move: (logn _ _) => n; do 4?case: ifP => //; case/andP; exists n.
rewrite (isog_card isoG) card_quaternion // -(ltn_predK n_gt2) pdiv_pfactor //.
rewrite pfactorK // (ltn_predK n_gt2) n_gt2 isoG.
case: andP => // [[n_gt1 isoGD]].
have [[x y] genG [oy _ _]]:= generators_quaternion n_gt2 isoG.
have [_ _ _ X'y] := genG.
by case/dihedral2_structure: genG oy => // [[_ ->]].
Qed.

Lemma semidihedral_classP :
  extremal_class G = SemiDihedral <-> (exists2 n, n > 3 & G \isog 'SD_(2 ^ n)).
Proof.
rewrite /extremal_class; split=> [ | [n n_gt3 isoG]].
  by move: (logn _ _) => n; do 4?case: ifP => //; case/andP; exists n.
rewrite (isog_card isoG) card_semidihedral //.
rewrite -(ltn_predK n_gt3) pdiv_pfactor // pfactorK // (ltn_predK n_gt3) n_gt3.
have [[x y] genG [oy _]]:= generators_semidihedral n_gt3 isoG.
have [_ Gx _ X'y]:= genG.
case: andP => [[n_gt1 isoGD]|_].
  have [[_ oxy _ _] _ _ _]:= semidihedral_structure n_gt3 genG isoG oy.
  case: (dihedral2_structure n_gt1 genG isoGD) oxy => [[_ ->]] //.
  by rewrite !inE !groupMl ?cycle_id in X'y *.
case: andP => // [[n_gt2 isoGQ]|]; last by rewrite isoG.
by case: (quaternion_structure n_gt2 genG isoGQ) oy => [[_ ->]].
Qed.

Lemma odd_not_extremal2 : odd #|G| -> ~~ extremal2 G.
Proof.
rewrite /extremal2 /extremal_class; case: logn => // n'.
case: andP => [[n_gt1 isoG] | _].
  by rewrite (isog_card isoG) card_2dihedral ?odd_exp.
case: andP => [[n_gt2 isoG] | _].
  by rewrite (isog_card isoG) card_quaternion ?odd_exp.
case: andP => [[n_gt3 isoG] | _].
  by rewrite (isog_card isoG) card_semidihedral ?odd_exp.
by case: ifP.
Qed.

Lemma modular_group_classP :
  extremal_class G = ModularGroup
     <-> (exists2 p, prime p &
          exists2 n, n >= (p == 2) + 3 & G \isog 'Mod_(p ^ n)).
Proof.
rewrite /extremal_class; split=> [ | [p p_pr [n n_gt23 isoG]]].
  move: (pdiv _) => p; set n := logn p _; do 4?case: ifP => //.
  case/andP=> n_gt2 isoG _ _; rewrite ltnW //= => not_isoG _.
  exists p; first by move: n_gt2; rewrite /n lognE; case (prime p).
  exists n => //; case: eqP => // p2; rewrite ltn_neqAle; case: eqP => // n3.
  by case/idP: not_isoG; rewrite p2 -n3 in isoG *.
have n_gt2 := leq_trans (leq_addl _ _) n_gt23; have n_gt1 := ltnW n_gt2.
have n_gt0 := ltnW n_gt1; have def_n := prednK n_gt0.
have [[x y] genG mod_xy] := generators_modular_group p_pr n_gt2 isoG.
case/modular_group_structure: (genG) => // _ _ [_ _ nil2G] _ _.
have [oG _ _ _] := genG; have [oy _] := mod_xy.
rewrite oG -def_n pdiv_pfactor // def_n pfactorK // n_gt1 n_gt2 {}isoG /=.
case: (ltngtP p 2) => [|p_gt2|p2]; first by rewrite ltnNge prime_gt1.
  rewrite !(isog_sym G) !isogEcard card_2dihedral ?card_quaternion //= oG.
  rewrite leq_exp2r // leqNgt p_gt2 !andbF; case: and3P=> // [[n_gt3 _]].
  by rewrite card_semidihedral // leq_exp2r // leqNgt p_gt2.
rewrite p2 in genG oy n_gt23; rewrite n_gt23.
have: nil_class G <> n.-1.
  by apply/eqP; rewrite neq_ltn -ltnS nil2G def_n n_gt23.
case: ifP => [isoG | _]; first by case/dihedral2_structure: genG => // _ [].
case: ifP => [isoG | _]; first by case/quaternion_structure: genG => // _ [].
by case: ifP => // isoG; case/semidihedral_structure: genG => // _ [].
Qed.

End ExtremalClass.

Theorem extremal2_structure : forall (gT : finGroupType) (G : {group gT}) n x y,
  let cG := extremal_class G in
  let m := (2 ^ n)%N in let q := (2 ^ n.-1)%N in let r := (2 ^ n.-2)%N in
  let X := <[x]> in let yG := y ^: G in let xyG := (x * y) ^: G in
  let My := <<yG>> in let Mxy := <<xyG>> in
     extremal_generators G 2 n (x, y) ->
     extremal2 G -> (cG == SemiDihedral) ==> (#[y] == 2) ->
 [/\ [/\ (if cG == Quaternion then pprod X <[y]> else X ><| <[y]>) = G,
         if cG == SemiDihedral then #[x * y] = 4 else
           {in G :\: X, forall z, #[z] = (if cG == Dihedral then 2 else 4)},
         if cG != Quaternion then True else
         {in G, forall z, #[z] = 2 -> z = x ^+ r}
       & {in X & G :\: X, forall t z,
            t ^ z = (if cG == SemiDihedral then t ^+ r.-1 else t^-1)}],
      [/\ G ^`(1) = <[x ^+ 2]>, 'Phi(G) = G ^`(1), #|G^`(1)| = r
        & nil_class G = n.-1],
      [/\ if n > 2 then 'Z(G) = <[x ^+ r]> /\ #|'Z(G)| = 2 else 2.-abelem G,
          'Ohm_1(G) = (if cG == Quaternion then <[x ^+ r]> else
                       if cG == SemiDihedral then My else G),
          'Ohm_2(G) = G
        & forall k, k > 0 -> 'Mho^k(G) = <[x ^+ (2 ^ k)]>],
     [/\ yG :|: xyG = G :\: X, [disjoint yG & xyG]
       & forall H : {group gT}, maximal H G = (gval H \in pred3 X My Mxy)]
   & if n <= (cG == Quaternion) + 2 then True else
     [/\ forall U, cyclic U -> U \subset G -> #|G : U| = 2 -> U = X,
         if cG == Quaternion then My \isog 'Q_q else My \isog 'D_q,
         extremal_class My = (if cG == Quaternion then cG else Dihedral),
         if cG == Dihedral then Mxy \isog 'D_q else Mxy \isog 'Q_q
       & extremal_class Mxy = (if cG == Dihedral then cG else Quaternion)]].
Proof.
move=> gT G n x y cG m q r X yG xyG My Mxy genG; have [oG _ _ _] := genG.
have logG: logn (pdiv #|G|) #|G| = n by rewrite oG pfactorKpdiv.
rewrite /extremal2 -/cG; do [rewrite {1}/extremal_class /= {}logG] in cG *.
case: ifP => [isoG | _] in cG * => [_ _ /=|].
  case/andP: isoG => n_gt1 isoG.
  have:= dihedral2_structure n_gt1 genG isoG; rewrite -/X -/q -/r -/yG -/xyG.
  case=> [[defG oX' invXX'] nilG [defOhm defMho] maxG defZ].
  rewrite eqn_leq n_gt1 andbT add0n in defZ *; split=> //.
    split=> //; first by case: leqP defZ => // _ [].
    by apply/eqP; rewrite eqEsubset Ohm_sub -{1}defOhm Ohm_leq.
  case: leqP defZ => // n_gt2 [_ _ isoMy isoMxy defX].
  have n1_gt1: n.-1 > 1 by rewrite -(subnKC n_gt2).
  by split=> //; apply/dihedral_classP; exists n.-1.
case: ifP => [isoG | _] in cG * => [_ _ /=|].
  case/andP: isoG => n_gt2 isoG; rewrite n_gt2 add1n.
  have:= quaternion_structure n_gt2 genG isoG; rewrite -/X -/q -/r -/yG -/xyG.
  case=> [[defG oX' invXX'] nilG [defZ oZ def2 [-> ->] defMho]].
  case=> [[-> ->] maxG] isoM; split=> //.
  case: leqP isoM => // n_gt3 [//|isoMy isoMxy defX].
  have n1_gt2: n.-1 > 2 by rewrite -(subnKC n_gt3).
  by split=> //; apply/quaternion_classP; exists n.-1.
do [case: ifP => [isoG | _]; last by case: ifP] in cG * => /= _; move/eqnP=> oy.
case/andP: isoG => n_gt3 isoG; rewrite (leqNgt n) (ltnW n_gt3) /=.
have n1_gt2: n.-1 > 2 by rewrite -(subnKC n_gt3).
have:= semidihedral_structure n_gt3 genG isoG oy.
rewrite -/X -/q -/r -/yG -/xyG -/My -/Mxy.
case=> [[defG oxy invXX'] nilG [defZ oZ [-> ->] defMho] [[defX' tiX'] maxG]].
case=> isoMy isoMxy defX; do 2!split=> //.
  by apply/dihedral_classP; exists n.-1; first exact: ltnW.
by apply/quaternion_classP; exists n.-1.
Qed.

(* This is Aschbacher (23.4).  *)
Lemma maximal_cycle_extremal : forall gT p (G X : {group gT}),
    p.-group G -> ~~ abelian G -> cyclic X -> X \subset G -> #|G : X| = p ->
  (extremal_class G == ModularGroup) || (p == 2) && extremal2 G.
Proof.
move=> gT p G X pG not_cGG cycX sXG iXG.
rewrite /extremal2; set cG := extremal_class G.
have [|p_pr _ _] := pgroup_pdiv pG.
  by case: eqP not_cGG => // ->; rewrite abelian1.
have p_gt1 := prime_gt1 p_pr; have p_gt0 := ltnW p_gt1.
have [n oG] := p_natP pG; have n_gt2: n > 2.
  apply: contraR not_cGG; rewrite -leqNgt => n_le2.
  by rewrite (p2group_abelian pG) // oG pfactorK.
have def_n := subnKC n_gt2; have n_gt1 := ltnW n_gt2; have n_gt0 := ltnW n_gt1.
pose q := (p ^ n.-1)%N; pose r := (p ^ n.-2)%N.
have q_gt1: q > 1 by rewrite (ltn_exp2l 0) // -(subnKC n_gt2).
have r_gt0: r > 0 by rewrite expn_gt0 p_gt0.
have def_pr: (p * r)%N = q by rewrite /q /r -def_n.
have oX: #|X| = q by rewrite -(setIidPr sXG) -divg_index oG iXG /q -def_n mulKn.
have ntX: X :!=: 1 by rewrite -cardG_gt1 oX.
have maxX: maximal X G by rewrite p_index_maximal ?iXG.
have nsXG: X <| G := p_maximal_normal pG maxX; have [_ nXG] := andP nsXG.
have cXX: abelian X := cyclic_abelian cycX.
have scXG: 'C_G(X) = X.
  apply/eqP; rewrite eqEsubset subsetI sXG -abelianE cXX !andbT.
  apply: contraR not_cGG; case/subsetPn=> y; case/setIP=> Gy cXy notXy.
  rewrite -!cycle_subG in Gy notXy; rewrite -(mulg_normal_maximal nsXG _ Gy) //.
  by rewrite abelianM cycle_abelian cyclic_abelian // centsC cycle_subG.
have [x defX] := cyclicP X cycX; have pX := pgroupS sXG pG.
have Xx: x \in X by [rewrite defX cycle_id]; have Gx := subsetP sXG x Xx.
have [ox p_x]: #[x] = q /\ p.-elt x by rewrite defX in pX oX.
pose Z := <[x ^+ r]>.
have defZ: Z = 'Ohm_1(X) by rewrite defX (Ohm_p_cycle _ p_x) ox subn1 pfactorK.
have oZ: #|Z| = p by rewrite -orderE orderXdiv ox -def_pr ?dvdn_mull ?mulnK.
have cGZ: Z \subset 'C(G).
  have nsZG: Z <| G by rewrite defZ (char_normal_trans (Ohm_char 1 _)).
  move/implyP: (nil_meet_Z (pgroup_nil pG) nsZG); rewrite -cardG_gt1 oZ p_gt1.
  rewrite setIA (setIidPl (normal_sub nsZG)).
  by apply: contraR; move/prime_TIg=> -> //; rewrite oZ.
have X_Gp: forall y, y \in G -> y ^+ p \in X.
  move=> y Gy; have nXy: y \in 'N(X) := subsetP nXG y Gy.
  rewrite coset_idr ?groupX // morphX //; apply/eqP.
  by rewrite -order_dvdn -iXG -card_quotient // order_dvdG ?mem_quotient.
have [y X'y]: exists2 y, y \in G :\: X &
  (p == 2) + 3 <= n /\ x ^ y = x ^+ r.+1 \/ p = 2 /\ x * x ^ y \in Z.
- have [y Gy notXy]: exists2 y, y \in G & y \notin X.
    by apply/subsetPn; rewrite proper_subn ?(maxgroupp maxX).
  have nXy: y \in 'N(X) := subsetP nXG y Gy; pose ay := conj_aut X y.
  have oay: #[ay] = p.
    apply: nt_prime_order => //.
      by rewrite -morphX // mker // ker_conj_aut (subsetP cXX) ?X_Gp.
    rewrite (sameP eqP (kerP _ nXy)) ker_conj_aut.
    by apply: contra notXy => cXy; rewrite -scXG inE Gy.
  have [m []]:= cyclic_pgroup_Aut_structure pX cycX ntX.
  set Ap := 'O_p(_); case=> def_m [m1 _] [m_inj _] _ _ _.
  have sylAp: p.-Sylow(Aut X) Ap.
    by rewrite nilpotent_pcore_Hall // abelian_nil // Aut_cyclic_abelian.
  have Ap1ay: ay \in 'Ohm_1(Ap).
    rewrite (OhmE _ (pcore_pgroup _ _)) mem_gen // inE -order_dvdn oay dvdnn.
    rewrite (mem_normal_Hall sylAp) ?pcore_normal ?Aut_aut //.
    by rewrite /p_elt oay pnat_id.
  rewrite {1}oX pfactorK // -{1}def_n /=.
  have [p2 | odd_p] := even_prime p_pr; last first.
    rewrite (sameP eqP (prime_oddPn p_pr)) odd_p n_gt2.
    case=> _ [_ _ _] [_ _ [s [As os m_s defAp1]]].
    have [j def_s]: exists j, s = ay ^+ j.
      apply/cycleP; rewrite -cycle_subG subEproper eq_sym eqEcard -!orderE.
      by rewrite -defAp1 cycle_subG Ap1ay oay os leqnn .
    exists (y ^+ j); last first.
      left; rewrite -(norm_conj_autE _ Xx) ?groupX // morphX // -def_s.
      by rewrite -def_m // m_s expgn_znat // oX pfactorK ?eqxx.
    rewrite -scXG !inE groupX //= andbT -ker_conj_aut !inE morphX // -def_s.
    rewrite andbC -(inj_in_eq m_inj) ?group1 // m_s m1 oX pfactorK // -/r.
    rewrite mulrSr -subr_eq0 addrK -val_eqE /= val_Zp_nat //.
    by rewrite [_ == 0%N]dvdn_Pexp2l // -def_n ltnn.
  rewrite {1}p2 /= => [[t [At ot m_t]]]; rewrite {1}oX pfactorK // -{1}def_n.
  rewrite eqSS subn_eq0 => defA; exists y; rewrite ?inE ?notXy //.
  rewrite p2 -(norm_conj_autE _ Xx) //= -/ay -def_m ?Aut_aut //.
  case Tay: (ay \in <[t]>).
    rewrite cycle2g // !inE -order_eq1 oay p2 /= in Tay.
    by right; rewrite (eqP Tay) m_t expgn_zneg // mulgV group1.
  case: leqP defA => [_ defA | -> [a [Aa _ _ defA [s [As os m_s m_st defA1]]]]].
    by rewrite -defA Aut_aut in Tay.
  have: ay \in [set s; s * t].
    have: ay \in 'Ohm_1(Aut X) := subsetP (OhmS 1 (pcore_sub _ _)) ay Ap1ay.
    case/dprodP: (Ohm_dprod 1 defA) => _ <- _ _.
    rewrite defA1 (@Ohm_p_cycle _ _ 2) /p_elt ot //= expg1 cycle2g //.
    by rewrite mulUg mul1g inE Tay cycle2g // mulgU mulg1 mulg_set1.
  case/set2P=> ->; first by left; rewrite m_s expgn_znat // oX pfactorK // -p2.
  right; rewrite m_st expgn_znat // oX pfactorK // -p2 -/r.
  by rewrite -expgS prednK ?cycle_id.
have [Gy notXy] := setDP X'y; have nXy := subsetP nXG y Gy.
have defG: forall j, <[x]> <*> <[x ^+ j * y]> = G.
  move=> j; rewrite -defX -genM_mulgen.
  by rewrite (mulg_normal_maximal nsXG) ?cycle_subG ?groupMl ?groupX ?genGid.
have[i def_yp]: exists i, y ^- p = x ^+ i.
  by apply/cycleP; rewrite -defX groupV X_Gp.
have p_i: p %| i.
  apply: contraR notXy; rewrite -prime_coprime // => co_p_j.
  have genX: generator X (y ^- p).
    by rewrite def_yp defX generator_coprime ox coprime_expl.
  rewrite -scXG (setIidPl _) // centsC ((X :=P: _) genX) cycle_subG groupV.
  rewrite /= -(defG 0%N) mul1g cent_mulgen inE -defX (subsetP cXX) ?X_Gp //.
  by rewrite (subsetP (cycle_abelian y)) ?mem_cycle.
case=> [[n_gt23 xy] | [p2 Z_xxy]].
  suffices ->: cG = ModularGroup by []; apply/modular_group_classP.
  exists p => //; exists n => //; rewrite isogEcard card_modular_group //.
  rewrite  oG leqnn andbT Grp_modular_group // -/q -/r.
  have{i def_yp p_i} [i def_yp]: exists i, y ^- p = x ^+ i ^+ p.
    by case/dvdnP: p_i => j def_i; exists j; rewrite -expgn_mul -def_i.
  have Zyx: [~ y, x] \in Z.
    by rewrite -groupV invg_comm commgEl xy expgS mulKg cycle_id.
  have def_yxj: forall j, [~ y, x ^+ j] = [~ y, x] ^+ j.
    by move=> j; rewrite commgX /commute ?(centsP cGZ _ Zyx).
  have Zyxj: forall j, [~ y, x ^+ j] \in Z by move=> j; rewrite def_yxj groupX.
  have x_xjy: forall j, x ^ (x ^+ j * y) = x ^+ r.+1.
    by move=> j; rewrite conjgM {2}/conjg commuteX //= mulKg.
  case: (eqVneq ([~ y, x ^+ i] ^+ 'C(p, 2)) 1) => [cyxi | not_cyxi].
    apply/existsP; exists (x, x ^+ i * y); rewrite /= !xpair_eqE.
    rewrite defG x_xjy -order_dvdn ox dvdnn !eqxx andbT /=.
    rewrite expMg_Rmul /commute ?(centsP cGZ _ (Zyxj _)) ?groupX // cyxi.
    by rewrite -def_yp -mulgA mulKg.
  have [p2 | odd_p] := even_prime p_pr; last first.
    by rewrite -order_dvdn bin2odd ?dvdn_mulr // -oZ order_dvdG in not_cyxi.
  have def_yxi: [~ y, x ^+ i] = x ^+ r.
    have:= Zyxj i; rewrite /Z cycle_traject orderE oZ p2 !inE mulg1.
    by case/pred2P=> // cyxi; rewrite cyxi p2 eqxx in not_cyxi.
  apply/existsP; exists (x, x ^+ (i + r %/ 2) * y); rewrite /= !xpair_eqE.
  rewrite defG x_xjy -order_dvdn ox dvdnn !eqxx andbT /=.
  rewrite expMg_Rmul /commute ?(centsP cGZ _ (Zyxj _)) ?groupX // def_yxj.
  rewrite -expgn_mul muln_addl addnC !expgn_add (expgn_mul x i) -def_yp mulgKV.
  rewrite -def_yxj def_yxi p2 mulgA -expgn_add in n_gt23 *.
  rewrite -expg_mod_order ox /q /r p2 -(subnKC n_gt23) mulnC !expnS mulKn //.
  rewrite addnn -mul2n modnn mul1g -order_dvdn dvdn_mulr //.
  by rewrite -p2 -oZ order_dvdG.
have{i def_yp p_i} Zy2: y ^+ 2 \in Z.
  rewrite defZ (OhmE _ pX) -groupV -p2 def_yp mem_gen // inE groupX //= p2.
  rewrite  expgS -{2}def_yp -(mulKg y y) -conjgE -conjXg -conjVg def_yp conjXg.
  rewrite -expMgn //; last by apply: (centsP cXX); rewrite ?memJ_norm.
  by rewrite -order_dvdn (dvdn_trans (order_dvdG Z_xxy)) ?oZ.
rewrite !cycle_traject !orderE oZ p2 !inE !mulg1 /= in Z_xxy Zy2 *.
rewrite -eq_invg_mul eq_sym -[r]prednK // expgS (inj_eq (mulgI _)) in Z_xxy.
case/pred2P: Z_xxy => xy; last first.
  suffices ->: cG = SemiDihedral by []; apply/semidihedral_classP.
  have n_gt3: n > 3.
    case: ltngtP notXy => // [|n3]; first by rewrite ltnNge n_gt2.
    rewrite -scXG inE Gy defX cent_cycle; case/cent1P; red.
    by rewrite (conjgC x) xy /r p2 n3.
  exists n => //; rewrite isogEcard card_semidihedral // oG p2 leqnn andbT.
  rewrite Grp_semidihedral //; apply/existsP=> /=.
  case/pred2P: Zy2 => y2; [exists (x, y) | exists (x, x * y)].
    by rewrite /= -{1}[y]mul1g (defG 0%N) y2 xy -p2 -/q -ox expg_order.
  rewrite /= (defG 1%N) conjgM {2}/conjg mulKg -p2 -/q -ox expg_order -xy.
  rewrite !xpair_eqE !eqxx /= andbT p2 expgS {2}(conjgC x) xy mulgA -(mulgA x).
  rewrite [y * y]y2 -expgS -expgn_add addSnnS prednK // addnn -mul2n -p2 def_pr.
  by rewrite -ox expg_order.
case/pred2P: Zy2 => y2.
  suffices ->: cG = Dihedral by []; apply/dihedral_classP.
  exists n => //; rewrite isogEcard card_2dihedral // oG p2 leqnn andbT.
  rewrite Grp_2dihedral //; apply/existsP; exists (x, y) => /=.
  by rewrite /= -{1}[y]mul1g (defG 0%N) y2 xy -p2 -/q -ox expg_order.
suffices ->: cG = Quaternion by []; apply/quaternion_classP.
exists n => //; rewrite isogEcard card_quaternion // oG p2 leqnn andbT.
rewrite Grp_quaternion //; apply/existsP; exists (x, y) => /=.
by rewrite /= -{1}[y]mul1g (defG 0%N) y2 xy -p2 -/q -ox expg_order.
Qed.

(* This is Aschbacher (23.5) *)
Lemma cyclic_SCN : forall gT p (G U : {group gT}),
    p.-group G -> U \in 'SCN(G) -> ~~ abelian G -> cyclic U ->
    [/\ p = 2, #|G : U| = 2 & extremal2 G]
\/ exists M : {group gT},
   [/\ M :=: 'C_G('Mho^1(U)), #|M : U| = p, extremal_class M = ModularGroup,
       'Ohm_1(M)%G \in 'E_p^2(G) & 'Ohm_1(M) \char G].
Proof.
move=> gT p G U pG; case/SCN_P=> nsUG scUG not_cGG cycU.
have [sUG nUG] := andP nsUG; have cUU := cyclic_abelian cycU.
have pU := pgroupS sUG pG.
have ltUG: ~~ (G \subset U).
  by apply: contra not_cGG => sGU; exact: abelianS cUU.
have ntU: U :!=: 1.
  by apply: contra ltUG; move/eqP=> U1; rewrite -(setIidPl (cents1 G)) -U1 scUG.
have [p_pr _ [n oU]] := pgroup_pdiv pU ntU.
have p_gt1 := prime_gt1 p_pr; have p_gt0 := ltnW p_gt1.
have [u defU] := cyclicP _ cycU; have Uu: u \in U by rewrite defU cycle_id.
have Gu := subsetP sUG u Uu; have p_u := mem_p_elt pG Gu.
have defU1: 'Mho^1(U) = <[u ^+ p]> by rewrite defU (Mho_p_cycle _ p_u).
have modM1: forall M : {group gT},
    [/\ U \subset M, #|M : U| = p & extremal_class M = ModularGroup] ->
  M :=: 'C_M('Mho^1(U)) /\ 'Ohm_1(M)%G \in 'E_p^2(M).
- move=> M [sUM iUM]; case/modular_group_classP=> q q_pr {n oU}[n n_gt23 isoM].
  have n_gt2: n > 2 by exact: leq_trans (leq_addl _ _) n_gt23.
  have def_n: n = (n - 3).+3 by rewrite -{1}(subnKC n_gt2).
  have oM: #|M| = (q ^ n)%N by rewrite (isog_card isoM) card_modular_group.
  have pM: q.-group M by rewrite /pgroup oM pnat_exp pnat_id.
  have def_q: q = p; last rewrite {q q_pr}def_q in oM pM isoM n_gt23.
    by apply/eqP; rewrite eq_sym [p == q](pgroupP pM) // -iUM dvdn_indexg.
  have [[x y] genM modM] := generators_modular_group p_pr n_gt2 isoM.
  case/modular_group_structure: genM => // _ [defZ _ oZ] _ defMho.
  have ->: 'Mho^1(U) = 'Z(M).
    apply/eqP; rewrite eqEcard oZ defZ -(defMho 1%N) ?MhoS //= defU1 -orderE.
    suff ou: #[u] = (p * p ^ n.-2)%N by rewrite orderXdiv ou ?dvdn_mulr ?mulKn.
    by rewrite orderE -defU -(setIidPr sUM) -divg_index iUM oM def_n mulKn.
  case: eqP => [[p2 n3] | _ defOhm]; first by rewrite p2 n3 in n_gt23.
  have{defOhm} [|defM1 oM1] := defOhm 1%N; first by rewrite def_n.
  split; rewrite ?(setIidPl _) //; first by rewrite centsC subsetIr.
  rewrite inE oM1 pfactorK // andbT inE Ohm_sub abelem_Ohm1 //.
  exact: (card_p2group_abelian p_pr oM1).
have ou: #[u] = (p ^ n.+1)%N by rewrite defU in oU.
pose Gs := G / U; have pGs: p.-group Gs by rewrite quotient_pgroup.
have ntGs: Gs != 1 by rewrite -subG1 quotient_sub1.
have [_ _ [[|k] oGs]] := pgroup_pdiv pGs ntGs.
  have iUG: #|G : U| = p by rewrite -card_quotient ?oGs.
  case: (predU1P (maximal_cycle_extremal _ _ _ _ iUG)) => // [modG | ext2G].
    by right; exists G; case: (modM1 G) => // <- ->; rewrite Ohm_char.
  by left; case: eqP ext2G => // <-.
pose M := 'C_G('Mho^1(U)); right; exists [group of M].
have sMG: M \subset G by exact: subsetIl.
have [pM nUM] := (pgroupS sMG pG, subset_trans sMG nUG).
have sUM: U \subset M by rewrite subsetI sUG sub_abelian_cent ?Mho_sub.
pose A := Aut U; have cAA: abelian A by rewrite Aut_cyclic_abelian.
have sylAp: p.-Sylow(A) 'O_p(A) by rewrite nilpotent_pcore_Hall ?abelian_nil.
have [f [injf sfGsA fG]]: exists f : {morphism Gs >-> {perm gT}},
   [/\ 'injm f, f @* Gs \subset A & {in G, forall y, f (coset U y) u = u ^ y}].
- have [] := first_isom_loc [morphism of conj_aut U] nUG.
  rewrite ker_conj_aut scUG /= -/Gs => f injf im_f.
  exists f; rewrite im_f ?Aut_conj_aut //.
  split=> // y Gy; have nUy := subsetP nUG y Gy.
  suffices ->: f (coset U y) = conj_aut U y by rewrite norm_conj_autE.
  by apply: set1_inj; rewrite -!morphim_set1 ?mem_quotient // im_f ?sub1set.
have cGsGs: abelian Gs by rewrite -(injm_abelian injf) // (abelianS sfGsA).
have p_fGs: p.-group (f @* Gs) by rewrite morphim_pgroup.
have sfGsAp: f @* Gs \subset 'O_p(A).
  by rewrite (subset_normal_Hall _ sylAp) ?pcore_normal //; exact/andP.
have [a [fGa oa au n_gt01 cycGs]]: exists a,
  [/\ a \in f @* Gs, #[a] = p, a u = u ^+ (p ^ n).+1, (p == 2) + 1 <= n
    & cyclic Gs \/ p = 2 /\ (exists2 c, c \in f @* Gs & c u = u^-1)].
- have [m [[def_m _ _ _ _] _]] := cyclic_pgroup_Aut_structure pU cycU ntU.
  have ->: logn p #|U| = n.+1 by rewrite oU pfactorK.
  rewrite /= -/A; case: posnP => [_ defA | n_gt0 [c [Ac oc m_c defA]]].
    have:= cardSg sfGsAp; rewrite (card_Hall sylAp) /= -/A defA card_injm //.
    by rewrite oGs (part_p'nat (pcore_pgroup _ _)) pfactor_dvdn // logn1.
  have [p2 | odd_p] := even_prime p_pr; last first.
    case: eqP => [-> // | _] in odd_p *; rewrite odd_p in defA.
    have [[cycA _] _ [a [Aa oa m_a defA1]]] := defA.
    exists a; rewrite -def_m // oa m_a expgn_znat //.
    split=> //; last by left; rewrite -(injm_cyclic injf) ?(cyclicS sfGsA).
    have: f @* Gs != 1 by rewrite morphim_injm_eq1.
    rewrite -cycle_subG; apply: contraR => not_sfGs_a.
    by rewrite -(setIidPl sfGsAp) TI_Ohm1 // defA1 setIC prime_TIg -?orderE ?oa.
  do [rewrite {1}p2 /= eqn_leq n_gt0; case: leqP => /= [_ | n_gt1]] in defA.
    have:= cardSg sfGsAp; rewrite (card_Hall sylAp) /= -/A defA -orderE oc p2.
    by rewrite card_injm // oGs p2 pfactor_dvdn // p_part.
  have{defA} [s [As os _ defA [a [Aa oa m_a _ defA1]]]] := defA; exists a.
  have fGs_a: a \in f @* Gs.
    suffices: f @* Gs :&: <[s]> != 1.
      apply: contraR => not_fGs_a; rewrite TI_Ohm1 // defA1 setIC.
      by rewrite prime_TIg -?orderE ?oa // cycle_subG.
    have: (f @* Gs) * <[s]> \subset A by rewrite mulG_subG cycle_subG sfGsA.
    move/subset_leq_card; apply: contraL; move/eqP; move/TI_cardMg->.
    rewrite -(dprod_card defA) -ltnNge mulnC -!orderE ltn_pmul2r // oc.
    by rewrite card_injm // oGs p2 (ltn_exp2l 1%N).
  rewrite -def_m // oa m_a expgn_znat // p2; split=> //.
  rewrite abelian_rank1_cyclic // (rank_pgroup pGs) //.
  rewrite -(injm_p_rank injf) // p_rank_abelian 1?morphim_abelian //= p2 -/Gs.
  case: leqP => [|fGs1_gt1]; [by left | right].
  split=> //; exists c; last by rewrite -def_m // m_c expgn_zneg.
  have{defA1} defA1: <[a]> \x <[c]> = 'Ohm_1(Aut U).
    by rewrite -(Ohm_dprod 1 defA) defA1 (@Ohm_p_cycle 1 _ 2) /p_elt oc.
  have def_fGs1: 'Ohm_1(f @* Gs) = 'Ohm_1(A).
    apply/eqP; rewrite eqEcard OhmS // -(dprod_card defA1) -!orderE oa oc.
    by rewrite dvdn_leq ?(@pfactor_dvdn 2 2) ?cardG_gt0.
  rewrite (subsetP (Ohm_sub 1 _)) // def_fGs1 -cycle_subG.
  by case/dprodP: defA1 => _ <- _ _; rewrite mulG_subr.
have n_gt0: n > 0 := leq_trans (leq_addl _ _) n_gt01.
have [ys Gys _ def_a] := morphimP fGa.
have oys: #[ys] = p by rewrite -(order_injm injf) // -def_a oa.
have defMs: M / U = <[ys]>.
  apply/eqP; rewrite eq_sym eqEcard -orderE oys cycle_subG; apply/andP; split.
    have [y nUy Gy /= def_ys] := morphimP Gys.
    rewrite def_ys mem_quotient //= inE Gy defU1 cent_cycle cent1C.
    rewrite (sameP cent1P commgP) commgEl conjXg -fG //= -def_ys -def_a au.
    by rewrite -expgn_mul mulSn expgn_add mulKg -expnSr -ou expg_order.
  rewrite card_quotient // -(setIidPr sUM) -scUG setIA (setIidPl sMG).
  rewrite defU cent_cycle index_cent1 -(card_imset _ (mulgI u^-1)) -imset_comp.
  have <-: #|'Ohm_1(U)| = p.
    rewrite defU (Ohm_p_cycle 1 p_u) -orderE (orderXexp _ ou) ou pfactorK //.
    by rewrite subKn.
  rewrite (OhmE 1 pU) subset_leq_card ?sub_gen //; apply/subsetP=> uz.
  case/imsetP=> z; case/setIP; move/(subsetP nUG)=> nUz cU1z ->{uz}.
  have Uv' := groupVr Uu; have Uuz: u ^ z \in U by rewrite memJ_norm.
  rewrite inE groupM // expMgn /commute 1?(centsP cUU u^-1) //= expVgn -conjXg.
  by rewrite (sameP commgP cent1P) cent1C -cent_cycle -defU1.
have iUM: #|M : U| = p by rewrite -card_quotient ?defMs.
have not_cMM: ~~ abelian M.
  apply: contraL p_pr => cMM; rewrite -iUM -indexgI /= -/M.
  by rewrite (setIidPl _) ?indexgg // -scUG subsetI sMG sub_abelian_cent.
have modM: extremal_class M = ModularGroup.
  have sU1Z: 'Mho^1(U) \subset 'Z(M).
    by rewrite subsetI (subset_trans (Mho_sub 1 U)) // centsC subsetIr.
  case: (predU1P (maximal_cycle_extremal _ _ _ _ iUM)) => //=; rewrite -/M.
  case/andP; move/eqP=> p2 ext2M; rewrite p2 add1n in n_gt01.
  suffices{sU1Z}: #|'Z(M)| = 2.
    move/eqP; rewrite eqn_leq leqNgt (leq_trans _ (subset_leq_card sU1Z)) //.
    by rewrite defU1 -orderE (orderXexp 1 ou) subn1 p2 (ltn_exp2l 1).
  move: ext2M; rewrite /extremal2 !inE orbC -orbA; case/or3P; move/eqP.
  - case/semidihedral_classP=> m m_gt3 isoM.
    have [[x z] genM [oz _]] := generators_semidihedral m_gt3 isoM.
    by case/semidihedral_structure: genM => // _ _ [].
  - case/quaternion_classP=> m m_gt2 isoM.
    have [[x z] genM _] := generators_quaternion m_gt2 isoM.
    by case/quaternion_structure: genM => // _ _ [].
  case/dihedral_classP=> m m_gt1 isoM.
  have [[x z] genM _] := generators_2dihedral m_gt1 isoM.
  case/dihedral2_structure: genM not_cMM => // _ _ _ _.
  by case: (m == 2) => [|[]//]; move/abelem_abelian->.
split=> //.
  have [//|_] := modM1 [group of M]; rewrite !inE -andbA /=.
  by case/andP; move/subset_trans->.
have{cycGs} [cycGs | [p2 [c fGs_c u_c]]] := cycGs.
  suffices ->: 'Ohm_1(M) = 'Ohm_1(G) by exact: Ohm_char.
  suffices sG1M: 'Ohm_1(G) \subset M.
    by apply/eqP; rewrite eqEsubset -{2}(Ohm_id 1 G) !OhmS.
  rewrite -(quotientSGK _ sUM) ?(subset_trans (Ohm_sub _ G)) //= defMs.
  suffices ->: <[ys]> = 'Ohm_1(Gs) by rewrite morphim_Ohm.
  apply/eqP; rewrite eqEcard -orderE cycle_subG /= {1}(OhmE 1 pGs) /=.
  rewrite mem_gen ?inE ?Gys -?order_dvdn oys //=.
  rewrite -(part_pnat_id (pgroupS (Ohm_sub _ _) pGs)) p_part (leq_exp2l _ 1) //.
  by rewrite -p_rank_abelian -?rank_pgroup -?abelian_rank1_cyclic.
suffices charU1: 'Mho^1(U) \char G^`(1).
  rewrite (char_trans (Ohm_char _ _)) // subcent_char ?char_refl //.
  exact: char_trans (der_char 1 G).
suffices sUiG': 'Mho^1(U) \subset G^`(1).
  have cycG': cyclic G^`(1) by rewrite (cyclicS _ cycU) // der1_min.
  by case/cyclicP: cycG' sUiG' => zs ->; exact: cycle_subgroup_char.
rewrite defU1 cycle_subG p2 -groupV invMg -{2}u_c.
case/morphimP: fGs_c => zs _; case/morphimP=> z _ Gz -> ->{zs}.
by rewrite fG ?mem_commg.
Qed.

(* This is Aschbacher, exercise (8.4) *)
Lemma normal_rank1_structure : forall gT p (G : {group gT}),
    p.-group G -> (forall X : {group gT}, X <| G -> abelian X -> cyclic X) ->
  cyclic G \/ [&& p == 2, extremal2 G & (#|G| >= 16) || (G \isog 'Q_8)].
Proof.
move=> gT p G pG dn_G_1.
case/orP: (orbN (abelian G)) => [cGG | not_cGG]; first by left; rewrite dn_G_1.
have [X maxX]: {X | [max X | (X <| G) && abelian X]}.
  by apply: ex_maxgroup; exists 1%G; rewrite normal1 abelian1.
have cycX: cyclic X by rewrite dn_G_1; case/andP: (maxgroupp maxX).
have scX: X \in 'SCN(G) := max_SCN pG maxX.
have [[p2 _ cG] | [M [_ _ _]]] := cyclic_SCN pG scX not_cGG cycX; last first.
  rewrite 2!inE -andbA; case/and3P=> sEG abelE dimE_2 charE.
  have:= dn_G_1 _ (char_normal charE) (abelem_abelian abelE).
  by rewrite (abelem_cyclic abelE) (eqP dimE_2).
have [n oG] := p_natP pG; right; rewrite p2 cG /= in oG *.
rewrite oG (@leq_exp2l 2 4) //.
rewrite /extremal2 /extremal_class oG pfactorKpdiv // in cG.
case: andP cG => [[n_gt1 isoG] _ | _]; last first.
  by rewrite leq_eqVlt; case: (3 < n); case: eqP => //= <-; do 2?case: ifP.
have [[x y] genG _] := generators_2dihedral n_gt1 isoG.
have [_ _ _ [_ _ maxG]] := dihedral2_structure n_gt1 genG isoG.
rewrite 2!ltn_neqAle n_gt1 !(eq_sym _ n).
case: eqP => [_ abelG| _]; first by rewrite (abelem_abelian abelG) in not_cGG.
case: eqP => // -> [_ _ isoY _ _]; set Y := <<_>> in isoY.
have nxYG: Y <| G by rewrite (p_maximal_normal pG) // maxG !inE eqxx orbT.
have [// | [u v] genY _] := generators_2dihedral _ isoY.
case/dihedral2_structure: (genY) => //= _ _ _ _ abelY.
have:= dn_G_1 _ nxYG (abelem_abelian abelY).
by rewrite (abelem_cyclic abelY); case: genY => ->.
Qed.

(* Replacement for Section 4 proof. *)
Lemma odd_pgroup_rank1_cyclic : forall gT p (G : {group gT}),
  p.-group G -> odd #|G| -> cyclic G = ('r_p(G) <= 1).
Proof.
move=> gT p G pG oddG; rewrite -rank_pgroup //; apply/idP/idP=> [cycG | dimG1].
  by rewrite -abelian_rank1_cyclic ?cyclic_abelian.
have [X nsXG cXX|//|] := normal_rank1_structure pG; last first.
  by rewrite (negPf (odd_not_extremal2 oddG)) andbF.
by rewrite abelian_rank1_cyclic // (leq_trans (rankS (normal_sub nsXG))).
Qed.

(* This is the second part of Aschbacher, exercise (8.4). *)
Lemma prime_Ohm1P : forall gT p (G : {group gT}),
    p.-group G -> G :!=: 1 ->
  reflect (#|'Ohm_1(G)| = p)
          (cyclic G || (p == 2) && (extremal_class G == Quaternion)).
Proof.
move=> gT p G pG ntG; have [p_pr p_dvd_G _] := pgroup_pdiv pG ntG.
apply: (iffP idP) => [|oG1p].
  case/orP=> [cycG|]; first exact: Ohm1_cyclic_pgroup_prime.
  case/andP; move/eqP=> p2; move/eqP; case/quaternion_classP=> n n_gt2 isoG.
  rewrite p2; have [[x y]] := generators_quaternion n_gt2 isoG.
  by case/quaternion_structure=> // _ _ [<- oZ _ [->]].
have [X nsXG cXX|-> //|]:= normal_rank1_structure pG.
  have [sXG _] := andP nsXG; have pX := pgroupS sXG pG.
  rewrite abelian_rank1_cyclic // (rank_pgroup pX) p_rank_abelian //.
  rewrite -{2}(pfactorK 1 p_pr) -{3}oG1p dvdn_leq_log ?cardG_gt0 //.
  by rewrite cardSg ?OhmS.
case/and3P; move/eqP=> p2; rewrite p2 (orbC (cyclic G)) /extremal2.
case cG: (extremal_class G) => //; case: notF.
  case/dihedral_classP: cG => n n_gt1 isoG.
  have [[x y] genG _] := generators_2dihedral n_gt1 isoG.
  have [oG _ _ _] := genG; case/dihedral2_structure: genG => // _ _ [defG1 _] _.
  by case/idPn: n_gt1; rewrite -(@ltn_exp2l 2) // -oG -defG1 oG1p p2.
case/semidihedral_classP: cG => n n_gt3 isoG.
have [[x y] genG [oy _]] := generators_semidihedral n_gt3 isoG.
case/semidihedral_structure: genG => // _ _ [_ _ [defG1 _] _] _ [isoG1 _ _].
case/idPn: (n_gt3); rewrite -(ltn_predK n_gt3) ltnS -leqNgt -(@leq_exp2l 2) //.
rewrite -card_2dihedral //; last by rewrite -(subnKC n_gt3).
by rewrite -(isog_card isoG1) /= -defG1 oG1p p2.
Qed.

(* This is Aschbacher (23.9) *)
Theorem symplectic_type_group_structure : forall gT p (G : {group gT}),
    p.-group G -> (forall X : {group gT}, X \char G -> abelian X -> cyclic X) ->
  exists2 E : {group gT}, E :=: 1 \/ extraspecial E
  & exists R : {group gT},
    [/\ cyclic R \/ [/\ p = 2, extremal2 R & #|R| >= 16],
        E \* R = G
      & E :&: R = 'Z(E)].
Proof.
move=> gT p G pG sympG; have [H [charH]] := Thompson_critical pG.
have sHG := char_sub charH; have pH := pgroupS sHG pG.
set U := 'Z(H) => sPhiH_U sHG_U defU; set Z := 'Ohm_1(U).
have sZU: Z \subset U by rewrite Ohm_sub.
have charU: U \char G := char_trans (center_char H) charH.
have cUU: abelian U := center_abelian H.
have cycU: cyclic U by exact: sympG.
have pU: p.-group U := pgroupS (char_sub charU) pG.
have cHU: U \subset 'C(H) by rewrite subsetIr.
have cHsHs: abelian (H / Z).
  rewrite sub_der1_abelian //= (OhmE _ pU) genS //= -/U.
  apply/subsetP=> hk; case/imset2P=> h k Hh Hk ->{hk}.
  have Uhk: [~ h, k] \in U by rewrite (subsetP sHG_U) ?mem_commg ?(subsetP sHG).
  rewrite inE Uhk -commXg; last by red; rewrite -(centsP cHU).
  apply/commgP; red; rewrite (centsP cHU) // (subsetP sPhiH_U) //.
  by rewrite (Phi_mulgen pH) mem_gen // inE orbC (Mho_p_elt 1) ?(mem_p_elt pH).
have nsZH: Z <| H by rewrite sub_center_normal.
have [K /=] := inv_quotientS nsZH (Ohm_sub 1 (H / Z)); fold Z => defKs sZK sKH.
have nsZK: Z <| K := normalS sZK sKH nsZH; have [_ nZK] := andP nsZK.
have abelKs: p.-abelem (K / Z) by rewrite -defKs Ohm1_abelem ?quotient_pgroup.
have charK: K \char G.
  have charZ: Z \char H := char_trans (Ohm_char _ _) (center_char H).
  rewrite (char_trans _ charH) // (char_from_quotient nsZK) //.
  by rewrite -defKs Ohm_char.
have cycZK: cyclic 'Z(K).
  by rewrite sympG ?center_abelian ?(char_trans (center_char _)).
have [cKK | not_cKK] := orP (orbN (abelian K)).
  have defH: U = H.
    apply: center_abelian_id; apply: cyclic_center_factor.
    rewrite -(isog_cyclic (third_isog (Ohm_sub 1 _) nsZH (center_normal _))).
    rewrite quotient_cyclic //= -/Z abelian_rank1_cyclic //.
    have cKsKs: abelian (K / Z) by rewrite -defKs (abelianS (Ohm_sub 1 _)).
    have cycK: cyclic K by rewrite -(center_abelian_id cKK).
    by rewrite -rank_Ohm1 defKs -abelian_rank1_cyclic ?quotient_cyclic.
  have scH: H \in 'SCN(G) by apply/SCN_P; rewrite defU char_normal.
  have [cGG | not_cGG] := orP (orbN (abelian G)).
    exists 1%G; [by left | exists G; rewrite cprod1g (setIidPl _) ?sub1G //].
    by split; first left; rewrite ?center1 // sympG ?char_refl.
  have cycH: cyclic H by rewrite -{}defH.
  have [[p2 _ cG2]|[M [_ _ _]]] := cyclic_SCN pG scH not_cGG cycH; last first.
    do 2![case/setIdP] => _ abelE dimE_2 charE.
    have:= sympG _ charE (abelem_abelian abelE).
    by rewrite (abelem_cyclic abelE) (eqP dimE_2).
  have [n oG] := p_natP pG; rewrite p2 in oG.
  have [n_gt3 | n_le3] := ltnP 3 n.
    exists 1%G; [by left | exists G; rewrite cprod1g (setIidPl _) ?sub1G //].
    by split; first right; rewrite ?center1 // oG (@leq_exp2l 2 4).
  have esG: extraspecial G.
    by apply: (p3group_extraspecial pG); rewrite // p2 oG pfactorK.
  exists G; [by right | exists ('Z(G))%G; rewrite cprod_center_id setIA setIid].
  by split=> //; left; rewrite prime_cyclic; case: esG.
have ntK: K :!=: 1 by apply: contra not_cKK; move/eqP->; exact: abelian1.
have [p_pr _ _] := pgroup_pdiv (pgroupS sKH pH) ntK.
have p_gt1 := prime_gt1 p_pr; have p_gt0 := ltnW p_gt1.
have oZ: #|Z| = p.
  apply: Ohm1_cyclic_pgroup_prime => //=; apply: contra ntK; move/eqP.
  by move/(trivg_center_pgroup pH)=> GH; rewrite -subG1 -GH.
have sZ_ZK: Z \subset 'Z(K).
  by rewrite subsetI sZK (subset_trans (Ohm_sub _ _ )) // subIset ?centS ?orbT.
have sZsKs: 'Z(K) / Z \subset K / Z by rewrite quotientS ?center_sub.
have [Es /= splitKs] := abelem_split_dprod abelKs sZsKs.
have [_ /= defEsZs cEsZs tiEsZs] := dprodP splitKs.
have sEsKs: Es \subset K / Z by rewrite -defEsZs mulG_subr.
have [E defEs sZE sEK] := inv_quotientS nsZK sEsKs; rewrite /= -/Z in defEs sZE.
have [nZE nZ_ZK] := (subset_trans sEK nZK, subset_trans (center_sub K) nZK).
have defK: 'Z(K) * E = K.
  rewrite -(mulSGid sZ_ZK) -mulgA -quotientK ?mul_subG ?quotientMl //.
  by rewrite -defEs defEsZs quotientGK.
have defZE: 'Z(E) = Z.
  have cEZK: 'Z(K) \subset 'C(E) by rewrite subIset // orbC centS.
  have cE_Z: E \subset 'C(Z) by rewrite centsC (subset_trans sZ_ZK).
  apply/eqP; rewrite eqEsubset andbC subsetI sZE centsC cE_Z /=.
  rewrite -quotient_sub1 ?subIset ?nZE //= -/Z -tiEsZs subsetI defEs.
  rewrite !quotientS ?center_sub //= subsetI subIset ?sEK //=.
  by rewrite -defK centM setSI // centsC.
have sEH := subset_trans sEK sKH; have pE := pgroupS sEH pH.
have esE: extraspecial E.
  split; last by rewrite defZE oZ.
  have sPhiZ: 'Phi(E) \subset Z.
    rewrite -quotient_sub1 ?(subset_trans (Phi_sub _)) ?(quotient_Phi pE) //.
    rewrite subG1 (trivg_Phi (quotient_pgroup _ pE)) /= -defEs.
    by rewrite (abelemS sEsKs) //= -defKs Ohm1_abelem ?quotient_pgroup.
  have sE'Phi: E^`(1) \subset 'Phi(E) by rewrite (Phi_mulgen pE) mulgen_subl.
  have ntE': E^`(1) != 1.
    rewrite (sameP eqP commG1P) -abelianE; apply: contra not_cKK => cEE.
    by rewrite -defK mulGSid ?center_abelian // -(center_abelian_id cEE) defZE.
  have defE': E^`(1) = Z.
    apply/eqP; rewrite eqEcard (subset_trans sE'Phi) //= oZ.
    have [_ _ [n ->]] := pgroup_pdiv (pgroupS (der_sub _ _) pE) ntE'.
    by rewrite (leq_exp2l 1) ?prime_gt1.
  by split; rewrite defZE //; apply/eqP; rewrite eqEsubset sPhiZ -defE'.
have [spE _] := esE; have [defPhiE defE'] := spE.
have{defE'} sEG_E': [~: E, G] \subset E^`(1).
  rewrite defE' defZE /Z (OhmE _ pU) commGC genS //.
  apply/subsetP=> ge; case/imset2P=> g e Gg Ee ->{ge}.
  have He: e \in H by rewrite (subsetP sKH) ?(subsetP sEK).
  have Uge: [~ g, e] \in U by rewrite (subsetP sHG_U) ?mem_commg.
  rewrite inE Uge -commgX; last by red; rewrite -(centsP cHU).
  have sZ_ZG: Z \subset 'Z(G).
    have charZ: Z \char G := char_trans (Ohm_char _ _) charU.
    move/implyP: (nil_meet_Z (pgroup_nil pG) (char_normal charZ)).
    rewrite -cardG_gt1 oZ prime_gt1 //=; apply: contraR => not_sZ_ZG.
    by rewrite prime_TIg ?oZ.
  have: e ^+ p \in 'Z(G).
    rewrite (subsetP sZ_ZG) // -defZE -defPhiE (Phi_mulgen pE) mem_gen //.
    by rewrite inE orbC (Mho_p_elt 1) ?(mem_p_elt pE).
  by case/setIP=> _; move/centP=> cGep; apply/commgP; red; rewrite cGep.
have sEG: E \subset G := subset_trans sEK (char_sub charK).
set R := 'C_G(E); have{sEG_E'} defG: E \* R = G.
  by rewrite cprodC cprodEgen ?subsetIr // mulgenC -(critical_extraspecial pG).
have [_ defER cRE] := cprodP defG.
have defH: E \* 'C_H(E) = H by rewrite -(setIidPr sHG) setIAC (cprod_modl defG).
have{defH} [_ defH cRH_E] := cprodP defH.
have cRH_RH: abelian 'C_H(E).
  have sZ_ZRH: Z \subset 'Z('C_H(E)).
    rewrite subsetI -{1}defZE setSI //= (subset_trans sZU) // centsC.
    by rewrite subIset // centsC cHU.
  have nsZ_ZH: Z <| 'C_H(E) by rewrite sub_center_normal.
  have{sZ_ZRH nsZ_ZH} isoRHs := third_isog sZ_ZRH nsZ_ZH (center_normal _).
  rewrite cyclic_center_factor // -(isog_cyclic isoRHs) quotient_cyclic //.
  have defHs: Es \x ('C_H(E) / Z) = H / Z.
    rewrite defEs dprodE ?quotient_cents -?quotientMl ?defH -?quotientGI //=.
    by rewrite setIA (setIidPl sEH) ['C_E(E)]defZE trivg_quotient.
  have:= Ohm_dprod 1 defHs; rewrite /= defKs (Ohm1_id (abelemS sEsKs abelKs)).
  rewrite dprodC; case/dprodP=> _ defEsRHs1 cEsRHs1 tiEsRHs1.
  have sRHsHs: 'C_H(E) / Z \subset H / Z by rewrite quotientS ?subsetIl.
  have cRHsRHs: abelian ('C_H(E) / Z) by exact: abelianS cHsHs.
  have pHs: p.-group (H / Z) by rewrite quotient_pgroup.
  rewrite abelian_rank1_cyclic // (rank_pgroup (pgroupS sRHsHs pHs)).
  rewrite p_rank_abelian // -(leq_add2r (logn p #|Es|)) -logn_mul ?cardG_gt0 //.
  rewrite -TI_cardMg // defEsRHs1 /= -defEsZs TI_cardMg ?logn_mul ?cardG_gt0 //.
  by rewrite leq_add2r -abelem_cyclic ?(abelemS sZsKs) // quotient_cyclic.
have{cRH_RH} defRH: 'C_H(E) = U.
  apply/eqP; rewrite eqEsubset andbC setIS ?centS // subsetI subsetIl /=.
  by rewrite -{2}defH centM subsetI subsetIr.
have scUR: 'C_R(U) = U by rewrite -setIA -{1}defRH -centM defH.
have sUR: U \subset R by rewrite -defRH setSI.
have tiER: E :&: R = 'Z(E) by rewrite setIA (setIidPl (subset_trans sEH sHG)).
have [cRR | not_cRR] := orP (orbN (abelian R)).
  exists E; [by right | exists [group of R]; split=> //; left].
  by rewrite /= -(setIidPl (sub_abelian_cent cRR sUR)) scUR.
have{scUR} scUR: [group of U] \in 'SCN(R).
  by apply/SCN_P; rewrite (normalS sUR (subsetIl _ _)) // char_normal.
have pR: p.-group R := pgroupS (subsetIl _ _) pG.
have [R_le_3 | R_gt_3] := leqP (logn p #|R|) 3.
  have esR: extraspecial R := p3group_extraspecial pR not_cRR R_le_3.
  have esG: extraspecial G := cprod_extraspecial pG defG tiER esE esR.
  exists G; [by right | exists ('Z(G))%G; rewrite cprod_center_id setIA setIid].
  by split=> //; left; rewrite prime_cyclic; case: esG.
have [[p2 _ ext2R] | [M []]] := cyclic_SCN pR scUR not_cRR cycU.
  exists E; [by right | exists [group of R]; split=> //; right].
  by rewrite dvdn_leq ?(@pfactor_dvdn 2 4) ?cardG_gt0 // -{2}p2.
rewrite /= -/R => defM iUM modM _ _; pose N := 'C_G('Mho^1(U)).
have charZN2: 'Z('Ohm_2(N)) \char G.
  rewrite (char_trans (center_char _)) // (char_trans (Ohm_char _ _)) //.
  by rewrite subcent_char ?char_refl // (char_trans (Mho_char _ _)).
have:= sympG _ charZN2 (center_abelian _).
rewrite abelian_rank1_cyclic ?center_abelian // leqNgt; case/negP.
have defN: E \* M = N.
  rewrite defM (cprod_modl defG) // centsC (subset_trans (Mho_sub 1 _)) //.
  by rewrite /= -/U -defRH subsetIr.
case/modular_group_classP: modM => q q_pr [n n_gt23 isoM].
have{n_gt23} n_gt2 := leq_trans (leq_addl _ _) n_gt23.
have n_gt1 := ltnW n_gt2; have n_gt0 := ltnW n_gt1.
have [[x y] genM modM] := generators_modular_group q_pr n_gt2 isoM.
have{q_pr} defq: q = p; last rewrite {q}defq in genM modM isoM.
  have: p %| #|M| by rewrite -iUM dvdn_indexg.
  by have [-> _ _ _] := genM; rewrite euclid_exp // dvdn_prime2 //; case: eqP.
have [oM Mx ox X'y] := genM; have [My _] := setDP X'y; have [oy _] := modM.
have [sUM sMR]: U \subset M /\ M \subset R.
  by rewrite defM subsetI sUR subsetIl centsC (subset_trans (Mho_sub _ _)).
have oU1: #|'Mho^1(U)| = (p ^ n.-2)%N.
  have oU: #|U| = (p ^ n.-1)%N.
    by rewrite -(setIidPr sUM) -divg_index iUM oM -subn1 expn_sub.
  case/cyclicP: cycU pU oU => u -> p_u ou.
  by rewrite (Mho_p_cycle 1 p_u) -orderE (orderXexp 1 ou) subn1.
have sZU1: Z \subset 'Mho^1(U).
  rewrite -(cardSg_cyclic cycU) ?Ohm_sub ?Mho_sub // oZ oU1.
  by rewrite -(subnKC n_gt2) expnS dvdn_mulr.
case/modular_group_structure: genM => // _ [defZM _ oZM] _ _.
have:= n_gt2; rewrite leq_eqVlt eq_sym !xpair_eqE andbC.
case: eqP => [n3 _ _ | _ /= n_gt3 defOhmM].
  have eqZU1: Z = 'Mho^1(U) by apply/eqP; rewrite eqEcard sZU1 oZ oU1 n3 /=.
  rewrite (setIidPl _) in defM; first by rewrite -defM oM n3 pfactorK in R_gt_3.
  by rewrite centsC -eqZU1 (subset_trans sZE).
have{defOhmM} [|defM2 _] := defOhmM 2; first by rewrite -subn1 -ltn_add_sub.
do [set xpn3 := x ^+ _; set X2 := <[_]>] in defM2.
have oX2: #|X2| = (p ^ 2)%N.
  by rewrite -orderE (orderXexp _ ox) -{1}(subnKC n_gt2) addSn addnK.
have sZX2: Z \subset X2.
  have cycXp: cyclic <[x ^+ p]> := cycle_cyclic _.
  rewrite -(cardSg_cyclic cycXp) /=; first by rewrite oZ oX2 dvdn_mull.
    rewrite -defZM subsetI (subset_trans (Ohm_sub _ _)) //=.
    by rewrite (subset_trans sZU1) // centsC defM subsetIr.
  by rewrite /xpn3 ltn_subS //expnS expgn_mul cycleX.
have{defM2} [_ /= defM2 cYX2 tiX2Y] := dprodP defM2.
have{defN} [_ defN cME] := cprodP defN.
have cEM2: E \subset 'C('Ohm_2(M)).
  by rewrite (subset_trans cME) ?centS ?Ohm_sub.
have [cX2E cYE]: E \subset 'C(X2) /\ E \subset 'C(<[y]>).
 by apply/andP; rewrite -subsetI -centM defM2.
have pN: p.-group N := pgroupS (subsetIl _ _) pG.
have defN2: (E <*> X2) \x <[y]> = 'Ohm_2(N).
  rewrite dprodE ?mulgen_subG ?cYE //=; last first.
    rewrite -cycle_subG in My; rewrite mulgenC cent_mulgenEr //= -/X2.
    rewrite -(setIidPr My) setIA -group_modl ?cycle_subG ?groupX //.
    by rewrite mulGSid // (subset_trans _ sZX2) // -defZE -tiER setIS.
  apply/eqP; rewrite cent_mulgenEl // -mulgA defM2 eqEsubset mulG_subG.
  rewrite OhmS ?andbT; last by rewrite -defN mulG_subr.
  have expE: exponent E %| p ^ 2 by rewrite exponent_special ?(pgroupS sEG).
  rewrite /= (OhmE 2 pN) sub_gen /=; last 1 first.
    rewrite setIdE subsetI -defN mulG_subl.
    by apply/subsetP=> e Ee; rewrite inE (exponentP expE).
  rewrite -cent_mulgenEl // -genM_mulgen genS // -defN.
  apply/subsetP=> ez; case/setIdP; case/imset2P=> e z Ee Mz ->{ez}.
  rewrite expMgn; last by red; rewrite (centsP cME).
  rewrite (exponentP expE) // mul1g => zp2; rewrite mem_mulg //=.
  by rewrite (OhmE 2 (pgroupS sMR pR)) mem_gen // inE Mz.
have{defN2} defZN2: X2 \x <[y]> = 'Z('Ohm_2(N)).
  rewrite -[X2](mulSGid sZX2) /= -/Z -defZE -(center_dprod defN2).
  do 2!rewrite -{1}(center_abelian_id (cycle_abelian _)) -/X2; congr (_ \x _).
  by case/cprodP: (center_cprod (cprodEgen cX2E)).
have{defZN2} strZN2: \big[dprod/1]_(z <- [:: xpn3; y]) <[z]> = 'Z('Ohm_2(N)).
  by rewrite unlock /= dprodg1.
rewrite -size_abelian_type ?center_abelian //.
have pZN2: p.-group 'Z('Ohm_2(N)) by rewrite (pgroupS _ pN) // subIset ?Ohm_sub.
rewrite -(perm_eq_size (perm_eq_abelian_type pZN2 strZN2 _)) //= !inE.
rewrite !(eq_sym 1) -!order_eq1 oy orderE oX2.
by rewrite (eqn_exp2l 2 0) // (eqn_exp2l 1 0).
Qed.

(* This is Aschbacher (23.12) *)
Lemma Ohm1_extraspecial_odd : forall gT p (G : {group gT}),
    p.-group G -> extraspecial G -> odd #|G| ->
 let Y := 'Ohm_1(G) in
  [/\ exponent Y = p, #|G : Y| %| p
    & Y != G ->
      exists E : {group gT},
        [/\ #|G : Y| = p, #|E| = p \/ extraspecial E,
            exists2 X : {group gT}, #|X| = p & X \x E = Y
          & exists M : {group gT},
             [/\ M \isog 'Mod_(p ^ 3), M \* E = G & M :&: E = 'Z(M)]]].
Proof.
move=> gT p G pG esG oddG Y; have [spG _] := esG.
have [defPhiG defG'] := spG; set Z := 'Z(G) in defPhiG defG'.
have{spG} expG: exponent G %| p ^ 2 by exact: exponent_special.
have p_pr := extraspecial_prime pG esG.
have p_gt1 := prime_gt1 p_pr; have p_gt0 := ltnW p_gt1.
have oZ: #|Z| = p := card_center_extraspecial pG esG.
have nsZG: Z <| G := center_normal G; have [sZG nZG] := andP nsZG.
have nsYG: Y <| G := Ohm_normal 1 G; have [sYG nYG] := andP nsYG.
have ntZ: Z != 1 by rewrite -cardG_gt1 oZ.
have sZY: Z \subset Y.
  by apply: contraR ntZ => ?; rewrite -(setIidPl sZG) TI_Ohm1 ?prime_TIg ?oZ.
have ntY: Y != 1 by apply: contra ntZ; rewrite -!subG1; exact: subset_trans.
have p_odd: odd p by rewrite -oZ (oddSg sZG).
have expY: exponent Y %| p by rewrite exponent_Ohm1_class2 // nil_class2 defG'.
rewrite (prime_nt_dvdP _ p_pr expY) -?dvdn1 -?trivg_exponent //.
have [-> | neYG] := eqVneq Y G; first by rewrite indexgg dvd1n eqxx; split.
have sG1Z: 'Mho^1(G) \subset Z by rewrite -defPhiG (Phi_mulgen pG) mulgen_subr.
have Z_Gp: {in G, forall x, x ^+ p \in Z}.
  by move=> x Gx; rewrite /= (subsetP sG1Z) ?(Mho_p_elt 1) ?(mem_p_elt pG).
have{expG} oY': {in G :\: Y, forall u, #[u] = (p ^ 2)%N}.
  move=> u; case/setDP=> Gu notYu; apply/eqP.
  have [k ou] := p_natP (mem_p_elt pG Gu).
  rewrite eqn_dvd order_dvdn (exponentP expG) // eqxx ou dvdn_Pexp2l // ltnNge.
  apply: contra notYu => k_le_1; rewrite [Y](OhmE _ pG) mem_gen // inE Gu /=.
  by rewrite -order_dvdn ou dvdn_exp2l.
have isoMod3: forall M : {group gT},
    M \subset G -> ~~ abelian M -> ~~ (M \subset Y) -> #|M| = (p ^ 3)%N ->
  M \isog 'Mod_(p ^ 3).
- move=> M sMG not_cMM; case/subsetPn=> u Mu notYu oM.
  have pM := pgroupS sMG pG; have sUM: <[u]> \subset M by rewrite cycle_subG.
  have Y'u: u \in G :\: Y by rewrite inE notYu (subsetP sMG).
  have iUM: #|M : <[u]>| = p by rewrite -divgS // oM expnS -(oY' u) ?mulnK.
  have cM := maximal_cycle_extremal pM not_cMM (cycle_cyclic u) sUM iUM.
  rewrite (sameP eqP (prime_oddPn p_pr)) p_odd orbF in cM.
  rewrite /extremal_class oM pdiv_pfactor // pfactorK //= in cM.
  by do 3!case: ifP => // _ in cM.
have iYG: #|G : Y| = p.
  have [V maxV sYV]: {V : {group gT} | maximal V G & Y \subset V}.
    by apply: maxgroup_exists; rewrite properEneq neYG.
  have [sVG [u Gu notVu]] := properP _ _ (maxgroupp maxV).
  wlog [v Vv notYv]: / exists2 v, v \in V & v \notin Y.
    have [->| ] := eqVneq Y V; first by rewrite (p_maximal_index pG).
    by rewrite eqEsubset sYV => not_sVY; apply; exact/subsetPn.
  pose U := <[u]> <*> <[v]>; have Gv := subsetP sVG v Vv.
  have sUG: U \subset G by rewrite mulgen_subG !cycle_subG Gu.
  have Uu: u \in U by rewrite -cycle_subG mulgen_subl.
  have Uv: v \in U by rewrite -cycle_subG mulgen_subr.
  have not_sUY: ~~ (U \subset Y) by apply/subsetPn; exists v.
  have sU1U: 'Ohm_1(U) \subset U := Ohm_sub 1 _.
  have sU1Y: 'Ohm_1(U) \subset Y := OhmS 1 sUG.
  suffices defUV: U :&: V = 'Ohm_1(U).
    by rewrite (subsetP sU1Y) // -defUV inE Uv in notYv.
  suffices iU1U: #|U : 'Ohm_1(U)| = p.
    have: maximal 'Ohm_1(U) U by rewrite p_index_maximal ?Ohm_sub ?iU1U.
    case/maxgroupP=> _; apply; rewrite /= -/U.
      by apply/properP; split; last exists u; rewrite ?subsetIl ?inE ?Uu.
    by rewrite subsetI Ohm_sub (subset_trans sU1Y).
  apply/prime_nt_dvdP=> //.
    by apply: contra not_sUY; rewrite /U; move/eqP; case/(index1g sU1U)=> <-.
  have ov: #[v] = (p ^ 2)%N by rewrite oY' // inE notYv.
  have sZv: Z \subset <[v]>.
    suffices defZ: <[v ^+ p]> == Z by rewrite -(eqP defZ) cycleX.
    by rewrite eqEcard cycle_subG Z_Gp //= oZ -orderE (orderXexp 1 ov).
  have nvG: G \subset 'N(<[v]>) by rewrite sub_der1_norm ?cycle_subG // defG'.
  have [cUU | not_cUU] := orP (orbN (abelian U)).
    rewrite -divgS ?Ohm_sub // -(mul_card_Ohm_Mho_abelian 1 cUU) /= -/U.
    by rewrite mulKn ?cardG_gt0 //= -oZ cardSg ?(subset_trans (MhoS 1 sUG)).
  have oU: #|U| = (p ^ 3)%N.
    have nvu := subsetP nvG u Gu; have nvU := subset_trans sUG nvG.
    rewrite -(LaGrange (mulgen_subr _ _)) -orderE ov mulnC; congr (_ * _)%N.
    rewrite -card_quotient //= quotient_mulgen ?cycle_subG //=.
    rewrite quotient_cycle // -orderE; apply: nt_prime_order => //.
      by rewrite -morphX //= coset_id // (subsetP sZv) // Z_Gp.
    have svV: <[v]> \subset V by rewrite cycle_subG.
    by apply: contra notVu; move/eqP=> v_u; rewrite (subsetP svV) // coset_idr.
  have isoU := isoMod3 _ sUG not_cUU not_sUY oU; rewrite /= -/U in isoU.
  have [//|[x y] genU modU] := generators_modular_group p_pr _ isoU.
  case/modular_group_structure: genU => // _ _ _ _.
  case: eqP (p_odd) => [[-> //] | _ _]; case/(_ 1%N)=> // _ oU1.
  by rewrite -divgS // oU oU1 mulnK // muln_gt0 p_gt0.
have iC1U: forall (U : {group gT}) x,
  U \subset G -> x \in G :\: 'C(U) -> #|U : 'C_U[x]| = p.
- move=> U x sUG; case/setDP=> Gx not_cUx; apply/prime_nt_dvdP=> //.
    apply: contra not_cUx; rewrite -sub_cent1; move/eqP=> sUCx.
    by rewrite -(index1g _ sUCx) ?subsetIl ?subsetIr.
  rewrite -(@dvdn_pmul2l (#|U| * #|'C_G[x]|)) ?muln_gt0 ?cardG_gt0 //.
  have maxCx: maximal 'C_G[x] G.
    rewrite cent1_extraspecial_maximal //; apply: contra not_cUx.
    by rewrite inE Gx; exact: subsetP (centS sUG) _.
  rewrite {1}mul_cardG setIA (setIidPl sUG) -(p_maximal_index pG maxCx) -!mulnA.
  rewrite !LaGrange ?subsetIl // mulnC dvdn_pmul2l //.
  have [sCxG nCxG] := andP (p_maximal_normal pG maxCx).
  by rewrite -norm_mulgenEl ?cardSg ?mulgen_subG ?(subset_trans sUG).
have oCG: forall U : {group gT},
  Z \subset U -> U \subset G -> #|'C_G(U)| = (p * #|G : U|)%N.
- move=> U; elim: {U}_.+1 {-2}U (ltnSn #|U|) => // m IHm U leUm sZU sUG.
  have [<- | neZU] := eqVneq Z U.
    by rewrite -oZ LaGrange // (setIidPl _) // centsC subsetIr.
  have{neZU} [x Gx not_cUx]: exists2 x, x \in G & x \notin 'C(U).
    by apply/subsetPn; rewrite eqEsubset sZU subsetI sUG centsC in neZU.
  pose W := 'C_U[x]; have iWU: #|U : W| = p by rewrite iC1U // inE not_cUx.
  have maxW: maximal W U by rewrite p_index_maximal ?subsetIl ?iWU.
  have ltWU: W \proper U by exact: maxgroupp maxW.
  have [sWU [u Uu notWu]] := properP _ _ ltWU.
  have defU: W * <[u]> = U.
    have nsWU: W <| U := p_maximal_normal (pgroupS sUG pG) maxW.
    by rewrite (mulg_normal_maximal nsWU) ?cycle_subG.
  have sWG := subset_trans sWU sUG.
  have sZW: Z \subset W.
    by rewrite subsetI sZU -cent_set1 subIset ?centS ?orbT ?sub1set.
  have iCW_CU: #|'C_G(W) : 'C_G(U)| = p.
    rewrite -defU centM cent_cycle setIA /= -/W.
    rewrite iC1U ?subsetIl ?setIS ?centS // inE andbC (subsetP sUG) //=.
    rewrite -sub_cent1; apply/subsetPn; exists x.
      by rewrite inE Gx -sub_cent1 subsetIr.
    by rewrite -defU centM cent_cycle inE -sub_cent1 subsetIr in not_cUx.
  apply/eqP; rewrite -(eqn_pmul2r p_gt0) -{1}iCW_CU LaGrange ?setIS ?centS //.
  rewrite IHm ?(leq_trans (proper_card ltWU)) //= -/W.
  by rewrite -(LaGrange_index sUG sWU) iWU mulnA.
have oCY: #|'C_G(Y)| = (p ^ 2)%N by rewrite oCG // iYG.
have [x cYx notZx]: exists2 x, x \in 'C_G(Y) & x \notin Z.
  apply/subsetPn; rewrite proper_subn // properEcard setIS ?centS //=.
  by rewrite oZ oCY (ltn_exp2l 1 2).
have{cYx} [Gx cYx] := setIP cYx; have nZx := subsetP nZG x Gx.
have defCx: 'C_G[x] = Y.
  apply/eqP; rewrite eq_sym eqEcard subsetI sYG sub_cent1 cYx /=.
  rewrite -(leq_pmul2r p_gt0) -{2}iYG -(iC1U G x) ?LaGrange ?subsetIl //.
  by rewrite !inE Gx ?andbT in notZx *.
have Yx: x \in Y by rewrite -defCx inE Gx cent1id.
have ox: #[x] = p.
  by apply: nt_prime_order; rewrite ?(exponentP expY) // (group1_contra notZx).
have defCy: 'C_G(Y) = Z * <[x]>.
  apply/eqP; rewrite eq_sym eqEcard mulG_subG setIS ?centS //=.
  rewrite cycle_subG inE Gx cYx oCY TI_cardMg ?oZ -?orderE ?ox //=.
  by rewrite setIC prime_TIg -?orderE ?ox ?cycle_subG. 
have abelYt: p.-abelem (Y / Z).
  by rewrite (abelemS (quotientS _ sYG)) //= -/Z -defPhiG Phi_quotient_abelem.
have Yxt: coset Z x \in Y / Z by rewrite mem_quotient.
have{Yxt} [Et [sEtYt oEt defYt]] := p_abelem_split1 abelYt Yxt.
have nsZY: Z <| Y := normalS sZY sYG nsZG.
have [E defEt sZE sEY] := inv_quotientS nsZY sEtYt.
have{defYt} [_ defYt _ tiXEt] := dprodP defYt.
have defY: <[x]> \x E = Y.
  have nZX: <[x]> \subset 'N(Z) by rewrite cycle_subG.
  have TIxE: <[x]> :&: E = 1.
    rewrite prime_TIg -?orderE ?ox // -(quotientSGK _ sZE) ?quotient_cycle //.
    rewrite (sameP setIidPl eqP) eq_sym -defEt tiXEt -quotient_cycle //.
    by rewrite -subG1 quotient_sub1 // cycle_subG.
  rewrite dprodE //; last 1 first.
    by rewrite cycle_subG -sub_cent1 (subset_trans sEY) //= -/Y -defCx subsetIr.
  rewrite -[Y](quotientGK nsZY) -defYt cosetpreM -quotient_cycle //.
  rewrite quotientK // -(normC nZX) defEt quotientGK ?(normalS _ sEY) //.
  by rewrite -mulgA (mulSGid sZE).
have sEG := subset_trans sEY sYG; have nZE := subset_trans sEG nZG.
have defZE: 'Z(E) = Z.
  apply/eqP; rewrite eqEsubset andbC subsetI sZE subIset ?centS ?orbT //.
  rewrite -quotient_sub1 ?subIset ?nZE //= -tiXEt defEt subsetI andbC.
  rewrite quotientS ?center_sub //= -quotient_cycle //.
  rewrite -(quotient_mulgr _ <[x]>) /= -defCy quotientS // /Y.
  by case/dprodP: defY => _ <- _ _; rewrite centM setIA cent_cycle defCx setSI.
have pE := pgroupS sEG pG.
rewrite iYG; split=> // _; exists E.
split=> //; first 2 [by exists [group of <[x]>]].
  have:= sZE; rewrite subEproper; case/predU1P=> [<- | ltZE]; [by left | right].
  split; rewrite /special defZE ?oZ // (Phi_mulgen pE).
  have defE': E^`(1) = Z.
    have sE'Z: E^`(1) \subset Z by rewrite -defG' dergS.
    apply/eqP; rewrite eqEcard sE'Z -(prime_nt_dvdP _ _ (cardSg sE'Z)) ?oZ //=.
    rewrite -trivg_card1 (sameP eqP commG1P).
    by rewrite /proper sZE /= -/Z -defZE subsetI subxx in ltZE.
  split=> //; rewrite -defE'; apply/mulgen_idPl.
  by rewrite /= defE' -defPhiG (Phi_mulgen pG) mulgenC sub_gen ?subsetU ?MhoS.
have iEG: #|G : E| = (p ^ 2)%N.
  apply/eqP; rewrite -(@eqn_pmul2l #|E|) // LaGrange // -(LaGrange sYG) iYG.
  by rewrite -(dprod_card defY) -mulnA mulnCA -orderE ox.
pose M := 'C_G(E); exists [group of M] => /=.
have sMG: M \subset G := subsetIl _ _; have pM: p.-group M := pgroupS sMG pG.
have sZM: Z \subset M by rewrite setIS ?centS.
have oM: #|M| = (p ^ 3)%N by rewrite oCG ?iEG.
have defME: M * E = G.
  apply/eqP; rewrite eqEcard mulG_subG sMG sEG /= -(leq_pmul2r p_gt0).
  rewrite -{2}oZ -defZE /('Z(E)) -{2}(setIidPr sEG) setIAC -mul_cardG /= -/M.
  by rewrite -(LaGrange sEG) mulnAC -mulnA mulnC iEG oM.
have defZM: 'Z(M) = Z.
  apply/eqP; rewrite eqEsubset andbC subsetI sZM subIset ?centS ?orbT //=.
  by rewrite /Z /('Z(G)) -{2}defME centM setIA setIAC.
rewrite cprodE ?subsetIr // defME setIAC (setIidPr sEG) defZM isoMod3 //.
  rewrite abelianE (sameP setIidPl eqP) eqEcard subsetIl /= -/('Z(M)) -/M.
  by rewrite defZM oZ oM (leq_exp2l 3 1).
by apply: contra neYG => sMY; rewrite eqEsubset sYG -defME mulG_subG sMY.
Qed.

End ExtremalTheory.

Section ExponentPextraspecialTheory.

Variable p : nat.
Hypothesis p_pr : prime p.
Let p_gt1 := prime_gt1 p_pr.
Let p_gt0 := ltnW p_gt1.

Local Notation gtype := Pextraspecial.gtype.
Local Notation actp := (Pextraspecial.groupAction p).

Lemma card_pX1p2 : #|p^{1+2}| = (p ^ 3)%N.
Proof.
unlock gtype; rewrite -(sdprod_card (sdprod_sdpair _)).
rewrite !card_injm ?injm_sdpair1 ?injm_sdpair2 // !cardsT card_prod card_ord.
by rewrite -mulnA Zp_cast.
Qed.

Lemma Grp_pX1p2 :
  p^{1+2} \isog Grp (x : y : (x ^+ p, y ^+ p, [~ x, y, x], [~ x, y, y])).
Proof.
unlock gtype; apply: intro_isoGrp => [|rT H].
  apply/existsP; pose x := sdpair1 actp (0, 1)%R; pose y := sdpair2 actp 1%R.
  exists (x, y); rewrite /= !xpair_eqE; set z := [~ x, y]; set G := _ <*> _.
  have def_z: z = sdpair1 actp (1, 0)%R.
    rewrite [z]commgEl -sdpair_act ?inE //=.
    rewrite -morphV -?morphM ?inE //=; congr (sdpair1 _ (_, _)) => /=.
      by rewrite mulr1 mulKg.
    by rewrite mulVg.
  have def_xi: forall i, x ^+ i = sdpair1 _ (0, i%:R)%R.
    move=> i; rewrite -morphX ?inE //; congr (sdpair1 _ _).
    by apply/eqP; rewrite /eq_op /= !morphX ?inE ?exp1gn //=.
  have def_yi: forall i, y ^+ i = sdpair2 _ i%:R.
    by move=> i; rewrite -morphX ?inE //.
  have def_zi: forall i, z ^+ i = sdpair1 _ (i%:R, 0)%R.
    move=> i; rewrite def_z -morphX ?inE //; congr (sdpair1 _ _).
    by apply/eqP; rewrite /eq_op /= !morphX ?inE ?exp1gn ?andbT //=.
  rewrite def_xi def_yi char_Zp ?morph1 //.
  rewrite def_z -morphR ?inE // !commgEl -sdpair_act ?inE //= mulr0 addr0.
  rewrite mulVg -[_ * _]/(_ , _) /= !invg1 mulg1 !mul1g mulVg morph1 !andbT.
  have Gx: x \in G by rewrite -cycle_subG mulgen_subl.
  have Gy: y \in G by rewrite -cycle_subG mulgen_subr.
  rewrite eqEsubset subsetT -im_sdpair mulG_subG /= -/G; apply/andP; split.
    apply/subsetP=> u; case/morphimP=> [[i j] _ _ def_u].
    suffices ->: u = z ^+ i * x ^+ j by rewrite groupMl groupX ?groupR.
    rewrite def_zi def_xi !natr_Zp -morphM ?inE // def_u.
    by congr (sdpair1 _ (_, _)); rewrite ?mulg1 ?mul1g.
  apply/subsetP=> v; case/morphimP=> k _ _ def_v.
  suffices ->: v = y ^+ k by rewrite groupX.
  by rewrite def_yi natr_Zp.
case/existsP=> [[x y] /=]; set z := [~ x, y]; case/eqP=> defH xp yp.
move/eqP; move/commgP => czx; move/eqP; move/commgP => czy.
have zp: z ^+ p = 1 by rewrite -commXg // xp comm1g.
pose f1 (ij : 'Z_p * 'Z_p) := let: (i, j) := ij in z ^+ i * x ^+ j.
have f1M: {in setT &, {morph f1 : u v / u * v}}.
  case=> /= [i1 j1] [i2 j2] _ _ /=; rewrite {3 6}Zp_cast // !expg_mod //.
  rewrite !expgn_add !mulgA; congr (_ * _); rewrite -!mulgA; congr (_ * _).
  by apply: commuteX2.
pose f2 (k : 'Z_p) := y ^+ k.
have f2M: {in setT &, {morph f2 : u v / u * v}}.
  by move=> k1 k2 _ _; rewrite /f2 /= {3}Zp_cast // expg_mod // expgn_add.
have actf: {in setT & setT, morph_act actp 'J (Morphism f1M) (Morphism f2M)}.
  case=> /= i j k _ _; rewrite modn_addmr {4}Zp_cast // expg_mod // expgn_add.
  rewrite /f2 conjMg {1}/conjg (commuteX2 i k czy) mulKg -mulgA.
  congr (_ * _); rewrite (commuteX2 _ _ czx) mulnC expgn_mul.
  by rewrite -commXg // -commgX ?mulKVg // commXg // /commute commuteX.
apply/homgP; exists (xsdprod_morphism actf).
apply/eqP; rewrite eqEsubset -{2}defH -genM_mulgen gen_subG /= im_xsdprodm.
have Hx: x \in H by rewrite -cycle_subG -defH mulgen_subl.
have Hy: y \in H by rewrite -cycle_subG -defH mulgen_subr.
rewrite mulG_subG -andbA; apply/and3P; split.
- apply/subsetP=> u; case/morphimP=> [/= [i j] _ _ -> /=].
  by rewrite groupMl groupX ?groupR.
- by apply/subsetP=> v; case/morphimP=> /= k _ _ ->; rewrite groupX.
rewrite mulgSS ?cycle_subG //= morphimEdom; apply/imsetP.
  by exists (0, 1)%R; rewrite ?inE //= mul1g.
by exists 1%R; rewrite ?inE.
Qed.

Lemma pX1p2_pgroup : p.-group p^{1+2}.
Proof. by rewrite /pgroup card_pX1p2 pnat_exp pnat_id. Qed.

(* This is part of the existence half of Aschbacher ex. (8.7)(1) *)
Lemma pX1p2_extraspecial : extraspecial p^{1+2}.
Proof.
apply: (p3group_extraspecial pX1p2_pgroup); last first.
  by rewrite card_pX1p2 pfactorK.
case/existsP: (isoGrp_hom Grp_pX1p2) card_pX1p2 => [[x y]] /=.
case/eqP=> <- xp yp _ _ oXY.
apply: contraL (dvdn_cardMg <[x]> <[y]>) => cXY_XY.
rewrite -cent_mulgenEl ?(sub_abelian_cent2 cXY_XY) ?mulgen_subl ?mulgen_subr //.
rewrite oXY -!orderE pfactor_dvdn ?muln_gt0 ?order_gt0 // -leqNgt.
rewrite -(pfactorK 2 p_pr) dvdn_leq_log ?expn_gt0 ?p_gt0 //.
by rewrite dvdn_mul ?order_dvdn ?xp ?yp.
Qed.

(* This is part of the existence half of Aschbacher ex. (8.7)(1) *)
Lemma exponent_pX1p2 : odd p -> exponent p^{1+2} %| p.
Proof.
move=> p_odd; have pG := pX1p2_pgroup.
have ->: p^{1+2} = 'Ohm_1(p^{1+2}).
  apply/eqP; rewrite eqEsubset Ohm_sub andbT (OhmE 1 pG).
  case/existsP: (isoGrp_hom Grp_pX1p2) => [[x y]] /=.
  case/eqP=> <- xp yp _ _; rewrite mulgen_idl mulgen_idr genS //.
  by rewrite setIdE subsetI subset_gen subUset !sub1set !inE xp yp!eqxx.
have oddG: odd #|p^{1+2}| by rewrite card_pX1p2 odd_exp.
by have [-> _ _] := Ohm1_extraspecial_odd pG pX1p2_extraspecial oddG.
Qed.

(* This is the uniqueness half of Aschbacher ex. (8.7)(1) *)
Lemma isog_pX1p2 : forall (gT : finGroupType) (G : {group gT}),
  extraspecial G -> exponent G %| p -> #|G| = (p ^ 3)%N -> G \isog p^{1+2}.
Proof.
move=> gT G esG expGp oG; apply/(isoGrpP _ Grp_pX1p2).
rewrite card_pX1p2; split=> //.
have pG: p.-group G by rewrite /pgroup oG pnat_exp pnat_id.
have oZ := card_center_extraspecial pG esG.
have [x Gx notZx]: exists2 x, x \in G & x \notin 'Z(G).
  apply/subsetPn; rewrite proper_subn // properEcard center_sub oZ oG.
  by rewrite (ltn_exp2l 1 3).
have ox: #[x] = p.
  by apply: nt_prime_order; rewrite ?(exponentP expGp) ?(group1_contra notZx).
have [y Gy not_cxy]: exists2 y, y \in G & y \notin 'C[x].
  by apply/subsetPn; rewrite sub_cent1; rewrite inE Gx in notZx.
apply/existsP; exists (x, y) => /=; set z := [~ x, y].
have [[defPhiG defG'] _] := esG.
have Zz: z \in 'Z(G) by rewrite -defG' mem_commg.
have [Gz cGz] := setIP Zz; rewrite !xpair_eqE !(exponentP expGp) //.
have [_ nZG] := andP (center_normal G).
rewrite /commg /conjg !(centP cGz) // !mulKg mulVg !eqxx !andbT.
have sXY_G: <[x]> <*> <[y]> \subset G by rewrite mulgen_subG !cycle_subG Gx.
have defZ: <[z]> = 'Z(G).
  apply/eqP; rewrite eqEcard cycle_subG Zz oZ /= -orderE.
  rewrite (nt_prime_order p_pr) ?(exponentP expGp) //.
  by rewrite (sameP commgP cent1P) cent1C.
have sZ_XY: 'Z(G) \subset <[x]> <*> <[y]>.
  by rewrite -defZ cycle_subG groupR // mem_gen // inE cycle_id ?orbT.
rewrite eqEcard sXY_G /= oG -(LaGrange sZ_XY) oZ leq_pmul2l //.
rewrite -card_quotient ?(subset_trans sXY_G) //.
rewrite quotient_mulgen2 ?quotient_cycle ?cycle_subG ?(subsetP nZG) //.
have abelGz: p.-abelem (G / 'Z(G)) by rewrite -defPhiG Phi_quotient_abelem.
have [cGzGz expGz] := abelemP p_pr abelGz.
rewrite cent_mulgenEr ?(sub_abelian_cent2 cGzGz) ?cycle_subG ?mem_quotient //.
have oZx: #|<[coset 'Z(G) x]>| = p.
  rewrite -orderE (nt_prime_order p_pr) ?expGz ?mem_quotient //.
  by apply: contra notZx; move/eqP=> Zx; rewrite coset_idr ?(subsetP nZG).
rewrite TI_cardMg ?oZx -?orderE ?(nt_prime_order p_pr) ?expGz ?mem_quotient //.
  apply: contra not_cxy; move/eqP=> Zy.
  rewrite -cent_cycle (subsetP _ y (coset_idr _ Zy)) ?(subsetP nZG) //.
  by rewrite subIset ?centS ?orbT ?cycle_subG.
rewrite prime_TIg ?oZx // cycle_subG; apply: contra not_cxy.
case/cycleP=> i; rewrite -morphX ?(subsetP nZG) //; move/rcoset_kercosetP.
rewrite groupX ?(subsetP nZG) // cent1C; move/(_ isT isT); apply: subsetP.
rewrite mul_subG ?sub1set ?groupX ?cent1id //= -cent_cycle subIset // orbC.
by rewrite centS ?cycle_subG.
Qed.

End ExponentPextraspecialTheory.

Section GeneralExponentPextraspecialTheory.

Variable p : nat.

Lemma pX1p2id : p^{1+2*1} \isog p^{1+2}.
Proof. exact: ncprod1. Qed.

Lemma pX1p2S : forall n, xcprod_spec p^{1+2} p^{1+2*n} p^{1+2*n.+1}%type.
Proof. exact: ncprodS. Qed.

Lemma card_pX1p2n : forall n, prime p -> #|p^{1+2*n}| = (p ^ n.*2.+1)%N.
Proof.
move=> n p_pr; have pG := pX1p2_pgroup p_pr.
have oG := card_pX1p2 p_pr; have esG := pX1p2_extraspecial p_pr.
have oZ := card_center_extraspecial pG esG.
elim: n => [|n IHn]; first by rewrite (isog_card (ncprod0 _)) oZ.
case: pX1p2S => gz isoZ; rewrite -im_cpair cardMg_divn setI_im_cpair.
rewrite -injm_center ?{1}card_injm ?injm_cpairg1 ?injm_cpair1g ?center_sub //.
by rewrite oG oZ IHn -expn_add mulKn ?prime_gt0.
Qed.

Lemma pX1p2n_pgroup : forall n, prime p -> p.-group p^{1+2*n}.
Proof. by move=> n p_pr; rewrite /pgroup card_pX1p2n // pnat_exp pnat_id. Qed.

(* This is part of the existence half of Aschbacher (23.13) *)
Lemma exponent_pX1p2n : forall n, prime p -> odd p -> exponent p^{1+2*n} = p.
Proof.
move=> n p_pr odd_p; apply: prime_nt_dvdP => //.
  rewrite -dvdn1 -trivg_exponent -cardG_gt1 card_pX1p2n //.
  by rewrite (ltn_exp2l 0) // prime_gt1.
elim: n => [|n IHn].
  by rewrite (dvdn_trans (exponent_dvdn _)) ?card_pX1p2n.
case: pX1p2S => gz isoZ; rewrite -im_cpair /=.
apply/exponentP=> xy; case/imset2P=> x y C1x C2y ->{xy}.
rewrite expMgn; last exact: (centsP (im_cpair_cent isoZ)).
rewrite (exponentP _ y C2y) ?exponent_injm ?injm_cpair1g // mulg1.
by rewrite (exponentP _ x C1x) ?exponent_injm ?injm_cpairg1 // exponent_pX1p2.
Qed.

(* This is part of the existence half of Aschbacher (23.13) and (23.14) *)
Lemma pX1p2n_extraspecial : forall n,
  prime p -> n > 0 -> extraspecial p^{1+2*n}.
Proof.
move=> n p_pr; elim: n => [//|n IHn _].
have esG := pX1p2_extraspecial p_pr.
have [n0 | n_gt0] := posnP n.
  by apply: isog_extraspecial esG; rewrite isog_sym n0 pX1p2id.
case: pX1p2S (pX1p2n_pgroup n.+1 p_pr) => gz isoZ pGn.
apply: (cprod_extraspecial pGn (im_cpair_cprod isoZ) (setI_im_cpair isoZ)).
  by apply: injm_extraspecial esG; rewrite ?injm_cpairg1.
by apply: injm_extraspecial (IHn n_gt0); rewrite ?injm_cpair1g.
Qed.

(* This is the uniqueness half of Aschbacher (23.13); the proof incorporates *)
(* in part the proof that symplectic spaces are hyperbolic (19.16).          *)
Lemma isog_pX1p2n : forall n (gT : finGroupType) (G : {group gT}),
    prime p -> extraspecial G -> #|G| = (p ^ n.*2.+1)%N -> exponent G %| p ->
  G \isog p^{1+2*n}.
Proof.
move=> n gT G p_pr esG oG expG; have p_gt1 := prime_gt1 p_pr.
have not_le_p3_p: ~~ (p ^ 3 <= p) by rewrite (leq_exp2l 3 1).
have pG: p.-group G by rewrite /pgroup oG pnat_exp pnat_id.
have oZ := card_center_extraspecial pG esG.
have{pG esG} [Es p3Es defG] := extraspecial_structure pG esG.
set Z := 'Z(G) in oZ defG p3Es.
elim: Es {+}G => [|E Es IHs] S in n oG expG p3Es defG *.
  rewrite big_nil cprod1g in defG; rewrite -defG.
  have ->: n = 0%N.
    apply: double_inj; apply/eqP.
    by rewrite -eqSS -(eqn_exp2l _ _ p_gt1) -oG -defG oZ.
  by rewrite isog_cyclic_card prime_cyclic ?oZ ?card_pX1p2n //=.
rewrite big_cons -cprodA in defG; rewrite /= -andbA in p3Es.
have [[_ T _ defT] defET cTE] := cprodP defG; rewrite defT in defET cTE defG.
case/and3P: p3Es; move/eqP=> oE; move/eqP=> defZE; move/IHs=> {IHs}IHs.
have not_cEE: ~~ abelian E.
  apply: contra not_le_p3_p => cEE; rewrite -oE -oZ -defZE.
  by rewrite center_abelian_id.
have sES: E \subset S by rewrite -defET mulG_subl.
have sTS: T \subset S by rewrite -defET mulG_subr.
have expE: exponent E %| p by exact: dvdn_trans (exponentS sES) expG.
have expT: exponent T %| p by exact: dvdn_trans (exponentS sTS) expG.
have{expE not_cEE} isoE: E \isog p^{1+2}.
  apply: isog_pX1p2 => //.
  by apply: card_p3group_extraspecial p_pr oE _; rewrite defZE.
have sZT: 'Z(E) \subset T.
  by case/cprodP: defT => [[U _ -> _] <- _]; rewrite defZE mulG_subr.
case def_n: n => [|n'].
  case/negP: not_le_p3_p; rewrite def_n in oG; rewrite -oE -[p]oG.
  exact: subset_leq_card.
have zI_ET: E :&: T = 'Z(E).
  by apply/eqP; rewrite eqEsubset subsetI sZT subsetIl setIS // centsC.
have{n def_n oG} oT: #|T| = (p ^ n'.*2.+1)%N.
  apply/eqP; rewrite -(eqn_pmul2l (cardG_gt0 E)) mul_cardG zI_ET defET.
  by rewrite defZE oE oG oZ -expnSr -expn_add def_n.
have{IHs oT expT defT Es} isoT: T \isog p^{1+2*n'} by rewrite IHs.
case: pX1p2S => gz isoZ; rewrite (isog_cprod_by _ defG) //.
exact: Aut_extraspecial_full (pX1p2_pgroup p_pr) (pX1p2_extraspecial p_pr).
Qed.

End GeneralExponentPextraspecialTheory.

Lemma isog_2X1p2 : 2^{1+2} \isog 'D_8.
Proof.
have pr2: prime 2 by []; have oG := card_pX1p2 pr2; rewrite -[8]oG.
case/existsP: (isoGrp_hom (Grp_pX1p2 pr2)) => [[x y]] /=.
rewrite -/2^{1+2}; case/eqP=> defG x2 y2 _ _.
have not_oG_2: ~~ (#|2^{1+2}| %| 2) by rewrite oG.
have ox: #[x] = 2.
  apply: nt_prime_order => //; apply: contra not_oG_2 => x1.
  by rewrite -defG (eqP x1) cycle1 mulgen1G order_dvdn y2.
have oy: #[y] = 2.
  apply: nt_prime_order => //; apply: contra not_oG_2 => y1.
  by rewrite -defG (eqP y1) cycle1 mulgenG1 order_dvdn x2.
rewrite -defG mulgen_idl mulgen_idr involutions_gen_dihedral //.
apply: contra not_oG_2 => eq_xy; rewrite -defG (eqP eq_xy) (mulgen_idPl _) //.
by rewrite -orderE oy.
Qed.

Lemma Q8_extraspecial : extraspecial 'Q_8.
Proof.
have gt32: 3 > 2 by []; have isoQ: 'Q_8 \isog 'Q_(2 ^ 3) by exact: isog_refl.
have [[x y] genQ _] := generators_quaternion gt32 isoQ.
have [_ [defQ' defPhiQ _ _]] := quaternion_structure gt32 genQ isoQ.
case=> defZ oZ _ _ _ _ _; split; last by rewrite oZ.
by split; rewrite ?defPhiQ defZ.
Qed.

Lemma DnQ_P : forall n, xcprod_spec 'D^n 'Q_8 ('D^n*Q)%type.
Proof.
move=> n; apply: xcprodP.
have pQ: 2.-group 'Q_(2 ^ 3) by rewrite /pgroup card_quaternion.
have{pQ} oZQ := card_center_extraspecial pQ Q8_extraspecial.
suffices oZDn: #|'Z('D^n)| = 2.
  by rewrite isog_cyclic_card ?prime_cyclic ?oZQ ?oZDn.
have [-> | n_gt0] := posnP n; first by rewrite center_ncprod0 card_pX1p2n.
have pr2: prime 2 by []; have pDn := pX1p2n_pgroup n pr2.
exact: card_center_extraspecial (pX1p2n_extraspecial pr2 n_gt0).
Qed.

Lemma card_DnQ : forall n, #|'D^n*Q| = (2 ^ n.+1.*2.+1)%N.
Proof.
move=> n; have oQ: #|'Q_(2 ^ 3)| = 8 by rewrite card_quaternion.
have pQ: 2.-group 'Q_8 by rewrite /pgroup oQ.
case: DnQ_P => gz isoZ.
rewrite -im_cpair cardMg_divn setI_im_cpair cpair_center_id.
rewrite -injm_center 3?{1}card_injm ?injm_cpairg1 ?injm_cpair1g ?center_sub //.
rewrite oQ card_pX1p2n // (card_center_extraspecial pQ Q8_extraspecial).
by rewrite -divn_mulA // mulnC -(expn_add 2 2).
Qed.

Lemma DnQ_pgroup : forall n, 2.-group 'D^n*Q.
Proof. by move=> n; rewrite /pgroup card_DnQ pnat_exp. Qed.

(* Final part of the existence half of Aschbacher (23.14). *)
Lemma DnQ_extraspecial : forall n, extraspecial 'D^n*Q.
Proof.
move=> n; case: DnQ_P (DnQ_pgroup n) => gz isoZ pDnQ.
have [injDn injQ] := (injm_cpairg1 isoZ, injm_cpair1g isoZ).
have [n0 | n_gt0] := posnP n.
  rewrite -im_cpair mulSGid; first exact: injm_extraspecial Q8_extraspecial.
  apply/setIidPl; rewrite setI_im_cpair -injm_center //=.
  by congr (_ @* _); rewrite n0 center_ncprod0.
apply: (cprod_extraspecial pDnQ (im_cpair_cprod isoZ) (setI_im_cpair _)).
  exact: injm_extraspecial (pX1p2n_extraspecial _ _).
exact: injm_extraspecial Q8_extraspecial.
Qed.

(* A special case of the uniqueness half of Achsbacher (23.14). *)
Lemma isog_card8_extraspecial : forall (gT : finGroupType) (G : {group gT}),
  #|G| = 8 -> extraspecial G -> (G \isog 'D_8) || (G \isog 'Q_8).
Proof.
move=> gT G oG esG; have pG: 2.-group G by rewrite /pgroup oG.
apply/norP=> [[notG_D8 notG_Q8]].
have not_extG: extremal_class G = NotExtremal.
  by rewrite /extremal_class oG andFb (negPf notG_D8) (negPf notG_Q8).
have [x Gx ox] := exponent_witness (pgroup_nil pG).
pose X := <[x]>; have cycX: cyclic X := cycle_cyclic x.
have sXG: X \subset G by rewrite cycle_subG.
have iXG: #|G : X| = 2.
  by rewrite -divgS // oG -orderE -ox exponent_2extraspecial.
have not_cGG := extraspecial_non_abelian esG.
have:= maximal_cycle_extremal pG not_cGG cycX sXG iXG.
by rewrite /extremal2 not_extG.
Qed.

(* The uniqueness half of Achsbacher (23.14). The proof incorporates in part  *)
(* the proof that symplectic spces are hyperbolic (Aschbacher (19.16)), and   *)
(* the determination of quadratic spaces over 'F_2 (21.2); however we use     *)
(* the second part of exercise (8.4) to avoid resorting to Witt's lemma and   *)
(* Galois theory as in (20.9) and (21.1).                                     *)
Lemma isog_2extraspecial : forall (gT : finGroupType) (G : {group gT}) n,
  #|G| = (2 ^ n.*2.+1)%N -> extraspecial G -> G \isog 'D^n \/ G \isog 'D^n.-1*Q.
Proof.
move=> gT G n; elim: n G => [|n IHn] G oG esG.
  case/negP: (extraspecial_non_abelian esG).
  by rewrite cyclic_abelian ?prime_cyclic ?oG.
have pG: 2.-group G by rewrite /pgroup oG pnat_exp.
have oZ:= card_center_extraspecial pG esG.
have: 'Z(G) \subset 'Ohm_1(G).
  apply/subsetP=> z Zz; rewrite (OhmE _ pG) mem_gen //.
  by rewrite inE -order_dvdn -oZ order_dvdG ?(subsetP (center_sub G)).
rewrite subEproper; case/predU1P=> [defG1 | ltZG1].
  have [n' n'_gt2 isoG]: exists2 n', n' > 2 & G \isog 'Q_(2 ^ n').
    apply/quaternion_classP; apply/eqP.
    have not_cycG: ~~ cyclic G.
      by apply: contra (extraspecial_non_abelian esG); exact: cyclic_abelian.
    move: oZ; rewrite defG1; move/prime_Ohm1P; rewrite (negPf not_cycG) /=.
    by apply=> //; apply: contra not_cycG; move/eqP->; exact: cyclic1.
  have [n0 n'3]: n = 0%N /\ n' = 3.
    have [[x y] genG _] := generators_quaternion n'_gt2 isoG.
    have n'3: n' = 3.
      have [_ [_ _ oG' _] _ _ _] := quaternion_structure n'_gt2 genG isoG.
      apply/eqP; rewrite -(subnKC (ltnW n'_gt2)) subn2 !eqSS -(@eqn_exp2l 2) //.
      by rewrite -oG' -oZ; case: esG => [[_ ->]].
    by move/eqP: oG; have [-> _ _ _] := genG; rewrite n'3 eqn_exp2l //; case n.
  right; rewrite (isog_trans isoG) // n'3 n0 /=.
  case: DnQ_P => z isoZ; rewrite -im_cpair mulSGid ?sub_isog ?injm_cpair1g //.
  apply/setIidPl; rewrite setI_im_cpair -injm_center ?injm_cpairg1 //.
  by rewrite center_ncprod0.
case/andP: ltZG1 => _; rewrite (OhmE _ pG) gen_subG.
case/subsetPn=> x; case/setIdP=> Gx; move/eqP=> x2 notZx.
have ox: #[x] = 2 by exact: nt_prime_order (group1_contra notZx).
have Z'x: x \in G :\: 'Z(G) by rewrite inE notZx.
have [E [R [[oE oR] [defG ziER]]]] := split1_extraspecial pG esG Z'x.
case=> defZE defZR [esE Ex] esR.
have isoE: E \isog 2^{1+2}.
  apply: isog_trans (isog_symr isog_2X1p2).
  case/orP: (isog_card8_extraspecial oE esE) => // isoE; case/negP: notZx.
  have gt32: 3 > 2 by [].
  have [[y z] genE _] := generators_quaternion gt32 isoE.
  have [_ _ [defZx _ eq_y2 _ _] _ _] := quaternion_structure gt32 genE isoE.
  by rewrite (eq_y2 x) // -cycle_subG -defZx defZE.
rewrite oG doubleS 2!expnS divn_pmul2l ?mulKn // in oR.
have{esR} [defR | esR] := esR.
  have ->: n = 0%N by move/eqP: oR; rewrite defR oZ (eqn_exp2l 1) //; case n.
  left; apply: isog_trans (isog_symr (ncprod1 _)).
  by rewrite -defG defR -defZE cprod_center_id.
have AutZin2_1p2: Aut_in (Aut 2^{1+2}) 'Z(2^{1+2}) \isog Aut 'Z(2^{1+2}).
  exact: Aut_extraspecial_full (pX1p2_pgroup _) (pX1p2_extraspecial _).
have [isoR | isoR] := IHn R oR esR.
  by left; case: pX1p2S => gz isoZ; rewrite (isog_cprod_by _ defG).
have n_gt0: n > 0.
  have pR: 2.-group R by rewrite /pgroup oR pnat_exp.
  have:= min_card_extraspecial pR esR.
  by rewrite oR leq_exp2l // ltnS (leq_double 1).
case: DnQ_P isoR => gR isoZR /=; rewrite isog_sym; case/isogP=> fR injfR im_fR.
have [injDn injQ] := (injm_cpairg1 isoZR, injm_cpair1g isoZR).
pose Dn1 := cpairg1 isoZR @* 'D^n.-1; pose Q := cpair1g isoZR @* 'Q_8.
have defR: fR @* Dn1 \* fR @* Q = R.
  rewrite cprodE ?morphim_cents ?im_cpair_cent //.
  by rewrite -morphimMl ?subsetT ?im_cpair.
rewrite -defR cprodA in defG.
have [[Dn _ defDn _] _ _] := cprodP defG; rewrite defDn in defG.
have isoDn: Dn \isog 'D^n.
  rewrite -(prednK n_gt0); case: pX1p2S => gz isoZ.
  rewrite (isog_cprod_by _ defDn) //; last 1 first.
    by rewrite isog_sym (isog_trans _ (sub_isog _ _)) ?subsetT // sub_isog.
  rewrite /= -morphimIim im_fR setIA ziER; apply/setIidPl.
  rewrite defZE -defZR -{1}im_fR -injm_center // morphimS //.
  by rewrite -cpairg1_center morphimS // center_sub.
right; case: DnQ_P => gz isoZ; rewrite (isog_cprod_by _ defG) //; first 1 last.
- exact: Aut_extraspecial_full (pX1p2n_pgroup _ _) (pX1p2n_extraspecial _ _).
- by rewrite isog_sym (isog_trans _ (sub_isog _ _)) ?subsetT // sub_isog.
rewrite /= -morphimIim; case/cprodP: defDn => _ defDn cDn1E.
rewrite setICA setIA -defDn -group_modr ?morphimS ?subsetT //.
rewrite /= im_fR (setIC R) ziER -center_prod // defZE -defZR.
rewrite mulSGid /=; last first.
  by rewrite -{1}im_fR -injm_center // -cpairg1_center !morphimS ?center_sub.
rewrite -injm_center ?subsetT // -injmI // setI_im_cpair.
by rewrite -injm_center // cpairg1_center injm_center // im_fR mulGid.
Qed.

(* The first concluding remark of Aschbacher (23.14). *)
Lemma rank_Dn : forall n, 'r_2('D^n) = n.+1.
Proof.
elim=> [|n IHn]; first by rewrite p_rank_abelem ?prime_abelem ?card_pX1p2n.
have oDDn: #|'D^n.+1| = (2 ^ n.+1.*2.+1)%N by exact: card_pX1p2n.
have esDDn: extraspecial 'D^n.+1 by exact: pX1p2n_extraspecial.
do [case: pX1p2S => gz isoZ; set DDn := [set: _]] in oDDn esDDn *.
have pDDn: 2.-group DDn by rewrite /pgroup oDDn pnat_exp.
apply/eqP; rewrite eqn_leq; apply/andP; split.
  have [E EprE]:= p_rank_witness 2 [group of DDn].
  have [sEDDn abelE <-] := pnElemP EprE; have [pE cEE _]:= and3P abelE.
  rewrite -(@leq_exp2l 2) // -p_part part_pnat_id // -leq_sqr -expn_mulr -mulnn.
  rewrite muln2 doubleS expnS -oDDn -(@leq_pmul2r #|'C_DDn(E)|) ?cardG_gt0 //.
  rewrite {1}(card_subcent_extraspecial pDDn) // mulnCA -mulnA LaGrange //=.
  rewrite mulnAC mulnA leq_pmul2r ?cardG_gt0 // setTI.
  have ->: (2 * #|'C(E)| = #|'Z(DDn)| * #|'C(E)|)%N.
    by rewrite (card_center_extraspecial pDDn).
  by rewrite leq_mul ?subset_leq_card ?subsetIl.
have [inj1 injn] := (injm_cpairg1 isoZ, injm_cpair1g isoZ).
pose D := cpairg1 isoZ @* 2^{1+2}; pose Dn := cpair1g isoZ @* 'D^n.
have [E EprE] := p_rank_witness 2 [group of Dn].
rewrite injm_p_rank //= IHn in EprE; have [sEDn abelE dimE]:= pnElemP EprE.
have [x [Dx ox] notDnx]: exists x, [/\ x \in D, #[x] = 2 & x \notin Dn].
  have isoD: D \isog 'D_(2 ^ 3).
    by rewrite isog_sym -(isog_transl _ isog_2X1p2) sub_isog.
  have [//| [x y] genD [oy _]] := generators_2dihedral _ isoD.
  have [_ _ _ X'y] := genD; case/setDP: X'y; rewrite /= -/D => Dy notXy.
  exists y; split=> //; apply: contra notXy => Dny.
  case/dihedral2_structure: genD => // _ _ _ _ [defZD _ _ _ _].
  by rewrite (subsetP (cycleX x 2)) // -defZD -setI_im_cpair inE Dy.
have def_xE: <[x]> \x E = <[x]> <*> E.
  rewrite dprodEgen ?prime_TIg -?orderE ?ox // cycle_subG.
    by rewrite (subsetP (centS sEDn)) // (subsetP (im_cpair_cent _)).
  by rewrite (contra (subsetP sEDn x)).
apply/p_rank_geP; exists (<[x]> <*> E)%G.
rewrite 2!inE subsetT (dprod_abelem _ def_xE) abelE -(dprod_card def_xE).
by rewrite prime_abelem -?orderE ?ox //= logn_mul ?cardG_gt0 ?dimE.
Qed.

(* The second concluding remark of Aschbacher (23.14). *)
Lemma rank_DnQ : forall n, 'r_2('D^n*Q) = n.+1.
Proof.
move=> n; have pDnQ: 2.-group 'D^n*Q := DnQ_pgroup n.
have esDnQ: extraspecial 'D^n*Q := DnQ_extraspecial n.
do [case: DnQ_P => gz isoZ; set DnQ := setT] in pDnQ esDnQ *.
suffices [E]: exists2 E, E \in 'E*_2(DnQ) & logn 2 #|E| = n.+1.
  by rewrite (pmaxElem_extraspecial pDnQ esDnQ); case/pnElemP=> _ _ <-.
have oZ: #|'Z(DnQ)| = 2 by exact: card_center_extraspecial.
pose Dn := cpairg1 isoZ @* 'D^n; pose Q := cpair1g isoZ @* 'Q_8.
have [injDn injQ] := (injm_cpairg1 isoZ, injm_cpair1g isoZ).
have [E EprE]:= p_rank_witness 2 [group of Dn].
have [sEDn abelE dimE] := pnElemP EprE; have [pE cEE eE]:= and3P abelE.
rewrite injm_p_rank // rank_Dn in dimE; exists E => //.
have sZE: 'Z(DnQ) \subset E.
  have maxE := subsetP (p_rankElem_max _ _) E EprE.
  have abelZ: 2.-abelem 'Z(DnQ) by rewrite prime_abelem ?oZ.
  rewrite -(Ohm1_id abelZ) (OhmE _ (abelem_pgroup abelZ)) gen_subG.
  rewrite in_pmaxElemE // in maxE; rewrite -(eqP maxE) !setIdE setSI //=.
  by rewrite -cpairg1_center injm_center // setIS ?centS.
have scE: 'C_Dn(E) = E.
  apply/eqP; rewrite eq_sym eqEcard subsetI sEDn -abelianE cEE /=.
  have [n0 | n_gt0] := posnP n.
    rewrite subset_leq_card // subIset // (subset_trans _ sZE) //.
    by rewrite -cpairg1_center morphimS // n0 center_ncprod0.
  have pDn: 2.-group Dn by rewrite morphim_pgroup ?pX1p2n_pgroup.
  have esDn: extraspecial Dn.
    exact: injm_extraspecial (pX1p2n_extraspecial _ _).
  rewrite dvdn_leq ?cardG_gt0 // (card_subcent_extraspecial pDn) //=.
  rewrite -injm_center // cpairg1_center (setIidPl sZE) oZ.
  rewrite -(dvdn_pmul2l (cardG_gt0 E)) mulnn mulnCA LaGrange //.
  rewrite card_injm ?card_pX1p2n // -expnS pfactor_dvdn ?expn_gt0 ?cardG_gt0 //.
  by rewrite logn_exp dimE mul2n.
apply/pmaxElemP; split=> [|F E2F sEF]; first by rewrite inE subsetT abelE.
have{E2F} [_ abelF] := pElemP E2F; have [pF cFF eF] := and3P abelF.
apply/eqP; rewrite eqEsubset sEF andbT; apply/subsetP=> x Fx.
have DnQx: x \in Dn * Q by rewrite im_cpair inE.
have{DnQx} [y z Dn_y Qz def_x]:= imset2P DnQx.
have{Dn_y} Ey: y \in E.
  have cEz: z \in 'C(E).
    by rewrite (subsetP _ z Qz) // centsC (subset_trans sEDn) ?im_cpair_cent.
  rewrite -scE inE Dn_y -(groupMr _ cEz) -def_x (subsetP (centS sEF)) //.
  by rewrite (subsetP cFF).
rewrite def_x groupMl // (subsetP sZE) // -cpair1g_center injm_center //= -/Q.
have: z \in 'Ohm_1(Q).
  rewrite (OhmE 1 (pgroupS (subsetT Q) pDnQ)) mem_gen // inE Qz /=.
  rewrite -[z](mulKg y) -def_x (exponentP eF) ?groupM //.
  by rewrite groupV (subsetP sEF).
have isoQ: Q \isog 'Q_(2 ^ 3) by rewrite isog_sym sub_isog.
have [//|[u v] genQ _] := generators_quaternion _ isoQ.
by case/quaternion_structure: genQ => // _ _ [-> _ _ [-> _] _] _ _.
Qed.

(* The final concluding remark of Aschbacher (23.14). *)
Lemma not_isog_Dn_DnQ : forall n, ~~ ('D^n \isog 'D^n.-1*Q).
Proof.
case=> [|n] /=; first by rewrite isogEcard card_pX1p2n // card_DnQ andbF.
apply: contraL (leqnn n.+1) => isoDn1DnQ.
by rewrite -ltnNge -rank_Dn (isog_p_rank isoDn1DnQ) rank_DnQ.
Qed.

Section MoreRepresentation.

Variables (F : fieldType) (gT : finGroupType) (G : {group gT}) (n : nat).
Variable (rG : mx_representation F G n).

Lemma rfix_mx_conjsg : forall (A : {set gT}) x,
  x \in G -> A \subset G -> (rfix_mx rG (A :^ x) :=: rfix_mx rG A *m rG x)%MS.
Proof.
move=> A x Gx sAG; pose rf y := rfix_mx rG (A :^ y).
suffices{x Gx} IH: {in G &, forall y z, rf y *m rG z <= rf (y * z)%g}%MS.
  apply/eqmxP; rewrite -/(rf x) -[A]conjsg1 -/(rf 1%g).
  rewrite -{4}[x] mul1g -{1}[rf x](repr_mxKV rG Gx) -{1}(mulgV x).
  by rewrite submxMr IH ?groupV.
move=> x y Gx Gy; apply/rfix_mxP=> zxy; rewrite actM; case/imsetP=> zx Azx ->.
have Gzx: zx \in G by apply: subsetP Azx; rewrite conj_subG.
rewrite -mulmxA -repr_mxM ?groupM ?groupV // -conjgC repr_mxM // mulmxA.
by rewrite rfix_mx_id.
Qed.

End MoreRepresentation.

(* Interface to the Wielandt fixpoint formula; to become the main conclusion  *)
(* of a new file.                                                             *)
Theorem solvable_Wielandt_fixpoint : forall (I : finType) (gT : finGroupType),
    forall (A : I -> {group gT}) (n m : I -> nat) (G V : {group gT}),
    (forall i, m i + n i > 0 -> A i \subset G) ->
    G \subset 'N(V) -> coprime #|V| #|G| -> solvable V ->
    {in G, forall a, \sum_(i | a \in A i) m i = \sum_(i | a \in A i) n i}%N ->
  (\prod_i #|'C_V(A i)| ^ (m i * #|A i|)
    = \prod_i #|'C_V(A i)| ^ (n i * #|A i|))%N.
Admitted.

(* Elementary theory of Frobenius groups; should move to (and become the main *)
(* contents of) the frobenius.v file.                                         *)
(*  We define the following:                                                  *)
(*    [Frobenius G = K ><| H] <=>                                             *)
(*       G is (isomorphic to) a Frobenius group with kernel K and complement  *)
(*       H. This is an effective predicate (in bool), which tests the         *)
(*       equality with the semidirect product, and then the fact that H is a  *)
(*       proper self-normalizing TI-subgroup of G.                            *)
(*    [Frobenius G with complement H] <=>                                     *)
(*       G is (isomorphic to) a Frobenius group with complement H; same as    *)
(*       above, but without the semi-direct product.                          *)
(*    Frobenius_action G H S to <->                                           *)
(*       The action to of G on S defines an isomorphism of G with a           *)
(*       (permutation) Frobenius group, i.e., to is faithful and transitive   *)
(*       on S, no nontrivial element of G fixes more than one opint in S, and *)
(*       H is the stabilizer of some element of S, and non-trivial. Thus,     *)
(*        Frobenius_action G H S 'P                                           *)
(*       asserts that G is a Frobenius group in the classic sense.            *)
(*    has_Frobenius_action G H <->                                            *)
(*        Frobenius_action G H S to hold for some sT : finType, S : {set st}  *)
(*        and to : {action gT &-> sT}. This is a predicate in Prop, but is    *)
(*        exactly reflected by [Frobenius G with complement H] : bool.        *)
(* Note that at this point we do not have the existence or nilpotence of      *)
(* Frobenius kernels. This is not a problem, because in all the applications  *)
(* we make of Frobenius groups, the kernel and complement are already known.  *)

Section FrobeniusDefinitions.

Variables (gT : finGroupType) (G K H : {set gT}).

Definition Frobenius_group_with_complement :=
  [&& H \proper G, trivIset (H^# :^: G) & 'N_G(H) == H].

Definition Frobenius_group_with_kernel_and_complement :=
  (K ><| H == G) && Frobenius_group_with_complement.

Section FrobeniusAction.

Variables (sT : finType) (S : {set sT}) (to : {action gT &-> sT}).

Definition Frobenius_action :=
  [/\ [faithful G, on S | to],
      [transitive G, on S | to],
      {in G^#, forall x, #|'Fix_(S | to)[x]| <= 1},
      H != 1
    & exists2 u, u \in S & H = 'C_G[u | to]].

End FrobeniusAction.

CoInductive has_Frobenius_action : Prop :=
  HasFrobeniusAction sT S to of @Frobenius_action sT S to.

End FrobeniusDefinitions.

Notation "[ 'Frobenius' G 'with' 'complement' H ]" :=
  (Frobenius_group_with_complement G H)
  (at level 0, G at level 50, H at level 35,
   format "[ 'Frobenius'  G  'with'  'complement'  H ]") : group_scope.

Notation "[ 'Frobenius' G = K ><| H ]" :=
  (Frobenius_group_with_kernel_and_complement G K H)
  (at level 0, G at level 50, K, H at level 35,
   format "[ 'Frobenius'  G  =  K  ><|  H ]") : group_scope.

Section FrobeniusBasics.

Variable gT : finGroupType.
Implicit Type G H K R : {group gT}.

Lemma TIconjP : forall G H,
  reflect {in G &, forall x y, x * y^-1 \in 'N_G(H) \/ H :^ x :&: H :^ y = 1}
          (trivIset (H^# :^: G)).
Proof.
move=> G H; have defH := setD1K (group1 H).
apply: (iffP trivIsetP) => [tiHG x y Gx Gy | tiHG Hx Hy].
  have [||defHx|tiHxy] := tiHG (H^# :^ x) (H^# :^ y); rewrite ?mem_imset //.
    left; rewrite !inE groupM ?groupV //=.
    by rewrite -defH conjUg conjs1g conjsgM defHx actK.
  by right; apply/trivgP; rewrite -setDeq0 setDIl -!conjD1g disjoint_setI0.
case/imsetP=> x Gx ->{Hx}; case/imsetP=> y Gy ->{Hy}.
rewrite disjointEsetI !conjD1g -setDIl setDeq0.
have [nHxy|->] := tiHG x y Gx Gy; [left | by right].
by case/setIP: nHxy => _ nHxy; rewrite -{2}(normP nHxy) actM actKV.
Qed.
Implicit Arguments TIconjP [G H].

Lemma TIconj_SN_P : forall G H,
    H :!=: 1 -> H \subset G ->
  reflect {in G :\: H, forall x, H :&: H :^ x = 1}
          (trivIset (H^# :^: G) && ('N_G(H) == H)).
Proof.
move=> G H ntH sHG; apply: (iffP idP) => [|sntiHG].
  case/andP; move/TIconjP=> tiHG; move/eqP=> snHG x; case/setDP=> Gx notHx.
  have [//||] := tiHG 1 x _ Gx; rewrite ?conjsg1 //.
  by rewrite  mul1g snHG groupV (negPf notHx).
apply/andP; split.
  apply/TIconjP=> x y Gx Gy.
  have Gxy: x * y^-1 \in G by rewrite groupM ?groupV.
  case Hxy: (x * y^-1 \in H); [left | right].
    by rewrite inE Gxy (subsetP (normG H)).
  by rewrite -(mulgKV y x) actM -conjIg setIC sntiHG ?conjs1g ?inE ?Hxy.
rewrite eqEsubset subsetI sHG normG !andbT -setDeq0 setDE setIAC -setDE.
apply: contraR ntH; case/set0Pn=> x; case/setIP=> Gx nHx.
by rewrite -(sntiHG x Gx) (normP nHx) setIid.
Qed.

Lemma Frobenius_actionP : forall G H,
  reflect (has_Frobenius_action G H) [Frobenius G with complement H].
Proof.
move=> G H; apply: (iffP andP) => [[] | [sT S to [ffulG transG regG ntH]]].
  rewrite properEneq; case/andP=> neqHG sHG; case/andP=> tiHG; move/eqP=> snHG.
  suffices: Frobenius_action G H (rcosets H G) 'Rs by exact: HasFrobeniusAction.
  pose Hfix x := 'Fix_(rcosets H G | 'Rs)[x].
  have regG: {in G^#, forall x, #|Hfix x| <= 1}.
  - move=> x; case/setD1P=> nt_x Gx.
    have [->|[Hy]] := set_0Vmem (Hfix x); first by rewrite cards0.
    rewrite -(card1 Hy); case/setIP; case/imsetP=> y Gy ->{Hy} cHyx.
    apply: subset_leq_card; apply/subsetP=> Hz.
    case/setIP; case/imsetP=> z Gz ->{Hz} cHzx.
    rewrite -!sub_astab1 !astab1_act !sub1set astab1Rs in cHyx cHzx *.
    rewrite !inE (canF_eq (actK _ _)) -actM /= rcosetE rcoset_id // -snHG.
    have [//| tiHyz] := TIconjP tiHG y z Gy Gz.
    by case/negP: nt_x; rewrite -in_set1 -[[set 1]]tiHyz inE cHyx.
  have ntH: H :!=: 1.
    by apply: contra neqHG; move/eqP=> H1; rewrite -snHG H1 norm1 setIT.
  split=> //; first 1 last; first exact: transRs_rcosets.
    by exists (H : {set gT}); rewrite ?orbit_refl // astab1Rs (setIidPr sHG).
  apply/subsetP=> y; case/setIP=> Gy cHy; apply: contraR neqHG => nt_y.
  rewrite (index1g sHG) //; apply/eqP; rewrite eqn_leq indexg_gt0 andbT.
  apply: leq_trans (regG y _); last by rewrite setDE 2!inE Gy nt_y /=.
  by rewrite /Hfix (setIidPl _) -1?astabC ?sub1set.
case=> u Su defH; have sHG: H \subset G by rewrite defH subsetIl.
rewrite properEneq sHG andbT; split.
  apply: contra ntH; move/eqP=> /= defG.
  suffices defS: S = [set u] by rewrite -(trivgP ffulG) /= defS defH.
  apply/eqP; rewrite eq_sym eqEcard sub1set Su.
  by rewrite -(atransP transG u Su) card_orbit -defH defG indexgg cards1.
apply/(TIconj_SN_P ntH sHG)=> x; case/setDP=> Gx notHx.
apply/trivgP; apply/subsetP=> y; rewrite /= -sub1set defH conjIg -astab1_act.
rewrite !(sub_astab1, subsetI) sub1set -andbA; case/and4P=> Gy cuy _ cuxy.
move/implyP: (regG y); rewrite in_setD Gy; apply: contraLR => -> /=.
rewrite (cardD1 u) (cardD1 (to u x)) inE Su cuy inE /= inE cuxy.
rewrite (actsP (atrans_acts transG)) // Su; case: eqP => //.
by move/astab1P=> cux; case/negP: notHx; rewrite defH inE Gx.
Qed.

Lemma Frobenius_context : forall G H K,
    [Frobenius G = K ><| H] ->
  [/\ K ><| H = G, K :!=: 1, H :!=: 1, K \proper G & H \proper G].
Proof.
move=> G H K; case/andP; move/eqP=> defG frobG; have [ltHG _] := andP frobG.
have [_ _ _ [_ _ _ ntH _]] := Frobenius_actionP _ _ frobG.
split=> //.
  by apply: contra (proper_subn ltHG); move/eqP=> K1; rewrite -defG K1 sdprod1g.
have [_ <- _ tiHK] := sdprodP defG.
by rewrite properEcard mulG_subl TI_cardMg // ltn_Pmulr ?cardG_gt1.
Qed.

Lemma Frobenius_partition : forall G H K,
  [Frobenius G = K ><| H] -> partition (gval K |: (H^# :^: K)) G.
Proof.
move=> G H K frobG; have [defG _ ntH ltKG ltHG] := Frobenius_context frobG.
have{defG} [_ defG nKH tiKH] := sdprodP defG.
have [sKG sHG] := (proper_sub ltKG, proper_sub ltHG).
have [_ _ tiHG] := and4P frobG; move/eqP=> snHG.
set HG := H^# :^: K; set KHG := _ |: _.
have defHG: HG = H^# :^: G.
  apply: atransP (orbit_refl _ _ _).
  apply/(subgroup_transitiveP (orbit_refl _ _ _) sKG (atrans_orbit _ _ _)).
  by rewrite astab1Js normD1 snHG (normC nKH).
have tiKHG: forall Hx, Hx \in HG -> [disjoint K & Hx].
  move=> Hx; case/imsetP=> x Kx ->{Hx}; rewrite disjointEsetI.
  by rewrite conjD1g -(conjGid Kx) setDE setIA -conjIg tiKH conjs1g setICr.
have{tiKHG} tiKHG: trivIset KHG.
  apply/trivIsetP=> U V.
  case/setU1P=> [-> | HG_U]; case/setU1P=> [-> | HG_V]; auto.
    by right; rewrite disjoint_sym tiKHG.
  by apply: (trivIsetP tiHG); rewrite -defHG.
apply/and3P; split=> //; last first.
  rewrite !inE eqEcard cards0 leqNgt cardG_gt0 andbF /=.
  apply/imsetP=> [[x _]]; move/eqP; apply/negP.
  by rewrite eq_sym conjD1g setDeq0 sub_conjg conjs1g subG1.
rewrite eqEcard; apply/andP; split.
  apply/bigcupsP=> U; case/setU1P=> [-> // |].
  case/imsetP=> x Kx ->{U}; rewrite conj_subG ?(subsetP sKG) //.
  by rewrite subDset subsetU ?sHG ?orbT.
rewrite -(eqnP tiKHG) big_setU1 /=; last first.
  apply/imsetP=> [[x _]]; move/setP; move/(_ 1).
  by rewrite conjD1g group1 !inE eqxx.
rewrite (eq_bigr (fun _ => #|H|.-1)) => [|Hx]; last first.
  by case/imsetP=> x _ ->; rewrite cardJg (cardsD1 1 H) group1.
rewrite sum_nat_const card_conjugates normD1.
rewrite -{3}(setIidPl sKG) -setIA snHG tiKH indexg1 -mulnS prednK //.
by rewrite -TI_cardMg ?defG.
Qed.

Lemma Frobenius_action_kernel_def : forall G H K sT S to,
    K ><| H = G -> @Frobenius_action _ G H sT S to ->
  K :=: 1 :|: [set x \in G | 'Fix_(S | to)[x] == set0].
Proof.
move=> G H K sT S to defG FrobG.
have partG: partition (gval K |: (H^# :^: K)) G.
  apply: Frobenius_partition; apply/andP; rewrite defG; split=> //.
  by apply/Frobenius_actionP; exact: HasFrobeniusAction FrobG.
have{FrobG} [ffulG transG regG ntH [u Su defH]]:= FrobG.
apply/setP=> x; rewrite !inE.
have [-> | ntx]:= eqVneq x 1; first by rewrite group1 eqxx.
have [coverG _]:= andP partG.
have neKHy: forall y, gval K <> H^# :^ y.
  by move=> y; move/setP; move/(_ 1); rewrite group1 conjD1g setD11.
rewrite (negPf ntx) -(eqP coverG) /cover.
rewrite big_setU1 /= ?inE; last by apply/imsetP=> [[y _]]; exact: neKHy.
have [nsKG sHG _ _ tiKH] := sdprod_context defG; have [sKG nKG]:= andP nsKG.
symmetry; case Kx: (x \in K) => /=.
  apply/set0Pn=> [[v]]; case/setIP=> Sv; have [y Gy ->] := atransP2 transG Su Sv.
  rewrite -sub1set -astabC sub1set astab1_act mem_conjg => Hxy.
  case/negP: ntx; rewrite -in_set1 -(conjgKV y x) -mem_conjgV conjs1g -tiKH.
  by rewrite defH setIA inE -mem_conjg (setIidPl sKG) (normsP nKG) ?Kx.
apply/andP; case; case/bigcupP=> Hy; case/imsetP=> y Ky ->{Hy} Hyx.
case/set0Pn; exists (to u y).
rewrite inE (actsP (atrans_acts transG)) ?(subsetP sKG) // Su.
rewrite -sub1set -astabC sub1set astab1_act.
by rewrite conjD1g defH conjIg !inE in Hyx; case/and3P: Hyx.
Qed.

Lemma Frobenius_cent1_ker : forall G H K,
  [Frobenius G = K ><| H] -> {in K^#, forall x, 'C_G[x] \subset K}.
Proof.
move=> G H K frobG x; case/setD1P=> nt_x Kx.
rewrite -setDeq0 setDE -setIA -disjointEsetI disjoint_sym.
have [partG _ _] := and3P (Frobenius_partition frobG).
rewrite -(eqP partG) bigcup_disjoint // => U; case/setU1P=> [-> |].
  by rewrite disjointEsetI setIAC -setIA setICr setI0.
case/imsetP=> y Ky ->{U}; rewrite disjointEsetI setIAC -subset0 subIset //.
apply/orP; left; rewrite conjD1g setDE setIA -setDE subDset setU0.
rewrite -[x](conjgKV y) -conjg_set1 normJ -conjIg sub_conjg conjs1g.
apply/subsetP=> z; case/setIP=> cxz Hz; have [_ _ sntiHG]:= and3P frobG.
have{frobG} [defG _ ntH] := Frobenius_context frobG.
case/andP=> sKG _; case/andP=> sHG _; have [_ _ _ tiKH] := sdprodP defG.
rewrite -(TIconj_SN_P ntH sHG sntiHG (x ^ y^-1)).
  by rewrite inE Hz mem_conjg conjgE invgK mulgA -(cent1P cxz) mulgK.
have Kxy: x ^ y^-1 \in K by rewrite groupJ ?groupV.
rewrite inE (subsetP sKG) // andbT; apply: contra nt_x => Hxy.
by rewrite -in_set1 -(memJ_conjg _ y^-1) conjs1g -tiKH inE Kxy.
Qed.

Lemma Frobenius_reg_ker : forall G H K,
  [Frobenius G = K ><| H] -> {in H^#, forall x, 'C_K[x] = 1}.
Proof.
move=> G H K frobG x; case/setD1P=> nt_x Hx; apply/trivgP.
apply/subsetP=> y; case/setIP=> Ky cxy; apply: contraR nt_x => nty.
have K1y: y \in K^# by rewrite inE nty.
have [sHG tiKH]: H \subset G /\ K :&: H = 1.
  by case/Frobenius_context: frobG; case/sdprod_context.
suffices: x \in K :&: H by rewrite tiKH inE.
rewrite inE (subsetP (Frobenius_cent1_ker frobG K1y)) //.
by rewrite inE cent1C (subsetP sHG).
Qed.

Lemma regular_norm_dvd_pred : forall K H,
  H \subset 'N(K) -> {in H^#, forall x, 'C_(K)[x] = 1} -> #|H| %| #|K|.-1.
Proof.
move=> K H nKH regH.
have actsH: [acts H, on K^# | 'J] by rewrite astabsJ normD1.
rewrite (cardsD1 1 K) group1 -(acts_sum_card_orbit actsH) /=.
rewrite (eq_bigr (fun _ => #|H|)) ?sum_nat_const ?dvdn_mull // => xH.
case/imsetP=> x; case/setIdP=> ntx Kx ->; rewrite card_orbit astab1J.
rewrite ['C_H[x]](trivgP _) ?indexg1 //=.
apply/subsetP=> y; case/setIP=> Hy cxy; apply: contraR ntx => nty.
by rewrite -[[set 1]](regH y) inE ?nty // Kx cent1C.
Qed.

Lemma regular_norm_coprime : forall K H,
  H \subset 'N(K) -> {in H^#, forall x, 'C_(K)[x] = 1} -> coprime #|K| #|H|.
Proof.
move=> K H nKH regH.
by rewrite (coprime_dvdr (regular_norm_dvd_pred nKH regH)) ?coprimenP.
Qed.

Lemma Frobenius_dvd_ker1 : forall G H K,
  [Frobenius G = K ><| H] -> #|H| %| #|K|.-1.
Proof.
move=> G H K frobG; apply: regular_norm_dvd_pred (Frobenius_reg_ker frobG).
by case/Frobenius_context: frobG; case/sdprodP.
Qed.

Lemma Frobenius_coprime : forall G H K,
  [Frobenius G = K ><| H] -> coprime #|K| #|H|.
Proof.
move=> G H K frobG.
by rewrite (coprime_dvdr (Frobenius_dvd_ker1 frobG)) ?coprimenP.
Qed.

Lemma Frobenius_ker_Hall : forall G H K,
  [Frobenius G = K ><| H] -> Hall G K.
Proof.
move=> G H K frobG; have [defG _ _ ltKG _] := Frobenius_context frobG.
rewrite /Hall -divgS (proper_sub ltKG) //= -(sdprod_card defG) mulKn //.
exact: Frobenius_coprime frobG.
Qed.

Lemma Frobenius_compl_Hall : forall G H K,
  [Frobenius G = K ><| H] -> Hall G H.
Proof.
move=> G H K frobG; have [defG _ _ _ ltHG] := Frobenius_context frobG.
rewrite /Hall -divgS (proper_sub ltHG) //= -(sdprod_card defG) mulnK //.
by rewrite coprime_sym; exact: Frobenius_coprime frobG.
Qed.

(*
Theorem Frobenius_kernel_exists : forall G H,
  [Frobenius G with complement H] -> group_set (G :\: cover (H^# :^: G)).
Admitted.
*)

End FrobeniusBasics.

(* Start of Section 3 proper. *)
Section BGsection3.

Implicit Type F : fieldType.
Implicit Type gT : finGroupType.
Implicit Type p : nat.

(* This is B & G, Lemma 3.1. *)
Lemma Frobenius_semiregularP : forall gT (G K R : {group gT}),
    K ><| R = G -> K :!=: 1 -> R :!=: 1 ->
  reflect {in R^#, forall x, 'C_K[x] = 1} [Frobenius G = K ><| R].
Proof.
move=> gT G K R defG ntK ntR.
apply: (iffP idP)=> [|regG]; first exact: Frobenius_reg_ker.
have [nsKG sRG defKR nKR tiKR]:= sdprod_context defG; have [sKG _]:= andP nsKG.
apply/and3P; split; first by rewrite defG.
  by rewrite properEcard sRG -(sdprod_card defG) ltn_Pmull ?cardG_gt1.
apply/(TIconj_SN_P ntR sRG) => x; case/setDP=> Gx notRx.
apply/trivgP; apply: contraR notRx; case/subsetPn=> y; case/setIP=> Hy.
move: Gx; rewrite -defKR -(normC nKR); case/imset2P=> xr xk Rxr Kxk ->{x}.
rewrite groupMl //= conjsgM {xr Rxr}(conjGid Rxr).
case/imsetP=> z Rxz def_y nt_y; rewrite (subsetP (sub1G R)) //.
rewrite -(regG y); last by rewrite !(nt_y, inE).
rewrite inE Kxk -groupV cent1C (sameP cent1P commgP) -in_set1 -[[set 1]]tiKR.
rewrite inE {1}commgEr invgK groupM ?memJ_norm ?groupV ?(subsetP nKR) //=.
by rewrite commgEl {2}def_y actK groupM ?groupV.
Qed.

Lemma prime_FrobeniusP : forall gT (G K R : {group gT}),
    K :!=: 1 -> prime #|R| ->
  reflect (K ><| R = G /\ 'C_K(R) = 1) [Frobenius G = K ><| R].
Proof.
move=> gT G K R ntK R_pr; have ntR: R :!=: 1 by rewrite -cardG_gt1 prime_gt1.
have [defG | not_sdG] := eqVneq (K ><| R) G; last first.
  by apply: (iffP andP) => [] [defG]; rewrite defG ?eqxx in not_sdG.
apply: (iffP (Frobenius_semiregularP defG ntK ntR)) => [|[_]] regR.
  split=> //; have [x defR] := cyclicP _ (prime_cyclic R_pr).
  by rewrite defR cent_cycle regR // !inE defR cycle_id andbT -cycle_eq1 -defR.
move=> x; case/setD1P=> nt_x Rx; apply/trivgP.
rewrite /= -cent_cycle -regR setIS ?centS //.
apply: contraR nt_x; rewrite -cycle_eq1; move/(prime_TIg R_pr) <-.
by rewrite (setIidPr _) ?cycle_subG.
Qed.

(* This is B & G, Lemma 3.2. *)
Section FrobeniusQuotient.

Variables (gT : finGroupType) (G K R : {group gT}).

(* This is a special case of B & G, Lemma 3.2 (b). *)
Lemma Frobenius_proper_quotient : forall N : {group gT},
  [Frobenius G = K ><| R] -> solvable K -> N <| G -> N \proper K ->
  [Frobenius G / N = (K / N) ><| (R / N)].
Proof.
move=> N frobG solK nsNG; case/andP=> sNK ltNK.
have [defG _ ntR _ _] := Frobenius_context frobG.
have [nsKG sRG defKR nKR tiKR] := sdprod_context defG; have [sKG _]:= andP nsKG.
have nsNK := normalS sNK sKG nsNG.
apply/Frobenius_semiregularP=> [|||Nx].
- rewrite sdprodE ?quotient_norms //.
    by rewrite -quotientMl ?defKR ?normal_norm.
  by rewrite -quotientGI // tiKR quotient1.
- by rewrite -subG1 quotient_sub1 ?normal_norm.
- rewrite -subG1 quotient_sub1; last by rewrite (subset_trans sRG) ?normal_norm.
  apply: contra ntR => sRN.
  by rewrite -subG1 -tiKR subsetI (subset_trans sRN) /=.
rewrite !inE andbC; case/andP; case/morphimP=> x nNx Rx ->{Nx} notNx.
apply/trivgP; rewrite /= -cent_cycle -quotient_cycle //.
rewrite -coprime_quotient_cent ?cycle_subG //; last first.
  by apply: coprimegS (Frobenius_coprime frobG); rewrite cycle_subG.
rewrite cent_cycle (Frobenius_reg_ker frobG) ?quotient1 //.
by rewrite !inE Rx andbT; apply: contra notNx; move/eqP->; rewrite morph1.
Qed.

(* This is B & G, Lemma 3.2 (a). *)
Lemma Frobenius_normal_proper_ker : forall N : {group gT},
    [Frobenius G = K ><| R] -> solvable K -> N <| G -> ~~ (K \subset N) ->
  N \proper K.
Proof.
move=> N frobG solK nsNG ltNK; rewrite /proper ltNK andbT.
have [defG _ ntR _ _] := Frobenius_context frobG.
have [nsKG sRG defKR nKR tiKR] := sdprod_context defG; have [sKG _]:= andP nsKG.
pose H := N :&: K; have nsHG: H <| G by exact: normalI.
have [sNG nNG] := andP nsNG; have [_ nHG] := andP nsHG.
have ltHK: H \proper K by rewrite /proper subsetIr subsetI subxx andbT.
have nRKqH: K / H \subset 'N((N :&: R) / H).
  rewrite cents_norm // centsC quotient_cents2r // commg_subI //.
    by rewrite setIS ?(subset_trans sRG) ?normal_norm.
  by rewrite subsetI subxx ?(subset_trans sKG).
have ntKqH: K / H != 1.
  by rewrite -subG1 quotient_sub1 ?subsetI ?subxx ?andbT // (subset_trans sKG).
case/trivgPn: ntKqH => Hx KqHx ntHx.
have: (N :&: R) / H :&: ((N :&: R) / H) :^ Hx \subset [1].
  have frobGqH := Frobenius_proper_quotient frobG solK nsHG ltHK.
  have [defGqH _ ntRqH _ _] := Frobenius_context frobGqH.
  have{defGqH} [_ _ _ tiKRqH] := sdprodP defGqH.
  have [_ _ tiGqH] := and3P frobGqH.
  have GqHx: Hx \in G / H :\: R / H.
    rewrite inE (subsetP (quotientS _ sKG)) //= andbT.
    apply: contra ntHx => RqHx; rewrite -cycle_eq1 -subG1 -tiKRqH cycle_subG.
    by rewrite inE KqHx.
  rewrite -(TIconj_SN_P ntRqH (quotientS _ sRG) tiGqH Hx GqHx).
  by rewrite setISS ?conjSg ?quotientS ?subsetIr.
rewrite (setIidPr _); last by have:= subsetP nRKqH Hx KqHx; rewrite inE.
rewrite sub_conjg conjs1g quotient_sub1; last first.
  by rewrite subIset // (subset_trans sRG) ?orbT.
rewrite subsetI subsetIl (sameP setIidPl eqP) setIAC -setIA tiKR.
rewrite (setIidPr (sub1G N)) eq_sym /= => tiNR; rewrite -(setIidPl sNG).
case/and3P: (Frobenius_partition frobG); move/eqP=> <- _ _.
rewrite big_distrr /=; apply/bigcupsP=> U.
case/setU1P=> [->|]; [exact: subsetIr | case/imsetP=> x Kx ->{U}].
rewrite conjD1g setDE setIA subIset //.
rewrite -(normP (subsetP (subset_trans sKG nNG) x Kx)) -conjIg.
by rewrite (eqP tiNR) conjs1g sub1G.
Qed.

(* This is B & G, Lemma 3.2 (b). *)
Lemma Frobenius_quotient : forall N : {group gT},
    [Frobenius G = K ><| R] -> solvable K -> N <| G -> ~~ (K \subset N) ->
  [Frobenius G / N = (K / N) ><| (R / N)].
Proof.
move=> N frobG solK nsNG ltKN; apply: Frobenius_proper_quotient => //.
exact: (Frobenius_normal_proper_ker frobG).
Qed.

End FrobeniusQuotient.

(* This is B & G, Lemma 3.3. *)
Lemma Frobenius_rfix_compl : forall F gT (G K R : {group gT}) n,
    forall rG : mx_representation F G n,
    [Frobenius G = K ><| R] -> [char F]^'.-group K ->
  ~~ (K \subset rker rG) -> rfix_mx rG R != 0.
Proof.
move=> F gT G K R n rG frobG; rewrite /pgroup charf'_nat => nzK.
have [defG _ _ ltKG ltRG]:= Frobenius_context frobG.
have{ltKG ltRG} [sKG sRG]: K \subset G /\ R \subset G by rewrite !proper_sub.
apply: contra; move/eqP=> fixR0; rewrite rfix_mx_rstabC // -(eqmx_scale _ nzK).
pose gsum H := gring_op rG (gset_mx F G H).
have fixsum: forall H : {group gT}, H \subset G -> (gsum H <= rfix_mx rG H)%MS.
  move=> H; move/subsetP=> sHG; apply/rfix_mxP=> x Hx; have Gx := sHG x Hx.
  rewrite -gring_opG // -gring_opM ?envelop_mx_id //; congr (gring_op _ _).
  rewrite {2}/gset_mx (reindex_acts 'R _ Hx) ?astabsR //= mulmx_suml.
  by apply:eq_bigr=> y; move/sHG=> Gy; rewrite repr_mxM.
have: gsum G + rG 1 *+ #|K| = gsum K + \sum_(x \in K) gsum (R :^ x).
  rewrite -gring_opG // -sumr_const -!linear_sum -!linearD; congr gring_op.
  have bigTE := eq_bigl _ _ (fun _ => andbT _); rewrite {1}/gset_mx -bigTE.
  rewrite (set_partition_big _ (Frobenius_partition frobG)) /=.
  rewrite big_setU1 ?bigTE -?addrA /=; last first.
    apply: contraL (group1 K); case/imsetP=> x _ ->.
    by rewrite conjD1g !inE eqxx.
  congr (_ + _); rewrite big_imset /=; last first.
    case/and4P: frobG=> _ _ _; move/eqP=> snRG.
    case/sdprodP: defG => _ defG _ tiKR.
    move=> x y Kx Ky /= eqRxy; apply/eqP; rewrite eq_mulgV1 -in_set1.
    rewrite -[[set 1]]tiKR -snRG setIA inE -defG (setIidPl (mulG_subl _ _)).
    by rewrite groupM ?groupV //= -normD1 inE conjsgM eqRxy actK.
  rewrite -big_split; apply: eq_bigr => x Kx /=.
  by rewrite bigTE addrC conjD1g -big_setD1 ?group1.
have ->: gsum G = 0.
  apply/eqP; rewrite -submx0 -fixR0; apply: submx_trans (rfix_mxS rG sRG).
  exact: fixsum.
rewrite repr_mx1 -scalemx_nat add0r => ->.
rewrite big1 ?addr0 ?fixsum // => x Kx; have Gx := subsetP sKG x Kx.
apply/eqP; rewrite -submx0 (submx_trans (fixsum _ _)) ?conj_subG //.
by rewrite -(mul0mx _ (rG x)) -fixR0 rfix_mx_conjsg.
Qed.

(* This is B & G, Theorem 3.4. *)
Theorem odd_prime_sdprod_rfix0 : forall F gT (G K R : {group gT}) n,
    forall rG : mx_representation F G n,
    K ><| R = G -> solvable G -> odd #|G| -> coprime #|K| #|R| -> prime #|R| ->
    [char F]^'.-group G -> rfix_mx rG R = 0 ->
  [~: R, K] \subset rker rG.
Proof.
move=> F gT G; move: {2}_.+1 (ltnSn #|G|) => m.
elim: m => // m IHm in gT G *; rewrite ltnS => leGm K R n rG defG solG oddG.
set p := #|R| => coKR p_pr F'G regR.
have [nsKG sRG defKR nKR tiKR] := sdprod_context defG.
have [sKG nKG] := andP nsKG; have solK := solvableS sKG solG.
case: (eqsVneq K 1) => [-> | ntK]; first by rewrite commG1 sub1G.
have ker_ltK: forall H : {group gT},
  H \proper K -> R \subset 'N(H) -> [~: R, H] \subset rker rG.
- move=> H ltKH nHR; have sHK := proper_sub ltKH; set G1 := H <*> R.
  have sG1G: G1 \subset G by rewrite mulgen_subG (subset_trans sHK).
  have coHR := coprimeSg sHK coKR.
  have defG1: H ><| R = G1 by rewrite sdprodEgen // coprime_TIg.
  apply: subset_trans (subsetIr G1 _); rewrite -(rker_subg _ sG1G).
  apply: IHm; rewrite ?(solvableS sG1G) ?(oddSg sG1G) ?(pgroupS sG1G) //.
  apply: leq_trans leGm; rewrite /= norm_mulgenEr // -defKR !coprime_cardMg //.
  by rewrite ltn_pmul2r ?proper_card.
without loss [q q_pr qK]: / exists2 q, prime q & q.-group K.
  move=> IH; set q := pdiv #|K|.
  have q_pr: prime q by rewrite pdiv_prime ?cardG_gt1.
  have exHall := coprime_Hall_exists _ nKR coKR solK.
  have [Q sylQ nQR] := exHall q; have [Q' hallQ' nQ'R] := exHall q^'.
  have [sQK qQ _] := and3P sylQ; have [sQ'K q'Q' _] := and3P hallQ'.
  without loss{IH} ltQK: / Q \proper K.
    by rewrite properEneq; case: eqP IH => [<- -> | _ _ ->] //; exists q.
  have ltQ'K: Q' \proper K.
    rewrite properEneq; case: eqP (pgroupP q'Q' q q_pr) => //= ->.
    by rewrite !inE pdiv_dvd eqxx; apply.
  have nkerG := subset_trans _ (rker_norm rG).
  rewrite -quotient_cents2 ?nkerG //.
  have <-: Q * Q' = K.
    apply/eqP; rewrite eqEcard mulG_subG sQK sQ'K.
    rewrite coprime_cardMg ?(pnat_coprime qQ) //=.
    by rewrite (card_Hall sylQ) (card_Hall hallQ') partnC.
  rewrite quotientMl ?nkerG ?(subset_trans sQK) // centM subsetI.
  by rewrite !quotient_cents2r ?ker_ltK.
without loss{m IHm leGm} [ffulG cycZ]: / rker rG = 1 /\ cyclic 'Z(G).
  move=> IH; wlog [I M /= simM sumM _]: / mxsemisimple rG 1%:M.
    exact: (mx_reducible_semisimple (mxmodule1 _) (mx_Maschke _ F'G)).
  pose not_cRK_M i := ~~ ([~: R, K] \subset rstab rG (M i)).
  case: (pickP not_cRK_M) => [i | cRK_M]; last first.
    rewrite rfix_mx_rstabC ?comm_subG // -sumM.
    apply/sumsmx_subP=> i _; move/negbFE: (cRK_M i).
    by rewrite rfix_mx_rstabC ?comm_subG.
  have [modM ntM _] := simM i; pose rM := kquo_repr (submod_repr modM).
  do [rewrite {+}/not_cRK_M -(rker_submod modM) /=; set N := rker _] in rM *.
  case: (eqVneq N 1) => [N1 _ | ntN].
    apply: IH; split.
      by apply/trivgP; rewrite -N1 /N rker_submod rstabS ?submx1.
    have: mx_irreducible (submod_repr modM) by exact/submod_mx_irr.
    by apply: mx_faithful_irr_center_cyclic; exact/trivgP.
  have tiRN: R :&: N = 1.
    by apply: prime_TIg; rewrite //= rker_submod rfix_mx_rstabC // regR submx0.
  have nsNG: N <| G := rker_normal _; have [sNG nNG] := andP nsNG.
  have nNR := subset_trans sRG nNG.
  have sNK: N \subset K.
    have [pi hallK]: exists pi, pi.-Hall(G) K.
      by apply: HallP; rewrite -(coprime_sdprod_Hall defG).
    rewrite (subset_normal_Hall _ hallK) // /psubgroup sNG /=.
    apply: pnat_dvd (pHall_pgroup hallK).
    rewrite -(dvdn_pmul2r (prime_gt0 p_pr)) -!TI_cardMg // 1?setIC // defKR.
    by rewrite -norm_mulgenEr // cardSg // mulgen_subG sNG.
  have defGq: (K / N) ><| (R / N) = G / N.
    rewrite sdprodE ?quotient_norms -?quotientMr ?defKR //.
    by rewrite -quotientGI // tiKR quotient1.
  case/negP; rewrite -quotient_cents2  ?(subset_trans _ nNG) //= -/N.
  rewrite (sameP commG1P trivgP).
  apply: subset_trans (kquo_mx_faithful (submod_repr modM)).
  rewrite IHm ?quotient_sol ?coprime_morph ?morphim_odd ?quotient_pgroup //.
  - apply: leq_trans leGm; exact: ltn_quotient.
  - by rewrite card_quotient // -indexgI tiRN indexg1.
  apply/eqP; rewrite -submx0 rfix_quo // rfix_submod //.
  by rewrite regR capmx0 linear0 sub0mx.
wlog perfectK: / [~: K, R] = K.
  move=> IH; have: [~: K, R] \subset K by rewrite commg_subl.
  rewrite subEproper; case/predU1P=> //; move/ker_ltK.
  by rewrite commGC commg_normr coprime_commGid // commGC => ->.
have primeR: {in R^#, forall x, 'C_K[x] = 'C_K(R)}.
  move=> x; case/setD1P=> nt_x Rx; rewrite -cent_cycle ((<[x]> =P R) _) //.
  rewrite eqEsubset cycle_subG Rx; apply: contraR nt_x; move/prime_TIg.
  by rewrite -cycle_eq1 (setIidPr _) ?cycle_subG // => ->.
case cKK: (abelian K).
  rewrite commGC perfectK; move/eqP: regR; apply: contraLR.
  apply: Frobenius_rfix_compl => //; last exact: pgroupS F'G.
  rewrite -{2 4}perfectK coprime_abel_cent_TI // in primeR.
  by apply/Frobenius_semiregularP; rewrite // -cardG_gt1 prime_gt1.
have [spK defZK]: special K /\ 'C_K(R) = 'Z(K).
  apply: (abelian_charsimple_special qK) => //.
  apply/bigcupsP=> H; case/andP=> chHK cHH.
  have:= char_sub chHK; rewrite subEproper.
  case/predU1P=> [eqHK | ltHK]; first by rewrite eqHK cKK in cHH.
  have nHR: R \subset 'N(H) := char_norm_trans chHK nKR.
  by rewrite (sameP commG1P trivgP) /= commGC -ffulG ker_ltK.
have{spK} esK: extraspecial K.
  have abelZK := center_special_abelem qK spK.
  have: 'Z(K) != 1.
    by case: spK => _ <-; rewrite (sameP eqP commG1P) -abelianE cKK.
  case/(pgroup_pdiv (abelem_pgroup abelZK)) => _ _ [[|e] oK].
    by split; rewrite ?oK.
  suffices: cyclic 'Z(K) by rewrite (abelem_cyclic abelZK) oK pfactorK.
  rewrite (cyclicS _ cycZ) // subsetI subIset ?sKG //=.
  by rewrite -defKR centM subsetI -{2}defZK !subsetIr.
have [e e_gt0 oKqe] := card_extraspecial qK esK.
have cycR: cyclic R := prime_cyclic p_pr.
have co_q_p: coprime q p by rewrite oKqe coprime_pexpl in coKR.
move/eqP: regR; case/idPn.
rewrite defZK in primeR.
case: (repr_extraspecial_prime_sdprod_cycle _ _ defG _ oKqe) => // _.
apply=> //; last exact/trivgP.
apply: contraL (oddSg sRG oddG); move/eqP->; have:= oddSg sKG oddG.
by rewrite oKqe addn1 /= !odd_exp /= orbC => ->.
Qed.

(* Internal action version of B & G, Theorem 3.4. *)
Theorem odd_prime_sdprod_abelem_cent1 : forall k gT (G K R V : {group gT}),
    solvable G -> odd #|G| ->
    K <| G -> Hall G K -> R \in [complements to K in G] -> prime #|R| ->
    k.-abelem V -> G \subset 'N(V) -> ~~ (k %| #|G|) ->
  'C_V(R) = 1-> [~: R, K] \subset 'C_K(V).
Proof.
move=> k gT G K R V solG oddG nsKG hallK complGKR R_pr abelV nVG k'G regR.
have defG: K ><| R = G by apply/sdprod_normal_compl; rewrite complgC.
rewrite -(coprime_sdprod_Hall defG) in hallK.
have [_ sRG _ nKR _] := sdprod_context defG; rewrite subsetI commg_subr nKR.
case: (eqsVneq V 1) => [-> | ntV]; first exact: cents1.
pose rV := abelem_repr abelV ntV nVG.
apply: subset_trans (_ : rker rV \subset _); last first.
  by rewrite rker_abelem subsetIr.
apply: odd_prime_sdprod_rfix0 => //.
  have k_pr: prime k by case/pgroup_pdiv: (abelem_pgroup abelV).
  by rewrite /pgroup charf'_nat -val_eqE /= val_Fp_nat.
by apply/eqP; rewrite -submx0 rfix_abelem //= regR morphim1 rowg_mx1.
Qed.

(* This is B & G, Theorem 3.5. *)
Theorem Frobenius_prime_rfix1 : forall F gT (G K R : {group gT}) n,
    forall rG : mx_representation F G n,
    K ><| R = G -> solvable G -> prime #|R| -> 'C_K(R) = 1 ->
    [char F]^'.-group G -> \rank (rfix_mx rG R) = 1%N ->
  K^`(1) \subset rker rG.
Proof.
move=> F gT G K R n rG defG solG p_pr regR F'G fixRlin.
wlog closF: F rG F'G fixRlin / group_closure_field F gT.
  move=> IH; apply: (@group_closure_field_exists gT F) => [[Fc closFc [f fM]]].
  rewrite -(rker_map fM) IH //; last by rewrite -map_rfix_mx mxrank_map.
  by rewrite /pgroup charf'_nat -(ringM_nat fM) fieldM_eq0 // -charf'_nat.
move: {2}_.+1 (ltnSn #|K|) => m.
elim: m => // m IHm in gT G K R rG solG p_pr regR F'G closF fixRlin defG *.
rewrite ltnS => leKm.
have [nsKG sRG defKR nKR tiKR] := sdprod_context defG.
have [sKG nKG] := andP nsKG; have solK := solvableS sKG solG.
have cycR := prime_cyclic p_pr.
case: (eqsVneq K 1) => [-> | ntK]; first by rewrite derg1 commG1 sub1G.
have defR: forall x, x \in R^# -> <[x]> = R.  
  move=> x; case/setD1P; rewrite -cycle_subG -cycle_eq1 => ntX sXR.
  apply/eqP; rewrite eqEsubset sXR; apply: contraR ntX; move/(prime_TIg p_pr).
  by rewrite /= (setIidPr sXR) => ->.
have ntR: R :!=: 1 by rewrite -cardG_gt1 prime_gt1.
have frobG: [Frobenius G = K ><| R].
  by apply/Frobenius_semiregularP=> // x Rx; rewrite -cent_cycle defR.
case: (eqVneq (rker rG) 1) => [ffulG | ntC]; last first.
  set C := rker rG in ntC *; have nsCG: C <| G := rker_normal rG.
  have [sCG nCG] := andP nsCG.
  have nCK := subset_trans sKG nCG; have nCR := subset_trans sRG nCG.
  case sKC: (K \subset C); first exact: subset_trans (der_sub _ _) _.
  have sCK: C \subset K.
    by rewrite proper_sub // (Frobenius_normal_proper_ker frobG) ?sKC.
  have frobGq: [Frobenius G / C = (K / C) ><| (R / C)].
    by apply: Frobenius_quotient; rewrite ?sKC.
  have [defGq _ ntRq _ _] := Frobenius_context frobGq.
  rewrite -quotient_sub1 ?comm_subG ?quotient_der //= -/C.
  apply: subset_trans (kquo_mx_faithful rG).
  apply: IHm defGq _; rewrite 1?(quotient_sol, quotient_pgroup, rfix_quo) //.
  - rewrite card_quotient // -indexgI /= -/C setIC.
    by rewrite -(setIidPl sCK) -setIA tiKR (setIidPr (sub1G _)) indexg1.
  - have: cyclic (R / C) by [rewrite quotient_cyclic]; case/cyclicP=> Cx defRq.
    rewrite /= defRq cent_cycle (Frobenius_reg_ker frobGq) //= !inE defRq.
    by rewrite cycle_id -cycle_eq1 -defRq ntRq.
  - move=> Hq; rewrite -(group_inj (cosetpreK Hq)).
    by apply: quotient_splitting_field; rewrite ?subsetIl.
  by apply: leq_trans leKm; exact: ltn_quotient.
have ltK_abelian: forall N : {group gT},
  R \subset 'N(N) -> N \proper K -> abelian N.
- move=> N nNR ltNK; have [sNK _] := andP ltNK; apply/commG1P; apply/trivgP.
  rewrite -(setIidPr (sub1G (N <*> R))) /= -ffulG; set G1 := N <*> R.
  have sG1: G1 \subset G by rewrite mulgen_subG (subset_trans sNK).
  have defG1: N ><| R = G1.
    by rewrite sdprodEgen //; apply/trivgP; rewrite -tiKR setSI.
  rewrite -(rker_subg _ sG1).
  apply: IHm defG1 _; rewrite ?(solvableS sG1) ?(pgroupS sG1) //.
    by apply/trivgP; rewrite -regR setSI.
  by apply: leq_trans leKm; exact: proper_card.
have cK'K': abelian K^`(1).
  apply: ltK_abelian; first exact: char_norm_trans (der_char _ _) nKR.
  exact: (sol_der1_proper solK).
pose fixG := rfix_mx rG; pose NRmod N (U : 'M_n) := N <*> R \subset rstabs rG U.
have dx_modK_rfix: forall (N : {group gT}) U V,
    N \subset K -> R \subset 'N(N) -> NRmod N U -> NRmod N V ->
  mxdirect (U + V) -> (U <= fixG N)%MS || (V <= fixG N)%MS.
- move=> N U V sNK nNR nUNR nVNR dxUV.
  case: (eqsVneq N 1) => [-> | ntN]; first by rewrite -rfix_mx_rstabC sub1G.
  have sNRG: N <*> R \subset G by rewrite mulgen_subG (subset_trans sNK).
  pose rNR := subg_repr rG sNRG.
  have nfixU: forall W, NRmod N W -> ~~ (W <= fixG N)%MS -> (fixG R <= W)%MS.
    move=> W nWN not_cWN; rewrite (sameP capmx_idPr eqmxP).
    rewrite -(geq_leqif (mxrank_leqif_eq (capmxSr _ _))) fixRlin lt0n.
    rewrite mxrank_eq0 -(in_submodK (capmxSl _ _)) val_submod_eq0.
    have modW: mxmodule rNR W by rewrite /mxmodule rstabs_subg subsetI subxx.
    rewrite -(eqmx_eq0 (rfix_submod modW _)) ?mulgen_subr //.
    apply: Frobenius_rfix_compl (pgroupS (subset_trans sNK sKG) F'G) _.
      apply/Frobenius_semiregularP=> // [|x Rx].
        by rewrite sdprodEgen //; apply/trivgP; rewrite -tiKR setSI.
      by apply/trivgP; rewrite -regR /= -cent_cycle defR ?setSI.
    by rewrite rker_submod rfix_mx_rstabC ?mulgen_subl.
  have: fixG R != 0 by rewrite -mxrank_eq0 fixRlin.
  apply: contraR; case/norP=> not_fixU not_fixW.
  by rewrite -submx0 -(mxdirect_addsP dxUV) sub_capmx !nfixU.
have redG := mx_Maschke rG F'G.
wlog [U simU nfixU]: / exists2 U, mxsimple rG U & ~~ (U <= fixG K)%MS.
  move=> IH; wlog [I U /= simU sumU _]: / mxsemisimple rG 1%:M.
    exact: (mx_reducible_semisimple (mxmodule1 _) redG).
  case: (pickP (fun i => ~~ (U i <= fixG K))%MS) => [i nfixU | fixK].
    by apply: IH; exists (U i).
  apply: (subset_trans (der_sub _ _)); rewrite rfix_mx_rstabC // -sumU.
  by apply/sumsmx_subP=> i _; apply/idPn; rewrite fixK.
have [modU ntU minU] := simU; pose rU := submod_repr modU.
have irrU: mx_irreducible rU by exact/submod_mx_irr.
have [W modW sumUW dxUW] := redG U modU (submx1 U).
have cWK: (W <= fixG K)%MS.
  have:= dx_modK_rfix _ _ _ (subxx _) nKR _ _ dxUW.
  by rewrite /NRmod /= norm_mulgenEr // defKR (negPf nfixU); exact.
have nsK'G: K^`(1) <| G by exact: char_normal_trans (der_char _ _) nsKG.
have [sK'G nK'G] := andP nsK'G.
suffices nregK'U: (rfix_mx rU K^`(1))%MS != 0.
  rewrite rfix_mx_rstabC ?normal_sub // -sumUW addsmx_sub andbC.
  rewrite (submx_trans cWK) ?rfix_mxS ?der_sub //= (sameP capmx_idPl eqmxP).
  rewrite minU ?capmxSl ?capmx_module ?normal_rfix_mx_module //.
  apply: contra nregK'U => cUK'; rewrite (eqmx_eq0 (rfix_submod _ _)) //.
  by rewrite (eqP cUK') linear0.
pose rK := subg_repr rU (normal_sub nsKG); set p := #|R| in p_pr.
wlog sK: / socleType rK by exact: socle_exists.
have [i _ def_sK]: exists2 i, i \in setT & [set: sK] = orbit 'Cl G i.
  by apply/imsetP; exact: Clifford_atrans.
have card_sK: #|[set: sK]| =  #|G : 'C[i | 'Cl]|.
  by rewrite def_sK card_orbit_in ?indexgI.
have ciK: K \subset 'C[i | 'Cl].
  apply: subset_trans (astabS _ (subsetT _)).
  by apply: subset_trans (Clifford_astab _); exact: mulgen_subl.
pose M := socle_base i; have simM: mxsimple rK M := socle_simple i.
have [sKp | sK1 {ciK card_sK}]: #|[set: sK]| = p \/ #|[set: sK]| = 1%N.
- apply/pred2P; rewrite orbC card_sK; case/primeP: p_pr => _; apply.
  by rewrite (_ : p = #|G : K|) ?indexgS // -divgS // -(sdprod_card defG) mulKn.
- have{def_sK} def_sK: [set: sK] = orbit 'Cl R i.
    apply/eqP; rewrite eq_sym -subTset def_sK.
    apply/subsetP=> i_yz; case/imsetP=> yz; rewrite -{1}defKR.
    case/imset2P=> y z; move/(subsetP ciK); rewrite !inE sub1set inE.
    case/andP=> Gy; move/eqP=> ciy Rz -> ->{yz i_yz}.
    by rewrite actMin ?(subsetP sRG z Rz) // ciy mem_orbit.
  have inj_i: {in R &, injective ('Cl%act i)}.
    apply/dinjectiveP; apply/card_uniqP; rewrite size_map -cardE -/p.
    by rewrite -sKp def_sK /orbit Imset.imsetE cardsE.
  pose sM := (\sum_(y \in R) M *m rU y)%MS.
  have dxM: mxdirect sM.
    apply/mxdirect_sumsP=> y Ry; have Gy := subsetP sRG y Ry.
    pose j := 'Cl%act i y.
    apply/eqP; rewrite -submx0 -{2}(mxdirect_sumsP (Socle_direct sK) j) //.
    rewrite capmxS ?val_Clifford_act // ?submxMr ?component_mx_id //.
    apply/sumsmx_subP => z; case/andP=> Rz ne_z_y; have Gz := subsetP sRG z Rz.
    rewrite (sumsmx_sup ('Cl%act i z)) ?(inj_in_eq inj_i) //.
    by rewrite val_Clifford_act // ?submxMr // ?component_mx_id.
  pose inCR := \sum_(x \in R) rU x.
  have im_inCR: (inCR <= rfix_mx rU R)%MS.
    apply/rfix_mxP=> x Rx; have Gx := subsetP sRG x Rx.
    rewrite {2}[inCR](reindex_astabs 'R x) ?astabsR //= mulmx_suml.
    by apply: eq_bigr => y; move/(subsetP sRG)=> Gy; rewrite repr_mxM.
  pose inM := proj_mx M (\sum_(x \in R | x != 1) M *m rU x)%MS.
  have dxM1 := mxdirect_sumsP dxM _ (group1 R).
  rewrite repr_mx1 mulmx1 in dxM1.
  have inCR_K: M *m inCR *m inM = M.
    rewrite mulmx_sumr (bigD1 1) //= repr_mx1 mulmx1 mulmx_addl proj_mx_id //.
    by rewrite proj_mx_0 ?addr0 // summx_sub_sums.
  have [modM ntM _] := simM.
  have linM: \rank M = 1%N.
    apply/eqP; rewrite eqn_leq lt0n mxrank_eq0 ntM andbT.
    rewrite -inCR_K; apply: leq_trans (mxrankM_maxl _ _) _.
    apply: leq_trans (mxrankS (mulmx_sub _ im_inCR)) _.
    rewrite rfix_submod //; apply: leq_trans (mxrankM_maxl _ _) _.
    by rewrite -fixRlin mxrankS ?capmxSr.
  apply: contra (ntM); move/eqP; rewrite -submx0 => <-.
  by rewrite -(rfix_mx_rstabC rK) ?der_sub // -(rker_submod modM) rker_linear.
have{sK i M simM sK1 def_sK} irrK: mx_irreducible rK.
  have cycGq: cyclic (G / K) by rewrite -defKR quotient_mulgr quotient_cyclic.
  apply: (mx_irr_prime_index closF irrU cycGq simM) => x Gx /=.
  apply: (component_mx_iso simM); first exact: Clifford_simple.
  have jP: component_mx rK (M *m rU x) \in socle_enum sK.
    by apply: component_socle; exact: Clifford_simple.
  pose j := PackSocle jP; apply: submx_trans (_ : j <= _)%MS.
    by rewrite PackSocleK component_mx_id //; exact: Clifford_simple.
  have def_i: [set i] == [set: sK] by rewrite eqEcard subsetT cards1 sK1.
  by rewrite ((j =P i) _) // -in_set1 (eqP def_i) inE.
pose G' := K^`(1) <*> R.
have sG'G: G' \subset G by rewrite mulgen_subG sK'G.
pose rG' := subg_repr rU sG'G.
wlog irrG': / mx_irreducible rG'.
  move=> IH; wlog [M simM sM1]: / exists2 M, mxsimple rG' M & (M <= 1%:M)%MS.
    by apply: mxsimple_exists; rewrite ?mxmodule1; case: irrK.
  have [modM ntM _] := simM.
  have [M' modM' sumM dxM] := mx_Maschke rG' (pgroupS sG'G F'G) modM sM1.
  wlog{IH} ntM': / M' != 0.
    case: eqP sumM => [-> M1 _ | _ _ -> //]; apply: IH.
    by apply: mx_iso_simple simM; apply: eqmx_iso; rewrite addsmx0_id in M1.
  suffices: (K^`(1) \subset rstab rG' M) || (K^`(1) \subset rstab rG' M').
    rewrite !rfix_mx_rstabC ?mulgen_subl //; rewrite -!submx0 in ntM ntM' *.
    by case/orP; move/submx_trans=> sM; apply: (contra (sM _ _)).
  rewrite !rstab_subg !rstab_submod !subsetI mulgen_subl !rfix_mx_rstabC //.
  rewrite /mxmodule !rstabs_subg !rstabs_submod !subsetI !subxx in modM modM'.
  do 2!rewrite orbC -genmxE.
  rewrite dx_modK_rfix // /NRmod ?(eqmx_rstabs _ (genmxE _)) ?der_sub //.
    exact: subset_trans sRG nK'G.
  apply/mxdirect_addsP; apply/eqP; rewrite -genmx_cap (eqmx_eq0 (genmxE _)).
  rewrite -(in_submodK (submx_trans (capmxSl _ _) (val_submodP _))).
  rewrite val_submod_eq0 in_submodE -submx0 (submx_trans (capmxMr _ _ _)) //.
  by rewrite -!in_submodE !val_submodK (mxdirect_addsP dxM).
have nsK'K: K^`(1) <| K by exact: der_normal.
pose rK'K := subg_repr rK (normal_sub nsK'K).
have irrK'K: mx_absolutely_irreducible rK'K.
  wlog sK'K: / socleType rK'K by exact: socle_exists.
  have sK'_dv_K: #|[set: sK'K]| %| #|K|.
    exact: atrans_dvd_in (Clifford_atrans _ _).
  have nsK'G': K^`(1) <| G' := normalS (mulgen_subl _ _) sG'G nsK'G.
  pose rK'G' := subg_repr rG' (normal_sub nsK'G').
  wlog sK'G': / socleType rK'G' by exact: socle_exists.
  have coKp: coprime #|K| p := Frobenius_coprime frobG.
  have nK'R := subset_trans sRG nK'G.
  have sK'_dv_p: #|[set: sK'G']| %| p.
    suffices: #|G' : 'C([set: sK'G'] | 'Cl)| %| #|G' : K^`(1)|.
      rewrite -(divgS (mulgen_subl _ _)) /= {2}norm_mulgenEr //.
      rewrite coprime_cardMg ?(coprimeSg (normal_sub nsK'K)) //.
      rewrite mulKn ?cardG_gt0 // -indexgI; apply: dvdn_trans.
      exact: atrans_dvd_index_in (Clifford_atrans _ _).
    rewrite indexgS //; apply: subset_trans (Clifford_astab sK'G').
    exact: mulgen_subl.
  have eq_sK': #|[set: sK'K]| = #|[set: sK'G']|.
    rewrite !cardsT !cardE -!(size_map (fun i => socle_val i)).
    apply: perm_eq_size.
    rewrite uniq_perm_eq 1?(map_inj_uniq val_inj) 1?enum_uniq // => V.
    apply/mapP/mapP=> [] [i _ ->{V}].
      exists (PackSocle (component_socle sK'G' (socle_simple i))).
        by rewrite mem_enum.
      by rewrite PackSocleK.
    exists (PackSocle (component_socle sK'K (socle_simple i))).
      by rewrite mem_enum.
    by rewrite PackSocleK.
  have [i def_i]: exists i, [set: sK'G'] = [set i].
    apply/cards1P; rewrite -dvdn1 -{7}(eqnP coKp) dvdn_gcd.
    by rewrite -{1}eq_sK' sK'_dv_K sK'_dv_p.
  pose M := socle_base i; have simM : mxsimple rK'G' M := socle_simple i.
  have cycGq: cyclic (G' / K^`(1)).
    by rewrite /G' mulgenC quotient_mulgen ?quotient_cyclic.
  apply closF; apply: (mx_irr_prime_index closF irrG' cycGq simM) => x K'x /=.
  apply: (component_mx_iso simM); first exact: Clifford_simple.
  have jP: component_mx rK'G' (M *m rG' x) \in socle_enum sK'G'.
    by apply: component_socle; exact: Clifford_simple.
  pose j := PackSocle jP; apply: submx_trans (_ : j <= _)%MS.
    by rewrite PackSocleK component_mx_id //; exact: Clifford_simple.
  by rewrite ((j =P i) _) // -in_set1 -def_i inE.
have linU: \rank U = 1%N by apply/eqP; rewrite abelian_abs_irr in irrK'K.
case: irrU => _ nz1 _; apply: contra nz1; move/eqP=> fix0.
by rewrite -submx0 -fix0 -(rfix_mx_rstabC rK) ?der_sub // rker_linear.
Qed.

(* Internal action version of B & G, Theorem 3.5. *)
Theorem Frobenius_prime_cent_prime : forall k gT (G K R V : {group gT}),
    solvable G ->
    K <| G -> R \in [complements to K in G] -> prime #|R| -> 'C_K(R) = 1->
    k.-abelem V -> G \subset 'N(V) -> ~~ (k %| #|G|) ->
  #|'C_V(R)| = k -> K^`(1) \subset 'C_K(V).
Proof.
move=> k gT G K R V solG nsKG complGKR R_pr regRK abelV nVG k'G primeRV.
have defG: K ><| R = G by apply/sdprod_normal_compl; rewrite complgC.
have [_ sRG _ nKR _] := sdprod_context defG; rewrite subsetI der_sub.
case: (eqsVneq V 1) => [-> | ntV]; first exact: cents1.
pose rV := abelem_repr abelV ntV nVG.
apply: subset_trans (_ : rker rV \subset _); last first.
  by rewrite rker_abelem subsetIr.
have k_pr: prime k by case/pgroup_pdiv: (abelem_pgroup abelV).
apply: (Frobenius_prime_rfix1 defG) => //.
  by rewrite /pgroup charf'_nat -val_eqE /= val_Fp_nat.
apply/eqP; rewrite rfix_abelem // -(eqn_exp2l _ _ (prime_gt1 k_pr)).
rewrite -{1}(card_Fp k_pr) -card_rowg rowg_mxK.
by rewrite card_injm ?abelem_rV_injm ?subsetIl ?primeRV.
Qed.

(* Because it accounts for nearly half of the length of Section 3 (7 pages    *)
(* out of 16), and it is not used in the rest of Section 3, we have moved the *)
(* proof of B & G, Theorem 3.6 (odd_sdprod_Zgroup_cent_prime_plength1) to its *)
(* own separate file, BGtheorem3_6.v.                                         *)

(* This is B & G, Theorem 3.7. *)
Theorem odd_prime_Frobenius_kernel_nil : forall gT (G K R : {group gT}),
   K ><| R = G -> solvable G -> prime #|R| -> 'C_K(R) = 1 -> nilpotent K.
Proof.
move=> gT G K R defG solG R_pr regR.
elim: {K}_.+1 {-2}K (ltnSn #|K|) => // m IHm K leKm in G defG solG regR *.
have [nsKG sRG defKR nKR tiKR] := sdprod_context defG.
have [sKG nKG] := andP nsKG.
wlog ntK: / K :!=: 1 by case: eqP => [-> _ | _ ->] //; exact: nilpotent1.
have [L maxL _]: {L : {group gT} | maxnormal L K G & [1] \subset L}.
  by apply: maxgroup_exists; rewrite proper1G ntK norms1.
have [ltLK nLG]:= andP (maxgroupp maxL); have [sLK not_sKL]:= andP ltLK.
have{m leKm IHm}nilL: nilpotent L.
  pose G1 := L <*> R; have nLR := subset_trans sRG nLG.
  have sG1G: G1 \subset G by rewrite mulgen_subG (subset_trans sLK).
  have defG1: L ><| R = G1.
    by rewrite sdprodEgen //; apply/eqP; rewrite -subG1 -tiKR setSI.
  apply: (IHm _ _ _ defG1); rewrite ?(solvableS sG1G) ?(oddSg sG1G) //.
    exact: leq_trans (proper_card ltLK) _.
  by apply/eqP; rewrite -subG1 -regR setSI.
have sLG := subset_trans sLK sKG; have nsLG: L <| G by exact/andP.
have sLF: L \subset 'F(G) by exact: Fitting_max.
have frobG: [Frobenius G = K ><| R] by exact/prime_FrobeniusP.
have solK := solvableS sKG solG.
have frobGq := Frobenius_quotient frobG solK nsLG not_sKL.
suffices sKF: K \subset 'F(K) by exact: nilpotentS sKF (Fitting_nil K).
apply: subset_trans (chief_stab_sub_Fitting solG nsKG).
rewrite subsetI subxx; apply/bigcapsP=> [[X Y]] /=; set V := X / Y.
case/andP=> chiefXY sXF; have [maxY nsXG] := andP chiefXY.
have [ltYX nYG] := andP (maxgroupp maxY); have [sYX _]:= andP ltYX.
have [sXG nXG] := andP nsXG; have sXK := subset_trans sXF (Fitting_sub K).
have minV := chief_factor_minnormal chiefXY.
have cVL: L \subset 'C(V | 'Q).
  apply: subset_trans (subset_trans sLF (Fitting_stab_chief solG _)) _ => //.
  exact: (bigcap_inf (X, Y)).
have nVG: {acts G, on group V | 'Q}.
  by split; rewrite ?quotientS ?subsetT // actsQ // normal_norm.
pose V1 := sdpair1 <[nVG]> @* V.
have [p p_pr abelV]: exists2 p, prime p & p.-abelem V.
  apply/is_abelemP; apply: charsimple_solvable (quotient_sol _ _).
    exact: minnormal_charsimple minV.
  exact: nilpotent_sol (nilpotentS sXF (Fitting_nil _)).
have abelV1: p.-abelem V1 by rewrite morphim_abelem.
have injV1 := injm_sdpair1 <[nVG]>.
have ntV1: V1 :!=: 1.
  by rewrite -cardG_gt1 card_injm // cardG_gt1; case/andP: (mingroupp minV).
have nV1_G1 := im_sdpair_norm <[nVG]>.
pose rV := morphim_repr (abelem_repr abelV1 ntV1 nV1_G1) (subxx G).
have def_kerV: rker rV = 'C_G(V | 'Q).
  rewrite rker_morphim rker_abelem morphpreIdom morphpreIim -astabEsd //.
  by rewrite astab_actby setIid.
have kerL: L \subset rker rV by rewrite def_kerV subsetI sLG.
pose rVq := quo_repr kerL nLG.
suffices: K / L \subset rker rVq.
  rewrite rker_quo def_kerV quotientSGK //= 1?subsetI 1?(subset_trans sKG) //.
  by rewrite sLG.
have irrVq: mx_irreducible rVq.
  apply/quo_mx_irr; apply/morphim_mx_irr; apply/abelem_mx_irrP.
  apply/mingroupP; rewrite ntV1; split=> // U1; case/andP=> ntU1 nU1G sU1V.
  rewrite -(morphpreK sU1V); congr (_ @* _).
  case/mingroupP: minV => _; apply; last by rewrite sub_morphpre_injm.
  rewrite -subG1 sub_morphpre_injm ?sub1G // morphim1 subG1 ntU1 /=.
  set U := _ @*^-1 U1; rewrite -(cosetpreK U) quotient_norms //.
  have: [acts G, on U | <[nVG]>] by rewrite actsEsd ?subsetIl // morphpreK.
  rewrite astabs_actby subsetI subxx (setIidPr _) ?subsetIl //=.
  by rewrite -{1}(cosetpreK U) astabsQ ?normal_cosetpre //= -/U subsetI nYG.
have [q q_pr abelKq]: exists2 q, prime q & q.-abelem (K / L).
  apply/is_abelemP; apply: charsimple_solvable (quotient_sol _ solK).
  exact: maxnormal_charsimple maxL.
case (eqVneq q p) => [def_q | neq_qp].
  have sKGq: K / L \subset G / L by exact: quotientS.
  rewrite rfix_mx_rstabC //; have [_ _]:= irrVq; apply; rewrite ?submx1 //.
    by rewrite normal_rfix_mx_module ?quotient_normal.
  rewrite -(rfix_subg _ sKGq) rfix_pgroup_char //.
  apply: pi_pnat (abelem_pgroup abelKq) _.
  by rewrite inE /= q_pr def_q char_Fp_0.
suffices: rfix_mx rVq (R / L) == 0.
  apply: contraLR; apply: (Frobenius_rfix_compl frobGq).
  apply: pi_pnat (abelem_pgroup abelKq) _.
  by rewrite inE /= (charf_eq (char_Fp p_pr)).
rewrite -mxrank_eq0 (rfix_quo _ _ sRG) (rfix_morphim _ _ sRG).
rewrite (rfix_abelem _ _ _ (morphimS _ sRG)) mxrank_eq0 rowg_mx_eq0 -subG1.
rewrite (sub_abelem_rV_im _ _ _ (subsetIl _ _)) -(morphpreSK _ (subsetIl _ _)).
rewrite morphpreIim -gacentEsd gacent_actby gacentQ (setIidPr sRG) /=.
rewrite -coprime_quotient_cent ?(solvableS sXG) ?(subset_trans sRG) //.
  by rewrite {1}['C_X(R)](trivgP _) ?quotient1 ?sub1G // -regR setSI.
by apply: coprimeSg sXK _; exact: Frobenius_coprime frobG.
Qed.

(* This is B & G, Theorem 3.8. *)
Theorem odd_sdprod_primact_commg_sub_Fitting : forall gT (G K R : {group gT}),
    K ><| R = G -> odd #|G| -> solvable G ->
  (*1*) coprime #|K| #|R| ->
  (*2*) {in R^#, forall x, 'C_K[x] = 'C_K(R)} ->
  (*3*) 'C_('F(K))(R) = 1 ->
  [~: K, R] \subset 'F(K).
Proof.
move=> gT G; elim: {G}_.+1 {-2}G (ltnSn #|G|) => // n IHn G.
rewrite ltnS => leGn K R defG oddG solG coKR primR regR_F.
have [nsKG sRG defKR nKR tiKR] := sdprod_context defG.
have [sKG nKG] := andP nsKG.
have chF: 'F(K) \char K := Fitting_char K; have nFR := char_norm_trans chF nKR.
have nsFK := char_normal chF; have [sFK nFK] := andP nsFK.
pose KqF := K / 'F(K); have solK := solvableS sKG solG.
wlog [p p_pr pKqF]: / exists2 p, prime p & p.-group KqF.
  move=> IHp;  apply: wlog_neg => IH_KR; rewrite -quotient_cents2 //= -/KqF.
  set Rq := R / 'F(K); have nKRq: Rq \subset 'N(KqF) by exact: quotient_norms.
  rewrite centsC.
  apply: subset_trans (coprime_cent_Fitting nKRq _ _); last first.
  - exact: quotient_sol.
  - exact: coprime_morph.
  rewrite subsetI subxx centsC -['F(KqF)]Sylow_gen gen_subG.
  apply/bigcupsP=> Pq; case/SylowP=> p p_pr; rewrite /= -/KqF => sylPq.
  have chPq: Pq \char KqF.
   apply: char_trans (Fitting_char _); rewrite /= -/KqF.
    by rewrite (nilpotent_Hall_pcore (Fitting_nil _) sylPq) ?pcore_char.
  have [P defPq sFP sPK] := inv_quotientS nsFK (char_sub chPq).
  have nsFP: 'F(K) <| P by rewrite /normal sFP (subset_trans sPK).
  have{chPq} chP: P \char K.
    by apply: char_from_quotient nsFP (Fitting_char _) _; rewrite -defPq.
  have defFP: 'F(P) = 'F(K).
    apply/eqP; rewrite eqEsubset !Fitting_max ?Fitting_nil //.
    by rewrite char_normal ?(char_trans (Fitting_char _)).
  have coPR := coprimeSg sPK coKR.
  have nPR: R \subset 'N(P) := char_norm_trans chP nKR.
  pose G1 := P <*> R.
  have sG1G: G1 \subset G by rewrite /G1 -defKR norm_mulgenEr ?mulSg.
  have defG1: P ><| R = G1 by rewrite sdprodEgen ?coprime_TIg.
  rewrite defPq quotient_cents2r //= -defFP.
  have:= sPK; rewrite subEproper; case/predU1P=> [defP | ltPK].
    rewrite IHp // in IH_KR; exists p => //.
    by rewrite /KqF -{2}defP -defPq (pHall_pgroup sylPq).
  move/IHn: defG1 => ->; rewrite ?(oddSg sG1G) ?(solvableS sG1G) ?defFP //.
    apply: leq_trans leGn; rewrite /= norm_mulgenEr //.
    by rewrite -defKR !coprime_cardMg // ltn_pmul2r ?proper_card.
  by move=> x Rx; rewrite -(setIidPl sPK) -!setIA primR.
wlog r_pr: / prime #|R|; last set r := #|R| in r_pr.
  have [-> _ | [r r_pr]] := trivgVpdiv R; first by rewrite commG1 sub1G.
  case/Cauchy=> // x; rewrite -cycle_subG subEproper orderE; set X := <[x]>.
  case/predU1P=> [-> -> -> // | ltXR rX _]; have sXR := proper_sub ltXR.
  have defCX: 'C_K(X) = 'C_K(R).
    rewrite cent_cycle primR // !inE -order_gt1 orderE rX prime_gt1 //=.
    by rewrite -cycle_subG.
  have primX: {in X^#, forall y, 'C_K[y] = 'C_K(X)}.
    by move=> y; case/setD1P=> nty Xy; rewrite primR // !inE nty (subsetP sXR).
  have nKX := subset_trans sXR nKR; have coKX := coprimegS sXR coKR.
  pose H := K <*> X; have defH: K ><| X = H by rewrite sdprodEgen ?coprime_TIg.
  have sHG: H \subset G by rewrite /H -defKR norm_mulgenEr ?mulgSS.
  have ltHn: #|H| < n.
    rewrite (leq_trans _ leGn) /H ?norm_mulgenEr // -defKR !coprime_cardMg //.
    by rewrite ltn_pmul2l ?proper_card.
  have oddH := oddSg sHG oddG; have solH := solvableS sHG solG.
  have regX_F: 'C_('F(K))(X) = 1.
   by rewrite -regR_F -(setIidPl sFK) -!setIA defCX.
  have:= IHn _ ltHn _ _ defH oddH solH coKX primX regX_F.
  rewrite -!quotient_cents2 ?(subset_trans sXR) //; move/setIidPl <-.
  rewrite -coprime_quotient_cent ?(subset_trans sXR) // defCX.
  by rewrite coprime_quotient_cent ?subsetIr.
apply: subset_trans (chief_stab_sub_Fitting solG nsKG) => //.
rewrite subsetI commg_subl nKR; apply/bigcapsP => [[U V]] /=.
case/andP=> chiefUV sUF; set W := U / V.
have minW := chief_factor_minnormal chiefUV.
have [ntW nWG] := andP (mingroupp minW).
case/andP: (chiefUV); move/maxgroupp; do 2![case/andP]=> sVU _ nVG nsUG.
have sUK := subset_trans sUF sFK; have sVK := subset_trans sVU sUK.
have nVK := subset_trans sKG nVG; have nVR := subset_trans sRG nVG.
have [q q_pr abelW]: exists2 q, prime q & q.-abelem W.
  apply/is_abelemP; apply: charsimple_solvable (minnormal_charsimple minW) _.
  by rewrite quotient_sol // (solvableS sUK).
have regR_W: 'C_(W)(R / V) = 1.
  rewrite -coprime_quotient_cent ?(coprimeSg sUK) ?(solvableS sUK) //.
  by rewrite -(setIidPl sUF) -setIA regR_F (setIidPr _) ?quotient1 ?sub1G.
rewrite sub_astabQ comm_subG ?quotientR //=.
have defGv: (K / V) * (R / V) = G / V by rewrite -defKR quotientMl.
have oRv: #|R / V| = r.
  rewrite card_quotient // -indexgI -(setIidPr sVK) setICA setIA tiKR.
  by rewrite (setIidPl (sub1G _)) indexg1.
have defCW: 'C_(G / V)(W) = 'C_(K / V)(W).
  apply/eqP; rewrite eqEsubset andbC setSI ?quotientS //=.
  rewrite subsetI subsetIr /= andbT.
  rewrite -(coprime_mulG_setI_norm defGv) ?coprime_morph ?norms_cent //=.
  suffices ->: 'C_(R / V)(W) = 1 by rewrite mulg1 subsetIl.
  apply/trivgP; apply/subsetP=> x; case/setIP=> Rx cWx.
  apply: contraR ntW => ntx; rewrite -subG1 -regR_W subsetI subxx centsC /= -/W.
  by apply: contraR ntx; move/prime_TIg <-; rewrite ?oRv // inE Rx.
have [P sylP nPR] := coprime_Hall_exists p nKR coKR solK.
have [sPK pP _] := and3P sylP.
have nVP := subset_trans sPK nVK; have nFP := subset_trans sPK nFK.
have sylPv: p.-Sylow(K / V) (P / V) by rewrite quotient_pHall.
have defKv: (P / V) * 'C_(G / V)(W) = (K / V).
  rewrite defCW; apply/eqP; rewrite eqEsubset mulG_subG subsetIl quotientS //=.
  have sK_PF: K \subset P * 'F(K).
    rewrite (normC nFP) -quotientSK // subEproper eq_sym eqEcard quotientS //=.
    by rewrite (card_Hall (quotient_pHall nFP sylP)) part_pnat_id ?leqnn.
  rewrite (subset_trans (quotientS _ sK_PF)) // quotientMl // mulgS //.
  rewrite subsetI -quotient_astabQ !quotientS //.
  by rewrite (subset_trans (Fitting_stab_chief solG nsKG)) ?(bigcap_inf (U, V)).
have nW_ := subset_trans (quotientS _ _) nWG; have nWK := nW_ _ sKG. 
rewrite -quotient_cents2 ?norms_cent ?(nW_ _ sRG) //.
have [eq_qp | p'q] := eqVneq q p.
  apply: subset_trans (sub1G _); rewrite -trivg_quotient quotientS // centsC.
  apply/setIidPl; case/mingroupP: minW => _; apply; last exact: subsetIl.
  rewrite andbC normsI ?norms_cent // ?quotient_norms //=.
  have nsWK: W <| K / V by rewrite /normal quotientS.
  have sWP: W \subset P / V.
    by rewrite (normal_sub_max_pgroup (Hall_max sylPv)) -?eq_qp ?abelem_pgroup.
  rewrite -defKv centM setIA setIAC /=.
  rewrite ['C_W(_)](setIidPl _); last by rewrite centsC subsetIr.
  have nilPv: nilpotent (P / V) := pgroup_nil (pHall_pgroup sylPv).
  by rewrite -(setIidPl sWP) -setIA nil_meet_Z // (normalS _ (quotientS V sPK)).
rewrite -defKv -quotient_mulg -mulgA mulSGid ?subsetIr // quotient_mulg.
have sPG := subset_trans sPK sKG.
rewrite quotient_cents2 ?norms_cent ?nW_ //= commGC.
pose Hv := (P / V) <*> (R / V).
have sHGv: Hv \subset G / V by rewrite mulgen_subG !quotientS.
have solHv: solvable Hv := solvableS sHGv (quotient_sol V solG).
have sPHv: P / V \subset Hv by exact: mulgen_subl.
have nPRv: R / V \subset 'N(P / V) := quotient_norms _ nPR.
have coPRv: coprime #|P / V| #|R / V| := coprime_morph _ (coprimeSg sPK coKR).
apply: subset_trans (subsetIr (P / V) _).
have oHv: #|Hv| = (#|P / V| * #|R / V|)%N.
  by rewrite /Hv norm_mulgenEr // coprime_cardMg // oRv.
move/(odd_prime_sdprod_abelem_cent1 solHv): (abelW); apply=> //.
- exact: oddSg sHGv (quotient_odd _ _).
- by rewrite /normal sPHv mulgen_subG normG.
- by rewrite /Hall sPHv /= -divgS //= oHv mulKn ?cardG_gt0.
- by rewrite inE coprime_TIg ?eqxx //= norm_mulgenEr.
- by rewrite oRv.
- exact: subset_trans sHGv nWG.
rewrite oHv euclid //; apply/norP; split.
  by apply: contra p'q; exact: (pgroupP (pHall_pgroup sylPv)).
rewrite -p'natE //; apply: coprime_p'group (abelem_pgroup abelW) ntW.
by rewrite coprime_sym coprime_morph // (coprimeSg sUK).
Qed.

(* This is B & G, Theorem 3.9 (for external action), with the incorrectly *)
(* omitted nontriviality assumption reinstated.                           *)
Theorem ext_odd_regular_pgroup_cyclic : forall (aT rT : finGroupType) p,
    forall (D R : {group aT}) (K H : {group rT}) (to : groupAction D K),
    p.-group R -> odd #|R| -> H :!=: 1 ->
    {acts R, on group H | to} -> {in R^#, forall x, 'C_(H | to)[x] = 1} ->
  cyclic R.
Proof.
move=> aT rT p D R0 K H0 to pR0 oddR0 ntH0 actsR0 regR0.
pose gT := sdprod_groupType <[actsR0]>.
pose H : {group gT} := (sdpair1 <[actsR0]> @* H0)%G.
pose R : {group gT} := (sdpair2 <[actsR0]> @* R0)%G.
pose G : {group gT} := [set: gT]%G.
have{pR0} pR: p.-group R by rewrite morphim_pgroup.
have{oddR0} oddR: odd #|R| by rewrite morphim_odd.
case: (eqsVneq R 1) => [R1 | ntR].
  by rewrite -(im_invm (injm_sdpair2 <[actsR0]>)) {2}R1 morphim1 cyclic1.
have{ntH0} ntH: H :!=: 1.
  apply: contra ntH0; move/eqP => H1.
  by rewrite -(im_invm (injm_sdpair1 <[actsR0]>)) {2}H1 morphim1.
have{regR0 ntR} frobG: [Frobenius G = H ><| R].
  apply/Frobenius_semiregularP => // [|x]; first exact: sdprod_sdpair.
  case/setD1P=> nt_x; case/morphimP=> x2 _ Rx2 def_x.
  apply/trivgP; rewrite -(morphpreSK _ (subsetIl _ _)) morphpreI.
  rewrite /= -cent_cycle def_x -morphim_cycle // -gacentEsd.
  rewrite injmK ?injm_sdpair1 // (trivgP (injm_sdpair1 _)).
  rewrite -(regR0 x2) ?inE ?Rx2 ?andbT; last first.
    by apply: contra nt_x; rewrite def_x; move/eqP->; rewrite morph1.
  have [sRD sHK]: R0 \subset D /\ H0 \subset K by case actsR0; move/acts_dom.
  have sx2R: <[x2]> \subset R0 by rewrite cycle_subG.
  rewrite gacent_actby setIA setIid (setIidPr sx2R).
  rewrite !gacentE ?cycle_subG ?sub1set ?(subsetP sRD) //.
  by rewrite !setIS ?afixS ?sub_gen.
suffices: cyclic R by rewrite (injm_cyclic (injm_sdpair2 _)).
move: gT H R G => {aT rT to D K H0 R0 actsR0} gT H R G in ntH pR oddR frobG *.
have [defG _ _ _ _] := Frobenius_context frobG; case/sdprodP: defG => _ _ nHR _.
have coHR := Frobenius_coprime frobG.
rewrite (odd_pgroup_rank1_cyclic pR oddR) leqNgt; apply: contra ntH.
case/p_rank_geP=> E; rewrite 2!inE -andbA; case/and3P=> sER abelE dimE2.
have ncycE: ~~ cyclic E by rewrite (abelem_cyclic abelE) (eqP dimE2).
have nHE := subset_trans sER nHR; have coHE := coprimegS sER coHR.
rewrite -subG1 (coprime_abelian_gen_cent1 _ _ nHE) ?(abelem_abelian abelE) //.
rewrite big1 // => x; case/setD1P=> nt_x Ex; apply: val_inj => /=.
by apply: (Frobenius_reg_ker frobG); rewrite !inE nt_x (subsetP sER).
Qed.

(* Internal action version or 3.9 (possibly, the only one we should keep). *)
Theorem odd_regular_pgroup_cyclic : forall gT p (H R : {group gT}),
    p.-group R -> odd #|R| -> H :!=: 1 -> R \subset 'N(H) ->
    {in R^#, forall x, 'C_(H)[x] = 1} ->
  cyclic R.
Proof.
move=> gT p H R pR oddR ntH nHR regR.
have actsR: {acts R, on group H | 'J} by split; rewrite ?subsetT ?astabsJ.
apply: ext_odd_regular_pgroup_cyclic pR oddR ntH actsR _ => // x Rx.
by rewrite gacentJ cent_set1 regR.
Qed.

(* Another variant of the internal action, which avoids Frobenius groups     *)
(* altogether.                                                               *)
Theorem simple_odd_regular_pgroup_cyclic : forall gT p (H R : {group gT}),
    p.-group R -> odd #|R| -> H :!=: 1 -> R \subset 'N(H) ->
    {in R^#, forall x, 'C_(H)[x] = 1} ->
  cyclic R.
Proof.
move=> gT p H R pR oddR ntH nHR regR.
rewrite (odd_pgroup_rank1_cyclic pR oddR) leqNgt; apply: contra ntH.
case/p_rank_geP=> E; rewrite 2!inE -andbA; case/and3P=> sER abelE dimE2.
have ncycE: ~~ cyclic E by rewrite (abelem_cyclic abelE) (eqP dimE2).
have nHE := subset_trans sER nHR.
have coHE := coprimegS sER (regular_norm_coprime nHR regR).
rewrite -subG1 (coprime_abelian_gen_cent1 _ _ nHE) ?(abelem_abelian abelE) //.
rewrite big1 // => x; case/setD1P=> nt_x Ex; apply: val_inj => /=.
by rewrite regR // !inE nt_x (subsetP sER).
Qed.

Section Wielandt_Frobenius.

Variables (gT : finGroupType) (G K R : {group gT}).
Implicit Type A : {group gT}.

(* This is Peterfalvi (9.1). *)
Lemma Frobenius_Wielandt_fixpoint : forall M : {group gT},
    [Frobenius G = K ><| R] ->
    G \subset 'N(M) -> coprime #|M| #|G| -> solvable M ->
 [/\ (#|'C_M(G)| ^ #|R| * #|M| = #|'C_M(R)| ^ #|R| * #|'C_M(K)|)%N,
     'C_M(R) = 1 -> K \subset 'C(M)
   & 'C_M(K) = 1 -> (#|M| = #|'C_M(R)| ^ #|R|)%N].
Proof.
move=> M frobG nMG coMG solM; have [defG _ ntR _ _] := Frobenius_context frobG.
have [_ _ _ snRG] := and4P frobG; move/eqP: snRG => snRG.
have [nsKG sRG _ _ tiKR] := sdprod_context defG; have [sKG _] := andP nsKG.
pose m0 (_ : {group gT}) := 0%N.
pose Dm := [set 1%G; G]; pose Dn := K |: orbit 'JG K R.
pose m := [fun A => 0%N with 1%G |-> #|K|, G |-> 1%N].
pose n A : nat := A \in Dn.
have out_m: {in [predC Dm], m =1 m0}.
  by move=> A; rewrite !inE /=; case/norP; do 2!move/negbTE->.
have out_n: {in [predC Dn], n =1 m0}.
  by rewrite /n => A /=; move/negbTE=> /= ->.
have ntG: G != 1%G by case: eqP sRG => // -> <-; rewrite subG1.
have neqKR: K \notin orbit 'JG K R.
  apply/imsetP=> [[x _ defK]]; have:= Frobenius_dvd_ker1 frobG.
  by rewrite defK cardJg gtnNdvd // ?prednK // -subn1 subn_gt0 cardG_gt1.
have Gmn: forall A, m A + n A > 0 -> A \subset G.
  move=> A /=; case: eqP => [-> | ] _; first by rewrite sub1G.
  rewrite /n 2!inE; do 2!case: eqP => [-> // | ] _.
  case R_A: (A \in _) => // _; case/imsetP: R_A => x Kx ->{A}.
  by rewrite conj_subG ?(subsetP sKG).
have partG: {in G, forall a,
              \sum_(A | a \in gval A) m A = \sum_(A | a \in gval A) n A}%N.
- move=> a Ga; case: (eqVneq a 1) => [-> | nt_a].
    rewrite (bigD1 1%G) ?inE ?eqxx //= (bigD1 G) ?inE ?group1 //=.
    rewrite (negbTE ntG) !eqxx big1 ?addn1 => [|A]; last first.
      by rewrite group1 -negb_or -in_set2; exact: out_m.
    rewrite (bigID (mem Dn)) /= addnC big1 => [|A]; last first.
      by rewrite group1; exact: out_n.
    transitivity #|Dn|.
      rewrite cardsU1 neqKR card_orbit astab1JG.
      by rewrite -{3}(setIidPl sKG) -setIA snRG tiKR indexg1.
    by rewrite -sum1_card /n; apply: eq_big => [A | A ->]; rewrite ?group1.
  rewrite (bigD1 G) //= (negbTE ntG) eqxx big1 => [|A]; last first.
    case/andP=> Aa neAG; apply: out_m; rewrite !inE; case: eqP => // A1.
    by rewrite A1 inE (negbTE nt_a) in Aa.
  have [partG tiG _] := and3P (Frobenius_partition frobG).
  do [rewrite -(eqP partG); set pG := _ |: _] in Ga tiG.
  pose A := cover_at a pG.
  rewrite (bigD1 <<A>>%G) /=; last by rewrite mem_gen // mem_cover_at.
  rewrite big1 => [|B]; last first.
    case/andP=> Ba neqBA; rewrite -/(false : nat); congr (nat_of_bool _).
    apply: contraTF neqBA; rewrite negbK -val_eqE /=.
    case/setU1P=> [BK |]; last case/imsetP=> x Kx defB.
      rewrite BK -(cover_at_eq _ tiG) ?Ga -/A ?setU11 //= in Ba.
      by rewrite BK (eqP Ba) genGid.
    have Rx_a: a \in R^# :^ x by rewrite conjD1g !inE nt_a -(congr_group defB).
    rewrite -(cover_at_eq _ tiG) ?Ga -/A /= ?inE ?mem_imset ?orbT // in Rx_a.
    by rewrite defB (eqP Rx_a) /= conjD1g genD1 ?group1 // genGid.
  rewrite /n /A !inE -val_eqE /= -/(true : nat); congr ((_ : bool) + _)%N.
  case/setU1P: (cover_at_mem Ga) => [-> |]; first by rewrite genGid eqxx.
  case/imsetP=> x Kx ->; symmetry; apply/orP; right.
  apply/imsetP; exists x => //.
  by apply: val_inj; rewrite conjD1g /= genD1 ?group1 // genGid.
move/eqP: (solvable_Wielandt_fixpoint Gmn nMG coMG solM partG).
rewrite (bigD1 1%G) // (bigD1 G) //= eqxx (setIidPl (cents1 _)) cards1 muln1.
rewrite (negbTE ntG) eqxx mul1n -(sdprod_card defG) (mulnC #|K|) expn_mulr.
rewrite mulnA -expn_mull big1 ?muln1 => [|A]; last first.
  by rewrite -negb_or -in_set2; move/out_m; rewrite /m => /= ->.
rewrite mulnC eq_sym (bigID (mem Dn)) /= mulnC.
rewrite big1 ?mul1n => [|A]; last by move/out_n->.
rewrite big_setU1 //= /n setU11 mul1n.
rewrite (eq_bigr (fun _ => #|'C_M(R)| ^ #|R|)%N) => [|A R_A]; last first.
  rewrite inE R_A orbT mul1n; case/imsetP: R_A => x Kx ->.
  suffices nMx: x \in 'N(M) by rewrite -{1}(normP nMx) centJ -conjIg !cardJg.
  exact: subsetP (subsetP sKG x Kx).
rewrite mulnC prod_nat_const card_orbit astab1JG.
have ->: 'N_K(R) = 1 by rewrite -(setIidPl sKG) -setIA snRG tiKR.
rewrite indexg1 -expn_mull eq_sym eqn_exp2r ?cardG_gt0 //; move/eqP=> eq_fix.
split=> // [regR | regK].
  rewrite centsC (sameP setIidPl eqP) eqEcard subsetIl /=.
  move: eq_fix; rewrite regR cards1 exp1n mul1n => <-.
  suffices ->: 'C_M(G) = 1 by rewrite cards1 exp1n mul1n.
  by apply/trivgP; rewrite -regR setIS ?centS //; case/sdprod_context: defG.
move: eq_fix; rewrite regK cards1 muln1 => <-.
suffices ->: 'C_M(G) = 1 by rewrite cards1 exp1n mul1n.
by apply/trivgP; rewrite -regK setIS ?centS.
Qed.

End Wielandt_Frobenius.

(* This is B & G, Theorem 3.10. *)
Theorem Frobenius_primact : forall gT (G K R M : {group gT}),
    [Frobenius G = K ><| R] -> solvable G ->
    G \subset 'N(M) -> solvable M -> M :!=: 1 ->
  (*1*) coprime #|M| #|G| ->
  (*2*) {in R^#, forall x, 'C_M[x] = 'C_M(R)} ->
  (*3*) 'C_M(K) = 1 ->
  [/\ prime #|R|,
      #|M| = (#|'C_M(R)| ^ #|R|)%N
    & cyclic 'C_M(R) -> K^`(1) \subset 'C_K(M)].
Proof.
move=> gT G K R M; move: {2}_.+1 (ltnSn #|M|) => n.
elim: n => // n IHn in gT G K R M *; rewrite ltnS => leMn.
move=> frobG solG nMG solM ntM coMG primRM tcKM.
case: (Frobenius_Wielandt_fixpoint frobG nMG) => // _ _; move/(_ tcKM)=> oM.
have [defG ntK ntR ltKG _]:= Frobenius_context frobG.
have Rpr: prime #|R|.
  have [R1 | [r r_pr]] := trivgVpdiv R; first by case/eqP: ntR.
  case/Cauchy=> // x Rx ox; pose R0 := <[x]>; pose G0 := K <*> R0.
  have [_ defKR nKR tiKR] := sdprodP defG.
  have sR0R: R0 \subset R by rewrite cycle_subG.
  have sG0G: G0 \subset G by rewrite /G0 -genM_mulgen gen_subG -defKR mulgS.
  have nKR0 := subset_trans sR0R nKR; have nMG0 := subset_trans sG0G nMG.
  have ntx: <[x]> != 1 by rewrite cycle_eq1 -order_gt1 ox prime_gt1.
  case: (eqVneq 'C_M(R) 1) => [tcRM | ntcRM].
    by rewrite -cardG_gt1 oM tcRM cards1 exp1n in ntM.
  have frobG0: [Frobenius G0 = K ><| R0].
    apply/Frobenius_semiregularP=> // [|y].
      by apply: sdprodEgen nKR0 (trivgP _); rewrite -tiKR setIS.
    case/setD1P=> nty x_y; apply: (Frobenius_reg_ker frobG).
    by rewrite !inE nty (subsetP sR0R).
  case: (Frobenius_Wielandt_fixpoint frobG0 nMG0 (coprimegS _ coMG)) => // _ _.
  move/(_ tcKM); move/eqP; rewrite oM cent_cycle.
  rewrite primRM; last by rewrite !inE Rx andbT -cycle_eq1.
  by rewrite eqn_exp2l ?cardG_gt1 // -orderE ox; move/eqP->.
split=> // cyc_cMR.
have nM_MG: M <*> G \subset 'N(M) by rewrite mulgen_subG normG.
have [V minV sVM] := minnormal_exists ntM nM_MG.
have [] := minnormal_solvable minV sVM solM.
rewrite mulgen_subG; case/andP=> nVM nVG ntV; case/is_abelemP=> [q q_pr abelV].
have coVG := coprimeSg sVM coMG; have solV := solvableS sVM solM.
have cVK': K^`(1) \subset 'C_K(V).
  case: (eqVneq 'C_V(R) 1) => [tcVR | ntcRV].
    case: (Frobenius_Wielandt_fixpoint frobG nVG) => // _.
    by move/(_ tcVR)=> cVK _; rewrite (setIidPl cVK) der_sub.
  case/prime_FrobeniusP: frobG => //.
  case/sdprod_normal_compl=> nsKG; rewrite complgC => complR regR.
  have ocVR: #|'C_V(R)| = q.
    have [u def_u]: exists u, 'C_V(R) = <[u]>.
      by apply/cyclicP; apply: cyclicS (setSI _ sVM) cyc_cMR.
    move: ntcRV; rewrite def_u -orderE cycle_eq1.
    by case/(abelem_order_p abelV) => //; rewrite -cycle_subG -def_u subsetIl.
  apply: (Frobenius_prime_cent_prime _ nsKG complR _ _ abelV) => //.
  by rewrite -prime_coprime // -ocVR (coprimeSg (subsetIl _ _)).
have cMK': K^`(1) / V \subset 'C_(K / V)(M / V).
  case: (eqVneq (M / V) 1) => [-> | ntMV].
    by rewrite subsetI cents1 quotientS ?der_sub.
  have coKR := Frobenius_coprime frobG.
  case/prime_FrobeniusP: frobG => //.
  case/sdprod_context=> nsKG sRG defKR nKR tiKR regR; have [sKG _] := andP nsKG.
  have nVK := subset_trans sKG nVG; have nVR := subset_trans sRG nVG.
  have RVpr: prime #|R / V|.
    rewrite card_quotient // -indexgI setIC coprime_TIg ?(coprimegS sRG) //.
    by rewrite indexg1.
  have frobGV: [Frobenius G / V = (K / V) ><| (R / V)].
    apply/prime_FrobeniusP; rewrite // -?cardG_gt1 ?card_quotient //.
      rewrite -indexgI setIC coprime_TIg ?(coprimegS sKG) //.
      by rewrite indexg1 cardG_gt1.
    rewrite -coprime_norm_quotient_cent ?(coprimegS sRG) //= regR quotient1.
    rewrite -defKR quotientMl // sdprodE ?quotient_norms //.
    by rewrite coprime_TIg ?coprime_morph.
  have ltMVn: #|M / V| < n by apply: leq_trans leMn; rewrite ltn_quotient.
  rewrite quotient_der //; move/IHn: frobGV.
  case/(_ _ ltMVn); rewrite ?quotient_sol ?quotient_norms ?coprime_morph //.
  - move=> Vx; case/setD1P=> ntVx; case/morphimP=> x nVx Rx defVx.
    rewrite defVx /= -cent_cycle -quotient_cycle //; congr 'C__(_ / V).
    apply/eqP; rewrite eqEsubset cycle_subG Rx /=.
    apply: contraR ntVx; move/(prime_TIg Rpr); move/trivgP.
    rewrite defVx /= (setIidPr _) cycle_subG //; move/set1P->.
    by rewrite morph1.
  - rewrite -coprime_norm_quotient_cent ?(coprimegS sKG) ?(subset_trans sKG) //.
    by rewrite tcKM quotient1.
  case=> // _ _ -> //; rewrite -coprime_quotient_cent ?quotient_cyclic //.
  by rewrite (coprimegS sRG).
rewrite !subsetI in cVK' cMK' *.
case/andP: cVK' => sK'K cVK'; case/andP: cMK' => _ cMVK'; rewrite sK'K.
have sK'G: K^`(1) \subset G by rewrite (subset_trans sK'K) ?proper_sub.
have coMK': coprime #|M| #|K^`(1)| := coprimegS sK'G coMG.
rewrite (stable_factor_cent cVK') // /stable_factor /normal sVM nVM !andbT.
by rewrite commGC -quotient_cents2 // (subset_trans sK'G).
Qed.

End BGsection3.