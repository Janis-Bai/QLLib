From mathcomp Require Import all_boot all_order ssralg ssrint ssrnum matrix.
From mathcomp Require Import interval rat.
From mathcomp Require Import boolp classical_sets functions mathcomp_extra.
From mathcomp Require Import reals ereal interval_inference.
From mathcomp Require Import topology tvs normedtype landau sequences derive.
From mathcomp Require Import realfun interval_inference convex interval exp lebesgue_integral.
From mathcomp Require Import hoelder counting_measure cardinality measure all_algebra.
From mathcomp Require Import ess_sup_inf finmap.

From QLLib Require Import interval_einference.

Import Order.TTheory GRing.Theory Num.Theory.

(* A full line should represent a meaningful reasoning step *)
(** * Connectives in QLLib and their Properties *)
(** ** Definitions **)
Section definitions.

Context {R: realType}.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.
Local Open Scope order_scope.
Local Open Scope ereal_scope.

Definition p_sum_int_fun (a b: {nonneg \bar R}) (n: nat) := if n == 0%N then a else if n == 1%N then b else 0%:E%:nng.

Definition p_sum (p: \bar R) (a b: {nonneg \bar R}):=
  'N[counting]_p [(fun n => (p_sum_int_fun a b n)%:num)].

Definition p_sum_nng (p: \bar R) (a b: {nonneg \bar R}): {nonneg \bar R}.
Proof.
  exists (p_sum p a b).
  apply/andP. split.
  - apply/orP. left. by apply Lnorm_ge0.
  - rewrite in_itv /=. apply/andP. split; last done.
    by apply Lnorm_ge0.
Defined.
(** Inversion of nonnegative extended reals *)
Definition invnnge (a: {nonneg \bar R}) := a%:num^-1%:nng.

(** Multiplication of nonnegative extended reals *)
Definition mulnnge (a b: {nonneg \bar R}) := (a%:num * b%:num)%:nng.

(** Comultiplication of nonnegative extended reals *)
Definition comulnnge (a b: {nonneg \bar R}) := invnnge (mulnnge (invnnge a) (invnnge b)).

(** Division of nonnegative extended reals *)
Definition divnnge (a b: {nonneg \bar R}) := comulnnge (invnnge a) b.

(** p-sums, both for positive p and negative p *)
Definition p_sum_de_morgan (p: \bar R) (a b: {nonneg \bar R}): {nonneg \bar R} :=
  if (p > 0%R) then
    p_sum_nng p a b
  else if (p < 0%R) then
    invnnge (p_sum_nng (-p) (invnnge a) (invnnge b))
  else 0%:E%:nng.

End definitions.

Declare Scope nngereal_scope.

Notation "x `*" := (invnnge x) : nngereal_scope.
Notation "x -o y" := (divnnge x y) (at level 43, left associativity) : nngereal_scope.
Notation "x ⊗ y" := (mulnnge x y) (at level 46, left associativity) : nngereal_scope.
Notation "x ⊗* y" := (comulnnge x y) (at level 46, left associativity) : nngereal_scope.
Notation "x ⊕ [ p ] y" := (p_sum_de_morgan p x y) (at level 50, left associativity) : nngereal_scope.

Delimit Scope nngereal_scope with NNGE.

Section results.

Variable R: realType.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.
Local Open Scope order_scope.
Local Open Scope ereal_scope.
Local Open Scope nngereal_scope.

(** ** Properties of (harminic) p-sums *)
Lemma Lnorm_generalised_counting (p : R) (f: (\bar R)^nat):
  (p != 0%R) -> 'N[counting]_p%:E [f] = (\sum_(k <oo) (`| f k | `^ p)) `^ p^-1.
Proof.
  by move=> p0; rewrite unlock ge0_integral_count// => k; rewrite poweR_ge0.
Qed.
(** p-sums are defined as certain integrals. This lemma says that p sums are explicitly given by (a^p + b^p) ^ (1/p) *)
Lemma p_sum_spec (p : R) (a b: {nonneg \bar R}):
  (p != 0%R) -> p_sum p%:E a b = ((a%:num `^ p) + (b%:num `^ p)) `^ (1/p).
Proof.
  intros Hp. rewrite /p_sum.
  rewrite (Lnorm_generalised_counting p (fun n => (p_sum_int_fun a b n)%:num)) //.
  rewrite (nneseries_split _ 2).
  - rewrite eseries0.
    * have ->: (0%nat + 2%nat)%nat = 2%nat by rewrite add0n.
      rewrite addr0 big_ltn // big_ltn //.
      rewrite big_geq //=. rewrite !gee0_abs //.
      by rewrite div1r addr0.
    * rewrite /p_sum_int_fun //=.
      move=> [|[|i]] _ _ //=. rewrite normr0.
      by rewrite powR0 //=. (* x `^ 1 for x < 0 is not defined *)
  - by move=> [|[|k]] _ //=; apply poweR_ge0.
Qed.

(** Case analysis lemmas *)
Lemma nng_in_itv (a: \bar R):  Itv.spec ext_num_sem (Itv.Real `[0%Z, +oo[) a -> 0 <= a.
Proof.
  rewrite /ext_num_sem /Itv.spec. move=> /andP. rewrite in_itv /=.
  by move=> [_ /andP [Ha _]]. (* This notation is a mystery, discovered by accident *)
Qed.

Lemma nng_nngy (a: {nonneg \bar R}):
  (a%:num = +oo) \/ exists2 r, (r%:E >= 0) & a%:num = r%:E.
Proof.
  destruct a as [a Ha].
  have Hnng /=: 0 <= a by apply nng_in_itv.
  move: (gee0P a)=> [/(_ Hnng) [->|Hr] _]; first by left.
  by right.
Qed.

Lemma nng_0posy (a: {nonneg \bar R}):
  (a%:num = +oo) \/ (a%:num = 0) \/ exists2 r, (r%:E > 0) & a%:num = r%:E.
Proof.
  move: (nng_nngy a)=> [->|[r Hrnng ->]]; first by left.
  rewrite le_eqVlt in Hrnng.
  move: Hrnng => /orP [/eqP <-|Hr].
  - right. by left.
  - right. right. by exists r.
Qed.

Lemma nng_0posy' (a: {nonneg \bar R}):
  (a = +oo%:nng) \/ (a = 0%:E%:nng) \/ 0 < a%:num < +oo.
Proof.
  move: (nng_0posy a) => /= [Hy|[H0|[r Hr ->]]].
  - left. by apply/val_inj.
  - right. left. by apply/val_inj.
  - right. right. apply/andP. split; first done.
    apply (ltry r).
Qed.

Lemma gt0_nng_posy {a: {nonneg \bar R}}:
  0 < a%:num -> a%:num = +oo \/ exists2 r, (r%:E > 0) & a%:num = r%:E.
Proof.
  move=> Ha. destruct (nng_0posy a) as [->|[Ha'|[r Hr Hr']]]; subst.
  - by left.
  - rewrite Ha' in Ha. by rewrite ltxx in Ha.
  - right. exists r => //.
Qed.

Lemma lty_nng_0pos {a: {nonneg \bar R}}:
  a%:num < +oo -> a%:num = 0 \/ exists2 r, (r%:E > 0) & a%:num = r%:E.
Proof.
  move=> Ha. destruct (nng_0posy a) as [Ha'|[->|[r Hr Hr']]]; subst.
  - rewrite Ha' in Ha. by rewrite ltxx in Ha.
  - by left.
  - right. exists r => //.
Qed.

Lemma nng_0pos (a: {nonneg \bar R}):
  (a%:num = 0) \/ (a%:num > 0).
Proof.
  destruct (nng_0posy a) as [->|[->|[r Hr ->]]].
  - by right.
  - by left.
  - by right.
Qed.

Lemma fin_inveM_def_by_ineq (a b: \bar R):
  0%R < a -> 0%R < b -> a < +oo -> b < +oo -> (inveM_def (R:=R) a b).
Proof.
  rewrite !lt0e. move=> /andP [Ha Ha'] /andP [Hb Hb'] Ha'' Hb''.
  apply fin_inveM_def; try done.
  - apply fin_real. apply/andP. split; last done.
    apply (@lt_le_trans _ _ 0%R%:E -oo a); last done.
    by rewrite ltNye.
  - apply fin_real. apply/andP. split; last done.
    apply (@lt_le_trans _ _ 0%R%:E -oo b); last done.
    by rewrite ltNye.
Qed.

(** Inversion is involutive *)
Lemma invnnge_involutive:
  involutive (@invnnge R).
Proof.
  rewrite /involutive /cancel /invnnge /= => a.
  apply/val_inj => /=. by rewrite inveK.
Qed.

Lemma comulnnge_invnnge (a b: {nonneg \bar R}):
  (a ⊗* b) `* = (a `* ⊗ b `*).
Proof.
  by rewrite /comulnnge invnnge_involutive.
Qed.

Lemma mul0nng (a b: {nonneg \bar R}):
  a%:num = 0 -> a ⊗ b = 0%:E%:nng.
Proof.
  move=> Ha. apply /val_inj => /=.
  by rewrite Ha mul0e.
Qed.

Lemma mulnng0 (a b: {nonneg \bar R}):
  b%:num = 0 -> a ⊗ b = 0%:E%:nng.
Proof.
  move=> Hb. apply /val_inj => /=.
  by rewrite Hb mule0.
Qed.

Lemma comulynng (a b: {nonneg \bar R}):
  a%:num = +oo -> a ⊗* b = +oo%:nng.
Proof.
  move=> Ha. apply/val_inj => /=.
  by rewrite Ha invey mul0e inve0.
Qed.

Lemma comulnngy (a b: {nonneg \bar R}):
  b%:num = +oo -> a ⊗* b = +oo%:nng.
Proof.
  move=> Hb. apply/val_inj => /=.
  by rewrite Hb invey mule0 inve0.
Qed.

Lemma fin_gt0_comulnnge_eq_mulnnge (r s: R):
  0 < r%:E -> 0 < s%:E -> (r%:E^-1 * s%:E^-1)^-1 = r%:E * s%:E.
Proof.
  move=> Hr Hs.
  rewrite -inveM; last by (apply: fin_inveM_def_by_ineq; try apply: ltry).
  by rewrite inveK.
Qed.

Lemma comulnngery_eq_mulnngery (r: R):
  0 < r%:E -> (r%:E^-1 * +oo^-1)^-1 = r%:E * +oo.
Proof.
  move=> Hr.
  by rewrite gt0_muley // invey mule0 inve0.
Qed.

(* TODO Discuss how to make proof nicer *)
Lemma comulnnger0_eq_mulnnger0 (r: R):
  0 < r%:E -> (r%:E^-1 * 0^-1)^-1 = r%:E * 0.
Proof.
  move=> Hr.
  rewrite inve0 mule0 gt0_muley; first by rewrite invey.
  rewrite inve_gt0 //. apply/eqP. move=> H. rewrite H in Hr.
  by rewrite ltxx in Hr.
Qed.

(* The following proof contains lots of repetitions. How to improve on this? *)
Lemma neq0y_comulnnge_eq_mulnnge (a b: {nonneg \bar R}):
  (0 < a%:num \/ b%:num < +oo) /\ (0 < b%:num \/ a%:num < +oo)
     -> a ⊗* b = a ⊗ b.
Proof.
  move=> [[Ha1|Hb1] [Hb2|Ha2]]; apply/val_inj => /=.
  - move: (gt0_nng_posy Ha1) (gt0_nng_posy Hb2).
    move => [->|[r Hr ->]] [->|[s Hs ->]].
    + by rewrite invey mul0e inve0 gt0_muley.
    + by rewrite muleC (muleC +oo) comulnngery_eq_mulnngery.
    + by rewrite comulnngery_eq_mulnngery.
    + by rewrite fin_gt0_comulnnge_eq_mulnnge.
  - move: (gt0_nng_posy Ha1) => [Ha|[r Hr Hr']].
    + by rewrite Ha in Ha2.
    + rewrite Hr'. move: (nng_0posy b) => [->|[->|[s Hs ->]]].
      * by rewrite comulnngery_eq_mulnngery.
      * by rewrite comulnnger0_eq_mulnnger0.
      * by rewrite fin_gt0_comulnnge_eq_mulnnge.
  - move: (gt0_nng_posy Hb2) => [Hb|[r Hr Hr']].
    + by rewrite Hb in Hb1.
    + rewrite Hr'. move: (nng_0posy a) => [->|[->|[s Hs ->]]].
      * by rewrite muleC (muleC +oo) comulnngery_eq_mulnngery.
      * by rewrite muleC (muleC 0%R) comulnnger0_eq_mulnnger0.
      * by rewrite fin_gt0_comulnnge_eq_mulnnge.
  - move: (lty_nng_0pos Ha2) (lty_nng_0pos Hb1).
    move => [->|[r Hr ->]] [->|[s Hs ->]].
    + by rewrite !inve0 mule0 invey.
    + by rewrite muleC (muleC 0%R) comulnnger0_eq_mulnnger0.
    + by rewrite comulnnger0_eq_mulnnger0.
    + by rewrite fin_gt0_comulnnge_eq_mulnnge.
Qed.

(** p-sum and harmonic p-sum are dual to each other *)
Lemma p_sum_duality (p: \bar R) (a b: {nonneg \bar R}):
  p != 0 -> a ⊕[p] b = ((a `*) ⊕[-p] (b `*)) `*.
Proof.
  move=> Hp. rewrite /p_sum_de_morgan.
  destruct (0%R < p) eqn:E.
  - have ->: 0%R < -p = false by rewrite oppe_gt0; apply lt_gtF.
    by rewrite -oppe_gt0 !oppeK E !invnnge_involutive.
  - have Hp': p < 0%R.
      by move: (lt_total Hp) => /orP [//|H]; rewrite E in H.
    have ->: 0%R < -p by rewrite oppe_gt0.
    by rewrite Hp'.
Qed.

Lemma p_sum_fin (p: R) (a b: {nonneg \bar R}):
  (0 < p)%R -> a ⊕[p%:E] b =  ((adde (a%:num `^ p) (b%:num `^ p)) `^ (1/p))%:nng.
Proof.
  move=> Hp. apply/val_inj. simpl.
  have ->: (adde (a%:num `^ p) (b%:num `^ p)) `^ (1/p) = ((a%:num `^ p) + (b%:num `^ p)) `^ (1/p) by done.
  rewrite /p_sum_de_morgan. have ->: 0%R < p%:E by done.
  apply p_sum_spec. rewrite lt0r in Hp.
  by move: Hp => /andP [// _].
Qed.

(** 1-sum is just addition *)
Lemma p_sum_1 (a b: {nonneg \bar R}):
  a ⊕[1] b = (adde a%:num b%:num)%:nng.
Proof.
  rewrite p_sum_fin //. apply/val_inj => /=.
  by rewrite invr1 mul1r !poweRe1 //.
Qed.

Lemma harmonic_p_sum_fin (p: R) (a b: {nonneg \bar R}):
  (p < 0)%R -> a ⊕[p%:E] b =  ((adde ((a `*)%:num `^ (-p)) ((b `*)%:num `^ (-p))) `^ (1/(-p)))%:nng`*.
Proof.
  move=> Hp. apply/val_inj. simpl.
  have ->: adde ((a `*)%:num `^ (-p)) ((b `*)%:num `^ (-p)) = ((a `*)%:num `^ (-p)) + ((b `*)%:num `^ (-p)) by done.
  rewrite /p_sum_de_morgan.
  have ->: 0%R < p%:E = false
    by apply /negP; move: (lt_asym p%:E 0%R) => /andP H H'; apply H.
  have ->: p%:E < 0%R by done.
  simpl. rewrite p_sum_spec // oppr_eq0.
  by apply ltr0_neq0.
Qed.

Lemma harmonic_p_sum_1 (a b: {nonneg \bar R}):
  a ⊕[-1] b = (adde a%:num^-1 b%:num^-1)^-1%:nng.
Proof.
  rewrite harmonic_p_sum_fin //=. 
  apply/val_inj => /=. rewrite opprK invr1 mulr1.
  by rewrite !poweRe1 //.
Qed.
                                                                                       
(* The following shows that we can't define harmonic
   p-sum by the formula (adde (a%:num `^ p) (b%:num `^ p)) `^ (1/p)
   as this would result in errors if a = 0 or b = 0 as evidenced
   by the subsequent lemma: The computation yields 1,
   whereas Capucci defines harmonic p-sum as 0 if either
   summand is 0, so the case analysis in neg_p_sum_notNy
   is needed *)
Lemma harmonic_p_sum_incorrect:
  (@p_sum R ((-1)%:E) 0%:E%:nng 1%:E%:nng) = 1%:E.
Proof.
  rewrite p_sum_spec /=; last done.
  by rewrite powR0 // powR1 add0r mul1r invrN1 powRN powR1 invr1.
Qed.

(** The only null set wrt the counting measure is the empty set *)
Lemma counting_zero:
  forall (S: set nat), @counting _ R S = 0 -> S = set0.
Proof.
  move=> S. rewrite /counting.
  destruct (`[< finite_set S >]) eqn:E; rewrite E //=.
  move /eqP. rewrite eqe pnatr_eq0 size_eq0.
  move=> HS. apply fset_set_set0.
  - by apply /asboolP.
  - by apply /eqP.
Qed.

(** A property holding ae wrt the counting measure holds universally *)
Lemma ae_counting (P: nat -> bool):
  (\forall x \ae (@counting _ R), P x) <-> forall x, P x.
Proof.
  split.
  - move=> [S [_ HS HSP]] x. move: HSP.
    have ->: S = set0 by apply counting_zero.
    clear HS. move=> Hemp.
    apply subsetCl in Hemp. rewrite setC0 in Hemp.
    by apply Hemp.
  - move=> HP. exists set0. split; try done.
    apply subsetCl. rewrite setC0. move=> n _. by apply HP.
Qed.

Lemma counting_nat:
  0%R < @counting _ R [set: nat].
Proof.
  rewrite /counting.
  by have /asboolF -> //: ~finite_set [set: nat] by apply infinite_nat.
Qed.

(** Technical utility lemmas *)
Lemma ess_sup_bin_fun  (f: ({nonneg \bar R})^nat):
  (forall n, (2 <= n)%N -> f n = 0%:E%:nng) -> (forall n, 0 <= (f n)%:num)
  -> ess_sup counting (fun n => (f n)%:num) = maxe (f 0%N)%:num (f 1%N)%:num.
Proof.
  move=> Hfinsupp Hnng.  apply le_anti. apply /andP. split.
  - apply /ess_supP. exists set0. split; try done.
    apply subsetCl. rewrite setC0.
    move=> [|[|k]] _ /=; rewrite num_lee_max; apply /orP.
    * by left.
    * by right.
    * left. by rewrite Hfinsupp.
  - rewrite /ess_sup /mkset. apply /ereal_infP. move=> y Hyae.
    have Hy: forall x : nat, (f x)%:num <= y by apply ae_counting.
    clear Hyae. rewrite num_gee_max. apply/andP. split.
    * by move: Hy=> /(_ 0%N) /=.
    * by move: Hy=> /(_ 1%N) /=.
Qed.

Lemma maxe_translation (a b: {nonneg \bar R}):
  (maxe a b)%:num = maxe a%:num b%:num.
Proof.
  have Heq: (a < b)%O = (a%:num < b%:num) by done.
  by destruct (a%:num < b%:num) eqn:E; rewrite !/maxe E Heq.
Qed.

Lemma mine_translation (a b: {nonneg \bar R}):
  (mine a b)%:num = mine a%:num b%:num.
Proof.
  have Heq: (a < b)%O = (a%:num < b%:num) by done.
  by destruct (a%:num < b%:num) eqn:E; rewrite !/mine E Heq.
Qed.

Lemma p_sum_Lnorm_y (a b: {nonneg \bar R}):
  p_sum +oo a b = maxe a%:num b%:num.
Proof.
  rewrite /p_sum.
  rewrite unlock /Lnorm /= counting_nat.
  (* abse is absolute value for extended real *)
  (* \o is function composition *)
  apply le_anti. apply /andP. split.
  - apply /ess_supP. exists set0. split; try done.
    apply subsetCl. rewrite setC0.
    move=> [|[|_]] _ /=; rewrite /p_sum_int_fun ?gee0_abs // num_lee_max; apply /orP.
    * by left.
    * by right.
    * left. rewrite normr0.
      suff H: 0%R <= a%:nngnum by done. (* This surely should not be so complicated... *)
      by apply ge0e.
  - rewrite /ess_sup /mkset. apply /ereal_infP. move=> y Hyae.
    have Hy: forall x : nat, (abse \o (fun n => (p_sum_int_fun a b n)%:num)) x <= y.
    by apply ae_counting.
    clear Hyae. rewrite num_gee_max. apply/andP. split.
    * move: Hy=> /(_ 0%N) /=. by rewrite gee0_abs // /p_sum_int_fun.
    * move: Hy=> /(_ 1%N) /=. by rewrite gee0_abs // /p_sum_int_fun. (*copy-paste,bad*)
Qed.

(** oo-sum is just binary maximum *)
Lemma p_sum_y (a b: {nonneg \bar R}):
  a ⊕[+oo] b = (maxe a b).
Proof.
  apply/val_inj. simpl.
  rewrite /p_sum_de_morgan maxe_translation.
  have ->: (0%R < +oo) by done. rewrite /p_sum_nng /=.
  by apply p_sum_Lnorm_y.
Qed.

(** harmonic oo-sum is just binary minimum *)
Lemma harmonic_p_sum_Ny (a b: {nonneg \bar R}):
  a ⊕[-oo] b = (mine a b).
Proof.
  apply/val_inj. simpl. rewrite /p_sum_de_morgan.
  have ->: 0%R < -oo = false by done.
  have ->: -oo < 0%R by done.
  rewrite /p_sum_nng /=.
  rewrite p_sum_Lnorm_y /= mine_translation /mine /maxe.
  destruct (a%:num < b%:num) eqn:E.
  - suff ->: a%:num^-1 < b%:num^-1 = false by rewrite inveK.
    apply lt_gtF. by rewrite lte_pV2 // /in_mem /=.
  - destruct (a%:num == b%:num) eqn:E'.
    * have ->: a%:num = b%:num by apply/eqP.
      suff ->: (b%:num^-1 < b%:num^-1 = false) by rewrite inveK.
      apply/negP. apply/negP. rewrite -leNgt.
      by apply lexx.
    * rewrite lte_pV2 // /in_mem //=.
      have Habneq: a%:num != b%:num by move: E'=> /eqP H; apply/eqP.
      move: (lt_total Habneq) => /orP [H|->]; first by rewrite E in H.
      by rewrite inveK.
Qed.

Lemma pos_implies_non0 (r: R):
  0%R < r%:E -> r%:E != 0.
Proof.
  rewrite lt0e.  by move=> /andP [Hr _] //.
Qed.

Lemma neg_implies_non0 (r: R):
  r%:E < 0%R -> r%:E != 0.
Proof.
  move=> Hr.
  have /pos_implies_non0: 0 < (-r)%:E by rewrite EFinN oppe_gt0.
  by rewrite EFinN oppe_eq0.
Qed.

Lemma pos_implies_non0e (a: \bar R):
  0 < a -> a != 0.
Proof.
  rewrite lt0e. by move=> /andP [// _].
Qed.

Lemma pos_implies_fin_num (r: R):
  0%R < r%:E -> r%:E^-1 \is a fin_num.
Proof.
   move=> Hr. have H1: r%:E != 0%R. by apply pos_implies_non0. 
   by apply (fin_numV H1).
Qed.

Lemma pos_implies_nng (r: R):
  0%R < r%:E -> (0 <= r)%R.
Proof.
  rewrite lt0e. by move=> /andP [_ //].
Qed.

(* TODO Generalise for arbitrary odered types *)
Lemma lt_neq (p q: \bar R):
  (p < q)%O -> p != q.
Proof.
  move=> /lt_eqF /eqP H; by apply/eqP.
Qed.

Lemma lt_neq_sym (p q: \bar R):
  (p < q)%O -> q != p.
Proof.
  move=> H. apply/eqP. symmetry. apply/eqP.
  move: H. by apply lt_neq.
Qed.
       
Lemma lee0P (p: \bar R) : p <= 0 <-> p = -oo \/ exists2 r, (r <= 0)%R & p = r%:E.
Proof.
  split.
  - move=> Hp. rewrite -(oppeK p) oppe_le0 in Hp.
    move: (gee0P (-p)) => [/(_ Hp) [-Hp'|[r Hr Hr']] _].
    * left. by have -> /=: p = -(+oo) by rewrite -(oppeK p); f_equal.
    * right. exists (-r)%R; first by rewrite oppr_lte0.
      rewrite -(oppeK p). by rewrite Hr'.
  - by move=> [->|[r Hr ->]].
Qed.

Lemma posP (p: \bar R): 0 < p < +oo -> exists2 r, (0 < r)%R & p = r%:E.
Proof.
  move=> /andP [Hp0 Hpy]. move: (gee0P p) => [/(_ (ltW Hp0)) [Hpy'|[r Hr Hr']] _].
  - move: Hpy' Hpy. by rewrite ltey => ->.
  - exists r => //. by rewrite -lte_fin -Hr'.
Qed.

Lemma adde_p_sum_bounds (a b: \bar R) (p: R):
  0 < a < +oo -> 0 < b < +oo -> 0 < adde (a `^ p) (b `^ p) < +oo.
Proof.
  move=> /andP [Ha1 Ha2] /andP [Hb1 Hb2]. apply/andP. split.
  - by apply (@adde_gt0 _ (a `^ p) (b `^ p)); apply poweR_gt0.
  - by apply (@lte_add_pinfty _ (a `^ p) (b `^ p)); apply poweR_lty.
Qed.

Lemma p_sum_bounds (a b: \bar R) (p: R):
  0 < a < +oo -> 0 < b < +oo -> 0 < adde (a `^ p) (b `^ p) `^ (1 / p) < +oo.
Proof.
  move=> /andP [Ha1 Ha2] /andP [Hb1 Hb2]. apply/andP. split.
  - by apply poweR_gt0, (@adde_gt0 _ (a `^ p) (b `^ p)); apply poweR_gt0.
  - by apply poweR_lty, (@lte_add_pinfty _ (a `^ p) (b `^ p)); apply poweR_lty.
Qed.

Lemma nonneg_not_Ny (a: {nonneg \bar R}):
  a%:num != -oo.
Proof.
  by rewrite -ltNye (@lt_le_trans _ _ 0).
Qed.

Lemma nonneg_not_0 (p q: R):
 (q <= p)%R -> (0 < q)%R -> p != 0%R.
Proof.
  move=> Hpq Hq.
  suff: (0 < p)%R. by rewrite lt0r; move=> /andP [// _].
  by eapply lt_le_trans; first exact Hq.
Qed.

Lemma invp_add_le1 (a b: R):
  (0 < a)%R -> (0 < b)%R -> ((a + b)^-1 * a <= 1)%R.
Proof.
  move=> Ha Hb.
  have: (0 < a + b)%R by apply addr_gt0.
  rewrite lt0r=> /andP [Hab _].
  rewrite -(@mulVf _ (a + b)%R) //. apply ltW in Ha, Hb.
  apply ler_pM => //; last by rewrite lerDl.
  by rewrite invr_ge0 addr_ge0.
Qed.

(** Power function for real exponent greater equal 1 is subadditive
    Should be added to exp.v *)
Lemma ge1_poweR_subadditive (a b: {nonneg \bar R}) (p: R):
  (1 <= p)%R -> a%:num `^ p + b%:num `^ p <= (a%:num + b%:num) `^ p.
Proof.
  intros Hp.
  move: (nng_0posy a) => [->|[->|[r Hr Hr']]].
  - rewrite addye; last by apply nonneg_not_Ny.
    rewrite poweRyr; last by apply (nonneg_not_0 _ 1 Hp).
    by rewrite addye; last by apply nonneg_not_Ny.
  - rewrite poweR0r; last by apply (nonneg_not_0 _ 1 Hp).
    by rewrite !add0e.
  - move: (nng_0posy b) => [->|[->|[s Hs Hs']]].
    * rewrite addey; last by rewrite Hr' -ltNye ltNyr.
      rewrite poweRyr; last by apply (nonneg_not_0 _ 1 Hp).
      by rewrite addey; last by rewrite Hr' -ltNye ltNyr.
    * rewrite adde0 poweR0r; last by apply (nonneg_not_0 _ 1 Hp).
      by rewrite adde0.
    * have Hrsnon0: (a%:num + b%:num) `^ p != 0.
        by rewrite Hr' Hs'; apply pos_implies_non0e, poweR_gt0, adde_gt0.
      have Hrsinvfin: ((adde a%:num b%:num) `^ p)^-1 \is a fin_num.
        by apply (@fin_numV _ ((adde a%:num b%:num) `^ p));
          first done; apply nonneg_not_Ny.
      have  Hrsinvgt0: 0 < ((adde a%:num b%:num) `^ p)^-1.
        by rewrite inve_gt0 // Hr' Hs';
          first by apply poweR_gt0, (@adde_gt0 _ r%:E s%:E).
      rewrite -(@lee_pmul2l _ (((a%:num + b%:num) `^ p)^-1)) //.
      rewrite mulVe //; last by apply fin_num_poweR; rewrite fin_numD Hr' Hs'.
      rewrite muleDr //; last by rewrite Hr'; apply fin_num_adde_defr.
      rewrite Hs' Hr' -(@fineK _ (r%:E + s%:E)) //=.
      rewrite inver /=. rewrite Hs' Hr' /= in Hrsnon0.
      have Hrs': ((r + s) `^ p)%R == 0%R = false.
        by apply/eqP; move=> H; move: H Hrsnon0 => -> /eqP H; apply H.
      rewrite Hrs' -EFinM -EFinD -powRN -mulN1r powRrM powRN.
      rewrite !powRr1; last by apply ltW, addr_gt0.
      rewrite Hs' Hr' inver Hrs' in Hrsinvgt0.
      have Hrsinvgt0': (0%R < ((r + s)^-1))%R.
        by rewrite invr_gt0 addr_gt0 //; apply ltW. 
      rewrite -!powRM //; try by apply ltW.
      have ->: 1%R = ((r + s)^-1 * r + (r + s)^-1 * s)%R.
      rewrite -mulrDr mulVf //; first by apply/eqP => Hfls; move: Hrsinvgt0';
        rewrite Hfls invr0 ltxx. 
      apply lee_tofin, lerD; apply ge1r_powR => //;
        apply/andP; split; try by apply mulr_gt0.
      + by rewrite invp_add_le1.
      + by rewrite addrC invp_add_le1.
Qed.

(** p-sum and harmonic p-sum are commutative *)
Lemma p_sumC (p: \bar R):
  (0 < p) -> commutative (fun a b => a ⊕[p] b).
Proof.
  move=> Hp a b. apply/val_inj. simpl.
  move: (gee0P p) => [/(_ (ltW Hp)) [->|[r Hr Hr']] _].
  - by rewrite !p_sum_y comparable_maxC.
  - clear Hr. have Hr: (0 < r)%R by rewrite -lte_fin -Hr'.
    rewrite Hr' !(p_sum_fin _ _ _ Hr). simpl.
    have ->: (adde (a%:num `^ r) (b%:num `^ r)) `^ (1/r) = ((a%:num `^ r) + (b%:num `^ r)) `^ (1/r) by done.
    by rewrite addeC. (* addeC won't work if both sides of the equation mention adde *)
Qed.

Lemma harmonic_p_sumC (p: \bar R):
  (p < 0) -> commutative (fun a b => a ⊕[p] b).
Proof.
  move=> Hp a b.
  have Hp': p != 0%R.
    by apply lt_eqF in Hp; apply/eqP; move: Hp => /eqP.
  rewrite p_sum_duality // (p_sum_duality _ b a) //.
  by rewrite p_sumC //= oppe_gt0.  
Qed.

Lemma p_sumA_explicit (a b c: {nonneg \bar R}) (r: R) (Hr: r != 0%R): 
  adde (a%:nngnum `^ r) ((adde (b%:nngnum `^ r) (c%:nngnum `^ r) `^ (1 / r)) `^ r) `^ (1 / r) =
    adde ((adde (a%:nngnum `^ r) (b%:nngnum `^ r) `^ (1 / r)) `^ r) (c%:nngnum `^ r) `^ (1 / r).
Proof.
  rewrite  -!poweRrM -!mulrA !mulVf //. 
  rewrite !mul1r poweRe1 // poweRe1 //.
  have ->: (adde (a%:num `^ r) (adde (b%:num `^ r) (c%:num `^ r)) `^ r^-1) = (a%:num `^ r + (b%:num `^ r + c%:num `^ r)) `^ r^-1 by done.
  by rewrite addeA.
Qed.

(** p-sum and harmonic p-sum are associative *)
Lemma p_sumA (p: \bar R):
  (0 < p) -> associative (fun a b => a ⊕[p] b).
Proof.
  move=> Hp a b c. apply/val_inj. simpl.
  move: (gee0P p) => [/(_ (ltW Hp)) [->|[r Hr Hr']] _];
    first by rewrite !p_sum_y comparable_maxA.
  clear Hr. have Hr: (0 < r)%R by rewrite -lte_fin -Hr'.
  rewrite Hr' !(p_sum_fin _ _ _ Hr). apply p_sumA_explicit.
  move: Hr. rewrite lt0r. by move=> /andP [// _].
Qed.

Lemma harmonic_p_sumA (p: \bar R):
  (p < 0) -> associative (fun a b => a ⊕[p] b).
Proof.
  move=> Hp a b c.
  have Hp': p != 0%R.
    by apply lt_eqF in Hp; apply/eqP; move: Hp => /eqP.
  rewrite p_sum_duality // (p_sum_duality _ b c) // invnnge_involutive.
  rewrite (p_sum_duality _ a b) //  (p_sum_duality _ _ c) //.
  by rewrite invnnge_involutive p_sumA // oppe_gt0.
Qed.

Lemma p_sum_0nng (a b: {nonneg \bar R}) (p: \bar R):
  0 < p -> a%:num = 0 -> a ⊕[p] b = b.
Proof.
  move=> Hp Ha. apply/val_inj => /=.
  move: (gee0P p) => [/(_ (ltW Hp)) [->|[r _ Hr]] _].
  - rewrite p_sum_y maxe_translation /maxe Ha.
    destruct (0 < b%:num) eqn:E => //.
    have: 0 <= b%:num by done.
    rewrite le_eqVlt => /orP [/eqP //|Hb]. by rewrite Hb in E.  
  - subst. rewrite p_sum_fin //= Ha poweR0r;
      last by (apply/eqP => Hr; rewrite Hr ltxx in Hp).
    have ->: adde 0%R (b%:num `^ r)  = 0 + b%:num `^ r by done.
    rewrite add0e -poweRrM mul1r divrr; first by rewrite poweRe1.
    by apply unitf_gt0.
Qed.

Lemma p_sum_nng0 (a b: {nonneg \bar R}) (p: \bar R):
  0 < p -> b%:num = 0 -> a ⊕[p] b = a.
Proof.
  move=> Hp. rewrite p_sumC //. by apply p_sum_0nng.
Qed.

Lemma harmonic_p_sum_ynng (a b: {nonneg \bar R}) (p: \bar R):
  p < 0 -> a%:num = +oo -> a ⊕[p] b = b.
Proof.
  move=> Hp Ha. rewrite p_sum_duality; last by apply lt_neq.
  have Hainv: (a `*)%:num = 0 by rewrite -invey /=; f_equal.
  rewrite p_sum_0nng //; last by rewrite oppe_gt0.
  by rewrite invnnge_involutive.
Qed.

Lemma harmonic_p_sum_nngy (a b: {nonneg \bar R}) (p: \bar R):
  p < 0 -> b%:num = +oo -> a ⊕[p] b = a.
Proof.
  move=> Hp. rewrite harmonic_p_sumC //. by apply harmonic_p_sum_ynng.
Qed.

Lemma p_sum_ynng (a b: {nonneg \bar R}) (p: \bar R):
  0 < p -> a%:num = +oo -> a ⊕[p] b = +oo%:nng.
Proof.
  move=> Hp Ha. apply/val_inj => /=.
  move: (gee0P p) => [/(_ (ltW Hp)) [->|[r _ Hr]] _].
  - by rewrite p_sumC // p_sum_y maxe_translation Ha real_maxey.
  - subst. rewrite p_sum_fin //= Ha.
    have ->: adde (+oo `^ r) (b%:num `^ r) = +oo `^ r + b%:num `^ r by done.
    rewrite poweRyr; last by (apply/eqP => H; rewrite H ltxx in Hp).
    rewrite addye; last by (rewrite -ltNye; apply: (@lt_le_trans _ _ 0)).
    rewrite poweRyr //. rewrite div1r.
    suff: (r^-1%R == 0%R = false) by move => /eqP Hr; apply/eqP.
    by rewrite gt_eqF // invr_gt0.
Qed.

Lemma p_sum_nngy  (a b: {nonneg \bar R}) (p: \bar R):
  0 < p -> b%:num = +oo -> a ⊕[p] b = +oo%:nng.
Proof.
  move=> Hp Hb. by rewrite p_sumC // p_sum_ynng.
Qed.

Lemma harmonic_p_sum_0nng (a b: {nonneg \bar R}) (p: \bar R):
  p < 0 -> a%:num = 0 -> a ⊕[p] b = 0%:E%:nng.
Proof.
  move=> Hp Ha. rewrite p_sum_duality; last by apply lt_neq.
  have Hainv: (a `*)%:num = +oo by rewrite -inve0 /=; f_equal.
  rewrite p_sum_ynng //; last by rewrite oppe_gt0.
  apply/val_inj => /=. by rewrite invey.
Qed.

Lemma harmonic_p_sum_nng0 (a b: {nonneg \bar R}) (p: \bar R):
  p < 0 -> b%:num = 0 -> a ⊕[p] b = 0%:E%:nng.
Proof.           
  move=> Hp Hb. rewrite harmonic_p_sumC //.
  by rewrite harmonic_p_sum_0nng.
Qed.


(* Automation to solve x <= +oo would be nice *)
(** ** Interplay of the connectives *)
Lemma mul_comul_ineq (a b : {nonneg \bar R}): (a ⊗ b)%:num <= (a ⊗* b)%:num.
Proof.
  move: (nng_0posy a) (nng_0posy b) => /= [->|[->|[r Hr ->]]] [->|[->|[s Hs ->]]].
  - by rewrite invey mul0e inve0 mulyy.
  - by rewrite invey mul0e inve0 mule0.
  - by rewrite invey gt0_mulye // mul0e inve0.
  - by rewrite invey inve0 mul0e mule0 inve0.
  - by rewrite inve0 mul0e.
  - rewrite mul0e inve0 gt0_mulye // inve_gt0 //.
    by apply pos_implies_non0.
  - by rewrite gt0_muley // invey mule0 inve0.
  - rewrite mule0 inve0 gt0_muley // inve_gt0 //.
    by apply pos_implies_non0.
  - rewrite inveM; first by rewrite !inveK. 
    apply fin_inveM_def; try by rewrite inve_eq0.
    * by apply pos_implies_fin_num.
    * by apply pos_implies_fin_num.
Qed.

Lemma mule_lty_gt0 (a b : \bar R):
  0 < a -> 0 < b -> a * b < +oo -> (a < +oo) && (b < +oo).
Proof.
  move=> Ha Hb Hab. destruct a as [s| | ]; last done.
  - destruct b as [t| | ]; last done.
    + apply/andP. split; apply (@ltry R).
    + move: (gt0_mulye Ha) Hab. rewrite muleC.
      move=> ->. by rewrite ltxx.
  - move: (gt0_mulye Hb) Hab=> ->. by rewrite ltxx.
Qed.

Lemma nngNy_fin_num (a: \bar R):
  0 <= a -> a < +oo -> a \is a fin_num.
Proof.
  move=> Ha1 Ha2.
  apply fin_real. apply/andP. split; last done.
  by eapply lt_le_trans; last exact Ha1.
Qed.
 
Lemma mul_comul_equiv (a b c : {nonneg \bar R}):
  ((a ⊗ b)%:num <= c`*%:num) <-> (a%:num <= (b ⊗ c)`*%:num). (* Should we use = instead? *)
Proof.
  split.
  - move: (nng_0pos a) => /= [->|Ha] Hineq; first by rewrite inve_ge0.
    move: (nng_0pos b) Hineq => /= [->|Hb] Hineq.
    * rewrite mul0e inve0. by apply (leey (a%:nngnum)).
    * have Hc: c%:num < +oo.
      suff: c%:num != +oo by rewrite ltey.
      apply/eqP. move=> Hc. rewrite Hc invey in Hineq.
      have: 0%R < a%:num * b%:num by apply mule_gt0.
      by move: (le_gtF Hineq) => ->.
      move: (nng_0pos c) Hineq => [->|Hc'] Hineq; first by rewrite mule0 inve0 leey.
      have Hineq': a%:num * b%:num < +oo.
      apply (le_lt_trans Hineq).
      move: Hc'. rewrite ltey lt0e. move=> /andP [/eqP Hc' _].
      apply/eqP. move=> Hc''. apply Hc'. rewrite -invey.
      have <-: c%:num^-1^-1 = +oo^-1 by apply f_equal.
      by rewrite inveK.
      move: (mule_lty_gt0 a%:num b%:num Ha Hb Hineq') => /andP [Ha' Hb'].
      rewrite inveM.
      + rewrite -(mule1 a%:nngnum) muleC.
        have Hb'': b%:num != 0%R by move: Hb; rewrite lt0e; move=> /andP [// _].
        rewrite -(@divee _ b%:num); last done; last by apply nngNy_fin_num.
        rewrite (muleC b%:nngnum b%:nngnum^-1). rewrite muleC in Hineq.
        move: (@lee_pmul _ (b%:num^-1) (b%:num^-1) (b%:num * a%:num) (c%:num^-1)).
        rewrite inve_ge0 muleA.
        have Hineq'': 0%R <= b%:nngnum * a%:nngnum.
          by apply ltW in Ha, Hb; apply mule_ge0. 
        move=> /(_ (ltW Hb) Hineq'') Hdone. by apply Hdone.
      + move: Hc' Hb. rewrite !lt0e. move=> /andP [Hc' Hc''] /andP [Hb Hb''].
        by apply fin_inveM_def; try done; apply nngNy_fin_num. 
  - move: (nng_0pos a) => /= [->|Ha] Hineq; first by rewrite mul0e inve_ge0.
    move: (nng_0pos b) => /= [->|Hb]; first by rewrite mule0 inve_ge0.
    have Hc: c%:num < +oo.
      suff: c%:num != +oo by rewrite ltey.
      apply/eqP. move=> Hc. rewrite Hc in Hineq.
      rewrite gt0_muley // invey in Hineq. by move: (lt_geF Ha) Hineq => ->.
    move: (nng_0pos c) => [->|Hc'];
      first by (rewrite inve0; apply (leey (a%:nngnum * b%:nngnum))).
    have Hb': b%:num < +oo.
      rewrite ltey. apply/eqP. move=> Hb'.
      by rewrite Hb' (gt0_mulye Hc') invey (lt_geF Ha) in Hineq.
    rewrite inveM in Hineq; last by apply fin_inveM_def_by_ineq.
    rewrite muleC.
    move: (@lee_pmul _ (b%:num) (b%:num) (a%:num) (b%:num^-1 / c%:num)).
    move=> /(_  (ltW Hb) (ltW Ha) _ Hineq). rewrite muleA.
    have Hb'': (b%:num != 0%R).
      by move: Hb; rewrite lt0e; move=> /andP [// _].
    rewrite (@divee _ b%:num) //; last by (apply nngNy_fin_num; apply ltW in Hb).
    rewrite mul1e. move=> Hineq'. by apply Hineq'.
Qed.

Lemma div_adjoint (a b c: {nonneg \bar R}):
  a%:num <= (b -o c)%:num <-> (a ⊗ b)%:num <= c%:num.
Proof.
  rewrite /divnnge /=. split; rewrite inveK; move=> Hineq.
  - move: (mul_comul_equiv a b (c `*)) => [_ H]. rewrite -(inveK c%:num).
    by apply H.
  - move: (mul_comul_equiv a b (c `*)) => [H _]. apply H.
    by rewrite /= inveK.
Qed.

Local Ltac gt0_pred_solve := rewrite inE; apply/andP;  split; first rewrite unitf_gt0 //; by apply powR_gt0.

(* TODO: This lemma should be added to exp.v *)
Lemma lt0_ler_powR (r: R) : (r <= 0)%R ->
  {in Num.pos &, {homo ((@powR R) ^~ r) : x y / (x <= y)%R >-> (y <= x)%R}}.
Proof.
  move=> r0 x y. rewrite !posrE. move=> Hx Hy Hxy.
  destruct (r == 0%R) eqn:E.
  + have ->: r = 0%R by apply/eqP. by rewrite !powRr0.
  + have E': r != 0%R by apply /eqP; move: E => /eqP.
    have ->: r = (--r)%R by rewrite opprK.
    have Hoppr: (0 <= -r)%R by rewrite oppr_ge0.
    rewrite (powRN y) (powRN x). rewrite ler_pV2 //; try by gt0_pred_solve.
    rewrite ge0_ler_powR //; by rewrite nnegrE; apply pos_implies_nng.
Qed.

Lemma poweR_gt0_lty (a: \bar R) (p: R):
  0 < a < +oo -> 0 < a `^ p < +oo.
Proof.
  move=> /andP [Ha0 Hay]. apply/andP. split; first by apply poweR_gt0.
  by apply poweR_lty.
Qed.

Lemma lt0r_ler_poweR (r: R) (a b: \bar R): (r <= 0)%R ->
  0 < a < +oo -> 0 < b < +oo -> (a <= b) -> (b `^ r <= a `^ r).
Proof.
  move=> Hr Ha Hb Hba.
  move: (posP _ Ha) (posP _ Hb) => [s Hs Hs'] [t Ht Ht'].
  rewrite Hs' Ht' !poweR_EFin lee_fin lt0_ler_powR //.
  by rewrite -lee_fin -Ht' -Hs'.
Qed.
(** ** Inequalities Concerning p-sums *)
Local Ltac itv_poweR_solve := rewrite in_itv /=; apply/andP; split; first done; rewrite leey.

Lemma p_sum_left_semiadditive (a b: {nonneg \bar R}) (p: \bar R):
  (0 < p) -> a%:num <= (a ⊕[p] b)%:num.
Proof.
  move=> Hp. move: (gee0P p) => [/(_ (ltW Hp)) [->|[r _ Hr]] _].
  - rewrite p_sum_y maxe_translation num_lee_max.
    apply/orP. by left.
  - rewrite Hr. rewrite Hr in Hp.
    rewrite p_sum_fin //=.
    rewrite <- (@poweRe1 _ a%:num) at 1; try done.
    have ->: a%:nngnum `^ 1 = a%:nngnum `^ (r / r).
      by rewrite -(@divff _ r) //; apply pos_implies_non0.
    rewrite (@poweRrM _ _ r r^-1) div1r.
    apply gt0_ler_poweR.
    * rewrite invr_ge0. by apply ltW in Hp.
    * by itv_poweR_solve.
    * by itv_poweR_solve.
    * rewrite <- adde0 at 1. by rewrite leeD.
Qed.

Lemma p_sum_right_semiadditive (a b: {nonneg \bar R}) (p: \bar R):
  (0 < p) -> b%:num <= (a ⊕[p] b)%:num.
Proof.
  move=> Hp. rewrite p_sumC //.
  by apply p_sum_left_semiadditive.
Qed.

Lemma harmonic_p_sum_left_semiadditive (a b: {nonneg \bar R}) (p: \bar R):
  (p < 0) -> (a ⊕[p] b)%:num <= a%:num.
Proof.
  move=> Hp.
  have Hp': p != 0%R.
    by apply lt_eqF in Hp; apply/eqP; move: Hp => /eqP.
  rewrite p_sum_duality //= -lee_pV2; try rewrite /in_mem //=.
  rewrite inveK.
  have ->: a%:num^-1 = (a `*)%:num by done.
  apply p_sum_left_semiadditive. by rewrite oppe_gt0.
Qed.

Lemma harmonic_p_sum_right_semiadditive (a b: {nonneg \bar R}) (p: \bar R):
  (p < 0) -> (a ⊕[p] b)%:num <= b%:num.
Proof.
  move=> Hp. rewrite harmonic_p_sumC //.
  by apply harmonic_p_sum_left_semiadditive.
Qed.

Lemma lty_p_sum_lty (a b: {nonneg \bar R}) (p: \bar R):
  0 < p -> a%:num < +oo -> b%:num < +oo -> (a ⊕[p] b)%:num < +oo.
Proof.
  move=> Hp Ha Hb.
  move: (gee0P p) => [/(_ (ltW Hp)) [->|[r _ Hr]] _].
  - rewrite p_sum_y maxe_translation num_gte_max.
    apply/andP. by split.
  - subst. rewrite p_sum_fin //=. apply poweR_lty.
    by apply: lte_add_pinfty; apply poweR_lty.
Qed.

Local Ltac itv_solve := rewrite in_itv /=; apply/andP; split; first done; apply (@leey R).

Lemma p_sum_left_monotone (a a' b: {nonneg \bar R}) (p: \bar R):
  0 < p -> a%:num <= a'%:num -> (a ⊕[p] b)%:num <= (a' ⊕[p] b)%:num.
Proof.
  move=> Hp Haa'.
  move: (gee0P p) => [/(_ (ltW Hp)) [->|[r Hr Hr']] _].
  - rewrite !p_sum_y !maxe_translation num_gee_max. apply/andP.
    split; rewrite num_lee_max; apply/orP; last by right.
    by left.
  - rewrite Hr' in Hp. rewrite Hr' !p_sum_fin //=. apply gt0_ler_poweR; try by itv_solve.
    + by rewrite div1r invr_ge0.
    + apply (leeD2r (b%:nngnum `^ r)).
      by apply gt0_ler_poweR; try by itv_solve. 
Qed.

Lemma p_sum_right_monotone (a b b': {nonneg \bar R}) (p: \bar R):
  0 < p -> b%:num <= b'%:num -> (a ⊕[p] b)%:num <= (a ⊕[p] b')%:num.
Proof.
  move=> Hp. rewrite (p_sumC _ _ a b) // (p_sumC _ _ a b') //.
  by apply p_sum_left_monotone.
Qed.

Lemma p_sum_both_monotone (a a' b b': {nonneg \bar R}) (p: \bar R):
  0 < p -> (a <= a')%O -> (b <= b')%O
    -> ((a ⊕[p] b) <= (a' ⊕[p] b'))%O.
Proof.
  move=> Hp Ha Hb.
  eapply le_trans; first by apply (p_sum_left_monotone a a').
  by apply p_sum_right_monotone.
Qed.
  
Lemma harmonic_p_sum_left_monotone (a a' b: {nonneg \bar R}) (p: \bar R):
  p < 0 -> a%:num <= a'%:num -> (a ⊕[p] b)%:num <= (a' ⊕[p] b)%:num.
Proof.
  move=> Hp Haa'.
  have Hp': p != 0%R.
    by apply lt_eqF in Hp; apply/eqP; move: Hp => /eqP.
  rewrite p_sum_duality // (p_sum_duality _ a' _) //=.
  rewrite lee_pV2; try rewrite /in_mem //=.
  apply p_sum_left_monotone=> /=; first by rewrite oppe_gt0.
  by rewrite lee_pV2 //; rewrite /in_mem //=.
Qed.

Lemma harmonic_p_sum_right_monotone (a b b': {nonneg \bar R}) (p: \bar R):
  p < 0 -> b%:num <= b'%:num -> (a ⊕[p] b)%:num <= (a ⊕[p] b')%:num.
Proof.
  move=> Hp. rewrite (harmonic_p_sumC _ _ a b) //.
  rewrite (harmonic_p_sumC _ _ a b') //.
  by apply harmonic_p_sum_left_monotone.
Qed.

Lemma harmonic_p_sum_both_monotone (a a' b b': {nonneg \bar R}) (p: \bar R):
  p < 0 -> (a <= a')%O -> (b <= b')%O
    -> ((a ⊕[p] b) <= (a' ⊕[p] b'))%O.
Proof.
  move=> Hp Ha Hb.
  eapply le_trans; first by apply (harmonic_p_sum_left_monotone a a').
  by apply harmonic_p_sum_right_monotone.
Qed.

Lemma p_sum_mulDr (a b c: {nonneg \bar R}) (p: \bar R):
  0 < p -> c ⊗ (a ⊕[p] b) = (c ⊗ a) ⊕[p] (c ⊗ b).
Proof.
  move=> Hp. apply/val_inj => /=.
  move: (gee0P p) => [/(_ (ltW Hp)) [->|[r Hr Hr']] _].
  - rewrite !p_sum_y !maxe_translation /=.
    destruct (nng_nngy c) as [Hc|[x Hx Hx']].
    + rewrite Hc /maxe. move: (nng_0pos a) (nng_0pos b) => [->|Ha] [->|Hb].
      * rewrite !mule0.
        by destruct ((0%R: \bar R) < 0%R) eqn:E; rewrite E mule0.
      * rewrite Hb mule0 gt0_mulye //.
        by have ->: 0%R < +oo by done.
      * have ->: a%:num < 0%R = false by apply lt_gtF.
        by rewrite mule0 gt0_mulye.
      * rewrite (@gt0_mulye _ a%:num) // (@gt0_mulye _ b%:num) //.
        by destruct (a%:num < b%:num) eqn:E; rewrite E;
          destruct ((+oo: \bar R) < +oo) eqn:E'; rewrite E' gt0_mulye.
    + rewrite Hx'. by apply: maxe_pMr.    
  - subst. rewrite !p_sum_fin //=.
    have ->: c%:num * adde (a%:num `^ r) (b%:num `^ r) `^ (1/r)
         = c%:num `^ (r * r^-1) * (adde (a%:num `^ r) (b%:num `^ r)) `^ (1/r).
      by rewrite divrr; [rewrite poweRe1 | apply unitf_gt0].
    rewrite poweRrM.
    have ->: (c%:num `^ r) `^ r^-1 = (c%:num `^ r) `^ (1/r) by rewrite div1r.
    by rewrite -poweRM // ge0_muleDr // !poweRM.
Qed.

Lemma harmonic_p_sum_comulDr (a b c: {nonneg \bar R}) (p: \bar R):
  p < 0 -> c ⊗* (a ⊕[p] b) = (c ⊗* a) ⊕[p] (c ⊗* b).
Proof.
  move=> Hp.
  have Hp': p != 0%R.
    by apply lt_eqF in Hp; apply/eqP; move: Hp => /eqP.
  rewrite p_sum_duality // (p_sum_duality _ (c ⊗* a) _) //.
  rewrite !comulnnge_invnnge -p_sum_mulDr;
    last by rewrite oppe_gt0.
  by rewrite /comulnnge  invnnge_involutive.
Qed.

Lemma p_sum_comulDr (a b c: {nonneg \bar R}) (p: \bar R):
  0 < p -> c ⊗* (a ⊕[p] b) = (c ⊗* a) ⊕[p] (c ⊗* b).
Proof.
  move=> Hp. apply/val_inj => /=.
  move: (nng_0posy c) => [Hc|[Hc|[r Hr Hr']]].
  - rewrite !comulynng // (p_sum_ynng +oo%:nng) //=.
    by rewrite Hc invey mul0e inve0.
  - rewrite Hc inve0.
    move: (nng_0posy a) => [Ha|[Ha|[s Hs Hs']]].
    + rewrite comulnngy // (p_sum_ynng +oo%:nng) //.
      by rewrite (p_sum_ynng a) //= invey mule0 inve0.
    + rewrite (p_sum_0nng a) //. Check neq0y_comulnnge_eq_mulnnge.
      move: (nng_0posy b) => [Hb|[Hb|[t Ht Ht']]].
      * rewrite (comulnngy _ b) // p_sum_nngy //= Hb.
        by rewrite invey mule0 inve0.
      * rewrite (neq0y_comulnnge_eq_mulnnge c a);
          last by split; [right; rewrite Ha | right; rewrite Hc].
        rewrite (neq0y_comulnnge_eq_mulnnge c b);
          last by split; [right; rewrite Hb | right; rewrite Hc].
        rewrite -p_sum_mulDr // (p_sum_0nng a) //= Hc mul0e.
        by rewrite Hb inve0 gt0_muley.
      * rewrite (neq0y_comulnnge_eq_mulnnge c a);
          last by split; [right; rewrite Ha | right; rewrite Hc].
        rewrite (neq0y_comulnnge_eq_mulnnge c b);
          last by split; [right; rewrite Ht' ltry | right; rewrite Hc].
        rewrite -p_sum_mulDr // (p_sum_0nng a) //= Hc mul0e.
        rewrite gt0_mulye // inve_gt0 ?Ht' //.
        by apply lt_neq_sym.
    + move: (nng_0posy b) => [Hb|[Hb|[t Ht Ht']]].
      * rewrite (p_sum_nngy a) //= invey mule0 inve0.
        by rewrite (comulnngy _ b) // (p_sum_nngy _ +oo%:nng).
      * rewrite (p_sum_nng0 a) //.
        rewrite (neq0y_comulnnge_eq_mulnnge c a);
          last by split; [right; rewrite Hs' ltry | right; rewrite Hc].
        rewrite (neq0y_comulnnge_eq_mulnnge c b);
          last by split; [right; rewrite Hb | right; rewrite Hc].
        rewrite -p_sum_mulDr // mul0nng //= gt0_mulye ?invey //.
        rewrite inve_gt0 Hs' //. by apply lt_neq_sym.
      * rewrite (neq0y_comulnnge_eq_mulnnge c a);
          last by split; [right; rewrite Hs' ltry | right; rewrite Hc].
        rewrite (neq0y_comulnnge_eq_mulnnge c b);
          last by split; [right; rewrite Ht' ltey | right; rewrite Hc].
        rewrite -p_sum_mulDr // mul0nng //= gt0_mulye ?invey //.
        have Hab: 0%R < (a ⊕ [p] b)%:num.
          eapply lt_le_trans; last by apply: p_sum_left_semiadditive. by rewrite Hs'.
        rewrite inve_gt0 //; first by apply lt_neq_sym.
        rewrite -ltey. by apply lty_p_sum_lty; rewrite ?Hs' ?Ht' ?ltry.
  - move: (nng_0posy a) => [Ha|[Ha|[s Hs Hs']]].
    + rewrite p_sum_ynng //= invey mule0 inve0.
      by rewrite (comulnngy c a) // (p_sum_ynng +oo%:nng).
    + move: (nng_0posy b) => [Hb|[Hb|[t Ht Ht']]].
      * rewrite p_sum_nngy //= invey mule0 inve0.
        by rewrite (comulnngy c b) // (p_sum_nngy _ +oo%:nng).
      * rewrite (p_sum_nng0 a) //.
        rewrite (neq0y_comulnnge_eq_mulnnge c a);
          last by split; [right; rewrite Ha | right; rewrite Hr' ltry].
        rewrite (neq0y_comulnnge_eq_mulnnge c b);
          last by split; [right; rewrite Hb | right; rewrite Hr' ltry].
        rewrite -p_sum_mulDr // p_sum_0nng // mulnng0 //=.
        rewrite Ha inve0 gt0_muley ?invey // Hr'.
        rewrite inve_gt0 //. by apply lt_neq_sym.
      * rewrite p_sum_0nng //.
        rewrite (neq0y_comulnnge_eq_mulnnge c a);
          last by split; [right; rewrite Ha | right; rewrite Hr' ltry].
        rewrite (neq0y_comulnnge_eq_mulnnge c b);
          last by split; [right; rewrite Ht' ltry | right; rewrite Hr' ltry].
        rewrite -p_sum_mulDr // p_sum_0nng //= Hr' Ht'.
        by apply fin_gt0_comulnnge_eq_mulnnge.
    + rewrite (neq0y_comulnnge_eq_mulnnge c a);
        last by split; [right; rewrite Hs' ltry | right; rewrite Hr' ltry].
      rewrite (neq0y_comulnnge_eq_mulnnge c b);
        last by split; [left; rewrite Hr' | right; rewrite Hr' ltry].
      rewrite -p_sum_mulDr // -neq0y_comulnnge_eq_mulnnge // Hr'.
      split; first by left.
      right. by rewrite ltry.
Qed.

Lemma harmonic_p_sum_mulDr (a b c: {nonneg \bar R}) (p: \bar R):
  p < 0 -> c ⊗ (a ⊕[p] b) = (c ⊗ a) ⊕[p] (c ⊗ b).
Proof.
  move=> Hp. rewrite p_sum_duality; last by apply lt_neq.
  rewrite (p_sum_duality _ (c ⊗ a)); last by apply lt_neq.
  rewrite -(invnnge_involutive c).
  have ->: ((c `*) `* ⊗ a) = ((c `*) `* ⊗ (a `*) `*)
    by rewrite (invnnge_involutive a).
  have ->: ((c `*) `* ⊗ b) = ((c `*) `* ⊗ (b `*) `*)
    by rewrite (invnnge_involutive b).
  rewrite -!comulnnge_invnnge.
  rewrite p_sum_comulDr ?oppe_gt0 //.
  by rewrite !invnnge_involutive.
Qed.
 
Lemma mul_p_sum_le_max_mul (a b c d: {nonneg \bar R}) (p: \bar R):
  p != 0 -> ((a ⊕[p] b) ⊗ (c ⊕[-p] d) <= maxe (a ⊗ c) (b ⊗ d))%O. 
Proof.
Admitted.
End results.
