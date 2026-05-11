From mathcomp Require Import all_ssreflect ssralg ssrint ssrnum matrix.
From mathcomp Require Import interval rat.
From mathcomp Require Import boolp classical_sets functions mathcomp_extra.
From mathcomp Require Import unstable reals ereal interval_inference.
From mathcomp Require Import topology tvs normedtype landau sequences derive.
From mathcomp Require Import realfun interval_inference convex interval exp lebesgue_integral.
From mathcomp Require Import hoelder counting_measure cardinality measure all_algebra.
From mathcomp Require Import ess_sup_inf finmap.

Import Order.TTheory GRing.Theory Num.Theory.

(* A full line should represent a meaningful reasoning step *)

Definition tuple (xy: nat * nat): Prop.
Proof.
  admit.
Admitted.

Lemma tup_nice xy: tuple xy -> xy.1 = xy.2.
Proof.
  admit.
Admitted.

Lemma bull (xy: nat * nat): xy.1 = xy.2 -> False.
Proof.
Admitted.

Goal forall (xy: nat * nat), tuple xy -> xy.1 = xy.2.
Proof.
  case => x-y-/=-Hxy.
  Restart.
  case => x y /= Hxy.
  Restart.
  move => xy. case: xy => x y /= Hxy.
  Restart.
  move => [x y] /=.
  Restart.
  move => [x y] /= /tup_nice-Hx.
  Restart.
  move => [x y] /= /(tup_nice _) //.
  Restart.
  move => [x y] /tup_nice //=. (* Also works with // instead of //= *)
  Restart.
  move => [x y] /= /tup_nice Hx.
Admitted.

Goal forall (xy: nat * nat), tuple xy -> odd xy.1 -> xy.1 = xy.2.
Proof.
  move => [[//|x] y] /= Htp Ho.
  move => {Ho}.
  Restart.
  move => [[//|x] y] /= /tup_nice /= Hx _ //.
  Restart.
  move => [[//|x] y] /= /tup_nice/bull //. 
  Restart.
Admitted.

Goal (forall x: nat, x = x) -> 42 = 42.
Proof.
  move => /(_ 42) //.
Qed.

Goal (forall x y: nat, x = y) -> 42 = 2.
Proof.
  move => /(_ 42 2) ->.
  Restart.
  move => /(_ 2 42) <-.
Admitted.

Goal forall x y: nat, x = y -> y = x.
Proof.
  move => x y Hxy.
  (* Error: wrong order of push's case: Hxy y => /=. *)
  case: y Hxy => //.
  Restart.
  move => x y Hxy => {Hxy}.
  Restart.
  move => x y Hxy.
  (* Error move: {Hxy}. *)
  move: y {Hxy}.
  Restart.
  move => x y Hxy.
  case EqnE: y Hxy => [|y'] Hxy.
  move: tup_nice.
Admitted.

Definition tupledef := fun (k: nat) => (1,2).

Lemma com: forall x y: nat, x + y = y + x.
Proof.               
  have Htst: (forall x: nat, x = x).
  by [].
  have /tupledef [x y]: nat.
  exact 42.
  have /tupledef[x' y']: nat.
  exact 42.
  Restart.
  suff /tupledef[x y]: nat. (* suff is like have, but swaps goals *)
Admitted.
  
Lemma subnK : forall n m, n <= m -> m - n + n = m.
Proof.
  move=> m n le_n_m.
  move: n m le_n_m.
  move => n m H.
  move: n m H => n' m' H'.
  
  elim: n' m' H' => [|n' IHn'] m' => [_ | H'].
  admit.
Admitted.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.
Local Open Scope order_scope.
Local Open Scope ereal_scope.


Section test.

Variable R: realType.

(* Unset Printing Notations. *)
(* Itv.Top is fake interval containing everything (?),
   Itv.Real is a real interval (not to be confused with
   interval of real numbers) 
   Itv.def requires interval int, doesn't work with realnumber interval *)
Check integral_count.

Local Open Scope ring_scope.

(* Definition p_sum (p: R) (x y : {nonneg \bar R}) : {nonneg \bar R}.
Proof.
  exists (poweR ((poweR (x%:num) (1/p)) + (poweR (y%:num) (1/p))) p) => /=.
  rewrite /ext_num_sem/=.
  rewrite in_itv. move => //=. apply andbT.
  wlog nat.
  apply/andP. split.
  - cbn. rewrite comparable0r.
  Search (0 >=< _%O).
  rewrite comparable0r.*)
  
(* Definition p_sum (p: R) (x y : {nonneg \bar R}): {nonneg \bar R} := ((((x%:num `^ (1/p)))%:nng + y%:num `^ (1/p)%:nng) `^ p)%:nng.
Check p_sum. *)


Definition square_fun (r: {nonneg \bar R}): ({nonneg \bar R}).
Proof.
  destruct r as [[x| |] Hx].
  - exists (EFin (powR x 2%R)).
    unfold ext_num_sem. cbn. apply/andP; split.
    + unfold Order.comparable. apply/orP. left.
      cbn. apply (powR_ge0 (x) 2%R).
    + erewrite in_itv. cbn. apply/andP. split; last easy.
      apply (powR_ge0 (x) 2%R).
  - exists (EPInf R).
    unfold ext_num_sem.
    unfold map_itv.
    cbn.
    apply/andP; split.
    + by apply cmp0y.
    + rewrite in_itv. apply/andP. split; last easy.
      cbn. 
      Check @real_ltry.
      specialize (@real_ltry R (0%Z%:~R)) as Hspz.
      move: Hspz => <-.
      specialize (@lt0y R) as Hr.
      apply Hr.
  - unfold ext_num_sem in Hx. cbn in Hx.
    move/andP: Hx => [Hx1 Hx2]. rewrite in_itv in Hx2.
    cbn in Hx2. exfalso. auto.
Defined.

(* Local Open Scope ring_scope. *)
Check poweR.

(*
Definition sqr (r : {nonneg \bar R}) (t: R): {nonneg \bar R} := ( poweR ((poweR (r%:num) (1/t)) + (poweR (r%:num) (1/t))) t)%:nng.
Print sqr.
Local Close Scope ring_scope.*)


Definition square_fun' (r : {nonneg \bar R}) : {nonneg \bar R}.
Proof.
  exists (r%:num ^+ 2)%E => /=.
rewrite /ext_num_sem /=.
rewrite in_itv /= andbT.
rewrite mule_ge0// andbT.
by rewrite realMe.
Defined.


Goal ((0 : int) <= (2%Z : int))%R -> ((0 : R) <= 2%R)%R.
Proof.
  trivial.
  Show Proof. Check Instances.natmul_inum.
Qed.

Local Close Scope classical_set_scope.
Local Close Scope ring_scope.
Local Close Scope order_scope.
Local Close Scope ereal_scope.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.
Local Open Scope order_scope.
Local Open Scope ereal_scope.

Check (2%R%:E \in `[0%R%:E,+oo[).
Locate "\in".


Lemma two_is_nng: 2%R%:E \in `[(0%R%:E: \bar R),+oo].
Proof.
  rewrite in_itv/= leey lee_fin ler0n. easy.
Qed.

Lemma two_is_nng': 2%R%:E \in `[(0%R%:E: \bar R),+oo[.
Proof.
  apply/andP. split.
  - Locate Num.Theory.ler01.
    have Hleq: ((0%R <= 1%R)%R). intro t. apply Num.Theory.ler01.
    specialize (Hleq R). 
    simpl.
   Search ((0 <= _)%R). specialize (le0z_nat 2) as Hleq2. trivial.
 (*  intros t. Search (2).
    specialize (Hadd R). symmetry in Hadd. rewrite Hadd.
    Set Printing Depth 1.   
    Print Num.Theory.
    apply Num.Theory.addr_ge0.
    * exact Hleq.
    * exact Hleq.*)
  - Search (_%R \is Num.real).
    admit.
Admitted.

Check (2%R%:E \in `[0%R%:E,(+oo: \bar R)]).

Locate set.


Check ([set x | x = 0%nat \/ x = 1%nat]).

Definition two_elem_set := [set x | x = 0%nat \/ x = 1%nat].

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.
Local Open Scope card_scope.


Lemma two_elem_set_has_two_elem: @counting _ R `I_2 = 2%R%:E.
Proof.
  rewrite /counting.
  have /asboolT ->: finite_set `I_2.
  by apply finite_II.
  suff ->: (((size (finmap.enum_fset (fset_set `I_2)))) = 2%nat).
  by done.
  by apply card_fset_set.
Qed.
Check @counting.

Check `I_2.
Definition thefun (n: nat): \bar R := match n with
                                      | 0 => 1%R%:E
                                      | S 0 => 2%R%:E
                                      | _ => 0%R%:E
                                      end.

Local Open Scope Lnorm_scope.
Lemma norm_compute: 'N[counting]_1 [thefun] = 3%R%:E.
Proof. 
  specialize (@Lnorm_counting _ 1 thefun) => -> //.
  rewrite (nneseries_split _ 2).
  - rewrite eseries0. rewrite addr0.
    * have ->: (0%nat + 2%nat)%nat = 2%nat by rewrite add0n.
      rewrite big_ltn //= big_ltn //=. (* It took me quite log to figure that that the lemma is in bigop.v *)
      rewrite big_geq //=.
      rewrite normr_nat normr1 invr1 !powRr1 //. 
      by rewrite addr0 //=. 
    * move=> [|[|i]] _ _ //=. rewrite normr0.
      by apply (@poweRe1 R 0%:E).
  - by move=> [|[|k]] _ //=.
Qed.

Local Open Scope ereal_scope.

Definition p_sum_int_fun (a b: \bar R) (n: nat) := match n with
                                      | 0 => a
                                      | S 0 => b
                                      | _ => 0%R%:E
                                                   end.

Definition p_sum_int_fun' (a b: \bar R) (g: bool) := if g then a else b.

Definition p_sum_int_fun'' (a b: \bar R) (n: nat) := if n == 0%N then a else if n == 1%N then b else 0.


Definition p_sum'' (p: \bar R) (a b: {nonneg \bar R}):= 'N[counting]_p [p_sum_int_fun'' a%:num b%:num].


Lemma p_sum_correct_fin (p : R) (a b: {nonneg \bar R}):
  (0 < p)%R -> p_sum'' p%:E a b = (a%:num `^ p + b%:num `^ p) `^ (1/p).
Proof.
  intros Hp. rewrite /p_sum''.
  Check Lnorm_counting.
  rewrite (@Lnorm_counting _ _ (p_sum_int_fun'' a%:nngnum b%:nngnum)) //.
  rewrite (nneseries_split _ 2).
  - rewrite eseries0.
    * have ->: (0%nat + 2%nat)%nat = 2%nat by rewrite add0n.
      rewrite addr0 big_ltn // big_ltn //.
      rewrite big_geq //=. rewrite !gee0_abs //.
      by rewrite div1r addr0.
    * rewrite /p_sum_int_fun'' //=.  rewrite /p_sum_int_fun'' //=.
      move=> [|[|i]] _ _ //=. rewrite normr0.
      rewrite powR0 //=. by apply lt0r_neq0. (* x `^ 1 for x < 0 is not defined *)
  - by move=> [|[|k]] _ //=; apply poweR_ge0.
Qed.

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
    

Lemma p_sum_correct_y (a b: {nonneg \bar R}):
  p_sum'' +oo a b = maxe a%:num b%:num.
Proof.
  rewrite /p_sum''. rewrite unlock /Lnorm /=.
  have ->: 0%R < counting [set: nat].
  move=> R' /=. rewrite /counting.
  by have /asboolF -> //: ~finite_set [set: nat] by apply infinite_nat.
  (* abse is absolute value for extended real *)
  (* \o is function composition *)
  apply le_anti. apply /andP. split.
  - apply /ess_supP. exists set0. split; try done.
    apply subsetCl. rewrite setC0.
    move=> [|[|_]] _ /=; rewrite /p_sum_int_fun'' ?gee0_abs // num_lee_max; apply /orP.
    * by left.
    * by right.
    * left. rewrite normr0.
      suff H: 0%R <= a%:nngnum by done. (* This surely should not be so complicated... *)
      by apply ge0e.
  - rewrite /ess_sup /mkset. apply /ereal_infP. move=> y Hyae.
    have Hy: forall x : nat, (abse \o p_sum_int_fun'' a%:nngnum b%:nngnum) x <= y.
    by apply ae_counting.
    clear Hyae. rewrite num_gee_max. apply/andP. split.
    * move: Hy=> /(_ 0%N) /=. by rewrite gee0_abs // /p_sum_int_fun''.
    * move: Hy=> /(_ 1%N) /=. by rewrite gee0_abs // /p_sum_int_fun''. (*copy-paste,bad*)
Qed.

Definition invnnge (a: {nonneg \bar R}) : {nonneg \bar R}.
Proof.
  exists (a%:num^-1).
  rewrite /ext_num_sem /=. apply/andP. split.
  - rewrite /Order.comparable. apply/orP. left. by rewrite inve_ge0.
  - rewrite in_itv /=. apply/andP. by rewrite inve_ge0. (* Not nice that both subgoals similar... *)
Defined.

Lemma invnnge_correct (a: {nonneg \bar R}):
  (invnnge a)%:num = 1 / a%:num.
Proof.
  by rewrite /invnnge /= div1e.
Qed.

Definition mulnnge (a b: {nonneg \bar R}) := (a%:num * b%:num)%:nng.

Definition comulnnge (a b: {nonneg \bar R}) := invnnge (mulnnge (invnnge a) (invnnge b)).

Declare Scope nngereal_scope.

Locate "*". Print Grammar constr. 

Notation "x `*" := (invnnge x) : nngereal_scope.
Notation "x `⊗ y" := (mulnnge x y) (at level 46, left associativity) : nngereal_scope.
Notation "x `⊗* y" := (comulnnge x y) (at level 46, left associativity) : nngereal_scope.
Notation "x `⊕^ p y" := (p_sum'' p x y) (at level 50, left associativity) : nngereal_scope.
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
  Print if_spec.
  Print ltP.
  Print Order.ltl_xor_ge. About le_lt_trans.
  ltl_xor_ge (disp : Order.disp_t) (T : latticeType disp) 
(x y : T) : T -> T -> T -> T -> T -> T -> T -> T -> bool -> bool -> Set :=
    LtlNotGe : (x < y)%O -> Order.ltl_xor_ge x y x x y y x x y y false true
  | GelNotLt : (y <= x)%O -> Order.ltl_xor_ge x y y y x x y y x x true false.
  move: (nng_nngy a)=> [->|[r Hrnng ->]]; first by left.
  rewrite le_eqVlt in Hrnng.
  move: Hrnng => /orP [/eqP <-|Hr].
  - right. by left.
  - right. right. by exists r.
Qed.

Lemma nng_0pos (a: {nonneg \bar R}):
  (a%:num = 0) \/ (a%:num > 0).
Proof.
  destruct (nng_0posy a) as [->|[->|[r Hr ->]]].
  - by right.
  - by left.
  - by right.
Qed.

Open Scope nngereal_scope.

Lemma pos_implies_non0 (r: R):
  0%R < r%:E -> r%:E != 0.
Proof.
  rewrite lt0e.  by move=> /andP [Hr _] //.
Qed.

Lemma pos_implies_fin_num (r: R):
  0%R < r%:E -> r%:E^-1 \is a fin_num.
Proof.
   move=> Hr. have H1: r%:E != 0%R. by apply pos_implies_non0. 
   by apply (fin_numV H1).
Qed.

(** Automation to solve x <= +oo would be nice *)

Lemma mul_comul_ineq (a b : {nonneg \bar R}): (a `⊗ b)%:num <= (a `⊗* b)%:num.
Proof.
  move: (nng_0posy a) (nng_0posy b) => /= [->|[->|[r Hr ->]]] [->|[->|[s Hs ->]]].
  -  rewrite invey mul0e inve0 mulyy.
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


Lemma tst (a b c : {nonneg \bar R}):
  ((a `⊗ b)%:num <= c`*%:num) <-> (a%:num <= (b `⊗ c)`*%:num). (* Should we use = instead *)
Proof.
  split.
  - move: (nng_0pos a) => /= [->|Ha] Hineq.
    * by rewrite inve_ge0.
    * move: (nng_0pos b) Hineq => /= [->|Hb] Hineq.
     + rewrite mul0e inve0. by apply (leey (a%:nngnum)).
     + have Hc: c%:num < +oo.
       suff Hc': c%:num != +oo by rewrite ltey.
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
       have Ha': a%:num < +oo by apply (le_lt_trans )
       Search (_ < +oo).
       Search (_ <= _ -> _ < _ -> _ < _).
       have Ha': (a%:num < +oo).
       -- by  Search (_ <= +oo).
       Search ((_ < _) -> (_ < _) -> False).
       Search (_ < +oo).  by done.
