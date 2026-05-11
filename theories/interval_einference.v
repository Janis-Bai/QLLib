From HB Require Import structures.
From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat eqtype choice.
From mathcomp Require Import order interval ssralg.
From mathcomp Require Import orderedzmod numdomain numfield ssrint.
From mathcomp Require Import all_ssreflect ssralg ssrint ssrnum matrix.
From mathcomp Require Import interval interval_inference reals rat.
From mathcomp Require Import boolp classical_sets functions mathcomp_extra.
From mathcomp Require Import constructive_ereal exp.

Import Order.TTheory GRing.Theory Num.Theory.

Section ereal_inv_interval.

Local Open Scope ring_scope.
Local Open Scope order_scope.
Local Open Scope ereal_scope.
  Variable R: realType.

  Local Notation ext_num_def := (Itv.def ext_num_sem).
  Local Notation ext_num_spec := (Itv.spec ext_num_sem).

  Lemma realIe:
    forall x: \bar R, 0%:E >=< x -> 0%:E >=< x^-1.
  Proof.
    move=> x. rewrite /Order.comparable.
    move=> /orP [Hnpos|Hnneg]; apply/orP.
    - left. by rewrite inve_ge0.
    - move: Hnneg. rewrite Order.POrderTheory.le_eqVlt. (* How to import this? *)
      move=> /orP [/eqP ->|Hneg].
      + left. rewrite inve0. by specialize (@leey R (0%:E)). (* apply leey causes Rocq to diverge *)
      + right.
        have Hinfe: (x != +oo).
        rewrite -ltey. eapply lt_le_trans; first exact Hneg.
        by specialize (@leey R (0%:E)).
        have Hnon0: (x != 0) by move: Hneg => /lt_eqF /eqP Hneg; apply/eqP. 
        rewrite inve_le0 //. by apply ltW.
  Qed.

  Definition keep_neg_strict_bound b :=
  match b with
  | BSide b 0%Z => +oo%O (* Needed because 0^-1 = +oo *)
  | BSide b (Negz _) => BLeft 0%Z
  | BSide _ (Posz _) => +oo%O
  | BInfty _ => +oo%O
  end.

  Definition int_inve i :=
  let: Interval l u := i in
  Interval (IntItv.keep_nonneg_bound l) (keep_neg_strict_bound u).
  
  Lemma ext_num_spec_div xi (x : ext_num_def xi) (r := Itv.real1 int_inve xi) :
    ext_num_spec r (x%:inum^-1 : \bar R).
  Proof.
    apply: Itv.spec_real1 (Itv.P x).
    case: x => x /= _ [l u]. rewrite /ext_num_sem /=.
    move=> /and3P[xr /= lx xu].
    apply/andP. split; first by apply realIe.
    rewrite in_itv.  apply/andP. split.
    - destruct l as [b i|b].
      + destruct i as [n|n] eqn:Ei; last done.
        destruct b; rewrite bnd_simp /= in lx; rewrite /= inve_ge0;
        have Hineq: 0%R <= (n%:~R)%:E by done.
        * by eapply le_le_trans.
        * apply ltW. by eapply le_lt_trans.
      + done. 
    - destruct u as [b i|b]; last done.
      destruct i as [[|n]|n].
      + by destruct b.
      + by destruct b. 
      + destruct b; rewrite bnd_simp /= in xu; rewrite /= inve_lt0.
        * apply ltW in xu. by eapply le_lt_trans; first exact xu.
        * by eapply le_lt_trans; first exact xu.
  Qed.

  Canonical inve_inum xi (x : ext_num_def xi) :=
    Itv.mk (ext_num_spec_div _ x).

  Definition poweR_itv i :=
  let: Interval l u := i in
  Interval (IntItv.keep_pos_bound l) +oo%O.

  Lemma ext_num_spec_poweR (i : Itv.t) (x : ext_num_def i) p
    (r := powR_itv i)  :
    ext_num_spec r (x%:inum `^ p : \bar R).
  Proof.
   rewrite {}/r. case: i x => [|[l u]] x /=; [by apply/and3P; rewrite ?num_real|].
   case: x => [x /=/and3P[xr lx xu]].
   rewrite /ext_num_sem /=. apply/andP. split.
   - apply/orP. left. by apply poweR_ge0.
   - rewrite in_itv. apply/andP. split; last done. simpl.
     destruct l as [b i|b]; last done.
     + destruct i as [[|n]|n]; simpl; last done.
       * destruct b; simpl; first by apply poweR_ge0.
         by apply poweR_gt0.
       * destruct b; rewrite bnd_simp in lx; apply poweR_gt0.
         -- eapply lt_le_trans; last apply lx.
            by rewrite lte_fin.
         -- eapply le_lt_trans; last apply lx.
            by rewrite lee_fin.
  Qed.

  Canonical poweR_inum i (x : ext_num_def i) p :=
    Itv.mk (ext_num_spec_poweR _ x p).

End ereal_inv_interval.
