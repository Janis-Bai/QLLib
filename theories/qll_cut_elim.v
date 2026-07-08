From Stdlib Require Import List Wf_nat.

From mathcomp Require Import all_boot all_order ssralg ssrint ssrnum.
From mathcomp Require Import reals constructive_ereal classical_sets ereal zify.

From QLLib Require Import qll_defs qll_core_facts nonneg_ereal list_lemmas.

Import Order.TTheory.

Import ListNotations.

Section cut_elim.

Context {R: realType}.
Context {p: {posnum \bar R}}.
Context {atoms: Type}.

Open Scope qll_calculus.     

(** * Cut Elimination Proof for pQLL *)
(** ** Fundamental Definitions *)
(** Rank of a formula (i.e. number of connectives in a formula) *)
Fixpoint fm_rank (form: @qll_formula R p atoms) := match form with
  | atom _ | neg_atom _ | 𝟙 | ⊥ | ⊤  => 1
  | A ⊗ B | (A ⊗* B) | A ∧[_] B | A ∨[_] B => fm_rank A + fm_rank B + 1
  end.

Lemma rank_neg_invariant A:
  fm_rank A = fm_rank A`*.
Proof.
  by induction A as [a | a | | | | [| | |] A IHA B IHB] => //=; rewrite IHA IHB.
Qed.

(** Size of proofs *)
Fixpoint pf_size {Γ: list (@qll_formula R p atoms)} (P: ⊢O Γ) := match P with
  | OAX _ => 1
  | OEMP => 1
  | OEFQ _ => 1
  | OCUT _ _ _ _ P1 P2 => pf_size P1 + pf_size P2 + 1
  | OMIX _ _ P1 P2 => pf_size P1 + pf_size P2 + 1
  | OEXCH _ _ _ _ P => pf_size P + 1
  | Otensor _ _ _ _ P1 P2 => pf_size P1 + pf_size P2 + 1
  | Opar _ _ _ P => pf_size P + 1
  | Oone => 1
  | Oor _ _ _ P1 P2 => pf_size P1 + pf_size P2 + 1
  | Oand _ _ _ P1 P2 => pf_size P1 + pf_size P2 + 1
  | Otop _ => 1
  end.

Open Scope ring_scope.
Open Scope ereal_scope.

(** ** Inductive Hypotheses for Cut Admissibility Proof *)
Definition IH_form_rk (rk: nat) := forall Σ Γ Δ A (P1: ⊢O A `*::Γ) (P2: ⊢O Σ ++ A::Δ),
   (fm_rank A < rk)%coq_nat ->
   Ocut_free P1 -> Ocut_free P2 ->
   exists Q:  ⊢O Σ ++ Γ ++ Δ, Ocut_free Q /\
   ((Ovalidity P1 ⊗ Ovalidity P2)%NNGE%:num <= (Ovalidity Q)%:num)%O.

Definition IH_proof_sz (sz rk: nat) := forall Σ Γ Δ A (P1: ⊢O A `*::Γ) (P2: ⊢O Σ ++ A::Δ),
   (pf_size P1 + pf_size P2 < sz)%coq_nat ->
   (fm_rank A <= rk)%coq_nat ->
   Ocut_free P1 -> Ocut_free P2 ->
   exists Q:  ⊢O Σ ++ Γ ++ Δ, Ocut_free Q /\
   ((Ovalidity P1 ⊗ Ovalidity P2)%NNGE%:num <= (Ovalidity Q)%:num)%O.

(** ** Cut Admissibility *)
(* We need rk as parameter here:
were we to instantiate IH_proof_sz with (fm_rank A) instead of rk
this lemma would still be provable (with the same proof), but using it in
the cut admissibility lemma below would require lots of boilerplate proof script *) 
Lemma cut_adm_exch_case {Σ Γ Γ' Δ Δ' A B C} sz rk: 
  (IH_proof_sz sz rk) -> (Σ ++ A::Δ = Γ' ++ C::B::Δ')%SEQ ->
    forall (P1: ⊢O A `*::Γ) (P2: ⊢O Γ' ++ B::C::Δ'),
    Ocut_free P1 -> Ocut_free P2 ->
    (pf_size P1 + pf_size P2 < sz)%coq_nat -> (fm_rank A <= rk)%coq_nat ->
    exists Q: ⊢O Σ ++ Γ ++ Δ, Ocut_free Q /\ 
    ((Ovalidity P1 ⊗ Ovalidity (OEXCH _ _ _ _ P2))%NNGE <= Ovalidity Q)%O.
Proof.
  rewrite /IH_proof_sz => IHsz Heq P1 P2 Hcf1 Hcf2 Hsz Hrk /=.
  exch_inv_tac Heq; subst.
  - move: P2 Hcf2 IHsz Hsz => /=. rewrite cat_two_cons_cat_lift => P2 Hcf2 IHsz Hsz.
      specialize (IHsz _ _ _ _ P1 P2).
      destruct IHsz as [Q [Hcf HQval]] => //.
      revert Q Hcf HQval. rewrite -catA => Q Hcf HQval. rewrite -catA.
      by exists (OEXCH _ _ _ _ Q).
  - move: P2 Hcf2 IHsz Hsz => /=. rewrite -cat_cons_cat_lift => P2 Hcf2 IHsz Hsz.
      specialize (IHsz _ _ _ _ P1 P2).
      destruct IHsz as [Q [Hcf HQval]] => //.
      revert Q Hcf HQval. rewrite !catA => Q Hcf HQval. 
      by exists (OEXCH _ _ _ _ Q).
  - rewrite -cat_cons_eq_cat_cat.
      suff [Q [HQcut HQval]]: exists Q: ⊢O Γ' ++ Γ ++ C::Δ', Ocut_free Q /\
              (Ovalidity P1 ⊗ Ovalidity P2)%NNGE%:num <= (Ovalidity Q)%:num.
        move: (Olist_form_exch_r Q) => /= [Q' [HQ'val HQ'cut]].
        exists Q' => /=. split; first by rewrite -HQ'cut.
        by rewrite -HQ'val.
      destruct (IHsz _ _ _ _ P1 P2) as [Q [HQcut HQval]] => //=.
      by exists Q.
  - suff [Q [HQcut HQval]]: exists Q: ⊢O Γ' ++ B :: Γ ++ Δ', Ocut_free Q /\
              (Ovalidity P1 ⊗ Ovalidity P2)%NNGE%:num <= (Ovalidity Q)%:num.
        destruct (Olist_form_exch_l Q) as [Q' [HQ'val HQ'cut]].
        exists Q' => /=. split; first by rewrite -HQ'cut.
        by rewrite -HQ'val.
      move: P2 Hcf2 IHsz Hsz => /=. rewrite cat_cons_eq_cat_cat.
      move => P2 Hcf2 IHsz Hsz.
      destruct (IHsz _ _ _ _ P1 P2) as [Q [HQcut HQval]] => //.
      rewrite cat_cons_eq_cat_cat. by exists Q.
Qed.

Lemma cut_adm_exch_switch_case {Σ Γ Γ' Δ C D E} sz rk:
  (IH_proof_sz sz rk) -> (Σ ++ E::D::Δ = C `* :: Γ)%SEQ ->
    forall P1: ⊢O Σ ++ (D::E::Δ), forall P2: ⊢O C :: Γ',
    Ocut_free P1 -> Ocut_free P2 ->
    (pf_size P1 + pf_size P2 < sz)%coq_nat -> (fm_rank C <= rk)%coq_nat ->
    exists Q : ⊢O Γ ++ Γ', Ocut_free Q /\
    (Ovalidity P1)%:nngnum * (Ovalidity P2)%:nngnum <= (Ovalidity Q)%:nngnum.
Proof.
  rewrite /IH_proof_sz => IHsz Heq P1 P2 Hcf1 Hcf2 Hsz Hrk /=.
  move: P2 IHsz Hcf2 Hsz. rewrite (neg_involutive C) => P2 IHsz Hcf2 Hsz.
  rewrite muleC -(cats0 (_ ++ _)) -catA. (* Workaround, -(cats0 Δ') fails to rewrite *)
  symmetry in Heq. rewrite -(@cat0s _ (C `* :: Γ)) in Heq.
  destruct (cut_adm_exch_case sz rk IHsz Heq P2 P1) as [Q [HQcut HQval]] => //;
    [by lia | by rewrite -rank_neg_invariant |].
  rewrite -(cat0s (_ ++ _ ++ _)). 
  move: Q HQcut HQval. rewrite -(cats0 (_ ++ _ ++ _)) -catA -catA => Q HQcut HQval.     
  destruct (Olist_list_exch Q) as [Q' [HQ'val HQ'cut]].
  exists Q'. split; first by rewrite -HQ'cut. by rewrite -HQ'val.
Qed.

Lemma cut_adm_mix_case {Σ Γ Δ Σ' Γ' A} sz rk:
  (IH_proof_sz sz rk) -> (Σ' ++ Γ')%SEQ = (Σ ++ A :: Δ)%SEQ ->
    forall P1: ⊢O A`* :: Γ, forall P2_1: ⊢O Σ', forall P2_2: ⊢O Γ',
    Ocut_free P1 -> Ocut_free P2_1 -> Ocut_free P2_2 ->
    (fm_rank A <= rk)%coq_nat -> 
    (pf_size P1 + pf_size P2_1 + pf_size P2_2 < sz)%coq_nat ->
    exists Q: ⊢O Σ ++ Γ ++ Δ, Ocut_free Q /\
    ((Ovalidity P1 ⊗ Ovalidity (OMIX _ _ P2_1 P2_2))%NNGE)%:num <= (Ovalidity Q)%:num.
Proof.
  rewrite /IH_proof_sz => IHsz Heq P1 P2_1 P2_2 Hcf1 Hcf2_1 Hcf2_2 Hsz Hrk /=.
  cat_cons_cat_inv_tac Heq; subst. 
  - specialize (IHsz Σ Γ Σ0 A P1 P2_1).
    destruct IHsz as [Q [Hcf HQval]] => //=; first by lia.
    rewrite catA catA -(catA Σ _ _). exists (OMIX _ _ Q P2_2).
    repeat split => //=. rewrite muleA.
    by apply: lee_pmul.
  - specialize (IHsz Σ0 Γ Δ A P1 P2_2).
    destruct IHsz as [Q [Hcf HQval]] => //=; first by lia.
    rewrite -catA. exists (OMIX _ _ P2_1 Q). repeat split => //=.
    rewrite (@muleC _ (Ovalidity P2_1)%:num (Ovalidity P2_2)%:num) muleA.
    rewrite (@muleC _ (Ovalidity P2_1)%:num (Ovalidity Q)%:num).
    by apply: lee_pmul.
Qed.

Lemma cut_adm_mix_switch_case {Γ Δ Σ' Γ' A} sz rk:
  IH_proof_sz sz rk -> (Σ' ++ Γ')%SEQ = (A`*::Γ)%SEQ ->
    forall P1_1: ⊢O Σ', forall P1_2: ⊢O Γ', forall P2: ⊢O A::Δ,
    Ocut_free P1_1 -> Ocut_free P1_2 -> Ocut_free P2 ->
    (fm_rank A <= rk)%coq_nat -> 
    (pf_size P1_1 + pf_size P1_2 + pf_size P2 < sz)%coq_nat ->
    exists Q: ⊢O Γ ++ Δ, Ocut_free Q /\
    ((Ovalidity (OMIX _ _ P1_1 P1_2) ⊗ Ovalidity P2)%NNGE)%:num <= (Ovalidity Q)%:num.
Proof.
  rewrite /IH_proof_sz => IHsz Heq P1_1 P1_2 P2 Hcf1_1 Hcf1_2 Hcf2 Hsz Hrk /=.
  destruct (cat_cons_inv _ _ _ _ Heq) as [[Σ HΣ]|[HA HA']]; subst;
  move: P2 Hcf2 Hrk => //;
  have ->: A::Δ = (A`*) `*::Δ by rewrite -neg_involutive.
  - move=> P2 Hcf2 Hrk.
    destruct (IHsz [] _ _ _ P2 P1_1) as [Q [HQcut HQval]] => //=;
      [by lia | by rewrite -rank_neg_invariant |].
    inversion Heq. subst.
    pose P := (OMIX _ _ P1_2 Q). simpl in P. 
    rewrite -catA -(cat0s (_ ++ _ ++ _)) -(cats0 ([] ++ _)) -catA -catA.
    suff [Q' [HQ'cut HQ'val]]: exists Q: ⊢O [] ++ (Γ' ++ Δ) ++ Σ ++ [], Ocut_free Q /\
      (Ovalidity P1_1)%:num * (Ovalidity P1_2)%:num * (Ovalidity P2)%:num <=
      (Ovalidity Q)%:num.
      by destruct (Olist_list_exch Q') as [T [HTval HTcut]]; exists T;
      split; [rewrite -HTcut | rewrite -HTval].
    rewrite cats0 cat0s -catA. exists P. split => //=.
    rewrite muleC muleA (muleC _ (Ovalidity Q)%:num). 
    by apply: lee_pmul.
  - move=> P2 Hcf2 Hrk.
    destruct (IHsz [] _ _ _ P2 P1_2) as [Q [HQcut HQval]] => //=;
      [by lia | by rewrite -rank_neg_invariant |].
    rewrite -(cat0s (_ ++ _)) -(cats0 ([] ++ _)) -catA -catA.
    suff [Q' [HQ'cut HQ'val]]: exists Q: ⊢O [] ++ Δ ++ Γ ++ [], Ocut_free Q /\
      (Ovalidity P1_1)%:num * (Ovalidity P1_2)%:num * (Ovalidity P2)%:num <=
      (Ovalidity Q)%:num.
      by destruct (Olist_list_exch Q') as [T [HTval HTcut]]; exists T;
      split; [rewrite -HTcut | rewrite -HTval].
    rewrite cats0. exists (OMIX _ _ P1_1 Q). split => //=.
    rewrite /= muleC in HQval. rewrite -muleA. 
    by apply: lee_pmul.
Qed.

Lemma cut_adm_and_vs_or_case {Γ Δ A B} rk:
  IH_form_rk rk ->
    forall (P1_1: ⊢O A `* :: Γ) (P1_2: ⊢O B `* :: Γ) (P2_1: ⊢O A :: Δ) (P2_2: ⊢O B :: Δ),
    Ocut_free P1_1 -> Ocut_free P1_2 -> Ocut_free P2_1 -> Ocut_free P2_2 ->
    (fm_rank A + fm_rank B < rk)%coq_nat ->
    exists Q : ⊢O Γ ++ Δ, Ocut_free Q /\
    ((Ovalidity P1_1 ⊕ [- p%:posnum] Ovalidity P1_2)%NNGE)%:nngnum *
    ((Ovalidity P2_1 ⊕ [p%:posnum] Ovalidity P2_2)%NNGE)%:nngnum <= (Ovalidity Q)%:nngnum.
Proof.
  rewrite /IH_form_rk => IHrk P1_1 P1_2 P2_1 P2_2 Hcf1_1 Hcf1_2 Hcf2_1 Hcf2_2 Hrk.
  pose Hle := (le_total (Ovalidity P2_1 ⊗ Ovalidity P1_1)%NNGE%:num
                     (Ovalidity P1_2 ⊗ Ovalidity P2_2)%NNGE%:num).
  move: Hle => /orP /= [Hle|Hle]. (* Workaround *)
  - destruct (IHrk [] _ _ _ P1_2 P2_2) as [Q [HQcut HQval]] => //;
      first by lia.
    exists Q. split => //. rewrite muleC.
    eapply le_trans; first by apply: mul_p_sum_le_max_mul.
    eapply le_trans; last by apply HQval.
    simpl. rewrite maxe_translation num_gee_max.
    apply/andP. split => //. by rewrite muleC.
  - destruct (IHrk [] _ _ _ P1_1 P2_1) as [Q [HQcut HQval]] => //;
      first by lia.
    exists Q. split => //. rewrite muleC.
    eapply le_trans; first by apply: mul_p_sum_le_max_mul.
    eapply le_trans; last by apply HQval.
    simpl. rewrite maxe_translation num_gee_max.
    apply/andP. split => //=; first by rewrite muleC.
    by rewrite (muleC (Ovalidity P2_2)%:num _) (muleC (Ovalidity P1_1)%:num _).
Qed.

Theorem Ocut_admissibility {Σ Γ Δ: list (@qll_formula R p atoms)} {A}:
  forall P1: ⊢O A `*::Γ, forall P2: ⊢O Σ ++ A::Δ, Ocut_free P1 -> Ocut_free P2 ->
    exists Q: ⊢O Σ ++ Γ ++ Δ, Ocut_free Q /\ ((Ovalidity P1 ⊗ Ovalidity P2)%NNGE <= Ovalidity Q)%O.
Proof.
  enough (forall rk sz Σ Γ Δ A (P1: ⊢O A `*::Γ) (P2: ⊢O Σ ++ A::Δ), (fm_rank A <= rk)%coq_nat -> sz = (pf_size P1 + pf_size P2)%N -> Ocut_free P1 -> Ocut_free P2 -> exists Q: ⊢O Σ ++ Γ ++ Δ, Ocut_free Q /\ ((Ovalidity P1 ⊗ Ovalidity P2)%NNGE%:num <= (Ovalidity Q)%:num)%O) as H;
    first by (move=> P1 P2; apply (H (fm_rank A) (pf_size P1 + pf_size P2)%N) => //).
  clear Σ Γ Δ A.
  induction rk as [rk IHrk0] using lt_wf_rect. 
  have IHrk: IH_form_rk rk. 
    by move => Σ Γ Δ A P1 P2 Hrk; apply (IHrk0 (fm_rank A) Hrk (pf_size P1 + pf_size P2)%N) => //.
  rewrite /IH_form_rk in IHrk.  clear IHrk0.
  
  induction sz as [sz IHsz0] using lt_wf_rect.
  have IHsz: IH_proof_sz sz rk.
    by move => Σ Γ Δ A P1 P2 Hsz Hrk; apply (IHsz0 (pf_size P1 + pf_size P2)%N) => //.
  rewrite /IH_proof_sz in IHsz. clear IHsz0.
  move => Σ Γ Δ A P1 P2 Hrk Heqsz Hcf1 Hcf2. subst sz.
  
  remember (Σ ++ A :: Δ)%SEQ as ΣAΔ. destruct_Oprv P2 Σ' Γ' Δ' B C P2_1 P2_2 P2.
  - (* OAX *)
    destruct Σ as [| x Σ]; inversion HeqΣAΔ; subst.
    + rewrite /= mule1. 
      move: P1 Hcf1 IHsz. rewrite -(neg_involutive B) => P1 Hcf1 IHsz. (* Workaround *)
      specialize (@Olist_form_exch_l _ _ _ Γ [] [] B) as HQ. rewrite cats0 /= in HQ. 
      destruct (HQ P1) as [Q [HQval HQcf]]. exists Q. split; first by rewrite -HQcf.
      rewrite HQval. by apply lexx.
    + symmetry in H1. apply elt_eq_unit in H1 as [Hn [Hm Hk]]. rewrite -Hn Hm Hk.
      rewrite cats0. simpl. exists P1. split => //. by rewrite mule1.
  - (* OEMP *)
    by destruct Σ as [| x Σ]; simpl in HeqΣAΔ; discriminate.
  - (* OEFQ *)
    exists (OEFQ _). split => //=. by rewrite mule0.
  - (* OCUT *)
    done.
  - (* OMIX *)
    destruct Hcf2.
    eapply (cut_adm_mix_case (pf_size P1 + pf_size (OMIX _ _ P2_1 P2_2)) rk) => //=.
    by lia.
  - (* OEXCH *)
    eapply (cut_adm_exch_case (pf_size P1 + (pf_size P2 + 1)) rk) => //. 
    by lia.
  - (* Otensor *)
    destruct Σ as [| D Σ]; inversion HeqΣAΔ; subst.
    + remember ((B ⊗ C) `* :: Γ) as BCΓ. 
      destruct_Oprv P1 Σ Σ' Δ D E P1_1 P1_2 P1; try inversion HeqBCΓ.
      * have -> /=: D = B ⊗ C by rewrite (neg_involutive D) (neg_involutive (B ⊗ C)) H0.
        rewrite mul1e. exists (Otensor _ _ _ _ P2_1 P2_2). by split.
      * exists (OEFQ _) => /=. rewrite mul0e. by split.
      * done.
      * simpl. destruct Hcf1. 
        pose P := Otensor _ _ _ _ P2_1 P2_2.
        apply (cut_adm_mix_switch_case _ rk IHsz HeqBCΓ P1_1 P1_2 P) => //=.
        by lia.
      * simpl in IHsz. simpl. pose P2 := (Otensor _ _ _ _ P2_1 P2_2).
        apply (cut_adm_exch_switch_case _ _ IHsz HeqBCΓ P1 P2) => //=.
        by lia.
      * simpl in *. inversion HeqBCΓ. subst. move: P2_1 P2_2 Hcf2 IHsz.
        rewrite -(cat0s (B::Γ')) -(cat0s (C::Δ')) => P2_1 P2_2 Hcf2 IHzs.
        destruct Hcf2 as [Hcf2_1 Hcf2_2].
        destruct (IHrk _ _ _ _ P1 P2_1) as [Q1 [HQ1cut HQ1val]]  => //; first by lia.
        move: Q1 HQ1cut HQ1val. rewrite catA -cat_cons_cat_lift cat0s => Q1 HQ1cut HQ1val. 
        destruct (IHrk _ _ _ _ Q1 P2_2) as [Q2 [HQ2cut HQ2val]] => //; first by lia.
        rewrite catA -(cat0s ((Γ ++ Γ') ++ Δ')). exists Q2. split => //.
        eapply le_trans; last exact HQ2val. rewrite muleA.
        by apply: (lee_pmul _ _ HQ1val _) => //.
    + cat_cons_cat_inv_tac H1; subst; destruct Hcf2 as [Hcf2_1 Hcf2_2] => /=.
      * destruct (IHsz (B::Σ) _ _ _ P1 P2_1) as [Q [HQcut HQval]] => //=; first by lia.
        rewrite catA catA -(catA Σ). 
        exists (Otensor _ _ (Σ ++ Γ ++ Σ0) _ Q P2_2). split => //=.
        rewrite muleA. by apply: (lee_pmul _ _ HQval _).
      * destruct (IHsz (C::Σ0) _ _ _ P1 P2_2) as [Q [HQcut HQval]] => //=; first by lia.
        rewrite -catA. exists (Otensor _ _ _ (Σ0 ++ Γ ++ Δ) P2_1 Q).
        split => //=. rewrite (muleC (Ovalidity P2_1)%:num _) muleA.
        rewrite (muleC _ (Ovalidity Q)%:num). by apply: (lee_pmul _ _ HQval _).
  - (* Opar *) 
    destruct Σ as [| D Σ]; inversion HeqΣAΔ; subst.
    + remember ((B ⊗* C) `* :: Γ) as BCΓ. 
      destruct_Oprv P1 Σ Σ' Δ' D E P1_1 P1_2 P1; try inversion HeqBCΓ.
      * have -> /=: D = B ⊗* C by rewrite (neg_involutive D) (neg_involutive (B ⊗* C)) H0.
        rewrite mul1e => /=. exists (Opar _ _ _ P2). by split.
      * exists (OEFQ _) => /=. rewrite mul0e. by split.
      * done.
      * simpl. destruct Hcf1. 
        pose P := Opar _ _ _ P2. 
        apply (cut_adm_mix_switch_case _ _ IHsz HeqBCΓ P1_1 P1_2 P) => //=.
        by lia.
      * pose P := Opar _ _ _ P2.
        apply (cut_adm_exch_switch_case _ _ IHsz HeqBCΓ P1 P) => //=.
        by lia.
      * subst. destruct Hcf1 as [Hcf1_1 Hcf1_2]. 
        move: P2 Hcf2 IHsz => /=. rewrite -(cat0s (_::_::_)) => P2 Hcf2 IHzs. 
        destruct (IHrk _ _ _ _ P1_1 P2) as [Q1 [HQ1cut HQ1val]] => //;
          first by (cbn in Hrk; lia).
        destruct (IHrk _ _ _ _ P1_2 Q1) as [Q2 [HQ2cut HQ2val]] => //;
          first by (cbn in Hrk; lia).
        rewrite -catA. exists Q2. split => //=. 
        eapply le_trans; last by apply HQ2val. 
        rewrite (muleC _ (Ovalidity P1_2)%:num) -muleA. 
        by apply: lee_pmul.
    + move: P2 Hcf2 IHsz => /=.
      rewrite -(cat0s (_ :: _)) cat_two_cons_cat_lift cat0s => P2 Hcf2 IHsz.
      destruct (IHsz _ _ _ _ P1 P2) as [Q [HQcut HQval]] => //=; first by lia.
      by exists (Opar _ _ _ Q).
  - (* Oone *)
    destruct Σ as [| B Σ]; inversion HeqΣAΔ; subst.
    + remember (𝟙 `* :: Γ) as OneΓ. 
      destruct_Oprv P1 Σ Σ' Δ' D E P1_1 P1_2 P1; try inversion HeqOneΓ.
      * destruct Γ as [| A Γ]; inversion H1; subst.
        have ->: A = 𝟙`* by rewrite -H0 -neg_involutive.
        simpl. exists Oone. split => //=. rewrite mule1. 
        by apply lexx.
      * exists (OEFQ _) => /=. rewrite mul0e. by split.
      * done.
      * destruct Hcf1.
        apply (cut_adm_mix_switch_case _ _ IHsz HeqOneΓ P1_1 P1_2 Oone) => //=.
        by lia.
      * apply (cut_adm_exch_switch_case _ _ IHsz HeqOneΓ P1 Oone) => //=.
        by lia.
      * exists OEMP. split => //=. rewrite mule1. 
        by apply lexx.
    + exfalso. by apply (list_elem_list_emp_inv _ _ _ H1).
  - (* Oor *)
    destruct Σ as [| D Σ]; inversion HeqΣAΔ; subst.
    + remember ((B ∨[_] C) `* :: Γ) as BCΓ.
      destruct_Oprv P1 Σ Σ' Δ' D E P1_1 P1_2 P1; try inversion HeqBCΓ.
      * have -> /=: D = (B ∨[_] C)
          by rewrite (neg_involutive D) (neg_involutive (B ∨[_] C)) H0. 
       rewrite mul1e. exists (Oor _ _ _ P2_1 P2_2). by split.
      * exists (OEFQ _) => /=. rewrite mul0e. by split.
      * done.
      * destruct Hcf1. 
        pose P := Oor _ _ _ P2_1 P2_2.
        apply (cut_adm_mix_switch_case _ _ IHsz HeqBCΓ P1_1 P1_2 P) => //=.
        by lia.
      * pose P := Oor _ _ _ P2_1 P2_2.
        apply (cut_adm_exch_switch_case _ _ IHsz HeqBCΓ P1 P) => //=.
        by lia.
      * subst. simpl in *. destruct Hcf1, Hcf2.
        apply (cut_adm_and_vs_or_case rk IHrk P1_1 P1_2 P2_1 P2_2) => //=.
        by lia.
    + simpl. destruct Hcf2 as [Hcf2_1 Hcf2_2].
      destruct (IHsz (B::Σ) _ _ _ P1 P2_1) as [Q1 [HQ1cut HQ1val]] => //=;
        first by lia.
      destruct (IHsz (C::Σ) _ _ _ P1 P2_2) as [Q2 [HQ2cut HQ2val]] => //=;
        first by lia. 
      exists (Oor _ _ _ Q1 Q2). split => //=.
      have ->: (Ovalidity P1)%:num * ((Ovalidity P2_1 ⊕ [p%:num] Ovalidity P2_2)%NNGE)%:num
           = (Ovalidity P1 ⊗ ((Ovalidity P2_1 ⊕ [p%:num] Ovalidity P2_2)))%NNGE%:num.
        by done.       
      rewrite p_sum_mulDr => //. by apply: p_sum_both_monotone.
  - (* Oand *)
    destruct Σ as [| D Σ]; inversion HeqΣAΔ; subst.
    + remember ((B ∧[_] C) `* :: Γ) as BCΓ.
      destruct_Oprv P1 Σ Σ' Δ' D E P1_1 P1_2 P1; try inversion HeqBCΓ.
      * have -> /=: D = (B ∧[_] C).
          by rewrite (neg_involutive D) (neg_involutive (B ∧[_] C)) H0.
        rewrite mul1e. exists (Oand _ _ _ P2_1 P2_2). by split.
      * exists (OEFQ _) => /=. rewrite mul0e. by split.
      * done.
      * destruct Hcf1. 
        pose P := Oand _ _ _ P2_1 P2_2.
        apply (cut_adm_mix_switch_case _ _ IHsz HeqBCΓ P1_1 P1_2 P) => //=.
        by lia.
      * pose P := Oand _ _ _ P2_1 P2_2.
        apply (cut_adm_exch_switch_case _ _ IHsz HeqBCΓ P1 P) => //=.
        by lia.
      * subst. simpl in *. move: P2_1 P2_2 Hcf2 IHsz.
        have ->: B::Δ = (B `*) `* :: Δ by rewrite -neg_involutive.
        have ->: C::Δ = (C `*) `* :: Δ by rewrite -neg_involutive.
        move => P2_1 P2_2 Hcf2 IHsz.  destruct Hcf1, Hcf2.
        
        destruct (cut_adm_and_vs_or_case _ IHrk P2_1 P2_2 P1_1 P1_2) as [Q [HQcut HQval]]=> //=;
          first by (rewrite -!rank_neg_invariant; lia).
        destruct (Otwo_list_list_exch Q) as [Q2 [HQ2val HQ2cut]].
        exists Q2. split => /=; first by rewrite -HQ2cut. 
        by rewrite muleC -HQ2val.
    + simpl. destruct Hcf2 as [Hcf2_1 Hcf2_2].
      destruct (IHsz (B::Σ) _ _ _ P1 P2_1) as [Q1 [HQ1cut HQ1val]] => //=;
        first by lia.
      destruct (IHsz (C::Σ) _ _ _ P1 P2_2) as [Q2 [HQ2cut HQ2val]] => //=;
        first by lia. 
      exists (Oand _ _ _ Q1 Q2). split => //=.
      have ->:  (Ovalidity P1)%:num * ((Ovalidity P2_1 ⊕ [-p%:num] Ovalidity P2_2)%NNGE)%:num
           = (Ovalidity P1 ⊗ ((Ovalidity P2_1 ⊕ [-p%:num] Ovalidity P2_2)))%NNGE%:num.
        by done.
      rewrite harmonic_p_sum_mulDr //.
      by apply: harmonic_p_sum_both_monotone. 
  - (* Otop *)
    destruct Σ as [| D Σ]; inversion HeqΣAΔ; subst.
    + remember (⊤ `* :: Γ) as HTΓ.
      destruct_Oprv P1 Σ Σ' Δ' D E P1_1 P1_2 P1; try inversion HeqHTΓ.
      * have -> /=: D = ⊥ `* by rewrite -H0 -neg_involutive.
        exists (Otop _). split => //=. by rewrite mul1e.
      * exists (OEFQ _). split => //=. by rewrite mul0e.
      * done.
      * destruct Hcf1 as [Hcf1_1 Hcf1_2].
        apply (cut_adm_mix_switch_case  _ _ IHsz HeqHTΓ P1_1 P1_2 (Otop Δ)) => //=.
        by lia.
      * apply (cut_adm_exch_switch_case  _ _ IHsz HeqHTΓ P1 (Otop Δ)) => //=.
        by lia.
    + have [Heq0|Hneq0] := eqVneq (Ovalidity P1)%:num 0.
      * exists (OEFQ _). split => //=. by rewrite Heq0 mul0e.
      * exists (Otop _). split => //=. rewrite gt0_muley //.
        rewrite lt0e. apply/andP. by split.
Qed.

(** ** Cut Emilination for One- and Two-Sided calculi *)

Corollary Ocut_elimination {Γ: list (@qll_formula R p atoms)} (P: ⊢O Γ):
  exists Q: ⊢O Γ, Ocut_free Q /\ (Ovalidity P <= Ovalidity Q)%O.
Proof.
  induction_Oprv P Σ Γ Δ A B P1 IH1 P2 IH2 P IH => /=;
    try destruct IH1 as [Q1 [HQ1cut HQ1val]]; 
    try destruct IH2 as [Q2 [HQ2cut HQ2val]];
    try destruct IH as [Q [HQcut HQval]].
  - (* OAX *)
    by exists (OAX _).
  - (* OEMP *)
    by exists OEMP.
  - (* OEFQ *)
    by exists (OEFQ _).
  - (* OCUT *)
    (* The interesting case. We need to derive an instance of the cut rule, which
       is achieved via the cut admissibility theorem *)
    move: (Ocut_admissibility Q1 Q2 HQ1cut HQ2cut) => [Q [HQcut HQval]].
    exists Q. split => //. apply: le_trans; last by apply: HQval.
    by apply: lee_pmul.
  - (* OMIX *)
    exists (OMIX _ _ Q1 Q2) => /=. repeat split => //.
    by apply: lee_pmul.
  - (* OEXCH *)
    by exists (OEXCH _ _ _ _ Q).
  - (* Otensor *)
    exists (Otensor _ _ _ _ Q1 Q2) => /=. repeat split => //.
    by apply: lee_pmul.
  - (* Opar *)
    by exists (Opar _ _ _ Q).
  - (* Oone *)
    by exists Oone.
  - (* Oor *)
    exists (Oor _ _ _ Q1 Q2) => /=. repeat split => //.
    by apply: p_sum_both_monotone.
  - (* Oand *)
    exists (Oand _ _ _ Q1 Q2) => /=. repeat split => //.
    by apply: harmonic_p_sum_both_monotone.
  - (* Otop *)
    by exists (Otop _).
Qed.

Theorem cut_elimination {Σ Γ: list (@qll_formula R p atoms)} (P: Σ ⊢ Γ):
  exists Q: Σ ⊢ Γ, cut_free Q /\ (validity P <= validity Q)%O.
Proof.
  (* Proof strategy: Translate P into a one-sided derivation,
     the eliminate the cuts using the theorem for one-sided calculi,
     and then translate the cut-free proof back into the two-sided calculus. *)
  have [Q [-> HQcut]] := two_sided_to_one_sided_trans P.
  have [Q' [HQ'cut HQ'val]] := Ocut_elimination Q.
  have [P' [HP'val HP'cut]] := one_sided_to_two_sided_list_neg_trans Q'.
  exists P'. rewrite -HP'cut -HP'val. by split.
Qed.

End cut_elim.
