From Stdlib Require Import List PeanoNat.

From mathcomp Require Import all_boot all_order ssralg ssrint ssrnum rat.
From mathcomp Require Import reals constructive_ereal classical_sets ereal zify.

From QLLib Require Import qll_defs qll_core_facts nonneg_ereal list_lemmas.
From QLLib Require Import qll_rat_validity.

Import Order.TTheory.

Import ListNotations.

(** A transparent strong induction principle on nat. Stdlib's lt_wf_rect
    recurses over accessibility proofs that are sealed by Qed, which
    blocks the reduction of any term defined by it; recursion on an
    explicit fuel bound is structural, so the cut-free proofs extracted
    from the cut elimination theorem below compute. The Peano lemmas
    supplying the bounds are only carried along, never matched, so their
    opacity is harmless. *)
Fixpoint lt_wf_rect_t_aux (fuel: nat) (P: nat -> Type)
    (F: forall n, (forall m, (m < n)%coq_nat -> P m) -> P n)
    {struct fuel}: forall m, (m < fuel)%coq_nat -> P m :=
  match fuel with
  | O => fun m Hm => False_rect (P m) (PeanoNat.Nat.nlt_0_r m Hm)
  | S fuel' => fun m Hm =>
      F m (fun k Hk => lt_wf_rect_t_aux fuel' P F k
        (PeanoNat.Nat.lt_le_trans k m fuel' Hk
           (proj1 (PeanoNat.Nat.lt_succ_r m fuel') Hm)))
  end.

Definition lt_wf_rect_t (n: nat) (P: nat -> Type)
    (F: forall n, (forall m, (m < n)%coq_nat -> P m) -> P n): P n :=
  lt_wf_rect_t_aux (S n) P F n (PeanoNat.Nat.lt_succ_diag_r n).

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

(** Size of proofs, for any one-sided theory *)
Fixpoint pf_size {OT: @Oqll_theory R p atoms} {Γ: list (@qll_formula R p atoms)}
    (P: ⊢O[ OT ] Γ) := match P with
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
  | OAXM _ _ => 1
  end.

Open Scope ring_scope.
Open Scope ereal_scope.

Section theory_parametric.

(** * Theory-Parametric Cut Elimination *)
(** The whole development below is parametric in a one-sided theory OT
    (locally, ⊢O means ⊢O[OT]) subject to two hypotheses: its axioms are
    atomic — their sequents are singleton (negated) propositional
    constants, so no logical rule can have an axiom formula as principal
    formula — and dual axiom pairs have validity product at most 1, so an
    axiom-against-axiom cut soundly collapses to the empty rule. The
    empty theory satisfies both vacuously and recovers the axiom-free
    theorems; grounded theories are the motivating instance. The
    two-sided theorem is additionally parametric in a two-sided theory T
    (locally, ⊢ means ⊢[T]) related to OT by the translation hypotheses
    of qll_core_facts. *)
Context {OT: @Oqll_theory R p atoms}.
Context {T: @qll_theory R p atoms}.

Local Notation "⊢O Γ" := (@Oprv R p atoms OT Γ) (at level 61): qll_calculus.
Local Notation "A ⊢ B" := (@prv R p atoms T A B) (at level 61): qll_calculus.

Hypothesis OT_atomic: forall ax, OT ax ->
  exists a: atoms, Oax_seq ax = [atom a] \/ Oax_seq ax = [neg_atom a].

Hypothesis OT_dual_bound: forall ax ax' (A: @qll_formula R p atoms),
  OT ax -> OT ax' -> Oax_seq ax = [A] -> Oax_seq ax' = [A `*] ->
  ((Oax_bound ax' ⊗ Oax_bound ax)%NNGE%:num <= 1%:E)%O.

Hypothesis ax_compat: forall ax, T ax ->
  OT (mkOAxiom (ax_bound ax) (list_neg (ax_lhs ax) ++ ax_rhs ax)%SEQ).

Hypothesis Oax_deriv: forall oax, OT oax ->
  {Q: [] ⊢ Oax_seq oax | Oax_bound oax = validity Q /\ True = cut_free Q}.

(** ** Inductive Hypotheses for Cut Admissibility Proof *)
Definition IH_form_rk (rk: nat) := forall Σ Γ Δ A (P1: ⊢O A `*::Γ) (P2: ⊢O Σ ++ A::Δ),
   (fm_rank A < rk)%coq_nat ->
   Ocut_free P1 -> Ocut_free P2 ->
   {Q: ⊢O Σ ++ Γ ++ Δ | Ocut_free Q /\
   ((Ovalidity P1 ⊗ Ovalidity P2)%NNGE%:num <= (Ovalidity Q)%:num)%O}.

Definition IH_proof_sz (sz rk: nat) := forall Σ Γ Δ A (P1: ⊢O A `*::Γ) (P2: ⊢O Σ ++ A::Δ),
   (pf_size P1 + pf_size P2 < sz)%coq_nat ->
   (fm_rank A <= rk)%coq_nat ->
   Ocut_free P1 -> Ocut_free P2 ->
   {Q: ⊢O Σ ++ Γ ++ Δ | Ocut_free Q /\
   ((Ovalidity P1 ⊗ Ovalidity P2)%NNGE%:num <= (Ovalidity Q)%:num)%O}.

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
    {Q: ⊢O Σ ++ Γ ++ Δ | Ocut_free Q /\
    ((Ovalidity P1 ⊗ Ovalidity (OEXCH _ _ _ _ P2))%NNGE <= Ovalidity Q)%O}.
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
      (* enough is the stdlib (transparent) counterpart of ssr's suff, whose
         proof term is sealed behind the Qed-opaque ssr_have_upoly (idem below) *)
      enough ({Q: ⊢O Γ' ++ Γ ++ C::Δ' | Ocut_free Q /\
              (Ovalidity P1 ⊗ Ovalidity P2)%NNGE%:num <= (Ovalidity Q)%:num})
        as [Q [HQcut HQval]].
        move: (Olist_form_exch_r Q) => /= [Q' [HQ'val HQ'cut]].
        exists Q' => /=. split; first by rewrite -HQ'cut.
        by rewrite -HQ'val.
      destruct (IHsz _ _ _ _ P1 P2) as [Q [HQcut HQval]] => //=.
      by exists Q.
  - enough ({Q: ⊢O Γ' ++ B :: Γ ++ Δ' | Ocut_free Q /\
              (Ovalidity P1 ⊗ Ovalidity P2)%NNGE%:num <= (Ovalidity Q)%:num})
      as [Q [HQcut HQval]].
        destruct (Olist_form_exch_l Q) as [Q' [HQ'val HQ'cut]].
        exists Q' => /=. split; first by rewrite -HQ'cut.
        by rewrite -HQ'val.
      move: P2 Hcf2 IHsz Hsz => /=. rewrite cat_cons_eq_cat_cat.
      move => P2 Hcf2 IHsz Hsz.
      destruct (IHsz _ _ _ _ P1 P2) as [Q [HQcut HQval]] => //.
      rewrite cat_cons_eq_cat_cat. by exists Q.
Defined.

Lemma cut_adm_exch_switch_case {Σ Γ Γ' Δ C D E} sz rk:
  (IH_proof_sz sz rk) -> (Σ ++ E::D::Δ = C `* :: Γ)%SEQ ->
    forall P1: ⊢O Σ ++ (D::E::Δ), forall P2: ⊢O C :: Γ',
    Ocut_free P1 -> Ocut_free P2 ->
    (pf_size P1 + pf_size P2 < sz)%coq_nat -> (fm_rank C <= rk)%coq_nat ->
    {Q: ⊢O Γ ++ Γ' | Ocut_free Q /\
    (Ovalidity P1)%:nngnum * (Ovalidity P2)%:nngnum <= (Ovalidity Q)%:nngnum}.
Proof.
  rewrite /IH_proof_sz => IHsz Heq P1 P2 Hcf1 Hcf2 Hsz Hrk /=.
  move: P2 IHsz Hcf2 Hsz. rewrite (neg_involutive C) => P2 IHsz Hcf2 Hsz.
  rewrite -(cats0 (_ ++ _)) -catA. (* Workaround, -(cats0 Δ') fails to rewrite *)
  symmetry in Heq. rewrite -(@cat0s _ (C `* :: Γ)) in Heq.
  destruct (cut_adm_exch_case sz rk IHsz Heq P2 P1) as [Q [HQcut HQval]] => //;
    [by lia | by rewrite -rank_neg_invariant |].
  rewrite -(cat0s (_ ++ _ ++ _)).
  move: Q HQcut HQval. rewrite -(cats0 (_ ++ _ ++ _)) -catA -catA => Q HQcut HQval.
  destruct (Olist_list_exch Q) as [Q' [HQ'val HQ'cut]].
  exists Q'. split; first by rewrite -HQ'cut. by rewrite muleC -HQ'val.
Defined.

Lemma cut_adm_mix_case {Σ Γ Δ Σ' Γ' A} sz rk:
  (IH_proof_sz sz rk) -> (Σ' ++ Γ')%SEQ = (Σ ++ A :: Δ)%SEQ ->
    forall P1: ⊢O A`* :: Γ, forall P2_1: ⊢O Σ', forall P2_2: ⊢O Γ',
    Ocut_free P1 -> Ocut_free P2_1 -> Ocut_free P2_2 ->
    (fm_rank A <= rk)%coq_nat -> 
    (pf_size P1 + pf_size P2_1 + pf_size P2_2 < sz)%coq_nat ->
    {Q: ⊢O Σ ++ Γ ++ Δ | Ocut_free Q /\
    ((Ovalidity P1 ⊗ Ovalidity (OMIX _ _ P2_1 P2_2))%NNGE)%:num <= (Ovalidity Q)%:num}.
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
Defined.

Lemma cut_adm_mix_switch_case {Γ Δ Σ' Γ' A} sz rk:
  IH_proof_sz sz rk -> (Σ' ++ Γ')%SEQ = (A`*::Γ)%SEQ ->
    forall P1_1: ⊢O Σ', forall P1_2: ⊢O Γ', forall P2: ⊢O A::Δ,
    Ocut_free P1_1 -> Ocut_free P1_2 -> Ocut_free P2 ->
    (fm_rank A <= rk)%coq_nat -> 
    (pf_size P1_1 + pf_size P1_2 + pf_size P2 < sz)%coq_nat ->
    {Q: ⊢O Γ ++ Δ | Ocut_free Q /\
    ((Ovalidity (OMIX _ _ P1_1 P1_2) ⊗ Ovalidity P2)%NNGE)%:num <= (Ovalidity Q)%:num}.
Proof.
  rewrite /IH_proof_sz => IHsz Heq P1_1 P1_2 P2 Hcf1_1 Hcf1_2 Hcf2 Hsz Hrk /=.
  assert (HAD: A::Δ = (A`*) `*::Δ). by rewrite -neg_involutive.
  destruct (cat_cons_inv _ _ _ _ Heq) as [[Σ HΣ]|[HA HA']]; subst;
  move: P2 Hcf2 Hrk => //; rewrite HAD.
  - move=> P2 Hcf2 Hrk.
    destruct (IHsz [] _ _ _ P2 P1_1) as [Q [HQcut HQval]] => //=;
      [by lia | by rewrite -rank_neg_invariant |].
    inversion Heq. subst.
    pose P := (OMIX _ _ P1_2 Q). simpl in P.
    rewrite -catA -(cat0s (_ ++ _ ++ _)) -(cats0 ([] ++ _)) -catA -catA.
    enough ({Q: ⊢O [] ++ (Γ' ++ Δ) ++ Σ ++ [] | Ocut_free Q /\
      (Ovalidity P1_1)%:num * (Ovalidity P1_2)%:num * (Ovalidity P2)%:num <=
      (Ovalidity Q)%:num}) as [Q' [HQ'cut HQ'val]].
      by destruct (Olist_list_exch Q') as [T0 [HT0val HT0cut]]; exists T0;
      split; [rewrite -HT0cut | rewrite -HT0val].
    rewrite cats0 cat0s -catA. exists P. split => //=.
    rewrite muleC muleA (muleC _ (Ovalidity Q)%:num).
    by apply: lee_pmul.
  - move=> P2 Hcf2 Hrk.
    destruct (IHsz [] _ _ _ P2 P1_2) as [Q [HQcut HQval]] => //=;
      [by lia | by rewrite -rank_neg_invariant |].
    rewrite -(cat0s (_ ++ _)) -(cats0 ([] ++ _)) -catA -catA.
    enough ({Q: ⊢O [] ++ Δ ++ Γ ++ [] | Ocut_free Q /\
      (Ovalidity P1_1)%:num * (Ovalidity P1_2)%:num * (Ovalidity P2)%:num <=
      (Ovalidity Q)%:num}) as [Q' [HQ'cut HQ'val]].
      by destruct (Olist_list_exch Q') as [T0 [HT0val HT0cut]]; exists T0;
      split; [rewrite -HT0cut | rewrite -HT0val].
    rewrite cats0. exists (OMIX _ _ P1_1 Q). split => //=.
    rewrite /= muleC in HQval. rewrite -muleA.
    by apply: lee_pmul.
Defined.

(** ** The Axiom Case *)
(** Cutting a proof of ⊢O A`*, Γ against an axiom with sequent [A]: the
    cut commutes over P1 (through the mix and exchange lemmas above,
    inside the same size induction) until the occurrence of A`* is
    principal, which — the theory being atomic — happens only at an OAX
    leaf, where the axiom itself remains, or at a dual axiom, where the
    axiom-against-axiom cut collapses to the empty rule, soundly by the
    dual-bound hypothesis. *)
Lemma cut_adm_ax_case {Γ A} sz rk b:
  (IH_proof_sz sz rk) -> forall Hmem: OT (mkOAxiom b [A]),
    forall P1: ⊢O A `*::Γ,
    Ocut_free P1 ->
    (pf_size P1 + 1 <= sz)%coq_nat -> (fm_rank A <= rk)%coq_nat ->
    {Q: ⊢O Γ ++ [] | Ocut_free Q /\
    ((Ovalidity P1 ⊗ b)%NNGE%:num <= (Ovalidity Q)%:num)%O}.
Proof.
  move=> IHsz Hmem P1 Hcf1 Hsz Hrk.
  remember (A `*:: Γ) as AΓ.
  destruct_Oprv P1 Σ' Γ' Δ' B C P1_1 P1_2 P1'; try inversion HeqAΓ.
  - (* OAX: the axiom remains *)
    subst.
    assert (HB: B = A). by rewrite (neg_involutive B) (neg_involutive A) H0.
    rewrite HB.
    exists (OAXM (mkOAxiom b [A]) Hmem). split => //=. by rewrite mul1e.
  - (* OEFQ *)
    exists (OEFQ _) => /=. split => //. by rewrite mul0e.
  - (* OCUT *)
    done.
  - (* OMIX: commute; refine, as ssr apply's keyed unification does not
       reduce the Oax_seq projection in the axiom's type *)
    simpl. destruct Hcf1.
    refine (cut_adm_mix_switch_case _ rk IHsz HeqAΓ P1_1 P1_2
             (OAXM (mkOAxiom b [A]) Hmem) _ _ _ _ _); try by [].
    by cbn in Hsz |- *; lia.
  - (* OEXCH: commute *)
    refine (cut_adm_exch_switch_case _ _ IHsz HeqAΓ P1'
             (OAXM (mkOAxiom b [A]) Hmem) _ _ _ _); try by [].
    by cbn in Hsz |- *; lia.
  - (* Otensor: impossible, the axiom formula is atomic *)
    exfalso. destruct (OT_atomic _ Hmem) as [a [Ha|Ha]]; simpl in Ha;
    inversion Ha; subst A; simpl in H0; discriminate H0.
  - (* Opar *)
    exfalso. destruct (OT_atomic _ Hmem) as [a [Ha|Ha]]; simpl in Ha;
    inversion Ha; subst A; simpl in H0; discriminate H0.
  - (* Oone *)
    exfalso. destruct (OT_atomic _ Hmem) as [a [Ha|Ha]]; simpl in Ha;
    inversion Ha; subst A; simpl in H0; discriminate H0.
  - (* Oor *)
    exfalso. destruct (OT_atomic _ Hmem) as [a [Ha|Ha]]; simpl in Ha;
    inversion Ha; subst A; simpl in H0; discriminate H0.
  - (* Oand *)
    exfalso. destruct (OT_atomic _ Hmem) as [a [Ha|Ha]]; simpl in Ha;
    inversion Ha; subst A; simpl in H0; discriminate H0.
  - (* Otop *)
    exfalso. destruct (OT_atomic _ Hmem) as [a [Ha|Ha]]; simpl in Ha;
    inversion Ha; subst A; simpl in H0; discriminate H0.
  - (* OAXM: the axiom-against-axiom cut collapses to the empty rule *)
    destruct B as [b' s']. simpl in HeqAΓ. subst s'.
    destruct Γ as [| g Γ0]; last first.
      exfalso. destruct (OT_atomic _ P1_1) as [a [Ha|Ha]]; simpl in Ha;
      by case: Ha => _ Habs; discriminate Habs.
    exists OEMP. split => //=.
    exact: (OT_dual_bound _ _ A Hmem P1_1 erefl erefl).
Defined.

(** ** The Choice Oracle *)
(** Cut elimination takes two semantic decisions: which branch of an
    ∨-vs-∧ principal cut to keep (the one with the larger validity
    product), and whether a validity is 0 (when cutting against ⊤-R).
    On abstract reals these comparisons are classical; we abstract them
    as an oracle on (products of) validities of subproofs, so that
    instances with computable validities (e.g. rational, for annotation 1)
    can decide them effectively. *)
Section with_choice_oracle.

Variable vcmp: forall (Γ1 Γ2 Γ3 Γ4: list (@qll_formula R p atoms)),
  ⊢O Γ1 -> ⊢O Γ2 -> ⊢O Γ3 -> ⊢O Γ4 -> bool.
Hypothesis vcmpE: forall Γ1 Γ2 Γ3 Γ4
    (P1: ⊢O Γ1) (P2: ⊢O Γ2) (P3: ⊢O Γ3) (P4: ⊢O Γ4),
  vcmp Γ1 Γ2 Γ3 Γ4 P1 P2 P3 P4 =
  ((Ovalidity P1 ⊗ Ovalidity P2)%NNGE%:num
     <= (Ovalidity P3 ⊗ Ovalidity P4)%NNGE%:num)%O.

Variable veq0: forall (Γ: list (@qll_formula R p atoms)), ⊢O Γ -> bool.
Hypothesis veq0E: forall Γ (P: ⊢O Γ), veq0 Γ P = ((Ovalidity P)%:num == 0).

Lemma cut_adm_and_vs_or_case {Γ Δ A B} rk:
  IH_form_rk rk ->
    forall (P1_1: ⊢O A `* :: Γ) (P1_2: ⊢O B `* :: Γ) (P2_1: ⊢O A :: Δ) (P2_2: ⊢O B :: Δ),
    Ocut_free P1_1 -> Ocut_free P1_2 -> Ocut_free P2_1 -> Ocut_free P2_2 ->
    (fm_rank A + fm_rank B < rk)%coq_nat ->
    {Q: ⊢O Γ ++ Δ | Ocut_free Q /\
    ((Ovalidity P1_1 ⊕ [- p%:posnum] Ovalidity P1_2)%NNGE)%:nngnum *
    ((Ovalidity P2_1 ⊕ [p%:posnum] Ovalidity P2_2)%NNGE)%:nngnum <= (Ovalidity Q)%:nngnum}.
Proof.
  rewrite /IH_form_rk => IHrk P1_1 P1_2 P2_1 P2_2 Hcf1_1 Hcf1_2 Hcf2_1 Hcf2_2 Hrk.
  (* A boolean case split on the oracle: the goal is Type-valued, so the
     Prop disjunction produced by orP on le_total may not be destructed;
     going through the oracle moreover lets instances compute the choice.
     The correctness equation vcmpE is only invoked inside the Prop-valued
     haves: rewriting it into the Type-valued goal would plant a transport
     along an opaque proof, blocking the reduction of the witness *)
  case Hle: (vcmp _ _ _ _ P2_1 P1_1 P1_2 P2_2).
  - assert (Hle2: ((Ovalidity P2_1 ⊗ Ovalidity P1_1)%NNGE%:num
        <= (Ovalidity P1_2 ⊗ Ovalidity P2_2)%NNGE%:num)%O).
      by rewrite -(vcmpE _ _ _ _ P2_1 P1_1 P1_2 P2_2) Hle.
    destruct (IHrk [] _ _ _ P1_2 P2_2) as [Q [HQcut HQval]] => //;
      first by lia.
    exists Q. split => //. rewrite muleC.
    eapply le_trans; first by apply: mul_p_sum_le_max_mul.
    eapply le_trans; last by apply HQval.
    simpl. rewrite maxe_translation num_gee_max.
    apply/andP. split => //. by rewrite muleC.
  - assert (Hle2: ((Ovalidity P1_2 ⊗ Ovalidity P2_2)%NNGE%:num
        <= (Ovalidity P2_1 ⊗ Ovalidity P1_1)%NNGE%:num)%O).
      by move: (le_total (Ovalidity P2_1 ⊗ Ovalidity P1_1)%NNGE%:num
                         (Ovalidity P1_2 ⊗ Ovalidity P2_2)%NNGE%:num);
        rewrite -(vcmpE _ _ _ _ P2_1 P1_1 P1_2 P2_2) Hle /=.
    destruct (IHrk [] _ _ _ P1_1 P2_1) as [Q [HQcut HQval]] => //;
      first by lia.
    exists Q. split => //. rewrite muleC.
    eapply le_trans; first by apply: mul_p_sum_le_max_mul.
    eapply le_trans; last by apply HQval.
    simpl. rewrite maxe_translation num_gee_max.
    apply/andP. split => //=; first by rewrite muleC.
    by rewrite (muleC (Ovalidity P2_2)%:num _) (muleC (Ovalidity P1_1)%:num _).
Defined.

Theorem Ocut_admissibility {Σ Γ Δ: list (@qll_formula R p atoms)} {A}:
  forall P1: ⊢O A `*::Γ, forall P2: ⊢O Σ ++ A::Δ, Ocut_free P1 -> Ocut_free P2 ->
    {Q: ⊢O Σ ++ Γ ++ Δ | Ocut_free Q /\ ((Ovalidity P1 ⊗ Ovalidity P2)%NNGE <= Ovalidity Q)%O}.
Proof.
  enough (forall rk sz Σ Γ Δ A (P1: ⊢O A `*::Γ) (P2: ⊢O Σ ++ A::Δ), (fm_rank A <= rk)%coq_nat -> sz = (pf_size P1 + pf_size P2)%N -> Ocut_free P1 -> Ocut_free P2 -> {Q: ⊢O Σ ++ Γ ++ Δ | Ocut_free Q /\ ((Ovalidity P1 ⊗ Ovalidity P2)%NNGE%:num <= (Ovalidity Q)%:num)%O}) as H;
    first by (move=> P1 P2; apply (H (fm_rank A) (pf_size P1 + pf_size P2)%N) => //).
  clear Σ Γ Δ A.
  induction rk as [rk IHrk0] using lt_wf_rect_t.
  assert (IHrk: IH_form_rk rk).
    by move => Σ Γ Δ A P1 P2 Hrk; apply (IHrk0 (fm_rank A) Hrk (pf_size P1 + pf_size P2)%N) => //.
  rewrite /IH_form_rk in IHrk.  clear IHrk0.
  
  induction sz as [sz IHsz0] using lt_wf_rect_t.
  assert (IHsz: IH_proof_sz sz rk).
    by move => Σ Γ Δ A P1 P2 Hsz Hrk; apply (IHsz0 (pf_size P1 + pf_size P2)%N) => //.
  rewrite /IH_proof_sz in IHsz. clear IHsz0.
  move => Σ Γ Δ A P1 P2 Hrk Heqsz Hcf1 Hcf2. subst sz.
  
  remember (Σ ++ A :: Δ)%SEQ as ΣAΔ. destruct_Oprv P2 Σ' Γ' Δ' B C P2_1 P2_2 P2.
  - (* OAX *)
    destruct Σ as [| x Σ]; inversion HeqΣAΔ; subst.
    + move: P1 Hcf1 IHsz. rewrite -(neg_involutive B) => P1 Hcf1 IHsz. (* Workaround *)
      specialize (@Olist_form_exch_l _ _ _ OT Γ [] [] B) as HQ. rewrite cats0 /= in HQ.
      destruct (HQ P1) as [Q [HQval HQcf]]. exists Q. split; first by rewrite -HQcf.
      rewrite /= mule1 HQval. by apply lexx.
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
      * assert (HD: D = B ⊗ C). by rewrite (neg_involutive D) (neg_involutive (B ⊗ C)) H0.
        rewrite HD /=.
        exists (Otensor _ _ _ _ P2_1 P2_2). split => //. by rewrite mul1e.
      * exists (OEFQ _) => /=. split => //. by rewrite mul0e.
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
      * (* OAXM: impossible, the axioms of the theory are atomic *)
        exfalso. destruct (OT_atomic _ P1_1) as [a [Ha|Ha]];
        rewrite Ha in HeqBCΓ; by inversion HeqBCΓ.
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
      * assert (HD: D = B ⊗* C). by rewrite (neg_involutive D) (neg_involutive (B ⊗* C)) H0.
        rewrite HD /=.
        exists (Opar _ _ _ P2). split => //=. by rewrite mul1e.
      * exists (OEFQ _) => /=. split => //. by rewrite mul0e.
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
      * (* OAXM: impossible, the axioms of the theory are atomic *)
        exfalso. destruct (OT_atomic _ P1_1) as [a [Ha|Ha]];
        rewrite Ha in HeqBCΓ; by inversion HeqBCΓ.
    + move: P2 Hcf2 IHsz => /=.
      rewrite -(cat0s (_ :: _)) cat_two_cons_cat_lift cat0s => P2 Hcf2 IHsz.
      destruct (IHsz _ _ _ _ P1 P2) as [Q [HQcut HQval]] => //=; first by lia.
      by exists (Opar _ _ _ Q).
  - (* Oone *)
    destruct Σ as [| B Σ]; inversion HeqΣAΔ; subst.
    + remember (𝟙 `* :: Γ) as OneΓ. 
      destruct_Oprv P1 Σ Σ' Δ' D E P1_1 P1_2 P1; try inversion HeqOneΓ.
      * destruct Γ as [| A Γ]; inversion H1; subst.
        assert (HA: A = 𝟙`*). by rewrite -H0 -neg_involutive.
        rewrite HA.
        simpl. exists Oone. split => //=. rewrite mule1.
        by apply lexx.
      * exists (OEFQ _) => /=. split => //. by rewrite mul0e.
      * done.
      * destruct Hcf1.
        apply (cut_adm_mix_switch_case _ _ IHsz HeqOneΓ P1_1 P1_2 Oone) => //=.
        by lia.
      * apply (cut_adm_exch_switch_case _ _ IHsz HeqOneΓ P1 Oone) => //=.
        by lia.
      * exists OEMP. split => //=. rewrite mule1. 
        by apply lexx.
      * (* OAXM: impossible, the axioms of the theory are atomic *)
        exfalso. destruct (OT_atomic _ P1_1) as [a [Ha|Ha]];
        rewrite Ha in HeqOneΓ; by inversion HeqOneΓ.
    + exfalso. by apply (list_elem_list_emp_inv _ _ _ H1).
  - (* Oor *)
    destruct Σ as [| D Σ]; inversion HeqΣAΔ; subst.
    + remember ((B ∨[_] C) `* :: Γ) as BCΓ.
      destruct_Oprv P1 Σ Σ' Δ' D E P1_1 P1_2 P1; try inversion HeqBCΓ.
      * assert (HD: D = (B ∨[_] C)).
          by rewrite (neg_involutive D) (neg_involutive (B ∨[_] C)) H0.
        rewrite HD /=.
        exists (Oor _ _ _ P2_1 P2_2). split => //. by rewrite mul1e.
      * exists (OEFQ _) => /=. split => //. by rewrite mul0e.
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
      * (* OAXM: impossible, the axioms of the theory are atomic *)
        exfalso. destruct (OT_atomic _ P1_1) as [a [Ha|Ha]];
        rewrite Ha in HeqBCΓ; by inversion HeqBCΓ.
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
      * assert (HD: D = (B ∧[_] C)).
          by rewrite (neg_involutive D) (neg_involutive (B ∧[_] C)) H0.
        rewrite HD /=.
        exists (Oand _ _ _ P2_1 P2_2). split => //. by rewrite mul1e.
      * exists (OEFQ _) => /=. split => //. by rewrite mul0e.
      * done.
      * destruct Hcf1. 
        pose P := Oand _ _ _ P2_1 P2_2.
        apply (cut_adm_mix_switch_case _ _ IHsz HeqBCΓ P1_1 P1_2 P) => //=.
        by lia.
      * pose P := Oand _ _ _ P2_1 P2_2.
        apply (cut_adm_exch_switch_case _ _ IHsz HeqBCΓ P1 P) => //=.
        by lia.
      * subst. simpl in *.
        assert (HBD: B::Δ = (B `*) `* :: Δ). by rewrite -neg_involutive.
        assert (HCD: C::Δ = (C `*) `* :: Δ). by rewrite -neg_involutive.
        move: P2_1 P2_2 Hcf2 IHsz. rewrite HBD HCD.
        move => P2_1 P2_2 Hcf2 IHsz.  destruct Hcf1, Hcf2.
        
        destruct (cut_adm_and_vs_or_case _ IHrk P2_1 P2_2 P1_1 P1_2) as [Q [HQcut HQval]]=> //=;
          first by (rewrite -!rank_neg_invariant; lia).
        destruct (Otwo_list_list_exch Q) as [Q2 [HQ2val HQ2cut]].
        exists Q2. split => /=; first by rewrite -HQ2cut. 
        by rewrite muleC -HQ2val.
      * (* OAXM: impossible, the axioms of the theory are atomic *)
        exfalso. destruct (OT_atomic _ P1_1) as [a [Ha|Ha]];
        rewrite Ha in HeqBCΓ; by inversion HeqBCΓ.
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
      * assert (HD: D = ⊥ `*). by rewrite -H0 -neg_involutive.
        rewrite HD /=.
        exists (Otop _). split => //=. by rewrite mul1e.
      * exists (OEFQ _). split => //=. by rewrite mul0e.
      * done.
      * destruct Hcf1 as [Hcf1_1 Hcf1_2].
        apply (cut_adm_mix_switch_case  _ _ IHsz HeqHTΓ P1_1 P1_2 (Otop Δ)) => //=.
        by lia.
      * apply (cut_adm_exch_switch_case  _ _ IHsz HeqHTΓ P1 (Otop Δ)) => //=.
        by lia.
      * (* OAXM: impossible, the axioms of the theory are atomic *)
        exfalso. destruct (OT_atomic _ P1_1) as [a [Ha|Ha]];
        rewrite Ha in HeqHTΓ; by inversion HeqHTΓ.
    + (* As above, the boolean oracle decides the case split; its
         correctness equation veq0E is only used inside the Prop-valued
         haves *)
      case Hz: (veq0 _ P1).
      * assert (Heq0: (Ovalidity P1)%:num = 0).
          by apply/eqP; rewrite -(veq0E _ P1) Hz.
        exists (OEFQ _). split => //=. by rewrite Heq0 mul0e.
      * assert (Hneq0: (Ovalidity P1)%:num != 0).
          by apply/negbT; rewrite -(veq0E _ P1) Hz.
        exists (Otop _). split => //=. rewrite gt0_muley //.
        rewrite lt0e. apply/andP. by split.
  - (* OAXM: the cut runs into an axiom of the atomic theory. The record
       is destructured so that, once its sequent is substituted, the
       axiom is rebuilt from its own components and everything matches
       definitionally: no transport is needed on the witness path *)
    destruct B as [b s]. simpl in HeqΣAΔ. subst s.
    destruct Σ as [| s0 Σ0]; last first.
      exfalso. destruct (OT_atomic _ P2_1) as [a [Ha|Ha]]; simpl in Ha;
      case: Ha => _ Habs; by destruct Σ0; discriminate Habs.
    destruct Δ as [| d0 Δ0]; last first.
      exfalso. destruct (OT_atomic _ P2_1) as [a [Ha|Ha]]; simpl in Ha;
      by case: Ha => _ Habs; discriminate Habs.
    by refine (cut_adm_ax_case _ rk b IHsz P2_1 P1 _ _ _).
Defined.

(** ** Cut Emilination for One- and Two-Sided calculi *)

Corollary Ocut_elimination {Γ: list (@qll_formula R p atoms)} (P: ⊢O Γ):
  {Q: ⊢O Γ | Ocut_free Q /\ (Ovalidity P <= Ovalidity Q)%O}.
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
  - (* OAXM *)
    by exists (OAXM A P1).
Defined.

Theorem cut_elimination {Σ Γ: list (@qll_formula R p atoms)} (P: Σ ⊢ Γ):
  {Q: Σ ⊢ Γ | cut_free Q /\ (validity P <= validity Q)%O}.
Proof.
  (* Proof strategy: Translate P into a one-sided derivation,
     the eliminate the cuts using the theorem for one-sided calculi,
     and then translate the cut-free proof back into the two-sided calculus.
     The translation equations are kept as hypotheses and only used in the
     Prop component: rewriting them into the Type-valued goal would block
     the reduction of the extracted witness *)
  destruct (two_sided_to_one_sided_trans ax_compat P) as [Q [HQval HQcut]].
  destruct (Ocut_elimination Q) as [Q' [HQ'cut HQ'val]].
  destruct (one_sided_to_two_sided_list_neg_trans Oax_deriv Q') as [P' [HP'val HP'cut]].
  exists P'. split; first by rewrite -HP'cut.
  by rewrite HQval -HP'val.
Defined.

End with_choice_oracle.

(** ** The Classical Oracle *)
(** The classical instance of the oracle: compare the validities
    themselves. This recovers cut elimination for arbitrary annotations,
    with classically decided choices. *)
Definition classical_vcmp {Γ1 Γ2 Γ3 Γ4: list (@qll_formula R p atoms)}
    (P1: ⊢O Γ1) (P2: ⊢O Γ2) (P3: ⊢O Γ3) (P4: ⊢O Γ4): bool :=
  ((Ovalidity P1 ⊗ Ovalidity P2)%NNGE%:num
     <= (Ovalidity P3 ⊗ Ovalidity P4)%NNGE%:num)%O.

Lemma classical_vcmpE Γ1 Γ2 Γ3 Γ4
    (P1: ⊢O Γ1) (P2: ⊢O Γ2) (P3: ⊢O Γ3) (P4: ⊢O Γ4):
  classical_vcmp P1 P2 P3 P4 =
  ((Ovalidity P1 ⊗ Ovalidity P2)%NNGE%:num
     <= (Ovalidity P3 ⊗ Ovalidity P4)%NNGE%:num)%O.
Proof. by []. Qed.

Definition classical_veq0 {Γ: list (@qll_formula R p atoms)} (P: ⊢O Γ): bool :=
  (Ovalidity P)%:num == 0.

Lemma classical_veq0E Γ (P: ⊢O Γ):
  classical_veq0 P = ((Ovalidity P)%:num == 0).
Proof. by []. Qed.

(** As the statements live in Type, the rewritten cut-free proof can be
    extracted as a term, together with its specification *)
Definition Ocut_eliminate {Γ: list (@qll_formula R p atoms)} (P: ⊢O Γ): ⊢O Γ :=
  sval (Ocut_elimination (@classical_vcmp) classical_vcmpE
          (@classical_veq0) classical_veq0E P).

Lemma Ocut_eliminate_cut_free {Γ: list (@qll_formula R p atoms)} (P: ⊢O Γ):
  Ocut_free (Ocut_eliminate P).
Proof. exact: (proj1 (svalP (Ocut_elimination _ _ _ _ P))). Qed.

Lemma Ocut_eliminate_valid {Γ: list (@qll_formula R p atoms)} (P: ⊢O Γ):
  (Ovalidity P <= Ovalidity (Ocut_eliminate P))%O.
Proof. exact: (proj2 (svalP (Ocut_elimination _ _ _ _ P))). Qed.

Definition cut_eliminate {Σ Γ: list (@qll_formula R p atoms)} (P: Σ ⊢ Γ): Σ ⊢ Γ :=
  sval (cut_elimination (@classical_vcmp) classical_vcmpE
          (@classical_veq0) classical_veq0E P).

Lemma cut_eliminate_cut_free {Σ Γ: list (@qll_formula R p atoms)} (P: Σ ⊢ Γ):
  cut_free (cut_eliminate P).
Proof. exact: (proj1 (svalP (cut_elimination _ _ _ _ P))). Qed.

Lemma cut_eliminate_valid {Σ Γ: list (@qll_formula R p atoms)} (P: Σ ⊢ Γ):
  (validity P <= validity (cut_eliminate P))%O.
Proof. exact: (proj2 (svalP (cut_elimination _ _ _ _ P))). Qed.

End theory_parametric.

(** ** The Empty-Theory Instance *)
(** The empty theory has no axioms, so the theory hypotheses hold
    vacuously and the parametric results specialise to the axiom-free
    statements. The instances are explicit transparent terms. *)
Definition set0_atomic: forall ax: @Oqll_axiom R p atoms, set0 ax ->
    exists a: atoms, Oax_seq ax = [atom a] \/ Oax_seq ax = [neg_atom a] :=
  fun ax F => False_ind _ F.

Definition set0_dual_bound: forall (ax ax': @Oqll_axiom R p atoms)
      (A: @qll_formula R p atoms), set0 ax -> set0 ax' ->
    Oax_seq ax = [A] -> Oax_seq ax' = [A `*] ->
    ((Oax_bound ax' ⊗ Oax_bound ax)%NNGE%:num <= 1%:E)%O :=
  fun ax ax' A F => False_ind _ F.

Definition set0_ax_compat: forall ax: @qll_axiom R p atoms, set0 ax ->
    (set0: @Oqll_theory R p atoms)
      (mkOAxiom (ax_bound ax) (list_neg (ax_lhs ax) ++ ax_rhs ax)%SEQ) :=
  fun ax F => False_ind _ F.

Definition set0_Oax_deriv: forall oax: @Oqll_axiom R p atoms, set0 oax ->
    {Q: [] ⊢ Oax_seq oax | Oax_bound oax = validity Q /\ True = cut_free Q} :=
  fun oax F => False_rect _ F.

(** ** The Rational Oracle *)
Section rational_oracle.

(** With annotation 1 — e.g. the Bayesian reading — validities of
    one-sided proofs are extended rationals (Ovalidity_rat_spec), so the
    oracle is implemented by decidable comparisons of extended rationals:
    the branches kept by cut elimination are then decided by rational
    arithmetic over the proof trees rather than by classical comparisons
    of abstract reals. *)
Hypothesis p1: p%:num = 1.

Definition rat_vcmp {Γ1 Γ2 Γ3 Γ4: list (@qll_formula R p atoms)}
    (P1: ⊢O Γ1) (P2: ⊢O Γ2) (P3: ⊢O Γ3) (P4: ⊢O Γ4): bool :=
  ((Ovalidity_rat P1 * Ovalidity_rat P2)%E
     <= (Ovalidity_rat P3 * Ovalidity_rat P4)%E)%O.

Lemma rat_vcmpE Γ1 Γ2 Γ3 Γ4
    (P1: ⊢O Γ1) (P2: ⊢O Γ2) (P3: ⊢O Γ3) (P4: ⊢O Γ4):
  rat_vcmp P1 P2 P3 P4 =
  ((Ovalidity P1 ⊗ Ovalidity P2)%NNGE%:num
     <= (Ovalidity P3 ⊗ Ovalidity P4)%NNGE%:num)%O.
Proof.
  have G1 := Ovalidity_rat_ge0 P1 p1. have G2 := Ovalidity_rat_ge0 P2 p1.
  have G3 := Ovalidity_rat_ge0 P3 p1. have G4 := Ovalidity_rat_ge0 P4 p1.
  rewrite /rat_vcmp /= (Ovalidity_ratE P1 p1) (Ovalidity_ratE P2 p1)
    (Ovalidity_ratE P3 p1) (Ovalidity_ratE P4 p1).
  by rewrite -!ratreM // lee_ratre.
Qed.

Definition rat_veq0 {Γ: list (@qll_formula R p atoms)} (P: ⊢O Γ): bool :=
  Ovalidity_rat P == 0%E.

Lemma rat_veq0E Γ (P: ⊢O Γ): rat_veq0 P = ((Ovalidity P)%:num == 0).
Proof. by rewrite /rat_veq0 (Ovalidity_ratE P p1) ratre_eq0. Qed.

(** Cut elimination with rationally decided choices *)
Definition Ocut_eliminate_rat {Γ: list (@qll_formula R p atoms)} (P: ⊢O Γ): ⊢O Γ :=
  sval (Ocut_elimination set0_atomic set0_dual_bound
          (@rat_vcmp) rat_vcmpE (@rat_veq0) rat_veq0E P).

Lemma Ocut_eliminate_rat_cut_free {Γ: list (@qll_formula R p atoms)} (P: ⊢O Γ):
  Ocut_free (Ocut_eliminate_rat P).
Proof. exact: (proj1 (svalP (Ocut_elimination _ _ _ _ _ _ P))). Qed.

Lemma Ocut_eliminate_rat_valid {Γ: list (@qll_formula R p atoms)} (P: ⊢O Γ):
  (Ovalidity P <= Ovalidity (Ocut_eliminate_rat P))%O.
Proof. exact: (proj2 (svalP (Ocut_elimination _ _ _ _ _ _ P))). Qed.

Definition cut_eliminate_rat {Σ Γ: list (@qll_formula R p atoms)} (P: Σ ⊢ Γ): Σ ⊢ Γ :=
  sval (cut_elimination set0_atomic set0_dual_bound set0_ax_compat set0_Oax_deriv
          (@rat_vcmp) rat_vcmpE (@rat_veq0) rat_veq0E P).

Lemma cut_eliminate_rat_cut_free {Σ Γ: list (@qll_formula R p atoms)} (P: Σ ⊢ Γ):
  cut_free (cut_eliminate_rat P).
Proof. exact: (proj1 (svalP (cut_elimination _ _ _ _ _ _ _ _ P))). Qed.

Lemma cut_eliminate_rat_valid {Σ Γ: list (@qll_formula R p atoms)} (P: Σ ⊢ Γ):
  (validity P <= validity (cut_eliminate_rat P))%O.
Proof. exact: (proj2 (svalP (cut_elimination _ _ _ _ _ _ _ _ P))). Qed.

End rational_oracle.

(** ** Cut Elimination Computes *)
(** The proofs along the witness path are transparent (Defined, stdlib
    assert/enough instead of ssr's Qed-sealed have/suff, fuel recursion
    instead of opaque accessibility), the transports they contain rewrite
    along equality proofs that reduce to erefl on closed lists and
    formulas, and with the rational oracle the two semantic choices are
    decided by rational arithmetic: on a closed derivation, the extracted
    cut-free proof normalises inside Rocq by mere computation. *)
Section computation_tests.

Hypothesis p1: p%:num = 1.

(** A cut on 𝟙 in the one-sided calculus rewrites to the empty rule *)
Example Ocut_eliminate_rat_computes:
  Ocut_eliminate_rat p1 (OCUT 𝟙 [] [] [] Oone Oone) = OEMP.
Proof. by vm_compute. Qed.

(** A principal additive cut: the ∨-vs-∧ reduction is decided by the
    rational oracle, and the chosen branch again rewrites to OEMP *)
Example Ocut_eliminate_rat_computes_additive:
  Ocut_eliminate_rat p1
    (OCUT (𝟙 ∨[p] 𝟙) [] [] []
       (Oand 𝟙 𝟙 [] Oone Oone) (Oor 𝟙 𝟙 [] Oone Oone)) = OEMP.
Proof. by vm_compute. Qed.

(** Cutting against ⊤ consults the zero-test oracle: a cut premise of
    validity 1 keeps the ⊤ rule, one of validity 0 rewrites to EFQ *)
Example Ocut_eliminate_rat_computes_top:
  Ocut_eliminate_rat p1 (OCUT 𝟙 [⊤] [] [] Oone (Otop [𝟙])) = Otop [].
Proof. by vm_compute. Qed.

Example Ocut_eliminate_rat_computes_top_zero:
  Ocut_eliminate_rat p1 (OCUT 𝟙 [⊤] [] [] (OEFQ [𝟙 `*]) (Otop [𝟙]))
  = OEFQ [⊤].
Proof. by vm_compute. Qed.

(** The two-sided extraction computes through the translations as well *)
Example cut_eliminate_rat_computes:
  cut_eliminate_rat p1 (CUT 𝟙 [] [] [] [] one_R one_L) = EMP.
Proof. by vm_compute. Qed.

End computation_tests.

End cut_elim.
