From Stdlib Require Import List Wf_nat.

From mathcomp Require Import all_boot all_order ssralg ssrint ssrnum.
From mathcomp Require Import reals constructive_ereal classical_sets ereal zify.

From QLLib Require Import qll_core wf_rec nonneg_ereal List_more.

Import Order.TTheory.

Import ListNotations.

Section cut_elim.

Context {R: realType}.
Context {p: {posnum \bar R}}.
Context {atoms: Type}.

Open Scope qll_calculus.

(* Variable size: forall {Δ: Corelib.Init.Datatypes.list (@qll_formula R p atoms)}, ⊢O  Δ -> nat. *)

(* Ltac unit_vs_elt_inv H := 
  match type of H with
  | ?a :: nil = ?l1 ++ ?x :: ?l2 =>
      let Hnil1 := fresh in
      let Hnil2 := fresh in
      symmetry in H; apply elt_eq_unit in H as [H [Hnil1 Hnil2]];
      (try subst x); (try subst a); rewrite ?Hnil1; rewrite ?Hnil2 in *;
      clear Hnil1 Hnil2; (try clear l1); (try clear l2)
  | ?l1 ++ ?x :: ?l2 = ?a :: nil =>
      let Hnil1 := fresh in
      let Hnil2 := fresh in
      apply elt_eq_unit in H as [H [Hnil1 Hnil2]];
      (try subst x); (try subst a); rewrite ?Hnil1; rewrite ?Hnil2 in *;
      clear Hnil1 Hnil2; (try clear l1); (try clear l2)
  end. *)


(* Lemma tst {Σ Γ Δ: list (@qll_formula R p atoms)} A:
  ⊢O A `*::Γ -> ⊢O Σ ++ A::Δ -> ⊢O Σ ++ Γ ++ Δ.
Proof.
  move=> P1 P2.
  have H: forall n: nat, (n < size P2)%N -> n = S n. by admit.
  remember (Σ ++ (A :: Δ)%SEQ) as l. destruct P2.
  -  destruct Σ; inversion Heql; subst. simpl. admit.
    
     symmetry in H2. apply elt_eq_unit in H2 as [Hn [Hm Hk]]. rewrite -Hn Hm Hk.
     inversion Heql. rewrite Hm Hk /= in Heql. by rewrite cats0 /=.
  - by destruct Σ; inversion Heql.
  - by apply OEFQ.
Admitted. *)
     

Fixpoint fm_rank (form: @qll_formula R p atoms) := match form with
  | atom _ | neg_atom _ | 𝟙 | ⊥ | ⊤  => 1
  | A ⊗ B | (A ⊗* B) | A ∧[_] B | A ∨[_] B => fm_rank A + fm_rank B + 1
  end.

Lemma rank_neg_invariant A:
  fm_rank A = fm_rank A`*.
Proof.
  by induction A as [a | a | | | | [| | |] A IHA B IHB] => //=; rewrite IHA IHB.
Qed.

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

Fixpoint cut_free {Γ: list (@qll_formula R p atoms)} (P: ⊢O Γ) := match P with
  | OAX _ => True
  | OEMP => True
  | OEFQ _ => True
  | OCUT _ _ _ _ _ _ => False
  | OMIX _ _ P1 P2 => cut_free P1 /\ cut_free P2
  | OEXCH _ _ _ _ P => cut_free P
  | Otensor _ _ _ _ P1 P2 => cut_free P1 /\ cut_free P2
  | Opar _ _ _ P => cut_free P
  | Oone => True
  | Oor _ _ _ P1 P2 => cut_free P1 /\ cut_free P2
  | Oand _ _ _ P1 P2 => cut_free P1 /\ cut_free P2
  | Otop _ => True
end.

Open Scope ring_scope.
Open Scope ereal_scope.

Lemma cat_cons_eq_cat_cat X (Γ Σ: list X) A:
  (Γ ++ A::Σ = (Γ ++ [A]) ++ Σ)%SEQ.
Proof.
  induction Γ as [|B Γ IHΓ]; simpl; first done.
  by rewrite IHΓ.
Qed.

Lemma cat_cons_cat_lift X (Γ Σ Δ: list X) A:
  (Γ ++ A::(Σ ++ Δ) = (Γ ++ (A::Σ)) ++ Δ)%SEQ.
Proof.
  induction Γ as [| C Γ IHΓ]; first done.
  cbn. by rewrite IHΓ.
Qed.

Lemma cat_two_cons_cat_lift X (Γ Σ Δ: list X) A B:
  (Γ ++ A::B::(Σ ++ Δ) = (Γ ++ (A::B::Σ)) ++ Δ)%SEQ.
Proof.
  induction Γ as [| C Γ IHΓ]; first done.
  cbn. by rewrite IHΓ.
Qed.

Lemma list_form_exch_l {Γ Σ Δ: list (@qll_formula R p atoms)} {A}:
  forall P: ⊢O Σ ++ A::Γ ++ Δ, exists Q: ⊢O Σ ++ Γ ++ A::Δ,
    Ovalidity P = Ovalidity Q /\ (cut_free P -> cut_free Q).
Proof.
  induction Γ as [| B Γ IHΓ] in Σ |-*; simpl.
  - move => P. by exists P.
  - move => P. rewrite cat_cons_eq_cat_cat.
    pose P' := (OEXCH _ _ _ _ P).
    have HPval: Ovalidity P = Ovalidity P' by done.
    have HPcut: cut_free P -> cut_free P' by done.
    move: P' HPval HPcut. rewrite cat_cons_eq_cat_cat => P' HPval HPcut.
    destruct (IHΓ _ P') as [Q [HQval HQcut]].  exists Q. split.
    + by rewrite HPval.
    + by move => /HPcut.
Qed.

Lemma list_form_exch_r {Γ Σ Δ: list (@qll_formula R p atoms)} {A}:
  forall P: ⊢O Σ ++ Γ ++ A::Δ, exists Q: ⊢O Σ ++ A::Γ ++ Δ,
    Ovalidity P = Ovalidity Q /\ (cut_free P -> cut_free Q).
Proof.
  induction Γ as [| B Γ IHΓ] in Σ |-*; simpl.
  - move => P. by exists P.
  - move => P. suff [Q [HQval HQcut]]: exists Q: ⊢O Σ ++ B::A::(Γ ++ Δ),
      Ovalidity P = Ovalidity Q /\ (cut_free P -> cut_free Q)
      by exists (OEXCH _ _ _ _ Q).
   rewrite cat_cons_eq_cat_cat.
   move: P. rewrite cat_cons_eq_cat_cat => P. 
   by apply IHΓ.
Qed.

Lemma list_list_exch {Σ Γ Γ' Δ: list (@qll_formula R p atoms)}:
  forall P: ⊢O Σ ++ Γ ++ Γ' ++ Δ, exists Q: ⊢O Σ ++ Γ' ++ Γ ++ Δ,
    Ovalidity P = Ovalidity Q /\ (cut_free P -> cut_free Q).
Proof.
  induction Γ as [|A Γ IHΓ] in Γ' |-*; simpl; move => P; first by exists P.
  destruct (list_form_exch_l P) as [Q1 [HQ1val HQ1cut]]. 
  move: Q1 HQ1val HQ1cut. rewrite cat_cons_cat_lift -catA => Q1 HQ1val HQ1cut.
  destruct (IHΓ _ Q1) as [Q2 [HQ2val HQ2cut]].
  destruct (list_form_exch_l Q2) as [Q3 [HQ3val HQ3cut]].
  exists Q3. split; first by rewrite HQ1val HQ2val.
  by move => /HQ1cut /HQ2cut /=.
Qed.

Lemma two_list_list_exch {Σ Γ: list (@qll_formula R p atoms)}:
  forall P: ⊢O Σ ++ Γ, exists Q: ⊢O Γ ++ Σ,
    Ovalidity P = Ovalidity Q /\ (cut_free P -> cut_free Q).
Proof.
  have ->: (Σ ++ Γ = [] ++ Σ ++ Γ ++ [])%SEQ by rewrite cat0s cats0.
  have ->: (Γ ++ Σ = [] ++ Γ ++ Σ ++ [])%SEQ by rewrite cat0s cats0.
  by apply list_list_exch.
Qed.

Lemma exch_inv X (Γ Δ Γ' Δ': list X) (A B C: X):
  Γ ++ A::Δ = Γ' ++ B::C::Δ' ->
  {Σ & (Γ = Γ' ++ B::C::Σ /\ Δ' = Σ ++ A::Δ)%SEQ}
  + {Σ & (Δ = Σ ++ B::C::Δ' /\ Γ' = Γ ++ A::Σ)%SEQ}
  + (Γ = Γ' ++ [B] /\ A = C /\ Δ = Δ')%SEQ
  + (Δ = C::Δ' /\ A = B /\ Γ = Γ')%SEQ.
Proof.
  induction Γ as [|D Γ IHΓ] in Γ' |-*;
  destruct Γ' as [| E Γ']; simpl; move => Heq.
  - right. inversion Heq. by repeat split => //.
  - left. left. right. inversion Heq. by exists Γ'.
  - inversion Heq; subst. destruct Γ as [| D Γ].
    + inversion H1; subst. left. by right.
    + inversion H1; subst. repeat left. by exists Γ.
  - inversion Heq; subst. 
    destruct (IHΓ _ H1) as [[[[Σ [H2 H3]]|[Σ [H2 H3]]]|[H2 [H3 H4]]]|[H2 [H3 H4]]]; clear IHΓ.
    + repeat left. exists Σ. split => //. by f_equal.
    + left. left. right. exists Σ. split => //. by f_equal.
    + left. right. subst. done.
    + right. subst. done.
Qed.

#[local] Ltac exch_inv_exec_core H p :=
  match type of H with
  | cat _ (cons _ _) = cat _ (cons _ (cons _ _)) => apply exch_inv in H as p
  | (cat _ (cons _ (cons _ _))) = (cat _ (cons _ _)) => symmetry in H;
                                      apply exch_inv in H as p
  | _ => idtac "k"                                                           
  end.

Tactic Notation "exch_inv_tac" hyp(H) "as" simple_intropattern(p) := exch_inv_exec_core H p.
Tactic Notation "exch_inv_tac" hyp(H) :=
  let Σ := fresh "Σ" in
  let Σ' := fresh "Σ'" in
  let H1 := fresh H in
  let H2 := fresh H in
  let H3 := fresh H in
  exch_inv_exec_core H ipattern:([[[[Σ [H1 H2]]|[Σ [H1 H2]]]|[H1 [H2 H3]]]|[H1 [H2 H3]]]).


Lemma cat_cons_inv {X} (Σ Γ Δ: list X) A:
  Σ ++ Δ = A::Γ -> {Σ' & (A::Σ' = Σ)%SEQ} + (Σ = [] /\ Δ = A::Γ).
Proof.
Admitted.

Lemma list_elem_list_emp_inv {X} (Σ Γ: list X) A:
  [] = (Σ ++ A :: Γ) -> False.
Proof.
  move => H.
  by induction Σ; inversion H.
Qed.

Definition IH_form_rk (rk: nat) := forall Σ Γ Δ A (P1: ⊢O A `*::Γ) (P2: ⊢O Σ ++ A::Δ),
   (fm_rank A < rk)%coq_nat ->
   cut_free P1 -> cut_free P2 ->
   exists Q:  ⊢O Σ ++ Γ ++ Δ, cut_free Q /\
   ((Ovalidity P1 ⊗ Ovalidity P2)%NNGE%:num <= (Ovalidity Q)%:num)%O.

Definition IH_proof_sz (sz rk: nat) := forall Σ Γ Δ A (P1: ⊢O A `*::Γ) (P2: ⊢O Σ ++ A::Δ),
   (pf_size P1 + pf_size P2 < sz)%coq_nat ->
   (fm_rank A <= rk)%coq_nat ->
   cut_free P1 -> cut_free P2 ->
   exists Q:  ⊢O Σ ++ Γ ++ Δ, cut_free Q /\
   ((Ovalidity P1 ⊗ Ovalidity P2)%NNGE%:num <= (Ovalidity Q)%:num)%O.

(* We need rk as parameter here:
were we to instantiate IH_proof_sz with (fm_rank A) instead of rk
this lemma would still be provable (with the same proof), but using it in
the cut admissibility lemma below would require lots of boilerplate proof script *) 
Lemma cut_adm_exch_case {Σ Γ Γ' Δ Δ' A B C} sz rk: 
  (IH_proof_sz sz rk) -> (Σ ++ A::Δ = Γ' ++ C::B::Δ')%SEQ ->
    forall (P1: ⊢O A `*::Γ) (P2: ⊢O Γ' ++ B::C::Δ'),
    cut_free P1 -> cut_free P2 ->
    (pf_size P1 + pf_size P2 < sz)%coq_nat -> (fm_rank A <= rk)%coq_nat ->
    exists Q: ⊢O Σ ++ Γ ++ Δ, cut_free Q /\ 
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
      suff [Q [HQcut HQval]]: exists Q: ⊢O Γ' ++ Γ ++ C::Δ', cut_free Q /\
              (Ovalidity P1 ⊗ Ovalidity P2)%NNGE%:num <= (Ovalidity Q)%:num.
        destruct (list_form_exch_r Q) as [Q' [HQ'val HQ'cut]].
        exists Q' => /=. split; first by apply HQ'cut.
        by rewrite -HQ'val.
      destruct (IHsz _ _ _ _ P1 P2) as [Q [HQcut HQval]] => //=.
      by exists Q.
  - suff [Q [HQcut HQval]]: exists Q: ⊢O Γ' ++ B :: Γ ++ Δ', cut_free Q /\
              (Ovalidity P1 ⊗ Ovalidity P2)%NNGE%:num <= (Ovalidity Q)%:num.
        destruct (list_form_exch_l Q) as [Q' [HQ'val HQ'cut]].
        exists Q' => /=. split; first by apply HQ'cut.
        by rewrite -HQ'val.
      move: P2 Hcf2 IHsz Hsz => /=. rewrite cat_cons_eq_cat_cat.
      move => P2 Hcf2 IHsz Hsz.
      destruct (IHsz _ _ _ _ P1 P2) as [Q [HQcut HQval]] => //.
      rewrite cat_cons_eq_cat_cat. by exists Q.
Qed.

Lemma cut_adm_exch_switch_case {Σ Γ Γ' Δ C D E} sz rk:
  (IH_proof_sz sz rk) -> (Σ ++ E::D::Δ = C `* :: Γ)%SEQ ->
    forall P1: ⊢O Σ ++ (D::E::Δ), forall P2: ⊢O C :: Γ',
    cut_free P1 -> cut_free P2 ->
    (pf_size P1 + pf_size P2 < sz)%coq_nat -> (fm_rank C <= rk)%coq_nat ->
    exists Q : ⊢O Γ ++ Γ', cut_free Q /\
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
  destruct (list_list_exch Q) as [Q' [HQ'val HQ'cut]].
  exists Q'. split; first by apply HQ'cut. by rewrite -HQ'val.
Qed.

Lemma cut_adm_mix_case {Σ Γ Δ Σ' Γ' A} sz rk:
  (IH_proof_sz sz rk) -> (Σ' ++ Γ')%SEQ = (Σ ++ A :: Δ)%SEQ ->
    forall P1: ⊢O A`* :: Γ, forall P2_1: ⊢O Σ', forall P2_2: ⊢O Γ',
    cut_free P1 -> cut_free P2_1 -> cut_free P2_2 ->
    (fm_rank A <= rk)%coq_nat -> 
    (pf_size P1 + pf_size P2_1 + pf_size P2_2 < sz)%coq_nat ->
    exists Q: ⊢O Σ ++ Γ ++ Δ, cut_free Q /\
    ((Ovalidity P1 ⊗ Ovalidity (OMIX _ _ P2_1 P2_2))%NNGE)%:num <= (Ovalidity Q)%:num.
Proof.
  rewrite /IH_proof_sz => IHsz Heq P1 P2_1 P2_2 Hcf1 Hcf2_1 Hcf2_2 Hsz Hrk /=.
  dichot_elt_app_inf_exec Heq; subst. 
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
    cut_free P1_1 -> cut_free P1_2 -> cut_free P2 ->
    (fm_rank A <= rk)%coq_nat -> 
    (pf_size P1_1 + pf_size P1_2 + pf_size P2 < sz)%coq_nat ->
    exists Q: ⊢O Γ ++ Δ, cut_free Q /\
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
    suff [Q' [HQ'cut HQ'val]]: exists Q: ⊢O [] ++ (Γ' ++ Δ) ++ Σ ++ [], cut_free Q /\
      (Ovalidity P1_1)%:num * (Ovalidity P1_2)%:num * (Ovalidity P2)%:num <=
      (Ovalidity Q)%:num.
      by destruct (list_list_exch Q') as [T [HTval HTcut]]; exists T;
      split; [apply HTcut | rewrite -HTval].
    rewrite cats0 cat0s -catA. exists P. split => //=.
    rewrite muleC muleA (muleC _ (Ovalidity Q)%:num). 
    by apply: lee_pmul.
  - move=> P2 Hcf2 Hrk.
    destruct (IHsz [] _ _ _ P2 P1_2) as [Q [HQcut HQval]] => //=;
      [by lia | by rewrite -rank_neg_invariant |].
    rewrite -(cat0s (_ ++ _)) -(cats0 ([] ++ _)) -catA -catA.
    suff [Q' [HQ'cut HQ'val]]: exists Q: ⊢O [] ++ Δ ++ Γ ++ [], cut_free Q /\
      (Ovalidity P1_1)%:num * (Ovalidity P1_2)%:num * (Ovalidity P2)%:num <=
      (Ovalidity Q)%:num.
      by destruct (list_list_exch Q') as [T [HTval HTcut]]; exists T;
      split; [apply HTcut | rewrite -HTval].
    rewrite cats0. exists (OMIX _ _ P1_1 Q). split => //=.
    rewrite /= muleC in HQval. rewrite -muleA. 
    by apply: lee_pmul.
Qed.

Lemma cut_adm_and_vs_or_case {Γ Δ A B} rk:
  IH_form_rk rk ->
    forall (P1_1: ⊢O A `* :: Γ) (P1_2: ⊢O B `* :: Γ) (P2_1: ⊢O A :: Δ) (P2_2: ⊢O B :: Δ),
    cut_free P1_1 -> cut_free P1_2 -> cut_free P2_1 -> cut_free P2_2 ->
    (fm_rank A + fm_rank B < rk)%coq_nat ->
    exists Q : ⊢O Γ ++ Δ, cut_free Q /\
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

Lemma cut_admissibility {Σ Γ Δ: list (@qll_formula R p atoms)} A:
  forall P1: ⊢O A `*::Γ, forall P2: ⊢O Σ ++ A::Δ, cut_free P1 -> cut_free P2 ->
    exists Q: ⊢O Σ ++ Γ ++ Δ, cut_free Q /\ ((Ovalidity P1 ⊗ Ovalidity P2)%NNGE <= Ovalidity Q)%O.
Proof.
  enough (forall rk sz Σ Γ Δ A (P1: ⊢O A `*::Γ) (P2: ⊢O Σ ++ A::Δ), (fm_rank A <= rk)%coq_nat -> sz = (pf_size P1 + pf_size P2)%N -> cut_free P1 -> cut_free P2 -> exists Q: ⊢O Σ ++ Γ ++ Δ, cut_free Q /\ ((Ovalidity P1 ⊗ Ovalidity P2)%NNGE%:num <= (Ovalidity Q)%:num)%O) as H;
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
      specialize (@list_form_exch_l Γ [] [] B) as HQ. rewrite cats0 /= in HQ. 
      destruct (HQ P1) as [Q [HQval HQcf]]. exists Q. split; first by apply HQcf.
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
    (* Set Ltac Debug. *)
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
    + dichot_elt_app_inf_exec H1; subst; destruct Hcf2 as [Hcf2_1 Hcf2_2] => /=.
      * destruct (IHsz (B::Σ) _ _ _ P1 P2_1) as [Q [HQcut HQval]] => //=; first by lia.
        rewrite catA catA -(catA Σ). 
        exists (Otensor _ _ (Σ ++ Γ ++ Σ0) _ Q P2_2). split => //=.
        rewrite muleA. by apply: (lee_pmul _ _ HQval _).
      * destruct (IHsz (C::Σ0) _ _ _ P1 P2_2) as [Q [HQcut HQval]] => //=; first by lia.
        rewrite -catA. exists (Otensor _ _ _ (Σ0 ++ Γ ++ Δ) P2_1 Q).
        split => //=. rewrite (muleC (Ovalidity P2_1)%:num _) muleA.
        rewrite (muleC _ (Ovalidity Q)%:num). by apply: (lee_pmul _ _ HQval _).
  -  destruct Σ as [| D Σ]; inversion HeqΣAΔ; subst.
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
        destruct (two_list_list_exch Q) as [Q2 [HQ2val HQ2cut]].
        exists Q2. split => /=; first by apply HQ2cut. 
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
Admitted.
End cut_elim.



(* Obsolote code, remove soon *)

Fixpoint pf_depth {Γ Δ: list (@qll_formula R p atoms)} (P: Γ ⊢ Δ) := match P with
  | AX _ => True
  | EMP => True
  | EFQ _ _ => True
  | CUT _ _ _ _ _ P1 P2 => max (pf_depth P1) (pf_depth P2) + 1
  | MIX_star _ _ _ _ P1 P2 => max (pf_depth P1) (pf_depth P2) + 1
  | tensor_L _ _ _ _ P => pf_depth P + 1
  | tensor_R _ _ _ _ _ _ P1 P2 => max (pf_depth P1) (pf_depth P2) + 1
  | par_L _ _ _ _ _ _ P1 P2 => max (pf_depth P1) (pf_depth P2) + 1
  | par_R _ _ _ _ P => pf_depth P + 1
  | one_L => 1
  | one_R => 1
  | neg_L _ _ _ P => pf_depth P + 1
  | neg_R _ _ _ P => pf_depth P + 1
  | or_L _ _ _ _ P1 P2 => max (pf_depth P1) (pf_depth P2) + 1
  | or_R _ _ _ _ P1 P2 => max (pf_depth P1) (pf_depth P2) + 1
  | and_L _ _ _ _ P1 P2 => max (pf_depth P1) (pf_depth P2) + 1
  | and_R _ _ _ _ P1 P2 => max (pf_depth P1) (pf_depth P2) + 1
  | bot_L => 1
  | top_R => 1
  | EXCH_L _ _ _ _ _ P => pf_depth P + 1
  | EXCH_R _ _ _ _ _ P => pf_depth P + 1
  end.

Fixpoint cut_count {Γ Δ: list (@qll_formula R p atoms)} (P: Γ ⊢ Δ) := match P with
  | AX _ => 0
  | EMP => 0
  | EFQ _ _ => 0
  | CUT _ _ _ _ _ P1 P2 => cut_count P1 + cut_count P2 + 1
  | MIX_star _ _ _ _ P1 P2 => cut_count P1 + cut_count P2
  | tensor_L _ _ _ _ P => cut_count P
  | tensor_R _ _ _ _ _ _ P1 P2 => cut_count P1 + cut_count P2
  | par_L _ _ _ _ _ _ P1 P2 => cut_count P1 + cut_count P2
  | par_R _ _ _ _ P => cut_count P
  | one_L => 0
  | one_R => 0
  | neg_L _ _ _ P => cut_count P
  | neg_R _ _ _ P => cut_count P
  | or_L _ _ _ _ P1 P2 => cut_count P1 + cut_count P2
  | or_R _ _ _ _ P1 P2 => cut_count P1 + cut_count P2
  | and_L _ _ _ _ P1 P2 => cut_count P1 + cut_count P2
  | and_R _ _ _ _ P1 P2 => cut_count P1 + cut_count P2
  | bot_L => 0
  | top_R => 0
  | EXCH_L _ _ _ _ _ P => cut_count P
  | EXCH_R _ _ _ _ _ P => cut_count P
  end.

(* A proof is cut-free if it contains 0 applications of cut *)
Definition cut_free {Γ Δ} (P: Γ ⊢ Δ) := cut_count P = 0.

Fixpoint max_cut_rank {Γ Δ: list (@qll_formula R p atoms)} (P: Γ ⊢ Δ) := match P with
  | AX _ => 0
  | EMP => 0
  | EFQ _ _ => 0
  | CUT A _ _ _ _ P1 P2 => max (fm_rank A) (max (max_cut_rank P1) (max_cut_rank P2))
  | MIX_star _ _ _ _ P1 P2 => max (max_cut_rank P1) (max_cut_rank P2)
  | tensor_L _ _ _ _ P => max_cut_rank P
  | tensor_R _ _ _ _ _ _ P1 P2 => max (max_cut_rank P1) (max_cut_rank P2)
  | par_L _ _ _ _ _ _ P1 P2 => max (max_cut_rank P1) (max_cut_rank P2)
  | par_R _ _ _ _ P => max_cut_rank P
  | one_L => 0
  | one_R => 0
  | neg_L _ _ _ P => max_cut_rank P
  | neg_R _ _ _ P => max_cut_rank P
  | or_L _ _ _ _ P1 P2 => max (max_cut_rank P1) (max_cut_rank P2)
  | or_R _ _ _ _ P1 P2 => max (max_cut_rank P1) (max_cut_rank P2)
  | and_L _ _ _ _ P1 P2 => max (max_cut_rank P1) (max_cut_rank P2)
  | and_R _ _ _ _ P1 P2 => max (max_cut_rank P1) (max_cut_rank P2)
  | bot_L => 0
  | top_R => 0
  | EXCH_L _ _ _ _ _ P => max_cut_rank P
  | EXCH_R _ _ _ _ _ P => max_cut_rank P
  end.

Fixpoint num_cut_rank {Γ Δ: list (@qll_formula R p atoms)} r (P: Γ ⊢ Δ) := match P with
  | AX _ => 0
  | EMP => 0
  | EFQ _ _ => 0
  | CUT A _ _ _ _ P1 P2 => (if r == fm_rank A then 1 else 0) + num_cut_rank r P1 + num_cut_rank r P2
  | MIX_star _ _ _ _ P1 P2 => num_cut_rank r P1 + num_cut_rank r P2
  | tensor_L _ _ _ _ P => num_cut_rank r P
  | tensor_R _ _ _ _ _ _ P1 P2 => num_cut_rank r P1 + num_cut_rank r P2
  | par_L _ _ _ _ _ _ P1 P2 => num_cut_rank r P1 + num_cut_rank r P2
  | par_R _ _ _ _ P => num_cut_rank r P
  | one_L => 0
  | one_R => 0
  | neg_L _ _ _ P => num_cut_rank r P
  | neg_R _ _ _ P => num_cut_rank r P
  | or_L _ _ _ _ P1 P2 => num_cut_rank r P1 + num_cut_rank r P2
  | or_R _ _ _ _ P1 P2 => num_cut_rank r P1 + num_cut_rank r P2
  | and_L _ _ _ _ P1 P2 => num_cut_rank r P1 + num_cut_rank r P2
  | and_R _ _ _ _ P1 P2 => num_cut_rank r P1 + num_cut_rank r P2
  | bot_L => 0
  | top_R => 0
  | EXCH_L _ _ _ _ _ P => num_cut_rank r P
  | EXCH_R _ _ _ _ _ P => num_cut_rank r P
  end.

Definition num_max_cut_rank {Γ Δ: list (@qll_formula R p atoms)} (P: Γ ⊢ Δ) := num_cut_rank (max_cut_rank P) P.

Fixpoint cut_depths_sum {Γ Δ: list (@qll_formula R p atoms)} (P: Γ ⊢ Δ) := match P with
  | AX _ => 0
  | EMP => 0
  | EFQ _ _ => 0
  | CUT A _ _ _ _ P1 P2 => cut_depths_sum P1 + cut_depths_sum P2 + pf_depth P
  | MIX_star _ _ _ _ P1 P2 => cut_depths_sum P1 + cut_depths_sum P2
  | tensor_L _ _ _ _ P => cut_depths_sum P
  | tensor_R _ _ _ _ _ _ P1 P2 => cut_depths_sum P1 + cut_depths_sum P2
  | par_L _ _ _ _ _ _ P1 P2 => cut_depths_sum P1 + cut_depths_sum P2
  | par_R _ _ _ _ P => cut_depths_sum P
  | one_L => 0
  | one_R => 0
  | neg_L _ _ _ P => cut_depths_sum P
  | neg_R _ _ _ P => cut_depths_sum P
  | or_L _ _ _ _ P1 P2 => cut_depths_sum P1 + cut_depths_sum P2
  | or_R _ _ _ _ P1 P2 => cut_depths_sum P1 + cut_depths_sum P2
  | and_L _ _ _ _ P1 P2 => cut_depths_sum P1 + cut_depths_sum P2
  | and_R _ _ _ _ P1 P2 => cut_depths_sum P1 + cut_depths_sum P2
  | bot_L => 0
  | top_R => 0
  | EXCH_L _ _ _ _ _ P => cut_depths_sum P
  | EXCH_R _ _ _ _ _ P => cut_depths_sum P
  end.

Definition cut_elim_order {Γ Δ: list (@qll_formula R p atoms)} (P Q: Γ ⊢ Δ) :=
  four_lex_explicit lt lt lt lt (max_cut_rank P, num_max_cut_rank P, cut_count P, cut_depths_sum P)
     (max_cut_rank Q, num_max_cut_rank Q, cut_count Q, cut_depths_sum Q).

Lemma cut_elim_order_wf {Γ Δ: list (@qll_formula R p atoms)}:
  well_founded (@cut_elim_order Γ Δ).
Proof.
  unfold cut_elim_order.
  pose H := (well_founded_retract _ (fun P => (max_cut_rank P, num_max_cut_rank P, cut_count P, cut_depths_sum P)) well_founded_nat_quadruple).
  by apply H.
Defined. 

End size_functions.


Section elimination_lemmas.

Context {R: realType}.
Context {p: {nonneg \bar R}}.
Context {atoms: Type}.

Open Scope list_scope.
Open Scope ereal_scope.
Open Scope nngereal_scope.
Open Scope qll_calculus.

(** ** Structural Rules *)

Lemma AX_vs_hypothesis {Γ Δ: list (@qll_formula R p atoms)} {A} (P: A::Γ ⊢ Δ):
  (exists Q, P = CUT A [A] Γ [] Δ (AX A) Q)
  -> exists Q: A::Γ ⊢ Δ, validity Q = validity P /\ (cut_count Q < cut_count P)%N.
Proof. 
  move=> [Q ->]. exists Q => /=. split; last by lia.
  apply/val_inj => /=. by rewrite mul1e.
Defined.

Lemma tst {Γ Δ: list (@qll_formula R p atoms)} (P: Γ ⊢ Δ):
  False.
Proof.
  destruct P.
  - admit.
  - admit.
  - admit.
  - admit.
  - 




End elimination_lemmas.
