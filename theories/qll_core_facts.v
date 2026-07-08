From mathcomp Require Import all_boot all_order ssralg ssrint ssrnum.
From mathcomp Require Import interval interval_inference rat.
From mathcomp Require Import reals constructive_ereal classical_sets ereal.

From QLLib Require Import interval_einference nonneg_ereal qll_defs list_lemmas.

Import Num.Theory GRing.Theory Order.

From Stdlib Require Import List Permutation.

Import ListNotations.

Section basic_facts.

Context {R: realType}.
Context {p: {posnum \bar R}}.
Context {atoms: Type}.

Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope nngereal_scope.
Local Open Scope ereal_scope.
Local Open Scope list_scope.
Local Open Scope qll_calculus.

Lemma neg_involutive (form: @qll_formula R p atoms):
  form = neg (neg form).
Proof.
  by induction form as [a | a | | | | [| | |] A IHA B IHB] => //=;
  cbn; rewrite -IHA -IHB.
Qed.

Lemma proof_le_provability {A} {B} P:
  (@validity R p atoms A B P)%:num <= provability A B.
Proof.
  apply le_ereal_sup_tmp. exists ((validity P)%:nngnum) => //.
  rewrite /provability_set /=. by exists P.
Qed.

End basic_facts.


Section core_deduction_facts.

Context {R: realType}.
Context {p: {posnum \bar R}}.
Context {atoms: Type}.

Open Scope qll_calculus.

Lemma cat_cons_comm X (Σ Γ: list X) A:
  (A :: Σ ++ Γ = (A :: Σ) ++ Γ)%SEQ.
Proof. by []. Qed.

(** ** Exchange lemmas for once-sided calculus *)
Lemma Olist_form_exch_l {Γ Σ Δ: list (@qll_formula R p atoms)} {A}:
  forall P: ⊢O Σ ++ A::Γ ++ Δ, exists Q: ⊢O Σ ++ Γ ++ A::Δ,
    Ovalidity P = Ovalidity Q /\ Ocut_free P = Ocut_free Q.
Proof.
  induction Γ as [| B Γ IHΓ] in Σ |-*; simpl.
  - move => P. by exists P.
  - move => P. rewrite cat_cons_eq_cat_cat.
    pose P' := (OEXCH _ _ _ _ P).
    have ->: Ovalidity P = Ovalidity P' by done.
    have ->: Ocut_free P = Ocut_free P' by done.
    move: P'. rewrite cat_cons_eq_cat_cat => P'.
    destruct (IHΓ _ P') as [Q [HQval HQcut]].  exists Q. by split.
Qed.

Lemma Olist_form_form_exch_l {Γ Σ Δ: list (@qll_formula R p atoms)} {A B}:
  forall P: ⊢O Σ ++ A::B::Γ ++ Δ, exists Q: ⊢O Σ ++ Γ ++ A::B::Δ,
    Ovalidity P = Ovalidity Q /\ Ocut_free P = Ocut_free Q.
Proof.
  move=> P. pose P' := OEXCH _ _ _ _ P.
  have ->: Ovalidity P = Ovalidity P' by done.
  have ->: Ocut_free P = Ocut_free P' by done.
  move: P'. rewrite cat_cons_comm. clear P => P.
  move: (Olist_form_exch_l P) => [Q [-> ->]].
  move: (Olist_form_exch_l Q) => [Q' [-> ->]]. clear P Q.
  by exists Q'.
Qed. 

Lemma Olist_form_exch_r {Γ Σ Δ: list (@qll_formula R p atoms)} {A}:
  forall P: ⊢O Σ ++ Γ ++ A::Δ, exists Q: ⊢O Σ ++ A::Γ ++ Δ,
    Ovalidity P = Ovalidity Q /\ Ocut_free P = Ocut_free Q.
Proof.
  induction Γ as [| B Γ IHΓ] in Σ |-*; simpl.
  - move => P. by exists P.
  - move => P. suff [Q [-> ->]]: exists Q: ⊢O Σ ++ B::A::(Γ ++ Δ),
      Ovalidity P = Ovalidity Q /\ Ocut_free P = Ocut_free Q
      by exists (OEXCH _ _ _ _ Q).
   rewrite cat_cons_eq_cat_cat.
   move: P. rewrite cat_cons_eq_cat_cat => P. 
   by apply IHΓ.
Qed.

Lemma Olist_form_form_exch_r {Γ Σ Δ: list (@qll_formula R p atoms)} {A B}:
  forall P: ⊢O Σ ++ Γ ++ A::B::Δ, exists Q: ⊢O Σ ++ A::B::Γ ++ Δ,
    Ovalidity P = Ovalidity Q /\ Ocut_free P = Ocut_free Q.
Proof.
  move => P.
  move: (Olist_form_exch_r P). rewrite cat_cons_comm. 
  move => [Q [-> ->]].
  move: (Olist_form_exch_r Q) => /= [Q' [-> ->]]. clear P Q.
  by exists (OEXCH _ _ _ _ Q').
Qed. 

Lemma Olist_list_exch {Σ Γ Γ' Δ: list (@qll_formula R p atoms)}:
  forall P: ⊢O Σ ++ Γ ++ Γ' ++ Δ, exists Q: ⊢O Σ ++ Γ' ++ Γ ++ Δ,
    Ovalidity P = Ovalidity Q /\ Ocut_free P = Ocut_free Q.
Proof.
  induction Γ as [|A Γ IHΓ] in Γ' |-*; simpl; move => P; first by exists P.
  destruct (Olist_form_exch_l P) as [Q1 [-> ->]]. 
  move: Q1. rewrite cat_cons_cat_lift -catA => Q1.
  destruct (IHΓ _ Q1) as [Q2 [-> ->]] => /=.
  destruct (Olist_form_exch_l Q2) as [Q3 [-> ->]].
  by exists Q3.
Qed.

Lemma Otwo_list_list_exch {Σ Γ: list (@qll_formula R p atoms)}:
  forall P: ⊢O Σ ++ Γ, exists Q: ⊢O Γ ++ Σ,
    Ovalidity P = Ovalidity Q /\ Ocut_free P = Ocut_free Q.
Proof.
  have ->: (Σ ++ Γ = [] ++ Σ ++ Γ ++ [])%SEQ by rewrite cat0s cats0.
  have ->: (Γ ++ Σ = [] ++ Γ ++ Σ ++ [])%SEQ by rewrite cat0s cats0.
  by apply Olist_list_exch.
Qed.

Lemma list_form_exch_rr {Γ Γ' Σ Δ: list (@qll_formula R p atoms)} {A}:
  forall P: Γ' ⊢ Σ ++ Γ ++ A::Δ, exists Q: Γ' ⊢ Σ ++ A::Γ ++ Δ,
    validity P = validity Q /\ cut_free P = cut_free Q.
Proof.
  induction Γ as [| B Γ IHΓ] in Σ |-*; simpl.
  - move=> P. by exists P.
  - rewrite cat_cons_eq_cat_cat => P.
    move: (IHΓ _ P). rewrite -cat_cons_eq_cat_cat. 
    move => [Q [-> ->]]. by exists (EXCH_R _ _ _ _ _ Q).
Qed.

Lemma list_form_exch_rl {Γ Γ' Σ Δ: list (@qll_formula R p atoms)} {A}:
  forall P: Γ' ⊢ Σ ++ A::Γ ++ Δ, exists Q: Γ' ⊢ Σ ++ Γ ++ A::Δ,
    validity P = validity Q /\ cut_free P = cut_free Q.
Proof.
  induction Γ as [| B Γ IHΓ] in Σ |-*; simpl.
  - move=> P. by exists P.
  - move=> P. pose P' := EXCH_R _ _ _ _ _ P.
    have ->: cut_free P = cut_free P' by done.
    have ->: validity P = validity P' by done.
    move: P'. clear P. rewrite cat_cons_eq_cat_cat => P. 
    move: (IHΓ _ P). rewrite -cat_cons_eq_cat_cat. 
    move => [Q [-> ->]]. by exists Q.
Qed.

Lemma list_list_exch_r {Γ Γ' Σ Σ' Δ: list (@qll_formula R p atoms)}:
  forall P: Γ' ⊢ Σ ++ Σ' ++ Γ ++ Δ, exists Q: Γ' ⊢ Σ ++ Γ ++ Σ' ++ Δ,
    validity P = validity Q /\ cut_free P = cut_free Q.
Proof.
  induction Γ as [| B Γ IHΓ] in Σ |-*; simpl.
  - move=> P. by exists P.
  - move=> P. move: (list_form_exch_rr P). 
    rewrite cat_cons_eq_cat_cat. move=> [Q [-> ->]].
    move: (IHΓ _ Q). rewrite -cat_cons_eq_cat_cat.
    move=> [Q' [-> ->]]. by exists Q'.
Qed.
(* TODO It would be nive to have a lemma as follows. 
   Sadly, in Permutation types, ++ is interpeted as app, whereas
   here (due to using mathcomp), ++ is interpreted as cat 
Lemma perm_exch {Σ: list (@qll_formula R p atoms)}:
  forall P: ⊢O Σ, forall Σ', Permutation Σ Σ' -> exists Q: ⊢O Σ',
    Ovalidity P = Ovalidity Q /\ (Ocut_free P -> Ocut_free Q). *)

(** Equivalence between two- and single-sided calculi for pQLL *)

Fixpoint list_neg (Σ: list (@qll_formula R p atoms)) := match Σ with
  | [] => []
  | A::Σ => A `*::(list_neg Σ)
  end.

Lemma list_neg_catD Σ Γ:
  (list_neg (Σ ++ Γ) = list_neg Σ ++ list_neg Γ)%SEQ.
Proof.
  induction Σ as [| A Σ IHΣ] => //=.
  by rewrite IHΣ.
Qed.

Lemma two_sided_to_one_sided_trans {Σ Γ} (P: Σ ⊢ Γ):
  exists Q: ⊢O (list_neg Σ) ++ Γ, validity P = Ovalidity Q /\
    cut_free P = Ocut_free Q.
Proof.
  induction_prv P Γ Γ' Δ Δ' A B IH1 P1 IH2 P2 IH P' => /=;
    try destruct IH1 as [Q1 [HQ1val HQ1cut]]; 
    try destruct IH2 as [Q2 [HQ2val HQ2cut]];
    try destruct IH as [Q [HQval HQcut]];
    rewrite ?HQ1val ?HQ2val ?HQ1cut ?HQ2cut ?HQval ?HQcut;
    try clear HQ1val HQ1cut HQ2val HQ2cut;
    try clear HQval HQcut.
  - (* AX *) 
    exists (OAX _) => /=. by split.
  - (* EMP *)
    exists OEMP => /=. by split.
  - (* EFQ *)
    exists (OEFQ _) => /=. by split.
  - (* CUT *)
    simpl in Q2. rewrite list_neg_catD.
    suff [Q [-> ->]]: exists Q: ⊢O (list_neg Γ ++ list_neg Γ') ++ Δ' ++ Δ ++ [],
      (Ovalidity Q1 ⊗ Ovalidity Q2)%NNGE = Ovalidity Q /\ False = Ocut_free Q.
      by rewrite -(cats0 ((_ ++ _) ++ _ ++ _)) -!(catA _ _ []);
      destruct (Olist_list_exch Q) as [Q' [-> HQ']]; exists Q'.
    rewrite cats0 catA -(catA _ _ Δ') -catA. exists (OCUT _ _ _ _ Q2 Q1) => //=. 
    by rewrite mulnngeC.
  - (* MIX *)
    rewrite list_neg_catD -catA.
    suff [Q [-> ->]]: exists Q: ⊢O list_neg Γ ++ Δ ++ list_neg Γ' ++ Δ',
      (Ovalidity Q1 ⊗ Ovalidity Q2)%NNGE = Ovalidity Q /\
      (Ocut_free Q1 /\ Ocut_free Q2) = Ocut_free Q.
      by destruct (Olist_list_exch Q) as [Q' [-> ->]];
      exists Q'; split => //=.
    rewrite catA. by exists (OMIX _ _ Q1 Q2).
  - (* tensor_L *)
     by exists (Opar _ _ _ Q).
  - (* tensor_R *)
    move: (@Olist_form_exch_r _ [] _ _ Q1) => [Q1' [-> ->]].
    move: (@Olist_form_exch_r _ [] _ _ Q2) => [Q2' [-> ->]].
    suff [Q [-> ->]]: exists Q : ⊢O A ⊗ B :: (list_neg Γ ++ list_neg Γ') ++ Δ ++ Δ',
      (Ovalidity Q1' ⊗ Ovalidity Q2')%NNGE = Ovalidity Q /\
      (Ocut_free Q1' /\ Ocut_free Q2') = Ocut_free Q.
      by rewrite list_neg_catD; move: (@Olist_form_exch_l _ [] _ _ Q) => [Q' [-> ->]];
      exists Q'.
    rewrite -catA cat_cons_comm.
    pose Q := (Otensor _ _ _ _ Q1' Q2').
    have ->: (Ovalidity Q1' ⊗ Ovalidity Q2')%NNGE = Ovalidity Q by done.
    have ->: (Ocut_free Q1' /\ Ocut_free Q2') = Ocut_free Q by done.
    move: Q. rewrite -catA cat_cons_comm => Q.
    move: (@Olist_list_exch _ _ _ _ Q) => [Q' [-> ->]].
    by exists Q'.
  - (* par_L *)
    rewrite list_neg_catD. simpl in Q1, Q2.
    pose Q := (Otensor _ _ _ _ Q1 Q2).
    have ->: (Ovalidity Q1 ⊗ Ovalidity Q2)%NNGE = Ovalidity Q by done.
    have ->: (Ocut_free Q1 /\ Ocut_free Q2) = Ocut_free Q by done.
    move: Q. rewrite -!catA !cat_cons_comm => Q.
    move: (@Olist_list_exch _ _ _ _ Q) => [Q' [-> ->]].
    by exists Q'.
  - (* par_R *)
    move: Q. rewrite -(cat0s (_ ++ _)) => Q.
    move: (Olist_form_form_exch_r Q) => /= [Q' [-> ->]]. clear Q.
    move: (@Olist_form_exch_l _ [] _ _ (Opar _ _ _ Q')) => /= [Q [-> ->]].
    by exists Q.
  - (* one_L *)
    by exists Oone.
  - (* one_R *)
    by exists Oone.
  - (* neg_L *)
    rewrite -neg_involutive.
    move: (@Olist_form_exch_r _ [] _ _ Q) => /= [Q' [-> ->]].
    by exists Q'.
  - (* neg_R *)
    simpl in Q.
    move: (@Olist_form_exch_l _ [] _ _ Q) => /= [Q' [-> ->]].
    by exists Q'.
  - (* or_L *)
    simpl in Q1, Q2. by exists (Oand _ _ _ Q1 Q2).
  - (* or_R *)
    move: (@Olist_form_exch_r _ [] _ _ Q1) => /= [Q1' [-> ->]].
    move: (@Olist_form_exch_r _ [] _ _ Q2) => /= [Q2' [-> ->]].
    move: (@Olist_form_exch_l _ [] _ _ (Oor _ _ _ Q1' Q2')) => /= [Q [-> ->]].
    by exists Q.
  - (* and_L *)
    simpl in Q1, Q2. by exists (Oor _ _ _ Q1 Q2).
  - (* and_R *)
    move: (@Olist_form_exch_r _ [] _ _ Q1) => /= [Q1' [-> ->]].
    move: (@Olist_form_exch_r _ [] _ _ Q2) => /= [Q2' [-> ->]].
    move: (@Olist_form_exch_l _ [] _ _ (Oand _ _ _ Q1' Q2')) => /= [Q [-> ->]].
    by exists Q.
  - (* bot_L *)
    by exists (Otop _).
  - (* top_R *)
    move: (@Olist_form_exch_l _ [] _ _ (Otop (list_neg Γ ++ Δ))) => /= [Q [-> ->]].
    by exists Q.
  - (* EXCH_L *)
    move: Q. rewrite !list_neg_catD -!catA /= => Q.
    by exists (OEXCH _ _ _ _ Q).
  - (* EXCH_R *)
    move: Q. rewrite !(catA (list_neg Γ) Δ) => Q.
    by exists (OEXCH _ _ _ _ Q).
Qed.

Lemma one_sided_to_two_sided_trans {Σ: list (@qll_formula R p atoms)} (P: ⊢O Σ):
  exists Q: [] ⊢ Σ, Ovalidity P = validity Q /\ (Ocut_free P = cut_free Q).
Proof.
  induction_Oprv P Σ Γ Δ A B P1 IH1 P2 IH2 P IH => /=;
    try destruct IH1 as [Q1 [HQ1val HQ1cut]]; 
    try destruct IH2 as [Q2 [HQ2val HQ2cut]];
    try destruct IH as [Q [HQval HQcut]];
    rewrite ?HQ1val ?HQ2val ?HQ1cut ?HQ2cut ?HQval ?HQcut;
    try clear HQ1val HQ1cut HQ2val HQ2cut;
    try clear HQval HQcut.
  - (* OAX *)
    by exists (neg_R _ _ _ (AX A)).
  - (* OEMP *)
    by exists EMP.
  - (* OEFQ *)
    by exists (EFQ _ _).
  - (* OCUT *)
    move: (@list_form_exch_rr _ _ [] _ _ Q2) => /= [Q2' [-> _]].
    pose Q1' := neg_L _ _ _ Q1.
    have ->: validity Q1 = validity Q1' by done.
    move: Q1'. rewrite -neg_involutive. clear Q1 => Q1.
    pose Q := CUT _ _ _ _ _ Q2' Q1.
    have ->: False = cut_free Q by done.
    have ->: (validity Q1 ⊗ validity Q2')%NNGE = validity Q by rewrite mulnngeC.
    move: Q. have ->: ((Σ ++ Δ) ++ Γ = Σ ++ Δ ++ Γ ++ [])%SEQ. 
      by rewrite cats0 -catA.
    move=> /= Q. move: (list_list_exch_r Q) => [Q' [-> ->]].
    move: Q'. rewrite cats0 => Q'. by exists Q'. 
  - (* OMIX *)
    by exists (MIX _ _ _ _ Q1 Q2).
  - (* OEXCH *)
    by exists (EXCH_R _ _ _ _ _ Q).
  - (* Otensor *)
    by exists (tensor_R _ _ _ _ _ _ Q1 Q2).
  - (* Opar *)
    by exists (par_R _ _ _ _ Q).
  - (* Oone *)
    by exists one_R.
  - (* Oor *)
    by exists (or_R _ _ _ _ Q1 Q2).
  - (* Oand *)
    by exists (and_R _ _ _ _ Q1 Q2).
  - (* Otop *)
    by exists (top_R _ _).
Qed.

Lemma list_neg_push {Σ Γ Δ} (P: Δ ⊢ list_neg Σ ++ Γ):
  exists Q: Σ ++ Δ ⊢ Γ, validity P = validity Q /\ cut_free P = cut_free Q.
Proof.
  move: P. induction Σ as [|A Σ IHΣ] in Γ |-*; simpl; move=> P.
  - by exists P.
  - move: (@list_form_exch_rl _ _ [] _ _ P) => /= [Q [-> ->]].
    move: (IHΣ _ Q) => [Q' [-> ->]].
    have ->: (A :: Σ ++ Δ =  A `* `* :: Σ ++ Δ)%SEQ by rewrite -neg_involutive.
    by exists (neg_L _ _ _ Q').
Qed.

Corollary one_sided_to_two_sided_list_neg_trans {Σ Γ} (P: ⊢O list_neg Σ ++ Γ):
  exists Q: Σ ⊢ Γ, Ovalidity P = validity Q /\ Ocut_free P = cut_free Q.
Proof.
  move: (one_sided_to_two_sided_trans P) => [Q [-> ->]].
  move: (list_neg_push Q). by rewrite cats0.
Qed.

(* Two sided provability and one sided provabilities coincide.
    TODO Prove this. Should follow from the results above *)
(* Theorem one_sided_two_sided_equiv {Σ Γ}:
  provability Σ Γ = Oprovability (list_neg Σ ++ Γ). *)

End core_deduction_facts.


(** ** Towards Completeness of QLL Without Atoms **)
Section rat_completeness_facts.

Context {R: realType}.
Context {atoms: Type}.

Local Open Scope ring_scope.
Local Open Scope rat_scope.
Local Open Scope ereal_scope.
Local Open Scope nngereal_scope.
Local Open Scope qll_calculus.

Lemma ge0_not_gt0_eq0 (q: rat):
  (0 <= q)%R -> (0%R: \bar R) < (ratr q)%:E = false -> q = 0%:R.
Proof.
  move=> Hle0 Hnlt0.
  apply/eqP. move: Hle0. rewrite le0r=> /orP [//|Hcon].
  have Hcon': ((0: \bar R) < (ratr q)%:E)
    by apply lte_tofin; rewrite ltr0q.
  by rewrite Hcon' in Hnlt0.
Qed.

(* Check lt_neqAle. Check eqVneq. *)
Lemma ge0_neq0_gt0r (r: R):
  (0 <= r)%R -> r != 0%R -> (0 < r)%R.
Proof.
  move=> Hgeq0 Hneq0.
  rewrite lt0r. apply/andP. split; last done.
  apply/eqP. move=> H. rewrite H in Hneq0.
  by move: Hneq0=> /eqP.
Qed.

Lemma invr_non0 (r: R):
  r != 0%R -> r^-1%:E = r%:E^-1.
Proof.
  rewrite inver. move=> /eqP Hr0.
  suff ->: r == 0%R = false by done.
  by apply/eqP.
Qed.

Definition False_ind' (T: Type) (x: False): T := match x with end.
Definition atom_func := False_ind' ({nonneg \bar R}).

Lemma mulye_eval_form {p} (f: @qll_formula _ p _) q:
  (0 <= q)%R  -> (ratr q)%:E = (〚 f 〛_ atom_func)%:num
    -> (+oo * (〚 f 〛_ atom_func)%:num = +oo) \/
     (exists p : rat, (0 <= p)%R /\
     (ratr p)%:E = +oo * (〚 f 〛_ atom_func)%:num). 
Proof.
  move => Hq <-. destruct ((0: \bar R) < (ratr q)%:E) eqn:E.
  - left. by rewrite gt0_mulye.
  - right. exists 0%:R. split=> //.
    by rewrite (ge0_not_gt0_eq0 q) // ratr_nat mule0.
Qed.

Lemma addye_eval_form {p} (f: @qll_formula _ p _) q:
  (0 <= q)%R  -> (ratr q)%:E = (〚 f 〛_ atom_func)%:num
    -> ((adde +oo^-1 (〚 f 〛_ atom_func)%:num^-1)^-1 = +oo) \/
     (exists p : rat, (0 <= p)%R /\
     (ratr p)%:E = (adde +oo^-1 (〚 f 〛_ atom_func)%:num^-1)^-1).
Proof.
  move=> Hq <-. rewrite invey.
    destruct ((ratr q)%:E == (0%R: \bar R)) eqn:E'; move: E'=> /eqP Hq0.
    * rewrite Hq0. right. exists 0%:R. split=> //.
      rewrite inve0. have ->: (adde 0%R +oo = 0%R + +oo) by done.
      by rewrite add0e invey ratr_nat.
    * right. exists q. split=> //.
      have ->: (adde 0%R (ratr q)%:E^-1 = 0%R + (ratr q)%:E^-1) by done.
      by rewrite add0e inveK.
Qed.

Lemma ratr_add_inv_switch (p q: rat):
  p != 0%R -> q != 0%R -> (0 <= p)%R -> (0 <= q)%R ->
    (ratr (p^-1%R + q^-1%R)%R^-1)%:E = (@adde R (ratr p)%:E^-1 (ratr q)%:E^-1)^-1.
Proof.
  move=> Hp0 Hq0 Hpgt Hqgt. rewrite rmorphV //=.
  - rewrite -(opprK q^-1%R) ratr_is_additive rmorphN //= opprK. (* There must be a better way *)
    rewrite !rmorphV //= invr_non0.
    * rewrite -(invr_non0 (ratr p)) ?fmorph_eq0 //.
      by rewrite -(invr_non0 (ratr q)) ?fmorph_eq0.
    * by rewrite lt0r_neq0 // addr_gt0 // invr_gt0 lt0r;
        apply /andP; split; rewrite ?ler0q ?fmorph_eq0.
  - by rewrite unitfE lt0r_neq0 // addr_gt0 // invr_gt0 lt0r;
      apply /andP; split.
Qed.

(* some lemmas about adde. This is a workaround, as the underlying properties are proved
   in MathComp-analysis using the "+"-notation instead of adde, and somehow if
   the goal contains is adde a b, one cannot use addeC to rewrite to adde b a.
   We use adde instead of "+" as interval inference does not work property
   with "+", only with adde *) 
Lemma adde_hack (a b: \bar R):
  adde a b = a + b.
Proof. by []. Qed.

Lemma addeC_hack (a b: \bar R):
  adde a b = adde b a.
Proof.
  by rewrite adde_hack addeC.
Qed.

Lemma addye_hack (a: \bar R):
  a != -oo -> adde +oo a = +oo.
Proof.
  move=> Ha. by rewrite adde_hack addye.
Qed.

(** Evaluation of a formula without atoms where all additive connectives
    are annotated by 1 yields a nonnegative rational number or infinity *)
Lemma eval_no_atoms_is_rat (f: @qll_formula R 1%:pos False):
  (〚 f 〛_atom_func)%:num = +oo
    \/ exists q: rat, (0 <= q)%R /\
      (ratr q)%:E = (〚 f 〛_atom_func)%:num.
Proof.
  induction f as [a|a| | | |[| | | ] f1 [IHf1|[p [Hp Hp']]] f2 [IHf2|[q [Hq Hq']]]] => /=.
  - by exfalso.
  - by exfalso.
  - right. exists 1%:R. split => //. by rewrite ratr_nat.
  - right. exists 0%:R. split => //. by rewrite ratr_nat.
  - by left.
  - left. by rewrite IHf1 IHf2.
  - rewrite IHf1. by apply (mulye_eval_form f2 q).
  - rewrite IHf2. rewrite muleC. by apply (mulye_eval_form f1 p).
  - right. exists (p * q)%R. split; first by apply mulr_ge0.
    by rewrite -Hp' -Hq' ratr_is_monoid_morphism.
  - left. by rewrite IHf1 IHf2 invey mule0 inve0.
  - left. by rewrite IHf1 invey mul0e inve0.
  - left. by rewrite IHf2 invey mule0 inve0.
  - have [->|Hf2] := eqVneq (〚 f2 〛_ atom_func)%:num 0%R.
    * rewrite inve0. right.
      exists 0%:R. split=> //. rewrite -Hp'.
      destruct ((ratr p)%:E == (0%R: \bar R)) eqn:E'.
      + have ->: ((ratr p)%:E = (0%R: \bar R)) by apply/eqP.
        by rewrite inve0 gt0_muley // invey ratr_nat.     
      + have Hp0: ((ratr p)%:E != (0%R: \bar R)) by rewrite E'. 
        rewrite gt0_muley; first by rewrite invey ratr_nat.
        rewrite inve_gt0 //. apply lte_tofin. rewrite lt0r.
        apply/andP. split=> //. by rewrite ler0q.
   * right. rewrite -Hp' -Hq'.
     have [->|Hp0] := eqVneq (ratr p)%:E (0%R: \bar R).
     + rewrite inve0. rewrite -Hq' in Hf2.
       exists 0%:R. split=> //.
       rewrite gt0_mulye; first by rewrite invey ratr_nat.
       rewrite inve_gt0 // lte_tofin // lt0r. apply/andP.
       split=> //. by rewrite ler0q.
     + rewrite -Hq' in Hf2. exists (p * q)%R. split; first by apply mulr_ge0.
       rewrite -!invr_non0 //.
       -- by rewrite invf_div invrK mulrC ratr_is_monoid_morphism.
       -- suff /eqP H: (((ratr p)^-1 / ratr q)%R != (0%R :R)).
            by apply/eqP; move=> H'; apply H; rewrite H'.
          by apply lt0r_neq0, mulr_gt0; rewrite invr_gt0;
            apply ge0_neq0_gt0r => //; rewrite ler0q.
  - left. rewrite harmonic_p_sum_1 /= IHf1 IHf2.
    rewrite invey adde_hack.
    by rewrite adde0 inve0. 
  - rewrite harmonic_p_sum_1 /= IHf1. 
    by apply (addye_eval_form _ q).
  - rewrite  harmonic_p_sum_1 /= IHf2 addeC_hack.
    by apply (addye_eval_form _ p).
  - rewrite  harmonic_p_sum_1 /= -Hp' -Hq'. right.
    have [->|Hp0] := eqVneq (ratr p)%:E (0%R: \bar R).
    * rewrite inve0 addye_hack ?inve_eqNy;
        last by rewrite -ltNye ltNyr.
      exists 0%:R. split => //. by rewrite invey ratr_nat.
    * have [->|Hq0] := eqVneq (ratr q)%:E (0%R: \bar R).
      + exists 0%:R. split => //. rewrite inve0 -invr_non0 //.
        rewrite addeC_hack addye_hack; first by rewrite invey ratr_nat.
        by rewrite -ltNye ltNyr.
      + exists ((p^-1 + q^-1)^-1)%R. split.
        -- by rewrite invr_ge0 addr_ge0 // invr_ge0.
        -- by apply ratr_add_inv_switch => //; apply/eqP => H;
             [move: Hp0|move: Hq0]; rewrite H rmorph0 eqxx.
  - rewrite p_sum_1 /= IHf1 IHf2. by left.
  - rewrite p_sum_1 /= IHf1. left.
    by rewrite addye_hack //= -ltNye -Hq' ltNyr.
  - rewrite  p_sum_1 /= IHf2. left.
    by rewrite addeC_hack addye_hack //= -ltNye -Hp' ltNyr.
  - rewrite  p_sum_1 /=. right.
    exists (p + q)%R. split; first by apply addr_ge0.
    rewrite adde_hack -Hp' -Hq'  -(opprK q%R) ratr_is_additive. (* Ugly workaround *)
    by rewrite rmorphN /= !opprK.
Qed.

Lemma eval_le_valid (f: @qll_formula R 1%:pos False):
  exists P: [] ⊢ [f], (〚 f 〛_atom_func)%:num <= (validity P)%:num.
Proof.
  induction f as [a|a| | | |[| | | ] f1 [P1 IH1] f2 [P2 IH2]].
  - by exfalso.
  - by exfalso.
  - by exists one_R.
  - by exists (EFQ [] [⊥]).
  - by exists (top_R _ _).
  - exists (tensor_R _ _ _ _ _ _ P1 P2) => /=.
    by apply (@lee_pmul _ _ _ _ (validity P2)%:nngnum). (* Just applying lee_pmus causes Rocq to diverge or take ages *)
  - pose P := (par_R _ _ _ _ (MIX _ _ _ _ P1 P2)). admit.
 (*   exists P => /=. Check lee_pV2. rewrite lee_pV2; try by rewrite /in_mem /=. 
     by apply (@lee_pmul _ _ _ (validity P2)%:num^-1 _) => //;
       rewrite lee_pV2 //; rewrite /in_mem /=.
  - exists (and_R f1 f2 [] [] P1 P2) => /=. 
    rewrite !harmonic_p_sum_1 /=.
    rewrite lee_pV2; try by rewrite /in_mem /=. 
    by apply (@leeD _ (validity P1)%:num^-1 _ _ _); (* Same, just applying diverges *)
      rewrite lee_pV2; try rewrite /in_mem /=. 
  - exists (or_R f1 f2 [] [] P1 P2) => /=. 
    rewrite !p_sum_1 /=.
    by apply (@leeD _ _ _ _ (validity P2)%:num). *)
Admitted.

Corollary complete_for_rat (f: @qll_formula R 1%:pos False):
  (〚 f 〛_atom_func)%:num <= |/ [] ⊢- [f] |/.
Proof.
  destruct (eval_le_valid f) as [P HP].
  eapply le_trans; first exact HP.
  by apply proof_le_provability.
Qed.

End rat_completeness_facts.
