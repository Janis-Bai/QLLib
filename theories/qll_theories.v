From mathcomp Require Import all_boot all_order ssralg ssrint ssrnum.
From mathcomp Require Import interval interval_inference rat.
From mathcomp Require Import reals constructive_ereal classical_sets ereal.

From QLLib Require Import interval_einference nonneg_ereal qll_defs.
From QLLib Require Import qll_core_facts qll_cut_elim.

Import Order.TTheory GRing.Theory Num.Theory.

From Stdlib Require Import List.

Import ListNotations.

(* Restore mathcomp's seq := list, shadowed by Stdlib's List.seq *)
Notation seq := list.

(** * Theories over pQLL *)
(** Axioms r ≤ Γ ⊢ Δ and theories (sets of axioms) are defined in qll_defs,
    where the calculus is parameterised by a theory. This file provides
    constructions of theories and of derivations in them. *)

(** ** Grounded Theories *)
Section grounded.

Context {R: realType}.
(** The annotation of the additive connectives *)
Context {p: {posnum \bar R}}.
(** The propositional constants the theory may mention *)
Context {V: Type}.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.
Local Open Scope ereal_scope.
Local Open Scope nngereal_scope.
Local Open Scope list_scope.
Local Open Scope qll_calculus.

(** The theory grounded on a valuation v of the propositional constants:
    for every constant a it contains the axioms

      v(a)  ≤  ⊢ a           and          v(a)`*  ≤  a ⊢

    where `* is inversion of nonnegative extended reals. *)
Definition grounded_theory (v: V -> {nonneg \bar R}): @qll_theory R p V :=
  [set (v a ≤ [] ⊢ [atom a]) | a in [set: V]] `|`
  [set (((v a) `*)%NNGE ≤ [atom a] ⊢ []) | a in [set: V]].

(** Membership in a grounded theory, spelled out *)
Lemma grounded_theoryP (v: V -> {nonneg \bar R}) ax:
  grounded_theory v ax <->
  exists a: V, ax = (v a ≤ [] ⊢ [atom a])
            \/ ax = (((v a) `*)%NNGE ≤ [atom a] ⊢ []).
Proof.
  split.
  - by move=> [[a _ <-]|[a _ <-]]; exists a; [left|right].
  - by move=> [a [->|->]]; [left|right]; exists a.
Qed.

(** ** Cut Elimination for Grounded Theories *)
(** The one-sided form of the grounded theory: the axioms v(a) ≤ ⊢ a and
    v(a)`* ≤ a ⊢ become one-sided axioms with sequents [a] and [a`*] *)
Definition Ogrounded_theory (v: V -> {nonneg \bar R}): @Oqll_theory R p V :=
  [set mkOAxiom (v a) [atom a] | a in [set: V]] `|`
  [set mkOAxiom ((v a) `*)%NNGE [neg_atom a] | a in [set: V]].

Lemma Ogrounded_theoryP (v: V -> {nonneg \bar R}) ax:
  Ogrounded_theory v ax <->
  exists a: V, ax = mkOAxiom (v a) [atom a]
            \/ ax = mkOAxiom ((v a) `*)%NNGE [neg_atom a].
Proof.
  split.
  - by move=> [[a _ <-]|[a _ <-]]; exists a; [left|right].
  - by move=> [a [->|->]]; [left|right]; exists a.
Qed.

(** Grounded theories satisfy the hypotheses of the theory-parametric cut
    elimination of qll_cut_elim: the axioms are atomic, and dual axiom
    pairs — v(a) for ⊢ a against v(a)`* for a ⊢ — have validity product
    at most 1, by the inversion bound on nonnegative extended reals. *)
Lemma Ogrounded_atomic (v: V -> {nonneg \bar R}):
  forall ax, Ogrounded_theory v ax ->
  exists a: V, Oax_seq ax = [atom a] \/ Oax_seq ax = [neg_atom a].
Proof.
  by move=> ax /Ogrounded_theoryP [a [->|->]]; exists a; [left|right].
Qed.

Lemma Ogrounded_dual_bound (v: V -> {nonneg \bar R}):
  forall ax ax' (A: @qll_formula R p V),
  Ogrounded_theory v ax -> Ogrounded_theory v ax' ->
  Oax_seq ax = [A] -> Oax_seq ax' = [A `*] ->
  ((Oax_bound ax' ⊗ Oax_bound ax)%NNGE%:num <= 1%:E)%O.
Proof.
  move=> ax ax' A Hax Hax' HA HA'.
  move/Ogrounded_theoryP: Hax => [a [Ea|Ea]]; subst ax;
  move/Ogrounded_theoryP: Hax' => [a' [Ea'|Ea']]; subst ax';
  simpl in HA, HA'; injection HA as HA; subst A; simpl in HA'.
  - (* both positive: impossible *) by discriminate HA'.
  - (* ⊢ a against a ⊢: v(a)`* ⊗ v(a) ≤ 1 *)
    injection HA' as HA'. subst a'. simpl.
    exact: mul_invnnge_le1.
  - (* a ⊢ against ⊢ a: v(a) ⊗ v(a)`* ≤ 1 *)
    injection HA' as HA'. subst a'.
    rewrite mulnngeC. exact: mul_invnnge_le1.
  - (* both negative: impossible *) by discriminate HA'.
Qed.

(** The two hypotheses relating the grounded theory to its one-sided
    form: the compatibility of the axioms with the translation (Prop),
    and the extractable two-sided derivations of the one-sided axioms.
    In the latter, the returned derivation is built from the components
    of the axiom itself — the axiom rule for a positive axiom, negation
    right over the axiom rule for a negative one — so that its validity
    is the axiom's bound definitionally; the memberships are Prop payload
    and do not block the reduction of the witness. *)
Lemma grounded_ax_compat (v: V -> {nonneg \bar R}):
  forall ax, grounded_theory v ax ->
  Ogrounded_theory v (mkOAxiom (ax_bound ax) (list_neg (ax_lhs ax) ++ ax_rhs ax)%SEQ).
Proof.
  by move=> ax /grounded_theoryP [a [->|->]] /=; [left|right]; exists a.
Qed.

Definition grounded_Oax_deriv (v: V -> {nonneg \bar R}):
  forall oax, Ogrounded_theory v oax ->
  {Q: [] ⊢[grounded_theory v] Oax_seq oax |
    Oax_bound oax = validity Q /\ True = cut_free Q}.
Proof.
  move=> oax Hmem. destruct oax as [b s]. simpl.
  destruct s as [|f rest];
    first by exfalso; move/Ogrounded_theoryP: Hmem => [a [Ha|Ha]]; discriminate Ha.
  destruct rest as [|f2 rest];
    last by exfalso; move/Ogrounded_theoryP: Hmem => [a [Ha|Ha]]; discriminate Ha.
  destruct f as [a|a| | | |c f1 f2];
    try by exfalso; move/Ogrounded_theoryP: Hmem => [a' [Ha|Ha]]; discriminate Ha.
  - (* positive axiom: the axiom rule itself *)
    assert (Hm2: grounded_theory v (mkAxiom b [] [atom a])).
    { move/Ogrounded_theoryP: Hmem => [a' [Ha|Ha]]; last by discriminate Ha.
      inversion Ha; subst. apply/grounded_theoryP. exists a'. by left. }
    exists (AXM (mkAxiom b [] [atom a]) Hm2). by split.
  - (* negative axiom: negation right over the axiom rule *)
    assert (Hm2: grounded_theory v (mkAxiom b [atom a] [])).
    { move/Ogrounded_theoryP: Hmem => [a' [Ha|Ha]]; first by discriminate Ha.
      inversion Ha; subst. apply/grounded_theoryP. exists a'. by right. }
    exists (neg_R (atom a) [] [] (AXM (mkAxiom b [atom a] []) Hm2)). by split.
Defined.

(** Cut elimination for grounded theories, with the classical choice
    oracle: the instance of the theory-parametric extractor. An instance
    with computable choices requires computable validities, hence
    rational bounds — cf. the rational oracle of qll_cut_elim. *)
Definition grounded_cut_eliminate (v: V -> {nonneg \bar R}) {Σ Γ}
    (P: Σ ⊢[grounded_theory v] Γ): Σ ⊢[grounded_theory v] Γ :=
  cut_eliminate (Ogrounded_atomic v) (Ogrounded_dual_bound v)
                (grounded_ax_compat v) (grounded_Oax_deriv v) P.

Lemma grounded_cut_eliminate_cut_free (v: V -> {nonneg \bar R}) {Σ Γ}
    (P: Σ ⊢[grounded_theory v] Γ):
  cut_free (grounded_cut_eliminate v P).
Proof. exact: cut_eliminate_cut_free. Qed.

Lemma grounded_cut_eliminate_valid (v: V -> {nonneg \bar R}) {Σ Γ}
    (P: Σ ⊢[grounded_theory v] Γ):
  (validity P <= validity (grounded_cut_eliminate v P))%O.
Proof. exact: cut_eliminate_valid. Qed.

End grounded.




(** ** Derivations of Big Disjunctions of Atoms *)
Section big_or_derivations.

Context {R: realType}.
Context {p: {posnum \bar R}}.
Context {atoms: Type}.
Context {T: @qll_theory R p atoms}.

Local Open Scope ring_scope.
Local Open Scope ereal_scope.
Local Open Scope list_scope.
Local Open Scope qll_calculus.

Local Notation form := (@qll_formula R p atoms).

(** Compact ⋁-left: eliminate a disjunction of atoms given a derivation
    for every disjunct. The hidden leaf closing the empty disjunction is
    bot_L, whose validity +oo is the unit of harmonic p-sums, so the
    validity of the whole derivation is the harmonic p-sum of the
    validities of the premises. *)
Fixpoint foldr_or_L (l: seq atoms) (Δ: list form)
    (Ps: forall e: atoms, ([atom e]: list form) ⊢[T] Δ):
    ([foldr (fun e f => atom e ∨[p] f) ⊥ l]: list form) ⊢[T] Δ :=
  match l with
  | [::] => bot_L [] Δ
  | e :: l' => or_L _ _ [] Δ (Ps e) (foldr_or_L l' Δ Ps)
  end.

(** Compact ⋁-right: dually, introduce a disjunction of atoms given a
    derivation for every disjunct. The hidden leaf is EFQ with validity 0,
    the unit of p-sums, so the validity of the whole derivation is the
    p-sum of the validities of the premises. *)
Fixpoint foldr_or_R (l: seq atoms) (Γ: list form)
    (Ps: forall e: atoms, Γ ⊢[T] [atom e]):
    Γ ⊢[T] [foldr (fun e f => atom e ∨[p] f) ⊥ l] :=
  match l with
  | [::] => EFQ Γ [⊥]
  | e :: l' => or_R _ _ Γ [] (Ps e) (foldr_or_R l' Γ Ps)
  end.

(** Both combinators preserve cut-freeness of their premises *)
Lemma foldr_or_L_cut_free (l: seq atoms) (Δ: list form)
    (Ps: forall e: atoms, ([atom e]: list form) ⊢[T] Δ):
  (forall e, cut_free (Ps e)) -> cut_free (foldr_or_L l Δ Ps).
Proof.
  by move=> HPs; elim: l => //= e l IH.
Qed.

Lemma foldr_or_R_cut_free (l: seq atoms) (Γ: list form)
    (Ps: forall e: atoms, Γ ⊢[T] [atom e]):
  (forall e, cut_free (Ps e)) -> cut_free (foldr_or_R l Γ Ps).
Proof.
  by move=> HPs; elim: l => //= e l IH.
Qed.

End big_or_derivations.

(** * Example: Bayesian Probability *)
Section bayesian_probability.

Context {R: realType}.
(** For the Bayesian reading one takes the annotation p = 1, so that ⊕[1]
    is addition and the validity of a disjunction of outcomes is the sum of
    their probabilities. Nothing below depends on this choice, so we keep
    the annotation generic. *)
Context {p: {posnum \bar R}}.
(** A finite set of outcomes serves as the propositional constants *)
Context {Omega: finType}.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.
Local Open Scope ereal_scope.
Local Open Scope nngereal_scope.
Local Open Scope list_scope.
Local Open Scope qll_calculus.

Local Notation form := (@qll_formula R p Omega).

(** A probability distribution on the outcomes. Neither unitarity
    (∑ pr = 1) nor boundedness (pr ≤ 1) is needed for the construction,
    so we allow arbitrary valuations of the outcomes. *)
Variable pr: Omega -> {nonneg \bar R}.

(** The Bayesian theory of pr is the theory grounded on pr: it asserts
    pr(e) ≤ ⊢ e and pr(e)`* ≤ e ⊢ for every outcome e *)
Definition bayesian_theory: @qll_theory R p Omega := grounded_theory pr.

(** The grounded axioms, used as derivations in the Bayesian theory *)
Definition bayes_axR (e: Omega): ([]: list form) ⊢[bayesian_theory] [atom e].
Proof.
  by apply: (AXM (pr e ≤ [] ⊢ [atom e])); left; exists e.
Defined.

Definition bayes_axL (e: Omega): ([atom e]: list form) ⊢[bayesian_theory] [].
Proof.
  by apply: (AXM (((pr e) `*)%NNGE ≤ [atom e] ⊢ [])); right; exists e.
Defined.

(** An event E ⊆ Ω is expressed by the formula ⋁_{e ∈ E} e, the additive
    disjunction of its outcomes in enumeration order, the empty
    disjunction being ⊥. Since syntactic disjunction is neither
    associative nor commutative, formulas form no monoid and we use a
    fold rather than a bigop. *)
Definition event_formula (E: {set Omega}): form :=
  foldr (fun e f => atom e ∨[p] f) ⊥ (enum E).

(** Sanity check: evaluating the formula of E at a valuation w yields the
    p-sum of w over E, i.e. for p = 1 the mass w assigns to E *)
Lemma eval_event_formula (E: {set Omega}) (w: Omega -> {nonneg \bar R}):
  〚 event_formula E 〛_ w
    = \big[p_sum_de_morgan p%:num/(0%:E%:nng)]_(e <- enum E) w e.
Proof.
  rewrite /event_formula; elim: (enum E) => [|e l IH] /=.
  - by rewrite big_nil.
  - by rewrite big_cons IH.
Qed.

(** The sequents of interest relate two events in the Bayesian theory:
    derivations of D ⊢ E from the grounded axioms, and the associated
    provability, i.e. the sup of validities over them *)
Definition event_sequent (D E: {set Omega}) :=
  ([event_formula D] ⊢[bayesian_theory] [event_formula E]).

Definition event_provability (D E: {set Omega}) :=
  @provability R p Omega bayesian_theory [event_formula D] [event_formula E].


  (* User: the following will probably be refactored later; left only for future ref. *)
(** ** An Example Derivation: A ⊢ A ∩ B *)

(** The leaves of the example tree: a ⊢ b by MIX of the two axioms; its
    validity is the product pr(a)`* ⊗ pr(b) of the axiom bounds *)
Definition MIX_axioms (a b: Omega):
    ([atom a]: list form) ⊢[bayesian_theory] [atom b] :=
  MIX _ _ _ _ (bayes_axL a) (bayes_axR b).

(** The example proof tree deriving A ⊢ A ∩ B:

    ------- axL a    ------- axR b
      a ⊢               ⊢ b
    --------------------------- MIX     ⎤ for every a ∈ A,
              a ⊢ b                     ⎥ harmonic-p-summed
    --------------------------- or_L*   ⎦ by unravelling ⋁A
              A ⊢ b                     ⎤ for every b ∈ A ∩ B,
    --------------------------- or_R*   ⎥ p-summed by
            A ⊢ A ∩ B                   ⎦ unravelling ⋁(A ∩ B)
*)
Definition bayes_example_tree (A B: {set Omega}): event_sequent A (A :&: B) :=
  foldr_or_R (enum (A :&: B)) _
    (fun b => foldr_or_L (enum A) _ (fun a => MIX_axioms a b)).

(** ** Cutting the Example Against ⊢ A, and Cut Elimination *)

(** The direct derivation of ⊢ E: unravel ⋁E on the right, closing each
    disjunct with the grounded axiom ⊢ e. Its validity is the p-sum of pr
    over E — for p = 1, the probability of the event E. *)
Definition bayes_event_tree (E: {set Omega}):
    ([]: list form) ⊢[bayesian_theory] [event_formula E] :=
  foldr_or_R (enum E) [] bayes_axR.

Lemma bayes_event_tree_cut_free (E: {set Omega}):
  cut_free (bayes_event_tree E).
Proof.
  apply: foldr_or_R_cut_free => e. exact: I.
Qed.

(** Cutting the example tree A ⊢ A ∩ B against the direct derivation of
    ⊢ A yields a derivation of ⊢ A ∩ B. Its validity is the product of
    the validities of the two subtrees — for p = 1, the probability of A
    times the conditional-probability-shaped validity of the example. *)
Definition bayes_example_cut_tree (A B: {set Omega}):
    ([]: list form) ⊢[bayesian_theory] [event_formula (A :&: B)] :=
  CUT (event_formula A) [] [] [] [event_formula (A :&: B)]
      (bayes_event_tree A) (bayes_example_tree A B).

(** It is of course not cut-free, being literally a CUT node *)
Remark bayes_example_cut_tree_has_cut (A B: {set Omega}):
  ~ cut_free (bayes_example_cut_tree A B).
Proof. by []. Qed.

(** The tree obtained from the above by cut elimination — the grounded
    instance of the cut elimination theorem applied to the cut tree.
    Reduction trace, in compact form:
    - the cut commutes past the or_R* unravelling of ⋁(A ∩ B), leaving,
      for each b ∈ A ∩ B, a cut of ⊢ ⋁A against ⋁A ⊢ b;
    - these cuts are principal on ⋁A, and the quantitative ∨-reduction
      resolves them into cuts of the axiom ⊢ a against a ⊢ b, which is
      MIX (a ⊢) (⊢ b);
    - commuting into the MIX leaves the axiom-against-axiom cuts
      (⊢ a) vs (a ⊢); these are anchored on the theory and collapse to
      EMP, soundly, since their validity pr(a) ⊗ pr(a)`* is at most
      1 = validity EMP; MIX EMP (⊢ b) is then just the axiom ⊢ b.
    The quantitative guarantee of cut elimination is that validity does
    not decrease along this reduction. *)
Definition bayes_example_cut_free_tree (A B: {set Omega}):
    ([]: list form) ⊢[bayesian_theory] [event_formula (A :&: B)] :=
  grounded_cut_eliminate pr (bayes_example_cut_tree A B).

Lemma bayes_example_cut_free_tree_cut_free (A B: {set Omega}):
  cut_free (bayes_example_cut_free_tree A B).
Proof. exact: grounded_cut_eliminate_cut_free. Qed.

Lemma bayes_example_cut_free_tree_valid (A B: {set Omega}):
  (validity (bayes_example_cut_tree A B)
     <= validity (bayes_example_cut_free_tree A B))%O.
Proof. exact: grounded_cut_eliminate_valid. Qed.

End bayesian_probability.

Notation "⋁ E" := (event_formula E) (at level 35): qll_calculus.
