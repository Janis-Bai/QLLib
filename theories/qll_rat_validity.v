From mathcomp Require Import all_boot all_order ssralg ssrint ssrnum rat.
From mathcomp Require Import interval interval_inference.
From mathcomp Require Import reals constructive_ereal classical_sets ereal.

From QLLib Require Import interval_einference nonneg_ereal qll_defs.

Import Order.TTheory GRing.Theory Num.Theory.

From Stdlib Require Import List.

Import ListNotations.

(* Restore mathcomp's seq := list, shadowed by Stdlib's List.seq *)
Notation seq := list.

(** * Rational Validity of One-Sided Proofs *)
(** In the (axiom-free) one-sided calculus with additive annotation p = 1,
    validities are extended nonnegative rationals: the leaves have validity
    0, 1 or +oo, and the rules combine validities by multiplication, sums
    (⊕[1]) and harmonic sums (⊕[-1]), all of which preserve rationality.
    This file computes the rational representative of a validity, which
    makes comparisons of validities decidable. *)

Section rat_validity.

Context {R: realType}.
Context {p: {posnum \bar R}}.
Context {atoms: Type}.

Local Open Scope ring_scope.
Local Open Scope ereal_scope.
Local Open Scope nngereal_scope.
Local Open Scope qll_calculus.

(** ** Embedding of Extended Rationals into Extended Reals *)
Definition ratre (x: \bar rat): \bar R :=
  match x with
  | EFin q => (ratr q)%:E
  | +oo%E => +oo
  | -oo%E => -oo
  end.

Fact le0Ny_rat: (0 <= (-oo: \bar rat))%E = false.
Proof. by []. Qed.

(** Reduction equations, needed as ratre applications do not always reduce
    where we rewrite *)
Lemma ratreE (q: rat): ratre q%:E = (ratr q)%:E.
Proof. by []. Qed.

Lemma ratrey: ratre +oo%E = +oo.
Proof. by []. Qed.

Lemma ratreNy: ratre -oo%E = -oo.
Proof. by []. Qed.

Lemma ratre0: ratre 0 = 0.
Proof. by rewrite /= rmorph0. Qed.

Lemma ratre1: ratre 1 = 1.
Proof. by rewrite /= rmorph1. Qed.

(** The embedding is an order embedding *)
Lemma lee_ratre (x y: \bar rat): (ratre x <= ratre y) = (x <= y)%E.
Proof.
  by case: x => [qx||]; case: y => [qy||] => //;
    rewrite ?ratreE ?ratrey ?ratreNy ?leey ?leNye // !lee_fin ler_rat.
Qed.

Lemma ratre_eq0 (x: \bar rat): (ratre x == 0) = (x == 0%E).
Proof.
  by case: x => [q||] => //;
    rewrite ?ratreE ?ratrey ?ratreNy // !eqe fmorph_eq0.
Qed.

Lemma ratre_ge0 (x: \bar rat): (0 <= ratre x) = (0 <= x)%E.
Proof. by rewrite -[in LHS]ratre0 lee_ratre. Qed.

(** adde and the + notation denote convertible but syntactically distinct
    terms (cf. the adde_hack workaround in qll_core_facts); the p-sum
    lemmas expose adde, so we state additivity in terms of adde *)
Lemma addeE (S: numDomainType) (a b: \bar S): adde a b = (a + b)%E.
Proof. by []. Qed.

(** The embedding commutes with the operations combining validities *)
Lemma ratreD (x y: \bar rat): ratre (x + y)%E = adde (ratre x) (ratre y).
Proof.
  by case: x => [qx||]; case: y => [qy||] => //;
    rewrite !addeE -EFinD !ratreE rmorphD EFinD.
Qed.

Lemma ratreM (x y: \bar rat):
  (0 <= x)%E -> (0 <= y)%E -> ratre (x * y)%E = ratre x * ratre y.
Proof.
  case: x => [qx||]; case: y => [qy||] => Hx Hy //;
    try by [move: Hx; rewrite le0Ny_rat | move: Hy; rewrite le0Ny_rat].
  - by rewrite -EFinM !ratreE rmorphM EFinM.
  - move: Hx; rewrite lee_fin le_eqVlt => /orP [/eqP <-|Hx].
    + by rewrite mul0e !ratreE ratrey !rmorph0 mul0e.
    + have Hq: (0: \bar rat) < qx%:E by rewrite lte_fin.
      have HqR: (0: \bar R) < (ratr qx)%:E by rewrite lte_fin ltr0q.
      by rewrite !ratreE ratrey !gt0_muley.
  - move: Hy; rewrite lee_fin le_eqVlt => /orP [/eqP <-|Hy].
    + by rewrite mule0 !ratreE ratrey !rmorph0 mule0.
    + have Hq: (0: \bar rat) < qy%:E by rewrite lte_fin.
      have HqR: (0: \bar R) < (ratr qy)%:E by rewrite lte_fin ltr0q.
      by rewrite !ratreE ratrey !gt0_mulye.
Qed.

Lemma ratreV (x: \bar rat):
  (0 <= x)%E -> ratre (x^-1)%E = (ratre x)^-1.
Proof.
  case: x => [q||] => Hx //;
    try by move: Hx; rewrite le0Ny_rat.
  - rewrite !ratreE !inver fmorph_eq0.
    by case: (q == 0%R) => //=; rewrite fmorphV.
  - by rewrite ratrey !invey /= rmorph0.
Qed.

(** ** The Rational Mirror of Ovalidity *)
Fixpoint Ovalidity_rat {Γ: list (@qll_formula R p atoms)} (P: ⊢O Γ): \bar rat :=
  match P with
  | OAX _ => 1%E
  | OEMP => 1%E
  | OEFQ _ => 0%E
  | OCUT _ _ _ _ P1 P2 => (Ovalidity_rat P1 * Ovalidity_rat P2)%E
  | OMIX _ _ P1 P2 => (Ovalidity_rat P1 * Ovalidity_rat P2)%E
  | OEXCH _ _ _ _ P => Ovalidity_rat P
  | Otensor _ _ _ _ P1 P2 => (Ovalidity_rat P1 * Ovalidity_rat P2)%E
  | Opar _ _ _ P => Ovalidity_rat P
  | Oone => 1%E
  | Oor _ _ _ P1 P2 => (Ovalidity_rat P1 + Ovalidity_rat P2)%E
  | Oand _ _ _ P1 P2 =>
      (((Ovalidity_rat P1)^-1 + (Ovalidity_rat P2)^-1)^-1)%E
  | Otop _ => +oo%E
  (* dead branch: the empty theory has no axioms *)
  | OAXM _ _ => 0%E
  end.

(** For annotation 1, the rational mirror represents the validity, and it
    is nonnegative (the two statements are proven simultaneously, as the
    morphism properties of the embedding require nonnegativity) *)
Lemma Ovalidity_rat_spec {Γ: list (@qll_formula R p atoms)} (P: ⊢O Γ):
  p%:num = 1 ->
  ((Ovalidity P)%:num = ratre (Ovalidity_rat P)) /\ (0 <= Ovalidity_rat P)%E.
Proof.
  move=> p1.
  induction_Oprv P Σ Γ' Δ A B P1 IH1 P2 IH2 P0 IH => /=;
    try destruct IH1 as [E1 G1];
    try destruct IH2 as [E2 G2];
    try destruct IH as [E G].
  - (* OAX *) by split; [rewrite rmorph1|].
  - (* OEMP *) by split; [rewrite rmorph1|].
  - (* OEFQ *) by split; [rewrite rmorph0|].
  - (* OCUT *) by split; [rewrite E1 E2 ratreM | apply: mule_ge0].
  - (* OMIX *) by split; [rewrite E1 E2 ratreM | apply: mule_ge0].
  - (* OEXCH *) by split.
  - (* Otensor *) by split; [rewrite E1 E2 ratreM | apply: mule_ge0].
  - (* Opar *) by split.
  - (* Oone *) by split; [rewrite rmorph1|].
  - (* Oor *)
    split; last by apply: adde_ge0.
    by rewrite p1 p_sum_1 /= E1 E2 ratreD.
  - (* Oand *)
    have Hinv: (0 <= (Ovalidity_rat P1)^-1 + (Ovalidity_rat P2)^-1)%E.
      by apply: adde_ge0; rewrite inve_ge0.
    split; last by rewrite inve_ge0.
    rewrite p1 harmonic_p_sum_1 /= E1 E2.
    by rewrite -(ratreV _ G1) -(ratreV _ G2) -ratreD -(ratreV _ Hinv).
  - (* Otop *) by split.
  - (* OAXM: vacuous, as the theory is empty *) by case: P1.
Qed.

Corollary Ovalidity_ratE {Γ: list (@qll_formula R p atoms)} (P: ⊢O Γ):
  p%:num = 1 -> (Ovalidity P)%:num = ratre (Ovalidity_rat P).
Proof. by move=> p1; have [] := Ovalidity_rat_spec P p1. Qed.

Corollary Ovalidity_rat_ge0 {Γ: list (@qll_formula R p atoms)} (P: ⊢O Γ):
  p%:num = 1 -> (0 <= Ovalidity_rat P)%E.
Proof. by move=> p1; have [] := Ovalidity_rat_spec P p1. Qed.

End rat_validity.
