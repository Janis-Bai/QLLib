From Stdlib Require Import List.

From mathcomp Require Import all_boot all_order ssralg ssrint ssrnum.
From mathcomp Require Import interval interval_inference rat.
From mathcomp Require Import reals constructive_ereal classical_sets ereal.

From QLLib Require Import interval_einference nonneg_ereal.

Import Order.TTheory GRing.Theory Num.Theory.

Import ListNotations.

Declare Scope qll_calculus.
Delimit Scope qll_calculus with QLLC.

(* Type of all extended reals in interval i, somehow not yet in the library *)
(* TODO What is phant actually? *)
Definition itvnume (R : numDomainType) (i: interval int) & phant R :=
  Itv.def (@ext_num_sem R) (Itv.Real i).

Notation "{ 'itv' \bar R & i }" := (itvnume R i (Phant R)) : qll_calculus.

Section syntax.

Open Scope qll_calculus.

(* Quantifying this type over an interval allows us to prove completeness for the
   rationals where the and/or connectives are only annotated by 1.
   For general Capucci Logic, the interval used for i will be `[0,+oo] *) 
Inductive qll_connective {R: realType} {i: interval int}: Type :=
| tensor: qll_connective
| par: qll_connective
| add_and: {itv \bar R & i} -> qll_connective
| add_or: {itv \bar R & i} -> qll_connective.

Inductive qll_formula {R: realType} {i: interval int} {atoms: Type}: Type :=
| atom: atoms -> qll_formula
| neg_atom: atoms -> qll_formula
| one: qll_formula
| bot: qll_formula
| top: qll_formula
| bin: @qll_connective R i -> qll_formula -> qll_formula -> qll_formula.

End syntax.

(* TODO: Discuss notation levels and make them appropriate *)
Notation "A ⊗ B" := (@bin _ _ _ tensor A B) (at level 46, left associativity): qll_calculus.
Notation "A ⊗* B" := (@bin _ _ _ par A B) (at level 46, left associativity): qll_calculus.
Notation "A ∧[ p ] B" := (@bin _ _ _ (add_and p) A B) (at level 47, left associativity): qll_calculus.
Notation "A ∨[ p ] B" := (@bin _ _ _ (add_or p) A B) (at level 48, left associativity): qll_calculus.
Notation "⊥" := (@bot _ _ _): qll_calculus.
Notation "⊤" := (@top _ _ _): qll_calculus.
Notation "𝟙" := (@one _ _ _): qll_calculus.

Section negation.

Local Open Scope ring_scope.
Local Open Scope ereal_scope.
Local Open Scope qll_calculus.

Context {R: realType}.
Context {i: interval int}.
Context {atoms: Type}.

Fixpoint neg (form: @qll_formula R i atoms): qll_formula := match form with
| atom a => neg_atom a
| neg_atom a => atom a
| 𝟙 => 𝟙
| ⊥ => ⊤
| ⊤ => ⊥
| A ⊗ B => (neg A) ⊗* (neg B)
| (A ⊗* B) => (neg A) ⊗ (neg B)
| A ∧[p] B => (neg A) ∨[p] (neg B)
| A ∨[p] B => (neg A) ∧[p] (neg B)                                                        end.

Compute (neg (⊥ ⊗* (⊥ ⊗ 𝟙))).

End negation.

Notation "A `*" := (neg A): qll_calculus.
Notation "A --o B" := (@bin _ _ _ par (neg A) B) (at level 45, right associativity): qll_calculus.

Section deduction.

Context {R: realType}.
Context {i: interval int}.  
Context {atoms: Type}.

Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope list_scope.
Local Open Scope nngereal_scope.
Local Open Scope ereal_scope.
Local Open Scope qll_calculus.

(* Notation for prv and the rules is inspired by Rocq Library of undecidability *)

Reserved Notation "A ⊢ B" (at level 61).

(* prv can't have type ending with Prop as elimination restriction would
   otherwise prevent us from computing the (numeric hence computational) 
   validity of a given deriviation *)
(* TODO Maybe make formula and list arguments in the constructors implicit? *)
Inductive prv : list (@qll_formula R i atoms) -> list (@qll_formula R i atoms) -> Type :=
| AX A:                  (* ---------------–----- *)
                                  [A] ⊢ [A]

| EMP:                   (* ---------------–----- *)
                                   [] ⊢ []  

| EFQ Γ Δ:               (* ---------------–----- *)
                                    Γ ⊢ Δ
| CUT A Γ Γ' Δ Δ': 
                            Γ ⊢ A::Δ -> A::Γ' ⊢ Δ'
                         (* ---------------–----- *)
                       ->     Γ ++ Γ' ⊢ Δ ++ Δ'
| MIX_star  Γ Γ' Δ Δ':
                               Γ ⊢ Δ -> Γ' ⊢ Δ'
                         (* ---------------–----- *)
                       ->     Γ ++ Γ' ⊢ Δ ++ Δ'
(* Multiplicative Rules *)
| tensor_L A B Γ Δ:
                                 A::B::Γ ⊢ Δ
                         (* ---------------–----- *)
                       ->       A ⊗ B::Γ ⊢ Δ
| tensor_R A B Γ Γ' Δ Δ':
                            Γ ⊢ A::Δ -> Γ' ⊢ B::Δ'
                         (* ---------------–----- *)
                       ->  Γ ++ Γ' ⊢ A ⊗ B::Δ ++ Δ'
| par_L A B Γ Γ' Δ Δ':
                            A::Γ ⊢ Δ -> B::Γ' ⊢ Δ'
                         (* ---------------–----- *)
                       ->  A ⊗* B::Γ ++ Γ' ⊢ Δ ++ Δ'
| par_R A B Γ Δ:
                                Γ ⊢ A::B::Δ
                         (* ---------------–----- *)
                       ->       Γ ⊢ A ⊗* B::Δ

| one_L:                 (* ---------------–----- *)
                                  [𝟙] ⊢ []

| one_R:                 (* ---------------–----- *)
                                  [] ⊢ [𝟙]

| neg_L A Γ Δ:
                                  Γ ⊢ A::Δ
                         (* ---------------–----- *)
                       ->        A`*::Γ ⊢ Δ
| neg_R A Γ Δ:
                                  A::Γ ⊢ Δ
                         (* ---------------–----- *)
                       ->        Γ ⊢ A`*::Δ
(* Additive Rules *)
| or_L p A B Γ Δ:
                            A::Γ ⊢ Δ -> B::Γ ⊢ Δ
                         (* ---------------–----- *)
                       ->     A ∨[p] B::Γ ⊢ Δ
| or_R p A B Γ Δ:
                            Γ ⊢ A::Δ -> Γ ⊢ B::Δ
                         (* ---------------–----- *)
                       ->     Γ ⊢ A ∨[p] B::Δ
| and_L p A B Γ Δ:
                            A::Γ ⊢ Δ -> B::Γ ⊢ Δ
                         (* ---------------–----- *)
                       ->     A ∧[p] B::Γ ⊢ Δ
| and_R p A B Γ Δ:
                            Γ ⊢ A::Δ -> Γ ⊢ B::Δ
                         (* ---------------–----- *)
                       ->     Γ ⊢ A ∧[p] B::Δ

| bot_L:                 (* ---------------–----- *)
                                  [⊥] ⊢ []

| top_R:                 (* ---------------–----- *)
                                  [] ⊢ [⊤]
(* Structural exchange rules as Rocq development uses lists instead of multisets *)
| EXCH_L A B Γ Γ' Δ: 
                             Γ ++ (A::B::Γ') ⊢ Δ
                         (* ---------------–----- *)
                       ->    Γ ++ (B::A::Γ') ⊢ Δ
| EXCH_R A B Γ Δ Δ': 
                             Γ ⊢ Δ ++ (A::B::Δ')
                         (* ---------------–----- *)
                       ->    Γ ⊢ Δ ++ (B::A::Δ')
where "A ⊢ B" := (prv A B): qll_calculus.

Fixpoint validity {Γ} {Δ} (P: Γ ⊢ Δ): {nonneg \bar R} :=
  match P with
  | AX _ => 1%:E%:nng
  | EMP => 1%:E%:nng
  | EFQ _ _ => 0%:E%:nng
  | CUT _ _ _ _ _ P1 P2 => ((validity P1) ⊗ (validity P2))%NNGE
  | MIX_star _ _ _ _ P1 P2 => ((validity P1) ⊗* (validity P2))%NNGE
  | tensor_L _ _ _ _ P => validity P 
  | tensor_R _ _ _ _ _ _ P1 P2 => ((validity P1) ⊗ (validity P2))%NNGE
  | par_L _ _ _ _ _ _ P1 P2 => ((validity P1) ⊗ (validity P2))%NNGE
  | par_R _ _ _ _ P => validity P
  | one_L => 1%:E%:nng
  | one_R => 1%:E%:nng
  | neg_L _ _ _ P => validity P
  | neg_R _ _ _ P => validity P
  | or_L p _ _ _ _ P1 P2 => (validity P1) ⊕[-p%:num] (validity P2) 
  | or_R p _ _ _ _ P1 P2 => (validity P1) ⊕[p%:num] (validity P2)
  | and_L p _ _ _ _ P1 P2 => (validity P1) ⊕[p%:num] (validity P2)
  | and_R p _ _ _ _ P1 P2 => (validity P1) ⊕[-p%:num] (validity P2)
  | bot_L => +oo%:nng
  | top_R => +oo%:nng
  | EXCH_L _ _ _ _ _ P => validity P
  | EXCH_R _ _ _ _ _ P => validity P
  end.

Definition provability_set A B := (Itv.r \o validity) @` [set: A ⊢ B].

(* Provability of the sequent A ⊢ B *)
(* TODO If we generalise this to arbitrary calculi, we need to make sure that sup ∅ = 0 *)
Definition provability A B := ereal_sup (provability_set A B).

Lemma proof_le_provability {A} {B} P:
  (@validity A B P)%:num <= provability A B.
Proof.
  apply le_ereal_sup_tmp. exists ((validity P)%:nngnum) => //.
  rewrite /provability_set /=. by exists P.
Qed.

End deduction.

Notation "A ⊢ B" := (@prv _ _ _ A B) (at level 61): qll_calculus. 
Notation "|/ A ⊢- B |/" := (@provability _ _ _ A B) (at level 61): qll_calculus. (* TODOFind better notation  *)


Section semantics.

Context {R: realType}.
Context {i: interval int}.  
Context {atoms: Type}.

Local Open Scope ring_scope.
Local Open Scope ereal_scope.
Local Open Scope nngereal_scope.
Local Open Scope qll_calculus.

Fixpoint eval_form (form: @qll_formula _ i _) (f: atoms -> {nonneg \bar R}) :=
  match form with
  | atom a => f a
  | neg_atom a => ((f a) `*)%NNGE
  | 𝟙 => 1%:E%:nng
  | ⊥ => 0%:E%:nng
  | ⊤ => +oo%:nng
  | A ⊗ B => ((eval_form A f) ⊗ (eval_form B f))%NNGE
  | (A ⊗* B) => ((eval_form A f) ⊗* (eval_form B f))%NNGE
  | A ∧[p] B => (eval_form A f) ⊕[-p%:num] (eval_form B f)
  | A ∨[p] B => (eval_form A f) ⊕[p%:num] (eval_form B f)         
  end.
                   
End semantics.

Notation "〚 form 〛_ f" := (@eval_form _ _ _ form f) (at level 61): qll_calculus.
(* TODO get nicer square brackets... *)
                  
Section rat_completeness.

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

Check lt_neqAle. Check eqVneq.
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

Lemma mulye_eval_form {i} (f: @qll_formula _ i _) q:
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

Lemma addye_eval_form {i} (f: @qll_formula _ i _) q:
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
  

(* In the remaining proofs of this section, we want the annotations of
   ∧ and ∨ to be 1. Achived by forcing the annotations to be in the interval
   [1,1] = {1}. *)
Definition itv_1 := `[1%Z,1%Z].

(* TODO How to make this proof short and concise? *)
Lemma in_itv_1_then_eq_1 (x: {itv \bar R & itv_1}):
  x%:num = 1.
Proof.
  destruct x as [r Hr]. simpl.
  rewrite /Itv.spec /ext_num_sem in Hr.
  move: Hr => /andP /=. rewrite in_itv /=.
  move=> [_ ] Hsandwich.
  symmetry. by apply le_anti. 
Qed.

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

Lemma eval_no_atoms_is_rat (f: @qll_formula R itv_1 False):
  (〚 f 〛_atom_func)%:num = +oo
    \/ exists q: rat, (0 <= q)%R /\
      (ratr q)%:E = (〚 f 〛_atom_func)%:num.
Proof.
  induction f as [a|a| | | |[| |r|r] f1 [IHf1|[p [Hp Hp']]] f2 [IHf2|[q [Hq Hq']]]] => /=.
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
  - left. rewrite in_itv_1_then_eq_1 harmonic_p_sum_1 /= IHf1 IHf2.
    rewrite invey adde_hack.
    by rewrite adde0 inve0. 
  - rewrite in_itv_1_then_eq_1 harmonic_p_sum_1 /= IHf1. 
    by apply (addye_eval_form _ q).
  - rewrite in_itv_1_then_eq_1 harmonic_p_sum_1 /= IHf2 addeC_hack.
    by apply (addye_eval_form _ p).
  - rewrite in_itv_1_then_eq_1 harmonic_p_sum_1 /= -Hp' -Hq'. right.
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
  - rewrite in_itv_1_then_eq_1 p_sum_1 /= IHf1 IHf2. by left.
  - rewrite in_itv_1_then_eq_1 p_sum_1 /= IHf1. left.
    by rewrite addye_hack //= -ltNye -Hq' ltNyr.
  - rewrite in_itv_1_then_eq_1 p_sum_1 /= IHf2. left.
    by rewrite addeC_hack addye_hack //= -ltNye -Hp' ltNyr.
  - rewrite in_itv_1_then_eq_1 p_sum_1 /=. right.
    exists (p + q)%R. split; first by apply addr_ge0.
    rewrite adde_hack -Hp' -Hq'  -(opprK q%R) ratr_is_additive. (* Ugly workaround *)
    by rewrite rmorphN /= !opprK.
Qed.

Lemma eval_le_valid (f: @qll_formula R itv_1 False):
  exists P: [] ⊢ [f], (〚 f 〛_atom_func)%:num <= (validity P)%:num.
Proof.
  induction f as [a|a| | | |[| |r|r] f1 [P1 IH1] f2 [P2 IH2]].
  - by exfalso.
  - by exfalso.
  - by exists one_R.
  - by exists (EFQ [] [⊥]).
  - by exists top_R.
  - exists (tensor_R _ _ _ _ _ _ P1 P2) => /=.
    by apply (@lee_pmul _ _ _ _ (validity P2)%:nngnum). (* Just applying lee_pmus causes Rocq to diverge or take ages *) Check MIX_star.
  - pose P := (par_R _ _ _ _ (MIX_star _ _ _ _ P1 P2)).
    exists P => /=. rewrite lee_pV2; try by rewrite /in_mem /=. 
     by apply (@lee_pmul _ _ _ (validity P2)%:num^-1 _) => //;
       rewrite lee_pV2 //; rewrite /in_mem /=.
  - exists (and_R r f1 f2 [] [] P1 P2) => /=. 
    rewrite in_itv_1_then_eq_1 !harmonic_p_sum_1 /=.
    rewrite lee_pV2; try by rewrite /in_mem /=. 
    by apply (@leeD _ (validity P1)%:num^-1 _ _ _); (* Same, just applying diverges *)
      rewrite lee_pV2; try rewrite /in_mem /=. 
  - exists (or_R r f1 f2 [] [] P1 P2) => /=. 
    rewrite in_itv_1_then_eq_1 !p_sum_1 /=.
    by apply (@leeD _ _ _ _ (validity P2)%:num).
Qed.

Corollary complete_for_rat (f: @qll_formula R itv_1 False):
  (〚 f 〛_atom_func)%:num <= |/ [] ⊢- [f] |/.
Proof.
  destruct (eval_le_valid f) as [P HP].
  eapply le_trans; first exact HP.
  by apply proof_le_provability.
Qed.
      
End rat_completeness.
