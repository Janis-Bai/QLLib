From mathcomp Require Import all_boot all_order ssralg ssrint ssrnum.
From mathcomp Require Import interval interval_inference rat.
From mathcomp Require Import reals constructive_ereal classical_sets ereal.

From QLLib Require Import interval_einference nonneg_ereal.

Import Order.TTheory GRing.Theory Num.Theory.

From Stdlib Require Import List.

Import ListNotations.

(* Stdlib's List.seq (the nat range function) shadows mathcomp's
   abbreviation seq := list when List is imported after mathcomp;
   restore the mathcomp convention *)
Notation seq := list.

Declare Scope qll_calculus.
Delimit Scope qll_calculus with QLLC.

(* Type of all extended reals in interval i, somehow not yet in the library *)
(* TODO What is phant actually? *)
Definition itvnume (R : numDomainType) (i: interval int) & phant R :=
  Itv.def (@ext_num_sem R) (Itv.Real i).

Notation "{ 'itv' \bar R & i }" := (itvnume R i (Phant R)) : qll_calculus.

(** * Mechanisation of Quantitative Linear Logic (QLL) *)
(** ** Syntax of Formulas *)
Section syntax.

Open Scope qll_calculus.

Inductive qll_connective {R: realType} {p: {posnum \bar R}}: Type :=
| tensor: qll_connective
| par: qll_connective
| add_and: qll_connective
| add_or: qll_connective.

Inductive qll_formula {R: realType} {p: {posnum \bar R}} {atoms: Type}: Type :=
| atom: atoms -> qll_formula
| neg_atom: atoms -> qll_formula
| one: qll_formula
| bot: qll_formula
| top: qll_formula
| bin: @qll_connective R p -> qll_formula -> qll_formula -> qll_formula.

End syntax.

(* TODO: Discuss notation levels and make them appropriate *)
Notation "A ⊗ B" := (@bin _ _ _ tensor A B) (at level 46, left associativity): qll_calculus.
Notation "A ⊗* B" := (@bin _ _ _ par A B) (at level 46, left associativity): qll_calculus.
Notation "A ∧[ p ] B" := (@bin _ p _ add_and A B) (at level 47, left associativity): qll_calculus.
Notation "A ∨[ p ] B" := (@bin _ p _ add_or A B) (at level 48, left associativity): qll_calculus.
Notation "⊥" := (@bot _ _ _): qll_calculus.
Notation "⊤" := (@top _ _ _): qll_calculus.
Notation "𝟙" := (@one _ _ _): qll_calculus.

(** ** Negation of Formulas *)
(** Notably, negation is a syntactic transformation of formulas *)
Section negation.

Local Open Scope ring_scope.
Local Open Scope ereal_scope.
Local Open Scope qll_calculus.

Context {R: realType}.
Context {p: {posnum \bar R}}.
Context {atoms: Type}.

Fixpoint neg (form: @qll_formula R p atoms): qll_formula := match form with
| atom a => neg_atom a
| neg_atom a => atom a
| 𝟙 => 𝟙
| ⊥ => ⊤
| ⊤ => ⊥
| A ⊗ B => (neg A) ⊗* (neg B)
| (A ⊗* B) => (neg A) ⊗ (neg B)
| A ∧[_] B => (neg A) ∨[p] (neg B)
| A ∨[_] B => (neg A) ∧[p] (neg B)                                                        end.

Compute (neg (⊥ ⊗* (⊥ ⊗ 𝟙))).

End negation.

Notation "A `*" := (neg A): qll_calculus.
Notation "A --o B" := (@bin _ _ _ par (neg A) B) (at level 45, right associativity, only parsing): qll_calculus.

(** ** Axioms and Theories **)
Section theories_def.

Context {R: realType}.
Context {p: {posnum \bar R}}.
Context {atoms: Type}.

(** An axiom r ≤ Γ ⊢ Δ postulates that the sequent Γ ⊢ Δ is derivable with
    validity at least r. Since formulas are parameterised by the type of
    their atoms, axioms over atoms mention at most the propositional
    constants in atoms by construction. *)
Record qll_axiom: Type := mkAxiom {
  ax_bound: {nonneg \bar R};
  ax_lhs: list (@qll_formula R p atoms);
  ax_rhs: list (@qll_formula R p atoms)
}.

(** A pQLL theory is a set of axioms *)
Definition qll_theory := set qll_axiom.

(** One-sided axioms and theories: an axiom r ≤ ⊢O Γ postulates that the
    one-sided sequent ⊢O Γ is derivable with validity at least r. The
    one-sided form of a two-sided axiom r ≤ Γ ⊢ Δ has sequent Γ`* ++ Δ. *)
Record Oqll_axiom: Type := mkOAxiom {
  Oax_bound: {nonneg \bar R};
  Oax_seq: list (@qll_formula R p atoms)
}.

Definition Oqll_theory := set Oqll_axiom.

End theories_def.

Notation "r ≤ Γ ⊢ Δ" := (mkAxiom r Γ Δ)
  (at level 70, Γ at level 60, Δ at level 60): qll_calculus.

(** ** Deduction Rules **)
(** The deduction rules are parameterised by a theory T: besides the
    logical rules, any axiom of T may be used as a leaf, with the
    validity postulated by the axiom *)
Section deduction.

Context {R: realType}.
Context {p: {posnum \bar R}}.
Context {atoms: Type}.
Context {T: @qll_theory R p atoms}.
Context {OT: @Oqll_theory R p atoms}.

Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope nngereal_scope.
Local Open Scope ereal_scope.
Local Open Scope list_scope.
Local Open Scope qll_calculus.

Reserved Notation "A ⊢ B" (at level 61).

(* prv can't have type ending with Prop as elimination restriction would
   otherwise prevent us from computing the (numeric hence computational) 
   validity of a given deriviation *)
(* TODO Maybe make formula and list arguments in the constructors implicit? *)
Inductive prv : list (@qll_formula R p atoms) -> list (@qll_formula R p atoms) -> Type :=
| AX A:                  (* --------------------- *)
                                  [A] ⊢ [A]

| EMP:                   (* --------------------- *)
                                   [] ⊢ []  

| EFQ Γ Δ:               (* --------------------- *)
                                    Γ ⊢ Δ
| CUT A Γ Γ' Δ Δ': 
                            Γ ⊢ A::Δ -> A::Γ' ⊢ Δ'
                         (* --------------------- *)
                       ->     Γ ++ Γ' ⊢ Δ ++ Δ'
| MIX  Γ Γ' Δ Δ':
                               Γ ⊢ Δ -> Γ' ⊢ Δ'
                         (* --------------------- *)
                       ->     Γ ++ Γ' ⊢ Δ ++ Δ'
(* Multiplicative Rules *)
| tensor_L A B Γ Δ:
                                 A::B::Γ ⊢ Δ
                         (* --------------------- *)
                       ->       A ⊗ B::Γ ⊢ Δ
| tensor_R A B Γ Γ' Δ Δ':
                            Γ ⊢ A::Δ -> Γ' ⊢ B::Δ'
                         (* --------------------- *)
                       ->  Γ ++ Γ' ⊢ A ⊗ B::Δ ++ Δ'
| par_L A B Γ Γ' Δ Δ':
                            A::Γ ⊢ Δ -> B::Γ' ⊢ Δ'
                         (* --------------------- *)
                       ->  A ⊗* B::Γ ++ Γ' ⊢ Δ ++ Δ'
| par_R A B Γ Δ:
                                Γ ⊢ A::B::Δ
                         (* --------------------- *)
                       ->       Γ ⊢ A ⊗* B::Δ

| one_L:                 (* --------------------- *)
                                  [𝟙] ⊢ []

| one_R:                 (* --------------------- *)
                                  [] ⊢ [𝟙]

| neg_L A Γ Δ:
                                  Γ ⊢ A::Δ
                         (* --------------------- *)
                       ->        A`*::Γ ⊢ Δ
| neg_R A Γ Δ:
                                  A::Γ ⊢ Δ
                         (* --------------------- *)
                       ->        Γ ⊢ A`*::Δ
(* Additive Rules *)
| or_L A B Γ Δ:
                            A::Γ ⊢ Δ -> B::Γ ⊢ Δ
                         (* --------------------- *)
                       ->     A ∨[p] B::Γ ⊢ Δ
| or_R A B Γ Δ:
                            Γ ⊢ A::Δ -> Γ ⊢ B::Δ
                         (* --------------------- *)
                       ->     Γ ⊢ A ∨[p] B::Δ
| and_L A B Γ Δ:
                            A::Γ ⊢ Δ -> B::Γ ⊢ Δ
                         (* --------------------- *)
                       ->     A ∧[p] B::Γ ⊢ Δ
| and_R A B Γ Δ:
                            Γ ⊢ A::Δ -> Γ ⊢ B::Δ
                         (* --------------------- *)
                       ->     Γ ⊢ A ∧[p] B::Δ

| bot_L Γ Δ:             (* --------------------- *)
                                  ⊥::Γ ⊢ Δ

| top_R Γ Δ:             (* --------------------- *)
                                  Γ ⊢ ⊤::Δ
(* Structural exchange rules as Rocq development uses lists instead of multisets *)
| EXCH_L A B Γ Γ' Δ: 
                             Γ ++ (A::B::Γ') ⊢ Δ
                         (* --------------------- *)
                       ->    Γ ++ (B::A::Γ') ⊢ Δ
| EXCH_R A B Γ Δ Δ':
                             Γ ⊢ (Δ ++ A::B::Δ')
                         (* --------------------- *)
                       ->    Γ ⊢ (Δ ++ B::A::Δ')
(* Axioms of the theory T *)
| AXM ax:                          T ax
                         (* --------------------- *)
                       ->    ax_lhs ax ⊢ ax_rhs ax
where "A ⊢ B" := (prv A B): qll_calculus.

(** ** Validity and Provability of Sequents **)
Fixpoint validity {Γ} {Δ} (P: Γ ⊢ Δ): {nonneg \bar R} :=
  match P with
  | AX _ => 1%:E%:nng
  | EMP => 1%:E%:nng
  | EFQ _ _ => 0%:E%:nng
  | CUT _ _ _ _ _ P1 P2 => ((validity P1) ⊗ (validity P2))%NNGE
  | MIX _ _ _ _ P1 P2 => ((validity P1) ⊗ (validity P2))%NNGE
  | tensor_L _ _ _ _ P => validity P 
  | tensor_R _ _ _ _ _ _ P1 P2 => ((validity P1) ⊗ (validity P2))%NNGE
  | par_L _ _ _ _ _ _ P1 P2 => ((validity P1) ⊗ (validity P2))%NNGE
  | par_R _ _ _ _ P => validity P
  | one_L => 1%:E%:nng
  | one_R => 1%:E%:nng
  | neg_L _ _ _ P => validity P
  | neg_R _ _ _ P => validity P
  | or_L _ _ _ _ P1 P2 => (validity P1) ⊕[-p%:num] (validity P2) 
  | or_R _ _ _ _ P1 P2 => (validity P1) ⊕[p%:num] (validity P2)
  | and_L _ _ _ _ P1 P2 => (validity P1) ⊕[p%:num] (validity P2)
  | and_R _ _ _ _ P1 P2 => (validity P1) ⊕[-p%:num] (validity P2)
  | bot_L _ _ => +oo%:nng
  | top_R _ _ => +oo%:nng
  | EXCH_L _ _ _ _ _ P => validity P
  | EXCH_R _ _ _ _ _ P => validity P
  | AXM ax _ => ax_bound ax
  end.

Definition provability_set A B := (Itv.r \o validity) @` [set: A ⊢ B].

(* Provability of the sequent A ⊢ B *)
(* TODO If we generalise this to arbitrary calculi, we need to make sure that sup ∅ = 0 *)
Definition provability A B := ereal_sup (provability_set A B).

(* Cut-freeness of proofs *)
Fixpoint cut_free {Γ} {Δ} (P: Γ ⊢ Δ) := match P with
  | AX _ => True
  | EMP => True
  | EFQ _ _ => True
  | CUT _ _ _ _ _ P1 P2 => False
  | MIX _ _ _ _ P1 P2 => cut_free P1 /\ cut_free P2
  | tensor_L _ _ _ _ P => cut_free P
  | tensor_R _ _ _ _ _ _ P1 P2 => cut_free P1 /\ cut_free P2
  | par_L _ _ _ _ _ _ P1 P2 => cut_free P1 /\ cut_free P2
  | par_R _ _ _ _ P => cut_free P
  | one_L => True
  | one_R => True
  | neg_L _ _ _ P => cut_free P
  | neg_R _ _ _ P => cut_free P
  | or_L _ _ _ _ P1 P2 => cut_free P1 /\ cut_free P2
  | or_R _ _ _ _ P1 P2 => cut_free P1 /\ cut_free P2
  | and_L _ _ _ _ P1 P2 => cut_free P1 /\ cut_free P2
  | and_R _ _ _ _ P1 P2 => cut_free P1 /\ cut_free P2
  | bot_L _ _ => True
  | top_R _ _ => True
  | EXCH_L _ _ _ _ _ P => cut_free P
  | EXCH_R _ _ _ _ _ P => cut_free P
  | AXM _ _ => True
  end.

Reserved Notation "⊢O A" (at level 61). (* One sided variant of the calculus *)

Inductive Oprv : list (@qll_formula R p atoms) -> Type :=
| OAX A:                     (* ---------------------- *)
                                      ⊢O [A `*; A] 

| OEMP:                      (* ---------------------- *)
                                         ⊢O []

| OEFQ Γ:                    (* ---------------------- *)
                                         ⊢O Γ

| OCUT A Σ Γ Δ:               ⊢O A `*::Γ -> ⊢O Σ ++ A::Δ
                             (* ---------------------- *)
                          ->        ⊢O Σ ++ Γ ++ Δ

| OMIX Γ Δ:                          ⊢O Γ -> ⊢O Δ
                             (* ---------------------- *)
                          ->          ⊢O Γ ++ Δ

| OEXCH A B Γ Δ:                   ⊢O Γ ++ (A::B::Δ)
                             (* ---------------------- *)
                          ->       ⊢O Γ ++ (B::A::Δ)

| Otensor A B Γ Δ:                ⊢O A::Γ -> ⊢O B::Δ
                             (* ---------------------- *)
                          ->       ⊢O A ⊗ B::Γ ++ Δ

| Opar A B Γ:                         ⊢O A::B::Γ
                             (* ---------------------- *)
                          ->         ⊢O A ⊗* B::Γ

| Oone:                      (* ---------------------- *)
                                       ⊢O [𝟙]

| Oor A B Γ:                       ⊢O A::Γ -> ⊢O B::Γ
                             (* --------------------- *)
                          ->         ⊢O A ∨[p] B::Γ

| Oand A B Γ:                      ⊢O A::Γ -> ⊢O B::Γ
                             (* --------------------- *)
                          ->         ⊢O A ∧[p] B::Γ

| Otop Γ:                    (* --------------------- *)
                                       ⊢O ⊤::Γ
(* Axioms of the one-sided theory OT *)
| OAXM ax:                            OT ax
                             (* ---------------------- *)
                          ->        ⊢O Oax_seq ax
where "⊢O A" := (Oprv A): qll_calculus.

Fixpoint Ovalidity {Γ} (P: ⊢O Γ): {nonneg \bar R} :=
  match P with
  | OAX _ => 1%:E%:nng
  | OEMP => 1%:E%:nng
  | OEFQ _ => 0%:E%:nng
  | OCUT _ _ _ _ P1 P2 => (Ovalidity P1 ⊗ Ovalidity P2)%NNGE
  | OMIX _ _ P1 P2 => (Ovalidity P1 ⊗ Ovalidity P2)%NNGE
  | OEXCH _ _ _ _ P => Ovalidity P
  | Otensor _ _ _ _ P1 P2 => (Ovalidity P1 ⊗ Ovalidity P2)%NNGE
  | Opar _ _ _ P => Ovalidity P
  | Oone => 1%:E%:nng
  | Oor _ _ _ P1 P2 => Ovalidity P1 ⊕[p%:num] Ovalidity P2
  | Oand _ _ _ P1 P2 => Ovalidity P1 ⊕[-p%:num] Ovalidity P2
  | Otop _ => +oo%:nng
  | OAXM ax _ => Oax_bound ax
  end.

Definition Oprovability_set Γ := (Itv.r \o Ovalidity) @` [set: ⊢O Γ].

Definition Oprovability Γ := ereal_sup (Oprovability_set Γ).

(* Cut-freeness of proofs *)
Fixpoint Ocut_free {Γ} (P: ⊢O Γ) := match P with
  | OAX _ => True
  | OEMP => True
  | OEFQ _ => True
  | OCUT _ _ _ _ _ _ => False
  | OMIX _ _ P1 P2 => Ocut_free P1 /\ Ocut_free P2
  | OEXCH _ _ _ _ P => Ocut_free P
  | Otensor _ _ _ _ P1 P2 => Ocut_free P1 /\ Ocut_free P2
  | Opar _ _ _ P => Ocut_free P
  | Oone => True
  | Oor _ _ _ P1 P2 => Ocut_free P1 /\ Ocut_free P2
  | Oand _ _ _ P1 P2 => Ocut_free P1 /\ Ocut_free P2
  | Otop _ => True
  | OAXM _ _ => True
end.

End deduction.

(* Derivability in a theory T; the plain ⊢ notation defaults to the empty theory *)
Notation "A ⊢[ T ] B" := (@prv _ _ _ T A B) (at level 61): qll_calculus.
Notation "A ⊢ B" := (@prv _ _ _ set0 A B) (at level 61): qll_calculus.
Notation "|/ A ⊢- B |/" := (@provability _ _ _ set0 A B) (at level 61): qll_calculus. (* TODOFind better notation  *)
Notation "⊢O[ OT ] Γ" := (@Oprv _ _ _ OT Γ) (at level 61): qll_calculus.
Notation "⊢O Γ" := (@Oprv _ _ _ set0 Γ) (at level 61): qll_calculus.
Notation "`| ⊢O Γ |" := (@Oprovability _ _ _ set0 Γ): qll_calculus.

Ltac induction_prv H Γ Γ' Δ Δ' A B IH1 P1 IH2 P2 IH P :=
  match type of H with
  | prv _ _ => induction H as [A
                            | 
                            | Γ Δ
                            | A Γ Γ' Δ Δ' P1 IH1 P2 IH2
                            | Γ Γ' Δ Δ' P1 IH1 P2 IH2
                            | A B Γ Δ P IH
                            | A B Γ Γ' Δ Δ' P1 IH1 P2 IH2
                            | A B Γ Γ' Δ Δ' P1 IH1 P2 IH2
                            | A B Γ Δ P IH
                            | 
                            |
                            | A Γ Δ P IH
                            | A Γ Δ P IH
                            | A B Γ Δ P1 IH1 P2 IH2
                            | A B Γ Δ P1 IH1 P2 IH2
                            | A B Γ Δ P1 IH1 P2 IH2
                            | A B Γ Δ P1 IH1 P2 IH2
                            | Γ Δ
                            | Γ Δ
                            | A B Γ Γ' Δ P IH
                            | A B Γ Δ Δ' P IH
                            | A P1 ]
  end.

(* Tactic to conveniently destruct Oprv deductions, inspired by Laurent's LL proof. *) 
Ltac destruct_Oprv H Σ Γ Δ A B P1 P2 P :=
  match type of H with
  | Oprv _ => destruct H as [ A
                            |
                            | Γ
                            | A Σ Γ Δ P1 P2
                            | Γ Δ P1 P2
                            | A B Γ Δ P
                            | A B Γ Δ P1 P2
                            | A B Γ P
                            |
                            | A B Γ P1 P2
                            | A B Γ P1 P2
                            | Γ
                            | A P1 ]
  end.

Ltac induction_Oprv H Σ Γ Δ A B P1 IH1 P2 IH2 P IH :=
  match type of H with
  | Oprv _ => induction H as [ A
                            |
                            | Γ
                            | A Σ Γ Δ P1 IH1 P2 IH2
                            | Γ Δ P1 IH1 P2 IH2
                            | A B Γ Δ P IH
                            | A B Γ Δ P1 IH1 P2 IH2
                            | A B Γ P IH
                            |
                            | A B Γ P1 IH1 P2 IH2
                            | A B Γ P1 IH1 P2 IH2
                            | Γ
                            | A P1 ]
  end.

(** ** Semantics: Interpretation of Formulas **)
Section semantics.

Context {R: realType}.
Context {p: {posnum \bar R}}.  
Context {atoms: Type}.

Local Open Scope ring_scope.
Local Open Scope ereal_scope.
Local Open Scope nngereal_scope.
Local Open Scope qll_calculus.

Fixpoint eval_form (form: @qll_formula _ p _) (f: atoms -> {nonneg \bar R}) :=
  match form with
  | atom a => f a
  | neg_atom a => ((f a) `*)%NNGE
  | 𝟙 => 1%:E%:nng
  | ⊥ => 0%:E%:nng
  | ⊤ => +oo%:nng
  | A ⊗ B => ((eval_form A f) ⊗ (eval_form B f))%NNGE
  | (A ⊗* B) => ((eval_form A f) ⊗* (eval_form B f))%NNGE
  | A ∧[_] B => (eval_form A f) ⊕[-p%:num] (eval_form B f)
  | A ∨[_] B => (eval_form A f) ⊕[p%:num] (eval_form B f)         
  end.
                   
End semantics.

Notation "〚 form 〛_ f" := (@eval_form _ _ _ form f) (at level 61): qll_calculus.
(* TODO get nicer square brackets... *)

