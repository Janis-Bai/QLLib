From mathcomp Require Import all_boot seq.
From Stdlib Require Import List.

Import ListNotations.

(** * Needed Lemmas on Lists and Decuction in pQLL *)
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

Lemma exch_inv X (Γ Δ Γ' Δ': list X) (A B C: X):
  Γ ++ A::Δ = Γ' ++ B::C::Δ' ->
  {Σ & (Γ = Γ' ++ B::C::Σ /\ Δ' = Σ ++ A::Δ)%SEQ}
  + {Σ & (Δ = Σ ++ B::C::Δ' /\ Γ' = Γ ++ A::Σ)%SEQ}
  + (Γ = Γ' ++ [B] /\ A = C /\ Δ = Δ')%SEQ
  + (Δ = C::Δ' /\ A = B /\ Γ = Γ')%SEQ.
Proof.
  induction Γ as [|D Γ IHΓ] in Γ' |-*;
  destruct Γ' as [|E Γ']; simpl; move => Heq.
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

#[local] Ltac exch_inv_tac_impl H p :=
  match type of H with
  | (_ ++ _ :: _ =  _ ++  _ :: _ :: _)%SEQ => apply exch_inv in H as p
  | (_ ++ _ :: _ :: _ = _ ++ _ :: _)%SEQ => symmetry in H;
                                      apply exch_inv in H as p
  | _ => idtac "Error"                                                           
  end.

Tactic Notation "exch_inv_tac" hyp(H) "as" simple_intropattern(p) := exch_inv_tac_impl H p.
Tactic Notation "exch_inv_tac" hyp(H) :=
  let Σ := fresh "Σ" in
  let Σ' := fresh "Σ'" in
  let H1 := fresh H in
  let H2 := fresh H in
  let H3 := fresh H in
  exch_inv_tac_impl H ipattern:([[[[Σ [H1 H2]]|[Σ [H1 H2]]]|[H1 [H2 H3]]]|[H1 [H2 H3]]]).


Lemma cat_cons_inv {X} (Σ Γ Δ: list X) A:
  Σ ++ Δ = A::Γ -> {Σ' & (A::Σ' = Σ)%SEQ} + (Σ = [] /\ Δ = A::Γ).
Proof.
  destruct Σ as [| B Σ] => /= HΣΔ; first by right; split.
  inversion HΣΔ; first by left; exists Σ.
Qed.

Lemma list_elem_list_emp_inv {X} (Σ Γ: list X) A:
  [] = (Σ ++ A :: Γ) -> False.
Proof.
  move => H.
  by induction Σ; inversion H.
Qed.

Lemma cat_cons_cat_inv {X} (Σ Γ Σ' Γ': list X) A:
  Σ ++ A::Γ = Σ' ++ Γ' ->
  {Δ & (Σ' = Σ ++ A::Δ /\ Γ = Δ ++ Γ')%SEQ}
  + {Δ & (Γ' = Δ ++ A::Γ /\ Σ = Σ' ++ Δ)%SEQ}.
Proof.
  induction Σ as [|B Σ IHΣ] in Σ' |-*; destruct Σ' as [|C Σ'] => /= Heq.
  - right. by exists [].
  - inversion Heq. subst. left. by exists Σ'.
  - right. by exists (B::Σ).
  - inversion Heq. destruct (IHΣ _ H1) as [[Δ [HΣ' HΓ]]|[Δ [HΓ' HΣ]]]; subst.
    + left. by exists Δ.
    + right. by exists Δ.
Qed.

#[local] Ltac cat_cons_cat_inv_tac_impl H p :=
  match type of H with
  | (_ ++ _ = _ ++ _ :: _)%SEQ => symmetry in H;
                            apply cat_cons_cat_inv in H as p
  | (_ ++ _ :: _ = _ ++ _)%SEQ => apply cat_cons_cat_inv in H as p
  | _ => idtac "Error"                                                           
  end.

Tactic Notation "cat_cons_cat_inv_tac" hyp(H) "as" simple_intropattern(p) := cat_cons_cat_inv_tac_impl H p.
Tactic Notation "cat_cons_cat_inv_tac" hyp(H) :=
  let Σ := fresh "Σ" in
  let H1 := fresh H in
  let H2 := fresh H in
  cat_cons_cat_inv_tac_impl H ipattern:([[Σ [H1 H2]]|[Σ [H1 H2]]]).

Lemma cat_cons_comm X (Σ Γ: list X) A:
  (A :: Σ ++ Γ = (A :: Σ) ++ Γ)%SEQ.
Proof. by []. Qed.
