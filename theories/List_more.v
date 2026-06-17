(** Add-ons for List library
Usefull tactics and properties apparently missing in the [List] library. *)

(* TODO rename di/trichot_... into decomp_xxx_eq_yyyy  and [vs] into [eq] for equality *)

Set Mangle Names.
Set Mangle Names Light.
Set Implicit Arguments.

From Stdlib Require Import PeanoNat.
From Stdlib Require Export List.
From mathcomp Require Import seq.
From OLlibs Require Import Bool_more.

Import EqNotations.


(** * Tactics *)

(** ** Simplification in lists *)

Ltac list_simpl :=
  repeat (
    repeat cbn;
    rewrite <- ? app_assoc, <- ? app_comm_cons, ? app_nil_r;
    rewrite <- ? map_rev, ? rev_involutive, ? rev_app_distr, ? rev_unit;
    rewrite ? map_app, ? flat_map_app).
#[local] Ltac list_simpl_hyp H :=
  repeat (
    repeat cbn in H;
    rewrite <- ? app_assoc, <- ? app_comm_cons, ? app_nil_r in H;
    rewrite <- ? map_rev, ? rev_involutive, ? rev_app_distr, ? rev_unit in H;
    rewrite ? map_app, ? flat_map_app in H).
Ltac list_simpl_hyps :=
  match goal with
  | H : _ |- _ => list_simpl_hyp H; revert H; list_simpl_hyps; intro H
  | _ => idtac
  end.
Tactic Notation "list_simpl" "in" "*" := list_simpl_hyps; list_simpl.
Tactic Notation "list_simpl" "in" hyp(H) := list_simpl_hyp H.


(** ** Removal of [cons] constructions *)

Lemma cons_is_app A (x:A) l : x :: l = (x :: nil) ++ l.
Proof. reflexivity. Qed.

Ltac cons2app :=
  repeat
  match goal with
  | |- context [ cons ?x ?l ] =>
         lazymatch l with
         | nil => fail
         | _ => rewrite (cons_is_app x l)
           (* one could prefer
                 [change (cons x l) with (app (cons x nil) l)]
              which leads to simpler generated term
              but does not work with existential variables *)
         end
  end.
#[local] Ltac cons2app_hyp H :=
  repeat
  match type of H with
  | context [ cons ?x ?l ]  =>
      lazymatch l with
      | nil => fail
      | _ =>  rewrite (cons_is_app x l) in H
           (* one could prefer
                 [change (cons x l) with (app (cons x nil) l) in H]
              which leads to simpler generated term
              but does not work with existential variables *)
      end
  end.
Ltac cons2app_hyps :=
  match goal with
  | H : _ |- _ => cons2app_hyp H; revert H; cons2app_hyps; intro H
  | _ => idtac
  end.
Tactic Notation "cons2app" "in" "*" := cons2app_hyps; cons2app.
Tactic Notation "cons2app" "in" hyp(H) := cons2app_hyp H.


(** ** Decomposition of lists and [list] equalities *)

Lemma decomp_length_add A (l : list A) n m : length l = n + m ->
  {'(l1, l2) | length l1 = n /\ length l2 = m & l = l1 ++ l2 }.
Proof.
induction n as [|n IHn] in l, m |- *; intro Heq.
- now split with (nil, l).
- destruct l as [|a l]; inversion Heq as [Heq2].
  specialize (IHn l m Heq2) as [(l1, l2) [<- <-] ->].
  split with (a :: l1, l2); [ split | ]; reflexivity.
Qed.

Ltac nil_vs_elt_inv H :=
  match type of H with
  | nil = ?x :: ?l2 => discriminate H
  | ?x :: ?l2 = nil => discriminate H
  | nil = ?l1 ++ ?x :: ?l2 => destruct l1; discriminate H
  | ?l1 ++ ?x :: ?l2 = nil => destruct l1; discriminate H
  end.

Ltac unit_vs_elt_inv H := 
  match type of H with
  | ?a :: nil = ?l1 ++ ?x :: ?l2 =>
      let Hnil1 := fresh in
      let Hnil2 := fresh in
      symmetry in H; apply elt_eq_unit in H as [H [Hnil1 Hnil2]];
      (try subst x); (try subst a); rewrite ? Hnil1, ? Hnil2 in *;
      clear Hnil1 Hnil2; (try clear l1); (try clear l2)
  | ?l1 ++ ?x :: ?l2 = ?a :: nil =>
      let Hnil1 := fresh in
      let Hnil2 := fresh in
      apply elt_eq_unit in H as [H [Hnil1 Hnil2]];
      (try subst x); (try subst a); rewrite ? Hnil1, ? Hnil2 in *;
      clear Hnil1 Hnil2; (try clear l1); (try clear l2)
  end.

Lemma dichot_app A (l1 l2 l3 l4 : list A) : l1 ++ l2 = l3 ++ l4 ->
     (exists l2', l1 ++ l2' = l3 /\ l2 = l2' ++ l4)
  \/ (exists l4', l1 = l3 ++ l4' /\ l4' ++ l2 = l4).
Proof. intros [l [[-> ->]|[-> ->]]]%app_eq_app; [ right | left ]; exists l; repeat split. Qed.

#[local] Ltac dichot_app_exec_core H p :=
  match type of H with
  | _ ++ _ = _ ++ _ => apply dichot_app in H as p
  end.
Tactic Notation "dichot_app_exec" hyp(H) "as" simple_intropattern(p) := dichot_app_exec_core H p.
Tactic Notation "dichot_app_exec" hyp(H) :=
  let l := fresh "l" in
  let H1 := fresh H in
  let H2 := fresh H in
  dichot_app_exec_core H ipattern:([[l [H1 H2]]|[l [H1 H2]]]).

Lemma dichot_elt_app A l1 (a : A) l2 l3 l4 : l1 ++ a :: l2 = l3 ++ l4 ->
     (exists l2', l1 ++ a :: l2' = l3 /\ l2 = l2' ++ l4)
  \/ (exists l4', l1 = l3 ++ l4' /\ l4' ++ a :: l2 = l4).
Proof.
induction l1 as [|b l1 IHl1] in l2, l3, l4 |- *; induction l3 as [|c l3 IHl3] in l4 |- *; cbn;
  intro Heq; inversion Heq as [[Heq'' Heq']].
- now right; exists (@nil A).
- now left; exists l3.
- now right; exists (b :: l1).
- destruct (IHl1 _ _ _ Heq') as [[l2' [<- H2'2]] | [l4' [-> H4'2]]].
  + now left; exists l2'.
  + now right; exists l4'.
Qed.

#[local] Ltac dichot_elt_app_exec_core H p :=
  match type of H with
  | _ ++ _ :: _ = _ ++ _ => apply dichot_elt_app in H as p
  | _ ++ _ = _ ++ _ :: _ => simple apply eq_sym in H;
                            apply dichot_elt_app in H as p
  end.
Tactic Notation "dichot_elt_app_exec" hyp(H) "as" simple_intropattern(p) := dichot_elt_app_exec_core H p.
Tactic Notation "dichot_elt_app_exec" hyp(H) :=
  let l := fresh "l" in
  let H1 := fresh H in
  let H2 := fresh H in
  dichot_elt_app_exec_core H ipattern:([[l [H1 H2]]|[l [H1 H2]]]).

Lemma trichot_elt_app A l1 (a : A) l2 l3 l4 l5 : l1 ++ a :: l2 = l3 ++ l4 ++ l5 ->
      (exists l2', l1 ++ a :: l2' = l3 /\ l2 = l2' ++ l4 ++ l5)
   \/ (exists l2' l2'', l1 = l3 ++ l2' /\ l2' ++ a :: l2'' = l4 /\ l2 = l2'' ++ l5)
   \/ (exists l5', l1 = l3 ++ l4 ++ l5' /\ l5' ++ a :: l2 = l5).
Proof.
induction l1 as [|b l1 IHl1] in l2, l3, l4, l5 |- *; induction l3 as [|c l3 IHl3] in l4, l5 |- *; cbn;
  intro Heq; simpl in Heq; inversion Heq as [[Heq' Heq'']].
- destruct l4 as [| a' l4]; inversion Heq'.
  + now right; right; exists nil.
  + now right; left; exists nil, l4.
- now left; exists l3.
- destruct l4 as [| a' l4]; inversion Heq' as [[Heq1 Heq2]].
  + now right; right; exists (b :: l1).
  + dichot_elt_app_exec Heq2; subst.
    * now right; left; exists (a' :: l1); eexists.
    * now right; right; eexists.
- destruct (IHl1 _ _ _ _ Heq'')
    as [[l' [<- ->]] | [ [l2' [l2'' [-> [<- ->]]]] | [l' [-> <-]] ]].
  + now left; exists l'.
  + now right; left; exists l2', l2''.
  + now right; right; exists l'.
Qed.

#[local] Ltac trichot_elt_app_exec_core H p :=
  match type of H with
  | _ ++ _ :: _ = _ ++ _ ++ _ => apply trichot_elt_app in H as p
  | _ ++ _ ++ _ = _ ++ _ :: _ => simple apply eq_sym in H;
                                 apply trichot_elt_app in H as p
  end.
Tactic Notation "trichot_elt_app_exec" hyp(H) "as" simple_intropattern(p) := trichot_elt_app_exec_core H p.
Tactic Notation "trichot_elt_app_exec" hyp(H) :=
  let l1 := fresh "l" in
  let l2 := fresh "l" in
  let H1 := fresh H in
  let H2 := fresh H in
  let H3 := fresh H in
  trichot_elt_app_exec_core H ipattern:([[l1 [H1 H2]] | [[l1 [l2 [H1 [H2 H3]]]] | [l2 [H1 H2]]]]).

Lemma trichot_elt_elt A l1 (a : A) l2 l3 b l4 : l1 ++ a :: l2 = l3 ++ b :: l4 ->
      (exists l2', l1 ++ a :: l2' = l3 /\ l2 = l2' ++ b :: l4)
   \/ (l1 = l3 /\ a = b /\ l2 = l4)
   \/ (exists l4', l1 = l3 ++ b :: l4' /\ l4' ++ a :: l2 = l4).
Proof.
intro Heq. change (b :: l4) with ((b :: nil) ++ l4) in Heq.
trichot_elt_app_exec Heq as [ | [[[|a' l2'] [l2'' [-> [[= -> H] ->]]]] | ]];
  [ now left | right; left .. | now right; right ].
- subst. list_simpl. repeat split.
- nil_vs_elt_inv H.
Qed.

#[local] Ltac trichot_elt_elt_exec_core H p :=
  match type of H with
  | ?lh ++ _ :: ?lr = ?l1 ++ ?x :: ?l2 =>
      apply trichot_elt_elt in H as p;
        [ try subst l1; try subst lr
        | try subst x; try subst l1; try subst l2
        | try subst l2; try subst lh ]
  end.
Tactic Notation "trichot_elt_elt_exec" hyp(H) "as" simple_intropattern(p) := trichot_elt_elt_exec_core H p.
Tactic Notation "trichot_elt_elt_exec" hyp(H) :=
  let l := fresh "l" in
  let H1 := fresh H in
  let H2 := fresh H in
  let H3 := fresh H in
  trichot_elt_elt_exec_core H ipattern:([[l [H1 H2]] | [[H1 [H2 H3]] | [l [H1 H2]]]]).

Lemma dichot_app_inf A (l1 l2 l3 l4 : list A) : l1 ++ l2 = l3 ++ l4 ->
     { l2' | l1 ++ l2' = l3 & l2 = l2' ++ l4 }
   + { l4' | l1 = l3 ++ l4' & l4' ++ l2 = l4 }.
Proof.
induction l1 as [|b l1 IHl1] in l2, l3, l4 |- *; induction l3 as [|c l3 IHl3] in l4 |- *;
  cbn; intro Heq; inversion Heq as [[Heq'' Heq']]; subst.
- now right; exists (@nil A).
- now left; exists (c :: l3).
- now right; exists (b :: l1).
- destruct (IHl1 _ _ _ Heq') as [[l2' <- H2'2] | [l4' -> H4'2]].
  + now left; exists l2'.
  + now right; exists l4'.
Qed.

#[local] Ltac dichot_app_inf_exec_core H p :=
  match type of H with
  | _ ++ _ = _ ++ _ => apply dichot_app_inf in H as p
  end.
Tactic Notation "dichot_app_inf_exec" hyp(H) "as" simple_intropattern(p) := dichot_app_inf_exec_core H p.
Tactic Notation "dichot_app_inf_exec" hyp(H) :=
  let l := fresh "l" in
  let H1 := fresh H in
  let H2 := fresh H in
  dichot_app_inf_exec_core H ipattern:([[l H1 H2]|[l H1 H2]]).

Lemma dichot_elt_app_inf A l1 (a : A) l2 l3 l4 : l1 ++ a :: l2 = l3 ++ l4 ->
     { l2' | l1 ++ a :: l2' = l3 & l2 = l2' ++ l4 }
   + { l4' | l1 = l3 ++ l4' & l4' ++ a :: l2 = l4 }.
Proof.
induction l1 as [|b l1 IHl1] in l2, l3, l4 |- *; induction l3 as [|c l3 IHl3] in l4 |- *;
  cbn; intro Heq; inversion Heq as [[Heq'' Heq']]; subst.
- now right; exists (@nil A).
- now left; exists l3.
- now right; exists (b :: l1).
- destruct (IHl1 _ _ _ Heq') as [[l2' <- H2'2] | [l4' -> H4'2]].
  + now left; exists l2'.
  + now right; exists l4'.
Qed.

#[local] Ltac dichot_elt_app_inf_exec_core H p :=
  match type of H with
  | _ ++ _ :: _ = _ ++ _ => apply dichot_elt_app_inf in H as p
  | _ ++ _ = _ ++ _ :: _ => simple apply eq_sym in H;
                            apply dichot_elt_app_inf in H as p
  end.
Tactic Notation "dichot_elt_app_inf_exec" hyp(H) "as" simple_intropattern(p) := dichot_elt_app_inf_exec_core H p.
Tactic Notation "dichot_elt_app_inf_exec" hyp(H) :=
  let l := fresh "Σ" in
  let H1 := fresh H in
  let H2 := fresh H in
  dichot_elt_app_inf_exec_core H ipattern:([[l H1 H2]|[l H1 H2]]).

Lemma trichot_elt_app_inf A l1 (a : A) l2 l3 l4 l5 : l1 ++ a :: l2 = l3 ++ l4 ++ l5 ->
     { l2' | l1 ++ a :: l2' = l3 & l2 = l2' ++ l4 ++ l5 }
   + {'(l3', l4') | l1 = l3 ++ l3' & l3' ++ a :: l4' = l4 /\ l2 = l4' ++ l5 }
   + { l5' | l1 = l3 ++ l4 ++ l5' & l5' ++ a :: l2 = l5 }.
Proof.
induction l1 as [|b l1 IHl1] in l2, l3, l4, l5 |- *; induction l3 as [|c l3 IHl3] in l4, l5 |- *;
  cbn; intro Heq; inversion Heq as [[Heq' Heq'']]; subst.
- destruct l4 as [| a' l4]; inversion Heq'.
  + now right; exists nil.
  + now left; right; exists (nil, l4).
- now left; left; exists l3.
- destruct l4 as [| a' l4]; inversion Heq' as [[Heq1 Heq2]].
  + now right; exists (b :: l1).
  + dichot_elt_app_inf_exec Heq2; subst.
    * now left; right; eexists (a' :: l1, _).
    * now right; eexists.
- destruct (IHl1 _ _ _ _ Heq'') as [ [[l' <- ->] | [(l2', l2'') -> [<- ->]]] | [l' -> <-] ].
  + now left; left; exists l'.
  + now left; right; exists (l2', l2'').
  + now right; exists l'.
Qed.

#[local] Ltac trichot_elt_app_inf_exec_core H p :=
  match type of H with
  | _ ++ _ :: _ = _ ++ _ ++ _ => apply trichot_elt_app_inf in H as p
  | _ ++ _ ++ _ = _ ++ _ :: _ => simple apply eq_sym in H;
                                 apply trichot_elt_app_inf in H as p
  end.
Tactic Notation "trichot_elt_app_inf_exec" hyp(H) "as" simple_intropattern(p) := trichot_elt_app_inf_exec_core H p.
Tactic Notation "trichot_elt_app_inf_exec" hyp(H) :=
  let l1 := fresh "l" in
  let l2 := fresh "l" in
  let H1 := fresh H in
  let H2 := fresh H in
  trichot_elt_app_inf_exec_core H ipattern:([[[l1 H1 H2] | [[l1 l2] H1 [H2 H3]] ] | [l2 H1 H2] ]).

Lemma trichot_elt_elt_inf A l1 (a : A) l2 l3 b l4 : l1 ++ a :: l2 = l3 ++ b :: l4 ->
     { l2' | l1 ++ a :: l2' = l3 & l2 = l2' ++ b :: l4 }
   + { l1 = l3 /\ a = b /\ l2 = l4 }
   + { l4' | l1 = l3 ++ b :: l4' & l4' ++ a :: l2 = l4 }.
Proof.
intro Heq. change (b :: l4) with ((b :: nil) ++ l4) in Heq.
trichot_elt_app_inf_exec Heq as [[ | [(l2', l2'') H'1 [H'2 H'3]]] | ]; subst;
  [ left; left | left; right | right ]; auto.
now destruct l2' as [|a' l2']; inversion H'2 as [[H1 H2]];
  subst; [ | destruct l2'; inversion H2 ]; list_simpl.
Qed.

#[local] Ltac trichot_elt_elt_inf_exec_core H p :=
  match type of H with
  | ?lh ++ _ :: ?lr = ?l1 ++ ?x :: ?l2 =>
      apply trichot_elt_elt_inf in H as p;
        [ try subst l1; try subst lr
        | try subst x; try subst l1; try subst l2
        | try subst l2; try subst lh ]
  end.
Tactic Notation "trichot_elt_elt_inf_exec" hyp(H) "as" simple_intropattern(p) := trichot_elt_elt_inf_exec_core H p.
Tactic Notation "trichot_elt_elt_inf_exec" hyp(H) :=
  let l := fresh "l" in
  let H1 := fresh H in
  let H2 := fresh H in
  let H3 := fresh H in
  trichot_elt_elt_inf_exec_core H ipattern:([[[l H1 H2] | [H1 [H2 H3]]] | [l H1 H2]]).
