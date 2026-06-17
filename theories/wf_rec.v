From Stdlib Require Import ssreflect Wf_nat.

Section well_founded_rec.

Lemma well_founded_ext {X} (R S: X -> X -> Prop):
  (forall x y, R x y -> S x y) -> well_founded S -> well_founded R.
Proof.
  move=> Hext HWFS. unfold well_founded.
  apply (well_founded_induction HWFS (fun y => Acc R y)).
  move=> x IH. constructor => y HRy. by apply IH, Hext.
Defined.

Definition retract {X Y} (σ: X -> Y) (R: Y -> Y -> Prop) x y := R (σ x) (σ y).

Lemma well_founded_retract {X Y} (R: Y -> Y -> Prop) (σ: X -> Y):
  well_founded R -> well_founded (retract σ R).
Proof.
  move=> HR. unfold well_founded.
  enough (forall y x, σ x = y -> Acc (retract σ R) x) as H.
  - move=> x. by eapply H.
  - apply (well_founded_induction HR (fun y => forall x, σ x = y -> Acc (retract σ R) x)).
    move=> y IH x Hx. constructor=> x' Hx'.
    apply (IH (σ x')); last done. unfold retract in Hx'.
    by rewrite -Hx.
Defined.
    
Definition lex {X Y} (R: X -> X -> Prop) (S: Y -> Y -> Prop) (a b: X * Y) :=
  R (fst a) (fst b) \/ (fst a = fst b /\ S (snd a) (snd b)).

Lemma well_founded_lex {X Y} (R: X -> X -> Prop) (S: Y -> Y -> Prop):
  well_founded R -> well_founded S -> well_founded (lex R S).
Proof.
  move=> HR HS.
  enough (forall x y, Acc (lex R S) (x, y)) as H; first by move=> [x y].
  apply (well_founded_induction HR (fun x => forall y, Acc (lex R S) (x, y))).
  move=> x IHx. apply (well_founded_induction_type HS).
  move=> y IHy. constructor. move=> [x' y']. rewrite /lex /=.
  move=> [Hlex|[-> Hlex]].
  - by apply IHx.
  - by apply IHy.
Defined.

Definition four_lex {W X Y Z} (R: W -> W -> Prop) (S: X -> X -> Prop)
  (T: Y -> Y -> Prop) (U: Z -> Z -> Prop) :=
  lex R (lex S (lex T U)).

Lemma four_lex_well_founded {W X Y Z} {R S T U}:
  well_founded R -> well_founded S ->
  well_founded T -> well_founded U ->
  well_founded (@four_lex W X Y Z R S T U).
Proof.
  move=> HR HS HT HU.
  apply well_founded_lex; first done.
  apply well_founded_lex; first done.
  by apply well_founded_lex.
Defined.

Definition four_lex_explicit {W X Y Z} (R: W -> W -> Prop) (S: X -> X -> Prop)
  (T: Y -> Y -> Prop) (U: Z -> Z -> Prop) (a b: W * X * Y * Z) :=
  match a, b with
  | (w,x,y,z), (w',x',y',z') => R w w' \/
                                (w = w' /\ S x x') \/
                                (w = w' /\ x = x' /\ T y y') \/
                                (w = w' /\ x = x' /\ y = y' /\ U z z')
  end.

Lemma well_founded_four_lex {W X Y Z} (R: W -> W -> Prop) (S: X -> X -> Prop)
  (T: Y -> Y -> Prop) (U: Z -> Z -> Prop):
  well_founded R -> well_founded S ->
  well_founded T -> well_founded U ->
  well_founded (four_lex_explicit R S T U).
Proof.
  move=> HR HS HT HU.
  enough (forall w x y z, Acc (four_lex_explicit R S T U) (w, x, y, z)) as H;
    first by move=> [[[w x] y] z].
  apply (well_founded_induction HR (fun w => forall x y z, Acc (four_lex_explicit R S T U) (w, x, y, z))).
  move => w IHw.
  apply (well_founded_induction HS (fun x => forall y z, Acc (four_lex_explicit R S T U) (w, x, y, z))).
  move => x IHx.
  apply (well_founded_induction HT (fun y => forall z, Acc (four_lex_explicit R S T U) (w, x, y, z))).
  move => y IHy.
  apply (well_founded_induction HU (fun z => Acc (four_lex_explicit R S T U) (w, x, y, z))).
  move => z IHz. constructor.
  move => [[[w' x'] y'] z'] [Hrww'|[[-> HSxx']|[[-> [-> HTyy']]|[-> [-> [-> HUxx']]]]]].
  - by apply IHw.
  - by apply IHx.
  - by apply IHy.
  - by apply IHz.
Defined.

Lemma well_founded_nat_quadruple:
  well_founded (four_lex_explicit lt lt lt lt).
Proof.
  by apply well_founded_four_lex; apply lt_wf.
Defined.

End well_founded_rec.
  
