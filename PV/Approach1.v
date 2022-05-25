(*
REFERENCES:
The code contained in this file is heavily based on the code from
    - "Software Foundations 1: Logical Foundations, Imp.v. Maps.v"
        "https://softwarefoundations.cis.upenn.edu/lf-current/Imp.html"
    - "Software Foundations 2: Programming Language Foundations, Hoare.v"
        "https://softwarefoundations.cis.upenn.edu/plf-current/Hoare.html"
Both by Benjamin C. Pierce, et al. 2021.
The base of this code has been taken directly from these files,
    and some code has been taken and edited to fit our project.
All additions and edits to the code has been by, or in coorporation with, ITU associate professor Alessandro Bruni.
The project has been supervised by course teacher Jesper Bengtson.

Code comments are provided to indicate authorship of the code.
  'Edited' mean code taken and edited from the books,
  no comment means code taken directly from the book.
*)


Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
From Coq Require Import Lists.List. Import ListNotations.
From mathcomp.ssreflect Require Import all_ssreflect.
From mathcomp Require Import finmap.
From infotheo Require Import fsdist proba.
Require Import Reals.

(*Added by Alessandro*)
Definition var := ordinal 64.

(*Edited by Alessandro*)
Definition state := {ffun var -> nat}.


Inductive aexp : Type :=
  | ANum (n : nat)
  | AId (x : var)
  | APlus (a1 a2 : aexp)
  | AMinus (a1 a2 : aexp)
  | AMult (a1 a2 : aexp).

Inductive bexp : Type :=
  | BTrue
  | BFalse
  | BEq (a1 a2 : aexp)
  | BLe (a1 a2 : aexp)
  | BNot (b : bexp)
  | BAnd (b1 b2 : bexp).

Coercion AId : var >-> aexp.
Coercion ANum : nat >-> aexp.

Declare Custom Entry com.
Declare Scope com_scope.
Notation "<{ e }>" := e (at level 0, e custom com at level 99) : com_scope.
Notation "( x )" := x (in custom com, x at level 99) : com_scope.
Notation "x" := x (in custom com at level 0, x constr at level 0) : com_scope.
Notation "f x .. y" := (.. (f x) .. y)
                  (in custom com at level 0, only parsing,
                  f constr at level 0, x constr at level 9,
                  y constr at level 9) : com_scope.
Notation "x + y" := (APlus x y) (in custom com at level 50, left associativity).
Notation "x - y" := (AMinus x y) (in custom com at level 50, left associativity).
Notation "x * y" := (AMult x y) (in custom com at level 40, left associativity).
Notation "'true'"  := true (at level 1).
Notation "'true'"  := BTrue (in custom com at level 0).
Notation "'false'"  := false (at level 1).
Notation "'false'"  := BFalse (in custom com at level 0).
Notation "x <= y" := (BLe x y) (in custom com at level 70, no associativity).
Notation "x = y"  := (BEq x y) (in custom com at level 70, no associativity).
Notation "x && y" := (BAnd x y) (in custom com at level 80, left associativity).
Notation "'~' b"  := (BNot b) (in custom com at level 75, right associativity).

Open Scope com_scope.

Fixpoint aeval (st : state) (a : aexp) : nat :=
  match a with
  | ANum n => n
  | AId x => st x
  | <{a1 + a2}> => (aeval st a1) + (aeval st a2)
  | <{a1 - a2}> => (aeval st a1) - (aeval st a2)
  | <{a1 * a2}> => (aeval st a1) * (aeval st a2)
  end.


Fixpoint beval (st : state) (b : bexp) : bool :=
  match b with
  | <{true}> => true
  | <{false}> => false
  | <{a1 = a2}> => (aeval st a1) =? (aeval st a2)
  | <{a1 <= a2}> => (aeval st a1) <=? (aeval st a2)
  | <{~ b1}> => negb (beval st b1)
  | <{b1 && b2}> => andb (beval st b1) (beval st b2)
  end.

(*Edited by Alessandro*)
Definition t_empty v : state := [ffun x => v].

(*Edited by Alessandro*)
Definition t_update st i v : state :=
  [ffun x => if i == x then v else st x].

Notation "'_' '!->' v " := (t_empty v)
  (at level 100, right associativity).

Notation "x '!->' v ';' m" := (t_update m x v)
  (at level 100, v at next level, right associativity).

(*Edited and proved by Alessandro*)
Lemma t_apply_empty : forall x v,
(_ !-> v) x = v.
Proof.
move => x v.
rewrite /t_empty=> /=.
by rewrite ffunE.
Qed.

(*Edited by Alessandro*)
Inductive com : Type :=
  | CSkip
  | CAsgn (x : var) (a : aexp)
  | CSeq (c1 c2 : com)
  | CIf (b : bexp) (c1 c2 : com)
  | CPlus (p : Reals_ext.Prob.t) (c1 c2 : com).


Notation "'skip'"  :=
    CSkip (in custom com at level 0) : com_scope.
Notation "x := y"  :=
    (CAsgn x y)
       (in custom com at level 0, x constr at level 0,
        y at level 85, no associativity) : com_scope.
Notation "x ; y" :=
    (CSeq x y)
      (in custom com at level 90, right associativity) : com_scope.
Notation "'if' x 'then' y 'else' z 'end'" :=
    (CIf x y z)
      (in custom com at level 89, x at level 99,
       y at level 99, z at level 99) : com_scope.


(*Added by Alessandro*)
Notation "c1 '[+' p ']' c2" := (CPlus p c1 c2) 
       (in custom com at level 90, p at level 85, right associativity) : com_scope.

(*Added by Alessandro*)
Fixpoint sample x a1 as_ := 
  match as_ with
  | [] => (<{x := a1}>)
  | (a2::as__) => <{ x := a1 [+ (Reals_ext.probdivRnnm 1 (List.length as_))] (sample x a2 as__)}>
  end.

(*Added by Alessandro*) 
Notation "x '$=' { a1 ; a2 ; .. ; an }" := (sample x a1 (cons a2 .. (cons an nil) ..))
  (in custom com at level 0, x constr at level 0,
  a1 at level 85, a2 at level 85, an at level 85, no associativity) : com_scope.

(*Added by Alessandro in collaboration w. group*)
Definition half : Reals_ext.Prob.t := Reals_ext.probdivRnnm 1 2.

(*Edited by group in collaboration w. Alessandro*)
Fixpoint ceval (st : state) (c : com) :=
  match c with
  | <{ skip }> => FSDist1.d st
  | <{ x := a }> => FSDist1.d (x !-> (aeval st a) ; st)
  | <{ c1 ; c2 }> =>
      let st' := ceval st c1 in
      FSDistBind.d st' (fun st => ceval st c2)
  | <{ if b then c1 else c2 end }> =>
      if (beval st b)
        then ceval st c1
        else ceval st c2
  | <{ c1 [+ p] c2}> => ConvFSDist.d p (ceval st c1) (ceval st c2)
  end.


Definition Assertion := state -> Prop.

Definition assert_implies (P Q : Assertion) : Prop :=
    forall st, P st -> Q st.

Definition Aexp : Type := state -> nat.

Definition assert_of_Prop (P : Prop) : Assertion := fun _ => P.
Definition Aexp_of_nat (n : nat) : Aexp := fun _ => n.
Definition Aexp_of_aexp (a : aexp) : Aexp := fun st => aeval st a.

Coercion assert_of_Prop : Sortclass >-> Assertion.
Coercion Aexp_of_nat : nat >-> Aexp.
Coercion Aexp_of_aexp : aexp >-> Aexp.

Arguments assert_of_Prop /.
Arguments Aexp_of_nat /.
Arguments Aexp_of_aexp /.

Declare Scope assertion_scope.
Bind Scope assertion_scope with Assertion.
Bind Scope assertion_scope with Aexp.
Delimit Scope assertion_scope with assertion.

Notation assert P := (P%assertion : Assertion).
Notation mkAexp a := (a%assertion : Aexp).
Notation "~ P" := (fun st => ~ assert P st) : assertion_scope.
Notation "P /\ Q" := (fun st => assert P st /\ assert Q st) : assertion_scope.
Notation "P \/ Q" := (fun st => assert P st \/ assert Q st) : assertion_scope.
Notation "P -> Q" := (fun st => assert P st ->  assert Q st) : assertion_scope.
Notation "P <-> Q" := (fun st => assert P st <->  assert Q st) : assertion_scope.
Notation "a = b" := (fun st => mkAexp a st = mkAexp b st) : assertion_scope.
Notation "a <> b" := (fun st => mkAexp a st <> mkAexp b st) : assertion_scope.
Notation "a <= b" := (fun st => mkAexp a st <= mkAexp b st) : assertion_scope.
Notation "a < b" := (fun st => mkAexp a st < mkAexp b st) : assertion_scope.
Notation "a >= b" := (fun st => mkAexp a st >= mkAexp b st) : assertion_scope.
Notation "a > b" := (fun st => mkAexp a st > mkAexp b st) : assertion_scope.
Notation "a + b" := (fun st => mkAexp a st + mkAexp b st) : assertion_scope.
Notation "a - b" := (fun st => mkAexp a st - mkAexp b st) : assertion_scope.
Notation "a * b" := (fun st => mkAexp a st * mkAexp b st) : assertion_scope.


(* ####### HOARE QUADRUPLE ####### *)

(*Added by Alessandro*)
Local Open Scope proba_scope.

(*Added by Alessandro*)
Local Open Scope com_scope.

(*Added by group in collaboration with Alessandro, under supervision from Jesper*)
Definition hoare_quad
            (P : Assertion) (c : com) (Q : Assertion) (d : R) : Prop :=
    forall st,
        P st ->
        let dst' := (ceval st c) in
        forall (s : {set [finType of finsupp dst']}),
        (forall st', st' \in s <-> Q (fsval st')) ->
        Pr (fdist_of_Dist dst') s = d.


(*Added by group in collaboration with Alessandro*)
Theorem test_skip: forall P,
hoare_quad P CSkip P 1.
Proof.
move => P /=.
rewrite /hoare_quad.
    move => st HPst s HQs //.
    rewrite /FSDist1.d /FSDist1.f.
    (*apply HPst in HQs.*) Admitted.


(*Added by group under supervision from Jesper*)
Theorem test_seq : forall P Q R d1 d2 c1 c2,
    hoare_quad Q c2 R d1 ->
    hoare_quad P c1 Q d2 ->
    hoare_quad P (CSeq c1 c2) R (d1 * d2).
Proof. Admitted.


Definition bassn b : Assertion :=
  fun st => (beval st b = true).

Coercion bassn : bexp >-> Assertion.

Arguments bassn /.


(*Added by group under supervision from Jesper*)
Theorem test_if : forall P Q (b: bexp) d c1 c2,
  hoare_quad (P /\ bassn b) c1 Q d ->
  hoare_quad (P /\ ~b) c2 Q d ->
  hoare_quad P (CIf b c1 c2) Q d.
Proof. Admitted.

(*Added by group under supervision from Jesper (does not compile)*)
(*Theorem test_plus : forall P Q c1 c2 p,
  hoare_quad P c1 Q p ->
  hoare_quad P c2 Q (1-p) ->
  hoare_quad P (CPlus p c1 c2) Q.*)


(*Added by group*)
Lemma twoCoins : forall x y,
hoare_quad
    BTrue
    (CSeq (CPlus half (CAsgn x (ANum 1)) (CAsgn x (ANum 2))) (CPlus half (CAsgn y (ANum 1)) (CAsgn y (ANum 2))))
    (x + y = 3)
    (Reals_ext.Prob.p half).
Proof.
intros. unfold hoare_quad. intros. destruct x. Admitted.




