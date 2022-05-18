Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
From Coq Require Import Bool.Bool.
From Coq Require Import Init.Nat.
From Coq Require Import Arith.Arith.
From Coq Require Import Arith.EqNat.
From Coq Require Import Arith.PeanoNat. Import Nat.
From Coq Require Import Lia.
From Coq Require Import Lists.List. Import ListNotations.
From Coq Require Import Strings.String.

From mathcomp.ssreflect Require Import all_ssreflect.
From mathcomp Require Import finmap.
From infotheo Require Import fsdist proba.
Require Import Reals.
From PV Require Export Main.

(*Definition var := ordinal 64.*)

(*Definition state := {ffun var -> nat}.*)


Definition Assertion := AExp.state -> Prop.

Definition assert_implies (P Q : Assertion) : Prop :=
    forall st, P st -> Q st.


Declare Scope hoare_spec_scope.
Notation "P ->> Q" := (assert_implies P Q)
                        (at level 80) : hoare_spec_scope.
Open Scope hoare_spec_scope.

Notation "P <<->> Q" :=
  (P ->> Q /\ Q ->> P) (at level 80) : hoare_spec_scope.

  Definition Aexp : Type := AExp.state -> nat.

  Definition assert_of_Prop (P : Prop) : Assertion := fun _ => P.
  Definition Aexp_of_nat (n : nat) : Aexp := fun _ => n.
  Definition Aexp_of_aexp (a : AExp.aexp) : Aexp := fun st => AExp.aeval st a.


Coercion assert_of_Prop : Sortclass >-> Assertion.
Coercion Aexp_of_nat : nat >-> Aexp.
Coercion Aexp_of_aexp : AExp.aexp >-> Aexp.

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
(*Notation "st '=[' c ']=>' st'" := (AExp.ceval c st st') (at level 40, c custom AExp.com at level 99,
st constr, st' constr at next level) : assertion_scope.*)


Definition ap {X} (f : nat -> X) (x : Aexp) :=
  fun st => f (x st).

Definition ap2 {X} (f : nat -> nat -> X) (x : Aexp) (y : Aexp) (st : AExp.state) :=
  f (x st) (y st).


(* ################## HOARE QUADRUPLES ################# *)

(*Definition hoare_triple
           (P : Assertion) (c : AExp.com) (Q : Assertion) : Prop :=
  forall st st',
     AExp.ceval (st c)  ->
     P st  ->
     Q st'.*)

Check AExp.ceval.
     
Check (finsupp (_ : FSDist_to_Type
(A:=finfun_choiceType (ordinal_finType 64) nat_choiceType)
(Phant (finfun_choiceType (ordinal_finType 64) nat_choiceType)))).

Local Open Scope proba_scope.
Local Open Scope com_scope.

Definition hoare_quad
            (P : Assertion) (c : AExp.com) (Q : Assertion) (d : R) : Prop :=
    forall st,
        P st ->
        let dst' := (AExp.ceval st c) in 
        forall (s : {set [finType of finsupp dst']}),
        (forall st', st' \in s <-> Q (fsval st')) ->
        Pr (fdist_of_Dist dst') s = d.

Notation "{{ P }}  c  {{ Q }}" :=
  (hoare_quad P c Q) (at level 90, c custom com at level 99)
  : com_scope.

Theorem test_skip: forall P,
  hoare_quad P AExp.CSkip P 1.
Proof.
intros. unfold hoare_quad. intros.
  move => P /=.
  rewrite /hoare_quad.
    move => st HPst s HQs //.
    rewrite /FSDist1.d /FSDist1.f /=.
    unfold FSDist1.d. unfold FSDist1.f. simpl in *.
    assert (H: [set st] \subset s). Admitted.


    Theorem test_seq : forall P Q R d1 d2 c1 c2,
    hoare_quad Q c2 R d1 ->
    hoare_quad P c1 Q d2 ->
    hoare_quad P (AExp.CSeq c1 c2) R (d1 * d2).
Proof. Admitted.

Definition bassn b : Assertion :=
  fun st => (AExp.beval st b = true).

Coercion bassn : AExp.bexp >-> Assertion.

Arguments bassn /.



Search AExp.bexp Assertion.
Theorem test_if : forall P Q (b: AExp.bexp) d c1 c2,
  hoare_quad (P /\ bassn b) c1 Q d ->
  hoare_quad (P /\ ~b) c2 Q d ->
  hoare_quad P (AExp.CIf b c1 c2) Q d.
Proof. Admitted.


Theorem test_plus forall P Q c1 c2 p,
  hoare_quad P c1 Q p ->
  hoare_quad P c2 Q (1-p) ->
  hoare_quad P (AExp.CPlus p c1 c2) Q

    

(* Prove that [set st] \subset s *)
(* Lemma Pr_incl E E' : E \subset E' -> Pr E <= Pr E'. *)
Pr [set st] <= Pr s <= 1
(* Lemma Pr_1 E : Pr E <= 1. *)
(* Lemma Pr_set1 a : Pr [set a] = P a. *)
(* Lemma f1 (d : t) : \sum_(a <- finsupp d) d a = 1.*)

(*Theorem hoare_skip : forall P,
  {{ P }} <{ skip }> {{ P }}.
Proof.*)
