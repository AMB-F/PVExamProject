
Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
From mathcomp.ssreflect Require Import all_ssreflect.
From infotheo Require Import convex fsdist Reals_ext ssrR proba fdist.
From mathcomp Require Import finmap choice.
Require Import Nat Reals List.

Open Scope R_scope.
Open Scope bool_scope.
Open Scope nat_scope.
Open Scope list_scope.
Open Scope proba_scope.
Open Scope convex_scope.

Definition var := ordinal 8.
Definition state := {ffun var -> nat}.

Inductive aexp : Type :=
  | ANum (n : nat)
  | AId (x : var)
  | APlus (a1 a2 : aexp)
  | AMinus (a1 a2 : aexp)
  | AMult (a1 a2 : aexp).

Definition X: var := inord 0.
Definition Y: var := inord 1.
Definition Z: var := inord 2.
Definition W: var := inord 3.

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

Definition t_empty v : state := [ffun x => v].

Definition t_update st i v : state :=
  [ffun x => if i == x then v else st x].

Notation "'_' '!->' v " := (t_empty v)
  (at level 100, right associativity).

Notation "x '!->' v ';' m" := (t_update m x v)
  (at level 100, v at next level, right associativity).

Lemma t_apply_empty : forall x v,
  (_ !-> v) x = v.
  Proof.
    move => x v.
    rewrite /t_empty=> /=.
    by rewrite ffunE.
  Qed.

Lemma t_update_eq : forall m x v,
  (x !-> v ; m) x = v.
Proof.
  move => m x v.
  rewrite /t_update => /=.
  by rewrite ffunE ifT.
  Qed.


Theorem t_update_neq : forall (m : state) x1 x2 v,
  x1 <> x2 -> (x1 !-> v ; m) x2 = m x2.
Proof.
  move => m x1 x2 v hneq.
  rewrite /t_update ffunE ifF => //.
  unfold not in hneq. destruct hneq.



  Admitted.

Lemma t_update_shadow : forall m x v1 v2,
  (x !-> v2 ; x !-> v1 ; m) = (x !-> v2 ; m).
  Proof.
    move => m x v1 v2.
    rewrite /t_update.
    apply ffunP => x0.
    case (Nat.eq_dec x x0) => eq.
    rewrite !ffunE !ifT => //; admit.
    rewrite !ffunE !ifT => //; admit.
Admitted.

Theorem t_update_same : forall (m : state) x,
  (x !-> m x ; m) = m.
Proof.
    move => m x.
    rewrite /t_update => /=.
    rewrite -(ffunE m).
Admitted.

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
Notation "c1 '[+' p ']' c2" := (CPlus p c1 c2) 
       (in custom com at level 90, p at level 85, right associativity) : com_scope.

Fixpoint sample x a1 as_ := 
  match as_ with
  | nil => (<{x := a1}>)
  | (a2::as__) =>
      (let l := List.length as__ in
      let p := (divRnnm 1 l)%:pr in
      <{ x := a1 [+ p ] (sample x a2 as__)}>)
  end.

Notation "x '$=' { a1 ; a2 ; .. ; an }" := (sample x a1 (cons a2 .. (cons an nil) ..))
  (in custom com at level 0, x constr at level 0,
  a1 at level 85, a2 at level 85, an at level 85, no associativity) : com_scope.

Definition plus2 : com :=
  <{ X := X + 2 }>.



(* I've changed this from `probdivRnnm 1 1` to `probdivRnnm 1 2` 
   as that seems to be right
*)
Definition half : prob := probdivRnnm 1 2.

Definition split : com :=
  <{ skip [+ half] skip }>.

Definition sampleex : com :=
  <{ X $= {X; 0 + 0} }>.

Definition XtimesYinZ : com :=
  <{ Z := X * Y }>.

Definition subtract_slowly_body : com :=
  <{ Z := Z - 1 ;
     X := X - 1 }>.

Fixpoint ceval (st : state) (c : com) : {dist state} :=
  match c with
  | <{ skip }> => FSDist1.d st
  | <{ x := a }> => FSDist1.d (x !-> (aeval st a) ; st)
  | <{ c1 ; c2 }> =>
      let dst' := ceval st c1 in
      FSDistBind.d dst' (fun st => ceval st c2)
  | <{ if b then c1 else c2 end }> =>
      if (beval st b)
        then ceval st c1
        else ceval st c2
  | <{ c1 [+ p] c2}> => (ceval st c1) <|p|> (ceval st c2)
  end.

Check ceval.

(* Hoare triples *)

Definition Assertion := {dist state} -> bool.

Definition hoare (P : Assertion) (c : com) (Q : Assertion) : Prop :=
    forall dst,
        (P dst -> Q (FSDistBind.d dst (fun st => ceval st c))) = true.

Notation "{{ P }}  c  {{ Q }}" :=
    (hoare P c Q) (at level 90, c custom com at level 99)
    : com_scope.

Open Scope proba_scope.
(*
Definition certain b dst : bool :=
    Pr dst (fun st => beval st b) == 1.*)

Definition conva : Assertion -> Assertion -> prob -> Assertion.
Admitted.

Axiom convaE : forall P d Q dst1 dst2,
    P dst1 = true ->
    Q dst2 = true ->
    conva P Q d (dst1 <| d |> dst2) = true.

Axiom hskip:
    forall P, {{ P }} skip {{ P }}.

Lemma hskip_proof:
    forall P, {{P}} skip {{P}}.
Proof.
intros. unfold hoare. Admitted.

(*Axiom hasgn:
  forall P x e, {{P}} x := e {{P}}.*)

Axiom hprob:
    forall P c1 c2 Q Q' d,
    {{ P }} c1 {{ Q }} ->
    {{ P }} c2 {{ Q' }} ->
    {{ P }} c1 [+ d ] c2 {{ conva Q Q' d }}.

Lemma hprob_proof:
    forall P c1 c2 Q Q' d,
      {{ P }} c1 {{ Q }} ->
    {{ P }} c2 {{ Q' }} ->
    {{ P }} c1 [+ d ] c2 {{ conva Q Q' d }}.
Proof.
intros. unfold hoare. unfold ceval. apply convaE.

Admitted.

Axiom hseq:
    forall P Q R c1 c2,
    {{ P }} c1 {{ Q }} ->
    {{ Q }} c2 {{ R }} ->
    {{ P }} c1 ; c2 {{ R }}.

Lemma hseq_proof:
  forall P Q R c1 c2,
  {{ P }} c1 {{ Q }} ->
  {{ Q }} c2 {{ R }} ->
  {{ P }} c1 ; c2 {{ R }}.
Proof.
intros. unfold hoare in *. unfold ceval in *.

Admitted.

(*unfold hoare in *. assert ()



subst. apply ceval with (c := <{ c1; c2 }>).*)

Axiom hcons_left:
    forall P Q R c,
    (forall dst, P dst = true -> Q dst = true) ->
    {{ Q }} c {{ R }} ->
    {{ P }} c {{ R }}.

Axiom hcons_right:
    forall P Q R c,
    (forall dst, Q dst = true -> R dst = true) ->
    {{ P }} c {{ Q }} ->
    {{ P }} c {{ R }}.

Search Reals_ext.Prob.t.
Search Pr _.


(* Lemma twoCoins : forall x y,
  {{fun _ => true}}
  x$={ANum 1; ANum 2} ; y $= {ANum 1; ANum 2}
  {{Pr (x + y = 3) == half}}. *)

(*
Definition certain b dst : bool :=
    Pr dst (fun st => beval st b) == 1.*)


Definition validate_postcond (dst: {dist state}) : bool :=
  let dst' := fdist_of_Dist dst in Pr dst' [set st | (st X) + (st Y) == 3] == half.

  (* 
      What is left to do in the function is to verify that the probability
      is equal to 1/2
  *)

Lemma two_coins : forall x y,
  {{ fun _ => true }}
  x $= {ANum 1; ANum 2} ; y $= {ANum 1; ANum 2}
  {{ validate_postcond }}.
Proof.
Admitted.



