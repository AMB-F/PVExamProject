(** * Imp: Simple Imperative Programs *)

Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
From Coq Require Import Bool.Bool.
From Coq Require Import Init.Nat.
From Coq Require Import Arith.Arith.
From Coq Require Import Arith.EqNat. Import Nat.
From Coq Require Import Lia.
From Coq Require Import Lists.List. Import ListNotations.
From Coq Require Import Strings.String.
(* From PV Require Import Maps. *)

From mathcomp.ssreflect Require Import all_ssreflect.
From infotheo Require Import fsdist.
Require Import Reals.

Module AExp.

Definition var := ordinal 64.

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
(* TODO: fix. Notation "[ a_1 .. a_n ]" := [ a_1 .. a_n ]. *)
Notation "'true'"  := true (at level 1).
Notation "'true'"  := BTrue (in custom com at level 0).
Notation "'false'"  := false (at level 1).
Notation "'false'"  := BFalse (in custom com at level 0).
Notation "x <= y" := (BLe x y) (in custom com at level 70, no associativity).
Notation "x = y"  := (BEq x y) (in custom com at level 70, no associativity).
Notation "x && y" := (BAnd x y) (in custom com at level 80, left associativity).
Notation "'~' b"  := (BNot b) (in custom com at level 75, right associativity).

Open Scope com_scope.

(** We can now write [3 + (X * 2)] instead  of [APlus 3 (AMult X 2)],
    and [true && ~(X <= 4)] instead of [BAnd true (BNot (BLe X 4))]. *)

Definition example_aexp : aexp := <{ 3 + (X * 2) }>.
Definition example_bexp : bexp := <{ true && ~(X <= 4) }>.

(** One downside of these and notation tricks -- coercions in
    particular -- is that they can make it a little harder for humans
    to calculate the types of expressions.  If you ever find yourself
    confused, try doing [Set Printing Coercions] to see exactly what
    is going on. *)

Print example_bexp.
(* ===> example_bexp = <{(true && ~ (X <= 4))}> *)

Set Printing Coercions.
Print example_bexp.
(* ===> example_bexp = <{(true && ~ (AId X <= ANum 4))}> *)

Unset Printing Coercions.

(* ================================================================= *)
(** ** Evaluation *)

Definition state := {ffun var -> nat}.

(** The arith and boolean evaluators are extended to handle
    variables in the obvious way, taking a state as an extra
    argument: *)

Fixpoint aeval (st : state) (a : aexp) : nat :=
  match a with
  | ANum n => n
  | AId x => st x                                (* <--- NEW *)
  | <{a1 + a2}> => (aeval st a1) + (aeval st a2)
  | <{a1 - a2}> => (aeval st a1) - (aeval st a2)
  | <{a1 * a2}> => (aeval st a1) * (aeval st a2)
  end.

Fixpoint beval (st : state) (b : bexp) : bool :=
  match b with
  | <{true}>      => true
  | <{false}>     => false
  | <{a1 = a2}>   => (aeval st a1) =? (aeval st a2)
  | <{a1 <= a2}>  => (aeval st a1) <=? (aeval st a2)
  | <{~ b1}>      => negb (beval st b1)
  | <{b1 && b2}>  => andb (beval st b1) (beval st b2)
  end.

(** We specialize our notation for total maps to the specific case of
    states, i.e. using [(_ !-> 0)] as empty state. *)

Definition t_empty v : state := [ffun x => v].

Definition t_update st i v : state :=
  [ffun x => if i == x then v else st x].

Notation "'_' '!->' v" := (t_empty v)
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


Theorem t_update_neq : forall (m: state) x1 x2 v,
  x1 <> x2 ->
  (x1 !-> v ; m) x2 = m x2.
Proof.
  Admitted.

Lemma t_update_shadow : forall m x v1 v2,
  (x !-> v2 ; x !-> v1 ; m) = (x !-> v2 ; m).
Proof.
  move => m x v1 v2.
  rewrite /t_update.
  apply ffunP => x0.
  case (eq_dec x x0) => eq.
  rewrite !ffunE !ifT => //; admit.
  rewrite !ffunE !ifF => //; admit.
Admitted.

Theorem t_update_same : forall (m: state) x,
  (x !-> m x ; m) = m.
Proof.
  move => m x.
  rewrite /t_update => /=.
  rewrite -(ffunE m).
Admitted.

Example aexp1 :
    aeval ( X !-> 5; _ !-> 0 ) <{ 3 + (X * 2) }>
  = 13.
Proof. rewrite /t_update => /=. rewrite t_update_eq. auto. Qed.

Example aexp2 :
    aeval ( X !-> 5 ; Y !-> 4; _ !-> 0 ) <{ Z + (X * Y) }>
  = 20.
Proof. rewrite /t_update => /=.
  rewrite t_update_eq.
  rewrite t_update_neq.
  rewrite t_update_neq.
  rewrite t_apply_empty.
  rewrite t_update_neq.
  rewrite t_update_eq.
  auto.
Admitted.

Example bexp1 :
    beval ( X !-> 5; _ !-> 0 ) <{ true && ~(X <= 4) }>
  = true.
Proof.
  rewrite /t_update => /=.
  rewrite t_update_eq. auto.
Qed.

(* ################################################################# *)
(** * Commands *)

(** Now we are ready define the syntax and behavior of Imp
    _commands_ (sometimes called _statements_). *)

(* ================================================================= *)
(** ** Syntax *)

(** Informally, commands [c] are described by the following BNF
    grammar.

     c := skip | x := a | c ; c | if b then c else c end
         | while b do c end
*)

(** Here is the formal definition of the abstract syntax of
    commands: *)

Inductive com : Type :=
  | CSkip
  | CAsgn (x : var) (a : aexp)
  | CSeq (c1 c2 : com)
  | CIf (b : bexp) (c1 c2 : com)
  | CPlus (p : R) (c1 c2 : com).

(** As for expressions, we can use a few [Notation] declarations to
    make reading and writing Imp programs more convenient. *)

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
Notation "c1 \+ p / c2" := (CPlus p c1 c2) 
            (in custom com at level 90, right associativity) : com_scope.
Fixpoint sample x a1 as_ := match as_ with
  [] => (<{ x := a1 }>)
  | (a2::as__) => CPlus (Rdiv R1 (INR (List.length as_))) <{x := a1}> (sample x a2 as__) 
  end.
Notation "x '$=' { a1 ; a2 ; .. ; an }" := (sample x a1 (cons a2 .. (cons an nil) ..))
  (in custom com at level 0, x constr at level 0,
  a1 at level 85, a2 at level 85, an at level 85, no associativity) : com_scope.

(* ================================================================= *)
(** ** Desugaring notations *)

(** Coq offers a rich set of features to manage the increasing
    complexity of the objects we work with, such as coercions
    and notations. However, their heavy usage can make for quite
    overwhelming syntax. It is often instructive to "turn off"
    those features to get a more elementary picture of things,
    using the following commands:

    - [Unset Printing Notations] (undo with [Set Printing Notations])
    - [Set Printing Coercions] (undo with [Unset Printing Coercions])
    - [Set Printing All] (undo with [Unset Printing All])

    These commands can also be used in the middle of a proof,
    to elaborate the current goal and context.
 *)

(* ================================================================= *)
(** ** The [Locate] command *)

(* ----------------------------------------------------------------- *)
(** *** Finding notations *)

(** When faced with unknown notation, use [Locate] with a _string_
    containing one of its symbols to see its possible interpretations. *)
Locate "&&".
(* ===>
    Notation
      "x && y" := BAnd x y (default interpretation)
      "x && y" := andb x y : bool_scope (default interpretation)
*)
Locate ";".
(* ===>
    Notation
      "x '|->' v ';' m" := update m x v (default interpretation)
      "x ; y" := CSeq x y : com_scope (default interpretation)
      "x '!->' v ';' m" := t_update m x v (default interpretation)
      "[ x ; y ; .. ; z ]" := cons x (cons y .. (cons z nil) ..) : list_scope
      (default interpretation) *)


(* ----------------------------------------------------------------- *)
(** *** Finding identifiers *)

(** When used with an identifier, the command [Locate] prints
    the full path to every value in scope with the same name.
    This is useful to troubleshoot problems due to variable
    shadowing. *)
Locate aexp.
(* ===>
     Inductive LF.Imp.aexp
     Inductive LF.Imp.AExp.aexp
       (shorter name to refer to it in current context is AExp.aexp)
     Inductive LF.Imp.aevalR_division.aexp
       (shorter name to refer to it in current context is aevalR_division.aexp)
     Inductive LF.Imp.aevalR_extended.aexp
       (shorter name to refer to it in current context is aevalR_extended.aexp)
*)

(* ================================================================= *)
(** ** More Examples *)

Definition plus2 : com :=
  <{ X := X + 2 }>.

Definition sampleex : com :=
  <{ X $= {X + 0; 0 + 0} }>.

Definition XtimesYinZ : com :=
  <{ Z := X * Y }>.

Definition subtract_slowly_body : com :=
  <{ Z := Z - 1 ;
     X := X - 1 }>.

Check (FSDist1.d (t_empty 0)).

Fixpoint ceval (st : state) (c : com) :=
  match c with
    | <{ skip }> =>
      FSDist1.d st
    | <{ x := a }> =>
      FSDist1.d (x !-> (aeval st a) ; st)
    | <{ c1 \+ p / c2 }> => FSDist1.d st (* bogus *)
    | <{ c1 ; c2 }> =>
        let st' := ceval st c1 in
        FSDistBind.d st' (fun st => ceval st c2)
    | <{ if b then c1 else c2 end}> =>
        if (beval st b)
          then ceval st c1
          else ceval st c2
  end.

(** In a traditional functional programming language like OCaml or
    Haskell we could add the [while] case as follows:

        Fixpoint ceval_fun (st : state) (c : com) : state :=
          match c with
            ...
            | <{ while b do c end}> =>
                if (beval st b)
                  then ceval_fun st <{c ; while b do c end}>
                  else st
          end.

    Coq doesn't accept such a definition ("Error: Cannot guess
    decreasing argument of fix") because the function we want to
    define is not guaranteed to terminate. Indeed, it _doesn't_ always
    terminate: for example, the full version of the [ceval_fun]
    function applied to the [loop] program above would never
    terminate. Since Coq is not just a functional programming language
    but also a consistent logic, any potentially non-terminating
    function needs to be rejected. Here is an (invalid!) program
    showing what would go wrong if Coq allowed non-terminating
    recursive functions:

         Fixpoint loop_false (n : nat) : False := loop_false n.

    That is, propositions like [False] would become provable
    ([loop_false 0] would be a proof of [False]), which would be
    a disaster for Coq's logical consistency.

    Thus, because it doesn't terminate on all inputs, [ceval_fun]
    cannot be written in Coq -- at least not without additional tricks
    and workarounds (see chapter [ImpCEvalFun] if you're curious
    about what those might be). *)

(* ================================================================= *)
(** ** Evaluation as a Relation *)

(** Here's a better way: define [ceval] as a _relation_ rather than a
    _function_ -- i.e., define it in [Prop] instead of [Type], as we
    did for [aevalR] above. *)

(** This is an important change.  Besides freeing us from awkward
    workarounds, it gives us a lot more flexibility in the definition.
    For example, if we add nondeterministic features like [any] to the
    language, we want the definition of evaluation to be
    nondeterministic -- i.e., not only will it not be total, it will
    not even be a function! *)

(** We'll use the notation [st =[ c ]=> st'] for the [ceval] relation:
    [st =[ c ]=> st'] means that executing program [c] in a starting
    state [st] results in an ending state [st'].  This can be
    pronounced "[c] takes state [st] to [st']". *)

(* ----------------------------------------------------------------- *)
(** *** Operational Semantics *)

(** Here is an informal definition of evaluation, presented as inference
    rules for readability:

                           -----------------                            (E_Skip)
                           st =[ skip ]=> st

                           aeval st a = n
                   -------------------------------                      (E_Asgn)
                   st =[ x := a ]=> (x !-> n ; st)

                           st  =[ c1 ]=> st'
                           st' =[ c2 ]=> st''
                         ---------------------                           (E_Seq)
                         st =[ c1;c2 ]=> st''

                          beval st b = true
                           st =[ c1 ]=> st'
                --------------------------------------               (E_IfTrue)
                st =[ if b then c1 else c2 end ]=> st'

                         beval st b = false
                           st =[ c2 ]=> st'
                --------------------------------------              (E_IfFalse)
                st =[ if b then c1 else c2 end ]=> st'

                         beval st b = false
                    -----------------------------                 (E_WhileFalse)
                    st =[ while b do c end ]=> st

                          beval st b = true
                           st =[ c ]=> st'
                  st' =[ while b do c end ]=> st''
                  --------------------------------                 (E_WhileTrue)
                  st  =[ while b do c end ]=> st''
*)

(** Here is the formal definition.  Make sure you understand
    how it corresponds to the inference rules. *)

Reserved Notation
         "st '=[' c ']=>' st'"
         (at level 40, c custom com at level 99,
          st constr, st' constr at next level).

Inductive ceval : com -> state -> state -> Prop :=
  | E_Skip : forall st,
      st =[ skip ]=> st
  | E_Asgn  : forall st a n x,
      aeval st a = n ->
      st =[ x := a ]=> (x !-> n ; st)
  | E_Seq : forall c1 c2 st st' st'',
      st  =[ c1 ]=> st'  ->
      st' =[ c2 ]=> st'' ->
      st  =[ c1 ; c2 ]=> st''
  | E_IfTrue : forall st st' b c1 c2,
      beval st b = true ->
      st =[ c1 ]=> st' ->
      st =[ if b then c1 else c2 end]=> st'
  | E_IfFalse : forall st st' b c1 c2,
      beval st b = false ->
      st =[ c2 ]=> st' ->
      st =[ if b then c1 else c2 end]=> st'
  | E_WhileFalse : forall b st c,
      beval st b = false ->
      st =[ while b do c end ]=> st
  | E_WhileTrue : forall st st' st'' b c,
      beval st b = true ->
      st  =[ c ]=> st' ->
      st' =[ while b do c end ]=> st'' ->
      st  =[ while b do c end ]=> st''

  where "st =[ c ]=> st'" := (ceval c st st').

(** The cost of defining evaluation as a relation instead of a
    function is that we now need to construct _proofs_ that some
    program evaluates to some result state, rather than just letting
    Coq's computation mechanism do it for us. *)

Example ceval_example1:
  empty_st =[
     X := 2;
     if (X <= 1)
       then Y := 3
       else Z := 4
     end
  ]=> (Z !-> 4 ; X !-> 2).
Proof.
  (* We must supply the intermediate state *)
  apply E_Seq with (X !-> 2).
  - (* assignment command *)
    apply E_Asgn. reflexivity.
  - (* if command *)
    apply E_IfFalse.
    reflexivity.
    apply E_Asgn. reflexivity.
Qed.

(** **** Exercise: 2 stars, standard (ceval_example2) *)
Example ceval_example2:
  empty_st =[
    X := 0;
    Y := 1;
    Z := 2
  ]=> (Z !-> 2 ; Y !-> 1 ; X !-> 0).
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

Set Printing Implicit.
Check @ceval_example2.

(** **** Exercise: 3 stars, standard, optional (pup_to_n)

    Write an Imp program that sums the numbers from [1] to [X]
    (inclusive: [1 + 2 + ... + X]) in the variable [Y].  Your program
    should update the state as shown in theorem [pup_to_2_ceval],
    which you can reverse-engineer to discover the program you should
    write.  The proof of that theorem will be somewhat lengthy. *)

Definition pup_to_n : com
  (* REPLACE THIS LINE WITH ":= _your_definition_ ." *). Admitted.

Theorem pup_to_2_ceval :
  (X !-> 2) =[
    pup_to_n
  ]=> (X !-> 0 ; Y !-> 3 ; X !-> 1 ; Y !-> 2 ; Y !-> 0 ; X !-> 2).
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(* ================================================================= *)
(** ** Determinism of Evaluation *)

(** Changing from a computational to a relational definition of
    evaluation is a good move because it frees us from the artificial
    requirement that evaluation should be a total function.  But it
    also raises a question: Is the second definition of evaluation
    really a partial _function_?  Or is it possible that, beginning from
    the same state [st], we could evaluate some command [c] in
    different ways to reach two different output states [st'] and
    [st'']?

    In fact, this cannot happen: [ceval] _is_ a partial function: *)

Theorem ceval_deterministic: forall c st st1 st2,
     st =[ c ]=> st1  ->
     st =[ c ]=> st2 ->
     st1 = st2.
Proof.
  intros c st st1 st2 E1 E2.
  generalize dependent st2.
  induction E1; intros st2 E2; inversion E2; subst.
  - (* E_Skip *) reflexivity.
  - (* E_Asgn *) reflexivity.
  - (* E_Seq *)
    rewrite (IHE1_1 st'0 H1) in *.
    apply IHE1_2. assumption.
  - (* E_IfTrue, b evaluates to true *)
      apply IHE1. assumption.
  - (* E_IfTrue,  b evaluates to false (contradiction) *)
      rewrite H in H5. discriminate.
  - (* E_IfFalse, b evaluates to true (contradiction) *)
      rewrite H in H5. discriminate.
  - (* E_IfFalse, b evaluates to false *)
      apply IHE1. assumption.
  - (* E_WhileFalse, b evaluates to false *)
    reflexivity.
  - (* E_WhileFalse, b evaluates to true (contradiction) *)
    rewrite H in H2. discriminate.
  - (* E_WhileTrue, b evaluates to false (contradiction) *)
    rewrite H in H4. discriminate.
  - (* E_WhileTrue, b evaluates to true *)
    rewrite (IHE1_1 st'0 H3) in *.
    apply IHE1_2. assumption.  Qed.

(* ################################################################# *)
(** * Reasoning About Imp Programs *)

(** We'll get deeper into more systematic and powerful techniques for
    reasoning about Imp programs in _Programming Language
    Foundations_, but we can get some distance just working with the
    bare definitions.  This section explores some examples. *)

Theorem plus2_spec : forall st n st',
  st X = n ->
  st =[ plus2 ]=> st' ->
  st' X = n + 2.
Proof.
  intros st n st' HX Heval.

  (** Inverting [Heval] essentially forces Coq to expand one step of
      the [ceval] computation -- in this case revealing that [st']
      must be [st] extended with the new value of [X], since [plus2]
      is an assignment. *)

  inversion Heval. subst. clear Heval. simpl.
  apply t_update_eq.  Qed.

(** **** Exercise: 3 stars, standard, optional (XtimesYinZ_spec)

    State and prove a specification of [XtimesYinZ]. *)

(* FILL IN HERE *)

(* Do not modify the following line: *)
Definition manual_grade_for_XtimesYinZ_spec : option (nat*string) := None.
(** [] *)

(** **** Exercise: 3 stars, standard, especially useful (loop_never_stops) *)
Theorem loop_never_stops : forall st st',
  ~(st =[ loop ]=> st').
Proof.
  intros st st' contra. unfold loop in contra.
  remember <{ while true do skip end }> as loopdef
           eqn:Heqloopdef.

  (** Proceed by induction on the assumed derivation showing that
      [loopdef] terminates.  Most of the cases are immediately
      contradictory (and so can be solved in one step with
      [discriminate]). *)

  (* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 3 stars, standard (no_whiles_eqv)

    Consider the following function: *)

Fixpoint no_whiles (c : com) : bool :=
  match c with
  | <{ skip }> =>
      true
  | <{ _ := _ }> =>
      true
  | <{ c1 ; c2 }> =>
      andb (no_whiles c1) (no_whiles c2)
  | <{ if _ then ct else cf end }> =>
      andb (no_whiles ct) (no_whiles cf)
  | <{ while _ do _ end }>  =>
      false
  end.

(** This predicate yields [true] just on programs that have no while
    loops.  Using [Inductive], write a property [no_whilesR] such that
    [no_whilesR c] is provable exactly when [c] is a program with no
    while loops.  Then prove its equivalence with [no_whiles]. *)

Inductive no_whilesR: com -> Prop :=
 (* FILL IN HERE *)
.

Theorem no_whiles_eqv:
  forall c, no_whiles c = true <-> no_whilesR c.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 4 stars, standard (no_whiles_terminating)

    Imp programs that don't involve while loops always terminate.
    State and prove a theorem [no_whiles_terminating] that says this.

    Use either [no_whiles] or [no_whilesR], as you prefer. *)

(* FILL IN HERE *)

(* Do not modify the following line: *)
Definition manual_grade_for_no_whiles_terminating : option (nat*string) := None.
(** [] *)

(* ################################################################# *)
(** * Additional Exercises *)

(** **** Exercise: 3 stars, standard (stack_compiler)

    Old HP Calculators, programming languages like Forth and Postscript,
    and abstract machines like the Java Virtual Machine all evaluate
    arithmetic expressions using a _stack_. For instance, the expression

      (2*3)+(3*(4-2))

   would be written as

      2 3 * 3 4 2 - * +

   and evaluated like this (where we show the program being evaluated
   on the right and the contents of the stack on the left):

      [ ]           |    2 3 * 3 4 2 - * +
      [2]           |    3 * 3 4 2 - * +
      [3, 2]        |    * 3 4 2 - * +
      [6]           |    3 4 2 - * +
      [3, 6]        |    4 2 - * +
      [4, 3, 6]     |    2 - * +
      [2, 4, 3, 6]  |    - * +
      [2, 3, 6]     |    * +
      [6, 6]        |    +
      [12]          |

  The goal of this exercise is to write a small compiler that
  translates [aexp]s into stack machine instructions.

  The instruction set for our stack language will consist of the
  following instructions:
     - [SPush n]: Push the number [n] on the stack.
     - [SLoad x]: Load the identifier [x] from the store and push it
                  on the stack
     - [SPlus]:   Pop the two top numbers from the stack, add them, and
                  push the result onto the stack.
     - [SMinus]:  Similar, but subtract the first number from the second.
     - [SMult]:   Similar, but multiply. *)

Inductive sinstr : Type :=
| SPush (n : nat)
| SLoad (x : string)
| SPlus
| SMinus
| SMult.

(** Write a function to evaluate programs in the stack language. It
    should take as input a state, a stack represented as a list of
    numbers (top stack item is the head of the list), and a program
    represented as a list of instructions, and it should return the
    stack after executing the program.  Test your function on the
    examples below.

    Note that it is unspecified what to do when encountering an
    [SPlus], [SMinus], or [SMult] instruction if the stack contains
    fewer than two elements.  In a sense, it is immaterial what we do,
    since a correct compiler will never emit such a malformed program.
    But for sake of later exercises, it would be best to skip the
    offending instruction and continue with the next one.  *)

Fixpoint s_execute (st : state) (stack : list nat)
                   (prog : list sinstr)
                 : list nat
  (* REPLACE THIS LINE WITH ":= _your_definition_ ." *). Admitted.

Check s_execute.

Example s_execute1 :
     s_execute empty_st []
       [SPush 5; SPush 3; SPush 1; SMinus]
   = [2; 5].
(* FILL IN HERE *) Admitted.

Example s_execute2 :
     s_execute (X !-> 3) [3;4]
       [SPush 4; SLoad X; SMult; SPlus]
   = [15; 4].
(* FILL IN HERE *) Admitted.

(** Next, write a function that compiles an [aexp] into a stack
    machine program. The effect of running the program should be the
    same as pushing the value of the expression on the stack. *)

Fixpoint s_compile (e : aexp) : list sinstr
  (* REPLACE THIS LINE WITH ":= _your_definition_ ." *). Admitted.

(** After you've defined [s_compile], prove the following to test
    that it works. *)

Example s_compile1 :
  s_compile <{ X - (2 * Y) }>
  = [SLoad X; SPush 2; SLoad Y; SMult; SMinus].
(* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 3 stars, standard (execute_app) *)

(** Execution can be decomposed in the following sense: executing
    stack program [p1 ++ p2] is the same as executing [p1], taking
    the resulting stack, and executing [p2] from that stack. Prove
    that fact. *)

Theorem execute_app : forall st p1 p2 stack,
  s_execute st stack (p1 ++ p2) = s_execute st (s_execute st stack p1) p2.
Proof.
  (* FILL IN HERE *) Admitted.

(** [] *)

(** **** Exercise: 3 stars, standard (stack_compiler_correct) *)

(** Now we'll prove the correctness of the compiler implemented in the
    previous exercise.  Begin by proving the following lemma. If it
    becomes difficult, consider whether your implementation of
    [s_execute] or [s_compile] could be simplified. *)

Lemma s_compile_correct_aux : forall st e stack,
  s_execute st stack (s_compile e) = aeval st e :: stack.
Proof.
  (* FILL IN HERE *) Admitted.

(** The main theorem should be a very easy corollary of that lemma. *)

Theorem s_compile_correct : forall (st : state) (e : aexp),
  s_execute st [] (s_compile e) = [ aeval st e ].
Proof.
  (* FILL IN HERE *) Admitted.

(** [] *)

(** **** Exercise: 3 stars, standard, optional (short_circuit)

    Most modern programming languages use a "short-circuit" evaluation
    rule for boolean [and]: to evaluate [BAnd b1 b2], first evaluate
    [b1].  If it evaluates to [false], then the entire [BAnd]
    expression evaluates to [false] immediately, without evaluating
    [b2].  Otherwise, [b2] is evaluated to determine the result of the
    [BAnd] expression.

    Write an alternate version of [beval] that performs short-circuit
    evaluation of [BAnd] in this manner, and prove that it is
    equivalent to [beval].  (N.b. This is only true because expression
    evaluation in Imp is rather simple.  In a bigger language where
    evaluating an expression might diverge, the short-circuiting [BAnd]
    would _not_ be equivalent to the original, since it would make more
    programs terminate.) *)

(* FILL IN HERE

    [] *)

Module BreakImp.
(** **** Exercise: 4 stars, advanced (break_imp)

    Imperative languages like C and Java often include a [break] or
    similar statement for interrupting the execution of loops. In this
    exercise we consider how to add [break] to Imp.  First, we need to
    enrich the language of commands with an additional case. *)

Inductive com : Type :=
  | CSkip
  | CBreak                        (* <--- NEW *)
  | CAsgn (x : string) (a : aexp)
  | CSeq (c1 c2 : com)
  | CIf (b : bexp) (c1 c2 : com)
  | CWhile (b : bexp) (c : com).

Notation "'break'" := CBreak (in custom com at level 0).
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
Notation "'while' x 'do' y 'end'" :=
         (CWhile x y)
            (in custom com at level 89, x at level 99, y at level 99) : com_scope.

(** Next, we need to define the behavior of [break].  Informally,
    whenever [break] is executed in a sequence of commands, it stops
    the execution of that sequence and signals that the innermost
    enclosing loop should terminate.  (If there aren't any
    enclosing loops, then the whole program simply terminates.)  The
    final state should be the same as the one in which the [break]
    statement was executed.

    One important point is what to do when there are multiple loops
    enclosing a given [break]. In those cases, [break] should only
    terminate the _innermost_ loop. Thus, after executing the
    following...

       X := 0;
       Y := 1;
       while ~(0 = Y) do
         while true do
           break
         end;
         X := 1;
         Y := Y - 1
       end

    ... the value of [X] should be [1], and not [0].

    One way of expressing this behavior is to add another parameter to
    the evaluation relation that specifies whether evaluation of a
    command executes a [break] statement: *)

Inductive result : Type :=
  | SContinue
  | SBreak.

Reserved Notation "st '=[' c ']=>' st' '/' s"
     (at level 40, c custom com at level 99, st' constr at next level).

(** Intuitively, [st =[ c ]=> st' / s] means that, if [c] is started in
    state [st], then it terminates in state [st'] and either signals
    that the innermost surrounding loop (or the whole program) should
    exit immediately ([s = SBreak]) or that execution should continue
    normally ([s = SContinue]).

    The definition of the "[st =[ c ]=> st' / s]" relation is very
    similar to the one we gave above for the regular evaluation
    relation ([st =[ c ]=> st']) -- we just need to handle the
    termination signals appropriately:

    - If the command is [skip], then the state doesn't change and
      execution of any enclosing loop can continue normally.

    - If the command is [break], the state stays unchanged but we
      signal a [SBreak].

    - If the command is an assignment, then we update the binding for
      that variable in the state accordingly and signal that execution
      can continue normally.

    - If the command is of the form [if b then c1 else c2 end], then
      the state is updated as in the original semantics of Imp, except
      that we also propagate the signal from the execution of
      whichever branch was taken.

    - If the command is a sequence [c1 ; c2], we first execute
      [c1].  If this yields a [SBreak], we skip the execution of [c2]
      and propagate the [SBreak] signal to the surrounding context;
      the resulting state is the same as the one obtained by
      executing [c1] alone. Otherwise, we execute [c2] on the state
      obtained after executing [c1], and propagate the signal
      generated there.

    - Finally, for a loop of the form [while b do c end], the
      semantics is almost the same as before. The only difference is
      that, when [b] evaluates to true, we execute [c] and check the
      signal that it raises.  If that signal is [SContinue], then the
      execution proceeds as in the original semantics. Otherwise, we
      stop the execution of the loop, and the resulting state is the
      same as the one resulting from the execution of the current
      iteration.  In either case, since [break] only terminates the
      innermost loop, [while] signals [SContinue]. *)

(** Based on the above description, complete the definition of the
    [ceval] relation. *)

Inductive ceval : com -> state -> result -> state -> Prop :=
  | E_Skip : forall st,
      st =[ CSkip ]=> st / SContinue
  (* FILL IN HERE *)

  where "st '=[' c ']=>' st' '/' s" := (ceval c st s st').

(** Now prove the following properties of your definition of [ceval]: *)

Theorem break_ignore : forall c st st' s,
     st =[ break; c ]=> st' / s ->
     st = st'.
Proof.
  (* FILL IN HERE *) Admitted.

Theorem while_continue : forall b c st st' s,
  st =[ while b do c end ]=> st' / s ->
  s = SContinue.
Proof.
  (* FILL IN HERE *) Admitted.

Theorem while_stops_on_break : forall b c st st',
  beval st b = true ->
  st =[ c ]=> st' / SBreak ->
  st =[ while b do c end ]=> st' / SContinue.
Proof.
  (* FILL IN HERE *) Admitted.

Theorem seq_continue : forall c1 c2 st st' st'',
  st =[ c1 ]=> st' / SContinue ->
  st' =[ c2 ]=> st'' / SContinue ->
  st =[ c1 ; c2 ]=> st'' / SContinue.
Proof.
  (* FILL IN HERE *) Admitted.

Theorem seq_stops_on_break : forall c1 c2 st st',
  st =[ c1 ]=> st' / SBreak ->
  st =[ c1 ; c2 ]=> st' / SBreak.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 3 stars, advanced, optional (while_break_true) *)
Theorem while_break_true : forall b c st st',
  st =[ while b do c end ]=> st' / SContinue ->
  beval st' b = true ->
  exists st'', st'' =[ c ]=> st' / SBreak.
Proof.
(* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 4 stars, advanced, optional (ceval_deterministic) *)
Theorem ceval_deterministic: forall (c:com) st st1 st2 s1 s2,
     st =[ c ]=> st1 / s1 ->
     st =[ c ]=> st2 / s2 ->
     st1 = st2 /\ s1 = s2.
Proof.
  (* FILL IN HERE *) Admitted.

(** [] *)
End BreakImp.

(** **** Exercise: 4 stars, standard, optional (add_for_loop)

    Add C-style [for] loops to the language of commands, update the
    [ceval] definition to define the semantics of [for] loops, and add
    cases for [for] loops as needed so that all the proofs in this
    file are accepted by Coq.

    A [for] loop should be parameterized by (a) a statement executed
    initially, (b) a test that is run on each iteration of the loop to
    determine whether the loop should continue, (c) a statement
    executed at the end of each loop iteration, and (d) a statement
    that makes up the body of the loop.  (You don't need to worry
    about making up a concrete Notation for [for] loops, but feel free
    to play with this too if you like.) *)

(* FILL IN HERE

    [] *)

(* 2021-08-11 15:11 *)
