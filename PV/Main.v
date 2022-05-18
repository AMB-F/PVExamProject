
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


Definition state := {ffun var -> nat}.

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
  move => m x1 x2 v.
  rewrite /t_update => /=.
  intros h1.
  rewrite ffunE ifT. subst.
  destruct h1.
  Admitted.


Lemma t_update_shadow : forall m x v1 v2,
  (x !-> v2 ; x !-> v1 ; m) = (x !-> v2 ; m).
  Proof.
    move => m x v1 v2.
    rewrite /t_update.
    apply ffunP => x0.
    case (eq_dec x x0) => eq.
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


(*
Fixpoint sample x a1 as_ := match as_ with
  [] => (<{ x := a1 }>)
  | (a2::as__) => <{ x := a1 [+ (Rdiv R1 (INR (List.length as_)))] (sample x a2 as__) }>
  end.
*)

Search Reals_ext.Prob.t.

(*Fixpoint sample x a1 as_ := 
  match as_ with
  | [] => (<{x := a1}>)
  | (a2::as__) => <{ x := a1 [+ (Reals_ext.probdivRnnm 1 (List.length as_))] (sample x a2 as__)}>
  end.*)

(*Lemma Prob_1_Div_Gt_0 : forall (n : nat),
  Rgt (Rdiv R1 (INR (n))) R0.
Proof.
intros. apply ssrR.divR_gt0.
Admitted.*)

(*Rinv_0_lt_compat: Hvis R>0 så (1/R) > 0*)


(*Search R1. Search Rlt. Search Rgt. assert (h1: Rgt R0 R1 -> R1 = R0 -> False).
  -- Search R1. apply Rgt_not_eq. *)

(*Lemma Prob_1_Div_Lte_1 : forall (n : nat),
  Rlt (Rdiv R1 (INR (n))) R1.
Proof.
intros. Search INR.
Admitted.*)

Search Reals_ext.Prob.t.



Fixpoint sample x a1 as_ := 
  match as_ with
  | [] => (<{x := a1}>)
  | (a2::as__) => <{ x := a1 [+ (Reals_ext.probdivRnnm 1 (List.length as_))] (sample x a2 as__)}>
  end.

Notation "x '$=' { a1 ; a2 ; .. ; an }" := (sample x a1 (cons a2 .. (cons an nil) ..))
  (in custom com at level 0, x constr at level 0,
  a1 at level 85, a2 at level 85, an at level 85, no associativity) : com_scope.


Definition plus2 : com :=
  <{ X := X + 2 }>.

Definition half : Reals_ext.Prob.t := Reals_ext.probdivRnnm 1 2.

Definition split : com :=
  <{ skip [+ half] skip }>.

Definition sampleex : com :=
  <{ X $= {X; 0 + 0} }>.

Definition XtimesYinZ : com :=
  <{ Z := X * Y }>.

Definition subtract_slowly_body : com :=
  <{ Z := Z - 1 ;
      X := X - 1 }>.


Check (FSDist1.d (t_empty 0)).


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


End AExp.






(*============== OLD STUFF ==================================*)


(*Reserved Notation
  "st '=[' c ']=>' st'"
  (at level 40, c custom com at level 99,
   st constr, st' constr at next level).

Type FSDist1.d.*)

(*Inductive ceval : com -> state -> state -> Reals_ext.Prob.t :=
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

  where "st =[ c ]=> st'" := (ceval c st st').*)


(*Definition state := mathcomp.ssreflect.fintype.ordinal 3.*)

(*Definition finType_map (A : finType) : finType := A -> A.*)

(*Definition state : finType := ordinal_finType 3.

Check (ordinal_finType 3).

Check state.

Print ordinal_finType.

Search FDist1.d.*)

(*ceval_fun/Imp is the thing you use to make the computation between pre- and postcondition in Hoare*)

(*Fixpoint ceval_fun (st : Main.state) (c : com) : Main.state :=
  match c with
    | skip => (*fdist1 ?*) FDist1.I1
    | 
  end.*)






(*From Imp.v*)
(*Fixpoint ceval_fun (st : state) (c : com) : state :=
  match c with
    | <{ skip }> =>
        st
    | <{ x := a }> =>
        (x !-> (aeval st a) ; st) (*What does the !-> mean?*)
    | <{ c1 ; c2 }> =>
        let st' := ceval_fun_fun_no_while st c1 in
        ceval_fun_fun_no_while st' c2
    | <{ if b then c1 else c2 end}> =>
        if (beval st b)
          then ceval_fun_fun_no_while st c1
          else ceval_fun_fun_no_while st c2
    | <{ x $= as_ }> => st (* bogus, change to make sampling (what is sampling) *)
  end.

  (*From alternative version of Imp.v*)
  Fixpoint ceval_fun_alternative(st : state) (c : com) : state :=
  match c with
    | SKIP =>
        st
    | x ::= a1 =>
        update st x (aeval st a1)
    | c1 ; c2 =>
        let st' := ceval_fun_fun_no_while st c1 in
        ceval_fun_fun_no_while st' c2
    | IFB b THEN c1 ELSE c2 FI =>
        if (beval st b)
          then ceval_fun_fun_no_while st c1
          else ceval_fun_fun_no_while st c2
    | WHILE b DO c END =>
        st  (* bogus *)
  end.*)


(*Type FDist1.f1 state.

Fixpoint skip s:= FDist1.f1 s.*)


(** 
This
i
a 
multi-line
text 
block
*)

(* ################################################################# *)
(** * This is a chaper header *)

(* ================================================================= *)
(** ** Sub-chapter heading *)

(* ################################################################# *)
(** * Denotation functions*)

(** 
skip
assignment x:n
if-else
sequence
direct sum (+) 

Fixpoint example:
Fixpoint pow2 n :=
  match n with
  | 0 => 1
  | S n' => 2 * (pow2 n')
  end.

*)

(*Fixpoint skip s := FDist1.f1 s*)


(* 2022 *)
