
Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
From PV Require Import Maps.
From Coq Require Import Bool.Bool.
From Coq Require Import Arith.Arith.
From Coq Require Import Arith.EqNat.
From Coq Require Import Arith.PeanoNat. Import Nat.
From Coq Require Import Lia.
From PV Require Export Imp.
From infotheo Require Import fdist proba.
From mathcomp.ssreflect Require Import fintype.


(*Definition state := mathcomp.ssreflect.fintype.ordinal 3.*)

(*Definition finType_map (A : finType) : finType := A -> A.*)

Definition state : finType := ordinal_finType 3.

Check (ordinal_finType 3).

Print ordinal_finType.

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
