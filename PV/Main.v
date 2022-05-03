
Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
From PV Require Import Maps.
From Coq Require Import Bool.Bool.
From Coq Require Import Arith.Arith.
From Coq Require Import Arith.EqNat.
From Coq Require Import Arith.PeanoNat. Import Nat.
From Coq Require Import Lia.
From PV Require Export Imp.



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

fixpoint skip s := fdist1 s

end.


(* 2022 *)
