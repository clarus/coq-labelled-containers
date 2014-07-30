Require Import Coq.Strings.String.
Require Import ExtLib.Structures.Maps.
Require Import ExtLib.Data.String.
Require Import ExtLib.Data.Map.FMapAList.

Definition StringMap := Map_alist RelDec_string.

(* Definition m1 : StringMap (V := nat) := empty. *)

Check StringMap.
Check add.