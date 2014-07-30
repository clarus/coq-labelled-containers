(** A simple and specialized version of labelled containers. *)
Require Import Coq.Lists.List.
Require Import Coq.Strings.Ascii.
Require Import Coq.Strings.String.

Module String.
  Fixpoint eqb (s1 s2 : string) : bool :=
    match (s1, s2) with
    | (EmptyString, EmptyString) => true
    | (EmptyString, String _ _) => false
    | (String _ _, EmptyString) => false
    | (String c1 s1, String c2 s2) =>
      if ascii_dec c1 c2 then
        eqb s1 s2
      else
        false
    end.
End String.

Definition test_to_unit (test : bool) :=
  if test then
    unit
  else
    Empty_set.

Definition unit_to_test (test : bool) (tt : test_to_unit test) : test = true.
  destruct test; [reflexivity | destruct tt].
Defined.

Module Map.
  Definition t : Type := list (string * Type).

  Definition empty : t :=
    nil.

  Fixpoint add (map : t) (label : string) (A : Type) : t :=
    match map with
    | nil => (label, A) :: nil
    | (label', A') :: map =>
      if String.eqb label label' then
        (label, A) :: map
      else
        (label', A') :: add map label A
    end.

  Fixpoint does_contain (map : t) (label : string) : bool :=
    match map with
    | nil => false
    | (label', _) :: map => orb (String.eqb label label') (does_contain map label)
    end.

  Fixpoint find_aux (map : t) (label : string) (H : does_contain map label = true) {struct map} : Type.
    destruct map as [|(label', A') map]; simpl in H.
    - refine (False_rect _ _).
      congruence.
    - destruct (String.eqb label label'); simpl in H.
      + exact A'.
      + exact (find_aux map label H).
  Defined.

  Definition find (map : t) (label : string) (tt : test_to_unit (does_contain map label)) : Type :=
    find_aux map label (unit_to_test _ tt).

  Module Example.
    Definition m1 : t := add (add (add (add empty "n" nat) "b" bool) "u" nat) "u" unit.

    Compute m1.
    Compute find m1 "b" tt.
    Fail Compute find m1 "bb" tt.
  End Example.
End Map.