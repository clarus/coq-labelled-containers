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

  Fixpoint is_included (map1 map2 : t) : bool :=
    match map1 with
    | nil => true
    | (label1, _) :: map1 => andb (does_contain map2 label1) (is_included map1 map2)
    end.

  Module Example.
    Definition m1 : t := add (add (add (add empty "n" nat) "b" bool) "u" nat) "u" unit.

    Compute m1.
    Compute find m1 "b" tt.
    Fail Compute find m1 "bb" tt.
  End Example.
End Map.

Module LabelledTuple.
  Inductive t : Map.t -> Type :=
  | Nil : t Map.empty
  | Cons : forall (map : Map.t) (label : string) (A : Type), A -> t (Map.add map label A).  
End LabelledTuple.

(** A combination of a let and a try. *)
Module TryLet.
  Definition ret {A B : Type} (result : A) : A + B :=
    inl result.

  Definition raise {A B : Type} (error : B) : A + B :=
    inr error.

  Notation "'try' X ':=' A 'with' E '=>' B 'in' C" :=
    (match A with
    | inl X => C
    | inr E => B
    end)
    (at level 200, X ident, E ident, A at level 100, B at level 200, C at level 200).

  Module List.
    Definition hd A (l : list A) : A + string :=
      match l with
      | nil => raise "hd expected a non-empty list" % string
      | x :: _ => ret x
      end.
  End List.

  Definition f (l : list nat) : nat :=
    try n := List.hd _ l with _ => 0 in
    2 * n.

  Compute List.hd nat nil.
  Compute f nil.
  Compute f (3 :: 5 :: 2 :: nil).
End TryLet.

(** Type classes for labelled tuples (experiments). *)
Module Tagged.
  Inductive t {Label : Type} (label : Label) (A : Type) : Type :=
  | make : A -> t label A.

  Arguments make [Label label A] _.

  Definition open {Label : Type} {label : Label} {A : Type} (x : t label A) : A :=
    match x with
    | make x => x
    end.
End Tagged.

Module Ref.
  Class C (A : Type) (T : Type) := make {
    get : T -> A;
    set : T -> A -> T }.

  Instance unit : C unit unit := {
    get tt := tt;
    set tt tt := tt }.

  Instance pair_left (A B : Type) : C A (A * B) := {
    get xy := fst xy;
    set xy x := (x, snd xy) }.

  Instance pair_right (A B1 B2 : Type) (I : C B1 B2) : C B1 (A * B2) := {
    get xy := get (snd xy);
    set xy y := (fst xy, set (snd xy) y) }.
End Ref.

Definition A : Type := prod nat (prod bool unit).

Definition table : A := (12, (false, tt)).

Compute Ref.get table.
Compute Ref.get (Ref.set table 13).
Compute Ref.get table : bool.
Compute Ref.get (Ref.set table true).
Compute Ref.get (Ref.set table true) : bool.

Open Local Scope string.

Definition A_nat_nat : Type := prod (Tagged.t "one" nat) (prod (Tagged.t "two" nat) unit).

Definition table_nat_nat : A_nat_nat := (Tagged.make 12, (Tagged.make 15, tt)).

Compute Ref.get table_nat_nat.
Compute Ref.get (Ref.set table_nat_nat (Tagged.make 13)).
Compute Tagged.open (label := "two") (Ref.get table_nat_nat).
Compute Ref.get (Ref.set table_nat_nat (Tagged.make (label := "two") 13)).
Compute Tagged.open (label := "two") (Ref.get (Ref.set table_nat_nat (Tagged.make (label := "two") 13))).




