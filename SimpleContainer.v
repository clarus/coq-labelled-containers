(** A simple and specialized version of labelled containers. *)
Require Import Coq.Lists.List.
Require Import Coq.Strings.Ascii.
Require Import Coq.Strings.String.

Import ListNotations.

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

Module ReferencesOnTuples.
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

  Module Test.
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
  End Test.
End ReferencesOnTuples.

Module Signature.
  Definition t := list Type.
End Signature.

Module Memory.
  Inductive t : Signature.t -> Type :=
  | Nil : t []
  | Cons : forall (A : Type) (sig : Signature.t), A -> t sig -> t (A :: sig).
  Arguments Cons [A sig] _ _.

  Definition head (A : Type) (sig : Signature.t) (mem : t (A :: sig)) : A :=
    match mem with
    | Cons _ _ x _ => x
    end.
  Arguments head [A sig] _.

  Definition tail (A : Type) (sig : Signature.t) (mem : t (A :: sig)) : t sig :=
    match mem with
    | Cons _ _ _ mem => mem
    end.
  Arguments tail [A sig] _.
End Memory.

Module Ref.
  Class C (A : Type) (sig : Signature.t) := make {
    get : Memory.t sig -> A;
    set : Memory.t sig -> A -> Memory.t sig }.

  Instance cons_left (A : Type) (sig : Signature.t) : C A (A :: sig) := {
    get mem := Memory.head mem;
    set mem x := Memory.Cons x (Memory.tail mem) }.

  Instance cons_right (A B : Type) (sig : Signature.t)
    (I : C A sig) : C A (B :: sig) := {
    get mem := get (Memory.tail mem);
    set mem x := Memory.Cons (Memory.head mem) (set (Memory.tail mem) x) }.
End Ref.

Module Test.
  Definition sig1 : Signature.t := [nat : Type; bool : Type].
  Definition mem1 : Memory.t sig1 :=
    Memory.Cons 12 (Memory.Cons false Memory.Nil).
  
  Compute Ref.get mem1 : nat.
  Compute Ref.get (Ref.set mem1 13) : nat.
  Compute Ref.get mem1 : bool.
  Compute Ref.get (Ref.set mem1 true) : nat.
  Compute Ref.get (Ref.set mem1 true) : bool.
  
  Definition incr (sig : Signature.t) (r : Ref.C nat sig) (mem : Memory.t sig)
    : Memory.t sig :=
    let n : nat := Ref.get mem in
    Ref.set mem (S n).
End Test.

Module M.
  Definition t (sig : Signature.t) (A : Type) :=
    Memory.t sig -> A * Memory.t sig.
  
  Definition ret (sig : Signature.t) (A : Type) (x : A) : t sig A :=
    fun s =>
      (x, s).
  Arguments ret [sig A] _ _.
  
  Definition bind (sig : Signature.t) (A B : Type)
    (x : t sig A) (f : A -> t sig B) : t sig B :=
    fun s =>
      let (x, s) := x s in
      f x s.
  Arguments bind [sig A B] _ _ _.
  
  Definition get (sig : Signature.t) (A : Type) (r : Ref.C A sig)
    : M.t sig A :=
    fun s =>
      (Ref.get (C := r) s, s).
  Arguments get [sig A] _ _.
  
  Definition set (sig : Signature.t) (A : Type) (r : Ref.C A sig) (x : A)
    : M.t sig unit :=
    fun s =>
      (tt, Ref.set (C := r) s x).
  Arguments set [sig A] _ _ _.
  
  Definition run (sig : Signature.t) (A : Type) (mem : Memory.t sig) (x : t sig A)
    : A :=
    fst (x mem).
  Arguments run [sig A] _ _.
  
  Module Notations.
    Notation "'let!' X ':=' A 'in' B" := (bind A (fun X => B))
      (at level 200, X ident, A at level 100, B at level 200).
    
    Notation "'do!' A 'in' B" := (bind A (fun _ => B))
      (at level 200, B at level 200).
  End Notations.
End M.

Module TestMonad.
  Import M.Notations.
  
  Definition incr (sig : Signature.t) (r : Ref.C nat sig) : M.t sig unit :=
    let! n := M.get r in
    M.set r (S n).
  Arguments incr [sig] _ _.
  
  Definition sig : Signature.t := [bool : Type; nat : Type].
  Definition mem : Memory.t sig :=
    Memory.Cons false (Memory.Cons 12 Memory.Nil).
  
  Definition two : nat :=
    M.run mem (
      let r : Ref.C nat _ := _ in
      do! M.set r 0 in
      do! incr r in
      do! incr r in
      M.get r).

  Compute two.
End TestMonad.
