Require Import Coq.Lists.List.

Import ListNotations.

Module Initialized.
  Record t : Type := New {
    typ : Type;
    init : typ }.
  Arguments New [typ] _.
End Initialized.

Module Signature.
  Definition t := list Initialized.t.
End Signature.

Module Memory.
  Inductive t : Signature.t -> Type :=
  | Nil : t []
  | Cons : forall (A : Initialized.t) (sig : Signature.t),
    Initialized.typ A -> t sig -> t (A :: sig).
  Arguments Cons [A sig] _ _.

  Definition head (A : Initialized.t) (sig : Signature.t) (mem : t (A :: sig))
    : Initialized.typ A :=
    match mem with
    | Cons _ _ x _ => x
    end.
  Arguments head [A sig] _.

  Definition tail (A : Initialized.t) (sig : Signature.t) (mem : t (A :: sig))
    : t sig :=
    match mem with
    | Cons _ _ _ mem => mem
    end.
  Arguments tail [A sig] _.
  
  Fixpoint init (sig : Signature.t) : t sig :=
    match sig with
    | [] => Nil
    | A :: sig => Cons (Initialized.init A) (init sig)
    end.
End Memory.

Module Ref.
  Class C (A : Type) (init : A) (sig : Signature.t) := make {
    get : Memory.t sig -> A;
    set : Memory.t sig -> A -> Memory.t sig }.

  Instance cons_right (A : Type) (init : A) (B : Initialized.t) (sig : Signature.t)
    (I : C A init sig) : C A init (B :: sig) := {
    get mem := get (Memory.tail mem);
    set mem x := Memory.Cons (Memory.head mem) (set (Memory.tail mem) x) }.

  Instance cons_left (A : Initialized.t) (sig : Signature.t)
    : C (Initialized.typ A) (Initialized.init A) (A :: sig) := {
    get mem := Memory.head mem;
    set mem x := Memory.Cons x (Memory.tail mem) }.
End Ref.

Module Test.
  Definition sig1 : Signature.t := [
    Initialized.New 12;
    Initialized.New false].
  Definition mem1 : Memory.t sig1 := Memory.init sig1.
  
  Definition n : nat :=
    let r : Ref.C _ 12 sig1 := _ in
    Ref.get (C := r) mem1.
  
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

  Check (
    let sig := _ in
    let r_nat : Ref.C nat sig := _ in
    let r_bool : Ref.C bool sig := _ in
    do! M.set r_nat 12 in
    do! M.set r_bool false in
    let! n := M.get r_nat in
    let! b := M.get r_bool in
    M.ret (n, b)).