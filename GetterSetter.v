Require Import Coq.Lists.List.

Import ListNotations.

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

Module Actor.
  Class C (A : Type) (loc : Signature.t) (sig : Signature.t) : Type := New {
    act : forall (T : Type),
      (A -> T * A) -> Memory.t sig -> T * Memory.t sig }.
  
  Instance cons_left (A : Type) (sig : Signature.t)
    : C A sig (A :: sig) := {
    act T f mem :=
      let v := Memory.head mem in
      let (x, v) := f v in
      (x, Memory.Cons v (Memory.tail mem)) }.
  
  Instance cons_right (A B : Type) (loc sig : Signature.t)
    (I : C A loc sig) : C A loc (B :: sig) := {
    act T f mem :=
      let (x, mem') := act T f (Memory.tail mem) in
      (x, Memory.Cons (Memory.head mem) mem') }.
End Actor.

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
  
  Definition act (sig loc : Signature.t) (A : Type) (a : Actor.C A loc sig)
    (T : Type) (f : A -> T * A)
    : M.t sig T :=
    fun s =>
      Actor.act (C := a) T f s.
  Arguments act [sig loc A] _ [T] _ _.
  
  Definition get (sig loc : Signature.t) (A : Type) (a : Actor.C A loc sig)
    : M.t sig A :=
    act a (fun v => (v, v)).
  Arguments get [sig loc A] _ _.
  
  Definition set (sig loc : Signature.t) (A : Type) (a : Actor.C A loc sig)
    (x : A) : M.t sig unit :=
    act a (fun _ => (tt, x)).
  Arguments set [sig loc A] _ _ _.
  
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

Module Test.
  Import M.Notations.
  
  Definition incr (sig loc : Signature.t) (a : Actor.C nat loc sig)
    : M.t sig unit :=
    let! n := M.get a in
    M.set a (S n).
  Arguments incr [sig loc] _ _.
  
  Definition sig : Signature.t := [bool : Type; nat : Type].
  Definition mem : Memory.t sig :=
    Memory.Cons false (Memory.Cons 12 Memory.Nil).
  
  Definition two : nat :=
    M.run mem (
      let a : Actor.C nat _ _ := _ in
      do! M.set a 0 in
      do! incr a in
      do! incr a in
      M.get a).

  Compute two.
  
  Definition test (sig : Signature.t) :=
    let a : Actor.C nat sig _ := _ in
      do! M.set a 0 in
      do! incr a in
      do! incr a in
      M.get a.
End Test.


