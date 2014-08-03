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

Module Output.
  Inductive t : Signature.t -> Type :=
  | Nil : t []
  | Cons : forall (A : Type) (channels : Signature.t),
    list A -> t channels -> t (A :: channels).
  Arguments Cons [A channels] _ _.
  
  Definition head (A : Type) (channels : Signature.t)
    (output : t (A :: channels)) : list A :=
    match output with
    | Cons _ _ x _ => x
    end.
  Arguments head [A channels] _.
  
  Definition tail (A : Type) (channels : Signature.t)
    (output : t (A :: channels)) : t channels :=
    match output with
    | Cons _ _ _ output => output
    end.
  Arguments tail [A channels] _.
  
  Fixpoint init (channels : Signature.t) : t channels :=
    match channels with
    | [] => Nil
    | _ :: channels => Cons [] (init channels)
    end.
End Output.

Module Getter.
  Class C (A : Type) (sig : Signature.t) := New {
    get : Memory.t sig -> A }.

  Instance cons_left (A : Type) (sig : Signature.t) : C A (A :: sig) := {
    get mem := Memory.head mem }.

  Instance cons_right (A B : Type) (sig : Signature.t)
    (I : C A sig) : C A (B :: sig) := {
    get mem := get (Memory.tail mem) }.
End Getter.

Module Writer.
  Class C (A : Type) (channels : Signature.t) := New {
    write : Output.t channels -> A -> Output.t channels }.

  Instance cons_left (A : Type) (channels : Signature.t)
    : C A (A :: channels) := {
    write output x := Output.Cons (x :: Output.head output) (Output.tail output) }.

  Instance cons_right (A B : Type) (channels : Signature.t)
    (I : C A channels) : C A (B :: channels) := {
    write output x := Output.Cons (Output.head output) (write (Output.tail output) x) }.
End Writer.

Module C.
  Inductive t (refs channels : Signature.t) : Type -> Type :=
  | ret : forall (A : Type), A ->
    t refs channels A
  | bind : forall (A B : Type),
    t refs channels A -> (A -> t refs channels B) -> t refs channels B
  | get : forall (A : Type), Getter.C A refs ->
    t refs channels A
  | write : forall (A : Type),
    A -> t refs channels unit.
End C.