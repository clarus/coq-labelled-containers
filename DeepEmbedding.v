Require Import Coq.Lists.List.
Require Import Coq.Strings.String.

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
  | write : forall (A : Type), Writer.C A channels ->
    A -> t refs channels unit.
  Arguments ret [refs channels A] _.
  Arguments bind [refs channels A B] _ _.
  Arguments get [refs channels A _].
  Arguments write [refs channels A _] _.

  Fixpoint run_aux (refs channels : Signature.t) (A : Type)
    (mem : Memory.t refs) (output : Output.t channels) (x : t refs channels A)
    : A * Output.t channels :=
    match x with
    | ret _ x => (x, output)
    | bind _ _ x f =>
      let (x, output) := run_aux _ _ _ mem output x in
      run_aux _ _ _ mem output (f x)
    | get _ getter => (Getter.get (C := getter) mem, output)
    | write _ writer v => (tt, Writer.write (C := writer) output v)
    end.

  Definition run (refs channels : Signature.t) (A : Type)
    (mem : Memory.t refs) (x : t refs channels A)
    : A * Output.t channels :=
    run_aux _ _ _ mem (Output.init channels) x.
  Arguments run [refs] _ [A] _ _.

  Module Notations.
    Notation "'let!' X ':=' A 'in' B" := (bind A (fun X => B))
      (at level 200, X ident, A at level 100, B at level 200).
    
    Notation "'let!' X ':' T ':=' A 'in' B" := (bind (A := T) A (fun X => B))
    (at level 200, X ident, A at level 100, T at level 200, B at level 200).

    Notation "'do!' A 'in' B" := (bind A (fun _ => B))
      (at level 200, B at level 200).
  End Notations.
End C.

Module Test.
  Import C.Notations.
  Open Local Scope string.

  Definition hello_world (refs channels : Signature.t) `{Writer.C string channels}
    (_ : unit) : C.t refs channels unit :=
    do! C.write _ "Hello " in
    C.write _ "world!".
  Arguments hello_world [refs channels _] _.

  Compute C.run [string : Type] Memory.Nil (hello_world tt).

  Definition read_and_print {refs channels : Signature.t}
    `{Getter.C nat refs} `{Writer.C nat channels}
    (_ : unit) : C.t refs channels unit :=
    let! n : nat := C.get _ in
    C.write _ n.

  Compute C.run [nat : Type] (Memory.Cons 12 Memory.Nil) (read_and_print tt).
End Test.

