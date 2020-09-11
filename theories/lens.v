(*
 * Copyright (C) BedRock Systems Inc. 2019-2020 Gregory Malecha
 *
 * SPDX-License-Identifier: LGPL-2.1 WITH BedRock Exception for use over network, see repository root for details.
 *)
Set Primitive Projections.
(* Set Universe Polymorphism. *)

Record Lens (a b c d : Type) : Type :=
{ view : a -> c
; over : (c -> d) -> a -> b
}.

Arguments over {_ _ _ _} _ _ _.
Arguments view {_ _ _ _} _ _.

Definition compose {a b c d e f : Type}
           (l1 : Lens a b c d) (l2 : Lens c d e f)
: Lens a b e f :=
{| view := fun x : a => view l2 (view l1 x)
 ; over := fun f0 : e -> f => over l1 (over l2 f0) |}.

Section ops.
  Context {a b c d : Type} (l : Lens a b c d).

  Definition set (new : d) : a -> b :=
    l.(over) (fun _ => new).
End ops.
