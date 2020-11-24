(*
 * Copyright (C) BedRock Systems Inc. 2019-2020 Gregory Malecha
 *
 * SPDX-License-Identifier: LGPL-2.1 WITH BedRock Exception for use over network, see repository root for details.
 *)
Require Import Lens.notation.
Require Import Lens.TC.TC.

Set Default Proof Using "Type".

Record Oops : Set :=
{ oops1 : nat }.

Fail Run TemplateProgram (genLens Oops).

Set Primitive Projections.

Record Foo : Set :=
{ foo : nat
; bar : bool }.


Run TemplateProgram (genLens Foo).

About _foo.
About _bar.

Goal {| foo := 3 ; bar := true |} .^ _foo = 3.
Proof. reflexivity. Qed.

Goal {| foo := 3 ; bar := true |} .^ _bar = true.
Proof. reflexivity. Qed.

Goal {| foo := 3 ; bar := true |} & _bar .= false = {| foo := 3 ; bar := false |}.
Proof. reflexivity. Qed.

Goal forall a b,
    {| foo := a ; bar := b |} & _bar .= false
                              & _foo .= 21 = {| foo := 21 ; bar := false |}.
Proof. reflexivity. Qed.
