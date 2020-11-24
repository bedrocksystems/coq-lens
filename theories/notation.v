(*
 * Copyright (C) BedRock Systems Inc. 2019-2020 Gregory Malecha
 *
 * SPDX-License-Identifier: LGPL-2.1 WITH BedRock Exception for use over network, see repository root for details.
 *)
Require Export Lens.lens.

Declare Scope lens_scope.
Delimit Scope lens_scope with lens.
Bind Scope lens_scope with Lens.

(* not sure about these levels *)
Notation "a & b" := (b a) (at level 50, only parsing, left associativity) : lens_scope.
Notation "a %= f" := (lens.over a f) (at level 45, left associativity) : lens_scope.
Notation "a .= b" := (lens.set a b) (at level 45, left associativity) : lens_scope.
Notation "a .^ f" := (lens.view f a) (at level 44, left associativity) : lens_scope.
(* level 19 to be compatible with Iris .@ *)
Notation "a .@ b" := (lens.compose a b) (at level 19, left associativity) : lens_scope.

Global Open Scope lens_scope.
