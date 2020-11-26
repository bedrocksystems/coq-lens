Set Primitive Projections.

Record Lens : Type :=
{ lens_oi : Type -> Type -> Prop
; lens_view : forall {i o}, lens_oi o i -> o -> i
; lens_set  : forall {o i}, lens_oi o i -> i -> o -> o
(* ; over : forall {o i o' i'}, lens_oi o i -> lens_oi o' i' -> *)
(*                       (i -> i') -> o -> o' *)
; view_set : forall o i (z : lens_oi o i) a x,
    @lens_view _ _ z (@lens_set _ _ z x a) = x
; set_view : forall o i (z : lens_oi o i) a x,
    @lens_set _ _ z (@lens_view _ _ z x) a = a
; set_set : forall o i (z : lens_oi o i) a x y,
    @lens_set _ _ z y (@lens_set _ _ z x a) = @lens_set _ _ z y a
}.






Record Lens (a b c d : Type) : Type :=
{ view : a -> c
; over : (c -> d) -> a -> b
}.


forall X Y, Lens (outer X) (outer Y) (inner X) (inner Y)

Arguments over {_ _ _ _} _ _ _.
Arguments view {_ _ _ _} _ _.

Definition lens_compose {a b c d e f : Type}
           (l1 : Lens a b c d) (l2 : Lens c d e f)
: Lens a b e f :=
{| view := fun x : a => view l2 (view l1 x)
 ; over := fun f0 : e -> f => over l1 (over l2 f0) |}.

Section ops.
  Context {a b c d : Type} (l : Lens a b c d).

  Definition set (new : d) : a -> b :=
    l.(over) (fun _ => new).
End ops.

Module LensNotation.
  Declare Scope lens_scope.
  Delimit Scope lens_scope with lens.

  Polymorphic Definition DO_LENS {T U : Type} (a : T) (f : T -> U) : U := f a.
  Notation "a & b" := (DO_LENS a b%lens) (at level 50, left associativity, format "a '&' '[v' b ']'" ).
  Notation "a %= f" := (Lens.over a%lens f) (at level 45, no associativity).
  Notation "a ^= b" := (Lens.set a%lens b) (at level 45, no associativity).
  Notation "a .^ b" := (Lens.view b a%lens) (at level 45, no associativity).

End LensNotation.
