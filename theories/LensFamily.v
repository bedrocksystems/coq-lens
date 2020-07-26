Set Primitive Projections.
Set Universe Polymorphism.

Record Lens : Type :=
{ lens_oi :> Type -> Type -> Type
; lens_view : forall {i o} `{oi : lens_oi o i}, o -> i
; lens_set  : forall {i o} `{oi : lens_oi o i}, i -> o -> o
(* ; over : forall {o i o' i'}, lens_oi o i -> lens_oi o' i' -> *)
(*                       (i -> i') -> o -> o' *)
(* ; view_set : forall o i (z : lens_oi o i) a x, *)
(*     @lens_view _ _ z (@lens_set _ _ z x a) = x *)
(* ; set_view : forall o i (z : lens_oi o i) a x, *)
(*     @lens_set _ _ z (@lens_view _ _ z x) a = a *)
(* ; set_set : forall o i (z : lens_oi o i) a x y, *)
(*     @lens_set _ _ z y (@lens_set _ _ z x a) = @lens_set _ _ z y a *)
}.

Existing Class lens_oi.

Variant LC (oi1 oi2 : Type -> Type -> Type) (a b : Type) : Type :=
| LCc {c} (_ : oi1 a c) (_ : oi2 c b).

Hint Extern 0 (@lens_oi _ _ _) => repeat (first [ eassumption | econstructor ]) : typeclass_instances.
Typeclasses eauto := debug.
Hint Mode lens_oi + - - : typeclass_instances.

Definition lens_compose (l1 l2 : Lens) : Lens :=
  {| lens_oi := LC l1.(lens_oi) l2.(lens_oi)
   ; lens_view := fun (i o : Type) (oi : LC l1 l2 o i) =>
                    match oi with
                    | @LCc _ _ _ _ c l l0 =>
                      fun X : o => lens_view l2 (oi:=l0) (lens_view l1 (oi:=l) X)
                    end
   ; lens_set := fun (i o : Type) (X : LC l1 l2 o i) =>
                   match X with
                   | @LCc _ _ _ _ c l l0 =>
                     fun (X0 : i) (X1 : o) =>
                       lens_set l1 (oi:=l) (lens_set l2 (oi:=l0) X0 (lens_view l1 (oi:=l) X1)) X1
                   end |}.

Variant Fst : Type -> Type -> Type :=
| FST {T U} : Fst (T * U) T.

Definition lfst : Lens.
refine {| lens_oi := Fst |}.
  destruct 1. apply fst.
  destruct 1. refine (fun x '(_,y) => (x,y)).
Defined.

Variant Snd : Type -> Type -> Type :=
| SND {T U} : Snd (T * U) U.

Definition lsnd : Lens.
refine {| lens_oi := Snd |}.
  destruct 1. apply snd.
  destruct 1. refine (fun y '(x,_) => (x,y)).
Defined.

  Declare Scope lens_scope.
  Delimit Scope lens_scope with lens.

  Polymorphic Definition DO_LENS {T U : Type} (a : T) (f : T -> U) : U := f a.
  Notation "a & b" := (DO_LENS a b%lens) (at level 50, left associativity, format "a '&' '[v' b ']'" ).
  (* Notation "a %= f" := (over a%lens f) (at level 45, no associativity). *)
  (* Notation "a ^= b" := (Lens.set a%lens b) (at level 45, no associativity). *)
  Notation "a .^ b" := (@lens_view b _ _ ltac:(typeclasses eauto) a%lens) (at level 45, no associativity).
  Notation "a ., b" := (@lens_compose a b) (at level 43, no associativity).

Existing Class Fst.
Existing Class Snd.
Existing Instance FST.
Existing Instance SND.

Typeclasses eauto := debug.
Definition x := ((1,2,3,4) .^ lfst ., lfst).
Print x.
Set Printing All. Print x.
Compute x.

: Lens a b e f :=
{| view := fun x : a => view l2 (view l1 x)
 ; over := fun f0 : e -> f => over l1 (over l2 f0) |}.







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

End LensNotation.
