Set Primitive Projections.
Set Universe Polymorphism.

Record Lens : Type :=
{ lens_oi :> Type -> Type -> Type
; lens_view : forall {i o} `{oi : lens_oi o i}, o -> i
; lens_set  : forall {i o} `{oi : lens_oi o i}, i -> o -> o
  (* ^ doesn't support strong set *)
; lens_over : forall {o i o' i'}, lens_oi o i -> lens_oi o' i' ->
                                  (i -> i') -> o -> o'
  (* ^ unwieldy to use in practice *)
; view_set : forall o i (z : lens_oi o i) a x,
     @lens_view _ _ z (@lens_set _ _ z x a) = x
; set_view : forall o i (z : lens_oi o i) a,
    @lens_set _ _ z (@lens_view _ _ z a) a = a
; set_set : forall o i (z : lens_oi o i) a x y,
    @lens_set _ _ z y (@lens_set _ _ z x a) = @lens_set _ _ z y a
(*; set_over : forall {i o i'} (l1 : lens_oi o i) (l2 : lens_oi o i') f (x : o),
    lens_over l1 l2 f x = @lens_set _ _ l2 (f (@lens_view _ _ l1 x)) x *)
}.

Variant LC (oi1 oi2 : Type -> Type -> Type) (a b : Type) : Type :=
| LCc {c} (_ : oi1 a c) (_ : oi2 c b).

Definition lens_compose (l1 l2 : Lens) : Lens.
refine
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
  refine (fun o i o' i' oi oi' f => _).
  destruct oi. destruct oi'.
  refine (lens_over l1 _ _ _).
  eassumption. eassumption.
  eapply (lens_over l2).
  eassumption. eassumption.
  assumption.
  { intros.
    destruct z. rewrite view_set. apply view_set. }
  { destruct z; intros. rewrite set_view. apply set_view. }
  { destruct z; intros. repeat first [ rewrite set_set | rewrite view_set | rewrite set_set ]. reflexivity. }
Defined.

Variant Fst (U : Type) : Type -> Type -> Type :=
| FST {T} : Fst U (T * U) T.

Definition lfst {U : Type} : Lens.
unshelve refine {| lens_oi := Fst U |}.
  destruct 1. apply fst.
  destruct 1. refine (fun x '(_,y) => (x,y)).
  { inversion 1; subst. inversion 1; subst. destruct 2. apply (X1 i0, u). }
  all: destruct z; destruct a; reflexivity.
Defined.

Variant Snd (T : Type) : Type -> Type -> Type :=
| SND {U} : Snd T (T * U) U.

Definition lsnd {T : Type} : Lens.
unshelve refine {| lens_oi := Snd T |}.
  destruct 1. apply snd.
  destruct 1. refine (fun y '(x,_) => (x,y)).
  { inversion 1. inversion 1. subst. refine (fun f '(x,y) => (x,f y)). }
  all: destruct z; destruct a; reflexivity.
Defined.

Declare Scope lens_scope.
Delimit Scope lens_scope with lens.

Polymorphic Definition DO_LENS {T : Type} (a : T) {U : Type} (f : T -> U) : U := f a.
Notation "a & b" := (DO_LENS a b%lens) (at level 50, left associativity, format "a '&' '[v' b ']'" ).
Notation "a %= f" := (@lens_over a%lens _ _ _ _ ltac:(repeat econstructor) ltac:(repeat econstructor) f) (at level 45, no associativity).
Notation "a .= b" := (@lens_set a%lens _ _ ltac:(repeat econstructor) b) (at level 45, no associativity).
Notation "a .^ b" := (@lens_view b%lens _ _ ltac:(repeat econstructor) a) (at level 45, no associativity, only parsing).
Notation "a .^ b" := (@lens_view b _ _ _ a%lens) (at level 45, no associativity, only printing).

Notation "a ., b" := (@lens_compose a b) (at level 43, no associativity).

Existing Class lens_oi.
Hint Extern 0 (@lens_oi _ _ _) => repeat econstructor : typeclass_instances.
Hint Extern 0 (_.(lens_oi) _ _) => repeat econstructor : typeclass_instances.

Typeclasses eauto := debug.


Definition zz : nat * nat := (@lens_view (lfst ., lfst) _ _ ltac:(typeclasses eauto) (1,2,true,4)).

Set Printing All.
  refine (@lens_view (lfst ., lfst) _ _ ltac:(repeat econstructor) (1,2,true,4)).
  refine ltac:(typeclasses eauto).
Set Printing All.   repeat econstructor.
  Defined.

(* todo(gmm): it seems necessary to include the explicit types below, but it isn't clear why
 *)
Definition x :=((1,2,true,4) .^ (@lfst nat) ., (@lfst bool)).
Definition y := (1,2,true,4) & (@lfst nat) .= (1,2,false).
Definition CONST {T U : Type} (u : U) : U := u.
Definition z := ((@lfst nat) %= (fun x => x)) (1,2,true,4).
Print y.
Print x.
Set Printing All. Print x.
Compute x.

