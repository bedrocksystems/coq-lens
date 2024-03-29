From Coq.Classes Require Import DecidableClass.
From Coq.Lists Require Import List.
From Coq.Strings Require Import String.
(* Avoid [From MetaCoq.Template Require Import utils All.]
to work around https://github.com/MetaCoq/metacoq/issues/580 *)
From MetaCoq.Template Require Import utils monad_utils.
From MetaCoq.Template Require Import Ast Loader TemplateMonad.
From Lens Require Import Lens.

Import MCMonadNotation.

Set Primitive Projections.

Record Info := {
  type   : ident;
  ctor   : ident;
  fields : list projection_body;
}.

Fixpoint countTo (n : nat) : list nat :=
  match n with
  | 0 => nil
  | S m => countTo m ++ (m :: nil)
  end.

Definition lensName (ls : String.string) (i : ident) : ident :=
  String.of_string (ls ++ String.to_string i).

MetaCoq Quote Definition cBuild_Lens := Build_Lens.

Local Definition mkLens (At : term) (fields : list projection_body) (i : nat)
: option (ident * term) :=
  match At with
  | tInd ind args =>
    let ctor := tConstruct ind 0 args in
    match nth_error fields i with
    | None => None
    | Some body =>
      let name := body.(proj_name) in
      let Bt := body.(proj_type) in (* FIXME use relevance? *)
      let p (x : nat) : projection := mkProjection ind 0 x in
      let get_body := tProj (p i) (tRel 0) in
      let f x :=
        let this := tProj (p x) (tRel 0) in
        if PeanoNat.Nat.eqb x i then tApp (tRel 1) (this :: nil) else this
      in
      let update_body := tApp ctor (map f (countTo (List.length fields))) in
      let def :=
        tApp cBuild_Lens (At :: At :: Bt :: Bt ::
          tLambda (mkBindAnn nAnon Relevant) At get_body ::
          tLambda (mkBindAnn nAnon Relevant) (tProd (mkBindAnn nAnon Relevant) Bt Bt) (tLambda (mkBindAnn nAnon Relevant) At update_body) ::
          nil
        )
      in
      Some (lensName "_" name, def)
    end
  | _ => None
  end.

Fixpoint get_arity (t : term) : nat :=
  match t with
  | tProd _ _ t => S (get_arity t)
  | _ => 0
  end.

Local Definition getFields (mi : mutual_inductive_body) (n : nat) : TemplateMonad Info :=
  match nth_error mi.(ind_bodies) n with
  | None => tmFail "no body for index"
  | Some oib =>
    match oib.(ind_ctors) with
    | nil => tmFail "`getFields` got empty type"
    | ctor :: nil =>
      let ctor_name := ctor.(cstr_name) in
      let ctor_type := ctor.(cstr_type) in
      match oib.(ind_projs) with
      | nil =>
        let ctor_arity := get_arity ctor_type in
        if decide (ctor_arity > get_arity oib.(ind_type)) then
          let name := String.to_string ctor_name in
          let arity := String.to_string (MCString.string_of_nat ctor_arity) in
          tmFail (String.of_string (
            "info: the constructor " ++ name ++ " has no projections but " ++
            "an arity of " ++ arity ++ ". Perhaps you forgot to enable " ++
            "primitive projections before the definition of the Record."
          )%string)
        else ret tt
      | _ => ret tt
      end ;;
      ret {| type := oib.(ind_name) ; ctor := ctor_name ; fields := oib.(ind_projs) |}
    | _ => tmFail "`getFields` got variant type"
    end
  end.
Local Definition genLensCore (info : Info) (ty : term) : TemplateMonad unit :=
  let gen i :=
    match mkLens ty info.(fields) i with
    | None   => tmFail "failed to build lens"
    | Some l => '(n, d) <- tmEval cbv l ;; tmMkDefinition n d
    end
  in
  monad_iter gen (countTo (List.length info.(fields))).

Definition genLens (T : Type) : TemplateMonad unit :=
  ty <- tmQuote T ;;
  i  <- match ty with tInd i _ => ret i | _ => tmFail "given type is not inductive" end ;;
  let name := i.(inductive_mind) in
  ind <- tmQuoteInductive name ;;
  info <- getFields ind i.(inductive_ind) ;;
  genLensCore info ty.

(*
[genLensK] can be used instead of [genLens] to avoid introducing
some universe constraints.

for an inductive X in file A.B.C,
basename:kername := (MPfile ["C"; "B"; "A"], "X")%string.

If the definition of X refers to any other inductive, they should not
be in the current section(s).
 *)
Definition genLensK (baseName : kername) : TemplateMonad unit :=
  let inductive :=
    {| inductive_mind := baseName; inductive_ind := 0 (* TODO: fix for mutual records *) |}
  in
  let ty := Ast.tInd inductive List.nil in
  ind <- tmQuoteInductive baseName ;;
  info <- getFields ind 0;;
  genLensCore info ty.
