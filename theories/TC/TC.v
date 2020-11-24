Require Import Coq.Classes.DecidableClass.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Local Open Scope string_scope.

From MetaCoq.Template Require Import
     monad_utils Ast Loader TemplateMonad.
Import MonadNotation.

Require Import Lens.lens.

Set Primitive Projections.

Record Info :=
{ type   : ident
; ctor   : ident
; fields : list (ident * term)
}.

Fixpoint countTo (n : nat) : list nat :=
  match n with
  | 0 => nil
  | S m => countTo m ++ (m :: nil)
  end.

Definition lensName (ls : string) (i : ident) : ident :=
  ls ++ i.

MetaCoq Quote Definition cBuild_Lens := Build_Lens.

Local Definition mkLens (At : term) (fields : list (ident * term)) (i : nat)
: option (ident * term) :=
  match At with
  | tInd ind args =>
    let ctor := tConstruct ind 0 args in
    match nth_error fields i with
    | None => None
    | Some (name, Bt) =>
      let p (x : nat) : projection := (ind, 0, x) in
      let get_body := tProj (p i) (tRel 0) in
      let f x :=
          let this := tProj (p x) (tRel 0) in
          if PeanoNat.Nat.eqb x i
          then tApp (tRel 1) (this :: nil)
          else this
      in
      let update_body :=
          tApp ctor (map f (countTo (List.length fields)))
      in
      Some ( lensName "_" name
           , tApp cBuild_Lens
                  (At :: At :: Bt :: Bt ::
                      tLambda nAnon At get_body ::
                      tLambda nAnon (tProd nAnon Bt Bt) (tLambda nAnon At update_body) ::
                      nil))
    end
  | _ => None
  end.

Fixpoint get_arity (t : term) : nat :=
  match t with
  | tProd _ _ t => S (get_arity t)
  | _ => 0
  end.

Local Definition getFields (mi : mutual_inductive_body) (n : nat)
: TemplateMonad Info :=
  match nth_error mi.(ind_bodies) n with
  | None => tmFail "no body for index"
  | Some oib =>
    match oib.(ind_ctors) with
    | nil => tmFail "`getFields` got empty type"
    | ctor :: nil =>
      let '(ctor_name,ctor_type,_) := ctor in
      match oib.(ind_projs) with
      | nil =>
        let ctor_arity := get_arity ctor_type in
        if decide (ctor_arity > get_arity oib.(ind_type)) then
          tmFail ("info: the constructor " ++ ctor_name ++ " has no projections but an arity of " ++ MCString.string_of_nat ctor_arity ++ ". Perhaps you forgot to enable primitive projections before the definition of the Record.")
        else ret tt
      | _ => ret tt
      end ;;
      ret {| type := oib.(ind_name)
           ; ctor := ctor_name
           ; fields := oib.(ind_projs)
           |}
    | _ => tmFail "`getFields` got variant type"
    end
  end.
Local Definition genLensCore info ty:=
    let gen i :=
          match mkLens ty info.(fields) i return TemplateMonad unit with
          | None => tmFail "failed to build lens"
          | Some x =>
            tmBind (tmEval cbv x) (fun '(n,d) =>
                                     _ <- tmMkDefinition n d ;;
                                     ret tt)
          end
      in
      monad_map gen (countTo (List.length info.(fields))) ;;
      ret tt.

Definition genLens (T : Type) : TemplateMonad unit :=
  ty <- tmQuote T ;;
  match ty with
  | tInd i _ =>
    let name := i.(inductive_mind) in
    ind <- tmQuoteInductive name ;;
    info <- getFields ind i.(inductive_ind) ;;
    genLensCore info ty
  | _ => tmFail "given type is not inductive"
  end.

(*
for an inductive X in file A.B.C,
basename:kername := (MPfile ["C"; "B"; "A"], "X")%string.

If the definition of F refers to any other inductive, they should not
be in the current section(s).
 *)
Definition genLensK (baseName : kername) : TemplateMonad unit :=
  let ty :=
      (Ast.tInd
         {|
           inductive_mind := baseName;
           inductive_ind := 0 (* TODO: fix for mutual records *) |}
         List.nil) in
  ind <- tmQuoteInductive baseName ;;
  info <- getFields ind 0;;
  genLensCore info ty.
