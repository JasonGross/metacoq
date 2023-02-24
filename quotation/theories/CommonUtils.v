From MetaCoq.Utils Require Import utils monad_utils MCList.
From MetaCoq.Common Require Import Kernames.
From MetaCoq.Template Require MonadBasicAst MonadAst TemplateMonad Ast Loader.
Require Import Equations.Prop.Classes.
Require Import Coq.Lists.List.
Import ListNotations.

Local Unset Universe Minimization ToSet.
Local Set Primitive Projections.
Local Open Scope bs.
Import MCMonadNotation.

Class debug_opt := debug : bool.
Class cls_is_true (b : bool) := is_truev : is_true b.

(* returns true if a modpath is suitable for quotation, i.e., does not mention functor-bound arguments *)
Fixpoint modpath_is_absolute (mp : modpath) : bool
  := match mp with
     | MPfile _ => true
     | MPbound _ _ _ => false
     | MPdot mp _ => modpath_is_absolute mp
     end.
Definition kername_is_absolute (kn : kername) : bool
  := modpath_is_absolute (fst kn).
(* gives the dirpath and the reversed list of idents, or None if bound *)
Fixpoint split_common_prefix_ls (mp1 mp2 : list ident) :=
  match mp1, mp2 with
  | [], _ | _, [] => ([], mp1, mp2)
  | i1 :: mp1, i2 :: mp2
    => if i1 == i2
       then let '(common, mp1, mp2) := split_common_prefix_ls mp1 mp2 in
            (i1 :: common, mp1, mp2)
       else ([], mp1, mp2)
  end.
Definition common_prefix_ls (mp1 mp2 : list ident) :=
  let '(common, _, _) := split_common_prefix_ls mp1 mp2 in common.
Fixpoint split_modpath (mp : modpath) : (list ident * (dirpath * option (ident * nat)))
  := match mp with
     | MPfile f => ([], (f, None))
     | MPbound f i idx => ([], (f, Some (i, idx)))
     | MPdot mp i => let '(l, d) := split_modpath mp in (i :: l, d)
     end.
(* returns None if either [mp] shares no prefix with [mp] or either modpath is bound, otherwise returns the list of idents of the common prefix *)
Definition split_common_prefix (mp1 mp2 : modpath) : option ((dirpath * option (ident * nat)) * (list ident * list ident * list ident))
  := match split_modpath mp1, split_modpath mp2 with
     | (mp1, f1), (mp2, f2)
       => if f1 == f2
          then Some (f1, split_common_prefix_ls (rev mp1) (rev mp2))
          else None
     end.
Definition common_prefix (mp1 mp2 : modpath) : option ((dirpath * option (ident * nat)) * list ident)
  := option_map (fun '(f, (common, _, _)) => (f, common)) (split_common_prefix mp1 mp2).
(* Kludge for not having https://github.com/MetaCoq/metacoq/issues/839 *)
Definition modpath_is_okay (cur_modpath : modpath) (mp : modpath) : bool
  := andb (modpath_is_absolute mp)
       match mp with
       | MPfile _ => true
       | MPbound _ _ _ => false
       | MPdot _ _
         => match common_prefix cur_modpath mp with
            | None => true (* it's not part of the current module, so it's fine *)
            | Some (_, []) => true (* only share the top-level, so it can't be a functor *)
            | Some _ => false
            end
       end.
Definition kername_is_okay (cur_modpath : modpath) (kn : kername) : bool
  := modpath_is_okay cur_modpath (fst kn).

Definition b_of_dec {P} (H : {P} + {~P}) : bool := if H then true else false.
Definition bp_of_dec {P H} : @b_of_dec P H = true -> P.
Proof. cbv [b_of_dec]; destruct H; auto; discriminate. Defined.
Definition pb_of_dec {P:Prop} {H} : P -> @b_of_dec P H = true.
Proof. cbv [b_of_dec]; destruct H; auto; discriminate. Defined.
Definition neg_bp_of_dec {P H} : @b_of_dec P H = false -> ~P.
Proof. cbv [b_of_dec]; destruct H; auto; discriminate. Defined.
Definition neg_pb_of_dec {P:Prop} {H} : ~P -> @b_of_dec P H = false.
Proof. cbv [b_of_dec]; destruct H; tauto. Defined.

(* TODO: move? *)
Definition kername_of_global_reference (g : global_reference) : option kername
  := match g with
     | VarRef _ => None
     | ConstRef x => Some x
     | IndRef ind
     | ConstructRef ind _
       => Some ind.(inductive_mind)
     end.

Definition replace_inductive_kn (t : inductive) (ind : inductive) : inductive
  := {| inductive_mind := ind.(inductive_mind) ; inductive_ind := t.(inductive_ind) |}.

Definition replace_inductive_modpath (mp : modpath) (ind : inductive) : inductive
  := {| inductive_mind := (mp, snd ind.(inductive_mind)) ; inductive_ind := ind.(inductive_ind) |}.

Definition rebase_global_reference (mp : modpath) (g : global_reference) : global_reference
  := match g with
     | VarRef x => VarRef x
     | ConstRef (_, i) => ConstRef (mp, i)
     | IndRef ind => IndRef (replace_inductive_modpath mp ind)
     | ConstructRef ind idx => ConstructRef (replace_inductive_modpath mp ind) idx
     end.

(* hack around https://github.com/MetaCoq/metacoq/issues/850 *)
Fixpoint dedup_grefs' (g : list global_reference) (seen : KernameSet.t) : list global_reference
  := match g with
     | nil => nil
     | g :: gs
       => match kername_of_global_reference g with
          | None => g :: dedup_grefs' gs seen
          | Some kn
            => if KernameSet.mem kn seen
               then dedup_grefs' gs seen
               else g :: dedup_grefs' gs (KernameSet.add kn seen)
          end
     end.
Definition dedup_grefs (g : list global_reference) : list global_reference
  := dedup_grefs' g KernameSet.empty.

Module WithTemplate.
  Import MetaCoq.Template.Loader.
  Import MetaCoq.Template.Ast.
  Import MetaCoq.Template.TemplateMonad.Core.

  (* unfolding Qed'd definitions for the benefit of quotation *)
  Polymorphic Definition tmUnfoldQed {A} (v : A) : TemplateMonad A
    := p <- tmQuote v;;
       v <- match p return TemplateMonad term with
            | tConst c u
              => cb <- tmQuoteConstant c true;;
                 match cb with
                 | {| cst_body := Some cb |} => tmReturn (subst_instance_constr u cb)
                 | {| cst_body := None |} => _ <- tmMsg "tmUnfoldQed: failed to find body for";; _ <- tmPrint v;; tmReturn p
                 end
            | _ => _ <- tmMsg "tmUnfoldQed: not const";; _ <- tmPrint v;; tmReturn p
            end;;
       tmUnquoteTyped A v.
  Notation transparentify v := (match tmUnfoldQed v return _ with v' => ltac:(run_template_program v' (fun v' => exact v')) end) (only parsing).

  #[local]
    Fixpoint tmRelaxSorts (U : Universe.t -> term) (t : term) {struct t} : term
    := match t with
       | tRel _
       | tVar _
       | tInt _
       | tFloat _
       | tConst _ _
       | tInd _ _
       | tConstruct _ _ _
         => t
       | tEvar ev args
         => tEvar ev (List.map (tmRelaxSorts U) args)
       | tCast t kind v
         => tCast (tmRelaxSorts U t) kind (tmRelaxSorts U v)
       | tProd na ty body
         => tProd na (tmRelaxSorts U ty) (tmRelaxSorts U body)
       | tLambda na ty body
         => tLambda na (tmRelaxSorts U ty) (tmRelaxSorts U body)
       | tLetIn na def def_ty body
         => tLetIn na (tmRelaxSorts U def) (tmRelaxSorts U def_ty) (tmRelaxSorts U body)
       | tApp f args
         => tApp (tmRelaxSorts U f) (List.map (tmRelaxSorts U) args)
       | tCase ci type_info discr branches
         => tCase ci (map_predicate (fun x => x) (tmRelaxSorts U) (tmRelaxSorts U) type_info) (tmRelaxSorts U discr) (map_branches (tmRelaxSorts U) branches)
       | tProj proj t
         => tProj proj (tmRelaxSorts U t)
       | tFix mfix idx
         => tFix (List.map (map_def (tmRelaxSorts U) (tmRelaxSorts U)) mfix) idx
       | tCoFix mfix idx
         => tCoFix (List.map (map_def (tmRelaxSorts U) (tmRelaxSorts U)) mfix) idx
       | tSort s => U s
       end.

  #[local]
    Fixpoint tmRelaxSortsInCodomain (U : Universe.t -> term) (t : term) {struct t} : term
    := match t with
       | tRel _
       | tVar _
       | tInt _
       | tFloat _
       | tConst _ _
       | tInd _ _
       | tConstruct _ _ _
       | tEvar _ _
       | tApp _ _
       | tProj _ _
         => t
       | tCast t kind v
         => tCast (tmRelaxSortsInCodomain U t) kind (tmRelaxSortsInCodomain U v)
       | tProd na ty body
         => tProd na ty (tmRelaxSortsInCodomain U body)
       | tLambda na ty body
         => tLambda na ty (tmRelaxSortsInCodomain U body)
       | tLetIn na def def_ty body
         => tLetIn na def def_ty (tmRelaxSortsInCodomain U body)
       | tCase ci type_info discr branches
         => tCase ci (map_predicate (fun x => x) (tmRelaxSortsInCodomain U) (tmRelaxSortsInCodomain U) type_info) discr (map_branches (tmRelaxSortsInCodomain U) branches)
       | tFix mfix idx
         => tFix (List.map (map_def (tmRelaxSortsInCodomain U) (tmRelaxSortsInCodomain U)) mfix) idx
       | tCoFix mfix idx
         => tCoFix (List.map (map_def (tmRelaxSortsInCodomain U) (tmRelaxSortsInCodomain U)) mfix) idx
       | tSort s => U s
       end.

  #[local]
    Definition tmRelaxSet (U : term) (t : term) : term
    := tmRelaxSorts (fun s => match option_map Level.is_set (Universe.get_is_level s) with
                              | Some true => U
                              | _ => tSort s
                              end)
         t.

  #[local]
    Definition tmRelaxType (U : term) (t : term) : term
    := tmRelaxSorts (fun s => match Universe.get_is_level s with
                              | Some _ => U
                              | _ => tSort s
                              end)
         t.

  #[local]
    Definition tmRelaxSetInCodomain (U : term) (t : term) : term
    := tmRelaxSortsInCodomain (fun s => match option_map Level.is_set (Universe.get_is_level s) with
                              | Some true => U
                              | _ => tSort s
                              end)
         t.

  #[local]
    Definition tmRelaxTypeInCodomain (U : term) (t : term) : term
    := tmRelaxSortsInCodomain (fun s => match Universe.get_is_level s with
                              | Some _ => U
                              | _ => tSort s
                              end)
         t.

  #[local]
    Definition tmRelaxOnlyType (U : term) (t : term) : term
    := tmRelaxSorts (fun s => match option_map Level.is_set (Universe.get_is_level s) with
                              | Some false => U
                              | _ => tSort s
                              end)
         t.

  Polymorphic Definition tmRetypeMagicRelaxSet@{U a b t u} {A : Type@{a}} (B : Type@{b}) (x : A) : TemplateMonad@{t u} B
    := qx <- tmQuote x;;
       qU <- tmQuoteUniverse@{U _ _};;
       let qx := tmRelaxSet (tSort qU) qx in
       tmUnquoteTyped B qx.

  Polymorphic Definition tmRetypeMagicRelaxType@{U a b t u} {A : Type@{a}} (B : Type@{b}) (x : A) : TemplateMonad@{t u} B
    := qx <- tmQuote x;;
       qU <- tmQuoteUniverse@{U _ _};;
       let qx := tmRelaxType (tSort qU) qx in
       tmUnquoteTyped B qx.

  Polymorphic Definition tmRetypeMagicRelaxSetInCodomain@{U a b t u} {A : Type@{a}} (B : Type@{b}) (x : A) : TemplateMonad@{t u} B
    := qx <- tmQuote x;;
       qU <- tmQuoteUniverse@{U _ _};;
       let qx := tmRelaxSetInCodomain (tSort qU) qx in
       tmUnquoteTyped B qx.

  Polymorphic Definition tmRetypeMagicRelaxSetInAppArgsCodomain@{U a b t u} {A : Type@{a}} (B : Type@{b}) (x : A) : TemplateMonad@{t u} B
    := qx <- tmQuote x;;
       qU <- tmQuoteUniverse@{U _ _};;
       let transform := tmRelaxSetInCodomain (tSort qU) in
       let qx := match qx with
                 | tApp f args => tApp f (List.map transform args)
                 | tSort _ => transform qx
                 | _ => qx
                 end in
       tmUnquoteTyped B qx.

  Polymorphic Definition tmRetypeMagicRelaxTypeInCodomain@{U a b t u} {A : Type@{a}} (B : Type@{b}) (x : A) : TemplateMonad@{t u} B
    := qx <- tmQuote x;;
       qU <- tmQuoteUniverse@{U _ _};;
       let qx := tmRelaxTypeInCodomain (tSort qU) qx in
       tmUnquoteTyped B qx.

  Polymorphic Definition tmRetypeMagicRelaxOnlyType@{U a b t u} {A : Type@{a}} (B : Type@{b}) (x : A) : TemplateMonad@{t u} B
    := qx <- tmQuote x;;
       qU <- tmQuoteUniverse@{U _ _};;
       let qx := tmRelaxOnlyType (tSort qU) qx in
       tmUnquoteTyped B qx.

  Polymorphic Definition tmRetypeRelaxSet@{U a t u} {A : Type@{a}} (x : A) : TemplateMonad@{t u} A
    := tmRetypeMagicRelaxSet@{U a a t u} A x.
  Polymorphic Definition tmRetypeRelaxType@{U a t u} {A : Type@{a}} (x : A) : TemplateMonad@{t u} A
    := tmRetypeMagicRelaxType@{U a a t u} A x.
  Polymorphic Definition tmRetypeRelaxSetInCodomain@{U a t u} {A : Type@{a}} (x : A) : TemplateMonad@{t u} A
    := tmRetypeMagicRelaxSetInCodomain@{U a a t u} A x.
  Polymorphic Definition tmRetypeRelaxSetInAppArgsCodomain@{U a t u} {A : Type@{a}} (x : A) : TemplateMonad@{t u} A
    := tmRetypeMagicRelaxSetInAppArgsCodomain@{U a a t u} A x.
  Polymorphic Definition tmRetypeRelaxTypeInCodomain@{U a t u} {A : Type@{a}} (x : A) : TemplateMonad@{t u} A
    := tmRetypeMagicRelaxTypeInCodomain@{U a a t u} A x.
  Polymorphic Definition tmRetypeRelaxOnlyType@{U a t u} {A : Type@{a}} (x : A) : TemplateMonad@{t u} A
    := tmRetypeMagicRelaxOnlyType@{U a a t u} A x.

  Polymorphic Definition tmQuoteToGlobalReference {A} (n : A) : TemplateMonad global_reference
    := qn <- tmQuote n;;
       match qn with
       | tVar id => tmReturn (VarRef id)
       | tConst c u => tmReturn (ConstRef c)
       | tInd ind u => tmReturn (IndRef ind)
       | tConstruct ind idx u => tmReturn (ConstructRef ind idx)
       | _ => _ <- tmMsg "tmQuoteToGlobalReference: Not a global reference";;
              _ <- tmPrint n;;
              _ <- tmPrint qn;;
              tmFail "tmQuoteToGlobalReference: Not a global reference"
       end.

  Polymorphic Definition tmObj_magic {A B} (x : A) : TemplateMonad B
    := qx <- tmQuote x;;
       tmUnquoteTyped B qx.

  Polymorphic Definition tmRetype {A} (x : A) : TemplateMonad A
    := tmObj_magic x.

  Polymorphic Definition tmExtractBaseModPathFromMod (mp : qualid) : TemplateMonad modpath
    := vs <- tmQuoteModule mp;;
       match option_map kername_of_global_reference (hd_error vs) with
       | Some (Some (mp, _)) => ret mp
       | _ => tmFail "tmExtractBaseModPathFromMod: module has no accessible constant with a kername"
       end.
End WithTemplate.
Export WithTemplate (transparentify, tmQuoteToGlobalReference, tmRetypeRelaxSet, tmRetypeRelaxType, tmRetypeRelaxSetInCodomain, tmRetypeRelaxSetInAppArgsCodomain, tmRetypeRelaxTypeInCodomain, tmRetypeRelaxOnlyType, tmRetypeMagicRelaxSet, tmRetypeMagicRelaxType, tmRetypeMagicRelaxSetInCodomain, tmRetypeMagicRelaxSetInAppArgsCodomain, tmRetypeMagicRelaxTypeInCodomain, tmRetypeMagicRelaxOnlyType, tmObj_magic, tmRetype, tmExtractBaseModPathFromMod).
