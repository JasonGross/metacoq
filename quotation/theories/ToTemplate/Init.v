From MetaCoq.Utils Require Export bytestring.
From MetaCoq.Utils Require Import utils MCList.
From MetaCoq.Template Require Import MonadBasicAst MonadAst TemplateMonad Ast Loader.
From MetaCoq.Quotation Require Export CommonUtils.
Require Import Equations.Prop.Classes.
Require Import Coq.Lists.List.
Import ListNotations.

Local Set Primitive Projections.
Local Open Scope bs.
Import MCMonadNotation.

Class quotation_of {T} (t : T) := quoted_term_of : Ast.term.
Class ground_quotable T := quote_ground : forall t : T, quotation_of t.
Class inductive_quotation_of {T} (t : T)
  := { qinductive : inductive
     ; qinst : Instance.t
     ; qquotation : quotation_of t := tInd qinductive qinst }.
Definition default_inductive_quotation_of {T} {t : T} (qt : quotation_of t) (pf : cls_is_true match qt with tInd _ _ => true | _ => false end)
  : inductive_quotation_of t
  := match qt return cls_is_true match qt with tInd _ _ => true | _ => false end -> _ with
     | tInd ind u => fun _ => @Build_inductive_quotation_of T t ind u
     | _ => fun pf : false = true => match diff_false_true pf with end
     end pf.

(* returns false iff a term is suitable for quotation at the top-level, i.e., returns true iff it mentions functor-bound arguments or is a local variable or evar *)
Definition head_term_is_bound (cur_modpath : modpath) (t : term) : bool
  := match t with
     | tConst kn _
     | tInd {| inductive_mind := kn |} _
     | tConstruct {| inductive_mind := kn |} _ _
     | tProj {| proj_ind := {| inductive_mind := kn |} |} _
     | tCase {| ci_ind := {| inductive_mind := kn |} |} _ _ _
       => negb (kername_is_okay cur_modpath kn)
     | tVar _
     | tEvar _ _
       => true
     | _ => false
     end.

Fixpoint head (t : term) : term
  := match t with
     | tCast t _ _
     | tApp t _
       => head t
     | _ => t
     end.

Definition infer_replacement_inductive {debug : debug_opt} (qt : term) : TemplateMonad (option inductive).
Proof.
  simple
    refine (match qt with
            | tInd ind u
            | tConstruct ind _ u
            | tCase {| ci_ind := ind |} {| puinst := u |} _ _
              => (indv <- tmUnquote (tInd ind u);;
                  let '(existT_typed_term _ indv) := indv in
                  v <- (tmInferInstance None (inductive_quotation_of indv));;
                  match v with
                  | my_Some v => ret (Some (replace_inductive_kn ind v.(qinductive)))
                  | my_None => (if debug then tmPrint (inductive_quotation_of indv) else ret tt);; ret None
                  end)
            | tProj {| proj_ind := ind |} t
              => (t <- tmUnquote t;;
                  let '(existT_typed_term ty _) := t in
                  ty <- tmEval hnf ty;;
                  ty <- tmQuote ty;;
                  let indv := head ty in
                  indv <- tmUnquote indv;;
                  let '(existT_typed_term _ indv) := indv in
                  v <- (tmInferInstance None (inductive_quotation_of indv));;
                  match v with
                  | my_Some v => ret (Some (replace_inductive_kn ind v.(qinductive)))
                  | my_None => (if debug then tmPrint (qt, inductive_quotation_of ind) else ret tt);; ret None
                  end)
            | _ => ret None
            end).
Defined.

Fixpoint replace_quotation_of' {debug : debug_opt} (do_top_inference : bool) (qt : term) : TemplateMonad term.
Proof.
  specialize (replace_quotation_of' debug).
  simple
    refine
    (let replace_quotation_of' := replace_quotation_of' true in
     let tmTryInferQuotation t
       := (t <- tmUnquote t;;
           let '(existT_typed_term _ t) := t in
           v <- tmInferInstance None (quotation_of t);;
           match v return TemplateMonad (option_instance Ast.term) with
           | my_Some v => ret (@my_Some _ v)
           | my_None => (if debug then tmPrint (quotation_of t) else ret tt);; ret (@my_None _)
           end) in
     let tmInferQuotation t
       := (v <- tmTryInferQuotation t;;
           match v return TemplateMonad Ast.term with
           | my_Some v => ret v
           | my_None => tmFail "No typeclass instance"
           end) in
     let tmMaybeInferQuotation 'tt :=
       if do_top_inference then tmInferQuotation qt else tmFail "Avoiding loops" in
     cur_modpath <- tmCurrentModPath tt;;
     match qt return TemplateMonad Ast.term with
     | tRel _
     | tSort _
     | tInt _
     | tFloat _
     | tConst _ _
       => if head_term_is_bound cur_modpath qt
          then tmMaybeInferQuotation tt
          else ret qt
     | tConstruct ind idx u
       => if head_term_is_bound cur_modpath qt
          then (ind <- infer_replacement_inductive qt;;
                match ind with
                | Some ind => ret (tConstruct ind idx u)
                | None => tmMaybeInferQuotation tt
                end)
          else ret qt
     | tInd ind u
       => if head_term_is_bound cur_modpath qt
          then if do_top_inference
               then (ind <- infer_replacement_inductive qt;;
                     match ind with
                     | Some ind => ret (tInd ind u)
                     | None => tmMaybeInferQuotation tt
                     end)
               else tmFail "Avoiding ind loops"
          else ret qt
     | tVar _
       => tmMaybeInferQuotation tt
     | tEvar ev args => args <- monad_map replace_quotation_of' args;; ret (tEvar ev args)
     | tLambda na T M => T <- replace_quotation_of' T;; M <- replace_quotation_of' M;; ret (tLambda na T M)
     | tApp u v => u <- replace_quotation_of' u;; v <- monad_map replace_quotation_of' v;; ret (mkApps u v)
     | tProd na A B => A <- replace_quotation_of' A;; B <- replace_quotation_of' B;; ret (tProd na A B)
     | tCast c kind ty => c <- replace_quotation_of' c;; ty <- replace_quotation_of' ty;; ret (tCast c kind ty)
     | tLetIn na b ty b' => b <- replace_quotation_of' b;; ty <- replace_quotation_of' ty;; b' <- replace_quotation_of' b';; ret (tLetIn na b ty b')
     | tProj p c
       => res <- (if head_term_is_bound cur_modpath qt
                  then (ind <- infer_replacement_inductive qt;;
                        match ind with
                        | Some ind
                          => let p := {| proj_ind := ind ; proj_npars := p.(proj_npars) ; proj_arg := p.(proj_arg) |} in
                             ret (inr p)
                        | None
                          => res <- tmMaybeInferQuotation tt;;
                             ret (inl res)
                        end)
                  else ret (inr p));;
          match res with
          | inl res => ret res
          | inr p => c <- replace_quotation_of' c;;
                     ret (tProj p c)
          end
     | tFix mfix idx =>
         mfix' <- monad_map (monad_map_def (TM:=TypeInstance) replace_quotation_of' replace_quotation_of') mfix;;
         ret (tFix mfix' idx)
     | tCoFix mfix idx =>
         mfix' <- monad_map (monad_map_def (TM:=TypeInstance) replace_quotation_of' replace_quotation_of') mfix;;
         ret (tCoFix mfix' idx)
     | tCase ci p c brs
       => res <- (if head_term_is_bound cur_modpath qt
                  then (ind <- infer_replacement_inductive qt;;
                        match ind with
                        | Some ind
                          => ret (inr {| ci_ind := ind ; ci_npar := ci.(ci_npar) ; ci_relevance := ci.(ci_relevance) |})
                        | None
                          => res <- tmMaybeInferQuotation tt;;
                             ret (inl res)
                        end)
                  else ret (inr ci));;
          match res with
          | inl res => ret res
          | inr ci
            => p' <- monad_map_predicate (TM:=TypeInstance) ret replace_quotation_of' replace_quotation_of' p;;
               brs' <- monad_map_branches (TM:=TypeInstance) replace_quotation_of' brs;;
               c <- replace_quotation_of' c;;
               ret (tCase ci p' c brs')
          end
     end);
    try exact _.
Defined.

Definition replace_quotation_of {debug : debug_opt} {T} (t : T) : TemplateMonad term
  := qt <- tmQuote t;;
     replace_quotation_of' false qt.

(** for fancier goals when we have [ground_quotable] for some subterms but not for subterms of those subterms *)
Definition make_quotation_of {debug : debug_opt} {T} (t : T) : TemplateMonad (quotation_of t).
Proof.
  simple
    refine
    (qt <- tmQuote t;;
     let tmInferQuotation t
       := (t <- tmUnquote t;;
           let '(existT_typed_term _ t) := t in
           v <- tmInferInstance None (quotation_of t);;
           match v with
           | my_Some v => ret v
           | my_None => (if debug then tmPrint (quotation_of t) else ret tt);; tmFail "No typeclass instance"
           end) in
     cur_modpath <- tmCurrentModPath tt;;
     if head_term_is_bound cur_modpath qt
     then ((if debug then tmPrint qt else ret tt);; tmFail "bound argument is not ground")
     else
       match qt return TemplateMonad Ast.term with
       | tSort _
       | tConst _ _
       | tConstruct _ _ _
       | tInt _
       | tFloat _
       | tInd _ _
         => ret qt
       | tCast t kind v
         => tmInferQuotation t
       | tApp f args
         => qf <- tmInferQuotation f;;
            qargs <- list_rect
                       (fun _ => TemplateMonad (list _))
                       (ret [])
                       (fun arg args qargs
                        => qarg <- tmInferQuotation arg;;
                           qargs <- qargs;;
                           ret (qarg :: qargs))
                       args;;
            ret (tApp qf qargs)
       | tProj proj t => tmFail "Proj is not reduced"
       | tRel n => tmFail "Rel is not ground"
       | tVar id => tmFail "Var is not ground"
       | tEvar ev args => tmFail "Evar is not ground"
       | tProd na ty body => tmFail "Prod not yet handled"
       | tLambda na ty body => tmFail "Lambda not yet handled"
       | tLetIn na def def_ty body => tmFail "LetIn not yet handled"
       | tCase ci type_info discr branches => tmFail "Case not yet handled"
       | tFix mfix idx => tmFail "Fix not yet handled"
       | tCoFix mfix idx => tmFail "CoFix not yet handled"
       end);
    exact _.
Defined.

Ltac replace_quotation_of_goal _ :=
  let t := match goal with |- quotation_of ?t => t end in
  run_template_program (replace_quotation_of t) (fun v => exact v).

Ltac make_quotation_of_goal _ :=
  let t := match goal with |- quotation_of ?t => t end in
  run_template_program (make_quotation_of t) (fun v => exact v).

Ltac adjust_quotation_of_by_econstructor_then tac1 tac2 :=
  let f := match goal with |- ?f _ => f end in
  unshelve (let g := open_constr:(f _) in
            change g);
  [ unshelve econstructor
  | ];
  [ ..
  | repeat match goal with |- context[?ev] => is_evar ev; generalize ev; intro end ];
  [ tac1 () ..
  | tac2 () ].

Ltac adjust_ground_quotable_by_econstructor_inversion _ :=
  let pf := fresh "pf" in
  intro pf;
  adjust_quotation_of_by_econstructor_then ltac:(fun _ => inversion pf; try assumption) ltac:(fun _ => try exact _).

Ltac revert_quotable_hyp _ :=
  match goal with
  | [ H : _ |- quotation_of ?v ]
    => lazymatch v with
       | H => fail
       | context[H] => idtac
       end;
       revert H;
       lazymatch goal with
       | [ |- forall x : ?A, quotation_of (@?P x) ]
         => assert (quotation_of P);
            [
            | intro H;
              pose proof (_ : quotation_of H);
              change (quotation_of (P H)); exact _ ]
       end
  end.
Ltac revert_quotable_hyps _ :=
  repeat revert_quotable_hyp ().

Module Export Instances.
  (* some performance settings *)
  #[export] Set Typeclasses Unique Instances.
  #[export] Instance default_debug : debug_opt | 1000 := false.
  #[export] Existing Instance quote_ground.
  #[export] Typeclasses Opaque quotation_of.
  #[export]
   Hint Extern 1 (quotation_of match ?t with _ => _ end) => is_var t; destruct t : typeclass_instances.
  #[export]
   Hint Extern 1 (ground_quotable match ?t with _ => _ end) => is_var t; destruct t : typeclass_instances.
  #[export]
   Hint Extern 1 (quotation_of _) => replace_quotation_of_goal () : typeclass_instances.
  #[export]
   Hint Extern 2 (quotation_of _) => make_quotation_of_goal () : typeclass_instances.
  (*#[export]
   Hint Extern 100 (quotation_of _) => progress revert_quotable_hyps () : typeclass_instances.*)
  #[export] Hint Mode cls_is_true + : typeclass_instances.
  #[export] Existing Instances qquotation | 10.
  (* Hack around COQBUG(https://github.com/coq/coq/issues/16760) *)
  #[export] Hint Extern 10 (@inductive_quotation_of ?T ?t) => simple notypeclasses refine (@default_inductive_quotation_of T t _ _) : typeclass_instances.
  #[export] Hint Extern 10 (cls_is_true ?b)
  => tryif is_evar b then refine (eq_refl true) else tryif has_evar b then fail else vm_compute; reflexivity
       : typeclass_instances.
  #[export] Hint Cut [
      ( _ * )
        qquotation
        ( _ * )
        qquotation
    ] : typeclass_instances.
End Instances.

Module StrongerInstances.
  #[export]
   Hint Extern 1 (quotation_of match ?t with _ => _ end) => destruct t : typeclass_instances.
  #[export]
   Hint Extern 1 (ground_quotable match ?t with _ => _ end) => destruct t : typeclass_instances.
End StrongerInstances.

(** Some helper lemmas for defining quotations *)
Definition ground_quotable_of_bp {b P} (H : b = true -> P) {qH : quotation_of H} (H_for_safety : P -> b = true) : ground_quotable P.
Proof.
  intro p.
  exact (Ast.mkApps qH [_ : quotation_of (@eq_refl bool true)]).
Defined.

Definition ground_quotable_neg_of_bp {b P} (H : b = false -> ~P) {qH : quotation_of H} (H_for_safety : ~P -> b = false) : ground_quotable (~P).
Proof.
  intro p.
  exact (Ast.mkApps qH [_ : quotation_of (@eq_refl bool false)]).
Defined.

Definition ground_quotable_of_dec {P} (H : {P} + {~P}) {qP : quotation_of P} {qH : quotation_of H} : ground_quotable P
  := ground_quotable_of_bp bp_of_dec pb_of_dec.
Definition ground_quotable_neg_of_dec {P} (H : {P} + {~P}) {qP : quotation_of P} {qH : quotation_of H} : ground_quotable (~P)
  := ground_quotable_neg_of_bp neg_bp_of_dec neg_pb_of_dec.
Definition ground_quotable_neq_of_EqDec {A x y} {qA : quotation_of A} {quoteA : ground_quotable A} {H : EqDec A} {qH : quotation_of H} : ground_quotable (x <> y :> A)
  := ground_quotable_neg_of_dec (H x y).
#[export] Hint Extern 1 (ground_quotable (?x <> ?y :> ?A)) => simple notypeclasses refine (@ground_quotable_neq_of_EqDec A x y _ _ _ _) : typeclass_instances.

Definition ground_quotable_of_iffT {A B} {quoteA : ground_quotable A} {qA : quotation_of A} {qB : quotation_of B} (H : A <~> B) {qH : quotation_of H} : ground_quotable B.
Proof.
  intro b.
  change (@quotation_of B (fst H (snd H b))).
  exact _.
Defined.
(* Transparent versions *)
Definition proj1 {A B} (x : A /\ B) : A := ltac:(apply x).
Definition proj2 {A B} (x : A /\ B) : B := ltac:(apply x).
Definition ground_quotable_of_iff {A B : Prop} {quoteA : ground_quotable A} {qA : quotation_of A} {qB : quotation_of B} (H : iff A B) {qH : quotation_of H} : ground_quotable B.
Proof.
  intro b.
  change (@quotation_of B (proj1 H (proj2 H b))).
  exact _.
Defined.
Definition quote_neg_of_iffT {A B} {quoteA : ground_quotable (A -> False)} {qA : quotation_of A} {qB : quotation_of B} (H : A <~> B) {qH : quotation_of H} : ground_quotable (B -> False).
Proof.
  intro nb.
  assert (na : A -> False) by (intro a; apply nb, H, a).
  change (@quotation_of (B -> False) (fun b => na (snd H b))).
  exact _.
Defined.
Definition quote_neg_of_iff {A B : Prop} {quoteA : ground_quotable (~A)} {qA : quotation_of A} {qB : quotation_of B} (H : iff A B) {qH : quotation_of H} : ground_quotable (~B).
Proof.
  intro nb.
  assert (na : ~A) by (intro a; apply nb, H, a).
  change (@quotation_of (~B) (fun b => na (proj2 H b))).
  exact _.
Defined.

Ltac unfold_quotation_of _ :=
  lazymatch goal with
  | [ |- @quotation_of ?A ?t ]
    => first [ progress cbv delta [t]
             | change (@quotation_of A (transparentify t)) ]
  end.

Definition tmMakeQuotationOfConstants {debug:debug_opt} (do_existing_instance : bool) (cs : list global_reference) : TemplateMonad unit
  := let warn_bad_ctx c ctx :=
       (_ <- tmMsg "tmMakeQuotationOfModule: cannot handle polymorphism";;
        _ <- tmPrint c;;
        _ <- tmPrint ctx;;
        tmReturn tt) in
     let tmDebugMsg s := (if debug
                          then tmMsg s
                          else tmReturn tt) in
     let tmDebugPrint {T} (v : T) := (if debug
                                      then tmPrint v
                                      else tmReturn tt) in
     let on_bad_relevance r :=
       (_ <- tmDebugMsg "skipping irrelevant constant";;
        _ <- tmDebugPrint r;;
        tmReturn []) in
     let cs := dedup_grefs cs in
     cs <- tmEval cbv cs;;
     _ <- tmDebugMsg "tmMakeQuotationOfConstants: looking up module constants";;
     ps <- monad_map
             (fun r
              => _ <- tmDebugMsg "tmMakeQuotationOfConstants: handling";;
                 _ <- tmDebugPrint r;;
                 match r with
                 | ConstRef ((mp, name) as c)
                   => '(inst, rel) <- (cb <- tmQuoteConstant c false;;
                                       inst <- match cb.(cst_universes) with
                                               | Monomorphic_ctx => tmReturn []
                                               | (Polymorphic_ctx (univs, constraints)) as ctx
                                                 => _ <- warn_bad_ctx r ctx;;
                                                    tmReturn []
                                               end;;
                                       tmReturn (inst, cb.(cst_relevance)));;
                      match rel with
                      | Irrelevant => on_bad_relevance r
                      | Relevant
                        => let c := tConst c inst in
                           _ <- tmDebugMsg "tmMakeQuotationOfConstants: tmUnquote";;
                           '{| my_projT1 := cty ; my_projT2 := cv |} <- tmUnquote c;;
                           _ <- tmDebugMsg "tmMakeQuotationOfConstants: tmUnquote done";;
                           let ty := @quotation_of cty cv in
                           tmReturn [("q" ++ name, {| my_projT1 := ty ; my_projT2 := c |})]
                      end
                 | IndRef ind
                   => inst <- (mib <- tmQuoteInductive ind.(inductive_mind);;
                               match mib.(ind_universes) with
                               | Monomorphic_ctx => tmReturn []
                               | (Polymorphic_ctx (univs, constraints)) as ctx
                                 => _ <- warn_bad_ctx r ctx;;
                                    tmReturn []
                               end);;
                      let '(mp, name) := ind.(inductive_mind) in
                      let c := tInd ind inst in
                      _ <- tmDebugMsg "tmMakeQuotationOfConstants: tmUnquote";;
                      '{| my_projT1 := cty ; my_projT2 := cv |} <- tmUnquote c;;
                      _ <- tmDebugMsg "tmMakeQuotationOfConstants: tmUnquote done";;
                      let ty := inductive_quotation_of cv in
                      let v : ty := {| qinductive := ind ; qinst := inst |} in
                      tmReturn [("q" ++ name, {| my_projT1 := ty ; my_projT2 := v |})]
                 | ConstructRef _ _ | VarRef _ => tmReturn []
                 end)
             cs;;
     let ps := flat_map (fun x => x) ps in
     _ <- tmDebugMsg "tmMakeQuotationOfConstants: relaxing Set and retyping module constants";;
     ps <- monad_map
             (fun '(name, {| my_projT1 := ty ; my_projT2 := v |})
              => _ <- tmDebugMsg ("tmMakeQuotationOfConstants: relaxing " ++ name);;
                 _ <- tmDebugPrint ("before"%bs, v, ":"%bs, ty);;
                 _ <- tmDebugPrint (tmRetypeRelaxSetInAppArgsCodomain ty);;
                 ty <- tmRetypeRelaxSetInAppArgsCodomain ty;;
                 _ <- tmDebugPrint (tmRetypeMagicRelaxSetInAppArgsCodomain ty v);;
                 v <- tmRetypeMagicRelaxSetInAppArgsCodomain ty v;;
                 _ <- tmDebugPrint (tmRetypeRelaxOnlyType ty);;
                 ty <- tmRetypeRelaxOnlyType ty;;
                 (* hack around https://github.com/MetaCoq/metacoq/issues/853 *)
                 _ <- tmDebugPrint (tmRetypeMagicRelaxOnlyType ty v);;
                 v <- tmRetypeMagicRelaxOnlyType ty v;;
                 _ <- tmDebugPrint ("after"%bs, v, ":"%bs, ty);;
                 tmReturn (name, {| my_projT1 := ty ; my_projT2 := v |}))
             ps;;
     _ <- tmDebugMsg "tmMakeQuotationOfConstants: defining module constants";;
     ps <- monad_map
             (fun '(name, {| my_projT1 := ty ; my_projT2 := v |})
              => (* debugging sanity checks for hack around https://github.com/MetaCoq/metacoq/issues/853 *)
                _ <- tmDebugPrint (tmRetype ty);;
                _ <- tmRetype ty;;
                _ <- tmDebugPrint (tmRetype v);;
                _ <- tmRetype v;;
                _ <- tmDebugPrint (@tmDefinition name ty v);;
                n <- @tmDefinition name ty v;;
                _ <- tmDebugMsg "tmMakeQuotationOfConstants: tmQuoteToGlobalReference";;
                qn <- tmQuoteToGlobalReference n;;
                tmReturn qn)
             ps;;
     _ <- (if do_existing_instance
           then
             _ <- tmDebugMsg "tmMakeQuotationOfConstants: making instances";;
             monad_map tmExistingInstance ps
           else tmReturn []);;
     tmReturn tt.

Definition tmMakeQuotationOfModule {debug:debug_opt} (do_existing_instance : bool) (m : qualid) : TemplateMonad _
  := cs <- tmQuoteModule m;;
     tmMakeQuotationOfConstants do_existing_instance cs.
Global Arguments tmMakeQuotationOfModule {_%bool} _%bool _%bs.

Definition tmMakeQuotationOfModuleAndRebase {debug:debug_opt} (do_existing_instance : bool) (reference_mp : qualid) (new_base_mp : modpath) : TemplateMonad _
  := cs <- tmQuoteModule reference_mp;;
     let cs := List.map (rebase_global_reference new_base_mp) cs in
     tmMakeQuotationOfConstants do_existing_instance cs.
Global Arguments tmMakeQuotationOfModuleAndRebase {_%bool} _%bool _%bs _.

(*
Require Import MSetPositive.
MetaCoq Run (tmMakeQuotationOfModule true "Coq.MSets.MSetPositive.PositiveSet"%bs).
*)
