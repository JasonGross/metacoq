(* -*- mode: coq; coq-prog-args: ("-emacs" "-q" "-w" "-deprecated-native-compiler-option" "-native-compiler" "no" "-R" "/github/workspace/metacoq/utils/theories" "MetaCoq.Utils" "-R" "/github/workspace/metacoq/common/theories" "MetaCoq.Common" "-R" "/github/workspace/metacoq/pcuic/theories" "MetaCoq.PCUIC" "-R" "/github/workspace/metacoq/template-coq/theories" "MetaCoq.Template" "-R" "/github/workspace/metacoq/template-pcuic/theories" "MetaCoq.TemplatePCUIC" "-R" "/github/workspace/metacoq/safechecker/theories" "MetaCoq.SafeChecker" "-R" "/github/workspace/metacoq/quotation/theories" "MetaCoq.Quotation" "-Q" "/github/workspace/cwd" "Top" "-Q" "/home/coq/.opam/4.13.1+flambda/lib/coq/user-contrib/Bignums" "Bignums" "-Q" "/home/coq/.opam/4.13.1+flambda/lib/coq/user-contrib/Equations" "Equations" "-Q" "/home/coq/.opam/4.13.1+flambda/lib/coq/user-contrib/Ltac2" "Ltac2" "-I" "/github/workspace/metacoq/template-coq" "-top" "MetaCoq.Quotation.ToPCUIC.Init.Typing") -*- *)
(* File reduced by coq-bug-minimizer from original input, then from 1736 lines to 188 lines, then from 201 lines to 687 lines, then from 692 lines to 320 lines *)
(* coqc version 8.16.1 compiled with OCaml 4.13.1
   coqtop version 8.16.1
   Modules that could not be inlined: MetaCoq.Quotation.ToPCUIC.Coq.Init
   Expected coqc runtime on this file: 4.956 sec *)
Axiom proof_admitted : False.
Tactic Notation "admit" := abstract case proof_admitted.
Module Export PCUICErrors.

Require MetaCoq.Utils.utils.
Import MetaCoq.Utils.utils.

Require MetaCoq.PCUIC.utils.PCUICPretty.
Import MetaCoq.PCUIC.PCUICAst.

Inductive ConversionError :=
| NotFoundConstants (c1 c2 : kername)

| NotFoundConstant (c : kername)

| LambdaNotConvertibleTypes
    (Γ1 : context) (na : aname) (A1 t1 : term)
    (Γ2 : context) (na' : aname) (A2 t2 : term)
    (e : ConversionError)

| LambdaNotConvertibleAnn
    (Γ1 : context) (na : aname) (A1 t1 : term)
    (Γ2 : context) (na' : aname) (A2 t2 : term)

| ProdNotConvertibleDomains
    (Γ1 : context) (na : aname) (A1 B1 : term)
    (Γ2 : context) (na' : aname) (A2 B2 : term)
    (e : ConversionError)

| ProdNotConvertibleAnn
    (Γ1 : context) (na : aname) (A1 B1 : term)
    (Γ2 : context) (na' : aname) (A2 B2 : term)

| ContextNotConvertibleAnn
    (Γ : context) (decl : context_decl)
    (Γ' : context) (decl' : context_decl)
| ContextNotConvertibleType
    (Γ : context) (decl : context_decl)
    (Γ' : context) (decl' : context_decl)
| ContextNotConvertibleBody
    (Γ : context) (decl : context_decl)
    (Γ' : context) (decl' : context_decl)
| ContextNotConvertibleLength

| CaseOnDifferentInd
    (Γ1 : context)
    (ci : case_info) (p : predicate term) (c : term) (brs : list (branch term))
    (Γ2 : context)
    (ci' : case_info) (p' : predicate term) (c' : term) (brs' : list (branch term))

| CasePredParamsUnequalLength
    (Γ1 : context)
    (ci : case_info) (p : predicate term) (c : term) (brs : list (branch term))
    (Γ2 : context)
    (ci' : case_info) (p' : predicate term) (c' : term) (brs' : list (branch term))

| CasePredUnequalUniverseInstances
    (Γ1 : context)
    (ci : case_info) (p : predicate term) (c : term) (brs : list (branch term))
    (Γ2 : context)
    (ci' : case_info) (p' : predicate term) (c' : term) (brs' : list (branch term))

| DistinctStuckProj
    (Γ : context) (p : projection) (c : term)
    (Γ' : context) (p' : projection) (c' : term)

| CannotUnfoldFix
    (Γ : context) (mfix : mfixpoint term) (idx : nat)
    (Γ' : context) (mfix' : mfixpoint term) (idx' : nat)

| FixRargMismatch (idx : nat)
    (Γ : context) (u : def term) (mfix1 mfix2 : mfixpoint term)
    (Γ' : context) (v : def term) (mfix1' mfix2' : mfixpoint term)

| FixMfixMismatch (idx : nat)
    (Γ : context) (mfix : mfixpoint term)
    (Γ' : context) (mfix' : mfixpoint term)

| DistinctCoFix
    (Γ : context) (mfix : mfixpoint term) (idx : nat)
    (Γ' : context) (mfix' : mfixpoint term) (idx' : nat)

| CoFixRargMismatch (idx : nat)
    (Γ : context) (u : def term) (mfix1 mfix2 : mfixpoint term)
    (Γ' : context) (v : def term) (mfix1' mfix2' : mfixpoint term)

| CoFixMfixMismatch (idx : nat)
    (Γ : context) (mfix : mfixpoint term)
    (Γ' : context) (mfix' : mfixpoint term)

| StackHeadError
    (leq : conv_pb)
    (Γ1 : context)
    (t1 : term) (args1 : list term) (u1 : term) (l1 : list term)
    (Γ2 : context)
    (t2 : term) (u2 : term) (l2 : list term)
    (e : ConversionError)

| StackTailError (leq : conv_pb)
    (Γ1 : context)
    (t1 : term) (args1 : list term) (u1 : term) (l1 : list term)
    (Γ2 : context)
    (t2 : term) (u2 : term) (l2 : list term)
    (e : ConversionError)

| StackMismatch
    (Γ1 : context) (t1 : term) (args1 l1 : list term)
    (Γ2 : context) (t2 : term) (l2 : list term)

| HeadMismatch
    (leq : conv_pb)
    (Γ1 : context) (t1 : term)
    (Γ2 : context) (t2 : term).

Inductive type_error :=
| UnboundRel (n : nat)
| UnboundVar (id : string)
| UnboundEvar (ev : nat)
| UndeclaredConstant (c : kername)
| UndeclaredInductive (c : inductive)
| UndeclaredConstructor (c : inductive) (i : nat)
| NotCumulSmaller {abstract_structure} (le : bool)
  (G : abstract_structure) (Γ : context) (t u t' u' : term) (e : ConversionError)
| NotConvertible {abstract_structure}
  (G : abstract_structure)
  (Γ : context) (t u : term)
| NotASort (t : term)
| NotAProduct (t t' : term)
| NotAnInductive (t : term)
| NotAnArity (t : term)
| IllFormedFix (m : mfixpoint term) (i : nat)
| UnsatisfiedConstraints (c : ConstraintSet.t)
| Msg (s : string).

Inductive env_error :=
| IllFormedDecl (e : string) (e : type_error)
| AlreadyDeclared (id : string).

End PCUICErrors.
Require MetaCoq.PCUIC.PCUICParallelReductionConfluence.
Require MetaCoq.Quotation.ToPCUIC.Coq.Init.
Import MetaCoq.Utils.utils.
Import MetaCoq.Common.MonadBasicAst.
Import MetaCoq.PCUIC.utils.PCUICAstUtils.
Import MetaCoq.PCUIC.PCUICMonadAst.
Import MetaCoq.PCUIC.PCUICAst.
Import MetaCoq.PCUIC.PCUICTyping.
Import MetaCoq.PCUIC.Syntax.PCUICReflect.
Import MetaCoq.TemplatePCUIC.PCUICTemplateMonad.
Import MetaCoq.TemplatePCUIC.Loader.
Export MetaCoq.Quotation.ToPCUIC.Init.
Import (hints) MetaCoq.Quotation.ToPCUIC.Coq.Init.
Import MCMonadNotation.
Import PCUICEnvironmentReflect.

Local Set Universe Polymorphism.
Local Unset Universe Minimization ToSet.

Class quotation_of_well_typed {cf : config.checker_flags} (Σ : global_env) {T} (t : T) {qT : quotation_of T} {qt : quotation_of t} := typing_quoted_term_of : wf Σ -> (Σ, Monomorphic_ctx) ;;; [] |- qt : qT.
Class ground_quotable_well_typed {cf : config.checker_flags} (Σ : global_env) T {qT : quotation_of T} {quoteT : ground_quotable T} := typing_quote_ground : forall t : T, quotation_of_well_typed Σ t.

Inductive dynlist := dnil | dcons {T} (t : T) (tl : dynlist).
Delimit Scope dynlist_scope with dynlist.
Notation "[ x ; y ; .. ; z ]" :=  (dcons x (dcons y .. (dcons z dnil) ..)) : dynlist_scope.

Definition erase_dynlist (globals : dynlist)
  := Eval cbv [dynlist_ind] in fun P n c => dynlist_ind (fun _ => P) n (fun T t _ r => c T t r) globals.
Definition env_for_globals (globals : forall P : Prop, P -> (forall x : Type, x -> P -> P) -> P) : TemplateMonad global_env_ext.
exact (qglobals <- tmQuoteRec globals;;
     ret (PCUICProgram.global_env_ext_map_global_env_ext (fst (qglobals:PCUICProgram.pcuic_program)))).
Defined.
Notation typing_restriction_for_globals ls
  := (match ls%dynlist return _ with
      | globals
        => ltac:(let globals := (eval cbv [erase_dynlist globals] in (erase_dynlist globals)) in
                 run_template_program
                   (env_for_globals globals)
                   (fun Σ => refine Σ))
      end)
       (only parsing).
Definition evalStateT {S M T} {TM : Monad M} (p : StateT S M T) (st : S) : M T.
exact ('(v, st) <- p st;;
     ret v).
Defined.

Variant quotation_check_error :=
  | QTypeError (_ : type_error)
  | QConfigNotNormalizing (cf : config.checker_flags)
  | QEnvError   (_ : env_error)
  | QContextTypeError (_ : type_error)
.

Definition quotation_check (cf : config.checker_flags) (Σ : global_env_ext) (Γ : context) (t T : term) : option quotation_check_error.
Admitted.
Lemma quotation_check_valid {cf Σ Γ t T} : quotation_check cf Σ Γ t T = None -> @wf_ext cf Σ * wf_local Σ Γ * @typing cf Σ Γ t T.
Admitted.
Definition universes_of_Instance (t : Instance.t) (acc : LevelSet.t) : LevelSet.t.
Admitted.
Definition universes_of_universe (t : Universe.t) (acc : LevelSet.t) : LevelSet.t.
Admitted.
Definition universes_of_prim_val {A} (universes_of_term' : A -> StateT LevelSet.t TemplateMonad A) (t : PCUICPrimitive.prim_val A) : StateT LevelSet.t TemplateMonad (PCUICPrimitive.prim_val A).
admit.
Defined.

Definition preuniverses_of_partial_term
  (universes_of_term : term -> StateT LevelSet.t TemplateMonad term)
  (t : term)
  : StateT LevelSet.t TemplateMonad term
  := qt <- State.lift (tmQuote t);;
     let '(qh, qargs) := decompose_app qt in
     rv <- match qh, qargs with
           | tRel _, _
           | tVar _, _
           | tEvar _ _, _
           | tConst _ _, _
             => ret (Some t)
           | tApp _ _, _
             => State.lift (tmPrint qt;; tmFail "preuniverses_of_partial_term: decompose_app should not return tApp")
           | tConstruct _ _ _, _
             => ret None
           | _, _
             => State.lift (tmPrint qt;; tmPrint (qh, qargs);; tmFail "preuniverses_of_partial_term: requires constructor tree or tRel, tVar, tEvar, tConst")
           end;;
     match rv with
     | Some rv => ret rv
     | None
       => universes_of_term t
     end.
Definition monad_map_universes {A} (f : A -> LevelSet.t -> LevelSet.t) (t : A) : StateT LevelSet.t TemplateMonad A.
exact (acc <- State.get;;
     State.set (f t acc);;
     ret t).
Defined.
Fixpoint universes_of_term' (t : term) : StateT LevelSet.t TemplateMonad term.
exact (let universes_of_term := preuniverses_of_partial_term universes_of_term' in
     match t with
     | tRel _
     | tVar _
       => ret t
     | tEvar _ l
       => _ <- monad_map universes_of_term l;;
          ret t
     | tSort u
       => _ <- monad_map_universes universes_of_universe u;;
          ret t
     | tProj _ c
       => _ <- universes_of_term c;;
          ret t
     | tProd _ A B
     | tLambda _ A B
     | tApp A B
       => _ <- universes_of_term A;;
          _ <- universes_of_term B;;
          ret t
     | tLetIn _ A B C
       => _ <- universes_of_term A;;
          _ <- universes_of_term B;;
          _ <- universes_of_term C;;
          ret t
     | tConst _ ui
     | tInd _ ui
     | tConstruct _ _ ui
       => _ <- monad_map_universes universes_of_Instance ui;;
          ret t
     | tFix mfix _
     | tCoFix mfix _
       => _ <- monad_map (monad_map_def universes_of_term universes_of_term) mfix;;
          ret t
     | tPrim prim
       => _ <- universes_of_prim_val universes_of_term prim;;
          ret t
     | tCase _ p c brs
       => _ <- monad_map_predicate
                 (monad_map_universes universes_of_Instance)
                 universes_of_term universes_of_term
                 (monad_map_context universes_of_term)
                 p;;
          _ <- universes_of_term c;;
          _ <- monad_map_branches universes_of_term (monad_map_context universes_of_term) brs;;
          ret t
     end).
Defined.
Definition universes_of_partial_term (t : term) : StateT LevelSet.t TemplateMonad LevelSet.t.
exact (preuniverses_of_partial_term universes_of_term' t;; State.get).
Defined.
Definition universes_of_type_of_quotation_of_well_typed' {cf Σ T t qT qt} (_ : @quotation_of_well_typed cf Σ T t qT qt) : TemplateMonad LevelSet.t.
exact (v <- evalStateT (universes_of_partial_term qT;; universes_of_partial_term qt) LevelSet.empty;;
     tmEval cbv v).
Defined.
Notation universes_of_type_of_quotation_of_well_typed qty
  := (match qty return _ with
      | qtyv
        => ltac:(run_template_program (universes_of_type_of_quotation_of_well_typed' qtyv) (fun v => exact v))
      end) (only parsing).
Definition merge_universe_levels (Σ : global_env_ext) (univs : LevelSet.t) : global_env_ext.
Admitted.
#[export] Instance well_typed_ground_quotable_of_bp
  {b P} (H : b = true -> P)
  {qH : quotation_of H} (H_for_safety : P -> b = true)
  {qP : quotation_of P}
  {cfH cfP : config.checker_flags} {ΣH ΣP}
  {qtyH : quotation_of_well_typed (cf:=cfH) ΣH H} {qtyP : quotation_of_well_typed (cf:=cfP) ΣP P}
  (Σ0' := typing_restriction_for_globals [bool; @eq bool])
  (Σ0 := merge_universe_levels
           Σ0'
           (LevelSet.union
              (universes_of_type_of_quotation_of_well_typed qtyH)
              (universes_of_type_of_quotation_of_well_typed qtyP)))
  (Σ := merge_global_envs Σ0 (merge_global_envs ΣH ΣP))
  {Hc : Is_true (compatibleb ΣH ΣP && compatibleb Σ0 (merge_global_envs ΣH ΣP))}
  (HwfP : @wf cfP ΣP)
  (HwfH : @wf cfH ΣH)
  : @ground_quotable_well_typed (config.union_checker_flags cfH cfP) Σ _ qP (@ground_quotable_of_bp b P H qH H_for_safety).
Proof.
  subst Σ0'.
  intros t wfΣ.
  Time  (intros; lazymatch goal with |- @typing ?cf ?Σ ?Γ ?t ?T => pose proof (@quotation_check_valid config.strictest_checker_flags Σ0 Γ t T) as H' end; clear H'; admit).
Time Timeout 1 Qed.
