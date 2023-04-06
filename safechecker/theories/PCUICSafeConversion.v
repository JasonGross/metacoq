(* -*- mode: coq; coq-prog-args: ("-emacs" "-q" "-w" "-deprecated-native-compiler-option" "-native-compiler" "no" "-R" "/github/workspace/metacoq/utils/theories" "MetaCoq.Utils" "-R" "/github/workspace/metacoq/common/theories" "MetaCoq.Common" "-R" "/github/workspace/metacoq/pcuic/theories" "MetaCoq.PCUIC" "-R" "/github/workspace/metacoq/safechecker/theories" "MetaCoq.SafeChecker" "-Q" "/github/workspace/cwd" "Top" "-Q" "/home/coq/.opam/4.13.1+flambda/lib/coq/user-contrib/Bignums" "Bignums" "-Q" "/home/coq/.opam/4.13.1+flambda/lib/coq/user-contrib/Equations" "Equations" "-Q" "/home/coq/.opam/4.13.1+flambda/lib/coq/user-contrib/Ltac2" "Ltac2" "-top" "MetaCoq.SafeChecker.PCUICSafeConversion") -*- *)
(* File reduced by coq-bug-minimizer from original input, then from 5927 lines to 1512 lines, then from 1095 lines to 222 lines, then from 235 lines to 2362 lines, then from 2362 lines to 1248 lines *)
(* coqc version 8.16.1 compiled with OCaml 4.13.1
   coqtop version 8.16.1
   Expected coqc runtime on this file: 112.421 sec *)
Require Coq.Init.Ltac.
Module Export AdmitTactic.
Module Import LocalFalse.
Inductive False : Prop := .
End LocalFalse.
Axiom proof_admitted : False.
Import Coq.Init.Ltac.
Tactic Notation "admit" := abstract case proof_admitted.
End AdmitTactic.
Module MetaCoq_DOT_SafeChecker_DOT_PCUICSafeReduce_WRAPPED.
Module PCUICSafeReduce.


Require Coq.Classes.RelationClasses.
Import Coq.Classes.RelationClasses.

Require MetaCoq.Utils.utils.
Import MetaCoq.Utils.utils.

Require MetaCoq.Common.config.
Import MetaCoq.Common.config.

Require MetaCoq.PCUIC.PCUICCanonicity.
Require MetaCoq.PCUIC.PCUICWellScopedCumulativity.
Require MetaCoq.PCUIC.Syntax.PCUICOnFreeVars.
Require MetaCoq.PCUIC.PCUICConversion.
Require MetaCoq.PCUIC.PCUICConfluence.
Require MetaCoq.PCUIC.PCUICSafeLemmata.
Require MetaCoq.PCUIC.PCUICValidity.
Require MetaCoq.PCUIC.PCUICReduction.
Require MetaCoq.PCUIC.utils.PCUICUtils.
Require MetaCoq.PCUIC.PCUICSN.
Require MetaCoq.PCUIC.PCUICSR.
Require MetaCoq.PCUIC.PCUICInversion.
Require MetaCoq.PCUIC.PCUICNormal.
Require MetaCoq.PCUIC.Syntax.PCUICPosition.
Require MetaCoq.PCUIC.PCUICTyping.
Require MetaCoq.PCUIC.Syntax.PCUICUnivSubst.
Require MetaCoq.PCUIC.Syntax.PCUICLiftSubst.
Require MetaCoq.PCUIC.PCUICGeneration.
Require MetaCoq.PCUIC.utils.PCUICAstUtils.
Require MetaCoq.PCUIC.PCUICAst.
Import MetaCoq.PCUIC.PCUICAst MetaCoq.PCUIC.utils.PCUICAstUtils
     MetaCoq.PCUIC.PCUICGeneration MetaCoq.PCUIC.Syntax.PCUICLiftSubst
     MetaCoq.PCUIC.Syntax.PCUICUnivSubst MetaCoq.PCUIC.PCUICTyping MetaCoq.PCUIC.Syntax.PCUICPosition MetaCoq.PCUIC.PCUICNormal
     MetaCoq.PCUIC.PCUICInversion MetaCoq.PCUIC.PCUICSR MetaCoq.PCUIC.PCUICSN
     MetaCoq.PCUIC.utils.PCUICUtils MetaCoq.PCUIC.PCUICReduction MetaCoq.PCUIC.PCUICValidity MetaCoq.PCUIC.PCUICSafeLemmata
     MetaCoq.PCUIC.PCUICConfluence MetaCoq.PCUIC.PCUICConversion
     MetaCoq.PCUIC.Syntax.PCUICOnFreeVars MetaCoq.PCUIC.PCUICWellScopedCumulativity
     MetaCoq.PCUIC.PCUICCanonicity.


Require MetaCoq.SafeChecker.PCUICWfEnv.
Require MetaCoq.SafeChecker.PCUICWfReduction.
Require MetaCoq.SafeChecker.PCUICErrors.
Import MetaCoq.SafeChecker.PCUICErrors MetaCoq.SafeChecker.PCUICWfReduction MetaCoq.SafeChecker.PCUICWfEnv.


Require Equations.Prop.DepElim.
Import Equations.Prop.DepElim.

Require Equations.Prop.Equations.
Import Equations.Prop.Equations.
Set Equations Transparent.
Set Equations With UIP.




Notation " `  t " := (proj1_sig t) (at level 10, t at next level) : metacoq_scope.

Set Default Goal Selector "!".

Local Set Keyed Unification.

Implicit Types (cf : checker_flags) (Σ : global_env_ext).

Lemma welltyped_is_closed_context {cf Σ} {wfΣ : wf Σ} {Γ t} :
  welltyped Σ Γ t -> is_closed_context Γ.
Admitted.
#[global] Hint Resolve welltyped_is_closed_context : fvs.

Lemma welltyped_is_open_term {cf Σ} {wfΣ : wf Σ} {Γ t} :
  welltyped Σ Γ t -> is_open_term Γ t.
Admitted.
#[global] Hint Resolve welltyped_is_open_term : fvs.


Section Measure.

  Context {cf : checker_flags} {no : normalizing_flags}.

  Context (flags : RedFlags.t).
  Context (Σ : global_env_ext).

  Definition R_aux Γ :=
    dlexprod (cored Σ Γ) (@posR).

  Definition R Γ u v :=
    R_aux Γ (zip u ; stack_pos (fst u) (snd u))
            (zip v ; stack_pos (fst v) (snd v)).

  Lemma cored_welltyped :
    forall {Γ u v},
      wf Σ -> welltyped Σ Γ u ->
      cored Σ Γ v u ->
      welltyped Σ Γ v.
Admitted.

  Lemma red_welltyped :
    forall {Γ u v},
      wf Σ -> welltyped Σ Γ u ->
      red (fst Σ) Γ u v ->
      welltyped Σ Γ v.
Admitted.

  Derive Signature for Acc.
  Lemma R_positionR :
    forall Γ t1 t2 (p1 : pos t1) (p2 : pos t2),
      t1 = t2 ->
      positionR (` p1) (` p2) ->
      R_aux Γ (t1 ; p1) (t2 ; p2).
Admitted.

  Definition Req Γ t t' :=
    t = t' \/ R Γ t t'.

  Lemma Rtrans :
    forall Γ u v w,
      R Γ u v ->
      R Γ v w ->
      R Γ u w.
admit.
Defined.

  Lemma Req_trans :
    forall {Γ}, Transitive (Req Γ).
admit.
Defined.

  Lemma R_to_Req :
    forall {Γ u v},
      R Γ u v ->
      Req Γ u v.
admit.
Defined.

  Instance Req_refl : forall Γ, Reflexive (Req Γ).
Admitted.

  Lemma R_Req_R :
    forall {Γ u v w},
      R Γ u v ->
      Req Γ v w ->
      R Γ u w.
Admitted.

End Measure.


Section Acc_sidecond_generator.
  Context {A : Type} {R : A -> A -> Prop} {P : A -> Prop}.
  Variable Pimpl : forall x y, P x -> R y x -> P y.

  Fixpoint Acc_intro_generator n (acc : forall t, P t -> Acc R t) : forall t, P t -> Acc R t :=
    match n with
        | O => acc
        | S n => fun x Px =>
                   Acc_intro x (fun y Hy => Acc_intro_generator n (Acc_intro_generator n acc) y (Pimpl _ _ Px Hy))
    end.
End Acc_sidecond_generator.

Opaque Acc_intro_generator.

Section Reduce.

  Context {cf : checker_flags} {no : normalizing_flags}.

  Context (flags : RedFlags.t).

  Context (X_type : abstract_env_impl).

  Context (X : X_type.π2.π1).

  Context {normalization_in : forall Σ, wf_ext Σ -> Σ ∼_ext X -> NormalizationIn Σ}.



  Local Definition heΣ Σ (wfΣ : abstract_env_ext_rel X Σ) :
    ∥ wf_ext Σ ∥ :=  abstract_env_ext_wf _ wfΣ.

  Local Definition hΣ Σ (wfΣ : abstract_env_ext_rel X Σ) :
    ∥ wf Σ ∥ := abstract_env_ext_sq_wf _ _ _ wfΣ.

  Existing Instance Req_refl.

Lemma acc_dlexprod_gen P Q A B (leA : P -> A -> A -> Prop)
  (HQ : ∥ ∑ p , Q p ∥)
  (HP : forall p p' x x', Q p -> Q p' -> leA p x x' -> leA p' x x')
  (leB : forall x : A, B x -> B x -> Prop) :
  (forall x, well_founded (leB x)) ->
  forall x,
    Acc (fun t t' => forall (p:P), Q p -> leA p t t') x ->
    forall y,
      Acc (leB x) y ->
      Acc (fun t t' => forall (p:P), Q p -> @dlexprod A B (leA p) leB t t') (x;y).
admit.
Defined.

Lemma dlexprod_Acc_gen P Q A B (leA : P -> A -> A -> Prop)
  (HQ : ∥ ∑ p , Q p ∥)
  (HP : forall p p' x x', Q p -> Q p' -> leA p x x' -> leA p' x x')
  (leB : forall x : A, B x -> B x -> Prop) :
    (forall x, well_founded (leB x)) ->
    forall x y,
      Acc (fun t t' => forall (p:P), Q p -> leA p t t') x ->
      Acc (fun t t' => forall (p:P), Q p -> @dlexprod A B (leA p) leB t t') (x;y).
admit.
Defined.

Definition R_singleton Abs A
  (R : Abs -> A -> A -> Prop) (Q : Abs -> Prop) x (q : Q x)
  (HQ : forall x x' , Q x -> Q x' -> x = x') (a a' : A) :
  R x a a' <-> (forall x, Q x -> R x a a').
Proof using Type.
  split.
  -
 intros H x' q'.
 specialize (HQ x x' q q').
subst; eauto.
  -
 eauto.
Defined.

Fixpoint Acc_equiv A (R R' : A -> A -> Prop)
  (Heq : forall a a', R a a' <-> R' a a') a
  (HAcc : Acc R a) : Acc R' a.
Proof using Type.
  econstructor.
intros.
apply Heq in H.
  destruct HAcc.
eapply Acc_equiv; eauto.
Defined.

Corollary R_Acc_aux :
    forall Γ t p,
    (forall Σ (wfΣ : abstract_env_ext_rel X Σ), welltyped Σ Γ t) ->
    (Acc (fun t t' => forall Σ (wfΣ : abstract_env_ext_rel X Σ), R_aux Σ Γ t t') (t ; p)).
  Proof using normalization_in.
    intros Γ t p h.
    eapply dlexprod_Acc_gen.
    -
 apply abstract_env_ext_exists.
    -
 intros.
eapply abstract_env_cored; try apply H1; eauto.
    -
 intros x.
unfold well_founded.
      eapply posR_Acc.
    -
 destruct (abstract_env_ext_exists X) as [[Σ wfΣ]];
      destruct (heΣ _ wfΣ).
      eapply Acc_equiv; try
      eapply normalization_in; eauto.
      eapply R_singleton with (Q := abstract_env_ext_rel X)
          (R := fun Σ a a' => cored Σ Γ a a'); eauto.
      intros; eapply abstract_env_ext_irr; eauto.
  Defined.

  Corollary R_Acc :
    forall Γ t,
      (forall Σ (wfΣ : abstract_env_ext_rel X Σ), welltyped Σ Γ (zip t)) ->
      Acc (fun t t' => forall Σ (wfΣ : abstract_env_ext_rel X Σ), R Σ Γ t t') t.
admit.
Defined.

  Definition inspect {A} (x : A) : { y : A | y = x } := exist x eq_refl.

  Definition Pr (t' : term * stack) π :=
    snd (decompose_stack π) = snd (decompose_stack (snd t')).

  Notation givePr := (_) (only parsing).

  Definition Pr' (t' : term * stack) :=
    isApp (fst t') = false /\
    (RedFlags.beta flags -> isLambda (fst t') -> isStackApp (snd t') = false).

  Notation givePr' := (conj _ (fun β hl => _)) (only parsing).

  Notation rec reduce t π :=
    (let smaller := _ in
     let '(exist res prf_Σ) := reduce t π smaller in
     exist res (fun Σ wfΣ => let '((conj prf (conj h (conj h1 h2)))) := prf_Σ Σ wfΣ in conj (Req_trans _ _ _ _ _ (R_to_Req _ (smaller Σ wfΣ))) (conj givePr givePr'))
    ) (only parsing).

  Notation give t π :=
    (exist (t,π) (fun Σ wfΣ => conj _ (conj givePr givePr'))) (only parsing).

  Tactic Notation "zip" "fold" "in" hyp(h) :=
    lazymatch type of h with
    | context C[ zipc ?t ?π ] =>
      let C' := context C[ zip (t,π) ] in
      change C' in h
    end.

  Tactic Notation "zip" "fold" :=
    lazymatch goal with
    | |- context C[ zipc ?t ?π ] =>
      let C' := context C[ zip (t,π) ] in
      change C'
    end.

  Lemma Req_red Σ :
    forall Γ x y,
      Req Σ Γ y x ->
      ∥ red Σ Γ (zip x) (zip y) ∥.
admit.
Defined.


  Ltac obTac :=

    Program.Tactics.program_simplify ;
    Equations.CoreTactics.equations_simpl ;
    try Program.Tactics.program_solve_wf ;
    try reflexivity.

  Obligation Tactic := obTac.

  Lemma discr_construct (t : term) : Prop. Admitted.

  Inductive construct_view : term -> Type :=
  | view_construct : forall ind n ui, construct_view (tConstruct ind n ui)
  | view_other : forall t, discr_construct t -> construct_view t.

  Lemma construct_viewc t : construct_view t. Admitted.


  Lemma red_discr (t : term) (π : stack) : Prop. Admitted.

  Inductive red_view : term -> stack -> Type :=
  | red_view_Rel c π : red_view (tRel c) π
  | red_view_LetIn A b B c π : red_view (tLetIn A b B c) π
  | red_view_Const c u π : red_view (tConst c u) π
  | red_view_App f a π : red_view (tApp f a) π
  | red_view_Lambda na A t a args : red_view (tLambda na A t) (App_l a :: args)
  | red_view_Fix mfix idx π : red_view (tFix mfix idx) π
  | red_view_Case ci p c brs π : red_view (tCase ci p c brs) π
  | red_view_Proj p c π : red_view (tProj p c) π
  | red_view_other t π : red_discr t π -> red_view t π.

  Lemma red_viewc t π : red_view t π. Admitted.

  Lemma discr_construct_cofix (t : term) : Prop. Admitted.

  Inductive construct_cofix_view : term -> Type :=
  | ccview_construct : forall ind n ui, construct_cofix_view (tConstruct ind n ui)
  | ccview_cofix : forall mfix idx, construct_cofix_view (tCoFix mfix idx)
  | ccview_other : forall t, discr_construct_cofix t -> construct_cofix_view t.

  Lemma cc_viewc t : construct_cofix_view t. Admitted.

  Lemma discr_construct0_cofix (t : term) : Prop. Admitted.

  Inductive construct0_cofix_view : term -> Type :=
  | cc0view_construct : forall ind ui, construct0_cofix_view (tConstruct ind 0 ui)
  | cc0view_cofix : forall mfix idx, construct0_cofix_view (tCoFix mfix idx)
  | cc0view_other : forall t, discr_construct0_cofix t -> construct0_cofix_view t.

  Lemma cc0_viewc t : construct0_cofix_view t. Admitted.

  Lemma _reduce_stack (Γ : context) (t : term) (π : stack)
            (h : forall Σ (wfΣ : abstract_env_ext_rel X Σ), welltyped Σ Γ (zip (t,π)))
            (reduce : forall t' π', (forall Σ (wfΣ : abstract_env_ext_rel X Σ), R Σ Γ (t',π') (t,π)) ->
                               { t'' : term * stack | forall Σ (wfΣ : abstract_env_ext_rel X Σ), Req Σ Γ t'' (t',π') /\ Pr t'' π' /\ Pr' t'' })
    : { t' : term * stack | forall Σ (wfΣ : abstract_env_ext_rel X Σ), Req Σ Γ t' (t,π) /\ Pr t' π /\ Pr' t' }.
    Admitted.

  Lemma welltyped_R_pres Σ (wfΣ : abstract_env_ext_rel X Σ) Γ :
    forall x y : term × stack, welltyped Σ Γ (zip x) -> R Σ Γ y x -> welltyped Σ Γ (zip y).
Admitted.

  Section reducewf.
    Context (Γ : context).

    Notation sigmaarg :=
      (sigma (fun t => sigma (fun π => forall Σ, abstract_env_ext_rel X Σ -> welltyped Σ Γ (zipc t π)))).

    Local Instance wf_proof : WellFounded (fun x y : sigmaarg =>
        forall Σ, abstract_env_ext_rel X Σ -> R Σ Γ (pr1 x, pr1 (pr2 x)) (pr1 y, pr1 (pr2 y))).
    Proof using normalization_in.
      intros [t [π wt]].

      unshelve eapply (Acc_intro_generator
        (R:=fun x y : sigmaarg => forall Σ (wfΣ : abstract_env_ext_rel X Σ), R Σ Γ (x.(pr1), x.(pr2).(pr1)) (y.(pr1), y.(pr2).(pr1)))
        (P:=fun x : sigmaarg => forall Σ (wfΣ : abstract_env_ext_rel X Σ), welltyped Σ Γ (zip (x.(pr1), x.(pr2).(pr1))))
        (fun x y Px Hy => _) 1000 _ {| pr1 := t; pr2 := {| pr1 := π; pr2 := wt |} |} wt).
      -
 cbn in *.
intros.
destruct y as [t' [π' wt']].
cbn.
now apply wt'.
      -
 cbn in *.
intros.
        destruct (abstract_env_ext_exists X) as [[Σ wfΣ]].
        destruct (hΣ _ wfΣ) as [hΣ].
pose proof (R_Acc Γ (t0.(pr1), t0.(pr2).(pr1)) H).
        clear -H0.
destruct t0 as [t [π wt]].
        cbn in *.
revert wt.
        depind H0.
intros wt.
constructor.
intros.
eapply H0.
        *
 cbn in H1.
exact H1.
        *
 reflexivity.
  Defined.

  Lemma reduce_stack_full (t : term) (π : stack) (h : forall Σ (wfΣ : abstract_env_ext_rel X Σ), welltyped Σ Γ (zip (t,π))) :
    { t' : term * stack | forall Σ (wfΣ : abstract_env_ext_rel X Σ), Req Σ Γ t' (t, π) /\ Pr t' π /\ Pr' t' }.
Admitted.

  End reducewf.

  Definition reduce_stack Γ t π h :=
    let '(exist ts _) := reduce_stack_full Γ t π h in ts.

  Lemma reduce_stack_Req :
    forall Σ (wfΣ : abstract_env_ext_rel X Σ) Γ t π h,
     Req Σ Γ (reduce_stack Γ t π h) (t, π).
Admitted.

  Theorem reduce_stack_sound :
    forall Σ (wfΣ : abstract_env_ext_rel X Σ) Γ t π h,
      ∥ Σ ;;; Γ ⊢ zip (t, π) ⇝ zip (reduce_stack Γ t π h) ∥.
Admitted.

  Lemma reduce_stack_decompose :
    forall Γ t π h,
      snd (decompose_stack (snd (reduce_stack Γ t π h))) =
      snd (decompose_stack π).
Admitted.

  Lemma reduce_stack_context :
    forall Γ t π h,
      stack_context (snd (reduce_stack Γ t π h)) =
      stack_context π.
Admitted.

  Definition isred (t : term * stack) :=
    isApp (fst t) = false /\
    (isLambda (fst t) -> isStackApp (snd t) = false).

  Lemma reduce_stack_isred :
    forall Γ t π h,
      RedFlags.beta flags ->
      isred (reduce_stack Γ t π h).
Admitted.

  Lemma reduce_stack_noApp :
    forall Γ t π h,
      isApp (fst (reduce_stack Γ t π h)) = false.
Admitted.

  Lemma reduce_stack_noLamApp :
    forall Γ t π h,
      RedFlags.beta flags ->
      isLambda (fst (reduce_stack Γ t π h)) ->
      isStackApp (snd (reduce_stack Γ t π h)) = false.
Admitted.

  Definition reduce_term Γ t
    (h : forall Σ, abstract_env_ext_rel X Σ -> welltyped Σ Γ t) :=
    zip (reduce_stack Γ t [] h).

  Theorem reduce_term_sound :
    forall Γ t (h : forall Σ, abstract_env_ext_rel X Σ -> welltyped Σ Γ t)
      Σ, abstract_env_ext_rel X Σ ->
      ∥ Σ ;;; Γ ⊢ t ⇝ reduce_term Γ t h ∥.
Admitted.

  Scheme Acc_ind' := Induction for Acc Sort Prop.

  Lemma Fix_F_prop :
    forall A R P f (pred : forall x : A, P x -> Prop) x hx,
      (forall x aux, (forall y hy, pred y (aux y hy)) -> pred x (f x aux)) ->
      pred x (@Fix_F A R P f x hx).
Admitted.

  Lemma reduce_stack_prop :
    forall Γ t π h (P : term × stack -> term × stack -> Prop),
      (forall t π h aux,
          (forall t' π' hR, P (t', π') (` (aux t' π' hR))) ->
          P (t, π) (` (_reduce_stack Γ t π h aux))) ->
      P (t, π) (reduce_stack Γ t π h).
Admitted.

  Lemma decompose_stack_at_appstack_None l s n :
    isStackApp s = false ->
    nth_error l n = None <->
    decompose_stack_at (appstack l s) n = None.
Admitted.

  Lemma mkApps_tApp hd arg args :
    mkApps (tApp hd arg) args = mkApps hd (arg :: args).
Admitted.

  Lemma tApp_mkApps hd args arg :
    tApp (mkApps hd args) arg = mkApps hd (args ++ [arg]).
Admitted.

  Lemma whnf_non_ctor_finite_ind_typed Σ Γ t ind u args :
    wf Σ ->
    whnf flags Σ Γ t ->
    isConstruct_app t = false ->
    check_recursivity_kind (lookup_env Σ) (inductive_mind ind) CoFinite = false ->
    Σ ;;; Γ |- t : mkApps (tInd ind u) args ->
    whne flags Σ Γ t.
Admitted.

  Definition isCoFix_app t :=
    match (decompose_app t).1 with
    | tCoFix _ _ => true
    | _ => false
    end.

  Lemma whnf_non_ctor_non_cofix_ind_typed Σ Γ t ind u args :
    wf Σ ->
    whnf flags Σ Γ t ->
    isConstruct_app t = false ->
    isCoFix_app t = false ->
    Σ ;;; Γ |- t : mkApps (tInd ind u) args ->
    whne flags Σ Γ t.
Admitted.

  Lemma whnf_fix_arg_whne mfix idx body Σ Γ t before args aftr ty :
    wf Σ ->
    unfold_fix mfix idx = Some (#|before|, body) ->
    match t with
    | tConstruct _ _ _ => False
    | tApp _ _ => False
    | _ => True
    end ->
    whnf flags Σ Γ (mkApps t args) ->
    Σ ;;; Γ |- mkApps (tFix mfix idx) (before ++ mkApps t args :: aftr) : ty ->
    whne flags Σ Γ (mkApps t args).
Admitted.

  Lemma whnf_case_arg_whne Σ Γ hd args ci p brs T :
    wf Σ ->
    match hd with
    | tApp _ _
    | tConstruct _ _ _
    | tCoFix _ _ => False
    | _ => True
    end ->
    whnf flags Σ Γ (mkApps hd args) ->
    Σ;;; Γ |- tCase ci p (mkApps hd args) brs : T ->
    whne flags Σ Γ (mkApps hd args).
Admitted.

  Lemma whnf_proj_arg_whne Σ Γ hd args p T :
    wf Σ ->
    match hd with
    | tApp _ _
    | tCoFix _ _ => False
    | tConstruct _ c _ => c <> 0
    | _ => True
    end ->
    whnf flags Σ Γ (mkApps hd args) ->
    Σ ;;; Γ |- tProj p (mkApps hd args) : T ->
    whne flags Σ Γ (mkApps hd args).
Admitted.

  Lemma reduce_stack_whnf :
    forall Γ t π h Σ (wfΣ : abstract_env_ext_rel X Σ),
      let '(u, ρ) := reduce_stack Γ t π h in
       ∥whnf flags Σ (Γ ,,, stack_context ρ) (zipp u ρ)∥.
Admitted.

  Theorem reduce_term_complete Σ (wfΣ : abstract_env_ext_rel X Σ) Γ t h :
    ∥whnf flags Σ Γ (reduce_term Γ t h)∥.
Admitted.

End Reduce.

Section ReduceFns.

  Context {cf : checker_flags} {no : normalizing_flags}
          {X_type : abstract_env_impl} {X : X_type.π2.π1} {normalization_in : forall Σ, wf_ext Σ -> Σ ∼_ext X -> NormalizationIn Σ}.


  Opaque reduce_stack_full.

  Definition hnf := reduce_term RedFlags.default X_type X.

  Theorem hnf_sound {Γ t h} Σ (wfΣ : abstract_env_ext_rel X Σ) : ∥ Σ ;;; Γ ⊢ t ⇝ hnf Γ t h ∥.
  Proof using Type.
    unfold hnf.
    destruct (reduce_term_sound RedFlags.default _ X _ _ h Σ wfΣ).
    sq.
eapply into_closed_red; fvs.
  Defined.

  Theorem hnf_complete {Γ t h} Σ (wfΣ : abstract_env_ext_rel X Σ) : ∥whnf RedFlags.default Σ Γ (hnf Γ t h)∥.
Admitted.

  Lemma reduce_to_sort (Γ : context) (t : term)
    (h : forall Σ (wfΣ : abstract_env_ext_rel X Σ), welltyped Σ Γ t)
    : typing_result_comp (∑ u, forall Σ (wfΣ : abstract_env_ext_rel X Σ), ∥ Σ ;;; Γ ⊢ t ⇝ tSort u ∥).
  Admitted.


  Lemma reduce_to_sort_complete {Γ t wt} Σ (wfΣ : abstract_env_ext_rel X Σ)
    e p :
    reduce_to_sort Γ t wt = TypeError_comp e p ->
    (forall s, red Σ Γ t (tSort s) -> False).
Admitted.

  Lemma reduce_to_prod (Γ : context) (t : term)
    (h : forall Σ (wfΣ : abstract_env_ext_rel X Σ), welltyped Σ Γ t)
    : typing_result_comp (∑ na a b, forall  Σ (wfΣ : abstract_env_ext_rel X Σ), ∥ Σ ;;; Γ ⊢ t ⇝ tProd na a b ∥).
  Admitted.


  Lemma reduce_to_prod_complete {Γ t wt} Σ (wfΣ : abstract_env_ext_rel X Σ)
    e p :
    reduce_to_prod Γ t wt = TypeError_comp e p ->
    (forall na a b, red Σ Γ t (tProd na a b) -> False).
Admitted.

  Lemma reduce_to_ind (Γ : context) (t : term)
    (h : forall Σ (wfΣ : abstract_env_ext_rel X Σ), welltyped Σ Γ t)
    : typing_result_comp (∑ i u l, forall Σ (wfΣ : abstract_env_ext_rel X Σ), ∥ Σ ;;; Γ ⊢ t ⇝ mkApps (tInd i u) l ∥).
  Admitted.


  Lemma reduce_to_ind_complete  Σ (wfΣ : abstract_env_ext_rel X Σ) Γ ty wat e p :
    reduce_to_ind Γ ty wat = TypeError_comp e p ->
    forall ind u args,
      red Σ Γ ty (mkApps (tInd ind u) args) ->
      False.
Admitted.


  Definition arity_ass := aname * term.

  Fixpoint mkAssumArity (l : list arity_ass) (s : Universe.t) : term :=
    match l with
    | [] => tSort s
    | (na, A) :: l => tProd na A (mkAssumArity l s)
    end.

  Definition arity_ass_context := rev_map (fun '(na, A) => vass na A).

  Lemma assumption_context_arity_ass_context l :
    assumption_context (arity_ass_context l).
Admitted.

  Lemma mkAssumArity_it_mkProd_or_LetIn (l : list arity_ass) (s : Universe.t) :
    mkAssumArity l s = it_mkProd_or_LetIn (arity_ass_context l) (tSort s).
Admitted.

  Lemma isArity_mkAssumArity l s :
    isArity (mkAssumArity l s).
Admitted.

  Record conv_arity {Γ T} : Type :=
    build_conv_arity {
        conv_ar_context : list arity_ass;
        conv_ar_univ : Universe.t;
        conv_ar_red : forall Σ (wfΣ : abstract_env_ext_rel X Σ), ∥ Σ ;;; Γ ⊢ T ⇝ mkAssumArity conv_ar_context conv_ar_univ ∥
      }.

  Global Arguments conv_arity : clear implicits.

  Lemma conv_arity_Is_conv_to_Arity {Γ T} :
    is_closed_context Γ ->
    is_open_term Γ T ->
    conv_arity Γ T ->
    forall Σ (wfΣ : abstract_env_ext_rel X Σ), Is_conv_to_Arity Σ Γ T.
Admitted.

  Lemma isArity_red Σ Γ u v :
    isArity u ->
    red Σ Γ u v ->
    isArity v.
Admitted.

  Lemma Is_conv_to_Arity_red Σ {wfΣ : wf Σ} Γ T T' :
    Is_conv_to_Arity Σ Γ T ->
    Σ ;;; Γ ⊢ T ⇝ T' ->
    Is_conv_to_Arity Σ Γ T'.
Admitted.

  Local Instance wellfounded Σ wfΣ {normalization:NormalizationIn Σ} : WellFounded (@hnf_subterm_rel _ Σ) :=
    @wf_hnf_subterm _ _ _ normalization (heΣ _ X Σ wfΣ).

End ReduceFns.

End PCUICSafeReduce.

End MetaCoq_DOT_SafeChecker_DOT_PCUICSafeReduce_WRAPPED.
Module Export MetaCoq_DOT_SafeChecker_DOT_PCUICSafeReduce.
Module Export MetaCoq.
Module Export SafeChecker.
Module PCUICSafeReduce.
Include MetaCoq_DOT_SafeChecker_DOT_PCUICSafeReduce_WRAPPED.PCUICSafeReduce.
End PCUICSafeReduce.

End SafeChecker.

End MetaCoq.

End MetaCoq_DOT_SafeChecker_DOT_PCUICSafeReduce.
Require MetaCoq.PCUIC.PCUICConvCumInversion.
Axiom proof_admitted : False.
Tactic Notation "admit" := abstract case proof_admitted.
Import MetaCoq.Utils.utils.
Import MetaCoq.Common.config.
Import MetaCoq.PCUIC.PCUICAst.
Import MetaCoq.PCUIC.PCUICTyping.
Import MetaCoq.PCUIC.PCUICConversion.
Import MetaCoq.PCUIC.PCUICNormal.
Import MetaCoq.PCUIC.Syntax.PCUICPosition.
Import MetaCoq.PCUIC.PCUICSN.
Import MetaCoq.PCUIC.PCUICWellScopedCumulativity.
Import MetaCoq.PCUIC.PCUICConvCumInversion.
Import MetaCoq.SafeChecker.PCUICErrors.
Import MetaCoq.SafeChecker.PCUICWfEnv.
Import MetaCoq.SafeChecker.PCUICSafeReduce.

  Context {cf : checker_flags} {nor : normalizing_flags}.

  Context (X_type : abstract_env_impl).

  Context (X : X_type.π2.π1).

  Inductive state :=
  | Reduction
  | Term
  | Args
  | Fallback.

  Notation wtp Γ t π :=
    (forall Σ (wfΣ : abstract_env_ext_rel X Σ), welltyped Σ Γ (zipc t π)) (only parsing).

  Record pack (Γ : context) := mkpack {
    st   : state ;
    tm1  : term ;
    stk1 : stack ;
    tm2  : term ;
    stk2 : stack ;
    wth  : wtp Γ tm2 stk2
  }.

  Arguments st {_} _.
  Arguments tm1 {_} _.
  Arguments stk1 {_} _.
  Arguments tm2 {_} _.
  Arguments stk2 {_} _.
  Arguments wth {_} _.

  Definition wterm Γ := { t : term | forall Σ (wfΣ : abstract_env_ext_rel X Σ), welltyped Σ Γ t }.

  Lemma R_aux (Γ : context) :
    (∑ t : term, pos t × (∑ w : wterm Γ, pos (` w) × state)) ->
    (∑ t : term, pos t × (∑ w : wterm Γ, pos (` w) × state)) -> Prop.
Admitted.

  Notation pzt u := (zipc (tm1 u) (stk1 u)) (only parsing).
  Notation pps1 u := (stack_pos (tm1 u) (stk1 u)) (only parsing).
  Notation pwt u := (exist (P := fun t => forall Σ, abstract_env_ext_rel X Σ -> welltyped Σ _ t)
                                 _ (fun Σ wfΣ => wth u Σ wfΣ)) (only parsing).
  Notation pps2 u := (stack_pos (tm2 u) (stk2 u)) (only parsing).

  Notation obpack u:=
    (pzt u ; (pps1 u, (pwt u; (pps2 u, st u)))) (only parsing).

  Axiom R : forall Γ : context, pack Γ -> pack Γ -> Prop.

  Notation conv_stack_ctx Γ π1 π2 :=
    (forall Σ, abstract_env_ext_rel X Σ -> ∥ (Σ ⊢ Γ ,,, stack_context π1 = Γ ,,, stack_context π2) ∥).

  Notation conv_term leq Γ t π t' π' :=
    (forall Σ, abstract_env_ext_rel X Σ -> conv_cum leq Σ (Γ ,,, stack_context π) (zipp t π) (zipp t' π'))
      (only parsing).

  Inductive ConversionResult (P : Prop) :=
  | Success (h : P)
  | Error (e : ConversionError) (h : ~P).

  Arguments Success {_} _.
  Arguments Error {_} _.

  Axiom isred_full : context -> term -> stack -> Prop.
  Lemma prog_discr (t1 t2 : term) : Prop.
Admitted.

  Definition Ret (s:state) Γ t π t' π' :=
    forall (leq : conv_pb),
      conv_stack_ctx Γ π π' ->
      True -> True -> True ->
      ConversionResult (conv_term leq Γ t π t' π').

  Definition Aux s Γ t1 π1 t2 π2 h2 :=
     forall s' t1' π1' t2' π2'
       (h1' : wtp Γ t1' π1')
       (h2' : wtp Γ t2' π2'),
       conv_stack_ctx Γ π1 π2 ->
       R Γ
         (mkpack Γ s' t1' π1' t2' π2' h2')
         (mkpack Γ s t1 π1 t2 π2 h2) ->
       Ret s' Γ t1' π1' t2' π2'.

  Notation expand aux := (fun a b c d e f g h i => aux _ _ _ _ _ _ _ _ _) (only parsing).

  Local Notation yes := (Success _) (only parsing).
  Local Notation no := (fun e => Error e _) (only parsing).

  Notation isconv_red_raw leq t1 π1 t2 π2 aux :=
    (aux Reduction t1 π1 t2 π2 _ _ _ _ leq _ I I I) (only parsing).

  Inductive fix_kind :=
  | IndFix
  | CoIndFix.

  Definition mFix k :=
    match k with
    | IndFix => tFix
    | CoIndFix => tCoFix
    end.

  Definition mFix_mfix fk :=
    match fk with
    | IndFix => Fix
    | CoIndFix => CoFix
    end.

  Equations isws_cumul_pb_fix_bodies (fk : fix_kind) (Γ : context) (idx : nat)
    (mfix1 mfix2 : mfixpoint term) (π : stack)
    (h : wtp Γ (mFix fk (mfix1 ++ mfix2) idx) π)
    (mfix1' mfix2' : mfixpoint term) (π' : stack)
    (h' : wtp Γ (mFix fk (mfix1' ++ mfix2') idx) π')
    (hx : conv_stack_ctx Γ π π')
    (h1 : ∥ All2 (fun u v => forall Σ (wfΣ : abstract_env_ext_rel X Σ), Σ ;;; Γ ,,, stack_context π ,,, fix_context_alt (map def_sig mfix1 ++ map def_sig mfix2) ⊢ u.(dbody) = v.(dbody)) mfix1 mfix1' ∥)
    (ha : ∥ All2 (fun u v =>
                    (forall Σ (wfΣ : abstract_env_ext_rel X Σ), Σ ;;; Γ ,,, stack_context π ⊢ u.(dtype) = v.(dtype)) ×
                    (u.(rarg) = v.(rarg)) * eq_binder_annot u.(dname) v.(dname)
           ) (mfix1 ++ mfix2) (mfix1' ++ mfix2') ∥)
    (aux : Aux Term Γ (mFix fk (mfix1 ++ mfix2) idx) π (mFix fk (mfix1' ++ mfix2') idx) π' h')
    : ConversionResult (∥ All2 (fun u v => forall Σ (wfΣ : abstract_env_ext_rel X Σ), Σ ;;; Γ ,,, stack_context π ,,, fix_context_alt (map def_sig mfix1 ++ map def_sig mfix2) ⊢ u.(dbody) = v.(dbody)) mfix2 mfix2' ∥)
    by struct mfix2 :=

  isws_cumul_pb_fix_bodies fk Γ idx mfix1 (u :: mfix2) π h mfix1' (v :: mfix2') π' h' hx h1 ha aux
  with isconv_red_raw Conv
        u.(dbody)
        (mFix_mfix fk (mfix1, def_hole_body u.(dname) u.(dtype) u.(rarg), mfix2) idx :: π)
        v.(dbody)
        (mFix_mfix fk (mfix1', def_hole_body v.(dname) v.(dtype) v.(rarg), mfix2') idx :: π')
        aux
  := {
  | Success h2
    with isws_cumul_pb_fix_bodies fk Γ idx
           (mfix1 ++ [u]) mfix2 π _
           (mfix1' ++ [v]) mfix2' π' _
           hx _ _ (expand aux)
    := {
    | Success h3 := yes ;
    | Error e h'' := no e
    } ;
  | Error e h'' := no e
  } ;

  isws_cumul_pb_fix_bodies fk Γ idx mfix1 [] π h mfix1' [] π' h' hx h1 ha aux := yes ;

  isws_cumul_pb_fix_bodies fk Γ idx mfix1 mfix2 π h mfix1' mfix2' π' h' hx h1 ha aux :=
    False_rect _ _.

  Next Obligation.
    destruct h1 as [h1], ha as [ha].
    apply All2_length in h1 as e1.
    apply All2_length in ha as ea.
    rewrite !app_length in ea.
simpl in ea.
lia.
  Qed.
  Next Obligation.
admit.
Defined.
  Next Obligation.
admit.
Defined.
  Next Obligation.
admit.
Defined.
  Next Obligation.
admit.
Defined.
  Next Obligation.
admit.
Defined.
  Next Obligation.
Admitted.
  Next Obligation.
Admitted.
  Next Obligation.
Admitted.
  Next Obligation.
Admitted.
  Next Obligation.
Admitted.
  Next Obligation.
admit.
Defined.
  Next Obligation.
admit.
  Defined.
  Next Obligation.
admit.
Defined.
