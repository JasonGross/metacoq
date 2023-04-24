From MetaCoq.Utils Require Export bytestring.
From MetaCoq.Utils Require Import utils MCList.
From MetaCoq.Common Require Import MonadBasicAst.
From MetaCoq.PCUIC.utils Require Import PCUICAstUtils.
From MetaCoq.PCUIC Require Import PCUICMonadAst PCUICAst PCUICTyping PCUICSpine PCUICArities PCUICSubstitution.
From MetaCoq.PCUIC.Typing Require Import PCUICWeakeningTyp PCUICWeakeningConfigTyp PCUICWeakeningEnvTyp PCUICClosedTyp.
From MetaCoq.PCUIC.Syntax Require Import PCUICLiftSubst PCUICClosed PCUICInduction PCUICReflect.
From MetaCoq.TemplatePCUIC Require Import PCUICTemplateMonad Loader.
From MetaCoq.SafeChecker Require Import PCUICSafeChecker.
From MetaCoq.Quotation Require Export CommonUtils.
From MetaCoq.Quotation.ToPCUIC Require Export Init.
From MetaCoq.Quotation.ToPCUIC Require Import (hints) Coq.Init.
Require Import Equations.Prop.Classes.
Require Import Coq.Lists.List.
Export TemplateMonad.Common (export, local, global).
Import ListNotations.
Import MCMonadNotation.
Import PCUICEnvironmentReflect.
(*
From MetaCoq.Template Require Import MonadBasicAst MonadAst All utils.
From MetaCoq.Template Require Import Typing utils.bytestring TermEquality ReflectAst Ast Reflect.
From MetaCoq.Lob.Template Require Export QuoteGround.Init.
Export utils.bytestring.
Require Import Coq.Lists.List.
Import ListNotations.

Local Set Primitive Projections.
Local Open Scope bs.
Import MCMonadNotation.
 *)

Local Set Universe Polymorphism.
Local Unset Universe Minimization ToSet.
Local Set Polymorphic Inductive Cumulativity.
(*
Module config.
  Class typing_restriction
    := { checker_flags_constraint : config.checker_flags -> bool
       ; global_env_ext_constraint : global_env_ext -> bool }.
  Definition and_typing_restriction (x y : typing_restriction) : typing_restriction
    := {| checker_flags_constraint cf := x.(checker_flags_constraint) cf && y.(checker_flags_constraint) cf;
         global_env_ext_constraint Σ := x.(global_env_ext_constraint) Σ && y.(global_env_ext_constraint) Σ |}.
  Definition or_typing_restriction (x y : typing_restriction) : typing_restriction
    := {| checker_flags_constraint cf := x.(checker_flags_constraint) cf && y.(checker_flags_constraint) cf;
         global_env_ext_constraint Σ := x.(global_env_ext_constraint) Σ && y.(global_env_ext_constraint) Σ |}.
  Module Export Notations.
    Declare Scope typing_restriction_scope.
    Delimit Scope typing_restriction_scope with typing_restriction.
    Bind Scope typing_restriction_scope with typing_restriction.
    Infix "&&" := and_typing_restriction : typing_restriction_scope.
    Infix "||" := or_typing_restriction : typing_restriction_scope.
  End Notations.
End config.
Export config.Notations.
*)
(* TODO: Right now, quotation / translation always claims constants are monomorphic; if there's eventually support for polymorphic quotation, we may want to not restrict typing to be monomorphic here *)
Class quotation_of_well_typed {cf : config.checker_flags} (Σ : global_env) {T} (t : T) {qT : quotation_of T} {qt : quotation_of t} := typing_quoted_term_of : wf Σ -> (Σ, Monomorphic_ctx) ;;; [] |- qt : qT.
Class ground_quotable_well_typed {cf : config.checker_flags} (Σ : global_env) T {qT : quotation_of T} {quoteT : ground_quotable T} := typing_quote_ground : forall t : T, quotation_of_well_typed Σ t.

Definition typing_quoted_term_of_general
  {cf : config.checker_flags} {Σ : global_env} {T} (t : T) {qT : quotation_of T} {qt : quotation_of t}
  {qty : @quotation_of_well_typed cf Σ T t _ _}
  {cf' : config.checker_flags} {Σ' : global_env} {Γ}
  : @wf cf Σ -> @wf cf' Σ' -> (let _ := cf' in wf_local (Σ', Monomorphic_ctx) Γ) -> extends Σ Σ' -> config.impl cf cf' -> @typing cf' (Σ', Monomorphic_ctx) Γ qt qT.
Proof.
  intros wfΣ wfΣ' wfΓ Hext Hcf.
  specialize (qty wfΣ).
  replace Γ with ([],,,Γ) by now rewrite app_context_nil_l.
  erewrite <- (@lift_closed _ _ qt), <- (@lift_closed _ _ qT).
  { eapply weakening; rewrite ?app_context_nil_l; try eassumption.
    eapply (@weakening_env cf' (Σ, _)); try eassumption.
    all: try now eapply (@weakening_config_wf cf cf'); assumption.
    eapply (@weakening_config cf cf'); assumption. }
  all: change 0 with #|[]:context|.
  all: try (eapply (@subject_closed cf (_, _)); eassumption).
  all: try (eapply (@type_closed cf (_, _)); eassumption).
Qed.

Definition typing_quoted_term_of_general_empty_ctx
  {cf : config.checker_flags} {Σ : global_env} {T} (t : T) {qT : quotation_of T} {qt : quotation_of t}
  {qty : @quotation_of_well_typed cf Σ T t _ _}
  {cf' : config.checker_flags} {Σ' : global_env}
  : @wf cf Σ -> @wf cf' Σ' -> extends Σ Σ' -> config.impl cf cf' -> @typing cf' (Σ', Monomorphic_ctx) [] qt qT.
Proof.
  intros; eapply (@typing_quoted_term_of_general cf Σ T t qT qt qty cf' Σ'); tea.
  constructor.
Qed.

(*
Class quotation_of_well_typed {Pcf : config.typing_restriction} {T} (t : T) {qT : quotation_of T} {qt : quotation_of t} := typing_quoted_term_of : forall cf Σ Γ, config.checker_flags_constraint cf -> config.global_env_ext_constraint Σ -> wf Σ -> wf_local Σ Γ -> Σ ;;; Γ |- qt : qT.
Class ground_quotable_well_typed {Pcf : config.typing_restriction} T {qT : quotation_of T} {quoteT : ground_quotable T} := typing_quote_ground : forall t : T, quotation_of_well_typed t.
*)
Class infer_quotation_of_well_typed (qt : term)
  := { wt_cf : config.checker_flags
     ; wt_Σ : global_env
     ; wt_T : Type
     ; wt_t : wt_T
     ; wt_qT : quotation_of wt_T
     ; wt_qt : quotation_of wt_t := qt
     ; wt_q : @quotation_of_well_typed wt_cf wt_Σ wt_T wt_t _ _ }.
Class infer_type_of (qt : term) := qtype_of : term.
Ltac infer_type_of qt
  := lazymatch (eval hnf in (_ : infer_quotation_of_well_typed qt)) with
     | {| wt_qT := ?qT |} => exact qT
     end.

Inductive dynlist := dnil | dcons {T} (t : T) (tl : dynlist).
Declare Scope dynlist_scope.
Delimit Scope dynlist_scope with dynlist.
Bind Scope dynlist_scope with dynlist.
Infix "::" := dcons : dynlist_scope.
Notation "[ ]" := dnil : dynlist_scope.
Notation "[ x ]" := (dcons x dnil) : dynlist_scope.
Notation "[ x ; y ; .. ; z ]" :=  (dcons x (dcons y .. (dcons z dnil) ..)) : dynlist_scope.

(*
Fixpoint quote_dynlist (d : dynlist) : TemplateMonad (list term)
  := match d with
     | dnil => ret []
     | dcons _ t rest => qt <- tmQuote t;; qts <- quote_dynlist rest;; ret (qt :: qts)
     end.

Definition constraint_for_globals (globals : dynlist) : TemplateMonad (global_env_ext -> bool)
  := qts <- quote_dynlist globals;;
     inds <- monad_map (fun qt => match Init.head qt with
                                  | tInd {| inductive_mind := mind |} _
                                    => ind <- tmQuoteInductive mind;;
                                       (*tmPrint ind;;*)
                                       ret (mind, ind)
                                  | _ => tmPrint ("ensure present not inductive"%bs, qt);; tmFail "ensure present not inductive"%bs
                                  end) qts;;
     ret (fun Σ : global_env_ext
          => List.fold_right andb true (List.map (fun '(mind, ind) => lookup_env Σ.1 mind == Some (InductiveDecl ind)) inds)).
 *)
(* don't use [dynlist] inductive when quoting *)
Definition erase_dynlist (globals : dynlist)
  := Eval cbv [dynlist_ind] in fun P n c => dynlist_ind (fun _ => P) n (fun T t _ r => c T t r) globals.
Definition env_for_globals (globals : forall P : Prop, P -> (forall x : Type, x -> P -> P) -> P) : TemplateMonad global_env_ext
  := qglobals <- tmQuoteRec globals;;
     ret (PCUICProgram.global_env_ext_map_global_env_ext (fst (qglobals:PCUICProgram.pcuic_program))).

Notation ground_quotable_well_typed_using ls T
  := (match ls%dynlist, T return _ with
      | globals, T'
        => ltac:(let T' := (eval cbv delta [T'] in T') in
                 let globals := (eval cbv [erase_dynlist globals] in (erase_dynlist globals)) in
                 run_template_program
                   (env_for_globals globals)
                   (fun Σ => refine (@ground_quotable_well_typed
                                       _ Σ
                                       T' _ _)))
      end)
       (only parsing).
Notation quotation_of_well_typed_using ls t
  := (match ls%dynlist, t return _ with
      | globals, t'
        => ltac:(let t' := (eval cbv delta [t'] in t') in
                 let globals := (eval cbv [erase_dynlist globals] in (erase_dynlist globals)) in
                 run_template_program
                   (env_for_globals globals)
                   (fun Σ => refine (@quotation_of_well_typed
                                       _ Σ
                                       _ t' _ _)))
      end)
       (only parsing).
Notation typing_restriction_for_globals ls
  := (match ls%dynlist return _ with
      | globals
        => ltac:(let globals := (eval cbv [erase_dynlist globals] in (erase_dynlist globals)) in
                 run_template_program
                   (env_for_globals globals)
                   (fun Σ => refine Σ))
      end)
       (only parsing).


Module Export Instances.
  #[export] Existing Instance Build_infer_quotation_of_well_typed.
  #[export] Hint Extern 0 (infer_quotation_of_well_typed ?qt)
  => simple notypeclasses refine (@Build_infer_quotation_of_well_typed qt _ _ _ _ _ _);
     [ .. | typeclasses eauto ]
       : typeclass_instances.
  #[export] Hint Extern 0 (infer_type_of ?qt) => infer_type_of qt : typeclass_instances.
  (* #[export] *)
  Coercion wt_q : infer_quotation_of_well_typed >-> quotation_of_well_typed.
  (*#[export] Instance default_typing_restriction : config.typing_restriction | 1000
    := {| config.checker_flags_constraint cf := true
       ; config.global_env_ext_constraint Σ := true |}.*)
  #[export] Existing Instance typing_quote_ground.
End Instances.

Definition lift_step
  : forall (lift' : nat -> nat -> term -> term) (n k : nat) (t : term), term.
Proof.
  let v := (eval cbv delta [lift] in lift) in
  let liftTy := lazymatch goal with |- ?T -> _ => T end in
  run_template_program
    (lift <- tmQuote v;;
     qliftTy <- tmQuote liftTy;;
     match lift with
     | tFix [b] _
       => tmUnquote
            (tLambda
               {| binder_name := nNamed "lift'"; binder_relevance := Relevant |}
               qliftTy
               b.(dbody))
     | _ => tmPrint lift;; tmFail "bad lift body"
     end)
    (fun v => lazymatch v with
              | {| my_projT2 := ?v |} => exact v
              end).
Defined.

Definition prelift (lift : nat -> nat -> term -> term) (n k : nat) (t : term) : term
  := if match n with 0 => true | _ => false end
     then t
     else lift n k t.
Fixpoint lift' n k t {struct t} := lift_step (prelift lift') n k t.
Definition lift_opt n k t := prelift lift' n k t.

Lemma eq_prelift lift n k t
  : lift n k t = PCUICAst.lift n k t
    -> prelift lift n k t = PCUICAst.lift n k t.
Proof.
  destruct n; cbn; auto.
  rewrite !lift0_id; reflexivity.
Qed.

Lemma eq_lift' n k t : lift' n k t = PCUICAst.lift n k t.
Proof.
  revert n k; induction t using term_forall_list_ind; intros; cbn -[prelift]; try reflexivity.
  all: f_equal.
  all: repeat first [ progress intros
                    | reflexivity
                    | solve [ eauto ]
                    | rewrite eq_prelift
                    | apply map_ext_in_iff
                    | apply map_def_eq_spec
                    | apply map_predicate_k_eq_spec
                    | apply map_branch_k_eq_spec
                    | progress cbv [shiftf] ].
  all: repeat first [ progress hnf in *
                    | solve [ eauto ]
                    | progress rdest
                    | progress sq
                    | match goal with
                      | [ H : All _ _ |- _ ] => pose proof (fun X H' => @All_In _ _ _ X H' H); clear H
                      | [ H : forall X, In X ?v -> _ |- _ ]
                        => exactly_once (idtac; multimatch goal with
                                                | [ H' : In _ v |- _ ]
                                                  => specialize (H _ H')
                                                end)
                      end ].
Qed.

Lemma eq_lift_opt n k t : lift_opt n k t = PCUICAst.lift n k t.
Proof.
  cbv [lift_opt]; rewrite eq_prelift; rewrite ?eq_lift'; reflexivity.
Qed.

Definition subst_step (lift' : nat -> nat -> term -> term)
  : forall (subst' : list term -> nat -> term -> term) (s : list term) (k : nat) (u : term), term.
Proof.
  let v := (eval cbv delta [subst] in subst) in
  let v := lazymatch (eval pattern (@PCUICAst.lift) in v) with
           | ?f _ => f
           end in
  let v := (eval cbv beta in (v lift')) in
  let substTy := lazymatch goal with |- ?T -> _ => T end in
  run_template_program
    (subst <- tmQuote v;;
     qsubstTy <- tmQuote substTy;;
     match subst with
     | tFix [b] _
       => tmUnquote
            (tLambda
               {| binder_name := nNamed "subst'"; binder_relevance := Relevant |}
               qsubstTy
               b.(dbody))
     | _ => tmPrint subst;; tmFail "bad subst body"
     end)
    (fun v => lazymatch v with
              | {| my_projT2 := ?v |} => exact v
              end).
Defined.

Definition presubst (subst : list term -> nat -> term -> term) (s : list term) (k : nat) (u : term) : term
  := if match s with [] => true | _ => false end
     then u
     else subst s k u.

Fixpoint subst' s k u {struct u} := subst_step lift_opt (presubst subst') s k u.
Definition subst_opt s k u := presubst subst' s k u.
Fixpoint subst'_nolift s k u {struct u} := subst_step (fun _ _ v => v) (presubst subst'_nolift) s k u.
Definition subst_nolift_opt s k u := presubst subst'_nolift s k u.

Lemma eq_presubst subst s k u
  : subst s k u = PCUICAst.subst s k u
    -> presubst subst s k u = PCUICAst.subst s k u.
Proof.
  destruct s; cbn; auto.
  rewrite !subst_empty; reflexivity.
Qed.

Lemma eq_subst' s k u : subst' s k u = PCUICAst.subst s k u.
Proof.
  revert s k; induction u using term_forall_list_ind; intros; cbn -[presubst]; try reflexivity.
  all: repeat destruct ?; subst.
  all: rewrite ?eq_lift_opt.
  all: f_equal.
  all: repeat first [ progress intros
                    | reflexivity
                    | solve [ eauto ]
                    | rewrite eq_presubst
                    | apply map_ext_in_iff
                    | apply map_def_eq_spec
                    | apply map_predicate_k_eq_spec
                    | apply map_branch_k_eq_spec
                    | progress cbv [shiftf] ].
  all: repeat first [ progress hnf in *
                    | solve [ eauto ]
                    | progress rdest
                    | progress sq
                    | match goal with
                      | [ H : All _ _ |- _ ] => pose proof (fun X H' => @All_In _ _ _ X H' H); clear H
                      | [ H : forall X, In X ?v -> _ |- _ ]
                        => exactly_once (idtac; multimatch goal with
                                                | [ H' : In _ v |- _ ]
                                                  => specialize (H _ H')
                                                end)
                      end ].
Qed.

Lemma eq_subst_opt s k u : subst_opt s k u = PCUICAst.subst s k u.
Proof.
  cbv [subst_opt]; rewrite eq_presubst; rewrite ?eq_subst'; reflexivity.
Qed.

Lemma eq_subst'_nolift s k u
  (Hs : Forall (fun t => closed t) s)
  : subst'_nolift s k u = PCUICAst.subst s k u.
Proof.
  revert k; induction u using term_forall_list_ind; intros; cbn -[presubst]; try reflexivity.
  all: repeat destruct ?; subst.
  all: rewrite ?lift_closed by now eapply Forall_forall in Hs; try eapply nth_error_In; tea.
  all: f_equal.
  all: repeat first [ progress intros
                    | reflexivity
                    | solve [ eauto ]
                    | rewrite eq_presubst
                    | apply map_ext_in_iff
                    | apply map_def_eq_spec
                    | apply map_predicate_k_eq_spec
                    | apply map_branch_k_eq_spec
                    | progress cbv [shiftf] ].
  all: repeat first [ progress hnf in *
                    | solve [ eauto ]
                    | progress rdest
                    | progress sq
                    | match goal with
                      | [ H : All _ _ |- _ ] => pose proof (fun X H' => @All_In _ _ _ X H' H); clear H
                      | [ H : forall X, In X ?v -> _ |- _ ]
                        => exactly_once (idtac; multimatch goal with
                                                | [ H' : In _ v |- _ ]
                                                  => specialize (H _ H')
                                                end)
                      end ].
Qed.

Lemma eq_subst_nolift_opt s k u
  (Hs : Forall (fun t : term => closed t) s)
  : subst_nolift_opt s k u = PCUICAst.subst s k u.
Proof.
  cbv [subst_nolift_opt]; rewrite eq_presubst; rewrite ?eq_subst'_nolift; tea; reflexivity.
Qed.

(*
Definition subst_nolift : list term -> nat -> term -> term.
Proof.
  let v := (eval cbv delta [subst] in subst) in
  let v := lazymatch (eval pattern (@lift) in v) with
           | ?f _ => f
           end in
  let v := (eval cbv beta in (v (fun _ _ x => x))) in
  exact v.
Defined.

Lemma closed_subst_nolift {cf : config.checker_flags} {Σ}
  (s : list term)
  (Γ' : list term)
  (Hs : All2 (fun t T => Σ ;;; [] |- t : T) s Γ')
  (wfΣ : wf Σ)
  : forall u k, subst s k u = subst_nolift s k u.
Proof.
  induction u using term_forall_list_ind; intros.
  all: cbn [subst subst_nolift].
  all: f_equal.
  all: repeat
         unshelve
         first [ progress intros
               | progress hnf in *
               | progress destruct_head'_prod
               | reflexivity
               | solve [ eauto ]
               | progress destruct ?
               | apply lift_closed
               | apply map_def_eq_spec
               | apply map_predicate_k_eq_spec
               | apply map_branch_k_eq_spec
               | now change 0 with #|[]:context|; eapply subject_closed
               | match goal with
                 | [ H : All _ ?x |- context[map _ ?x] ] => induction H; cbn [map]; congruence
                 | [ H : All _ ?x |- map (map_def (subst _ _) (subst _ ?k')) ?x = _ ]
                   => generalize k'; intro; induction H; cbn [map]; f_equal; try congruence
                 | [ H : nth_error ?s _ = Some _, H' : All2 _ ?s _ |- closedn _ _ = true ]
                   => eapply All2_nth_error_Some in H; [ | eassumption ]; destruct H as [? [_ ?]]
                 | [ H : All _ ?x |- context[map _ ?x] ] => induction H; cbn [map]; f_equal; try congruence
                 end ].
Qed.
 *)
Lemma closed_substitution {cf : config.checker_flags} {Σ : global_env_ext}
  (s : list term)
  (Γ' : list term)
  (t T : term)
  (wfΣ : wf Σ)
  (Hs : All2_fold (fun s0 Γ'0 t T => Σ ;;; [] |- t : subst0 s0 T) s Γ')
  (Γ'' := List.map (fun ty => {| BasicAst.decl_name := {| binder_name := nAnon; binder_relevance := Relevant |} ; BasicAst.decl_body := None ; BasicAst.decl_type := ty |}) Γ')
  (Ht : Σ ;;; Γ'' |- t : T)
  : Σ ;;; [] |- subst0 s t : subst0 s T.
Proof.
  apply (@substitution cf Σ wfΣ [] Γ'' s [] t T);
    try (cbn; rewrite app_context_nil_l; assumption).
  clear Ht t T.
  subst Γ''; induction Hs; cbn [List.map]; constructor; trivial.
  (*{ rewrite subst_closedn; [ assumption | ].
    change 0 with #|[]:context|.
    eapply @type_closed; eassumption. }*)
Qed.
Notation subst0_opt t := (subst_opt t 0).
Notation subst0_nolift_opt t := (subst_nolift_opt t 0).
Lemma closed_substitution_opt {cf : config.checker_flags} {Σ : global_env_ext}
  (s : list term)
  (Γ' : list term)
  (t T : term)
  (wfΣ : wf Σ)
  (Hs : All2_fold (fun s0 Γ'0 t T => Σ ;;; [] |- t : subst0_nolift_opt s0 T) s Γ')
  (Γ'' := List.map (fun ty => {| BasicAst.decl_name := {| binder_name := nAnon; binder_relevance := Relevant |} ; BasicAst.decl_body := None ; BasicAst.decl_type := ty |}) Γ')
  (Ht : Σ ;;; Γ'' |- t : T)
  : Σ ;;; [] |- subst0_nolift_opt s t : subst0_nolift_opt s T.
Proof.
  assert (H : Forall (fun t0 : term => closed t0) s).
  { clear -Hs wfΣ; induction Hs; constructor; eauto.
    change 0 with #|[]:context|.
    eapply @subject_closed; tea. }
  rewrite !eq_subst_nolift_opt; tea.
  eapply closed_substitution; tea.
  clear -Hs H.
  toAll.
  induction Hs; constructor; auto.
  all: match goal with H : All _ (_ :: _) |- _ => inversion H; subst; clear H end.
  all: rewrite eq_subst_nolift_opt in *; tea; try toAll; eauto.
Qed.

Fixpoint All2_fold_cps {A} (P : list A -> list A -> A -> A -> Type) (Q : Type) (l1 l2 : list A) {struct l1}
  := match l1, l2 with
     | [], [] => Q
     | [], _ | _, [] => True
     | x :: xs, y :: ys
       => P xs ys x y -> All2_fold_cps P Q xs ys
     end.

#[local] Hint Constructors All2_fold : core.
Lemma All2_fold_cps_id {A P Q l1 l2}
  : @All2_fold_cps A P Q l1 l2 <~> (All2_fold P l1 l2 -> Q).
Proof.
  split; revert l2; induction l1 as [|?? IH], l2 as [|? l2]; cbn.
  all: intros.
  all: try match goal with H : All2_fold _ _ _ |- _ => inversion H; subst end.
  all: intuition eauto.
Qed.

Lemma closed_substitution_cps {cf : config.checker_flags} {Σ : global_env_ext}
  (s : list term)
  (Γ' : list term)
  (t T : term)
  (wfΣ : wf Σ)
  (Γ'' := List.map (fun ty => {| BasicAst.decl_name := {| binder_name := nAnon; binder_relevance := Relevant |} ; BasicAst.decl_body := None ; BasicAst.decl_type := ty |}) Γ')
  : All2_fold_cps
      (fun s0 Γ'0 t T => Σ ;;; [] |- t : subst0_nolift_opt s0 T)
      ((Σ ;;; Γ'' |- t : T) -> (Σ ;;; [] |- subst0_nolift_opt s t : subst0_nolift_opt s T))
      s Γ'.
Proof.
  apply All2_fold_cps_id; intros; eapply closed_substitution_opt; eassumption.
Qed.

(*Check All2_fold.*)
(*
Lemma closed_substitution_nolift {cf : config.checker_flags} {Σ}
  (s : list term)
  (Γ' : list term)
  (t T : term)
  (Hs : All2 (fun t T => Σ ;;; [] |- t : T) s Γ')
  (wfΣ : wf Σ)
  (Γ'' := List.map (fun ty => {| BasicAst.decl_name := {| binder_name := nAnon; binder_relevance := Relevant |} ; BasicAst.decl_body := None ; BasicAst.decl_type := ty |}) Γ')
  (Ht : Σ ;;; Γ'' |- t : T)
  : Σ ;;; [] |- subst_nolift s 0 t : subst_nolift s 0 T.
Proof.
  erewrite <- !closed_subst_nolift by eassumption.
  now eapply @closed_substitution.
Qed.
*)

(* generates new version of [t * s], where [s] holds (de Bruijn index, quoted term, unquoted term, unquoted type) *)
Definition precollect_constants_k
  (collect_constants_k : nat -> term -> StateT (list (nat * term * term * term)) TemplateMonad term)
  (collect_constants_k_from_fix : nat -> term -> StateT (list (nat * term * term * term)) TemplateMonad term)
  (offset : nat) (t : term)
  : StateT (list (nat * term * term * term)) TemplateMonad term
  := qt <- State.lift (tmQuote t);;
     let '(qh, qargs) := decompose_app qt in
     rv <- match qh, qargs with
           | tRel _, _
           | tVar _, _
           | tEvar _ _, _
           | tConst _ _, _
             => s <- State.get;;
                match find (fun '(i, qv, v, vT) => qt == qv) s with
                | Some (i, qv, v, vT)
                  => i' <- State.lift (tmEval cbv (offset + i));;
                     ret (Some (tRel i'))
                | None
                  => vT <- State.lift (let tc := tmInferInstance None (infer_type_of t) in
                                       inst <- tc;;
                                       match inst with
                                       | my_Some vT => ret vT
                                       | my_None
                                         => tmPrint (t, qt, qh, qargs);;
                                            tmPrint tc;;
                                            tmFail "precollect_constants_k: could not infer instance"
                                       end);;
                     _ <- collect_constants_k_from_fix 0 vT;;
                     s <- State.get;;
                     i <- State.lift (tmEval cbv (List.length s));;
                     i' <- State.lift (tmEval cbv (offset + i));;
                     State.set ((i, qt, t, vT) :: s);;
                     ret (Some (tRel i'))
                end
           | tApp _ _, _
             => State.lift (tmPrint qt;; tmFail "decompose_app should not return tApp")
           | tConstruct _ _ _, _
             => ret None
           | _, _
             => State.lift (tmPrint qt;; tmPrint (qh, qargs);; tmFail "collect_constants: requires constructor tree or tRel, tVar, tEvar, tConst")
           end;;
     match rv with
     | Some rv => ret rv
     | None
       => collect_constants_k offset t
     end.


Fixpoint collect_constants_k'
  (collect_constants_k_from_fix : nat -> term -> StateT _ TemplateMonad term)
  (offset : nat) (t : term)
  : StateT _ TemplateMonad term
  := let collect_constants_k := precollect_constants_k (collect_constants_k' collect_constants_k_from_fix) collect_constants_k_from_fix in
     match t with
     | tRel _
     | tVar _
     | tSort _
     | tProj _ _
     | tPrim _
     | tConst _ _
     | tInd _ _
     | tConstruct _ _ _
       => ret t
     | tEvar n l
       => l <- monad_map (collect_constants_k offset) l;;
          ret (tEvar n l)
     | tProd na A B
       => A <- collect_constants_k offset A;;
          B <- collect_constants_k (S offset) B;;
          ret (tProd na A B)
     | tLambda na A t
       => A <- collect_constants_k offset A;;
          t <- collect_constants_k (S offset) t;;
          ret (tLambda na A t)
     | tLetIn na b B t
       => b <- collect_constants_k offset b;;
          B <- collect_constants_k offset B;;
          t <- collect_constants_k (S offset) t;;
          ret (tLetIn na b B t)
     | tApp u v
       => u <- collect_constants_k offset u;;
          v <- collect_constants_k offset v;;
          ret (tApp u v)
     | tCase indn p c brs
       => p <- monad_map_predicate_k ret collect_constants_k offset p;;
          c <- collect_constants_k offset c;;
          brs <- monad_map_branches_k collect_constants_k ret offset brs;;
          ret (tCase indn p c brs)
     | tFix mfix idx
       => mfix <- monad_map (monad_map_def (collect_constants_k offset) (collect_constants_k offset)) mfix;;
          ret (tFix mfix idx)
     | tCoFix mfix idx
       => mfix <- monad_map (monad_map_def (collect_constants_k offset) (collect_constants_k offset)) mfix;;
          ret (tCoFix mfix idx)
     end.

Definition collect_constants_k : nat -> term -> StateT (list (nat * term * term * term)) TemplateMonad term
  := fun n t st
     => tmFix (fun collect_constants_k_from_fix '(n, t, st)
               => let collect_constants_k_from_fix n t st := collect_constants_k_from_fix (n, t, st) in
                  precollect_constants_k (collect_constants_k' collect_constants_k_from_fix) collect_constants_k_from_fix n t st)
              (n, t, st).
Notation collect_constants := (collect_constants_k 0).

Definition List_map_alt {A} {B} := Eval cbv in @List.map A B.
Definition List_rev_alt {A} := Eval cbv in @rev A.

Fixpoint redo_types_and_indices' (ls : list (nat * term * term * term))
  : StateT _ TemplateMonad (list (nat * term * term * term))
  := match ls with
     | [] => ret []
     | (_, qv, v, vT) :: ls
       => State.set ls;;
          ls <- redo_types_and_indices' ls;;
          State.set ls;;
          vT <- collect_constants_k 0 vT;;
          ls <- monad_map (fun '(i, qt, t, vT) => ret (S i, qt, t, vT)) ls;;
          State.set ls;;
          ret ((0, qv, v, vT) :: ls)
     end.

Definition run_drop_state {S M T} {TM : Monad M} (p : StateT S M T) (st : S) : M T
  := '(v, st) <- p st;;
     ret v.

Definition redo_types_and_indices (ls : list (nat * term * term * term)) : TemplateMonad (list (nat * term * term * term))
  := run_drop_state (redo_types_and_indices' ls) ls.

Definition collect_constants_build_substituition (t : term) (T : term)
  : TemplateMonad (term (* t *) * term (* T *) * list term (* s *) * list term (* Γ *) )
  := qmap <- tmQuoteToGlobalReference (@List_map_alt);;
     qmap <- match kername_of_global_reference qmap with
             | Some kn => ret kn
             | None => tmPrint qmap;; tmFail "no List_map_alt"
             end;;
     qrev <- tmQuoteToGlobalReference (@List_rev_alt);;
     qrev <- match kername_of_global_reference qrev with
             | Some kn => ret kn
             | None => tmPrint qrev;; tmFail "no List_rev_alt"
             end;;
     '(T', st) <- collect_constants T [];;
     '(t', st) <- collect_constants t st;;
     st <- redo_types_and_indices st;;
     T' <- run_drop_state (collect_constants T) st;;
     t' <- run_drop_state (collect_constants t) st;;
     T' <- tmEval cbv T';;
     t' <- tmEval cbv t';;
     st <- tmEval hnf st;;
     tmPrint st;;
     s <- tmEval (unfold qmap) (List_map_alt (fun '(i, qv, v, vT) => v) st);;
     Γ <- tmEval (unfold qmap) (List_map_alt (fun '(i, qv, v, vT) => vT) st);;
     ret (t', T', s, Γ).
  (*
  (cf : config.checker_flags) (Σ : global_env_ext)
closed_substitution {cf : config.checker_flags} {Σ}
  (s : list term)
  (Γ' : list term)
  (t T : term)
  (Hs : All2_fold (fun s0 Γ'0 t T => Σ ;;; [] |- t : subst0 s0 T) s Γ')
  (wfΣ : wf Σ)
  (Γ'' := List.map (fun ty => {| BasicAst.decl_name := {| binder_name := nAnon; binder_relevance := Relevant |} ; BasicAst.decl_body := None ; BasicAst.decl_type := ty |}) Γ')
  (Ht : Σ ;;; Γ'' |- t : T)
  : Σ ;;; [] |- subst0 s t : subst0 s T.
Proof.
*)
(*

Definition replace_typing_for_safechecker (cf : config.checker_flags) Σ t T
  : TemplateMonad (@typing cf Σ [] t T).
  Print infer_quotation_of_well_typed.
  refine (let collect_all_constants := (T' <- collect_constants T;;
                                        t' <- collect_constants t;;
                                        ret (t', T')) in
          '((t', T'), Γ') <- collect_all_constants [];;
          let Γ' := map (fun '(_, _, t) => t) Γ' in
          tys <- monad_map
                   (fun t
                    => let tc := infer_quotation_of_well_typed t in
                       inst <- tmInferInstance None tc;;
                       match inst with
                       | my_Some v => ret v
                       | my_None => tmPrint tc;; tmFail "could not find instance"
                       end)
                   Γ';;
          _).

  infer_quotation_of_well_typed
 *)

#[export] Instance well_typed_ground_quotable_of_bp
  {b P} (H : b = true -> P)
  {qH : quotation_of H} (H_for_safety : P -> b = true)
  {qP : quotation_of P}
  {cfH cfP : config.checker_flags} {ΣH ΣP}
  {qtyH : quotation_of_well_typed (cf:=cfH) ΣH H} {qtyP : quotation_of_well_typed (cf:=cfP) ΣP P}
  (Σ0 := typing_restriction_for_globals [bool; @eq bool])
  (Σ := merge_global_envs Σ0 (merge_global_envs ΣH ΣP))
  {Hc : Is_true (compatibleb ΣH ΣP && compatibleb Σ0 (merge_global_envs ΣH ΣP))}
  (HwfP : @wf cfP ΣP)
  (HwfH : @wf cfH ΣH)
  : @ground_quotable_well_typed (config.union_checker_flags cfH cfP) Σ _ qP (@ground_quotable_of_bp b P H qH H_for_safety).
Proof.
  intros t wfΣ.
  apply Is_true_eq_true in Hc.
  rewrite !Bool.andb_true_iff in Hc.
  destruct_head'_and.
  cbv [PCUICProgram.global_env_ext_map_global_env_ext] in *.
  cbn [PCUICProgram.trans_env_env fst] in *.
  cbv [quote_ground ground_quotable_of_bp Init.quote_bool] in *.
  specialize (H_for_safety t); subst.
  lazymatch goal with
  | [ |- @typing ?cf ?Σ ?Γ ?t ?T ]
    => let H := fresh "H'" in
       run_template_program
         (collect_constants_build_substituition t T)
         (fun v
          => lazymatch v with
             | (?t', ?T', ?s', ?Γ')
               => pose proof (@closed_substitution_cps cf Σ s' Γ' t' T') as H;
                  cbv [All2_fold_cps] in H
             | ?v => fail 0 "invalid collect_constants_build_substituition ret" v
             end)
  end.
  pose proof (@extends_strictly_on_decls_l_merge). (* XXX FIXME *)
  simple apply H'; tea.
  all: cbv [subst_nolift_opt presubst subst'_nolift subst_step Nat.sub List.length nth_error Nat.leb].
  all: try match goal with
         | [ |- @typing ?cf (?Σ, Monomorphic_ctx) [] ?t ?T ]
           => notypeclasses refine (@typing_quoted_term_of_general_empty_ctx _ _ _ _ T t _ cf Σ _ _ _ _);
              [ typeclasses eauto | .. ]
         end.
  all: subst Σ.
  all: repeat match goal with
         | [ |- extends ?x ?x ] => apply extends_refl
         | [ |- extends ?x (merge_global_envs ?y ?z) ]
           => lazymatch z with
              | context[x] => transitivity z; [ | apply extends_r_merge ]
              | _
                => lazymatch y with
                   | x => try exact _
                   | context[x] => transitivity y; [ | try exact _ ]
                   | _ => idtac
                   end
              end
         | [ |- is_true (config.impl ?x ?x) ]
           => apply config.impl_refl
         | [ |- is_true (config.impl ?x (config.union_checker_flags ?y ?z)) ]
           => lazymatch z with
              | context[x]
                => apply (@config.impl_trans x z (config.union_checker_flags y z));
                   [ | apply config.union_checker_flags_spec ]
              | _
                => lazymatch y with
                   | context[x]
                     => apply (@config.impl_trans x y (config.union_checker_flags y z));
                        [ | apply config.union_checker_flags_spec ]
                   | _ => idtac
                   end
              end
         end.
  all: lazymatch goal with
       | [ |- wf _ ] => try assumption
       | [ H : context[compatibleb ?x ?y] |- compatible ?x ?y ]
         => destruct (@compatibleP x y); [ assumption | clear -H; try congruence ]
       | _ => idtac
       end.
  pose (@typecheck_program).
     EnvCheck_X_env_ext_type X_impl
       (∑ A : term,
          {X : X_env_ext_type X_impl
          | ∥ PCUICWfEnv.abstract_env_ext_rel X (p.1, φ)
              × wf_ext (p.1, φ) × BDTyping.infering (p.1, φ) [] p.2 A ∥})

  let cf := match goal with |- @typing ?cf _ _ _ _ => cf end in
  eapply (@weakening_env cf Σ0); tea.
  all: try eapply (@weakening_config_wf config.strictest_checker_flags).
  all: try eapply (@weakening_config config.strictest_checker_flags).
  all: try apply config.strictest_checker_flags_strictest.
  4: transitivity Σ0; try exact _; try apply extends_refl.
  all: try apply wf_ext_wf.

  2: { vm_compute.

            Check typecheck_program.
       4: { exact wfΣ.

  Set Printing All.
Search config.impl config.union_checker_flags.

  Search compatible compatibleb.
  2: apply extends_refl.
  2: etransitivity
  Search extends merge_global_envs.
  2: apply extends_m
  all: try assumption.
  all: subst
  all: lazymatch goal iwth
  Set Printing Implicit.
  exact _.
  end.
  end.
  run_template_program p (fun v => pose v as v').
  Lemma closed_substitution_cps {cf : config.checker_flags} {Σ : global_env_ext}
  (s : list term)
  (Γ' : list term)
  (t T : term)
  (wfΣ : wf Σ)


  closed_substitution_nolift {cf : config.checker_flags} {Σ}
  (s : list term)
  (Γ' : list term)
  (t T : term)
  (Hs : All2 (fun t T => Σ ;;; [] |- t : T) s Γ')
  (wfΣ : wf Σ)
  (Γ'' := List.map (fun ty => {| BasicAst.decl_name := {| binder_name := nAnon; binder_relevance := Relevant |} ; BasicAst.decl_body := None ; BasicAst.decl_type := ty |}) Γ')
  (Ht : Σ ;;; Γ'' |- t : T)
  : Σ ;;; [] |- subst_nolift s 0 t : subst_nolift s 0 T.
Proof.
  erewrite <- !closed_subst_nolift by eassumption.
  now eapply @closed_substitution.
Qed.
  cbn in p0.
    => run_template_program (collect_constants t []) (fun v => pose v)
  end.

  Search typing subst.
  Set Printing Implicit.
  Print context_decl.
  Print BasicAst.context_decl.
  Print aname.
  Print binder_annot.
  Check @substitution.
  epose (@substitution cf Σ Hwf []
           [{| BasicAst.decl_name := {| binder_name := nAnon; binder_relevance := Relevant |} ; BasicAst.decl_body := None ; BasicAst.decl_type := ltac:(lazymatch type of qtyH with @quotation_of_well_typed _ _ _ ?T _ => exact T end) |};
            {| BasicAst.decl_name := {| binder_name := nAnon; binder_relevance := Relevant |} ; BasicAst.decl_body := None ; BasicAst.decl_type := ltac:(lazymatch type of qtyP with @quotation_of_well_typed _ _ _ ?T _ => exact T end) |}] [qH; qP] []
        (tApp (tRel 0)
       (tApp
          (tApp
             (tConstruct
                {|
                  inductive_mind := (MPfile ["Logic"; "Init"; "Coq"], "eq");
                  inductive_ind := 0
                |} 0 [])
             (tInd
                {|
                  inductive_mind := (MPfile ["Datatypes"; "Init"; "Coq"], "bool");
                  inductive_ind := 0
                |} []))
          (tConstruct
             {|
               inductive_mind := (MPfile ["Datatypes"; "Init"; "Coq"], "bool");
               inductive_ind := 0
             |} 0 [])))
        (tRel 1)
        ) as v.
  clearbody v.
  cbn in v.
  rewrite !lift_closed in v.
  cbv [subst_context] in v.
  cbv [fold_context_k] in v.
  cbn in v.
  apply v.
  { constructor.
    constructor.
    constructor.
    all: rewrite !subst_closedn.
    3: apply qtyH.
    1:apply qtyP.
    all: try assumption.
    all: try solve [ constructor ].
    change (closedn 0) with (closedn #|[]:context|).
    eapply type_closed.
    eapply qtyH.
    all: try eassumption.
    now constructor. }
    apply closedn_
            eapply
    3: { move qtyH at bottom.
         hnf in qtyH.
         Unset Printing Implicit.
    2: apply qtyH.
    all: cbv [subst0]; cbn.
    2: {
  Unset Printing Implicit.
  Print aname.
  Check {| binder_name := nAnon; binder_relevance := Relevant |} : aname.
  Check nAnon.
  Search closedn lift.
  Print lift0.
  all: repeat
         repeat first [ assumption
                    | now constructor
                    | progress cbv [subst1] in *
                    | rewrite subst_closedn
                    | progress cbn [List.app ind_type]
                    | progress cbn [subst_instance subst_instance_constr subst_instance_univ]
                    | progress cbn [type_of_constructor]
                    | progress cbv [PCUICLookup.declared_minductive_gen]
                    | match goal with
                      | [ |- _;;;_ |- tApp _ _ : _ ] => eapply type_App
                      | [ |- _;;;_ |- tInd _ _ : _ ] => eapply type_Ind
                      | [ |- _;;;_ |- tConstruct _ _ _ : _ ] => eapply type_Construct
                      | [ H : @quotation_of_well_typed _ _ _ _ ?qP  |- _;;;_ |- ?qP : _ ]
                        => (idtac + eapply type_Cumul); [ eapply H | .. ]
                      | [ H : @quotation_of_well_typed _ _ _ _ ?qP  |- is_true (closedn 0 ?qP) ]
                        => eapply @subject_closed with (Γ:=[]); [ | eapply H ]; tea
                      | [ |- wf_local _ [] ] => constructor
                      | [ |- wf_local _ (_ ,, _) ] => constructor
                      | [ |- _;;;_ |- tProd _ _ _ : _ ] => eapply type_Prod
                      | [ |- _;;;_ |- tSort _ : _ ] => eapply type_Sort
                      | [ |- lift_typing _ _ _ _ _ ] => hnf; try eexists
                      | [ |- context[tApp ?f ?x] ]
                        => change (tApp f x) with (mkApps f [x])
                      | [ |- context[mkApps (mkApps ?f ?x) ?y] ]
                        => change (mkApps (mkApps f x) y) with (mkApps f (x ++ y))
                      | [ |- _;;;_ |- mkApps _ _ : _ ]
                        => eapply type_mkApps
                      | [ |- PCUICArities.typing_spine _ _ _ _ _ ]
                        => econstructor
                      | [ |- declared_inductive _ _ _ _ ] => eapply declared_inductive_from_gen; constructor; hnf
                      | [ |- declared_constructor _ _ _ _ _ ] => eapply declared_constructor_from_gen; repeat apply conj
                      | [ |- isType _ _ (tProd _ _ _) ] => apply isType_tProd; split
                      | [ |- isType _ _ (tSort _) ] => apply isType_Sort
                      | [ |- _ = _ ] => eassumption
                      | [ |- _;;;_ |- tSort _ <=s tSort _ ] => apply cumul_Sort
                      end ].
  all: lazymatch goal with
       | [ |- isType _ _ _ ] => cbn; econstructor
       | [ |- wf_universe _ _ ] => idtac
       | _ => cbn
       end.
  all: repeat
         repeat first [ assumption
                      | reflexivity
                    | progress cbv [subst1] in *
                    | rewrite subst_closedn
                    | progress cbn [List.app ind_type]
                    | progress cbn [subst_instance subst_instance_constr subst_instance_univ]
                    | progress cbn [type_of_constructor]
                    | progress cbv [PCUICLookup.declared_minductive_gen]
                    | match goal with
                      | [ |- context[tApp ?f ?x] ]
                        => change (tApp f x) with (mkApps f [x])
                      | [ |- context[mkApps (mkApps ?f ?x) ?y] ]
                        => change (mkApps (mkApps f x) y) with (mkApps f (x ++ y))
                      | [ |- _;;;_ |- mkApps _ _ : _ ]
                        => eapply type_mkApps
                      | [ |- _;;;_ |- tInd _ _ : _ ] => eapply type_Ind
                      | [ |- _;;;_ |- tConstruct _ _ _ : _ ] => eapply type_Construct
                      | [ |- _;;;_ |- tRel _ : _ ] => (idtac + eapply type_Cumul); [ eapply type_Rel | .. ]
                      | [ H : @quotation_of_well_typed _ _ _ _ ?qP  |- _;;;_ |- ?qP : _ ]
                        => (idtac + eapply type_Cumul); [ eapply H | .. ]
                      | [ H : @quotation_of_well_typed _ _ _ _ ?qP  |- is_true (closedn 0 ?qP) ]
                        => eapply @subject_closed with (Γ:=[]); [ | eapply H ]; tea
                      | [ |- wf_local _ [] ] => constructor
                      | [ |- wf_local _ (_ ,, _) ] => constructor
                      | [ |- _;;;_ |- tProd _ _ _ : _ ] => eapply type_Prod
                      | [ |- _;;;_ |- tSort _ : _ ] => eapply type_Sort
                      | [ |- lift_typing _ _ _ _ _ ] => hnf; try eexists
                      | [ |- PCUICArities.typing_spine _ _ _ _ _ ]
                        => econstructor
                      | [ |- declared_inductive _ _ _ _ ] => eapply declared_inductive_from_gen; constructor; hnf
                      | [ |- declared_constructor _ _ _ _ _ ] => eapply declared_constructor_from_gen; repeat apply conj
                      | [ |- isType _ _ (tProd _ _ _) ] => apply isType_tProd; split
                      | [ |- isType _ _ (tSort _) ] => apply isType_Sort
                      | [ |- _ = _ ] => eassumption
                      | [ |- _;;;_ |- tSort _ <=s tSort _ ] => apply cumul_Sort
                      end ].

  all: lazymatch goal with
       | [ |- isType _ _ _ ] => cbn; econstructor
       | [ |- wf_universe _ _ ] => idtac
       | _ => cbn
       end.
  all: repeat
         repeat first [ assumption
                      | reflexivity
                    | progress cbv [subst1] in *
                    | rewrite subst_closedn
                    | progress cbn [List.app ind_type]
                    | progress cbn [subst_instance subst_instance_constr subst_instance_univ]
                      | progress cbn [type_of_constructor]
                      | progress cbn [lift0 decl_type vass]
                    | progress cbv [PCUICLookup.declared_minductive_gen]
                    | match goal with
                      | [ |- context[tApp ?f ?x] ]
                        => change (tApp f x) with (mkApps f [x])
                      | [ |- context[mkApps (mkApps ?f ?x) ?y] ]
                        => change (mkApps (mkApps f x) y) with (mkApps f (x ++ y))
                      | [ |- _;;;_ |- mkApps _ _ : _ ]
                        => eapply type_mkApps
                      | [ |- _;;;_ |- tInd _ _ : _ ] => (idtac + eapply type_Cumul); [ eapply type_Ind | .. ]
                      | [ |- _;;;_ |- tConstruct _ _ _ : _ ] => eapply type_Construct
                      | [ |- _;;;_ |- tRel _ : _ ] => (idtac + eapply type_Cumul); [ eapply type_Rel | .. ]
                      | [ H : @quotation_of_well_typed _ _ _ _ ?qP  |- _;;;_ |- ?qP : _ ]
                        => (idtac + eapply type_Cumul); [ eapply H | .. ]
                      | [ H : @quotation_of_well_typed _ _ _ _ ?qP  |- is_true (closedn 0 ?qP) ]
                        => eapply @subject_closed with (Γ:=[]); [ | eapply H ]; tea
                      | [ |- wf_local _ [] ] => constructor
                      | [ |- wf_local _ (_ ,, _) ] => constructor
                      | [ |- _;;;_ |- tProd _ _ _ : _ ] => eapply type_Prod
                      | [ |- _;;;_ |- tSort _ : _ ] => eapply type_Sort
                      | [ |- lift_typing _ _ _ _ _ ] => hnf; try eexists
                      | [ |- PCUICArities.typing_spine _ _ _ _ _ ]
                        => econstructor
                      | [ |- declared_inductive _ _ _ _ ] => eapply declared_inductive_from_gen; constructor; hnf
                      | [ |- declared_constructor _ _ _ _ _ ] => eapply declared_constructor_from_gen; repeat apply conj
                      | [ |- isType _ _ (tProd _ _ _) ] => apply isType_tProd; split
                      | [ |- isType _ _ (tSort _) ] => apply isType_Sort
                      | [ |- _ = _ ] => eassumption
                      | [ |- _;;;_ |- tSort _ <=s tSort _ ] => apply cumul_Sort
                      end ].
  all: lazymatch goal with
       | [ |- wf_universe _ _ ] => shelve
       | _ => idtac
       end.
  2: { constructor 1; try refine (@eq_refl bool true).
       2: { hnf.
            Print PCUICEquality.eq_term_upto_univ_napp.
             reflexivity.
             constructor.
             reflexivity.
        cbn.
       refine (eq_refl true).
        cbn.
  2: { match goal with
  match goal
  all: match goal with |- _ ;;; _ |- ?e : _ => is_evar e; shelve | _ => idtac end.
  4: {
  match goal with
  all: try apply cumul_Sort.
  Print cumulSpec0.
Set Printing All.

  all:
  21: { cbv [type_of_constructor inductive_mind fst snd cstr_type ind_bodies subst0 inds List.length subst_instance subst_instance_constr].
  all: lazymatch goal with
       | [ |- isType _ _ _ ] => econstructor
       | _ => idtac
       end.
    end ].
  all: cbn.
  Search isType tApp.
  47: {
  all: cbn.
  53: { cbv [PCUICLookup.declared_minductive_gen].
  Search isType tRel.
  cbn -[wf_universe].
  cbv [subst_instance subst_instance_univ0 NonEmptySetFacts.map].
  Set Printing All.
  Search isType tSort.
  lazymatch goal with
  end.
  Search isType tProd.
  all: repeat first [ progress cbn [type_of_constructor ind_type ind_bodies inductive_ind nth_error]
                    | eassumption
                    | reflexivity
                    | match goal with
                      | [ |- declared_inductive _ _ _ _ ] => eapply declared_inductive_from_gen; constructor; hnf
                      | [ |- declared_constructor _ _ _ _ _ ] => eapply declared_constructor_from_gen; repeat apply conj
                      end ].
  all: repeat first [ progress cbn [type_of_constructor ind_type ind_bodies inductive_ind nth_error]
                    | progress cbv [type_of_constructor ind_type]
                    | eassumption
                    | reflexivity
                    | match goal with
                      | [ |- declared_inductive _ _ _ _ ] => eapply declared_inductive_from_gen; constructor; hnf
                      | [ |- declared_constructor _ _ _ _ _ ] => eapply declared_constructor_from_gen; repeat apply conj
                      | [ |- isType _ _ _ ] => eexists
                      end ].
  all: cbn.
  all: repeat first [ reflexivity
                    | eassumption
                    | match goal with
                      | [ |- _;;;_ |- tProd _ _ _ : _ ] => eapply type_Prod
                      | [ |- _;;;_ |- tSort _ : _ ] => eapply type_Sort
                      | [ |- _;;;_ |- tRel _ : _ ] => (idtac + eapply type_Cumul); [ eapply type_Rel | .. ]
                      | [ |- _;;;_ |- tInd _ _ : _ ] => (idtac + eapply type_Cumul); [ eapply type_Ind | .. ]
                      | [ |- wf_local _ [] ] => constructor
                      | [ |- wf_local _ [] ] => constructor
                      | [ |- wf_local _ (_ ,, _) ] => constructor
                      | [ |- lift_typing _ _ _ _ _ ] => hnf; try eexists
                      | [ |- declared_inductive _ _ _ _ ] => eapply declared_inductive_from_gen; constructor; hnf
                      | [ |- declared_constructor _ _ _ _ _ ] => eapply declared_constructor_from_gen; repeat apply conj
                      end ].
  all: match goal with |- wf_universe _ _ => shelve | _ => idtac end.
  all: cbn.
  cbn.
  Search wf_universe.
  2: {  Set Printing All.
                      | [ |- _;;;_ |- tInd _ _ : _ ] => eapply type_Ind
                      | [ |- _;;;_ |- tConstruct _ _ _ : _ ] => eapply type_Construct
Print type_of_constructor.
  hnf.
  Print isType.
  cbn [ind_type].
  all: lazymatch goal with
       | _ => idtac
       end.
  { constructor.
    hnf.
    eassumption.
  match goal with
  end.
  Search declared_inductive lookup_env.
  Set Printing Implicit.
  { repeat match goal with
           end.
    Search eqb.
    match goal with
    end.

  24: {
  Locate weaken_ctx.
  Check weaken_ctx.
  HERE
  3: { cbn.
       match goal with
       end.
  7: {
    match goal with
   end.

  eapply type_Ind.
  eapply type_mkApps.
  match goal with
  end.
  eapply type_App.
  2: {
    match goal with
    cbn [lift_typing].
  2: constructor.
  3: { lazymatch goal with
    end.
           (idtac + eapply type_Cumul); [ eapply H | .. ]
                                         ; eassumption

        constructor 3
  all: repeat first [ assumption
                    | match goal with
                      | [ |- _;;;_ |- tApp _ _ : _ ] => eapply type_App
                      | [ H : @quotation_of_well_typed _ _ _ _ ?qP  |- _;;;_ |- ?qP : _ ]
                        => (idtac + eapply type_Cumul); [ eapply H | .. ]
                      end ].
  2: {
  all: repeat first [ assumption
                    | match goal with
                      | [ |- _;;;_ |- tApp _ _ : _ ] => eapply type_App
                      | [ H : @quotation_of_well_typed _ _ _ _ ?qP  |- _;;;_ |- ?qP : _ ]
                        => (idtac + eapply type_Cumul); [ eapply H | .. ]
                      end ].
  2: { match goal with
                      | [ |- _;;;_ |- tApp _ _ : _ ] => eapply type_App
                      | [ H : @quotation_of_well_typed _ _ _ _ ?qP  |- _;;;_ |- ?qP : _ ]
                        => (idtac + eapply type_Cumul); [ eapply H | .. ]
                      end.
  eapply type_Prod.
  3: {
  all: repeat first [ assumption
                    | match goal with
                      | [ |- _;;;_ |- tApp _ _ : _ ] => eapply type_App
                      | [ |- _;;;_ |- qH : _ ]
                        => (idtac + eapply type_Cumul); [ eapply qtyH | .. ]
                      | [ |- _;;;_ |- qP : _ ]
                        => (idtac + eapply type_Cumul); [ eapply qtyP | .. ]
                      end ].
  3: { match goal with
                 | [ |- _;;;_ |- qP : _ ]
                   => (idtac + eapply type_Cumul); [ eapply qtyP | .. ]
    end.
      eapply qtyP.
  2: { exactly_once econstructor.
       Show Proof.
  2: eapply qtyH.
         | [ |- _;;;_ |- tProd _ _ _ : _ ] => eapply type_Prod
  { eapply type_App.
    eapply type_Prod.
    3: { eapply qtyH; assumption.
         assumption.
         assumption.
         assumption.
      hnf in qtyH.

  cbn [mkApps].

  Search typing tApp.
  Search mkApps typing.

  hnf in qtyH.
  hnf.


Class quotation_of_well_typed {Pcf : config.typing_restriction} {T} (t : T) {qT : quotation_of T} {qt : quotation_of t} := typing_quoted_term_of : forall cf Σ Γ, config.checker_flags_constraint cf -> config.global_env_ext_constraint Σ -> wf_local Σ Γ -> Σ ;;; Γ |- qt : qT.
Class ground_quotable_well_typed {Pcf : config.typing_restriction} T {qT : quotation_of T} {quoteT : ground_quotable T} := typing_quote_ground : forall t : T, quotation_of_well_typed t.


ground_quotable_well_typed {Pcf : config.typing_restriction} T {qT : quotation_of T} {quoteT : ground_quotable T} := typing_quote_ground : forall t : T, quotation_of_well_typed t.

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

(* avoid universe inconsistencies *)
#[export] Polymorphic Instance qfst_cps {A B} {qA : quotation_of A} {qB : quotation_of B} : quotation_of (@fst A B) | 0
  := tApp <% @fst %> [qA; qB].
#[export] Polymorphic Instance qsnd_cps {A B} {qA : quotation_of A} {qB : quotation_of B} : quotation_of (@snd A B) | 0
  := tApp <% @snd %> [qA; qB].
#[export] Polymorphic Instance qpair_cps {A B} {qA : quotation_of A} {qB : quotation_of B} : quotation_of (@pair A B) | 0
  := tApp <% @pair %> [qA; qB].
#[export] Polymorphic Instance qprod_cps {A B} {qA : quotation_of A} {qB : quotation_of B} : quotation_of (@prod A B) | 0
  := tApp <% @prod %> [qA; qB].
#[export] Polymorphic Instance qSome_cps {A} {qA : quotation_of A} : quotation_of (@Some A) | 0
  := tApp <% @Some %> [qA].
#[export] Polymorphic Instance qNone_cps {A} {qA : quotation_of A} : quotation_of (@None A) | 0
  := tApp <% @None %> [qA].
#[export] Polymorphic Instance qoption_cps {A} {qA : quotation_of A} : quotation_of (@option A) | 0
  := tApp <% @option %> [qA].
#[export] Polymorphic Instance qcons_cps {A} {qA : quotation_of A} : quotation_of (@cons A) | 0
  := tApp <% @cons %> [qA].
#[export] Polymorphic Instance qnil_cps {A} {qA : quotation_of A} : quotation_of (@nil A) | 0
  := tApp <% @nil %> [qA].
#[export] Polymorphic Instance qlist_cps {A} {qA : quotation_of A} : quotation_of (@list A) | 0
  := tApp <% @list %> [qA].

Polymorphic Definition ground_quotable_of_iffT {A B} {quoteA : ground_quotable A} {qA : quotation_of A} {qB : quotation_of B} (H : A <~> B) {qH : quotation_of H} : ground_quotable B.
Proof.
  intro b.
  change (@quotation_of B (fst H (snd H b))).
  make_quotation_of_goal ().
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

(* for universe adjustment with [tmDeclareQuotationOfModule], [tmMakeQuotationOfModule] *)
#[export] Unset MetaCoq Strict Unquote Universe Mode.
(* N.B. We need to kludge around COQBUG(https://github.com/coq/coq/issues/17303) in Kernames :-( *)
Polymorphic Definition tmMakeQuotationOfConstants_gen@{d t u _T _above_u'} {debug:debug_opt} (work_around_coq_bug_17303 : bool) (include_submodule : list ident -> bool) (include_supermodule : list ident -> list ident -> bool) (existing_instance : option hint_locality) (base : modpath) (cs : list global_reference) (tmDoWithDefinition : ident -> forall A : Type@{d}, A -> TemplateMonad@{t u} A) : TemplateMonad@{t u} unit
  := let warn_bad_ctx c ctx :=
       (_ <- tmMsg "tmPrepareMakeQuotationOfModule: cannot handle polymorphism";;
        _ <- tmPrint c;;
        _ <- tmPrint ctx;;
        tmReturn tt) in
     let tmDebugMsg s := (if debug
                          then tmMsg s
                          else tmReturn tt) in
     let tmDebugPrint {T : Type@{_T}} (v : T)
       := (if debug
           then tmPrint v
           else tmReturn tt) in
     let on_bad_relevance r :=
       (_ <- tmDebugMsg "skipping irrelevant constant";;
        _ <- tmDebugPrint r;;
        tmReturn tt) in
     let make_qname '(mp, name)
       (* ideally we'd replace _ with __ so that there can't be any collision, but the utility functions aren't written and we don't need it in practice *)
       := option_map
            (fun n => "q" ++ n)%bs
            match split_common_prefix base mp with
            | None => if include_supermodule [] []
                      then Some name
                      else None
            | Some (_, (_common, [], [])) => Some name
            | Some (_, (_common, [], postfix))
              => if include_submodule postfix
                 then Some (String.concat "__DOT__" postfix ++ "__" ++ name)
                 else None
            | Some (_, (_common, base_postfix, postfix))
              => if include_supermodule base_postfix postfix
                 then Some ("__DOT_DOT__" ++ String.concat "__DOT__" base_postfix ++ "__SLASH__" ++ String.concat "__DOT__" postfix ++ "__" ++ name)
                 else None
            end%bs in
     let tmDebugSkipGR '(mp, name) :=
       _ <- tmDebugMsg ("tmMakeQuotationOfConstants_gen: skipping excluded constant " ++ name);;
       _ <- tmDebugPrint (split_common_prefix base mp);;
       ret tt in
     let make_definition '(name, tyv)
       := ((let tmTyv := tmRetypeAroundMetaCoqBug853 name tyv in
            _ <- tmDebugPrint tmTyv;;
            '{| my_projT1 := ty ; my_projT2 := v |} <- tmTyv;;
            tmDef_name <- tmEval cbv (@tmDoWithDefinition (name:string));;
            let tmn := tmDef_name ty v in
            _ <- tmDebugPrint tmn;;
            n <- tmn;;
            _ <- tmDebugMsg "tmMakeQuotationOfConstants_gen: tmQuoteToGlobalReference";;
            qn <- tmQuoteToGlobalReference n;;
            tmReturn qn) : TemplateMonad global_reference) in
     let make_instance p
       := (match existing_instance return TemplateMonad unit with
           | Some locality
             => let tmEx := tmExistingInstance locality p in
                _ <- tmDebugPrint tmEx;;
                tmEx
           | None => tmReturn tt
           end) in
     let cs := dedup_grefs cs in
     cs <- tmEval cbv cs;;
     _ <- tmDebugMsg "tmMakeQuotationOfConstants_gen: looking up module constants";;
     ps <- monad_map@{_ _ Set _above_u'}
             (fun r
              => _ <- tmDebugMsg "tmMakeQuotationOfConstants_gen: handling";;
                 _ <- tmDebugPrint r;;
                 match r with
                 | ConstRef cr
                   => match make_qname cr with
                      | None => tmDebugSkipGR cr
                      | Some qname
                        => '(univs, rel) <- tmQuoteConstantUniversesAndRelevance cr false;;
                           match rel with
                           | Irrelevant => on_bad_relevance cr
                           | Relevant
                             => inst <- match univs with
                                        | Monomorphic_ctx => tmReturn ([] : Instance.t)
                                        | (Polymorphic_ctx (univs, constraints)) as ctx
                                          => _ <- warn_bad_ctx cr ctx;;
                                             tmReturn ([] : Instance.t)
                                        end;;
                                let c := tConst cr inst in
                                _ <- tmDebugMsg "tmMakeQuotationOfConstants_gen: tmUnquote";;
                                '{| my_projT1 := cty ; my_projT2 := cv |} <- tmUnquote c;;
                                _ <- tmDebugMsg "tmMakeQuotationOfConstants_gen: tmUnquote done";;
                                def <- make_definition
                                         (qname, if work_around_coq_bug_17303
                                                 then {| my_projT1 := term ; my_projT2 := c |}
                                                 else {| my_projT1 := @quotation_of cty cv ; my_projT2 := c |});;
                                make_instance def
                           end
                      end
                 | IndRef ind
                   => let '{| inductive_mind := r |} := ind in
                      match make_qname r with
                      | None => tmDebugSkipGR r
                      | Some qname
                        => inst <- (univs <- tmQuoteInductiveUniverses r;;
                                    match univs with
                                    | Monomorphic_ctx => tmReturn ([] : Instance.t)
                                    | (Polymorphic_ctx (univs, constraints)) as ctx
                                      => _ <- warn_bad_ctx r ctx;;
                                         tmReturn ([] : Instance.t)
                                    end);;
                           let c := tInd ind inst in
                           _ <- tmDebugMsg "tmMakeQuotationOfConstants_gen: tmUnquote";;
                           '{| my_projT1 := cty ; my_projT2 := cv |} <- tmUnquote c;;
                           _ <- tmDebugMsg "tmMakeQuotationOfConstants_gen: tmUnquote done";;
                           let tmcty := tmRetypeRelaxSetInCodomain@{t t u} qname cty in
                           _ <- tmDebugPrint tmcty;;
                           cty <- tmcty;;
                           let tmcv := tmObj_magic (B:=cty) cv in
                           _ <- tmDebugPrint tmcv;;
                           cv <- tmcv;;
                           let ty := @inductive_quotation_of cty cv in
                           let v : ty := {| qinductive := ind ; qinst := inst |} in
                           def <- make_definition
                                    (qname, {| my_projT1 := ty ; my_projT2 := v |});;
                           make_instance def
                      end
                 | ConstructRef _ _ | VarRef _ => tmReturn tt
                 end)
             cs;;
     ret tt.

Definition tmMakeQuotationOfConstants {debug:debug_opt} (include_submodule : list ident -> bool) (include_supermodule : list ident -> list ident -> bool) (existing_instance : option hint_locality) (base : modpath) (cs : list global_reference) : TemplateMonad unit
  := tmMakeQuotationOfConstants_gen false include_submodule include_supermodule existing_instance base cs (fun name ty body => @tmDefinition name ty body).

Definition tmMakeQuotationOfConstantsWorkAroundCoqBug17303 {debug:debug_opt} (include_submodule : list ident -> bool) (include_supermodule : list ident -> list ident -> bool) (base : modpath) (cs : list global_reference) : TemplateMonad unit
  := tmMakeQuotationOfConstants_gen true include_submodule include_supermodule None base cs (fun name ty body => @tmDefinition name ty body).

Definition tmDeclareQuotationOfConstants {debug:debug_opt} (include_submodule : list ident -> bool) (include_supermodule : list ident -> list ident -> bool) (existing_instance : option hint_locality) (base : modpath) (cs : list global_reference) : TemplateMonad unit
  := tmMakeQuotationOfConstants_gen false include_submodule include_supermodule existing_instance base cs (fun name ty _ => @tmAxiom name ty).

Variant submodule_inclusion := only_toplevel | all_submodules_except (_ : list (list ident)) | toplevel_and_submodules (_ : list (list ident)) | everything.

#[local] Typeclasses Transparent ident IdentOT.t.
Definition is_submodule_of (super : list ident) (sub : list ident) : bool
  := firstn #|super| sub == super.
Definition is_supermodule_of (sub : list ident) (super : list ident) : bool
  := is_submodule_of super sub.
Definition include_submodule_of_submodule_inclusion (si : submodule_inclusion) : list ident -> bool
  := match si with
     | only_toplevel => fun _ => false
     | all_submodules_except ls => fun i => negb (existsb (is_supermodule_of i) ls)
     | toplevel_and_submodules ls => fun i => existsb (is_supermodule_of i) ls
     | everything => fun _ => true
     end.
Definition include_supermodule_of_submodule_inclusion (si : submodule_inclusion) : list ident -> list ident -> bool
  := match si with
     | everything => fun _ _ => true
     | _ => fun _ _ => false
     end.

Definition tmMakeQuotationOfModule {debug:debug_opt} (include_submodule : submodule_inclusion) (existing_instance : option hint_locality) (m : qualid) : TemplateMonad _
  := cs <- tmQuoteModule m;;
     base <- tmLocateModule1 m;;
     let include_supermodule := include_supermodule_of_submodule_inclusion include_submodule in
     let include_submodule := include_submodule_of_submodule_inclusion include_submodule in
     tmMakeQuotationOfConstants include_submodule include_supermodule existing_instance base cs.
Global Arguments tmMakeQuotationOfModule {_%bool} _ _ _%bs.

Definition tmMakeQuotationOfModuleWorkAroundCoqBug17303 {debug:debug_opt} (include_submodule : submodule_inclusion) (m : qualid) : TemplateMonad _
  := cs <- tmQuoteModule m;;
     base <- tmLocateModule1 m;;
     let include_supermodule := include_supermodule_of_submodule_inclusion include_submodule in
     let include_submodule := include_submodule_of_submodule_inclusion include_submodule in
     tmMakeQuotationOfConstantsWorkAroundCoqBug17303 include_submodule include_supermodule base cs.
Global Arguments tmMakeQuotationOfModuleWorkAroundCoqBug17303 {_%bool} _ _%bs.

Definition tmDeclareQuotationOfModule {debug:debug_opt} (include_submodule : submodule_inclusion) (existing_instance : option hint_locality) (m : qualid) : TemplateMonad _
  := cs <- tmQuoteModule m;;
     base <- tmLocateModule1 m;;
     let include_supermodule := include_supermodule_of_submodule_inclusion include_submodule in
     let include_submodule := include_submodule_of_submodule_inclusion include_submodule in
     tmDeclareQuotationOfConstants include_submodule include_supermodule existing_instance base cs.
Global Arguments tmDeclareQuotationOfModule {_%bool} _ _ _%bs.

(*
Require Import MSetPositive.
Instance: debug_opt := true.
MetaCoq Run (tmMakeQuotationOfModule None "Coq.MSets.MSetPositive.PositiveSet"%bs).
*)
