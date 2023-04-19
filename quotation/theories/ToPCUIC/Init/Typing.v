From MetaCoq.Utils Require Export bytestring.
From MetaCoq.Utils Require Import utils MCList.
From MetaCoq.Common Require Import MonadBasicAst.
From MetaCoq.PCUIC Require Import PCUICMonadAst PCUICAst PCUICTyping Typing.PCUICWeakeningTyp Syntax.PCUICLiftSubst Syntax.PCUICClosed Typing.PCUICClosedTyp PCUICSpine PCUICArities PCUICSubstitution Syntax.PCUICInduction.
From MetaCoq.TemplatePCUIC Require Import PCUICTemplateMonad Loader.
From MetaCoq.Quotation Require Export CommonUtils.
From MetaCoq.Quotation.ToPCUIC Require Export Init.
From MetaCoq.Quotation.ToPCUIC Require Import (hints) Coq.Init.
Require Import Equations.Prop.Classes.
Require Import Coq.Lists.List.
Export TemplateMonad.Common (export, local, global).
Import ListNotations.
Import MCMonadNotation.
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

Class quotation_of_well_typed {Pcf : config.typing_restriction} {T} (t : T) {qT : quotation_of T} {qt : quotation_of t} := typing_quoted_term_of : forall cf Σ Γ, config.checker_flags_constraint cf -> config.global_env_ext_constraint Σ -> wf Σ -> wf_local Σ Γ -> Σ ;;; Γ |- qt : qT.
Class ground_quotable_well_typed {Pcf : config.typing_restriction} T {qT : quotation_of T} {quoteT : ground_quotable T} := typing_quote_ground : forall t : T, quotation_of_well_typed t.

Class infer_quotation_of_well_typed {T} {t : T} (qt : quotation_of t)
  := { wt_config : config.typing_restriction
     ; wt_qT : quotation_of T
     ; wt_q : @quotation_of_well_typed wt_config T t _ _ }.

Inductive dynlist := dnil | dcons {T} (t : T) (tl : dynlist).
Declare Scope dynlist_scope.
Delimit Scope dynlist_scope with dynlist.
Bind Scope dynlist_scope with dynlist.
Infix "::" := dcons : dynlist_scope.
Notation "[ ]" := dnil : dynlist_scope.
Notation "[ x ]" := (dcons x dnil) : dynlist_scope.
Notation "[ x ; y ; .. ; z ]" :=  (dcons x (dcons y .. (dcons z dnil) ..)) : dynlist_scope.

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

Notation ground_quotable_well_typed_using ls T
  := (match ls%dynlist, T return _ with
      | globals, T'
        => ltac:(let T' := (eval cbv delta [T'] in T') in
                 run_template_program
                   (constraint_for_globals globals)
                   (fun c => refine (@ground_quotable_well_typed
                                       {| config.checker_flags_constraint := _.(config.checker_flags_constraint)
                                       ; config.global_env_ext_constraint := c |}
                                       T' _ _)))
      end)
       (only parsing).
Notation quotation_of_well_typed_using ls t
  := (match ls%dynlist, t return _ with
      | globals, t'
        => ltac:(let t' := (eval cbv delta [t'] in t') in
                 run_template_program
                   (constraint_for_globals globals)
                   (fun c => refine (@quotation_of_well_typed
                                       {| config.checker_flags_constraint := _.(config.checker_flags_constraint)
                                       ; config.global_env_ext_constraint := c |}
                                       _ t' _ _)))
      end)
       (only parsing).
Notation typing_restriction_for_globals ls
  := (match ls%dynlist return _ with
      | globals
        => ltac:(run_template_program
                   (constraint_for_globals globals)
                   (fun c => refine ({| config.checker_flags_constraint := _.(config.checker_flags_constraint)
                                     ; config.global_env_ext_constraint := c |})))
      end)
       (only parsing).


Module Export Instances.
  #[export] Existing Instance Build_infer_quotation_of_well_typed.
  (* #[export] *)
  Coercion wt_q : infer_quotation_of_well_typed >-> quotation_of_well_typed.
  #[export] Instance default_typing_restriction : config.typing_restriction | 1000
    := {| config.checker_flags_constraint cf := true
       ; config.global_env_ext_constraint Σ := true |}.
  #[export] Existing Instance typing_quote_ground.
End Instances.

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

Lemma closed_substitution {cf : config.checker_flags} {Σ}
  (s : list term)
  (Γ' : list term)
  (t T : term)
  (Hs : All2 (fun t T => Σ ;;; [] |- t : T) s Γ')
  (wfΣ : wf Σ)
  (Γ'' := List.map (fun ty => {| BasicAst.decl_name := {| binder_name := nAnon; binder_relevance := Relevant |} ; BasicAst.decl_body := None ; BasicAst.decl_type := ty |}) Γ')
  (Ht : Σ ;;; Γ'' |- t : T)
  : Σ ;;; [] |- subst0 s t : subst0 s T.
Proof.
  apply (@substitution cf Σ wfΣ [] Γ'' s [] t T);
    try (cbn; rewrite app_context_nil_l; assumption).
  clear Ht t T.
  subst Γ''; induction Hs; cbn [List.map]; constructor; trivial.
  { rewrite subst_closedn; [ assumption | ].
    change 0 with #|[]:context|.
    eapply @type_closed; eassumption. }
Qed.

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

(* generates new version of [t * s], where [s] holds (de Bruijn index, quoted term, unquoted term) *)
Fixpoint collect_constants (qt : term) (ts : term * list (nat * term * term)) {struct qt} : term * list (nat * term * term)
  := let '(t, s) := ts in
     match qt with
     | tRel _
     | tVar _
     | tEvar _ _
     | tConst _ _
       => match find (fun '(i, qv, v) => qt == qv) s with
          | Some (i, qv, v) => (tRel i, s)
          | None
            => let i := List.length s in
               (tRel i, (i, qt, t) :: s)
          end
     | tSort _
     | tProd _ _ _
     | tLambda _ _ _
     | tInd _ _
     | tConstruct _ _ _
     | tProj _ _
     | tPrim _
       => (t, s)
     | tLetIn na b B t => _
     | tApp u v => _
     | tCase indn p c brs => _
     | tFix mfix idx => _
     | tCoFix mfix idx => _
     end

#[export] Instance well_typed_ground_quotable_of_bp {b P} (H : b = true -> P) {qH : quotation_of H} (H_for_safety : P -> b = true) {qP : quotation_of P} {Pcf : config.typing_restriction} {qtyH : quotation_of_well_typed H} {qtyP : quotation_of_well_typed P} : @ground_quotable_well_typed (Pcf && typing_restriction_for_globals [bool; @eq bool]) _ qP (@ground_quotable_of_bp b P H qH H_for_safety).
Proof.
  intros t cf Σ Γ Hcf HΣ Hwf HΓ.
  apply andb_andI in Hcf; apply andb_andI in HΣ.
  destruct Hcf, HΣ.
  cbn [config.checker_flags_constraint config.global_env_ext_constraint map fold_right] in *.
  cbv [quote_ground ground_quotable_of_bp Init.quote_bool] in *.
  specialize (H_for_safety t); subst.
  eapply @weaken_ctx with (Γ := nil); [ assumption .. | ].
  repeat match goal with
         | [ H : andb _ _ = true |- _ ] => apply andb_andI in H; destruct H
         | [ H : is_true (andb _ _) |- _ ] => apply andb_andI in H; destruct H
         | [ H : is_true (_ == _) |- _ ] => apply eqb_eq in H
         end.


  let G := match goal with
           | [ |- @typing ?cf ?Σ ?Γ ?t ?T ]
             =>

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
