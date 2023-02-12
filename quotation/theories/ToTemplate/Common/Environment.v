Require Import Coq.Lists.List.
Require Import Coq.Lists.ListDec.
From MetaCoq.Quotation.ToTemplate Require Export Coq.Init Coq.ssr utils BasicAst Primitive Universes.
From MetaCoq.Utils Require Import MCProd All_Forall MCRelations MCReflect.
From MetaCoq.Common Require Import Environment Universes.

Module Retroknowledge.
  #[export] Instance quote_t : ground_quotable Retroknowledge.t := ltac:(destruct 1; exact _).
  #[export] Instance quote_extends {x y} : ground_quotable (@Retroknowledge.extends x y) := ltac:(cbv [Retroknowledge.extends]; exact _).

  Module Instances.
    #[export] Existing Instances
     quote_t
     quote_extends
    .
  End Instances.
End Retroknowledge.
Export Retroknowledge.Instances.

Module Type QuoteTerm (T : Term).
  #[export] Declare Instance qterm : quotation_of T.term.
  #[export] Declare Instance quote_term : ground_quotable T.term.

  #[export] Declare Instance qtRel : quotation_of T.tRel.
  #[export] Declare Instance qtSort : quotation_of T.tSort.
  #[export] Declare Instance qtProd : quotation_of T.tProd.
  #[export] Declare Instance qtLambda : quotation_of T.tLambda.
  #[export] Declare Instance qtLetIn : quotation_of T.tLetIn.
  #[export] Declare Instance qtInd : quotation_of T.tInd.
  #[export] Declare Instance qtProj : quotation_of T.tProj.
  #[export] Declare Instance qmkApps : quotation_of T.mkApps.

  #[export] Declare Instance qlift : quotation_of T.lift.
  #[export] Declare Instance qsubst : quotation_of T.subst.
  #[export] Declare Instance qclosedn : quotation_of T.closedn.
  #[export] Declare Instance qnoccur_between : quotation_of T.noccur_between.
  #[export] Declare Instance qsubst_instance_constr : quotation_of T.subst_instance_constr.
End QuoteTerm.

Module Type QuotationOfEnvironment (T : Term) (Import E : EnvironmentSig T).
  #[export] Declare Instance qconstructor_body : inductive_quotation_of constructor_body.
  #[export] Declare Instance qprojection_body : inductive_quotation_of projection_body.
  #[export] Declare Instance qone_inductive_body : inductive_quotation_of one_inductive_body.
  #[export] Declare Instance qmutual_inductive_body : inductive_quotation_of mutual_inductive_body.
  #[export] Declare Instance qconstant_body : inductive_quotation_of constant_body.
  #[export] Declare Instance qglobal_decl : inductive_quotation_of global_decl.
  #[export] Declare Instance qglobal_env : inductive_quotation_of global_env.
  #[export] Declare Instance qAll_decls : inductive_quotation_of All_decls.
  #[export] Declare Instance qAll_decls_alpha : inductive_quotation_of All_decls_alpha.
End QuotationOfEnvironment.

Module QuoteEnvironment (T : Term) (Import E : EnvironmentSig T) (Import QT : QuoteTerm T) (Import QoE : QuotationOfEnvironment T E).

  #[export] Instance quote_constructor_body : ground_quotable constructor_body := ltac:(destruct 1; exact _).
  #[export] Instance quote_projection_body : ground_quotable projection_body := ltac:(destruct 1; exact _).
  #[export] Instance quote_one_inductive_body : ground_quotable one_inductive_body := ltac:(destruct 1; exact _).
  #[export] Instance quote_mutual_inductive_body : ground_quotable mutual_inductive_body := ltac:(destruct 1; exact _).
  #[export] Instance quote_constant_body : ground_quotable constant_body := ltac:(destruct 1; exact _).
  #[export] Instance quote_global_decl : ground_quotable global_decl := ltac:(destruct 1; exact _).

  #[export] Instance quote_global_env : ground_quotable global_env := ltac:(destruct 1; exact _).

  #[export] Instance qcst_type : quotation_of cst_type := ltac:(cbv -[quotation_of]; exact _).
  #[export] Instance qcst_body : quotation_of cst_body := ltac:(cbv -[quotation_of]; exact _).
  #[export] Instance qcst_universes : quotation_of cst_universes := ltac:(cbv -[quotation_of]; exact _).
  #[export] Instance quniverses : quotation_of universes := ltac:(cbv -[quotation_of]; exact _).
  #[export] Instance qdeclarations : quotation_of declarations := ltac:(cbv -[quotation_of]; exact _).
  #[export] Instance qglobal_declarations : quotation_of global_declarations := ltac:(cbv [global_declarations]; exact _).
  #[export] Instance qglobal_env_ext : quotation_of global_env_ext := ltac:(cbv -[quotation_of]; exact _).
  #[export] Instance qtyp_or_sort : quotation_of typ_or_sort := ltac:(cbv -[quotation_of]; exact _).

  Local Definition extends_sig_prop (Σ Σ' : global_env) (k : Kernames.kername) (decls : list global_decl)
    := lookup_envs Σ' k = decls ++ lookup_envs Σ k.
  Local Definition extends_prop (Σ Σ' : global_env) : _ × global_decl -> _
    := fun '(c, _) => sigT (extends_sig_prop Σ Σ' c).
  Local Definition extends_fun (Σ Σ' : global_env)
    := All (extends_prop Σ Σ') (declarations Σ).

  #[export] Instance qextends_sig_prop {Σ Σ' k decls} : quotation_of (extends_sig_prop Σ Σ' k decls) := ltac:(cbv [extends_sig_prop]; exact _).
  #[export] Instance qextends_prop {Σ Σ' k} : quotation_of (extends_prop Σ Σ' k) := ltac:(cbv [extends_prop]; exact _).
  Import MetaCoq.Utils.bytestring.
  Open Scope bs_scope.
  Print qextends_prop.
  Check "ab"%bs.
  #[export] Instance qextends_fun {Σ Σ' k decls} : quotation_of (extends_sig_prop Σ Σ' k decls) := ltac:(cbv [extends_prop]; exact _).

  exact _.
  cbv -[quotation_of].
  (Σ Σ' : global_env) (k : Kernames.kername) (decls : list global_decl)

goal 2 (ID 10586) is:
 quotation_of
   (fun (Σ Σ' : global_env) '(c, _) =>
    {decls : list global_decl & lookup_envs Σ' c = decls ++ lookup_envs Σ c})
goal 3 (ID 10859) is:
 quotation_of
   (fun (Σ Σ' : global_env) (k : Kernames.kername) (decls : list global_decl) =>
    lookup_envs Σ' k = decls ++ lookup_envs Σ k)


  Local Lemma forall_all_helper_iff {Σ Σ' : global_env}
    : (forall c, { decls & lookup_envs Σ' c = (decls ++ lookup_envs Σ c)%list })
        <~> All (fun '(c, _) => { decls & lookup_envs Σ' c = (decls ++ lookup_envs Σ c)%list }) (declarations Σ).
  Proof.
    split.
    { intro H.
      apply In_All; intros [c ?] _; specialize (H c); assumption. }
    { intros H c.
      generalize (fun n k H' => @nth_error_all _ _ _ n (c, k) H' H).
      destruct (In_dec Kernames.KernameSet.E.eq_dec c (List.map fst (declarations Σ))) as [H'|H'].
      { induction (declarations Σ) as [|[k ?] xs IH]; cbn in *.
        { exfalso; assumption. }.
        { destruct (eqb_specT k c); subst.
          { intro H''; specialize (H'' 0 _ eq_refl); cbn in H''.
            exact H''. }
          { assert (H'' : In c (map fst xs)) by now destruct H'.
            inversion H; subst.
            intro H'''; apply IH; auto.
            intros; eapply (H''' (S _)); cbn; eassumption. } } }
      { unfold lookup_envs in *.
        intros _.
        clear H.
        induction (declarations Σ) as [|x xs IH]; cbn in *.
        { eexists; rewrite List.app_nil_r; reflexivity. }
        { destruct (eqb_specT c x.1); subst.
          { exfalso; intuition. }
          { apply IH.
            intuition. } } } }
  Qed.

  (* quotable versions *)
  Definition extends_alt (Σ Σ' : global_env) :=
    [× Σ.(universes) ⊂_cs Σ'.(universes),
      All (fun '(c, _) => { decls & lookup_envs Σ' c = (decls ++ lookup_envs Σ c)%list }) (declarations Σ) &
      Retroknowledge.extends Σ.(retroknowledge) Σ'.(retroknowledge)].

  Definition extends_decls_alt (Σ Σ' : global_env) :=
    [× Σ.(universes) = Σ'.(universes),
      All (fun c => { decls & lookup_envs Σ' c.1 = (decls ++ lookup_envs Σ c.1)%list }) (declarations Σ) &
      Σ.(retroknowledge) = Σ'.(retroknowledge)].

  #[export] Instance quote_extends_alt {Σ Σ'} : ground_quotable (@extends_alt Σ Σ').
  cbv [extends_alt].
  apply @quote_and3; try exact _.
  2: apply @quote_All; try exact _.
  3: intro.
  Import StrongerInstances.
  3: destruct x.
  3: apply @quote_sigT; try exact _.
  all: revert_quotable_hyps ().
  all: clear.

  3: { clear.
  3: exact _.
    := ltac:(cbv [extends_alt]; exact _).

  Definition quote_extends_alt  Σ Σ' : global_env) :=
  #[export] Instance qtyp_or_sort : quotation_of typ_or_sort := ltac:(cbv -[quotation_of]; exact _).
    [× Σ.(universes) ⊂_cs Σ'.(universes),
      All (fun '(c, _) => { decls & lookup_envs Σ' c = (decls ++ lookup_envs Σ c)%list }) (declarations Σ) &
      Retroknowledge.extends Σ.(retroknowledge) Σ'.(retroknowledge)].

  Definition extends_decls_alt (Σ Σ' : global_env) :=
    [× Σ.(universes) = Σ'.(universes),
      All (fun '(c, _) => { decls & lookup_envs Σ' c = (decls ++ lookup_envs Σ c)%list }) (declarations Σ) &
      Σ.(retroknowledge) = Σ'.(retroknowledge)].

  #[export] Instance quote_extends {Σ Σ'} : ground_quotable (@extends Σ Σ').
  cbv [extends].
  apply @MCProd.quote_and3; try exact _.
  revert_quotable_hyps ().

  exact
  repeat match goal with
  | [ H : _ |- quotation_of _ ]
    => revert H;
       lazymatch goal with
       | [ |- forall x : ?A, quotation_of (@?P x) ]
         => assert (quotation_of P);
            [
            | intro H;
              pose proof (_ : quotation_of H);
              change (quotation_of (P H)); exact _ ]
       end
  end.

  repeat match goal with H : _ |- _ => revert H end.
  match goal with
  | [ |-
  pose proof (_ : ground_quotable global_env).
  pose proof (_ : quotation_of Σ).
  pose proof (_ : quotation_of Σ').


    := ltac:(cbv [extends]; exact _).
  #[export] Instance quote_extends_decls {Σ Σ'} : ground_quotable (@extends_decls Σ Σ') := ltac:(cbv [extends_decls]; exact _).
  #[export] Instance quote_extends_strictly_on_decls {Σ Σ'} : ground_quotable (@extends_strictly_on_decls Σ Σ') := ltac:(cbv [extends_strictly_on_decls]; exact _).
  #[export] Instance quote_strictly_extends_decls {Σ Σ'} : ground_quotable (@strictly_extends_decls Σ Σ') := ltac:(cbv [strictly_extends_decls]; exact _).

  #[export] Instance quote_primitive_invariants {cdecl} : ground_quotable (primitive_invariants cdecl) := _.

  #[export] Instance quote_All_decls {P t t'} {qP : quotation_of P} {quoteP : forall t t', ground_quotable (P t t')} : ground_quotable (All_decls P t t') := ltac:(induction 1; exact _).
  #[export] Instance quote_All_decls_alpha {P t t'} {qP : quotation_of P} {quoteP : forall t t', ground_quotable (P t t')} : ground_quotable (All_decls_alpha P t t') := ltac:(induction 1; exact _).
  #[export] Instance qcontext : quotation_of context := ltac:(cbv [context]; exact _).
  #[export] Instance qsubst_context : quotation_of subst_context := ltac:(cbv [subst_context]; exact _).
  #[export] Instance qsmash_context : quotation_of smash_context := ltac:(cbv [smash_context]; exact _).

  #[export] Instance qind_finite : quotation_of ind_finite := ltac:(cbv [ind_finite]; exact _).
  #[export] Instance qind_npars : quotation_of ind_npars := ltac:(cbv [ind_npars]; exact _).
  #[export] Instance qind_params : quotation_of ind_params := ltac:(cbv [ind_params]; exact _).
  #[export] Instance qind_bodies : quotation_of ind_bodies := ltac:(cbv [ind_bodies]; exact _).
  #[export] Instance qind_universes : quotation_of ind_universes := ltac:(cbv [ind_universes]; exact _).
  #[export] Instance qind_variance : quotation_of ind_variance := ltac:(cbv [ind_variance]; exact _).

  #[export] Instance qcontext_assumptions : quotation_of context_assumptions := ltac:(cbv [context_assumptions]; exact _).
  #[export] Instance qextended_subst : quotation_of extended_subst := ltac:(cbv [extended_subst]; exact _).
  #[export] Instance qlift_context : quotation_of lift_context := ltac:(cbv [lift_context]; exact _).
  #[export] Instance qexpand_lets_k_ctx : quotation_of expand_lets_k_ctx := ltac:(cbv [expand_lets_k_ctx]; exact _).
  #[export] Instance qexpand_lets_ctx : quotation_of expand_lets_ctx := ltac:(cbv [expand_lets_ctx]; exact _).

  #[export] Instance qcstr_name : quotation_of cstr_name := ltac:(cbv [cstr_name]; exact _).
  #[export] Instance qcstr_args : quotation_of cstr_args := ltac:(cbv [cstr_args]; exact _).
  #[export] Instance qcstr_indices : quotation_of cstr_indices := ltac:(cbv [cstr_indices]; exact _).
  #[export] Instance qcstr_type : quotation_of cstr_type := ltac:(cbv [cstr_type]; exact _).
  #[export] Instance qcstr_arity : quotation_of cstr_arity := ltac:(cbv [cstr_arity]; exact _).

  #[export] Instance qexpand_lets_k : quotation_of expand_lets_k := ltac:(cbv [expand_lets_k]; exact _).
  #[export] Instance qexpand_lets : quotation_of expand_lets := ltac:(cbv [expand_lets]; exact _).

  #[export] Instance qfst_ctx : quotation_of fst_ctx := ltac:(cbv [fst_ctx]; exact _).

  #[export] Instance qlookup_global : quotation_of lookup_global := ltac:(cbv [lookup_global]; exact _).
  #[export] Instance qlookup_env : quotation_of lookup_env := ltac:(cbv [lookup_env]; exact _).

  #[export] Instance qind_name : quotation_of ind_name := ltac:(cbv [ind_name]; exact _).
  #[export] Instance qind_indices : quotation_of ind_indices := ltac:(cbv [ind_indices]; exact _).
  #[export] Instance qind_sort : quotation_of ind_sort := ltac:(cbv [ind_sort]; exact _).
  #[export] Instance qind_type : quotation_of ind_type := ltac:(cbv [ind_type]; exact _).
  #[export] Instance qind_kelim : quotation_of ind_kelim := ltac:(cbv [ind_kelim]; exact _).
  #[export] Instance qind_ctors : quotation_of ind_ctors := ltac:(cbv [ind_ctors]; exact _).
  #[export] Instance qind_projs : quotation_of ind_projs := ltac:(cbv [ind_projs]; exact _).
  #[export] Instance qind_relevance : quotation_of ind_relevance := ltac:(cbv [ind_relevance]; exact _).

  Module Instances.
    #[export] Existing Instances
     quote_constructor_body
     quote_projection_body
     quote_one_inductive_body
     quote_mutual_inductive_body
     quote_constant_body
     quote_global_decl
     quote_global_env
     qcst_type
     qcst_body
     qcst_universes
     quniverses
     qdeclarations
     qglobal_declarations
     qglobal_env_ext
     qtyp_or_sort
     qcontext
     qsubst_context
     qsmash_context
     qind_params
     qcontext_assumptions
     qextended_subst
     qlift_context
     qexpand_lets_k_ctx
     qexpand_lets_ctx
     qcstr_name
     qcstr_args
     qcstr_indices
     qcstr_type
     qcstr_arity
     qexpand_lets_k
     qexpand_lets
     qind_finite
     qind_npars
     qind_params
     qind_bodies
     qind_universes
     qind_variance
     qfst_ctx
     qlookup_global
     qlookup_env
     qind_name
     qind_indices
     qind_sort
     qind_type
     qind_kelim
     qind_ctors
     qind_projs
     qind_relevance
     quote_extends
     quote_extends_decls
     quote_primitive_invariants
     quote_All_decls
     quote_All_decls_alpha
    .
  End Instances.
End QuoteEnvironment.
