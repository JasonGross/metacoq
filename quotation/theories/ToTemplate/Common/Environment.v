Require Import Coq.Lists.List.
Require Import Coq.Lists.ListDec.
From MetaCoq.Utils Require Import MCProd All_Forall MCRelations MCReflect.
From MetaCoq.Common Require Import Environment Universes.
From MetaCoq.Quotation.ToTemplate Require Export Init.
From MetaCoq.Quotation.ToTemplate Require Export (hints) Coq.Init Coq.ssr utils BasicAst Primitive Universes Kernames.
From MetaCoq.Quotation.ToTemplate.QuotationOf.Common Require Export Environment.Sig.

Module Retroknowledge.
  #[export] Instance quote_t : ground_quotable Retroknowledge.t.
  destruct 1.
  Set Typeclasses Debug Verbosity 2.
  Typeclasses Opaque ground_quotable Kernames.kername is_allowed_elimination is_lSet valid_constraints valid_constraints0
  ConstraintSet.Empty
ConstraintSet.In
ConstraintSet.Subset
ConstraintSetOrdProp.Above
ConstraintSetOrdProp.Below
Kernames.KernameMap.Empty
Kernames.KernameSet.Empty
Kernames.KernameSet.Equal
Kernames.KernameSet.In
Kernames.KernameSet.Subset
Kernames.KernameSetOrdProp.Above
Kernames.KernameSetOrdProp.Below
LevelExprSet.Empty
LevelExprSet.Equal
LevelExprSet.In
LevelExprSet.Subset
LevelExprSetOrdProp.Above
LevelExprSetOrdProp.Below
LevelSet.Empty
LevelSet.In
LevelSet.Subset
LevelSetOrdProp.Above
LevelSetOrdProp.Below
MCOption.on_Some
MCOption.on_Some_or_None
MCOption.option_default
Universe.on_sort
compare_universe
consistent
consistent_extension_on
declared_cstr_levels
eq_levelalg
eq_universe
eq_universe_
is_allowed_elimination_cuniv
is_uprop
is_uproplevel
is_uproplevel_or_set
is_usprop
is_utype
leq_cuniverse_n
leq_universe
leq_universe_n_
satisfies
leq_universe_n
leq_levelalg_n
ConstraintSet.t
LevelSet.t
Kernames.KernameSet.t
  .
  Time pose (_ : ground_quotable (option Kernames.kername)).
  Debug:
Calling typeclass resolution with flags: depth = ∞,unique = false,do_split = true,fail = false
Debug:
1: looking for (ground_quotable (option Kernames.kername)) without backtracking
Debug: 1.1: simple apply @Init.quote_option on
(ground_quotable (option Kernames.kername)), 2 subgoal(s)
Debug: 1.1-1 : (quotation_of Kernames.kername)
Debug: 1.1-1: looking for (quotation_of Kernames.kername) without backtracking
Debug: 1.1-1.1: exact qkername on (quotation_of Kernames.kername), 0 subgoal(s)
Debug: 1.1-2 : (ground_quotable Kernames.kername)
Debug: 1.1-2: looking for (ground_quotable Kernames.kername) without backtracking
Debug: 1.1-2.1: exact Kernames.quote_kername on
(ground_quotable Kernames.kername), 0 subgoal(s)

Finished transaction in 3.407 secs (3.407u,0.s) (successful)

  exact _.
    := ltac:(destruct 1; exact _).
  Typeclasses eauto := debug.
  #[export] Instance quote_extends {x y} : ground_quotable (@Retroknowledge.extends x y).
  cbv [Retroknowledge.extends].
  simple apply @Init.quote_and.
  Time exact _.
  Time exact _.
  all: simple apply @MCOption.quote_option_extends.
  Time exact _.
  Time exact _.
  Time exact _.
  Time intros.
  Search ground_quotable kername.
  Typeclasses Opaque Kernames.kername.
  Time exact _.
  Time exact _.
  Time pose proof (_ : quotation_of x).
  Time pose proof (_ : quotation_of y).
  Time replace_quotation_of_goal ().
  Time exact _.
  simple apply
  cbv [
    := ltac:(cbv [Retroknowledge.extends]; exact _).
HERE
End Retroknowledge.
Export (hints) Retroknowledge.

Module QuoteEnvironment (T : Term) (Import E : EnvironmentSig T) (Import qT : QuotationOfTerm T) (Import QuoteT : QuoteTerm T) (Import qE : QuotationOfEnvironment T E).

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
  #[export] Instance qretroknowledge : quotation_of retroknowledge := ltac:(cbv -[quotation_of]; exact _).
  #[export] Instance qdeclarations : quotation_of declarations := ltac:(cbv -[quotation_of]; exact _).
  #[export] Instance qglobal_declarations : quotation_of global_declarations := ltac:(cbv [global_declarations]; exact _).
  #[export] Instance qglobal_env_ext : quotation_of global_env_ext := ltac:(cbv -[quotation_of]; exact _).
  #[export] Instance qtyp_or_sort : quotation_of typ_or_sort := ltac:(cbv -[quotation_of]; exact _).
  #[export] Instance qlookup_globals : quotation_of lookup_globals := ltac:(cbv [lookup_globals]; exact _).
  #[export] Instance qlookup_envs : quotation_of lookup_envs := ltac:(cbv [lookup_envs]; exact _).

  Local Lemma forall_all_helper_iff {Σ Σ' : global_env}
    : (forall c, { decls & lookup_envs Σ' c = (decls ++ lookup_envs Σ c)%list })
        <~> All (fun '(c, _) => { decls & lookup_envs Σ' c = decls ++ lookup_envs Σ c }) (declarations Σ).
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
      All (fun '(c, _) => { decls & lookup_envs Σ' c = decls ++ lookup_envs Σ c }) (declarations Σ) &
      Retroknowledge.extends Σ.(retroknowledge) Σ'.(retroknowledge)].

  Definition extends_decls_alt (Σ Σ' : global_env) :=
    [× Σ.(universes) = Σ'.(universes),
      All (fun '(c, _) => { decls & lookup_envs Σ' c = decls ++ lookup_envs Σ c }) (declarations Σ) &
      Σ.(retroknowledge) = Σ'.(retroknowledge)].

  #[export] Instance quote_extends_alt {Σ Σ'} : ground_quotable (@extends_alt Σ Σ') := ltac:(cbv [extends_alt]; exact _).
  #[export] Instance quote_extends_decls_alt {Σ Σ'} : ground_quotable (@extends_decls_alt Σ Σ') := ltac:(cbv [extends_decls_alt]; exact _).
  #[export] Instance qextends_alt : quotation_of extends_alt := ltac:(cbv [extends_alt]; exact _).
  #[export] Instance qextends_decls_alt : quotation_of extends_decls_alt := ltac:(cbv [extends_decls_alt]; exact _).
  #[export] Instance qextends : quotation_of extends := ltac:(cbv [extends]; exact _).
  #[export] Instance qextends_decls : quotation_of extends_decls := ltac:(cbv [extends_decls]; exact _).

  Local Lemma extends_alt_iff {Σ Σ'} : extends_alt Σ Σ' <~> extends Σ Σ'.
  Proof.
    cbv [extends extends_alt].
    destruct (@forall_all_helper_iff Σ Σ').
    split; intros []; split; auto with nocore.
  Defined.

  Local Lemma extends_decls_alt_iff {Σ Σ'} : extends_decls_alt Σ Σ' <~> extends_decls Σ Σ'.
  Proof.
    cbv [extends_decls extends_decls_alt].
    destruct (@forall_all_helper_iff Σ Σ').
    split; intros []; split; auto with nocore.
  Defined.

   #[export] Instance quote_extends {Σ Σ'} : ground_quotable (@extends Σ Σ') := ground_quotable_of_iffT extends_alt_iff.
   #[export] Instance quote_extends_decls {Σ Σ'} : ground_quotable (@extends_decls Σ Σ') := ground_quotable_of_iffT (@extends_alt_iff Σ Σ').
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
     qretroknowledge
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
