(* -*- mode: coq; coq-prog-args: ("-emacs" "-q" "-w" "-deprecated-native-compiler-option" "-native-compiler" "no" "-R" "/github/workspace/metacoq/utils/theories" "MetaCoq.Utils" "-R" "/github/workspace/metacoq/common/theories" "MetaCoq.Common" "-R" "/github/workspace/metacoq/pcuic/theories" "MetaCoq.PCUIC" "-R" "/github/workspace/metacoq/safechecker/theories" "MetaCoq.SafeChecker" "-Q" "/github/workspace/cwd" "Top" "-Q" "/home/coq/.opam/4.13.1+flambda/lib/coq/user-contrib/Bignums" "Bignums" "-Q" "/home/coq/.opam/4.13.1+flambda/lib/coq/user-contrib/Equations" "Equations" "-Q" "/home/coq/.opam/4.13.1+flambda/lib/coq/user-contrib/Ltac2" "Ltac2" "-top" "MetaCoq.SafeChecker.PCUICSafeConversion") -*- *)
(* File reduced by coq-bug-minimizer from original input, then from 5927 lines to 1512 lines, then from 1095 lines to 222 lines, then from 235 lines to 2362 lines, then from 2362 lines to 1248 lines, then from 920 lines to 181 lines, then from 194 lines to 977 lines, then from 982 lines to 198 lines, then from 211 lines to 823 lines, then from 827 lines to 300 lines, then from 313 lines to 861 lines, then from 864 lines to 379 lines, then from 392 lines to 1922 lines, then from 1920 lines to 505 lines *)
(* coqc version 8.16.1 compiled with OCaml 4.13.1
   coqtop version 8.16.1
   Expected coqc runtime on this file: 7.452 sec *)
Require Coq.Init.Ltac.
Require Coq.Bool.Bool.
Require Coq.ZArith.ZArith.
Require Coq.Arith.Arith.
Require Coq.micromega.Lia.
Require Coq.Lists.List.
Require Coq.Init.Nat.
Require Coq.Strings.Ascii.
Require Coq.Strings.String.
Require Coq.Classes.Morphisms.
Require Coq.extraction.Extraction.
Require Coq.Unicode.Utf8_core.
Require Equations.Init.
Require Equations.Signature.
Require Equations.CoreTactics.
Require Coq.Relations.Relation_Definitions.
Require Equations.Prop.Logic.
Require Equations.Prop.Classes.
Require Coq.Program.Tactics.
Require Equations.Prop.EqDec.
Require Equations.Prop.DepElim.
Require Coq.Relations.Relations.
Require Equations.Prop.Constants.
Require Coq.Bool.Bvector.
Require Coq.Arith.Wf_nat.
Require Coq.Wellfounded.Wellfounded.
Require Coq.Relations.Relation_Operators.
Require Coq.Wellfounded.Lexicographic_Product.
Require Coq.Program.Wf.
Require Coq.Logic.FunctionalExtensionality.
Require Equations.Prop.Subterm.
Require Equations.Prop.FunctionalInduction.
Require Equations.Prop.Tactics.
Require Equations.Prop.NoConfusion.
Require Equations.Prop.EqDecInstances.
Require Equations.Prop.Loader.
Require Equations.Prop.Telescopes.
Require Equations.Prop.Equations.
Require MetaCoq.Utils.MCPrelude.
Require Coq.ssr.ssreflect.
Require MetaCoq.Utils.MCReflect.
Require Coq.Unicode.Utf8.
Require Coq.Lists.SetoidList.
Require Coq.Classes.CRelationClasses.
Require Equations.Type.Logic.
Require Equations.Type.Relation.
Require Equations.Type.Relation_Properties.
Require MetaCoq.Utils.MCRelations.
Require Coq.ssr.ssrbool.
Require MetaCoq.Utils.ReflectEq.
Require MetaCoq.Utils.MCList.
Require Coq.Classes.RelationClasses.
Require MetaCoq.Utils.MCProd.
Require MetaCoq.Utils.MCOption.
Require MetaCoq.Utils.MCSquash.
Require MetaCoq.Utils.All_Forall.
Require MetaCoq.Utils.MCArith.
Require Coq.Structures.OrderedType.
Require Coq.Structures.Orders.
Require MetaCoq.Utils.MCCompare.
Require MetaCoq.Utils.MCEquality.
Require Coq.Init.Decimal.
Require Coq.Numbers.DecimalString.
Require Coq.NArith.NArith.
Require Coq.Strings.Byte.
Require Coq.NArith.BinNat.
Require MetaCoq.Utils.ByteCompare.
Require MetaCoq.Utils.ByteCompareSpec.
Require MetaCoq.Utils.bytestring.
Require MetaCoq.Utils.MCString.
Require MetaCoq.Utils.MCTactics.SpecializeBy.
Require MetaCoq.Utils.MCTactics.Zeta1.
Require MetaCoq.Utils.MCTactics.GeneralizeOverHoles.
Require MetaCoq.Utils.MCTactics.FindHyp.
Require MetaCoq.Utils.MCTactics.UniquePose.
Require MetaCoq.Utils.MCTactics.InHypUnderBindersDo.
Require MetaCoq.Utils.MCTactics.SpecializeUnderBindersBy.
Require MetaCoq.Utils.MCTactics.Head.
Require MetaCoq.Utils.MCTactics.DestructHyps.
Require MetaCoq.Utils.MCTactics.DestructHead.
Require MetaCoq.Utils.MCTactics.SpecializeAllWays.
Require MetaCoq.Utils.MCTactics.SplitInContext.
Require Ltac2.Init.
Require Ltac2.Message.
Require Ltac2.Control.
Require Ltac2.Ltac1.
Require MetaCoq.Utils.MCUtils.
Require MetaCoq.Utils.monad_utils.
Require MetaCoq.Utils.utils.
Require Coq.btauto.Btauto.
Require MetaCoq.Common.config.
Require Coq.Structures.OrdersAlt.
Require Coq.MSets.MSetList.
Require Coq.MSets.MSetAVL.
Require Coq.MSets.MSetFacts.
Require Coq.MSets.MSetProperties.
Require Coq.MSets.MSetDecide.
Require Coq.FSets.FMapAVL.
Require Coq.Setoids.Setoid.
Require Coq.Structures.OrderedTypeAlt.
Require Coq.Structures.OrderedTypeEx.
Require Coq.FSets.FMapFacts.
Require MetaCoq.Common.Kernames.
Require Coq.Floats.SpecFloat.
Require MetaCoq.Common.BasicAst.
Require MetaCoq.Common.Universes.
Require Coq.ssr.ssrfun.
Require Coq.Numbers.Cyclic.Int63.Uint63.
Require Coq.Floats.PrimFloat.
Require Coq.Floats.FloatOps.
Require Coq.Numbers.HexadecimalString.
Require MetaCoq.Common.Primitive.
Require MetaCoq.Common.Environment.
Require MetaCoq.PCUIC.PCUICSN.
Axiom proof_admitted : False.
Tactic Notation "admit" := abstract case proof_admitted.
Import MetaCoq.Utils.utils.
Import MetaCoq.Common.config.
Import MetaCoq.Common.uGraph.
Import MetaCoq.PCUIC.PCUICAst.
Import MetaCoq.PCUIC.PCUICTyping.

Lemma wf_ext_gc_of_uctx {cf:checker_flags} {Σ : global_env_ext} (HΣ : ∥ wf_ext Σ ∥)
: ∑ uctx', gc_of_uctx (global_ext_uctx Σ) = Some uctx'.
Admitted.

Section EqualityDecGen.



End EqualityDecGen.
Import MetaCoq.Utils.utils.
Import MetaCoq.Common.config.
Import MetaCoq.Common.uGraph.
Import MetaCoq.PCUIC.PCUICAst.
Import MetaCoq.PCUIC.PCUICTyping.

Definition on_global_decls {cf:checker_flags} Σ :=
  on_global_decls_data cumulSpec0 (lift_typing typing) (cf:=cf) Σ.(universes) Σ.(retroknowledge) Σ.(declarations).

Class abstract_env_struct {cf:checker_flags} (abstract_env_impl abstract_env_ext_impl : Type) := {

  abstract_env_rel : abstract_env_impl -> global_env -> Prop;
  abstract_env_ext_rel : abstract_env_ext_impl -> global_env_ext -> Prop;

  abstract_env_init (cs:ContextSet.t) (retro : Retroknowledge.t) : on_global_univs cs -> abstract_env_impl;
  abstract_env_add_decl X (kn:kername) (d:global_decl) :
   (forall Σ, abstract_env_rel X Σ -> ∥ on_global_decls Σ kn d ∥)
   -> abstract_env_impl;
  abstract_env_add_udecl X udecl :
    (forall Σ, abstract_env_rel X Σ -> ∥ on_udecl Σ.(universes) udecl ∥) ->
    abstract_env_ext_impl ;
  abstract_pop_decls : abstract_env_impl -> abstract_env_impl ;

  abstract_env_lookup : abstract_env_ext_impl -> kername -> option global_decl;
  abstract_primitive_constant : abstract_env_ext_impl -> Primitive.prim_tag -> option kername;

  abstract_env_level_mem : abstract_env_ext_impl -> Level.t -> bool;
  abstract_env_leqb_level_n : abstract_env_ext_impl -> Z -> Level.t -> Level.t -> bool;
  abstract_env_guard : abstract_env_ext_impl -> FixCoFix -> context -> mfixpoint term -> bool;
  abstract_env_is_consistent : abstract_env_impl -> LevelSet.t * GoodConstraintSet.t -> bool ;

}.

Class abstract_env_prop {cf:checker_flags} (abstract_env_impl abstract_env_ext_impl: Type)
  `{!abstract_env_struct abstract_env_impl abstract_env_ext_impl} : Prop := {

  abstract_env_ext_exists X : ∥ ∑ Σ , abstract_env_ext_rel X Σ ∥;
  abstract_env_ext_wf X {Σ} : abstract_env_ext_rel X Σ -> ∥ wf_ext Σ ∥ ;
  abstract_env_ext_irr X {Σ Σ'} :
      abstract_env_ext_rel X Σ -> abstract_env_ext_rel X Σ' ->  Σ = Σ';

  abstract_env_exists X : ∥ ∑ Σ , abstract_env_rel X Σ ∥;
  abstract_env_wf X {Σ} : abstract_env_rel X Σ -> ∥ wf Σ ∥;
  abstract_env_irr X {Σ Σ'} :
    abstract_env_rel X Σ -> abstract_env_rel X Σ' ->  Σ = Σ';

  abstract_env_init_correct univs retro cuniv :
    abstract_env_rel (abstract_env_init univs retro cuniv)
    {| universes := univs; declarations := []; retroknowledge := retro |} ;
  abstract_env_add_decl_correct X Σ kn d H : abstract_env_rel X Σ ->
    abstract_env_rel (abstract_env_add_decl X kn d H) (add_global_decl Σ (kn,d));
  abstract_env_add_udecl_rel X {Σ} udecl H :
    (abstract_env_rel X Σ.1 /\ Σ.2 = udecl) <->
    abstract_env_ext_rel (abstract_env_add_udecl X udecl H) Σ;
  abstract_pop_decls_correct X decls (prf : forall Σ : global_env, abstract_env_rel X Σ ->
            exists d, Σ.(declarations) = d :: decls) :
    let X' := abstract_pop_decls X in
    forall Σ Σ', abstract_env_rel X Σ -> abstract_env_rel X' Σ' ->
                      Σ'.(declarations) = decls /\ Σ.(universes) = Σ'.(universes) /\
                      Σ.(retroknowledge) = Σ'.(retroknowledge);

  abstract_env_lookup_correct X {Σ} kn decl : abstract_env_ext_rel X Σ ->
      In (kn, decl) (declarations Σ) <-> abstract_env_lookup X kn = Some decl ;

  abstract_env_leqb_level_n_correct X {Σ} (wfΣ : abstract_env_ext_rel X Σ):
    let uctx := (wf_ext_gc_of_uctx (abstract_env_ext_wf X wfΣ)).π1 in
    leqb_level_n_spec_gen uctx (abstract_env_leqb_level_n X);
  abstract_env_level_mem_correct X {Σ} (wfΣ : abstract_env_ext_rel X Σ) l:
    LevelSet.In l (global_ext_levels Σ) <-> abstract_env_level_mem X l;
  abstract_env_is_consistent_correct X Σ uctx udecl :
    abstract_env_rel X Σ ->
    ConstraintSet.For_all (declared_cstr_levels (LevelSet.union udecl.1 (global_levels Σ))) udecl.2 ->
    gc_of_uctx udecl = Some uctx ->
    consistent_extension_on (global_uctx Σ) udecl.2 <-> abstract_env_is_consistent X uctx ;

  abstract_env_guard_correct X {Σ} (wfΣ : abstract_env_ext_rel X Σ) fix_cofix Γ mfix :
      guard fix_cofix Σ Γ mfix <-> abstract_env_guard X fix_cofix Γ mfix;
  abstract_primitive_constant_correct X tag Σ :
    abstract_env_ext_rel X Σ -> abstract_primitive_constant X tag = PCUICEnvironment.primitive_constant Σ tag
  }.

Definition abstract_env_impl {cf:checker_flags} := ∑ X Y Z, @abstract_env_prop _ X Y Z.

Global Instance abstract_env_impl_abstract_env_struct {cf:checker_flags} (Σ : abstract_env_impl) : abstract_env_struct Σ.π1 Σ.π2.π1.
Admitted.

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

Module Export MetaCoq_DOT_PCUIC_DOT_PCUICConvCumInversion_WRAPPED.
Module Export PCUICConvCumInversion.
Import MetaCoq.PCUIC.PCUICWellScopedCumulativity.

Definition conv_cum {cf:checker_flags} pb Σ Γ u v :=
  ∥ Σ ;;; Γ ⊢ u ≤[pb] v ∥.

#[global] Hint Resolve sq : core.

End PCUICConvCumInversion.
Module Export MetaCoq.
Module Export PCUIC.
Module Export PCUICConvCumInversion.
Include MetaCoq_DOT_PCUIC_DOT_PCUICConvCumInversion_WRAPPED.PCUICConvCumInversion.
End PCUICConvCumInversion.
Import MetaCoq.PCUIC.Syntax.PCUICPosition.
Import MetaCoq.PCUIC.PCUICSN.
Import MetaCoq.PCUIC.PCUICWellScopedCumulativity.
Import MetaCoq.PCUIC.PCUICConvCumInversion.

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
