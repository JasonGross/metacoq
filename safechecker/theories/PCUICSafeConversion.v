(* -*- mode: coq; coq-prog-args: ("-emacs" "-q" "-w" "-deprecated-native-compiler-option" "-native-compiler" "no" "-R" "/github/workspace/metacoq/utils/theories" "MetaCoq.Utils" "-R" "/github/workspace/metacoq/common/theories" "MetaCoq.Common" "-R" "/github/workspace/metacoq/pcuic/theories" "MetaCoq.PCUIC" "-R" "/github/workspace/metacoq/safechecker/theories" "MetaCoq.SafeChecker" "-Q" "/github/workspace/cwd" "Top" "-Q" "/home/coq/.opam/4.13.1+flambda/lib/coq/user-contrib/Bignums" "Bignums" "-Q" "/home/coq/.opam/4.13.1+flambda/lib/coq/user-contrib/Equations" "Equations" "-Q" "/home/coq/.opam/4.13.1+flambda/lib/coq/user-contrib/Ltac2" "Ltac2" "-top" "MetaCoq.SafeChecker.PCUICSafeConversion") -*- *)
(* File reduced by coq-bug-minimizer from original input, then from 5927 lines to 1512 lines *)
(* coqc version 8.16.1 compiled with OCaml 4.13.1
   coqtop version 8.16.1
   Expected coqc runtime on this file: 50.537 sec *)
Require Coq.Init.Ltac.
Require Coq.Logic.ProofIrrelevance.
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
Require Coq.Structures.OrderedTypeAlt.
Require Coq.MSets.MSetAVL.
Require Coq.MSets.MSetFacts.
Require Coq.MSets.MSetProperties.
Require Coq.MSets.MSetDecide.
Require Coq.ZArith.Zcompare.
Require Coq.MSets.MSetInterface.
Require MetaCoq.Utils.wGraph.
Require Coq.Structures.OrdersAlt.
Require Coq.MSets.MSetList.
Require Coq.FSets.FMapAVL.
Require Coq.Setoids.Setoid.
Require Coq.Structures.OrderedTypeEx.
Require Coq.FSets.FMapFacts.
Require MetaCoq.Common.Kernames.
Require Coq.Floats.SpecFloat.
Require MetaCoq.Common.BasicAst.
Require MetaCoq.Common.Universes.
Require Coq.Classes.SetoidTactics.
Require MetaCoq.Common.uGraph.
Require Coq.ssr.ssrfun.
Require Coq.Numbers.Cyclic.Int63.Uint63.
Require Coq.Floats.PrimFloat.
Require Coq.Floats.FloatOps.
Require Coq.Numbers.HexadecimalString.
Require MetaCoq.Common.Primitive.
Require MetaCoq.Common.Environment.
Require Coq.Floats.FloatAxioms.
Require MetaCoq.Common.Reflect.
Require Coq.Classes.CMorphisms.
Require MetaCoq.Common.EnvironmentTyping.
Require MetaCoq.PCUIC.utils.PCUICPrimitive.
Require MetaCoq.PCUIC.PCUICAst.
Require MetaCoq.PCUIC.utils.PCUICSize.
Require MetaCoq.PCUIC.utils.PCUICAstUtils.
Require Coq.Program.Program.
Require Coq.PArith.BinPos.
Require Coq.Arith.Compare_dec.
Require MetaCoq.Utils.LibHypsNaming.
Require MetaCoq.PCUIC.Syntax.PCUICCases.
Require MetaCoq.PCUIC.Syntax.PCUICInduction.
Require MetaCoq.PCUIC.Syntax.PCUICReflect.
Require MetaCoq.PCUIC.Syntax.PCUICLiftSubst.
Require MetaCoq.PCUIC.Syntax.PCUICUnivSubst.
Require MetaCoq.PCUIC.PCUICEquality.
Require MetaCoq.PCUIC.utils.PCUICUtils.
Require MetaCoq.PCUIC.Syntax.PCUICPosition.
Require MetaCoq.PCUIC.utils.PCUICOnOne.
Require MetaCoq.Utils.MCPred.
Require MetaCoq.PCUIC.PCUICSigmaCalculus.
Require MetaCoq.PCUIC.Syntax.PCUICClosed.
Require MetaCoq.PCUIC.Syntax.PCUICOnFreeVars.
Require MetaCoq.PCUIC.PCUICCumulativitySpec.
Require MetaCoq.PCUIC.PCUICTyping.
Require MetaCoq.PCUIC.PCUICGlobalEnv.
Require MetaCoq.PCUIC.Syntax.PCUICTactics.
Require MetaCoq.PCUIC.PCUICReduction.
Require MetaCoq.PCUIC.PCUICCumulativity.
Require MetaCoq.PCUIC.PCUICContextSubst.
Require MetaCoq.PCUIC.PCUICWeakeningEnv.
Require MetaCoq.PCUIC.Conversion.PCUICWeakeningEnvConv.
Require MetaCoq.PCUIC.Syntax.PCUICNamelessDef.
Require MetaCoq.PCUIC.Syntax.PCUICRenameDef.
Require MetaCoq.PCUIC.Syntax.PCUICInstDef.
Require MetaCoq.PCUIC.PCUICGuardCondition.
Require MetaCoq.PCUIC.Typing.PCUICWeakeningEnvTyp.
Require MetaCoq.PCUIC.Conversion.PCUICClosedConv.
Require MetaCoq.PCUIC.Typing.PCUICClosedTyp.
Require MetaCoq.PCUIC.Syntax.PCUICViews.
Require MetaCoq.PCUIC.Conversion.PCUICRenameConv.
Require MetaCoq.PCUIC.Conversion.PCUICWeakeningConv.
Require MetaCoq.PCUIC.Conversion.PCUICOnFreeVarsConv.
Require MetaCoq.PCUIC.Typing.PCUICRenameTyp.
Require MetaCoq.PCUIC.Typing.PCUICWeakeningTyp.
Require MetaCoq.PCUIC.Conversion.PCUICUnivSubstitutionConv.
Require MetaCoq.PCUIC.Conversion.PCUICInstConv.
Require MetaCoq.PCUIC.Typing.PCUICInstTyp.
Require MetaCoq.PCUIC.PCUICSubstitution.
Require MetaCoq.PCUIC.PCUICContextReduction.
Require MetaCoq.PCUIC.Syntax.PCUICDepth.
Require MetaCoq.PCUIC.PCUICParallelReduction.
Require MetaCoq.PCUIC.PCUICParallelReductionConfluence.
Require MetaCoq.PCUIC.PCUICRedTypeIrrelevance.
Require MetaCoq.PCUIC.PCUICConfluence.
Require MetaCoq.PCUIC.PCUICWellScopedCumulativity.
Require MetaCoq.PCUIC.PCUICContextConversion.
Require MetaCoq.PCUIC.PCUICConversion.
Require MetaCoq.PCUIC.PCUICCasesContexts.
Require MetaCoq.PCUIC.PCUICGeneration.
Require MetaCoq.PCUIC.Typing.PCUICContextConversionTyp.
Require MetaCoq.PCUIC.PCUICInversion.
Require MetaCoq.PCUIC.Typing.PCUICUnivSubstitutionTyp.
Require MetaCoq.PCUIC.PCUICContexts.
Require MetaCoq.PCUIC.PCUICWfUniverses.
Require MetaCoq.PCUIC.PCUICArities.
Require MetaCoq.PCUIC.PCUICSpine.
Require MetaCoq.PCUIC.PCUICInductives.
Require MetaCoq.PCUIC.PCUICValidity.
Require MetaCoq.PCUIC.PCUICInductiveInversion.
Require MetaCoq.PCUIC.PCUICAlpha.
Require MetaCoq.PCUIC.PCUICSR.
Require MetaCoq.PCUIC.PCUICNormal.
Require MetaCoq.PCUIC.PCUICSafeLemmata.
Require MetaCoq.PCUIC.PCUICCumulProp.
Require MetaCoq.PCUIC.PCUICPrincipality.
Require MetaCoq.PCUIC.PCUICSN.
Require MetaCoq.PCUIC.PCUICConvCumInversion.
Require MetaCoq.PCUIC.utils.PCUICPretty.
Require MetaCoq.SafeChecker.PCUICErrors.
Require MetaCoq.Utils.canonicaltries.String2pos.
Require MetaCoq.Utils.canonicaltries.CanonicalTries.
Require MetaCoq.Common.EnvMap.
Require MetaCoq.SafeChecker.PCUICEqualityDec.
Require MetaCoq.SafeChecker.PCUICWfEnv.
Require MetaCoq.PCUIC.PCUICCSubst.
Require MetaCoq.PCUIC.PCUICWcbvEval.
Require MetaCoq.PCUIC.PCUICElimination.
Require MetaCoq.PCUIC.PCUICCanonicity.
Require Equations.Type.FunctionalExtensionality.
Require Equations.Type.WellFounded.
Require MetaCoq.SafeChecker.PCUICWfReduction.
Require MetaCoq.SafeChecker.PCUICSafeReduce.

Module Export AdmitTactic.
Module Import LocalFalse.
Inductive False : Prop := .
End LocalFalse.
Axiom proof_admitted : False.
Import Coq.Init.Ltac.
Tactic Notation "admit" := abstract case proof_admitted.
End AdmitTactic.
Import Coq.Logic.ProofIrrelevance.
Import MetaCoq.Utils.utils.
Import MetaCoq.Common.config MetaCoq.Common.uGraph.
Import MetaCoq.PCUIC.PCUICAst MetaCoq.PCUIC.utils.PCUICAstUtils
     MetaCoq.PCUIC.Syntax.PCUICReflect MetaCoq.PCUIC.Syntax.PCUICLiftSubst MetaCoq.PCUIC.Syntax.PCUICUnivSubst MetaCoq.PCUIC.PCUICTyping MetaCoq.PCUIC.PCUICGlobalEnv
     MetaCoq.PCUIC.PCUICCumulativity MetaCoq.PCUIC.PCUICConversion MetaCoq.PCUIC.PCUICEquality MetaCoq.PCUIC.PCUICConversion
     MetaCoq.PCUIC.PCUICSafeLemmata MetaCoq.PCUIC.PCUICNormal MetaCoq.PCUIC.PCUICInversion MetaCoq.PCUIC.PCUICReduction MetaCoq.PCUIC.Syntax.PCUICPosition
     MetaCoq.PCUIC.PCUICPrincipality MetaCoq.PCUIC.PCUICContextConversion MetaCoq.PCUIC.Typing.PCUICContextConversionTyp MetaCoq.PCUIC.PCUICSN MetaCoq.PCUIC.utils.PCUICUtils MetaCoq.PCUIC.PCUICWfUniverses
     MetaCoq.PCUIC.Syntax.PCUICOnFreeVars MetaCoq.PCUIC.PCUICWellScopedCumulativity
     MetaCoq.PCUIC.Conversion.PCUICWeakeningEnvConv MetaCoq.PCUIC.Typing.PCUICWeakeningEnvTyp
     MetaCoq.PCUIC.Conversion.PCUICWeakeningConv MetaCoq.PCUIC.Typing.PCUICWeakeningTyp
     MetaCoq.PCUIC.Syntax.PCUICClosed MetaCoq.PCUIC.Typing.PCUICClosedTyp MetaCoq.PCUIC.PCUICConvCumInversion .
Import MetaCoq.SafeChecker.PCUICErrors MetaCoq.SafeChecker.PCUICWfEnv MetaCoq.SafeChecker.PCUICSafeReduce MetaCoq.SafeChecker.PCUICEqualityDec.
Import Equations.Prop.DepElim.
Import Equations.Prop.Equations.

Local Set Keyed Unification.

Set Default Goal Selector "!".

Implicit Types (cf : checker_flags) (Σ : global_env_ext).

#[global]
Instance red_brs_refl Σ p Γ: CRelationClasses.Reflexive (@red_brs Σ p Γ).
Admitted.

#[global]
Instance conv_cum_trans {cf leq} {Σ : global_env_ext} {Γ} : wf Σ -> RelationClasses.Transitive (@conv_cum cf leq Σ Γ).
Admitted.

Lemma closed_red_mkApps_tConst_axiom {cf} {Σ} {wfΣ : wf Σ} {Γ} {cst u} {args : list term} {cb c} :
  declared_constant Σ cst cb -> cst_body cb = None ->
  Σ ;;; Γ ⊢ mkApps (tConst cst u) args ⇝ c ->
  ∑ args' : list term,
  (c = mkApps (tConst cst u) args') * (red_terms Σ Γ args args').
Admitted.



Section Conversion.

  Context {cf : checker_flags} {nor : normalizing_flags}.

  Context (X_type : abstract_env_impl).

  Context (X : X_type.π2.π1).

  Context {normalization_in : forall Σ, wf_ext Σ -> Σ ∼_ext X -> NormalizationIn Σ}.

  Local Definition heΣ Σ (wfΣ : abstract_env_ext_rel X Σ) :
    ∥ wf_ext Σ ∥ :=  abstract_env_ext_wf _ wfΣ.

  Local Definition hΣ Σ (wfΣ : abstract_env_ext_rel X Σ) :
    ∥ wf Σ ∥ := abstract_env_ext_sq_wf _ _ _ wfΣ.

  Set Equations Transparent.
  Set Equations With UIP.

  Inductive state :=
  | Reduction
  | Term
  | Args
  | Fallback.

  Inductive stateR : state -> state -> Prop :=
  | stateR_Term_Reduction : stateR Term Reduction
  | stateR_Args_Term : stateR Args Term
  | stateR_Fallback_Term : stateR Fallback Term
  | stateR_Args_Fallback : stateR Args Fallback.

  Derive Signature for stateR.

  Lemma stateR_Acc :
    forall s, Acc stateR s.
Admitted.

  Notation wtp Γ t π :=
    (forall Σ (wfΣ : abstract_env_ext_rel X Σ), welltyped Σ Γ (zipc t π)) (only parsing).

  Set Primitive Projections.

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

  Definition wcored Γ (u v : wterm Γ) :=
    forall Σ (wfΣ : abstract_env_ext_rel X Σ), cored' Σ Γ (` u) (` v).

  Lemma wcored_wf :
    forall Γ, well_founded (wcored Γ).
Admitted.

  Import MetaCoq.PCUIC.PCUICAlpha.

  Definition eqt u v := ∥ u ≡α v ∥.

  Lemma eqt_eqterm {Σ} {wfΣ : abstract_env_ext_rel X Σ} {u v} :
    u ≡α v -> eq_term Σ Σ u v.
Admitted.

  Local Instance eqt_refl : RelationClasses.Reflexive eqt.
Admitted.

  Lemma eq_term_valid_pos :
    forall {u v p},
      validpos u p ->
      eqt u v ->
      validpos v p.
Admitted.

  Definition weqt {Γ} (u v : wterm Γ) :=
    eqt (` u) (` v).

  Lemma R_aux (Γ : context) :
    (∑ t : term, pos t × (∑ w : wterm Γ, pos (` w) × state)) ->
    (∑ t : term, pos t × (∑ w : wterm Γ, pos (` w) × state)) -> Prop. Admitted.

  Derive Signature for Subterm.lexprod.

  Lemma R_aux_Acc :
    forall Γ t p w q s,
      (forall Σ, abstract_env_ext_rel X Σ -> welltyped Σ Γ t) ->
      Acc (R_aux Γ) (t ; (p, (w ; (q, s)))).
Admitted.

  Notation pzt u := (zipc (tm1 u) (stk1 u)) (only parsing).
  Notation pps1 u := (stack_pos (tm1 u) (stk1 u)) (only parsing).
  Notation pwt u := (exist (P := fun t => forall Σ, abstract_env_ext_rel X Σ -> welltyped Σ _ t)
                                 _ (fun Σ wfΣ => wth u Σ wfΣ)) (only parsing).
  Notation pps2 u := (stack_pos (tm2 u) (stk2 u)) (only parsing).

  Notation obpack u:=
    (pzt u ; (pps1 u, (pwt u; (pps2 u, st u)))) (only parsing).

  Definition R Γ (u v : pack Γ) :=
    R_aux Γ (obpack u) (obpack v).

  Lemma R_Acc :
    forall Γ u,
      (forall Σ (wfΣ : abstract_env_ext_rel X Σ), welltyped Σ Γ (zipc (tm1 u) (stk1 u))) ->
      Acc (R Γ) u.
Admitted.

  Notation eq_term Σ t u := (eq_term Σ Σ t u).

  Lemma R_aux_irrelevance Γ x y z :
    ((x.π1; x.π2.1), (existT (fun x => pos x × state) (` x.π2.2.π1) x.π2.2.π2)) =
    ((y.π1; y.π2.1), (existT (fun x => pos x × state) (` y.π2.2.π1) y.π2.2.π2)) ->
    R_aux Γ z x -> R_aux Γ z y.
Admitted.

  Lemma R_irrelevance Γ x y z :
    (x.(st), x.(tm1), x.(stk1), x.(tm2), x.(stk2)) =
    (y.(st), y.(tm1), y.(stk1), y.(tm2), y.(stk2)) ->
    R Γ z x -> R Γ z y.
Admitted.

  Lemma R_cored :
    forall Γ p1 p2,
      (forall Σ (wfΣ : abstract_env_ext_rel X Σ), cored Σ Γ (pzt p1) (pzt p2)) ->
      R Γ p1 p2.
Admitted.

  Lemma R_aux_positionR :
    forall Γ t1 t2 (p1 : pos t1) (p2 : pos t2) s1 s2,
      eqt t1 t2 ->
      positionR (` p1) (` p2) ->
      R_aux Γ (t1 ; (p1, s1)) (t2 ; (p2, s2)).
Admitted.

  Lemma R_positionR :
    forall Γ p1 p2,
      (eqt (pzt p1) (pzt p2)) ->
      positionR (` (pps1 p1)) (` (pps1 p2)) ->
      R Γ p1 p2.
Admitted.

  Lemma R_aux_cored2 :
    forall Γ t1 t2 (p1 : pos t1) (p2 : pos t2) w1 w2 q1 q2 s1 s2,
      (eqt t1 t2) ->
      ` p1 = ` p2 ->
      (forall Σ (wfΣ : abstract_env_ext_rel X Σ), cored' Σ Γ (` w1) (` w2)) ->
      R_aux Γ (t1 ; (p1, (w1 ; (q1, s1)))) (t2 ; (p2, (w2 ; (q2, s2)))).
Admitted.

  Lemma R_cored2 :
    forall Γ p1 p2,
      (eqt (pzt p1) (pzt p2)) ->
      ` (pps1 p1) = ` (pps1 p2) ->
      (forall Σ (wfΣ : abstract_env_ext_rel X Σ),
          cored Σ Γ (` (pwt p1)) (` (pwt p2))) ->
      R Γ p1 p2.
Admitted.

  Lemma R_aux_positionR2 :
    forall Γ t1 t2 (p1 : pos t1) (p2 : pos t2) w1 w2 q1 q2 s1 s2,
      (eqt t1 t2) ->
      ` p1 = ` p2 ->
      (eqt (` w1) (` w2)) ->
      positionR (` q1) (` q2) ->
      R_aux Γ (t1 ; (p1, (w1 ; (q1, s1)))) (t2 ; (p2, (w2 ; (q2, s2)))).
Admitted.

  Lemma R_positionR2 :
    forall Γ p1 p2,
      (eqt (pzt p1) (pzt p2)) ->
      ` (pps1 p1) = ` (pps1 p2) ->
      (eqt (` (pwt p1)) (` (pwt p2))) ->
      positionR (` (pps2 p1)) (` (pps2 p2)) ->
      R Γ p1 p2.
Admitted.

  Lemma R_aux_stateR :
    forall Γ t1 t2 (p1 : pos t1) (p2 : pos t2) w1 w2 q1 q2 s1 s2 ,
      (eqt t1 t2) ->
      ` p1 = ` p2 ->
      (eqt (` w1) (` w2)) ->
      ` q1 = ` q2 ->
      stateR s1 s2 ->
      R_aux Γ (t1 ; (p1, (w1 ; (q1, s1)))) (t2 ; (p2, (w2 ; (q2, s2)))).
Admitted.

  Lemma R_stateR :
    forall Γ p1 p2,
      (eqt (pzt p1) (pzt p2)) ->
      ` (pps1 p1) = ` (pps1 p2) ->
      (eqt (` (pwt p1)) (` (pwt p2))) ->
      ` (pps2 p1) = ` (pps2 p2) ->
      stateR (st p1) (st p2) ->
      R Γ p1 p2.
Admitted.

  Definition abstract_env_compare_global_instance := compare_global_instance (abstract_env_lookup X) (abstract_env_eq X).

  Notation eqb_ctx := (eqb_ctx_gen (abstract_env_eq X) abstract_env_compare_global_instance).
  Notation eqb_term := (eqb_term_upto_univ (abstract_env_eq X) (abstract_env_eq X) abstract_env_compare_global_instance).
  Notation leqb_term := (eqb_term_upto_univ (abstract_env_eq X) (abstract_env_leq X) abstract_env_compare_global_instance).

  Definition eqb_term_stack t1 π1 t2 π2 :=
    eqb_ctx (stack_context π1) (stack_context π2) &&
    eqb_term (zipp t1 π1) (zipp t2 π2).

  Lemma iff_reflect (P : Prop) (b : bool) :
    P <-> b -> reflect P b.
Admitted.

  Definition wf_universe_iff  Σ u :
    wf_universeb Σ u <-> wf_universe Σ u.
Admitted.

  Definition wf_universe_instance_iff  Σ u :
    wf_universeb_instance Σ u <-> wf_universe_instance Σ u.
Admitted.

  Notation conv_stack_ctx Γ π1 π2 :=
    (forall Σ, abstract_env_ext_rel X Σ -> ∥ (Σ ⊢ Γ ,,, stack_context π1 = Γ ,,, stack_context π2) ∥).

  Notation conv_term leq Γ t π t' π' :=
    (forall Σ, abstract_env_ext_rel X Σ -> conv_cum leq Σ (Γ ,,, stack_context π) (zipp t π) (zipp t' π'))
      (only parsing).

  Notation alt_conv_term Γ t π t' π' :=
    (forall Σ, abstract_env_ext_rel X Σ -> ∥ Σ ;;; Γ ,,, stack_context π ⊢ zipp t π = zipp t' π' ∥)
      (only parsing).

  Inductive ConversionResult (P : Prop) :=
  | Success (h : P)
  | Error (e : ConversionError) (h : ~P).

  Arguments Success {_} _.
  Arguments Error {_} _.

  Definition isred_full Γ t π :=
    isApp t = false /\
    forall Σ, abstract_env_ext_rel X Σ -> ∥whnf RedFlags.nodelta Σ (Γ,,, stack_context π) (zipp t π)∥.

  Lemma isred_full_nobeta Γ t π :
    isred_full Γ t π ->
    isLambda t ->
    isStackApp π = false.
Admitted.

  Lemma eta_pair {A B} (p q : A * B) :
    p = q ->
    (p.1, p.2) = (q.1, q.2).
Admitted.

  Ltac is_var t :=
    match goal with
    | v : _ |- _ =>
      match t with
      | v => idtac
      end
    end.

  Lemma zipp_stack_cat_decompose_stack t π π' :
    zipp t (π ++ (decompose_stack π').2) = zipp t π.
Admitted.

  Lemma zipc_decompose_stack_empty t π :
    (decompose_stack π).2 = [] ->
    zipc t π = zipp t π.
Admitted.

  Ltac reduce_stack_facts Σ wfΣ :=
    repeat
      match goal with
      | [H: (?a, ?b) = reduce_stack ?f _ ?X ?Γ ?t ?π ?h |- _] =>
        let rid := fresh "r" in
        let decompid := fresh "d" in
        let whid := fresh "w" in
        let isr := fresh "isr" in
        pose proof (reduce_stack_sound f _ X Σ wfΣ Γ t π h) as [rid];
        pose proof (reduce_stack_decompose f _ X Γ t π h) as decompid;
        pose proof (reduce_stack_whnf f _ X Γ t π h Σ wfΣ) as whid;
        pose proof (reduce_stack_isred f _ X Γ t π h) as isr;
        rewrite <- H in rid, decompid, whid, isr; cbn in rid, decompid, whid, isr;
        clear H
      end.

  Lemma zipc_unfold_decompose_stack t π :
    zipc t π = zipc (mkApps t (decompose_stack π).1) (decompose_stack π).2.
Admitted.

  Ltac simpl_stacks :=
    (repeat
       match goal with
       | [H: (?a, ?b) = decompose_stack ?π |- _] =>
         is_var a;
         is_var b;
         apply eta_pair in H; cbn in H; noconf H
       end);
    (repeat
       match goal with
       | [H: context[decompose_stack (appstack ?l ?ρ)] |- _] =>
         (rewrite (decompose_stack_appstack l ρ) in H; cbn in H) || fail 2
       | [H: context[stack_context (?π ++ ?π')] |- _] =>
         (rewrite (stack_context_stack_cat π' π) in H; cbn in H) || fail 2
       | [H: (decompose_stack ?π).2 = [], H': context[stack_context ?π] |- _] =>
         (rewrite <- (stack_context_decompose π), H in H'; cbn in H') || fail 2
       | [H: (decompose_stack ?π).2 = [], H': context[zipc ?t ?π] |- _] =>
         (rewrite (zipc_decompose_stack_empty t π H) in H'; cbn in H') || fail 2
       | [H: context[stack_context (decompose_stack ?π).2] |- _] =>
         (rewrite (stack_context_decompose π) in H; cbn in H) || fail 2
       | [H: context[zipp ?t (?π ++ (decompose_stack ?π').2)] |- _] =>
         (rewrite (zipp_stack_cat_decompose_stack t π π') in H; cbn in H) || fail 2
       | [H: context[zipc ?t (appstack ?args ?π)] |- _] =>
         (rewrite (@zipc_appstack t args π) in H; cbn in H) || fail 2
       | [H: context[zipc ?t (?π ++ ?π')] |- _] =>
         (rewrite (zipc_stack_cat t π π') in H; cbn in H) || fail 2
       | [H: context[zip (mkApps ?t (decompose_stack ?π).1, decompose_stack ?π).2] |- _] =>
         unfold zip in H
       | [H: context[zipc (mkApps ?t (decompose_stack ?π).1) (decompose_stack ?π).2] |- _] =>
         (rewrite <- (zipc_unfold_decompose_stack t π) in H; cbn in H) || fail 2
       | [H: isStackApp ?π = false, H': context[zipp ?t ?π] |- _] =>
         (rewrite (zipp_noStackApp t π H) in H'; cbn in H') || fail 2
       | [H: (decompose_stack ?π).2 = (decompose_stack ?π').2, H': context[stack_context ?π] |- _] =>
         (rewrite <- (stack_context_decompose π), H, (stack_context_decompose π') in H'; cbn in H')
         || fail 2

       | [|- context[decompose_stack (appstack ?l ?ρ)]] =>
         (rewrite (decompose_stack_appstack l ρ); cbn) || fail 2
       | [|- context[stack_context (?π ++ ?π')]] =>
         (rewrite (stack_context_stack_cat π' π); cbn) || fail 2
       | [H: (decompose_stack ?π).2 = [] |- context[stack_context ?π]] =>
         (rewrite <- (stack_context_decompose π), H; cbn) || fail 2
       | [H: (decompose_stack ?π).2 = [] |- context[zipc ?t ?π]] =>
         (rewrite (zipc_decompose_stack_empty t π H); cbn) || fail 2
       | [|- context[stack_context (decompose_stack ?π).2]] =>
         (rewrite (stack_context_decompose π); cbn) || fail 2
       | [|- context[zipp ?t (?π ++ (decompose_stack ?π').2)]] =>
         (rewrite (zipp_stack_cat_decompose_stack t π π'); cbn) || fail 2
       | [|- context[zipc ?t (appstack ?args ?π)]] =>
         (rewrite (@zipc_appstack t args π); cbn) || fail 2
       | [|- context[zipc ?t (?π ++ ?π')]] =>
         (rewrite (zipc_stack_cat t π π'); cbn) || fail 2
       | [|- context[zip (mkApps ?t (decompose_stack ?π).1, decompose_stack ?π).2]] =>
         unfold zip
       | [|- context[zipc (mkApps ?t (decompose_stack ?π).1) (decompose_stack ?π).2]] =>
         (rewrite <- (zipc_unfold_decompose_stack t π); cbn) || fail 2
       | [H: isStackApp ?π = false |- context[zipp ?t ?π]] =>
         (rewrite (zipp_noStackApp t π H); cbn) || fail 2
       | [H: (decompose_stack ?π).2 = (decompose_stack ?π').2 |- context[stack_context ?π]] =>
         (rewrite <- (stack_context_decompose π), H, (stack_context_decompose π'); cbn) || fail 2
       end);
    repeat
      match goal with
      | [H: context[zipp ?t ?π] |- _] => rewrite (zipp_as_mkApps t π) in H
      | [|- context[zipp ?t ?π]] => rewrite (zipp_as_mkApps t π)
      end.

  Ltac simpl_reduce_stack Σ wfΣ := reduce_stack_facts Σ wfΣ ; simpl_stacks.


  Lemma prog_discr (t1 t2 : term) : Prop. Admitted.


  Definition Ret s Γ t π t' π' :=
    forall (leq : conv_pb),
      conv_stack_ctx Γ π π' ->
      (match s with Fallback | Term => isred_full Γ t π | _ => True end) ->
      (match s with Fallback | Term => isred_full Γ t' π' | _ => True end) ->
      (match s with | Fallback => prog_discr t t' | _ => True end) ->
      match s with
      | Reduction
      | Term
      | Fallback => ConversionResult (conv_term leq Γ t π t' π')
      | Args => ConversionResult (forall Σ, abstract_env_ext_rel X Σ -> ∥ws_cumul_pb_terms Σ (Γ,,, stack_context π)
                                   (decompose_stack π).1
                                   (decompose_stack π').1∥)
      end.

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


  Local Notation repack e :=
    (match e with Success h => Success _ | Error er h => Error er _ end)
    (only parsing).

  Notation isconv_red_raw leq t1 π1 t2 π2 aux :=
    (aux Reduction t1 π1 t2 π2 _ _ _ _ leq _ I I I) (only parsing).
  Notation isconv_prog_raw leq t1 π1 t2 π2 aux :=
    (aux Term t1 π1 t2 π2 _ _ _ _ leq _ _ _ I) (only parsing).
  Notation isconv_args_raw leq t1 π1 t2 π2 aux :=
    (aux Args t1 π1 t2 π2 _ _ _ _ leq _ I I I) (only parsing).
  Notation isconv_fallback_raw leq t1 π1 t2 π2 aux :=
    (aux Fallback t1 π1 t2 π2 _ _ _ _ leq _ _ _ _) (only parsing).

  Notation isconv_red leq t1 π1 t2 π2 aux :=
    (repack (isconv_red_raw leq t1 π1 t2 π2 aux)) (only parsing).
  Notation isconv_prog leq t1 π1 t2 π2 aux :=
    (repack (isconv_prog_raw leq t1 π1 t2 π2 aux)) (only parsing).
  Notation isconv_args leq t1 π1 t2 π2 aux :=
    (repack (isconv_args_raw leq t1 π1 t2 π2 aux)) (only parsing).
  Notation isconv_fallback leq t1 π1 t2 π2 aux :=
    (repack (isconv_fallback_raw leq t1 π1 t2 π2 aux)) (only parsing).

  Lemma _isconv_red (Γ : context) (leq : conv_pb)
            (t1 : term) (π1 : stack) (h1 : wtp Γ t1 π1)
            (t2 : term) (π2 : stack) (h2 : wtp Γ t2 π2)
            (hx : conv_stack_ctx Γ π1 π2)
            (aux : Aux Reduction Γ t1 π1 t2 π2 h2)
    : ConversionResult (conv_term leq Γ t1 π1 t2 π2). Admitted.
  Axiom unfold_one_fix : forall (Γ : context) (mfix : mfixpoint term)
            (idx : nat) (π : stack) (h : wtp Γ (tFix mfix idx) π),
    option (term * stack).

  Derive NoConfusion NoConfusionHom for option.

  Lemma unfold_one_fix_red_zipp :
    forall Γ mfix idx π h fn ξ,
      Some (fn, ξ) = unfold_one_fix Γ mfix idx π h ->
      forall Σ (wfΣ : abstract_env_ext_rel X Σ), ∥ red (fst Σ) (Γ ,,, stack_context π) (zipp (tFix mfix idx) π) (zipp fn ξ) ∥.
Admitted.

  Lemma unfold_one_fix_red_zippx :
    forall Γ mfix idx π h fn ξ,
      Some (fn, ξ) = unfold_one_fix Γ mfix idx π h ->
      forall Σ (wfΣ : abstract_env_ext_rel X Σ), ∥ red (fst Σ) Γ (zippx (tFix mfix idx) π) (zippx fn ξ) ∥.
Admitted.

  Lemma unfold_one_fix_red :
    forall Γ mfix idx π h fn ξ,
      Some (fn, ξ) = unfold_one_fix Γ mfix idx π h ->
      forall Σ (wfΣ : abstract_env_ext_rel X Σ), ∥ red (fst Σ) Γ (zipc (tFix mfix idx) π) (zipc fn ξ) ∥.
Admitted.

  Lemma unfold_one_fix_cored :
    forall Γ mfix idx π h fn ξ,
      Some (fn, ξ) = unfold_one_fix Γ mfix idx π h ->
      forall Σ (wfΣ : abstract_env_ext_rel X Σ), cored (fst Σ) Γ (zipc fn ξ) (zipc (tFix mfix idx) π).
Admitted.

  Lemma unfold_one_fix_decompose :
    forall Γ mfix idx π h fn ξ,
      Some (fn, ξ) = unfold_one_fix Γ mfix idx π h ->
      snd (decompose_stack π) = snd (decompose_stack ξ).
Admitted.

  Lemma unfold_one_fix_None Γ mfix idx π wf :
    None = unfold_one_fix Γ mfix idx π wf ->
    ∥∑args,
     forall Σ (wfΣ : abstract_env_ext_rel X Σ),
      All2 (red Σ (Γ,,, stack_context π)) (decompose_stack π).1 args ×
      whnf RedFlags.default Σ (Γ,,, stack_context π) (mkApps (tFix mfix idx) args)∥.
Admitted.

  Inductive prog_view : term -> term -> Type :=
  | prog_view_App u1 v1 u2 v2 :
      prog_view (tApp u1 v1) (tApp u2 v2)

  | prog_view_Const c1 u1 c2 u2 :
      prog_view (tConst c1 u1) (tConst c2 u2)

  | prog_view_Lambda na1 A1 b1 na2 A2 b2 :
      prog_view (tLambda na1 A1 b1) (tLambda na2 A2 b2)

  | prog_view_Prod na1 A1 B1 na2 A2 B2 :
      prog_view (tProd na1 A1 B1) (tProd na2 A2 B2)

  | prog_view_Case ci p c brs ci' p' c' brs' :
      prog_view (tCase ci p c brs) (tCase ci' p' c' brs')

  | prog_view_Proj p c p' c' :
      prog_view (tProj p c) (tProj p' c')

  | prog_view_Fix mfix idx mfix' idx' :
      prog_view (tFix mfix idx) (tFix mfix' idx')

  | prog_view_CoFix mfix idx mfix' idx' :
      prog_view (tCoFix mfix idx) (tCoFix mfix' idx')

  | prog_view_other :
      forall u v, prog_discr u v -> prog_view u v.

  Lemma prog_viewc u v : prog_view u v.
    Admitted.

  Lemma welltyped_wf_local Σ Γ t :
    welltyped Σ Γ t ->
    ∥ wf_local Σ Γ ∥.
Admitted.

  Definition eqb_universe_instance_gen eq u v :=
    forallb2 eq (map Universe.make u) (map Universe.make v).

  Definition eqb_universe_instance :=
    eqb_universe_instance_gen (abstract_env_eq X).

  Lemma eqb_universe_instance_spec :
    forall u v Σ (wfΣ : abstract_env_ext_rel X Σ),
      forallb (wf_universeb Σ) (map Universe.make u) ->
      forallb (wf_universeb Σ) (map Universe.make v) ->
      eqb_universe_instance u v ->
      R_universe_instance (eq_universe (global_ext_constraints Σ)) u v.
Admitted.

  Arguments LevelSet.mem : simpl never.

  Definition abstract_conv_pb_relb `{cf : checker_flags}
    (pb : conv_pb) :=
    match pb with
    | Conv => abstract_env_eq X
    | Cumul => abstract_env_leq X
    end.

  Lemma compare_universeb_complete Σ (wfΣ : abstract_env_ext_rel X Σ) leq u u' :
    wf_universe Σ u ->
    wf_universe Σ u' ->
    compare_universe leq (global_ext_constraints Σ) u u' ->
    abstract_conv_pb_relb leq u u'.
Admitted.

  Lemma get_level_make l :
    LevelExpr.get_level (LevelExpr.make l) = l.
Admitted.

  Lemma compare_universeb_make_complete Σ (wfΣ : abstract_env_ext_rel X Σ) leq x y :
    wf_universe_level Σ x ->
    wf_universe_level Σ y ->
    compare_universe leq (global_ext_constraints Σ) (Universe.make x) (Universe.make y) ->
    abstract_conv_pb_relb leq (Universe.make x) (Universe.make y).
Admitted.

  Lemma eqb_universe_instance_complete Σ (wfΣ : abstract_env_ext_rel X Σ) u u' :
    wf_universe_instance Σ u ->
    wf_universe_instance Σ u' ->
    R_universe_instance (eq_universe (global_ext_constraints Σ)) u u' ->
    eqb_universe_instance u u'.
Admitted.

  Lemma compare_universe_variance_complete Σ (wfΣ : abstract_env_ext_rel X Σ) leq v u u' :
    wf_universe_level Σ u ->
    wf_universe_level Σ u' ->
    R_universe_variance (eq_universe Σ) (compare_universe leq Σ) v u u' ->
    compare_universe_variance (abstract_env_eq X) (abstract_conv_pb_relb leq) v u u'.
Admitted.

  Lemma compare_universe_instance_variance_complete Σ (wfΣ : abstract_env_ext_rel X Σ) leq v u u' :
    wf_universe_instance Σ u ->
    wf_universe_instance Σ u' ->
    R_universe_instance_variance (eq_universe Σ) (compare_universe leq Σ) v u u' ->
    compare_universe_instance_variance (abstract_env_eq X) (abstract_conv_pb_relb leq) v u u'.
Admitted.

  Lemma consistent_instance_ext_wf Σ udecl u :
    consistent_instance_ext Σ udecl u ->
    wf_universe_instance Σ u.
Admitted.

  Lemma welltyped_zipc_tConst_inv Σ (wfΣ : abstract_env_ext_rel X Σ) Γ c u π :
    welltyped Σ Γ (zipc (tConst c u) π) ->
    exists cst,
      declared_constant Σ c cst
      × consistent_instance_ext Σ (cst_universes cst) u.
Admitted.

  Lemma red_conv_cum_l {leq Γ u v Σ}{wfΣ : abstract_env_ext_rel X Σ} :
    Σ ;;; Γ ⊢ u ⇝ v -> conv_cum leq Σ Γ u v.
Admitted.

  Lemma red_conv_cum_r {leq Γ u v Σ}{wfΣ : abstract_env_ext_rel X Σ} :
    Σ ;;; Γ ⊢ u ⇝ v -> conv_cum leq Σ Γ v u.
Admitted.

  Lemma closed_red_zipp {Σ Γ t u π} :
    is_open_term Γ (zipp t π) ->
    Σ ;;; Γ ⊢ t ⇝ u ->
    Σ ;;; Γ ⊢ zipp t π ⇝ zipp u π.
Admitted.

  Ltac specialize_Σ wfΣ :=
    repeat match goal with | h : _ |- _ => specialize (h _ wfΣ) end.

  Lemma unfold_constants (Γ : context) (leq : conv_pb)
            (c : kername) (u : Instance.t) (π1 : stack)
            (h1 : wtp Γ (tConst c u) π1)
            (c' : kername) (u' : Instance.t) (π2 : stack)
            (h2 : wtp Γ (tConst c' u') π2)
            (ne : c <> c' \/ (c = c' /\ ~eqb_universe_instance u u'))
            (hx : conv_stack_ctx Γ π1 π2)
            (aux : Aux Term Γ (tConst c u) π1 (tConst c' u') π2 h2)
    : ConversionResult (conv_term leq Γ (tConst c u) π1 (tConst c' u') π2).
    Admitted.

  Lemma welltyped_zipc_tCase_brs_length Σ (wfΣ : abstract_env_ext_rel X Σ) Γ ci motive discr brs π :
    welltyped Σ Γ (zipc (tCase ci motive discr brs) π) ->
    exists mib oib, declared_inductive Σ ci mib oib /\ #|brs| = #|ind_ctors oib|.
Admitted.

  Lemma isconv_context_aux
            (Γ Γ' Δ Δ' : context)
            (cc : forall Σ (wfΣ : abstract_env_ext_rel X Σ), ∥Σ ⊢ Γ = Γ'∥)
            (check :
               forall (leq : conv_pb) (Δh : context_hole) (t : term) (Δh' : context_hole) (t' : term),
                 Δ = fill_context_hole Δh t ->
                 Δ' = fill_context_hole Δh' t' ->
                 (forall Σ (wfΣ : abstract_env_ext_rel X Σ), ∥ ws_cumul_ctx_pb_rel Conv Σ Γ (context_hole_context Δh) (context_hole_context Δh')∥) ->
                 ConversionResult (forall Σ (wfΣ : abstract_env_ext_rel X Σ), conv_cum leq Σ (Γ,,, context_hole_context Δh) t t'))
            (Δpre Δ'pre Δpost Δ'post : context)
            (eq : Δ = Δpre ,,, Δpost)
            (eq' : Δ' = Δ'pre ,,, Δ'post) :
    ConversionResult (forall Σ (wfΣ : abstract_env_ext_rel X Σ), ∥ws_cumul_ctx_pb_rel Conv Σ Γ Δpre Δ'pre∥).
  Admitted.

  Definition isconv_context
            (Γ Γ' Δ Δ' : context)
            (cc : forall Σ (wfΣ : abstract_env_ext_rel X Σ), ∥ Σ ⊢ Γ = Γ' ∥)
            (check :
               forall (leq : conv_pb) (Δh : context_hole) (t : term) (Δh' : context_hole) (t' : term),
                 Δ = fill_context_hole Δh t ->
                 Δ' = fill_context_hole Δh' t' ->
                 (forall Σ (wfΣ : abstract_env_ext_rel X Σ),  ∥ws_cumul_ctx_pb_rel Conv Σ Γ (context_hole_context Δh) (context_hole_context Δh')∥) ->
                 ConversionResult (forall Σ (wfΣ : abstract_env_ext_rel X Σ), conv_cum leq Σ (Γ,,, context_hole_context Δh) t t'))
    : ConversionResult (forall Σ (wfΣ : abstract_env_ext_rel X Σ), ∥ws_cumul_ctx_pb_rel Conv Σ Γ Δ Δ'∥) :=
    isconv_context_aux Γ Γ' Δ Δ' cc check Δ Δ' [] [] eq_refl eq_refl.

  Lemma case_conv_brs_inv {Γ ci br br' p c brs1 brs2 π}
  (h : wtp Γ (tCase ci p c (brs1 ++ br :: brs2)) π)
  (p' : predicate term) (c' : term) (brs1' brs2' : list (branch term))
  (π' : stack) (h' : wtp Γ (tCase ci p' c' (brs1' ++ br' :: brs2')) π')
  (hx : conv_stack_ctx Γ π π')
  (hp : forall Σ (wfΣ : abstract_env_ext_rel X Σ), ∥ ws_cumul_pb_predicate Σ (Γ ,,, stack_context π) p p' ∥)
  (h1 : forall Σ (wfΣ : abstract_env_ext_rel X Σ), ∥ ws_cumul_pb_brs Σ (Γ ,,, stack_context π) p brs1 brs1' ∥) :
  ∥ ∑ mdecl idecl,
    [× forall Σ (wfΣ : abstract_env_ext_rel X Σ), declared_inductive Σ ci mdecl idecl,
       #|pparams p| = ind_npars mdecl,
       #|pparams p'| = ind_npars mdecl,
       eq_context_gen eq eq br.(bcontext) br'.(bcontext),
       test_context_k (fun k : nat => on_free_vars (closedP k (fun _ : nat => true)))
         #|pparams p| br.(bcontext) &
       test_context_k (fun k : nat => on_free_vars (closedP k (fun _ : nat => true)))
         #|pparams p'| br'.(bcontext)] ∥.
Admitted.

  Lemma isconv_branches (Γ : context)
    (ci : case_info)
    (p : predicate term) (c : term) (brs1 brs2 : list (branch term))
    (π : stack) (h : wtp Γ (tCase ci p c (brs1 ++ brs2)) π)
    (p' : predicate term) (c' : term) (brs1' brs2' : list (branch term))
    (π' : stack) (h' : wtp Γ (tCase ci p' c' (brs1' ++ brs2')) π')
    (hx : conv_stack_ctx Γ π π')
    (hp : forall Σ (wfΣ : abstract_env_ext_rel X Σ), ∥ ws_cumul_pb_predicate Σ (Γ ,,, stack_context π) p p' ∥)
    (h1 : forall Σ (wfΣ : abstract_env_ext_rel X Σ), ∥ ws_cumul_pb_brs Σ (Γ ,,, stack_context π) p brs1 brs1' ∥)
    (aux : Aux Term Γ (tCase ci p c (brs1 ++ brs2)) π (tCase ci p' c' (brs1' ++ brs2')) π' h')
    : ConversionResult (forall Σ (wfΣ : abstract_env_ext_rel X Σ), ∥ ws_cumul_pb_brs Σ (Γ ,,, stack_context π) p brs2 brs2' ∥).

    Admitted.

  Lemma isconv_branches' (Γ : context)
    (ci : case_info)
    (p : predicate term) (c : term) (brs : list (branch term))
    (π : stack) (h : wtp Γ (tCase ci p c brs) π)
    (ci' : case_info)
    (p' : predicate term) (c' : term) (brs' : list (branch term))
    (π' : stack) (h' : wtp Γ (tCase ci' p' c' brs') π')
    (hx : conv_stack_ctx Γ π π')
    (hp : forall Σ (wfΣ : abstract_env_ext_rel X Σ), ∥ ws_cumul_pb_predicate Σ (Γ ,,, stack_context π) p p' ∥)
    (ei : ci = ci')
    (aux : Aux Term Γ (tCase ci p c brs) π (tCase ci' p' c' brs') π' h')
    : ConversionResult (forall Σ (wfΣ : abstract_env_ext_rel X Σ), ∥ ws_cumul_pb_brs Σ (Γ ,,, stack_context π) p brs brs' ∥).
Admitted.


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

  Definition mFixRargMismatch fk :=
    match fk with
    | IndFix => FixRargMismatch
    | CoIndFix => CoFixRargMismatch
    end.

  Definition mFixMfixMismatch fk :=
    match fk with
    | IndFix => FixMfixMismatch
    | CoIndFix => CoFixMfixMismatch
    end.

  Lemma isws_cumul_pb_fix_types (fk : fix_kind) (Γ : context)
    (idx : nat)
    (mfix1 mfix2 : mfixpoint term) (π : stack)
    (h : wtp Γ (mFix fk (mfix1 ++ mfix2) idx) π)
    (mfix1' mfix2' : mfixpoint term) (π' : stack)
    (h' : wtp Γ (mFix fk (mfix1' ++ mfix2') idx) π')
    (hx : conv_stack_ctx Γ π π')
    (h1 : ∥ All2 (fun u v =>
                   (forall Σ (wfΣ : abstract_env_ext_rel X Σ), Σ ;;; Γ ,,, stack_context π ⊢ u.(dtype) = v.(dtype)) ×
                   (u.(rarg) = v.(rarg)) * eq_binder_annot u.(dname) v.(dname)
            ) mfix1 mfix1' ∥)
    (aux : Aux Term Γ (mFix fk (mfix1 ++ mfix2) idx) π (mFix fk (mfix1' ++ mfix2') idx) π' h')
    : ConversionResult (∥ All2 (fun u v =>
          (forall Σ (wfΣ : abstract_env_ext_rel X Σ), Σ ;;; Γ ,,, stack_context π ⊢ u.(dtype) = v.(dtype)) ×
          (u.(rarg) = v.(rarg)) * eq_binder_annot u.(dname) v.(dname)
                          ) mfix2 mfix2' ∥).
    Admitted.

  Lemma conv_context_decl Pcmp :
    forall Σ Γ Δ d d',
      conv_context Pcmp Σ Γ Δ ->
      conv_decls Pcmp Σ Γ Δ d d' ->
      conv_context Pcmp Σ (Γ ,, d) (Δ ,, d').
Admitted.

  Lemma stack_entry_context_mFix_mfix_bd :
    forall fk na ty ra mfix1 mfix2 idx,
      stack_entry_context (mFix_mfix fk (mfix1, def_hole_body na ty ra, mfix2) idx) =
      fix_context_alt (map def_sig mfix1 ++ (na,ty) :: map def_sig mfix2).
admit.
Defined.

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
