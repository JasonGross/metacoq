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

}.

Class abstract_env_prop {cf:checker_flags} (abstract_env_impl abstract_env_ext_impl: Type)
  `{!abstract_env_struct abstract_env_impl abstract_env_ext_impl} : Prop := { }.

Definition abstract_env_impl {cf:checker_flags} := ∑ X Y Z, @abstract_env_prop _ X Y Z.

Global Instance abstract_env_impl_abstract_env_struct {cf:checker_flags} (Σ : abstract_env_impl) : abstract_env_struct Σ.π1 Σ.π2.π1.
Admitted.

Inductive ConversionError :=
.

Module Export MetaCoq_DOT_PCUIC_DOT_PCUICConvCumInversion_WRAPPED.
Module Export PCUICConvCumInversion.
Import MetaCoq.PCUIC.PCUICWellScopedCumulativity.

Axiom conv_cum : forall {cf:checker_flags}, conv_pb -> global_env_ext -> context -> term -> term -> Prop.

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

  Axiom wtp : context -> term -> stack -> Prop.

  Record pack (Γ : context) := mkpack {
    st   : state ;
    tm1  : term ;
    stk1 : stack ;
    tm2  : term ;
    stk2 : stack ;
    wth  : wtp Γ tm2 stk2
  }.

  Axiom R : forall Γ : context, pack Γ -> pack Γ -> Prop.

  Axiom conv_stack_ctx : context -> stack -> stack -> Prop.

  Axiom conv_term : conv_pb -> context -> term -> stack -> term -> stack -> Prop.

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
  Axiom admit : forall {T}, T.
  Equations isws_cumul_pb_fix_bodies {term fix_kind} (fk : fix_kind) (idx : nat)
    (mfix1 mfix2 : mfixpoint term)
    (mfix1' mfix2' : mfixpoint term)
    (h1 : ∥ All2 (fun u v => True) mfix1 mfix1' ∥)
    : True
    by struct mfix2 :=

  isws_cumul_pb_fix_bodies fk idx mfix1 (u :: mfix2) mfix1' (v :: mfix2') h1 := I ;
  isws_cumul_pb_fix_bodies fk idx mfix1 [] mfix1' [] h1 := I ;
  isws_cumul_pb_fix_bodies fk idx mfix1 mfix2 mfix1' mfix2' h1 := False_rect _ _.

  Next Obligation.
    destruct h1 as [h1].
    apply All2_length in h1 as e1.
admit.
  Qed.
  Next Obligation.
admit.
Defined.
