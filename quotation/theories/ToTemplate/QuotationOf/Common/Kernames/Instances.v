From MetaCoq.Quotation.ToTemplate Require Export Init.
From MetaCoq.Common Require Import Kernames.
From MetaCoq.Quotation.ToTemplate.QuotationOf.Coq.Structures Require Import Orders.Sig OrdersAlt.Sig OrdersFacts.Sig.
From MetaCoq.Quotation.ToTemplate.QuotationOf.Coq.MSets Require Import MSetAVL.Sig MSetProperties.Sig.
Import List.ListNotations.
Local Open Scope list_scope.
(*
From Coq Require Import Lists.List.
From MetaCoq.Common Require Import Kernames.
From MetaCoq.Utils Require Import bytestring monad_utils.
From MetaCoq.Utils Require Import utils MCList.
From MetaCoq.Template Require Import Loader TemplateMonad.
From MetaCoq.Template Require Import MonadBasicAst MonadAst TemplateMonad Ast Loader.
Require Import Equations.Prop.Classes.
Require Import Coq.Lists.List.
Import ListNotations.

Local Open Scope bs.
Import MCMonadNotation.
Import ListNotations.

Local Set Primitive Projections.
Local Unset Universe Minimization ToSet.
Local Open Scope bs.
Import MCMonadNotation.
Set Printing Universes.
MetaCoq Run (foo <- tmUnquote (tConst
                                 (MPdot (MPdot (MPfile ["Kernames"; "Common"; "MetaCoq"]) "Kername") "OT",
                                   "t") []);;
             let '{| my_projT1 := ty ; my_projT2 := v |} := foo in
             _ <- @tmDefinition "foo" _ (let x : ty := v in tt);;
             _ <- @tmDefinition "bar" _ (let x : ty := v in tt);;
             ret tt).
Set Printing All.
Print bar.
Defined.
  run_template_program (gr <- tmLocate1 "Kername.OT.t";;
                        match gr with
                        | ConstRef cr => v <- tmUnquote (tConst cr nil);;
                                         ret (v, tConst cr nil)
                        | _ => tmFail ""
                        end) (fun v => pose v).

MetaCoq Run (tmMakeQuotationOfModule everything None "KernameSetOrdProp.ME").
 *)
HERE
Module qKername <: QuotationOfOrderedType Kername.
  Module qOT <: QuotationOfOrderedTypeOrig Kername.OT.
    MetaCoq Run (tmMakeQuotationOfModule everything None "Kername.OT").
  End qOT.
  MetaCoq Run (tmMakeQuotationOfModuleWorkAroundCoqBug17303 (all_submodules_except [["OT"]]%bs) (*None*) "Kername").
End qKername.
(*
Module qKernameSet <: MSetAVL.QuotationOfMake Kername KernameSet.
  Instance :debug_opt := true.
  Set Printing Implicit. Set Printing Universes.
  MetaCoq Run (tmMakeQuotationOfModule everything None "KernameSet").
End qKernameSet.
*)
Module qKernameSetOrdProp <: QuotationOfOrdProperties KernameSet KernameSetOrdProp.
  Module qME <: QuotationOfOrderedTypeFacts KernameSet.E KernameSetOrdProp.ME.
    Set Printing Implicit. Set Printing Universes.
    Instance: debug_opt := true.
    MetaCoq Run (tmMakeQuotationOfModule everything None "KernameSetOrdProp.ME").
  End qME.
  Module qML. (* OrderedTypeLists(M.E). *)
    MetaCoq Run (tmMakeQuotationOfModule everything None "KernameSetOrdProp.ML").
  End qML.
  Module qP <: QuotationOfWProperties KernameSet KernameSetOrdProp.P.
    MetaCoq Run (tmMakeQuotationOfModule everything None "KernameSetOrdProp.ME").
  End qP.
  MetaCoq Run (tmMakeQuotationOfModule (all_submodules_except [["ME"]; ["ML"]; ["P"]]%bs) None "KernameSetOrdProp").


  Module qME := Structures.QuotationOfOrderedTypeFacts KernameSet.E KernameSetOrdProp.ME qKername.
  (*Module qML := QuotationOfOrderedTypeLists M.E F.ML.*)
  Module qP <: MSets.QuotationOfWProperties KernameSet KernameSetOrdProp.P.
    Module qDec <: MSets.QuotationOfWDecideOn Kername KernameSet KernameSetOrdProp.P.Dec.
      Module qF <: MSets.QuotationOfWFactsOn Kername KernameSet KernameSetOrdProp.P.Dec.F.
        Module F'. Include KernameSetOrdProp.P.Dec.F. End F'.
        MetaCoq Run (Kernames_mp <- tmExtractBaseModPathFromMod "MetaCoq.Common.Kernames";; tmMakeQuotationOfModuleAndRebase false "F'" (MPdot (MPdot (MPdot (MPdot Kernames_mp "KernameSetOrdProp") "P") "Dec") "F")).
      End qF.
      Module qMSetDecideAuxiliary.
        Module MSetDecideAuxiliary'. Include KernameSetOrdProp.P.Dec.MSetDecideAuxiliary. End MSetDecideAuxiliary'.
        MetaCoq Run (Kernames_mp <- tmExtractBaseModPathFromMod "MetaCoq.Common.Kernames";; tmMakeQuotationOfModuleAndRebase false "MSetDecideAuxiliary'" (MPdot (MPdot (MPdot (MPdot Kernames_mp "KernameSetOrdProp") "P") "Dec") "MSetDecideAuxiliary")).
      End qMSetDecideAuxiliary.
    End qDec.
    Module qFM <: MSets.QuotationOfWFactsOn Kername KernameSet KernameSetOrdProp.P.FM.
      Module FM'. Include KernameSetOrdProp.P.FM. End FM'.
      MetaCoq Run (Kernames_mp <- tmExtractBaseModPathFromMod "MetaCoq.Common.Kernames";; tmMakeQuotationOfModuleAndRebase false "FM'" (MPdot (MPdot (MPdot Kernames_mp "KernameSetOrdProp") "P") "FM")).
    End qFM.
    Module P'. Include KernameSetOrdProp.P. End P'.
    MetaCoq Run (Kernames_mp <- tmExtractBaseModPathFromMod "MetaCoq.Common.Kernames";; tmMakeQuotationOfModuleAndRebase false "P'" (MPdot (MPdot Kernames_mp "KernameSetOrdProp") "P")).
  End qP.
  Module KernameSetOrdProp'. Include KernameSetOrdProp. End KernameSetOrdProp'.
  MetaCoq Run (Kernames_mp <- tmExtractBaseModPathFromMod "MetaCoq.Common.Kernames";; tmMakeQuotationOfModuleAndRebase false "KernameSetOrdProp'" (MPdot Kernames_mp "KernameSetOrdProp")).
End qKernameSetOrdProp.
Module qKernameMap <: FMapAVL.QuotationOfMake Kername.OT KernameMap qKername.qOT.
  Module qRaw.
    Module qProofs.
      Module qMX := Structures.QuotationOfOrderedTypeOrigFacts Kername.OT KernameMap.Raw.Proofs.MX qKername.qOT.
      Module qPX := Structures.QuotationOfKeyOrderedTypeOrig Kername.OT KernameMap.Raw.Proofs.PX qKername.qOT.
      Module qL <: FMapList.QuotationOfRaw Kername.OT KernameMap.Raw.Proofs.L qKername.qOT.
        Module qMX := Structures.QuotationOfOrderedTypeOrigFacts Kername.OT KernameMap.Raw.Proofs.L.MX qKername.qOT.
        Module qPX := Structures.QuotationOfKeyOrderedTypeOrig Kername.OT KernameMap.Raw.Proofs.L.PX qKername.qOT.
        Module L'. Include KernameMap.Raw.Proofs.L. End L'.
        MetaCoq Run (Kernames_mp <- tmExtractBaseModPathFromMod "MetaCoq.Common.Kernames";; tmMakeQuotationOfModuleAndRebase false "L'" (MPdot (MPdot (MPdot (MPdot Kernames_mp "KernameMap") "Raw") "Proofs") "L")).
      End qL.
      Module Proofs'. Include KernameMap.Raw.Proofs. End Proofs'.
      MetaCoq Run (Kernames_mp <- tmExtractBaseModPathFromMod "MetaCoq.Common.Kernames";; tmMakeQuotationOfModuleAndRebase false "Proofs'" (MPdot (MPdot (MPdot Kernames_mp "KernameMap") "Raw") "Proofs")).
    End qProofs.
    Module Raw'. Include KernameMap.Raw. End Raw'.
    MetaCoq Run (Kernames_mp <- tmExtractBaseModPathFromMod "MetaCoq.Common.Kernames";; tmMakeQuotationOfModuleAndRebase false "Raw'" (MPdot (MPdot Kernames_mp "KernameMap") "Raw")).
  End qRaw.
  Module KernameMap'. Include KernameMap. End KernameMap'.
  MetaCoq Run (Kernames_mp <- tmExtractBaseModPathFromMod "MetaCoq.Common.Kernames";; tmMakeQuotationOfModuleAndRebase false "KernameMap'" (MPdot Kernames_mp "KernameMap")).
End qKernameMap.
Module qKernameMapFact.
  Module qF <: QuotationOfWFacts_fun Kername.OT KernameMap KernameMapFact.F.
    Module F'. Include KernameMapFact.F. End F'.
    MetaCoq Run (Kernames_mp <- tmExtractBaseModPathFromMod "MetaCoq.Common.Kernames";; tmMakeQuotationOfModuleAndRebase false "F'" (MPdot (MPdot Kernames_mp "KernameMapFact") "F")).
  End qF.
End qKernameMapFact.

Module QuoteKernameSet := MSets.QuoteMSetAVL Kername KernameSet KernameSetOrdProp qKername qKernameSet qKernameSetOrdProp.
Export (hints) QuoteKernameSet.
Module QuoteKernameMap := FSets.QuoteFMapAVL Kername.OT KernameMap KernameMapFact.F qKername.qOT qKernameMap qKernameMapFact.qF.
Export (hints) QuoteKernameMap.
