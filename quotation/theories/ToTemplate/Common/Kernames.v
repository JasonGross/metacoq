From Coq Require Import Lists.List.
From MetaCoq.Quotation.ToTemplate Require Export Init.
From MetaCoq.Quotation.ToTemplate Require Export (hints) Coq.Init Coq.Structures Coq.MSets Coq.FSets bytestring.
From MetaCoq.Common Require Import Kernames.
From MetaCoq.Utils Require Import bytestring monad_utils.
From MetaCoq.Template Require Import Loader TemplateMonad.

Local Open Scope bs.
Import MCMonadNotation.
Import ListNotations.

#[export] Instance quote_modpath : ground_quotable modpath := ltac:(induction 1; exact _).

Module qKername <: QuotationOfOrderedType Kername.
  MetaCoq Run (tmMakeQuotationOfModule false "Kername").
  Module qOT <: QuotationOfOrderedTypeOrig Kername.OT.
    (* kludge around https://github.com/MetaCoq/metacoq/issues/847 *)
    Module OT'. Include Kername.OT. End OT'.
    MetaCoq Run (Kername_mp <- tmExtractBaseModPathFromMod "Kername";; tmMakeQuotationOfModuleAndRebase false "OT'" (MPdot Kername_mp "OT")).
  End qOT.
End qKername.

Module qKernameSet <: MSetAVL.QuotationOfMake Kername KernameSet.
  (* kludge around https://github.com/MetaCoq/metacoq/issues/847 *)
  Module KernameSet'. Include KernameSet. End KernameSet'.
  Module qRaw.
    Module Raw'. Include KernameSet.Raw. End Raw'.
    MetaCoq Run (Kernames_mp <- tmExtractBaseModPathFromMod "Kernames";; tmMakeQuotationOfModuleAndRebase false "Raw'" (MPdot (MPdot Kernames_mp "KernameSet") "Raw")).
  End qRaw.
  MetaCoq Run (Kernames_mp <- tmExtractBaseModPathFromMod "Kernames";; tmMakeQuotationOfModuleAndRebase false "KernameSet'" (MPdot Kernames_mp "KernameSet")).
End qKernameSet.
Module qKernameSetOrdProp <: MSets.QuotationOfOrdProperties KernameSet KernameSetOrdProp qKername.
  Module qME := Structures.QuotationOfOrderedTypeFacts KernameSet.E KernameSetOrdProp.ME qKername.
  (*Module qML := QuotationOfOrderedTypeLists M.E F.ML.*)
  Module qP <: MSets.QuotationOfWProperties KernameSet KernameSetOrdProp.P.
    Module qDec <: MSets.QuotationOfWDecideOn Kername KernameSet KernameSetOrdProp.P.Dec.
      Module qF <: MSets.QuotationOfWFactsOn Kername KernameSet KernameSetOrdProp.P.Dec.F.
        Module F'. Include KernameSetOrdProp.P.Dec.F. End F'.
        MetaCoq Run (Kernames_mp <- tmExtractBaseModPathFromMod "Kernames";; tmMakeQuotationOfModuleAndRebase false "F'" (MPdot (MPdot (MPdot (MPdot Kernames_mp "KernameSetOrdProp") "P") "Dec") "F")).
      End qF.
      Module qMSetDecideAuxiliary.
        Module MSetDecideAuxiliary'. Include KernameSetOrdProp.P.Dec.MSetDecideAuxiliary. End MSetDecideAuxiliary'.
        MetaCoq Run (Kernames_mp <- tmExtractBaseModPathFromMod "Kernames";; tmMakeQuotationOfModuleAndRebase false "MSetDecideAuxiliary'" (MPdot (MPdot (MPdot (MPdot Kernames_mp "KernameSetOrdProp") "P") "Dec") "MSetDecideAuxiliary")).
      End qMSetDecideAuxiliary.
    End qDec.
    Module qFM <: MSets.QuotationOfWFactsOn Kername KernameSet KernameSetOrdProp.P.FM.
      Module FM'. Include KernameSetOrdProp.P.FM. End FM'.
      MetaCoq Run (Kernames_mp <- tmExtractBaseModPathFromMod "Kernames";; tmMakeQuotationOfModuleAndRebase false "FM'" (MPdot (MPdot (MPdot Kernames_mp "KernameSetOrdProp") "P") "FM")).
    End qFM.
    Module P'. Include KernameSetOrdProp.P. End P'.
    MetaCoq Run (Kernames_mp <- tmExtractBaseModPathFromMod "Kernames";; tmMakeQuotationOfModuleAndRebase false "P'" (MPdot (MPdot Kernames_mp "KernameSetOrdProp") "P")).
  End qP.
  Module KernameSetOrdProp'. Include KernameSetOrdProp. End KernameSetOrdProp'.
  MetaCoq Run (Kernames_mp <- tmExtractBaseModPathFromMod "Kernames";; tmMakeQuotationOfModuleAndRebase false "KernameSetOrdProp'" (MPdot Kernames_mp "KernameSetOrdProp")).
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
        MetaCoq Run (Kernames_mp <- tmExtractBaseModPathFromMod "Kernames";; tmMakeQuotationOfModuleAndRebase false "L'" (MPdot (MPdot (MPdot (MPdot Kernames_mp "KernameMap") "Raw") "Proofs") "L")).
      End qL.
      Module Proofs'. Include KernameMap.Raw.Proofs. End Proofs'.
      MetaCoq Run (Kernames_mp <- tmExtractBaseModPathFromMod "Kernames";; tmMakeQuotationOfModuleAndRebase false "Proofs'" (MPdot (MPdot (MPdot Kernames_mp "KernameMap") "Raw") "Proofs")).
    End qProofs.
    Module Raw'. Include KernameMap.Raw. End Raw'.
    MetaCoq Run (Kernames_mp <- tmExtractBaseModPathFromMod "Kernames";; tmMakeQuotationOfModuleAndRebase false "Raw'" (MPdot (MPdot Kernames_mp "KernameMap") "Raw")).
  End qRaw.
  Module KernameMap'. Include KernameMap. End KernameMap'.
  MetaCoq Run (Kernames_mp <- tmExtractBaseModPathFromMod "Kernames";; tmMakeQuotationOfModuleAndRebase false "KernameMap'" (MPdot Kernames_mp "KernameMap")).
End qKernameMap.
Module qKernameMapFact.
  Module qF <: QuotationOfWFacts_fun Kername.OT KernameMap KernameMapFact.F.
    Module F'. Include KernameMapFact.F. End F'.
    MetaCoq Run (Kernames_mp <- tmExtractBaseModPathFromMod "Kernames";; tmMakeQuotationOfModuleAndRebase false "F'" (MPdot (MPdot Kernames_mp "KernameMapFact") "F")).
  End qF.
End qKernameMapFact.

Module QuoteKernameSet := MSets.QuoteMSetAVL Kername KernameSet KernameSetOrdProp qKername qKernameSet qKernameSetOrdProp.
Export (hints) QuoteKernameSet.
Module QuoteKernameMap := FSets.QuoteFMapAVL Kername.OT KernameMap KernameMapFact.F qKername.qOT qKernameMap qKernameMapFact.qF.
Export (hints) QuoteKernameMap.

#[export] Instance quote_inductive : ground_quotable inductive := ltac:(destruct 1; exact _).
#[export] Instance quote_projection : ground_quotable projection := ltac:(destruct 1; exact _).
#[export] Instance quote_global_reference : ground_quotable global_reference := ltac:(destruct 1; exact _).
